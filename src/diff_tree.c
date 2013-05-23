/*
 * Copyright (C) 2012 the libgit2 contributors
 *
 * This file is part of libgit2, distributed under the GNU GPL v2 with
 * a Linking Exception. For full terms see the included COPYING file.
 */

#include "common.h"
#include "iterator.h"
#include "diff.h"
#include "diff_tree.h"

#include "git2/diff_tree.h"
#include "git2/oid.h"
#include "git2/config.h"

/**
 * n-way tree differencing
 */

static int index_entry_cmp(git_index_entry *a, git_index_entry *b)
{
	int diff;
	
	assert (a && b);

	/* Ignore tree changes */
	if (S_ISDIR(a->mode) && S_ISDIR(b->mode))
		return 0;
	
	if ((diff = a->mode - b->mode) == 0)
		diff = git_oid_cmp(&a->oid, &b->oid);
	
	return diff;
}

int git_diff_tree_many(
	git_repository *repo,
	git_tree **trees,
	size_t trees_length,
	uint32_t flags,
	git_diff_tree_many_cb callback,
	void *payload)
{
	git_iterator **iterators;
	git_index_entry **items = NULL, *best_cur_item, **cur_items;
	git_vector_cmp entry_compare = git_index_entry__cmp;
	int cur_item_modified;
	size_t i;
	int error = 0;
	
	assert(repo && trees && callback);
	
	iterators = git__calloc(trees_length, sizeof(git_iterator *));
	GITERR_CHECK_ALLOC(iterators);
	
	items = git__calloc(trees_length, sizeof(git_index_entry *));
	GITERR_CHECK_ALLOC(items);
	
	cur_items = git__calloc(trees_length, sizeof(git_index_entry *));
	GITERR_CHECK_ALLOC(cur_items);
	
	for (i = 0; i < trees_length; i++) {
		if ((error = git_iterator_for_tree(&iterators[i], trees[i], 0, NULL, NULL)) < 0)
			return -1;
	}
	
	/* Set up the iterators */
	for (i = 0; i < trees_length; i++) {
		if ((error = git_iterator_current((const git_index_entry **)&items[i],
			iterators[i])) < 0)
			goto done;
	}
	
	while (true) {
		memset(cur_items, 0x0, sizeof(git_index_entry *) * trees_length);
		best_cur_item = NULL;
		cur_item_modified = 0;
		
		/* Find the next path(s) to consume from each iterator */
		for (i = 0; i < trees_length; i++) {
			if (items[i] == NULL) {
				cur_item_modified = 1;
				continue;
			}
			
			if (best_cur_item == NULL) {
				best_cur_item = items[i];
				cur_items[i] = items[i];
			} else {
				int path_diff = entry_compare(items[i], best_cur_item);
								
				if (path_diff < 0) {
					/*
					 * Found an item that sorts before our current item, make
					 * our current item this one.
					 */
					memset(cur_items, 0x0, sizeof(git_index_entry *) * trees_length);
					cur_item_modified = 1;
					best_cur_item = items[i];
					cur_items[i] = items[i];
				} else if (path_diff > 0) {
					/* No entry for the current item, this is modified */
					cur_item_modified = 1;
				} else if (path_diff == 0) {
					cur_items[i] = items[i];
					
					if (!cur_item_modified && !(flags & GIT_DIFF_TREE_RETURN_UNMODIFIED))
						cur_item_modified = index_entry_cmp(best_cur_item, items[i]);
				}
			}
		}
		
		if (best_cur_item == NULL)
			break;
		
		if (cur_item_modified || (flags & GIT_DIFF_TREE_RETURN_UNMODIFIED)) {
			if (callback((const git_index_entry **)cur_items, payload)) {
				error = GIT_EUSER;
				goto done;
			}
		}
		
		/* Advance each iterator that participated */
		for (i = 0; i < trees_length; i++) {
			if (cur_items[i] != NULL &&
				(error = git_iterator_advance((const git_index_entry **)&items[i],
				iterators[i])) < 0)
				goto done;
		}
	}
	
done:
	for (i = 0; i < trees_length; i++)
		git_iterator_free(iterators[i]);
	
	git__free(iterators);
	git__free(items);
	git__free(cur_items);
	
	return error;
}

/**
 * Three-way tree differencing
 */

typedef enum {
	INDEX_ANCESTOR = 0,
	INDEX_OURS = 1,
	INDEX_THEIRS = 2
} diff_tree_threeway_index;

struct diff_tree_threeway_data {
	git_diff_tree_list *diff_tree;
	
	const char *df_path;
	const char *prev_path;
	git_diff_tree_delta *prev_delta_tree;
};

static git_diff_tree_list *diff_tree__list_alloc(git_repository *repo)
{
	git_diff_tree_list *diff_tree =
		git__calloc(1, sizeof(git_diff_tree_list));
	
	if (diff_tree == NULL)
		return NULL;
	
	diff_tree->repo = repo;
	
	if (git_vector_init(&diff_tree->deltas, 0, git_diff_delta__cmp) < 0 ||
		git_pool_init(&diff_tree->pool, 1, 0) < 0)
		return NULL;
	
	return diff_tree;
}

GIT_INLINE(const char *) diff_tree__path(const git_diff_tree_delta *delta_tree)
{
	if (GIT_DIFF_TREE_FILE_EXISTS(delta_tree->ancestor))
		return delta_tree->ancestor.file.path;
	else if (GIT_DIFF_TREE_FILE_EXISTS(delta_tree->ours))
		return delta_tree->ours.file.path;
	else if (GIT_DIFF_TREE_FILE_EXISTS(delta_tree->theirs))
		return delta_tree->theirs.file.path;
	
	return NULL;
}

GIT_INLINE(bool) diff_tree__delta_added_or_modified(
	const git_diff_tree_delta *delta_tree)
{
	if (delta_tree->ours.status == GIT_DELTA_ADDED ||
		delta_tree->ours.status == GIT_DELTA_MODIFIED ||
		delta_tree->theirs.status == GIT_DELTA_ADDED ||
		delta_tree->theirs.status == GIT_DELTA_MODIFIED)
		return true;
		
	return false;
}

GIT_INLINE(bool) path_is_prefixed(const char *parent, const char *child)
{
	size_t child_len = strlen(child);
	size_t parent_len = strlen(parent);
	
	if (child_len < parent_len ||
		strncmp(parent, child, parent_len) != 0)
		return 0;

	return (child[parent_len] == '/');
}

GIT_INLINE(int) diff_tree__compute_df_conflict(
	struct diff_tree_threeway_data *threeway_data,
	git_diff_tree_delta *delta_tree)
{
	const char *cur_path = diff_tree__path(delta_tree);
	
	/* Determine if this is a D/F conflict or the child of one */
	if (threeway_data->df_path &&
		path_is_prefixed(threeway_data->df_path, cur_path))
		delta_tree->df_conflict = GIT_DIFF_TREE_DF_CHILD;
	else if(threeway_data->df_path)
		threeway_data->df_path = NULL;
	else if (threeway_data->prev_path &&
		diff_tree__delta_added_or_modified(threeway_data->prev_delta_tree) &&
		diff_tree__delta_added_or_modified(delta_tree) &&
		path_is_prefixed(threeway_data->prev_path, cur_path)) {
		delta_tree->df_conflict = GIT_DIFF_TREE_DF_CHILD;
		
		threeway_data->prev_delta_tree->df_conflict = GIT_DIFF_TREE_DF_DIRECTORY_FILE;
		threeway_data->df_path = threeway_data->prev_path;
	}

	threeway_data->prev_path = cur_path;
	threeway_data->prev_delta_tree = delta_tree;
	
	return 0;
}

GIT_INLINE(int) diff_tree__compute_conflict(
	git_diff_tree_delta *delta_tree)
{
	if (delta_tree->ours.status == GIT_DELTA_ADDED &&
		delta_tree->theirs.status == GIT_DELTA_ADDED)
		delta_tree->conflict = GIT_DIFF_TREE_CONFLICT_BOTH_ADDED;
	else if (delta_tree->ours.status == GIT_DELTA_MODIFIED &&
		delta_tree->theirs.status == GIT_DELTA_MODIFIED)
		delta_tree->conflict = GIT_DIFF_TREE_CONFLICT_BOTH_MODIFIED;
	else if (delta_tree->ours.status == GIT_DELTA_DELETED &&
		delta_tree->theirs.status == GIT_DELTA_DELETED)
		delta_tree->conflict = GIT_DIFF_TREE_CONFLICT_BOTH_DELETED;
	else if (delta_tree->ours.status == GIT_DELTA_MODIFIED &&
		delta_tree->theirs.status == GIT_DELTA_DELETED)
		delta_tree->conflict = GIT_DIFF_TREE_CONFLICT_MODIFY_DELETE;
	else if (delta_tree->ours.status == GIT_DELTA_DELETED &&
		delta_tree->theirs.status == GIT_DELTA_MODIFIED)
		delta_tree->conflict = GIT_DIFF_TREE_CONFLICT_MODIFY_DELETE;
	else
		delta_tree->conflict = GIT_DIFF_TREE_CONFLICT_NONE;

	return 0;
}

static git_diff_tree_delta *diff_tree__delta_from_entries(
	struct diff_tree_threeway_data *threeway_data,
	const git_index_entry **entries)
{
	git_diff_tree_delta *delta_tree;
	git_diff_tree_entry *tree_entries[3];
	size_t i;
	
	if ((delta_tree = git_pool_malloc(&threeway_data->diff_tree->pool, sizeof(git_diff_tree_delta))) == NULL)
		return NULL;
	
	tree_entries[INDEX_ANCESTOR] = &delta_tree->ancestor;
	tree_entries[INDEX_OURS] = &delta_tree->ours;
	tree_entries[INDEX_THEIRS] = &delta_tree->theirs;
	
	for (i = 0; i < 3; i++) {
		if (entries[i] == NULL)
			continue;

		if ((tree_entries[i]->file.path = git_pool_strdup(&threeway_data->diff_tree->pool, entries[i]->path)) == NULL)
			return NULL;
		
		git_oid_cpy(&tree_entries[i]->file.oid, &entries[i]->oid);
		tree_entries[i]->file.size = entries[i]->file_size;
		tree_entries[i]->file.mode = entries[i]->mode;
		tree_entries[i]->file.flags |= GIT_DIFF_FLAG_VALID_OID;
	}
	
	for (i = 1; i < 3; i++) {
		if (entries[INDEX_ANCESTOR] == NULL && entries[i] == NULL)
			continue;
		
		if (entries[INDEX_ANCESTOR] == NULL && entries[i] != NULL)
			tree_entries[i]->status |= GIT_DELTA_ADDED;
		else if (entries[INDEX_ANCESTOR] != NULL && entries[i] == NULL)
			tree_entries[i]->status |= GIT_DELTA_DELETED;
		else if (S_ISDIR(entries[INDEX_ANCESTOR]->mode) ^ S_ISDIR(entries[i]->mode))
			tree_entries[i]->status |= GIT_DELTA_TYPECHANGE;
		else if(S_ISLNK(entries[INDEX_ANCESTOR]->mode) ^ S_ISLNK(entries[i]->mode))
			tree_entries[i]->status |= GIT_DELTA_TYPECHANGE;
		else if (git_oid_cmp(&entries[INDEX_ANCESTOR]->oid, &entries[i]->oid) ||
			entries[INDEX_ANCESTOR]->mode != entries[i]->mode)
			tree_entries[i]->status |= GIT_DELTA_MODIFIED;
	}
	
	return delta_tree;
}

static int diff_tree__create_delta(const git_index_entry **tree_items, void *payload)
{
	struct diff_tree_threeway_data *threeway_data = payload;
	git_diff_tree_delta *delta_tree;
	
	assert(tree_items && threeway_data);
	
	if ((delta_tree = diff_tree__delta_from_entries(threeway_data, tree_items)) == NULL ||
		diff_tree__compute_conflict(delta_tree) < 0 ||
		diff_tree__compute_df_conflict(threeway_data, delta_tree) < 0 ||
		git_vector_insert(&threeway_data->diff_tree->deltas, delta_tree) < 0)
		return -1;
	
	return 0;
}

int git_diff_tree(git_diff_tree_list **out,
	git_repository *repo,
	git_tree *ancestor_tree,
	git_tree *our_tree,
	git_tree *their_tree,
	uint32_t flags)
{
	struct diff_tree_threeway_data threeway_data;
	git_diff_tree_list *diff_tree;
	git_tree *trees[3];
	int error = 0;
	
	assert(out && repo && ancestor_tree && our_tree && their_tree);
	
	*out = NULL;

	diff_tree = diff_tree__list_alloc(repo);
	GITERR_CHECK_ALLOC(diff_tree);
	
	memset(&threeway_data, 0x0, sizeof(struct diff_tree_threeway_data));
	threeway_data.diff_tree = diff_tree;
	
	trees[INDEX_ANCESTOR] = ancestor_tree;
	trees[INDEX_OURS] = our_tree;
	trees[INDEX_THEIRS] = their_tree;
	
	if ((error = git_diff_tree_many(repo, trees, 3, flags, diff_tree__create_delta, &threeway_data)) < 0)
		git_diff_tree_list_free(diff_tree);
	
	if (error >= 0)
		*out = diff_tree;

	return error;
}

int git_diff_tree_foreach(
	git_diff_tree_list *diff_tree,
	git_diff_tree_delta_cb callback,
	void *payload)
{
	git_diff_tree_delta *delta;
	size_t i;
	int error = 0;
	
	assert (diff_tree && callback);
	
	git_vector_foreach(&diff_tree->deltas, i, delta) {
		if (callback(delta, payload) != 0) {
			error = GIT_EUSER;
			break;
		}
	}
	
	return error;
}

void git_diff_tree_list_free(git_diff_tree_list *diff_tree)
{
	if (!diff_tree)
		return;
	
	git_vector_free(&diff_tree->deltas);
	git_pool_clear(&diff_tree->pool);
	git__free(diff_tree);
}
