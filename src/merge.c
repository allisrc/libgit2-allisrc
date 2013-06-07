/*
 * Copyright (C) the libgit2 contributors. All rights reserved.
 *
 * This file is part of libgit2, distributed under the GNU GPL v2 with
 * a Linking Exception. For full terms see the included COPYING file.
 */

#include "common.h"
#include "posix.h"
#include "buffer.h"
#include "repository.h"
#include "revwalk.h"
#include "commit_list.h"
#include "merge.h"
#include "path.h"
#include "refs.h"
#include "object.h"
#include "iterator.h"
#include "refs.h"
#include "diff.h"
#include "diff_tree.h"
#include "checkout.h"
#include "tree.h"
#include "merge_file.h"
#include "blob.h"
#include "hashsig.h"
#include "oid.h"

#include "git2/types.h"
#include "git2/repository.h"
#include "git2/object.h"
#include "git2/commit.h"
#include "git2/merge.h"
#include "git2/refs.h"
#include "git2/reset.h"
#include "git2/checkout.h"
#include "git2/signature.h"
#include "git2/config.h"
#include "git2/tree.h"
#include "git2/sys/index.h"

#define GIT_MERGE_INDEX_ENTRY_EXISTS(X)	((X).mode != 0)

typedef enum {
	TREE_IDX_ANCESTOR = 0,
	TREE_IDX_OURS = 1,
	TREE_IDX_THEIRS = 2
} merge_tree_index_t;

/* Tracks D/F conflicts */
struct merge_diff_df_data {
	const char *df_path;
	const char *prev_path;
	git_merge_diff *prev_conflict;
};


/* Merge base computation */

int git_merge_base_many(git_oid *out, git_repository *repo, const git_oid input_array[], size_t length)
{
	git_revwalk *walk;
	git_vector list;
	git_commit_list *result = NULL;
	int error = -1;
	unsigned int i;
	git_commit_list_node *commit;

	assert(out && repo && input_array);

	if (length < 2) {
		giterr_set(GITERR_INVALID, "At least two commits are required to find an ancestor. Provided 'length' was %u.", length);
		return -1;
	}

	if (git_vector_init(&list, length - 1, NULL) < 0)
		return -1;

	if (git_revwalk_new(&walk, repo) < 0)
		goto cleanup;

	for (i = 1; i < length; i++) {
		commit = git_revwalk__commit_lookup(walk, &input_array[i]);
		if (commit == NULL)
			goto cleanup;

		git_vector_insert(&list, commit);
	}

	commit = git_revwalk__commit_lookup(walk, &input_array[0]);
	if (commit == NULL)
		goto cleanup;

	if (git_merge__bases_many(&result, walk, commit, &list) < 0)
		goto cleanup;

	if (!result) {
		giterr_set(GITERR_MERGE, "No merge base found");
		error = GIT_ENOTFOUND;
		goto cleanup;
	}

	git_oid_cpy(out, &result->item->oid);

	error = 0;

cleanup:
	git_commit_list_free(&result);
	git_revwalk_free(walk);
	git_vector_free(&list);
	return error;
}

int git_merge_base(git_oid *out, git_repository *repo, const git_oid *one, const git_oid *two)
{
	git_revwalk *walk;
	git_vector list;
	git_commit_list *result = NULL;
	git_commit_list_node *commit;
	void *contents[1];

	if (git_revwalk_new(&walk, repo) < 0)
		return -1;

	commit = git_revwalk__commit_lookup(walk, two);
	if (commit == NULL)
		goto on_error;

	/* This is just one value, so we can do it on the stack */
	memset(&list, 0x0, sizeof(git_vector));
	contents[0] = commit;
	list.length = 1;
	list.contents = contents;

	commit = git_revwalk__commit_lookup(walk, one);
	if (commit == NULL)
		goto on_error;

	if (git_merge__bases_many(&result, walk, commit, &list) < 0)
		goto on_error;

	if (!result) {
		git_revwalk_free(walk);
		giterr_set(GITERR_MERGE, "No merge base found");
		return GIT_ENOTFOUND;
	}

	git_oid_cpy(out, &result->item->oid);
	git_commit_list_free(&result);
	git_revwalk_free(walk);

	return 0;

on_error:
	git_revwalk_free(walk);
	return -1;
}

static int interesting(git_pqueue *list)
{
	unsigned int i;
	/* element 0 isn't used - we need to start at 1 */
	for (i = 1; i < list->size; i++) {
		git_commit_list_node *commit = list->d[i];
		if ((commit->flags & STALE) == 0)
			return 1;
	}

	return 0;
}

int git_merge__bases_many(git_commit_list **out, git_revwalk *walk, git_commit_list_node *one, git_vector *twos)
{
	int error;
	unsigned int i;
	git_commit_list_node *two;
	git_commit_list *result = NULL, *tmp = NULL;
	git_pqueue list;

	/* if the commit is repeated, we have a our merge base already */
	git_vector_foreach(twos, i, two) {
		if (one == two)
			return git_commit_list_insert(one, out) ? 0 : -1;
	}

	if (git_pqueue_init(&list, twos->length * 2, git_commit_list_time_cmp) < 0)
		return -1;

	if (git_commit_list_parse(walk, one) < 0)
		return -1;

	one->flags |= PARENT1;
	if (git_pqueue_insert(&list, one) < 0)
		return -1;

	git_vector_foreach(twos, i, two) {
		git_commit_list_parse(walk, two);
		two->flags |= PARENT2;
		if (git_pqueue_insert(&list, two) < 0)
			return -1;
	}

	/* as long as there are non-STALE commits */
	while (interesting(&list)) {
		git_commit_list_node *commit;
		int flags;

		commit = git_pqueue_pop(&list);

		flags = commit->flags & (PARENT1 | PARENT2 | STALE);
		if (flags == (PARENT1 | PARENT2)) {
			if (!(commit->flags & RESULT)) {
				commit->flags |= RESULT;
				if (git_commit_list_insert(commit, &result) == NULL)
					return -1;
			}
			/* we mark the parents of a merge stale */
			flags |= STALE;
		}

		for (i = 0; i < commit->out_degree; i++) {
			git_commit_list_node *p = commit->parents[i];
			if ((p->flags & flags) == flags)
				continue;

			if ((error = git_commit_list_parse(walk, p)) < 0)
				return error;

			p->flags |= flags;
			if (git_pqueue_insert(&list, p) < 0)
				return -1;
		}
	}

	git_pqueue_free(&list);

	/* filter out any stale commits in the results */
	tmp = result;
	result = NULL;

	while (tmp) {
		struct git_commit_list *next = tmp->next;
		if (!(tmp->item->flags & STALE))
			if (git_commit_list_insert_by_date(tmp->item, &result) == NULL)
				return -1;

		git__free(tmp);
		tmp = next;
	}

	*out = result;
	return 0;
}

int git_repository_mergehead_foreach(git_repository *repo,
	git_repository_mergehead_foreach_cb cb,
	void *payload)
{
	git_buf merge_head_path = GIT_BUF_INIT, merge_head_file = GIT_BUF_INIT;
	char *buffer, *line;
	size_t line_num = 1;
	git_oid oid;
	int error = 0;

	assert(repo && cb);

	if ((error = git_buf_joinpath(&merge_head_path, repo->path_repository,
		GIT_MERGE_HEAD_FILE)) < 0)
		return error;

	if ((error = git_futils_readbuffer(&merge_head_file,
		git_buf_cstr(&merge_head_path))) < 0)
		goto cleanup;

	buffer = merge_head_file.ptr;

	while ((line = git__strsep(&buffer, "\n")) != NULL) {
		if (strlen(line) != GIT_OID_HEXSZ) {
			giterr_set(GITERR_INVALID, "Unable to parse OID - invalid length");
			error = -1;
			goto cleanup;
		}

		if ((error = git_oid_fromstr(&oid, line)) < 0)
			goto cleanup;

		if (cb(&oid, payload) < 0) {
			error = GIT_EUSER;
			goto cleanup;
		}

		++line_num;
	}

	if (*buffer) {
		giterr_set(GITERR_MERGE, "No EOL at line %d", line_num);
		error = -1;
		goto cleanup;
	}

cleanup:
	git_buf_free(&merge_head_path);
	git_buf_free(&merge_head_file);

	return error;
}

GIT_INLINE(int) index_entry_cmp(const git_index_entry *a, const git_index_entry *b)
{
	int value = 0;

	if (a->path == NULL)
		return (b->path == NULL) ? 0 : 1;

	if ((value = a->mode - b->mode) == 0 &&
		(value = git_oid__cmp(&a->oid, &b->oid)) == 0)
		value = strcmp(a->path, b->path);

	return value;
}

GIT_INLINE(int) merge_file_cmp(const git_diff_file *a, const git_diff_file *b)
{
	int value = 0;
    
    if (a->path == NULL)
        return (b->path == NULL) ? 0 : 1;
    
	if ((value = a->mode - b->mode) == 0 &&
		(value = git_oid_cmp(&a->oid, &b->oid)) == 0)
		value = strcmp(a->path, b->path);

	return value;
}

/* Xdiff (automerge/diff3) computation */

typedef struct {
	bool automergeable;
	
	const char *path;
	int mode;

	unsigned char *data;
	size_t len;
} merge_filediff_result;

#define MERGE_FILEDIFF_RESULT_INIT		{0}

static const char *merge_filediff_best_path(const git_diff_tree_delta *delta)
{
	if (!GIT_DIFF_TREE_FILE_EXISTS(delta->ancestor)) {
		if (strcmp(delta->ours.file.path, delta->theirs.file.path) == 0)
			return delta->ours.file.path;
		
		return NULL;
	}
	
	if (strcmp(delta->ancestor.file.path, delta->ours.file.path) == 0)
		return delta->theirs.file.path;
	else if(strcmp(delta->ancestor.file.path, delta->theirs.file.path) == 0)
		return delta->ours.file.path;
	
	return NULL;
}

static int merge_filediff_best_mode(const git_diff_tree_delta *delta)
{
	/*
	 * If ancestor didn't exist and either ours or theirs is executable,
	 * assume executable.  Otherwise, if any mode changed from the ancestor,
	 * use that one.
	 */
	if (!GIT_DIFF_TREE_FILE_EXISTS(delta->ancestor)) {
		if (delta->ours.file.mode == GIT_FILEMODE_BLOB_EXECUTABLE ||
			delta->theirs.file.mode == GIT_FILEMODE_BLOB_EXECUTABLE)
			return GIT_FILEMODE_BLOB_EXECUTABLE;
		
		return GIT_FILEMODE_BLOB;
	}
	
	if (delta->ancestor.file.mode == delta->ours.file.mode)
		return delta->theirs.file.mode;
	else if(delta->ancestor.file.mode == delta->theirs.file.mode)
		return delta->ours.file.mode;
	
	return 0;
}

static char *merge_filediff_entry_name(const git_merge_head_old *merge_head,
	const git_diff_tree_entry *entry,
	bool rename)
{
	char oid_str[GIT_OID_HEXSZ];
	git_buf name = GIT_BUF_INIT;
	
	assert(merge_head && entry);

	if (merge_head->branch_name)
		git_buf_puts(&name, merge_head->branch_name);
	else {
		git_oid_fmt(oid_str, &merge_head->oid);
		git_buf_put(&name, oid_str, GIT_OID_HEXSZ);
	}
	
	if (rename) {
		git_buf_putc(&name, ':');
		git_buf_puts(&name, entry->file.path);
	}
	
	return name.ptr;
}

static int merge_filediff_entry_names(char **our_path,
	char **their_path,
	const git_merge_head *merge_heads[],
	const git_diff_tree_delta *delta)
{
	bool rename;

	*our_path = NULL;
	*their_path = NULL;

	if (!merge_heads)
		return 0;

	/*
	 * If all the paths are identical, decorate the diff3 file with the branch
	 * names.  Otherwise, use branch_name:path
	 */
	rename = GIT_DIFF_TREE_FILE_EXISTS(delta->ours) &&
		GIT_DIFF_TREE_FILE_EXISTS(delta->theirs) &&
		strcmp(delta->ours.file.path, delta->theirs.file.path) != 0;

	if (GIT_DIFF_TREE_FILE_EXISTS(delta->ours) &&
		(*our_path = merge_filediff_entry_name(merge_heads[1], &delta->ours, rename)) == NULL)
		return -1;

	if (GIT_DIFF_TREE_FILE_EXISTS(delta->theirs) &&
		(*their_path = merge_filediff_entry_name(merge_heads[2], &delta->theirs, rename)) == NULL)
		return -1;

	return 0;
}

static int merge_filediff(
	merge_filediff_result *result,
	git_odb *odb,
	const git_merge_head_old *merge_heads[],
	const git_diff_tree_delta *delta,
	unsigned int flags)
{
	git_odb_object *ancestor_odb = NULL, *our_odb = NULL, *their_odb = NULL;
	char *our_name = NULL, *their_name = NULL;
	mmfile_t ancestor_mmfile, our_mmfile, their_mmfile;
	xmparam_t xmparam;
	mmbuffer_t mmbuffer;
	int xdl_result;
	int error = 0;

	assert(result && odb && delta);
	
	memset(result, 0x0, sizeof(merge_filediff_result));
	
	/* Can't automerge unless ours and theirs exist */
	if (!GIT_DIFF_TREE_FILE_EXISTS(delta->ours) ||
		!GIT_DIFF_TREE_FILE_EXISTS(delta->theirs))
		return 0;

	/* Reject filename collisions */
	result->path = merge_filediff_best_path(delta);
	result->mode = merge_filediff_best_mode(delta);

	if (result->path == NULL || result->mode == 0)
		return 0;
	
	memset(&xmparam, 0x0, sizeof(xmparam_t));
	
	if (merge_heads &&
		(error = merge_filediff_entry_names(&our_name, &their_name, merge_heads, delta)) < 0)
		return -1;

	/* Ancestor isn't decorated in diff3, use NULL. */
	xmparam.ancestor = NULL;
	xmparam.file1 = our_name ? our_name : delta->ours.file.path;
	xmparam.file2 = their_name ? their_name : delta->theirs.file.path;

	if (GIT_DIFF_TREE_FILE_EXISTS(delta->ancestor)) {
		if ((error = git_odb_read(&ancestor_odb, odb, &delta->ancestor.file.oid)) < 0)
			goto done;
		
		ancestor_mmfile.size = git_odb_object_size(ancestor_odb);
		ancestor_mmfile.ptr = (char *)git_odb_object_data(ancestor_odb);
	} else
		memset(&ancestor_mmfile, 0x0, sizeof(mmfile_t));

	if (GIT_DIFF_TREE_FILE_EXISTS(delta->ours)) {
		if ((error = git_odb_read(&our_odb, odb, &delta->ours.file.oid)) < 0)
			goto done;
		
		our_mmfile.size = git_odb_object_size(our_odb);
		our_mmfile.ptr = (char *)git_odb_object_data(our_odb);
	} else
		memset(&our_mmfile, 0x0, sizeof(mmfile_t));
	
	if (GIT_DIFF_TREE_FILE_EXISTS(delta->theirs)) {
		if ((error = git_odb_read(&their_odb, odb, &delta->theirs.file.oid)) < 0)
			goto done;
		
		their_mmfile.size = git_odb_object_size(their_odb);
		their_mmfile.ptr = (char *)git_odb_object_data(their_odb);
	} else
		memset(&their_mmfile, 0x0, sizeof(mmfile_t));
	
	if (flags & GIT_MERGE_RESOLVE_FAVOR_OURS)
		xmparam.favor = XDL_MERGE_FAVOR_OURS;

	if (flags & GIT_MERGE_RESOLVE_FAVOR_THEIRS)
		xmparam.favor = XDL_MERGE_FAVOR_THEIRS;

	if ((xdl_result = xdl_merge(&ancestor_mmfile, &our_mmfile, &their_mmfile, &xmparam, &mmbuffer)) < 0) {
		giterr_set(GITERR_MERGE, "Failed to perform automerge.");
		error = -1;
		goto done;
	}
	
	result->automergeable = (xdl_result == 0);
	result->data = (unsigned char *)mmbuffer.ptr;
	result->len = mmbuffer.size;
	
done:
	git__free(our_name);
	git__free(their_name);

	git_odb_object_free(ancestor_odb);
	git_odb_object_free(our_odb);
	git_odb_object_free(their_odb);

	return error;
}

static void merge_filediff_result_free(merge_filediff_result *result)
{
	/* xdiff uses malloc() not git_malloc, so we use free(), not git_free() */
	if (result->data != NULL)
		free(result->data);
}

/* Conflict resolution */

static int merge_file_index_remove(git_index *index, const git_diff_tree_delta *delta)
{
	if (!GIT_DIFF_TREE_FILE_EXISTS(delta->ours))
		return 0;

	return git_index_remove(index, delta->ours.file.path, 0);
}

static int merge_file_apply(git_index *index,
	const git_diff_tree_delta *delta,
	const git_diff_tree_entry *entry)
{
	git_index_entry index_entry;
	int error = 0;
	
	assert (index && entry);
	
	if (!GIT_DIFF_TREE_FILE_EXISTS(*entry))
		error = merge_file_index_remove(index, delta);
	else {
		memset(&index_entry, 0x0, sizeof(git_index_entry));
		
		index_entry.path = (char *)entry->file.path;
		index_entry.mode = entry->file.mode;
		index_entry.file_size = entry->file.size;
		git_oid_cpy(&index_entry.oid, &entry->file.oid);

		error = git_index_add(index, &index_entry);
	}
	
	return error;
}

static int merge_mark_conflict_resolved(git_index *index, const git_diff_tree_delta *delta)
{
    const char *path;
    assert(index && delta);
	
	if (GIT_DIFF_TREE_FILE_EXISTS(delta->ancestor))
		path = delta->ancestor.file.path;
	else if (GIT_DIFF_TREE_FILE_EXISTS(delta->ours))
		path = delta->ours.file.path;
	else if (GIT_DIFF_TREE_FILE_EXISTS(delta->theirs))
		path = delta->theirs.file.path;
    else
        return -1;
	
	return git_index_reuc_add(index, path,
		delta->ancestor.file.mode, &delta->ancestor.file.oid,
		delta->ours.file.mode, &delta->ours.file.oid,
		delta->theirs.file.mode, &delta->theirs.file.oid);
}

static int merge_mark_conflict_unresolved(git_index *index, const git_diff_tree_delta *delta)
{
	bool ancestor_exists = 0, ours_exists = 0, theirs_exists = 0;
    git_index_entry ancestor_entry, our_entry, their_entry;
    int error = 0;

    assert(index && delta);
	
	if ((ancestor_exists = GIT_DIFF_TREE_FILE_EXISTS(delta->ancestor))) {
		memset(&ancestor_entry, 0x0, sizeof(git_index_entry));
		ancestor_entry.path = (char *)delta->ancestor.file.path;
		ancestor_entry.mode = delta->ancestor.file.mode;
		git_oid_cpy(&ancestor_entry.oid, &delta->ancestor.file.oid);
	}
	
	if ((ours_exists = GIT_DIFF_TREE_FILE_EXISTS(delta->ours))) {
		memset(&our_entry, 0x0, sizeof(git_index_entry));
		our_entry.path = (char *)delta->ours.file.path;
		our_entry.mode = delta->ours.file.mode;
		git_oid_cpy(&our_entry.oid, &delta->ours.file.oid);
	}
	
	if ((theirs_exists = GIT_DIFF_TREE_FILE_EXISTS(delta->theirs))) {
		memset(&their_entry, 0x0, sizeof(git_index_entry));
		their_entry.path = (char *)delta->theirs.file.path;
		their_entry.mode = delta->theirs.file.mode;
		git_oid_cpy(&their_entry.oid, &delta->theirs.file.oid);
	}

	if ((error = merge_file_index_remove(index, delta)) >= 0)
		error = git_index_conflict_add(index,
			ancestor_exists ? &ancestor_entry : NULL,
			ours_exists ? &our_entry : NULL,
			theirs_exists ? &their_entry : NULL);
	
	return error;
}

// duplicate merge_conflict_resolve_trivial function,
// this is from the old repo
static int merge_conflict_resolve_trivial_old(
	int *resolved,
	git_repository *repo,
	git_index *index,
	const git_diff_tree_delta *delta,
	unsigned int resolve_flags)
{
    int ancestor_empty, ours_empty, theirs_empty;
    int ours_changed, theirs_changed, ours_theirs_differ;
	git_diff_tree_entry const *result = NULL;
    int error = 0;
    
	GIT_UNUSED(resolve_flags);

    assert(resolved && repo && index && delta);
    
    *resolved = 0;
    
	/* TODO: (optionally) reject children of d/f conflicts */
	
	if (delta->df_conflict == GIT_DIFF_TREE_DF_DIRECTORY_FILE)
		return 0;

	ancestor_empty = !GIT_DIFF_TREE_FILE_EXISTS(delta->ancestor);
	ours_empty = !GIT_DIFF_TREE_FILE_EXISTS(delta->ours);
	theirs_empty = !GIT_DIFF_TREE_FILE_EXISTS(delta->theirs);
	
	ours_changed = (delta->ours.status != GIT_DELTA_UNMODIFIED);
	theirs_changed = (delta->theirs.status != GIT_DELTA_UNMODIFIED);
	ours_theirs_differ = ours_changed && theirs_changed &&
		merge_file_cmp(&delta->ours.file, &delta->theirs.file);
    
    /*
     * Note: with only one ancestor, some cases are not distinct:
     *
     * 16: ancest:anc1/anc2, head:anc1, remote:anc2 = result:no merge
     * 3: ancest:(empty)^, head:head, remote:(empty) = result:no merge
     * 2: ancest:(empty)^, head:(empty), remote:remote = result:no merge
     *
     * Note that the two cases that take D/F conflicts into account
     * specifically do not need to be explicitly tested, as D/F conflicts
     * would fail the *empty* test:
     *
     * 3ALT: ancest:(empty)+, head:head, remote:*empty* = result:head
     * 2ALT: ancest:(empty)+, head:*empty*, remote:remote = result:remote
     *
     * Note that many of these cases need not be explicitly tested, as
     * they simply degrade to "all different" cases (eg, 11):
     *
     * 4: ancest:(empty)^, head:head, remote:remote = result:no merge
     * 7: ancest:ancest+, head:(empty), remote:remote = result:no merge
     * 9: ancest:ancest+, head:head, remote:(empty) = result:no merge
     * 11: ancest:ancest+, head:head, remote:remote = result:no merge
     */
    
    /* 5ALT: ancest:*, head:head, remote:head = result:head */
    if (ours_changed && !ours_empty && !ours_theirs_differ)
		result = &delta->ours;
    /* 6: ancest:ancest+, head:(empty), remote:(empty) = result:no merge */
    else if (ours_changed && ours_empty && theirs_empty)
        *resolved = 0;
    /* 8: ancest:ancest^, head:(empty), remote:ancest = result:no merge */
    else if (ours_empty && !theirs_changed)
        *resolved = 0;
    /* 10: ancest:ancest^, head:ancest, remote:(empty) = result:no merge */
    else if (!ours_changed && theirs_empty)
        *resolved = 0;
    /* 13: ancest:ancest+, head:head, remote:ancest = result:head */
    else if (ours_changed && !theirs_changed)
		result = &delta->ours;
    /* 14: ancest:ancest+, head:ancest, remote:remote = result:remote */
    else if (!ours_changed && theirs_changed)
		result = &delta->theirs;
    else
        *resolved = 0;

    if (result != NULL && (error = merge_file_apply(index, delta, result)) >= 0)
        *resolved = 1;
    
	/* Note: trivial resolution does not update the REUC. */
	
    return error;
}

static int merge_conflict_resolve_removed(
	int *resolved,
	git_repository *repo,
	git_index *index,
	const git_diff_tree_delta *delta,
	unsigned int resolve_flags)
{
    int ours_empty, theirs_empty;
    int ours_changed, theirs_changed;
	git_diff_tree_entry const *result = NULL;
    int error = 0;

	GIT_UNUSED(resolve_flags);

    assert(resolved && repo && index && delta);

    *resolved = 0;
	
	if (resolve_flags & GIT_MERGE_RESOLVE_NO_REMOVED)
		return 0;

	/* TODO: (optionally) reject children of d/f conflicts */

	if (delta->df_conflict == GIT_DIFF_TREE_DF_DIRECTORY_FILE)
		return 0;

	ours_empty = !GIT_DIFF_TREE_FILE_EXISTS(delta->ours);
	theirs_empty = !GIT_DIFF_TREE_FILE_EXISTS(delta->theirs);

	ours_changed = (delta->ours.status != GIT_DELTA_UNMODIFIED);
	theirs_changed = (delta->theirs.status != GIT_DELTA_UNMODIFIED);
    
    /* Handle some cases that are not "trivial" but are, well, trivial. */
    
	/* Removed in both */
    if (ours_changed && ours_empty && theirs_empty)
		result = &delta->ours;
	/* Removed in ours */
    else if (ours_empty && !theirs_changed)
		result = &delta->ours;
	/* Removed in theirs */
    else if (!ours_changed && theirs_empty)
		result = &delta->theirs;
    
	if (result != NULL &&
		(error = merge_file_apply(index, delta, result)) >= 0 &&
		(error = merge_mark_conflict_resolved(index, delta)) >= 0)
        *resolved = 1;

    return error;
}

static int merge_conflict_resolve_trivial(
	int *resolved,
	git_merge_diff_list *diff_list,
	const git_merge_diff *conflict)
{
	int ours_empty, theirs_empty;
	int ours_changed, theirs_changed, ours_theirs_differ;
	git_index_entry const *result = NULL;
	int error = 0;

	assert(resolved && diff_list && conflict);

	*resolved = 0;

	if (conflict->type == GIT_MERGE_DIFF_DIRECTORY_FILE ||
		conflict->type == GIT_MERGE_DIFF_RENAMED_ADDED)
		return 0;

	if (conflict->our_status == GIT_DELTA_RENAMED ||
		conflict->their_status == GIT_DELTA_RENAMED)
		return 0;

	ours_empty = !GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry);
	theirs_empty = !GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry);

	ours_changed = (conflict->our_status != GIT_DELTA_UNMODIFIED);
	theirs_changed = (conflict->their_status != GIT_DELTA_UNMODIFIED);
	ours_theirs_differ = ours_changed && theirs_changed &&
		index_entry_cmp(&conflict->our_entry, &conflict->their_entry);

	/*
	 * Note: with only one ancestor, some cases are not distinct:
	 *
	 * 16: ancest:anc1/anc2, head:anc1, remote:anc2 = result:no merge
	 * 3: ancest:(empty)^, head:head, remote:(empty) = result:no merge
	 * 2: ancest:(empty)^, head:(empty), remote:remote = result:no merge
	 *
	 * Note that the two cases that take D/F conflicts into account
	 * specifically do not need to be explicitly tested, as D/F conflicts
	 * would fail the *empty* test:
	 *
	 * 3ALT: ancest:(empty)+, head:head, remote:*empty* = result:head
	 * 2ALT: ancest:(empty)+, head:*empty*, remote:remote = result:remote
	 *
	 * Note that many of these cases need not be explicitly tested, as
	 * they simply degrade to "all different" cases (eg, 11):
	 *
	 * 4: ancest:(empty)^, head:head, remote:remote = result:no merge
	 * 7: ancest:ancest+, head:(empty), remote:remote = result:no merge
	 * 9: ancest:ancest+, head:head, remote:(empty) = result:no merge
	 * 11: ancest:ancest+, head:head, remote:remote = result:no merge
	 */

	/* 5ALT: ancest:*, head:head, remote:head = result:head */
	if (ours_changed && !ours_empty && !ours_theirs_differ)
		result = &conflict->our_entry;
	/* 6: ancest:ancest+, head:(empty), remote:(empty) = result:no merge */
	else if (ours_changed && ours_empty && theirs_empty)
		*resolved = 0;
	/* 8: ancest:ancest^, head:(empty), remote:ancest = result:no merge */
	else if (ours_empty && !theirs_changed)
		*resolved = 0;
	/* 10: ancest:ancest^, head:ancest, remote:(empty) = result:no merge */
	else if (!ours_changed && theirs_empty)
		*resolved = 0;
	/* 13: ancest:ancest+, head:head, remote:ancest = result:head */
	else if (ours_changed && !theirs_changed)
		result = &conflict->our_entry;
	/* 14: ancest:ancest+, head:ancest, remote:remote = result:remote */
	else if (!ours_changed && theirs_changed)
		result = &conflict->their_entry;
	else
		*resolved = 0;

	if (result != NULL &&
		GIT_MERGE_INDEX_ENTRY_EXISTS(*result) &&
		(error = git_vector_insert(&diff_list->staged, (void *)result)) >= 0)
		*resolved = 1;

	/* Note: trivial resolution does not update the REUC. */

	return error;
}

static int merge_conflict_resolve_one_removed(
	int *resolved,
	git_merge_diff_list *diff_list,
	const git_merge_diff *conflict)
{
	int ours_empty, theirs_empty;
	int ours_changed, theirs_changed;
	int error = 0;

	assert(resolved && diff_list && conflict);

	*resolved = 0;

	if (conflict->type == GIT_MERGE_DIFF_DIRECTORY_FILE ||
		conflict->type == GIT_MERGE_DIFF_RENAMED_ADDED)
		return 0;

	ours_empty = !GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry);
	theirs_empty = !GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry);

	ours_changed = (conflict->our_status != GIT_DELTA_UNMODIFIED);
	theirs_changed = (conflict->their_status != GIT_DELTA_UNMODIFIED);

	/* Removed in both */
	if (ours_changed && ours_empty && theirs_empty)
		*resolved = 1;
	/* Removed in ours */
	else if (ours_empty && !theirs_changed)
		*resolved = 1;
	/* Removed in theirs */
	else if (!ours_changed && theirs_empty)
		*resolved = 1;

	if (*resolved)
		git_vector_insert(&diff_list->resolved, (git_merge_diff *)conflict);

	return error;
}


static int merge_conflict_resolve_one_renamed(
	int *resolved,
	git_merge_diff_list *diff_list,
	const git_merge_diff *conflict)
{
	int ours_renamed, theirs_renamed;
	int ours_changed, theirs_changed;
	git_index_entry *merged;
	int error = 0;

	assert(resolved && diff_list && conflict);

	*resolved = 0;

	if (!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry) ||
		!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry))
		return 0;

	ours_renamed = (conflict->our_status == GIT_DELTA_RENAMED);
	theirs_renamed = (conflict->their_status == GIT_DELTA_RENAMED);

	if (!ours_renamed && !theirs_renamed)
		return 0;

	/* Reject one file in a 2->1 conflict */
	if (conflict->type == GIT_MERGE_DIFF_BOTH_RENAMED_2_TO_1 ||
		conflict->type == GIT_MERGE_DIFF_BOTH_RENAMED_1_TO_2 ||
		conflict->type == GIT_MERGE_DIFF_RENAMED_ADDED)
		return 0;

	ours_changed = (git_oid__cmp(&conflict->ancestor_entry.oid, &conflict->our_entry.oid) != 0);
	theirs_changed = (git_oid__cmp(&conflict->ancestor_entry.oid, &conflict->their_entry.oid) != 0);

	/* if both are modified (and not to a common target) require a merge */
	if (ours_changed && theirs_changed &&
		git_oid__cmp(&conflict->our_entry.oid, &conflict->their_entry.oid) != 0)
		return 0;

	if ((merged = git_pool_malloc(&diff_list->pool, sizeof(git_index_entry))) == NULL)
		return -1;

	if (ours_changed)
		memcpy(merged, &conflict->our_entry, sizeof(git_index_entry));
	else
		memcpy(merged, &conflict->their_entry, sizeof(git_index_entry));

	if (ours_renamed)
		merged->path = conflict->our_entry.path;
	else
		merged->path = conflict->their_entry.path;

	*resolved = 1;

	git_vector_insert(&diff_list->staged, merged);
	git_vector_insert(&diff_list->resolved, (git_merge_diff *)conflict);

	return error;
}

// duplicate merge_conflict_resolve_automerge function,
// this one is from the old repo
static int merge_conflict_resolve_automerge_old(
	int *resolved,
	git_repository *repo,
	git_index *index,
	const git_diff_tree_delta *delta,
	unsigned int resolve_flags)
{
	git_odb *odb = NULL;
	merge_filediff_result result = MERGE_FILEDIFF_RESULT_INIT;
	git_index_entry index_entry;
	git_oid automerge_oid;
	int error = 0;
	
	assert(resolved && repo && index && delta);
	
	*resolved = 0;
	
	if (resolve_flags & GIT_MERGE_RESOLVE_NO_AUTOMERGE)
		return 0;

	/* Reject D/F conflicts */
	if (delta->df_conflict == GIT_DIFF_TREE_DF_DIRECTORY_FILE)
		return 0;

	/* Reject link/file conflicts. */
	if ((S_ISLNK(delta->ancestor.file.mode) ^ S_ISLNK(delta->ours.file.mode)) ||
		(S_ISLNK(delta->ancestor.file.mode) ^ S_ISLNK(delta->theirs.file.mode)))
		return 0;

	/* TODO: reject children of d/f conflicts */

	/* TODO: reject name conflicts */

	if ((error = git_repository_odb(&odb, repo)) < 0)
		goto done;

	if ((error = merge_filediff(&result, odb, NULL, delta, resolve_flags)) < 0 ||
		!result.automergeable ||
		(error = git_odb_write(&automerge_oid, odb, result.data, result.len, GIT_OBJ_BLOB)) < 0)
		goto done;
	
	memset(&index_entry, 0x0, sizeof(git_index_entry));

	index_entry.path = (char *)result.path;
	index_entry.file_size = result.len;
	index_entry.mode = result.mode;
	git_oid_cpy(&index_entry.oid, &automerge_oid);
	
	if ((error = git_index_add(index, &index_entry)) >= 0 &&
		(error = merge_mark_conflict_resolved(index, delta)) >= 0)
		*resolved = 1;

done:
	merge_filediff_result_free(&result);
	git_odb_free(odb);
	
	return error;
}

static int merge_conflict_resolve_automerge(
	int *resolved,
	git_merge_diff_list *diff_list,
	const git_merge_diff *conflict,
	unsigned int automerge_flags)
{
	git_merge_file_input ancestor = GIT_MERGE_FILE_INPUT_INIT,
		ours = GIT_MERGE_FILE_INPUT_INIT,
		theirs = GIT_MERGE_FILE_INPUT_INIT;
	git_merge_file_result result = GIT_MERGE_FILE_RESULT_INIT;
	git_index_entry *index_entry;
	git_odb *odb = NULL;
	git_oid automerge_oid;
	int error = 0;

	assert(resolved && diff_list && conflict);

	*resolved = 0;

	if (automerge_flags == GIT_MERGE_AUTOMERGE_NONE)
		return 0;

	/* Reject D/F conflicts */
	if (conflict->type == GIT_MERGE_DIFF_DIRECTORY_FILE)
		return 0;

	/* Reject link/file conflicts. */
	if ((S_ISLNK(conflict->ancestor_entry.mode) ^ S_ISLNK(conflict->our_entry.mode)) ||
		(S_ISLNK(conflict->ancestor_entry.mode) ^ S_ISLNK(conflict->their_entry.mode)))
		return 0;

	/* Reject name conflicts */
	if (conflict->type == GIT_MERGE_DIFF_BOTH_RENAMED_2_TO_1 ||
		conflict->type == GIT_MERGE_DIFF_RENAMED_ADDED)
		return 0;

	if ((conflict->our_status & GIT_DELTA_RENAMED) == GIT_DELTA_RENAMED &&
		(conflict->their_status & GIT_DELTA_RENAMED) == GIT_DELTA_RENAMED &&
		strcmp(conflict->ancestor_entry.path, conflict->their_entry.path) != 0)
		return 0;

	if ((error = git_repository_odb(&odb, diff_list->repo)) < 0 ||
		(error = git_merge_file_input_from_index_entry(&ancestor, diff_list->repo, &conflict->ancestor_entry)) < 0 ||
		(error = git_merge_file_input_from_index_entry(&ours, diff_list->repo, &conflict->our_entry)) < 0 ||
		(error = git_merge_file_input_from_index_entry(&theirs, diff_list->repo, &conflict->their_entry)) < 0 ||
		(error = git_merge_files(&result, &ancestor, &ours, &theirs, automerge_flags)) < 0 ||
		!result.automergeable ||
		(error = git_odb_write(&automerge_oid, odb, result.data, result.len, GIT_OBJ_BLOB)) < 0)
		goto done;

	if ((index_entry = git_pool_malloc(&diff_list->pool, sizeof(git_index_entry))) == NULL)
	GITERR_CHECK_ALLOC(index_entry);

	index_entry->path = git_pool_strdup(&diff_list->pool, result.path);
	GITERR_CHECK_ALLOC(index_entry->path);

	index_entry->file_size = result.len;
	index_entry->mode = result.mode;
	git_oid_cpy(&index_entry->oid, &automerge_oid);

	git_vector_insert(&diff_list->staged, index_entry);
	git_vector_insert(&diff_list->resolved, (git_merge_diff *)conflict);

	*resolved = 1;

done:
	git_merge_file_input_free(&ancestor);
	git_merge_file_input_free(&ours);
	git_merge_file_input_free(&theirs);
	git_merge_file_result_free(&result);
	git_odb_free(odb);

	return error;
}

// duplicate merge_conflict_resolve function,
// this is from the old repo
static int merge_conflict_resolve_old(
	int *out,
	git_repository *repo,
	git_index *index,
	const git_diff_tree_delta *delta,
	unsigned int resolve_flags)
{
	int resolved = 0;
	int error = 0;
	
	*out = 0;
	
	if ((error = merge_conflict_resolve_trivial_old(&resolved, repo, index, delta, resolve_flags)) < 0)
		goto done;
	
	if (!resolved && (error = merge_conflict_resolve_removed(&resolved, repo, index, delta, resolve_flags)) < 0)
		goto done;

	if (!resolved && (error = merge_conflict_resolve_automerge_old(&resolved, repo, index, delta, resolve_flags)) < 0)
		goto done;

	if (!resolved)
		error = merge_mark_conflict_unresolved(index, delta);
	
	*out = resolved;
	
done:
	return error;
}

static int merge_conflict_resolve(
	int *out,
	git_merge_diff_list *diff_list,
	const git_merge_diff *conflict,
	unsigned int automerge_flags)
{
	int resolved = 0;
	int error = 0;

	*out = 0;

	if ((error = merge_conflict_resolve_trivial(&resolved, diff_list, conflict)) < 0)
		goto done;

	if (automerge_flags != GIT_MERGE_AUTOMERGE_NONE) {
		if (!resolved && (error = merge_conflict_resolve_one_removed(&resolved, diff_list, conflict)) < 0)
			goto done;

		if (!resolved && (error = merge_conflict_resolve_one_renamed(&resolved, diff_list, conflict)) < 0)
			goto done;

		if (!resolved && (error = merge_conflict_resolve_automerge(&resolved, diff_list, conflict, automerge_flags)) < 0)
			goto done;
	}

	*out = resolved;

done:
	return error;
}

/* Rename detection and coalescing */

struct merge_diff_similarity {
	unsigned char similarity;
	size_t other_idx;
};

static int index_entry_similarity_exact(
	git_repository *repo,
	git_index_entry *a,
	size_t a_idx,
	git_index_entry *b,
	size_t b_idx,
	void **cache,
	const git_merge_tree_opts *opts)
{
	GIT_UNUSED(repo);
	GIT_UNUSED(a_idx);
	GIT_UNUSED(b_idx);
	GIT_UNUSED(cache);
	GIT_UNUSED(opts);

	if (git_oid__cmp(&a->oid, &b->oid) == 0)
		return 100;

	return 0;
}

static int index_entry_similarity_calc(
	void **out,
	git_repository *repo,
	git_index_entry *entry,
	const git_merge_tree_opts *opts)
{
	git_blob *blob;
	git_diff_file diff_file = {{{0}}};
	git_off_t blobsize;
	int error;

	*out = NULL;

	if ((error = git_blob_lookup(&blob, repo, &entry->oid)) < 0)
		return error;

	git_oid_cpy(&diff_file.oid, &entry->oid);
	diff_file.path = entry->path;
	diff_file.size = entry->file_size;
	diff_file.mode = entry->mode;
	diff_file.flags = 0;

	blobsize = git_blob_rawsize(blob);

	/* file too big for rename processing */
	if (!git__is_sizet(blobsize))
		return 0;

	error = opts->metric->buffer_signature(out, &diff_file,
		git_blob_rawcontent(blob), (size_t)blobsize,
		opts->metric->payload);

	git_blob_free(blob);

	return error;
}

static int index_entry_similarity_inexact(
	git_repository *repo,
	git_index_entry *a,
	size_t a_idx,
	git_index_entry *b,
	size_t b_idx,
	void **cache,
	const git_merge_tree_opts *opts)
{
	int score = 0;
	int error = 0;

	if (GIT_MODE_TYPE(a->mode) != GIT_MODE_TYPE(b->mode))
		return 0;

	/* update signature cache if needed */
	if (!cache[a_idx] && (error = index_entry_similarity_calc(&cache[a_idx], repo, a, opts)) < 0)
		return error;
	if (!cache[b_idx] && (error = index_entry_similarity_calc(&cache[b_idx], repo, b, opts)) < 0)
		return error;

	/* some metrics may not wish to process this file (too big / too small) */
	if (!cache[a_idx] || !cache[b_idx])
		return 0;

	/* compare signatures */
	if (opts->metric->similarity(
		&score, cache[a_idx], cache[b_idx], opts->metric->payload) < 0)
		return -1;

	/* clip score */
	if (score < 0)
		score = 0;
	else if (score > 100)
		score = 100;

	return score;
}

static int merge_diff_mark_similarity(
	git_repository *repo,
	git_merge_diff_list *diff_list,
	struct merge_diff_similarity *similarity_ours,
	struct merge_diff_similarity *similarity_theirs,
	int (*similarity_fn)(git_repository *, git_index_entry *, size_t, git_index_entry *, size_t, void **, const git_merge_tree_opts *),
	void **cache,
	const git_merge_tree_opts *opts)
{
	size_t i, j;
	git_merge_diff *conflict_src, *conflict_tgt;
	int similarity;

	git_vector_foreach(&diff_list->conflicts, i, conflict_src) {
		/* Items can be the source of a rename iff they have an item in the
		 * ancestor slot and lack an item in the ours or theirs slot. */
		if (!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_src->ancestor_entry) ||
			(GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_src->our_entry) &&
			 GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_src->their_entry)))
			continue;

		git_vector_foreach(&diff_list->conflicts, j, conflict_tgt) {
			size_t our_idx = diff_list->conflicts.length + j;
			size_t their_idx = (diff_list->conflicts.length * 2) + j;

			if (GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_tgt->ancestor_entry))
				continue;

			if (GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_tgt->our_entry) &&
				!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_src->our_entry)) {
				similarity = similarity_fn(repo, &conflict_src->ancestor_entry, i, &conflict_tgt->our_entry, our_idx, cache, opts);

				if (similarity == GIT_EBUFS)
					continue;
				else if (similarity < 0)
					return similarity;

				if (similarity > similarity_ours[i].similarity &&
					similarity > similarity_ours[j].similarity) {
					/* Clear previous best similarity */
					if (similarity_ours[i].similarity > 0)
						similarity_ours[similarity_ours[i].other_idx].similarity = 0;

					if (similarity_ours[j].similarity > 0)
						similarity_ours[similarity_ours[j].other_idx].similarity = 0;

					similarity_ours[i].similarity = similarity;
					similarity_ours[i].other_idx = j;

					similarity_ours[j].similarity = similarity;
					similarity_ours[j].other_idx = i;
				}
			}

			if (GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_tgt->their_entry) &&
				!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict_src->their_entry)) {
				similarity = similarity_fn(repo, &conflict_src->ancestor_entry, i, &conflict_tgt->their_entry, their_idx, cache, opts);

				if (similarity > similarity_theirs[i].similarity &&
					similarity > similarity_theirs[j].similarity) {
					/* Clear previous best similarity */
					if (similarity_theirs[i].similarity > 0)
						similarity_theirs[similarity_theirs[i].other_idx].similarity = 0;

					if (similarity_theirs[j].similarity > 0)
						similarity_theirs[similarity_theirs[j].other_idx].similarity = 0;

					similarity_theirs[i].similarity = similarity;
					similarity_theirs[i].other_idx = j;

					similarity_theirs[j].similarity = similarity;
					similarity_theirs[j].other_idx = i;
				}
			}
		}
	}

	return 0;
}

/*
 * Rename conflicts:
 *
 *      Ancestor   Ours   Theirs
 *
 * 0a   A          A      A        No rename
 *  b   A          A*     A        No rename (ours was rewritten)
 *  c   A          A      A*       No rename (theirs rewritten)
 * 1a   A          A      B[A]     Rename or rename/edit
 *  b   A          B[A]   A        (automergeable)
 * 2    A          B[A]   B[A]     Both renamed (automergeable)
 * 3a   A          B[A]            Rename/delete
 *  b   A                 B[A]      (same)
 * 4a   A          B[A]   B        Rename/add [B~ours B~theirs]
 *  b   A          B      B[A]      (same)
 * 5    A          B[A]   C[A]     Both renamed ("1 -> 2")
 * 6    A          C[A]            Both renamed ("2 -> 1")
 *      B                 C[B]     [C~ours C~theirs]    (automergeable)
 */
static void merge_diff_mark_rename_conflict(
	git_merge_diff_list *diff_list,
	struct merge_diff_similarity *similarity_ours,
	bool ours_renamed,
	size_t ours_source_idx,
	struct merge_diff_similarity *similarity_theirs,
	bool theirs_renamed,
	size_t theirs_source_idx,
	git_merge_diff *target,
	const git_merge_tree_opts *opts)
{
	git_merge_diff *ours_source = NULL, *theirs_source = NULL;

	if (ours_renamed)
		ours_source = diff_list->conflicts.contents[ours_source_idx];

	if (theirs_renamed)
		theirs_source = diff_list->conflicts.contents[theirs_source_idx];

	/* Detect 2->1 conflicts */
	if (ours_renamed && theirs_renamed) {
		/* Both renamed to the same target name. */
		if (ours_source_idx == theirs_source_idx)
			ours_source->type = GIT_MERGE_DIFF_BOTH_RENAMED;
		else {
			ours_source->type = GIT_MERGE_DIFF_BOTH_RENAMED_2_TO_1;
			theirs_source->type = GIT_MERGE_DIFF_BOTH_RENAMED_2_TO_1;
		}
	} else if (ours_renamed) {
		/* If our source was also renamed in theirs, this is a 1->2 */
		if (similarity_theirs[ours_source_idx].similarity >= opts->rename_threshold)
			ours_source->type = GIT_MERGE_DIFF_BOTH_RENAMED_1_TO_2;

		else if (GIT_MERGE_INDEX_ENTRY_EXISTS(target->their_entry)) {
			ours_source->type = GIT_MERGE_DIFF_RENAMED_ADDED;
			target->type = GIT_MERGE_DIFF_RENAMED_ADDED;
		}

		else if (!GIT_MERGE_INDEX_ENTRY_EXISTS(ours_source->their_entry))
			ours_source->type = GIT_MERGE_DIFF_RENAMED_DELETED;

		else if (ours_source->type == GIT_MERGE_DIFF_MODIFIED_DELETED)
			ours_source->type = GIT_MERGE_DIFF_RENAMED_MODIFIED;
	} else if (theirs_renamed) {
		/* If their source was also renamed in ours, this is a 1->2 */
		if (similarity_ours[theirs_source_idx].similarity >= opts->rename_threshold)
			theirs_source->type = GIT_MERGE_DIFF_BOTH_RENAMED_1_TO_2;

		else if (GIT_MERGE_INDEX_ENTRY_EXISTS(target->our_entry)) {
			theirs_source->type = GIT_MERGE_DIFF_RENAMED_ADDED;
			target->type = GIT_MERGE_DIFF_RENAMED_ADDED;
		}

		else if (!GIT_MERGE_INDEX_ENTRY_EXISTS(theirs_source->our_entry))
			theirs_source->type = GIT_MERGE_DIFF_RENAMED_DELETED;

		else if (theirs_source->type == GIT_MERGE_DIFF_MODIFIED_DELETED)
			theirs_source->type = GIT_MERGE_DIFF_RENAMED_MODIFIED;
	}
}

GIT_INLINE(void) merge_diff_coalesce_rename(
	git_index_entry *source_entry,
	git_delta_t *source_status,
	git_index_entry *target_entry,
	git_delta_t *target_status)
{
	/* Coalesce the rename target into the rename source. */
	memcpy(source_entry, target_entry, sizeof(git_index_entry));
	*source_status = GIT_DELTA_RENAMED;

	memset(target_entry, 0x0, sizeof(git_index_entry));
	*target_status = GIT_DELTA_UNMODIFIED;
}

static void merge_diff_list_coalesce_renames(
	git_merge_diff_list *diff_list,
	struct merge_diff_similarity *similarity_ours,
	struct merge_diff_similarity *similarity_theirs,
	const git_merge_tree_opts *opts)
{
	size_t i;
	bool ours_renamed = 0, theirs_renamed = 0;
	size_t ours_source_idx = 0, theirs_source_idx = 0;
	git_merge_diff *ours_source, *theirs_source, *target;

	for (i = 0; i < diff_list->conflicts.length; i++) {
		target = diff_list->conflicts.contents[i];

		ours_renamed = 0;
		theirs_renamed = 0;

		if (GIT_MERGE_INDEX_ENTRY_EXISTS(target->our_entry) &&
			similarity_ours[i].similarity >= opts->rename_threshold) {
			ours_source_idx = similarity_ours[i].other_idx;

			ours_source = diff_list->conflicts.contents[ours_source_idx];

			merge_diff_coalesce_rename(
				&ours_source->our_entry,
				&ours_source->our_status,
				&target->our_entry,
				&target->our_status);

			similarity_ours[ours_source_idx].similarity = 0;
			similarity_ours[i].similarity = 0;

			ours_renamed = 1;
		}

		/* insufficient to determine direction */
		if (GIT_MERGE_INDEX_ENTRY_EXISTS(target->their_entry) &&
			similarity_theirs[i].similarity >= opts->rename_threshold) {
			theirs_source_idx = similarity_theirs[i].other_idx;

			theirs_source = diff_list->conflicts.contents[theirs_source_idx];

			merge_diff_coalesce_rename(
				&theirs_source->their_entry,
				&theirs_source->their_status,
				&target->their_entry,
				&target->their_status);

			similarity_theirs[theirs_source_idx].similarity = 0;
			similarity_theirs[i].similarity = 0;

			theirs_renamed = 1;
		}

		merge_diff_mark_rename_conflict(diff_list,
			similarity_ours, ours_renamed, ours_source_idx,
			similarity_theirs, theirs_renamed, theirs_source_idx,
			target, opts);
	}
}

static int merge_diff_empty(const git_vector *conflicts, size_t idx)
{
	git_merge_diff *conflict = conflicts->contents[idx];

	return (!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->ancestor_entry) &&
		!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry) &&
		!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry));
}

static void merge_diff_list_count_candidates(
	git_merge_diff_list *diff_list,
	size_t *src_count,
	size_t *tgt_count)
{
	git_merge_diff *entry;
	size_t i;

	*src_count = 0;
	*tgt_count = 0;

	git_vector_foreach(&diff_list->conflicts, i, entry) {
		if (GIT_MERGE_INDEX_ENTRY_EXISTS(entry->ancestor_entry) &&
			(!GIT_MERGE_INDEX_ENTRY_EXISTS(entry->our_entry) ||
			!GIT_MERGE_INDEX_ENTRY_EXISTS(entry->their_entry)))
			src_count++;
		else if (!GIT_MERGE_INDEX_ENTRY_EXISTS(entry->ancestor_entry))
			tgt_count++;
	}
}

int git_merge_diff_list__find_renames(
	git_repository *repo,
	git_merge_diff_list *diff_list,
	const git_merge_tree_opts *opts)
{
	struct merge_diff_similarity *similarity_ours, *similarity_theirs;
	void **cache = NULL;
	size_t cache_size = 0;
	size_t src_count, tgt_count, i;
	int error = 0;

	assert(diff_list && opts);

	if ((opts->flags & GIT_MERGE_TREE_FIND_RENAMES) == 0)
		return 0;

	similarity_ours = git__calloc(diff_list->conflicts.length,
		sizeof(struct merge_diff_similarity));
	GITERR_CHECK_ALLOC(similarity_ours);

	similarity_theirs = git__calloc(diff_list->conflicts.length,
		sizeof(struct merge_diff_similarity));
	GITERR_CHECK_ALLOC(similarity_theirs);

	/* Calculate similarity between items that were deleted from the ancestor
	 * and added in the other branch.
	 */
	if ((error = merge_diff_mark_similarity(repo, diff_list, similarity_ours,
		similarity_theirs, index_entry_similarity_exact, NULL, opts)) < 0)
		goto done;

	if (diff_list->conflicts.length <= opts->target_limit) {
		cache_size = diff_list->conflicts.length * 3;
		cache = git__calloc(cache_size, sizeof(void *));
		GITERR_CHECK_ALLOC(cache);

		merge_diff_list_count_candidates(diff_list, &src_count, &tgt_count);

		if (src_count > opts->target_limit || tgt_count > opts->target_limit) {
			/* TODO: report! */
		} else {
			if ((error = merge_diff_mark_similarity(
				repo, diff_list, similarity_ours, similarity_theirs,
				index_entry_similarity_inexact, cache, opts)) < 0)
				goto done;
		}
	}

	/* For entries that are appropriately similar, merge the new name's entry
	 * into the old name.
	 */
	merge_diff_list_coalesce_renames(diff_list, similarity_ours, similarity_theirs, opts);

	/* And remove any entries that were merged and are now empty. */
	git_vector_remove_matching(&diff_list->conflicts, merge_diff_empty);

done:
	if (cache != NULL) {
		for (i = 0; i < cache_size; ++i) {
			if (cache[i] != NULL)
				opts->metric->free_signature(cache[i], opts->metric->payload);
		}

		git__free(cache);
	}

	git__free(similarity_ours);
	git__free(similarity_theirs);

	return error;
}

/* Directory/file conflict handling */

GIT_INLINE(const char *) merge_diff_path(
	const git_merge_diff *conflict)
{
	if (GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->ancestor_entry))
		return conflict->ancestor_entry.path;
	else if (GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry))
		return conflict->our_entry.path;
	else if (GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry))
		return conflict->their_entry.path;

	return NULL;
}

GIT_INLINE(bool) merge_diff_any_side_added_or_modified(
	const git_merge_diff *conflict)
{
	if (conflict->our_status == GIT_DELTA_ADDED ||
		conflict->our_status == GIT_DELTA_MODIFIED ||
		conflict->their_status == GIT_DELTA_ADDED ||
		conflict->their_status == GIT_DELTA_MODIFIED)
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

GIT_INLINE(int) merge_diff_detect_df_conflict(
	struct merge_diff_df_data *df_data,
	git_merge_diff *conflict)
{
	const char *cur_path = merge_diff_path(conflict);

	/* Determine if this is a D/F conflict or the child of one */
	if (df_data->df_path &&
		path_is_prefixed(df_data->df_path, cur_path))
		conflict->type = GIT_MERGE_DIFF_DF_CHILD;
	else if(df_data->df_path)
		df_data->df_path = NULL;
	else if (df_data->prev_path &&
		merge_diff_any_side_added_or_modified(df_data->prev_conflict) &&
		merge_diff_any_side_added_or_modified(conflict) &&
		path_is_prefixed(df_data->prev_path, cur_path)) {
		conflict->type = GIT_MERGE_DIFF_DF_CHILD;

		df_data->prev_conflict->type = GIT_MERGE_DIFF_DIRECTORY_FILE;
		df_data->df_path = df_data->prev_path;
	}

	df_data->prev_path = cur_path;
	df_data->prev_conflict = conflict;

	return 0;
}

/* Conflict handling */

GIT_INLINE(int) merge_diff_detect_type(
	git_merge_diff *conflict)
{
	if (conflict->our_status == GIT_DELTA_ADDED &&
		conflict->their_status == GIT_DELTA_ADDED)
		conflict->type = GIT_MERGE_DIFF_BOTH_ADDED;
	else if (conflict->our_status == GIT_DELTA_MODIFIED &&
			 conflict->their_status == GIT_DELTA_MODIFIED)
		conflict->type = GIT_MERGE_DIFF_BOTH_MODIFIED;
	else if (conflict->our_status == GIT_DELTA_DELETED &&
			 conflict->their_status == GIT_DELTA_DELETED)
		conflict->type = GIT_MERGE_DIFF_BOTH_DELETED;
	else if (conflict->our_status == GIT_DELTA_MODIFIED &&
			 conflict->their_status == GIT_DELTA_DELETED)
		conflict->type = GIT_MERGE_DIFF_MODIFIED_DELETED;
	else if (conflict->our_status == GIT_DELTA_DELETED &&
			 conflict->their_status == GIT_DELTA_MODIFIED)
		conflict->type = GIT_MERGE_DIFF_MODIFIED_DELETED;
	else
		conflict->type = GIT_MERGE_DIFF_NONE;

	return 0;
}

GIT_INLINE(int) index_entry_dup(
	git_index_entry *out,
	git_pool *pool,
	const git_index_entry *src)
{
	if (src != NULL) {
		memcpy(out, src, sizeof(git_index_entry));

		if ((out->path = git_pool_strdup(pool, src->path)) == NULL)
			return -1;
	}

	return 0;
}

GIT_INLINE(int) merge_delta_type_from_index_entries(
	const git_index_entry *ancestor,
	const git_index_entry *other)
{
	if (ancestor == NULL && other == NULL)
		return GIT_DELTA_UNMODIFIED;
	else if (ancestor == NULL && other != NULL)
		return GIT_DELTA_ADDED;
	else if (ancestor != NULL && other == NULL)
		return GIT_DELTA_DELETED;
	else if (S_ISDIR(ancestor->mode) ^ S_ISDIR(other->mode))
		return GIT_DELTA_TYPECHANGE;
	else if(S_ISLNK(ancestor->mode) ^ S_ISLNK(other->mode))
		return GIT_DELTA_TYPECHANGE;
	else if (git_oid__cmp(&ancestor->oid, &other->oid) ||
			 ancestor->mode != other->mode)
		return GIT_DELTA_MODIFIED;

	return GIT_DELTA_UNMODIFIED;
}

static git_merge_diff *merge_diff_from_index_entries(
	git_merge_diff_list *diff_list,
	const git_index_entry **entries)
{
	git_merge_diff *conflict;
	git_pool *pool = &diff_list->pool;

	if ((conflict = git_pool_malloc(pool, sizeof(git_merge_diff))) == NULL)
		return NULL;

	if (index_entry_dup(&conflict->ancestor_entry, pool, entries[TREE_IDX_ANCESTOR]) < 0 ||
		index_entry_dup(&conflict->our_entry, pool, entries[TREE_IDX_OURS]) < 0 ||
		index_entry_dup(&conflict->their_entry, pool, entries[TREE_IDX_THEIRS]) < 0)
		return NULL;

	conflict->our_status = merge_delta_type_from_index_entries(
		entries[TREE_IDX_ANCESTOR], entries[TREE_IDX_OURS]);
	conflict->their_status = merge_delta_type_from_index_entries(
		entries[TREE_IDX_ANCESTOR], entries[TREE_IDX_THEIRS]);

	return conflict;
}

/* Merge trees */

static int merge_index_insert_conflict(
	git_merge_diff_list *diff_list,
	struct merge_diff_df_data *merge_df_data,
	const git_index_entry *tree_items[3])
{
	git_merge_diff *conflict;

	if ((conflict = merge_diff_from_index_entries(diff_list, tree_items)) == NULL ||
		merge_diff_detect_type(conflict) < 0 ||
		merge_diff_detect_df_conflict(merge_df_data, conflict) < 0 ||
		git_vector_insert(&diff_list->conflicts, conflict) < 0)
		return -1;

	return 0;
}

static int merge_index_insert_unmodified(
	git_merge_diff_list *diff_list,
	const git_index_entry *tree_items[3])
{
	int error = 0;
	git_index_entry *entry;

	entry = git_pool_malloc(&diff_list->pool, sizeof(git_index_entry));
	GITERR_CHECK_ALLOC(entry);

	if ((error = index_entry_dup(entry, &diff_list->pool, tree_items[0])) >= 0)
		error = git_vector_insert(&diff_list->staged, entry);

	return error;
}

int git_merge_diff_list__find_differences(
	git_merge_diff_list *diff_list,
	const git_tree *ancestor_tree,
	const git_tree *our_tree,
	const git_tree *their_tree)
{
	git_iterator *iterators[3] = {0};
	const git_index_entry *items[3] = {0}, *best_cur_item, *cur_items[3];
	git_vector_cmp entry_compare = git_index_entry__cmp;
	struct merge_diff_df_data df_data = {0};
	int cur_item_modified;
	size_t i, j;
	int error = 0;

	assert(diff_list && our_tree && their_tree);

	if ((error = git_iterator_for_tree(&iterators[TREE_IDX_ANCESTOR], (git_tree *)ancestor_tree, GIT_ITERATOR_DONT_IGNORE_CASE, NULL, NULL)) < 0 ||
		(error = git_iterator_for_tree(&iterators[TREE_IDX_OURS], (git_tree *)our_tree, GIT_ITERATOR_DONT_IGNORE_CASE, NULL, NULL)) < 0 ||
		(error = git_iterator_for_tree(&iterators[TREE_IDX_THEIRS], (git_tree *)their_tree, GIT_ITERATOR_DONT_IGNORE_CASE, NULL, NULL)) < 0)
		goto done;

	/* Set up the iterators */
	for (i = 0; i < 3; i++) {
		if ((error = git_iterator_current(&items[i], iterators[i])) < 0)
			goto done;
	}

	while (true) {
		for (i = 0; i < 3; i++)
			cur_items[i] = NULL;

		best_cur_item = NULL;
		cur_item_modified = 0;

		/* Find the next path(s) to consume from each iterator */
		for (i = 0; i < 3; i++) {
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
					for (j = 0; j < i; j++)
						cur_items[j] = NULL;

					cur_item_modified = 1;
					best_cur_item = items[i];
					cur_items[i] = items[i];
				} else if (path_diff > 0) {
					/* No entry for the current item, this is modified */
					cur_item_modified = 1;
				} else if (path_diff == 0) {
					cur_items[i] = items[i];

					if (!cur_item_modified)
						cur_item_modified = index_entry_cmp(best_cur_item, items[i]);
				}
			}
		}

		if (best_cur_item == NULL)
			break;

		if (cur_item_modified)
			error = merge_index_insert_conflict(diff_list, &df_data, cur_items);
		else
			error = merge_index_insert_unmodified(diff_list, cur_items);

		/* Advance each iterator that participated */
		for (i = 0; i < 3; i++) {
			if (cur_items[i] != NULL &&
				(error = git_iterator_advance(&items[i], iterators[i])) < 0)
				goto done;
		}
	}

done:
	for (i = 0; i < 3; i++)
		git_iterator_free(iterators[i]);

	return error;
}

git_merge_diff_list *git_merge_diff_list__alloc(git_repository *repo)
{
	git_merge_diff_list *diff_list = git__calloc(1, sizeof(git_merge_diff_list));

	if (diff_list == NULL)
		return NULL;

	diff_list->repo = repo;

	if (git_vector_init(&diff_list->staged, 0, NULL) < 0 ||
		git_vector_init(&diff_list->conflicts, 0, NULL) < 0 ||
		git_vector_init(&diff_list->resolved, 0, NULL) < 0 ||
		git_pool_init(&diff_list->pool, 1, 0) < 0)
		return NULL;

	return diff_list;
}

void git_merge_diff_list__free(git_merge_diff_list *diff_list)
{
	if (!diff_list)
		return;

	git_vector_free(&diff_list->staged);
	git_vector_free(&diff_list->conflicts);
	git_vector_free(&diff_list->resolved);
	git_pool_clear(&diff_list->pool);
	git__free(diff_list);
}

static int merge_tree_normalize_opts(
	git_repository *repo,
	git_merge_tree_opts *opts,
	const git_merge_tree_opts *given)
{
	git_config *cfg = NULL;
	int error = 0;

	assert(repo && opts);

	if ((error = git_repository_config__weakptr(&cfg, repo)) < 0)
		return error;

	if (given != NULL)
		memcpy(opts, given, sizeof(git_merge_tree_opts));
	else {
		git_merge_tree_opts init = GIT_MERGE_TREE_OPTS_INIT;
		memcpy(opts, &init, sizeof(init));

		opts->flags = GIT_MERGE_TREE_FIND_RENAMES;
		opts->rename_threshold = GIT_MERGE_TREE_RENAME_THRESHOLD;
	}

	if (!opts->target_limit) {
		int32_t limit = 0;

		opts->target_limit = GIT_MERGE_TREE_TARGET_LIMIT;

		if (git_config_get_int32(&limit, cfg, "merge.renameLimit") < 0) {
			giterr_clear();

			if (git_config_get_int32(&limit, cfg, "diff.renameLimit") < 0)
				giterr_clear();
		}

		if (limit > 0)
			opts->target_limit = limit;
	}

	/* assign the internal metric with whitespace flag as payload */
	if (!opts->metric) {
		opts->metric = git__malloc(sizeof(git_diff_similarity_metric));
		GITERR_CHECK_ALLOC(opts->metric);

		opts->metric->file_signature = git_diff_find_similar__hashsig_for_file;
		opts->metric->buffer_signature = git_diff_find_similar__hashsig_for_buf;
		opts->metric->free_signature = git_diff_find_similar__hashsig_free;
		opts->metric->similarity = git_diff_find_similar__calc_similarity;

		if (opts->flags & GIT_DIFF_FIND_IGNORE_WHITESPACE)
			opts->metric->payload = (void *)GIT_HASHSIG_IGNORE_WHITESPACE;
		else if (opts->flags & GIT_DIFF_FIND_DONT_IGNORE_WHITESPACE)
			opts->metric->payload = (void *)GIT_HASHSIG_NORMAL;
		else
			opts->metric->payload = (void *)GIT_HASHSIG_SMART_WHITESPACE;
	}

	return 0;
}


static int merge_index_insert_reuc(
	git_index *index,
	size_t idx,
	const git_index_entry *entry)
{
	const git_index_reuc_entry *reuc;
	int mode[3] = { 0, 0, 0 };
	git_oid const *oid[3] = { NULL, NULL, NULL };
	size_t i;

	if (!GIT_MERGE_INDEX_ENTRY_EXISTS(*entry))
		return 0;

	if ((reuc = git_index_reuc_get_bypath(index, entry->path)) != NULL) {
		for (i = 0; i < 3; i++) {
			mode[i] = reuc->mode[i];
			oid[i] = &reuc->oid[i];
		}
	}

	mode[idx] = entry->mode;
	oid[idx] = &entry->oid;

	return git_index_reuc_add(index, entry->path,
		mode[0], oid[0], mode[1], oid[1], mode[2], oid[2]);
}

int index_from_diff_list(git_index **out, git_merge_diff_list *diff_list)
{
	git_index *index;
	size_t i;
	git_index_entry *entry;
	git_merge_diff *conflict;
	int error = 0;

	*out = NULL;

	if ((error = git_index_new(&index)) < 0)
		return error;

	git_vector_foreach(&diff_list->staged, i, entry) {
		if ((error = git_index_add(index, entry)) < 0)
			goto on_error;
	}

	git_vector_foreach(&diff_list->conflicts, i, conflict) {
		const git_index_entry *ancestor =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->ancestor_entry) ?
			&conflict->ancestor_entry : NULL;

		const git_index_entry *ours =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry) ?
			&conflict->our_entry : NULL;

		const git_index_entry *theirs =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry) ?
			&conflict->their_entry : NULL;

		if ((error = git_index_conflict_add(index, ancestor, ours, theirs)) < 0)
			goto on_error;
	}

	/* Add each rename entry to the rename portion of the index. */
	git_vector_foreach(&diff_list->conflicts, i, conflict) {
		const char *ancestor_path, *our_path, *their_path;

		if (!GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->ancestor_entry))
			continue;

		ancestor_path = conflict->ancestor_entry.path;

		our_path =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry) ?
			conflict->our_entry.path : NULL;

		their_path =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry) ?
			conflict->their_entry.path : NULL;

		if ((our_path && strcmp(ancestor_path, our_path) != 0) ||
			(their_path && strcmp(ancestor_path, their_path) != 0)) {
			if ((error = git_index_name_add(index, ancestor_path, our_path, their_path)) < 0)
				goto on_error;
		}
	}

	/* Add each entry in the resolved conflict to the REUC independently, since
	 * the paths may differ due to renames. */
	git_vector_foreach(&diff_list->resolved, i, conflict) {
		const git_index_entry *ancestor =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->ancestor_entry) ?
			&conflict->ancestor_entry : NULL;

		const git_index_entry *ours =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->our_entry) ?
			&conflict->our_entry : NULL;

		const git_index_entry *theirs =
			GIT_MERGE_INDEX_ENTRY_EXISTS(conflict->their_entry) ?
			&conflict->their_entry : NULL;

		if (ancestor != NULL &&
			(error = merge_index_insert_reuc(index, TREE_IDX_ANCESTOR, ancestor)) < 0)
			goto on_error;

		if (ours != NULL &&
			(error = merge_index_insert_reuc(index, TREE_IDX_OURS, ours)) < 0)
			goto on_error;

		if (theirs != NULL &&
			(error = merge_index_insert_reuc(index, TREE_IDX_THEIRS, theirs)) < 0)
			goto on_error;
	}

	*out = index;
	return 0;

on_error:
	git_index_free(index);

	return error;
}

/* Merge trees */

static int merge_trees(
	git_merge_result *result,
	git_repository *repo,
	git_index *index,
	git_tree *ancestor_tree,
	git_tree *our_tree,
	git_tree *their_tree,
	const git_merge_trees_opts *opts)
{
	git_diff_tree_delta *delta;
	size_t i;
	int error = 0;

	if ((error = git_diff_tree(&result->diff_tree, repo, ancestor_tree, our_tree, their_tree, opts->diff_flags)) < 0)
		return error;
	
	git_vector_foreach(&result->diff_tree->deltas, i, delta) {
        int resolved = 0;
		
		if ((error = merge_conflict_resolve_old(&resolved, repo, index, delta, opts->resolve_flags)) < 0)
			return error;
		
        if (!resolved)
			git_vector_insert(&result->conflicts, delta);
	}

	return 0;
}

static int merge_trees_octopus(
	git_merge_result *result,
	git_repository *repo,
	git_index *index,
	const git_tree *ancestor_tree,
	const git_tree *our_tree,
	const git_tree **their_trees,
	size_t their_trees_len,
	const git_merge_trees_opts *opts)
{
	GIT_UNUSED(result);
	GIT_UNUSED(repo);
	GIT_UNUSED(index);
	GIT_UNUSED(ancestor_tree);
	GIT_UNUSED(our_tree);
	GIT_UNUSED(their_trees);
	GIT_UNUSED(their_trees_len);
	GIT_UNUSED(opts);
	
	giterr_set(GITERR_MERGE, "Merge octopus is not yet implemented.");
	return -1;
}

static int merge_trees_normalize_opts(
	git_merge_trees_opts *opts,
	const git_merge_trees_opts *given)
{
	if (given != NULL)
		memcpy(opts, given, sizeof(git_merge_trees_opts));
	else
		memset(opts, 0x0, sizeof(git_merge_trees_opts));

	return 0;
}

int git_merge_trees(
	git_index **out,
	git_repository *repo,
	const git_tree *ancestor_tree,
	const git_tree *our_tree,
	const git_tree *their_tree,
	const git_merge_tree_opts *given_opts)
{
	git_merge_diff_list *diff_list;
	git_merge_tree_opts opts;
	git_merge_diff *conflict;
	git_vector changes;
	size_t i;
	int error = 0;

	assert(out && repo && our_tree && their_tree);

	*out = NULL;

	if ((error = merge_tree_normalize_opts(repo, &opts, given_opts)) < 0)
		return error;

	diff_list = git_merge_diff_list__alloc(repo);
	GITERR_CHECK_ALLOC(diff_list);

	if ((error = git_merge_diff_list__find_differences(diff_list, ancestor_tree, our_tree, their_tree)) < 0 ||
		(error = git_merge_diff_list__find_renames(repo, diff_list, &opts)) < 0)
		goto done;

	memcpy(&changes, &diff_list->conflicts, sizeof(git_vector));
	git_vector_clear(&diff_list->conflicts);

	git_vector_foreach(&changes, i, conflict) {
		int resolved = 0;

		if ((error = merge_conflict_resolve(&resolved, diff_list, conflict, opts.automerge_flags)) < 0)
			goto done;

		if (!resolved)
			git_vector_insert(&diff_list->conflicts, conflict);
	}

	if (!given_opts || !given_opts->metric)
		git__free(opts.metric);

	error = index_from_diff_list(out, diff_list);

done:
	git_merge_diff_list__free(diff_list);

	return error;
}

/* Merge setup / cleanup */

static int write_orig_head(
	git_repository *repo,
	const git_merge_head *our_head)
{
	git_filebuf file = GIT_FILEBUF_INIT;
	git_buf file_path = GIT_BUF_INIT;
	char orig_oid_str[GIT_OID_HEXSZ + 1];
	int error = 0;

	assert(repo && our_head);

	git_oid_tostr(orig_oid_str, GIT_OID_HEXSZ+1, &our_head->oid);

	if ((error = git_buf_joinpath(&file_path, repo->path_repository, GIT_ORIG_HEAD_FILE)) == 0 &&
		(error = git_filebuf_open(&file, file_path.ptr, GIT_FILEBUF_FORCE)) == 0 &&
		(error = git_filebuf_printf(&file, "%s\n", orig_oid_str)) == 0)
		error = git_filebuf_commit(&file, 0666);

	if (error < 0)
		git_filebuf_cleanup(&file);

	git_buf_free(&file_path);

	return error;
}

static int write_merge_head(
	git_repository *repo,
	const git_merge_head *heads[],
	size_t heads_len)
{
	git_filebuf file = GIT_FILEBUF_INIT;
	git_buf file_path = GIT_BUF_INIT;
	char merge_oid_str[GIT_OID_HEXSZ + 1];
	size_t i;
	int error = 0;

	assert(repo && heads);

	if ((error = git_buf_joinpath(&file_path, repo->path_repository, GIT_MERGE_HEAD_FILE)) < 0 ||
		(error = git_filebuf_open(&file, file_path.ptr, GIT_FILEBUF_FORCE)) < 0)
		goto cleanup;

	for (i = 0; i < heads_len; i++) {
		git_oid_tostr(merge_oid_str, GIT_OID_HEXSZ+1, &heads[i]->oid);

		if ((error = git_filebuf_printf(&file, "%s\n", merge_oid_str)) < 0)
			goto cleanup;
	}

	error = git_filebuf_commit(&file, 0666);

cleanup:
	if (error < 0)
		git_filebuf_cleanup(&file);

	git_buf_free(&file_path);

	return error;
}

static int write_merge_mode(git_repository *repo, unsigned int flags)
{
	git_filebuf file = GIT_FILEBUF_INIT;
	git_buf file_path = GIT_BUF_INIT;
	int error = 0;

	/* For future expansion */
	GIT_UNUSED(flags);

	assert(repo);

	if ((error = git_buf_joinpath(&file_path, repo->path_repository, GIT_MERGE_MODE_FILE)) < 0 ||
		(error = git_filebuf_open(&file, file_path.ptr, GIT_FILEBUF_FORCE)) < 0)
		goto cleanup;

	error = git_filebuf_commit(&file, 0666);

cleanup:
	if (error < 0)
		git_filebuf_cleanup(&file);

	git_buf_free(&file_path);

	return error;
}

struct merge_msg_entry {
	const git_merge_head *merge_head;
	bool written;
};

static int msg_entry_is_branch(
	const struct merge_msg_entry *entry,
	git_vector *entries)
{
	GIT_UNUSED(entries);

	return (entry->written == 0 &&
		entry->merge_head->remote_url == NULL &&
		entry->merge_head->ref_name != NULL &&
		git__strncmp(GIT_REFS_HEADS_DIR, entry->merge_head->ref_name, strlen(GIT_REFS_HEADS_DIR)) == 0);
}

static int msg_entry_is_tracking(
	const struct merge_msg_entry *entry,
	git_vector *entries)
{
	GIT_UNUSED(entries);

	return (entry->written == 0 &&
		entry->merge_head->remote_url == NULL &&
		entry->merge_head->ref_name != NULL &&
		git__strncmp(GIT_REFS_REMOTES_DIR, entry->merge_head->ref_name, strlen(GIT_REFS_REMOTES_DIR)) == 0);
}

static int msg_entry_is_tag(
	const struct merge_msg_entry *entry,
	git_vector *entries)
{
	GIT_UNUSED(entries);

	return (entry->written == 0 &&
		entry->merge_head->remote_url == NULL &&
		entry->merge_head->ref_name != NULL &&
		git__strncmp(GIT_REFS_TAGS_DIR, entry->merge_head->ref_name, strlen(GIT_REFS_TAGS_DIR)) == 0);
}

static int msg_entry_is_remote(
	const struct merge_msg_entry *entry,
	git_vector *entries)
{
	if (entry->written == 0 &&
		entry->merge_head->remote_url != NULL &&
		entry->merge_head->ref_name != NULL &&
		git__strncmp(GIT_REFS_HEADS_DIR, entry->merge_head->ref_name, strlen(GIT_REFS_HEADS_DIR)) == 0)
	{
		struct merge_msg_entry *existing;

		/* Match only branches from the same remote */
		if (entries->length == 0)
			return 1;

		existing = git_vector_get(entries, 0);

		return (git__strcmp(existing->merge_head->remote_url,
			entry->merge_head->remote_url) == 0);
	}

	return 0;
}

static int msg_entry_is_oid(
	const struct merge_msg_entry *merge_msg_entry)
{
	return (merge_msg_entry->written == 0 &&
		merge_msg_entry->merge_head->ref_name == NULL &&
		merge_msg_entry->merge_head->remote_url == NULL);
}

static int merge_msg_entry_written(
	const struct merge_msg_entry *merge_msg_entry)
{
	return (merge_msg_entry->written == 1);
}

static int merge_msg_entries(
	git_vector *v,
	const struct merge_msg_entry *entries,
	size_t len,
	int (*match)(const struct merge_msg_entry *entry, git_vector *entries))
{
	size_t i;
	int matches, total = 0;

	git_vector_clear(v);

	for (i = 0; i < len; i++) {
		if ((matches = match(&entries[i], v)) < 0)
			return matches;
		else if (!matches)
			continue;

		git_vector_insert(v, (struct merge_msg_entry *)&entries[i]);
		total++;
	}

	return total;
}

static int merge_msg_write_entries(
	git_filebuf *file,
	git_vector *entries,
	const char *item_name,
	const char *item_plural_name,
	size_t ref_name_skip,
	const char *source,
	char sep)
{
	struct merge_msg_entry *entry;
	size_t i;
	int error = 0;

	if (entries->length == 0)
		return 0;

	if (sep && (error = git_filebuf_printf(file, "%c ", sep)) < 0)
		goto done;

	if ((error = git_filebuf_printf(file, "%s ",
		(entries->length == 1) ? item_name : item_plural_name)) < 0)
		goto done;

	git_vector_foreach(entries, i, entry) {
		if (i > 0 &&
			(error = git_filebuf_printf(file, "%s", (i == entries->length - 1) ? " and " : ", ")) < 0)
			goto done;

		if ((error = git_filebuf_printf(file, "'%s'", entry->merge_head->ref_name + ref_name_skip)) < 0)
			goto done;

		entry->written = 1;
	}

	if (source)
		error = git_filebuf_printf(file, " of %s", source);

done:
	return error;
}

static int merge_msg_write_branches(
	git_filebuf *file,
	git_vector *entries,
	char sep)
{
	return merge_msg_write_entries(file, entries,
		"branch", "branches", strlen(GIT_REFS_HEADS_DIR), NULL, sep);
}

static int merge_msg_write_tracking(
	git_filebuf *file,
	git_vector *entries,
	char sep)
{
	return merge_msg_write_entries(file, entries,
		"remote-tracking branch", "remote-tracking branches", 0, NULL, sep);
}

static int merge_msg_write_tags(
	git_filebuf *file,
	git_vector *entries,
	char sep)
{
	return merge_msg_write_entries(file, entries,
		"tag", "tags", strlen(GIT_REFS_TAGS_DIR), NULL, sep);
}

static int merge_msg_write_remotes(
	git_filebuf *file,
	git_vector *entries,
	char sep)
{
	const char *source;

	if (entries->length == 0)
		return 0;

	source = ((struct merge_msg_entry *)entries->contents[0])->merge_head->remote_url;

	return merge_msg_write_entries(file, entries,
		"branch", "branches", strlen(GIT_REFS_HEADS_DIR), source, sep);
}

static int write_merge_msg(
	git_repository *repo,
	const git_merge_head *heads[],
	size_t heads_len)
{
	git_filebuf file = GIT_FILEBUF_INIT;
	git_buf file_path = GIT_BUF_INIT;
	char oid_str[GIT_OID_HEXSZ + 1];
	struct merge_msg_entry *entries;
	git_vector matching = GIT_VECTOR_INIT;
	size_t i;
	char sep = 0;
	int error = 0;

	assert(repo && heads);

	entries = git__calloc(heads_len, sizeof(struct merge_msg_entry));
	GITERR_CHECK_ALLOC(entries); 

	if (git_vector_init(&matching, heads_len, NULL) < 0)
		return -1;

	for (i = 0; i < heads_len; i++)
		entries[i].merge_head = heads[i];

	if ((error = git_buf_joinpath(&file_path, repo->path_repository, GIT_MERGE_MSG_FILE)) < 0 ||
		(error = git_filebuf_open(&file, file_path.ptr, GIT_FILEBUF_FORCE)) < 0 ||
		(error = git_filebuf_write(&file, "Merge ", 6)) < 0)
		goto cleanup;

	/*
	 * This is to emulate the format of MERGE_MSG by core git.
	 *
	 * Core git will write all the commits specified by OID, in the order
	 * provided, until the first named branch or tag is reached, at which
	 * point all branches will be written in the order provided, then all
	 * tags, then all remote tracking branches and finally all commits that
	 * were specified by OID that were not already written.
	 *
	 * Yes.  Really.
	 */
	for (i = 0; i < heads_len; i++) {
		if (!msg_entry_is_oid(&entries[i]))
			break;

		git_oid_fmt(oid_str, &entries[i].merge_head->oid);
		oid_str[GIT_OID_HEXSZ] = '\0';

		if ((error = git_filebuf_printf(&file, "%scommit '%s'", (i > 0) ? "; " : "", oid_str)) < 0)
			goto cleanup;

		entries[i].written = 1;
	}

	if (i)
		sep = ';';

	if ((error = merge_msg_entries(&matching, entries, heads_len, msg_entry_is_branch)) < 0 ||
		(error = merge_msg_write_branches(&file, &matching, sep)) < 0)
		goto cleanup;

	if (matching.length)
		sep =',';

	if ((error = merge_msg_entries(&matching, entries, heads_len, msg_entry_is_tracking)) < 0 ||
		(error = merge_msg_write_tracking(&file, &matching, sep)) < 0)
		goto cleanup;

	if (matching.length)
		sep =',';
	
	if ((error = merge_msg_entries(&matching, entries, heads_len, msg_entry_is_tag)) < 0 ||
		(error = merge_msg_write_tags(&file, &matching, sep)) < 0)
		goto cleanup;

	if (matching.length)
		sep =',';

	/* We should never be called with multiple remote branches, but handle
	 * it in case we are... */
	while ((error = merge_msg_entries(&matching, entries, heads_len, msg_entry_is_remote)) > 0) {
		if ((error = merge_msg_write_remotes(&file, &matching, sep)) < 0)
			goto cleanup;

		if (matching.length)
			sep =',';
	}

	if (error < 0)
		goto cleanup;

	for (i = 0; i < heads_len; i++) {
		if (merge_msg_entry_written(&entries[i]))
			continue;

		git_oid_fmt(oid_str, &entries[i].merge_head->oid);
		oid_str[GIT_OID_HEXSZ] = '\0';

		if ((error = git_filebuf_printf(&file, "; commit '%s'", oid_str)) < 0)
			goto cleanup;
	}

	if ((error = git_filebuf_printf(&file, "\n")) < 0 ||
		(error = git_filebuf_commit(&file, 0666)) < 0)
		goto cleanup;

cleanup:
	if (error < 0)
		git_filebuf_cleanup(&file);

	git_buf_free(&file_path);

	git_vector_free(&matching);
	git__free(entries);

	return error;
}

int git_merge__setup(
	git_repository *repo,
	const git_merge_head *our_head,
	const git_merge_head *heads[],
	size_t heads_len,
	unsigned int flags)
{
	int error = 0;

	assert (repo && our_head && heads);
	
	if ((error = write_orig_head(repo, our_head)) == 0 &&
		(error = write_merge_head(repo, heads, heads_len)) == 0 &&
		(error = write_merge_mode(repo, flags)) == 0) {
		error = write_merge_msg(repo, heads, heads_len);
	}

	return error;
}

int git_repository_merge_cleanup(git_repository *repo)
{
	int error = 0;
	git_buf merge_head_path = GIT_BUF_INIT,
		merge_mode_path = GIT_BUF_INIT,
		merge_msg_path = GIT_BUF_INIT;

	assert(repo);

	if (git_buf_joinpath(&merge_head_path, repo->path_repository, GIT_MERGE_HEAD_FILE) < 0 ||
		git_buf_joinpath(&merge_mode_path, repo->path_repository, GIT_MERGE_MODE_FILE) < 0 ||
		git_buf_joinpath(&merge_msg_path, repo->path_repository, GIT_MERGE_MSG_FILE) < 0)
		return -1;

	if (git_path_isfile(merge_head_path.ptr)) {
		if ((error = p_unlink(merge_head_path.ptr)) < 0)
			goto cleanup;
	}

	if (git_path_isfile(merge_mode_path.ptr))
		(void)p_unlink(merge_mode_path.ptr);

	if (git_path_isfile(merge_msg_path.ptr))
		(void)p_unlink(merge_msg_path.ptr);

cleanup:
	git_buf_free(&merge_msg_path);
	git_buf_free(&merge_mode_path);
	git_buf_free(&merge_head_path);

	return error;
}

/* Merge heads are the input to merge */

static int merge_head_init(
	git_merge_head **out,
	git_repository *repo,
	const char *ref_name,
	const char *remote_url,
	const git_oid *oid)
{
	git_merge_head *head;
	int error = 0;

	assert(out && oid);

	*out = NULL;

	head = git__calloc(1, sizeof(git_merge_head));
	GITERR_CHECK_ALLOC(head);

	if (ref_name) {
		head->ref_name = git__strdup(ref_name);
		GITERR_CHECK_ALLOC(head->ref_name);
	}

	if (remote_url) {
		head->remote_url = git__strdup(remote_url);
		GITERR_CHECK_ALLOC(head->remote_url);
	}

	git_oid_cpy(&head->oid, oid);

	if ((error = git_commit_lookup(&head->commit, repo, &head->oid)) < 0) {
		git_merge_head_free(head);
		return error;
	}

	*out = head;
	return error;
}

int git_merge_head_from_ref(
	git_merge_head **out,
	git_repository *repo,
	git_reference *ref)
{
	git_reference *resolved;
	int error = 0;

	assert(out && repo && ref);

	*out = NULL;

	if ((error = git_reference_resolve(&resolved, ref)) < 0)
		return error;
	
	error = merge_head_init(out, repo, git_reference_name(ref), NULL,
		git_reference_target(resolved));

	git_reference_free(resolved);
	return error;
}

int git_merge_head_from_oid(
	git_merge_head **out,
	git_repository *repo,
	const git_oid *oid)
{
	assert(out && repo && oid);

	return merge_head_init(out, repo, NULL, NULL, oid);
}

int git_merge_head_from_fetchhead(
	git_merge_head **out,
	git_repository *repo,
	const char *branch_name,
	const char *remote_url,
	const git_oid *oid)
{
	assert(repo && branch_name && remote_url && oid);

	return merge_head_init(out, repo, branch_name, remote_url, oid);
}

void git_merge_head_free(git_merge_head *head)
{
	if (head == NULL)
		return;

	if (head->commit != NULL)
		git_object_free((git_object *)head->commit);

	if (head->ref_name != NULL)
		git__free(head->ref_name);

	if (head->remote_url != NULL)
		git__free(head->remote_url);

	git__free(head);
}

/* Merge setup */

static int write_orig_head_old(git_repository *repo, const git_merge_head_old *our_head)
{
	git_filebuf orig_head_file = GIT_FILEBUF_INIT;
	git_buf orig_head_path = GIT_BUF_INIT;
	char orig_oid_str[GIT_OID_HEXSZ + 1];
	int error = 0;

	assert(repo && our_head);

	git_oid_tostr(orig_oid_str, GIT_OID_HEXSZ+1, &our_head->oid);

	if ((error = git_buf_joinpath(&orig_head_path, repo->path_repository, GIT_ORIG_HEAD_FILE)) == 0 &&
		(error = git_filebuf_open(&orig_head_file, orig_head_path.ptr, GIT_FILEBUF_FORCE)) == 0 &&
		(error = git_filebuf_printf(&orig_head_file, "%s\n", orig_oid_str)) == 0)
		error = git_filebuf_commit(&orig_head_file, MERGE_CONFIG_FILE_MODE);

	if (error < 0)
		git_filebuf_cleanup(&orig_head_file);

	git_buf_free(&orig_head_path);

	return error;
}

static int write_merge_head_old(git_repository *repo, const git_merge_head_old *their_heads[], size_t their_heads_len)
{
	git_filebuf merge_head_file = GIT_FILEBUF_INIT;
	git_buf merge_head_path = GIT_BUF_INIT;
	char merge_oid_str[GIT_OID_HEXSZ + 1];
	size_t i;
	int error = 0;

	assert(repo && their_heads);

	if ((error = git_buf_joinpath(&merge_head_path, repo->path_repository, GIT_MERGE_HEAD_FILE)) < 0 ||
		(error = git_filebuf_open(&merge_head_file, merge_head_path.ptr, GIT_FILEBUF_FORCE)) < 0)
		goto cleanup;

	for (i = 0; i < their_heads_len; i++) {
		git_oid_tostr(merge_oid_str, GIT_OID_HEXSZ+1, &their_heads[i]->oid);

		if ((error = git_filebuf_printf(&merge_head_file, "%s\n", merge_oid_str)) < 0)
			goto cleanup;
	}

	error = git_filebuf_commit(&merge_head_file, MERGE_CONFIG_FILE_MODE);

cleanup:
	if (error < 0)
		git_filebuf_cleanup(&merge_head_file);

	git_buf_free(&merge_head_path);

	return error;
}

static int write_merge_mode_old(git_repository *repo, unsigned int flags)
{
	git_filebuf merge_mode_file = GIT_FILEBUF_INIT;
	git_buf merge_mode_path = GIT_BUF_INIT;
	int error = 0;

	assert(repo);

	if ((error = git_buf_joinpath(&merge_mode_path, repo->path_repository, GIT_MERGE_MODE_FILE)) < 0 ||
		(error = git_filebuf_open(&merge_mode_file, merge_mode_path.ptr, GIT_FILEBUF_FORCE)) < 0)
		goto cleanup;

	/*
	 * TODO: no-ff is the only thing allowed here at present.  One would
	 * presume they would be space-delimited when there are more, but
	 * this needs to be revisited.
	 */
	
	if (flags & GIT_MERGE_NO_FASTFORWARD) {
		if ((error = git_filebuf_write(&merge_mode_file, "no-ff", 5)) < 0)
			goto cleanup;
	}

	error = git_filebuf_commit(&merge_mode_file, MERGE_CONFIG_FILE_MODE);

cleanup:
	if (error < 0)
		git_filebuf_cleanup(&merge_mode_file);

	git_buf_free(&merge_mode_path);

	return error;
}

static int write_merge_msg_old(git_repository *repo, const git_merge_head_old *their_heads[], size_t their_heads_len)
{
	git_filebuf merge_msg_file = GIT_FILEBUF_INIT;
	git_buf merge_msg_path = GIT_BUF_INIT;
	char merge_oid_str[GIT_OID_HEXSZ + 1];
	size_t i, j;
    bool *wrote;
	int error = 0;

	assert(repo && their_heads);

    if ((wrote = git__calloc(their_heads_len, sizeof(bool))) == NULL)
        return -1;
    
	if ((error = git_buf_joinpath(&merge_msg_path, repo->path_repository, GIT_MERGE_MSG_FILE)) < 0 ||
		(error = git_filebuf_open(&merge_msg_file, merge_msg_path.ptr, GIT_FILEBUF_FORCE)) < 0 ||
		(error = git_filebuf_write(&merge_msg_file, "Merge", 5)) < 0)
		goto cleanup;

    /*
     * This is to emulate the format of MERGE_MSG by core git.
     *
     * Yes.  Really.
     */
    for (i = 0; i < their_heads_len; i++) {
        if (wrote[i])
            continue;
        
        /* At the first branch, write all the branches */
        if (their_heads[i]->branch_name != NULL) {
            bool multiple_branches = 0;
            size_t last_branch_idx = i;
            
            for (j = i+1; j < their_heads_len; j++) {
                if (their_heads[j]->branch_name != NULL) {
                    multiple_branches = 1;
                    last_branch_idx = j;
                }
            }
            
            if ((error = git_filebuf_printf(&merge_msg_file, "%s %s", (i > 0) ? ";" : "", multiple_branches ? "branches" : "branch")) < 0)
                goto cleanup;
            
            for (j = i; j < their_heads_len; j++) {
                if (their_heads[j]->branch_name == NULL)
                    continue;
                
                if (j > i) {
                    if ((error = git_filebuf_printf(&merge_msg_file, "%s", (last_branch_idx == j) ? " and" : ",")) < 0)
                        goto cleanup;
                }
                
                if ((error = git_filebuf_printf(&merge_msg_file, " '%s'", their_heads[j]->branch_name)) < 0)
                    goto cleanup;
                
                wrote[j] = 1;
            }
        } else {
            git_oid_fmt(merge_oid_str, &their_heads[i]->oid);
            merge_oid_str[GIT_OID_HEXSZ] = '\0';
            
            if ((error = git_filebuf_printf(&merge_msg_file, "%s commit '%s'", (i > 0) ? ";" : "", merge_oid_str)) < 0)
                goto cleanup;
        }
    }

	if ((error = git_filebuf_printf(&merge_msg_file, "\n")) < 0 ||
		(error = git_filebuf_commit(&merge_msg_file, MERGE_CONFIG_FILE_MODE)) < 0)
		goto cleanup;

cleanup:
	if (error < 0)
		git_filebuf_cleanup(&merge_msg_file);

	git_buf_free(&merge_msg_path);
    git__free(wrote);

	return error;
}

static int merge_conflict_write_diff3(int *conflict_written,
	git_repository *repo,
	const git_merge_head_old *ancestor_head,
	const git_merge_head_old *our_head,
	const git_merge_head_old *their_head,
	const git_diff_tree_delta *delta,
	unsigned int flags)
{
	git_odb *odb = NULL;
	merge_filediff_result result = MERGE_FILEDIFF_RESULT_INIT;
	git_merge_head_old const *merge_heads[3] = { ancestor_head, our_head, their_head };
	git_buf workdir_path = GIT_BUF_INIT;
	git_filebuf output = GIT_FILEBUF_INIT;
	int error = 0;
	
	assert(conflict_written && repo && ancestor_head && our_head && their_head && delta);
	
	*conflict_written = 0;
	
	if (flags & GIT_MERGE_CONFLICT_NO_DIFF3)
		return 0;

	/* Reject link/file conflicts. */
	if ((S_ISLNK(delta->ancestor.file.mode) ^ S_ISLNK(delta->ours.file.mode)) ||
		(S_ISLNK(delta->ancestor.file.mode) ^ S_ISLNK(delta->theirs.file.mode)))
		return 0;
	
	/* Reject D/F conflicts */
	if (delta->df_conflict == GIT_DIFF_TREE_DF_DIRECTORY_FILE)
		return 0;

	/* TODO: reject name conflicts? */
	
	git_repository_odb(&odb, repo);
	
	/* TODO: mkpath2file mode */
	if (!GIT_DIFF_TREE_FILE_EXISTS(delta->ours) || !GIT_DIFF_TREE_FILE_EXISTS(delta->theirs) ||
		(error = git_repository_odb(&odb, repo)) < 0 ||
		(error = merge_filediff(&result, odb, merge_heads, delta, 0)) < 0 ||
		result.path == NULL || result.mode == 0 ||
		(error = git_buf_joinpath(&workdir_path, git_repository_workdir(repo), result.path)) < 0 ||
		(error = git_futils_mkpath2file(workdir_path.ptr, 0755) < 0) ||
		(error = git_filebuf_open(&output, workdir_path.ptr, GIT_FILEBUF_DO_NOT_BUFFER)) < 0 ||
		(error = git_filebuf_write(&output, result.data, result.len)) < 0 ||
		(error = git_filebuf_commit(&output, result.mode)) < 0)
		goto done;
	
	*conflict_written = 1;

done:
	merge_filediff_result_free(&result);
	git_odb_free(odb);
	git_buf_free(&workdir_path);
	
	return error;
}

static int merge_conflict_write_file(
	git_repository *repo,
	const git_diff_tree_entry *entry,
	const char *path)
{
	git_checkout_opts opts = GIT_CHECKOUT_OPTS_INIT;
	
	opts.file_open_flags =  O_WRONLY | O_CREAT | O_TRUNC | O_EXCL;
	
	if (path == NULL)
		path = entry->file.path;

	return git_checkout_blob(repo, &entry->file.oid, path, entry->file.mode, &opts);
}

static int merge_conflict_write_side(
	git_repository *repo,
	const git_merge_head_old *merge_head,
	const git_diff_tree_delta *delta,
	const git_diff_tree_entry *entry,
	unsigned int flags)
{
	const char *path = entry->file.path;
	git_buf path_with_branch = GIT_BUF_INIT;
	char oid_str[GIT_OID_HEXSZ];
	int error = 0;
	
	assert(repo && merge_head && entry);
	
	/* TODO: what if this file exists? */

	/* 
	 * Mutate the name if we're D/F conflicted or if we didn't write a diff3
	 * file.
	 */
	if (delta->df_conflict == GIT_DIFF_TREE_DF_DIRECTORY_FILE ||
		(flags & GIT_MERGE_CONFLICT_NO_DIFF3)) {
		git_buf_puts(&path_with_branch, entry->file.path);
		git_buf_putc(&path_with_branch, '~');
		
		if (merge_head->branch_name)
			git_buf_puts(&path_with_branch, merge_head->branch_name);
		else {
			git_oid_fmt(oid_str, &merge_head->oid);
			git_buf_put(&path_with_branch, oid_str, GIT_OID_HEXSZ);
		}
		
		path = git_buf_cstr(&path_with_branch);
	}

	error = merge_conflict_write_file(repo, entry, path);

	git_buf_free(&path_with_branch);
	
	return error;
}

static int merge_conflict_write_sides(
	int *conflict_written,
	git_repository *repo,
	const git_merge_head_old *ancestor_head,
	const git_merge_head_old *our_head,
	const git_merge_head_old *their_head,
	const git_diff_tree_delta *delta,
	unsigned int flags)
{
	int error = 0;
	
	GIT_UNUSED(flags);

	assert(conflict_written && repo && ancestor_head && our_head && their_head && delta);
	
	*conflict_written = 0;
	
	if (GIT_DIFF_TREE_FILE_EXISTS(delta->ours) &&
		(error = merge_conflict_write_side(repo, our_head, delta, &delta->ours, flags)) < 0)
		goto done;
	
	if (GIT_DIFF_TREE_FILE_EXISTS(delta->theirs) &&
		(error = merge_conflict_write_side(repo, their_head, delta, &delta->theirs, flags)) < 0)
		goto done;

done:
	if (error >= 0)
		*conflict_written = 1;

	return error;
}

static int merge_conflict_write(int *out,
	git_repository *repo,
	const git_merge_head_old *ancestor_head,
	const git_merge_head_old *our_head,
	const git_merge_head_old *their_head,
	const git_diff_tree_delta *delta,
	unsigned int flags)
{
	int conflict_written = 0;
	int error = 0;

	assert(out && repo && ancestor_head && our_head && their_head && delta);
	
	*out = 0;

	if ((error = merge_conflict_write_diff3(&conflict_written, repo, ancestor_head,
		our_head, their_head, delta, flags)) < 0)
		goto done;

	if (!conflict_written)
		error = merge_conflict_write_sides(&conflict_written, repo, ancestor_head,
			our_head, their_head, delta, flags);

	*out = conflict_written;

done:
	return error;
}

int git_merge__setup_old(
	git_repository *repo,
	const git_merge_head_old *our_head,
    const git_merge_head_old *their_heads[],
	size_t their_heads_len,
	unsigned int flags)
{
	int error = 0;

	assert (repo && our_head && their_heads);
	
	if ((error = write_orig_head_old(repo, our_head)) == 0 &&
		(error = write_merge_head_old(repo, their_heads, their_heads_len)) == 0 &&
		(error = write_merge_mode_old(repo, flags)) == 0) {
		error = write_merge_msg_old(repo, their_heads, their_heads_len);
	}

	return error;
}

/* Merge branches */

static int merge_ancestor_head(
	git_merge_head_old **ancestor_head,
	git_repository *repo,
	const git_merge_head_old *our_head,
	const git_merge_head_old **their_heads,
	size_t their_heads_len)
{
	git_oid *oids, ancestor_oid;
	size_t i;
	int error = 0;
	
	assert(repo && our_head && their_heads);
	
	oids = git__calloc(their_heads_len + 1, sizeof(git_oid));
	GITERR_CHECK_ALLOC(oids);
	
	git_oid_cpy(&oids[0], git_commit_id(our_head->commit));

	for (i = 0; i < their_heads_len; i++)
		git_oid_cpy(&oids[i + 1], &their_heads[i]->oid);
	
	if ((error = git_merge_base_many(&ancestor_oid, repo, oids, their_heads_len + 1)) < 0)
		goto on_error;

	error = git_merge_head_from_oid_old(ancestor_head, repo, &ancestor_oid);

on_error:
	git__free(oids);
	return error;
}

GIT_INLINE(bool) merge_check_uptodate(
	git_merge_result *result,
	const git_merge_head_old *our_head,
	const git_merge_head_old *their_head)
{
	if (git_oid_cmp(&our_head->oid, &their_head->oid) == 0) {
		result->is_uptodate = 1;
		return true;
	}
	
	return false;
}

GIT_INLINE(bool) merge_check_fastforward(
	git_merge_result *result,
	const git_merge_head_old *ancestor_head,
	const git_merge_head_old *our_head,
	const git_merge_head_old *their_head,
	unsigned int flags)
{
	if ((flags & GIT_MERGE_NO_FASTFORWARD) == 0 &&
		git_oid_cmp(&ancestor_head->oid, &our_head->oid) == 0) {
		result->is_fastforward = 1;
		git_oid_cpy(&result->fastforward_oid, &their_head->oid);
		
		return true;
	}
	
	return false;
}

static int merge_normalize_opts(
	git_merge_opts *opts,
	const git_merge_opts *given)
{
	int error = 0;
	unsigned int default_checkout_strategy = GIT_CHECKOUT_SAFE |
		GIT_CHECKOUT_SAFE_CREATE |
		GIT_CHECKOUT_REMOVE_UNTRACKED |
		GIT_CHECKOUT_ALLOW_CONFLICTS;

	if (given != NULL) {
		memcpy(opts, given, sizeof(git_merge_opts));

		if (!opts->checkout_opts.checkout_strategy)
			opts->checkout_opts.checkout_strategy = default_checkout_strategy;

		error = merge_trees_normalize_opts(&opts->merge_trees_opts, &given->merge_trees_opts);
	} else {
		git_merge_opts default_opts = GIT_MERGE_OPTS_INIT;
		memcpy(opts, &default_opts, sizeof(git_merge_opts));
		
		opts->checkout_opts.checkout_strategy = default_checkout_strategy;

		error = merge_trees_normalize_opts(&opts->merge_trees_opts, NULL);
	}

	return error;
}

int git_merge(
	git_merge_result **out,
	git_repository *repo,
	const git_merge_head_old **their_heads,
	size_t their_heads_len,
	const git_merge_opts *given_opts)
{
	git_merge_result *result;
	git_merge_opts opts;
	git_reference *our_ref = NULL;
	git_merge_head_old *ancestor_head = NULL, *our_head = NULL;
	git_tree *ancestor_tree = NULL, *our_tree = NULL, **their_trees = NULL;
	git_index *index;
	git_diff_tree_delta *delta;
	size_t i;
	int error = 0;

	assert(out && repo && their_heads);
	
	*out = NULL;
	
	result = git__calloc(1, sizeof(git_merge_result));
	GITERR_CHECK_ALLOC(result);
	
	their_trees = git__calloc(their_heads_len, sizeof(git_tree *));
	GITERR_CHECK_ALLOC(their_trees);
	
	if (merge_normalize_opts(&opts, given_opts) < 0)
		goto on_error;
	
	if ((error = git_repository__ensure_not_bare(repo, "merge")) < 0)
		goto on_error;
	
	if ((error = git_reference_lookup(&our_ref, repo, GIT_HEAD_FILE)) < 0 ||
		(error = git_merge_head_from_ref_old(&our_head, repo, our_ref)) < 0 ||
		(error = merge_ancestor_head(&ancestor_head, repo, our_head, their_heads, their_heads_len)) < 0)
		goto on_error;
	
	if (their_heads_len == 1 &&
		(merge_check_uptodate(result, our_head, their_heads[0]) ||
		merge_check_fastforward(result, ancestor_head, our_head, their_heads[0], opts.merge_flags))) {
		*out = result;
		goto done;
	}
	
	/* Write the merge files to the repository. */
	if ((error = git_merge__setup_old(repo, our_head, their_heads, their_heads_len, opts.merge_flags)) < 0)
		goto on_error;
	
	if ((error = git_commit_tree(&ancestor_tree, ancestor_head->commit)) < 0 ||
		(error = git_commit_tree(&our_tree, our_head->commit)) < 0)
		goto on_error;
	
	for (i = 0; i < their_heads_len; i++) {
		if ((error = git_commit_tree(&their_trees[i], their_heads[i]->commit)) < 0)
			goto on_error;
	}

	if ((error = git_repository_index__weakptr(&index, repo)) < 0)
		goto on_error;
	
	/* TODO: recursive */
	if (their_heads_len == 1)
		error = merge_trees(result, repo, index, ancestor_tree, our_tree,
			their_trees[0], &opts.merge_trees_opts);
	else
		error = merge_trees_octopus(result, repo, index, ancestor_tree, our_tree,
			(const git_tree **)their_trees, their_heads_len, &opts.merge_trees_opts);
	
	if (error < 0)
		goto on_error;
	
	/* TODO: hack to workaround checkout dir/file stuff */
	if ((error = git_checkout_index(repo, index, &opts.checkout_opts)) < 0 ||
		(error = git_checkout_index(repo, index, &opts.checkout_opts)) < 0 ||
		(error = git_index_write(index)) < 0)
		goto on_error;
	
	if (their_heads_len == 1) {
		git_vector_foreach(&result->conflicts, i, delta) {
			int conflict_written = 0;
			
			if ((error = merge_conflict_write(&conflict_written, repo,
				ancestor_head, our_head, their_heads[0], delta, opts.conflict_flags)) < 0)
				goto on_error;
		}
	}
	
	*out = result;
	goto done;
	
on_error:
	git__free(result);

done:
	git_tree_free(ancestor_tree);
	git_tree_free(our_tree);
	
	for (i = 0; i < their_heads_len; i++)
		git_tree_free(their_trees[i]);
	
	git__free(their_trees);
	
	git_merge_head_free_old(our_head);
	git_merge_head_free_old(ancestor_head);
	
	git_reference_free(our_ref);

	return error;
}

/* Merge result data */

int git_merge_result_is_uptodate(git_merge_result *merge_result)
{
	assert(merge_result);
	
	return merge_result->is_uptodate;
}

int git_merge_result_is_fastforward(git_merge_result *merge_result)
{
	assert(merge_result);

	return merge_result->is_fastforward;
}

int git_merge_result_fastforward_oid(git_oid *out, git_merge_result *merge_result)
{
	assert(out && merge_result);

	git_oid_cpy(out, &merge_result->fastforward_oid);
	return 0;
}

int git_merge_result_delta_foreach(git_merge_result *merge_result,
	git_diff_tree_delta_cb delta_cb,
	void *payload)
{
	git_diff_tree_delta *delta;
	size_t i;
	int error = 0;
	
	assert(merge_result && delta_cb);
	
	git_vector_foreach(&merge_result->conflicts, i, delta) {
		if (delta_cb(delta, payload) != 0) {
			error = GIT_EUSER;
			break;
		}
	}
	
	return error;
}

int git_merge_result_conflict_foreach(git_merge_result *merge_result,
	git_diff_tree_delta_cb conflict_cb,
	void *payload)
{
	git_diff_tree_delta *delta;
	size_t i;
	int error = 0;
	
	assert(merge_result && conflict_cb);
	
	git_vector_foreach(&merge_result->conflicts, i, delta) {
		if (conflict_cb(delta, payload) != 0) {
			error = GIT_EUSER;
			break;
		}
	}
	
	return error;
}

void git_merge_result_free(git_merge_result *merge_result)
{
	if (merge_result == NULL)
		return;
	
	git_vector_free(&merge_result->conflicts);
	
	git_diff_tree_list_free(merge_result->diff_tree);
	merge_result->diff_tree = NULL;

	git__free(merge_result);
}

/* git_merge_head functions
 * from old repo
 */

static int merge_head_init_old(git_merge_head_old **out,
	git_repository *repo,
	const char *branch_name,
	const git_oid *oid)
{
    git_merge_head_old *head;
	int error = 0;
    
    assert(out && oid);
    
    *out = NULL;

    head = git__calloc(1, sizeof(git_merge_head));
    GITERR_CHECK_ALLOC(head);

    if (branch_name) {
        head->branch_name = git__strdup(branch_name);
        GITERR_CHECK_ALLOC(head->branch_name);
    }
    
    git_oid_cpy(&head->oid, oid);

	if ((error = git_commit_lookup(&head->commit, repo, &head->oid)) < 0) {
		git_merge_head_free_old(head);
		return error;
	}
    
    *out = head;
    return error;
}

int git_merge_head_from_ref_old(git_merge_head_old **out,
	git_repository *repo,
	git_reference *ref)
{
    git_reference *resolved;
    char const *ref_name = NULL;
    int error = 0;
    
    assert(out && ref);
    
    *out = NULL;
    
    if ((error = git_reference_resolve(&resolved, ref)) < 0)
        return error;
	
	ref_name = git_reference_name(ref);
	
	if (git__prefixcmp(ref_name, GIT_REFS_HEADS_DIR) == 0)
        ref_name += strlen(GIT_REFS_HEADS_DIR);

    error = merge_head_init_old(out, repo, ref_name, git_reference_target(resolved));

    git_reference_free(resolved);
    return error;
}

int git_merge_head_from_oid_old(git_merge_head_old **out,
	git_repository *repo,
	const git_oid *oid)
{
    return merge_head_init_old(out, repo, NULL, oid);
}

void git_merge_head_free_old(git_merge_head_old *head)
{
    if (head == NULL)
        return;

	if (head->commit != NULL)
		git_object_free((git_object *)head->commit);
    
    if (head->branch_name != NULL)
        git__free(head->branch_name);
    
    git__free(head);
}
