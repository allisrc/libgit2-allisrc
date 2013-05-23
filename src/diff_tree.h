/*
 * Copyright (C) 2009-2012 the libgit2 contributors
 *
 * This file is part of libgit2, distributed under the GNU GPL v2 with
 * a Linking Exception. For full terms see the included COPYING file.
 */
#ifndef INCLUDE_diff_tree_h__
#define INCLUDE_diff_tree_h__

#include "repository.h"
#include "pool.h"
#include "vector.h"

#define GIT_DIFF_TREE_FILE_EXISTS(X)	((X).file.mode != 0)

struct git_diff_tree_list {
	git_repository *repo;
	git_pool pool;

	git_vector deltas;    /* vector of git_diff_tree_delta */
};

#endif
