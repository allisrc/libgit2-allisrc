/*
 * Copyright (C) the libgit2 contributors. All rights reserved.
 *
 * This file is part of libgit2, distributed under the GNU GPL v2 with
 * a Linking Exception. For full terms see the included COPYING file.
 */

#include "git2.h"
#include "smart.h"
#include "git2/cred_helpers.h"

static void plaintext_free(struct git_cred *cred)
{
	git_cred_userpass_plaintext *c = (git_cred_userpass_plaintext *)cred;
	size_t pass_len = strlen(c->password);

	git__free(c->username);

	/* Zero the memory which previously held the password */
	memset(c->password, 0x0, pass_len);
	git__free(c->password);

	memset(c, 0, sizeof(*c));

	git__free(c);
}

int git_cred_userpass_plaintext_new(
	git_cred **cred,
	const char *username,
	const char *password)
{
	git_cred_userpass_plaintext *c;

	if (!cred)
		return -1;

	c = git__malloc(sizeof(git_cred_userpass_plaintext));
	GITERR_CHECK_ALLOC(c);

	c->parent.credtype = GIT_CREDTYPE_USERPASS_PLAINTEXT;
	c->parent.free = plaintext_free;
	c->username = git__strdup(username);

	if (!c->username) {
		git__free(c);
		return -1;
	}

	c->password = git__strdup(password);

	if (!c->password) {
		git__free(c->username);
		git__free(c);
		return -1;
	}

	*cred = &c->parent;
	return 0;
}

#ifdef GIT_SSH
static void ssh_password_free(git_cred *cred)
{
	git_cred_ssh_password *c = (git_cred_ssh_password *)cred;
	int pass_len = strlen(c->password);

	git__free(c->username);

	/* Zero the memory which previously held the password */
	memset(c->password, 0x0, pass_len);
	git__free(c->password);

	git__free(c);
}

int git_cred_ssh_password_new(
	git_cred **cred,
	const char *username,
	const char *password)
{
	git_cred_ssh_password *c;

	if (!cred)
		return -1;

	c = (git_cred_ssh_password *)git__malloc(sizeof(git_cred_ssh_password));
	GITERR_CHECK_ALLOC(c);

	c->parent.credtype = GIT_CREDTYPE_SSH_PASSWORD;
	c->parent.free = ssh_password_free;
	c->username = git__strdup(username);

	if (!c->username) {
		git__free(c);
		return -1;
	}

	c->password = git__strdup(password);

	if (!c->password) {
		git__free(c->username);
		git__free(c);
		return -1;
	}

	*cred = &c->parent;
	return 0;
}

static void ssh_publickey_free(git_cred *cred)
{
	git_cred_ssh_publickey *c = (git_cred_ssh_publickey *)cred;

	if (c->passphrase) {
		int pass_len = strlen(c->passphrase);
		/* Zero the memory which previously held the password */
		memset(c->passphrase, 0x0, pass_len);
		git__free(c->passphrase);
	}

	git__free(c->username);

	git__free(c);
}

int git_cred_ssh_publickey_new(
	git_cred **cred,
	const char *username,
	const char *publickey,
	const char *privatekey,
	const char *passphrase)
{
	git_cred_ssh_publickey *c;

	if (!cred)
		return -1;

	c = (git_cred_ssh_publickey *)git__malloc(sizeof(git_cred_ssh_publickey));
	GITERR_CHECK_ALLOC(c);

	memset(c, 0, sizeof(git_cred_ssh_publickey));
	c->parent.credtype = GIT_CREDTYPE_SSH_PUBLICKEY;
	c->parent.free = ssh_publickey_free;
	c->username = git__strdup(username);

	if (!c->username) {
		git__free(c);
		return -1;
	}

	c->privatekey = git__strdup(privatekey);

	if (!c->privatekey) {
		git__free(c->username);
		git__free(c);
		return -1;
	}

    if (publickey != NULL)
        c->publickey = git__strdup(publickey);
    if (passphrase != NULL)
        c->passphrase = git__strdup(passphrase);

	*cred = &c->parent;
	return 0;
}

#endif
