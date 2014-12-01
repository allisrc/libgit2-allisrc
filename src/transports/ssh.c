/*
* Copyright (C) 2009-2012 the libgit2 contributors
*
* This file is part of libgit2, distributed under the GNU GPL v2 with
* a Linking Exception. For full terms see the included COPYING file.
*/

#ifdef GIT_SSH

#include <libssh2.h>

#include "git2.h"
#include "buffer.h"
#include "netops.h"
#include "smart.h"

#define OWNING_SUBTRANSPORT(s) ((ssh_subtransport *)(s)->parent.subtransport)

static const char prefix_ssh[] = "ssh://";
static const char cmd_uploadpack[] = "git-upload-pack";
static const char cmd_receivepack[] = "git-receive-pack";
static bool is_socket_zero = false;
static const bool ssh2_nb = true;

#define CHUNK_SIZE 32700

typedef struct {
	git_smart_subtransport_stream parent;
	const char *cmd;
	char *url;
	unsigned sent_command: 1;
} ssh_stream;

typedef struct {
	git_smart_subtransport parent;
	transport_smart *owner;
	ssh_stream *current_stream;
	git_cred *cred;
	char *host;
	char *port;
	char *user_from_url;
	gitno_socket socket;
	unsigned connected: 1;
	LIBSSH2_SESSION *session;
	LIBSSH2_CHANNEL *channel;
} ssh_subtransport;

/*
* Create a git protocol request.
*
* For example: 0035git-upload-pack /libgit2/libgit2\0host=github.com\0
*                  git-receive-pack /libgit2/libgit2\0host=github.com\0
*/
static int gen_proto(git_buf *request, const char *cmd, const char *url)
{
	char *delim, *repo;

	if (!cmd)
		//cmd = cmd_uploadpack;
			return -1;

	delim = strchr(url, '/');
	if (delim == NULL) {
		giterr_set(GITERR_NET, "Malformed URL");
		return -1;
	}

	repo = delim;

	git_buf_grow(request, strlen(cmd) + strlen(repo) + 2);
	git_buf_printf(request, "%s %s", cmd, repo);
	git_buf_putc(request, '\0');

	if (git_buf_oom(request))
		return -1;

	return 0;
}

static int ssh_set_error(LIBSSH2_SESSION *session)
{
	char *error;

	libssh2_session_last_error(session, &error, NULL, 0);
	giterr_set(GITERR_NET, "SSH error: %s", error);

	return -1;
}

static int send_command(ssh_stream *s)
{
	int error;
	git_buf request = GIT_BUF_INIT;
	ssh_subtransport *t = OWNING_SUBTRANSPORT(s);

	error = gen_proto(&request, s->cmd, s->url);
	if (error < 0)
		goto cleanup;

	/* It looks like negative values are errors here, and positive values
	* are the number of bytes sent. */
	if (!ssh2_nb)
		error = libssh2_channel_exec(t->channel, git_buf_cstr(&request));
	else {
		do {
			error = libssh2_channel_exec(t->channel, git_buf_cstr(&request));
		} while (error == LIBSSH2_ERROR_EAGAIN);
	}

	if (error >= 0)
		s->sent_command = 1;

cleanup:
	git_buf_free(&request);
	return error >= 0 ? error : ssh_set_error(t->session);
}

static int ssh_stream_read(
	git_smart_subtransport_stream *stream,
	char *buffer,
	size_t buf_size,
	size_t *bytes_read)
{
	int error;
	ssh_stream *s = (ssh_stream *)stream;
	ssh_subtransport *t = OWNING_SUBTRANSPORT(s);
	gitno_buffer buf;
	struct timeval timeout;
	fd_set fd;

	*bytes_read = 0;

	if (!s->sent_command && send_command(s) < 0)
		return -1;

	gitno_buffer_setup(&t->socket, &buf, buffer, buf_size);

	if (!ssh2_nb) {
		error = libssh2_channel_read(t->channel, buf.data, buf.len);
		if (error < 0)
			return ssh_set_error(t->session);
		else
			buf.offset = error;
	}
	else {
		do {
			error = libssh2_channel_read(t->channel, buf.data, buf.len);
			if (error == LIBSSH2_ERROR_EAGAIN) {
				timeout.tv_sec = 5;
				timeout.tv_usec = 0;

				do {
					FD_ZERO(&fd);
					FD_SET(t->socket.socket, &fd);

					error = select(t->socket.socket + 1, &fd, NULL, NULL, &timeout);
					/* negative is error and zero is timeout */
					if (error <= 0) {
						return error < 0 ? error : LIBSSH2_ERROR_TIMEOUT;
					}
					else if (FD_ISSET(t->socket.socket, &fd))
						break;
					Sleep(500);
				} while (1);
			}
			else if (error >= 0) {
				buf.offset = error;
				goto on_exit;
			}
			else
				return ssh_set_error(t->session);
		} while (1);
	}

on_exit:
	*bytes_read = buf.offset;

	return 0;
}

static int ssh_stream_write(
	git_smart_subtransport_stream *stream,
	const char *buffer,
	size_t len)
{
	ssh_stream *s = (ssh_stream *)stream;
	ssh_subtransport *t = OWNING_SUBTRANSPORT(s);
	int rc;
	int32_t total = 0;
	int32_t left = len;		// object size is limited to 4G bytes.
	const char *unwritten = buffer;
	struct timeval timeout;
	fd_set fd;

	if (!s->sent_command && send_command(s) < 0)
		return -1;

	// send the packet in chunks if it is too big
	if (!ssh2_nb) {
		if (len > CHUNK_SIZE) {
			do {
				rc = libssh2_channel_write(t->channel, unwritten, CHUNK_SIZE > left ? left : CHUNK_SIZE);
				if (rc < 0)
					return rc;
				unwritten += CHUNK_SIZE;
				left -= CHUNK_SIZE;
				total += rc;
			} while (left > 0);
		}
		else {
			total = libssh2_channel_write(t->channel, buffer, len);
		}
	}
	else {
		if (len > CHUNK_SIZE) {
			do {
				do {
					rc = libssh2_channel_write(t->channel, unwritten, CHUNK_SIZE > left ? left : CHUNK_SIZE);
					// condition 1: error and return error
					if (rc < 0 && rc != LIBSSH2_ERROR_EAGAIN)
						return rc;
					// condition 2: EAGAIN, loop
					else if (rc == LIBSSH2_ERROR_EAGAIN) {
						timeout.tv_sec = 5;
						timeout.tv_usec = 0;

						do {
							FD_ZERO(&fd);
							FD_SET(t->socket.socket, &fd);

							rc = select(t->socket.socket + 1, NULL, &fd, NULL, &timeout);
							/* negative is error and zero is timeout */
							if (rc <= 0) {
								return rc < 0 ? rc : LIBSSH2_ERROR_TIMEOUT;
							}
							else if (FD_ISSET(t->socket.socket, &fd))
								break;
							Sleep(500);
						} while (1);
					}
					// condition 3: normal situation, keep writing
					else
						break;
				} while (1);
				unwritten += CHUNK_SIZE;
				left -= CHUNK_SIZE;
				total += rc;
			} while (left > 0);
		}
		else {
			do {
				total = libssh2_channel_write(t->channel, buffer, len);
				// condition 1: error and return error
				if (total < 0 && total != LIBSSH2_ERROR_EAGAIN)
					return total;
				// condition 2: EAGAIN, loop
				else if (total == LIBSSH2_ERROR_EAGAIN) {
					timeout.tv_sec = 5;
					timeout.tv_usec = 0;

					do {
						FD_ZERO(&fd);
						FD_SET(t->socket.socket, &fd);

						total = select(t->socket.socket + 1, NULL, &fd, NULL, &timeout);
						/* negative is error and zero is timeout */
						if (total <= 0) {
							return total < 0 ? total : LIBSSH2_ERROR_TIMEOUT;
						}
						else if (FD_ISSET(t->socket.socket, &fd))
							break;
						Sleep(500);
					} while (1);
				}
				// condition 3: normal situation, keep writing
				else
					break;
			} while (1);
		}
	}

	return total;
}

static void ssh_stream_free(git_smart_subtransport_stream *stream)
{
	ssh_stream *s = (ssh_stream *)stream;

	git__free(s->url);
	git__free(s);
}

static int ssh_stream_alloc(
	git_smart_subtransport_stream **stream,
	ssh_subtransport *t,
	const char *url,
	const char *cmd)
{
	ssh_stream *s;

	if (!stream)
		return -1;

	s = (ssh_stream *)git__calloc(sizeof(ssh_stream), 1);
	GITERR_CHECK_ALLOC(s);

	s->parent.subtransport = &t->parent;
	s->parent.read = ssh_stream_read;
	s->parent.write = ssh_stream_write;
	s->parent.free = ssh_stream_free;

	s->url = git__strdup(url);
	s->cmd = cmd;

	*stream = &s->parent;
	return 0;
}

static int ssh_uploadpack_ls(
	git_smart_subtransport_stream **stream,
	ssh_subtransport *t,
	const char *url)
{
	ssh_stream *s;

	*stream = NULL;

	if (ssh_stream_alloc(stream, t, url, cmd_uploadpack) < 0)
		return -1;

	s = (ssh_stream *)*stream;
	t->current_stream = s;

	return 0;
}

static int ssh_uploadpack(
	git_smart_subtransport_stream **stream,
	ssh_subtransport *t)
{
	if (t->current_stream) {
		*stream = &t->current_stream->parent;
		return 0;
	}

	giterr_set(GITERR_NET, "Must call UPLOADPACK_LS before UPLOADPACK");
	return -1;
}

static int ssh_receivepack_ls(
	git_smart_subtransport_stream **stream,
	ssh_subtransport *t,
	const char *url)
{
	ssh_stream *s;

	*stream = NULL;

	if (ssh_stream_alloc(stream, t, url, cmd_receivepack) < 0)
		return -1;

	s = (ssh_stream *)*stream;
	t->current_stream = s;

	return 0;
}

static int ssh_receivepack(
	git_smart_subtransport_stream **stream,
	ssh_subtransport *t)
{
	if (t->current_stream) {
		*stream = &t->current_stream->parent;
		return 0;
	}

	giterr_set(GITERR_NET, "Must call RECEIVEPACK_LS before RECEIVEPACK");
	return -1;
}

static int ssh_action(
	git_smart_subtransport_stream **stream,
	git_smart_subtransport *smart_transport,
	const char *url,
	git_smart_service_t action)
{
	git_cred_ssh_publickey *c;
	int rc;
	ssh_subtransport *t = (ssh_subtransport *)smart_transport;
	const char *default_port = "22";

	if (!stream)
		return -1;

	if (!git__prefixcmp(url, prefix_ssh))
		url += strlen(prefix_ssh);

	if (!t->host || !t->port) {
		if (gitno_extract_host_and_port(&t->host, &t->port,
			url, default_port) < 0)
			return -1;
	}

	if (!t->connected) {
		if (!t->owner->cred_acquire_cb) {
			giterr_set(GITERR_NET, "No credential callback given");
			return -1;
		}

		// make sure libssh2_init is called only once
		// socket has to be a unique number
		//pthread_mutex_lock(&mutexsum);
		if (gitno_connect(&t->socket, t->host, t->port, 0) < 0)
			return -1;
		if (t->socket.socket == 0) {
			is_socket_zero = true;
		}

		t->session = libssh2_session_init();
		if (t->session == NULL) {
			giterr_set(GITERR_NET, "Failed to init SSH session");
			return -1;
		}

		if (!ssh2_nb)
			libssh2_session_set_blocking(t->session, 1);
		else
			libssh2_session_set_blocking(t->session, 0);

		// explicitly set timeout to 0, so that there is no timeout for blocking function calls
		if (!ssh2_nb)
			libssh2_session_set_timeout(t->session, 0);

		if (!ssh2_nb) {
			if (libssh2_session_handshake(t->session,
				(libssh2_socket_t)(t->socket.socket)) < 0) {
					ssh_set_error(t->session);
					do {
						rc = libssh2_session_free(t->session);
						if (rc == LIBSSH2_ERROR_EAGAIN)
							Sleep(2000);
					} while (rc == LIBSSH2_ERROR_EAGAIN);
					return -1;
			}
		}
		else {
			do {
				rc = libssh2_session_handshake(t->session,
					(libssh2_socket_t)(t->socket.socket));
				if (rc < 0 && rc != LIBSSH2_ERROR_EAGAIN) {
					ssh_set_error(t->session);
					do {
						rc = libssh2_session_free(t->session);
						if (rc == LIBSSH2_ERROR_EAGAIN)
							Sleep(2000);
					} while (rc == LIBSSH2_ERROR_EAGAIN);
					return -1;
				}
				Sleep(1000);
			} while (rc == LIBSSH2_ERROR_EAGAIN);
		}

		if (t->owner->cred_acquire_cb(&t->cred, t->owner->url,
			t->user_from_url,
			GIT_CREDTYPE_SSH_PUBLICKEY,
			t->owner->cred_acquire_payload) < 0) {
				do {
					rc = libssh2_session_free(t->session);
					if (rc == LIBSSH2_ERROR_EAGAIN)
						Sleep(2000);
				} while (rc == LIBSSH2_ERROR_EAGAIN);
				return -1;
		}

		assert(t->cred);

		c = (git_cred_ssh_publickey *)t->cred;
		if (!ssh2_nb) {
			rc = libssh2_userauth_publickey_fromfile(t->session,
				c->username, NULL, c->privatekey, NULL);
			if (rc < 0) {
				ssh_set_error(t->session);
				do {
					rc = libssh2_session_free(t->session);
					if (rc == LIBSSH2_ERROR_EAGAIN)
						Sleep(2000);
				} while (rc == LIBSSH2_ERROR_EAGAIN);
				return -1;
			}
		}
		else {
			do {
				rc = libssh2_userauth_publickey_fromfile(t->session,
					c->username, NULL, c->privatekey, NULL);
				if (rc < 0 && rc != LIBSSH2_ERROR_EAGAIN) {
					ssh_set_error(t->session);
					do {
						rc = libssh2_session_free(t->session);
						if (rc == LIBSSH2_ERROR_EAGAIN)
							Sleep(2000);
					} while (rc == LIBSSH2_ERROR_EAGAIN);
					return -1;
				}
				Sleep(1000);
			} while (rc == LIBSSH2_ERROR_EAGAIN);
		}

		if (!ssh2_nb) {
			t->channel = libssh2_channel_open_session(t->session);
			if (t->channel == NULL) {
				ssh_set_error(t->session);
				do {
					rc = libssh2_session_free(t->session);
					if (rc == LIBSSH2_ERROR_EAGAIN)
						Sleep(2000);
				} while (rc == LIBSSH2_ERROR_EAGAIN);
				return -1;
			}
		}
		else {
			do {
				t->channel = libssh2_channel_open_session(t->session);
				if (t->channel == NULL && libssh2_session_last_errno(t->session) != LIBSSH2_ERROR_EAGAIN) {
					ssh_set_error(t->session);
					do {
						rc = libssh2_session_free(t->session);
						if (rc == LIBSSH2_ERROR_EAGAIN)
							Sleep(2000);
					} while (rc == LIBSSH2_ERROR_EAGAIN);
					return -1;
				}
				Sleep(500);
			} while (t->channel == NULL);
		}

		t->connected = 1;
	}

	switch (action) {
	case GIT_SERVICE_UPLOADPACK_LS:
		return ssh_uploadpack_ls(stream, t, url);

	case GIT_SERVICE_UPLOADPACK:
		return ssh_uploadpack(stream, t);

	case GIT_SERVICE_RECEIVEPACK_LS:
		return ssh_receivepack_ls(stream, t, url);

	case GIT_SERVICE_RECEIVEPACK:
		return ssh_receivepack(stream, t);
	}

	*stream = NULL;
	return -1;
}

static int ssh_close(git_smart_subtransport *subtransport)
{
	ssh_subtransport *t = (ssh_subtransport *) subtransport;

	//pthread_mutex_lock(&mutexsum);
	if (t->socket.socket > 0) {
		gitno_close(&t->socket);
		memset(&t->socket, 0x0, sizeof(gitno_socket));
		t->socket.socket = -1;
	}
	// socket is zero is a special case
	else if (t->socket.socket == 0 && is_socket_zero) {
		gitno_close(&t->socket);
		memset(&t->socket, 0x0, sizeof(gitno_socket));
		t->socket.socket = -1;
		is_socket_zero = false;
	}
	//pthread_mutex_unlock(&mutexsum);

	if (t->cred) {
		t->cred->free(t->cred);
		t->cred = NULL;
	}

	if (t->host) {
		git__free(t->host);
		t->host = NULL;
	}

	if (t->port) {
		git__free(t->port);
		t->port = NULL;
	}

	if (t->user_from_url) {
		git__free(t->user_from_url);
		t->user_from_url = NULL;
	}

	return 0;
}

static void ssh_free(git_smart_subtransport *smart_transport)
{
	ssh_subtransport *t = (ssh_subtransport *)smart_transport;
	int rc;

	if (t->connected == 1) {
		do {
			rc = libssh2_channel_close(t->channel);
			if (rc == LIBSSH2_ERROR_EAGAIN)
				Sleep(2000);
		} while (rc == LIBSSH2_ERROR_EAGAIN);
		do {
			rc = libssh2_channel_free(t->channel);
			if (rc == LIBSSH2_ERROR_EAGAIN)
				Sleep(2000);
		} while (rc == LIBSSH2_ERROR_EAGAIN);

		do {
			rc = libssh2_session_disconnect(t->session, NULL);
			if (rc == LIBSSH2_ERROR_EAGAIN)
				Sleep(2000);
		} while (rc == LIBSSH2_ERROR_EAGAIN);
		do {
			rc = libssh2_session_free(t->session);
			if (rc == LIBSSH2_ERROR_EAGAIN)
				Sleep(2000);
		} while (rc == LIBSSH2_ERROR_EAGAIN);
	}

	gitno_close(&t->socket);

	if (t->cred)
		t->cred->free(t->cred);

	git__free(t->host);
	git__free(t->port);
	git__free(t);
}

int git_smart_subtransport_ssh(git_smart_subtransport **out, git_transport *owner)
{
	ssh_subtransport *t;

	if (!out)
		return -1;

	t = (ssh_subtransport *)git__calloc(sizeof(ssh_subtransport), 1);
	GITERR_CHECK_ALLOC(t);

	t->owner = (transport_smart *)owner;
	t->parent.action = ssh_action;
	t->parent.close = ssh_close;
	t->parent.free = ssh_free;

	*out = (git_smart_subtransport *) t;
	return 0;
}

#endif /* GIT_SSH */
