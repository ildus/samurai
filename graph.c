#define _POSIX_C_SOURCE 200809L
#include <ctype.h>
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include "env.h"
#include "graph.h"
#include "htab.h"
#include "util.h"
#include "time.h"

#ifdef __VMS
#include <rms.h>
#include <iodef.h>
#include <ssdef.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <descrip.h>
#include <lbrdef.h>
#include <lbr$routines.h>
#include <credef.h>
#include <mhddef.h>
#include <lhidef.h>
#include <lib$routines.h>
#include <starlet.h>
#endif

static struct hashtable *allnodes;
struct edge *alledges;

static void
delnode(void *p)
{
	struct node *n = p;

	if (n->shellpath != n->path)
		free(n->shellpath);
	free(n->use);
	free(n->path);
	free(n);
}

void
graphinit(void)
{
	struct edge *e;

	/* delete old nodes and edges in case we rebuilt the manifest */
	delhtab(allnodes, delnode);
	while (alledges) {
		e = alledges;
		alledges = e->allnext;
		free(e->out);
		free(e->in);
		free(e);
	}
	allnodes = mkhtab(1024);
}

struct node *
mknode(struct string *path)
{
	void **v;
	struct node *n;
	struct hashtablekey k;

	htabkey(&k, path->s, path->n);
	v = htabput(allnodes, &k);
	if (*v) {
		free(path);
		return *v;
	}
	n = xmalloc(sizeof(*n));
	n->path = path;
	n->shellpath = NULL;
	n->gen = NULL;
	n->use = NULL;
	n->nuse = 0;
	n->mtime = MTIME_UNKNOWN;
	n->logmtime = MTIME_MISSING;
	n->hash = 0;
	n->id = -1;
	*v = n;

	return n;
}

struct node *
nodeget(const char *path, size_t len)
{
	struct hashtablekey k;

	if (!len)
		len = strlen(path);
	htabkey(&k, path, len);
	return htabget(allnodes, &k);
}

#ifdef __VMS
#define DEFAULT_FILE_SPECIFICATION "[]*.*;0"

static void
get_file_revtime(const char *path, int64_t *out)
{
	struct FAB xfab;
	struct NAM xnam;
	struct XABDAT xab;
	char esa[256];
	char filename[256];

	/* get the input file specification
	 */
	memset(out, 0, sizeof(*out));
	memset(filename, 0, sizeof(filename));
	memset(esa, 0, sizeof(esa));

	xnam = cc$rms_nam;
	xnam.nam$l_esa = esa;
	xnam.nam$b_ess = sizeof(esa) - 1;
	xnam.nam$l_rsa = filename;
	xnam.nam$b_rss = sizeof(filename) - 1;

	xab = cc$rms_xabdat;       /* initialize extended attributes */
	xab.xab$b_cod = XAB$C_DAT; /* ask for date */
	xab.xab$l_nxt = NULL;      /* terminate XAB chain      */

	xfab = cc$rms_fab;
	xfab.fab$l_dna = (__char_ptr32)DEFAULT_FILE_SPECIFICATION;
	xfab.fab$b_dns = sizeof(DEFAULT_FILE_SPECIFICATION) - 1;
	xfab.fab$l_fop = FAB$M_NAM;
	xfab.fab$l_fna = (__char_ptr32)path; /* address of file name	    */
	xfab.fab$b_fns = strlen(path);       /* length of file name	    */
	xfab.fab$l_nam = &xnam;              /* address of NAB block	    */
	xfab.fab$l_xab = (char *)&xab;       /* address of XAB block     */

	sys$open(&xfab);
	sys$close(&xfab);

	*out = xab.xab$q_rdt;
}
#endif

void
nodestat(struct node *n)
{
	struct stat st;

	if (stat(n->path->s, &st) < 0) {
		if (errno != ENOENT)
			fatal("stat %s:", n->path->s);
		n->mtime = MTIME_MISSING;
	} else {
#ifdef __VMS
		get_file_revtime(n->path->s, &n->mtime);
#elif defined(__APPLE__)
		n->mtime = (int64_t)st.st_mtime * 1000000000 + st.st_mtimensec;
/*
Illumos hides the members of st_mtim when you define _POSIX_C_SOURCE
since it has not been updated to support POSIX.1-2008:
https://www.illumos.org/issues/13327
*/
#elif defined(__sun)
		n->mtime = (int64_t)st.st_mtim.__tv_sec * 1000000000 + st.st_mtim.__tv_nsec;
#else
		n->mtime = (int64_t)st.st_mtim.tv_sec * 1000000000 + st.st_mtim.tv_nsec;
#endif
	}
}

struct string *
nodepath(struct node *n, bool escape)
{
	char *s, *d;
	int nquote;

	if (!escape)
		return n->path;
	if (n->shellpath)
		return n->shellpath;
	escape = false;
	nquote = 0;
	for (s = n->path->s; *s; ++s) {
		if (!isalnum(*(unsigned char *)s) && !strchr("_+-./", *s))
			escape = true;
		if (*s == '\'')
			++nquote;
	}
	if (escape) {
		n->shellpath = mkstr(n->path->n + 2 + 3 * nquote);
		d = n->shellpath->s;
		*d++ = '\'';
		for (s = n->path->s; *s; ++s) {
			*d++ = *s;
			if (*s == '\'') {
				*d++ = '\\';
				*d++ = '\'';
				*d++ = '\'';
			}
		}
		*d++ = '\'';
	} else {
		n->shellpath = n->path;
	}
	return n->shellpath;
}

void
nodeuse(struct node *n, struct edge *e)
{
	/* allocate in powers of two */
	if (!(n->nuse & (n->nuse - 1)))
		n->use = xreallocarray(n->use, n->nuse ? n->nuse * 2 : 1, sizeof(e));
	n->use[n->nuse++] = e;
}

struct edge *
mkedge(struct environment *parent)
{
	struct edge *e;

	e = xmalloc(sizeof(*e));
	e->env = mkenv(parent);
	e->pool = NULL;
	e->out = NULL;
	e->nout = 0;
	e->in = NULL;
	e->nin = 0;
	e->flags = 0;
	e->allnext = alledges;
	alledges = e;

	return e;
}

void
edgehash(struct edge *e)
{
	static const char sep[] = ";rspfile=";
	struct string *cmd, *rsp, *s;

	if (e->flags & FLAG_HASH)
		return;
	e->flags |= FLAG_HASH;
	cmd = edgevar(e, "command", true);
	if (!cmd)
		fatal("rule '%s' has no command", e->rule->name);
	rsp = edgevar(e, "rspfile_content", true);
	if (rsp && rsp->n > 0) {
		s = mkstr(cmd->n + sizeof(sep) - 1 + rsp->n);
		memcpy(s->s, cmd->s, cmd->n);
		memcpy(s->s + cmd->n, sep, sizeof(sep) - 1);
		memcpy(s->s + cmd->n + sizeof(sep) - 1, rsp->s, rsp->n);
		s->s[s->n] = '\0';
		e->hash = murmurhash64a(s->s, s->n);
		free(s);
	} else {
		e->hash = murmurhash64a(cmd->s, cmd->n);
	}
}

static struct edge *
mkphony(struct node *n)
{
	struct edge *e;

	e = mkedge(rootenv);
	e->rule = &phonyrule;
	e->inimpidx = 0;
	e->inorderidx = 0;
	e->outimpidx = 1;
	e->nout = 1;
	e->out = xmalloc(sizeof(n));
	e->out[0] = n;

	return e;
}

void
edgeadddeps(struct edge *e, struct node **deps, size_t ndeps)
{
	struct node **order, *n;
	size_t norder, i;

	for (i = 0; i < ndeps; ++i) {
		n = deps[i];
		if (!n->gen)
			n->gen = mkphony(n);
		nodeuse(n, e);
	}
	e->in = xreallocarray(e->in, e->nin + ndeps, sizeof(e->in[0]));
	order = e->in + e->inorderidx;
	norder = e->nin - e->inorderidx;
	memmove(order + ndeps, order, norder * sizeof(e->in[0]));
	memcpy(order, deps, ndeps * sizeof(e->in[0]));
	e->inorderidx += ndeps;
	e->nin += ndeps;
}
