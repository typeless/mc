#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <inttypes.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#include "util.h"
#include "parse.h"
#include "mi.h"
#include "../config.h"

static void
collectfn(Node *n, Node ***fn, size_t *nfn)
{
	switch (n->type) {
	case Nexpr:
		if (exprop(n) == Olit && tybase(exprtype(n))->type == Tyfunc)
			lappend(fn, nfn, n);
		break;
	default:;
	}
}

static void
genfunc(FILE *fd, Node *n)
{
	switch (n->type) {
	case Ndecl:
		//printf("decl: %s:%s\n", n->decl.name->name.ns, n->decl.name->name.name);
		break;
	default:;
	}
}

void
genc(FILE *fd)
{
	Node *n;
	size_t i;
	Node **fn;
	size_t nfn;


	nfn = 0;
	fn = NULL;
	for (i = 0; i < file.nstmts; i++) {
		n = file.stmts[i];

		if (getenv("DUMPN"))
			dumpn(n, stdout);

		switch (n->type) {
		case Nuse: /* nothing to do */
		case Nimpl:
			break;
		case Ndecl:
			n = flattenfn(n);
			collectfn(n->decl.init, &fn, &nfn);
			printf("nfn:%ld\n", nfn);
			genfunc(fd, n);
			//simpglobl(n, globls, &fn, &nfn, &blob, &nblob);
			break;
		default:
			die("Bad node %s in toplevel", nodestr[n->type]);
			break;
		}
	}

	fclose(fd);
}
