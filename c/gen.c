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
#include "asm.h"
#include "../config.h"

static Node *abortoob;
static Type *tyintptr;
static Type *tyword;
static Type *tyvoid;

void
initconsts(Htab *globls)
{
	Type *ty;
	Node *name;
	Node *dcl;

	tyintptr = mktype(Zloc, Tyuint64);
	tyword = mktype(Zloc, Tyuint);
	tyvoid = mktype(Zloc, Tyvoid);

	ty = mktyfunc(Zloc, NULL, 0, mktype(Zloc, Tyvoid));
	ty->type = Tycode;
	name = mknsname(Zloc, "_rt", "abort_oob");
	dcl = mkdecl(Zloc, name, ty);
	dcl->decl.isconst = 1;
	dcl->decl.isextern = 1;

	abortoob = mkexpr(Zloc, Ovar, name, NULL);
	abortoob->expr.type = ty;
	abortoob->expr.did = dcl->decl.did;
	abortoob->expr.isconst = 1;
}

void
gen(char *out)
{
	FILE *fd;
	char buf[1024];
	char *infile;

	swapsuffix(buf, sizeof buf, out, ".o", ".c");
	fd = fopen(buf, "w");
	if (!fd)
		die("Couldn't open fd %s", buf);

	infile = "-";
	if (1)
		infile = strdup(buf);

	// snprintf(buf, sizeof(buf), "tee out.c | %s %s %s %s", "cc", "-c -x c -g -o", out, infile);
	// fprintf(stderr, "cmd: %s\n", buf);
	//  fd = popen(buf, "w");
	//  if (!fd) {
	//	die("Couldn't open fd %s", buf);
	//  }

	genc(fd);
	fclose(fd);

	snprintf(buf, sizeof(buf), "%s %s %s %s", "cc", "-O2 -c -x c -g -fno-stack-protector -o", out, infile);
	fprintf(stderr, "cmd: %s\n", buf);
	system(buf);

	// pclose(fd);
}
