#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <inttypes.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include <fcntl.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/wait.h>

#include "util.h"
#include "parse.h"
#include "mi.h"
#include "asm.h"

#include "../config.h"

/* FIXME: move into one place...? */
File file;
char debugopt[128];
int writeasm;
int extracheck = 1;
int p9asm;
char *outfile;
char *objdir;
char **incpaths;
char *localincpath;
size_t nincpaths;

static void
usage(char *prog)
{
	printf("%s [-?|-h] [-o outfile] [-O dir] [-d[dbgopts]] inputs\n", prog);
	printf("\t-?|-h\tPrint this help\n");
	printf("\t-o\tOutput to outfile\n");
	printf("\t-O dir\tOutput to dir\n");
	printf("\t-S\tGenerate assembly source alongside object code\n");
	printf("\t-T\tCompile in test mode\n");
	printf("\t-c\tEnable additional (possibly flaky) checking\n");
	printf("\t-I path\tAdd 'path' to use search path\n");
	printf("\t-d\tPrint debug dumps. Recognized options: f r p i\n");
	printf("\t-G\tGenerate asm in gas syntax\n");
	printf("\t-9\tGenerate asm in plan 9 syntax\n");
	printf("\t-d opts: additional debug logging. Options are listed below:\n");
	printf("\t\tf: log folded trees\n");
	printf("\t\tl: log lowered pre-cfg trees\n");
	printf("\t\tT: log tree immediately\n");
	printf("\t\tr: log register allocation activity\n");
	printf("\t\ti: log instruction selection activity\n");
	printf("\t\tu: log type unifications\n");
}

static void
swapout(char *buf, size_t sz, char *suf)
{
	char *psuffix;
	psuffix = strrchr(outfile, '.');
	if (psuffix != NULL)
		swapsuffix(buf, sz, outfile, psuffix, suf);
	else
		bprintf(buf, sz, "%s%s", outfile, suf);
}

static void
mkpath(char *p)
{
	char *e, path[256];

	e = p;
	assert(strlen(p) < sizeof(path));
	while ((e = strstr(e, "/")) != NULL) {
		memcpy(path, p, (e - p));
		path[e - p] = 0;
		mkdir(path, 0755);
		e++;
	}
}

static char *
dirname(char *path)
{
	char *p;

	p = strrchr(path, '/');
	if (p)
		return strdupn(path, p - path);
	else
		return xstrdup(".");
}

static int
hasmain(void)
{
	Node *n, *name;

	name = mknsname(Zloc, NULL, "main");
	n = getdcl(file.globls, name);
	if (!n)
		return 0;
	n = n->decl.name;
	if (n->name.ns)
		return 0;
	return 1;
}

static void
genuse(char *path)
{
	FILE *f;
	char buf[256];
	char *psuffix;
	size_t i;

	if (outfile != NULL)
		swapout(buf, 1024, ".use");
	else {
		psuffix = strrchr(path, '+');
		i = 0;
		if (objdir)
			i = bprintf(buf, sizeof buf, "%s/", objdir);
		if (psuffix != NULL)
			swapsuffix(buf + i, sizeof buf - i, path, psuffix, ".use");
		else
			swapsuffix(buf + i, sizeof buf - i, path, ".myr", ".use");
	}
	mkpath(buf);
	f = fopen(buf, "w");
	if (!f) {
		fprintf(stderr, "could not open path %s\n", buf);
		exit(1);
	}
	writeuse(f);
	fclose(f);
}

int
main(int argc, char **argv)
{
	char objfile[256];
	char *psuffix;
	Optctx ctx;
	size_t i, j;

	outfile = NULL;

	optinit(&ctx, "cd:?hSo:I:9G:O:T", argv, argc);
	sizefn = size;
	while (!optdone(&ctx)) {
		switch (optnext(&ctx)) {
		case 'O':
			objdir = ctx.optarg;
			break;
		case 'o':
			outfile = ctx.optarg;
			break;
		case 'S':
			writeasm = 1;
			break;
		case '?':
		case 'h':
			usage(argv[0]);
			exit(0);
			break;
		case 'c':
			extracheck = 1;
			break;
		case 'd':
			while (ctx.optarg && *ctx.optarg)
				debugopt[*ctx.optarg++ & 0x7f]++;
			break;
		case 'I':
			lappend(&incpaths, &nincpaths, ctx.optarg);
			break;
		case 'T':
			allowhidden++;
			break;
		default:
			usage(argv[0]);
			exit(0);
			break;
		}
	}

	/* Sysinit is arbitrary code defined by the configure script */
	Sysinit;

	lappend(&incpaths, &nincpaths, Instroot "/lib/myr");

	if (ctx.nargs == 0) {
		fprintf(stderr, "No input files given\n");
		exit(1);
	} else if (ctx.nargs > 1)
		outfile = NULL;

	for (i = 0; i < ctx.nargs; i++) {
		if (outfile)
			localincpath = dirname(outfile);
		else
			localincpath = dirname(ctx.args[i]);

		initfile(&file, ctx.args[0]);
		tokinit(ctx.args[i]);
		yyparse();

		/* before we do anything to the parse */
		if (debugopt['T'])
			dump(stdout);
		loaduses();
		if (hasmain()) {
			genautocall(file.init, file.ninit, file.localinit, "__init__");
			genautocall(file.fini, file.nfini, file.localfini, "__fini__");
		}
		infer();
		tagexports(0);
		/* after all type inference */
		if (debugopt['t'])
			dump(stdout);

		if (outfile != NULL)
			strncpy(objfile, outfile, sizeof(objfile));
		else {
			psuffix = strrchr(ctx.args[i], '+');
			j = 0;
			if (objdir)
				j = bprintf(objfile, sizeof objfile, "%s/", objdir);
			if (psuffix != NULL)
				swapsuffix(objfile + j, sizeof objfile - j, ctx.args[i], psuffix, Objsuffix);
			else
				swapsuffix(objfile + j, sizeof objfile - j, ctx.args[i], ".myr", Objsuffix);
		}
		genuse(ctx.args[i]);
		gen(objfile);

		free(localincpath);
	}

	return 0;
}
