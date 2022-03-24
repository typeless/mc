#include <ctype.h>
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
#include <errno.h>

#include "util.h"
#include "parse.h"
#include "mi.h"
#include "asm.h"
#include "../config.h"

/**
 * We assume that every function literal is uniquely identified by its nid.
 */

#define Tdindirect 0x80

static void emit_block(FILE *fd, Node *n);

__attribute__((unused)) static Type *
tysubst(Type *t)
{
	while (t->type == Tyvar && tytab[t->tid]) {
		t = tytab[t->tid];
	}
	return t;
}
static void emit_expr(FILE *fd, Node *n);

static void
emit_type(FILE *fd, Type *t)
{
	int hasns;
	size_t i;

	switch (t->type) {
	case Tyvoid:
	case Tybool:
	case Tychar:
	case Tyint8:
	case Tyint16:
	case Tyint32:
	case Tyint:
	case Tyint64:
	case Tybyte:
	case Tyuint8:
	case Tyuint16:
	case Tyuint32:
	case Tyuint:
	case Tyuint64:
	case Tyflt32:
	case Tyflt64:
		fprintf(fd, " _Ty%d", t->tid);
		break;
	case Tyvalist:
		fprintf(fd, "...");
		break;
	case Typtr:
		emit_type(fd, t->sub[0]);
		fprintf(fd, " *");
		break;
	case Tyarray:
		fprintf(fd, "typeof(");
		emit_type(fd, t->sub[0]);
		if (t->asize) {
			fprintf(fd, "[%lld]", t->asize->expr.args[0]->lit.intval);
		} else {
			fprintf(fd, "[]");
		}
		fprintf(fd, ")");
		break;
	case Tytuple:
		fprintf(fd, "struct {");
		for (size_t i = 0; i < t->nsub; i++) {
			emit_type(fd, t->sub[i]);
			fprintf(fd, " _%ld;", i);
		}
		fprintf(fd, "}");
		break;
	case Tystruct:
		fprintf(fd, "struct {");
		for (i = 0; i < t->nmemb; i++) {
			// emit_type(fd, decltype(t->sdecls[i]));
			fprintf(fd, "_Ty%d", decltype(t->sdecls[i])->tid);
			fprintf(fd, " %s;", declname(t->sdecls[i]));
		}
		fprintf(fd, "}");
		break;
	case Tyunion:
		fprintf(fd, "struct {");
		fprintf(fd, "uint32_t _tag;");
		fprintf(fd, "union {");
		for (i = 0; i < t->nmemb; i++) {
			char *ns = t->udecls[i]->name->name.ns;
			char *name = t->udecls[i]->name->name.name;
			fprintf(fd, "struct %s%s%s {", ns ? ns : "", ns ? "$" : "", name);
			emit_type(fd, t->udecls[i]->etype);
			fprintf(fd, "; };");
		}
		fprintf(fd, "}");
		fprintf(fd, "}");
		break;
	case Tyslice:
		fprintf(fd, "struct {");
		emit_type(fd, t->sub[0]);
		fprintf(fd, "*p; uint32_t len /* size_t */; }");
		break;
	case Tyfunc:
		fprintf(fd, "typeof(");
		fprintf(fd, "_Ty%d ", t->sub[0]->tid);
		// emit_type(fd, t->sub[0]);
		fprintf(fd, " (*)(");
		if (t->nsub > 1) {
			for (size_t i = 1; i < t->nsub; i++) {
				// emit_type(fd, t->sub[i]);
				if (t->sub[i]->type == Tyvalist) {
					fprintf(fd, "...");
				} else {
					fprintf(fd, "_Ty%d", t->sub[i]->tid);
				}
				if (i + 1 < t->nsub) {
					fprintf(fd, ", ");
				}
			}
		} else {
			fprintf(fd, "void");
		}
		fprintf(fd, ")");
		fprintf(fd, ")");
		break;
	case Tyname:
	case Tygeneric:
		hasns = t->name->name.ns != NULL;
		fprintf(fd, "%s%s%s", hasns ? t->name->name.ns : "", hasns ? "$" : "", namestr(t->name));
		break;
		break;
	case Typaram:
		fprintf(fd, "_Ty%d /* Typaram %s */", t->tid, tystr(t));
		break;
	case Tyvar:
		fprintf(fd, "_Ty%d", t->tid);
		// emit_type(fd, tytab[t->tid]);
		break;
	default:
		fprintf(stderr, "/* Invalid type: %s id: %d */\n", tystr(t), t->tid);
		assert(0);
	}
}

static void
emit_call(FILE *fd, Node *n)
{
	Node **env;
	Node *dcl;
	size_t nargs, nenv;
	size_t i;

	assert(n->type == Nexpr);
	assert(n->expr.op == Ocall);
	assert(n->expr.args[0]->type == Nexpr);
	assert(n->expr.args[0]->expr.op == Ovar || n->expr.args[0]->expr.op == Olit);

	nenv = 0;
	nargs = 0;
	if (n->expr.args[0]->expr.op == Olit) {
		assert(n->expr.args[0]->type == Nexpr);
		assert(n->expr.args[0]->expr.op == Olit);
		assert(n->expr.args[0]->expr.args[0]->type == Nlit);
		assert(n->expr.args[0]->expr.args[0]->lit.littype == Lfunc);
		assert(n->expr.args[0]->expr.args[0]->lit.fnval->type == Nfunc);
		fprintf(fd, "_fn%d", n->expr.args[0]->expr.args[0]->lit.fnval->nid);

		nargs = n->expr.args[0]->expr.args[0]->lit.fnval->func.nargs;
		env = getclosure(n->expr.args[0]->expr.args[0]->lit.fnval->func.scope, &nenv);
	} else if (n->expr.args[0]->expr.op == Ovar) {
		dcl = decls[n->expr.args[0]->expr.did];
		nargs = n->expr.nargs;
		fprintf(fd, "/*ns:%s %s*/\n", dcl->decl.name->name.ns, declname(dcl));
		if (dcl->decl.name->name.ns) {
			fprintf(fd, "%s$", dcl->decl.name->name.ns);
		}
		fprintf(fd, "%s", declname(dcl));
	}
	fprintf(fd, "(");
	if (nenv > 0) {
		fprintf(fd, "&(struct _envty$%d){", n->expr.args[0]->expr.args[0]->lit.fnval->nid);
		for (i = 0; i < nenv; i++) {
			fprintf(fd, "\t._v%ld = _v%ld,\n", env[i]->decl.did, env[i]->decl.did);
		}
		fprintf(fd, "}%s", nargs ? "," : "");
	}
	for (i = 1; i < nargs; i++) {
		emit_expr(fd, n->expr.args[i]);
		if (i + 1 < nargs) {
			fprintf(fd, " ,");
		}
	}
	fprintf(fd, ")");
}

static void
emit_expr(FILE *fd, Node *n)
{
	Node **args;
	Node *dcl;

	assert(n->type == Nexpr);

	args = n->expr.args;
	switch (exprop(n)) {
	case Oundef:
		break;
	case Olit:
		switch (args[0]->lit.littype) {
		case Lchr:
			fprintf(fd, "'%c'", args[0]->lit.chrval);
			break;
		case Lbool:
			fprintf(fd, "%s", args[0]->lit.boolval ? "true" : "false");
			break;
		case Lint:
			fprintf(fd, "%lld", args[0]->lit.intval);
			break;
		case Lflt:
			fprintf(fd, "%f", args[0]->lit.fltval);
			break;
		case Lstr:
			// fprintf(fd, "\"%.*s\"", (int)args[0]->lit.strval.len, args[0]->lit.strval.buf);
			fprintf(fd, "(_Ty%d){\"", n->expr.type->tid);
			for (size_t i = 0; i < args[0]->lit.strval.len; i++) {
				char ch = args[0]->lit.strval.buf[i];
				if (iscntrl(ch) || ch == '\\' || ch == '\"' || ch == '\'') {
					fprintf(fd, "\\%03o", ch);
				} else {
					fputc(ch, fd);
				}
			}
			fprintf(fd, "\", %ld}", args[0]->lit.strval.len);
			break;
		case Lfunc:
			fprintf(fd, "(const uintptr_t[2]){");
			fprintf(fd, "_v%d,", args[0]->lit.fnval->nid);
			fprintf(fd, "0");
			fprintf(fd, "}\n");
			break;
		case Llbl:
			assert(0);
			break;
		case Lvoid:
			assert(0);
			break;
		default:
			assert(0);
		}
		break;
	case Otup:
		fprintf(fd, "((_Ty%d) {", exprtype(n)->tid);
		// fprintf(fd, "((");
		// emit_type(fd, exprtype(n));
		// fprintf(fd, ") {");
		for (size_t i = 0; i < n->expr.nargs; i++) {
			emit_expr(fd, n->expr.args[i]);
			if (i + 1 < n->expr.nargs) {
				fprintf(fd, ", ");
			}
		}
		fprintf(fd, "})");
		break;
	case Oadd:
		emit_expr(fd, args[0]);
		fprintf(fd, "+");
		emit_expr(fd, args[1]);
		break;
	case Osub:
		emit_expr(fd, args[0]);
		fprintf(fd, "-");
		emit_expr(fd, args[1]);
		break;
	case Omul:
		emit_expr(fd, args[0]);
		fprintf(fd, "*");
		emit_expr(fd, args[1]);
		break;
	case Odiv:
		emit_expr(fd, args[0]);
		fprintf(fd, "/");
		emit_expr(fd, args[1]);
		break;
	case Omod:
		emit_expr(fd, args[0]);
		fprintf(fd, "%%");
		emit_expr(fd, args[1]);
		break;
	case Oneg:
		fprintf(fd, "-");
		emit_expr(fd, args[0]);
		break;
	case Obor:
		emit_expr(fd, args[0]);
		fprintf(fd, "|");
		emit_expr(fd, args[1]);
		break;
	case Oband:
		emit_expr(fd, args[0]);
		fprintf(fd, "&");
		emit_expr(fd, args[1]);
		break;
	case Obxor:
		emit_expr(fd, args[0]);
		fprintf(fd, "^");
		emit_expr(fd, args[1]);
		break;
	case Obsl:
		emit_expr(fd, args[0]);
		fprintf(fd, "<<");
		emit_expr(fd, args[1]);
		break;
	case Obsr:
		emit_expr(fd, args[0]);
		fprintf(fd, ">>");
		emit_expr(fd, args[1]);
		break;
	case Obnot:
		emit_expr(fd, args[0]);
		fprintf(fd, "~");
		emit_expr(fd, args[1]);
		break;
	case Opreinc:
		fprintf(fd, "++");
		emit_expr(fd, args[0]);
		break;
	case Opostinc:
		emit_expr(fd, args[0]);
		fprintf(fd, "++");
		break;
	case Opredec:
		fprintf(fd, "--");
		emit_expr(fd, args[0]);
		break;
	case Opostdec:
		emit_expr(fd, args[0]);
		fprintf(fd, "--");
		break;
	case Oaddr:
		fprintf(fd, "&");
		emit_expr(fd, n->expr.args[0]);
		break;
	case Oderef:
		fprintf(fd, "*");
		emit_expr(fd, n->expr.args[0]);
		break;
	case Olor:
		emit_expr(fd, args[0]);
		fprintf(fd, "||");
		emit_expr(fd, args[1]);
		break;
	case Oland:
		emit_expr(fd, args[0]);
		fprintf(fd, "&&");
		emit_expr(fd, args[1]);
		break;
	case Olnot:
		fprintf(fd, "!");
		emit_expr(fd, args[0]);
		break;
	case Oeq:
		emit_expr(fd, args[0]);
		fprintf(fd, "==");
		emit_expr(fd, args[1]);
		break;
	case One:
		emit_expr(fd, args[0]);
		fprintf(fd, "!=");
		emit_expr(fd, args[1]);
		break;
	case Ogt:
		emit_expr(fd, args[0]);
		fprintf(fd, ">");
		emit_expr(fd, args[1]);
		break;
	case Oge:
		emit_expr(fd, args[0]);
		fprintf(fd, ">=");
		emit_expr(fd, args[1]);
		break;
	case Olt:
		emit_expr(fd, args[0]);
		fprintf(fd, "<");
		emit_expr(fd, args[1]);
		break;
	case Ole:
		emit_expr(fd, args[0]);
		fprintf(fd, "<=");
		emit_expr(fd, args[1]);
		break;
	case Oasn:
		emit_expr(fd, args[0]);
		fprintf(fd, "=");
		emit_expr(fd, args[1]);
		break;
	case Oaddeq:
		emit_expr(fd, args[0]);
		fprintf(fd, "+=");
		emit_expr(fd, args[1]);
		break;
	case Osubeq:
		emit_expr(fd, args[0]);
		fprintf(fd, "-=");
		emit_expr(fd, args[1]);
		break;
	case Omuleq:
		emit_expr(fd, args[0]);
		fprintf(fd, "*=");
		emit_expr(fd, args[1]);
		break;
	case Odiveq:
		emit_expr(fd, args[0]);
		fprintf(fd, "/=");
		emit_expr(fd, args[1]);
		break;
	case Omodeq:
		emit_expr(fd, args[0]);
		fprintf(fd, "%%=");
		emit_expr(fd, args[1]);
		break;
	case Oboreq:
		emit_expr(fd, args[0]);
		fprintf(fd, "|=");
		emit_expr(fd, args[1]);
		break;
	case Obandeq:
		emit_expr(fd, args[0]);
		fprintf(fd, "&=");
		emit_expr(fd, args[1]);
		break;
	case Obxoreq:
		emit_expr(fd, args[0]);
		fprintf(fd, "^=");
		emit_expr(fd, args[1]);
		break;
	case Obsleq:
		emit_expr(fd, args[0]);
		fprintf(fd, "<<=");
		emit_expr(fd, args[1]);
		break;
	case Obsreq:
		emit_expr(fd, args[0]);
		fprintf(fd, ">>=");
		emit_expr(fd, args[1]);
		break;
	case Oidx:
		if (exprtype(n->expr.args[0])->type == Tyslice) {
			emit_expr(fd, n->expr.args[0]);
			fprintf(fd, ".p");
		}
		fprintf(fd, "[");
		emit_expr(fd, n->expr.args[1]);
		fprintf(fd, "]");
		break;
	case Oslice:
		assert(0);
		break;
	case Omemb:
		emit_expr(fd, args[0]);
		fprintf(fd, ".");
		emit_expr(fd, args[1]);
		break;
	case Otupmemb:
		assert(0);
		break;
	case Osize:
		fprintf(fd, "sizeof(");
		emit_expr(fd, args[0]);
		fprintf(fd, ")");
		break;
	case Ocall:
		emit_call(fd, n);
		break;
	case Ocast:
		fprintf(fd, "((_Ty%d)(", exprtype(n)->tid);
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, "))");
		break;
	case Oret:
		fprintf(fd, "return ");
		emit_expr(fd, n->expr.args[0]);
		break;
	case Ojmp:
		assert(0);
		break;
	case Obreak:
		assert(0);
		break;
	case Ocontinue:
		assert(0);
		break;
	case Ovar:
		dcl = decls[n->expr.did];
		if (dcl->decl.isextern) {
			fprintf(fd, "%s /* did: %ld */", declname(dcl), dcl->decl.did);
		} else {
			fprintf(fd, "_v%ld /* %s */", dcl->decl.did, declname(dcl));
		}
		break;
	case Otupget:
		assert(n->expr.args[0]->type == Nexpr);
		assert(n->expr.args[1]->expr.op == Olit);
		assert(n->expr.args[1]->expr.args[0]->lit.littype == Lint);
		fprintf(fd, "((_v%d).", n->expr.args[0]->nid);
		fprintf(fd, "_%llu)", n->expr.args[1]->expr.args[0]->lit.intval);
		break;
	default:;
		fprintf(stderr, "op: %s\n", opstr[exprop(n)]);
		assert(0);
	}
}

static void
emit_objdecl(FILE *fd, Node *n)
{
	assert(n->type == Ndecl);

	if (n->decl.isextern) {
		fprintf(fd, "extern ");
		// fprintf(fd, "__attribute__((alias(\"%s\")))", declname(n));
	}
	if (!n->decl.isextern && n->decl.isglobl) {
		if (n->decl.vis == Visintern || n->decl.vis == Vishidden) {
			fprintf(fd, "static ");
		}
	}

	fprintf(fd, "_Ty%d ", decltype(n)->tid);
	if (n->decl.isextern) {
		fprintf(fd, "%s", declname(n));
	} else {
		fprintf(fd, "_v%ld", n->decl.did);
	}
	if (n->decl.init) {
		fprintf(fd, " = ");
		emit_expr(fd, n->decl.init);
	}
	fprintf(fd, "; /* %s ****/ \n", declname(n));
}

static void
emit_match_rec(FILE *fd, Dtree *dt)
{
	size_t i;

	fprintf(fd, "/* dt->id: %d */\n", dt->id);

	/* the we jump to the accept label when generating the parent */
	if (dt->accept) {
		fprintf(fd, "goto _%s; /*  if (dt->accept) ... */\n", lblstr(dt->lbl) + 1);
		return;
	}

	fprintf(fd, "switch (");
	emit_expr(fd, dt->load);
	fprintf(fd, ") {\n");
	for (i = 0; i < dt->nnext; i++) {
		fprintf(fd, "case ");
		emit_expr(fd, dt->pat[i]);
		fprintf(fd, ":\n");
		emit_match_rec(fd, dt->next[i]);
	}
	if (dt->any) {
		fprintf(fd, "default:\n");
		emit_match_rec(fd, dt->any);
	}
	fprintf(fd, "}\n");
}

static void
emit_match(FILE *fd, Node *n)
{
	Dtree *dt;
	Node **lbl;
	size_t nlbl;
	Node *val;

	nlbl = 0;
	lbl = NULL;
	for (size_t i = 0; i < n->matchstmt.nmatches; i++) {
		lappend(&lbl, &nlbl, genlbl(n->matchstmt.matches[i]->match.block->loc));
	}

	val = n->matchstmt.val;
	fprintf(fd, "do {\n");

	// emit_type(fd, exprtype(val));
	fprintf(fd, "_Ty%d _v%d = ", exprtype(val)->tid, val->nid);
	// fprintf(fd, "_Ty%d _v%d = ", exprtype(val)->tid, val->nid);
	emit_expr(fd, val);
	fprintf(fd, ";");
	fprintf(fd, "\n\n");
	dt = gendtree(n, val, lbl, nlbl);
	if (1)
		emit_match_rec(fd, dt);
	fprintf(fd, "\nbreak;\n");
	for (size_t i = -0; i < n->matchstmt.nmatches; i++) {
		fprintf(fd, "\n_%s: /* Accept */ {\n", lblstr(lbl[i]) + 1);
		emit_block(fd, n->matchstmt.matches[i]->match.block);
		fprintf(fd, "\n}\n");
	}

	fprintf(fd, "} while (0);\n");
}

static void
emit_stmt(FILE *fd, Node *n)
{

	assert(n->type == Ndecl || n->type == Nexpr || n->type == Nifstmt || n->type == Nmatchstmt || n->type == Nloopstmt);

	fprintf(fd, "/* ntype:%s */\n", nodestr[n->type]);
	switch (n->type) {
	case Ndecl:
		emit_objdecl(fd, n);
		break;
	case Nifstmt:
		fprintf(fd, "if (");
		emit_expr(fd, n->ifstmt.cond);
		fprintf(fd, ") {\n");
		emit_block(fd, n->ifstmt.iftrue);
		if (n->ifstmt.iffalse) {
			fprintf(fd, "} else ");
			emit_block(fd, n->ifstmt.iffalse);
		}
		fprintf(fd, "}");
		break;
	case Nmatchstmt:
		emit_match(fd, n);
		break;
	case Nloopstmt:
		fprintf(fd, "for (;;) {\n");
		fprintf(fd, "}");
		break;
	case Nexpr:
		emit_expr(fd, n);
		fprintf(fd, ";");
		break;
	default:
		assert(0);
	}
	fprintf(fd, "\n");
}

static void
emit_block(FILE *fd, Node *n)
{
	assert(n->type == Nblock);
	for (size_t i = 0; i < n->block.nstmts; i++) {
		emit_stmt(fd, n->block.stmts[i]);
	}
}

static void
emit_func(FILE *fd, Node *n)
{
	// size_t i;

	assert(n->type == Nfunc);
	// for (i = 0; i < n->func.nargs; i++) {
	//	emit_objdecl(fd, n->func.args[i]);
	// }
	emit_block(fd, n->func.body);
}

static void
emit_fnval(FILE *fd, Node *n)
{
	assert(n->type == Nexpr);
	assert(n->expr.op == Olit);
	assert(n->expr.args[0]->type == Nlit);
	assert(n->expr.args[0]->lit.littype == Lfunc);
	emit_func(fd, n->expr.args[0]->lit.fnval);
}

static size_t tysize(Type *t);
static size_t tyalign(Type *ty);

static size_t
alignto(size_t sz, Type *t)
{
	return align(sz, tyalign(t));
}

size_t
size(Node *n)
{
	Type *t;

	if (n->type == Nexpr)
		t = n->expr.type;
	else
		t = n->decl.type;
	return tysize(t);
}

static size_t
tysize(Type *t)
{
	size_t sz;
	size_t i;

	sz = 0;
	if (!t)
		die("size of empty type => bailing.");
	switch (t->type) {
	case Tyvoid:
		return 0;
	case Tybool:
	case Tyint8:
	case Tybyte:
	case Tyuint8:
		return 1;
	case Tyint16:
	case Tyuint16:
		return 2;
	case Tyint:
	case Tyint32:
	case Tyuint:
	case Tyuint32:
	case Tychar: /* utf32 */
		return 4;

	case Typtr:
	case Tyvalist: /* ptr to first element of valist */
		return Ptrsz;

	case Tyint64:
	case Tyuint64:
		return 8;

		/*end integer types*/
	case Tyflt32:
		return 4;
	case Tyflt64:
		return 8;

	case Tycode:
		return Ptrsz;
	case Tyfunc:
		return 2 * Ptrsz;
	case Tyslice:
		return 2 * Ptrsz; /* len; ptr */
	case Tyname:
		return tysize(t->sub[0]);
	case Tyarray:
		if (!t->asize)
			return 0;
		t->asize = fold(t->asize, 1);
		assert(exprop(t->asize) == Olit);
		return t->asize->expr.args[0]->lit.intval * tysize(t->sub[0]);
	case Tytuple:
		for (i = 0; i < t->nsub; i++) {
			sz = alignto(sz, t->sub[i]);
			sz += tysize(t->sub[i]);
		}
		sz = alignto(sz, t);
		return sz;
		break;
	case Tystruct:
		for (i = 0; i < t->nmemb; i++) {
			sz = alignto(sz, decltype(t->sdecls[i]));
			sz += size(t->sdecls[i]);
		}
		sz = alignto(sz, t);
		return sz;
		break;
	case Tyunion:
		sz = Wordsz;
		for (i = 0; i < t->nmemb; i++)
			if (t->udecls[i]->etype)
				sz = max(sz, tysize(t->udecls[i]->etype) + Wordsz);
		return align(sz, tyalign(t));
		break;
	case Tygeneric:
	case Tybad:
	case Tyvar:
	case Typaram:
	case Tyunres:
	case Ntypes:
		die("Type %s does not have size; why did it get down to here?", tystr(t));
		break;
	}
	return -1;
}

static size_t
tyalign(Type *ty)
{
	size_t align, i;

	align = 1;
	ty = tybase(ty);
	switch (ty->type) {
	case Tyarray:
		align = tyalign(ty->sub[0]);
		break;
	case Tytuple:
		for (i = 0; i < ty->nsub; i++)
			align = max(align, tyalign(ty->sub[i]));
		break;
	case Tyunion:
		align = 4;
		for (i = 0; i < ty->nmemb; i++)
			if (ty->udecls[i]->etype)
				align = max(align, tyalign(ty->udecls[i]->etype));
		break;
	case Tystruct:
		for (i = 0; i < ty->nmemb; i++)
			align = max(align, tyalign(decltype(ty->sdecls[i])));
		break;
	case Tyslice:
		align = 8;
		break;
	default:
		align = max(align, tysize(ty));
	}
	return min(align, Ptrsz);
}

static char *
tydescid(char *buf, size_t bufsz, Type *ty)
{
	char *sep, *ns;
	char *p, *end;
	size_t i;

	sep = "";
	ns = "";
	p = buf;
	end = buf + bufsz;
	ty = tydedup(ty);
	if (ty->type == Tyname) {
		if (ty->name->name.ns) {
			ns = ty->name->name.ns;
			sep = "$";
		}
		if (ty->vis != Visintern || ty->isimport)
			p += bprintf(p, end - p, "_tydesc$%s%s%s", ns, sep, ty->name->name.name, ty->tid);
		else
			p += bprintf(p, end - p, "_tydesc$%s%s%s$%d", ns, sep, ty->name->name.name, ty->tid);
		for (i = 0; i < ty->narg; i++)
			p += tyidfmt(p, end - p, ty->arg[i]);
	} else {
		if (file.globls->name) {
			ns = file.globls->name;
			sep = "$";
		}
		bprintf(buf, bufsz, "_tydesc%s%s$%d", sep, ns, ty->tid);
	}
	return buf;
}

static void
emit_typeinfo(FILE *fd, Type *ty)
{
	fprintf(fd, "%ld /* size */,", tysize(ty));
	fprintf(fd, "%ld /* align */,", tyalign((ty)));
}

size_t
emit_namevec(FILE *fd, Node *n)
{
	char *buf;
	size_t i, len;

	assert(n->type == Nname);

	if (n->name.ns) {
		len = strlen(n->name.name) + strlen(n->name.ns) + 1;
		buf = xalloc(len + 1);
		bprintf(buf, len + 1, "%s.%s", n->name.ns, n->name.name);
	} else {
		len = strlen(n->name.name);
		buf = xalloc(len + 1);
		bprintf(buf, len + 1, "%s", n->name.name);
	}
	fprintf(fd, "/* namevec */ %ld,", len);
	for (i = 0; i < len; i++) {
		fprintf(fd, "'%c',", buf[i]);
	}
	return len;
}

static void
emit_tydescsub(FILE *fd, Type *ty)
{
	char buf[512];
	Node *len;
	size_t i;

	switch (ty->type) {
	case Ntypes:
	case Tyvar:
	case Tybad:
	case Typaram:
	case Tygeneric:
	case Tycode:
	case Tyunres:
		die("invalid type in tydesc");
		break;
		/* atomic types -- nothing else to do */
	case Tyvoid:
	case Tychar:
	case Tybool:
	case Tyint8:
	case Tyint16:
	case Tyint:
	case Tyint32:
	case Tyint64:
	case Tybyte:
	case Tyuint8:
	case Tyuint16:
	case Tyuint:
	case Tyuint32:
	case Tyuint64:
	case Tyflt32:
	case Tyflt64:
	case Tyvalist:
		break;
	case Typtr:
		emit_tydescsub(fd, ty->sub[0]);
		break;
	case Tyslice:
		emit_tydescsub(fd, ty->sub[0]);
		break;
	case Tyarray:
		emit_typeinfo(fd, ty);
		ty->asize = fold(ty->asize, 1);
		len = ty->asize;
		if (len) {
			assert(len->type == Nexpr);
			len = len->expr.args[0];
			assert(len->type == Nlit && len->lit.littype == Lint);
			fprintf(fd, "%lld /* len of array */, ", len->lit.intval);
		} else {
			fprintf(fd, "%d /* len of array */, ", 0);
		}
		emit_tydescsub(fd, ty->sub[0]);
		break;
	case Tyfunc:
		fprintf(fd, "%ld /* arity of func */,", ty->nsub);
		for (i = 0; i < ty->nsub; i++) {
			emit_tydescsub(fd, ty->sub[i]);
		}
		break;
	case Tytuple:
		emit_typeinfo(fd, ty);
		fprintf(fd, "%ld /* arity of tuple */,", ty->nsub);
		for (i = 0; i < ty->nsub; i++) {
			emit_tydescsub(fd, ty->sub[i]);
		}
		break;
	case Tystruct:
		emit_typeinfo(fd, ty);
		fprintf(fd, "%ld /* nmemb of struct */,", ty->nmemb);
		for (i = 0; i < ty->nmemb; i++) {
			emit_namevec(fd, ty->sdecls[i]->decl.name);
			emit_tydescsub(fd, ty->sdecls[i]->decl.type);
		}
		break;
	case Tyunion:
		emit_typeinfo(fd, ty);
		fprintf(fd, "%ld /* nmemb of union */,", ty->nmemb);
		for (i = 0; i < ty->nmemb; i++) {
			emit_namevec(fd, ty->udecls[i]->name);
			if (ty->udecls[i]->etype) {
				emit_tydescsub(fd, ty->udecls[i]->etype);
			} else {
				fprintf(fd, "%d, ", 1);
				fprintf(fd, "%d, ", Tybad);
			}
		}
		break;
	case Tyname:
		i = bprintf(buf, sizeof buf, "%s", Symprefix);
		tydescid(buf + i, sizeof buf - i, ty);
		// lappend(&sub, &nsub, mkblobref(buf, 0, isextern));
		fprintf(fd, "%s, %s, %s, %s, /*FIXME*/\n", buf, buf, buf, buf);
		break;
	}
}

static void
emit_tydesc(FILE *fd, Type *ty)
{
	size_t sz;

	if (ty->type == Tyname && hasparams(ty)) {
		return;
	}

	fprintf(fd, "static const char _tydesc$%d[] = {", ty->tid);
	if (ty->type == Tyname) {
		// b = mkblobseq(NULL, 0);
		// sz = mkblobi(Btimin, 0);
		// sub = namedesc(ty);
		// sz->ival = blobsz(sub);
		// lappend(&b->seq.sub, &b->seq.nsub, sz);
		// lappend(&b->seq.sub, &b->seq.nsub, sub);
		// if (ty->vis != Visintern)
		//	b->isglobl = 1;
		if (ty->name->name.ns) {
			sz = snprintf(NULL, 0, "%s.%s", ty->name->name.ns, ty->name->name.name);
		} else {
			sz = snprintf(NULL, 0, "%s", ty->name->name.name);
		}
		fprintf(fd, "%ld /* sz of _Ty%d*/, ", sz, ty->tid);
		fprintf(fd, "%d,\n", Tyname);
		sz = emit_namevec(fd, ty->name);
		emit_tydescsub(fd, ty->sub[0]);
	} else {
		emit_tydescsub(fd, ty);
	}
	fprintf(fd, "}\n");
}

void
genfuncdecl(FILE *fd, Node *n, Node *init)
{
	Type *t;
	Node **args, **env;
	size_t nargs, nenv;

	t = decltype(n);

	assert(n->type == Ndecl);
	assert(t->type == Tyfunc);
	assert(t->nsub > 0);

	nenv = 0;
	nargs = 0;
	if (init) {
		env = getclosure(init->expr.args[0]->lit.fnval->func.scope, &nenv);
		args = init->expr.args[0]->lit.fnval->func.args;
		nargs = init->expr.args[0]->lit.fnval->func.nargs;
	}

	fprintf(fd, "/* %s : %s */\n", declname(n), tystr(t));

	/* Declare a struct for storing closure environment */
	if (nenv) {
		fprintf(fd, "struct $%s$env {\n", declname(n));
		for (size_t i = 0; i < nenv; i++) {
			Type *envty = decltype(env[i]);
			fprintf(fd, "\t%s %s;\n", tystr(envty), declname(env[i]));
		}
		fprintf(fd, "};\n\n");
	}

	fprintf(fd, "/* vis:%d\n*/\n", n->decl.vis);
	if (n->decl.isextern) {
		fprintf(fd, "extern ");
	}
	if (!n->decl.isextern && n->decl.isglobl) {
		if (n->decl.vis == Visintern || n->decl.vis == Vishidden) {
			if (!streq(declname(n), "__init__") && !streq(declname(n), "__fini__") && !streq(declname(n), "main")) {
				fprintf(fd, "static ");
			}
		}
	}
	fprintf(fd, "_Ty%d\n%s(", t->sub[0]->tid, declname(n));

	/* Insert the parameter for closure env (which may be an empty struct) */
	if (nenv > 0) {
		fprintf(fd, "struct $%s$env %s%s", declname(n), "$env", nargs ? "," : "");
	}

	if (nenv == 0 && t->nsub == 1) {
		fprintf(fd, "void");
	} else {
		for (size_t i = 1; i < t->nsub; i++) {
			fprintf(fd, "_Ty%d ", t->sub[i]->tid); //_v%ld/*%s*/%s", decltype(dcl)->tid, dcl->decl.did, declname(dcl), i + 1 == nargs ? "" : ", ");
			if (i - 1 < nargs) {
				Node *dcl = args[i - 1];
				fprintf(fd, " _v%ld /* %s */", dcl->decl.did, declname(dcl));
			}
			if (i + 1 < t->nsub) {
				fprintf(fd, ", ");
			}
		}
	}
	fprintf(fd, ")\n");
	if (init) {
		fprintf(fd, "{\n");
		emit_fnval(fd, init);
		fprintf(fd, "}\n\n");
	} else {
		fprintf(fd, ";\n");
	}
}

static void
emit_fnenvty(FILE *fd, Node *n)
{
	size_t nenv;
	Node **env;

	assert(n->type == Nfunc);

	nenv = 0;
	env = getclosure(n->func.scope, &nenv);
	fprintf(fd, "/* nid:%d nenv:%ld */\n", n->nid, nenv);
	if (nenv) {
		fprintf(fd, "struct _envty$%d {\n", n->nid);
		for (size_t i = 0; i < nenv; i++) {
			Type *envty = decltype(env[i]);
			fprintf(fd, "\t_Ty%d /* %s */ _v%ld /* %s */;\n", envty->tid, tystr(envty), env[i]->decl.did, declname(env[i]));
		}
		fprintf(fd, "};\n\n");
	}
}

static void
emit_fndef(FILE *fd, Node *n)
{
	Node **args, **env;
	size_t nargs, nenv;
	Type *t;

	assert(n->type == Nfunc);

	nenv = 0;
	nargs = 0;
	env = getclosure(n->func.scope, &nenv);
	args = n->func.args;
	nargs = n->func.nargs;
	t = n->func.type;

	fprintf(fd, "static ");
	fprintf(fd, "_Ty%d\n", t->sub[0]->tid);
	fprintf(fd, "_fn%d(", n->nid);

	if (nenv > 0) {
		fprintf(fd, "struct _envty$%d * $env%s", n->nid, nargs ? "," : "");
	}

	if (nenv == 0 && t->nsub == 1) {
		fprintf(fd, "void");
	} else {
		for (size_t i = 1; i < t->nsub; i++) {
			fprintf(fd, "_Ty%d ", t->sub[i]->tid);
			if (i - 1 < nargs) {
				Node *dcl = args[i - 1];
				fprintf(fd, " _v%ld /* %s */", dcl->decl.did, declname(dcl));
			}
			if (i + 1 < t->nsub) {
				fprintf(fd, ", ");
			}
		}
	}

	fprintf(fd, ")\n");

	fprintf(fd, "{\n");

	for (size_t i = 0; i < nenv; i++) {
		Type *envty = decltype(env[i]);
		fprintf(fd, "\t_Ty%d /* %s */ _v%ld = %s->_v%ld;\n", envty->tid, tystr(envty), env[i]->decl.did, "$env", env[i]->decl.did);
	}

	emit_func(fd, n);
	fprintf(fd, "}\n\n");
}

__attribute__((unused)) static char *
tytystr(Type *t)
{
	switch (t->type) {
	case Tybad:
		return "bad";
	case Tyvoid:
		return "void";
	case Tybool:
		return "bool";
	case Tychar:
		return "char";
	case Tyint8:
		return "int8";
	case Tyint16:
		return "int16";
	case Tyint:
		return "int";
	case Tyint32:
		return "int32";
	case Tyint64:
		return "int64";
	case Tybyte:
		return "byte";
	case Tyuint8:
		return "uint8";
	case Tyuint16:
		return "uint16";
	case Tyuint:
		return "uint";
	case Tyuint32:
		return "uint32";
	case Tyuint64:
		return "uint64";
	case Tyflt32:
		return "flt32";
	case Tyflt64:
		return "flt64";
	case Tyvalist:
		return "...";
	case Tyvar:
		return "$n";
	case Typtr:
		return "ptr";
	case Tyslice:
		return "slice";
	case Tyarray:
		return "array";
	case Tycode:
		return "code";
	case Tyfunc:
		return "func";
	case Tytuple:
		return "tuple";
	case Typaram:
		return "param";
	case Tyunres:
		return "unresolved";
	case Tyname:
		return "name";
	case Tygeneric:
		return "generic";
	case Tystruct:
		return "struct";
	case Tyunion:
		return "union";
	case Ntypes:
		return "not a type";
	}
	return "not a type";
}

static void
emit_typedef_rec(FILE *fd, Type *t, Bitset *visited)
{
	size_t i;
	int hasns;

	if (!t) {
		return;
	}
	while (tytab[t->tid])
		t = tytab[t->tid];

	fprintf(fd, "/* tid: %d visited:%d type: %s %s */\n", t->tid, bshas(visited, t->tid), tytystr(t), tystr(t));

	if (bshas(visited, t->tid)) {
		return;
	}
	bsput(visited, t->tid);

	switch (t->type) {
	case Tyvoid:
		fprintf(fd, "typedef void _Ty%d; /* Tyvoid */\n", t->tid);
		break;
	case Tybool:
		fprintf(fd, "typedef bool _Ty%d; /* Tybool */\n", t->tid);
		break;
	case Tychar:
		fprintf(fd, "typedef char _Ty%d; /* Tychar */\n", t->tid);
		break;
	case Tyint8:
		fprintf(fd, "typedef int8_t _Ty%d; /* Tyint8 */\n", t->tid);
		break;
	case Tyint16:
		fprintf(fd, "typedef int8_t _Ty%d; /* Tyint16 */\n", t->tid);
		break;
	case Tyint32:
		fprintf(fd, "typedef int8_t _Ty%d; /* Tyint32 */\n", t->tid);
		break;
	case Tyint:
		fprintf(fd, "typedef int _Ty%d; /* Tyint */\n", t->tid);
		break;
	case Tyint64:
		fprintf(fd, "typedef int64_t _Ty%d; /* Tyint64 */\n", t->tid);
		break;
	case Tybyte:
		fprintf(fd, "typedef uint8_t _Ty%d; /* Tybyte */\n", t->tid);
		break;
	case Tyuint8:
		fprintf(fd, "typedef uint8_t _Ty%d; /* Tyuint8 */\n", t->tid);
		break;
	case Tyuint16:
		fprintf(fd, "typedef uint16_t _Ty%d; /* Tyuint16 */\n", t->tid);
		break;
	case Tyuint32:
		fprintf(fd, "typedef uint32_t _Ty%d; /* Tyuint32_t*/\n", t->tid);
		break;
	case Tyuint:
		fprintf(fd, "typedef unsigned int _Ty%d; /* Tyuint */\n", t->tid);
		break;
	case Tyuint64:
		fprintf(fd, "typedef uint64_t _Ty%d; /* Tyuint64 */\n", t->tid);
		break;
	case Tyflt32:
		fprintf(fd, "typedef float _Ty%d; /* Tyflt32 */\n", t->tid);
		break;
	case Tyflt64:
		fprintf(fd, "typedef double _Ty%d; /* Tyflt64 */\n", t->tid);
		break;
	case Tyvalist:
		fprintf(fd, "//typedef va_list _Ty%d; /* Tyvalist */\n", t->tid);
		break;
	case Typtr:
		emit_typedef_rec(fd, t->sub[0], visited);
		fprintf(fd, "typedef ");
		fprintf(fd, "_Ty%d * _Ty%d;\n", t->sub[0]->tid, t->tid);
		break;
	case Tyarray:
		emit_typedef_rec(fd, t->sub[0], visited);

		fprintf(fd, "typedef ");
		fprintf(fd, "_Ty%d _Ty%d", t->sub[0]->tid, t->tid);
		if (t->asize) {
			fprintf(fd, "[%lld]", t->asize->expr.args[0]->lit.intval);
		} else {
			fprintf(fd, "[]");
		}
		fprintf(fd, ";\n");
		break;
	case Tytuple:
		for (i = 0; i < t->nsub; i++) {
			emit_typedef_rec(fd, t->sub[i], visited);
		}
		fprintf(fd, "typedef struct {");
		for (i = 0; i < t->nsub; i++) {
			fprintf(fd, "_Ty%d _%ld;", t->sub[i]->tid, i);
		}
		fprintf(fd, "} _Ty%d;\n", t->tid);
		// fprintf(fd, "typedef ");
		// emit_type(fd, t);
		// fprintf(fd, " _Ty%d;\n", t->tid);
		break;
	case Tystruct:
		for (i = 0; i < t->nmemb; i++) {
			emit_typedef_rec(fd, decltype(t->sdecls[i]), visited);
		}
		fprintf(fd, "typedef struct {");
		for (i = 0; i < t->nmemb; i++) {
			fprintf(fd, "_Ty%d", decltype(t->sdecls[i])->tid);
			fprintf(fd, " %s;", declname(t->sdecls[i]));
		}
		fprintf(fd, "} _Ty%d;\n", t->tid);
		break;
	case Tyunion:
		for (i = 0; i < t->nmemb; i++) {
			emit_typedef_rec(fd, t->udecls[i]->etype, visited);
		}
		fprintf(fd, "typedef struct {");
		fprintf(fd, "uint32_t _tag;");
		fprintf(fd, "union {");
		for (i = 0; i < t->nmemb; i++) {
			char *ns = t->udecls[i]->name->name.ns;
			char *name = t->udecls[i]->name->name.name;
			if (t->udecls[i]->etype) {
				fprintf(fd, "_Ty%d %s%s%s;", t->udecls[i]->etype->tid, ns ? ns : "", ns ? "$" : "", name);
			} else {
				fprintf(fd, "/* no etype */\n");
			}
		}
		fprintf(fd, "};");
		fprintf(fd, "} _Ty%d;", t->tid);
		break;
	case Tyslice:
		emit_typedef_rec(fd, t->sub[0], visited);

		fprintf(fd, "typedef ");
		// emit_type(fd, t);
		fprintf(fd, "struct { _Ty%d *p; uint32_t len /* size_t */; }", t->sub[0]->tid);
		fprintf(fd, " _Ty%d;\n", t->tid);
		break;
	case Tyfunc:
		for (i = 0; i < t->nsub; i++) {
			emit_typedef_rec(fd, t->sub[i], visited);
		}
		fprintf(fd, "typedef ");
		emit_type(fd, t);
		fprintf(fd, " _Ty%d; /* Tyfunc */\n", t->tid);
		break;
	case Tyname:
	case Tygeneric:
		hasns = t->name->name.ns != NULL;
		emit_typedef_rec(fd, t->sub[0], visited);
		fprintf(fd, "typedef ");
		// emit_type(fd, t->sub[0]);
		//  fprintf(fd, " %s%s%s;\n", hasns ? t->name->name.ns : "", hasns ? "$" : "", t->name->name.name);
		fprintf(fd, "_Ty%d _Ty%d; /*%s%s%s*/\n", t->sub[0]->tid, t->tid, hasns ? t->name->name.ns : "", hasns ? "$" : "", t->name->name.name);
		break;
	case Typaram:
		fprintf(fd, "typedef struct {}");
		fprintf(fd, "_Ty%d;\n", t->tid);
		break;
	case Tyvar:
		fprintf(fd, "/* Tyvar %d*/\n", t->tid);
		emit_typedef_rec(fd, tytab[t->tid], visited);
		break;
	default:
		fprintf(stderr, "/* Invalid type: %s id: %d */\n", tystr(t), t->tid);
		assert(0);
	}
}

static void
emit_typedefs(FILE *fd)
{
	Type *t;
	Bitset *visited;
	size_t i;

	visited = mkbs();

	fprintf(fd, "/* Ntypes: %d */\n", Ntypes);
	for (i = 0; i < ntypes; i++) {
		t = types[i];
		if (!t->resolved) {
			continue;
		}
		if (t->type == Tyvalist) {
			continue;
		}

		/* Non-termainl types */
		if (bshas(visited, t->tid)) {
			continue;
		}
		emit_typedef_rec(fd, t, visited);
	}
	bsfree(visited);
}

static void
emit_includes(FILE *fd)
{
	fprintf(fd, "#include <stddef.h>\n");
	fprintf(fd, "#include <stdbool.h>\n");
	fprintf(fd, "#include <stdint.h>\n");
	fprintf(fd, "\n");
}

static void
gentype(FILE *fd, Type *ty)
{
	ty = tydedup(ty);
	if (ty->type == Tyvar || ty->isemitted)
		return;

	ty->isemitted = 1;
	emit_tydesc(fd, ty);
}

static void
gentypes(FILE *fd)
{
	Type *ty;
	size_t i;

	for (i = Ntypes; i < ntypes; i++) {
		if (!types[i]->isreflect)
			continue;
		ty = tydedup(types[i]);
		if (ty->isemitted || ty->isimport)
			continue;
		gentype(fd, ty);
	}
}

static void
scan(Node ***fnvals, size_t *nfnval, Node *n, Bitset *visited)
{
	size_t i;
	Node *init;

	if (bshas(visited, n->nid)) {
		return;
	}
	bsput(visited, n->nid);

	switch (n->type) {
	case Nblock:
		for (i = 0; i < n->block.nstmts; i++) {
			scan(fnvals, nfnval, n->block.stmts[i], visited);
		}
		break;
	case Nloopstmt:
		scan(fnvals, nfnval, n->loopstmt.init, visited);
		scan(fnvals, nfnval, n->loopstmt.body, visited);
		scan(fnvals, nfnval, n->loopstmt.step, visited);
		scan(fnvals, nfnval, n->loopstmt.cond, visited);
		break;
	case Niterstmt:
		scan(fnvals, nfnval, n->iterstmt.elt, visited);
		scan(fnvals, nfnval, n->iterstmt.seq, visited);
		scan(fnvals, nfnval, n->iterstmt.body, visited);
		break;
	case Nifstmt:
		scan(fnvals, nfnval, n->ifstmt.cond, visited);
		scan(fnvals, nfnval, n->ifstmt.iftrue, visited);
		scan(fnvals, nfnval, n->ifstmt.iffalse, visited);
		break;
	case Nmatchstmt:
		for (i = 0; i < n->matchstmt.nmatches; i++) {
			scan(fnvals, nfnval, n->matchstmt.matches[i], visited);
		}
		break;
	case Nexpr:
		switch (exprop(n)) {
		case Olit:
			switch (n->expr.args[0]->lit.littype) {
			case Lfunc:
				scan(fnvals, nfnval, n->expr.args[0]->lit.fnval->func.body, visited);
				lappend(fnvals, nfnval, n->expr.args[0]->lit.fnval);
				break;
			default:;
			}
			break;
		case Ovar:
			init = decls[n->expr.did]->decl.init;
			if (init)
				scan(fnvals, nfnval, init, visited);
			break;
		default:
			for (size_t i = 0; i < n->expr.nargs; i++) {
				scan(fnvals, nfnval, n->expr.args[i], visited);
			}
			break;
		}
		break;
	case Ndecl:
		scan(fnvals, nfnval, n->decl.init, visited);
		break;
	default:;
	}
}

static ulong
fnhash(void *p)
{
	return ((Node *)p)->nid * 366787;
}

static int
fneq(void *a, void *b)
{
	return ((Node *)a)->nid == ((Node *)b)->nid;
}

void
genc(FILE *fd)
{
	Node *n;
	size_t i;
	Node **fnvals;
	size_t nfnvals;
	Bitset *visited;
	Htab *fndcl;

	for (size_t i = 0; i < file.nfiles; i++) {
		fprintf(fd, "/* Filename: %s */\n", file.files[i]);
	}

	pushstab(file.globls);

	emit_includes(fd);
	emit_typedefs(fd);

	gentypes(fd);

	fnvals = NULL;
	nfnvals = 0;
	visited = mkbs();
	fndcl = mkht(fnhash, fneq);
	for (i = 0; i < file.nstmts; i++) {
		n = file.stmts[i];
		if (n->type != Ndecl)
			continue;
		if (isconstfn(n)) {
			htput(fndcl, n->decl.init->expr.args[0]->lit.fnval, n);
			scan(&fnvals, &nfnvals, n, visited);
			// genfuncdecl(fd, n, n->decl.init);
		} else {
			emit_objdecl(fd, n);
		}
	}
	htfree(fndcl);
	bsfree(visited);

	/* Output all struct defining func env */
	for (i = 0; i < nfnvals; i++) {
		assert(fnvals[i]->type == Nfunc);
		fprintf(fd, "/* envty nid:%d */\n", fnvals[i]->nid);
		emit_fnenvty(fd, fnvals[i]);
	}

	/* Output all function definitions */
	for (i = 0; i < nfnvals; i++) {
		Node *n = fnvals[i];
		assert(n->type == Nfunc);
		fprintf(fd, "/* nid:%d@%i */\n", n->nid, lnum(n->loc));
		emit_fndef(fd, fnvals[i]);
	}

	popstab();

	fprintf(fd, "\n");
}
