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
 * Conventions:
 * 1. Types are named '_Ty{tid}'
 * 2. Struct types of type descriptors are named '_Tydesc{tid}'
 * 3. Symbol names of type descriptors are named by tydescid()
 * 4. Variables are named '_v{did}'
 * 5. function literals are named '_fn{lit.fnval->nid}'
 */


char *
asmname(Node *dcl)
{
	char buf[1024];
	char *vis, *pf, *ns, *name, *sep;
	Node *n;

	n = dcl->decl.name;
	pf = Symprefix;
	ns = n->name.ns;
	name = n->name.name;
	vis = "";
	sep = "";
	//if (asmsyntax == Plan9)
	//	if (islocal(dcl))
	//		vis = "<>";
	if (!ns || !ns[0])
		ns = "";
	else
		sep = "$";
	if (name[0] == '.')
		pf = "";

	bprintf(buf, sizeof buf, "%s%s%s%s%s", pf, ns, sep, name, vis);
	return strdup(buf);
}

char *
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
		bprintf(buf, bufsz, "_tydesc%s%s$%d",sep, ns, ty->tid);
	}
	return buf;
}

static void
fillglobls(Stab *st, Htab *globls)
{
	size_t i, j, nk, nns;
	void **k, **ns;
	Stab *stab;
	Node *s;

	k = htkeys(st->dcl, &nk);
	for (i = 0; i < nk; i++) {
		s = htget(st->dcl, k[i]);
		//if (isconstfn(s))
		//	s->decl.type = codetype(s->decl.type);
		htput(globls, s, asmname(s));
	}
	free(k);

	ns = htkeys(file.ns, &nns);
	for (j = 0; j < nns; j++) {
		stab = htget(file.ns, ns[j]);
		k = htkeys(stab->dcl, &nk);
		for (i = 0; i < nk; i++) {
			s = htget(stab->dcl, k[i]);
			htput(globls, s, asmname(s));
		}
		free(k);
	}
	free(ns);
}

char *
genlocallblstr(char *buf, size_t sz)
{
	return genlblstr(buf, 128, "");
}


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
		fprintf(fd, "uintptr_t _tag;");
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
		fprintf(fd, "*p; size_t len /* size_t */; }");
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
		//if (dcl->decl.name->name.ns) {
		//	fprintf(fd, "%s$", dcl->decl.name->name.ns);
		//}
		//fprintf(fd, "%s", declname(dcl));
		fprintf(fd, "%s", asmname(dcl));
	}
	fprintf(fd, "(");
	if (nenv > 0) {
		fprintf(fd, "%s &(struct _envty$%d){", nargs > 0 ? "," : "", n->expr.args[0]->expr.args[0]->lit.fnval->nid);
		for (i = 0; i < nenv; i++) {
			//fprintf(fd, "\t._v%ld = ", env[i]->decl.did);
			if (env[i]->decl.isglobl)
				fprintf(fd, "%s,\n", asmname(env[i]));
			else
				fprintf(fd, "_v%ld,\n", env[i]->decl.did);
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
	Ucon *uc;

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
			fprintf(fd, "_fn%d,", args[0]->lit.fnval->nid);
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
	case Oarr:
	case Ostruct:
		fprintf(fd, "(");
		fprintf(fd, "(const _Ty%d)", tysearch(exprtype(n))->tid);

		fprintf(fd," {");
		for (size_t i = 0; i < n->expr.nargs; i++) {
			emit_expr(fd, n->expr.args[i]);
			if (i + 1 < n->expr.nargs) {
				fprintf(fd, ", ");
			}
		}
		fprintf(fd, "})");
		break;
	case Oucon:
		uc = finducon(tybase(exprtype(n)), n->expr.args[0]);
		fprintf(fd, "(");
		fprintf(fd, "(const _Ty%d)", tysearch(exprtype(n))->tid);
		fprintf(fd," {");
		fprintf(fd, "._utag = %ld,", uc->id);
		if (n->expr.args[1]) {
			fprintf(fd, "._udata = {");
			emit_expr(fd, n->expr.args[1]);
			fprintf(fd, "},");
		}
		fprintf(fd, "})");
		break;
	case Oadd:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "+");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Osub:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "-");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Omul:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "*");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Odiv:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "/");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Omod:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "%%");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Oneg:
		fprintf(fd, "-");
		emit_expr(fd, args[0]);
		break;
	case Obor:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "|");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Oband:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "&");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Obxor:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "^");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Obsl:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "<<");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Obsr:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, ">>");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
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
		fprintf(fd, "(");
		fprintf(fd, "&");
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, ")");
		break;
	case Oderef:
		fprintf(fd, "(");
		fprintf(fd, "*");
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, ")");
		break;
	case Olor:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "||");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Oland:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "&&");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Olnot:
		fprintf(fd, "!");
		emit_expr(fd, args[0]);
		break;
	case Oeq:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "==");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case One:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "!=");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Ogt:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, ">");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Oge:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, ">=");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Olt:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "<");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
		break;
	case Ole:
		fprintf(fd, "(");
		emit_expr(fd, args[0]);
		fprintf(fd, "<=");
		emit_expr(fd, args[1]);
		fprintf(fd, ")");
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
		fprintf(fd, "(_Ty%d){", n->expr.type->tid);
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, "+ %lld", n->expr.args[1]->lit.intval);
		fprintf(fd, ", %lld}", args[2]->lit.intval);
		break;
	case Omemb:
		emit_expr(fd, args[0]);
		fprintf(fd, "%s%s", args[0]->expr.type->type == Typtr ? "->" : ".", namestr(args[1]));
		break;
	case Otupmemb:
		assert(0);
		break;
	case Osize:
		fprintf(fd, "sizeof(");
		fprintf(fd, "_Ty%d", args[0]->decl.type->tid);
		fprintf(fd, ")");
		break;
	case Ocall:
		emit_call(fd, n);
		break;
	case Ocast:
		fprintf(fd, "((_Ty%d)(", exprtype(n)->tid);
		switch (exprtype(n->expr.args[0])->type) {
		case Tyslice:
			emit_expr(fd, n->expr.args[0]);
			fprintf(fd, ".p");
			break;
		default:
			emit_expr(fd, n->expr.args[0]);
		}
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
	case Outag:
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, "._utag");
		break;
	case Oudata:
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, "._udata");
		break;
	case Ovar:
		dcl = decls[n->expr.did];
		if (dcl->decl.isextern) {
			fprintf(fd, "%s /* did: %ld */", asmname(dcl), dcl->decl.did);
		} else if (dcl->decl.isglobl) {
			fprintf(fd, "%s " , asmname(dcl));
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
	char name[256];

	if (n->decl.isextern) {
		fprintf(fd, "extern ");
	}
	if (!n->decl.isextern && n->decl.isglobl) {
		if (n->decl.vis == Visintern || n->decl.vis == Vishidden) {
			fprintf(fd, "static ");
		}
	}

	if (n->decl.isconst) {
		fprintf(fd, "const ");
	}

	fprintf(fd, "_Ty%d ", tysearch(decltype(n))->tid);
	if (n->decl.isextern) {
		snprintf(name, sizeof(name), "%s", asmname(n));
	} else if(n->decl.isglobl) {
		snprintf(name, sizeof(name), "%s", asmname(n));
	} else {
		snprintf(name, sizeof(name), "_v%ld", n->decl.did);
	}
	fprintf(fd, "%s", name);

	if (n->decl.init) {
		fprintf(fd, " = ");
		emit_expr(fd, n->decl.init);
	}
	fprintf(fd, ";\n");
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

	assert(n->type == Nblock || n->type == Ndecl || n->type == Nexpr || n->type == Nifstmt || n->type == Nmatchstmt || n->type == Nloopstmt);

	fprintf(fd, "/* ntype:%s */\n", nodestr[n->type]);
	switch (n->type) {
	case Nblock:
		emit_block(fd, n);
		break;
	case Ndecl:
		emit_objdecl(fd, n);
		break;
	case Nifstmt:
		fprintf(fd, "if (");
		emit_expr(fd, n->ifstmt.cond);
		fprintf(fd, ") {\n");
		emit_stmt(fd, n->ifstmt.iftrue);
		if (n->ifstmt.iffalse) {
			fprintf(fd, "} else {");
			emit_stmt(fd, n->ifstmt.iffalse);
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

size_t
alignto(size_t sz, Type *t)
{
	return align(sz, tyalign(t));
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

/* Stolen from mc/6/simp.c */
static Node *
vatypeinfo(Node *n)
{
	Node *ti, *tp, *td, *tn;
	Type *ft, *vt, **st;
	size_t nst, i;
	char buf[1024];

	st = NULL;
	nst = 0;
	ft = exprtype(n->expr.args[0]);
	/* The structure of ft->sub:
	 *   [return, normal, args, ...]
	 *
	 * The structure of n->expr.sub:
	 *    [fn, normal, args, , variadic, args]
	 *
	 * We want to start at variadic, so we want
	 * to count from ft->nsub - 1, up to n->expr.nsub.
	 */
	for (i = ft->nsub - 1; i < n->expr.nargs; i++) {
		lappend(&st, &nst, exprtype(n->expr.args[i]));
	}
	vt = mktytuple(n->loc, st, nst);
	tagreflect(vt);

	/* make the decl */
	tn = mkname(Zloc, tydescid(buf, sizeof buf, vt));
	td = mkdecl(Zloc, tn, mktype(n->loc, Tybyte));
	td->decl.isglobl = 1;
	td->decl.isconst = 1;
	td->decl.ishidden = 1;

	/* and the var */
	ti = mkexpr(Zloc, Ovar, tn, NULL);
	ti->expr.type = td->decl.type;
	ti->expr.did = td->decl.did;

	/* and the pointer */
	tp = mkexpr(Zloc, Oaddr, ti, NULL);
	tp->expr.type = mktyptr(n->loc, td->decl.type);

	//htput(s->globls, td, asmname(td));
	return tp;
}

void
genfuncdecl(FILE *fd, Node *n, Node *init)
{
	Type *t;
	Node **args, **env;
	size_t nargs, nenv;

	t = decltype(n);

	assert(n->type == Ndecl);
	assert(t->type == Tyfunc || t->type == Tycode);
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

	fprintf(fd, "/* vis:%d isimport:%d\n*/\n", n->decl.vis, n->decl.isimport);
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
	fprintf(fd, "_Ty%d ", t->sub[0]->tid);
	fprintf(fd, "%s(", asmname(n));

	if (nenv > 0) {
		fprintf(fd, ", struct $%s$env %s%s", declname(n), "$env", nargs ? "," : "");
	}

	/* Insert the parameter for closure env (which may be an empty struct) */
	if (nenv == 0 && t->nsub == 1) {
		fprintf(fd, "void");
	} else {
		for (size_t i = 1; i < t->nsub; i++) {
			if (t->sub[i]->type == Tyvalist)
				fprintf(fd, "...");
			else
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

	fprintf(fd, ")");
	if (init) {
		fprintf(fd, "\n{\n");
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
emit_fndef(FILE *fd, Node *n, Node *dcl)
{
	Node **args, **env;
	size_t nargs, nenv;
	Type *t;

	assert(n->type == Nfunc);
	assert(dcl == NULL || dcl->type == Ndecl);

	nenv = 0;
	nargs = 0;
	env = getclosure(n->func.scope, &nenv);
	args = n->func.args;
	nargs = n->func.nargs;
	t = n->func.type;

	if (!n->decl.isextern && n->decl.isglobl) {
		if (n->decl.vis == Visintern) {
			if (!streq(declname(n), "__init__") && !streq(declname(n), "__fini__") && !streq(declname(n), "main")) {
				fprintf(fd, "static ");
			}
		}
	}

	fprintf(fd, "_Ty%d\n", t->sub[0]->tid);

	if (dcl)
		fprintf(fd, "%s(", asmname(dcl));
	else
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
emit_forward_decl_rec(FILE *fd, Type *t, Bitset *visited)
{
	Type *tn, *ts;
	if (!t) {
		return;
	}

	t = tysearch(t);
	switch (t->type) {
	case Typtr:
		if (t->sub) {
			tn = tysearch(t->sub[0]);
			if (tn->type == Tyname) {
				ts = tysearch(tn->sub[0]);
				if (ts->type == Tystruct) {
					fprintf(fd, "struct _Ty%d;\n", ts->tid);
					fprintf(fd, "typedef struct _Ty%d _Ty%d;/*ty=%s -> %s*/\n", ts->tid, ts->tid, tytystr(ts), tytystr(ts));
					fprintf(fd, "typedef _Ty%d _Ty%d;\n", ts->tid, tn->tid);
					fprintf(fd, "typedef _Ty%d *_Ty%d; /*ty=%s -> %s*/\n", tn->tid, t->tid, tytystr(tn), tytystr(t));
				}
			}
		}
		break;
	default:
		;
	}
}

static void
emit_typedef_rec(FILE *fd, Type *t, Bitset *visited)
{
	size_t i;
	int hasns;

	if (!t) {
		return;
	}
	t = tysearch(t);

	if (bshas(visited, t->tid)) {
		return;
	}
	bsput(visited, t->tid);
	fprintf(fd, "/* tid: %d visited:%d type: %s %s */\n", t->tid, bshas(visited, t->tid), tytystr(t), tystr(t));

	switch (t->type) {
	case Tyvoid:
		fprintf(fd, "typedef void _Ty%d; /* Tyvoid */", t->tid);
		break;
	case Tybool:
		fprintf(fd, "typedef bool _Ty%d; /* Tybool */", t->tid);
		break;
	case Tychar:
		fprintf(fd, "typedef char _Ty%d; /* Tychar */", t->tid);
		break;
	case Tyint8:
		fprintf(fd, "typedef int8_t _Ty%d; /* Tyint8 */", t->tid);
		break;
	case Tyint16:
		fprintf(fd, "typedef int8_t _Ty%d; /* Tyint16 */", t->tid);
		break;
	case Tyint32:
		fprintf(fd, "typedef int8_t _Ty%d; /* Tyint32 */", t->tid);
		break;
	case Tyint:
		fprintf(fd, "typedef int _Ty%d; /* Tyint */", t->tid);
		break;
	case Tyint64:
		fprintf(fd, "typedef int64_t _Ty%d; /* Tyint64 */", t->tid);
		break;
	case Tybyte:
		fprintf(fd, "typedef uint8_t _Ty%d; /* Tybyte */", t->tid);
		break;
	case Tyuint8:
		fprintf(fd, "typedef uint8_t _Ty%d; /* Tyuint8 */", t->tid);
		break;
	case Tyuint16:
		fprintf(fd, "typedef uint16_t _Ty%d; /* Tyuint16 */", t->tid);
		break;
	case Tyuint32:
		fprintf(fd, "typedef uint32_t _Ty%d; /* Tyuint32_t*/", t->tid);
		break;
	case Tyuint:
		fprintf(fd, "typedef unsigned int _Ty%d; /* Tyuint */", t->tid);
		break;
	case Tyuint64:
		fprintf(fd, "typedef uint64_t _Ty%d; /* Tyuint64 */", t->tid);
		break;
	case Tyflt32:
		fprintf(fd, "typedef float _Ty%d; /* Tyflt32 */", t->tid);
		break;
	case Tyflt64:
		fprintf(fd, "typedef double _Ty%d; /* Tyflt64 */", t->tid);
		break;
	case Tyvalist:
		fprintf(fd, "typedef __builtin_va_list _Ty%d; /* Tyvalist */", t->tid);
		break;
	case Typtr:
		emit_typedef_rec(fd, t->sub[0], visited);
		fprintf(fd, "typedef ");
		fprintf(fd, "_Ty%d * _Ty%d;", t->sub[0]->tid, t->tid);
		fprintf(fd, "/* %s -> %s*/", tytystr(t->sub[0]), tytystr(tybase(t->sub[0])));
		break;
	case Tyarray:
		emit_typedef_rec(fd, t->sub[0], visited);

		fprintf(fd, "typedef struct {");
		fprintf(fd, "_Ty%d ", t->sub[0]->tid);
		if (t->asize) {
			fprintf(fd, "elem[%lld];", t->asize->expr.args[0]->lit.intval);
		} else {
			fprintf(fd, "elem[0];");
		}
		fprintf(fd, "} _Ty%d;", t->tid);
		break;
	case Tytuple:
		for (i = 0; i < t->nsub; i++) {
			emit_typedef_rec(fd, t->sub[i], visited);
		}
		fprintf(fd, "typedef struct {");
		for (i = 0; i < t->nsub; i++) {
			fprintf(fd, "_Ty%d _%ld;", t->sub[i]->tid, i);
		}
		fprintf(fd, "} _Ty%d;", t->tid);
		// fprintf(fd, "typedef ");
		// emit_type(fd, t);
		// fprintf(fd, " _Ty%d;\n", t->tid);
		break;
	case Tystruct:
		for (i = 0; i < t->nmemb; i++) {
			emit_typedef_rec(fd, decltype(t->sdecls[i]), visited);
		}
		//fprintf(fd, "typedef struct {");
		fprintf(fd, "struct _Ty%d {", t->tid);
		for (i = 0; i < t->nmemb; i++) {
			fprintf(fd, "_Ty%d", decltype(t->sdecls[i])->tid);
			fprintf(fd, " %s;", declname(t->sdecls[i]));
		}
		//fprintf(fd, "} _Ty%d;", t->tid);
		fprintf(fd, "};\n");
		fprintf(fd, "typedef struct _Ty%d _Ty%d;\n", t->tid, t->tid);
		break;
	case Tyunion:
		for (i = 0; i < t->nmemb; i++) {
			emit_typedef_rec(fd, t->udecls[i]->etype, visited);
		}
		fprintf(fd, "typedef struct {");
		fprintf(fd, "uintptr_t _utag;");
		fprintf(fd, "union {");
		for (i = 0; i < t->nmemb; i++) {
			char *ns = t->udecls[i]->name->name.ns;
			char *name = t->udecls[i]->name->name.name;
			if (t->udecls[i]->etype) {
				fprintf(fd, "_Ty%d %s%s%s;", t->udecls[i]->etype->tid, ns ? ns : "", ns ? "$" : "", name);
			} else {
				fprintf(fd, "/* no etype */");
			}
		}
		fprintf(fd, "} _udata;");
		fprintf(fd, "} _Ty%d;", t->tid);
		break;
	case Tyslice:
		emit_typedef_rec(fd, t->sub[0], visited);

		fprintf(fd, "typedef ");
		// emit_type(fd, t);
		fprintf(fd, "struct { _Ty%d *p; size_t len; }", t->sub[0]->tid);
		fprintf(fd, " _Ty%d;", t->tid);
		break;
	case Tyfunc:
		for (i = 0; i < t->nsub; i++) {
			emit_typedef_rec(fd, t->sub[i], visited);
		}
		fprintf(fd, "typedef ");
		emit_type(fd, t);
		fprintf(fd, " _Ty%d; /* Tyfunc */", t->tid);
		break;
	case Tyname:
	case Tygeneric:
		emit_typedef_rec(fd, t->sub[0], visited);

		hasns = t->name->name.ns != NULL;
		fprintf(fd, "typedef ");
		// emit_type(fd, t->sub[0]);
		//  fprintf(fd, " %s%s%s;\n", hasns ? t->name->name.ns : "", hasns ? "$" : "", t->name->name.name);
		fprintf(fd, "_Ty%d _Ty%d; /*%s%s%s*/", t->sub[0]->tid, t->tid, hasns ? t->name->name.ns : "", hasns ? "$" : "", t->name->name.name);
		//fprintf(fd, "struct { _Ty%d _; } _Ty%d ;; /*%s%s%s*/", t->sub[0]->tid, t->tid, hasns ? t->name->name.ns : "", hasns ? "$" : "", t->name->name.name);
		break;
	case Typaram:
		fprintf(fd, "typedef struct {}");
		fprintf(fd, "_Ty%d;", t->tid);
		break;
	case Tyvar:
		fprintf(fd, "/* Tyvar %d*/", t->tid);
		emit_typedef_rec(fd, tytab[t->tid], visited);
		break;
	default:
		fprintf(stderr, "/* Invalid type: %s id: %d */", tystr(t), t->tid);
		assert(0);
	}
	fprintf(fd, "/* %s */\n", tytystr(t));
}

static void
emit_typedefs(FILE *fd)
{
	Type *t;
	Bitset *visited;
	size_t i;

	fprintf(fd, "/* Ntypes: %d */\n", Ntypes);
#if 0
	for (i = 0; i < ntypes; i++) {
		Type *u;
		t = types[i];
		u = tytab[t->tid];
		fprintf(fd, "/* type _Ty%d -> _Ty%d (ty=%s) resolved:%d */\n", t->tid, u ? u->tid : -1, tytystr(t), t->resolved);
	}
#endif

	visited = mkbs();

	fprintf(fd, "/* START OF FORWARD DECLARATIONS */\n");
	for (i = 0; i < ntypes; i++) {
		t = types[i];
		emit_forward_decl_rec(fd, t, visited);
	}
	fprintf(fd, "/* END OF FORWARD DECLARATIONS */\n");

	bsclear(visited);
	for (i = 0; i < ntypes; i++) {
		t = tysearch(types[i]);
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
	fprintf(fd, "#include <stdarg.h>\n");
	fprintf(fd, "\n");
}

static size_t
encodemin(FILE *fd, uvlong val)
{
	size_t i, shift, bytes;
	uint8_t b;

	if (fd)
		fprintf(fd, "{");

	if (val < 128) {
		if (fd)
			fprintf(fd, " %lld},", val);
		return 1;
	}

	for (i = 1; i < 8; i++)
		if (val < 1ULL << (7*i))
			break;
	shift = 8 - i;
	b = ~0ull << (shift + 1);
	b |= val & ~(~0ull << shift);
	bytes = 1;
	if (fd)
		fprintf(fd, " 0x%02x,", b);
	val >>=  shift;
	while (val != 0) {
		if(fd)
			fprintf(fd, " 0x%02x,", (uint)val & 0xff);
		val >>= 8;
		bytes++;
	}

	if (fd)
		fprintf(fd, "},\n");

	return bytes;
}

static void
writeblob_struct(FILE *fd, Blob *b, size_t *count)
{
	size_t i;

	if (!b)
		return;
	switch (b->type) {
	case Btimin:	fprintf(fd, "\tuint8_t _iminv%ld[%ld];\n", (*count)++, encodemin(NULL, b->ival)); break;
	case Bti8:	fprintf(fd, "\tuint8_t _i8v%ld;\n", (*count)++);	break;
	case Bti16:	fprintf(fd, "\tuint16_t _i16v%ld;\n", (*count)++);	break;
	case Bti32:	fprintf(fd, "\tuint32_t _i32v%ld;\n", (*count)++);	break;
	case Bti64:	fprintf(fd, "\tuint64_t _i64v%ld;\n", (*count)++);	break;
	case Btbytes:	fprintf(fd, "\tuint8_t _bytesv%ld[%ld];\n", (*count)++, b->bytes.len);	break;
	case Btpad:	fprintf(fd, "\tuint8_t  _pad%ld[%lld];\n", (*count)++, b->npad);	break;
	case Btref:	fprintf(fd, "\tvoid * _ref%ld;\n", (*count)++);	break;
	case Btseq:
		for (i = 0; i < b->seq.nsub; i++)
			writeblob_struct(fd, b->seq.sub[i], count);
		break;
	}
}

static void
writebytes(FILE *fd, char *p, size_t sz)
{
	size_t i;

	fprintf(fd, "{");
	for (i = 0; i < sz; i++) {
		if (isprint(p[i]))
			fprintf(fd, " '%c',", p[i]);
		else
			fprintf(fd, " \\%03o,", (uint8_t)p[i] & 0xff);
		/* line wrapping for readability */
		if (i % 60 == 59)
			fprintf(fd, "\n");
	}
	fprintf(fd, "},\n");
}

static void
writeblob(FILE *fd, Blob *b)
{
	size_t i;

	if (!b)
		return;
	switch (b->type) {
	case Btimin:	encodemin(fd, b->ival);	break;
	case Bti8:	fprintf(fd, " 0x%02llx,\n", b->ival);	break;
	case Bti16:	fprintf(fd, " 0x%04llx,\n", b->ival);	break;
	case Bti32:	fprintf(fd, " 0x%08llx,\n", b->ival);	break;
	case Bti64:	fprintf(fd, " 0x%016llx,\n", b->ival);	break;
	case Btbytes:	writebytes(fd, b->bytes.buf, b->bytes.len);	break;
	case Btpad:	fprintf(fd, " {0,},\n");	break;
	case Btref:	fprintf(fd, " (char *)&%s + %zd,\n", b->ref.str, b->ref.off);	break;
	case Btseq:
		for (i = 0; i < b->seq.nsub; i++)
			writeblob(fd, b->seq.sub[i]);
		break;
	}
}

static void
gentype(FILE *fd, Type *ty)
{
	Blob *b;
	size_t blob_id;
	char buf[512];

	ty = tydedup(ty);
	if (ty->type == Tyvar)
		return;

	b = tydescblob(ty);
	if (b->isglobl)
		b->iscomdat = 1;
	//if (asmsyntax == Gnugaself)
	//	fprintf(fd, ".section .data.%s,\"aw\",@progbits\n", b->lbl);
	
	blob_id = 0;
	fprintf(fd, "const struct _Tydesc%d {\n", ty->tid);
	writeblob_struct(fd, b, &blob_id);
	fprintf(fd, "} %s = {\n", tydescid(buf, sizeof buf, ty));
	writeblob(fd, b);
	fprintf(fd, "};\n");

	blobfree(b);
}

static void
emit_prototypes(FILE *fd, Htab *globls, Node **fnvals, size_t nfnvals)
{
	void **k;
	Node *n;
	size_t i, nk;

	fprintf(fd, "/* START OF EXTERNS */\n");
	k = htkeys(globls, &nk);
	for (i = 0; i < nk; i++) {
		n = k[i];
		if (decltype(n)->type != Tyfunc && !n->decl.isextern)
			continue;
		if (!decltype(n)->resolved)
			continue;
		switch (decltype(n)->type) {
		case Tyfunc:
			genfuncdecl(fd, n, NULL);
			break;
		default:
			emit_objdecl(fd, n);
		}
	}
	fprintf(fd, "/* END OF EXTERNS */\n");
}

static void
gentypes(FILE *fd)
{
	Type *ty;
	size_t i, nreflects;
	Type **reflects;
	char buf[512];


	reflects = NULL;
	nreflects = 0;
	/* Forward declarations */
	for (i = Ntypes; i < ntypes; i++) {
		if (!types[i]->isreflect)
			continue;
		ty = tydedup(types[i]);
		if (ty->isemitted)
			continue;
		ty->isemitted = 1;
		lappend(&reflects, &nreflects, ty);

		fprintf(fd, "extern const struct _Tydesc%d %s;\n", ty->tid, tydescid(buf, sizeof buf, ty));
	}

	for (i = 0; i < nreflects; i++) {
		ty = reflects[i];
		if (ty->isimport)
			continue;
		gentype(fd, ty);
	}
	fprintf(fd, "\n");
}

static void
scan(Node ***fnvals, size_t *nfnval, Node ***fncalls, size_t *nfncalls, Node *n, Bitset *visited)
{
	size_t i;
	Node *init;

	if (n == NULL || bshas(visited, n->nid)) {
		return;
	}
	bsput(visited, n->nid);

	switch (n->type) {
	case Nblock:
		for (i = 0; i < n->block.nstmts; i++) {
			scan(fnvals, nfnval, fncalls, nfncalls, n->block.stmts[i], visited);
		}
		break;
	case Nloopstmt:
		scan(fnvals, nfnval, fncalls, nfncalls, n->loopstmt.init, visited);
		scan(fnvals, nfnval, fncalls, nfncalls, n->loopstmt.body, visited);
		scan(fnvals, nfnval, fncalls, nfncalls, n->loopstmt.step, visited);
		scan(fnvals, nfnval, fncalls, nfncalls, n->loopstmt.cond, visited);
		break;
	case Niterstmt:
		scan(fnvals, nfnval, fncalls, nfncalls, n->iterstmt.elt, visited);
		scan(fnvals, nfnval, fncalls, nfncalls, n->iterstmt.seq, visited);
		scan(fnvals, nfnval, fncalls, nfncalls, n->iterstmt.body, visited);
		break;
	case Nifstmt:
		scan(fnvals, nfnval, fncalls, nfncalls, n->ifstmt.cond, visited);
		scan(fnvals, nfnval, fncalls, nfncalls, n->ifstmt.iftrue, visited);
		scan(fnvals, nfnval, fncalls, nfncalls, n->ifstmt.iffalse, visited);
		break;
	case Nmatchstmt:
		for (i = 0; i < n->matchstmt.nmatches; i++) {
			scan(fnvals, nfnval, fncalls, nfncalls, n->matchstmt.matches[i], visited);
		}
		break;
	case Nexpr:
		switch (exprop(n)) {
		case Olit:
			switch (n->expr.args[0]->lit.littype) {
			case Lfunc:
				scan(fnvals, nfnval, fncalls, nfncalls, n->expr.args[0]->lit.fnval->func.body, visited);
				lappend(fnvals, nfnval, n->expr.args[0]->lit.fnval);
				break;
			default:;
			}
			break;
		case Ocall:
			lappend(fncalls, nfncalls, n);
			for (i = 0; i < n->expr.nargs; i++)
				scan(fnvals, nfnval, fncalls, nfncalls, n->expr.args[i], visited);
			break;
		case Ovar:
			init = decls[n->expr.did]->decl.init;
			if (init)
				scan(fnvals, nfnval, fncalls, nfncalls, init, visited);
			break;
		default:
			for (size_t i = 0; i < n->expr.nargs; i++) {
				scan(fnvals, nfnval, fncalls, nfncalls, n->expr.args[i], visited);
			}
			break;
		}
		break;
	case Ndecl:
		scan(fnvals, nfnval, fncalls, nfncalls, n->decl.init, visited);
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
	Node **fnvals, **fncalls, **objdecls;
	size_t nfnvals, nfncalls, nobjdecls;
	Bitset *visited;
	Htab *fndcl;
	Htab *globls;

	globls = mkht(varhash, vareq);
	fillglobls(file.globls, globls);
	pushstab(file.globls);

	fnvals = NULL;
	nfnvals = 0;
	fncalls = NULL;
	nfncalls = 0;
	objdecls = NULL;
	nobjdecls = 0;

	visited = mkbs();
	fndcl = mkht(fnhash, fneq);
	for (i = 0; i < file.nstmts; i++) {
		n = file.stmts[i];
		if (n->type != Ndecl)
			continue;
		if (n->decl.isextern || n->decl.isgeneric)
			continue;

		if (isconstfn(n)) {
			htput(fndcl, n->decl.init->expr.args[0]->lit.fnval, n);
			scan(&fnvals, &nfnvals, &fncalls, &nfncalls, n, visited);
		} else {
			lappend(&objdecls, &nobjdecls, n);
		}
	}
	bsfree(visited);

	/* Translate valist arguments to tuple types */
	for (i = 0; i < nfncalls; i++) {
		Type *ft;
		Node *n, **args;
		size_t nargs, j;
		int notsyscall;

		n = fncalls[i];

		assert(n->type == Nexpr && exprop(n) == Ocall);

		notsyscall = 1;
		if (exprop(n->expr.args[0]) == Ovar) {
			Node *dcl = decls[n->expr.args[0]->expr.did];
			notsyscall = !streq(asmname(dcl), "sys$syscall");
		}

		ft = exprtype(n->expr.args[0]);
		args = NULL;
		nargs = 0;
		for (j = 0; j < n->expr.nargs; j++) {
			if (notsyscall && j < ft->nsub && tybase(ft->sub[j])->type == Tyvalist)
				lappend(&args, &nargs, vatypeinfo(n));
			if (tybase(exprtype(n->expr.args[j]))->type == Tyvoid)
				continue;
			lappend(&args, &nargs, n->expr.args[j]);
		}
		free(n->expr.args);
		n->expr.args = args;
		n->expr.nargs = nargs;
	}

	/* Start to output C code */
	for (size_t i = 0; i < file.nfiles; i++) {
		fprintf(fd, "/* Filename: %s */\n", file.files[i]);
	}
	emit_includes(fd);
	emit_typedefs(fd);

	/* Output all struct defining func env */
	for (i = 0; i < nfnvals; i++) {
		assert(fnvals[i]->type == Nfunc);
		emit_fnenvty(fd, fnvals[i]);
	}
	emit_prototypes(fd, globls, fnvals, nfnvals);

	/* Output type descriptors */
	gentypes(fd);

	for (i = 0; i < nobjdecls; i++) {
		emit_objdecl(fd, objdecls[i]);
	}

	/* Output all function definitions */
	for (i = 0; i < nfnvals; i++) {
		Node *dcl;
		Node *n = fnvals[i];
		assert(n->type == Nfunc);
		dcl = htget(fndcl, n);
		fprintf(fd, "/* nid:%d@%i */\n", n->nid, lnum(n->loc));
		emit_fndef(fd, fnvals[i], dcl);
	}

	popstab();

	htfree(fndcl);
	fprintf(fd, "\n");
}
