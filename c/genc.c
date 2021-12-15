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
emit_expr(FILE *fd, Node *n)
{
	Node **args;
	size_t nargs;
	Node *dcl;

	assert(n->type == Nexpr);

	args = n->expr.args;
	switch (exprop(n)) {
	case Ovar:
		dcl = decls[n->expr.did];
		if (dcl->decl.isextern) {
			fprintf(fd, "%s /* did: %ld */", declname(dcl), dcl->decl.did);
		} else {
			fprintf(fd, "_v%ld /* %s */", dcl->decl.did, declname(dcl));
		}
		break;
	case Olit:
		switch (args[0]->lit.littype) {
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
		case Lint:
			fprintf(fd, "%lld", args[0]->lit.intval);
			break;
		case Lchr:
			fprintf(fd, "'%c'", args[0]->lit.chrval);
			break;
		case Lbool:
			fprintf(fd, "%s", args[0]->lit.boolval ? "true" : "false");
			break;
		case Lflt:
			fprintf(fd, "%f", args[0]->lit.fltval);
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
	case Ocast:
		fprintf(fd, "((_Ty%d)(", exprtype(n)->tid);
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, "))");
		break;
	case Oret:
		fprintf(fd, "return ");
		emit_expr(fd, n->expr.args[0]);
		fprintf(fd, ";");
		break;
	case Ocall:
		assert(n->expr.args[0]->type == Nexpr);
		assert(n->expr.args[0]->expr.op == Ovar);
		dcl = decls[n->expr.args[0]->expr.did];
		nargs = n->expr.nargs;
		if (dcl->decl.name->name.ns) {
			fprintf(fd, "%s$", dcl->decl.name->name.ns);
		}
		fprintf(fd, "%s(", declname(dcl));
		for (size_t i = 1; i < nargs; i++) {
			emit_expr(fd, n->expr.args[i]);
			if (i + 1 < nargs) {
				fprintf(fd, " ,");
			}
		}
		fprintf(fd, ")");
		break;
	case Otupget:
		assert(n->expr.args[0]->type == Nexpr);
		assert(n->expr.args[1]->expr.op == Olit);
		assert(n->expr.args[1]->expr.args[0]->lit.littype == Lint);
		fprintf(fd, "((_v%d).", n->expr.args[0]->nid);
		fprintf(fd, "_%llu)", n->expr.args[1]->expr.args[0]->lit.intval);
		break;
	case Oasn:
		break;
	case Oaddr:
		fprintf(fd, "&");
		emit_expr(fd, n->expr.args[0]);
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
	fprintf(fd, "; /* %s */ \n", declname(n));
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

static void
genfuncdecl(FILE *fd, Node *n)
{
	Type *t;
	Node *init;
	Node **args, **env;
	size_t nargs, nenv;

	t = decltype(n);
	init = n->decl.init;

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
			fprintf(fd, "_Ty%d %s%s%s;", t->udecls[i]->etype->tid, ns ? ns : "", ns ? "$" : "", name);
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
		if (tytab[t->tid] && t->type != Tyvar) {
			fprintf(stderr, "TYPE %s -> %s reolve:%d\n", tytystr((t)), tytystr(tytab[t->tid]), t->resolved);
			// assert(t->type == Tyvar);
		}
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

void
genc(FILE *fd)
{
	Node *n;
	size_t i;

	for (size_t i = 0; i < file.nfiles; i++) {
		fprintf(fd, "/* Filename: %s */\n", file.files[i]);
	}

	pushstab(file.globls);

	emit_includes(fd);
	emit_typedefs(fd);

	for (i = 0; i < file.nstmts; i++) {
		n = file.stmts[i];
		switch (n->type) {
		case Nuse: /* nothing to do */
		case Nimpl:
			break;
		case Ndecl:
			// n = flattenfn(n);
			if (isconstfn(n)) {
				if (!getenv("D"))
					genfuncdecl(fd, n);
				else
					dumpn(n, stderr);
			} else {
				emit_objdecl(fd, n);
			}
			break;
		default:
			die("Bad node %s in toplevel", nodestr[n->type]);
			break;
		}
	}
	popstab();

	fprintf(fd, "\n");

	fclose(fd);
}
