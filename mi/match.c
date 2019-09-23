#include <stdio.h>
#include <inttypes.h>
#include <stdarg.h>
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
#include "dtree.h"

Dtree *gendtree(Node *m, Node *val, Node **lbl, size_t nlbl, int startid);
Dtree *gendtree2(Node *m, Node *val, Node **lbl, size_t nlbl, int startid);
static int addpat(Node *pat, Node *val,
		Dtree *start, Dtree *accept,
		Node ***cap, size_t *ncap,
		Dtree ***end, size_t *nend);
void dtreedump(FILE *fd, Dtree *dt);


static int ndtree;

static Node *
utag(Node *n)
{
	Node *tag;

	tag = mkexpr(n->loc, Outag, n, NULL);
	tag->expr.type = mktype(n->loc, Tyint32);
	return tag;
}

static Node *
uvalue(Node *n, Type *ty)
{
	Node *elt;

	elt = mkexpr(n->loc, Oudata, n, NULL);
	elt->expr.type = ty;
	return elt;
}

static Node *
tupelt(Node *n, size_t i)
{
	Node *idx, *elt;

	idx = mkintlit(n->loc, i);
	idx->expr.type = mktype(n->loc, Tyuint64);
	elt = mkexpr(n->loc, Otupget, n, idx, NULL);
	elt->expr.type = tybase(exprtype(n))->sub[i];
	return elt;
}

static Node *
arrayelt(Node *n, size_t i)
{
	Node *idx, *elt;

	idx = mkintlit(n->loc, i);
	idx->expr.type = mktype(n->loc, Tyuint64);
	elt = mkexpr(n->loc, Oidx, n, idx, NULL);
	elt->expr.type = tybase(exprtype(n))->sub[0];
	return elt;
}

static Node *
findmemb(Node *pat, Node *name)
{
	Node *n;
	size_t i;

	for (i = 0; i < pat->expr.nargs; i++) {
		n = pat->expr.args[i];
		if (nameeq(n->expr.idx, name))
			return n;
	}
	return NULL;
}

static Dtree *
dtbytag(Dtree *t, Ucon *uc)
{
	uint32_t tagval;
	Node *taglit;
	size_t i;

	for (i = 0; i < t->npat; i++) {
		taglit = t->pat[i]->expr.args[0];
		tagval = taglit->lit.intval;
		if (tagval == uc->id) {
			return t->next[i];
		}
	}
	return NULL;
}

static Node *
structmemb(Node *n, Node *name, Type *ty)
{
	Node *elt;

	elt = mkexpr(n->loc, Omemb, n, name, NULL);
	elt->expr.type = ty;
	return elt;
}

static Node *
addcapture(Node *n, Node **cap, size_t ncap)
{
	Node **blk;
	size_t nblk, i;

	nblk = 0;
	blk = NULL;

	for (i = 0; i < ncap; i++)
		lappend(&blk, &nblk, cap[i]);
	for (i = 0; i < n->block.nstmts; i++)
		lappend(&blk, &nblk, n->block.stmts[i]);
	lfree(&n->block.stmts, &n->block.nstmts);
	n->block.stmts = blk;
	n->block.nstmts = nblk;
	return n;
}

static Dtree *
mkdtree(Srcloc loc, Node *lbl)
{
	Dtree *t;

	t = zalloc(sizeof(Dtree));
	t->lbl = lbl;
	t->loc = loc;
	t->id = ndtree++;
	return t;
}

static Dtree *
nextnode(Srcloc loc, size_t idx, size_t count, Dtree *accept)
{
	if (idx == count - 1)
		return accept;
	else
		return mkdtree(loc, genlbl(loc));
}

static size_t
nconstructors(Type *t)
{
	if (!t)
		return 0;

	t = tybase(t);
	switch (t->type) {
	case Tyvoid:	return 1;	break;
	case Tybool:	return 2;	break;
	case Tychar:	return 0x10ffff;	break;

	/* signed ints */
	case Tyint8:	return 0x100;	break;
	case Tyint16:	return 0x10000;	break;
	case Tyint32:	return 0x100000000;	break;
	case Tyint:	return 0x100000000;	break;
	case Tyint64:	return ~0ull;	break;

	/* unsigned ints */
	case Tybyte:	return 0x100;	break;
	case Tyuint8:	return 0x100;	break;
	case Tyuint16:	return 0x10000;	break;
	case Tyuint32:	return 0x100000000;	break;
	case Tyuint:	return 0x100000000;	break;
	case Tyuint64:	return ~0ull;	break;

	/* floats */
	case Tyflt32:	return ~0ull;	break;
	case Tyflt64:	return ~0ull;	break;

	/* complex types */
	case Typtr:	return 1;	break;
	case Tyarray:	return 1;	break;
	case Tytuple:	return 1;	break;
	case Tystruct:  return 1;
	case Tyunion:	return t->nmemb;	break;
	case Tyslice:	return ~0ULL;	break;

	case Tyvar: case Typaram: case Tyunres: case Tyname:
	case Tybad: case Tyvalist: case Tygeneric: case Ntypes:
	case Tyfunc: case Tycode:
		die("Invalid constructor type %s in match", tystr(t));
		break;
	}
	return 0;
}

static int
verifymatch(Dtree *t)
{
	size_t i;
	int ret;

	if (t->accept)
		return 1;

	ret = 0;
	if (t->nnext == t->nconstructors || t->any)
		ret = 1;
	for (i = 0; i < t->nnext; i++)
		if (!verifymatch(t->next[i]))
			ret = 0;
	return ret;
}

static int
acceptall(Dtree *t, Dtree *accept)
{
	size_t i;
	int ret;

	if (t->accept || t->any == accept)
		return 0;

	ret = 1;
	if (t->any)
		ret = acceptall(t->any, accept);
	else
		t->any = accept;

	for (i = 0; i < t->nnext; i++)
		if (acceptall(t->next[i], accept))
			ret = 1;
	return ret;
}

static int
isnonrecursive(Dtree *dt, Type *ty)
{
	if (istyprimitive(ty) || ty->type == Tyvoid || ty->type == Tyfunc || ty->type == Typtr)
		return 1;
	if (ty->type == Tystruct)
		return ty->nmemb == 0;
	if (ty->type == Tyarray)
		return fold(ty->asize, 1)->expr.args[0]->lit.intval == 0;
	return 0;
}

static int
addwildrec(Srcloc loc, Type *ty, Dtree *start, Dtree *accept, Dtree ***end, size_t *nend)
{
	Dtree *next, **last, **tail;
	size_t i, j, nelt, nlast, ntail;
	Node *asize;
	Ucon *uc;
	int ret;

	tail = NULL;
	ntail = 0;
	ty = tybase(ty);
	if (ty->type == Typtr && start->any && start->any->ptrwalk) {
		return addwildrec(loc, ty->sub[0], start->any, accept, end, nend);
	} else if (isnonrecursive(start, ty)) {
		if (start->accept || start == accept)
			return 0;
		for (i = 0; i < start->nnext; i++)
			lappend(end, nend, start->next[i]);
		if (start->any) {
			lappend(end, nend, start->any);
			return 0;
		} else {
			start->any = accept;
			lappend(end, nend, accept);
			return 1;
		}
	}

	ret = 0;
	last = NULL;
	nlast = 0;
	switch (ty->type) {
	case Tytuple:
		lappend(&last, &nlast, start);
		for (i = 0; i < ty->nsub; i++) {
			next = nextnode(loc, i, ty->nsub, accept);
			tail = NULL;
			ntail = 0;
			for (j = 0; j < nlast; j++)
				if (addwildrec(loc, ty->sub[i], last[j], next, &tail, &ntail))
					ret = 1;
			lfree(&last, &nlast);
			last = tail;
			nlast = ntail;
		}
		break;
	case Tyarray:
		lappend(&last, &nlast, start);
		asize = fold(ty->asize, 1);
		nelt = asize->expr.args[0]->lit.intval;
		for (i = 0; i < nelt; i++) {
			next = nextnode(loc, i, nelt, accept);
			tail = NULL;
			ntail = 0;
			for (j = 0; j < nlast; j++)
				if (addwildrec(loc, ty->sub[0], last[j], next, &tail, &ntail))
					ret = 1;
			lfree(&last, &nlast);
			last = tail;
			nlast = ntail;
		}
		break;
	case Tystruct:
		lappend(&last, &nlast, start);
		for (i = 0; i < ty->nmemb; i++) {
			next = nextnode(loc, i, ty->nmemb, accept);
			tail = NULL;
			ntail = 0;
			for (j = 0; j < nlast; j++)
				if (addwildrec(loc, decltype(ty->sdecls[i]), last[j], next, &tail, &ntail))
					ret = 1;
			lfree(&last, &nlast);
			last = tail;
			nlast = ntail;
		}
		break;
	case Tyunion:
		for (i = 0; i < ty->nmemb; i++) {
			uc = ty->udecls[i];
			next = dtbytag(start, uc);
			if (next) {
				if (uc->etype) {
					if (addwildrec(loc, uc->etype, next, accept, end, nend))
						ret = 1;
				} else {
					lappend(end, nend, next);
				}
			}
		}
		if (!start->any) {
			start->any = accept;
			ret = 1;
		}
		lappend(&last, &nlast, accept);
		break;
	case Tyslice:
		ret = acceptall(start, accept);
		lappend(&last, &nlast, accept);
		break;
	default:
		die("unreachable");
	}
	lcat(end, nend, last, nlast);
	lfree(&last, &nlast);
	return ret;
}

static int
addwild(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	Node *asn;

	if (cap && ncap) {
		asn = mkexpr(pat->loc, Oasn, pat, val, NULL);
		asn->expr.type = exprtype(pat);
		lappend(cap, ncap, asn);
	}
	return addwildrec(pat->loc, exprtype(pat), start, accept, end, nend);
}

static int
addunion(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	Node *tagid;
	Dtree *next;
	Ucon *uc;

	if (start->any) {
		lappend(end, nend, start->any);
		return 0;
	}

	uc = finducon(tybase(exprtype(pat)), pat->expr.args[0]);
	next = dtbytag(start, uc);
	if (next) {
		if (!uc->etype) {
			lappend(end, nend, next);
			return 0;
		} else {
			return addpat(pat->expr.args[1], uvalue(val, uc->etype), next, accept, cap, ncap, end, nend);
		}
	}

	if (!start->load) {
		start->load = utag(val);
		start->nconstructors = nconstructors(tybase(exprtype(pat)));
	}

	tagid = mkintlit(pat->loc, uc->id);
	tagid->expr.type = mktype(pat->loc, Tyint32);
	lappend(&start->pat, &start->npat, tagid);
	if (uc->etype) {
		next = mkdtree(pat->loc, genlbl(pat->loc));
		lappend(&start->next, &start->nnext, next);
		addpat(pat->expr.args[1], uvalue(val, uc->etype), next, accept, cap, ncap, end, nend);
	} else {
		lappend(&start->next, &start->nnext, accept);
		lappend(end, nend, accept);
	}
	return 1;
}

static int
addstr(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	Dtree **tail, **last, *next;
	size_t i, j, n, ntail, nlast;
	Node *p, *v, *lit;
	Type *ty;
	char *s;
	int ret;

	lit = pat->expr.args[0];
	n = lit->lit.strval.len;
	s = lit->lit.strval.buf;

	ty = mktype(pat->loc, Tyuint64);
	p = mkintlit(lit->loc, n);
	v = structmemb(val, mkname(pat->loc, "len"), ty);
	p->expr.type = ty;

	if (n == 0)
		next = accept;
	else
		next = mkdtree(pat->loc, genlbl(pat->loc));

	last = NULL;
	nlast = 0;
	ret = 0;
	if (addpat(p, v, start, next, cap, ncap, &last, &nlast))
		ret = 1;

	ty = mktype(pat->loc, Tybyte);
	for (i = 0; i < n; i++) {
		p = mkintlit(lit->loc, s[i]);
		p->expr.type = ty;
		v = arrayelt(val, i);

		tail = NULL;
		ntail = 0;
		next = nextnode(pat->loc, i, n, accept);
		for (j = 0; j < nlast; j++)
			if (addpat(p, v, last[j], next, NULL, NULL, &tail, &ntail))
				ret = 1;
		lfree(&last, &nlast);
		last = tail;
		nlast = ntail;
	}
	lcat(end, nend, last, nlast);
	lfree(&last, &nlast);
	return ret;
}

static int
addlit(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	size_t i;

	if (pat->expr.args[0]->lit.littype == Lstr) {
		return addstr(pat, val, start, accept, cap, ncap, end, nend);
	} else {
		/* if we already have a match, we're not adding a new node */
		if (start->any) {
			lappend(end, nend, start->any);
			return 0;
		}

		for (i = 0; i < start->npat; i++) {
			if (liteq(start->pat[i]->expr.args[0], pat->expr.args[0])) {
				lappend(end, nend, start->next[i]);
				return 0;
			}
		}

		/* wire up an edge from start to 'accept' */
		if (!start->load) {
			start->load = val;
			start->nconstructors = nconstructors(exprtype(pat));
		}
		lappend(&start->pat, &start->npat, pat);
		lappend(&start->next, &start->nnext, accept);
		lappend(end, nend, accept);
		return 1;
	}
}

static int
addtup(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	size_t nargs, nlast, ntail, i, j;
	Dtree *next, **last, **tail;
	Node **args;
	int ret;

	args = pat->expr.args;
	nargs = pat->expr.nargs;
	last = NULL;
	nlast = 0;
	lappend(&last, &nlast, start);
	ret = 0;

	for (i = 0; i < nargs; i++) {
		next = nextnode(args[i]->loc, i, nargs, accept);
		tail = NULL;
		ntail = 0;
		for (j = 0; j < nlast; j++)
			if (addpat(pat->expr.args[i], tupelt(val, i), last[j], next, cap, ncap, &tail, &ntail))
				ret = 1;
		lfree(&last, &nlast);
		last = tail;
		nlast = ntail;
	}
	lcat(end, nend, last, nlast);
	lfree(&last, &nlast);
	return ret;
}

static int
addarr(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	size_t nargs, nlast, ntail, i, j;
	Dtree *next, **last, **tail;
	Node **args;
	int ret;

	args = pat->expr.args;
	nargs = pat->expr.nargs;
	last = NULL;
	nlast = 0;
	lappend(&last, &nlast, start);
	ret = 0;

	for (i = 0; i < nargs; i++) {
		next = nextnode(args[i]->loc, i, nargs, accept);
		tail = NULL;
		ntail = 0;
		for (j = 0; j < nlast; j++)
			if (addpat(pat->expr.args[i], arrayelt(val, i), last[j], next, cap, ncap, &tail, &ntail))
				ret = 1;
		lfree(&last, &nlast);
		last = tail;
		nlast = ntail;
	}
	lcat(end, nend, last, nlast);
	lfree(&last, &nlast);
	return ret;
}

static int
addstruct(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	Dtree *next, **last, **tail;
	Node *memb, *name;
	Type *ty, *mty;
	size_t i, j, ntail, nlast;
	int ret;

	ret = 0;
	last = NULL;
	nlast = 0;
	lappend(&last, &nlast, start);
	ty = tybase(exprtype(pat));

	for (i = 0; i < ty->nmemb; i++) {
		mty = decltype(ty->sdecls[i]);
		name = ty->sdecls[i]->decl.name;
		memb = findmemb(pat, name);
		next = nextnode(pat->loc, i, ty->nmemb, accept);
		tail = NULL;
		ntail = 0;

		/* add a _ capture if we don't specify the value */
		if (!memb) {
			memb = mkexpr(ty->sdecls[i]->loc, Ogap, NULL);
			memb->expr.type = mty;
		}
		for (j = 0; j < nlast; j++) {
			if (addpat(memb, structmemb(val, name, mty), last[j], next, cap, ncap, &tail, &ntail))
				ret = 1;
		}
		lfree(&last, &nlast);
		last = tail;
		nlast = ntail;
	}
	lcat(end, nend, last, nlast);
	lfree(&last, &nlast);
	return ret;
}

static int
addderefpat(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	Node *deref;
	Dtree *walk;

	deref = mkexpr(val->loc, Oderef, val, NULL);
	deref->expr.type = exprtype(pat->expr.args[0]);
	start->nconstructors = nconstructors(exprtype(deref));
	if (start->any && !start->any->ptrwalk)
		return 0;
	else if (!start->any)
		start->any = mkdtree(pat->loc, genlbl(pat->loc));
	walk = start->any;
	walk->ptrwalk = 1;
	return addpat(pat->expr.args[0], deref, walk, accept, cap, ncap, end, nend);
}

static int
addpat(Node *pat, Node *val, Dtree *start, Dtree *accept, Node ***cap, size_t *ncap, Dtree ***end, size_t *nend)
{
	int ret;
	Node *dcl;
	Type *ty;

	pat = fold(pat, 1);
	ret = 0;
	switch (exprop(pat)) {
	case Ovar:
		dcl = decls[pat->expr.did];
		if (dcl->decl.isconst) {
			ty = decltype(dcl);
			if (ty->type == Tyfunc || ty->type == Tycode || ty->type == Tyvalist)
				fatal(dcl, "bad pattern %s:%s: unmatchable type", declname(dcl), tystr(ty));
			if (!dcl->decl.init)
				fatal(dcl, "bad pattern %s:%s: missing initializer", declname(dcl), tystr(ty));
			ret = addpat(dcl->decl.init, val, start, accept, cap, ncap, end, nend);
		} else {
			ret = addwild(pat, val, start, accept, cap, ncap, end, nend);
		}
		break;
	case Oucon:
		ret = addunion(pat, val, start, accept, cap, ncap, end, nend);
		break;
	case Olit:
		ret = addlit(pat, val, start, accept, cap, ncap, end, nend);
		break;
	case Otup:
		ret = addtup(pat, val, start, accept, cap, ncap, end, nend);
		break;
	case Oarr:
		ret = addarr(pat, val, start, accept, cap, ncap, end, nend);
		break;
	case Ostruct:
		ret = addstruct(pat, val, start, accept, cap, ncap, end, nend);
		break;
	case Ogap:
		ret = addwild(pat, NULL, start, accept, NULL, NULL, end, nend);
		break;
	case Oaddr:
		ret = addderefpat(pat, val, start, accept, cap, ncap, end, nend);
		break;
	default:
		fatal(pat, "unsupported pattern %s of type %s", opstr[exprop(pat)], tystr(exprtype(pat)));
		break;
	}
	return ret;
}


/* val must be a pure, fully evaluated value */
Dtree *
gendtree(Node *m, Node *val, Node **lbl, size_t nlbl, int startid)
{
	Dtree *start, *accept, **end;
	Node **pat, **cap;
	size_t npat, ncap, nend;
	size_t i;

	ndtree = startid;

	pat = m->matchstmt.matches;
	npat = m->matchstmt.nmatches;

	end = NULL;
	nend = 0;
	start = mkdtree(m->loc, genlbl(m->loc));
	for (i = 0; i < npat; i++) {
		cap = NULL;
		ncap = 0;
		accept = mkdtree(lbl[i]->loc, lbl[i]);
		accept->accept = 1;

		if (!addpat(pat[i]->match.pat, val, start, accept, &cap, &ncap, &end, &nend))
			fatal(pat[i], "pattern matched by earlier case");
		addcapture(pat[i]->match.block, cap, ncap);
	}
	if (debugopt['M'])
		dtreedump(stdout, start);
	if (!verifymatch(start))
		fatal(m, "nonexhaustive pattern set in match statement");
	return start;
}

void
genmatchcode(Dtree *dt, Node ***out, size_t *nout)
{
	Node *jmp, *eq, *fail;
	int emit;
	size_t i;

	if (dt->emitted)
		return;
	dt->emitted = 1;

	/* the we jump to the accept label when generating the parent */
	if (dt->accept) {
		jmp = mkexpr(dt->loc, Ojmp, dt->lbl, NULL);
		jmp->expr.type = mktype(dt->loc, Tyvoid);
		lappend(out, nout, jmp);
		return;
	}

	lappend(out, nout, dt->lbl);
	for (i = 0; i < dt->nnext; i++) {
		if (i == dt->nnext - 1 && dt->any) {
			fail = dt->any->lbl;
			emit = 0;
		} else {
			fail = genlbl(dt->loc);
			emit = 1;
		}

		eq = mkexpr(dt->loc, Oeq, dt->load, dt->pat[i], NULL);
		eq->expr.type = mktype(dt->loc, Tybool);
		jmp = mkexpr(dt->loc, Ocjmp, eq, dt->next[i]->lbl, fail, NULL);
		jmp->expr.type = mktype(dt->loc, Tyvoid);
		lappend(out, nout, jmp);

		genmatchcode(dt->next[i], out, nout);
		if (emit)
			lappend(out, nout, fail);
	}
	if (dt->any) {
		jmp = mkexpr(dt->loc, Ojmp, dt->any->lbl, NULL);
		jmp->expr.type = mktype(dt->loc, Tyvoid);
		lappend(out, nout, jmp);
		genmatchcode(dt->any, out, nout);
	}
}

void
genonematch(Node *pat, Node *val, Node *iftrue, Node *iffalse, Node ***out, size_t *nout, Node ***cap, size_t *ncap)
{
	Dtree *start, *accept, *reject, **end;
	size_t nend;

	end = NULL;
	nend = 0;

	start = mkdtree(pat->loc, genlbl(pat->loc));
	accept = mkdtree(iftrue->loc, iftrue);
	accept->accept = 1;
	reject = mkdtree(iffalse->loc, iffalse);
	reject->accept = 1;

	assert(addpat(pat, val, start, accept, cap, ncap, &end, &nend));
	acceptall(start, reject);
	genmatchcode(start, out, nout);
}

void
genmatch(Node *m, Node *val, Node ***out, size_t *nout)
{
	Node **pat, **lbl, *end, *endlbl;
	size_t npat, nlbl, i;
	Dtree *dt;

	lbl = NULL;
	nlbl = 0;

	pat = m->matchstmt.matches;
	npat = m->matchstmt.nmatches;
	for (i = 0; i < npat; i++)
		lappend(&lbl, &nlbl, genlbl(pat[i]->match.block->loc));


	endlbl = genlbl(m->loc);
	dt = gendtree2(m, val, lbl, nlbl, ndtree);
	genmatchcode(dt, out, nout);

	for (i = 0; i < npat; i++) {
		end = mkexpr(pat[i]->loc, Ojmp, endlbl, NULL);
		end->expr.type = mktype(end->loc, Tyvoid);
		lappend(out, nout, lbl[i]);
		lappend(out, nout, pat[i]->match.block);
		lappend(out, nout, end);
	}
	lappend(out, nout, endlbl);

	if (debugopt['m']) {
		dtreedump(stdout, dt);
		for (i = 0; i < *nout; i++)
			dumpn((*out)[i], stdout);
	}
}


void
dtreedumplit(FILE *fd, Dtree *dt, Node *n, size_t depth)
{
	char *s;

	s = lblstr(dt->lbl);
	switch (n->lit.littype) {
	case Lvoid:	findentf(fd, depth, "%s: Lvoid\n");	break;
	case Lchr:	findentf(fd, depth, "%s: Lchr %c\n", s, n->lit.chrval);	break;
	case Lbool:	findentf(fd, depth, "%s: Lbool %s\n", s, n->lit.boolval ? "true" : "false");	break;
	case Lint:	findentf(fd, depth, "%s: Lint %llu\n", s, n->lit.intval);	break;
	case Lflt:	findentf(fd, depth, "%s: Lflt %lf\n", s, n->lit.fltval);	break;
	case Lstr:	findentf(fd, depth, "%s: Lstr %.*s\n", s, (int)n->lit.strval.len, n->lit.strval.buf);	break;
	case Llbl:	findentf(fd, depth, "%s: Llbl %s\n", s, n->lit.lblval);	break;
	case Lfunc:	findentf(fd, depth, "%s: Lfunc\n");	break;
	}
}

void
dtreedumpnode(FILE *fd, Dtree *dt, size_t depth)
{
	size_t i;

	if (dt->accept)
		findentf(fd, depth, "%s: accept\n", lblstr(dt->lbl));

	for (i = 0; i < dt->nnext; i++) {
		dtreedumplit(fd, dt, dt->pat[i]->expr.args[0], depth);
		dtreedumpnode(fd, dt->next[i], depth + 1);
	}
	if (dt->any) {
		findentf(fd, depth, "%s: wildcard\n", lblstr(dt->lbl));
		dtreedumpnode(fd, dt->any, depth + 1);
	}
}

void
dtreedump(FILE *fd, Dtree *dt)
{
	dtreedumpnode(fd, dt, 0);
}

// The instances of the struct are immutable.
typedef struct Frontier {
	int i;
	Node *lbl;
	Node **pat;
	size_t npat;
	Node **load;
	size_t nload;
	Node **cap;
	size_t ncap;
} Frontier;

static void
addrec(Frontier *fs, Node *val, Node *pat)
{
	size_t i, n;
	Type *ty, *mty;
	Node *memb, *name, *tagid, *p, *v, *lit, *dcl, *asn, *deref;
	Ucon *uc;
	char *s;

	pat = fold(pat, 1);
	switch (exprop(pat)) {
	case Ogap:
		lappend(&fs->pat, &fs->npat, pat);
		lappend(&fs->load, &fs->nload, val);
		break;
	case Ovar:
		dcl = decls[pat->expr.did];
		if (dcl->decl.isconst) {
			ty = decltype(dcl);
			if (ty->type == Tyfunc || ty->type == Tycode || ty->type == Tyvalist) {
				fatal(dcl, "bad pattern %s:%s: unmatchable type", declname(dcl), tystr(ty));
			}
			if (!dcl->decl.init) {
				fatal(dcl, "bad pattern %s:%s: missing initializer", declname(dcl), tystr(ty));
			}
			addrec(fs, val, dcl->decl.init);
		} else {
			asn = mkexpr(pat->loc, Oasn, pat, val, NULL);
			asn->expr.type = exprtype(pat);
			lappend(&fs->pat, &fs->npat, pat);
			lappend(&fs->load, &fs->nload, val);
			lappend(&fs->cap, &fs->ncap, asn);
		}
		break;
	case Olit:
		if (pat->expr.args[0]->lit.littype == Lstr) {
			lit = pat->expr.args[0];
			n = lit->lit.strval.len;
			s = lit->lit.strval.buf;

			ty = mktype(pat->loc, Tyuint64);
			p = mkintlit(lit->loc, n);
			p ->expr.type = ty;
			v = structmemb(val, mkname(pat->loc, "len"), ty);

			addrec(fs, v, p);

			ty = mktype(pat->loc, Tybyte);
			for (i = 0; i < n; i++) {
				p = mkintlit(lit->loc, s[i]);
				p->expr.type = ty;
				v = arrayelt(val, i);
				addrec(fs, v, p);
			}

		} else {
			lappend(&fs->pat, &fs->npat, pat);
			lappend(&fs->load, &fs->nload, val);
		}
		break;
	case Oaddr:
		deref = mkexpr(val->loc, Oderef, val, NULL);
		deref->expr.type = exprtype(pat->expr.args[0]);
		addrec(fs, deref, pat->expr.args[0]);
		break;
	case Oucon:
		uc = finducon(tybase(exprtype(pat)), pat->expr.args[0]);
		tagid = mkintlit(pat->loc, uc->id);
		tagid->expr.type = mktype(pat->loc, Tyint32);
		addrec(fs, utag(val), tagid);
		if (uc->etype) {
			addrec(fs, uvalue(val, uc->etype), pat->expr.args[1]);
		}
		break;
	case Otup:
		for (i = 0; i < pat->expr.nargs; i++) {
			addrec(fs, tupelt(val, i), pat->expr.args[i]);
		}
		break;
	case Oarr:
		for (i = 0; i < pat->expr.nargs; i++) {
			addrec(fs, arrayelt(val, i), pat->expr.args[i]);
		}
		break;
	case Ostruct:
		ty = tybase(exprtype(pat));
		for (i = 0; i < ty->nmemb; i++) {
			mty = decltype(ty->sdecls[i]);
			name = ty->sdecls[i]->decl.name;
			memb = findmemb(pat, name);
			if (!memb) {
				memb = mkexpr(ty->sdecls[i]->loc, Ogap, NULL);
				memb->expr.type = mty;
			}
			addrec(fs, structmemb(val, name, mty), memb);
		}
		break;
	default:
		fatal(pat, "unsupported pattern %s of type %s", opstr[exprop(pat)], tystr(exprtype(pat)));
		break;
	}
}

static void
genfrontier(int i, Node *val, Node *pat, Node *lbl, Frontier ***frontier, size_t *nfrontier)
{
	Frontier *fs;

	fs = zalloc(sizeof(Frontier));
	fs->i = i;
	fs->lbl = lbl;
	addrec(fs, val, pat);
	lappend(frontier, nfrontier, fs);
}

static Frontier *
project(Node *pat, Node *val, Frontier *fs)
{
	size_t i, cursor;
	//Node *pi;
	Node *c;
	Node **_pat, **_load;
	size_t _npat, _nload;
	Frontier *_fs;

	assert (fs->npat == fs->nload);

	// select the current frontier when the sub-term val does not present in the frontier fs
	//pi = NULL;
	c = NULL;
	cursor = -1;
	for (i = 0; i < fs->npat; i++) {
		if (val == fs->load[i]) {
			//pi = val;
			c = fs->pat[i];
			cursor = i;
			break;
		}
	}

	// if the sub-term pi is not in the frontier,
	// then we do not reduce the frontier.
	if (cursor == -1) {
		return fs;
	}

	switch (exprop(c)) {
	case Ovar:
	case Ogap:
		// if the pattern at the sub-term pi of this frontier is not a constructor,
		// then we do not reduce the frontier.
		return fs;
	default:
		break;
	}

	// if constructor at the sub-term pi is not the constructor we want to project,
	// then return null.
	if (pat != c) {
		return NULL;
	}

	// Duplicate the pat and load lists
	_pat = _load = NULL;
	_npat = _nload = 0;
	lcat(&_pat, &_npat, fs->pat, fs->npat);
	lcat(&_load, &_nload, fs->load, fs->nload);

	ldel(&_pat, &_npat, cursor);
	ldel(&_load, &_nload, cursor);


	switch (exprop(c)) {
	case Ovar:
	case Ogap:
		break;
	case Olit:
		break;
	default:
		break;
	}

	_fs = zalloc(sizeof(Frontier));
	_fs->i = fs->i;
	_fs->lbl = fs->lbl;
	_fs->pat = _pat;
	_fs->npat = _npat;
	_fs->load = _load;
	_fs->nload = _nload;

	return _fs;
}

static Dtree *
compile(Frontier **frontier, size_t nfrontier)
{
	size_t i, j, k;
	Dtree *dt, *_dt, **edge, *any;
	Frontier *fs, *_fs, **_frontier, **defaults ;
	Node **cs, *p, *pat, *pi, **_pat;
	size_t ncs, ncons, _nfrontier, nedge, ndefaults, _npat;


	assert(nfrontier > 0);

	fs = frontier[0];

	assert(fs->npat == fs->nload);

	ncons = 0;
	for (i = 0; i < fs->npat; i++) {
		switch (exprop(fs->pat[i])) {
		case Ovar:
		case Ogap:
			break;
		default:
			ncons++;
		}
	}
	if (ncons == 0) {
		dt = mkdtree(fs->lbl->loc, fs->lbl);
		dt->accept = 1;
		return dt;
	}

	assert(fs->nload > 0);

	// always select the first found constructor
	for (i = 0; i < fs->npat; i++) {
		switch (exprop(fs->pat[i])) {
		case Ovar:
		case Ogap:
			continue;
		default:
			pi = fs->load[i];
			pat = fs->pat[i];
			goto pi_found;
		}
	}

pi_found:
	// when the input frontiers have any constructor
	// collect all constructors of the same path in all frontiers {(i,f)} to CS

	cs = NULL;
	ncs = 0;
	for (i = 0; i < nfrontier; i++) {
		fs = frontier[i];
		for (j = 0; j < fs->npat; j++) {
			p = fs->pat[j];
			switch (exprop(p)) {
			case Ovar:
			case Ogap:
				break;
			default:
				if (fs->load[j] == pi) {
					lappend(&cs, &ncs, p);
				}
			}
		}
	}

	// compile the edges
	edge = NULL;
	nedge = 0;
	_pat = NULL;
	_npat = 0;
	for (i = 0; i < ncs; i++) {
		_frontier = NULL;
		_nfrontier = 0;
		for (j = 0; j < nfrontier; j++) {
			fs = frontier[j];
			_fs = project(cs[i], pi, fs);
			if (_fs != NULL) {
				lappend(&_frontier, &_nfrontier, _fs);
			}
		}

		if (_nfrontier > 0) {
			dt = compile(_frontier, _nfrontier);
			lappend(&edge, &nedge, dt);
			lappend(&_pat, &_npat, cs[i]);

		}
	}

	// compile the defaults
	defaults = NULL;
	ndefaults = 0;
	for (i = 0; i < nfrontier; i++) {
		fs = frontier[i];
		k = -1;
		for (j = 0; j < fs->npat; j++) {
			p = fs->pat[j];
			// locate the occurrence of pi in fs
			if (pi == fs->load[j]) {
				k = j;
			}
		}

		if (k == -1 || exprop(fs->pat[k]) == Ovar || exprop(fs->pat[k]) == Ogap) {
			lappend(&defaults, &ndefaults, fs);
		}
	}
	if (ndefaults) {
		any = compile(defaults, ndefaults);
	} else {
		any = NULL;
	}


	// construct the result dtree
	_dt = mkdtree(pat->loc, genlbl(pat->loc));
	_dt->load = pi;
	_dt->npat = _npat,
	_dt->pat = _pat,
	_dt->nnext = nedge;
	_dt->next = edge;
	_dt->any = any;
	return _dt;
}


Dtree *
gendtree2(Node *m, Node *val, Node **lbl, size_t nlbl, int startid)
{
	Dtree *root;
	Node **pat;
	size_t npat;
	size_t i;
	Frontier **frontier;
	size_t nfrontier;


	ndtree = startid;

	pat = m->matchstmt.matches;
	npat = m->matchstmt.nmatches;

	frontier = NULL;
	nfrontier = 0;
	for (i = 0; i < npat; i++) {
		genfrontier(i, val, pat[i]->match.pat, lbl[i], &frontier, &nfrontier);
	}
	for (i = 0; i < nfrontier; i++) {
		addcapture(pat[i]->match.block, frontier[i]->cap, frontier[i]->ncap);
	}
	root = compile(frontier, nfrontier);

	if (debugopt['M'])
		dtreedump(stdout, root);

	return root;
}

