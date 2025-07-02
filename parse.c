#include "all.h"
#include <ctype.h>
#include <stdarg.h>

// -----------------------------------------------------------------------------
// This file implements the parser for the QBE intermediate representation (IR).
// It handles tokenization, parsing of functions, types, data, and top-level
// constructs, and builds the in-memory representation of the IR for further
// compilation stages.
// -----------------------------------------------------------------------------

enum {
	Ksb = 4, /* matches Oarg/Opar/Jret */
	Kub,
	Ksh,
	Kuh,
	Kc,
	K0,

	Ke = -2, /* erroneous mode */
	Km = Kl, /* memory pointer */
};

// Table of operation properties, filled from ops.h
Op optab[NOp] = {
#undef F
#define F(cf, hi, id, co, as, im, ic, lg, cv, pn) \
	.canfold = cf, \
	.hasid = hi, .idval = id, \
	.commutes = co, .assoc = as, \
	.idemp = im, \
	.cmpeqwl = ic, .cmplgtewl = lg, .eqval = cv, \
	.pinned = pn
#define O(op, k, flags) [O##op]={.name = #op, .argcls = k, flags},
	#include "ops.h"
#undef F
};

typedef enum {
	PXXX,   // No state
	PLbl,   // Parsing a label
	PPhi,   // Parsing phi instructions
	PIns,   // Parsing regular instructions
	PEnd,   // End of function/block
} PState;

// Token types for the lexer
// These include keywords, punctuation, and literal types
// Used throughout the parser to identify the next input
// See also: kwmap[] for string mapping

enum Token {
	Txxx = 0,

	/* aliases */
	Tloadw = NPubOp,
	Tloadl,
	Tloads,
	Tloadd,
	Talloc1,
	Talloc2,

	Tblit,
	Tcall,
	Tenv,
	Tphi,
	Tjmp,
	Tjnz,
	Tret,
	Thlt,
	Texport,
	Tthread,
	Tcommon,
	Tfunc,
	Ttype,
	Tdata,
	Tsection,
	Talign,
	Tdbgfile,
	Tl,
	Tw,
	Tsh,
	Tuh,
	Th,
	Tsb,
	Tub,
	Tb,
	Td,
	Ts,
	Tz,

	Tint,
	Tflts,
	Tfltd,
	Ttmp,
	Tlbl,
	Tglo,
	Ttyp,
	Tstr,

	Tplus,
	Teq,
	Tcomma,
	Tlparen,
	Trparen,
	Tlbrace,
	Trbrace,
	Tnl,
	Tdots,
	Teof,

	Ntok
};

static char *kwmap[Ntok] = {
	[Tloadw] = "loadw",
	[Tloadl] = "loadl",
	[Tloads] = "loads",
	[Tloadd] = "loadd",
	[Talloc1] = "alloc1",
	[Talloc2] = "alloc2",
	[Tblit] = "blit",
	[Tcall] = "call",
	[Tenv] = "env",
	[Tphi] = "phi",
	[Tjmp] = "jmp",
	[Tjnz] = "jnz",
	[Tret] = "ret",
	[Thlt] = "hlt",
	[Texport] = "export",
	[Tthread] = "thread",
	[Tcommon] = "common",
	[Tfunc] = "function",
	[Ttype] = "type",
	[Tdata] = "data",
	[Tsection] = "section",
	[Talign] = "align",
	[Tdbgfile] = "dbgfile",
	[Tsb] = "sb",
	[Tub] = "ub",
	[Tsh] = "sh",
	[Tuh] = "uh",
	[Tb] = "b",
	[Th] = "h",
	[Tw] = "w",
	[Tl] = "l",
	[Ts] = "s",
	[Td] = "d",
	[Tz] = "z",
	[Tdots] = "...",
};

enum {
	NPred = 63,

	TMask = 16383, /* for temps hash */
	BMask = 8191, /* for blocks hash */

	K = 11183273, /* found using tools/lexh.c */
	M = 23,
};

static uchar lexh[1 << (32-M)];
static FILE *inf;
static char *inpath;
static int thead;
static struct {
	char chr;
	double fltd;
	float flts;
	int64_t num;
	char *str;
} tokval;
static int lnum;

static Fn *curf;
static int *tmph;
static int tmphcap;
static Phi **plink;
static Blk *curb;
static Blk **blink;
static Blk *blkh[BMask+1];
static int nblk;
static int rcls;
static uint ntyp;

/**
 * Reports a fatal error, prints a formatted message with file and line number,
 * and exits the program. Used for unrecoverable parse errors.
 *
 * @param s Format string for the error message
 * @param ... Arguments for the format string
 */
void
err(char *s, ...)
{
	va_list ap;

	va_start(ap, s);
	fprintf(stderr, "qbe:%s:%d: ", inpath, lnum);
	vfprintf(stderr, s, ap);
	fprintf(stderr, "\n");
	va_end(ap);
	exit(1);
}

/**
 * Initializes the lexer keyword hash table. Populates kwmap and lexh
 * for fast keyword lookup. Only runs once per process.
 */
static void
lexinit()
{
	static int done;
	int i;
	long h;

	if (done)
		return;
	for (i=0; i<NPubOp; ++i)
		if (optab[i].name)
			kwmap[i] = optab[i].name;
	assert(Ntok <= UCHAR_MAX);
	for (i=0; i<Ntok; ++i)
		if (kwmap[i]) {
			h = hash(kwmap[i])*K >> M;
			assert(lexh[h] == Txxx);
			lexh[h] = i;
		}
	done = 1;
}

/**
 * Reads an integer literal from the input file, handling optional minus sign.
 * Returns the parsed integer as int64_t. Used by the lexer for Tint tokens.
 */
static int64_t
getint()
{
	uint64_t n;
	int c, m;

	n = 0;
	c = fgetc(inf);
	m = (c == '-');
	if (m)
		c = fgetc(inf);
	do {
		n = 10*n + (c - '0');
		c = fgetc(inf);
	} while ('0' <= c && c <= '9');
	ungetc(c, inf);
	if (m)
		n = 1 + ~n;
	return *(int64_t *)&n;
}

/**
 * Lexical analyzer: reads the next token from the input file and sets tokval.
 * Handles keywords, identifiers, literals, punctuation, and comments.
 * Returns the token type (enum Token value).
 *
 * @return Token type (enum Token)
 */
static int
lex()
{
	static char tok[NString];
	int c, i, esc;
	int t;

	do
		c = fgetc(inf);
	while (isblank(c));
	t = Txxx;
	tokval.chr = c;
	switch (c) {
	case EOF:
		return Teof;
	case ',':
		return Tcomma;
	case '(':
		return Tlparen;
	case ')':
		return Trparen;
	case '{':
		return Tlbrace;
	case '}':
		return Trbrace;
	case '=':
		return Teq;
	case '+':
		return Tplus;
	case 's':
		if (fscanf(inf, "_%f", &tokval.flts) != 1)
			break;
		return Tflts;
	case 'd':
		if (fscanf(inf, "_%lf", &tokval.fltd) != 1)
			break;
		return Tfltd;
	case '%':
		t = Ttmp;
		c = fgetc(inf);
		goto Alpha;
	case '@':
		t = Tlbl;
		c = fgetc(inf);
		goto Alpha;
	case '$':
		t = Tglo;
		if ((c = fgetc(inf)) == '"')
			goto Quoted;
		goto Alpha;
	case ':':
		t = Ttyp;
		c = fgetc(inf);
		goto Alpha;
	case '#':
		while ((c=fgetc(inf)) != '\n' && c != EOF)
			;
		/* fall through */
	case '\n':
		lnum++;
		return Tnl;
	}
	if (isdigit(c) || c == '-') {
		ungetc(c, inf);
		tokval.num = getint();
		return Tint;
	}
	if (c == '"') {
		t = Tstr;
	Quoted:
		tokval.str = vnew(2, 1, PFn);
		tokval.str[0] = c;
		esc = 0;
		for (i=1;; i++) {
			c = fgetc(inf);
			if (c == EOF)
				err("unterminated string");
			vgrow(&tokval.str, i+2);
			tokval.str[i] = c;
			if (c == '"' && !esc) {
				tokval.str[i+1] = 0;
				return t;
			}
			esc = (c == '\\' && !esc);
		}
	}
Alpha:
	if (!isalpha(c) && c != '.' && c != '_')
		err("invalid character %c (%d)", c, c);
	i = 0;
	do {
		if (i >= NString-1)
			err("identifier too long");
		tok[i++] = c;
		c = fgetc(inf);
	} while (isalpha(c) || c == '$' || c == '.' || c == '_' || isdigit(c));
	tok[i] = 0;
	ungetc(c, inf);
	tokval.str = tok;
	if (t != Txxx) {
		return t;
	}
	t = lexh[hash(tok)*K >> M];
	if (t == Txxx || strcmp(kwmap[t], tok) != 0) {
		err("unknown keyword %s", tok);
		return Txxx;
	}
	return t;
}

/**
 * Peeks at the next token without consuming it.
 * If the lookahead token (thead) is not set, calls lex() to fetch it.
 *
 * @return The next token type (enum Token)
 */
static int
peek()
{
	if (thead == Txxx)
		thead = lex();
	return thead;
}

/**
 * Consumes and returns the next token.
 * If a lookahead token is set, returns it and clears the lookahead.
 * Otherwise, calls peek() to fetch the next token.
 *
 * @return The next token type (enum Token)
 */
static int
next()
{
	int t;

	t = peek();
	thead = Txxx;
	return t;
}

/**
 * Consumes tokens until a non-newline token is found, then returns it.
 * Used to skip blank lines in the parser.
 *
 * @return The next non-newline token type (enum Token)
 */
static int
nextnl()
{
	int t;

	while ((t = next()) == Tnl)
		;
	return t;
}

/**
 * Consumes the next token and checks that it matches the expected type.
 * If not, reports a parse error and exits.
 *
 * @param t The expected token type
 */
static void
expect(int t)
{
	static char *ttoa[] = {
		[Tlbl] = "label",
		[Tcomma] = ",",
		[Teq] = "=",
		[Tnl] = "newline",
		[Tlparen] = "(",
		[Trparen] = ")",
		[Tlbrace] = "{",
		[Trbrace] = "}",
		[Teof] = 0,
	};
	char buf[128], *s1, *s2;
	int t1;

	t1 = next();
	if (t == t1)
		return;
	s1 = ttoa[t] ? ttoa[t] : "??";
	s2 = ttoa[t1] ? ttoa[t1] : "??";
	sprintf(buf, "%s expected, got %s instead", s1, s2);
	err(buf);
}

/**
 * Looks up or creates a temporary variable reference by name.
 * Used for parsing SSA temporary references (e.g., %tmp).
 *
 * @param v Name of the temporary variable
 * @return Reference to the temporary (TMP(t))
 */
static Ref
tmpref(char *v)
{
	int t, i;

	if (tmphcap/2 <= curf->ntmp-Tmp0) {
		free(tmph);
		tmphcap = tmphcap ? tmphcap*2 : TMask+1;
		tmph = emalloc(tmphcap * sizeof tmph[0]);
		for (t=Tmp0; t<curf->ntmp; t++) {
			i = hash(curf->tmp[t].name) & (tmphcap-1);
			for (; tmph[i]; i=(i+1) & (tmphcap-1))
				;
			tmph[i] = t;
		}
	}
	i = hash(v) & (tmphcap-1);
	for (; tmph[i]; i=(i+1) & (tmphcap-1)) {
		t = tmph[i];
		if (strcmp(curf->tmp[t].name, v) == 0)
			return TMP(t);
	}
	t = curf->ntmp;
	tmph[i] = t;
	newtmp(0, Kx, curf);
	strcpy(curf->tmp[t].name, v);
	return TMP(t);
}

/**
 * Parses a reference (temporary, constant, global, thread, or literal).
 * Handles %tmp, integer, float, double, thread, global, and string references.
 *
 * @return The parsed reference (Ref)
 */
static Ref
parseref()
{
	Con c;

	memset(&c, 0, sizeof c);
	switch (next()) {
	default:
		return R;
	case Ttmp:
		return tmpref(tokval.str);
	case Tint:
		c.type = CBits;
		c.bits.i = tokval.num;
		break;
	case Tflts:
		c.type = CBits;
		c.bits.s = tokval.flts;
		c.flt = 1;
		break;
	case Tfltd:
		c.type = CBits;
		c.bits.d = tokval.fltd;
		c.flt = 2;
		break;
	case Tthread:
		c.sym.type = SThr;
		expect(Tglo);
		/* fall through */
	case Tglo:
		c.type = CAddr;
		c.sym.id = intern(tokval.str);
		break;
	}
	return newcon(&c, curf);
}

/**
 * Finds a type index by name in the typ[] array.
 * Used for resolving :typename references during parsing.
 *
 * @param i Number of types to search
 * @return Index of the matching type, or error if not found
 */
static int
findtyp(int i)
{
	while (--i >= 0)
		if (strcmp(tokval.str, typ[i].name) == 0)
			return i;
	err("undefined type :%s", tokval.str);
}

/**
 * Parses a type/class specifier (e.g., :type, sb, ub, sh, uh, w, l, s, d).
 * Optionally sets the type index for :type.
 *
 * @param tyn Pointer to store type index (for :type)
 * @return Class code (Kc, Ksb, Kub, etc.)
 */
static int
parsecls(int *tyn)
{
	switch (next()) {
	default:
		err("invalid class specifier");
	case Ttyp:
		*tyn = findtyp(ntyp);
		return Kc;
	case Tsb:
		return Ksb;
	case Tub:
		return Kub;
	case Tsh:
		return Ksh;
	case Tuh:
		return Kuh;
	case Tw:
		return Kw;
	case Tl:
		return Kl;
	case Ts:
		return Ks;
	case Td:
		return Kd;
	}
}

/**
 * Parses a function argument or parameter list.
 * Handles variadic arguments, environment parameters, and type classes.
 * Emits appropriate Oarg/Opar instructions for each argument.
 *
 * @param arg 1 if parsing arguments, 0 if parsing parameters
 * @return 1 if function is variadic, 0 otherwise
 */
static int
parserefl(int arg)
{
	int k, ty, env, hasenv, vararg;
	Ref r;

	hasenv = 0;
	vararg = 0;
	expect(Tlparen);
	while (peek() != Trparen) {
		if (curi - insb >= NIns)
			err("too many instructions");
		if (!arg && vararg)
			err("no parameters allowed after '...'");
		switch (peek()) {
		case Tdots:
			if (vararg)
				err("only one '...' allowed");
			vararg = 1;
			if (arg) {
				*curi = (Ins){.op = Oargv};
				curi++;
			}
			next();
			goto Next;
		case Tenv:
			if (hasenv)
				err("only one environment allowed");
			hasenv = 1;
			env = 1;
			next();
			k = Kl;
			break;
		default:
			env = 0;
			k = parsecls(&ty);
			break;
		}
		r = parseref();
		if (req(r, R))
			err("invalid argument");
		if (!arg && rtype(r) != RTmp)
			err("invalid function parameter");
		if (env)
			if (arg)
				*curi = (Ins){Oarge, k, R, {r}};
			else
				*curi = (Ins){Opare, k, r, {R}};
		else if (k == Kc)
			if (arg)
				*curi = (Ins){Oargc, Kl, R, {TYPE(ty), r}};
			else
				*curi = (Ins){Oparc, Kl, r, {TYPE(ty)}};
		else if (k >= Ksb)
			if (arg)
				*curi = (Ins){Oargsb+(k-Ksb), Kw, R, {r}};
			else
				*curi = (Ins){Oparsb+(k-Ksb), Kw, r, {R}};
		else
			if (arg)
				*curi = (Ins){Oarg, k, R, {r}};
			else
				*curi = (Ins){Opar, k, r, {R}};
		curi++;
	Next:
		if (peek() == Trparen)
			break;
		expect(Tcomma);
	}
	expect(Trparen);
	return vararg;
}

/**
 * Finds or creates a basic block by name.
 * Used for label resolution and jump targets.
 *
 * @param name Name of the block
 * @return Pointer to the found or created block
 */
static Blk *
findblk(char *name)
{
	Blk *b;
	uint32_t h;

	h = hash(name) & BMask;
	for (b=blkh[h]; b; b=b->dlink)
		if (strcmp(b->name, name) == 0)
			return b;
	b = newblk();
	b->id = nblk++;
	strcpy(b->name, name);
	b->dlink = blkh[h];
	blkh[h] = b;
	return b;
}

/**
 * Closes the current basic block by duplicating its instructions.
 * Resets the instruction buffer for the next block.
 */
static void
closeblk()
{
	idup(curb, insb, curi-insb);
	blink = &curb->link;
	curi = insb;
}

/**
 * Parses a single line of the function body.
 * Handles labels, instructions, phi nodes, jumps, returns, and block ends.
 * Updates the parser state machine and emits instructions as needed.
 *
 * @param ps Current parser state (PState)
 * @return Next parser state (PState)
 */
static PState
parseline(PState ps)
{
	Ref arg[NPred] = {R};
	Blk *blk[NPred];
	Phi *phi;
	Ref r;
	Blk *b;
	Con *c;
	int t, op, i, k, ty;

	t = nextnl();
	if (ps == PLbl && t != Tlbl && t != Trbrace)
		err("label or } expected");
	switch (t) {
	case Ttmp:
		r = tmpref(tokval.str);
		expect(Teq);
		k = parsecls(&ty);
		op = next();
		break;
	default:
		if (isstore(t)) {
		case Tblit:
		case Tcall:
		case Ovastart:
			/* operations without result */
			r = R;
			k = Kw;
			op = t;
			break;
		}
		err("label, instruction or jump expected");
	case Trbrace:
		return PEnd;
	case Tlbl:
		b = findblk(tokval.str);
		if (curb && curb->jmp.type == Jxxx) {
			closeblk();
			curb->jmp.type = Jjmp;
			curb->s1 = b;
		}
		if (b->jmp.type != Jxxx)
			err("multiple definitions of block @%s", b->name);
		*blink = b;
		curb = b;
		plink = &curb->phi;
		expect(Tnl);
		return PPhi;
	case Tret:
		curb->jmp.type = Jretw + rcls;
		if (peek() == Tnl)
			curb->jmp.type = Jret0;
		else if (rcls != K0) {
			r = parseref();
			if (req(r, R))
				err("invalid return value");
			curb->jmp.arg = r;
		}
		goto Close;
	case Tjmp:
		curb->jmp.type = Jjmp;
		goto Jump;
	case Tjnz:
		curb->jmp.type = Jjnz;
		r = parseref();
		if (req(r, R))
			err("invalid argument for jnz jump");
		curb->jmp.arg = r;
		expect(Tcomma);
	Jump:
		expect(Tlbl);
		curb->s1 = findblk(tokval.str);
		if (curb->jmp.type != Jjmp) {
			expect(Tcomma);
			expect(Tlbl);
			curb->s2 = findblk(tokval.str);
		}
		if (curb->s1 == curf->start || curb->s2 == curf->start)
			err("invalid jump to the start block");
		goto Close;
	case Thlt:
		curb->jmp.type = Jhlt;
	Close:
		expect(Tnl);
		closeblk();
		return PLbl;
	case Odbgloc:
		op = t;
		k = Kw;
		r = R;
		expect(Tint);
		arg[0] = INT(tokval.num);
		if (arg[0].val != tokval.num)
			err("line number too big");
		if (peek() == Tcomma) {
			next();
			expect(Tint);
			arg[1] = INT(tokval.num);
			if (arg[1].val != tokval.num)
				err("column number too big");
		} else
			arg[1] = INT(0);
		goto Ins;
	}
	if (op == Tcall) {
		curf->leaf = 0;
		arg[0] = parseref();
		parserefl(1);
		op = Ocall;
		expect(Tnl);
		if (k == Kc) {
			k = Kl;
			arg[1] = TYPE(ty);
		}
		if (k >= Ksb)
			k = Kw;
		goto Ins;
	}
	if (op == Tloadw)
		op = Oloadsw;
	if (op >= Tloadl && op <= Tloadd)
		op = Oload;
	if (op == Talloc1 || op == Talloc2)
		op = Oalloc;
	if (op == Ovastart && !curf->vararg)
		err("cannot use vastart in non-variadic function");
	if (k >= Ksb)
		err("size class must be w, l, s, or d");
	i = 0;
	if (peek() != Tnl)
		for (;;) {
			if (i == NPred)
				err("too many arguments");
			if (op == Tphi) {
				expect(Tlbl);
				blk[i] = findblk(tokval.str);
			}
			arg[i] = parseref();
			if (req(arg[i], R))
				err("invalid instruction argument");
			i++;
			t = peek();
			if (t == Tnl)
				break;
			if (t != Tcomma)
				err(", or end of line expected");
			next();
		}
	next();
	switch (op) {
	case Tphi:
		if (ps != PPhi || curb == curf->start)
			err("unexpected phi instruction");
		phi = alloc(sizeof *phi);
		phi->to = r;
		phi->cls = k;
		phi->arg = vnew(i, sizeof arg[0], PFn);
		memcpy(phi->arg, arg, i * sizeof arg[0]);
		phi->blk = vnew(i, sizeof blk[0], PFn);
		memcpy(phi->blk, blk, i * sizeof blk[0]);
		phi->narg = i;
		*plink = phi;
		plink = &phi->link;
		return PPhi;
	case Tblit:
		if (curi - insb >= NIns-1)
			err("too many instructions");
		memset(curi, 0, 2 * sizeof(Ins));
		curi->op = Oblit0;
		curi->arg[0] = arg[0];
		curi->arg[1] = arg[1];
		curi++;
		if (rtype(arg[2]) != RCon)
			err("blit size must be constant");
		c = &curf->con[arg[2].val];
		r = INT(c->bits.i);
		if (c->type != CBits
		|| rsval(r) < 0
		|| rsval(r) != c->bits.i)
			err("invalid blit size");
		curi->op = Oblit1;
		curi->arg[0] = r;
		curi++;
		return PIns;
	default:
		if (op >= NPubOp)
			err("invalid instruction");
	Ins:
		if (curi - insb >= NIns)
			err("too many instructions");
		curi->op = op;
		curi->cls = k;
		curi->to = r;
		curi->arg[0] = arg[0];
		curi->arg[1] = arg[1];
		curi++;
		return PIns;
	}
}

/**
 * Checks if a reference is used with the correct type/class in the function.
 * Allows some flexibility for word/long class merging.
 *
 * @param r Reference to check
 * @param k Expected class
 * @param fn Function containing the reference
 * @return 1 if the reference is valid, 0 otherwise
 */
static int
usecheck(Ref r, int k, Fn *fn)
{
	return rtype(r) != RTmp || fn->tmp[r.val].cls == k
		|| (fn->tmp[r.val].cls == Kl && k == Kw);
}

/**
 * Performs type checking and validation for all instructions and phi nodes
 * in a function. Ensures that temporaries are assigned consistent types,
 * phi nodes match predecessor blocks, and jump arguments are valid.
 *
 * @param fn Function to type check
 */
static void
typecheck(Fn *fn)
{
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;
	int k;
	Tmp *t;
	Ref r;
	BSet pb[1], ppb[1];

	fill_preds_of_function(fn);
	bsinit(pb, fn->nblk);
	bsinit(ppb, fn->nblk);
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link)
			fn->tmp[p->to.val].cls = p->cls;
		for (i=b->ins; i<&b->ins[b->nins]; i++)
			if (rtype(i->to) == RTmp) {
				t = &fn->tmp[i->to.val];
				if (clsmerge(&t->cls, i->cls))
					err("temporary %%%s is assigned with"
						" multiple types", t->name);
			}
	}
	for (b=fn->start; b; b=b->link) {
		bszero(pb);
		for (n=0; n<b->npred; n++)
			bsset(pb, b->pred[n]->id);
		for (p=b->phi; p; p=p->link) {
			bszero(ppb);
			t = &fn->tmp[p->to.val];
			for (n=0; n<p->narg; n++) {
				k = t->cls;
				if (bshas(ppb, p->blk[n]->id))
					err("multiple entries for @%s in phi %%%s",
						p->blk[n]->name, t->name);
				if (!usecheck(p->arg[n], k, fn))
					err("invalid type for operand %%%s in phi %%%s",
						fn->tmp[p->arg[n].val].name, t->name);
				bsset(ppb, p->blk[n]->id);
			}
			if (!bsequal(pb, ppb))
				err("predecessors not matched in phi %%%s", t->name);
		}
		for (i=b->ins; i<&b->ins[b->nins]; i++)
			for (n=0; n<2; n++) {
				k = optab[i->op].argcls[n][i->cls];
				r = i->arg[n];
				t = &fn->tmp[r.val];
				if (k == Ke)
					err("invalid instruction type in %s",
						optab[i->op].name);
				if (rtype(r) == RType)
					continue;
				if (rtype(r) != -1 && k == Kx)
					err("no %s operand expected in %s",
						n == 1 ? "second" : "first",
						optab[i->op].name);
				if (rtype(r) == -1 && k != Kx)
					err("missing %s operand in %s",
						n == 1 ? "second" : "first",
						optab[i->op].name);
				if (!usecheck(r, k, fn))
					err("invalid type for %s operand %%%s in %s",
						n == 1 ? "second" : "first",
						t->name, optab[i->op].name);
			}
		r = b->jmp.arg;
		if (isret(b->jmp.type)) {
			if (b->jmp.type == Jretc)
				k = Kl;
			else if (b->jmp.type >= Jretsb)
				k = Kw;
			else
				k = b->jmp.type - Jretw;
			if (!usecheck(r, k, fn))
				goto JErr;
		}
		if (b->jmp.type == Jjnz && !usecheck(r, Kw, fn))
		JErr:
			err("invalid type for jump argument %%%s in block @%s",
				fn->tmp[r.val].name, b->name);
		if (b->s1 && b->s1->jmp.type == Jxxx)
			err("block @%s is used undefined", b->s1->name);
		if (b->s2 && b->s2->jmp.type == Jxxx)
			err("block @%s is used undefined", b->s2->name);
	}
}

/**
 * Parses a function definition, including its signature, parameters,
 * body, and all contained blocks and instructions. Handles variadic
 * and environment parameters, and sets up the function's data structures.
 *
 * @param lnk Linkage information for the function
 * @return Pointer to the parsed function (Fn *)
 */
static Fn *
parsefn(Lnk *lnk)
{
	Blk *b;
	int i;
	PState ps;

	curb = 0;
	nblk = 0;
	curi = insb;
	curf = alloc(sizeof *curf);
	curf->ntmp = 0;
	curf->ncon = 2;
	curf->tmp = vnew(curf->ntmp, sizeof curf->tmp[0], PFn);
	curf->con = vnew(curf->ncon, sizeof curf->con[0], PFn);
	for (i=0; i<Tmp0; ++i)
		if (T.fpr0 <= i && i < T.fpr0 + T.nfpr)
			newtmp(0, Kd, curf);
		else
			newtmp(0, Kl, curf);
	curf->con[0].type = CBits;
	curf->con[0].bits.i = 0xdeaddead;  /* UNDEF */
	curf->con[1].type = CBits;
	curf->lnk = *lnk;
	curf->leaf = 1;
	blink = &curf->start;
	curf->retty = Kx;
	if (peek() != Tglo)
		rcls = parsecls(&curf->retty);
	else
		rcls = K0;
	if (next() != Tglo)
		err("function name expected");
	strncpy(curf->name, tokval.str, NString-1);
	curf->vararg = parserefl(0);
	if (nextnl() != Tlbrace)
		err("function body must start with {");
	ps = PLbl;
	do
		ps = parseline(ps);
	while (ps != PEnd);
	if (!curb)
		err("empty function");
	if (curb->jmp.type == Jxxx)
		err("last block misses jump");
	curf->mem = vnew(0, sizeof curf->mem[0], PFn);
	curf->nmem = 0;
	curf->nblk = nblk;
	curf->rpo = vnew(nblk, sizeof curf->rpo[0], PFn);
	for (b=curf->start; b; b=b->link)
		b->dlink = 0; /* was trashed by findblk() */
	for (i=0; i<BMask+1; ++i)
		blkh[i] = 0;
	memset(tmph, 0, tmphcap * sizeof tmph[0]);
	typecheck(curf);
	return curf;
}

/**
 * Parses the fields of a struct or union type.
 * Handles primitive and user-defined types, alignment, and padding.
 * Updates the type's size and alignment.
 *
 * @param fld Array of fields to fill
 * @param ty Type being constructed
 * @param t Initial token for the field
 */
static void
parsefields(Field *fld, Typ *ty, int t)
{
	Typ *ty1;
	int n, c, a, al, type;
	uint64_t sz, s;

	n = 0;
	sz = 0;
	al = ty->align;
	while (t != Trbrace) {
		ty1 = 0;
		switch (t) {
		default: err("invalid type member specifier");
		case Td: type = Fd; s = 8; a = 3; break;
		case Tl: type = Fl; s = 8; a = 3; break;
		case Ts: type = Fs; s = 4; a = 2; break;
		case Tw: type = Fw; s = 4; a = 2; break;
		case Th: type = Fh; s = 2; a = 1; break;
		case Tb: type = Fb; s = 1; a = 0; break;
		case Ttyp:
			type = FTyp;
			ty1 = &typ[findtyp(ntyp-1)];
			s = ty1->size;
			a = ty1->align;
			break;
		}
		if (a > al)
			al = a;
		a = (1 << a) - 1;
		a = ((sz + a) & ~a) - sz;
		if (a) {
			if (n < NField) {
				/* padding */
				fld[n].type = FPad;
				fld[n].len = a;
				n++;
			}
		}
		t = nextnl();
		if (t == Tint) {
			c = tokval.num;
			t = nextnl();
		} else
			c = 1;
		sz += a + c*s;
		if (type == FTyp)
			s = ty1 - typ;
		for (; c>0 && n<NField; c--, n++) {
			fld[n].type = type;
			fld[n].len = s;
		}
		if (t != Tcomma)
			break;
		t = nextnl();
	}
	if (t != Trbrace)
		err(", or } expected");
	fld[n].type = FEnd;
	a = 1 << al;
	if (sz < ty->size)
		sz = ty->size;
	ty->size = (sz + a - 1) & -a;
	ty->align = al;
}

/**
 * Parses a type definition, including its name, alignment, and fields.
 * Handles both struct and union types, as well as 'dark' types (opaque).
 * Updates the global typ[] array with the new type.
 */
static void
parsetyp()
{
	Typ *ty;
	int t, al;
	uint n;

	/* be careful if extending the syntax
	 * to handle nested types, any pointer
	 * held to typ[] might be invalidated!
	 */
	vgrow(&typ, ntyp+1);
	ty = &typ[ntyp++];
	ty->isdark = 0;
	ty->isunion = 0;
	ty->align = -1;
	ty->size = 0;
	if (nextnl() != Ttyp ||  nextnl() != Teq)
		err("type name and then = expected");
	strcpy(ty->name, tokval.str);
	t = nextnl();
	if (t == Talign) {
		if (nextnl() != Tint)
			err("alignment expected");
		for (al=0; tokval.num /= 2; al++)
			;
		ty->align = al;
		t = nextnl();
	}
	if (t != Tlbrace)
		err("type body must start with {");
	t = nextnl();
	if (t == Tint) {
		ty->isdark = 1;
		ty->size = tokval.num;
		if (ty->align == -1)
			err("dark types need alignment");
		if (nextnl() != Trbrace)
			err("} expected");
		return;
	}
	n = 0;
	ty->fields = vnew(1, sizeof ty->fields[0], PHeap);
	if (t == Tlbrace) {
		ty->isunion = 1;
		do {
			if (t != Tlbrace)
				err("invalid union member");
			vgrow(&ty->fields, n+1);
			parsefields(ty->fields[n++], ty, nextnl());
			t = nextnl();
		} while (t != Trbrace);
	} else
		parsefields(ty->fields[n++], ty, t);
	ty->nunion = n;
}

/**
 * Parses a data reference for a data section entry.
 * Handles global/thread references and optional offsets.
 *
 * @param d Data entry to update
 */
static void
parsedatref(Dat *d)
{
	int t;

	d->isref = 1;
	d->u.ref.name = tokval.str;
	d->u.ref.off = 0;
	t = peek();
	if (t == Tplus) {
		next();
		if (next() != Tint)
			err("invalid token after offset in ref");
		d->u.ref.off = tokval.num;
	}
}

/**
 * Parses a string literal for a data section entry.
 * Updates the data entry with the string value.
 *
 * @param d Data entry to update
 */
static void
parsedatstr(Dat *d)
{
	d->isstr = 1;
	d->u.str = tokval.str;
}

/**
 * Parses a data section entry, including its name, alignment, and contents.
 * Handles all supported data types (integers, floats, strings, references).
 * Calls the provided callback for each parsed data item.
 *
 * @param cb Callback to invoke for each data item
 * @param lnk Linkage information for the data
 */
static void
parsedat(void cb(Dat *), Lnk *lnk)
{
	char name[NString] = {0};
	int t;
	Dat d;

	if (nextnl() != Tglo || nextnl() != Teq)
		err("data name, then = expected");
	strncpy(name, tokval.str, NString-1);
	t = nextnl();
	lnk->align = 8;
	if (t == Talign) {
		if (nextnl() != Tint)
			err("alignment expected");
		if (tokval.num <= 0 || tokval.num > CHAR_MAX
		|| (tokval.num & (tokval.num-1)) != 0)
			err("invalid alignment");
		lnk->align = tokval.num;
		t = nextnl();
	}
	d.type = DStart;
	d.name = name;
	d.lnk = lnk;
	cb(&d);

	if (t != Tlbrace)
		err("expected data contents in { .. }");
	for (;;) {
		switch (nextnl()) {
		default: err("invalid size specifier %c in data", tokval.chr);
		case Trbrace: goto Done;
		case Tl: d.type = DL; break;
		case Tw: d.type = DW; break;
		case Th: d.type = DH; break;
		case Tb: d.type = DB; break;
		case Ts: d.type = DW; break;
		case Td: d.type = DL; break;
		case Tz: d.type = DZ; break;
		}
		t = nextnl();
		do {
			d.isstr = 0;
			d.isref = 0;
			memset(&d.u, 0, sizeof d.u);
			if (t == Tflts)
				d.u.flts = tokval.flts;
			else if (t == Tfltd)
				d.u.fltd = tokval.fltd;
			else if (t == Tint)
				d.u.num = tokval.num;
			else if (t == Tglo)
				parsedatref(&d);
			else if (t == Tstr)
				parsedatstr(&d);
			else
				err("constant literal expected");
			cb(&d);
			t = nextnl();
		} while (t == Tint || t == Tflts || t == Tfltd || t == Tstr || t == Tglo);
		if (t == Trbrace)
			break;
		if (t != Tcomma)
			err(", or } expected");
	}
Done:
	d.type = DEnd;
	cb(&d);
}

/**
 * Parses linkage attributes for a function or data section.
 * Handles export, thread, common, and section attributes.
 * Updates the Lnk structure with the parsed attributes.
 *
 * @param lnk Linkage structure to update
 * @return The next token after linkage attributes
 */
static int
parselnk(Lnk *lnk)
{
	int t, haslnk;

	for (haslnk=0;; haslnk=1)
		switch ((t=nextnl())) {
		case Texport:
			lnk->export = 1;
			break;
		case Tthread:
			lnk->thread = 1;
			break;
		case Tcommon:
			lnk->common = 1;
			break;
		case Tsection:
			if (lnk->sec)
				err("only one section allowed");
			if (next() != Tstr)
				err("section \"name\" expected");
			lnk->sec = tokval.str;
			if (peek() == Tstr) {
				next();
				lnk->secf = tokval.str;
			}
			break;
		default:
			if (t == Tfunc && lnk->thread)
				err("only data may have thread linkage");
			if (haslnk && t != Tdata && t != Tfunc)
				err("only data and function have linkage");
			return t;
		}
}

/**
 * Main entry point for parsing a QBE IR file.
 * Handles top-level constructs: dbgfile, function, data, type, and EOF.
 * Calls the appropriate callback for each parsed item.
 *
 * @param f Input file pointer
 * @param path Path to the input file (for error messages)
 * @param dbgfile Callback for debug file directives
 * @param data Callback for data section entries
 * @param func Callback for function definitions
 */
void
parse(FILE *f, char *path, void dbgfile(char *), void data(Dat *), void func(Fn *))
{
	Lnk lnk;
	uint n;

	lexinit();
	inf = f;
	inpath = path;
	lnum = 1;
	thead = Txxx;
	ntyp = 0;
	typ = vnew(0, sizeof typ[0], PHeap);
	for (;;) {
		lnk = (Lnk){0};
		switch (parselnk(&lnk)) {
		default:
			err("top-level definition expected");
		case Tdbgfile:
			expect(Tstr);
			dbgfile(tokval.str);
			break;
		case Tfunc:
			lnk.align = 16;
			func(parsefn(&lnk));
			break;
		case Tdata:
			parsedat(data, &lnk);
			break;
		case Ttype:
			parsetyp();
			break;
		case Teof:
			for (n=0; n<ntyp; n++)
				if (typ[n].nunion)
					vfree(typ[n].fields);
			vfree(typ);
			return;
		}
	}
}

/**
 * Prints a constant value to a file for debugging or IR output.
 * Handles addresses, bits, and floating-point constants.
 *
 * @param c Constant to print
 * @param f Output file pointer
 */
static void
printcon(Con *c, FILE *f)
{
	switch (c->type) {
	case CUndef:
		break;
	case CAddr:
		if (c->sym.type == SThr)
			fprintf(f, "thread ");
		fprintf(f, "$%s", str(c->sym.id));
		if (c->bits.i)
			fprintf(f, "%+"PRIi64, c->bits.i);
		break;
	case CBits:
		if (c->flt == 1)
			fprintf(f, "s_%f", c->bits.s);
		else if (c->flt == 2)
			fprintf(f, "d_%lf", c->bits.d);
		else
			fprintf(f, "%"PRIi64, c->bits.i);
		break;
	}
}

/**
 * Prints a reference (temporary, constant, slot, etc.) to a file.
 * Used for debugging and IR output.
 *
 * @param r Reference to print
 * @param fn Function context (for temporary names)
 * @param f Output file pointer
 */
void
printref(Ref r, Fn *fn, FILE *f)
{
	int i;
	Mem *m;

	switch (rtype(r)) {
	case RTmp:
		if (r.val < Tmp0)
			fprintf(f, "R%d", r.val);
		else
			fprintf(f, "%%%s", fn->tmp[r.val].name);
		break;
	case RCon:
		if (req(r, UNDEF))
			fprintf(f, "UNDEF");
		else
			printcon(&fn->con[r.val], f);
		break;
	case RSlot:
		fprintf(f, "S%d", rsval(r));
		break;
	case RCall:
		fprintf(f, "%04x", r.val);
		break;
	case RType:
		fprintf(f, ":%s", typ[r.val].name);
		break;
	case RMem:
		i = 0;
		m = &fn->mem[r.val];
		fputc('[', f);
		if (m->offset.type != CUndef) {
			printcon(&m->offset, f);
			i = 1;
		}
		if (!req(m->base, R)) {
			if (i)
				fprintf(f, " + ");
			printref(m->base, fn, f);
			i = 1;
		}
		if (!req(m->index, R)) {
			if (i)
				fprintf(f, " + ");
			fprintf(f, "%d * ", m->scale);
			printref(m->index, fn, f);
		}
		fputc(']', f);
		break;
	case RInt:
		fprintf(f, "%d", rsval(r));
		break;
	case -1:
		fprintf(f, "R");
		break;
	}
}

/**
 * Prints a function in QBE IR format to a file.
 * Includes all blocks, phi nodes, instructions, and jumps.
 * Used for debugging and IR output.
 *
 * @param fn Function to print
 * @param f Output file pointer
 */
void
printfn(Fn *fn, FILE *f)
{
	static char ktoc[] = "wlsd";
	static char *jtoa[NJmp] = {
	#define X(j) [J##j] = #j,
		JMPS(X)
	#undef X
	};
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;

	fprintf(f, "function $%s() {\n", fn->name);
	for (b=fn->start; b; b=b->link) {
		fprintf(f, "@%s\n", b->name);
		for (p=b->phi; p; p=p->link) {
			fprintf(f, "\t");
			printref(p->to, fn, f);
			fprintf(f, " =%c phi ", ktoc[p->cls]);
			assert(p->narg);
			for (n=0;; n++) {
				fprintf(f, "@%s ", p->blk[n]->name);
				printref(p->arg[n], fn, f);
				if (n == p->narg-1) {
					fprintf(f, "\n");
					break;
				} else
					fprintf(f, ", ");
			}
		}
		for (i=b->ins; i<&b->ins[b->nins]; i++) {
			fprintf(f, "\t");
			if (!req(i->to, R)) {
				printref(i->to, fn, f);
				fprintf(f, " =%c ", ktoc[i->cls]);
			}
			assert(optab[i->op].name);
			fprintf(f, "%s", optab[i->op].name);
			if (req(i->to, R))
				switch (i->op) {
				case Oarg:
				case Oswap:
				case Oxcmp:
				case Oacmp:
				case Oacmn:
				case Oafcmp:
				case Oxtest:
				case Oxdiv:
				case Oxidiv:
					fputc(ktoc[i->cls], f);
				}
			if (!req(i->arg[0], R)) {
				fprintf(f, " ");
				printref(i->arg[0], fn, f);
			}
			if (!req(i->arg[1], R)) {
				fprintf(f, ", ");
				printref(i->arg[1], fn, f);
			}
			fprintf(f, "\n");
		}
		switch (b->jmp.type) {
		case Jret0:
		case Jretsb:
		case Jretub:
		case Jretsh:
		case Jretuh:
		case Jretw:
		case Jretl:
		case Jrets:
		case Jretd:
		case Jretc:
			fprintf(f, "\t%s", jtoa[b->jmp.type]);
			if (b->jmp.type != Jret0 || !req(b->jmp.arg, R)) {
				fprintf(f, " ");
				printref(b->jmp.arg, fn, f);
			}
			if (b->jmp.type == Jretc)
				fprintf(f, ", :%s", typ[fn->retty].name);
			fprintf(f, "\n");
			break;
		case Jhlt:
			fprintf(f, "\thlt\n");
			break;
		case Jjmp:
			if (b->s1 != b->link)
				fprintf(f, "\tjmp @%s\n", b->s1->name);
			break;
		default:
			fprintf(f, "\t%s ", jtoa[b->jmp.type]);
			if (b->jmp.type == Jjnz) {
				printref(b->jmp.arg, fn, f);
				fprintf(f, ", ");
			}
			assert(b->s1 && b->s2);
			fprintf(f, "@%s, @%s\n", b->s1->name, b->s2->name);
			break;
		}
	}
	fprintf(f, "}\n");
}
