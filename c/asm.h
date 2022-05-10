#define Maxarg 4 /* maximum number of args an insn can have */
#define Wordsz 4 /* the size of a "natural int" */
#define Ptrsz  8 /* the size of a machine word (ie, pointer size) */

typedef enum {
	Bti8,
	Bti16,
	Bti32,
	Bti64,
	Btimin,     /* byte-packed uint */
	Btref,
	Btbytes,
	Btseq,
	Btpad,
} Blobtype;

typedef struct Blob Blob;
struct Blob {
	Blobtype type;
	size_t align;
	char *lbl;  /* may be null */
	char isglobl;
	char iscomdat;
	union {
		uvlong npad;
		uvlong ival;
		struct {
			char *str;
			char isextern;
			size_t off;
		} ref;
		struct {
			size_t len;
			char *buf;
		} bytes;
		struct {
			size_t nsub;
			Blob **sub;
		} seq;
	};
};


/* globals */
/* options */
/* blob stuff */
Blob *mkblobpad(size_t sz);
Blob *mkblobi(Blobtype type, uint64_t ival);
Blob *mkblobbytes(char *buf, size_t len);
Blob *mkblobseq(Blob **sub, size_t nsub);
Blob *mkblobref(char *lbl, size_t off, int isextern);
void blobfree(Blob *b);

Blob *tydescblob(Type *t);
Blob *litblob(Htab *globls, Htab *strtab, Node *n);
size_t blobsz(Blob *b);

size_t size(Node *n);
void gen(char *out);
void genc(FILE *fd);
