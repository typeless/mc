#define Maxarg 4 /* maximum number of args an insn can have */
#define Wordsz 4 /* the size of a "natural int" */
#define Ptrsz  8 /* the size of a machine word (ie, pointer size) */

/* globals */
/* options */
size_t size(Node *n);
void gen(char *out);
void genc(FILE *fd);
