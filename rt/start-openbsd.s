.section ".note.openbsd.ident", "a"
	.p2align 2
	.long   8
	.long   4
	.long   1
	.ascii "OpenBSD\0"
	.long   0
	.p2align 2

.data
/* sys.__cenvp : byte## */
.globl sys$__cenvp
sys$__cenvp:
    .quad 0

.text
/*
 * The entry point for the whole program.
 * This is called by the OS. In order, it:
 *  - Sets up all argc entries as slices
 *  - Converts argc/argv to a slice
 *  - Stashes a raw envp copy in __cenvp (for syscalls to use)
 *  - Calls main()
 */
.globl _start
_start:
	movq	%rsp,%rbp
	andq	$-16,%rsp		/* align the stack pointer */

	/* load argc, argv, envp from stack */
	movq	(%rbp),%rax		/* argc */
	leaq	8(%rbp),%rbx		/* argv */
	leaq	16(%rbp,%rax,8),%rcx	/* envp = argv + 8*argc + 8 */

	/* store envp for some syscalls to use without converting */
	movq    %rcx,sys$__cenvp(%rip)

	/* stack allocate sizeof(byte[:])*argc */
	imulq	$16,%rax,%rdx
	subq	%rdx,%rsp
	movq	%rsp,%rcx		/* args[:] */

	/* convert argc, argv to byte[:][:] for args. */
	pushq	%rax
	pushq	%rcx
	call	cvt

	xorq %rbp,%rbp
	/*
	  we're done startup, and we kind of want
	  to call kbind here, but this breaks
	  when we dynamically link in libc.
	 */
	/* call pre-main initializers */
	call	__init__
	/* enter the main program */
	call	main
	/* exit(0) */
	xorq	%rdi,%rdi
	movq	$1,%rax
	syscall

/*
 * provide __guard_local for if we are
 * linking against libc
 */
.section ".openbsd.randomdata", "aw"
	.global	__guard_local
	.hidden	__guard_local
	.type	__guard_local, "object"
	.p2align	3
__guard_local:
	.quad	0
	.size	__guard_local, 8

.section ".note.openbsd.ident", "a"
        .p2align 2
        .long   8
        .long   4
        .long   1
        .ascii "OpenBSD\0"
        .long   0
        .p2align 2
