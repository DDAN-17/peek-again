	.text
	.file	"lib.ad118e182f7a4706-cgu.0"
	.section	.text.do_it,"ax",@progbits
	.globl	do_it
	.p2align	4, 0x90
	.type	do_it,@function
do_it:
	.cfi_startproc
	movq	%rdi, %rax
	movl	$1, %edi
	testq	%rdx, %rdx
	je	.LBB0_1
	leaq	1(%rsi), %rcx
	cmpb	$69, (%rsi)
	jne	.LBB0_3
	cmpq	$1, %rdx
	jne	.LBB0_6
	xorl	%r8d, %r8d
	jmp	.LBB0_7
.LBB0_1:
	xorl	%r8d, %r8d
	movq	%rsi, %rcx
	jmp	.LBB0_7
.LBB0_3:
	movq	%rsi, %r8
	jmp	.LBB0_7
.LBB0_6:
	movq	%rcx, %r8
	leaq	2(%rsi), %rcx
	xorl	%edi, %edi
	cmpb	$69, 1(%rsi)
	setne	%dil
.LBB0_7:
	addq	%rdx, %rsi
	movq	%rdi, (%rax)
	movq	%r8, 16(%rax)
	movq	%rcx, 24(%rax)
	movq	%rsi, 32(%rax)
	retq
.Lfunc_end0:
	.size	do_it, .Lfunc_end0-do_it
	.cfi_endproc

	.ident	"rustc version 1.81.0 (eeb90cda1 2024-09-04)"
	.section	".note.GNU-stack","",@progbits
