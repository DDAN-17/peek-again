	.text
	.file	"prior.69b695203a219be6-cgu.0"
	.section	.text.do_it,"ax",@progbits
	.globl	do_it
	.p2align	4, 0x90
	.type	do_it,@function
do_it:
	.cfi_startproc
	movq	%rdi, %rax
	movl	$1, %ecx
	testq	%rdx, %rdx
	je	.LBB0_1
	leaq	1(%rsi), %rdi
	cmpb	$69, (%rsi)
	jne	.LBB0_3
	cmpq	$1, %rdx
	jne	.LBB0_6
	xorl	%r8d, %r8d
	jmp	.LBB0_7
.LBB0_1:
	xorl	%r8d, %r8d
	movq	%rsi, %rdi
	jmp	.LBB0_7
.LBB0_3:
	movq	%rsi, %r8
	jmp	.LBB0_7
.LBB0_6:
	movq	%rdi, %r8
	leaq	2(%rsi), %rdi
	xorl	%ecx, %ecx
	cmpb	$69, 1(%rsi)
	setne	%cl
.LBB0_7:
	addq	%rdx, %rsi
	movq	%rcx, (%rax)
	movq	%r8, 8(%rax)
	movq	%rdi, 24(%rax)
	movq	%rsi, 32(%rax)
	retq
.Lfunc_end0:
	.size	do_it, .Lfunc_end0-do_it
	.cfi_endproc

	.ident	"rustc version 1.81.0 (eeb90cda1 2024-09-04)"
	.section	".note.GNU-stack","",@progbits
