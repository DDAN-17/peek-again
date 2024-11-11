	.text
	.file	"lib.ad118e182f7a4706-cgu.0"
	.section	.text.analysis,"ax",@progbits
	.globl	analysis
	.p2align	4, 0x90
	.type	analysis,@function
analysis:
	.cfi_startproc
	movq	%rdi, %rax
	testq	%rdx, %rdx
	je	.LBB0_1
	leaq	1(%rsi), %rcx
	xorl	%edi, %edi
	cmpb	$69, (%rsi)
	setne	%dil
	movq	%rsi, %r8
	jmp	.LBB0_3
.LBB0_1:
	movl	$1, %edi
	xorl	%r8d, %r8d
	movq	%rsi, %rcx
.LBB0_3:
	addq	%rdx, %rsi
	movq	%rdi, (%rax)
	movq	%r8, 8(%rax)
	movq	%rcx, 32(%rax)
	movq	%rsi, 40(%rax)
	retq
.Lfunc_end0:
	.size	analysis, .Lfunc_end0-analysis
	.cfi_endproc

	.ident	"rustc version 1.81.0 (eeb90cda1 2024-09-04)"
	.section	".note.GNU-stack","",@progbits
