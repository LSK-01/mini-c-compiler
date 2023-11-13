	.section	__TEXT,__text,regular,pure_instructions
	.build_version macos, 13, 0
	.globl	_addition                       ; -- Begin function addition
	.p2align	2
_addition:                              ; @addition
	.cfi_startproc
; %bb.0:                                ; %entry
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]             ; 16-byte Folded Spill
	.cfi_def_cfa_offset 32
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mul	w8, w0, w1
	add	w9, w0, w1
	cmp	w0, #4
	stp	w0, w1, [sp, #4]
	csel	w0, w9, w8, eq
	str	w9, [sp, #12]
	bl	_print_int
	ldp	x29, x30, [sp, #16]             ; 16-byte Folded Reload
	ldr	w0, [sp, #12]
	add	sp, sp, #32
	ret
	.cfi_endproc
                                        ; -- End function
.subsections_via_symbols
