
build/add_carry:	file format mach-o arm64

Disassembly of section __TEXT,__text:

00000001000039c0 <_addInt__stdZprivateZdigitsutils_u184>:
1000039c0: d10183ff    	sub	sp, sp, #0x60
1000039c4: a9025ff8    	stp	x24, x23, [sp, #0x20]
1000039c8: a90357f6    	stp	x22, x21, [sp, #0x30]
1000039cc: a9044ff4    	stp	x20, x19, [sp, #0x40]
1000039d0: a9057bfd    	stp	x29, x30, [sp, #0x50]
1000039d4: 910143fd    	add	x29, sp, #0x50
1000039d8: aa0003f3    	mov	x19, x0
1000039dc: b0000048    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
1000039e0: f9400908    	ldr	x8, [x8, #0x10]
1000039e4: f9400108    	ldr	x8, [x8]
1000039e8: f9000fe8    	str	x8, [sp, #0x18]
1000039ec: 90000048    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
1000039f0: 91178108    	add	x8, x8, #0x5e0
1000039f4: f101903f    	cmp	x1, #0x64
1000039f8: 54000403    	b.lo	0x100003a78 <_addInt__stdZprivateZdigitsutils_u184+0xb8>
1000039fc: d2800009    	mov	x9, #0x0                ; =0
100003a00: d29eb86a    	mov	x10, #0xf5c3            ; =62915
100003a04: f2ab850a    	movk	x10, #0x5c28, lsl #16
100003a08: f2d851ea    	movk	x10, #0xc28f, lsl #32
100003a0c: f2e51eaa    	movk	x10, #0x28f5, lsl #48
100003a10: 528ff38b    	mov	w11, #0x7f9c            ; =32668
100003a14: 910003ec    	mov	x12, sp
100003a18: aa0103ed    	mov	x13, x1
100003a1c: d342fc2e    	lsr	x14, x1, #2
100003a20: 9bca7dce    	umulh	x14, x14, x10
100003a24: d342fdc1    	lsr	x1, x14, #2
100003a28: 1b0b342e    	madd	w14, w1, w11, w13
100003a2c: 531f79ce    	lsl	w14, w14, #1
100003a30: 93403dce    	sxth	x14, w14
100003a34: 8b09018f    	add	x15, x12, x9
100003a38: 786e690e    	ldrh	w14, [x8, x14]
100003a3c: 79002dee    	strh	w14, [x15, #0x16]
100003a40: d1000929    	sub	x9, x9, #0x2
100003a44: d344fdad    	lsr	x13, x13, #4
100003a48: f109c1bf    	cmp	x13, #0x270
100003a4c: 54fffe68    	b.hi	0x100003a18 <_addInt__stdZprivateZdigitsutils_u184+0x58>
100003a50: 91005d29    	add	x9, x9, #0x17
100003a54: f100243f    	cmp	x1, #0x9
100003a58: 54000169    	b.ls	0x100003a84 <_addInt__stdZprivateZdigitsutils_u184+0xc4>
100003a5c: 8b01050a    	add	x10, x8, x1, lsl #1
100003a60: 39400548    	ldrb	w8, [x10, #0x1]
100003a64: 3940014a    	ldrb	w10, [x10]
100003a68: d1000535    	sub	x21, x9, #0x1
100003a6c: 910003eb    	mov	x11, sp
100003a70: 3835696a    	strb	w10, [x11, x21]
100003a74: 14000006    	b	0x100003a8c <_addInt__stdZprivateZdigitsutils_u184+0xcc>
100003a78: 528002e9    	mov	w9, #0x17               ; =23
100003a7c: f100243f    	cmp	x1, #0x9
100003a80: 54fffee8    	b.hi	0x100003a5c <_addInt__stdZprivateZdigitsutils_u184+0x9c>
100003a84: 1100c028    	add	w8, w1, #0x30
100003a88: aa0903f5    	mov	x21, x9
100003a8c: 910003f6    	mov	x22, sp
100003a90: 38296ac8    	strb	w8, [x22, x9]
100003a94: 52800308    	mov	w8, #0x18               ; =24
100003a98: f9400277    	ldr	x23, [x19]
100003a9c: cb150114    	sub	x20, x8, x21
100003aa0: 8b1402e1    	add	x1, x23, x20
100003aa4: aa1303e0    	mov	x0, x19
100003aa8: 94000f28    	bl	0x100007748 <_setLengthStrV2>
100003aac: f9400668    	ldr	x8, [x19, #0x8]
100003ab0: 8b170108    	add	x8, x8, x23
100003ab4: 91002100    	add	x0, x8, #0x8
100003ab8: 8b1502c1    	add	x1, x22, x21
100003abc: aa1403e2    	mov	x2, x20
100003ac0: 94001eb0    	bl	0x10000b580 <_strlen+0x10000b580>
100003ac4: f9400fe8    	ldr	x8, [sp, #0x18]
100003ac8: b0000049    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
100003acc: f9400929    	ldr	x9, [x9, #0x10]
100003ad0: f9400129    	ldr	x9, [x9]
100003ad4: eb08013f    	cmp	x9, x8
100003ad8: 540000e1    	b.ne	0x100003af4 <_addInt__stdZprivateZdigitsutils_u184+0x134>
100003adc: a9457bfd    	ldp	x29, x30, [sp, #0x50]
100003ae0: a9444ff4    	ldp	x20, x19, [sp, #0x40]
100003ae4: a94357f6    	ldp	x22, x21, [sp, #0x30]
100003ae8: a9425ff8    	ldp	x24, x23, [sp, #0x20]
100003aec: 910183ff    	add	sp, sp, #0x60
100003af0: d65f03c0    	ret
100003af4: 94001e85    	bl	0x10000b508 <_strlen+0x10000b508>

0000000100003af8 <_addInt__stdZprivateZdigitsutils_u187>:
100003af8: d10183ff    	sub	sp, sp, #0x60
100003afc: a9025ff8    	stp	x24, x23, [sp, #0x20]
100003b00: a90357f6    	stp	x22, x21, [sp, #0x30]
100003b04: a9044ff4    	stp	x20, x19, [sp, #0x40]
100003b08: a9057bfd    	stp	x29, x30, [sp, #0x50]
100003b0c: 910143fd    	add	x29, sp, #0x50
100003b10: aa0103f4    	mov	x20, x1
100003b14: aa0003f3    	mov	x19, x0
100003b18: b0000048    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100003b1c: f9400908    	ldr	x8, [x8, #0x10]
100003b20: f9400108    	ldr	x8, [x8]
100003b24: f9000fe8    	str	x8, [sp, #0x18]
100003b28: b7f80481    	tbnz	x1, #0x3f, 0x100003bb8 <_addInt__stdZprivateZdigitsutils_u187+0xc0>
100003b2c: 90000048    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100003b30: 91178108    	add	x8, x8, #0x5e0
100003b34: f101929f    	cmp	x20, #0x64
100003b38: 54000623    	b.lo	0x100003bfc <_addInt__stdZprivateZdigitsutils_u187+0x104>
100003b3c: d2800009    	mov	x9, #0x0                ; =0
100003b40: d29eb86a    	mov	x10, #0xf5c3            ; =62915
100003b44: f2ab850a    	movk	x10, #0x5c28, lsl #16
100003b48: f2d851ea    	movk	x10, #0xc28f, lsl #32
100003b4c: f2e51eaa    	movk	x10, #0x28f5, lsl #48
100003b50: 528ff38b    	mov	w11, #0x7f9c            ; =32668
100003b54: 910003ec    	mov	x12, sp
100003b58: aa1403ed    	mov	x13, x20
100003b5c: d342fe8e    	lsr	x14, x20, #2
100003b60: 9bca7dce    	umulh	x14, x14, x10
100003b64: d342fdd4    	lsr	x20, x14, #2
100003b68: 1b0b368e    	madd	w14, w20, w11, w13
100003b6c: 531f79ce    	lsl	w14, w14, #1
100003b70: 93403dce    	sxth	x14, w14
100003b74: 8b09018f    	add	x15, x12, x9
100003b78: 786e690e    	ldrh	w14, [x8, x14]
100003b7c: 79002dee    	strh	w14, [x15, #0x16]
100003b80: d1000929    	sub	x9, x9, #0x2
100003b84: d344fdad    	lsr	x13, x13, #4
100003b88: f109c1bf    	cmp	x13, #0x270
100003b8c: 54fffe68    	b.hi	0x100003b58 <_addInt__stdZprivateZdigitsutils_u187+0x60>
100003b90: 91005d29    	add	x9, x9, #0x17
100003b94: f100269f    	cmp	x20, #0x9
100003b98: 54000389    	b.ls	0x100003c08 <_addInt__stdZprivateZdigitsutils_u187+0x110>
100003b9c: 8b14050a    	add	x10, x8, x20, lsl #1
100003ba0: 39400548    	ldrb	w8, [x10, #0x1]
100003ba4: 3940014a    	ldrb	w10, [x10]
100003ba8: d1000535    	sub	x21, x9, #0x1
100003bac: 910003eb    	mov	x11, sp
100003bb0: 3835696a    	strb	w10, [x11, x21]
100003bb4: 14000017    	b	0x100003c10 <_addInt__stdZprivateZdigitsutils_u187+0x118>
100003bb8: cb1403f4    	neg	x20, x20
100003bbc: aa1303e0    	mov	x0, x19
100003bc0: 52800021    	mov	w1, #0x1                ; =1
100003bc4: 94000de5    	bl	0x100007358 <_prepareAdd>
100003bc8: a9402269    	ldp	x9, x8, [x19]
100003bcc: 8b090108    	add	x8, x8, x9
100003bd0: 528005a9    	mov	w9, #0x2d               ; =45
100003bd4: 39002109    	strb	w9, [x8, #0x8]
100003bd8: a9402668    	ldp	x8, x9, [x19]
100003bdc: 91000508    	add	x8, x8, #0x1
100003be0: f9000268    	str	x8, [x19]
100003be4: 8b080128    	add	x8, x9, x8
100003be8: 3900211f    	strb	wzr, [x8, #0x8]
100003bec: 90000048    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100003bf0: 91178108    	add	x8, x8, #0x5e0
100003bf4: f101929f    	cmp	x20, #0x64
100003bf8: 54fffa22    	b.hs	0x100003b3c <_addInt__stdZprivateZdigitsutils_u187+0x44>
100003bfc: 528002e9    	mov	w9, #0x17               ; =23
100003c00: f100269f    	cmp	x20, #0x9
100003c04: 54fffcc8    	b.hi	0x100003b9c <_addInt__stdZprivateZdigitsutils_u187+0xa4>
100003c08: 1100c288    	add	w8, w20, #0x30
100003c0c: aa0903f5    	mov	x21, x9
100003c10: 910003f6    	mov	x22, sp
100003c14: 38296ac8    	strb	w8, [x22, x9]
100003c18: 52800308    	mov	w8, #0x18               ; =24
100003c1c: f9400277    	ldr	x23, [x19]
100003c20: cb150114    	sub	x20, x8, x21
100003c24: 8b1402e1    	add	x1, x23, x20
100003c28: aa1303e0    	mov	x0, x19
100003c2c: 94000ec7    	bl	0x100007748 <_setLengthStrV2>
100003c30: f9400668    	ldr	x8, [x19, #0x8]
100003c34: 8b170108    	add	x8, x8, x23
100003c38: 91002100    	add	x0, x8, #0x8
100003c3c: 8b1502c1    	add	x1, x22, x21
100003c40: aa1403e2    	mov	x2, x20
100003c44: 94001e4f    	bl	0x10000b580 <_strlen+0x10000b580>
100003c48: f9400fe8    	ldr	x8, [sp, #0x18]
100003c4c: b0000049    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
100003c50: f9400929    	ldr	x9, [x9, #0x10]
100003c54: f9400129    	ldr	x9, [x9]
100003c58: eb08013f    	cmp	x9, x8
100003c5c: 540000e1    	b.ne	0x100003c78 <_addInt__stdZprivateZdigitsutils_u187+0x180>
100003c60: a9457bfd    	ldp	x29, x30, [sp, #0x50]
100003c64: a9444ff4    	ldp	x20, x19, [sp, #0x40]
100003c68: a94357f6    	ldp	x22, x21, [sp, #0x30]
100003c6c: a9425ff8    	ldp	x24, x23, [sp, #0x20]
100003c70: 910183ff    	add	sp, sp, #0x60
100003c74: d65f03c0    	ret
100003c78: 94001e24    	bl	0x10000b508 <_strlen+0x10000b508>

0000000100003c7c <_dollar___add95carry_u320>:
100003c7c: d100c3ff    	sub	sp, sp, #0x30
100003c80: a9014ff4    	stp	x20, x19, [sp, #0x10]
100003c84: a9027bfd    	stp	x29, x30, [sp, #0x20]
100003c88: 910083fd    	add	x29, sp, #0x20
100003c8c: aa0003f3    	mov	x19, x0
100003c90: b0000048    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100003c94: 9102c108    	add	x8, x8, #0xb0
100003c98: 3dc00100    	ldr	q0, [x8]
100003c9c: 3d8003e0    	str	q0, [sp]
100003ca0: 910003e0    	mov	x0, sp
100003ca4: 528000a1    	mov	w1, #0x5                ; =5
100003ca8: 94000dac    	bl	0x100007358 <_prepareAdd>
100003cac: a94023e9    	ldp	x9, x8, [sp]
100003cb0: 8b090108    	add	x8, x8, x9
100003cb4: 52800e69    	mov	w9, #0x73               ; =115
100003cb8: 79001909    	strh	w9, [x8, #0xc]
100003cbc: 528d2d89    	mov	w9, #0x696c             ; =26988
100003cc0: 72ac4da9    	movk	w9, #0x626d, lsl #16
100003cc4: b9000909    	str	w9, [x8, #0x8]
100003cc8: f94003e8    	ldr	x8, [sp]
100003ccc: 91001508    	add	x8, x8, #0x5
100003cd0: f90003e8    	str	x8, [sp]
100003cd4: 910003e0    	mov	x0, sp
100003cd8: 52800041    	mov	w1, #0x2                ; =2
100003cdc: 94000d9f    	bl	0x100007358 <_prepareAdd>
100003ce0: a94023e9    	ldp	x9, x8, [sp]
100003ce4: 8b090108    	add	x8, x8, x9
100003ce8: 3900291f    	strb	wzr, [x8, #0xa]
100003cec: 52840749    	mov	w9, #0x203a             ; =8250
100003cf0: 79001109    	strh	w9, [x8, #0x8]
100003cf4: f94003e8    	ldr	x8, [sp]
100003cf8: 91000908    	add	x8, x8, #0x2
100003cfc: f90003e8    	str	x8, [sp]
100003d00: 910003e0    	mov	x0, sp
100003d04: aa1303e1    	mov	x1, x19
100003d08: 94000efa    	bl	0x1000078f0 <_addQuoted__add95carry_u395>
100003d0c: 910003e0    	mov	x0, sp
100003d10: 52800021    	mov	w1, #0x1                ; =1
100003d14: 94000d91    	bl	0x100007358 <_prepareAdd>
100003d18: a94023e9    	ldp	x9, x8, [sp]
100003d1c: 8b090108    	add	x8, x8, x9
100003d20: 52800529    	mov	w9, #0x29               ; =41
100003d24: 79001109    	strh	w9, [x8, #0x8]
100003d28: a94007e8    	ldp	x8, x1, [sp]
100003d2c: 91000500    	add	x0, x8, #0x1
100003d30: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100003d34: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100003d38: 9100c3ff    	add	sp, sp, #0x30
100003d3c: d65f03c0    	ret

0000000100003d40 <_collectionToString__add95carry_u408>:
100003d40: d10183ff    	sub	sp, sp, #0x60
100003d44: a90167fa    	stp	x26, x25, [sp, #0x10]
100003d48: a9025ff8    	stp	x24, x23, [sp, #0x20]
100003d4c: a90357f6    	stp	x22, x21, [sp, #0x30]
100003d50: a9044ff4    	stp	x20, x19, [sp, #0x40]
100003d54: a9057bfd    	stp	x29, x30, [sp, #0x50]
100003d58: 910143fd    	add	x29, sp, #0x50
100003d5c: aa0603f4    	mov	x20, x6
100003d60: aa0503f3    	mov	x19, x5
100003d64: aa0403f8    	mov	x24, x4
100003d68: aa0303f5    	mov	x21, x3
100003d6c: aa0003f6    	mov	x22, x0
100003d70: a9007fff    	stp	xzr, xzr, [sp]
100003d74: 910003e0    	mov	x0, sp
100003d78: 94000e17    	bl	0x1000075d4 <_eqcopy___system_u2636>
100003d7c: f94002c1    	ldr	x1, [x22]
100003d80: 910003e0    	mov	x0, sp
100003d84: 94000eda    	bl	0x1000078ec <_addQuoted__add95carry_u445>
100003d88: f94006d9    	ldr	x25, [x22, #0x8]
100003d8c: 910003e0    	mov	x0, sp
100003d90: aa1503e1    	mov	x1, x21
100003d94: 94000d71    	bl	0x100007358 <_prepareAdd>
100003d98: f10006bf    	cmp	x21, #0x1
100003d9c: 540005ab    	b.lt	0x100003e50 <_collectionToString__add95carry_u408+0x110>
100003da0: 910006b7    	add	x23, x21, #0x1
100003da4: 91002318    	add	x24, x24, #0x8
100003da8: a94023e9    	ldp	x9, x8, [sp]
100003dac: 8b090108    	add	x8, x8, x9
100003db0: 91002100    	add	x0, x8, #0x8
100003db4: aa1803e1    	mov	x1, x24
100003db8: aa1703e2    	mov	x2, x23
100003dbc: 94001df1    	bl	0x10000b580 <_strlen+0x10000b580>
100003dc0: f94003e8    	ldr	x8, [sp]
100003dc4: 8b150108    	add	x8, x8, x21
100003dc8: f90003e8    	str	x8, [sp]
100003dcc: 910003e0    	mov	x0, sp
100003dd0: aa1903e1    	mov	x1, x25
100003dd4: 94000ec6    	bl	0x1000078ec <_addQuoted__add95carry_u445>
100003dd8: f9400ad9    	ldr	x25, [x22, #0x10]
100003ddc: 910003e0    	mov	x0, sp
100003de0: aa1503e1    	mov	x1, x21
100003de4: 94000d5d    	bl	0x100007358 <_prepareAdd>
100003de8: a94023e9    	ldp	x9, x8, [sp]
100003dec: 8b090108    	add	x8, x8, x9
100003df0: 91002100    	add	x0, x8, #0x8
100003df4: aa1803e1    	mov	x1, x24
100003df8: aa1703e2    	mov	x2, x23
100003dfc: 94001de1    	bl	0x10000b580 <_strlen+0x10000b580>
100003e00: f94003e8    	ldr	x8, [sp]
100003e04: 8b150108    	add	x8, x8, x21
100003e08: f90003e8    	str	x8, [sp]
100003e0c: 910003e0    	mov	x0, sp
100003e10: aa1903e1    	mov	x1, x25
100003e14: 94000eb6    	bl	0x1000078ec <_addQuoted__add95carry_u445>
100003e18: f9400ed6    	ldr	x22, [x22, #0x18]
100003e1c: 910003e0    	mov	x0, sp
100003e20: aa1503e1    	mov	x1, x21
100003e24: 94000d4d    	bl	0x100007358 <_prepareAdd>
100003e28: a94023e9    	ldp	x9, x8, [sp]
100003e2c: 8b090108    	add	x8, x8, x9
100003e30: 91002100    	add	x0, x8, #0x8
100003e34: aa1803e1    	mov	x1, x24
100003e38: aa1703e2    	mov	x2, x23
100003e3c: 94001dd1    	bl	0x10000b580 <_strlen+0x10000b580>
100003e40: f94003e8    	ldr	x8, [sp]
100003e44: 8b150108    	add	x8, x8, x21
100003e48: f90003e8    	str	x8, [sp]
100003e4c: 1400000f    	b	0x100003e88 <_collectionToString__add95carry_u408+0x148>
100003e50: 910003e0    	mov	x0, sp
100003e54: aa1903e1    	mov	x1, x25
100003e58: 94000ea5    	bl	0x1000078ec <_addQuoted__add95carry_u445>
100003e5c: f9400ad7    	ldr	x23, [x22, #0x10]
100003e60: 910003e0    	mov	x0, sp
100003e64: aa1503e1    	mov	x1, x21
100003e68: 94000d3c    	bl	0x100007358 <_prepareAdd>
100003e6c: 910003e0    	mov	x0, sp
100003e70: aa1703e1    	mov	x1, x23
100003e74: 94000e9e    	bl	0x1000078ec <_addQuoted__add95carry_u445>
100003e78: f9400ed6    	ldr	x22, [x22, #0x18]
100003e7c: 910003e0    	mov	x0, sp
100003e80: aa1503e1    	mov	x1, x21
100003e84: 94000d35    	bl	0x100007358 <_prepareAdd>
100003e88: 910003e0    	mov	x0, sp
100003e8c: aa1603e1    	mov	x1, x22
100003e90: 94000e97    	bl	0x1000078ec <_addQuoted__add95carry_u445>
100003e94: 910003e0    	mov	x0, sp
100003e98: aa1303e1    	mov	x1, x19
100003e9c: 94000d2f    	bl	0x100007358 <_prepareAdd>
100003ea0: f94003e0    	ldr	x0, [sp]
100003ea4: f100067f    	cmp	x19, #0x1
100003ea8: 5400012b    	b.lt	0x100003ecc <_collectionToString__add95carry_u408+0x18c>
100003eac: f94007e8    	ldr	x8, [sp, #0x8]
100003eb0: 8b000108    	add	x8, x8, x0
100003eb4: 91002100    	add	x0, x8, #0x8
100003eb8: 91002281    	add	x1, x20, #0x8
100003ebc: 91000662    	add	x2, x19, #0x1
100003ec0: 94001db0    	bl	0x10000b580 <_strlen+0x10000b580>
100003ec4: f94003e8    	ldr	x8, [sp]
100003ec8: 8b130100    	add	x0, x8, x19
100003ecc: f94007e1    	ldr	x1, [sp, #0x8]
100003ed0: a9457bfd    	ldp	x29, x30, [sp, #0x50]
100003ed4: a9444ff4    	ldp	x20, x19, [sp, #0x40]
100003ed8: a94357f6    	ldp	x22, x21, [sp, #0x30]
100003edc: a9425ff8    	ldp	x24, x23, [sp, #0x20]
100003ee0: a94167fa    	ldp	x26, x25, [sp, #0x10]
100003ee4: 910183ff    	add	sp, sp, #0x60
100003ee8: d65f03c0    	ret

0000000100003eec <_dollar___add95carry_u403>:
100003eec: 90000042    	adrp	x2, 0x10000b000 <_bench__add95carry_u844+0x104>
100003ef0: 911b6042    	add	x2, x2, #0x6d8
100003ef4: 90000044    	adrp	x4, 0x10000b000 <_bench__add95carry_u844+0x104>
100003ef8: 911ba084    	add	x4, x4, #0x6e8
100003efc: 90000046    	adrp	x6, 0x10000b000 <_bench__add95carry_u844+0x104>
100003f00: 911be0c6    	add	x6, x6, #0x6f8
100003f04: 52800021    	mov	w1, #0x1                ; =1
100003f08: 52800043    	mov	w3, #0x2                ; =2
100003f0c: 52800025    	mov	w5, #0x1                ; =1
100003f10: 17ffff8c    	b	0x100003d40 <_collectionToString__add95carry_u408>

0000000100003f14 <_dollar___systemZdollars_u8>:
100003f14: d10083ff    	sub	sp, sp, #0x20
100003f18: a9017bfd    	stp	x29, x30, [sp, #0x10]
100003f1c: 910043fd    	add	x29, sp, #0x10
100003f20: aa0003e1    	mov	x1, x0
100003f24: a9007fff    	stp	xzr, xzr, [sp]
100003f28: 910003e0    	mov	x0, sp
100003f2c: 97fffef3    	bl	0x100003af8 <_addInt__stdZprivateZdigitsutils_u187>
100003f30: a94007e0    	ldp	x0, x1, [sp]
100003f34: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100003f38: 910083ff    	add	sp, sp, #0x20
100003f3c: d65f03c0    	ret

0000000100003f40 <_raiseOutOfMem__system_u5730>:
100003f40: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100003f44: 910003fd    	mov	x29, sp
100003f48: 90000088    	adrp	x8, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
100003f4c: f9421908    	ldr	x8, [x8, #0x430]
100003f50: b4000048    	cbz	x8, 0x100003f58 <_raiseOutOfMem__system_u5730+0x18>
100003f54: d63f0100    	blr	x8
100003f58: b0000048    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100003f5c: f9400d08    	ldr	x8, [x8, #0x18]
100003f60: f9400100    	ldr	x0, [x8]
100003f64: 94000003    	bl	0x100003f70 <_rawWrite>
100003f68: 52800020    	mov	w0, #0x1                ; =1
100003f6c: 94001d70    	bl	0x10000b52c <_strlen+0x10000b52c>

0000000100003f70 <_rawWrite>:
100003f70: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100003f74: a9017bfd    	stp	x29, x30, [sp, #0x10]
100003f78: 910043fd    	add	x29, sp, #0x10
100003f7c: aa0003f3    	mov	x19, x0
100003f80: 90000040    	adrp	x0, 0x10000b000 <_bench__add95carry_u844+0x104>
100003f84: 9133a000    	add	x0, x0, #0xce8
100003f88: 52800021    	mov	w1, #0x1                ; =1
100003f8c: 528001c2    	mov	w2, #0xe                ; =14
100003f90: aa1303e3    	mov	x3, x19
100003f94: 94001d72    	bl	0x10000b55c <_strlen+0x10000b55c>
100003f98: aa1303e0    	mov	x0, x19
100003f9c: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100003fa0: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100003fa4: 14001d65    	b	0x10000b538 <_strlen+0x10000b538>

0000000100003fa8 <_allocPages__system_u6064>:
100003fa8: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100003fac: 910003fd    	mov	x29, sp
100003fb0: d2800000    	mov	x0, #0x0                ; =0
100003fb4: 52800062    	mov	w2, #0x3                ; =3
100003fb8: 52820043    	mov	w3, #0x1002             ; =4098
100003fbc: 12800004    	mov	w4, #-0x1               ; =-1
100003fc0: d2800005    	mov	x5, #0x0                ; =0
100003fc4: 94001d72    	bl	0x10000b58c <_strlen+0x10000b58c>
100003fc8: 91000408    	add	x8, x0, #0x1
100003fcc: f100051f    	cmp	x8, #0x1
100003fd0: 54000069    	b.ls	0x100003fdc <_allocPages__system_u6064+0x34>
100003fd4: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100003fd8: d65f03c0    	ret
100003fdc: 97ffffd9    	bl	0x100003f40 <_raiseOutOfMem__system_u5730>

0000000100003fe0 <_tryAllocPages__system_u6068>:
100003fe0: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100003fe4: 910003fd    	mov	x29, sp
100003fe8: d2800000    	mov	x0, #0x0                ; =0
100003fec: 52800062    	mov	w2, #0x3                ; =3
100003ff0: 52820043    	mov	w3, #0x1002             ; =4098
100003ff4: 12800004    	mov	w4, #-0x1               ; =-1
100003ff8: d2800005    	mov	x5, #0x0                ; =0
100003ffc: 94001d64    	bl	0x10000b58c <_strlen+0x10000b58c>
100004000: b100041f    	cmn	x0, #0x1
100004004: 9a8003e0    	csel	x0, xzr, x0, eq
100004008: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000400c: d65f03c0    	ret

0000000100004010 <_llAlloc__system_u6072>:
100004010: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100004014: a9014ff4    	stp	x20, x19, [sp, #0x10]
100004018: a9027bfd    	stp	x29, x30, [sp, #0x20]
10000401c: 910083fd    	add	x29, sp, #0x20
100004020: aa0103f3    	mov	x19, x1
100004024: aa0003f4    	mov	x20, x0
100004028: f9543415    	ldr	x21, [x0, #0x2868]
10000402c: b4000095    	cbz	x21, 0x10000403c <_llAlloc__system_u6072+0x2c>
100004030: f94002a8    	ldr	x8, [x21]
100004034: eb13011f    	cmp	x8, x19
100004038: 540002ea    	b.ge	0x100004094 <_llAlloc__system_u6072+0x84>
10000403c: d2800000    	mov	x0, #0x0                ; =0
100004040: 52820001    	mov	w1, #0x1000             ; =4096
100004044: 52800062    	mov	w2, #0x3                ; =3
100004048: 52820043    	mov	w3, #0x1002             ; =4098
10000404c: 12800004    	mov	w4, #-0x1               ; =-1
100004050: d2800005    	mov	x5, #0x0                ; =0
100004054: 94001d4e    	bl	0x10000b58c <_strlen+0x10000b58c>
100004058: 91000408    	add	x8, x0, #0x1
10000405c: f100051f    	cmp	x8, #0x1
100004060: 540002e9    	b.ls	0x1000040bc <_llAlloc__system_u6072+0xac>
100004064: f9143680    	str	x0, [x20, #0x2868]
100004068: f9543a88    	ldr	x8, [x20, #0x2870]
10000406c: 91400508    	add	x8, x8, #0x1, lsl #12   ; =0x1000
100004070: f9143a88    	str	x8, [x20, #0x2870]
100004074: f0000028    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100004078: 3dc1c500    	ldr	q0, [x8, #0x710]
10000407c: 3d800000    	str	q0, [x0]
100004080: f9000815    	str	x21, [x0, #0x10]
100004084: 52800309    	mov	w9, #0x18               ; =24
100004088: 5281fd08    	mov	w8, #0xfe8              ; =4072
10000408c: aa0003f5    	mov	x21, x0
100004090: 14000002    	b	0x100004098 <_llAlloc__system_u6072+0x88>
100004094: f94006a9    	ldr	x9, [x21, #0x8]
100004098: 8b150120    	add	x0, x9, x21
10000409c: cb130108    	sub	x8, x8, x19
1000040a0: 8b130129    	add	x9, x9, x19
1000040a4: a90026a8    	stp	x8, x9, [x21]
1000040a8: aa1303e1    	mov	x1, x19
1000040ac: a9427bfd    	ldp	x29, x30, [sp, #0x20]
1000040b0: a9414ff4    	ldp	x20, x19, [sp, #0x10]
1000040b4: a8c357f6    	ldp	x22, x21, [sp], #0x30
1000040b8: 14001d17    	b	0x10000b514 <_strlen+0x10000b514>
1000040bc: 97ffffa1    	bl	0x100003f40 <_raiseOutOfMem__system_u5730>

00000001000040c0 <_addHeapLink__system_u6110>:
1000040c0: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
1000040c4: a9014ff4    	stp	x20, x19, [sp, #0x10]
1000040c8: a9027bfd    	stp	x29, x30, [sp, #0x20]
1000040cc: 910083fd    	add	x29, sp, #0x20
1000040d0: aa0203f3    	mov	x19, x2
1000040d4: aa0103f4    	mov	x20, x1
1000040d8: aa0003f5    	mov	x21, x0
1000040dc: 52861608    	mov	w8, #0x30b0             ; =12464
1000040e0: 8b080000    	add	x0, x0, x8
1000040e4: f9400008    	ldr	x8, [x0]
1000040e8: f100791f    	cmp	x8, #0x1e
1000040ec: 540003cb    	b.lt	0x100004164 <_addHeapLink__system_u6110+0xa4>
1000040f0: f940f400    	ldr	x0, [x0, #0x1e8]
1000040f4: b5ffff80    	cbnz	x0, 0x1000040e4 <_addHeapLink__system_u6110+0x24>
1000040f8: f95436b6    	ldr	x22, [x21, #0x2868]
1000040fc: b4000096    	cbz	x22, 0x10000410c <_addHeapLink__system_u6110+0x4c>
100004100: f94002c8    	ldr	x8, [x22]
100004104: f107c108    	subs	x8, x8, #0x1f0
100004108: 540003ea    	b.ge	0x100004184 <_addHeapLink__system_u6110+0xc4>
10000410c: d2800000    	mov	x0, #0x0                ; =0
100004110: 52820001    	mov	w1, #0x1000             ; =4096
100004114: 52800062    	mov	w2, #0x3                ; =3
100004118: 52820043    	mov	w3, #0x1002             ; =4098
10000411c: 12800004    	mov	w4, #-0x1               ; =-1
100004120: d2800005    	mov	x5, #0x0                ; =0
100004124: 94001d1a    	bl	0x10000b58c <_strlen+0x10000b58c>
100004128: 91000408    	add	x8, x0, #0x1
10000412c: f100051f    	cmp	x8, #0x1
100004130: 54000689    	b.ls	0x100004200 <_addHeapLink__system_u6110+0x140>
100004134: f91436a0    	str	x0, [x21, #0x2868]
100004138: f9543aa8    	ldr	x8, [x21, #0x2870]
10000413c: 91400508    	add	x8, x8, #0x1, lsl #12   ; =0x1000
100004140: f9143aa8    	str	x8, [x21, #0x2870]
100004144: f0000028    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100004148: 3dc1c500    	ldr	q0, [x8, #0x710]
10000414c: 3d800000    	str	q0, [x0]
100004150: f9000816    	str	x22, [x0, #0x10]
100004154: 52800309    	mov	w9, #0x18               ; =24
100004158: 5281bf08    	mov	w8, #0xdf8              ; =3576
10000415c: aa0003f6    	mov	x22, x0
100004160: 1400000a    	b	0x100004188 <_addHeapLink__system_u6110+0xc8>
100004164: 8b081009    	add	x9, x0, x8, lsl #4
100004168: a900cd34    	stp	x20, x19, [x9, #0x8]
10000416c: 91000508    	add	x8, x8, #0x1
100004170: f9000008    	str	x8, [x0]
100004174: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100004178: a9414ff4    	ldp	x20, x19, [sp, #0x10]
10000417c: a8c357f6    	ldp	x22, x21, [sp], #0x30
100004180: d65f03c0    	ret
100004184: f94006c9    	ldr	x9, [x22, #0x8]
100004188: 8b160120    	add	x0, x9, x22
10000418c: 9107c129    	add	x9, x9, #0x1f0
100004190: a90026c8    	stp	x8, x9, [x22]
100004194: 6f00e400    	movi.2d	v0, #0000000000000000
100004198: ad0e8000    	stp	q0, q0, [x0, #0x1d0]
10000419c: ad0d8000    	stp	q0, q0, [x0, #0x1b0]
1000041a0: ad0c8000    	stp	q0, q0, [x0, #0x190]
1000041a4: ad0b8000    	stp	q0, q0, [x0, #0x170]
1000041a8: ad0a8000    	stp	q0, q0, [x0, #0x150]
1000041ac: ad098000    	stp	q0, q0, [x0, #0x130]
1000041b0: ad088000    	stp	q0, q0, [x0, #0x110]
1000041b4: ad078000    	stp	q0, q0, [x0, #0xf0]
1000041b8: ad068000    	stp	q0, q0, [x0, #0xd0]
1000041bc: ad058000    	stp	q0, q0, [x0, #0xb0]
1000041c0: ad048000    	stp	q0, q0, [x0, #0x90]
1000041c4: ad038000    	stp	q0, q0, [x0, #0x70]
1000041c8: ad028000    	stp	q0, q0, [x0, #0x50]
1000041cc: ad018000    	stp	q0, q0, [x0, #0x30]
1000041d0: ad008000    	stp	q0, q0, [x0, #0x10]
1000041d4: 3d800000    	str	q0, [x0]
1000041d8: f9594ea8    	ldr	x8, [x21, #0x3298]
1000041dc: f900f408    	str	x8, [x0, #0x1e8]
1000041e0: f9194ea0    	str	x0, [x21, #0x3298]
1000041e4: a900cc14    	stp	x20, x19, [x0, #0x8]
1000041e8: 52800028    	mov	w8, #0x1                ; =1
1000041ec: f9000008    	str	x8, [x0]
1000041f0: a9427bfd    	ldp	x29, x30, [sp, #0x20]
1000041f4: a9414ff4    	ldp	x20, x19, [sp, #0x10]
1000041f8: a8c357f6    	ldp	x22, x21, [sp], #0x30
1000041fc: d65f03c0    	ret
100004200: 97ffff50    	bl	0x100003f40 <_raiseOutOfMem__system_u5730>

0000000100004204 <_intSetGet__system_u6205>:
100004204: 8b210c00    	add	x0, x0, w1, uxtb #3
100004208: f9400000    	ldr	x0, [x0]
10000420c: b4000080    	cbz	x0, 0x10000421c <_intSetGet__system_u6205+0x18>
100004210: f9400408    	ldr	x8, [x0, #0x8]
100004214: eb01011f    	cmp	x8, x1
100004218: 54ffff81    	b.ne	0x100004208 <_intSetGet__system_u6205+0x4>
10000421c: d65f03c0    	ret

0000000100004220 <_contains__system_u6254>:
100004220: 9349fc28    	asr	x8, x1, #9
100004224: aa0803e9    	mov	x9, x8
100004228: d37d1d09    	ubfiz	x9, x8, #3, #8
10000422c: 8b090009    	add	x9, x0, x9
100004230: f9400129    	ldr	x9, [x9]
100004234: b4000149    	cbz	x9, 0x10000425c <_contains__system_u6254+0x3c>
100004238: f940052a    	ldr	x10, [x9, #0x8]
10000423c: eb08015f    	cmp	x10, x8
100004240: 54ffff81    	b.ne	0x100004230 <_contains__system_u6254+0x10>
100004244: d3462028    	ubfx	x8, x1, #6, #3
100004248: 8b080d28    	add	x8, x9, x8, lsl #3
10000424c: f9400908    	ldr	x8, [x8, #0x10]
100004250: 9ac12508    	lsr	x8, x8, x1
100004254: 12000100    	and	w0, w8, #0x1
100004258: d65f03c0    	ret
10000425c: 52800000    	mov	w0, #0x0                ; =0
100004260: d65f03c0    	ret

0000000100004264 <_requestOsChunks__system_u6507>:
100004264: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100004268: a9014ff4    	stp	x20, x19, [sp, #0x10]
10000426c: a9027bfd    	stp	x29, x30, [sp, #0x20]
100004270: 910083fd    	add	x29, sp, #0x20
100004274: aa0103f4    	mov	x20, x1
100004278: aa0003f3    	mov	x19, x0
10000427c: 52861448    	mov	w8, #0x30a2             ; =12450
100004280: 8b080016    	add	x22, x0, x8
100004284: 394002c8    	ldrb	w8, [x22]
100004288: 34000208    	cbz	w8, 0x1000042c8 <_requestOsChunks__system_u6507+0x64>
10000428c: f9585661    	ldr	x1, [x19, #0x30a8]
100004290: eb14003f    	cmp	x1, x20
100004294: 5400044a    	b.ge	0x10000431c <_requestOsChunks__system_u6507+0xb8>
100004298: d2800000    	mov	x0, #0x0                ; =0
10000429c: aa1403e1    	mov	x1, x20
1000042a0: 52800062    	mov	w2, #0x3                ; =3
1000042a4: 52820043    	mov	w3, #0x1002             ; =4098
1000042a8: 12800004    	mov	w4, #-0x1               ; =-1
1000042ac: d2800005    	mov	x5, #0x0                ; =0
1000042b0: 94001cb7    	bl	0x10000b58c <_strlen+0x10000b58c>
1000042b4: 91000408    	add	x8, x0, #0x1
1000042b8: f100051f    	cmp	x8, #0x1
1000042bc: 54000f29    	b.ls	0x1000044a0 <_requestOsChunks__system_u6507+0x23c>
1000042c0: aa0003f5    	mov	x21, x0
1000042c4: 1400002f    	b	0x100004380 <_requestOsChunks__system_u6507+0x11c>
1000042c8: f9544668    	ldr	x8, [x19, #0x2888]
1000042cc: f140411f    	cmp	x8, #0x10, lsl #12      ; =0x10000
1000042d0: 540000ca    	b.ge	0x1000042e8 <_requestOsChunks__system_u6507+0x84>
1000042d4: 52880001    	mov	w1, #0x4000             ; =16384
1000042d8: f9185661    	str	x1, [x19, #0x30a8]
1000042dc: eb14003f    	cmp	x1, x20
1000042e0: 54fffdcb    	b.lt	0x100004298 <_requestOsChunks__system_u6507+0x34>
1000042e4: 1400000e    	b	0x10000431c <_requestOsChunks__system_u6507+0xb8>
1000042e8: d342fd08    	lsr	x8, x8, #2
1000042ec: 913ffd08    	add	x8, x8, #0xfff
1000042f0: 9274c908    	and	x8, x8, #0x7ffffffffffff000
1000042f4: f9585669    	ldr	x9, [x19, #0x30a8]
1000042f8: d37ff929    	lsl	x9, x9, #1
1000042fc: eb09011f    	cmp	x8, x9
100004300: 9a89b108    	csel	x8, x8, x9, lt
100004304: 52a7e009    	mov	w9, #0x3f000000         ; =1056964608
100004308: eb09011f    	cmp	x8, x9
10000430c: 9a89b101    	csel	x1, x8, x9, lt
100004310: f9185661    	str	x1, [x19, #0x30a8]
100004314: eb14003f    	cmp	x1, x20
100004318: 54fffc0b    	b.lt	0x100004298 <_requestOsChunks__system_u6507+0x34>
10000431c: d2800000    	mov	x0, #0x0                ; =0
100004320: 52800062    	mov	w2, #0x3                ; =3
100004324: 52820043    	mov	w3, #0x1002             ; =4098
100004328: 12800004    	mov	w4, #-0x1               ; =-1
10000432c: d2800005    	mov	x5, #0x0                ; =0
100004330: 94001c97    	bl	0x10000b58c <_strlen+0x10000b58c>
100004334: 91000408    	add	x8, x0, #0x1
100004338: f100051f    	cmp	x8, #0x1
10000433c: 540001e8    	b.hi	0x100004378 <_requestOsChunks__system_u6507+0x114>
100004340: d2800000    	mov	x0, #0x0                ; =0
100004344: aa1403e1    	mov	x1, x20
100004348: 52800062    	mov	w2, #0x3                ; =3
10000434c: 52820043    	mov	w3, #0x1002             ; =4098
100004350: 12800004    	mov	w4, #-0x1               ; =-1
100004354: d2800005    	mov	x5, #0x0                ; =0
100004358: 94001c8d    	bl	0x10000b58c <_strlen+0x10000b58c>
10000435c: 91000408    	add	x8, x0, #0x1
100004360: f100051f    	cmp	x8, #0x1
100004364: 540009e9    	b.ls	0x1000044a0 <_requestOsChunks__system_u6507+0x23c>
100004368: aa0003f5    	mov	x21, x0
10000436c: 52800028    	mov	w8, #0x1                ; =1
100004370: 390002c8    	strb	w8, [x22]
100004374: 14000003    	b	0x100004380 <_requestOsChunks__system_u6507+0x11c>
100004378: aa0003f5    	mov	x21, x0
10000437c: f9585674    	ldr	x20, [x19, #0x30a8]
100004380: f9543a68    	ldr	x8, [x19, #0x2870]
100004384: 8b140108    	add	x8, x8, x20
100004388: f9143a68    	str	x8, [x19, #0x2870]
10000438c: f9544268    	ldr	x8, [x19, #0x2880]
100004390: 8b140108    	add	x8, x8, x20
100004394: f9144268    	str	x8, [x19, #0x2880]
100004398: aa1303e0    	mov	x0, x19
10000439c: aa1503e1    	mov	x1, x21
1000043a0: aa1403e2    	mov	x2, x20
1000043a4: 97ffff47    	bl	0x1000040c0 <_addHeapLink__system_u6110>
1000043a8: a901febf    	stp	xzr, xzr, [x21, #0x18]
1000043ac: f90006b4    	str	x20, [x21, #0x8]
1000043b0: 8b150289    	add	x9, x20, x21
1000043b4: 934cfd2a    	asr	x10, x9, #12
1000043b8: 52851408    	mov	w8, #0x28a0             ; =10400
1000043bc: 9355fd2b    	asr	x11, x9, #21
1000043c0: aa0b03ec    	mov	x12, x11
1000043c4: d37d1d6c    	ubfiz	x12, x11, #3, #8
1000043c8: 8b080268    	add	x8, x19, x8
1000043cc: 8b0c010c    	add	x12, x8, x12
1000043d0: f940018c    	ldr	x12, [x12]
1000043d4: b40001cc    	cbz	x12, 0x10000440c <_requestOsChunks__system_u6507+0x1a8>
1000043d8: f940058d    	ldr	x13, [x12, #0x8]
1000043dc: eb0b01bf    	cmp	x13, x11
1000043e0: 54ffff81    	b.ne	0x1000043d0 <_requestOsChunks__system_u6507+0x16c>
1000043e4: d34cfd2b    	lsr	x11, x9, #12
1000043e8: d346214a    	ubfx	x10, x10, #6, #3
1000043ec: 8b0a0d8a    	add	x10, x12, x10, lsl #3
1000043f0: f940094a    	ldr	x10, [x10, #0x10]
1000043f4: 9acb254a    	lsr	x10, x10, x11
1000043f8: 360000aa    	tbz	w10, #0x0, 0x10000440c <_requestOsChunks__system_u6507+0x1a8>
1000043fc: f940012a    	ldr	x10, [x9]
100004400: 9240014a    	and	x10, x10, #0x1
100004404: aa14014a    	orr	x10, x10, x20
100004408: f900012a    	str	x10, [x9]
10000440c: f9544a69    	ldr	x9, [x19, #0x2890]
100004410: 5282000a    	mov	w10, #0x1000            ; =4096
100004414: f100013f    	cmp	x9, #0x0
100004418: 9a890149    	csel	x9, x10, x9, eq
10000441c: cb0902aa    	sub	x10, x21, x9
100004420: 934cfd4b    	asr	x11, x10, #12
100004424: 9355fd4c    	asr	x12, x10, #21
100004428: aa0c03ed    	mov	x13, x12
10000442c: d37d1d8d    	ubfiz	x13, x12, #3, #8
100004430: 8b0d0108    	add	x8, x8, x13
100004434: f9400108    	ldr	x8, [x8]
100004438: b4000228    	cbz	x8, 0x10000447c <_requestOsChunks__system_u6507+0x218>
10000443c: f940050d    	ldr	x13, [x8, #0x8]
100004440: eb0c01bf    	cmp	x13, x12
100004444: 54ffff81    	b.ne	0x100004434 <_requestOsChunks__system_u6507+0x1d0>
100004448: d34cfd4c    	lsr	x12, x10, #12
10000444c: d346216b    	ubfx	x11, x11, #6, #3
100004450: 8b0b0d08    	add	x8, x8, x11, lsl #3
100004454: f9400908    	ldr	x8, [x8, #0x10]
100004458: 9acc2508    	lsr	x8, x8, x12
10000445c: 36000108    	tbz	w8, #0x0, 0x10000447c <_requestOsChunks__system_u6507+0x218>
100004460: f9400548    	ldr	x8, [x10, #0x8]
100004464: eb09011f    	cmp	x8, x9
100004468: 540000a1    	b.ne	0x10000447c <_requestOsChunks__system_u6507+0x218>
10000446c: f94002a8    	ldr	x8, [x21]
100004470: 92400108    	and	x8, x8, #0x1
100004474: aa090108    	orr	x8, x8, x9
100004478: 14000003    	b	0x100004484 <_requestOsChunks__system_u6507+0x220>
10000447c: f94002a8    	ldr	x8, [x21]
100004480: 92400108    	and	x8, x8, #0x1
100004484: f90002a8    	str	x8, [x21]
100004488: f9144a74    	str	x20, [x19, #0x2890]
10000448c: aa1503e0    	mov	x0, x21
100004490: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100004494: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100004498: a8c357f6    	ldp	x22, x21, [sp], #0x30
10000449c: d65f03c0    	ret
1000044a0: 97fffea8    	bl	0x100003f40 <_raiseOutOfMem__system_u5730>

00000001000044a4 <_intSetPut__system_u6237>:
1000044a4: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
1000044a8: a9014ff4    	stp	x20, x19, [sp, #0x10]
1000044ac: a9027bfd    	stp	x29, x30, [sp, #0x20]
1000044b0: 910083fd    	add	x29, sp, #0x20
1000044b4: aa0203f3    	mov	x19, x2
1000044b8: aa0003f4    	mov	x20, x0
1000044bc: 8b330c35    	add	x21, x1, w19, uxtb #3
1000044c0: aa1503e0    	mov	x0, x21
1000044c4: f9400000    	ldr	x0, [x0]
1000044c8: b4000100    	cbz	x0, 0x1000044e8 <_intSetPut__system_u6237+0x44>
1000044cc: f9400408    	ldr	x8, [x0, #0x8]
1000044d0: eb13011f    	cmp	x8, x19
1000044d4: 54ffff81    	b.ne	0x1000044c4 <_intSetPut__system_u6237+0x20>
1000044d8: a9427bfd    	ldp	x29, x30, [sp, #0x20]
1000044dc: a9414ff4    	ldp	x20, x19, [sp, #0x10]
1000044e0: a8c357f6    	ldp	x22, x21, [sp], #0x30
1000044e4: d65f03c0    	ret
1000044e8: f9543696    	ldr	x22, [x20, #0x2868]
1000044ec: b4000096    	cbz	x22, 0x1000044fc <_intSetPut__system_u6237+0x58>
1000044f0: f94002c8    	ldr	x8, [x22]
1000044f4: f1014108    	subs	x8, x8, #0x50
1000044f8: 540002ea    	b.ge	0x100004554 <_intSetPut__system_u6237+0xb0>
1000044fc: d2800000    	mov	x0, #0x0                ; =0
100004500: 52820001    	mov	w1, #0x1000             ; =4096
100004504: 52800062    	mov	w2, #0x3                ; =3
100004508: 52820043    	mov	w3, #0x1002             ; =4098
10000450c: 12800004    	mov	w4, #-0x1               ; =-1
100004510: d2800005    	mov	x5, #0x0                ; =0
100004514: 94001c1e    	bl	0x10000b58c <_strlen+0x10000b58c>
100004518: 91000408    	add	x8, x0, #0x1
10000451c: f100051f    	cmp	x8, #0x1
100004520: 540003a9    	b.ls	0x100004594 <_intSetPut__system_u6237+0xf0>
100004524: f9143680    	str	x0, [x20, #0x2868]
100004528: f9543a88    	ldr	x8, [x20, #0x2870]
10000452c: 91400508    	add	x8, x8, #0x1, lsl #12   ; =0x1000
100004530: f9143a88    	str	x8, [x20, #0x2870]
100004534: f0000028    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100004538: 3dc1c500    	ldr	q0, [x8, #0x710]
10000453c: 3d800000    	str	q0, [x0]
100004540: f9000816    	str	x22, [x0, #0x10]
100004544: 52800309    	mov	w9, #0x18               ; =24
100004548: 5281f308    	mov	w8, #0xf98              ; =3992
10000454c: aa0003f6    	mov	x22, x0
100004550: 14000002    	b	0x100004558 <_intSetPut__system_u6237+0xb4>
100004554: f94006c9    	ldr	x9, [x22, #0x8]
100004558: 8b160120    	add	x0, x9, x22
10000455c: 91014129    	add	x9, x9, #0x50
100004560: a90026c8    	stp	x8, x9, [x22]
100004564: 6f00e400    	movi.2d	v0, #0000000000000000
100004568: ad018000    	stp	q0, q0, [x0, #0x30]
10000456c: ad008000    	stp	q0, q0, [x0, #0x10]
100004570: 3d800000    	str	q0, [x0]
100004574: f94002a8    	ldr	x8, [x21]
100004578: f9000008    	str	x8, [x0]
10000457c: f90002a0    	str	x0, [x21]
100004580: f9000413    	str	x19, [x0, #0x8]
100004584: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100004588: a9414ff4    	ldp	x20, x19, [sp, #0x10]
10000458c: a8c357f6    	ldp	x22, x21, [sp], #0x30
100004590: d65f03c0    	ret
100004594: 97fffe6b    	bl	0x100003f40 <_raiseOutOfMem__system_u5730>

0000000100004598 <_incl__system_u6295>:
100004598: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
10000459c: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000045a0: 910043fd    	add	x29, sp, #0x10
1000045a4: aa0203f3    	mov	x19, x2
1000045a8: 9349fc42    	asr	x2, x2, #9
1000045ac: 97ffffbe    	bl	0x1000044a4 <_intSetPut__system_u6237>
1000045b0: d3462268    	ubfx	x8, x19, #6, #3
1000045b4: 8b080c08    	add	x8, x0, x8, lsl #3
1000045b8: f9400909    	ldr	x9, [x8, #0x10]
1000045bc: 5280002a    	mov	w10, #0x1               ; =1
1000045c0: 9ad3214a    	lsl	x10, x10, x19
1000045c4: aa0a0129    	orr	x9, x9, x10
1000045c8: f9000909    	str	x9, [x8, #0x10]
1000045cc: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000045d0: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000045d4: d65f03c0    	ret

00000001000045d8 <_splitChunk2__system_u6555>:
1000045d8: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
1000045dc: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000045e0: 910043fd    	add	x29, sp, #0x10
1000045e4: 8b020033    	add	x19, x1, x2
1000045e8: f9400428    	ldr	x8, [x1, #0x8]
1000045ec: cb020109    	sub	x9, x8, x2
1000045f0: a901fe7f    	stp	xzr, xzr, [x19, #0x18]
1000045f4: a9002662    	stp	x2, x9, [x19]
1000045f8: f9000a60    	str	x0, [x19, #0x10]
1000045fc: f9400428    	ldr	x8, [x1, #0x8]
100004600: 8b01010a    	add	x10, x8, x1
100004604: 934cfd4b    	asr	x11, x10, #12
100004608: 52851408    	mov	w8, #0x28a0             ; =10400
10000460c: 9355fd4c    	asr	x12, x10, #21
100004610: aa0c03ed    	mov	x13, x12
100004614: d37d1d8d    	ubfiz	x13, x12, #3, #8
100004618: 8b080008    	add	x8, x0, x8
10000461c: 8b0d010d    	add	x13, x8, x13
100004620: f94001ad    	ldr	x13, [x13]
100004624: b40001cd    	cbz	x13, 0x10000465c <_splitChunk2__system_u6555+0x84>
100004628: f94005ae    	ldr	x14, [x13, #0x8]
10000462c: eb0c01df    	cmp	x14, x12
100004630: 54ffff81    	b.ne	0x100004620 <_splitChunk2__system_u6555+0x48>
100004634: d34cfd4c    	lsr	x12, x10, #12
100004638: d346216b    	ubfx	x11, x11, #6, #3
10000463c: 8b0b0dab    	add	x11, x13, x11, lsl #3
100004640: f940096b    	ldr	x11, [x11, #0x10]
100004644: 9acc256b    	lsr	x11, x11, x12
100004648: 360000ab    	tbz	w11, #0x0, 0x10000465c <_splitChunk2__system_u6555+0x84>
10000464c: f940014b    	ldr	x11, [x10]
100004650: 9240016b    	and	x11, x11, #0x1
100004654: aa090169    	orr	x9, x11, x9
100004658: f9000149    	str	x9, [x10]
10000465c: f9000422    	str	x2, [x1, #0x8]
100004660: 934cfe74    	asr	x20, x19, #12
100004664: 9355fe62    	asr	x2, x19, #21
100004668: aa0803e1    	mov	x1, x8
10000466c: 97ffff8e    	bl	0x1000044a4 <_intSetPut__system_u6237>
100004670: d3462288    	ubfx	x8, x20, #6, #3
100004674: 8b080c08    	add	x8, x0, x8, lsl #3
100004678: f9400909    	ldr	x9, [x8, #0x10]
10000467c: 5280002a    	mov	w10, #0x1               ; =1
100004680: 9ad4214a    	lsl	x10, x10, x20
100004684: aa0a0129    	orr	x9, x9, x10
100004688: f9000909    	str	x9, [x8, #0x10]
10000468c: aa1303e0    	mov	x0, x19
100004690: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100004694: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100004698: d65f03c0    	ret

000000010000469c <_addChunkToMatrix__system_u6034>:
10000469c: f9400428    	ldr	x8, [x1, #0x8]
1000046a0: 7103fd1f    	cmp	w8, #0xff
1000046a4: 1a9f97e9    	cset	w9, hi
1000046a8: d37d7d29    	ubfiz	x9, x9, #3, #32
1000046ac: d3587d0a    	ubfx	x10, x8, #24, #8
1000046b0: 7100015f    	cmp	w10, #0x0
1000046b4: 5280030a    	mov	w10, #0x18              ; =24
1000046b8: 5280020b    	mov	w11, #0x10              ; =16
1000046bc: 9a8a016a    	csel	x10, x11, x10, eq
1000046c0: 7140411f    	cmp	w8, #0x10, lsl #12      ; =0x10000
1000046c4: 9a8a3129    	csel	x9, x9, x10, lo
1000046c8: 92407d0a    	and	x10, x8, #0xffffffff
1000046cc: 9ac9254a    	lsr	x10, x10, x9
1000046d0: f000002b    	adrp	x11, 0x10000b000 <_bench__add95carry_u844+0x104>
1000046d4: 911cc16b    	add	x11, x11, #0x730
1000046d8: 38aa696a    	ldrsb	x10, [x11, x10]
1000046dc: 8b0a012a    	add	x10, x9, x10
1000046e0: d1001549    	sub	x9, x10, #0x5
1000046e4: 9ac92909    	asr	x9, x8, x9
1000046e8: d1001948    	sub	x8, x10, #0x6
1000046ec: f900103f    	str	xzr, [x1, #0x20]
1000046f0: 8b08200a    	add	x10, x0, x8, lsl #8
1000046f4: 8b090d4b    	add	x11, x10, x9, lsl #3
1000046f8: 913da16a    	add	x10, x11, #0xf68
1000046fc: f947b56c    	ldr	x12, [x11, #0xf68]
100004700: f9000c2c    	str	x12, [x1, #0x18]
100004704: f947b56b    	ldr	x11, [x11, #0xf68]
100004708: b400004b    	cbz	x11, 0x100004710 <_addChunkToMatrix__system_u6034+0x74>
10000470c: f9001161    	str	x1, [x11, #0x20]
100004710: f9000141    	str	x1, [x10]
100004714: 8b08080a    	add	x10, x0, x8, lsl #2
100004718: b950054b    	ldr	w11, [x10, #0x1004]
10000471c: 5280002c    	mov	w12, #0x1               ; =1
100004720: 1ac92189    	lsl	w9, w12, w9
100004724: 2a090169    	orr	w9, w11, w9
100004728: b9100549    	str	w9, [x10, #0x1004]
10000472c: b9500009    	ldr	w9, [x0, #0x1000]
100004730: 1ac82188    	lsl	w8, w12, w8
100004734: 2a080128    	orr	w8, w9, w8
100004738: b9100008    	str	w8, [x0, #0x1000]
10000473c: d65f03c0    	ret

0000000100004740 <_splitChunk__system_u6579>:
100004740: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100004744: a9014ff4    	stp	x20, x19, [sp, #0x10]
100004748: a9027bfd    	stp	x29, x30, [sp, #0x20]
10000474c: 910083fd    	add	x29, sp, #0x20
100004750: aa0003f3    	mov	x19, x0
100004754: 8b020034    	add	x20, x1, x2
100004758: f9400428    	ldr	x8, [x1, #0x8]
10000475c: cb020109    	sub	x9, x8, x2
100004760: a901fe9f    	stp	xzr, xzr, [x20, #0x18]
100004764: a9002682    	stp	x2, x9, [x20]
100004768: f9000a80    	str	x0, [x20, #0x10]
10000476c: f9400428    	ldr	x8, [x1, #0x8]
100004770: 8b01010a    	add	x10, x8, x1
100004774: 934cfd4b    	asr	x11, x10, #12
100004778: 52851408    	mov	w8, #0x28a0             ; =10400
10000477c: 9355fd4c    	asr	x12, x10, #21
100004780: aa0c03ed    	mov	x13, x12
100004784: d37d1d8d    	ubfiz	x13, x12, #3, #8
100004788: 8b080008    	add	x8, x0, x8
10000478c: 8b0d010d    	add	x13, x8, x13
100004790: f94001ad    	ldr	x13, [x13]
100004794: b40001cd    	cbz	x13, 0x1000047cc <_splitChunk__system_u6579+0x8c>
100004798: f94005ae    	ldr	x14, [x13, #0x8]
10000479c: eb0c01df    	cmp	x14, x12
1000047a0: 54ffff81    	b.ne	0x100004790 <_splitChunk__system_u6579+0x50>
1000047a4: d34cfd4c    	lsr	x12, x10, #12
1000047a8: d346216b    	ubfx	x11, x11, #6, #3
1000047ac: 8b0b0dab    	add	x11, x13, x11, lsl #3
1000047b0: f940096b    	ldr	x11, [x11, #0x10]
1000047b4: 9acc256b    	lsr	x11, x11, x12
1000047b8: 360000ab    	tbz	w11, #0x0, 0x1000047cc <_splitChunk__system_u6579+0x8c>
1000047bc: f940014b    	ldr	x11, [x10]
1000047c0: 9240016b    	and	x11, x11, #0x1
1000047c4: aa090169    	orr	x9, x11, x9
1000047c8: f9000149    	str	x9, [x10]
1000047cc: f9000422    	str	x2, [x1, #0x8]
1000047d0: 934cfe95    	asr	x21, x20, #12
1000047d4: 9355fe82    	asr	x2, x20, #21
1000047d8: aa1303e0    	mov	x0, x19
1000047dc: aa0803e1    	mov	x1, x8
1000047e0: 97ffff31    	bl	0x1000044a4 <_intSetPut__system_u6237>
1000047e4: d34622a8    	ubfx	x8, x21, #6, #3
1000047e8: 8b080c09    	add	x9, x0, x8, lsl #3
1000047ec: f940092a    	ldr	x10, [x9, #0x10]
1000047f0: 52800028    	mov	w8, #0x1                ; =1
1000047f4: 9ad5210b    	lsl	x11, x8, x21
1000047f8: aa0b014a    	orr	x10, x10, x11
1000047fc: f900092a    	str	x10, [x9, #0x10]
100004800: f9400689    	ldr	x9, [x20, #0x8]
100004804: 7103fd3f    	cmp	w9, #0xff
100004808: 1a9f97ea    	cset	w10, hi
10000480c: d37d7d4a    	ubfiz	x10, x10, #3, #32
100004810: d3587d2b    	ubfx	x11, x9, #24, #8
100004814: 7100017f    	cmp	w11, #0x0
100004818: 5280030b    	mov	w11, #0x18              ; =24
10000481c: 5280020c    	mov	w12, #0x10              ; =16
100004820: 9a8b018b    	csel	x11, x12, x11, eq
100004824: 7140413f    	cmp	w9, #0x10, lsl #12      ; =0x10000
100004828: 9a8b314a    	csel	x10, x10, x11, lo
10000482c: 92407d2b    	and	x11, x9, #0xffffffff
100004830: 9aca256b    	lsr	x11, x11, x10
100004834: f000002c    	adrp	x12, 0x10000b000 <_bench__add95carry_u844+0x104>
100004838: 911cc18c    	add	x12, x12, #0x730
10000483c: 38ab698b    	ldrsb	x11, [x12, x11]
100004840: 8b0b014b    	add	x11, x10, x11
100004844: d100156a    	sub	x10, x11, #0x5
100004848: 9aca292a    	asr	x10, x9, x10
10000484c: d1001969    	sub	x9, x11, #0x6
100004850: f900129f    	str	xzr, [x20, #0x20]
100004854: 8b09226b    	add	x11, x19, x9, lsl #8
100004858: 8b0a0d6c    	add	x12, x11, x10, lsl #3
10000485c: 913da18b    	add	x11, x12, #0xf68
100004860: f947b58d    	ldr	x13, [x12, #0xf68]
100004864: f9000e8d    	str	x13, [x20, #0x18]
100004868: f947b58c    	ldr	x12, [x12, #0xf68]
10000486c: b400004c    	cbz	x12, 0x100004874 <_splitChunk__system_u6579+0x134>
100004870: f9001194    	str	x20, [x12, #0x20]
100004874: f9000174    	str	x20, [x11]
100004878: 8b090a6b    	add	x11, x19, x9, lsl #2
10000487c: b950056c    	ldr	w12, [x11, #0x1004]
100004880: 1aca210a    	lsl	w10, w8, w10
100004884: 2a0a018a    	orr	w10, w12, w10
100004888: b910056a    	str	w10, [x11, #0x1004]
10000488c: b950026a    	ldr	w10, [x19, #0x1000]
100004890: 1ac92108    	lsl	w8, w8, w9
100004894: 2a080148    	orr	w8, w10, w8
100004898: b9100268    	str	w8, [x19, #0x1000]
10000489c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
1000048a0: a9414ff4    	ldp	x20, x19, [sp, #0x10]
1000048a4: a8c357f6    	ldp	x22, x21, [sp], #0x30
1000048a8: d65f03c0    	ret

00000001000048ac <_removeChunkFromMatrix2__system_u6025>:
1000048ac: f8418c28    	ldr	x8, [x1, #0x18]!
1000048b0: 8b022009    	add	x9, x0, x2, lsl #8
1000048b4: 8b030d29    	add	x9, x9, x3, lsl #3
1000048b8: f9083528    	str	x8, [x9, #0x1068]
1000048bc: b4000088    	cbz	x8, 0x1000048cc <_removeChunkFromMatrix2__system_u6025+0x20>
1000048c0: f900111f    	str	xzr, [x8, #0x20]
1000048c4: a9007c3f    	stp	xzr, xzr, [x1]
1000048c8: d65f03c0    	ret
1000048cc: 8b020809    	add	x9, x0, x2, lsl #2
1000048d0: b950052a    	ldr	w10, [x9, #0x1004]
1000048d4: 52800028    	mov	w8, #0x1                ; =1
1000048d8: 1ac3210b    	lsl	w11, w8, w3
1000048dc: 6a2b014a    	bics	w10, w10, w11
1000048e0: b910052a    	str	w10, [x9, #0x1004]
1000048e4: 54ffff01    	b.ne	0x1000048c4 <_removeChunkFromMatrix2__system_u6025+0x18>
1000048e8: b9500009    	ldr	w9, [x0, #0x1000]
1000048ec: 1ac22108    	lsl	w8, w8, w2
1000048f0: 0a280128    	bic	w8, w9, w8
1000048f4: b9100008    	str	w8, [x0, #0x1000]
1000048f8: a9007c3f    	stp	xzr, xzr, [x1]
1000048fc: d65f03c0    	ret

0000000100004900 <_getBigChunk__system_u6608>:
100004900: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
100004904: a90157f6    	stp	x22, x21, [sp, #0x10]
100004908: a9024ff4    	stp	x20, x19, [sp, #0x20]
10000490c: a9037bfd    	stp	x29, x30, [sp, #0x30]
100004910: 9100c3fd    	add	x29, sp, #0x30
100004914: aa0003f3    	mov	x19, x0
100004918: 7103fc3f    	cmp	w1, #0xff
10000491c: 1a9f97e8    	cset	w8, hi
100004920: d37d7d08    	ubfiz	x8, x8, #3, #32
100004924: d3587c29    	ubfx	x9, x1, #24, #8
100004928: 7100013f    	cmp	w9, #0x0
10000492c: 52800309    	mov	w9, #0x18               ; =24
100004930: 5280020a    	mov	w10, #0x10              ; =16
100004934: 9a89014b    	csel	x11, x10, x9, eq
100004938: 7140403f    	cmp	w1, #0x10, lsl #12      ; =0x10000
10000493c: 9a8b310b    	csel	x11, x8, x11, lo
100004940: 92407c28    	and	x8, x1, #0xffffffff
100004944: 9acb250c    	lsr	x12, x8, x11
100004948: f0000028    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
10000494c: 911cc108    	add	x8, x8, #0x730
100004950: 38ac690c    	ldrsb	x12, [x8, x12]
100004954: 8b0c016b    	add	x11, x11, x12
100004958: d100156b    	sub	x11, x11, #0x5
10000495c: 5280002c    	mov	w12, #0x1               ; =1
100004960: 9acb218b    	lsl	x11, x12, x11
100004964: 913ffd6b    	add	x11, x11, #0xfff
100004968: 9274cd6b    	and	x11, x11, #0xfffffffffffff000
10000496c: 8b0b002c    	add	x12, x1, x11
100004970: d100058c    	sub	x12, x12, #0x1
100004974: cb0b03eb    	neg	x11, x11
100004978: 8a0b018b    	and	x11, x12, x11
10000497c: 52a7e00c    	mov	w12, #0x3f000000        ; =1056964608
100004980: eb0c017f    	cmp	x11, x12
100004984: 9a8cb174    	csel	x20, x11, x12, lt
100004988: 7100029f    	cmp	w20, #0x0
10000498c: 1a9f07eb    	cset	w11, ne
100004990: d37d7d6b    	ubfiz	x11, x11, #3, #32
100004994: d3587e8c    	ubfx	x12, x20, #24, #8
100004998: 7100019f    	cmp	w12, #0x0
10000499c: 9a890149    	csel	x9, x10, x9, eq
1000049a0: 7140429f    	cmp	w20, #0x10, lsl #12     ; =0x10000
1000049a4: 9a893169    	csel	x9, x11, x9, lo
1000049a8: 92744e8a    	and	x10, x20, #0xfffff000
1000049ac: 9ac9254a    	lsr	x10, x10, x9
1000049b0: 38aa690a    	ldrsb	x10, [x8, x10]
1000049b4: 8b0a0129    	add	x9, x9, x10
1000049b8: d100152c    	sub	x12, x9, #0x5
1000049bc: 9acc2a8a    	asr	x10, x20, x12
1000049c0: d100814b    	sub	x11, x10, #0x20
1000049c4: d1001929    	sub	x9, x9, #0x6
1000049c8: 8b09080a    	add	x10, x0, x9, lsl #2
1000049cc: b950054a    	ldr	w10, [x10, #0x1004]
1000049d0: 1280000d    	mov	w13, #-0x1              ; =-1
1000049d4: 9acb21ab    	lsl	x11, x13, x11
1000049d8: 6a0b014b    	ands	w11, w10, w11
1000049dc: 54000321    	b.ne	0x100004a40 <_getBigChunk__system_u6608+0x140>
1000049e0: b9500269    	ldr	w9, [x19, #0x1000]
1000049e4: 1280000a    	mov	w10, #-0x1              ; =-1
1000049e8: 9acc214a    	lsl	x10, x10, x12
1000049ec: 0a0a0129    	and	w9, w9, w10
1000049f0: 4b0903ea    	neg	w10, w9
1000049f4: 0a0a0129    	and	w9, w9, w10
1000049f8: 7103fd3f    	cmp	w9, #0xff
1000049fc: 1a9f97ea    	cset	w10, hi
100004a00: d37d7d4a    	ubfiz	x10, x10, #3, #32
100004a04: 53187d2b    	lsr	w11, w9, #24
100004a08: 7100017f    	cmp	w11, #0x0
100004a0c: 5280030b    	mov	w11, #0x18              ; =24
100004a10: 5280020c    	mov	w12, #0x10              ; =16
100004a14: 9a8b018b    	csel	x11, x12, x11, eq
100004a18: 7140413f    	cmp	w9, #0x10, lsl #12      ; =0x10000
100004a1c: 9a8b314a    	csel	x10, x10, x11, lo
100004a20: 9aca2529    	lsr	x9, x9, x10
100004a24: 38a96909    	ldrsb	x9, [x8, x9]
100004a28: 8b090149    	add	x9, x10, x9
100004a2c: f100053f    	cmp	x9, #0x1
100004a30: 540003eb    	b.lt	0x100004aac <_getBigChunk__system_u6608+0x1ac>
100004a34: 8b090a6a    	add	x10, x19, x9, lsl #2
100004a38: b950054a    	ldr	w10, [x10, #0x1004]
100004a3c: aa0a03eb    	mov	x11, x10
100004a40: 4b0b03ec    	neg	w12, w11
100004a44: 0a0c016b    	and	w11, w11, w12
100004a48: 7103fd7f    	cmp	w11, #0xff
100004a4c: 1a9f97ec    	cset	w12, hi
100004a50: d37d7d8c    	ubfiz	x12, x12, #3, #32
100004a54: 53187d6d    	lsr	w13, w11, #24
100004a58: 710001bf    	cmp	w13, #0x0
100004a5c: 5280030d    	mov	w13, #0x18              ; =24
100004a60: 5280020e    	mov	w14, #0x10              ; =16
100004a64: 9a8d01cd    	csel	x13, x14, x13, eq
100004a68: 7140417f    	cmp	w11, #0x10, lsl #12     ; =0x10000
100004a6c: 9a8d318c    	csel	x12, x12, x13, lo
100004a70: 9acc256b    	lsr	x11, x11, x12
100004a74: 38ab6908    	ldrsb	x8, [x8, x11]
100004a78: 8b08018b    	add	x11, x12, x8
100004a7c: 8b092268    	add	x8, x19, x9, lsl #8
100004a80: 8b0b0d08    	add	x8, x8, x11, lsl #3
100004a84: f9483515    	ldr	x21, [x8, #0x1068]
100004a88: b4000135    	cbz	x21, 0x100004aac <_getBigChunk__system_u6608+0x1ac>
100004a8c: 52820d0c    	mov	w12, #0x1068            ; =4200
100004a90: 8b0c010d    	add	x13, x8, x12
100004a94: aa1503e8    	mov	x8, x21
100004a98: f8418d0c    	ldr	x12, [x8, #0x18]!
100004a9c: f90001ac    	str	x12, [x13]
100004aa0: b40002cc    	cbz	x12, 0x100004af8 <_getBigChunk__system_u6608+0x1f8>
100004aa4: f900119f    	str	xzr, [x12, #0x20]
100004aa8: 1400001e    	b	0x100004b20 <_getBigChunk__system_u6608+0x220>
100004aac: aa1303e0    	mov	x0, x19
100004ab0: f142029f    	cmp	x20, #0x80, lsl #12     ; =0x80000
100004ab4: 540000aa    	b.ge	0x100004ac8 <_getBigChunk__system_u6608+0x1c8>
100004ab8: 52a00101    	mov	w1, #0x80000            ; =524288
100004abc: 97fffdea    	bl	0x100004264 <_requestOsChunks__system_u6507>
100004ac0: aa0003f5    	mov	x21, x0
100004ac4: 14000007    	b	0x100004ae0 <_getBigChunk__system_u6608+0x1e0>
100004ac8: aa1403e1    	mov	x1, x20
100004acc: 97fffde6    	bl	0x100004264 <_requestOsChunks__system_u6507>
100004ad0: aa0003f5    	mov	x21, x0
100004ad4: f9400408    	ldr	x8, [x0, #0x8]
100004ad8: eb08029f    	cmp	x20, x8
100004adc: 540000aa    	b.ge	0x100004af0 <_getBigChunk__system_u6608+0x1f0>
100004ae0: aa1303e0    	mov	x0, x19
100004ae4: aa1503e1    	mov	x1, x21
100004ae8: aa1403e2    	mov	x2, x20
100004aec: 97ffff15    	bl	0x100004740 <_splitChunk__system_u6579>
100004af0: f9000ab3    	str	x19, [x21, #0x10]
100004af4: 14000014    	b	0x100004b44 <_getBigChunk__system_u6608+0x244>
100004af8: 8b090a6d    	add	x13, x19, x9, lsl #2
100004afc: 5280002c    	mov	w12, #0x1               ; =1
100004b00: 1acb218b    	lsl	w11, w12, w11
100004b04: 6a2b014a    	bics	w10, w10, w11
100004b08: b91005aa    	str	w10, [x13, #0x1004]
100004b0c: 540000a1    	b.ne	0x100004b20 <_getBigChunk__system_u6608+0x220>
100004b10: b950026a    	ldr	w10, [x19, #0x1000]
100004b14: 1ac92189    	lsl	w9, w12, w9
100004b18: 0a290149    	bic	w9, w10, w9
100004b1c: b9100269    	str	w9, [x19, #0x1000]
100004b20: a9007d1f    	stp	xzr, xzr, [x8]
100004b24: 91400688    	add	x8, x20, #0x1, lsl #12  ; =0x1000
100004b28: f94006a9    	ldr	x9, [x21, #0x8]
100004b2c: eb09011f    	cmp	x8, x9
100004b30: 540000ac    	b.gt	0x100004b44 <_getBigChunk__system_u6608+0x244>
100004b34: aa1303e0    	mov	x0, x19
100004b38: aa1503e1    	mov	x1, x21
100004b3c: aa1403e2    	mov	x2, x20
100004b40: 97ffff00    	bl	0x100004740 <_splitChunk__system_u6579>
100004b44: 52800036    	mov	w22, #0x1               ; =1
100004b48: f90002b6    	str	x22, [x21]
100004b4c: 934cfeb7    	asr	x23, x21, #12
100004b50: 52851408    	mov	w8, #0x28a0             ; =10400
100004b54: 8b080261    	add	x1, x19, x8
100004b58: 9355fea2    	asr	x2, x21, #21
100004b5c: aa1303e0    	mov	x0, x19
100004b60: 97fffe51    	bl	0x1000044a4 <_intSetPut__system_u6237>
100004b64: d34622e8    	ubfx	x8, x23, #6, #3
100004b68: 8b080c08    	add	x8, x0, x8, lsl #3
100004b6c: f9400909    	ldr	x9, [x8, #0x10]
100004b70: 9ad722ca    	lsl	x10, x22, x23
100004b74: aa090149    	orr	x9, x10, x9
100004b78: f9000909    	str	x9, [x8, #0x10]
100004b7c: f9544268    	ldr	x8, [x19, #0x2880]
100004b80: cb140108    	sub	x8, x8, x20
100004b84: f9144268    	str	x8, [x19, #0x2880]
100004b88: aa1503e0    	mov	x0, x21
100004b8c: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100004b90: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100004b94: a94157f6    	ldp	x22, x21, [sp, #0x10]
100004b98: a8c45ff8    	ldp	x24, x23, [sp], #0x40
100004b9c: d65f03c0    	ret

0000000100004ba0 <_getSmallChunk__system_u6636>:
100004ba0: 52820001    	mov	w1, #0x1000             ; =4096
100004ba4: 17ffff57    	b	0x100004900 <_getBigChunk__system_u6608>

0000000100004ba8 <_compensateCounters__system_u6730>:
100004ba8: f9401429    	ldr	x9, [x1, #0x28]
100004bac: b40001a9    	cbz	x9, 0x100004be0 <_compensateCounters__system_u6730+0x38>
100004bb0: d2800008    	mov	x8, #0x0                ; =0
100004bb4: 14000004    	b	0x100004bc4 <_compensateCounters__system_u6730+0x1c>
100004bb8: 8b020108    	add	x8, x8, x2
100004bbc: f9400129    	ldr	x9, [x9]
100004bc0: b4000129    	cbz	x9, 0x100004be4 <_compensateCounters__system_u6730+0x3c>
100004bc4: 9274cd2a    	and	x10, x9, #0xfffffffffffff000
100004bc8: eb01015f    	cmp	x10, x1
100004bcc: 54ffff60    	b.eq	0x100004bb8 <_compensateCounters__system_u6730+0x10>
100004bd0: f9401c2a    	ldr	x10, [x1, #0x38]
100004bd4: 9100054a    	add	x10, x10, #0x1
100004bd8: f9001c2a    	str	x10, [x1, #0x38]
100004bdc: 17fffff7    	b	0x100004bb8 <_compensateCounters__system_u6730+0x10>
100004be0: d2800008    	mov	x8, #0x0                ; =0
100004be4: b9403029    	ldr	w9, [x1, #0x30]
100004be8: 0b080129    	add	w9, w9, w8
100004bec: b9003029    	str	w9, [x1, #0x30]
100004bf0: f9544409    	ldr	x9, [x0, #0x2888]
100004bf4: cb080128    	sub	x8, x9, x8
100004bf8: f9144408    	str	x8, [x0, #0x2888]
100004bfc: d65f03c0    	ret

0000000100004c00 <_excl__system_u6317>:
100004c00: 9349fc28    	asr	x8, x1, #9
100004c04: aa0803e9    	mov	x9, x8
100004c08: d37d1d09    	ubfiz	x9, x8, #3, #8
100004c0c: 8b090009    	add	x9, x0, x9
100004c10: f9400129    	ldr	x9, [x9]
100004c14: b4000169    	cbz	x9, 0x100004c40 <_excl__system_u6317+0x40>
100004c18: f940052a    	ldr	x10, [x9, #0x8]
100004c1c: eb08015f    	cmp	x10, x8
100004c20: 54ffff81    	b.ne	0x100004c10 <_excl__system_u6317+0x10>
100004c24: d3462028    	ubfx	x8, x1, #6, #3
100004c28: 8b080d28    	add	x8, x9, x8, lsl #3
100004c2c: f9400909    	ldr	x9, [x8, #0x10]
100004c30: 5280002a    	mov	w10, #0x1               ; =1
100004c34: 9ac1214a    	lsl	x10, x10, x1
100004c38: 8a2a0129    	bic	x9, x9, x10
100004c3c: f9000909    	str	x9, [x8, #0x10]
100004c40: d65f03c0    	ret

0000000100004c44 <_freeHugeChunk__system_u6632>:
100004c44: aa0103e8    	mov	x8, x1
100004c48: f9400421    	ldr	x1, [x1, #0x8]
100004c4c: 934cfd09    	asr	x9, x8, #12
100004c50: 9355fd0a    	asr	x10, x8, #21
100004c54: aa0a03eb    	mov	x11, x10
100004c58: d37d1d4b    	ubfiz	x11, x10, #3, #8
100004c5c: 5285140c    	mov	w12, #0x28a0            ; =10400
100004c60: 8b0c000c    	add	x12, x0, x12
100004c64: 8b0b018b    	add	x11, x12, x11
100004c68: f940016b    	ldr	x11, [x11]
100004c6c: b400018b    	cbz	x11, 0x100004c9c <_freeHugeChunk__system_u6632+0x58>
100004c70: f940056c    	ldr	x12, [x11, #0x8]
100004c74: eb0a019f    	cmp	x12, x10
100004c78: 54ffff81    	b.ne	0x100004c68 <_freeHugeChunk__system_u6632+0x24>
100004c7c: d34cfd0a    	lsr	x10, x8, #12
100004c80: d3462129    	ubfx	x9, x9, #6, #3
100004c84: 8b090d69    	add	x9, x11, x9, lsl #3
100004c88: f940092b    	ldr	x11, [x9, #0x10]
100004c8c: 5280002c    	mov	w12, #0x1               ; =1
100004c90: 9aca218a    	lsl	x10, x12, x10
100004c94: 8a2a016a    	bic	x10, x11, x10
100004c98: f900092a    	str	x10, [x9, #0x10]
100004c9c: f9543c09    	ldr	x9, [x0, #0x2878]
100004ca0: f954380a    	ldr	x10, [x0, #0x2870]
100004ca4: eb0a013f    	cmp	x9, x10
100004ca8: 9a8ac129    	csel	x9, x9, x10, gt
100004cac: f9143c09    	str	x9, [x0, #0x2878]
100004cb0: cb010149    	sub	x9, x10, x1
100004cb4: f9143809    	str	x9, [x0, #0x2870]
100004cb8: aa0803e0    	mov	x0, x8
100004cbc: 14001a37    	b	0x10000b598 <_strlen+0x10000b598>

0000000100004cc0 <_removeChunkFromMatrix__system_u5983>:
100004cc0: aa0103e8    	mov	x8, x1
100004cc4: f8418d09    	ldr	x9, [x8, #0x18]!
100004cc8: f85f010a    	ldur	x10, [x8, #-0x10]
100004ccc: 7103fd5f    	cmp	w10, #0xff
100004cd0: 1a9f97eb    	cset	w11, hi
100004cd4: d37d7d6b    	ubfiz	x11, x11, #3, #32
100004cd8: d3587d4c    	ubfx	x12, x10, #24, #8
100004cdc: 7100019f    	cmp	w12, #0x0
100004ce0: 5280030c    	mov	w12, #0x18              ; =24
100004ce4: 5280020d    	mov	w13, #0x10              ; =16
100004ce8: 9a8c01ac    	csel	x12, x13, x12, eq
100004cec: 7140415f    	cmp	w10, #0x10, lsl #12     ; =0x10000
100004cf0: 9a8c316b    	csel	x11, x11, x12, lo
100004cf4: 92407d4c    	and	x12, x10, #0xffffffff
100004cf8: f000002d    	adrp	x13, 0x10000b000 <_bench__add95carry_u844+0x104>
100004cfc: 911cc1ad    	add	x13, x13, #0x730
100004d00: 9acb258c    	lsr	x12, x12, x11
100004d04: 38ac69ac    	ldrsb	x12, [x13, x12]
100004d08: 8b0c016b    	add	x11, x11, x12
100004d0c: d100156c    	sub	x12, x11, #0x5
100004d10: 9acc294a    	asr	x10, x10, x12
100004d14: b4000069    	cbz	x9, 0x100004d20 <_removeChunkFromMatrix__system_u5983+0x60>
100004d18: f940102c    	ldr	x12, [x1, #0x20]
100004d1c: f900112c    	str	x12, [x9, #0x20]
100004d20: d1001969    	sub	x9, x11, #0x6
100004d24: d100814b    	sub	x11, x10, #0x20
100004d28: f940102c    	ldr	x12, [x1, #0x20]
100004d2c: b400006c    	cbz	x12, 0x100004d38 <_removeChunkFromMatrix__system_u5983+0x78>
100004d30: f940010d    	ldr	x13, [x8]
100004d34: f9000d8d    	str	x13, [x12, #0x18]
100004d38: 8b09200c    	add	x12, x0, x9, lsl #8
100004d3c: 8b0b0d8b    	add	x11, x12, x11, lsl #3
100004d40: f948356c    	ldr	x12, [x11, #0x1068]
100004d44: eb01019f    	cmp	x12, x1
100004d48: 54000060    	b.eq	0x100004d54 <_removeChunkFromMatrix__system_u5983+0x94>
100004d4c: a9007d1f    	stp	xzr, xzr, [x8]
100004d50: d65f03c0    	ret
100004d54: 52820d0c    	mov	w12, #0x1068            ; =4200
100004d58: 8b0c016b    	add	x11, x11, x12
100004d5c: f940010c    	ldr	x12, [x8]
100004d60: f900016c    	str	x12, [x11]
100004d64: b5ffff4c    	cbnz	x12, 0x100004d4c <_removeChunkFromMatrix__system_u5983+0x8c>
100004d68: 8b09080c    	add	x12, x0, x9, lsl #2
100004d6c: b950058d    	ldr	w13, [x12, #0x1004]
100004d70: 5280002b    	mov	w11, #0x1               ; =1
100004d74: 1aca216a    	lsl	w10, w11, w10
100004d78: 6a2a01aa    	bics	w10, w13, w10
100004d7c: b910058a    	str	w10, [x12, #0x1004]
100004d80: 54fffe61    	b.ne	0x100004d4c <_removeChunkFromMatrix__system_u5983+0x8c>
100004d84: b950000a    	ldr	w10, [x0, #0x1000]
100004d88: 1ac92169    	lsl	w9, w11, w9
100004d8c: 0a290149    	bic	w9, w10, w9
100004d90: b9100009    	str	w9, [x0, #0x1000]
100004d94: a9007d1f    	stp	xzr, xzr, [x8]
100004d98: d65f03c0    	ret

0000000100004d9c <_freeBigChunk__system_u6584>:
100004d9c: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
100004da0: a90157f6    	stp	x22, x21, [sp, #0x10]
100004da4: a9024ff4    	stp	x20, x19, [sp, #0x20]
100004da8: a9037bfd    	stp	x29, x30, [sp, #0x30]
100004dac: 9100c3fd    	add	x29, sp, #0x30
100004db0: aa0103f4    	mov	x20, x1
100004db4: aa0003f3    	mov	x19, x0
100004db8: f9544008    	ldr	x8, [x0, #0x2880]
100004dbc: a940242a    	ldp	x10, x9, [x1]
100004dc0: 8b090108    	add	x8, x8, x9
100004dc4: f9144008    	str	x8, [x0, #0x2880]
100004dc8: f0000035    	adrp	x21, 0x10000b000 <_bench__add95carry_u844+0x104>
100004dcc: 911cc2b5    	add	x21, x21, #0x730
100004dd0: f27ff948    	ands	x8, x10, #0xfffffffffffffffe
100004dd4: f9000028    	str	x8, [x1]
100004dd8: 540016c0    	b.eq	0x1000050b0 <_freeBigChunk__system_u6584+0x314>
100004ddc: cb080296    	sub	x22, x20, x8
100004de0: 934cfec8    	asr	x8, x22, #12
100004de4: 5285140a    	mov	w10, #0x28a0            ; =10400
100004de8: 9355fec9    	asr	x9, x22, #21
100004dec: aa0903eb    	mov	x11, x9
100004df0: d37d1d2b    	ubfiz	x11, x9, #3, #8
100004df4: 8b0a0261    	add	x1, x19, x10
100004df8: 8b0b002a    	add	x10, x1, x11
100004dfc: f940014a    	ldr	x10, [x10]
100004e00: b400158a    	cbz	x10, 0x1000050b0 <_freeBigChunk__system_u6584+0x314>
100004e04: f940054b    	ldr	x11, [x10, #0x8]
100004e08: eb09017f    	cmp	x11, x9
100004e0c: 54ffff81    	b.ne	0x100004dfc <_freeBigChunk__system_u6584+0x60>
100004e10: d34cfec9    	lsr	x9, x22, #12
100004e14: d3462108    	ubfx	x8, x8, #6, #3
100004e18: 8b080d48    	add	x8, x10, x8, lsl #3
100004e1c: f9400908    	ldr	x8, [x8, #0x10]
100004e20: 9ac92508    	lsr	x8, x8, x9
100004e24: 36001468    	tbz	w8, #0x0, 0x1000050b0 <_freeBigChunk__system_u6584+0x314>
100004e28: 394002c8    	ldrb	w8, [x22]
100004e2c: 37001428    	tbnz	w8, #0x0, 0x1000050b0 <_freeBigChunk__system_u6584+0x314>
100004e30: f94006c8    	ldr	x8, [x22, #0x8]
100004e34: d13f0509    	sub	x9, x8, #0xfc1
100004e38: 529e07ca    	mov	w10, #0xf03e            ; =61502
100004e3c: 72a7dfea    	movk	w10, #0x3eff, lsl #16
100004e40: eb0a013f    	cmp	x9, x10
100004e44: 54001368    	b.hi	0x1000050b0 <_freeBigChunk__system_u6584+0x314>
100004e48: d3587d09    	ubfx	x9, x8, #24, #8
100004e4c: 7100013f    	cmp	w9, #0x0
100004e50: 52800309    	mov	w9, #0x18               ; =24
100004e54: 5280020a    	mov	w10, #0x10              ; =16
100004e58: 9a890149    	csel	x9, x10, x9, eq
100004e5c: 7140411f    	cmp	w8, #0x10, lsl #12      ; =0x10000
100004e60: 5280010a    	mov	w10, #0x8               ; =8
100004e64: 9a893149    	csel	x9, x10, x9, lo
100004e68: 92407d0a    	and	x10, x8, #0xffffffff
100004e6c: 9ac9254a    	lsr	x10, x10, x9
100004e70: 38aa6aaa    	ldrsb	x10, [x21, x10]
100004e74: 8b0a012b    	add	x11, x9, x10
100004e78: d1001569    	sub	x9, x11, #0x5
100004e7c: 9ac9250a    	lsr	x10, x8, x9
100004e80: aa1603e9    	mov	x9, x22
100004e84: f8418d2c    	ldr	x12, [x9, #0x18]!
100004e88: b400006c    	cbz	x12, 0x100004e94 <_freeBigChunk__system_u6584+0xf8>
100004e8c: f94012cd    	ldr	x13, [x22, #0x20]
100004e90: f900118d    	str	x13, [x12, #0x20]
100004e94: d100196b    	sub	x11, x11, #0x6
100004e98: d100814c    	sub	x12, x10, #0x20
100004e9c: f94012cd    	ldr	x13, [x22, #0x20]
100004ea0: b400006d    	cbz	x13, 0x100004eac <_freeBigChunk__system_u6584+0x110>
100004ea4: f940012e    	ldr	x14, [x9]
100004ea8: f9000dae    	str	x14, [x13, #0x18]
100004eac: 8b0b226d    	add	x13, x19, x11, lsl #8
100004eb0: 8b0c0dac    	add	x12, x13, x12, lsl #3
100004eb4: f948358d    	ldr	x13, [x12, #0x1068]
100004eb8: eb1601bf    	cmp	x13, x22
100004ebc: 54000221    	b.ne	0x100004f00 <_freeBigChunk__system_u6584+0x164>
100004ec0: 52820d0d    	mov	w13, #0x1068            ; =4200
100004ec4: 8b0d018c    	add	x12, x12, x13
100004ec8: f940012d    	ldr	x13, [x9]
100004ecc: f900018d    	str	x13, [x12]
100004ed0: b500018d    	cbnz	x13, 0x100004f00 <_freeBigChunk__system_u6584+0x164>
100004ed4: 8b0b0a6d    	add	x13, x19, x11, lsl #2
100004ed8: b95005ae    	ldr	w14, [x13, #0x1004]
100004edc: 5280002c    	mov	w12, #0x1               ; =1
100004ee0: 1aca218a    	lsl	w10, w12, w10
100004ee4: 6a2a01ca    	bics	w10, w14, w10
100004ee8: b91005aa    	str	w10, [x13, #0x1004]
100004eec: 540000a1    	b.ne	0x100004f00 <_freeBigChunk__system_u6584+0x164>
100004ef0: b950026a    	ldr	w10, [x19, #0x1000]
100004ef4: 1acb218b    	lsl	w11, w12, w11
100004ef8: 0a2b014a    	bic	w10, w10, w11
100004efc: b910026a    	str	w10, [x19, #0x1000]
100004f00: a9007d3f    	stp	xzr, xzr, [x9]
100004f04: f9400689    	ldr	x9, [x20, #0x8]
100004f08: 8b080128    	add	x8, x9, x8
100004f0c: f90006c8    	str	x8, [x22, #0x8]
100004f10: 934cfe89    	asr	x9, x20, #12
100004f14: 9355fe8a    	asr	x10, x20, #21
100004f18: aa0a03eb    	mov	x11, x10
100004f1c: d37d1d4b    	ubfiz	x11, x10, #3, #8
100004f20: 8b0b002b    	add	x11, x1, x11
100004f24: f940016b    	ldr	x11, [x11]
100004f28: b40001ab    	cbz	x11, 0x100004f5c <_freeBigChunk__system_u6584+0x1c0>
100004f2c: f940056c    	ldr	x12, [x11, #0x8]
100004f30: eb0a019f    	cmp	x12, x10
100004f34: 54ffff81    	b.ne	0x100004f24 <_freeBigChunk__system_u6584+0x188>
100004f38: d34cfe88    	lsr	x8, x20, #12
100004f3c: d3462129    	ubfx	x9, x9, #6, #3
100004f40: 8b090d69    	add	x9, x11, x9, lsl #3
100004f44: f940092a    	ldr	x10, [x9, #0x10]
100004f48: 5280002b    	mov	w11, #0x1               ; =1
100004f4c: 9ac82168    	lsl	x8, x11, x8
100004f50: 8a280148    	bic	x8, x10, x8
100004f54: f9000928    	str	x8, [x9, #0x10]
100004f58: f94006c8    	ldr	x8, [x22, #0x8]
100004f5c: 52800029    	mov	w9, #0x1                ; =1
100004f60: 72a7e009    	movk	w9, #0x3f00, lsl #16
100004f64: aa1603f4    	mov	x20, x22
100004f68: eb09011f    	cmp	x8, x9
100004f6c: 54000a2b    	b.lt	0x1000050b0 <_freeBigChunk__system_u6584+0x314>
100004f70: 52a7e009    	mov	w9, #0x3f000000         ; =1056964608
100004f74: 8b0902d4    	add	x20, x22, x9
100004f78: 929fffea    	mov	x10, #-0x10000          ; =-65536
100004f7c: f2b8200a    	movk	x10, #0xc100, lsl #16
100004f80: 8b0a0108    	add	x8, x8, x10
100004f84: a901fe9f    	stp	xzr, xzr, [x20, #0x18]
100004f88: a9002289    	stp	x9, x8, [x20]
100004f8c: f9000a93    	str	x19, [x20, #0x10]
100004f90: f94006c9    	ldr	x9, [x22, #0x8]
100004f94: 8b160129    	add	x9, x9, x22
100004f98: 934cfd2a    	asr	x10, x9, #12
100004f9c: 9355fd2b    	asr	x11, x9, #21
100004fa0: aa0b03ec    	mov	x12, x11
100004fa4: d37d1d6c    	ubfiz	x12, x11, #3, #8
100004fa8: 8b0c002c    	add	x12, x1, x12
100004fac: f940018c    	ldr	x12, [x12]
100004fb0: b40001cc    	cbz	x12, 0x100004fe8 <_freeBigChunk__system_u6584+0x24c>
100004fb4: f940058d    	ldr	x13, [x12, #0x8]
100004fb8: eb0b01bf    	cmp	x13, x11
100004fbc: 54ffff81    	b.ne	0x100004fac <_freeBigChunk__system_u6584+0x210>
100004fc0: d34cfd2b    	lsr	x11, x9, #12
100004fc4: d346214a    	ubfx	x10, x10, #6, #3
100004fc8: 8b0a0d8a    	add	x10, x12, x10, lsl #3
100004fcc: f940094a    	ldr	x10, [x10, #0x10]
100004fd0: 9acb254a    	lsr	x10, x10, x11
100004fd4: 360000aa    	tbz	w10, #0x0, 0x100004fe8 <_freeBigChunk__system_u6584+0x24c>
100004fd8: f940012a    	ldr	x10, [x9]
100004fdc: 9240014a    	and	x10, x10, #0x1
100004fe0: aa080148    	orr	x8, x10, x8
100004fe4: f9000128    	str	x8, [x9]
100004fe8: 52a7e008    	mov	w8, #0x3f000000         ; =1056964608
100004fec: f90006c8    	str	x8, [x22, #0x8]
100004ff0: 934cfe97    	asr	x23, x20, #12
100004ff4: 9355fe82    	asr	x2, x20, #21
100004ff8: aa1303e0    	mov	x0, x19
100004ffc: 97fffd2a    	bl	0x1000044a4 <_intSetPut__system_u6237>
100005000: d34622e8    	ubfx	x8, x23, #6, #3
100005004: 8b080c09    	add	x9, x0, x8, lsl #3
100005008: f940092a    	ldr	x10, [x9, #0x10]
10000500c: 52800028    	mov	w8, #0x1                ; =1
100005010: 9ad7210b    	lsl	x11, x8, x23
100005014: aa0b014a    	orr	x10, x10, x11
100005018: f900092a    	str	x10, [x9, #0x10]
10000501c: f94006c9    	ldr	x9, [x22, #0x8]
100005020: 7103fd3f    	cmp	w9, #0xff
100005024: 1a9f97ea    	cset	w10, hi
100005028: d37d7d4a    	ubfiz	x10, x10, #3, #32
10000502c: d3587d2b    	ubfx	x11, x9, #24, #8
100005030: 7100017f    	cmp	w11, #0x0
100005034: 5280030b    	mov	w11, #0x18              ; =24
100005038: 5280020c    	mov	w12, #0x10              ; =16
10000503c: 9a8b018b    	csel	x11, x12, x11, eq
100005040: 7140413f    	cmp	w9, #0x10, lsl #12      ; =0x10000
100005044: 9a8b314a    	csel	x10, x10, x11, lo
100005048: 92407d2b    	and	x11, x9, #0xffffffff
10000504c: 9aca256b    	lsr	x11, x11, x10
100005050: 38ab6aab    	ldrsb	x11, [x21, x11]
100005054: 8b0b014b    	add	x11, x10, x11
100005058: d100156a    	sub	x10, x11, #0x5
10000505c: 9aca292a    	asr	x10, x9, x10
100005060: d1001969    	sub	x9, x11, #0x6
100005064: f90012df    	str	xzr, [x22, #0x20]
100005068: 8b09226b    	add	x11, x19, x9, lsl #8
10000506c: 8b0a0d6c    	add	x12, x11, x10, lsl #3
100005070: 913da18b    	add	x11, x12, #0xf68
100005074: f947b58d    	ldr	x13, [x12, #0xf68]
100005078: f9000ecd    	str	x13, [x22, #0x18]
10000507c: f947b58c    	ldr	x12, [x12, #0xf68]
100005080: b400004c    	cbz	x12, 0x100005088 <_freeBigChunk__system_u6584+0x2ec>
100005084: f9001196    	str	x22, [x12, #0x20]
100005088: f9000176    	str	x22, [x11]
10000508c: 8b090a6b    	add	x11, x19, x9, lsl #2
100005090: b950056c    	ldr	w12, [x11, #0x1004]
100005094: 1aca210a    	lsl	w10, w8, w10
100005098: 2a0a018a    	orr	w10, w12, w10
10000509c: b910056a    	str	w10, [x11, #0x1004]
1000050a0: b950026a    	ldr	w10, [x19, #0x1000]
1000050a4: 1ac92108    	lsl	w8, w8, w9
1000050a8: 2a080148    	orr	w8, w10, w8
1000050ac: b9100268    	str	w8, [x19, #0x1000]
1000050b0: f940068a    	ldr	x10, [x20, #0x8]
1000050b4: 8b14014d    	add	x13, x10, x20
1000050b8: 934cfdab    	asr	x11, x13, #12
1000050bc: 52851409    	mov	w9, #0x28a0             ; =10400
1000050c0: 9355fda8    	asr	x8, x13, #21
1000050c4: aa0803ec    	mov	x12, x8
1000050c8: d37d1d0c    	ubfiz	x12, x8, #3, #8
1000050cc: 8b090261    	add	x1, x19, x9
1000050d0: 8b0c0029    	add	x9, x1, x12
1000050d4: aa0903ec    	mov	x12, x9
1000050d8: f940018c    	ldr	x12, [x12]
1000050dc: b40014ec    	cbz	x12, 0x100005378 <_freeBigChunk__system_u6584+0x5dc>
1000050e0: f940058e    	ldr	x14, [x12, #0x8]
1000050e4: eb0801df    	cmp	x14, x8
1000050e8: 54ffff81    	b.ne	0x1000050d8 <_freeBigChunk__system_u6584+0x33c>
1000050ec: d34cfdae    	lsr	x14, x13, #12
1000050f0: d346216b    	ubfx	x11, x11, #6, #3
1000050f4: 8b0b0d8c    	add	x12, x12, x11, lsl #3
1000050f8: f940098f    	ldr	x15, [x12, #0x10]
1000050fc: 5280002c    	mov	w12, #0x1               ; =1
100005100: 9ace218c    	lsl	x12, x12, x14
100005104: ea0c01ff    	tst	x15, x12
100005108: 54001380    	b.eq	0x100005378 <_freeBigChunk__system_u6584+0x5dc>
10000510c: 394001ae    	ldrb	w14, [x13]
100005110: 3700134e    	tbnz	w14, #0x0, 0x100005378 <_freeBigChunk__system_u6584+0x5dc>
100005114: f94005ae    	ldr	x14, [x13, #0x8]
100005118: f13f05df    	cmp	x14, #0xfc1
10000511c: 540012eb    	b.lt	0x100005378 <_freeBigChunk__system_u6584+0x5dc>
100005120: 12b8200f    	mov	w15, #0x3effffff        ; =1056964607
100005124: eb0f015f    	cmp	x10, x15
100005128: 5400128c    	b.gt	0x100005378 <_freeBigChunk__system_u6584+0x5dc>
10000512c: 7103fddf    	cmp	w14, #0xff
100005130: 1a9f97ea    	cset	w10, hi
100005134: d37d7d4a    	ubfiz	x10, x10, #3, #32
100005138: d3587dcf    	ubfx	x15, x14, #24, #8
10000513c: 710001ff    	cmp	w15, #0x0
100005140: 5280030f    	mov	w15, #0x18              ; =24
100005144: 52800210    	mov	w16, #0x10              ; =16
100005148: 9a8f020f    	csel	x15, x16, x15, eq
10000514c: 714041df    	cmp	w14, #0x10, lsl #12     ; =0x10000
100005150: 9a8f314a    	csel	x10, x10, x15, lo
100005154: 92407dcf    	and	x15, x14, #0xffffffff
100005158: 9aca25ef    	lsr	x15, x15, x10
10000515c: 38af6aaf    	ldrsb	x15, [x21, x15]
100005160: 8b0f0150    	add	x16, x10, x15
100005164: d100160a    	sub	x10, x16, #0x5
100005168: 9aca25cf    	lsr	x15, x14, x10
10000516c: aa0d03ea    	mov	x10, x13
100005170: f8418d51    	ldr	x17, [x10, #0x18]!
100005174: b4000071    	cbz	x17, 0x100005180 <_freeBigChunk__system_u6584+0x3e4>
100005178: f94011a0    	ldr	x0, [x13, #0x20]
10000517c: f9001220    	str	x0, [x17, #0x20]
100005180: d1001a10    	sub	x16, x16, #0x6
100005184: d10081f1    	sub	x17, x15, #0x20
100005188: f94011a0    	ldr	x0, [x13, #0x20]
10000518c: b4000060    	cbz	x0, 0x100005198 <_freeBigChunk__system_u6584+0x3fc>
100005190: f9400142    	ldr	x2, [x10]
100005194: f9000c02    	str	x2, [x0, #0x18]
100005198: 8b102260    	add	x0, x19, x16, lsl #8
10000519c: 8b110c11    	add	x17, x0, x17, lsl #3
1000051a0: f9483620    	ldr	x0, [x17, #0x1068]
1000051a4: eb0d001f    	cmp	x0, x13
1000051a8: 54000221    	b.ne	0x1000051ec <_freeBigChunk__system_u6584+0x450>
1000051ac: 52820d0d    	mov	w13, #0x1068            ; =4200
1000051b0: 8b0d022d    	add	x13, x17, x13
1000051b4: f9400151    	ldr	x17, [x10]
1000051b8: f90001b1    	str	x17, [x13]
1000051bc: b5000191    	cbnz	x17, 0x1000051ec <_freeBigChunk__system_u6584+0x450>
1000051c0: 8b100a71    	add	x17, x19, x16, lsl #2
1000051c4: b9500620    	ldr	w0, [x17, #0x1004]
1000051c8: 5280002d    	mov	w13, #0x1               ; =1
1000051cc: 1acf21af    	lsl	w15, w13, w15
1000051d0: 6a2f000f    	bics	w15, w0, w15
1000051d4: b910062f    	str	w15, [x17, #0x1004]
1000051d8: 540000a1    	b.ne	0x1000051ec <_freeBigChunk__system_u6584+0x450>
1000051dc: b950026f    	ldr	w15, [x19, #0x1000]
1000051e0: 1ad021ad    	lsl	w13, w13, w16
1000051e4: 0a2d01ed    	bic	w13, w15, w13
1000051e8: b910026d    	str	w13, [x19, #0x1000]
1000051ec: a9007d5f    	stp	xzr, xzr, [x10]
1000051f0: f940068a    	ldr	x10, [x20, #0x8]
1000051f4: 8b0e014a    	add	x10, x10, x14
1000051f8: f900068a    	str	x10, [x20, #0x8]
1000051fc: f9400129    	ldr	x9, [x9]
100005200: b4000129    	cbz	x9, 0x100005224 <_freeBigChunk__system_u6584+0x488>
100005204: f940052d    	ldr	x13, [x9, #0x8]
100005208: eb0801bf    	cmp	x13, x8
10000520c: 54ffff81    	b.ne	0x1000051fc <_freeBigChunk__system_u6584+0x460>
100005210: 8b0b0d28    	add	x8, x9, x11, lsl #3
100005214: f9400909    	ldr	x9, [x8, #0x10]
100005218: 8a2c0129    	bic	x9, x9, x12
10000521c: f9000909    	str	x9, [x8, #0x10]
100005220: f940068a    	ldr	x10, [x20, #0x8]
100005224: 52800028    	mov	w8, #0x1                ; =1
100005228: 72a7e008    	movk	w8, #0x3f00, lsl #16
10000522c: eb08015f    	cmp	x10, x8
100005230: 54000a4b    	b.lt	0x100005378 <_freeBigChunk__system_u6584+0x5dc>
100005234: 52a7e009    	mov	w9, #0x3f000000         ; =1056964608
100005238: 8b090296    	add	x22, x20, x9
10000523c: 929fffe8    	mov	x8, #-0x10000           ; =-65536
100005240: f2b82008    	movk	x8, #0xc100, lsl #16
100005244: 8b080148    	add	x8, x10, x8
100005248: a901fedf    	stp	xzr, xzr, [x22, #0x18]
10000524c: a90022c9    	stp	x9, x8, [x22]
100005250: f9000ad3    	str	x19, [x22, #0x10]
100005254: f9400689    	ldr	x9, [x20, #0x8]
100005258: 8b140129    	add	x9, x9, x20
10000525c: 934cfd2a    	asr	x10, x9, #12
100005260: 9355fd2b    	asr	x11, x9, #21
100005264: aa0b03ec    	mov	x12, x11
100005268: d37d1d6c    	ubfiz	x12, x11, #3, #8
10000526c: 8b0c002c    	add	x12, x1, x12
100005270: f940018c    	ldr	x12, [x12]
100005274: b40001cc    	cbz	x12, 0x1000052ac <_freeBigChunk__system_u6584+0x510>
100005278: f940058d    	ldr	x13, [x12, #0x8]
10000527c: eb0b01bf    	cmp	x13, x11
100005280: 54ffff81    	b.ne	0x100005270 <_freeBigChunk__system_u6584+0x4d4>
100005284: d34cfd2b    	lsr	x11, x9, #12
100005288: d346214a    	ubfx	x10, x10, #6, #3
10000528c: 8b0a0d8a    	add	x10, x12, x10, lsl #3
100005290: f940094a    	ldr	x10, [x10, #0x10]
100005294: 9acb254a    	lsr	x10, x10, x11
100005298: 360000aa    	tbz	w10, #0x0, 0x1000052ac <_freeBigChunk__system_u6584+0x510>
10000529c: f940012a    	ldr	x10, [x9]
1000052a0: 9240014a    	and	x10, x10, #0x1
1000052a4: aa080148    	orr	x8, x10, x8
1000052a8: f9000128    	str	x8, [x9]
1000052ac: 52a7e008    	mov	w8, #0x3f000000         ; =1056964608
1000052b0: f9000688    	str	x8, [x20, #0x8]
1000052b4: 934cfed7    	asr	x23, x22, #12
1000052b8: 9355fec2    	asr	x2, x22, #21
1000052bc: aa1303e0    	mov	x0, x19
1000052c0: 97fffc79    	bl	0x1000044a4 <_intSetPut__system_u6237>
1000052c4: d34622e8    	ubfx	x8, x23, #6, #3
1000052c8: 8b080c09    	add	x9, x0, x8, lsl #3
1000052cc: f940092a    	ldr	x10, [x9, #0x10]
1000052d0: 52800028    	mov	w8, #0x1                ; =1
1000052d4: 9ad7210b    	lsl	x11, x8, x23
1000052d8: aa0b014a    	orr	x10, x10, x11
1000052dc: f900092a    	str	x10, [x9, #0x10]
1000052e0: f94006c9    	ldr	x9, [x22, #0x8]
1000052e4: 7103fd3f    	cmp	w9, #0xff
1000052e8: 1a9f97ea    	cset	w10, hi
1000052ec: d37d7d4a    	ubfiz	x10, x10, #3, #32
1000052f0: d3587d2b    	ubfx	x11, x9, #24, #8
1000052f4: 7100017f    	cmp	w11, #0x0
1000052f8: 5280030b    	mov	w11, #0x18              ; =24
1000052fc: 5280020c    	mov	w12, #0x10              ; =16
100005300: 9a8b018b    	csel	x11, x12, x11, eq
100005304: 7140413f    	cmp	w9, #0x10, lsl #12      ; =0x10000
100005308: 9a8b314a    	csel	x10, x10, x11, lo
10000530c: 92407d2b    	and	x11, x9, #0xffffffff
100005310: 9aca256b    	lsr	x11, x11, x10
100005314: 38ab6aab    	ldrsb	x11, [x21, x11]
100005318: 8b0b014b    	add	x11, x10, x11
10000531c: d100156a    	sub	x10, x11, #0x5
100005320: 9aca292a    	asr	x10, x9, x10
100005324: d1001969    	sub	x9, x11, #0x6
100005328: f90012df    	str	xzr, [x22, #0x20]
10000532c: 8b09226b    	add	x11, x19, x9, lsl #8
100005330: 8b0a0d6c    	add	x12, x11, x10, lsl #3
100005334: 913da18b    	add	x11, x12, #0xf68
100005338: f947b58d    	ldr	x13, [x12, #0xf68]
10000533c: f9000ecd    	str	x13, [x22, #0x18]
100005340: f947b58c    	ldr	x12, [x12, #0xf68]
100005344: b400004c    	cbz	x12, 0x10000534c <_freeBigChunk__system_u6584+0x5b0>
100005348: f9001196    	str	x22, [x12, #0x20]
10000534c: f9000176    	str	x22, [x11]
100005350: 8b090a6b    	add	x11, x19, x9, lsl #2
100005354: b950056c    	ldr	w12, [x11, #0x1004]
100005358: 1aca210a    	lsl	w10, w8, w10
10000535c: 2a0a018a    	orr	w10, w12, w10
100005360: b910056a    	str	w10, [x11, #0x1004]
100005364: b950026a    	ldr	w10, [x19, #0x1000]
100005368: 1ac92108    	lsl	w8, w8, w9
10000536c: 2a080148    	orr	w8, w10, w8
100005370: b9100268    	str	w8, [x19, #0x1000]
100005374: f940068a    	ldr	x10, [x20, #0x8]
100005378: 7103fd5f    	cmp	w10, #0xff
10000537c: 1a9f97e8    	cset	w8, hi
100005380: d37d7d08    	ubfiz	x8, x8, #3, #32
100005384: d3587d49    	ubfx	x9, x10, #24, #8
100005388: 7100013f    	cmp	w9, #0x0
10000538c: 52800309    	mov	w9, #0x18               ; =24
100005390: 5280020b    	mov	w11, #0x10              ; =16
100005394: 9a890169    	csel	x9, x11, x9, eq
100005398: 7140415f    	cmp	w10, #0x10, lsl #12     ; =0x10000
10000539c: 9a893108    	csel	x8, x8, x9, lo
1000053a0: 92407d49    	and	x9, x10, #0xffffffff
1000053a4: 9ac82529    	lsr	x9, x9, x8
1000053a8: 38a96aa9    	ldrsb	x9, [x21, x9]
1000053ac: 8b090108    	add	x8, x8, x9
1000053b0: d1001509    	sub	x9, x8, #0x5
1000053b4: 9ac92949    	asr	x9, x10, x9
1000053b8: d1001908    	sub	x8, x8, #0x6
1000053bc: f900129f    	str	xzr, [x20, #0x20]
1000053c0: 8b08226a    	add	x10, x19, x8, lsl #8
1000053c4: 8b090d4b    	add	x11, x10, x9, lsl #3
1000053c8: 913da16a    	add	x10, x11, #0xf68
1000053cc: f947b56c    	ldr	x12, [x11, #0xf68]
1000053d0: f9000e8c    	str	x12, [x20, #0x18]
1000053d4: f947b56b    	ldr	x11, [x11, #0xf68]
1000053d8: b400004b    	cbz	x11, 0x1000053e0 <_freeBigChunk__system_u6584+0x644>
1000053dc: f9001174    	str	x20, [x11, #0x20]
1000053e0: f9000154    	str	x20, [x10]
1000053e4: 8b080a6a    	add	x10, x19, x8, lsl #2
1000053e8: b950054b    	ldr	w11, [x10, #0x1004]
1000053ec: 5280002c    	mov	w12, #0x1               ; =1
1000053f0: 1ac92189    	lsl	w9, w12, w9
1000053f4: 2a090169    	orr	w9, w11, w9
1000053f8: b9100549    	str	w9, [x10, #0x1004]
1000053fc: b9500269    	ldr	w9, [x19, #0x1000]
100005400: 1ac82188    	lsl	w8, w12, w8
100005404: 2a080128    	orr	w8, w9, w8
100005408: b9100268    	str	w8, [x19, #0x1000]
10000540c: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100005410: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100005414: a94157f6    	ldp	x22, x21, [sp, #0x10]
100005418: a8c45ff8    	ldp	x24, x23, [sp], #0x40
10000541c: d65f03c0    	ret

0000000100005420 <_deallocBigChunk__system_u6654>:
100005420: f9400428    	ldr	x8, [x1, #0x8]
100005424: f9544409    	ldr	x9, [x0, #0x2888]
100005428: cb080129    	sub	x9, x9, x8
10000542c: f9144409    	str	x9, [x0, #0x2888]
100005430: 52800029    	mov	w9, #0x1                ; =1
100005434: 72a7e009    	movk	w9, #0x3f00, lsl #16
100005438: eb09011f    	cmp	x8, x9
10000543c: 540003eb    	b.lt	0x1000054b8 <_deallocBigChunk__system_u6654+0x98>
100005440: 934cfc29    	asr	x9, x1, #12
100005444: 9355fc2a    	asr	x10, x1, #21
100005448: aa0a03eb    	mov	x11, x10
10000544c: d37d1d4b    	ubfiz	x11, x10, #3, #8
100005450: 5285140c    	mov	w12, #0x28a0            ; =10400
100005454: 8b0c000c    	add	x12, x0, x12
100005458: 8b0b018b    	add	x11, x12, x11
10000545c: f940016b    	ldr	x11, [x11]
100005460: b400018b    	cbz	x11, 0x100005490 <_deallocBigChunk__system_u6654+0x70>
100005464: f940056c    	ldr	x12, [x11, #0x8]
100005468: eb0a019f    	cmp	x12, x10
10000546c: 54ffff81    	b.ne	0x10000545c <_deallocBigChunk__system_u6654+0x3c>
100005470: d34cfc2a    	lsr	x10, x1, #12
100005474: d3462129    	ubfx	x9, x9, #6, #3
100005478: 8b090d69    	add	x9, x11, x9, lsl #3
10000547c: f940092b    	ldr	x11, [x9, #0x10]
100005480: 5280002c    	mov	w12, #0x1               ; =1
100005484: 9aca218a    	lsl	x10, x12, x10
100005488: 8a2a016a    	bic	x10, x11, x10
10000548c: f900092a    	str	x10, [x9, #0x10]
100005490: f9543c09    	ldr	x9, [x0, #0x2878]
100005494: f954380a    	ldr	x10, [x0, #0x2870]
100005498: eb0a013f    	cmp	x9, x10
10000549c: 9a8ac129    	csel	x9, x9, x10, gt
1000054a0: f9143c09    	str	x9, [x0, #0x2878]
1000054a4: cb080149    	sub	x9, x10, x8
1000054a8: f9143809    	str	x9, [x0, #0x2870]
1000054ac: aa0103e0    	mov	x0, x1
1000054b0: aa0803e1    	mov	x1, x8
1000054b4: 14001839    	b	0x10000b598 <_strlen+0x10000b598>
1000054b8: 17fffe39    	b	0x100004d9c <_freeBigChunk__system_u6584>

00000001000054bc <_freeDeferredObjects__system_u6765>:
1000054bc: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
1000054c0: a90157f6    	stp	x22, x21, [sp, #0x10]
1000054c4: a9024ff4    	stp	x20, x19, [sp, #0x20]
1000054c8: a9037bfd    	stp	x29, x30, [sp, #0x30]
1000054cc: 9100c3fd    	add	x29, sp, #0x30
1000054d0: aa0003f3    	mov	x19, x0
1000054d4: 52851408    	mov	w8, #0x28a0             ; =10400
1000054d8: 8b080015    	add	x21, x0, x8
1000054dc: 52800296    	mov	w22, #0x14              ; =20
1000054e0: 52800037    	mov	w23, #0x1               ; =1
1000054e4: 72a7e017    	movk	w23, #0x3f00, lsl #16
1000054e8: 52800038    	mov	w24, #0x1               ; =1
1000054ec: f9400c34    	ldr	x20, [x1, #0x18]
1000054f0: f9000c3f    	str	xzr, [x1, #0x18]
1000054f4: f9400428    	ldr	x8, [x1, #0x8]
1000054f8: f9544669    	ldr	x9, [x19, #0x2888]
1000054fc: cb080129    	sub	x9, x9, x8
100005500: f9144669    	str	x9, [x19, #0x2888]
100005504: eb17011f    	cmp	x8, x23
100005508: 540003cb    	b.lt	0x100005580 <_freeDeferredObjects__system_u6765+0xc4>
10000550c: 934cfc29    	asr	x9, x1, #12
100005510: 9355fc2a    	asr	x10, x1, #21
100005514: aa0a03eb    	mov	x11, x10
100005518: d37d1d4b    	ubfiz	x11, x10, #3, #8
10000551c: 8b0b02ab    	add	x11, x21, x11
100005520: f940016b    	ldr	x11, [x11]
100005524: b400016b    	cbz	x11, 0x100005550 <_freeDeferredObjects__system_u6765+0x94>
100005528: f940056c    	ldr	x12, [x11, #0x8]
10000552c: eb0a019f    	cmp	x12, x10
100005530: 54ffff81    	b.ne	0x100005520 <_freeDeferredObjects__system_u6765+0x64>
100005534: d34cfc2a    	lsr	x10, x1, #12
100005538: d3462129    	ubfx	x9, x9, #6, #3
10000553c: 8b090d69    	add	x9, x11, x9, lsl #3
100005540: f940092b    	ldr	x11, [x9, #0x10]
100005544: 9aca230a    	lsl	x10, x24, x10
100005548: 8a2a016a    	bic	x10, x11, x10
10000554c: f900092a    	str	x10, [x9, #0x10]
100005550: f9543e69    	ldr	x9, [x19, #0x2878]
100005554: f9543a6a    	ldr	x10, [x19, #0x2870]
100005558: eb0a013f    	cmp	x9, x10
10000555c: 9a8ac129    	csel	x9, x9, x10, gt
100005560: f9143e69    	str	x9, [x19, #0x2878]
100005564: cb080149    	sub	x9, x10, x8
100005568: f9143a69    	str	x9, [x19, #0x2870]
10000556c: aa0103e0    	mov	x0, x1
100005570: aa0803e1    	mov	x1, x8
100005574: 94001809    	bl	0x10000b598 <_strlen+0x10000b598>
100005578: b50000b6    	cbnz	x22, 0x10000558c <_freeDeferredObjects__system_u6765+0xd0>
10000557c: 14000008    	b	0x10000559c <_freeDeferredObjects__system_u6765+0xe0>
100005580: aa1303e0    	mov	x0, x19
100005584: 97fffe06    	bl	0x100004d9c <_freeBigChunk__system_u6584>
100005588: b40000b6    	cbz	x22, 0x10000559c <_freeDeferredObjects__system_u6765+0xe0>
10000558c: d10006d6    	sub	x22, x22, #0x1
100005590: aa1403e1    	mov	x1, x20
100005594: b5fffad4    	cbnz	x20, 0x1000054ec <_freeDeferredObjects__system_u6765+0x30>
100005598: 14000014    	b	0x1000055e8 <_freeDeferredObjects__system_u6765+0x12c>
10000559c: b4000274    	cbz	x20, 0x1000055e8 <_freeDeferredObjects__system_u6765+0x12c>
1000055a0: 52851308    	mov	w8, #0x2898             ; =10392
1000055a4: 8b080269    	add	x9, x19, x8
1000055a8: f9544e6a    	ldr	x10, [x19, #0x2898]
1000055ac: f9000e8a    	str	x10, [x20, #0x18]
1000055b0: aa0a03e8    	mov	x8, x10
1000055b4: c8a8fd34    	casl	x8, x20, [x9]
1000055b8: eb0a011f    	cmp	x8, x10
1000055bc: 54000160    	b.eq	0x1000055e8 <_freeDeferredObjects__system_u6765+0x12c>
1000055c0: 52851309    	mov	w9, #0x2898             ; =10392
1000055c4: 8b090269    	add	x9, x19, x9
1000055c8: aa1403ea    	mov	x10, x20
1000055cc: f8018d48    	str	x8, [x10, #0x18]!
1000055d0: f9544e6b    	ldr	x11, [x19, #0x2898]
1000055d4: f900014b    	str	x11, [x10]
1000055d8: aa0b03e8    	mov	x8, x11
1000055dc: c8a8fd34    	casl	x8, x20, [x9]
1000055e0: eb0b011f    	cmp	x8, x11
1000055e4: 54ffff21    	b.ne	0x1000055c8 <_freeDeferredObjects__system_u6765+0x10c>
1000055e8: a9437bfd    	ldp	x29, x30, [sp, #0x30]
1000055ec: a9424ff4    	ldp	x20, x19, [sp, #0x20]
1000055f0: a94157f6    	ldp	x22, x21, [sp, #0x10]
1000055f4: a8c45ff8    	ldp	x24, x23, [sp], #0x40
1000055f8: d65f03c0    	ret

00000001000055fc <_getHugeChunk__system_u6628>:
1000055fc: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100005600: a9014ff4    	stp	x20, x19, [sp, #0x10]
100005604: a9027bfd    	stp	x29, x30, [sp, #0x20]
100005608: 910083fd    	add	x29, sp, #0x20
10000560c: aa0103f5    	mov	x21, x1
100005610: aa0003f3    	mov	x19, x0
100005614: d2800000    	mov	x0, #0x0                ; =0
100005618: 52800062    	mov	w2, #0x3                ; =3
10000561c: 52820043    	mov	w3, #0x1002             ; =4098
100005620: 12800004    	mov	w4, #-0x1               ; =-1
100005624: d2800005    	mov	x5, #0x0                ; =0
100005628: 940017d9    	bl	0x10000b58c <_strlen+0x10000b58c>
10000562c: 91000408    	add	x8, x0, #0x1
100005630: f100051f    	cmp	x8, #0x1
100005634: 54000349    	b.ls	0x10000569c <_getHugeChunk__system_u6628+0xa0>
100005638: aa0003f4    	mov	x20, x0
10000563c: f9543a68    	ldr	x8, [x19, #0x2870]
100005640: 8b150108    	add	x8, x8, x21
100005644: f9143a68    	str	x8, [x19, #0x2870]
100005648: a901fc1f    	stp	xzr, xzr, [x0, #0x18]
10000564c: 52800036    	mov	w22, #0x1               ; =1
100005650: a9005416    	stp	x22, x21, [x0]
100005654: f9000813    	str	x19, [x0, #0x10]
100005658: 934cfc15    	asr	x21, x0, #12
10000565c: 52851408    	mov	w8, #0x28a0             ; =10400
100005660: 8b080261    	add	x1, x19, x8
100005664: 9355fc02    	asr	x2, x0, #21
100005668: aa1303e0    	mov	x0, x19
10000566c: 97fffb8e    	bl	0x1000044a4 <_intSetPut__system_u6237>
100005670: d34622a8    	ubfx	x8, x21, #6, #3
100005674: 8b080c08    	add	x8, x0, x8, lsl #3
100005678: f9400909    	ldr	x9, [x8, #0x10]
10000567c: 9ad522ca    	lsl	x10, x22, x21
100005680: aa0a0129    	orr	x9, x9, x10
100005684: f9000909    	str	x9, [x8, #0x10]
100005688: aa1403e0    	mov	x0, x20
10000568c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005690: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100005694: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005698: d65f03c0    	ret
10000569c: 97fffa29    	bl	0x100003f40 <_raiseOutOfMem__system_u5730>

00000001000056a0 <_rawAlloc__system_u6797>:
1000056a0: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
1000056a4: a9014ff4    	stp	x20, x19, [sp, #0x10]
1000056a8: a9027bfd    	stp	x29, x30, [sp, #0x20]
1000056ac: 910083fd    	add	x29, sp, #0x20
1000056b0: aa0003f3    	mov	x19, x0
1000056b4: 91003c28    	add	x8, x1, #0xf
1000056b8: 927ced15    	and	x21, x8, #0xfffffffffffffff0
1000056bc: f13f02bf    	cmp	x21, #0xfc0
1000056c0: 540002ec    	b.gt	0x10000571c <_rawAlloc__system_u6797+0x7c>
1000056c4: 9344feb4    	asr	x20, x21, #4
1000056c8: 9341fea8    	asr	x8, x21, #1
1000056cc: f8686a68    	ldr	x8, [x19, x8]
1000056d0: b40008a8    	cbz	x8, 0x1000057e4 <_rawAlloc__system_u6797+0x144>
1000056d4: f9401500    	ldr	x0, [x8, #0x28]
1000056d8: b4000de0    	cbz	x0, 0x100005894 <_rawAlloc__system_u6797+0x1f4>
1000056dc: f940000a    	ldr	x10, [x0]
1000056e0: f900150a    	str	x10, [x8, #0x28]
1000056e4: 9274cc09    	and	x9, x0, #0xfffffffffffff000
1000056e8: eb09011f    	cmp	x8, x9
1000056ec: 54000080    	b.eq	0x1000056fc <_rawAlloc__system_u6797+0x5c>
1000056f0: f9401d09    	ldr	x9, [x8, #0x38]
1000056f4: d1000529    	sub	x9, x9, #0x1
1000056f8: f9001d09    	str	x9, [x8, #0x38]
1000056fc: aa0803e9    	mov	x9, x8
100005700: b8430d2b    	ldr	w11, [x9, #0x30]!
100005704: 4b15016b    	sub	w11, w11, w21
100005708: b900012b    	str	w11, [x9]
10000570c: b4000d6a    	cbz	x10, 0x1000058b8 <_rawAlloc__system_u6797+0x218>
100005710: eb2bc2bf    	cmp	x21, w11, sxtw
100005714: 54000eec    	b.gt	0x1000058f0 <_rawAlloc__system_u6797+0x250>
100005718: 14000090    	b	0x100005958 <_rawAlloc__system_u6797+0x2b8>
10000571c: aa0103f4    	mov	x20, x1
100005720: 52851308    	mov	w8, #0x2898             ; =10392
100005724: 8b080268    	add	x8, x19, x8
100005728: f83f8101    	swp	xzr, x1, [x8]
10000572c: b4000061    	cbz	x1, 0x100005738 <_rawAlloc__system_u6797+0x98>
100005730: aa1303e0    	mov	x0, x19
100005734: 97ffff62    	bl	0x1000054bc <_freeDeferredObjects__system_u6765>
100005738: 9100c295    	add	x21, x20, #0x30
10000573c: 529ffa28    	mov	w8, #0xffd1             ; =65489
100005740: 72a7dfe8    	movk	w8, #0x3eff, lsl #16
100005744: eb08029f    	cmp	x20, x8
100005748: 5400040b    	b.lt	0x1000057c8 <_rawAlloc__system_u6797+0x128>
10000574c: d2800000    	mov	x0, #0x0                ; =0
100005750: aa1503e1    	mov	x1, x21
100005754: 52800062    	mov	w2, #0x3                ; =3
100005758: 52820043    	mov	w3, #0x1002             ; =4098
10000575c: 12800004    	mov	w4, #-0x1               ; =-1
100005760: d2800005    	mov	x5, #0x0                ; =0
100005764: 9400178a    	bl	0x10000b58c <_strlen+0x10000b58c>
100005768: 91000408    	add	x8, x0, #0x1
10000576c: f100051f    	cmp	x8, #0x1
100005770: 54001029    	b.ls	0x100005974 <_rawAlloc__system_u6797+0x2d4>
100005774: aa0003f4    	mov	x20, x0
100005778: f9543a68    	ldr	x8, [x19, #0x2870]
10000577c: 8b150108    	add	x8, x8, x21
100005780: f9143a68    	str	x8, [x19, #0x2870]
100005784: a901fc1f    	stp	xzr, xzr, [x0, #0x18]
100005788: 52800036    	mov	w22, #0x1               ; =1
10000578c: a9005416    	stp	x22, x21, [x0]
100005790: f9000813    	str	x19, [x0, #0x10]
100005794: 934cfc15    	asr	x21, x0, #12
100005798: 52851408    	mov	w8, #0x28a0             ; =10400
10000579c: 8b080261    	add	x1, x19, x8
1000057a0: 9355fc02    	asr	x2, x0, #21
1000057a4: aa1303e0    	mov	x0, x19
1000057a8: 97fffb3f    	bl	0x1000044a4 <_intSetPut__system_u6237>
1000057ac: d34622a8    	ubfx	x8, x21, #6, #3
1000057b0: 8b080c08    	add	x8, x0, x8, lsl #3
1000057b4: f9400909    	ldr	x9, [x8, #0x10]
1000057b8: 9ad522ca    	lsl	x10, x22, x21
1000057bc: aa0a0129    	orr	x9, x9, x10
1000057c0: f9000909    	str	x9, [x8, #0x10]
1000057c4: 14000005    	b	0x1000057d8 <_rawAlloc__system_u6797+0x138>
1000057c8: aa1303e0    	mov	x0, x19
1000057cc: aa1503e1    	mov	x1, x21
1000057d0: 97fffc4c    	bl	0x100004900 <_getBigChunk__system_u6608>
1000057d4: aa0003f4    	mov	x20, x0
1000057d8: 9100c280    	add	x0, x20, #0x30
1000057dc: f9400695    	ldr	x21, [x20, #0x8]
1000057e0: 1400005e    	b	0x100005958 <_rawAlloc__system_u6797+0x2b8>
1000057e4: aa1303e0    	mov	x0, x19
1000057e8: 52820001    	mov	w1, #0x1000             ; =4096
1000057ec: 97fffc45    	bl	0x100004900 <_getBigChunk__system_u6608>
1000057f0: f9001c1f    	str	xzr, [x0, #0x38]
1000057f4: f9000415    	str	x21, [x0, #0x8]
1000057f8: 5281f808    	mov	w8, #0xfc0              ; =4032
1000057fc: 4b150108    	sub	w8, w8, w21
100005800: 29065408    	stp	w8, w21, [x0, #0x30]
100005804: aa0003e8    	mov	x8, x0
100005808: f8018d1f    	str	xzr, [x8, #0x18]!
10000580c: 8b140e69    	add	x9, x19, x20, lsl #3
100005810: 91200129    	add	x9, x9, #0x800
100005814: a9027c1f    	stp	xzr, xzr, [x0, #0x20]
100005818: f83f8129    	swp	xzr, x9, [x9]
10000581c: f9001409    	str	x9, [x0, #0x28]
100005820: d280000a    	mov	x10, #0x0               ; =0
100005824: b50002a9    	cbnz	x9, 0x100005878 <_rawAlloc__system_u6797+0x1d8>
100005828: b9403009    	ldr	w9, [x0, #0x30]
10000582c: 0b0a0129    	add	w9, w9, w10
100005830: b9003009    	str	w9, [x0, #0x30]
100005834: f954466b    	ldr	x11, [x19, #0x2888]
100005838: cb0a016a    	sub	x10, x11, x10
10000583c: f914466a    	str	x10, [x19, #0x2888]
100005840: eb29c2bf    	cmp	x21, w9, sxtw
100005844: 5400010c    	b.gt	0x100005864 <_rawAlloc__system_u6797+0x1c4>
100005848: d37df289    	lsl	x9, x20, #3
10000584c: f8696a6a    	ldr	x10, [x19, x9]
100005850: f900010a    	str	x10, [x8]
100005854: f8696a68    	ldr	x8, [x19, x9]
100005858: b4000048    	cbz	x8, 0x100005860 <_rawAlloc__system_u6797+0x1c0>
10000585c: f9001100    	str	x0, [x8, #0x20]
100005860: f8347a60    	str	x0, [x19, x20, lsl #3]
100005864: 91010000    	add	x0, x0, #0x40
100005868: 1400003c    	b	0x100005958 <_rawAlloc__system_u6797+0x2b8>
10000586c: 8b15014a    	add	x10, x10, x21
100005870: f9400129    	ldr	x9, [x9]
100005874: b4fffda9    	cbz	x9, 0x100005828 <_rawAlloc__system_u6797+0x188>
100005878: 9274cd2b    	and	x11, x9, #0xfffffffffffff000
10000587c: eb0b001f    	cmp	x0, x11
100005880: 54ffff60    	b.eq	0x10000586c <_rawAlloc__system_u6797+0x1cc>
100005884: f9401c0b    	ldr	x11, [x0, #0x38]
100005888: 9100056b    	add	x11, x11, #0x1
10000588c: f9001c0b    	str	x11, [x0, #0x38]
100005890: 17fffff7    	b	0x10000586c <_rawAlloc__system_u6797+0x1cc>
100005894: b9403509    	ldr	w9, [x8, #0x34]
100005898: 8b09010a    	add	x10, x8, x9
10000589c: 91010140    	add	x0, x10, #0x40
1000058a0: 0b150129    	add	w9, w9, w21
1000058a4: b9003509    	str	w9, [x8, #0x34]
1000058a8: aa0803e9    	mov	x9, x8
1000058ac: b8430d2a    	ldr	w10, [x9, #0x30]!
1000058b0: 4b15014a    	sub	w10, w10, w21
1000058b4: b900012a    	str	w10, [x9]
1000058b8: 8b140e6a    	add	x10, x19, x20, lsl #3
1000058bc: 9120014a    	add	x10, x10, #0x800
1000058c0: f83f814b    	swp	xzr, x11, [x10]
1000058c4: f900150b    	str	x11, [x8, #0x28]
1000058c8: d280000a    	mov	x10, #0x0               ; =0
1000058cc: b50002eb    	cbnz	x11, 0x100005928 <_rawAlloc__system_u6797+0x288>
1000058d0: b940012b    	ldr	w11, [x9]
1000058d4: 0b0a016b    	add	w11, w11, w10
1000058d8: b900012b    	str	w11, [x9]
1000058dc: f9544669    	ldr	x9, [x19, #0x2888]
1000058e0: cb0a0129    	sub	x9, x9, x10
1000058e4: f9144669    	str	x9, [x19, #0x2888]
1000058e8: eb2bc2bf    	cmp	x21, w11, sxtw
1000058ec: 5400036d    	b.le	0x100005958 <_rawAlloc__system_u6797+0x2b8>
1000058f0: f8747a6b    	ldr	x11, [x19, x20, lsl #3]
1000058f4: aa0803e9    	mov	x9, x8
1000058f8: f8418d2a    	ldr	x10, [x9, #0x18]!
1000058fc: eb08017f    	cmp	x11, x8
100005900: 54000220    	b.eq	0x100005944 <_rawAlloc__system_u6797+0x2a4>
100005904: f940110b    	ldr	x11, [x8, #0x20]
100005908: f9000d6a    	str	x10, [x11, #0x18]
10000590c: f9400d0a    	ldr	x10, [x8, #0x18]
100005910: b400022a    	cbz	x10, 0x100005954 <_rawAlloc__system_u6797+0x2b4>
100005914: f9401108    	ldr	x8, [x8, #0x20]
100005918: 1400000e    	b	0x100005950 <_rawAlloc__system_u6797+0x2b0>
10000591c: 8b15014a    	add	x10, x10, x21
100005920: f940016b    	ldr	x11, [x11]
100005924: b4fffd6b    	cbz	x11, 0x1000058d0 <_rawAlloc__system_u6797+0x230>
100005928: 9274cd6c    	and	x12, x11, #0xfffffffffffff000
10000592c: eb0c011f    	cmp	x8, x12
100005930: 54ffff60    	b.eq	0x10000591c <_rawAlloc__system_u6797+0x27c>
100005934: f9401d0c    	ldr	x12, [x8, #0x38]
100005938: 9100058c    	add	x12, x12, #0x1
10000593c: f9001d0c    	str	x12, [x8, #0x38]
100005940: 17fffff7    	b	0x10000591c <_rawAlloc__system_u6797+0x27c>
100005944: f8347a6a    	str	x10, [x19, x20, lsl #3]
100005948: b400006a    	cbz	x10, 0x100005954 <_rawAlloc__system_u6797+0x2b4>
10000594c: d2800008    	mov	x8, #0x0                ; =0
100005950: f9001148    	str	x8, [x10, #0x20]
100005954: a9007d3f    	stp	xzr, xzr, [x9]
100005958: f9544668    	ldr	x8, [x19, #0x2888]
10000595c: 8b150108    	add	x8, x8, x21
100005960: f9144668    	str	x8, [x19, #0x2888]
100005964: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005968: a9414ff4    	ldp	x20, x19, [sp, #0x10]
10000596c: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005970: d65f03c0    	ret
100005974: 97fff973    	bl	0x100003f40 <_raiseOutOfMem__system_u5730>

0000000100005978 <_alloc__system_u7055>:
100005978: 17ffff4a    	b	0x1000056a0 <_rawAlloc__system_u6797>

000000010000597c <_allocImpl__system_u1742>:
10000597c: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100005980: 910003fd    	mov	x29, sp
100005984: aa0003e1    	mov	x1, x0
100005988: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000598c: 91000000    	add	x0, x0, #0x0
100005990: f9400008    	ldr	x8, [x0]
100005994: d63f0100    	blr	x8
100005998: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000599c: 17ffff41    	b	0x1000056a0 <_rawAlloc__system_u6797>

00000001000059a0 <_allocSharedImpl>:
1000059a0: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
1000059a4: 910003fd    	mov	x29, sp
1000059a8: aa0003e1    	mov	x1, x0
1000059ac: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000059b0: 91000000    	add	x0, x0, #0x0
1000059b4: f9400008    	ldr	x8, [x0]
1000059b8: d63f0100    	blr	x8
1000059bc: a8c17bfd    	ldp	x29, x30, [sp], #0x10
1000059c0: 17ffff38    	b	0x1000056a0 <_rawAlloc__system_u6797>

00000001000059c4 <_toNimStr>:
1000059c4: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
1000059c8: a9014ff4    	stp	x20, x19, [sp, #0x10]
1000059cc: a9027bfd    	stp	x29, x30, [sp, #0x20]
1000059d0: 910083fd    	add	x29, sp, #0x20
1000059d4: f100043f    	cmp	x1, #0x1
1000059d8: 540002ab    	b.lt	0x100005a2c <_toNimStr+0x68>
1000059dc: aa0103f3    	mov	x19, x1
1000059e0: aa0003f4    	mov	x20, x0
1000059e4: 91000436    	add	x22, x1, #0x1
1000059e8: 91002421    	add	x1, x1, #0x9
1000059ec: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000059f0: 91000000    	add	x0, x0, #0x0
1000059f4: f9400008    	ldr	x8, [x0]
1000059f8: d63f0100    	blr	x8
1000059fc: 97ffff29    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100005a00: aa0003f5    	mov	x21, x0
100005a04: f8008413    	str	x19, [x0], #0x8
100005a08: aa1403e1    	mov	x1, x20
100005a0c: aa1603e2    	mov	x2, x22
100005a10: 940016dc    	bl	0x10000b580 <_strlen+0x10000b580>
100005a14: aa1303e0    	mov	x0, x19
100005a18: aa1503e1    	mov	x1, x21
100005a1c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005a20: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100005a24: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005a28: d65f03c0    	ret
100005a2c: d2800013    	mov	x19, #0x0               ; =0
100005a30: d2800015    	mov	x21, #0x0               ; =0
100005a34: aa1303e0    	mov	x0, x19
100005a38: aa1503e1    	mov	x1, x21
100005a3c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005a40: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100005a44: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005a48: d65f03c0    	ret

0000000100005a4c <_cstrToNimstr>:
100005a4c: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100005a50: a9014ff4    	stp	x20, x19, [sp, #0x10]
100005a54: a9027bfd    	stp	x29, x30, [sp, #0x20]
100005a58: 910083fd    	add	x29, sp, #0x20
100005a5c: b4000300    	cbz	x0, 0x100005abc <_cstrToNimstr+0x70>
100005a60: aa0003f4    	mov	x20, x0
100005a64: 940016dc    	bl	0x10000b5d4 <_strlen+0x10000b5d4>
100005a68: f100041f    	cmp	x0, #0x1
100005a6c: 5400028b    	b.lt	0x100005abc <_cstrToNimstr+0x70>
100005a70: aa0003f3    	mov	x19, x0
100005a74: 91000416    	add	x22, x0, #0x1
100005a78: 91002401    	add	x1, x0, #0x9
100005a7c: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005a80: 91000000    	add	x0, x0, #0x0
100005a84: f9400008    	ldr	x8, [x0]
100005a88: d63f0100    	blr	x8
100005a8c: 97ffff05    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100005a90: aa0003f5    	mov	x21, x0
100005a94: f8008413    	str	x19, [x0], #0x8
100005a98: aa1403e1    	mov	x1, x20
100005a9c: aa1603e2    	mov	x2, x22
100005aa0: 940016b8    	bl	0x10000b580 <_strlen+0x10000b580>
100005aa4: aa1303e0    	mov	x0, x19
100005aa8: aa1503e1    	mov	x1, x21
100005aac: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005ab0: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100005ab4: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005ab8: d65f03c0    	ret
100005abc: d2800013    	mov	x19, #0x0               ; =0
100005ac0: d2800015    	mov	x21, #0x0               ; =0
100005ac4: aa1303e0    	mov	x0, x19
100005ac8: aa1503e1    	mov	x1, x21
100005acc: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005ad0: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100005ad4: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005ad8: d65f03c0    	ret

0000000100005adc <_rawDealloc__system_u6973>:
100005adc: aa0103e9    	mov	x9, x1
100005ae0: 9274cc21    	and	x1, x1, #0xfffffffffffff000
100005ae4: a940a828    	ldp	x8, x10, [x1, #0x8]
100005ae8: f13f011f    	cmp	x8, #0xfc0
100005aec: 540002ac    	b.gt	0x100005b40 <_rawDealloc__system_u6973+0x64>
100005af0: eb00015f    	cmp	x10, x0
100005af4: 54000500    	b.eq	0x100005b94 <_rawDealloc__system_u6973+0xb8>
100005af8: 91003d0b    	add	x11, x8, #0xf
100005afc: f100011f    	cmp	x8, #0x0
100005b00: 9a88b168    	csel	x8, x11, x8, lt
100005b04: 9344fd08    	asr	x8, x8, #4
100005b08: d37df108    	lsl	x8, x8, #3
100005b0c: 8b08014a    	add	x10, x10, x8
100005b10: f944014b    	ldr	x11, [x10, #0x800]
100005b14: f900012b    	str	x11, [x9]
100005b18: f940082a    	ldr	x10, [x1, #0x10]
100005b1c: 8b08014a    	add	x10, x10, x8
100005b20: 9120014c    	add	x12, x10, #0x800
100005b24: aa0b03ea    	mov	x10, x11
100005b28: c8aafd89    	casl	x10, x9, [x12]
100005b2c: eb0b015f    	cmp	x10, x11
100005b30: 54000300    	b.eq	0x100005b90 <_rawDealloc__system_u6973+0xb4>
100005b34: f900012a    	str	x10, [x9]
100005b38: f940082a    	ldr	x10, [x1, #0x10]
100005b3c: 17fffff4    	b	0x100005b0c <_rawDealloc__system_u6973+0x30>
100005b40: eb00015f    	cmp	x10, x0
100005b44: 540005e0    	b.eq	0x100005c00 <_rawDealloc__system_u6973+0x124>
100005b48: 52851308    	mov	w8, #0x2898             ; =10392
100005b4c: 8b080149    	add	x9, x10, x8
100005b50: f9544d4b    	ldr	x11, [x10, #0x2898]
100005b54: f9000c2b    	str	x11, [x1, #0x18]
100005b58: aa0b03e8    	mov	x8, x11
100005b5c: c8a8fd21    	casl	x8, x1, [x9]
100005b60: eb0b011f    	cmp	x8, x11
100005b64: 54000160    	b.eq	0x100005b90 <_rawDealloc__system_u6973+0xb4>
100005b68: 52851309    	mov	w9, #0x2898             ; =10392
100005b6c: 8b090149    	add	x9, x10, x9
100005b70: aa0103eb    	mov	x11, x1
100005b74: f8018d68    	str	x8, [x11, #0x18]!
100005b78: f9544d4c    	ldr	x12, [x10, #0x2898]
100005b7c: f900016c    	str	x12, [x11]
100005b80: aa0c03e8    	mov	x8, x12
100005b84: c8a8fd21    	casl	x8, x1, [x9]
100005b88: eb0c011f    	cmp	x8, x12
100005b8c: 54ffff21    	b.ne	0x100005b70 <_rawDealloc__system_u6973+0x94>
100005b90: d65f03c0    	ret
100005b94: f954440a    	ldr	x10, [x0, #0x2888]
100005b98: cb08014a    	sub	x10, x10, x8
100005b9c: f914440a    	str	x10, [x0, #0x2888]
100005ba0: 91003d0a    	add	x10, x8, #0xf
100005ba4: f100011f    	cmp	x8, #0x0
100005ba8: 9a88b14a    	csel	x10, x10, x8, lt
100005bac: 9344fd4a    	asr	x10, x10, #4
100005bb0: f86a780b    	ldr	x11, [x0, x10, lsl #3]
100005bb4: f100017f    	cmp	x11, #0x0
100005bb8: fa411164    	ccmp	x11, x1, #0x4, ne
100005bbc: 540006c1    	b.ne	0x100005c94 <_rawDealloc__system_u6973+0x1b8>
100005bc0: f940142b    	ldr	x11, [x1, #0x28]
100005bc4: f900012b    	str	x11, [x9]
100005bc8: f9001429    	str	x9, [x1, #0x28]
100005bcc: b9803029    	ldrsw	x9, [x1, #0x30]
100005bd0: eb09011f    	cmp	x8, x9
100005bd4: 5400076d    	b.le	0x100005cc0 <_rawDealloc__system_u6973+0x1e4>
100005bd8: d37df14b    	lsl	x11, x10, #3
100005bdc: f86b680c    	ldr	x12, [x0, x11]
100005be0: f9000c2c    	str	x12, [x1, #0x18]
100005be4: f86b680b    	ldr	x11, [x0, x11]
100005be8: b400004b    	cbz	x11, 0x100005bf0 <_rawDealloc__system_u6973+0x114>
100005bec: f9001161    	str	x1, [x11, #0x20]
100005bf0: f82a7801    	str	x1, [x0, x10, lsl #3]
100005bf4: 0b080128    	add	w8, w9, w8
100005bf8: b9003028    	str	w8, [x1, #0x30]
100005bfc: d65f03c0    	ret
100005c00: f954440a    	ldr	x10, [x0, #0x2888]
100005c04: cb08014a    	sub	x10, x10, x8
100005c08: f914440a    	str	x10, [x0, #0x2888]
100005c0c: 5280002a    	mov	w10, #0x1               ; =1
100005c10: 72a7e00a    	movk	w10, #0x3f00, lsl #16
100005c14: eb0a011f    	cmp	x8, x10
100005c18: 54000523    	b.lo	0x100005cbc <_rawDealloc__system_u6973+0x1e0>
100005c1c: 934cfd2a    	asr	x10, x9, #12
100005c20: 9355fd2b    	asr	x11, x9, #21
100005c24: aa0b03ec    	mov	x12, x11
100005c28: d37d1d6c    	ubfiz	x12, x11, #3, #8
100005c2c: 5285140d    	mov	w13, #0x28a0            ; =10400
100005c30: 8b0d000d    	add	x13, x0, x13
100005c34: 8b0c01ac    	add	x12, x13, x12
100005c38: f940018c    	ldr	x12, [x12]
100005c3c: b400018c    	cbz	x12, 0x100005c6c <_rawDealloc__system_u6973+0x190>
100005c40: f940058d    	ldr	x13, [x12, #0x8]
100005c44: eb0b01bf    	cmp	x13, x11
100005c48: 54ffff81    	b.ne	0x100005c38 <_rawDealloc__system_u6973+0x15c>
100005c4c: d34cfd29    	lsr	x9, x9, #12
100005c50: d346214a    	ubfx	x10, x10, #6, #3
100005c54: 8b0a0d8a    	add	x10, x12, x10, lsl #3
100005c58: f940094b    	ldr	x11, [x10, #0x10]
100005c5c: 5280002c    	mov	w12, #0x1               ; =1
100005c60: 9ac92189    	lsl	x9, x12, x9
100005c64: 8a290169    	bic	x9, x11, x9
100005c68: f9000949    	str	x9, [x10, #0x10]
100005c6c: f9543c09    	ldr	x9, [x0, #0x2878]
100005c70: f954380a    	ldr	x10, [x0, #0x2870]
100005c74: eb0a013f    	cmp	x9, x10
100005c78: 9a8ac129    	csel	x9, x9, x10, gt
100005c7c: f9143c09    	str	x9, [x0, #0x2878]
100005c80: cb080149    	sub	x9, x10, x8
100005c84: f9143809    	str	x9, [x0, #0x2870]
100005c88: aa0103e0    	mov	x0, x1
100005c8c: aa0803e1    	mov	x1, x8
100005c90: 14001642    	b	0x10000b598 <_strlen+0x10000b598>
100005c94: f940156a    	ldr	x10, [x11, #0x28]
100005c98: f900012a    	str	x10, [x9]
100005c9c: f9001569    	str	x9, [x11, #0x28]
100005ca0: b9403169    	ldr	w9, [x11, #0x30]
100005ca4: 0b080128    	add	w8, w9, w8
100005ca8: b9003168    	str	w8, [x11, #0x30]
100005cac: f9401d68    	ldr	x8, [x11, #0x38]
100005cb0: 91000508    	add	x8, x8, #0x1
100005cb4: f9001d68    	str	x8, [x11, #0x38]
100005cb8: d65f03c0    	ret
100005cbc: 17fffc38    	b	0x100004d9c <_freeBigChunk__system_u6584>
100005cc0: 0b080128    	add	w8, w9, w8
100005cc4: b9003028    	str	w8, [x1, #0x30]
100005cc8: 713f011f    	cmp	w8, #0xfc0
100005ccc: 54fff621    	b.ne	0x100005b90 <_rawDealloc__system_u6973+0xb4>
100005cd0: f9401c28    	ldr	x8, [x1, #0x38]
100005cd4: b5fff5e8    	cbnz	x8, 0x100005b90 <_rawDealloc__system_u6973+0xb4>
100005cd8: f86a780b    	ldr	x11, [x0, x10, lsl #3]
100005cdc: aa0103e8    	mov	x8, x1
100005ce0: f8418d09    	ldr	x9, [x8, #0x18]!
100005ce4: eb01017f    	cmp	x11, x1
100005ce8: 540000e0    	b.eq	0x100005d04 <_rawDealloc__system_u6973+0x228>
100005cec: f940102a    	ldr	x10, [x1, #0x20]
100005cf0: f9000d49    	str	x9, [x10, #0x18]
100005cf4: f9400c29    	ldr	x9, [x1, #0x18]
100005cf8: b40000e9    	cbz	x9, 0x100005d14 <_rawDealloc__system_u6973+0x238>
100005cfc: f940102a    	ldr	x10, [x1, #0x20]
100005d00: 14000004    	b	0x100005d10 <_rawDealloc__system_u6973+0x234>
100005d04: f82a7809    	str	x9, [x0, x10, lsl #3]
100005d08: b4000069    	cbz	x9, 0x100005d14 <_rawDealloc__system_u6973+0x238>
100005d0c: d280000a    	mov	x10, #0x0               ; =0
100005d10: f900112a    	str	x10, [x9, #0x20]
100005d14: a9007d1f    	stp	xzr, xzr, [x8]
100005d18: 52820008    	mov	w8, #0x1000             ; =4096
100005d1c: f9000428    	str	x8, [x1, #0x8]
100005d20: 17fffc1f    	b	0x100004d9c <_freeBigChunk__system_u6584>

0000000100005d24 <_dealloc__system_u7063>:
100005d24: 17ffff6e    	b	0x100005adc <_rawDealloc__system_u6973>

0000000100005d28 <_deallocImpl__system_u1746>:
100005d28: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100005d2c: 910003fd    	mov	x29, sp
100005d30: aa0003e1    	mov	x1, x0
100005d34: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005d38: 91000000    	add	x0, x0, #0x0
100005d3c: f9400008    	ldr	x8, [x0]
100005d40: d63f0100    	blr	x8
100005d44: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100005d48: 17ffff65    	b	0x100005adc <_rawDealloc__system_u6973>

0000000100005d4c <_deallocSharedImpl__system_u1759>:
100005d4c: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100005d50: 910003fd    	mov	x29, sp
100005d54: aa0003e1    	mov	x1, x0
100005d58: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005d5c: 91000000    	add	x0, x0, #0x0
100005d60: f9400008    	ldr	x8, [x0]
100005d64: d63f0100    	blr	x8
100005d68: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100005d6c: 17ffff5c    	b	0x100005adc <_rawDealloc__system_u6973>

0000000100005d70 <_deallocShared>:
100005d70: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100005d74: 910003fd    	mov	x29, sp
100005d78: aa0003e1    	mov	x1, x0
100005d7c: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005d80: 91000000    	add	x0, x0, #0x0
100005d84: f9400008    	ldr	x8, [x0]
100005d88: d63f0100    	blr	x8
100005d8c: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100005d90: 17ffff53    	b	0x100005adc <_rawDealloc__system_u6973>

0000000100005d94 <_unregisterCycle__system_u3071>:
100005d94: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100005d98: 910003fd    	mov	x29, sp
100005d9c: aa0003e8    	mov	x8, x0
100005da0: f9400409    	ldr	x9, [x0, #0x8]
100005da4: d37ced2a    	lsl	x10, x9, #4
100005da8: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005dac: 91006000    	add	x0, x0, #0x18
100005db0: f940000b    	ldr	x11, [x0]
100005db4: d63f0160    	blr	x11
100005db8: f940080b    	ldr	x11, [x0, #0x10]
100005dbc: d100414a    	sub	x10, x10, #0x10
100005dc0: f940000c    	ldr	x12, [x0]
100005dc4: 8b0c116c    	add	x12, x11, x12, lsl #4
100005dc8: 3cdf0180    	ldur	q0, [x12, #-0x10]
100005dcc: 3caa6960    	str	q0, [x11, x10]
100005dd0: f940080b    	ldr	x11, [x0, #0x10]
100005dd4: f86a696a    	ldr	x10, [x11, x10]
100005dd8: f9000549    	str	x9, [x10, #0x8]
100005ddc: f9400009    	ldr	x9, [x0]
100005de0: d1000529    	sub	x9, x9, #0x1
100005de4: f9000009    	str	x9, [x0]
100005de8: f900051f    	str	xzr, [x8, #0x8]
100005dec: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100005df0: d65f03c0    	ret

0000000100005df4 <_init__system_u3309>:
100005df4: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100005df8: a9017bfd    	stp	x29, x30, [sp, #0x10]
100005dfc: 910043fd    	add	x29, sp, #0x10
100005e00: aa0003f3    	mov	x19, x0
100005e04: a900041f    	stp	xzr, x1, [x0]
100005e08: d37cec21    	lsl	x1, x1, #4
100005e0c: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005e10: 91000000    	add	x0, x0, #0x0
100005e14: f9400008    	ldr	x8, [x0]
100005e18: d63f0100    	blr	x8
100005e1c: 97fffe21    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100005e20: f9000a60    	str	x0, [x19, #0x10]
100005e24: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100005e28: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100005e2c: d65f03c0    	ret

0000000100005e30 <_ptrSize__system_u7043>:
100005e30: 9274cc08    	and	x8, x0, #0xfffffffffffff000
100005e34: f9400508    	ldr	x8, [x8, #0x8]
100005e38: d100c109    	sub	x9, x8, #0x30
100005e3c: f13f051f    	cmp	x8, #0xfc1
100005e40: 9a89b100    	csel	x0, x8, x9, lt
100005e44: d65f03c0    	ret

0000000100005e48 <_realloc__system_u7066>:
100005e48: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100005e4c: a9014ff4    	stp	x20, x19, [sp, #0x10]
100005e50: a9027bfd    	stp	x29, x30, [sp, #0x20]
100005e54: 910083fd    	add	x29, sp, #0x20
100005e58: aa0103f3    	mov	x19, x1
100005e5c: aa0003f4    	mov	x20, x0
100005e60: f100045f    	cmp	x2, #0x1
100005e64: 5400024b    	b.lt	0x100005eac <_realloc__system_u7066+0x64>
100005e68: aa0203f6    	mov	x22, x2
100005e6c: aa1403e0    	mov	x0, x20
100005e70: aa0203e1    	mov	x1, x2
100005e74: 97fffe0b    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100005e78: aa0003f5    	mov	x21, x0
100005e7c: b4000233    	cbz	x19, 0x100005ec0 <_realloc__system_u7066+0x78>
100005e80: 9274ce68    	and	x8, x19, #0xfffffffffffff000
100005e84: f9400508    	ldr	x8, [x8, #0x8]
100005e88: d100c109    	sub	x9, x8, #0x30
100005e8c: f13f051f    	cmp	x8, #0xfc1
100005e90: 9a89b108    	csel	x8, x8, x9, lt
100005e94: eb16011f    	cmp	x8, x22
100005e98: 9a96b102    	csel	x2, x8, x22, lt
100005e9c: aa1503e0    	mov	x0, x21
100005ea0: aa1303e1    	mov	x1, x19
100005ea4: 940015b7    	bl	0x10000b580 <_strlen+0x10000b580>
100005ea8: 14000003    	b	0x100005eb4 <_realloc__system_u7066+0x6c>
100005eac: d2800015    	mov	x21, #0x0               ; =0
100005eb0: b4000093    	cbz	x19, 0x100005ec0 <_realloc__system_u7066+0x78>
100005eb4: aa1403e0    	mov	x0, x20
100005eb8: aa1303e1    	mov	x1, x19
100005ebc: 97ffff08    	bl	0x100005adc <_rawDealloc__system_u6973>
100005ec0: aa1503e0    	mov	x0, x21
100005ec4: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005ec8: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100005ecc: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005ed0: d65f03c0    	ret

0000000100005ed4 <_reallocImpl__system_u1748>:
100005ed4: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100005ed8: a9014ff4    	stp	x20, x19, [sp, #0x10]
100005edc: a9027bfd    	stp	x29, x30, [sp, #0x20]
100005ee0: 910083fd    	add	x29, sp, #0x20
100005ee4: aa0103f6    	mov	x22, x1
100005ee8: aa0003f3    	mov	x19, x0
100005eec: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005ef0: 91000000    	add	x0, x0, #0x0
100005ef4: f9400008    	ldr	x8, [x0]
100005ef8: d63f0100    	blr	x8
100005efc: aa0003f4    	mov	x20, x0
100005f00: f100043f    	cmp	x1, #0x1
100005f04: 5400022b    	b.lt	0x100005f48 <_reallocImpl__system_u1748+0x74>
100005f08: aa1403e0    	mov	x0, x20
100005f0c: aa1603e1    	mov	x1, x22
100005f10: 97fffde4    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100005f14: aa0003f5    	mov	x21, x0
100005f18: b4000233    	cbz	x19, 0x100005f5c <_reallocImpl__system_u1748+0x88>
100005f1c: 9274ce68    	and	x8, x19, #0xfffffffffffff000
100005f20: f9400508    	ldr	x8, [x8, #0x8]
100005f24: d100c109    	sub	x9, x8, #0x30
100005f28: f13f051f    	cmp	x8, #0xfc1
100005f2c: 9a89b108    	csel	x8, x8, x9, lt
100005f30: eb16011f    	cmp	x8, x22
100005f34: 9a96b102    	csel	x2, x8, x22, lt
100005f38: aa1503e0    	mov	x0, x21
100005f3c: aa1303e1    	mov	x1, x19
100005f40: 94001590    	bl	0x10000b580 <_strlen+0x10000b580>
100005f44: 14000003    	b	0x100005f50 <_reallocImpl__system_u1748+0x7c>
100005f48: d2800015    	mov	x21, #0x0               ; =0
100005f4c: b4000093    	cbz	x19, 0x100005f5c <_reallocImpl__system_u1748+0x88>
100005f50: aa1403e0    	mov	x0, x20
100005f54: aa1303e1    	mov	x1, x19
100005f58: 97fffee1    	bl	0x100005adc <_rawDealloc__system_u6973>
100005f5c: aa1503e0    	mov	x0, x21
100005f60: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100005f64: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100005f68: a8c357f6    	ldp	x22, x21, [sp], #0x30
100005f6c: d65f03c0    	ret

0000000100005f70 <_reallocSharedImpl__system_u1761>:
100005f70: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100005f74: a9014ff4    	stp	x20, x19, [sp, #0x10]
100005f78: a9027bfd    	stp	x29, x30, [sp, #0x20]
100005f7c: 910083fd    	add	x29, sp, #0x20
100005f80: aa0103f6    	mov	x22, x1
100005f84: aa0003f3    	mov	x19, x0
100005f88: f0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100005f8c: 91000000    	add	x0, x0, #0x0
100005f90: f9400008    	ldr	x8, [x0]
100005f94: d63f0100    	blr	x8
100005f98: aa0003f4    	mov	x20, x0
100005f9c: f100043f    	cmp	x1, #0x1
100005fa0: 5400022b    	b.lt	0x100005fe4 <_reallocSharedImpl__system_u1761+0x74>
100005fa4: aa1403e0    	mov	x0, x20
100005fa8: aa1603e1    	mov	x1, x22
100005fac: 97fffdbd    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100005fb0: aa0003f5    	mov	x21, x0
100005fb4: b4000233    	cbz	x19, 0x100005ff8 <_reallocSharedImpl__system_u1761+0x88>
100005fb8: 9274ce68    	and	x8, x19, #0xfffffffffffff000
100005fbc: f9400508    	ldr	x8, [x8, #0x8]
100005fc0: d100c109    	sub	x9, x8, #0x30
100005fc4: f13f051f    	cmp	x8, #0xfc1
100005fc8: 9a89b108    	csel	x8, x8, x9, lt
100005fcc: eb16011f    	cmp	x8, x22
100005fd0: 9a96b102    	csel	x2, x8, x22, lt
100005fd4: aa1503e0    	mov	x0, x21
100005fd8: aa1303e1    	mov	x1, x19
100005fdc: 94001569    	bl	0x10000b580 <_strlen+0x10000b580>
100005fe0: 14000003    	b	0x100005fec <_reallocSharedImpl__system_u1761+0x7c>
100005fe4: d2800015    	mov	x21, #0x0               ; =0
100005fe8: b4000093    	cbz	x19, 0x100005ff8 <_reallocSharedImpl__system_u1761+0x88>
100005fec: aa1403e0    	mov	x0, x20
100005ff0: aa1303e1    	mov	x1, x19
100005ff4: 97fffeba    	bl	0x100005adc <_rawDealloc__system_u6973>
100005ff8: aa1503e0    	mov	x0, x21
100005ffc: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100006000: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100006004: a8c357f6    	ldp	x22, x21, [sp], #0x30
100006008: d65f03c0    	ret

000000010000600c <_resize__system_u3225>:
10000600c: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
100006010: a90157f6    	stp	x22, x21, [sp, #0x10]
100006014: a9024ff4    	stp	x20, x19, [sp, #0x20]
100006018: a9037bfd    	stp	x29, x30, [sp, #0x30]
10000601c: 9100c3fd    	add	x29, sp, #0x30
100006020: aa0003f3    	mov	x19, x0
100006024: a940d009    	ldp	x9, x20, [x0, #0x8]
100006028: 8b090528    	add	x8, x9, x9, lsl #1
10000602c: f100011f    	cmp	x8, #0x0
100006030: 9a88a508    	cinc	x8, x8, lt
100006034: 9341fd08    	asr	x8, x8, #1
100006038: f9000408    	str	x8, [x0, #0x8]
10000603c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006040: 91000000    	add	x0, x0, #0x0
100006044: f940000a    	ldr	x10, [x0]
100006048: d63f0140    	blr	x10
10000604c: aa0003f5    	mov	x21, x0
100006050: f100053f    	cmp	x9, #0x1
100006054: 5400024b    	b.lt	0x10000609c <_resize__system_u3225+0x90>
100006058: d37ced17    	lsl	x23, x8, #4
10000605c: aa1503e0    	mov	x0, x21
100006060: aa1703e1    	mov	x1, x23
100006064: 97fffd8f    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100006068: aa0003f6    	mov	x22, x0
10000606c: b4000234    	cbz	x20, 0x1000060b0 <_resize__system_u3225+0xa4>
100006070: 9274ce88    	and	x8, x20, #0xfffffffffffff000
100006074: f9400508    	ldr	x8, [x8, #0x8]
100006078: d100c109    	sub	x9, x8, #0x30
10000607c: f13f051f    	cmp	x8, #0xfc1
100006080: 9a89b108    	csel	x8, x8, x9, lt
100006084: eb17011f    	cmp	x8, x23
100006088: 9a97b102    	csel	x2, x8, x23, lt
10000608c: aa1603e0    	mov	x0, x22
100006090: aa1403e1    	mov	x1, x20
100006094: 9400153b    	bl	0x10000b580 <_strlen+0x10000b580>
100006098: 14000003    	b	0x1000060a4 <_resize__system_u3225+0x98>
10000609c: d2800016    	mov	x22, #0x0               ; =0
1000060a0: b4000094    	cbz	x20, 0x1000060b0 <_resize__system_u3225+0xa4>
1000060a4: aa1503e0    	mov	x0, x21
1000060a8: aa1403e1    	mov	x1, x20
1000060ac: 97fffe8c    	bl	0x100005adc <_rawDealloc__system_u6973>
1000060b0: f9000a76    	str	x22, [x19, #0x10]
1000060b4: a9437bfd    	ldp	x29, x30, [sp, #0x30]
1000060b8: a9424ff4    	ldp	x20, x19, [sp, #0x20]
1000060bc: a94157f6    	ldp	x22, x21, [sp, #0x10]
1000060c0: a8c45ff8    	ldp	x24, x23, [sp], #0x40
1000060c4: d65f03c0    	ret

00000001000060c8 <_init__system_u3361>:
1000060c8: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
1000060cc: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000060d0: 910043fd    	add	x29, sp, #0x10
1000060d4: aa0003f3    	mov	x19, x0
1000060d8: a900041f    	stp	xzr, x1, [x0]
1000060dc: d37cec21    	lsl	x1, x1, #4
1000060e0: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000060e4: 91000000    	add	x0, x0, #0x0
1000060e8: f9400008    	ldr	x8, [x0]
1000060ec: d63f0100    	blr	x8
1000060f0: 97fffd6c    	bl	0x1000056a0 <_rawAlloc__system_u6797>
1000060f4: f9000a60    	str	x0, [x19, #0x10]
1000060f8: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000060fc: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100006100: d65f03c0    	ret

0000000100006104 <_pop__system_u3107>:
100006104: f9400808    	ldr	x8, [x0, #0x10]
100006108: f9400009    	ldr	x9, [x0]
10000610c: d1000529    	sub	x9, x9, #0x1
100006110: 8b09110a    	add	x10, x8, x9, lsl #4
100006114: a9400548    	ldp	x8, x1, [x10]
100006118: f9000009    	str	x9, [x0]
10000611c: aa0803e0    	mov	x0, x8
100006120: d65f03c0    	ret

0000000100006124 <_markGray__system_u3128>:
100006124: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100006128: a9017bfd    	stp	x29, x30, [sp, #0x10]
10000612c: 910043fd    	add	x29, sp, #0x10
100006130: aa0203f3    	mov	x19, x2
100006134: aa0003e8    	mov	x8, x0
100006138: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000613c: 91012000    	add	x0, x0, #0x48
100006140: f9400009    	ldr	x9, [x0]
100006144: d63f0120    	blr	x9
100006148: f9400109    	ldr	x9, [x8]
10000614c: 9240052a    	and	x10, x9, #0x3
100006150: f100055f    	cmp	x10, #0x1
100006154: 54000720    	b.eq	0x100006238 <_markGray__system_u3128+0x114>
100006158: aa0003f4    	mov	x20, x0
10000615c: 927ef52a    	and	x10, x9, #0xfffffffffffffffc
100006160: b240014a    	orr	x10, x10, #0x1
100006164: f900010a    	str	x10, [x8]
100006168: f9401e6a    	ldr	x10, [x19, #0x38]
10000616c: 9100054a    	add	x10, x10, #0x1
100006170: f9001e6a    	str	x10, [x19, #0x38]
100006174: f940266a    	ldr	x10, [x19, #0x48]
100006178: 8b891149    	add	x9, x10, x9, asr #4
10000617c: 91000529    	add	x9, x9, #0x1
100006180: f9002669    	str	x9, [x19, #0x48]
100006184: f9401029    	ldr	x9, [x1, #0x20]
100006188: b4000089    	cbz	x9, 0x100006198 <_markGray__system_u3128+0x74>
10000618c: 91004100    	add	x0, x8, #0x10
100006190: aa1303e1    	mov	x1, x19
100006194: d63f0120    	blr	x9
100006198: 39400288    	ldrb	w8, [x20]
10000619c: 350004e8    	cbnz	w8, 0x100006238 <_markGray__system_u3128+0x114>
1000061a0: f9400268    	ldr	x8, [x19]
1000061a4: f100051f    	cmp	x8, #0x1
1000061a8: 540000aa    	b.ge	0x1000061bc <_markGray__system_u3128+0x98>
1000061ac: 14000023    	b	0x100006238 <_markGray__system_u3128+0x114>
1000061b0: f9400268    	ldr	x8, [x19]
1000061b4: f100011f    	cmp	x8, #0x0
1000061b8: 5400040d    	b.le	0x100006238 <_markGray__system_u3128+0x114>
1000061bc: f9400a69    	ldr	x9, [x19, #0x10]
1000061c0: d1000508    	sub	x8, x8, #0x1
1000061c4: 8b081129    	add	x9, x9, x8, lsl #4
1000061c8: a940252a    	ldp	x10, x9, [x9]
1000061cc: f9000268    	str	x8, [x19]
1000061d0: f9400140    	ldr	x0, [x10]
1000061d4: f85f000b    	ldur	x11, [x0, #-0x10]
1000061d8: d100416a    	sub	x10, x11, #0x10
1000061dc: f81f000a    	stur	x10, [x0, #-0x10]
1000061e0: f940226c    	ldr	x12, [x19, #0x40]
1000061e4: 9100058c    	add	x12, x12, #0x1
1000061e8: f900226c    	str	x12, [x19, #0x40]
1000061ec: 9240056b    	and	x11, x11, #0x3
1000061f0: f100057f    	cmp	x11, #0x1
1000061f4: 54fffe00    	b.eq	0x1000061b4 <_markGray__system_u3128+0x90>
1000061f8: 927ef548    	and	x8, x10, #0xfffffffffffffffc
1000061fc: b2400108    	orr	x8, x8, #0x1
100006200: f81f0008    	stur	x8, [x0, #-0x10]
100006204: f9401e68    	ldr	x8, [x19, #0x38]
100006208: 91000508    	add	x8, x8, #0x1
10000620c: f9001e68    	str	x8, [x19, #0x38]
100006210: f9402668    	ldr	x8, [x19, #0x48]
100006214: 8b8a1108    	add	x8, x8, x10, asr #4
100006218: 91000908    	add	x8, x8, #0x2
10000621c: f9002668    	str	x8, [x19, #0x48]
100006220: f9401128    	ldr	x8, [x9, #0x20]
100006224: b4fffc68    	cbz	x8, 0x1000061b0 <_markGray__system_u3128+0x8c>
100006228: aa1303e1    	mov	x1, x19
10000622c: d63f0100    	blr	x8
100006230: 39400288    	ldrb	w8, [x20]
100006234: 34fffbe8    	cbz	w8, 0x1000061b0 <_markGray__system_u3128+0x8c>
100006238: a9417bfd    	ldp	x29, x30, [sp, #0x10]
10000623c: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100006240: d65f03c0    	ret

0000000100006244 <_scanBlack__system_u3099>:
100006244: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100006248: a9014ff4    	stp	x20, x19, [sp, #0x10]
10000624c: a9027bfd    	stp	x29, x30, [sp, #0x20]
100006250: 910083fd    	add	x29, sp, #0x20
100006254: aa0203f3    	mov	x19, x2
100006258: aa0003e8    	mov	x8, x0
10000625c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006260: 91012000    	add	x0, x0, #0x48
100006264: f9400009    	ldr	x9, [x0]
100006268: d63f0120    	blr	x9
10000626c: aa0003f4    	mov	x20, x0
100006270: f9400109    	ldr	x9, [x8]
100006274: 927ef529    	and	x9, x9, #0xfffffffffffffffc
100006278: f9000109    	str	x9, [x8]
10000627c: f9400055    	ldr	x21, [x2]
100006280: f9401029    	ldr	x9, [x1, #0x20]
100006284: b4000089    	cbz	x9, 0x100006294 <_scanBlack__system_u3099+0x50>
100006288: 91004100    	add	x0, x8, #0x10
10000628c: aa1303e1    	mov	x1, x19
100006290: d63f0120    	blr	x9
100006294: 39400288    	ldrb	w8, [x20]
100006298: 350002e8    	cbnz	w8, 0x1000062f4 <_scanBlack__system_u3099+0xb0>
10000629c: f9400268    	ldr	x8, [x19]
1000062a0: eb0802bf    	cmp	x21, x8
1000062a4: 5400028a    	b.ge	0x1000062f4 <_scanBlack__system_u3099+0xb0>
1000062a8: f9400a69    	ldr	x9, [x19, #0x10]
1000062ac: d1000508    	sub	x8, x8, #0x1
1000062b0: 8b081129    	add	x9, x9, x8, lsl #4
1000062b4: a940252a    	ldp	x10, x9, [x9]
1000062b8: f9000268    	str	x8, [x19]
1000062bc: f9400140    	ldr	x0, [x10]
1000062c0: f85f000b    	ldur	x11, [x0, #-0x10]
1000062c4: 9100416a    	add	x10, x11, #0x10
1000062c8: f81f000a    	stur	x10, [x0, #-0x10]
1000062cc: f240057f    	tst	x11, #0x3
1000062d0: 54fffe80    	b.eq	0x1000062a0 <_scanBlack__system_u3099+0x5c>
1000062d4: 927ef548    	and	x8, x10, #0xfffffffffffffffc
1000062d8: f81f0008    	stur	x8, [x0, #-0x10]
1000062dc: f9401128    	ldr	x8, [x9, #0x20]
1000062e0: b4fffde8    	cbz	x8, 0x10000629c <_scanBlack__system_u3099+0x58>
1000062e4: aa1303e1    	mov	x1, x19
1000062e8: d63f0100    	blr	x8
1000062ec: 39400288    	ldrb	w8, [x20]
1000062f0: 34fffd68    	cbz	w8, 0x10000629c <_scanBlack__system_u3099+0x58>
1000062f4: a9427bfd    	ldp	x29, x30, [sp, #0x20]
1000062f8: a9414ff4    	ldp	x20, x19, [sp, #0x10]
1000062fc: a8c357f6    	ldp	x22, x21, [sp], #0x30
100006300: d65f03c0    	ret

0000000100006304 <_scan__system_u3184>:
100006304: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100006308: a9014ff4    	stp	x20, x19, [sp, #0x10]
10000630c: a9027bfd    	stp	x29, x30, [sp, #0x20]
100006310: 910083fd    	add	x29, sp, #0x20
100006314: aa0203f3    	mov	x19, x2
100006318: aa0003e8    	mov	x8, x0
10000631c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006320: 91012000    	add	x0, x0, #0x48
100006324: f9400009    	ldr	x9, [x0]
100006328: d63f0120    	blr	x9
10000632c: f9400109    	ldr	x9, [x8]
100006330: 9240052a    	and	x10, x9, #0x3
100006334: f100055f    	cmp	x10, #0x1
100006338: 54000f41    	b.ne	0x100006520 <_scan__system_u3184+0x21c>
10000633c: aa0003f4    	mov	x20, x0
100006340: 927ef52a    	and	x10, x9, #0xfffffffffffffffc
100006344: b7f80429    	tbnz	x9, #0x3f, 0x1000063c8 <_scan__system_u3184+0xc4>
100006348: f900010a    	str	x10, [x8]
10000634c: f9400275    	ldr	x21, [x19]
100006350: f9401029    	ldr	x9, [x1, #0x20]
100006354: b4000089    	cbz	x9, 0x100006364 <_scan__system_u3184+0x60>
100006358: 91004100    	add	x0, x8, #0x10
10000635c: aa1303e1    	mov	x1, x19
100006360: d63f0120    	blr	x9
100006364: 39400288    	ldrb	w8, [x20]
100006368: 35000dc8    	cbnz	w8, 0x100006520 <_scan__system_u3184+0x21c>
10000636c: f9400268    	ldr	x8, [x19]
100006370: eb0802bf    	cmp	x21, x8
100006374: 54000d6a    	b.ge	0x100006520 <_scan__system_u3184+0x21c>
100006378: f9400a69    	ldr	x9, [x19, #0x10]
10000637c: d1000508    	sub	x8, x8, #0x1
100006380: 8b081129    	add	x9, x9, x8, lsl #4
100006384: a940252a    	ldp	x10, x9, [x9]
100006388: f9000268    	str	x8, [x19]
10000638c: f9400140    	ldr	x0, [x10]
100006390: f85f000b    	ldur	x11, [x0, #-0x10]
100006394: 9100416a    	add	x10, x11, #0x10
100006398: f81f000a    	stur	x10, [x0, #-0x10]
10000639c: f240057f    	tst	x11, #0x3
1000063a0: 54fffe80    	b.eq	0x100006370 <_scan__system_u3184+0x6c>
1000063a4: 927ef548    	and	x8, x10, #0xfffffffffffffffc
1000063a8: f81f0008    	stur	x8, [x0, #-0x10]
1000063ac: f9401128    	ldr	x8, [x9, #0x20]
1000063b0: b4fffde8    	cbz	x8, 0x10000636c <_scan__system_u3184+0x68>
1000063b4: aa1303e1    	mov	x1, x19
1000063b8: d63f0100    	blr	x8
1000063bc: 39400288    	ldrb	w8, [x20]
1000063c0: 34fffd68    	cbz	w8, 0x10000636c <_scan__system_u3184+0x68>
1000063c4: 14000057    	b	0x100006520 <_scan__system_u3184+0x21c>
1000063c8: b27f0149    	orr	x9, x10, #0x2
1000063cc: f9000109    	str	x9, [x8]
1000063d0: f9401029    	ldr	x9, [x1, #0x20]
1000063d4: b4000089    	cbz	x9, 0x1000063e4 <_scan__system_u3184+0xe0>
1000063d8: 91004100    	add	x0, x8, #0x10
1000063dc: aa1303e1    	mov	x1, x19
1000063e0: d63f0120    	blr	x9
1000063e4: 39400288    	ldrb	w8, [x20]
1000063e8: 350009c8    	cbnz	w8, 0x100006520 <_scan__system_u3184+0x21c>
1000063ec: f9400275    	ldr	x21, [x19]
1000063f0: f10006bf    	cmp	x21, #0x1
1000063f4: 5400096b    	b.lt	0x100006520 <_scan__system_u3184+0x21c>
1000063f8: 52800008    	mov	w8, #0x0                ; =0
1000063fc: 14000007    	b	0x100006418 <_scan__system_u3184+0x114>
100006400: f9400269    	ldr	x9, [x19]
100006404: aa0803e0    	mov	x0, x8
100006408: aa0003e8    	mov	x8, x0
10000640c: aa0903f5    	mov	x21, x9
100006410: f100013f    	cmp	x9, #0x0
100006414: 5400086d    	b.le	0x100006520 <_scan__system_u3184+0x21c>
100006418: f9400a6a    	ldr	x10, [x19, #0x10]
10000641c: d10006a9    	sub	x9, x21, #0x1
100006420: 8b09114a    	add	x10, x10, x9, lsl #4
100006424: a940294b    	ldp	x11, x10, [x10]
100006428: f9000269    	str	x9, [x19]
10000642c: f9400160    	ldr	x0, [x11]
100006430: f85f000b    	ldur	x11, [x0, #-0x10]
100006434: 9240056c    	and	x12, x11, #0x3
100006438: f100059f    	cmp	x12, #0x1
10000643c: 54fffe41    	b.ne	0x100006404 <_scan__system_u3184+0x100>
100006440: 927ef569    	and	x9, x11, #0xfffffffffffffffc
100006444: b7f8054b    	tbnz	x11, #0x3f, 0x1000064ec <_scan__system_u3184+0x1e8>
100006448: f81f0009    	stur	x9, [x0, #-0x10]
10000644c: f9401149    	ldr	x9, [x10, #0x20]
100006450: b40000a9    	cbz	x9, 0x100006464 <_scan__system_u3184+0x160>
100006454: aa1303e1    	mov	x1, x19
100006458: d63f0120    	blr	x9
10000645c: 39400288    	ldrb	w8, [x20]
100006460: aa0803e9    	mov	x9, x8
100006464: 350005e9    	cbnz	w9, 0x100006520 <_scan__system_u3184+0x21c>
100006468: f9400269    	ldr	x9, [x19]
10000646c: eb0902bf    	cmp	x21, x9
100006470: 54fffcac    	b.gt	0x100006404 <_scan__system_u3184+0x100>
100006474: f9400a6a    	ldr	x10, [x19, #0x10]
100006478: 8b09114a    	add	x10, x10, x9, lsl #4
10000647c: d100214a    	sub	x10, x10, #0x8
100006480: 14000005    	b	0x100006494 <_scan__system_u3184+0x190>
100006484: d100414a    	sub	x10, x10, #0x10
100006488: 9100052b    	add	x11, x9, #0x1
10000648c: eb0b02bf    	cmp	x21, x11
100006490: 5400040a    	b.ge	0x100006510 <_scan__system_u3184+0x20c>
100006494: d1000529    	sub	x9, x9, #0x1
100006498: a97fad4c    	ldp	x12, x11, [x10, #-0x8]
10000649c: f9400180    	ldr	x0, [x12]
1000064a0: f85f000d    	ldur	x13, [x0, #-0x10]
1000064a4: 910041ac    	add	x12, x13, #0x10
1000064a8: f81f000c    	stur	x12, [x0, #-0x10]
1000064ac: 924005ad    	and	x13, x13, #0x3
1000064b0: b4fffead    	cbz	x13, 0x100006484 <_scan__system_u3184+0x180>
1000064b4: 927ef58c    	and	x12, x12, #0xfffffffffffffffc
1000064b8: f81f000c    	stur	x12, [x0, #-0x10]
1000064bc: f940116b    	ldr	x11, [x11, #0x20]
1000064c0: b4fffe2b    	cbz	x11, 0x100006484 <_scan__system_u3184+0x180>
1000064c4: f9000269    	str	x9, [x19]
1000064c8: aa1303e1    	mov	x1, x19
1000064cc: d63f0160    	blr	x11
1000064d0: 39400288    	ldrb	w8, [x20]
1000064d4: 35000268    	cbnz	w8, 0x100006520 <_scan__system_u3184+0x21c>
1000064d8: 52800000    	mov	w0, #0x0                ; =0
1000064dc: f9400269    	ldr	x9, [x19]
1000064e0: eb0902bf    	cmp	x21, x9
1000064e4: 54fffc8d    	b.le	0x100006474 <_scan__system_u3184+0x170>
1000064e8: 17ffffc8    	b	0x100006408 <_scan__system_u3184+0x104>
1000064ec: b27f0129    	orr	x9, x9, #0x2
1000064f0: f81f0009    	stur	x9, [x0, #-0x10]
1000064f4: f9401149    	ldr	x9, [x10, #0x20]
1000064f8: b4fff849    	cbz	x9, 0x100006400 <_scan__system_u3184+0xfc>
1000064fc: aa1303e1    	mov	x1, x19
100006500: d63f0120    	blr	x9
100006504: 39400288    	ldrb	w8, [x20]
100006508: 34fff7c8    	cbz	w8, 0x100006400 <_scan__system_u3184+0xfc>
10000650c: 14000005    	b	0x100006520 <_scan__system_u3184+0x21c>
100006510: f9000269    	str	x9, [x19]
100006514: 35000068    	cbnz	w8, 0x100006520 <_scan__system_u3184+0x21c>
100006518: 52800000    	mov	w0, #0x0                ; =0
10000651c: 17ffffbb    	b	0x100006408 <_scan__system_u3184+0x104>
100006520: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100006524: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100006528: a8c357f6    	ldp	x22, x21, [sp], #0x30
10000652c: d65f03c0    	ret

0000000100006530 <_collectColor__system_u3209>:
100006530: a9ba6ffc    	stp	x28, x27, [sp, #-0x60]!
100006534: a90167fa    	stp	x26, x25, [sp, #0x10]
100006538: a9025ff8    	stp	x24, x23, [sp, #0x20]
10000653c: a90357f6    	stp	x22, x21, [sp, #0x30]
100006540: a9044ff4    	stp	x20, x19, [sp, #0x40]
100006544: a9057bfd    	stp	x29, x30, [sp, #0x50]
100006548: 910143fd    	add	x29, sp, #0x50
10000654c: aa0303f3    	mov	x19, x3
100006550: aa0203f4    	mov	x20, x2
100006554: aa0103f8    	mov	x24, x1
100006558: aa0003f6    	mov	x22, x0
10000655c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006560: 91012000    	add	x0, x0, #0x48
100006564: f9400008    	ldr	x8, [x0]
100006568: d63f0100    	blr	x8
10000656c: f94002c8    	ldr	x8, [x22]
100006570: 92400509    	and	x9, x8, #0x3
100006574: eb02013f    	cmp	x9, x2
100006578: 54000061    	b.ne	0x100006584 <_collectColor__system_u3209+0x54>
10000657c: f94006c9    	ldr	x9, [x22, #0x8]
100006580: b4000109    	cbz	x9, 0x1000065a0 <_collectColor__system_u3209+0x70>
100006584: a9457bfd    	ldp	x29, x30, [sp, #0x50]
100006588: a9444ff4    	ldp	x20, x19, [sp, #0x40]
10000658c: a94357f6    	ldp	x22, x21, [sp, #0x30]
100006590: a9425ff8    	ldp	x24, x23, [sp, #0x20]
100006594: a94167fa    	ldp	x26, x25, [sp, #0x10]
100006598: a8c66ffc    	ldp	x28, x27, [sp], #0x60
10000659c: d65f03c0    	ret
1000065a0: aa0003f5    	mov	x21, x0
1000065a4: 927ef508    	and	x8, x8, #0xfffffffffffffffc
1000065a8: f90002c8    	str	x8, [x22]
1000065ac: a941a668    	ldp	x8, x9, [x19, #0x18]
1000065b0: d0000057    	adrp	x23, 0x100010000 <_allocator__system_u7104>
1000065b4: 910002f7    	add	x23, x23, #0x0
1000065b8: eb08013f    	cmp	x9, x8
1000065bc: 5400012d    	b.le	0x1000065e0 <_collectColor__system_u3209+0xb0>
1000065c0: f9401679    	ldr	x25, [x19, #0x28]
1000065c4: 8b081329    	add	x9, x25, x8, lsl #4
1000065c8: a9006136    	stp	x22, x24, [x9]
1000065cc: 91000508    	add	x8, x8, #0x1
1000065d0: f9000e68    	str	x8, [x19, #0x18]
1000065d4: f9401308    	ldr	x8, [x24, #0x20]
1000065d8: b5000588    	cbnz	x8, 0x100006688 <_collectColor__system_u3209+0x158>
1000065dc: 1400002e    	b	0x100006694 <_collectColor__system_u3209+0x164>
1000065e0: 8b090528    	add	x8, x9, x9, lsl #1
1000065e4: f100011f    	cmp	x8, #0x0
1000065e8: 9a88a508    	cinc	x8, x8, lt
1000065ec: 9341fd08    	asr	x8, x8, #1
1000065f0: f9001268    	str	x8, [x19, #0x20]
1000065f4: f940167a    	ldr	x26, [x19, #0x28]
1000065f8: f94002ea    	ldr	x10, [x23]
1000065fc: aa1703e0    	mov	x0, x23
100006600: d63f0140    	blr	x10
100006604: aa0003fb    	mov	x27, x0
100006608: f100053f    	cmp	x9, #0x1
10000660c: 5400024b    	b.lt	0x100006654 <_collectColor__system_u3209+0x124>
100006610: d37ced1c    	lsl	x28, x8, #4
100006614: aa1b03e0    	mov	x0, x27
100006618: aa1c03e1    	mov	x1, x28
10000661c: 97fffc21    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100006620: aa0003f9    	mov	x25, x0
100006624: b400023a    	cbz	x26, 0x100006668 <_collectColor__system_u3209+0x138>
100006628: 9274cf48    	and	x8, x26, #0xfffffffffffff000
10000662c: f9400508    	ldr	x8, [x8, #0x8]
100006630: d100c109    	sub	x9, x8, #0x30
100006634: f13f051f    	cmp	x8, #0xfc1
100006638: 9a89b108    	csel	x8, x8, x9, lt
10000663c: eb1c011f    	cmp	x8, x28
100006640: 9a9cb102    	csel	x2, x8, x28, lt
100006644: aa1903e0    	mov	x0, x25
100006648: aa1a03e1    	mov	x1, x26
10000664c: 940013cd    	bl	0x10000b580 <_strlen+0x10000b580>
100006650: 14000003    	b	0x10000665c <_collectColor__system_u3209+0x12c>
100006654: d2800019    	mov	x25, #0x0               ; =0
100006658: b400009a    	cbz	x26, 0x100006668 <_collectColor__system_u3209+0x138>
10000665c: aa1b03e0    	mov	x0, x27
100006660: aa1a03e1    	mov	x1, x26
100006664: 97fffd1e    	bl	0x100005adc <_rawDealloc__system_u6973>
100006668: f9001679    	str	x25, [x19, #0x28]
10000666c: f9400e68    	ldr	x8, [x19, #0x18]
100006670: 8b081329    	add	x9, x25, x8, lsl #4
100006674: a9006136    	stp	x22, x24, [x9]
100006678: 91000508    	add	x8, x8, #0x1
10000667c: f9000e68    	str	x8, [x19, #0x18]
100006680: f9401308    	ldr	x8, [x24, #0x20]
100006684: b4000088    	cbz	x8, 0x100006694 <_collectColor__system_u3209+0x164>
100006688: 910042c0    	add	x0, x22, #0x10
10000668c: aa1303e1    	mov	x1, x19
100006690: d63f0100    	blr	x8
100006694: 394002a8    	ldrb	w8, [x21]
100006698: 35fff768    	cbnz	w8, 0x100006584 <_collectColor__system_u3209+0x54>
10000669c: f9400268    	ldr	x8, [x19]
1000066a0: f100051f    	cmp	x8, #0x1
1000066a4: 54fff70b    	b.lt	0x100006584 <_collectColor__system_u3209+0x54>
1000066a8: f94002e9    	ldr	x9, [x23]
1000066ac: aa1703e0    	mov	x0, x23
1000066b0: d63f0120    	blr	x9
1000066b4: aa0003f6    	mov	x22, x0
1000066b8: 14000006    	b	0x1000066d0 <_collectColor__system_u3209+0x1a0>
1000066bc: 394002a8    	ldrb	w8, [x21]
1000066c0: 35fff628    	cbnz	w8, 0x100006584 <_collectColor__system_u3209+0x54>
1000066c4: f9400268    	ldr	x8, [x19]
1000066c8: f100011f    	cmp	x8, #0x0
1000066cc: 54fff5cd    	b.le	0x100006584 <_collectColor__system_u3209+0x54>
1000066d0: f9400a69    	ldr	x9, [x19, #0x10]
1000066d4: d1000508    	sub	x8, x8, #0x1
1000066d8: 8b081129    	add	x9, x9, x8, lsl #4
1000066dc: a9406d2a    	ldp	x10, x27, [x9]
1000066e0: f9000268    	str	x8, [x19]
1000066e4: f9400157    	ldr	x23, [x10]
1000066e8: aa1703fc    	mov	x28, x23
1000066ec: f85f0f89    	ldr	x9, [x28, #-0x10]!
1000066f0: f900015f    	str	xzr, [x10]
1000066f4: 9240052a    	and	x10, x9, #0x3
1000066f8: eb14015f    	cmp	x10, x20
1000066fc: 54fffe61    	b.ne	0x1000066c8 <_collectColor__system_u3209+0x198>
100006700: f940078a    	ldr	x10, [x28, #0x8]
100006704: b5fffe2a    	cbnz	x10, 0x1000066c8 <_collectColor__system_u3209+0x198>
100006708: a941aa68    	ldp	x8, x10, [x19, #0x18]
10000670c: eb08015f    	cmp	x10, x8
100006710: 5400006d    	b.le	0x10000671c <_collectColor__system_u3209+0x1ec>
100006714: f9401678    	ldr	x24, [x19, #0x28]
100006718: 14000022    	b	0x1000067a0 <_collectColor__system_u3209+0x270>
10000671c: 8b0a0548    	add	x8, x10, x10, lsl #1
100006720: f100011f    	cmp	x8, #0x0
100006724: 9a88a508    	cinc	x8, x8, lt
100006728: 9341fd08    	asr	x8, x8, #1
10000672c: f9001268    	str	x8, [x19, #0x20]
100006730: f9401679    	ldr	x25, [x19, #0x28]
100006734: f100055f    	cmp	x10, #0x1
100006738: 5400024b    	b.lt	0x100006780 <_collectColor__system_u3209+0x250>
10000673c: d37ced1a    	lsl	x26, x8, #4
100006740: aa1603e0    	mov	x0, x22
100006744: aa1a03e1    	mov	x1, x26
100006748: 97fffbd6    	bl	0x1000056a0 <_rawAlloc__system_u6797>
10000674c: aa0003f8    	mov	x24, x0
100006750: b4000239    	cbz	x25, 0x100006794 <_collectColor__system_u3209+0x264>
100006754: 9274cf28    	and	x8, x25, #0xfffffffffffff000
100006758: f9400508    	ldr	x8, [x8, #0x8]
10000675c: d100c109    	sub	x9, x8, #0x30
100006760: f13f051f    	cmp	x8, #0xfc1
100006764: 9a89b108    	csel	x8, x8, x9, lt
100006768: eb1a011f    	cmp	x8, x26
10000676c: 9a9ab102    	csel	x2, x8, x26, lt
100006770: aa1803e0    	mov	x0, x24
100006774: aa1903e1    	mov	x1, x25
100006778: 94001382    	bl	0x10000b580 <_strlen+0x10000b580>
10000677c: 14000003    	b	0x100006788 <_collectColor__system_u3209+0x258>
100006780: d2800018    	mov	x24, #0x0               ; =0
100006784: b4000099    	cbz	x25, 0x100006794 <_collectColor__system_u3209+0x264>
100006788: aa1603e0    	mov	x0, x22
10000678c: aa1903e1    	mov	x1, x25
100006790: 97fffcd3    	bl	0x100005adc <_rawDealloc__system_u6973>
100006794: f9001678    	str	x24, [x19, #0x28]
100006798: f9400e68    	ldr	x8, [x19, #0x18]
10000679c: f9400389    	ldr	x9, [x28]
1000067a0: 8b08130a    	add	x10, x24, x8, lsl #4
1000067a4: a9006d5c    	stp	x28, x27, [x10]
1000067a8: 91000508    	add	x8, x8, #0x1
1000067ac: f9000e68    	str	x8, [x19, #0x18]
1000067b0: 927ef528    	and	x8, x9, #0xfffffffffffffffc
1000067b4: f9000388    	str	x8, [x28]
1000067b8: f9401368    	ldr	x8, [x27, #0x20]
1000067bc: b4fff808    	cbz	x8, 0x1000066bc <_collectColor__system_u3209+0x18c>
1000067c0: aa1703e0    	mov	x0, x23
1000067c4: aa1303e1    	mov	x1, x19
1000067c8: d63f0100    	blr	x8
1000067cc: 17ffffbc    	b	0x1000066bc <_collectColor__system_u3209+0x18c>

00000001000067d0 <_align__system_u1628>:
1000067d0: 8b010008    	add	x8, x0, x1
1000067d4: d1000508    	sub	x8, x8, #0x1
1000067d8: cb0103e9    	neg	x9, x1
1000067dc: 8a090108    	and	x8, x8, x9
1000067e0: f100003f    	cmp	x1, #0x0
1000067e4: 9a880000    	csel	x0, x0, x8, eq
1000067e8: d65f03c0    	ret

00000001000067ec <_alignedDealloc>:
1000067ec: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
1000067f0: 910003fd    	mov	x29, sp
1000067f4: aa0003e8    	mov	x8, x0
1000067f8: f100443f    	cmp	x1, #0x11
1000067fc: 5400006b    	b.lt	0x100006808 <_alignedDealloc+0x1c>
100006800: 785fe109    	ldurh	w9, [x8, #-0x2]
100006804: cb090108    	sub	x8, x8, x9
100006808: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000680c: 91000000    	add	x0, x0, #0x0
100006810: f9400009    	ldr	x9, [x0]
100006814: d63f0120    	blr	x9
100006818: aa0803e1    	mov	x1, x8
10000681c: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100006820: 17fffcaf    	b	0x100005adc <_rawDealloc__system_u6973>

0000000100006824 <_nimRawDispose>:
100006824: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100006828: 910003fd    	mov	x29, sp
10000682c: aa0103e8    	mov	x8, x1
100006830: 91003c29    	add	x9, x1, #0xf
100006834: cb0103ea    	neg	x10, x1
100006838: 8a0a0129    	and	x9, x9, x10
10000683c: 5280020a    	mov	w10, #0x10              ; =16
100006840: f100003f    	cmp	x1, #0x0
100006844: 9a890149    	csel	x9, x10, x9, eq
100006848: cb090001    	sub	x1, x0, x9
10000684c: f100451f    	cmp	x8, #0x11
100006850: 5400006b    	b.lt	0x10000685c <_nimRawDispose+0x38>
100006854: 785fe028    	ldurh	w8, [x1, #-0x2]
100006858: cb080021    	sub	x1, x1, x8
10000685c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006860: 91000000    	add	x0, x0, #0x0
100006864: f9400008    	ldr	x8, [x0]
100006868: d63f0100    	blr	x8
10000686c: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100006870: 17fffc9b    	b	0x100005adc <_rawDealloc__system_u6973>

0000000100006874 <_deinit__system_u3348>:
100006874: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100006878: a9017bfd    	stp	x29, x30, [sp, #0x10]
10000687c: 910043fd    	add	x29, sp, #0x10
100006880: aa0003f3    	mov	x19, x0
100006884: f9400801    	ldr	x1, [x0, #0x10]
100006888: b40000e1    	cbz	x1, 0x1000068a4 <_deinit__system_u3348+0x30>
10000688c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006890: 91000000    	add	x0, x0, #0x0
100006894: f9400008    	ldr	x8, [x0]
100006898: d63f0100    	blr	x8
10000689c: 97fffc90    	bl	0x100005adc <_rawDealloc__system_u6973>
1000068a0: f9000a7f    	str	xzr, [x19, #0x10]
1000068a4: a9007e7f    	stp	xzr, xzr, [x19]
1000068a8: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000068ac: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000068b0: d65f03c0    	ret

00000001000068b4 <_collectCyclesBacon__system_u3281>:
1000068b4: d101c3ff    	sub	sp, sp, #0x70
1000068b8: a9016ffc    	stp	x28, x27, [sp, #0x10]
1000068bc: a90267fa    	stp	x26, x25, [sp, #0x20]
1000068c0: a9035ff8    	stp	x24, x23, [sp, #0x30]
1000068c4: a90457f6    	stp	x22, x21, [sp, #0x40]
1000068c8: a9054ff4    	stp	x20, x19, [sp, #0x50]
1000068cc: a9067bfd    	stp	x29, x30, [sp, #0x60]
1000068d0: 910183fd    	add	x29, sp, #0x60
1000068d4: aa0103f6    	mov	x22, x1
1000068d8: aa0003f3    	mov	x19, x0
1000068dc: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000068e0: 91012000    	add	x0, x0, #0x48
1000068e4: f9400008    	ldr	x8, [x0]
1000068e8: d63f0100    	blr	x8
1000068ec: aa0003f4    	mov	x20, x0
1000068f0: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000068f4: 91006000    	add	x0, x0, #0x18
1000068f8: f9400008    	ldr	x8, [x0]
1000068fc: d63f0100    	blr	x8
100006900: aa0003f5    	mov	x21, x0
100006904: f9400018    	ldr	x24, [x0]
100006908: eb01031f    	cmp	x24, x1
10000690c: 540003ed    	b.le	0x100006988 <_collectCyclesBacon__system_u3281+0xd4>
100006910: d37cef19    	lsl	x25, x24, #4
100006914: aa1903f7    	mov	x23, x25
100006918: aa1803fa    	mov	x26, x24
10000691c: f9400aa8    	ldr	x8, [x21, #0x10]
100006920: 8b170108    	add	x8, x8, x23
100006924: a97f0500    	ldp	x0, x1, [x8, #-0x10]
100006928: aa1303e2    	mov	x2, x19
10000692c: 97fffdfe    	bl	0x100006124 <_markGray__system_u3128>
100006930: 39400288    	ldrb	w8, [x20]
100006934: 35000fa8    	cbnz	w8, 0x100006b28 <_collectCyclesBacon__system_u3281+0x274>
100006938: d100075a    	sub	x26, x26, #0x1
10000693c: d10042f7    	sub	x23, x23, #0x10
100006940: eb16035f    	cmp	x26, x22
100006944: 54fffecc    	b.gt	0x10000691c <_collectCyclesBacon__system_u3281+0x68>
100006948: a9442269    	ldp	x9, x8, [x19, #0x40]
10000694c: eb09011f    	cmp	x8, x9
100006950: 54000220    	b.eq	0x100006994 <_collectCyclesBacon__system_u3281+0xe0>
100006954: 52800057    	mov	w23, #0x2               ; =2
100006958: f9400aa8    	ldr	x8, [x21, #0x10]
10000695c: 8b190108    	add	x8, x8, x25
100006960: a97f0500    	ldp	x0, x1, [x8, #-0x10]
100006964: aa1303e2    	mov	x2, x19
100006968: 97fffe67    	bl	0x100006304 <_scan__system_u3184>
10000696c: 39400288    	ldrb	w8, [x20]
100006970: 35000dc8    	cbnz	w8, 0x100006b28 <_collectCyclesBacon__system_u3281+0x274>
100006974: d1000718    	sub	x24, x24, #0x1
100006978: d1004339    	sub	x25, x25, #0x10
10000697c: eb16031f    	cmp	x24, x22
100006980: 54fffecc    	b.gt	0x100006958 <_collectCyclesBacon__system_u3281+0xa4>
100006984: 14000008    	b	0x1000069a4 <_collectCyclesBacon__system_u3281+0xf0>
100006988: a9442269    	ldp	x9, x8, [x19, #0x40]
10000698c: eb09011f    	cmp	x8, x9
100006990: 54000081    	b.ne	0x1000069a0 <_collectCyclesBacon__system_u3281+0xec>
100006994: 52800037    	mov	w23, #0x1               ; =1
100006998: 39014277    	strb	w23, [x19, #0x50]
10000699c: 14000002    	b	0x1000069a4 <_collectCyclesBacon__system_u3281+0xf0>
1000069a0: 52800057    	mov	w23, #0x2               ; =2
1000069a4: b0000028    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
1000069a8: 3dc1c900    	ldr	q0, [x8, #0x720]
1000069ac: aa1303f8    	mov	x24, x19
1000069b0: 3c818f00    	str	q0, [x24, #0x18]!
1000069b4: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000069b8: 91000000    	add	x0, x0, #0x0
1000069bc: f9400008    	ldr	x8, [x0]
1000069c0: d63f0100    	blr	x8
1000069c4: aa0003f6    	mov	x22, x0
1000069c8: 52851308    	mov	w8, #0x2898             ; =10392
1000069cc: 8b080008    	add	x8, x0, x8
1000069d0: f83f8101    	swp	xzr, x1, [x8]
1000069d4: b4000061    	cbz	x1, 0x1000069e0 <_collectCyclesBacon__system_u3281+0x12c>
1000069d8: aa1603e0    	mov	x0, x22
1000069dc: 97fffab8    	bl	0x1000054bc <_freeDeferredObjects__system_u6765>
1000069e0: aa1603e0    	mov	x0, x22
1000069e4: 52880601    	mov	w1, #0x4030             ; =16432
1000069e8: 97fff7c6    	bl	0x100004900 <_getBigChunk__system_u6608>
1000069ec: d2800008    	mov	x8, #0x0                ; =0
1000069f0: 9100c009    	add	x9, x0, #0x30
1000069f4: f940040a    	ldr	x10, [x0, #0x8]
1000069f8: f95446cb    	ldr	x11, [x22, #0x2888]
1000069fc: 8b0a016a    	add	x10, x11, x10
100006a00: f91446ca    	str	x10, [x22, #0x2888]
100006a04: f9001669    	str	x9, [x19, #0x28]
100006a08: 92800019    	mov	x25, #-0x1              ; =-1
100006a0c: f94002a9    	ldr	x9, [x21]
100006a10: 91000739    	add	x25, x25, #0x1
100006a14: eb09033f    	cmp	x25, x9
100006a18: 540001aa    	b.ge	0x100006a4c <_collectCyclesBacon__system_u3281+0x198>
100006a1c: 9100411a    	add	x26, x8, #0x10
100006a20: f9400aa9    	ldr	x9, [x21, #0x10]
100006a24: 8b080128    	add	x8, x9, x8
100006a28: a9400500    	ldp	x0, x1, [x8]
100006a2c: f900041f    	str	xzr, [x0, #0x8]
100006a30: aa1703e2    	mov	x2, x23
100006a34: aa1303e3    	mov	x3, x19
100006a38: 97fffebe    	bl	0x100006530 <_collectColor__system_u3209>
100006a3c: 39400289    	ldrb	w9, [x20]
100006a40: aa1a03e8    	mov	x8, x26
100006a44: 34fffe49    	cbz	w9, 0x100006a0c <_collectCyclesBacon__system_u3281+0x158>
100006a48: 14000038    	b	0x100006b28 <_collectCyclesBacon__system_u3281+0x274>
100006a4c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006a50: 9100c000    	add	x0, x0, #0x30
100006a54: f9400008    	ldr	x8, [x0]
100006a58: d63f0100    	blr	x8
100006a5c: aa0003f7    	mov	x23, x0
100006a60: f9400008    	ldr	x8, [x0]
100006a64: f90007e8    	str	x8, [sp, #0x8]
100006a68: 92f00008    	mov	x8, #0x7fffffffffffffff ; =9223372036854775807
100006a6c: f9000008    	str	x8, [x0]
100006a70: f90002bf    	str	xzr, [x21]
100006a74: f9400308    	ldr	x8, [x24]
100006a78: f100051f    	cmp	x8, #0x1
100006a7c: 5400040b    	b.lt	0x100006afc <_collectCyclesBacon__system_u3281+0x248>
100006a80: d280001a    	mov	x26, #0x0               ; =0
100006a84: d280001b    	mov	x27, #0x0               ; =0
100006a88: 5280021c    	mov	w28, #0x10              ; =16
100006a8c: f9401668    	ldr	x8, [x19, #0x28]
100006a90: 8b1a0108    	add	x8, x8, x26
100006a94: a9406509    	ldp	x9, x25, [x8]
100006a98: 91004135    	add	x21, x9, #0x10
100006a9c: f9400328    	ldr	x8, [x25]
100006aa0: b40000a8    	cbz	x8, 0x100006ab4 <_collectCyclesBacon__system_u3281+0x200>
100006aa4: aa1503e0    	mov	x0, x21
100006aa8: d63f0100    	blr	x8
100006aac: 39400288    	ldrb	w8, [x20]
100006ab0: 350001c8    	cbnz	w8, 0x100006ae8 <_collectCyclesBacon__system_u3281+0x234>
100006ab4: 79802328    	ldrsh	x8, [x25, #0x10]
100006ab8: 91003d09    	add	x9, x8, #0xf
100006abc: cb0803ea    	neg	x10, x8
100006ac0: 8a0a0129    	and	x9, x9, x10
100006ac4: 7100011f    	cmp	w8, #0x0
100006ac8: 9a890389    	csel	x9, x28, x9, eq
100006acc: cb0902a1    	sub	x1, x21, x9
100006ad0: f100451f    	cmp	x8, #0x11
100006ad4: 5400006b    	b.lt	0x100006ae0 <_collectCyclesBacon__system_u3281+0x22c>
100006ad8: 785fe028    	ldurh	w8, [x1, #-0x2]
100006adc: cb080021    	sub	x1, x1, x8
100006ae0: aa1603e0    	mov	x0, x22
100006ae4: 97fffbfe    	bl	0x100005adc <_rawDealloc__system_u6973>
100006ae8: 9100077b    	add	x27, x27, #0x1
100006aec: f9400308    	ldr	x8, [x24]
100006af0: 9100435a    	add	x26, x26, #0x10
100006af4: eb08037f    	cmp	x27, x8
100006af8: 54fffcab    	b.lt	0x100006a8c <_collectCyclesBacon__system_u3281+0x1d8>
100006afc: f94007e8    	ldr	x8, [sp, #0x8]
100006b00: f90002e8    	str	x8, [x23]
100006b04: f9400e68    	ldr	x8, [x19, #0x18]
100006b08: a942a661    	ldp	x1, x9, [x19, #0x28]
100006b0c: 8b080128    	add	x8, x9, x8
100006b10: f9001a68    	str	x8, [x19, #0x30]
100006b14: b4000081    	cbz	x1, 0x100006b24 <_collectCyclesBacon__system_u3281+0x270>
100006b18: aa1603e0    	mov	x0, x22
100006b1c: 97fffbf0    	bl	0x100005adc <_rawDealloc__system_u6973>
100006b20: f900167f    	str	xzr, [x19, #0x28]
100006b24: a9007f1f    	stp	xzr, xzr, [x24]
100006b28: a9467bfd    	ldp	x29, x30, [sp, #0x60]
100006b2c: a9454ff4    	ldp	x20, x19, [sp, #0x50]
100006b30: a94457f6    	ldp	x22, x21, [sp, #0x40]
100006b34: a9435ff8    	ldp	x24, x23, [sp, #0x30]
100006b38: a94267fa    	ldp	x26, x25, [sp, #0x20]
100006b3c: a9416ffc    	ldp	x28, x27, [sp, #0x10]
100006b40: 9101c3ff    	add	sp, sp, #0x70
100006b44: d65f03c0    	ret

0000000100006b48 <_deinit__system_u3373>:
100006b48: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100006b4c: a9017bfd    	stp	x29, x30, [sp, #0x10]
100006b50: 910043fd    	add	x29, sp, #0x10
100006b54: aa0003f3    	mov	x19, x0
100006b58: f9400801    	ldr	x1, [x0, #0x10]
100006b5c: b40000e1    	cbz	x1, 0x100006b78 <_deinit__system_u3373+0x30>
100006b60: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006b64: 91000000    	add	x0, x0, #0x0
100006b68: f9400008    	ldr	x8, [x0]
100006b6c: d63f0100    	blr	x8
100006b70: 97fffbdb    	bl	0x100005adc <_rawDealloc__system_u6973>
100006b74: f9000a7f    	str	xzr, [x19, #0x10]
100006b78: a9007e7f    	stp	xzr, xzr, [x19]
100006b7c: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100006b80: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100006b84: d65f03c0    	ret

0000000100006b88 <_collectCycles__system_u3409>:
100006b88: d10203ff    	sub	sp, sp, #0x80
100006b8c: a9064ff4    	stp	x20, x19, [sp, #0x60]
100006b90: a9077bfd    	stp	x29, x30, [sp, #0x70]
100006b94: 9101c3fd    	add	x29, sp, #0x70
100006b98: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006b9c: 91012000    	add	x0, x0, #0x48
100006ba0: f9400008    	ldr	x8, [x0]
100006ba4: d63f0100    	blr	x8
100006ba8: aa0003f4    	mov	x20, x0
100006bac: 6f00e400    	movi.2d	v0, #0000000000000000
100006bb0: f9002bff    	str	xzr, [sp, #0x50]
100006bb4: ad0183e0    	stp	q0, q0, [sp, #0x30]
100006bb8: ad0083e0    	stp	q0, q0, [sp, #0x10]
100006bbc: 3d8003e0    	str	q0, [sp]
100006bc0: 52808008    	mov	w8, #0x400              ; =1024
100006bc4: f90007e8    	str	x8, [sp, #0x8]
100006bc8: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006bcc: 91000000    	add	x0, x0, #0x0
100006bd0: f9400008    	ldr	x8, [x0]
100006bd4: d63f0100    	blr	x8
100006bd8: aa0003f3    	mov	x19, x0
100006bdc: 52851308    	mov	w8, #0x2898             ; =10392
100006be0: 8b080008    	add	x8, x0, x8
100006be4: f83f8101    	swp	xzr, x1, [x8]
100006be8: b4000061    	cbz	x1, 0x100006bf4 <_collectCycles__system_u3409+0x6c>
100006bec: aa1303e0    	mov	x0, x19
100006bf0: 97fffa33    	bl	0x1000054bc <_freeDeferredObjects__system_u6765>
100006bf4: aa1303e0    	mov	x0, x19
100006bf8: 52880601    	mov	w1, #0x4030             ; =16432
100006bfc: 97fff741    	bl	0x100004900 <_getBigChunk__system_u6608>
100006c00: 9100c008    	add	x8, x0, #0x30
100006c04: f9400409    	ldr	x9, [x0, #0x8]
100006c08: f954466a    	ldr	x10, [x19, #0x2888]
100006c0c: 8b090149    	add	x9, x10, x9
100006c10: f9144669    	str	x9, [x19, #0x2888]
100006c14: f9000be8    	str	x8, [sp, #0x10]
100006c18: 910003e0    	mov	x0, sp
100006c1c: d2800001    	mov	x1, #0x0                ; =0
100006c20: 97ffff25    	bl	0x1000068b4 <_collectCyclesBacon__system_u3281>
100006c24: 39400288    	ldrb	w8, [x20]
100006c28: 350001e8    	cbnz	w8, 0x100006c64 <_collectCycles__system_u3409+0xdc>
100006c2c: f9400be1    	ldr	x1, [sp, #0x10]
100006c30: b4000081    	cbz	x1, 0x100006c40 <_collectCycles__system_u3409+0xb8>
100006c34: aa1303e0    	mov	x0, x19
100006c38: 97fffba9    	bl	0x100005adc <_rawDealloc__system_u6973>
100006c3c: f9000bff    	str	xzr, [sp, #0x10]
100006c40: a9007fff    	stp	xzr, xzr, [sp]
100006c44: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006c48: 91006000    	add	x0, x0, #0x18
100006c4c: f9400008    	ldr	x8, [x0]
100006c50: d63f0100    	blr	x8
100006c54: f9400008    	ldr	x8, [x0]
100006c58: b40000e8    	cbz	x8, 0x100006c74 <_collectCycles__system_u3409+0xec>
100006c5c: 394143e8    	ldrb	w8, [sp, #0x50]
100006c60: 340001c8    	cbz	w8, 0x100006c98 <_collectCycles__system_u3409+0x110>
100006c64: a9477bfd    	ldp	x29, x30, [sp, #0x70]
100006c68: a9464ff4    	ldp	x20, x19, [sp, #0x60]
100006c6c: 910203ff    	add	sp, sp, #0x80
100006c70: d65f03c0    	ret
100006c74: aa0003f4    	mov	x20, x0
100006c78: f9400801    	ldr	x1, [x0, #0x10]
100006c7c: b4000081    	cbz	x1, 0x100006c8c <_collectCycles__system_u3409+0x104>
100006c80: aa1303e0    	mov	x0, x19
100006c84: 97fffb96    	bl	0x100005adc <_rawDealloc__system_u6973>
100006c88: f9000a9f    	str	xzr, [x20, #0x10]
100006c8c: a9007e9f    	stp	xzr, xzr, [x20]
100006c90: 394143e8    	ldrb	w8, [sp, #0x50]
100006c94: 35fffe88    	cbnz	w8, 0x100006c64 <_collectCycles__system_u3409+0xdc>
100006c98: a94327ea    	ldp	x10, x9, [sp, #0x30]
100006c9c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006ca0: 9100c000    	add	x0, x0, #0x30
100006ca4: f9400008    	ldr	x8, [x0]
100006ca8: d63f0100    	blr	x8
100006cac: f9400008    	ldr	x8, [x0]
100006cb0: eb0a053f    	cmp	x9, x10, lsl #1
100006cb4: 540001cd    	b.le	0x100006cec <_collectCycles__system_u3409+0x164>
100006cb8: b27fefe9    	mov	x9, #0x1ffffffffffffffe ; =2305843009213693950
100006cbc: eb09011f    	cmp	x8, x9
100006cc0: 54fffd2c    	b.gt	0x100006c64 <_collectCycles__system_u3409+0xdc>
100006cc4: 8b080509    	add	x9, x8, x8, lsl #1
100006cc8: d341fd29    	lsr	x9, x9, #1
100006ccc: 5280180a    	mov	w10, #0xc0              ; =192
100006cd0: f100051f    	cmp	x8, #0x1
100006cd4: 9a89b148    	csel	x8, x10, x9, lt
100006cd8: f9000008    	str	x8, [x0]
100006cdc: a9477bfd    	ldp	x29, x30, [sp, #0x70]
100006ce0: a9464ff4    	ldp	x20, x19, [sp, #0x60]
100006ce4: 910203ff    	add	sp, sp, #0x80
100006ce8: d65f03c0    	ret
100006cec: f100611f    	cmp	x8, #0x18
100006cf0: 5400014b    	b.lt	0x100006d18 <_collectCycles__system_u3409+0x190>
100006cf4: b201f3e9    	mov	x9, #-0x5555555555555556 ; =-6148914691236517206
100006cf8: f2955569    	movk	x9, #0xaaab
100006cfc: 9bc97d08    	umulh	x8, x8, x9
100006d00: 927ff908    	and	x8, x8, #0xfffffffffffffffe
100006d04: f9000008    	str	x8, [x0]
100006d08: a9477bfd    	ldp	x29, x30, [sp, #0x70]
100006d0c: a9464ff4    	ldp	x20, x19, [sp, #0x60]
100006d10: 910203ff    	add	sp, sp, #0x80
100006d14: d65f03c0    	ret
100006d18: 52800208    	mov	w8, #0x10               ; =16
100006d1c: f9000008    	str	x8, [x0]
100006d20: a9477bfd    	ldp	x29, x30, [sp, #0x70]
100006d24: a9464ff4    	ldp	x20, x19, [sp, #0x60]
100006d28: 910203ff    	add	sp, sp, #0x80
100006d2c: d65f03c0    	ret

0000000100006d30 <_registerCycle__system_u3434>:
100006d30: a9bb67fa    	stp	x26, x25, [sp, #-0x50]!
100006d34: a9015ff8    	stp	x24, x23, [sp, #0x10]
100006d38: a90257f6    	stp	x22, x21, [sp, #0x20]
100006d3c: a9034ff4    	stp	x20, x19, [sp, #0x30]
100006d40: a9047bfd    	stp	x29, x30, [sp, #0x40]
100006d44: 910103fd    	add	x29, sp, #0x40
100006d48: aa0103f3    	mov	x19, x1
100006d4c: aa0003f4    	mov	x20, x0
100006d50: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006d54: 91006000    	add	x0, x0, #0x18
100006d58: f9400008    	ldr	x8, [x0]
100006d5c: d63f0100    	blr	x8
100006d60: aa0003f5    	mov	x21, x0
100006d64: f9400008    	ldr	x8, [x0]
100006d68: 91000509    	add	x9, x8, #0x1
100006d6c: f9000689    	str	x9, [x20, #0x8]
100006d70: f9400816    	ldr	x22, [x0, #0x10]
100006d74: b40000b6    	cbz	x22, 0x100006d88 <_registerCycle__system_u3434+0x58>
100006d78: f94006a9    	ldr	x9, [x21, #0x8]
100006d7c: eb08013f    	cmp	x9, x8
100006d80: 5400038d    	b.le	0x100006df0 <_registerCycle__system_u3434+0xc0>
100006d84: 1400003d    	b	0x100006e78 <_registerCycle__system_u3434+0x148>
100006d88: b0000028    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100006d8c: 3dc1c900    	ldr	q0, [x8, #0x720]
100006d90: 3d8002a0    	str	q0, [x21]
100006d94: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006d98: 91000000    	add	x0, x0, #0x0
100006d9c: f9400008    	ldr	x8, [x0]
100006da0: d63f0100    	blr	x8
100006da4: aa0003f7    	mov	x23, x0
100006da8: 52851308    	mov	w8, #0x2898             ; =10392
100006dac: 8b080008    	add	x8, x0, x8
100006db0: f83f8101    	swp	xzr, x1, [x8]
100006db4: b4000061    	cbz	x1, 0x100006dc0 <_registerCycle__system_u3434+0x90>
100006db8: aa1703e0    	mov	x0, x23
100006dbc: 97fff9c0    	bl	0x1000054bc <_freeDeferredObjects__system_u6765>
100006dc0: aa1703e0    	mov	x0, x23
100006dc4: 52880601    	mov	w1, #0x4030             ; =16432
100006dc8: 97fff6ce    	bl	0x100004900 <_getBigChunk__system_u6608>
100006dcc: 9100c016    	add	x22, x0, #0x30
100006dd0: f9400408    	ldr	x8, [x0, #0x8]
100006dd4: f95446e9    	ldr	x9, [x23, #0x2888]
100006dd8: 8b080128    	add	x8, x9, x8
100006ddc: f91446e8    	str	x8, [x23, #0x2888]
100006de0: f9000ab6    	str	x22, [x21, #0x10]
100006de4: a94026a8    	ldp	x8, x9, [x21]
100006de8: eb08013f    	cmp	x9, x8
100006dec: 5400046c    	b.gt	0x100006e78 <_registerCycle__system_u3434+0x148>
100006df0: 8b090528    	add	x8, x9, x9, lsl #1
100006df4: f100011f    	cmp	x8, #0x0
100006df8: 9a88a508    	cinc	x8, x8, lt
100006dfc: 9341fd08    	asr	x8, x8, #1
100006e00: f90006a8    	str	x8, [x21, #0x8]
100006e04: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006e08: 91000000    	add	x0, x0, #0x0
100006e0c: f940000a    	ldr	x10, [x0]
100006e10: d63f0140    	blr	x10
100006e14: aa0003f7    	mov	x23, x0
100006e18: f100053f    	cmp	x9, #0x1
100006e1c: 5400020b    	b.lt	0x100006e5c <_registerCycle__system_u3434+0x12c>
100006e20: d37ced19    	lsl	x25, x8, #4
100006e24: aa1703e0    	mov	x0, x23
100006e28: aa1903e1    	mov	x1, x25
100006e2c: 97fffa1d    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100006e30: aa0003f8    	mov	x24, x0
100006e34: 9274cec8    	and	x8, x22, #0xfffffffffffff000
100006e38: f9400508    	ldr	x8, [x8, #0x8]
100006e3c: d100c109    	sub	x9, x8, #0x30
100006e40: f13f051f    	cmp	x8, #0xfc1
100006e44: 9a89b108    	csel	x8, x8, x9, lt
100006e48: eb19011f    	cmp	x8, x25
100006e4c: 9a99b102    	csel	x2, x8, x25, lt
100006e50: aa1603e1    	mov	x1, x22
100006e54: 940011cb    	bl	0x10000b580 <_strlen+0x10000b580>
100006e58: 14000002    	b	0x100006e60 <_registerCycle__system_u3434+0x130>
100006e5c: d2800018    	mov	x24, #0x0               ; =0
100006e60: aa1703e0    	mov	x0, x23
100006e64: aa1603e1    	mov	x1, x22
100006e68: 97fffb1d    	bl	0x100005adc <_rawDealloc__system_u6973>
100006e6c: f9000ab8    	str	x24, [x21, #0x10]
100006e70: f94002a8    	ldr	x8, [x21]
100006e74: aa1803f6    	mov	x22, x24
100006e78: 8b0812c9    	add	x9, x22, x8, lsl #4
100006e7c: a9004d34    	stp	x20, x19, [x9]
100006e80: 91000509    	add	x9, x8, #0x1
100006e84: f90002a9    	str	x9, [x21]
100006e88: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006e8c: 9100c000    	add	x0, x0, #0x30
100006e90: f9400009    	ldr	x9, [x0]
100006e94: d63f0120    	blr	x9
100006e98: f9400009    	ldr	x9, [x0]
100006e9c: d101fd08    	sub	x8, x8, #0x7f
100006ea0: eb08013f    	cmp	x9, x8
100006ea4: 540000ed    	b.le	0x100006ec0 <_registerCycle__system_u3434+0x190>
100006ea8: a9447bfd    	ldp	x29, x30, [sp, #0x40]
100006eac: a9434ff4    	ldp	x20, x19, [sp, #0x30]
100006eb0: a94257f6    	ldp	x22, x21, [sp, #0x20]
100006eb4: a9415ff8    	ldp	x24, x23, [sp, #0x10]
100006eb8: a8c567fa    	ldp	x26, x25, [sp], #0x50
100006ebc: d65f03c0    	ret
100006ec0: a9447bfd    	ldp	x29, x30, [sp, #0x40]
100006ec4: a9434ff4    	ldp	x20, x19, [sp, #0x30]
100006ec8: a94257f6    	ldp	x22, x21, [sp, #0x20]
100006ecc: a9415ff8    	ldp	x24, x23, [sp, #0x10]
100006ed0: a8c567fa    	ldp	x26, x25, [sp], #0x50
100006ed4: 17ffff2d    	b	0x100006b88 <_collectCycles__system_u3409>

0000000100006ed8 <_rememberCycle__system_u3474>:
100006ed8: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100006edc: 910003fd    	mov	x29, sp
100006ee0: f9400428    	ldr	x8, [x1, #0x8]
100006ee4: 340002e0    	cbz	w0, 0x100006f40 <_rememberCycle__system_u3474+0x68>
100006ee8: f100051f    	cmp	x8, #0x1
100006eec: 540003eb    	b.lt	0x100006f68 <_rememberCycle__system_u3474+0x90>
100006ef0: d37ced09    	lsl	x9, x8, #4
100006ef4: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006ef8: 91006000    	add	x0, x0, #0x18
100006efc: f940000a    	ldr	x10, [x0]
100006f00: d63f0140    	blr	x10
100006f04: f940080a    	ldr	x10, [x0, #0x10]
100006f08: d1004129    	sub	x9, x9, #0x10
100006f0c: f940000b    	ldr	x11, [x0]
100006f10: 8b0b114b    	add	x11, x10, x11, lsl #4
100006f14: 3cdf0160    	ldur	q0, [x11, #-0x10]
100006f18: 3ca96940    	str	q0, [x10, x9]
100006f1c: f940080a    	ldr	x10, [x0, #0x10]
100006f20: f8696949    	ldr	x9, [x10, x9]
100006f24: f9000528    	str	x8, [x9, #0x8]
100006f28: f9400008    	ldr	x8, [x0]
100006f2c: d1000508    	sub	x8, x8, #0x1
100006f30: f9000008    	str	x8, [x0]
100006f34: f900043f    	str	xzr, [x1, #0x8]
100006f38: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100006f3c: d65f03c0    	ret
100006f40: b5000148    	cbnz	x8, 0x100006f68 <_rememberCycle__system_u3474+0x90>
100006f44: 3940c048    	ldrb	w8, [x2, #0x30]
100006f48: 37000108    	tbnz	w8, #0x0, 0x100006f68 <_rememberCycle__system_u3474+0x90>
100006f4c: f9400028    	ldr	x8, [x1]
100006f50: 927ef508    	and	x8, x8, #0xfffffffffffffffc
100006f54: f9000028    	str	x8, [x1]
100006f58: aa0103e0    	mov	x0, x1
100006f5c: aa0203e1    	mov	x1, x2
100006f60: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100006f64: 17ffff73    	b	0x100006d30 <_registerCycle__system_u3434>
100006f68: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100006f6c: d65f03c0    	ret

0000000100006f70 <_nimDestroyAndDispose>:
100006f70: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100006f74: a9017bfd    	stp	x29, x30, [sp, #0x10]
100006f78: 910043fd    	add	x29, sp, #0x10
100006f7c: aa0003f3    	mov	x19, x0
100006f80: f9400008    	ldr	x8, [x0]
100006f84: f9400109    	ldr	x9, [x8]
100006f88: b4000169    	cbz	x9, 0x100006fb4 <_nimDestroyAndDispose+0x44>
100006f8c: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006f90: 91012000    	add	x0, x0, #0x48
100006f94: f9400008    	ldr	x8, [x0]
100006f98: d63f0100    	blr	x8
100006f9c: aa0003f4    	mov	x20, x0
100006fa0: aa1303e0    	mov	x0, x19
100006fa4: d63f0120    	blr	x9
100006fa8: 39400288    	ldrb	w8, [x20]
100006fac: 350002a8    	cbnz	w8, 0x100007000 <_nimDestroyAndDispose+0x90>
100006fb0: f9400268    	ldr	x8, [x19]
100006fb4: 79802108    	ldrsh	x8, [x8, #0x10]
100006fb8: 91003d09    	add	x9, x8, #0xf
100006fbc: cb0803ea    	neg	x10, x8
100006fc0: 8a0a0129    	and	x9, x9, x10
100006fc4: 7100011f    	cmp	w8, #0x0
100006fc8: 5280020a    	mov	w10, #0x10              ; =16
100006fcc: 9a890149    	csel	x9, x10, x9, eq
100006fd0: cb090261    	sub	x1, x19, x9
100006fd4: f100451f    	cmp	x8, #0x11
100006fd8: 5400006b    	b.lt	0x100006fe4 <_nimDestroyAndDispose+0x74>
100006fdc: 785fe028    	ldurh	w8, [x1, #-0x2]
100006fe0: cb080021    	sub	x1, x1, x8
100006fe4: d0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100006fe8: 91000000    	add	x0, x0, #0x0
100006fec: f9400008    	ldr	x8, [x0]
100006ff0: d63f0100    	blr	x8
100006ff4: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100006ff8: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100006ffc: 17fffab8    	b	0x100005adc <_rawDealloc__system_u6973>
100007000: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100007004: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100007008: d65f03c0    	ret

000000010000700c <_eqcopy___stdZtypedthreads_u223>:
10000700c: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100007010: a9017bfd    	stp	x29, x30, [sp, #0x10]
100007014: 910043fd    	add	x29, sp, #0x10
100007018: f9400013    	ldr	x19, [x0]
10000701c: b4000081    	cbz	x1, 0x10000702c <_eqcopy___stdZtypedthreads_u223+0x20>
100007020: f85f0028    	ldur	x8, [x1, #-0x10]
100007024: 91004108    	add	x8, x8, #0x10
100007028: f81f0028    	stur	x8, [x1, #-0x10]
10000702c: f9000001    	str	x1, [x0]
100007030: b4000513    	cbz	x19, 0x1000070d0 <_eqcopy___stdZtypedthreads_u223+0xc4>
100007034: aa1303e1    	mov	x1, x19
100007038: f85f0c28    	ldr	x8, [x1, #-0x10]!
10000703c: f1004108    	subs	x8, x8, #0x10
100007040: 540004e2    	b.hs	0x1000070dc <_eqcopy___stdZtypedthreads_u223+0xd0>
100007044: f9400262    	ldr	x2, [x19]
100007048: 52800020    	mov	w0, #0x1                ; =1
10000704c: 97ffffa3    	bl	0x100006ed8 <_rememberCycle__system_u3474>
100007050: f9400268    	ldr	x8, [x19]
100007054: f9400109    	ldr	x9, [x8]
100007058: b4000169    	cbz	x9, 0x100007084 <_eqcopy___stdZtypedthreads_u223+0x78>
10000705c: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007060: 91012000    	add	x0, x0, #0x48
100007064: f9400008    	ldr	x8, [x0]
100007068: d63f0100    	blr	x8
10000706c: aa0003f4    	mov	x20, x0
100007070: aa1303e0    	mov	x0, x19
100007074: d63f0120    	blr	x9
100007078: 39400288    	ldrb	w8, [x20]
10000707c: 350002a8    	cbnz	w8, 0x1000070d0 <_eqcopy___stdZtypedthreads_u223+0xc4>
100007080: f9400268    	ldr	x8, [x19]
100007084: 79802108    	ldrsh	x8, [x8, #0x10]
100007088: 91003d09    	add	x9, x8, #0xf
10000708c: cb0803ea    	neg	x10, x8
100007090: 8a0a0129    	and	x9, x9, x10
100007094: 7100011f    	cmp	w8, #0x0
100007098: 5280020a    	mov	w10, #0x10              ; =16
10000709c: 9a890149    	csel	x9, x10, x9, eq
1000070a0: cb090261    	sub	x1, x19, x9
1000070a4: f100451f    	cmp	x8, #0x11
1000070a8: 5400006b    	b.lt	0x1000070b4 <_eqcopy___stdZtypedthreads_u223+0xa8>
1000070ac: 785fe028    	ldurh	w8, [x1, #-0x2]
1000070b0: cb080021    	sub	x1, x1, x8
1000070b4: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000070b8: 91000000    	add	x0, x0, #0x0
1000070bc: f9400008    	ldr	x8, [x0]
1000070c0: d63f0100    	blr	x8
1000070c4: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000070c8: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000070cc: 17fffa84    	b	0x100005adc <_rawDealloc__system_u6973>
1000070d0: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000070d4: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000070d8: d65f03c0    	ret
1000070dc: f81f0268    	stur	x8, [x19, #-0x10]
1000070e0: f9400262    	ldr	x2, [x19]
1000070e4: 52800000    	mov	w0, #0x0                ; =0
1000070e8: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000070ec: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000070f0: 17ffff7a    	b	0x100006ed8 <_rememberCycle__system_u3474>

00000001000070f4 <_writeToStdErr__system_u4054>:
1000070f4: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
1000070f8: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000070fc: 910043fd    	add	x29, sp, #0x10
100007100: aa0103e2    	mov	x2, x1
100007104: b0000028    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100007108: f9400d08    	ldr	x8, [x8, #0x18]
10000710c: f9400113    	ldr	x19, [x8]
100007110: 52800021    	mov	w1, #0x1                ; =1
100007114: aa1303e3    	mov	x3, x19
100007118: 94001111    	bl	0x10000b55c <_strlen+0x10000b55c>
10000711c: aa1303e0    	mov	x0, x19
100007120: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100007124: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100007128: 14001104    	b	0x10000b538 <_strlen+0x10000b538>

000000010000712c <_showErrorMessage__system_u4059>:
10000712c: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
100007130: a90157f6    	stp	x22, x21, [sp, #0x10]
100007134: a9024ff4    	stp	x20, x19, [sp, #0x20]
100007138: a9037bfd    	stp	x29, x30, [sp, #0x30]
10000713c: 9100c3fd    	add	x29, sp, #0x30
100007140: aa0103e2    	mov	x2, x1
100007144: aa0003f6    	mov	x22, x0
100007148: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000714c: 91012000    	add	x0, x0, #0x48
100007150: f9400008    	ldr	x8, [x0]
100007154: d63f0100    	blr	x8
100007158: 90000078    	adrp	x24, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000715c: f9420b17    	ldr	x23, [x24, #0x410]
100007160: b40005f7    	cbz	x23, 0x10000721c <_showErrorMessage__system_u4059+0xf0>
100007164: aa0003f3    	mov	x19, x0
100007168: b4000316    	cbz	x22, 0x1000071c8 <_showErrorMessage__system_u4059+0x9c>
10000716c: aa1603e0    	mov	x0, x22
100007170: 94001119    	bl	0x10000b5d4 <_strlen+0x10000b5d4>
100007174: f100041f    	cmp	x0, #0x1
100007178: 5400028b    	b.lt	0x1000071c8 <_showErrorMessage__system_u4059+0x9c>
10000717c: aa0003f4    	mov	x20, x0
100007180: 91000417    	add	x23, x0, #0x1
100007184: 91002401    	add	x1, x0, #0x9
100007188: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000718c: 91000000    	add	x0, x0, #0x0
100007190: f9400008    	ldr	x8, [x0]
100007194: d63f0100    	blr	x8
100007198: 97fff942    	bl	0x1000056a0 <_rawAlloc__system_u6797>
10000719c: aa0003f5    	mov	x21, x0
1000071a0: f8008414    	str	x20, [x0], #0x8
1000071a4: aa1603e1    	mov	x1, x22
1000071a8: aa1703e2    	mov	x2, x23
1000071ac: 940010f5    	bl	0x10000b580 <_strlen+0x10000b580>
1000071b0: f9420b17    	ldr	x23, [x24, #0x410]
1000071b4: aa1403e0    	mov	x0, x20
1000071b8: aa1503e1    	mov	x1, x21
1000071bc: d63f02e0    	blr	x23
1000071c0: b5000115    	cbnz	x21, 0x1000071e0 <_showErrorMessage__system_u4059+0xb4>
1000071c4: 1400000f    	b	0x100007200 <_showErrorMessage__system_u4059+0xd4>
1000071c8: d2800014    	mov	x20, #0x0               ; =0
1000071cc: d2800015    	mov	x21, #0x0               ; =0
1000071d0: aa1403e0    	mov	x0, x20
1000071d4: aa1503e1    	mov	x1, x21
1000071d8: d63f02e0    	blr	x23
1000071dc: b4000135    	cbz	x21, 0x100007200 <_showErrorMessage__system_u4059+0xd4>
1000071e0: 39401ea8    	ldrb	w8, [x21, #0x7]
1000071e4: 373000e8    	tbnz	w8, #0x6, 0x100007200 <_showErrorMessage__system_u4059+0xd4>
1000071e8: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000071ec: 91000000    	add	x0, x0, #0x0
1000071f0: f9400008    	ldr	x8, [x0]
1000071f4: d63f0100    	blr	x8
1000071f8: aa1503e1    	mov	x1, x21
1000071fc: 97fffa38    	bl	0x100005adc <_rawDealloc__system_u6973>
100007200: 39400268    	ldrb	w8, [x19]
100007204: 35000268    	cbnz	w8, 0x100007250 <_showErrorMessage__system_u4059+0x124>
100007208: a9437bfd    	ldp	x29, x30, [sp, #0x30]
10000720c: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100007210: a94157f6    	ldp	x22, x21, [sp, #0x10]
100007214: a8c45ff8    	ldp	x24, x23, [sp], #0x40
100007218: d65f03c0    	ret
10000721c: b0000028    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100007220: f9400d08    	ldr	x8, [x8, #0x18]
100007224: f9400113    	ldr	x19, [x8]
100007228: aa1603e0    	mov	x0, x22
10000722c: 52800021    	mov	w1, #0x1                ; =1
100007230: aa1303e3    	mov	x3, x19
100007234: 940010ca    	bl	0x10000b55c <_strlen+0x10000b55c>
100007238: aa1303e0    	mov	x0, x19
10000723c: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100007240: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100007244: a94157f6    	ldp	x22, x21, [sp, #0x10]
100007248: a8c45ff8    	ldp	x24, x23, [sp], #0x40
10000724c: 140010bb    	b	0x10000b538 <_strlen+0x10000b538>
100007250: 3900027f    	strb	wzr, [x19]
100007254: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007258: 91018000    	add	x0, x0, #0x60
10000725c: f9400008    	ldr	x8, [x0]
100007260: d63f0100    	blr	x8
100007264: f9400008    	ldr	x8, [x0]
100007268: f9401d01    	ldr	x1, [x8, #0x38]
10000726c: 52800002    	mov	w2, #0x0                ; =0
100007270: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100007274: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100007278: a94157f6    	ldp	x22, x21, [sp, #0x10]
10000727c: a8c45ff8    	ldp	x24, x23, [sp], #0x40
100007280: 17ffff63    	b	0x10000700c <_eqcopy___stdZtypedthreads_u223>

0000000100007284 <_signalHandler>:
100007284: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100007288: a9017bfd    	stp	x29, x30, [sp, #0x10]
10000728c: 910043fd    	add	x29, sp, #0x10
100007290: aa0003f3    	mov	x19, x0
100007294: 51000808    	sub	w8, w0, #0x2
100007298: 71002d1f    	cmp	w8, #0xb
10000729c: 540000a8    	b.hi	0x1000072b0 <_signalHandler+0x2c>
1000072a0: b0000029    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
1000072a4: 91030129    	add	x9, x9, #0xc0
1000072a8: f868d934    	ldr	x20, [x9, w8, sxtw #3]
1000072ac: 14000003    	b	0x1000072b8 <_signalHandler+0x34>
1000072b0: 90000034    	adrp	x20, 0x10000b000 <_bench__add95carry_u844+0x104>
1000072b4: 91380294    	add	x20, x20, #0xe00
1000072b8: aa1403e0    	mov	x0, x20
1000072bc: 940010c6    	bl	0x10000b5d4 <_strlen+0x10000b5d4>
1000072c0: aa0003e1    	mov	x1, x0
1000072c4: aa1403e0    	mov	x0, x20
1000072c8: 97ffff99    	bl	0x10000712c <_showErrorMessage__system_u4059>
1000072cc: aa1303e0    	mov	x0, x19
1000072d0: d2800001    	mov	x1, #0x0                ; =0
1000072d4: 940010ba    	bl	0x10000b5bc <_strlen+0x10000b5bc>
1000072d8: aa1303e0    	mov	x0, x19
1000072dc: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000072e0: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000072e4: 140010b3    	b	0x10000b5b0 <_strlen+0x10000b5b0>

00000001000072e8 <_registerSignalHandler__system_u4628>:
1000072e8: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
1000072ec: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000072f0: 910043fd    	add	x29, sp, #0x10
1000072f4: 90000013    	adrp	x19, 0x100007000 <_nimDestroyAndDispose+0x90>
1000072f8: 910a1273    	add	x19, x19, #0x284
1000072fc: 52800040    	mov	w0, #0x2                ; =2
100007300: aa1303e1    	mov	x1, x19
100007304: 940010ae    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100007308: 52800160    	mov	w0, #0xb                ; =11
10000730c: aa1303e1    	mov	x1, x19
100007310: 940010ab    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100007314: 528000c0    	mov	w0, #0x6                ; =6
100007318: aa1303e1    	mov	x1, x19
10000731c: 940010a8    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100007320: 52800100    	mov	w0, #0x8                ; =8
100007324: aa1303e1    	mov	x1, x19
100007328: 940010a5    	bl	0x10000b5bc <_strlen+0x10000b5bc>
10000732c: 52800080    	mov	w0, #0x4                ; =4
100007330: aa1303e1    	mov	x1, x19
100007334: 940010a2    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100007338: 52800140    	mov	w0, #0xa                ; =10
10000733c: aa1303e1    	mov	x1, x19
100007340: 9400109f    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100007344: 528001a0    	mov	w0, #0xd                ; =13
100007348: 52800021    	mov	w1, #0x1                ; =1
10000734c: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100007350: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100007354: 1400109a    	b	0x10000b5bc <_strlen+0x10000b5bc>

0000000100007358 <_prepareAdd>:
100007358: a9bb67fa    	stp	x26, x25, [sp, #-0x50]!
10000735c: a9015ff8    	stp	x24, x23, [sp, #0x10]
100007360: a90257f6    	stp	x22, x21, [sp, #0x20]
100007364: a9034ff4    	stp	x20, x19, [sp, #0x30]
100007368: a9047bfd    	stp	x29, x30, [sp, #0x40]
10000736c: 910103fd    	add	x29, sp, #0x40
100007370: aa0003f4    	mov	x20, x0
100007374: a9404c08    	ldp	x8, x19, [x0]
100007378: 8b010118    	add	x24, x8, x1
10000737c: b4000533    	cbz	x19, 0x100007420 <_prepareAdd+0xc8>
100007380: f9400268    	ldr	x8, [x19]
100007384: b7f004e8    	tbnz	x8, #0x3e, 0x100007420 <_prepareAdd+0xc8>
100007388: 9241f908    	and	x8, x8, #0xbfffffffffffffff
10000738c: eb18011f    	cmp	x8, x24
100007390: 5400074a    	b.ge	0x100007478 <_prepareAdd+0x120>
100007394: 52800089    	mov	w9, #0x4                ; =4
100007398: d34ffd0a    	lsr	x10, x8, #15
10000739c: 8b08050b    	add	x11, x8, x8, lsl #1
1000073a0: f100017f    	cmp	x11, #0x0
1000073a4: 9a8ba56b    	cinc	x11, x11, lt
1000073a8: 9341fd6b    	asr	x11, x11, #1
1000073ac: d37ff90c    	lsl	x12, x8, #1
1000073b0: f100015f    	cmp	x10, #0x0
1000073b4: 9a8c116a    	csel	x10, x11, x12, ne
1000073b8: f100051f    	cmp	x8, #0x1
1000073bc: 9a8ab13a    	csel	x26, x9, x10, lt
1000073c0: eb1a031f    	cmp	x24, x26
1000073c4: 9a9ac319    	csel	x25, x24, x26, gt
1000073c8: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000073cc: 91000000    	add	x0, x0, #0x0
1000073d0: f9400008    	ldr	x8, [x0]
1000073d4: d63f0100    	blr	x8
1000073d8: aa0003f5    	mov	x21, x0
1000073dc: b100233f    	cmn	x25, #0x8
1000073e0: 5400066b    	b.lt	0x1000074ac <_prepareAdd+0x154>
1000073e4: 91002737    	add	x23, x25, #0x9
1000073e8: aa1503e0    	mov	x0, x21
1000073ec: aa1703e1    	mov	x1, x23
1000073f0: 97fff8ac    	bl	0x1000056a0 <_rawAlloc__system_u6797>
1000073f4: aa0003f6    	mov	x22, x0
1000073f8: 9274ce68    	and	x8, x19, #0xfffffffffffff000
1000073fc: f9400508    	ldr	x8, [x8, #0x8]
100007400: d100c109    	sub	x9, x8, #0x30
100007404: f13f051f    	cmp	x8, #0xfc1
100007408: 9a89b108    	csel	x8, x8, x9, lt
10000740c: eb17011f    	cmp	x8, x23
100007410: 9a97b102    	csel	x2, x8, x23, lt
100007414: aa1303e1    	mov	x1, x19
100007418: 9400105a    	bl	0x10000b580 <_strlen+0x10000b580>
10000741c: 14000025    	b	0x1000074b0 <_prepareAdd+0x158>
100007420: 91002701    	add	x1, x24, #0x9
100007424: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007428: 91000000    	add	x0, x0, #0x0
10000742c: f9400008    	ldr	x8, [x0]
100007430: d63f0100    	blr	x8
100007434: 97fff89b    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007438: f9000680    	str	x0, [x20, #0x8]
10000743c: f9000018    	str	x24, [x0]
100007440: f9400288    	ldr	x8, [x20]
100007444: f100051f    	cmp	x8, #0x1
100007448: 5400016b    	b.lt	0x100007474 <_prepareAdd+0x11c>
10000744c: 91002000    	add	x0, x0, #0x8
100007450: 91002261    	add	x1, x19, #0x8
100007454: eb18011f    	cmp	x8, x24
100007458: 9a98b102    	csel	x2, x8, x24, lt
10000745c: a9447bfd    	ldp	x29, x30, [sp, #0x40]
100007460: a9434ff4    	ldp	x20, x19, [sp, #0x30]
100007464: a94257f6    	ldp	x22, x21, [sp, #0x20]
100007468: a9415ff8    	ldp	x24, x23, [sp, #0x10]
10000746c: a8c567fa    	ldp	x26, x25, [sp], #0x50
100007470: 14001044    	b	0x10000b580 <_strlen+0x10000b580>
100007474: b40000f3    	cbz	x19, 0x100007490 <_prepareAdd+0x138>
100007478: a9447bfd    	ldp	x29, x30, [sp, #0x40]
10000747c: a9434ff4    	ldp	x20, x19, [sp, #0x30]
100007480: a94257f6    	ldp	x22, x21, [sp, #0x20]
100007484: a9415ff8    	ldp	x24, x23, [sp, #0x10]
100007488: a8c567fa    	ldp	x26, x25, [sp], #0x50
10000748c: d65f03c0    	ret
100007490: 3900201f    	strb	wzr, [x0, #0x8]
100007494: a9447bfd    	ldp	x29, x30, [sp, #0x40]
100007498: a9434ff4    	ldp	x20, x19, [sp, #0x30]
10000749c: a94257f6    	ldp	x22, x21, [sp, #0x20]
1000074a0: a9415ff8    	ldp	x24, x23, [sp, #0x10]
1000074a4: a8c567fa    	ldp	x26, x25, [sp], #0x50
1000074a8: d65f03c0    	ret
1000074ac: d2800016    	mov	x22, #0x0               ; =0
1000074b0: aa1503e0    	mov	x0, x21
1000074b4: aa1303e1    	mov	x1, x19
1000074b8: 97fff989    	bl	0x100005adc <_rawDealloc__system_u6973>
1000074bc: f9000696    	str	x22, [x20, #0x8]
1000074c0: f90002d9    	str	x25, [x22]
1000074c4: eb1a031f    	cmp	x24, x26
1000074c8: 54fffd8a    	b.ge	0x100007478 <_prepareAdd+0x120>
1000074cc: 8b160308    	add	x8, x24, x22
1000074d0: 91002500    	add	x0, x8, #0x9
1000074d4: cb180321    	sub	x1, x25, x24
1000074d8: a9447bfd    	ldp	x29, x30, [sp, #0x40]
1000074dc: a9434ff4    	ldp	x20, x19, [sp, #0x30]
1000074e0: a94257f6    	ldp	x22, x21, [sp, #0x20]
1000074e4: a9415ff8    	ldp	x24, x23, [sp, #0x10]
1000074e8: a8c567fa    	ldp	x26, x25, [sp], #0x50
1000074ec: 1400100a    	b	0x10000b514 <_strlen+0x10000b514>

00000001000074f0 <_nimAsgnStrV2>:
1000074f0: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
1000074f4: a9014ff4    	stp	x20, x19, [sp, #0x10]
1000074f8: a9027bfd    	stp	x29, x30, [sp, #0x20]
1000074fc: 910083fd    	add	x29, sp, #0x20
100007500: aa0203f3    	mov	x19, x2
100007504: aa0103f4    	mov	x20, x1
100007508: aa0003f5    	mov	x21, x0
10000750c: f9400401    	ldr	x1, [x0, #0x8]
100007510: eb02003f    	cmp	x1, x2
100007514: 54000081    	b.ne	0x100007524 <_nimAsgnStrV2+0x34>
100007518: f94002a8    	ldr	x8, [x21]
10000751c: eb14011f    	cmp	x8, x20
100007520: 54000520    	b.eq	0x1000075c4 <_nimAsgnStrV2+0xd4>
100007524: b40003f3    	cbz	x19, 0x1000075a0 <_nimAsgnStrV2+0xb0>
100007528: 39401e68    	ldrb	w8, [x19, #0x7]
10000752c: 373003a8    	tbnz	w8, #0x6, 0x1000075a0 <_nimAsgnStrV2+0xb0>
100007530: b0000056    	adrp	x22, 0x100010000 <_allocator__system_u7104>
100007534: 910002d6    	add	x22, x22, #0x0
100007538: b4000141    	cbz	x1, 0x100007560 <_nimAsgnStrV2+0x70>
10000753c: f9400028    	ldr	x8, [x1]
100007540: b7f00108    	tbnz	x8, #0x3e, 0x100007560 <_nimAsgnStrV2+0x70>
100007544: 9241f908    	and	x8, x8, #0xbfffffffffffffff
100007548: eb14011f    	cmp	x8, x20
10000754c: 540001aa    	b.ge	0x100007580 <_nimAsgnStrV2+0x90>
100007550: f94002c8    	ldr	x8, [x22]
100007554: aa1603e0    	mov	x0, x22
100007558: d63f0100    	blr	x8
10000755c: 97fff960    	bl	0x100005adc <_rawDealloc__system_u6973>
100007560: 91002681    	add	x1, x20, #0x9
100007564: f94002c8    	ldr	x8, [x22]
100007568: aa1603e0    	mov	x0, x22
10000756c: d63f0100    	blr	x8
100007570: 97fff84c    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007574: aa0003e1    	mov	x1, x0
100007578: f90006a0    	str	x0, [x21, #0x8]
10000757c: f9000014    	str	x20, [x0]
100007580: f90002b4    	str	x20, [x21]
100007584: 91002020    	add	x0, x1, #0x8
100007588: 91002261    	add	x1, x19, #0x8
10000758c: 91000682    	add	x2, x20, #0x1
100007590: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100007594: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100007598: a8c357f6    	ldp	x22, x21, [sp], #0x30
10000759c: 14000ff9    	b	0x10000b580 <_strlen+0x10000b580>
1000075a0: b4000101    	cbz	x1, 0x1000075c0 <_nimAsgnStrV2+0xd0>
1000075a4: 39401c28    	ldrb	w8, [x1, #0x7]
1000075a8: 373000c8    	tbnz	w8, #0x6, 0x1000075c0 <_nimAsgnStrV2+0xd0>
1000075ac: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000075b0: 91000000    	add	x0, x0, #0x0
1000075b4: f9400008    	ldr	x8, [x0]
1000075b8: d63f0100    	blr	x8
1000075bc: 97fff948    	bl	0x100005adc <_rawDealloc__system_u6973>
1000075c0: a9004eb4    	stp	x20, x19, [x21]
1000075c4: a9427bfd    	ldp	x29, x30, [sp, #0x20]
1000075c8: a9414ff4    	ldp	x20, x19, [sp, #0x10]
1000075cc: a8c357f6    	ldp	x22, x21, [sp], #0x30
1000075d0: d65f03c0    	ret

00000001000075d4 <_eqcopy___system_u2636>:
1000075d4: 17ffffc7    	b	0x1000074f0 <_nimAsgnStrV2>

00000001000075d8 <_realloc0Impl__system_u1751>:
1000075d8: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
1000075dc: a90157f6    	stp	x22, x21, [sp, #0x10]
1000075e0: a9024ff4    	stp	x20, x19, [sp, #0x20]
1000075e4: a9037bfd    	stp	x29, x30, [sp, #0x30]
1000075e8: 9100c3fd    	add	x29, sp, #0x30
1000075ec: aa0203f4    	mov	x20, x2
1000075f0: aa0103f3    	mov	x19, x1
1000075f4: aa0003f6    	mov	x22, x0
1000075f8: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000075fc: 91000000    	add	x0, x0, #0x0
100007600: f9400008    	ldr	x8, [x0]
100007604: d63f0100    	blr	x8
100007608: aa0003f7    	mov	x23, x0
10000760c: f100045f    	cmp	x2, #0x1
100007610: 5400022b    	b.lt	0x100007654 <_realloc0Impl__system_u1751+0x7c>
100007614: aa1703e0    	mov	x0, x23
100007618: aa1403e1    	mov	x1, x20
10000761c: 97fff821    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007620: aa0003f5    	mov	x21, x0
100007624: b4000236    	cbz	x22, 0x100007668 <_realloc0Impl__system_u1751+0x90>
100007628: 9274cec8    	and	x8, x22, #0xfffffffffffff000
10000762c: f9400508    	ldr	x8, [x8, #0x8]
100007630: d100c109    	sub	x9, x8, #0x30
100007634: f13f051f    	cmp	x8, #0xfc1
100007638: 9a89b108    	csel	x8, x8, x9, lt
10000763c: eb14011f    	cmp	x8, x20
100007640: 9a94b102    	csel	x2, x8, x20, lt
100007644: aa1503e0    	mov	x0, x21
100007648: aa1603e1    	mov	x1, x22
10000764c: 94000fcd    	bl	0x10000b580 <_strlen+0x10000b580>
100007650: 14000003    	b	0x10000765c <_realloc0Impl__system_u1751+0x84>
100007654: d2800015    	mov	x21, #0x0               ; =0
100007658: b4000096    	cbz	x22, 0x100007668 <_realloc0Impl__system_u1751+0x90>
10000765c: aa1703e0    	mov	x0, x23
100007660: aa1603e1    	mov	x1, x22
100007664: 97fff91e    	bl	0x100005adc <_rawDealloc__system_u6973>
100007668: eb130281    	subs	x1, x20, x19
10000766c: 5400006d    	b.le	0x100007678 <_realloc0Impl__system_u1751+0xa0>
100007670: 8b1302a0    	add	x0, x21, x19
100007674: 94000fa8    	bl	0x10000b514 <_strlen+0x10000b514>
100007678: aa1503e0    	mov	x0, x21
10000767c: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100007680: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100007684: a94157f6    	ldp	x22, x21, [sp, #0x10]
100007688: a8c45ff8    	ldp	x24, x23, [sp], #0x40
10000768c: d65f03c0    	ret

0000000100007690 <_reallocShared0Impl__system_u1764>:
100007690: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
100007694: a90157f6    	stp	x22, x21, [sp, #0x10]
100007698: a9024ff4    	stp	x20, x19, [sp, #0x20]
10000769c: a9037bfd    	stp	x29, x30, [sp, #0x30]
1000076a0: 9100c3fd    	add	x29, sp, #0x30
1000076a4: aa0203f4    	mov	x20, x2
1000076a8: aa0103f3    	mov	x19, x1
1000076ac: aa0003f6    	mov	x22, x0
1000076b0: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000076b4: 91000000    	add	x0, x0, #0x0
1000076b8: f9400008    	ldr	x8, [x0]
1000076bc: d63f0100    	blr	x8
1000076c0: aa0003f7    	mov	x23, x0
1000076c4: f100045f    	cmp	x2, #0x1
1000076c8: 5400022b    	b.lt	0x10000770c <_reallocShared0Impl__system_u1764+0x7c>
1000076cc: aa1703e0    	mov	x0, x23
1000076d0: aa1403e1    	mov	x1, x20
1000076d4: 97fff7f3    	bl	0x1000056a0 <_rawAlloc__system_u6797>
1000076d8: aa0003f5    	mov	x21, x0
1000076dc: b4000236    	cbz	x22, 0x100007720 <_reallocShared0Impl__system_u1764+0x90>
1000076e0: 9274cec8    	and	x8, x22, #0xfffffffffffff000
1000076e4: f9400508    	ldr	x8, [x8, #0x8]
1000076e8: d100c109    	sub	x9, x8, #0x30
1000076ec: f13f051f    	cmp	x8, #0xfc1
1000076f0: 9a89b108    	csel	x8, x8, x9, lt
1000076f4: eb14011f    	cmp	x8, x20
1000076f8: 9a94b102    	csel	x2, x8, x20, lt
1000076fc: aa1503e0    	mov	x0, x21
100007700: aa1603e1    	mov	x1, x22
100007704: 94000f9f    	bl	0x10000b580 <_strlen+0x10000b580>
100007708: 14000003    	b	0x100007714 <_reallocShared0Impl__system_u1764+0x84>
10000770c: d2800015    	mov	x21, #0x0               ; =0
100007710: b4000096    	cbz	x22, 0x100007720 <_reallocShared0Impl__system_u1764+0x90>
100007714: aa1703e0    	mov	x0, x23
100007718: aa1603e1    	mov	x1, x22
10000771c: 97fff8f0    	bl	0x100005adc <_rawDealloc__system_u6973>
100007720: eb130281    	subs	x1, x20, x19
100007724: 5400006d    	b.le	0x100007730 <_reallocShared0Impl__system_u1764+0xa0>
100007728: 8b1302a0    	add	x0, x21, x19
10000772c: 94000f7a    	bl	0x10000b514 <_strlen+0x10000b514>
100007730: aa1503e0    	mov	x0, x21
100007734: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100007738: a9424ff4    	ldp	x20, x19, [sp, #0x20]
10000773c: a94157f6    	ldp	x22, x21, [sp, #0x10]
100007740: a8c45ff8    	ldp	x24, x23, [sp], #0x40
100007744: d65f03c0    	ret

0000000100007748 <_setLengthStrV2>:
100007748: a9bb67fa    	stp	x26, x25, [sp, #-0x50]!
10000774c: a9015ff8    	stp	x24, x23, [sp, #0x10]
100007750: a90257f6    	stp	x22, x21, [sp, #0x20]
100007754: a9034ff4    	stp	x20, x19, [sp, #0x30]
100007758: a9047bfd    	stp	x29, x30, [sp, #0x40]
10000775c: 910103fd    	add	x29, sp, #0x40
100007760: aa0103f3    	mov	x19, x1
100007764: aa0003f4    	mov	x20, x0
100007768: b4000b41    	cbz	x1, 0x1000078d0 <_setLengthStrV2+0x188>
10000776c: f9400695    	ldr	x21, [x20, #0x8]
100007770: b4000595    	cbz	x21, 0x100007820 <_setLengthStrV2+0xd8>
100007774: f94002a8    	ldr	x8, [x21]
100007778: b7f00548    	tbnz	x8, #0x3e, 0x100007820 <_setLengthStrV2+0xd8>
10000777c: f9400289    	ldr	x9, [x20]
100007780: eb13013f    	cmp	x9, x19
100007784: 9241f908    	and	x8, x8, #0xbfffffffffffffff
100007788: fa53b100    	ccmp	x8, x19, #0x0, lt
10000778c: 540009ca    	b.ge	0x1000078c4 <_setLengthStrV2+0x17c>
100007790: 52800089    	mov	w9, #0x4                ; =4
100007794: d34ffd0a    	lsr	x10, x8, #15
100007798: 8b08050b    	add	x11, x8, x8, lsl #1
10000779c: f100017f    	cmp	x11, #0x0
1000077a0: 9a8ba56b    	cinc	x11, x11, lt
1000077a4: 9341fd6b    	asr	x11, x11, #1
1000077a8: d37ff90c    	lsl	x12, x8, #1
1000077ac: f100015f    	cmp	x10, #0x0
1000077b0: 9a8c116a    	csel	x10, x11, x12, ne
1000077b4: f100051f    	cmp	x8, #0x1
1000077b8: 9a8ab129    	csel	x9, x9, x10, lt
1000077bc: eb13013f    	cmp	x9, x19
1000077c0: 9a93c139    	csel	x25, x9, x19, gt
1000077c4: 9100251a    	add	x26, x8, #0x9
1000077c8: 91002736    	add	x22, x25, #0x9
1000077cc: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000077d0: 91000000    	add	x0, x0, #0x0
1000077d4: f9400008    	ldr	x8, [x0]
1000077d8: d63f0100    	blr	x8
1000077dc: aa0003f7    	mov	x23, x0
1000077e0: b100233f    	cmn	x25, #0x8
1000077e4: 540005eb    	b.lt	0x1000078a0 <_setLengthStrV2+0x158>
1000077e8: aa1703e0    	mov	x0, x23
1000077ec: aa1603e1    	mov	x1, x22
1000077f0: 97fff7ac    	bl	0x1000056a0 <_rawAlloc__system_u6797>
1000077f4: aa0003f8    	mov	x24, x0
1000077f8: 9274cea8    	and	x8, x21, #0xfffffffffffff000
1000077fc: f9400508    	ldr	x8, [x8, #0x8]
100007800: d100c109    	sub	x9, x8, #0x30
100007804: f13f051f    	cmp	x8, #0xfc1
100007808: 9a89b108    	csel	x8, x8, x9, lt
10000780c: eb16011f    	cmp	x8, x22
100007810: 9a96b102    	csel	x2, x8, x22, lt
100007814: aa1503e1    	mov	x1, x21
100007818: 94000f5a    	bl	0x10000b580 <_strlen+0x10000b580>
10000781c: 14000022    	b	0x1000078a4 <_setLengthStrV2+0x15c>
100007820: 91002661    	add	x1, x19, #0x9
100007824: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007828: 91000000    	add	x0, x0, #0x0
10000782c: f9400008    	ldr	x8, [x0]
100007830: d63f0100    	blr	x8
100007834: 97fff79b    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007838: f9000680    	str	x0, [x20, #0x8]
10000783c: f9000013    	str	x19, [x0]
100007840: f9400288    	ldr	x8, [x20]
100007844: f100051f    	cmp	x8, #0x1
100007848: 540001eb    	b.lt	0x100007884 <_setLengthStrV2+0x13c>
10000784c: 91002000    	add	x0, x0, #0x8
100007850: 910022a1    	add	x1, x21, #0x8
100007854: eb13011f    	cmp	x8, x19
100007858: 9a93b102    	csel	x2, x8, x19, lt
10000785c: 94000f49    	bl	0x10000b580 <_strlen+0x10000b580>
100007860: a9402688    	ldp	x8, x9, [x20]
100007864: eb13011f    	cmp	x8, x19
100007868: 5400016a    	b.ge	0x100007894 <_setLengthStrV2+0x14c>
10000786c: 8b080129    	add	x9, x9, x8
100007870: 91002120    	add	x0, x9, #0x8
100007874: cb080268    	sub	x8, x19, x8
100007878: 91000501    	add	x1, x8, #0x1
10000787c: 94000f26    	bl	0x10000b514 <_strlen+0x10000b514>
100007880: 14000011    	b	0x1000078c4 <_setLengthStrV2+0x17c>
100007884: 91000661    	add	x1, x19, #0x1
100007888: 91002000    	add	x0, x0, #0x8
10000788c: 94000f22    	bl	0x10000b514 <_strlen+0x10000b514>
100007890: 1400000d    	b	0x1000078c4 <_setLengthStrV2+0x17c>
100007894: 8b130128    	add	x8, x9, x19
100007898: 3900211f    	strb	wzr, [x8, #0x8]
10000789c: 1400000a    	b	0x1000078c4 <_setLengthStrV2+0x17c>
1000078a0: d2800018    	mov	x24, #0x0               ; =0
1000078a4: aa1703e0    	mov	x0, x23
1000078a8: aa1503e1    	mov	x1, x21
1000078ac: 97fff88c    	bl	0x100005adc <_rawDealloc__system_u6973>
1000078b0: 8b180340    	add	x0, x26, x24
1000078b4: cb1a02c1    	sub	x1, x22, x26
1000078b8: 94000f17    	bl	0x10000b514 <_strlen+0x10000b514>
1000078bc: f9000698    	str	x24, [x20, #0x8]
1000078c0: f9000319    	str	x25, [x24]
1000078c4: f9400688    	ldr	x8, [x20, #0x8]
1000078c8: 8b130108    	add	x8, x8, x19
1000078cc: 3900211f    	strb	wzr, [x8, #0x8]
1000078d0: f9000293    	str	x19, [x20]
1000078d4: a9447bfd    	ldp	x29, x30, [sp, #0x40]
1000078d8: a9434ff4    	ldp	x20, x19, [sp, #0x30]
1000078dc: a94257f6    	ldp	x22, x21, [sp, #0x20]
1000078e0: a9415ff8    	ldp	x24, x23, [sp, #0x10]
1000078e4: a8c567fa    	ldp	x26, x25, [sp], #0x50
1000078e8: d65f03c0    	ret

00000001000078ec <_addQuoted__add95carry_u445>:
1000078ec: 17fff035    	b	0x1000039c0 <_addInt__stdZprivateZdigitsutils_u184>

00000001000078f0 <_addQuoted__add95carry_u395>:
1000078f0: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
1000078f4: a9014ff4    	stp	x20, x19, [sp, #0x10]
1000078f8: a9027bfd    	stp	x29, x30, [sp, #0x20]
1000078fc: 910083fd    	add	x29, sp, #0x20
100007900: aa0003f4    	mov	x20, x0
100007904: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007908: 91012000    	add	x0, x0, #0x48
10000790c: f9400008    	ldr	x8, [x0]
100007910: d63f0100    	blr	x8
100007914: aa0003f6    	mov	x22, x0
100007918: aa0103e0    	mov	x0, x1
10000791c: 97fff174    	bl	0x100003eec <_dollar___add95carry_u403>
100007920: 394002c8    	ldrb	w8, [x22]
100007924: 350003a8    	cbnz	w8, 0x100007998 <_addQuoted__add95carry_u395+0xa8>
100007928: aa0003f5    	mov	x21, x0
10000792c: aa0103f3    	mov	x19, x1
100007930: aa1403e0    	mov	x0, x20
100007934: aa1503e1    	mov	x1, x21
100007938: 97fffe88    	bl	0x100007358 <_prepareAdd>
10000793c: f10006bf    	cmp	x21, #0x1
100007940: 5400014b    	b.lt	0x100007968 <_addQuoted__add95carry_u395+0x78>
100007944: a9402289    	ldp	x9, x8, [x20]
100007948: 8b090108    	add	x8, x8, x9
10000794c: 91002100    	add	x0, x8, #0x8
100007950: 91002261    	add	x1, x19, #0x8
100007954: 910006a2    	add	x2, x21, #0x1
100007958: 94000f0a    	bl	0x10000b580 <_strlen+0x10000b580>
10000795c: f9400288    	ldr	x8, [x20]
100007960: 8b150108    	add	x8, x8, x21
100007964: f9000288    	str	x8, [x20]
100007968: b4000193    	cbz	x19, 0x100007998 <_addQuoted__add95carry_u395+0xa8>
10000796c: 39401e68    	ldrb	w8, [x19, #0x7]
100007970: 37300148    	tbnz	w8, #0x6, 0x100007998 <_addQuoted__add95carry_u395+0xa8>
100007974: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007978: 91000000    	add	x0, x0, #0x0
10000797c: f9400008    	ldr	x8, [x0]
100007980: d63f0100    	blr	x8
100007984: aa1303e1    	mov	x1, x19
100007988: a9427bfd    	ldp	x29, x30, [sp, #0x20]
10000798c: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100007990: a8c357f6    	ldp	x22, x21, [sp], #0x30
100007994: 17fff852    	b	0x100005adc <_rawDealloc__system_u6973>
100007998: a9427bfd    	ldp	x29, x30, [sp, #0x20]
10000799c: a9414ff4    	ldp	x20, x19, [sp, #0x10]
1000079a0: a8c357f6    	ldp	x22, x21, [sp], #0x30
1000079a4: d65f03c0    	ret

00000001000079a8 <_echoBinSafe>:
1000079a8: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
1000079ac: a9014ff4    	stp	x20, x19, [sp, #0x10]
1000079b0: a9027bfd    	stp	x29, x30, [sp, #0x20]
1000079b4: 910083fd    	add	x29, sp, #0x20
1000079b8: aa0103f3    	mov	x19, x1
1000079bc: aa0003f4    	mov	x20, x0
1000079c0: b0000035    	adrp	x21, 0x10000c000 <_strlen+0x10000c000>
1000079c4: f94012b5    	ldr	x21, [x21, #0x20]
1000079c8: f94002a0    	ldr	x0, [x21]
1000079cc: 94000ede    	bl	0x10000b544 <_strlen+0x10000b544>
1000079d0: f100067f    	cmp	x19, #0x1
1000079d4: 540001cb    	b.lt	0x100007a0c <_echoBinSafe+0x64>
1000079d8: 91002294    	add	x20, x20, #0x8
1000079dc: 90000036    	adrp	x22, 0x10000b000 <_bench__add95carry_u844+0x104>
1000079e0: 9138bed6    	add	x22, x22, #0xe2f
1000079e4: a97fa281    	ldp	x1, x8, [x20, #-0x8]
1000079e8: 91002108    	add	x8, x8, #0x8
1000079ec: f100003f    	cmp	x1, #0x0
1000079f0: 9a8802c0    	csel	x0, x22, x8, eq
1000079f4: f94002a3    	ldr	x3, [x21]
1000079f8: 52800022    	mov	w2, #0x1                ; =1
1000079fc: 94000ed8    	bl	0x10000b55c <_strlen+0x10000b55c>
100007a00: 91004294    	add	x20, x20, #0x10
100007a04: f1000673    	subs	x19, x19, #0x1
100007a08: 54fffee1    	b.ne	0x1000079e4 <_echoBinSafe+0x3c>
100007a0c: f94002a3    	ldr	x3, [x21]
100007a10: 90000020    	adrp	x0, 0x10000b000 <_bench__add95carry_u844+0x104>
100007a14: 91384000    	add	x0, x0, #0xe10
100007a18: 52800021    	mov	w1, #0x1                ; =1
100007a1c: 52800022    	mov	w2, #0x1                ; =1
100007a20: 94000ecf    	bl	0x10000b55c <_strlen+0x10000b55c>
100007a24: f94002a0    	ldr	x0, [x21]
100007a28: 94000ec4    	bl	0x10000b538 <_strlen+0x10000b538>
100007a2c: f94002a0    	ldr	x0, [x21]
100007a30: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100007a34: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100007a38: a8c357f6    	ldp	x22, x21, [sp], #0x30
100007a3c: 14000ec5    	b	0x10000b550 <_strlen+0x10000b550>

0000000100007a40 <_rawNewString>:
100007a40: f100041f    	cmp	x0, #0x1
100007a44: 5400024b    	b.lt	0x100007a8c <_rawNewString+0x4c>
100007a48: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100007a4c: a9017bfd    	stp	x29, x30, [sp, #0x10]
100007a50: 910043fd    	add	x29, sp, #0x10
100007a54: aa0003f3    	mov	x19, x0
100007a58: 91002401    	add	x1, x0, #0x9
100007a5c: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007a60: 91000000    	add	x0, x0, #0x0
100007a64: f9400008    	ldr	x8, [x0]
100007a68: d63f0100    	blr	x8
100007a6c: 97fff70d    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007a70: aa0003e1    	mov	x1, x0
100007a74: f9000013    	str	x19, [x0]
100007a78: 3900201f    	strb	wzr, [x0, #0x8]
100007a7c: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100007a80: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100007a84: d2800000    	mov	x0, #0x0                ; =0
100007a88: d65f03c0    	ret
100007a8c: d2800001    	mov	x1, #0x0                ; =0
100007a90: d2800000    	mov	x0, #0x0                ; =0
100007a94: d65f03c0    	ret

0000000100007a98 <_allocShared0Impl__system_u1757>:
100007a98: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100007a9c: a9017bfd    	stp	x29, x30, [sp, #0x10]
100007aa0: 910043fd    	add	x29, sp, #0x10
100007aa4: aa0003f3    	mov	x19, x0
100007aa8: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007aac: 91000000    	add	x0, x0, #0x0
100007ab0: f9400008    	ldr	x8, [x0]
100007ab4: d63f0100    	blr	x8
100007ab8: aa1303e1    	mov	x1, x19
100007abc: 97fff6f9    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007ac0: aa1303e1    	mov	x1, x19
100007ac4: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100007ac8: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100007acc: 14000e92    	b	0x10000b514 <_strlen+0x10000b514>

0000000100007ad0 <_mnewString>:
100007ad0: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100007ad4: a9014ff4    	stp	x20, x19, [sp, #0x10]
100007ad8: a9027bfd    	stp	x29, x30, [sp, #0x20]
100007adc: 910083fd    	add	x29, sp, #0x20
100007ae0: f100041f    	cmp	x0, #0x1
100007ae4: 5400026b    	b.lt	0x100007b30 <_mnewString+0x60>
100007ae8: aa0003f3    	mov	x19, x0
100007aec: 91002415    	add	x21, x0, #0x9
100007af0: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007af4: 91000000    	add	x0, x0, #0x0
100007af8: f9400008    	ldr	x8, [x0]
100007afc: d63f0100    	blr	x8
100007b00: aa1503e1    	mov	x1, x21
100007b04: 97fff6e7    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007b08: aa0003f4    	mov	x20, x0
100007b0c: aa1503e1    	mov	x1, x21
100007b10: 94000e81    	bl	0x10000b514 <_strlen+0x10000b514>
100007b14: f9000293    	str	x19, [x20]
100007b18: aa1303e0    	mov	x0, x19
100007b1c: aa1403e1    	mov	x1, x20
100007b20: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100007b24: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100007b28: a8c357f6    	ldp	x22, x21, [sp], #0x30
100007b2c: d65f03c0    	ret
100007b30: d2800013    	mov	x19, #0x0               ; =0
100007b34: d2800014    	mov	x20, #0x0               ; =0
100007b38: aa1303e0    	mov	x0, x19
100007b3c: aa1403e1    	mov	x1, x20
100007b40: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100007b44: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100007b48: a8c357f6    	ldp	x22, x21, [sp], #0x30
100007b4c: d65f03c0    	ret

0000000100007b50 <_nimPrepareStrMutationImpl__system_u2387>:
100007b50: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100007b54: a9017bfd    	stp	x29, x30, [sp, #0x10]
100007b58: 910043fd    	add	x29, sp, #0x10
100007b5c: aa0003f3    	mov	x19, x0
100007b60: a9405008    	ldp	x8, x20, [x0]
100007b64: 91002501    	add	x1, x8, #0x9
100007b68: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007b6c: 91000000    	add	x0, x0, #0x0
100007b70: f9400008    	ldr	x8, [x0]
100007b74: d63f0100    	blr	x8
100007b78: 97fff6ca    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007b7c: f9000660    	str	x0, [x19, #0x8]
100007b80: f9400268    	ldr	x8, [x19]
100007b84: f8008408    	str	x8, [x0], #0x8
100007b88: 91002281    	add	x1, x20, #0x8
100007b8c: f9400268    	ldr	x8, [x19]
100007b90: 91000502    	add	x2, x8, #0x1
100007b94: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100007b98: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100007b9c: 14000e79    	b	0x10000b580 <_strlen+0x10000b580>

0000000100007ba0 <_insert__system_u8463>:
100007ba0: b4000a81    	cbz	x1, 0x100007cf0 <_insert__system_u8463+0x150>
100007ba4: a9bb67fa    	stp	x26, x25, [sp, #-0x50]!
100007ba8: a9015ff8    	stp	x24, x23, [sp, #0x10]
100007bac: a90257f6    	stp	x22, x21, [sp, #0x20]
100007bb0: a9034ff4    	stp	x20, x19, [sp, #0x30]
100007bb4: a9047bfd    	stp	x29, x30, [sp, #0x40]
100007bb8: 910103fd    	add	x29, sp, #0x40
100007bbc: aa0303f6    	mov	x22, x3
100007bc0: aa0203f5    	mov	x21, x2
100007bc4: aa0103f3    	mov	x19, x1
100007bc8: aa0003f4    	mov	x20, x0
100007bcc: f9400019    	ldr	x25, [x0]
100007bd0: 8b010321    	add	x1, x25, x1
100007bd4: 97fffedd    	bl	0x100007748 <_setLengthStrV2>
100007bd8: b0000057    	adrp	x23, 0x100010000 <_allocator__system_u7104>
100007bdc: 910002f7    	add	x23, x23, #0x0
100007be0: eb16033f    	cmp	x25, x22
100007be4: 5400040d    	b.le	0x100007c64 <_insert__system_u8463+0xc4>
100007be8: f94002e8    	ldr	x8, [x23]
100007bec: aa1703e0    	mov	x0, x23
100007bf0: d63f0100    	blr	x8
100007bf4: aa0003f8    	mov	x24, x0
100007bf8: 91001f39    	add	x25, x25, #0x7
100007bfc: 1400000a    	b	0x100007c24 <_insert__system_u8463+0x84>
100007c00: 8b190348    	add	x8, x26, x25
100007c04: 39400109    	ldrb	w9, [x8]
100007c08: 38336909    	strb	w9, [x8, x19]
100007c0c: f9400688    	ldr	x8, [x20, #0x8]
100007c10: 3839691f    	strb	wzr, [x8, x25]
100007c14: d1002328    	sub	x8, x25, #0x8
100007c18: d1000739    	sub	x25, x25, #0x1
100007c1c: eb16011f    	cmp	x8, x22
100007c20: 5400022d    	b.le	0x100007c64 <_insert__system_u8463+0xc4>
100007c24: f940069a    	ldr	x26, [x20, #0x8]
100007c28: 39401f48    	ldrb	w8, [x26, #0x7]
100007c2c: 3637fea8    	tbz	w8, #0x6, 0x100007c00 <_insert__system_u8463+0x60>
100007c30: f9400288    	ldr	x8, [x20]
100007c34: 91002501    	add	x1, x8, #0x9
100007c38: aa1803e0    	mov	x0, x24
100007c3c: 97fff699    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007c40: f9000680    	str	x0, [x20, #0x8]
100007c44: f9400288    	ldr	x8, [x20]
100007c48: f8008408    	str	x8, [x0], #0x8
100007c4c: 91002341    	add	x1, x26, #0x8
100007c50: f9400288    	ldr	x8, [x20]
100007c54: 91000502    	add	x2, x8, #0x1
100007c58: 94000e4a    	bl	0x10000b580 <_strlen+0x10000b580>
100007c5c: f940069a    	ldr	x26, [x20, #0x8]
100007c60: 17ffffe8    	b	0x100007c00 <_insert__system_u8463+0x60>
100007c64: f100067f    	cmp	x19, #0x1
100007c68: 540003ab    	b.lt	0x100007cdc <_insert__system_u8463+0x13c>
100007c6c: f94002e8    	ldr	x8, [x23]
100007c70: aa1703e0    	mov	x0, x23
100007c74: d63f0100    	blr	x8
100007c78: aa0003f7    	mov	x23, x0
100007c7c: 910022d6    	add	x22, x22, #0x8
100007c80: 910022b5    	add	x21, x21, #0x8
100007c84: 14000006    	b	0x100007c9c <_insert__system_u8463+0xfc>
100007c88: 384016a8    	ldrb	w8, [x21], #0x1
100007c8c: 38366b08    	strb	w8, [x24, x22]
100007c90: 910006d6    	add	x22, x22, #0x1
100007c94: f1000673    	subs	x19, x19, #0x1
100007c98: 54000220    	b.eq	0x100007cdc <_insert__system_u8463+0x13c>
100007c9c: f9400698    	ldr	x24, [x20, #0x8]
100007ca0: 39401f08    	ldrb	w8, [x24, #0x7]
100007ca4: 3637ff28    	tbz	w8, #0x6, 0x100007c88 <_insert__system_u8463+0xe8>
100007ca8: f9400288    	ldr	x8, [x20]
100007cac: 91002501    	add	x1, x8, #0x9
100007cb0: aa1703e0    	mov	x0, x23
100007cb4: 97fff67b    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007cb8: f9000680    	str	x0, [x20, #0x8]
100007cbc: f9400288    	ldr	x8, [x20]
100007cc0: f8008408    	str	x8, [x0], #0x8
100007cc4: 91002301    	add	x1, x24, #0x8
100007cc8: f9400288    	ldr	x8, [x20]
100007ccc: 91000502    	add	x2, x8, #0x1
100007cd0: 94000e2c    	bl	0x10000b580 <_strlen+0x10000b580>
100007cd4: f9400698    	ldr	x24, [x20, #0x8]
100007cd8: 17ffffec    	b	0x100007c88 <_insert__system_u8463+0xe8>
100007cdc: a9447bfd    	ldp	x29, x30, [sp, #0x40]
100007ce0: a9434ff4    	ldp	x20, x19, [sp, #0x30]
100007ce4: a94257f6    	ldp	x22, x21, [sp, #0x20]
100007ce8: a9415ff8    	ldp	x24, x23, [sp, #0x10]
100007cec: a8c567fa    	ldp	x26, x25, [sp], #0x50
100007cf0: d65f03c0    	ret

0000000100007cf4 <_nimCharToStr>:
100007cf4: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100007cf8: a9017bfd    	stp	x29, x30, [sp, #0x10]
100007cfc: 910043fd    	add	x29, sp, #0x10
100007d00: aa0003f3    	mov	x19, x0
100007d04: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007d08: 91000000    	add	x0, x0, #0x0
100007d0c: f9400008    	ldr	x8, [x0]
100007d10: d63f0100    	blr	x8
100007d14: 52800141    	mov	w1, #0xa                ; =10
100007d18: 97fff662    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007d1c: aa0003e1    	mov	x1, x0
100007d20: 7900101f    	strh	wzr, [x0, #0x8]
100007d24: 52800028    	mov	w8, #0x1                ; =1
100007d28: f9000008    	str	x8, [x0]
100007d2c: 39002013    	strb	w19, [x0, #0x8]
100007d30: 52800020    	mov	w0, #0x1                ; =1
100007d34: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100007d38: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100007d3c: d65f03c0    	ret

0000000100007d40 <_eqsink___system_u2642>:
100007d40: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100007d44: a9014ff4    	stp	x20, x19, [sp, #0x10]
100007d48: a9027bfd    	stp	x29, x30, [sp, #0x20]
100007d4c: 910083fd    	add	x29, sp, #0x20
100007d50: aa0203f3    	mov	x19, x2
100007d54: aa0103f5    	mov	x21, x1
100007d58: aa0003f4    	mov	x20, x0
100007d5c: f9400401    	ldr	x1, [x0, #0x8]
100007d60: b4000101    	cbz	x1, 0x100007d80 <_eqsink___system_u2642+0x40>
100007d64: 39401c28    	ldrb	w8, [x1, #0x7]
100007d68: 373000c8    	tbnz	w8, #0x6, 0x100007d80 <_eqsink___system_u2642+0x40>
100007d6c: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007d70: 91000000    	add	x0, x0, #0x0
100007d74: f9400008    	ldr	x8, [x0]
100007d78: d63f0100    	blr	x8
100007d7c: 97fff758    	bl	0x100005adc <_rawDealloc__system_u6973>
100007d80: a9004e95    	stp	x21, x19, [x20]
100007d84: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100007d88: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100007d8c: a8c357f6    	ldp	x22, x21, [sp], #0x30
100007d90: d65f03c0    	ret

0000000100007d94 <_add__system_u3618>:
100007d94: b4000321    	cbz	x1, 0x100007df8 <_add__system_u3618+0x64>
100007d98: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100007d9c: a9014ff4    	stp	x20, x19, [sp, #0x10]
100007da0: a9027bfd    	stp	x29, x30, [sp, #0x20]
100007da4: 910083fd    	add	x29, sp, #0x20
100007da8: 39400035    	ldrb	w21, [x1]
100007dac: 34000215    	cbz	w21, 0x100007dec <_add__system_u3618+0x58>
100007db0: aa0003f3    	mov	x19, x0
100007db4: 91000434    	add	x20, x1, #0x1
100007db8: aa1303e0    	mov	x0, x19
100007dbc: 52800021    	mov	w1, #0x1                ; =1
100007dc0: 97fffd66    	bl	0x100007358 <_prepareAdd>
100007dc4: a9402269    	ldp	x9, x8, [x19]
100007dc8: 8b090108    	add	x8, x8, x9
100007dcc: 39002115    	strb	w21, [x8, #0x8]
100007dd0: a9402668    	ldp	x8, x9, [x19]
100007dd4: 91000508    	add	x8, x8, #0x1
100007dd8: f9000268    	str	x8, [x19]
100007ddc: 8b080128    	add	x8, x9, x8
100007de0: 3900211f    	strb	wzr, [x8, #0x8]
100007de4: 38401695    	ldrb	w21, [x20], #0x1
100007de8: 35fffe95    	cbnz	w21, 0x100007db8 <_add__system_u3618+0x24>
100007dec: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100007df0: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100007df4: a8c357f6    	ldp	x22, x21, [sp], #0x30
100007df8: d65f03c0    	ret

0000000100007dfc <_dollar___system_u4251>:
100007dfc: d10283ff    	sub	sp, sp, #0xa0
100007e00: a9046ffc    	stp	x28, x27, [sp, #0x40]
100007e04: a90567fa    	stp	x26, x25, [sp, #0x50]
100007e08: a9065ff8    	stp	x24, x23, [sp, #0x60]
100007e0c: a90757f6    	stp	x22, x21, [sp, #0x70]
100007e10: a9084ff4    	stp	x20, x19, [sp, #0x80]
100007e14: a9097bfd    	stp	x29, x30, [sp, #0x90]
100007e18: 910243fd    	add	x29, sp, #0x90
100007e1c: aa0103f3    	mov	x19, x1
100007e20: aa0003f4    	mov	x20, x0
100007e24: b0000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100007e28: 91000000    	add	x0, x0, #0x0
100007e2c: f9400008    	ldr	x8, [x0]
100007e30: d63f0100    	blr	x8
100007e34: aa0003f5    	mov	x21, x0
100007e38: 5280fb21    	mov	w1, #0x7d9              ; =2009
100007e3c: 97fff619    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007e40: 5280fa08    	mov	w8, #0x7d0              ; =2000
100007e44: f9000008    	str	x8, [x0]
100007e48: 3900201f    	strb	wzr, [x0, #0x8]
100007e4c: a90303ff    	stp	xzr, x0, [sp, #0x30]
100007e50: f100069f    	cmp	x20, #0x1
100007e54: 54002d8b    	b.lt	0x100008404 <_dollar___system_u4251+0x608>
100007e58: d2800018    	mov	x24, #0x0               ; =0
100007e5c: d2800016    	mov	x22, #0x0               ; =0
100007e60: 52800317    	mov	w23, #0x18              ; =24
100007e64: 5280041a    	mov	w26, #0x20              ; =32
100007e68: a901cff4    	stp	x20, x19, [sp, #0x18]
100007e6c: 14000010    	b	0x100007eac <_dollar___system_u4251+0xb0>
100007e70: 9100c3e0    	add	x0, sp, #0x30
100007e74: 52800021    	mov	w1, #0x1                ; =1
100007e78: 97fffd38    	bl	0x100007358 <_prepareAdd>
100007e7c: a94323e9    	ldp	x9, x8, [sp, #0x30]
100007e80: 8b090108    	add	x8, x8, x9
100007e84: 52800149    	mov	w9, #0xa                ; =10
100007e88: 79001109    	strh	w9, [x8, #0x8]
100007e8c: a942a3f6    	ldp	x22, x8, [sp, #0x28]
100007e90: 91000518    	add	x24, x8, #0x1
100007e94: f9001bf8    	str	x24, [sp, #0x30]
100007e98: a941cff4    	ldp	x20, x19, [sp, #0x18]
100007e9c: 52800317    	mov	w23, #0x18              ; =24
100007ea0: 910006d6    	add	x22, x22, #0x1
100007ea4: eb1402df    	cmp	x22, x20
100007ea8: 54002aa0    	b.eq	0x1000083fc <_dollar___system_u4251+0x600>
100007eac: 9b174ed9    	madd	x25, x22, x23, x19
100007eb0: f8410f28    	ldr	x8, [x25, #0x10]!
100007eb4: b101911f    	cmn	x8, #0x64
100007eb8: 54000220    	b.eq	0x100007efc <_dollar___system_u4251+0x100>
100007ebc: b100291f    	cmn	x8, #0xa
100007ec0: 54000361    	b.ne	0x100007f2c <_dollar___system_u4251+0x130>
100007ec4: 9100c3e0    	add	x0, sp, #0x30
100007ec8: 52800221    	mov	w1, #0x11               ; =17
100007ecc: 97fffd23    	bl	0x100007358 <_prepareAdd>
100007ed0: a94323e9    	ldp	x9, x8, [sp, #0x30]
100007ed4: 8b090108    	add	x8, x8, x9
100007ed8: 9000002a    	adrp	x10, 0x10000b000 <_bench__add95carry_u844+0x104>
100007edc: 9120e14a    	add	x10, x10, #0x838
100007ee0: 3dc00140    	ldr	q0, [x10]
100007ee4: 3c808100    	stur	q0, [x8, #0x8]
100007ee8: 5280014a    	mov	w10, #0xa               ; =10
100007eec: 7900310a    	strh	w10, [x8, #0x18]
100007ef0: 91004538    	add	x24, x9, #0x11
100007ef4: f9001bf8    	str	x24, [sp, #0x30]
100007ef8: 17ffffea    	b	0x100007ea0 <_dollar___system_u4251+0xa4>
100007efc: 9100c3e0    	add	x0, sp, #0x30
100007f00: 52800061    	mov	w1, #0x3                ; =3
100007f04: 97fffd15    	bl	0x100007358 <_prepareAdd>
100007f08: a94323e9    	ldp	x9, x8, [sp, #0x30]
100007f0c: 8b090108    	add	x8, x8, x9
100007f10: 528baba9    	mov	w9, #0x5d5d             ; =23901
100007f14: 72a00149    	movk	w9, #0xa, lsl #16
100007f18: b9000909    	str	w9, [x8, #0x8]
100007f1c: f9401be8    	ldr	x8, [sp, #0x30]
100007f20: 91000d18    	add	x24, x8, #0x3
100007f24: f9001bf8    	str	x24, [sp, #0x30]
100007f28: 17ffffde    	b	0x100007ea0 <_dollar___system_u4251+0xa4>
100007f2c: 9b174ec9    	madd	x9, x22, x23, x19
100007f30: f9400d29    	ldr	x9, [x9, #0x18]
100007f34: f90017f6    	str	x22, [sp, #0x28]
100007f38: b4000bc9    	cbz	x9, 0x1000080b0 <_dollar___system_u4251+0x2b4>
100007f3c: 39400133    	ldrb	w19, [x9]
100007f40: 34000b93    	cbz	w19, 0x1000080b0 <_dollar___system_u4251+0x2b4>
100007f44: a900e3f9    	stp	x25, x24, [sp, #0x8]
100007f48: 91000534    	add	x20, x9, #0x1
100007f4c: 14000018    	b	0x100007fac <_dollar___system_u4251+0x1b0>
100007f50: 91002b81    	add	x1, x28, #0xa
100007f54: aa1503e0    	mov	x0, x21
100007f58: 97fff5d2    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100007f5c: f9001fe0    	str	x0, [sp, #0x38]
100007f60: f9000016    	str	x22, [x0]
100007f64: f9401be8    	ldr	x8, [sp, #0x30]
100007f68: f100051f    	cmp	x8, #0x1
100007f6c: 5400044b    	b.lt	0x100007ff4 <_dollar___system_u4251+0x1f8>
100007f70: 91002000    	add	x0, x0, #0x8
100007f74: 910022e1    	add	x1, x23, #0x8
100007f78: eb16011f    	cmp	x8, x22
100007f7c: 9a96b102    	csel	x2, x8, x22, lt
100007f80: 94000d80    	bl	0x10000b580 <_strlen+0x10000b580>
100007f84: a94323e9    	ldp	x9, x8, [sp, #0x30]
100007f88: 8b090108    	add	x8, x8, x9
100007f8c: 39002113    	strb	w19, [x8, #0x8]
100007f90: a94327e8    	ldp	x8, x9, [sp, #0x30]
100007f94: 91000508    	add	x8, x8, #0x1
100007f98: f9001be8    	str	x8, [sp, #0x30]
100007f9c: 8b080128    	add	x8, x9, x8
100007fa0: 3900211f    	strb	wzr, [x8, #0x8]
100007fa4: 38401693    	ldrb	w19, [x20], #0x1
100007fa8: 34000813    	cbz	w19, 0x1000080a8 <_dollar___system_u4251+0x2ac>
100007fac: a9435ffc    	ldp	x28, x23, [sp, #0x30]
100007fb0: 91000796    	add	x22, x28, #0x1
100007fb4: b4fffcf7    	cbz	x23, 0x100007f50 <_dollar___system_u4251+0x154>
100007fb8: f94002e8    	ldr	x8, [x23]
100007fbc: b7f7fca8    	tbnz	x8, #0x3e, 0x100007f50 <_dollar___system_u4251+0x154>
100007fc0: 9241f908    	and	x8, x8, #0xbfffffffffffffff
100007fc4: eb1c011f    	cmp	x8, x28
100007fc8: 54fffdec    	b.gt	0x100007f84 <_dollar___system_u4251+0x188>
100007fcc: f100051f    	cmp	x8, #0x1
100007fd0: 5400018b    	b.lt	0x100008000 <_dollar___system_u4251+0x204>
100007fd4: d34ffd09    	lsr	x9, x8, #15
100007fd8: b50003c9    	cbnz	x9, 0x100008050 <_dollar___system_u4251+0x254>
100007fdc: d37ff91a    	lsl	x26, x8, #1
100007fe0: eb1a02df    	cmp	x22, x26
100007fe4: 9a9ac2db    	csel	x27, x22, x26, gt
100007fe8: b100237f    	cmn	x27, #0x8
100007fec: 5400014a    	b.ge	0x100008014 <_dollar___system_u4251+0x218>
100007ff0: 14000020    	b	0x100008070 <_dollar___system_u4251+0x274>
100007ff4: b5fffc97    	cbnz	x23, 0x100007f84 <_dollar___system_u4251+0x188>
100007ff8: 3900201f    	strb	wzr, [x0, #0x8]
100007ffc: 17ffffe2    	b	0x100007f84 <_dollar___system_u4251+0x188>
100008000: 5280009a    	mov	w26, #0x4               ; =4
100008004: eb1a02df    	cmp	x22, x26
100008008: 9a9ac2db    	csel	x27, x22, x26, gt
10000800c: b100237f    	cmn	x27, #0x8
100008010: 5400030b    	b.lt	0x100008070 <_dollar___system_u4251+0x274>
100008014: 91002779    	add	x25, x27, #0x9
100008018: aa1503e0    	mov	x0, x21
10000801c: aa1903e1    	mov	x1, x25
100008020: 97fff5a0    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100008024: aa0003f8    	mov	x24, x0
100008028: 9274cee8    	and	x8, x23, #0xfffffffffffff000
10000802c: f9400508    	ldr	x8, [x8, #0x8]
100008030: d100c109    	sub	x9, x8, #0x30
100008034: f13f051f    	cmp	x8, #0xfc1
100008038: 9a89b108    	csel	x8, x8, x9, lt
10000803c: eb19011f    	cmp	x8, x25
100008040: 9a99b102    	csel	x2, x8, x25, lt
100008044: aa1703e1    	mov	x1, x23
100008048: 94000d4e    	bl	0x10000b580 <_strlen+0x10000b580>
10000804c: 1400000a    	b	0x100008074 <_dollar___system_u4251+0x278>
100008050: 8b080508    	add	x8, x8, x8, lsl #1
100008054: f100011f    	cmp	x8, #0x0
100008058: 9a88a508    	cinc	x8, x8, lt
10000805c: 9341fd1a    	asr	x26, x8, #1
100008060: eb1a02df    	cmp	x22, x26
100008064: 9a9ac2db    	csel	x27, x22, x26, gt
100008068: b100237f    	cmn	x27, #0x8
10000806c: 54fffd4a    	b.ge	0x100008014 <_dollar___system_u4251+0x218>
100008070: d2800018    	mov	x24, #0x0               ; =0
100008074: aa1503e0    	mov	x0, x21
100008078: aa1703e1    	mov	x1, x23
10000807c: 97fff698    	bl	0x100005adc <_rawDealloc__system_u6973>
100008080: f9001ff8    	str	x24, [sp, #0x38]
100008084: f900031b    	str	x27, [x24]
100008088: eb1a02df    	cmp	x22, x26
10000808c: 5280041a    	mov	w26, #0x20              ; =32
100008090: 54fff7aa    	b.ge	0x100007f84 <_dollar___system_u4251+0x188>
100008094: 8b180388    	add	x8, x28, x24
100008098: 91002900    	add	x0, x8, #0xa
10000809c: cb160361    	sub	x1, x27, x22
1000080a0: 94000d1d    	bl	0x10000b514 <_strlen+0x10000b514>
1000080a4: 17ffffb8    	b	0x100007f84 <_dollar___system_u4251+0x188>
1000080a8: a940e3f9    	ldp	x25, x24, [sp, #0x8]
1000080ac: f9400328    	ldr	x8, [x25]
1000080b0: f100011f    	cmp	x8, #0x0
1000080b4: 5400032d    	b.le	0x100008118 <_dollar___system_u4251+0x31c>
1000080b8: 9100c3e0    	add	x0, sp, #0x30
1000080bc: 52800021    	mov	w1, #0x1                ; =1
1000080c0: 97fffca6    	bl	0x100007358 <_prepareAdd>
1000080c4: a94323e9    	ldp	x9, x8, [sp, #0x30]
1000080c8: 8b090108    	add	x8, x8, x9
1000080cc: 52800509    	mov	w9, #0x28               ; =40
1000080d0: 79001109    	strh	w9, [x8, #0x8]
1000080d4: f9401be8    	ldr	x8, [sp, #0x30]
1000080d8: 91000508    	add	x8, x8, #0x1
1000080dc: f9001be8    	str	x8, [sp, #0x30]
1000080e0: f9400321    	ldr	x1, [x25]
1000080e4: 9100c3e0    	add	x0, sp, #0x30
1000080e8: 97ffee84    	bl	0x100003af8 <_addInt__stdZprivateZdigitsutils_u187>
1000080ec: 9100c3e0    	add	x0, sp, #0x30
1000080f0: 52800021    	mov	w1, #0x1                ; =1
1000080f4: 97fffc99    	bl	0x100007358 <_prepareAdd>
1000080f8: a94323e9    	ldp	x9, x8, [sp, #0x30]
1000080fc: 8b090108    	add	x8, x8, x9
100008100: 52800529    	mov	w9, #0x29               ; =41
100008104: 79001109    	strh	w9, [x8, #0x8]
100008108: f9401be8    	ldr	x8, [sp, #0x30]
10000810c: 91000508    	add	x8, x8, #0x1
100008110: f9001be8    	str	x8, [sp, #0x30]
100008114: 14000002    	b	0x10000811c <_dollar___system_u4251+0x320>
100008118: f9401be8    	ldr	x8, [sp, #0x30]
10000811c: d1002339    	sub	x25, x25, #0x8
100008120: cb080308    	sub	x8, x24, x8
100008124: 91006508    	add	x8, x8, #0x19
100008128: f100051f    	cmp	x8, #0x1
10000812c: 9a9fc513    	csinc	x19, x8, xzr, gt
100008130: 14000018    	b	0x100008190 <_dollar___system_u4251+0x394>
100008134: 91002b61    	add	x1, x27, #0xa
100008138: aa1503e0    	mov	x0, x21
10000813c: 97fff559    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100008140: f9001fe0    	str	x0, [sp, #0x38]
100008144: f9000014    	str	x20, [x0]
100008148: f9401be8    	ldr	x8, [sp, #0x30]
10000814c: f100051f    	cmp	x8, #0x1
100008150: 5400044b    	b.lt	0x1000081d8 <_dollar___system_u4251+0x3dc>
100008154: 91002000    	add	x0, x0, #0x8
100008158: 910022c1    	add	x1, x22, #0x8
10000815c: eb14011f    	cmp	x8, x20
100008160: 9a94b102    	csel	x2, x8, x20, lt
100008164: 94000d07    	bl	0x10000b580 <_strlen+0x10000b580>
100008168: a94323e9    	ldp	x9, x8, [sp, #0x30]
10000816c: 8b090108    	add	x8, x8, x9
100008170: 3900211a    	strb	w26, [x8, #0x8]
100008174: a94327e8    	ldp	x8, x9, [sp, #0x30]
100008178: 91000508    	add	x8, x8, #0x1
10000817c: f9001be8    	str	x8, [sp, #0x30]
100008180: 8b080128    	add	x8, x9, x8
100008184: 3900211f    	strb	wzr, [x8, #0x8]
100008188: f1000673    	subs	x19, x19, #0x1
10000818c: 54000800    	b.eq	0x10000828c <_dollar___system_u4251+0x490>
100008190: a9435bfb    	ldp	x27, x22, [sp, #0x30]
100008194: 91000774    	add	x20, x27, #0x1
100008198: b4fffcf6    	cbz	x22, 0x100008134 <_dollar___system_u4251+0x338>
10000819c: f94002c8    	ldr	x8, [x22]
1000081a0: b7f7fca8    	tbnz	x8, #0x3e, 0x100008134 <_dollar___system_u4251+0x338>
1000081a4: 9241f908    	and	x8, x8, #0xbfffffffffffffff
1000081a8: eb1b011f    	cmp	x8, x27
1000081ac: 54fffdec    	b.gt	0x100008168 <_dollar___system_u4251+0x36c>
1000081b0: f100051f    	cmp	x8, #0x1
1000081b4: 5400018b    	b.lt	0x1000081e4 <_dollar___system_u4251+0x3e8>
1000081b8: d34ffd09    	lsr	x9, x8, #15
1000081bc: b50003c9    	cbnz	x9, 0x100008234 <_dollar___system_u4251+0x438>
1000081c0: d37ff91a    	lsl	x26, x8, #1
1000081c4: eb1a029f    	cmp	x20, x26
1000081c8: 9a9ac29c    	csel	x28, x20, x26, gt
1000081cc: b100239f    	cmn	x28, #0x8
1000081d0: 5400014a    	b.ge	0x1000081f8 <_dollar___system_u4251+0x3fc>
1000081d4: 14000020    	b	0x100008254 <_dollar___system_u4251+0x458>
1000081d8: b5fffc96    	cbnz	x22, 0x100008168 <_dollar___system_u4251+0x36c>
1000081dc: 3900201f    	strb	wzr, [x0, #0x8]
1000081e0: 17ffffe2    	b	0x100008168 <_dollar___system_u4251+0x36c>
1000081e4: 5280009a    	mov	w26, #0x4               ; =4
1000081e8: eb1a029f    	cmp	x20, x26
1000081ec: 9a9ac29c    	csel	x28, x20, x26, gt
1000081f0: b100239f    	cmn	x28, #0x8
1000081f4: 5400030b    	b.lt	0x100008254 <_dollar___system_u4251+0x458>
1000081f8: 91002798    	add	x24, x28, #0x9
1000081fc: aa1503e0    	mov	x0, x21
100008200: aa1803e1    	mov	x1, x24
100008204: 97fff527    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100008208: aa0003f7    	mov	x23, x0
10000820c: 9274cec8    	and	x8, x22, #0xfffffffffffff000
100008210: f9400508    	ldr	x8, [x8, #0x8]
100008214: d100c109    	sub	x9, x8, #0x30
100008218: f13f051f    	cmp	x8, #0xfc1
10000821c: 9a89b108    	csel	x8, x8, x9, lt
100008220: eb18011f    	cmp	x8, x24
100008224: 9a98b102    	csel	x2, x8, x24, lt
100008228: aa1603e1    	mov	x1, x22
10000822c: 94000cd5    	bl	0x10000b580 <_strlen+0x10000b580>
100008230: 1400000a    	b	0x100008258 <_dollar___system_u4251+0x45c>
100008234: 8b080508    	add	x8, x8, x8, lsl #1
100008238: f100011f    	cmp	x8, #0x0
10000823c: 9a88a508    	cinc	x8, x8, lt
100008240: 9341fd1a    	asr	x26, x8, #1
100008244: eb1a029f    	cmp	x20, x26
100008248: 9a9ac29c    	csel	x28, x20, x26, gt
10000824c: b100239f    	cmn	x28, #0x8
100008250: 54fffd4a    	b.ge	0x1000081f8 <_dollar___system_u4251+0x3fc>
100008254: d2800017    	mov	x23, #0x0               ; =0
100008258: aa1503e0    	mov	x0, x21
10000825c: aa1603e1    	mov	x1, x22
100008260: 97fff61f    	bl	0x100005adc <_rawDealloc__system_u6973>
100008264: f9001ff7    	str	x23, [sp, #0x38]
100008268: f90002fc    	str	x28, [x23]
10000826c: eb1a029f    	cmp	x20, x26
100008270: 5280041a    	mov	w26, #0x20              ; =32
100008274: 54fff7aa    	b.ge	0x100008168 <_dollar___system_u4251+0x36c>
100008278: 8b170368    	add	x8, x27, x23
10000827c: 91002900    	add	x0, x8, #0xa
100008280: cb140381    	sub	x1, x28, x20
100008284: 94000ca4    	bl	0x10000b514 <_strlen+0x10000b514>
100008288: 17ffffb8    	b	0x100008168 <_dollar___system_u4251+0x36c>
10000828c: f9400328    	ldr	x8, [x25]
100008290: b4ffdf08    	cbz	x8, 0x100007e70 <_dollar___system_u4251+0x74>
100008294: 39400113    	ldrb	w19, [x8]
100008298: 34ffded3    	cbz	w19, 0x100007e70 <_dollar___system_u4251+0x74>
10000829c: 91000514    	add	x20, x8, #0x1
1000082a0: 14000018    	b	0x100008300 <_dollar___system_u4251+0x504>
1000082a4: 91002b61    	add	x1, x27, #0xa
1000082a8: aa1503e0    	mov	x0, x21
1000082ac: 97fff4fd    	bl	0x1000056a0 <_rawAlloc__system_u6797>
1000082b0: f9001fe0    	str	x0, [sp, #0x38]
1000082b4: f9000019    	str	x25, [x0]
1000082b8: f9401be8    	ldr	x8, [sp, #0x30]
1000082bc: f100051f    	cmp	x8, #0x1
1000082c0: 5400044b    	b.lt	0x100008348 <_dollar___system_u4251+0x54c>
1000082c4: 91002000    	add	x0, x0, #0x8
1000082c8: 910022c1    	add	x1, x22, #0x8
1000082cc: eb19011f    	cmp	x8, x25
1000082d0: 9a99b102    	csel	x2, x8, x25, lt
1000082d4: 94000cab    	bl	0x10000b580 <_strlen+0x10000b580>
1000082d8: a94323e9    	ldp	x9, x8, [sp, #0x30]
1000082dc: 8b090108    	add	x8, x8, x9
1000082e0: 39002113    	strb	w19, [x8, #0x8]
1000082e4: a94327e8    	ldp	x8, x9, [sp, #0x30]
1000082e8: 91000508    	add	x8, x8, #0x1
1000082ec: f9001be8    	str	x8, [sp, #0x30]
1000082f0: 8b080128    	add	x8, x9, x8
1000082f4: 3900211f    	strb	wzr, [x8, #0x8]
1000082f8: 38401693    	ldrb	w19, [x20], #0x1
1000082fc: 34ffdbb3    	cbz	w19, 0x100007e70 <_dollar___system_u4251+0x74>
100008300: a9435bfb    	ldp	x27, x22, [sp, #0x30]
100008304: 91000779    	add	x25, x27, #0x1
100008308: b4fffcf6    	cbz	x22, 0x1000082a4 <_dollar___system_u4251+0x4a8>
10000830c: f94002c8    	ldr	x8, [x22]
100008310: b7f7fca8    	tbnz	x8, #0x3e, 0x1000082a4 <_dollar___system_u4251+0x4a8>
100008314: 9241f908    	and	x8, x8, #0xbfffffffffffffff
100008318: eb1b011f    	cmp	x8, x27
10000831c: 54fffdec    	b.gt	0x1000082d8 <_dollar___system_u4251+0x4dc>
100008320: f100051f    	cmp	x8, #0x1
100008324: 5400018b    	b.lt	0x100008354 <_dollar___system_u4251+0x558>
100008328: d34ffd09    	lsr	x9, x8, #15
10000832c: b50003c9    	cbnz	x9, 0x1000083a4 <_dollar___system_u4251+0x5a8>
100008330: d37ff91a    	lsl	x26, x8, #1
100008334: eb1a033f    	cmp	x25, x26
100008338: 9a9ac33c    	csel	x28, x25, x26, gt
10000833c: b100239f    	cmn	x28, #0x8
100008340: 5400014a    	b.ge	0x100008368 <_dollar___system_u4251+0x56c>
100008344: 14000020    	b	0x1000083c4 <_dollar___system_u4251+0x5c8>
100008348: b5fffc96    	cbnz	x22, 0x1000082d8 <_dollar___system_u4251+0x4dc>
10000834c: 3900201f    	strb	wzr, [x0, #0x8]
100008350: 17ffffe2    	b	0x1000082d8 <_dollar___system_u4251+0x4dc>
100008354: 5280009a    	mov	w26, #0x4               ; =4
100008358: eb1a033f    	cmp	x25, x26
10000835c: 9a9ac33c    	csel	x28, x25, x26, gt
100008360: b100239f    	cmn	x28, #0x8
100008364: 5400030b    	b.lt	0x1000083c4 <_dollar___system_u4251+0x5c8>
100008368: 91002798    	add	x24, x28, #0x9
10000836c: aa1503e0    	mov	x0, x21
100008370: aa1803e1    	mov	x1, x24
100008374: 97fff4cb    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100008378: aa0003f7    	mov	x23, x0
10000837c: 9274cec8    	and	x8, x22, #0xfffffffffffff000
100008380: f9400508    	ldr	x8, [x8, #0x8]
100008384: d100c109    	sub	x9, x8, #0x30
100008388: f13f051f    	cmp	x8, #0xfc1
10000838c: 9a89b108    	csel	x8, x8, x9, lt
100008390: eb18011f    	cmp	x8, x24
100008394: 9a98b102    	csel	x2, x8, x24, lt
100008398: aa1603e1    	mov	x1, x22
10000839c: 94000c79    	bl	0x10000b580 <_strlen+0x10000b580>
1000083a0: 1400000a    	b	0x1000083c8 <_dollar___system_u4251+0x5cc>
1000083a4: 8b080508    	add	x8, x8, x8, lsl #1
1000083a8: f100011f    	cmp	x8, #0x0
1000083ac: 9a88a508    	cinc	x8, x8, lt
1000083b0: 9341fd1a    	asr	x26, x8, #1
1000083b4: eb1a033f    	cmp	x25, x26
1000083b8: 9a9ac33c    	csel	x28, x25, x26, gt
1000083bc: b100239f    	cmn	x28, #0x8
1000083c0: 54fffd4a    	b.ge	0x100008368 <_dollar___system_u4251+0x56c>
1000083c4: d2800017    	mov	x23, #0x0               ; =0
1000083c8: aa1503e0    	mov	x0, x21
1000083cc: aa1603e1    	mov	x1, x22
1000083d0: 97fff5c3    	bl	0x100005adc <_rawDealloc__system_u6973>
1000083d4: f9001ff7    	str	x23, [sp, #0x38]
1000083d8: f90002fc    	str	x28, [x23]
1000083dc: eb1a033f    	cmp	x25, x26
1000083e0: 5280041a    	mov	w26, #0x20              ; =32
1000083e4: 54fff7aa    	b.ge	0x1000082d8 <_dollar___system_u4251+0x4dc>
1000083e8: 8b170368    	add	x8, x27, x23
1000083ec: 91002900    	add	x0, x8, #0xa
1000083f0: cb190381    	sub	x1, x28, x25
1000083f4: 94000c48    	bl	0x10000b514 <_strlen+0x10000b514>
1000083f8: 17ffffb8    	b	0x1000082d8 <_dollar___system_u4251+0x4dc>
1000083fc: f9401fe1    	ldr	x1, [sp, #0x38]
100008400: 14000003    	b	0x10000840c <_dollar___system_u4251+0x610>
100008404: aa0003e1    	mov	x1, x0
100008408: d2800018    	mov	x24, #0x0               ; =0
10000840c: aa1803e0    	mov	x0, x24
100008410: a9497bfd    	ldp	x29, x30, [sp, #0x90]
100008414: a9484ff4    	ldp	x20, x19, [sp, #0x80]
100008418: a94757f6    	ldp	x22, x21, [sp, #0x70]
10000841c: a9465ff8    	ldp	x24, x23, [sp, #0x60]
100008420: a94567fa    	ldp	x26, x25, [sp, #0x50]
100008424: a9446ffc    	ldp	x28, x27, [sp, #0x40]
100008428: 910283ff    	add	sp, sp, #0xa0
10000842c: d65f03c0    	ret

0000000100008430 <_reportUnhandledErrorAux__system_u4280>:
100008430: a9bc6ffc    	stp	x28, x27, [sp, #-0x40]!
100008434: a90157f6    	stp	x22, x21, [sp, #0x10]
100008438: a9024ff4    	stp	x20, x19, [sp, #0x20]
10000843c: a9037bfd    	stp	x29, x30, [sp, #0x30]
100008440: 9100c3fd    	add	x29, sp, #0x30
100008444: d11f83ff    	sub	sp, sp, #0x7e0
100008448: aa0003f4    	mov	x20, x0
10000844c: 90000028    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100008450: f9400908    	ldr	x8, [x8, #0x10]
100008454: f9400108    	ldr	x8, [x8]
100008458: f81c83a8    	stur	x8, [x29, #-0x38]
10000845c: 91001ff6    	add	x22, sp, #0x7
100008460: 91001fe0    	add	x0, sp, #0x7
100008464: 5280fa21    	mov	w1, #0x7d1              ; =2001
100008468: 94000c2b    	bl	0x10000b514 <_strlen+0x10000b514>
10000846c: f9401680    	ldr	x0, [x20, #0x28]
100008470: b4000240    	cbz	x0, 0x1000084b8 <_reportUnhandledErrorAux__system_u4280+0x88>
100008474: f9401a81    	ldr	x1, [x20, #0x30]
100008478: 97fffe61    	bl	0x100007dfc <_dollar___system_u4251>
10000847c: aa0103f5    	mov	x21, x1
100008480: f11f3c1f    	cmp	x0, #0x7cf
100008484: 540001ec    	b.gt	0x1000084c0 <_reportUnhandledErrorAux__system_u4280+0x90>
100008488: aa0003f3    	mov	x19, x0
10000848c: 910022a8    	add	x8, x21, #0x8
100008490: f0000009    	adrp	x9, 0x10000b000 <_bench__add95carry_u844+0x104>
100008494: 9138bd29    	add	x9, x9, #0xe2f
100008498: f100001f    	cmp	x0, #0x0
10000849c: 9a880121    	csel	x1, x9, x8, eq
1000084a0: 91001fe0    	add	x0, sp, #0x7
1000084a4: aa1303e2    	mov	x2, x19
1000084a8: 5280fa23    	mov	w3, #0x7d1              ; =2001
1000084ac: 94000c14    	bl	0x10000b4fc <_strlen+0x10000b4fc>
1000084b0: b50000d5    	cbnz	x21, 0x1000084c8 <_reportUnhandledErrorAux__system_u4280+0x98>
1000084b4: 1400000d    	b	0x1000084e8 <_reportUnhandledErrorAux__system_u4280+0xb8>
1000084b8: d2800013    	mov	x19, #0x0               ; =0
1000084bc: 14000032    	b	0x100008584 <_reportUnhandledErrorAux__system_u4280+0x154>
1000084c0: d2800013    	mov	x19, #0x0               ; =0
1000084c4: b4000135    	cbz	x21, 0x1000084e8 <_reportUnhandledErrorAux__system_u4280+0xb8>
1000084c8: 39401ea8    	ldrb	w8, [x21, #0x7]
1000084cc: 373000e8    	tbnz	w8, #0x6, 0x1000084e8 <_reportUnhandledErrorAux__system_u4280+0xb8>
1000084d0: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000084d4: 91000000    	add	x0, x0, #0x0
1000084d8: f9400008    	ldr	x8, [x0]
1000084dc: d63f0100    	blr	x8
1000084e0: aa1503e1    	mov	x1, x21
1000084e4: 97fff57e    	bl	0x100005adc <_rawDealloc__system_u6973>
1000084e8: f11ece7f    	cmp	x19, #0x7b3
1000084ec: 540004cd    	b.le	0x100008584 <_reportUnhandledErrorAux__system_u4280+0x154>
1000084f0: f9400e82    	ldr	x2, [x20, #0x18]
1000084f4: 8b130055    	add	x21, x2, x19
1000084f8: f11f3ebf    	cmp	x21, #0x7cf
1000084fc: 540005cd    	b.le	0x1000085b4 <_reportUnhandledErrorAux__system_u4280+0x184>
100008500: f11f367f    	cmp	x19, #0x7cd
100008504: 5400070d    	b.le	0x1000085e4 <_reportUnhandledErrorAux__system_u4280+0x1b4>
100008508: f9400a94    	ldr	x20, [x20, #0x10]
10000850c: b4000794    	cbz	x20, 0x1000085fc <_reportUnhandledErrorAux__system_u4280+0x1cc>
100008510: aa1403e0    	mov	x0, x20
100008514: 94000c30    	bl	0x10000b5d4 <_strlen+0x10000b5d4>
100008518: 8b130008    	add	x8, x0, x19
10000851c: f11f3d1f    	cmp	x8, #0x7cf
100008520: 5400078d    	b.le	0x100008610 <_reportUnhandledErrorAux__system_u4280+0x1e0>
100008524: f11f367f    	cmp	x19, #0x7cd
100008528: 5400088d    	b.le	0x100008638 <_reportUnhandledErrorAux__system_u4280+0x208>
10000852c: f0000056    	adrp	x22, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
100008530: f94216d5    	ldr	x21, [x22, #0x428]
100008534: b4000915    	cbz	x21, 0x100008654 <_reportUnhandledErrorAux__system_u4280+0x224>
100008538: 91001fe0    	add	x0, sp, #0x7
10000853c: 94000c26    	bl	0x10000b5d4 <_strlen+0x10000b5d4>
100008540: f100041f    	cmp	x0, #0x1
100008544: 5400090b    	b.lt	0x100008664 <_reportUnhandledErrorAux__system_u4280+0x234>
100008548: aa0003f3    	mov	x19, x0
10000854c: 91000415    	add	x21, x0, #0x1
100008550: 91002401    	add	x1, x0, #0x9
100008554: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100008558: 91000000    	add	x0, x0, #0x0
10000855c: f9400008    	ldr	x8, [x0]
100008560: d63f0100    	blr	x8
100008564: 97fff44f    	bl	0x1000056a0 <_rawAlloc__system_u6797>
100008568: aa0003f4    	mov	x20, x0
10000856c: f8008413    	str	x19, [x0], #0x8
100008570: 91001fe1    	add	x1, sp, #0x7
100008574: aa1503e2    	mov	x2, x21
100008578: 94000c02    	bl	0x10000b580 <_strlen+0x10000b580>
10000857c: f94216d5    	ldr	x21, [x22, #0x428]
100008580: 1400003b    	b	0x10000866c <_reportUnhandledErrorAux__system_u4280+0x23c>
100008584: 8b1302c8    	add	x8, x22, x19
100008588: f0000009    	adrp	x9, 0x10000b000 <_bench__add95carry_u844+0x104>
10000858c: 91384929    	add	x9, x9, #0xe12
100008590: 91007273    	add	x19, x19, #0x1c
100008594: 3dc00120    	ldr	q0, [x9]
100008598: 3d800100    	str	q0, [x8]
10000859c: 3cc0c120    	ldur	q0, [x9, #0xc]
1000085a0: 3c80c100    	stur	q0, [x8, #0xc]
1000085a4: f9400e82    	ldr	x2, [x20, #0x18]
1000085a8: 8b130055    	add	x21, x2, x19
1000085ac: f11f3ebf    	cmp	x21, #0x7cf
1000085b0: 54fffa8c    	b.gt	0x100008500 <_reportUnhandledErrorAux__system_u4280+0xd0>
1000085b4: 91001fe8    	add	x8, sp, #0x7
1000085b8: 8b130100    	add	x0, x8, x19
1000085bc: f9401288    	ldr	x8, [x20, #0x20]
1000085c0: 91002108    	add	x8, x8, #0x8
1000085c4: f0000009    	adrp	x9, 0x10000b000 <_bench__add95carry_u844+0x104>
1000085c8: 9138bd29    	add	x9, x9, #0xe2f
1000085cc: f100005f    	cmp	x2, #0x0
1000085d0: 9a880121    	csel	x1, x9, x8, eq
1000085d4: 94000beb    	bl	0x10000b580 <_strlen+0x10000b580>
1000085d8: aa1503f3    	mov	x19, x21
1000085dc: f11f36bf    	cmp	x21, #0x7cd
1000085e0: 54fff94c    	b.gt	0x100008508 <_reportUnhandledErrorAux__system_u4280+0xd8>
1000085e4: 91001fe8    	add	x8, sp, #0x7
1000085e8: 528b6409    	mov	w9, #0x5b20             ; =23328
1000085ec: 78336909    	strh	w9, [x8, x19]
1000085f0: 91000a73    	add	x19, x19, #0x2
1000085f4: f9400a94    	ldr	x20, [x20, #0x10]
1000085f8: b5fff8d4    	cbnz	x20, 0x100008510 <_reportUnhandledErrorAux__system_u4280+0xe0>
1000085fc: d2800000    	mov	x0, #0x0                ; =0
100008600: 8b130013    	add	x19, x0, x19
100008604: f11f367f    	cmp	x19, #0x7cd
100008608: 54fff92c    	b.gt	0x10000852c <_reportUnhandledErrorAux__system_u4280+0xfc>
10000860c: 1400000b    	b	0x100008638 <_reportUnhandledErrorAux__system_u4280+0x208>
100008610: aa0003e2    	mov	x2, x0
100008614: 91001fe8    	add	x8, sp, #0x7
100008618: 8b130100    	add	x0, x8, x19
10000861c: aa1403e1    	mov	x1, x20
100008620: 94000bd8    	bl	0x10000b580 <_strlen+0x10000b580>
100008624: aa1403e0    	mov	x0, x20
100008628: 94000beb    	bl	0x10000b5d4 <_strlen+0x10000b5d4>
10000862c: 8b130013    	add	x19, x0, x19
100008630: f11f367f    	cmp	x19, #0x7cd
100008634: 54fff7cc    	b.gt	0x10000852c <_reportUnhandledErrorAux__system_u4280+0xfc>
100008638: 91001fe8    	add	x8, sp, #0x7
10000863c: 52814ba9    	mov	w9, #0xa5d              ; =2653
100008640: 78336909    	strh	w9, [x8, x19]
100008644: 91000a73    	add	x19, x19, #0x2
100008648: f0000056    	adrp	x22, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000864c: f94216d5    	ldr	x21, [x22, #0x428]
100008650: b5fff755    	cbnz	x21, 0x100008538 <_reportUnhandledErrorAux__system_u4280+0x108>
100008654: 91001fe0    	add	x0, sp, #0x7
100008658: aa1303e1    	mov	x1, x19
10000865c: 97fffab4    	bl	0x10000712c <_showErrorMessage__system_u4059>
100008660: 14000006    	b	0x100008678 <_reportUnhandledErrorAux__system_u4280+0x248>
100008664: d2800013    	mov	x19, #0x0               ; =0
100008668: d2800014    	mov	x20, #0x0               ; =0
10000866c: aa1303e0    	mov	x0, x19
100008670: aa1403e1    	mov	x1, x20
100008674: d63f02a0    	blr	x21
100008678: f85c83a8    	ldur	x8, [x29, #-0x38]
10000867c: 90000029    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
100008680: f9400929    	ldr	x9, [x9, #0x10]
100008684: f9400129    	ldr	x9, [x9]
100008688: eb08013f    	cmp	x9, x8
10000868c: 540000e1    	b.ne	0x1000086a8 <_reportUnhandledErrorAux__system_u4280+0x278>
100008690: 911f83ff    	add	sp, sp, #0x7e0
100008694: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100008698: a9424ff4    	ldp	x20, x19, [sp, #0x20]
10000869c: a94157f6    	ldp	x22, x21, [sp, #0x10]
1000086a0: a8c46ffc    	ldp	x28, x27, [sp], #0x40
1000086a4: d65f03c0    	ret
1000086a8: 94000b98    	bl	0x10000b508 <_strlen+0x10000b508>

00000001000086ac <_reportUnhandledError__system_u4374>:
1000086ac: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
1000086b0: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000086b4: 910043fd    	add	x29, sp, #0x10
1000086b8: aa0003f3    	mov	x19, x0
1000086bc: f0000048    	adrp	x8, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
1000086c0: f9421d08    	ldr	x8, [x8, #0x438]
1000086c4: b4000068    	cbz	x8, 0x1000086d0 <_reportUnhandledError__system_u4374+0x24>
1000086c8: aa1303e0    	mov	x0, x19
1000086cc: d63f0100    	blr	x8
1000086d0: aa1303e0    	mov	x0, x19
1000086d4: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000086d8: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000086dc: 17ffff55    	b	0x100008430 <_reportUnhandledErrorAux__system_u4280>

00000001000086e0 <_eqsink___stdZtypedthreads_u231>:
1000086e0: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
1000086e4: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000086e8: 910043fd    	add	x29, sp, #0x10
1000086ec: f9400013    	ldr	x19, [x0]
1000086f0: f9000001    	str	x1, [x0]
1000086f4: b4000513    	cbz	x19, 0x100008794 <_eqsink___stdZtypedthreads_u231+0xb4>
1000086f8: aa1303e1    	mov	x1, x19
1000086fc: f85f0c28    	ldr	x8, [x1, #-0x10]!
100008700: f1004108    	subs	x8, x8, #0x10
100008704: 540004e2    	b.hs	0x1000087a0 <_eqsink___stdZtypedthreads_u231+0xc0>
100008708: f9400262    	ldr	x2, [x19]
10000870c: 52800020    	mov	w0, #0x1                ; =1
100008710: 97fff9f2    	bl	0x100006ed8 <_rememberCycle__system_u3474>
100008714: f9400268    	ldr	x8, [x19]
100008718: f9400109    	ldr	x9, [x8]
10000871c: b4000169    	cbz	x9, 0x100008748 <_eqsink___stdZtypedthreads_u231+0x68>
100008720: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100008724: 91012000    	add	x0, x0, #0x48
100008728: f9400008    	ldr	x8, [x0]
10000872c: d63f0100    	blr	x8
100008730: aa0003f4    	mov	x20, x0
100008734: aa1303e0    	mov	x0, x19
100008738: d63f0120    	blr	x9
10000873c: 39400288    	ldrb	w8, [x20]
100008740: 350002a8    	cbnz	w8, 0x100008794 <_eqsink___stdZtypedthreads_u231+0xb4>
100008744: f9400268    	ldr	x8, [x19]
100008748: 79802108    	ldrsh	x8, [x8, #0x10]
10000874c: 91003d09    	add	x9, x8, #0xf
100008750: cb0803ea    	neg	x10, x8
100008754: 8a0a0129    	and	x9, x9, x10
100008758: 7100011f    	cmp	w8, #0x0
10000875c: 5280020a    	mov	w10, #0x10              ; =16
100008760: 9a890149    	csel	x9, x10, x9, eq
100008764: cb090261    	sub	x1, x19, x9
100008768: f100451f    	cmp	x8, #0x11
10000876c: 5400006b    	b.lt	0x100008778 <_eqsink___stdZtypedthreads_u231+0x98>
100008770: 785fe028    	ldurh	w8, [x1, #-0x2]
100008774: cb080021    	sub	x1, x1, x8
100008778: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000877c: 91000000    	add	x0, x0, #0x0
100008780: f9400008    	ldr	x8, [x0]
100008784: d63f0100    	blr	x8
100008788: a9417bfd    	ldp	x29, x30, [sp, #0x10]
10000878c: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100008790: 17fff4d3    	b	0x100005adc <_rawDealloc__system_u6973>
100008794: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100008798: a8c24ff4    	ldp	x20, x19, [sp], #0x20
10000879c: d65f03c0    	ret
1000087a0: f81f0268    	stur	x8, [x19, #-0x10]
1000087a4: f9400262    	ldr	x2, [x19]
1000087a8: 52800000    	mov	w0, #0x0                ; =0
1000087ac: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000087b0: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000087b4: 17fff9c9    	b	0x100006ed8 <_rememberCycle__system_u3474>

00000001000087b8 <_nimTestErrorFlag>:
1000087b8: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
1000087bc: a9017bfd    	stp	x29, x30, [sp, #0x10]
1000087c0: 910043fd    	add	x29, sp, #0x10
1000087c4: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000087c8: 91012000    	add	x0, x0, #0x48
1000087cc: f9400008    	ldr	x8, [x0]
1000087d0: d63f0100    	blr	x8
1000087d4: 39400008    	ldrb	w8, [x0]
1000087d8: 340000e8    	cbz	w8, 0x1000087f4 <_nimTestErrorFlag+0x3c>
1000087dc: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000087e0: 91018000    	add	x0, x0, #0x60
1000087e4: f9400008    	ldr	x8, [x0]
1000087e8: d63f0100    	blr	x8
1000087ec: f9400008    	ldr	x8, [x0]
1000087f0: b5000088    	cbnz	x8, 0x100008800 <_nimTestErrorFlag+0x48>
1000087f4: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000087f8: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000087fc: d65f03c0    	ret
100008800: aa0003f3    	mov	x19, x0
100008804: aa0803e0    	mov	x0, x8
100008808: 97ffffa9    	bl	0x1000086ac <_reportUnhandledError__system_u4374>
10000880c: aa1303e0    	mov	x0, x19
100008810: d2800001    	mov	x1, #0x0                ; =0
100008814: 97ffffb3    	bl	0x1000086e0 <_eqsink___stdZtypedthreads_u231>
100008818: 52800020    	mov	w0, #0x1                ; =1
10000881c: 94000b44    	bl	0x10000b52c <_strlen+0x10000b52c>

0000000100008820 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatssystemdotnim_Init000>:
100008820: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100008824: a9017bfd    	stp	x29, x30, [sp, #0x10]
100008828: 910043fd    	add	x29, sp, #0x10
10000882c: f0fffff3    	adrp	x19, 0x100007000 <_nimDestroyAndDispose+0x90>
100008830: 910a1273    	add	x19, x19, #0x284
100008834: 52800040    	mov	w0, #0x2                ; =2
100008838: aa1303e1    	mov	x1, x19
10000883c: 94000b60    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100008840: 52800160    	mov	w0, #0xb                ; =11
100008844: aa1303e1    	mov	x1, x19
100008848: 94000b5d    	bl	0x10000b5bc <_strlen+0x10000b5bc>
10000884c: 528000c0    	mov	w0, #0x6                ; =6
100008850: aa1303e1    	mov	x1, x19
100008854: 94000b5a    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100008858: 52800100    	mov	w0, #0x8                ; =8
10000885c: aa1303e1    	mov	x1, x19
100008860: 94000b57    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100008864: 52800080    	mov	w0, #0x4                ; =4
100008868: aa1303e1    	mov	x1, x19
10000886c: 94000b54    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100008870: 52800140    	mov	w0, #0xa                ; =10
100008874: aa1303e1    	mov	x1, x19
100008878: 94000b51    	bl	0x10000b5bc <_strlen+0x10000b5bc>
10000887c: 528001a0    	mov	w0, #0xd                ; =13
100008880: 52800021    	mov	w1, #0x1                ; =1
100008884: 94000b4e    	bl	0x10000b5bc <_strlen+0x10000b5bc>
100008888: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000888c: 91012000    	add	x0, x0, #0x48
100008890: f9400008    	ldr	x8, [x0]
100008894: d63f0100    	blr	x8
100008898: 39400008    	ldrb	w8, [x0]
10000889c: 340000e8    	cbz	w8, 0x1000088b8 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatssystemdotnim_Init000+0x98>
1000088a0: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
1000088a4: 91018000    	add	x0, x0, #0x60
1000088a8: f9400008    	ldr	x8, [x0]
1000088ac: d63f0100    	blr	x8
1000088b0: f9400008    	ldr	x8, [x0]
1000088b4: b5000088    	cbnz	x8, 0x1000088c4 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatssystemdotnim_Init000+0xa4>
1000088b8: a9417bfd    	ldp	x29, x30, [sp, #0x10]
1000088bc: a8c24ff4    	ldp	x20, x19, [sp], #0x20
1000088c0: d65f03c0    	ret
1000088c4: aa0003f3    	mov	x19, x0
1000088c8: aa0803e0    	mov	x0, x8
1000088cc: 97ffff78    	bl	0x1000086ac <_reportUnhandledError__system_u4374>
1000088d0: aa1303e0    	mov	x0, x19
1000088d4: d2800001    	mov	x1, #0x0                ; =0
1000088d8: 97ffff82    	bl	0x1000086e0 <_eqsink___stdZtypedthreads_u231>
1000088dc: 52800020    	mov	w0, #0x1                ; =1
1000088e0: 94000b13    	bl	0x10000b52c <_strlen+0x10000b52c>

00000001000088e4 <_validateUtf8__pureZunicode_u342>:
1000088e4: f100043f    	cmp	x1, #0x1
1000088e8: 5400078b    	b.lt	0x1000089d8 <_validateUtf8__pureZunicode_u342+0xf4>
1000088ec: aa0003e8    	mov	x8, x0
1000088f0: d2800000    	mov	x0, #0x0                ; =0
1000088f4: 14000004    	b	0x100008904 <_validateUtf8__pureZunicode_u342+0x20>
1000088f8: 91000400    	add	x0, x0, #0x1
1000088fc: eb01001f    	cmp	x0, x1
100008900: 540006ca    	b.ge	0x1000089d8 <_validateUtf8__pureZunicode_u342+0xf4>
100008904: 38e06909    	ldrsb	w9, [x8, x0]
100008908: 36ffff89    	tbz	w9, #0x1f, 0x1000088f8 <_validateUtf8__pureZunicode_u342+0x14>
10000890c: 92401d29    	and	x9, x9, #0xff
100008910: 927b092a    	and	x10, x9, #0xe0
100008914: f103015f    	cmp	x10, #0xc0
100008918: 54000161    	b.ne	0x100008944 <_validateUtf8__pureZunicode_u342+0x60>
10000891c: 7103093f    	cmp	w9, #0xc2
100008920: 91000409    	add	x9, x0, #0x1
100008924: fa412120    	ccmp	x9, x1, #0x0, hs
100008928: 540005aa    	b.ge	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
10000892c: 38696909    	ldrb	w9, [x8, x9]
100008930: 121a0529    	and	w9, w9, #0xc0
100008934: 7102013f    	cmp	w9, #0x80
100008938: 54000521    	b.ne	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
10000893c: 91000800    	add	x0, x0, #0x2
100008940: 17ffffef    	b	0x1000088fc <_validateUtf8__pureZunicode_u342+0x18>
100008944: 927c0d2a    	and	x10, x9, #0xf0
100008948: f103815f    	cmp	x10, #0xe0
10000894c: 540001e1    	b.ne	0x100008988 <_validateUtf8__pureZunicode_u342+0xa4>
100008950: 91000809    	add	x9, x0, #0x2
100008954: eb01013f    	cmp	x9, x1
100008958: 5400042a    	b.ge	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
10000895c: 8b08000a    	add	x10, x0, x8
100008960: 3940054a    	ldrb	w10, [x10, #0x1]
100008964: 121a054a    	and	w10, w10, #0xc0
100008968: 7102015f    	cmp	w10, #0x80
10000896c: 54000381    	b.ne	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
100008970: 38696909    	ldrb	w9, [x8, x9]
100008974: 121a0529    	and	w9, w9, #0xc0
100008978: 7102013f    	cmp	w9, #0x80
10000897c: 54000301    	b.ne	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
100008980: 91000c00    	add	x0, x0, #0x3
100008984: 17ffffde    	b	0x1000088fc <_validateUtf8__pureZunicode_u342+0x18>
100008988: 927d1129    	and	x9, x9, #0xf8
10000898c: f103c13f    	cmp	x9, #0xf0
100008990: 91000c09    	add	x9, x0, #0x3
100008994: fa410120    	ccmp	x9, x1, #0x0, eq
100008998: 5400022a    	b.ge	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
10000899c: 8b08000a    	add	x10, x0, x8
1000089a0: 3940054b    	ldrb	w11, [x10, #0x1]
1000089a4: 121a056b    	and	w11, w11, #0xc0
1000089a8: 7102017f    	cmp	w11, #0x80
1000089ac: 54000181    	b.ne	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
1000089b0: 3940094a    	ldrb	w10, [x10, #0x2]
1000089b4: 121a054a    	and	w10, w10, #0xc0
1000089b8: 7102015f    	cmp	w10, #0x80
1000089bc: 54000101    	b.ne	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
1000089c0: 38696909    	ldrb	w9, [x8, x9]
1000089c4: 121a0529    	and	w9, w9, #0xc0
1000089c8: 7102013f    	cmp	w9, #0x80
1000089cc: 54000081    	b.ne	0x1000089dc <_validateUtf8__pureZunicode_u342+0xf8>
1000089d0: 91001000    	add	x0, x0, #0x4
1000089d4: 17ffffca    	b	0x1000088fc <_validateUtf8__pureZunicode_u342+0x18>
1000089d8: 92800000    	mov	x0, #-0x1               ; =-1
1000089dc: d65f03c0    	ret

00000001000089e0 <_nucruneLen>:
1000089e0: f100043f    	cmp	x1, #0x1
1000089e4: 540004cb    	b.lt	0x100008a7c <_nucruneLen+0x9c>
1000089e8: aa0003e8    	mov	x8, x0
1000089ec: d2800009    	mov	x9, #0x0                ; =0
1000089f0: d2800000    	mov	x0, #0x0                ; =0
1000089f4: 528000ca    	mov	w10, #0x6               ; =6
1000089f8: 14000006    	b	0x100008a10 <_nucruneLen+0x30>
1000089fc: 5280002b    	mov	w11, #0x1               ; =1
100008a00: 91000400    	add	x0, x0, #0x1
100008a04: 8b0b0129    	add	x9, x9, x11
100008a08: eb01013f    	cmp	x9, x1
100008a0c: 540003aa    	b.ge	0x100008a80 <_nucruneLen+0xa0>
100008a10: 38e9690b    	ldrsb	w11, [x8, x9]
100008a14: 36ffff4b    	tbz	w11, #0x1f, 0x1000089fc <_nucruneLen+0x1c>
100008a18: 92401d6b    	and	x11, x11, #0xff
100008a1c: 927b096c    	and	x12, x11, #0xe0
100008a20: f103019f    	cmp	x12, #0xc0
100008a24: 54000061    	b.ne	0x100008a30 <_nucruneLen+0x50>
100008a28: 5280004b    	mov	w11, #0x2               ; =2
100008a2c: 17fffff5    	b	0x100008a00 <_nucruneLen+0x20>
100008a30: 927c0d6c    	and	x12, x11, #0xf0
100008a34: f103819f    	cmp	x12, #0xe0
100008a38: 54000061    	b.ne	0x100008a44 <_nucruneLen+0x64>
100008a3c: 5280006b    	mov	w11, #0x3               ; =3
100008a40: 17fffff0    	b	0x100008a00 <_nucruneLen+0x20>
100008a44: 927d116c    	and	x12, x11, #0xf8
100008a48: f103c19f    	cmp	x12, #0xf0
100008a4c: 54000061    	b.ne	0x100008a58 <_nucruneLen+0x78>
100008a50: 5280008b    	mov	w11, #0x4               ; =4
100008a54: 17ffffeb    	b	0x100008a00 <_nucruneLen+0x20>
100008a58: 927e156c    	and	x12, x11, #0xfc
100008a5c: f103e19f    	cmp	x12, #0xf8
100008a60: 54000061    	b.ne	0x100008a6c <_nucruneLen+0x8c>
100008a64: 528000ab    	mov	w11, #0x5               ; =5
100008a68: 17ffffe6    	b	0x100008a00 <_nucruneLen+0x20>
100008a6c: 927f196b    	and	x11, x11, #0xfe
100008a70: f103f17f    	cmp	x11, #0xfc
100008a74: 9a9f054b    	csinc	x11, x10, xzr, eq
100008a78: 17ffffe2    	b	0x100008a00 <_nucruneLen+0x20>
100008a7c: d2800000    	mov	x0, #0x0                ; =0
100008a80: d65f03c0    	ret

0000000100008a84 <_nsuformatBiggestFloat>:
100008a84: a9bc5ff8    	stp	x24, x23, [sp, #-0x40]!
100008a88: a90157f6    	stp	x22, x21, [sp, #0x10]
100008a8c: a9024ff4    	stp	x20, x19, [sp, #0x20]
100008a90: a9037bfd    	stp	x29, x30, [sp, #0x30]
100008a94: 9100c3fd    	add	x29, sp, #0x30
100008a98: d12803ff    	sub	sp, sp, #0xa00
100008a9c: aa0203f3    	mov	x19, x2
100008aa0: 90000028    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100008aa4: f9400908    	ldr	x8, [x8, #0x10]
100008aa8: f9400108    	ldr	x8, [x8]
100008aac: f81c83a8    	stur	x8, [x29, #-0x38]
100008ab0: 528004a8    	mov	w8, #0x25               ; =37
100008ab4: 39006be8    	strb	w8, [sp, #0x1a]
100008ab8: b7f801a1    	tbnz	x1, #0x3f, 0x100008aec <_nsuformatBiggestFloat+0x68>
100008abc: 5285c468    	mov	w8, #0x2e23             ; =11811
100008ac0: 7801b3e8    	sturh	w8, [sp, #0x1b]
100008ac4: 52800548    	mov	w8, #0x2a               ; =42
100008ac8: 390077e8    	strb	w8, [sp, #0x1d]
100008acc: f0000008    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100008ad0: 91214108    	add	x8, x8, #0x850
100008ad4: 38604908    	ldrb	w8, [x8, w0, uxtw]
100008ad8: 39007be8    	strb	w8, [sp, #0x1e]
100008adc: 39007fff    	strb	wzr, [sp, #0x1f]
100008ae0: fd0007e0    	str	d0, [sp, #0x8]
100008ae4: f90003e1    	str	x1, [sp]
100008ae8: 14000007    	b	0x100008b04 <_nsuformatBiggestFloat+0x80>
100008aec: f0000008    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100008af0: 91214108    	add	x8, x8, #0x850
100008af4: 38604908    	ldrb	w8, [x8, w0, uxtw]
100008af8: 39006fe8    	strb	w8, [sp, #0x1b]
100008afc: 390073ff    	strb	wzr, [sp, #0x1c]
100008b00: fd0003e0    	str	d0, [sp]
100008b04: 9100cfe0    	add	x0, sp, #0x33
100008b08: 91006be2    	add	x2, sp, #0x1a
100008b0c: 528138a1    	mov	w1, #0x9c5              ; =2501
100008b10: 94000aae    	bl	0x10000b5c8 <_strlen+0x10000b5c8>
100008b14: aa0003f4    	mov	x20, x0
100008b18: 93407c00    	sxtw	x0, w0
100008b1c: 97fffbed    	bl	0x100007ad0 <_mnewString>
100008b20: a90207e0    	stp	x0, x1, [sp, #0x20]
100008b24: 7100069f    	cmp	w20, #0x1
100008b28: 5400036b    	b.lt	0x100008b94 <_nsuformatBiggestFloat+0x110>
100008b2c: d2800015    	mov	x21, #0x0               ; =0
100008b30: 2a1403f4    	mov	w20, w20
100008b34: 9100cff6    	add	x22, sp, #0x33
100008b38: 14000009    	b	0x100008b5c <_nsuformatBiggestFloat+0xd8>
100008b3c: 910083e0    	add	x0, sp, #0x20
100008b40: 97fffc04    	bl	0x100007b50 <_nimPrepareStrMutationImpl__system_u2387>
100008b44: f94017e8    	ldr	x8, [sp, #0x28]
100008b48: 8b150108    	add	x8, x8, x21
100008b4c: 39002117    	strb	w23, [x8, #0x8]
100008b50: 910006b5    	add	x21, x21, #0x1
100008b54: eb15029f    	cmp	x20, x21
100008b58: 540001c0    	b.eq	0x100008b90 <_nsuformatBiggestFloat+0x10c>
100008b5c: 38756ad7    	ldrb	w23, [x22, x21]
100008b60: 321f02e8    	orr	w8, w23, #0x2
100008b64: 7100b91f    	cmp	w8, #0x2e
100008b68: 540000c1    	b.ne	0x100008b80 <_nsuformatBiggestFloat+0xfc>
100008b6c: f94017e8    	ldr	x8, [sp, #0x28]
100008b70: 39401d09    	ldrb	w9, [x8, #0x7]
100008b74: aa1303f7    	mov	x23, x19
100008b78: 3737fe29    	tbnz	w9, #0x6, 0x100008b3c <_nsuformatBiggestFloat+0xb8>
100008b7c: 17fffff3    	b	0x100008b48 <_nsuformatBiggestFloat+0xc4>
100008b80: f94017e8    	ldr	x8, [sp, #0x28]
100008b84: 39401d09    	ldrb	w9, [x8, #0x7]
100008b88: 3737fda9    	tbnz	w9, #0x6, 0x100008b3c <_nsuformatBiggestFloat+0xb8>
100008b8c: 17ffffef    	b	0x100008b48 <_nsuformatBiggestFloat+0xc4>
100008b90: a94207e0    	ldp	x0, x1, [sp, #0x20]
100008b94: f85c83a8    	ldur	x8, [x29, #-0x38]
100008b98: 90000029    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
100008b9c: f9400929    	ldr	x9, [x9, #0x10]
100008ba0: f9400129    	ldr	x9, [x9]
100008ba4: eb08013f    	cmp	x9, x8
100008ba8: 540000e1    	b.ne	0x100008bc4 <_nsuformatBiggestFloat+0x140>
100008bac: 912803ff    	add	sp, sp, #0xa00
100008bb0: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100008bb4: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100008bb8: a94157f6    	ldp	x22, x21, [sp, #0x10]
100008bbc: a8c45ff8    	ldp	x24, x23, [sp], #0x40
100008bc0: d65f03c0    	ret
100008bc4: 94000a51    	bl	0x10000b508 <_strlen+0x10000b508>

0000000100008bc8 <_nsuRepeatChar>:
100008bc8: d10103ff    	sub	sp, sp, #0x40
100008bcc: a90157f6    	stp	x22, x21, [sp, #0x10]
100008bd0: a9024ff4    	stp	x20, x19, [sp, #0x20]
100008bd4: a9037bfd    	stp	x29, x30, [sp, #0x30]
100008bd8: 9100c3fd    	add	x29, sp, #0x30
100008bdc: aa0103f4    	mov	x20, x1
100008be0: aa0003f3    	mov	x19, x0
100008be4: aa0103e0    	mov	x0, x1
100008be8: 97fffbba    	bl	0x100007ad0 <_mnewString>
100008bec: a90007e0    	stp	x0, x1, [sp]
100008bf0: f1000694    	subs	x20, x20, #0x1
100008bf4: 5400022b    	b.lt	0x100008c38 <_nsuRepeatChar+0x70>
100008bf8: d2800015    	mov	x21, #0x0               ; =0
100008bfc: 39401c28    	ldrb	w8, [x1, #0x7]
100008c00: 36300088    	tbz	w8, #0x6, 0x100008c10 <_nsuRepeatChar+0x48>
100008c04: 910003e0    	mov	x0, sp
100008c08: 97fffbd2    	bl	0x100007b50 <_nimPrepareStrMutationImpl__system_u2387>
100008c0c: f94007e1    	ldr	x1, [sp, #0x8]
100008c10: 8b150028    	add	x8, x1, x21
100008c14: 39002113    	strb	w19, [x8, #0x8]
100008c18: eb15029f    	cmp	x20, x21
100008c1c: 540000c0    	b.eq	0x100008c34 <_nsuRepeatChar+0x6c>
100008c20: f94007e1    	ldr	x1, [sp, #0x8]
100008c24: 910006b5    	add	x21, x21, #0x1
100008c28: 39401c28    	ldrb	w8, [x1, #0x7]
100008c2c: 3737fec8    	tbnz	w8, #0x6, 0x100008c04 <_nsuRepeatChar+0x3c>
100008c30: 17fffff8    	b	0x100008c10 <_nsuRepeatChar+0x48>
100008c34: a94007e0    	ldp	x0, x1, [sp]
100008c38: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100008c3c: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100008c40: a94157f6    	ldp	x22, x21, [sp, #0x10]
100008c44: 910103ff    	add	sp, sp, #0x40
100008c48: d65f03c0    	ret

0000000100008c4c <_nsuToUpperAsciiChar>:
100008c4c: 12001c08    	and	w8, w0, #0xff
100008c50: 51018509    	sub	w9, w8, #0x61
100008c54: 521b010a    	eor	w10, w8, #0x20
100008c58: 7100693f    	cmp	w9, #0x1a
100008c5c: 1a883148    	csel	w8, w10, w8, lo
100008c60: 13001d00    	sxtb	w0, w8
100008c64: d65f03c0    	ret

0000000100008c68 <_nsuToUpperAsciiStr>:
100008c68: d10103ff    	sub	sp, sp, #0x40
100008c6c: a90157f6    	stp	x22, x21, [sp, #0x10]
100008c70: a9024ff4    	stp	x20, x19, [sp, #0x20]
100008c74: a9037bfd    	stp	x29, x30, [sp, #0x30]
100008c78: 9100c3fd    	add	x29, sp, #0x30
100008c7c: aa0103f4    	mov	x20, x1
100008c80: aa0003f5    	mov	x21, x0
100008c84: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100008c88: 91012000    	add	x0, x0, #0x48
100008c8c: f9400008    	ldr	x8, [x0]
100008c90: d63f0100    	blr	x8
100008c94: aa0003f3    	mov	x19, x0
100008c98: aa1503e0    	mov	x0, x21
100008c9c: 97fffb8d    	bl	0x100007ad0 <_mnewString>
100008ca0: a90007e0    	stp	x0, x1, [sp]
100008ca4: f10006b5    	subs	x21, x21, #0x1
100008ca8: 5400032b    	b.lt	0x100008d0c <_nsuToUpperAsciiStr+0xa4>
100008cac: d2800016    	mov	x22, #0x0               ; =0
100008cb0: 91002294    	add	x20, x20, #0x8
100008cb4: b40000a1    	cbz	x1, 0x100008cc8 <_nsuToUpperAsciiStr+0x60>
100008cb8: 39401c28    	ldrb	w8, [x1, #0x7]
100008cbc: 36300068    	tbz	w8, #0x6, 0x100008cc8 <_nsuToUpperAsciiStr+0x60>
100008cc0: 910003e0    	mov	x0, sp
100008cc4: 97fffba3    	bl	0x100007b50 <_nimPrepareStrMutationImpl__system_u2387>
100008cc8: 39400268    	ldrb	w8, [x19]
100008ccc: 350001e8    	cbnz	w8, 0x100008d08 <_nsuToUpperAsciiStr+0xa0>
100008cd0: 38766a88    	ldrb	w8, [x20, x22]
100008cd4: 51018509    	sub	w9, w8, #0x61
100008cd8: 521b010a    	eor	w10, w8, #0x20
100008cdc: 7100693f    	cmp	w9, #0x1a
100008ce0: 1a883148    	csel	w8, w10, w8, lo
100008ce4: f94007e9    	ldr	x9, [sp, #0x8]
100008ce8: 8b160129    	add	x9, x9, x22
100008cec: 39002128    	strb	w8, [x9, #0x8]
100008cf0: eb1602bf    	cmp	x21, x22
100008cf4: 540000a0    	b.eq	0x100008d08 <_nsuToUpperAsciiStr+0xa0>
100008cf8: f94007e1    	ldr	x1, [sp, #0x8]
100008cfc: 910006d6    	add	x22, x22, #0x1
100008d00: b5fffdc1    	cbnz	x1, 0x100008cb8 <_nsuToUpperAsciiStr+0x50>
100008d04: 17fffff1    	b	0x100008cc8 <_nsuToUpperAsciiStr+0x60>
100008d08: a94007e0    	ldp	x0, x1, [sp]
100008d0c: a9437bfd    	ldp	x29, x30, [sp, #0x30]
100008d10: a9424ff4    	ldp	x20, x19, [sp, #0x20]
100008d14: a94157f6    	ldp	x22, x21, [sp, #0x10]
100008d18: 910103ff    	add	sp, sp, #0x40
100008d1c: d65f03c0    	ret

0000000100008d20 <_cpuTime__pureZtimes_u5240>:
100008d20: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100008d24: 910003fd    	mov	x29, sp
100008d28: 940009fe    	bl	0x10000b520 <_strlen+0x10000b520>
100008d2c: 9e620000    	scvtf	d0, x0
100008d30: d2d09008    	mov	x8, #0x848000000000     ; =145685290680320
100008d34: f2e825c8    	movk	x8, #0x412e, lsl #48
100008d38: 9e670101    	fmov	d1, x8
100008d3c: 1e611800    	fdiv	d0, d0, d1
100008d40: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100008d44: d65f03c0    	ret

0000000100008d48 <_inNanoseconds__pureZtimes_u878>:
100008d48: 52994008    	mov	w8, #0xca00             ; =51712
100008d4c: 72a77348    	movk	w8, #0x3b9a, lsl #16
100008d50: 9b080400    	madd	x0, x0, x8, x1
100008d54: d65f03c0    	ret

0000000100008d58 <_normalize__pureZtimes_u568>:
100008d58: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100008d5c: 910003fd    	mov	x29, sp
100008d60: aa0003e8    	mov	x8, x0
100008d64: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100008d68: 91012000    	add	x0, x0, #0x48
100008d6c: f9400009    	ldr	x9, [x0]
100008d70: d63f0120    	blr	x9
100008d74: 39400009    	ldrb	w9, [x0]
100008d78: 35000249    	cbnz	w9, 0x100008dc0 <_normalize__pureZtimes_u568+0x68>
100008d7c: d2929669    	mov	x9, #0x94b3             ; =38067
100008d80: f2a4dac9    	movk	x9, #0x26d6, lsl #16
100008d84: f2c17d09    	movk	x9, #0xbe8, lsl #32
100008d88: f2e225c9    	movk	x9, #0x112e, lsl #48
100008d8c: 9b497c29    	smulh	x9, x1, x9
100008d90: 935afd2a    	asr	x10, x9, #26
100008d94: 8b49fd49    	add	x9, x10, x9, lsr #63
100008d98: 8b080128    	add	x8, x9, x8
100008d9c: 5299400a    	mov	w10, #0xca00            ; =51712
100008da0: 72a7734a    	movk	w10, #0x3b9a, lsl #16
100008da4: 9b0a8529    	msub	x9, x9, x10, x1
100008da8: 8b0a012a    	add	x10, x9, x10
100008dac: 8b89fd00    	add	x0, x8, x9, asr #63
100008db0: f100013f    	cmp	x9, #0x0
100008db4: 9a89b141    	csel	x1, x10, x9, lt
100008db8: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100008dbc: d65f03c0    	ret
100008dc0: d2800000    	mov	x0, #0x0                ; =0
100008dc4: d2800001    	mov	x1, #0x0                ; =0
100008dc8: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100008dcc: d65f03c0    	ret

0000000100008dd0 <_ntDivDuration>:
100008dd0: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100008dd4: 910003fd    	mov	x29, sp
100008dd8: aa0003e8    	mov	x8, x0
100008ddc: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100008de0: 91012000    	add	x0, x0, #0x48
100008de4: f9400009    	ldr	x9, [x0]
100008de8: d63f0120    	blr	x9
100008dec: 39400009    	ldrb	w9, [x0]
100008df0: 350002c9    	cbnz	w9, 0x100008e48 <_ntDivDuration+0x78>
100008df4: 9ac20d09    	sdiv	x9, x8, x2
100008df8: 9b02a128    	msub	x8, x9, x2, x8
100008dfc: 5299400a    	mov	w10, #0xca00            ; =51712
100008e00: 72a7734a    	movk	w10, #0x3b9a, lsl #16
100008e04: 9b0a0508    	madd	x8, x8, x10, x1
100008e08: 9ac20d08    	sdiv	x8, x8, x2
100008e0c: d292966b    	mov	x11, #0x94b3            ; =38067
100008e10: f2a4dacb    	movk	x11, #0x26d6, lsl #16
100008e14: f2c17d0b    	movk	x11, #0xbe8, lsl #32
100008e18: f2e225cb    	movk	x11, #0x112e, lsl #48
100008e1c: 9b4b7d0b    	smulh	x11, x8, x11
100008e20: 935afd6c    	asr	x12, x11, #26
100008e24: 8b4bfd8b    	add	x11, x12, x11, lsr #63
100008e28: 8b090169    	add	x9, x11, x9
100008e2c: 9b0aa168    	msub	x8, x11, x10, x8
100008e30: 8b0a010a    	add	x10, x8, x10
100008e34: 8b88fd20    	add	x0, x9, x8, asr #63
100008e38: f100011f    	cmp	x8, #0x0
100008e3c: 9a88b141    	csel	x1, x10, x8, lt
100008e40: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100008e44: d65f03c0    	ret
100008e48: d2800000    	mov	x0, #0x0                ; =0
100008e4c: d2800001    	mov	x1, #0x0                ; =0
100008e50: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100008e54: d65f03c0    	ret

0000000100008e58 <_initDuration__pureZtimes_u489>:
100008e58: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
100008e5c: a9017bfd    	stp	x29, x30, [sp, #0x10]
100008e60: 910043fd    	add	x29, sp, #0x10
100008e64: aa0003e8    	mov	x8, x0
100008e68: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100008e6c: 91012000    	add	x0, x0, #0x48
100008e70: f9400009    	ldr	x9, [x0]
100008e74: d63f0120    	blr	x9
100008e78: 39400009    	ldrb	w9, [x0]
100008e7c: 35000729    	cbnz	w9, 0x100008f60 <_initDuration__pureZtimes_u489+0x108>
100008e80: 52875009    	mov	w9, #0x3a80             ; =14976
100008e84: 72a00129    	movk	w9, #0x9, lsl #16
100008e88: 528a300a    	mov	w10, #0x5180            ; =20864
100008e8c: 72a0002a    	movk	w10, #0x1, lsl #16
100008e90: 5280078b    	mov	w11, #0x3c              ; =60
100008e94: 5281c20c    	mov	w12, #0xe10             ; =3600
100008e98: d29ef9ed    	mov	x13, #0xf7cf            ; =63439
100008e9c: f2bc6a6d    	movk	x13, #0xe353, lsl #16
100008ea0: f2d374ad    	movk	x13, #0x9ba5, lsl #32
100008ea4: f2e4188d    	movk	x13, #0x20c4, lsl #48
100008ea8: 9b4d7c4d    	smulh	x13, x2, x13
100008eac: 9347fdae    	asr	x14, x13, #7
100008eb0: 8b4dfdcd    	add	x13, x14, x13, lsr #63
100008eb4: d2869b6e    	mov	x14, #0x34db            ; =13531
100008eb8: f2baf6ce    	movk	x14, #0xd7b6, lsl #16
100008ebc: f2dbd04e    	movk	x14, #0xde82, lsl #32
100008ec0: f2e8636e    	movk	x14, #0x431b, lsl #48
100008ec4: 9b4e7c2e    	smulh	x14, x1, x14
100008ec8: 9352fdcf    	asr	x15, x14, #18
100008ecc: 8b4efdee    	add	x14, x15, x14, lsr #63
100008ed0: d292966f    	mov	x15, #0x94b3            ; =38067
100008ed4: f2a4dacf    	movk	x15, #0x26d6, lsl #16
100008ed8: f2c17d0f    	movk	x15, #0xbe8, lsl #32
100008edc: f2e225cf    	movk	x15, #0x112e, lsl #48
100008ee0: 9b4f7d10    	smulh	x16, x8, x15
100008ee4: 935afe11    	asr	x17, x16, #26
100008ee8: 8b50fe30    	add	x16, x17, x16, lsr #63
100008eec: 52807d11    	mov	w17, #0x3e8             ; =1000
100008ef0: 9b1189a0    	msub	x0, x13, x17, x2
100008ef4: 52884802    	mov	w2, #0x4240             ; =16960
100008ef8: 72a001e2    	movk	w2, #0xf, lsl #16
100008efc: 9b0285c1    	msub	x1, x14, x2, x1
100008f00: 52994013    	mov	w19, #0xca00            ; =51712
100008f04: 72a77353    	movk	w19, #0x3b9a, lsl #16
100008f08: 9b13a208    	msub	x8, x16, x19, x8
100008f0c: 9b112028    	madd	x8, x1, x17, x8
100008f10: 9b022008    	madd	x8, x0, x2, x8
100008f14: 9b4f7d0f    	smulh	x15, x8, x15
100008f18: 935afdf1    	asr	x17, x15, #26
100008f1c: 8b4ffe2f    	add	x15, x17, x15, lsr #63
100008f20: 9b13a1e8    	msub	x8, x15, x19, x8
100008f24: 8b130111    	add	x17, x8, x19
100008f28: 8b1001ce    	add	x14, x14, x16
100008f2c: 8b0d006d    	add	x13, x3, x13
100008f30: 8b0d01cd    	add	x13, x14, x13
100008f34: 9b0b348b    	madd	x11, x4, x11, x13
100008f38: 9b0c2cab    	madd	x11, x5, x12, x11
100008f3c: 9b0a2cca    	madd	x10, x6, x10, x11
100008f40: 8b0f014a    	add	x10, x10, x15
100008f44: 9b0928e9    	madd	x9, x7, x9, x10
100008f48: 8b88fd20    	add	x0, x9, x8, asr #63
100008f4c: f100011f    	cmp	x8, #0x0
100008f50: 9a88b221    	csel	x1, x17, x8, lt
100008f54: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100008f58: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100008f5c: d65f03c0    	ret
100008f60: d2800000    	mov	x0, #0x0                ; =0
100008f64: d2800001    	mov	x1, #0x0                ; =0
100008f68: a9417bfd    	ldp	x29, x30, [sp, #0x10]
100008f6c: a8c24ff4    	ldp	x20, x19, [sp], #0x20
100008f70: d65f03c0    	ret

0000000100008f74 <_getMonoTime__stdZmonotimes_u10>:
100008f74: d100c3ff    	sub	sp, sp, #0x30
100008f78: a9014ff4    	stp	x20, x19, [sp, #0x10]
100008f7c: a9027bfd    	stp	x29, x30, [sp, #0x20]
100008f80: 910083fd    	add	x29, sp, #0x20
100008f84: 94000979    	bl	0x10000b568 <_strlen+0x10000b568>
100008f88: aa0003f3    	mov	x19, x0
100008f8c: f90007ff    	str	xzr, [sp, #0x8]
100008f90: 910023e0    	add	x0, sp, #0x8
100008f94: 94000978    	bl	0x10000b574 <_strlen+0x10000b574>
100008f98: 294127e8    	ldp	w8, w9, [sp, #0x8]
100008f9c: 9b087e68    	mul	x8, x19, x8
100008fa0: 9ac90d00    	sdiv	x0, x8, x9
100008fa4: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100008fa8: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100008fac: 9100c3ff    	add	sp, sp, #0x30
100008fb0: d65f03c0    	ret

0000000100008fb4 <_minus___stdZmonotimes_u58>:
100008fb4: cb010000    	sub	x0, x0, x1
100008fb8: d2800001    	mov	x1, #0x0                ; =0
100008fbc: d2800002    	mov	x2, #0x0                ; =0
100008fc0: d2800003    	mov	x3, #0x0                ; =0
100008fc4: d2800004    	mov	x4, #0x0                ; =0
100008fc8: d2800005    	mov	x5, #0x0                ; =0
100008fcc: d2800006    	mov	x6, #0x0                ; =0
100008fd0: d2800007    	mov	x7, #0x0                ; =0
100008fd4: 17ffffa1    	b	0x100008e58 <_initDuration__pureZtimes_u489>

0000000100008fd8 <_rotl__pureZrandom_u27>:
100008fd8: 4b0103e8    	neg	w8, w1
100008fdc: 9ac82c00    	ror	x0, x0, x8
100008fe0: d65f03c0    	ret

0000000100008fe4 <_next__pureZrandom_u39>:
100008fe4: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100008fe8: 910003fd    	mov	x29, sp
100008fec: aa0003e8    	mov	x8, x0
100008ff0: 90000040    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100008ff4: 91012000    	add	x0, x0, #0x48
100008ff8: f9400009    	ldr	x9, [x0]
100008ffc: d63f0120    	blr	x9
100009000: a9402909    	ldp	x9, x10, [x8]
100009004: 3940000b    	ldrb	w11, [x0]
100009008: 350000eb    	cbnz	w11, 0x100009024 <_next__pureZrandom_u39+0x40>
10000900c: 93c9252b    	ror	x11, x9, #0x9
100009010: ca09014c    	eor	x12, x10, x9
100009014: ca0c396b    	eor	x11, x11, x12, lsl #14
100009018: ca0c016b    	eor	x11, x11, x12
10000901c: 93cc718c    	ror	x12, x12, #0x1c
100009020: a900310b    	stp	x11, x12, [x8]
100009024: 8b090140    	add	x0, x10, x9
100009028: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000902c: d65f03c0    	ret

0000000100009030 <_rand__pureZrandom_u121>:
100009030: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100009034: 910003fd    	mov	x29, sp
100009038: aa0003e8    	mov	x8, x0
10000903c: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100009040: 91012000    	add	x0, x0, #0x48
100009044: f9400009    	ldr	x9, [x0]
100009048: d63f0120    	blr	x9
10000904c: b100043f    	cmn	x1, #0x1
100009050: 540003c0    	b.eq	0x1000090c8 <_rand__pureZrandom_u121+0x98>
100009054: b4000341    	cbz	x1, 0x1000090bc <_rand__pureZrandom_u121+0x8c>
100009058: 39400009    	ldrb	w9, [x0]
10000905c: 35000509    	cbnz	w9, 0x1000090fc <_rand__pureZrandom_u121+0xcc>
100009060: d280000a    	mov	x10, #0x0               ; =0
100009064: 92800009    	mov	x9, #-0x1               ; =-1
100009068: 9ac10929    	udiv	x9, x9, x1
10000906c: 9b017d29    	mul	x9, x9, x1
100009070: a940310b    	ldp	x11, x12, [x8]
100009074: aa0c03ed    	mov	x13, x12
100009078: aa0b03ee    	mov	x14, x11
10000907c: 93cb256b    	ror	x11, x11, #0x9
100009080: ca0c01cc    	eor	x12, x14, x12
100009084: ca0c396b    	eor	x11, x11, x12, lsl #14
100009088: ca0c016b    	eor	x11, x11, x12
10000908c: 93cc718c    	ror	x12, x12, #0x1c
100009090: 8b0d01cd    	add	x13, x14, x13
100009094: eb0901bf    	cmp	x13, x9
100009098: 540000a9    	b.ls	0x1000090ac <_rand__pureZrandom_u121+0x7c>
10000909c: 9100054e    	add	x14, x10, #0x1
1000090a0: f100515f    	cmp	x10, #0x14
1000090a4: aa0e03ea    	mov	x10, x14
1000090a8: 54fffe69    	b.ls	0x100009074 <_rand__pureZrandom_u121+0x44>
1000090ac: a900310b    	stp	x11, x12, [x8]
1000090b0: 91000428    	add	x8, x1, #0x1
1000090b4: 9ac809a9    	udiv	x9, x13, x8
1000090b8: 9b08b521    	msub	x1, x9, x8, x13
1000090bc: aa0103e0    	mov	x0, x1
1000090c0: a8c17bfd    	ldp	x29, x30, [sp], #0x10
1000090c4: d65f03c0    	ret
1000090c8: a9402909    	ldp	x9, x10, [x8]
1000090cc: 3940000b    	ldrb	w11, [x0]
1000090d0: 350000eb    	cbnz	w11, 0x1000090ec <_rand__pureZrandom_u121+0xbc>
1000090d4: 93c9252b    	ror	x11, x9, #0x9
1000090d8: ca09014c    	eor	x12, x10, x9
1000090dc: ca0c396b    	eor	x11, x11, x12, lsl #14
1000090e0: ca0c016b    	eor	x11, x11, x12
1000090e4: 93cc718c    	ror	x12, x12, #0x1c
1000090e8: a900310b    	stp	x11, x12, [x8]
1000090ec: 8b090141    	add	x1, x10, x9
1000090f0: aa0103e0    	mov	x0, x1
1000090f4: a8c17bfd    	ldp	x29, x30, [sp], #0x10
1000090f8: d65f03c0    	ret
1000090fc: d2800001    	mov	x1, #0x0                ; =0
100009100: aa0103e0    	mov	x0, x1
100009104: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100009108: d65f03c0    	ret

000000010000910c <_rand__pureZrandom_u117>:
10000910c: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
100009110: 910003fd    	mov	x29, sp
100009114: aa0003e8    	mov	x8, x0
100009118: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000911c: 91012000    	add	x0, x0, #0x48
100009120: f9400009    	ldr	x9, [x0]
100009124: d63f0120    	blr	x9
100009128: aa0003e9    	mov	x9, x0
10000912c: b100043f    	cmn	x1, #0x1
100009130: 54000100    	b.eq	0x100009150 <_rand__pureZrandom_u117+0x44>
100009134: b50002c1    	cbnz	x1, 0x10000918c <_rand__pureZrandom_u117+0x80>
100009138: d2800000    	mov	x0, #0x0                ; =0
10000913c: 39400129    	ldrb	w9, [x9]
100009140: 72001d3f    	tst	w9, #0xff
100009144: 540001e1    	b.ne	0x100009180 <_rand__pureZrandom_u117+0x74>
100009148: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000914c: d65f03c0    	ret
100009150: a9402d0a    	ldp	x10, x11, [x8]
100009154: 39400129    	ldrb	w9, [x9]
100009158: 350000e9    	cbnz	w9, 0x100009174 <_rand__pureZrandom_u117+0x68>
10000915c: 93ca254c    	ror	x12, x10, #0x9
100009160: ca0a016d    	eor	x13, x11, x10
100009164: ca0d398c    	eor	x12, x12, x13, lsl #14
100009168: ca0d018c    	eor	x12, x12, x13
10000916c: 93cd71ad    	ror	x13, x13, #0x1c
100009170: a900350c    	stp	x12, x13, [x8]
100009174: 8b0a0160    	add	x0, x11, x10
100009178: 72001d3f    	tst	w9, #0xff
10000917c: 54fffe60    	b.eq	0x100009148 <_rand__pureZrandom_u117+0x3c>
100009180: d2800000    	mov	x0, #0x0                ; =0
100009184: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100009188: d65f03c0    	ret
10000918c: 39400129    	ldrb	w9, [x9]
100009190: 35ffff89    	cbnz	w9, 0x100009180 <_rand__pureZrandom_u117+0x74>
100009194: d280000a    	mov	x10, #0x0               ; =0
100009198: 92800009    	mov	x9, #-0x1               ; =-1
10000919c: 9ac10929    	udiv	x9, x9, x1
1000091a0: 9b017d29    	mul	x9, x9, x1
1000091a4: a940310b    	ldp	x11, x12, [x8]
1000091a8: aa0c03ed    	mov	x13, x12
1000091ac: aa0b03ee    	mov	x14, x11
1000091b0: 93cb256b    	ror	x11, x11, #0x9
1000091b4: ca0e018c    	eor	x12, x12, x14
1000091b8: ca0c396b    	eor	x11, x11, x12, lsl #14
1000091bc: ca0c016b    	eor	x11, x11, x12
1000091c0: 93cc718c    	ror	x12, x12, #0x1c
1000091c4: 8b0e01ad    	add	x13, x13, x14
1000091c8: eb0901bf    	cmp	x13, x9
1000091cc: 540000a9    	b.ls	0x1000091e0 <_rand__pureZrandom_u117+0xd4>
1000091d0: 9100054e    	add	x14, x10, #0x1
1000091d4: f100515f    	cmp	x10, #0x14
1000091d8: aa0e03ea    	mov	x10, x14
1000091dc: 54fffe69    	b.ls	0x1000091a8 <_rand__pureZrandom_u117+0x9c>
1000091e0: a900310b    	stp	x11, x12, [x8]
1000091e4: 91000428    	add	x8, x1, #0x1
1000091e8: 9ac809a9    	udiv	x9, x13, x8
1000091ec: 9b08b520    	msub	x0, x9, x8, x13
1000091f0: a8c17bfd    	ldp	x29, x30, [sp], #0x10
1000091f4: d65f03c0    	ret

00000001000091f8 <_rand__pureZrandom_u146>:
1000091f8: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
1000091fc: 910003fd    	mov	x29, sp
100009200: aa0003e8    	mov	x8, x0
100009204: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100009208: 91012000    	add	x0, x0, #0x48
10000920c: f9400009    	ldr	x9, [x0]
100009210: d63f0120    	blr	x9
100009214: aa0003e9    	mov	x9, x0
100009218: b100051f    	cmn	x8, #0x1
10000921c: 54000100    	b.eq	0x10000923c <_rand__pureZrandom_u146+0x44>
100009220: b5000308    	cbnz	x8, 0x100009280 <_rand__pureZrandom_u146+0x88>
100009224: d2800000    	mov	x0, #0x0                ; =0
100009228: 39400128    	ldrb	w8, [x9]
10000922c: 72001d1f    	tst	w8, #0xff
100009230: 54000221    	b.ne	0x100009274 <_rand__pureZrandom_u146+0x7c>
100009234: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100009238: d65f03c0    	ret
10000923c: d000004c    	adrp	x12, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
100009240: 9112618c    	add	x12, x12, #0x498
100009244: a9402d8a    	ldp	x10, x11, [x12]
100009248: 39400128    	ldrb	w8, [x9]
10000924c: 350000e8    	cbnz	w8, 0x100009268 <_rand__pureZrandom_u146+0x70>
100009250: 93ca2549    	ror	x9, x10, #0x9
100009254: ca0a016d    	eor	x13, x11, x10
100009258: ca0d3929    	eor	x9, x9, x13, lsl #14
10000925c: ca0d0129    	eor	x9, x9, x13
100009260: 93cd71ad    	ror	x13, x13, #0x1c
100009264: a9003589    	stp	x9, x13, [x12]
100009268: 8b0a0160    	add	x0, x11, x10
10000926c: 72001d1f    	tst	w8, #0xff
100009270: 54fffe20    	b.eq	0x100009234 <_rand__pureZrandom_u146+0x3c>
100009274: d2800000    	mov	x0, #0x0                ; =0
100009278: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000927c: d65f03c0    	ret
100009280: 39400129    	ldrb	w9, [x9]
100009284: 35ffff89    	cbnz	w9, 0x100009274 <_rand__pureZrandom_u146+0x7c>
100009288: d280000b    	mov	x11, #0x0               ; =0
10000928c: 92800009    	mov	x9, #-0x1               ; =-1
100009290: 9ac80929    	udiv	x9, x9, x8
100009294: 9b087d2a    	mul	x10, x9, x8
100009298: d0000049    	adrp	x9, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000929c: 91126129    	add	x9, x9, #0x498
1000092a0: a940352c    	ldp	x12, x13, [x9]
1000092a4: aa0d03ee    	mov	x14, x13
1000092a8: aa0c03ef    	mov	x15, x12
1000092ac: 93cc258c    	ror	x12, x12, #0x9
1000092b0: ca0f01ad    	eor	x13, x13, x15
1000092b4: ca0d398c    	eor	x12, x12, x13, lsl #14
1000092b8: ca0d018c    	eor	x12, x12, x13
1000092bc: 93cd71ad    	ror	x13, x13, #0x1c
1000092c0: 8b0f01ce    	add	x14, x14, x15
1000092c4: eb0a01df    	cmp	x14, x10
1000092c8: 540000a9    	b.ls	0x1000092dc <_rand__pureZrandom_u146+0xe4>
1000092cc: 9100056f    	add	x15, x11, #0x1
1000092d0: f100517f    	cmp	x11, #0x14
1000092d4: aa0f03eb    	mov	x11, x15
1000092d8: 54fffe69    	b.ls	0x1000092a4 <_rand__pureZrandom_u146+0xac>
1000092dc: a900352c    	stp	x12, x13, [x9]
1000092e0: 91000508    	add	x8, x8, #0x1
1000092e4: 9ac809c9    	udiv	x9, x14, x8
1000092e8: 9b08b920    	msub	x0, x9, x8, x14
1000092ec: a8c17bfd    	ldp	x29, x30, [sp], #0x10
1000092f0: d65f03c0    	ret

00000001000092f4 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatspureatsrandomdotnim_Init000>:
1000092f4: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
1000092f8: 910003fd    	mov	x29, sp
1000092fc: d0000008    	adrp	x8, 0x10000b000 <_bench__add95carry_u844+0x104>
100009300: 91226108    	add	x8, x8, #0x898
100009304: 3dc00100    	ldr	q0, [x8]
100009308: d0000048    	adrp	x8, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000930c: 91126108    	add	x8, x8, #0x498
100009310: 3d800100    	str	q0, [x8]
100009314: d0000040    	adrp	x0, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
100009318: 91112000    	add	x0, x0, #0x448
10000931c: d2800001    	mov	x1, #0x0                ; =0
100009320: 940008a1    	bl	0x10000b5a4 <_strlen+0x10000b5a4>
100009324: a8c17bfd    	ldp	x29, x30, [sp], #0x10
100009328: 17fffd24    	b	0x1000087b8 <_nimTestErrorFlag>

000000010000932c <_alignString__pureZstrformat_u18>:
10000932c: d10183ff    	sub	sp, sp, #0x60
100009330: a90167fa    	stp	x26, x25, [sp, #0x10]
100009334: a9025ff8    	stp	x24, x23, [sp, #0x20]
100009338: a90357f6    	stp	x22, x21, [sp, #0x30]
10000933c: a9044ff4    	stp	x20, x19, [sp, #0x40]
100009340: a9057bfd    	stp	x29, x30, [sp, #0x50]
100009344: 910143fd    	add	x29, sp, #0x50
100009348: aa0403f7    	mov	x23, x4
10000934c: aa0303f5    	mov	x21, x3
100009350: aa0203f9    	mov	x25, x2
100009354: aa0103f8    	mov	x24, x1
100009358: aa0003f3    	mov	x19, x0
10000935c: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100009360: 91012000    	add	x0, x0, #0x48
100009364: f9400008    	ldr	x8, [x0]
100009368: d63f0100    	blr	x8
10000936c: a9007fff    	stp	xzr, xzr, [sp]
100009370: b4000702    	cbz	x2, 0x100009450 <_alignString__pureZstrformat_u18+0x124>
100009374: aa0003f6    	mov	x22, x0
100009378: 91002314    	add	x20, x24, #0x8
10000937c: f100031f    	cmp	x24, #0x0
100009380: 9a9403fa    	csel	x26, xzr, x20, eq
100009384: aa1a03e0    	mov	x0, x26
100009388: aa1303e1    	mov	x1, x19
10000938c: 97fffd56    	bl	0x1000088e4 <_validateUtf8__pureZunicode_u342>
100009390: 394002c8    	ldrb	w8, [x22]
100009394: 35000668    	cbnz	w8, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
100009398: b100041f    	cmn	x0, #0x1
10000939c: 54000060    	b.eq	0x1000093a8 <_alignString__pureZstrformat_u18+0x7c>
1000093a0: aa1303e0    	mov	x0, x19
1000093a4: 14000006    	b	0x1000093bc <_alignString__pureZstrformat_u18+0x90>
1000093a8: aa1a03e0    	mov	x0, x26
1000093ac: aa1303e1    	mov	x1, x19
1000093b0: 97fffd8c    	bl	0x1000089e0 <_nucruneLen>
1000093b4: 394002c8    	ldrb	w8, [x22]
1000093b8: 35000548    	cbnz	w8, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
1000093bc: eb000339    	subs	x25, x25, x0
1000093c0: 5400048d    	b.le	0x100009450 <_alignString__pureZstrformat_u18+0x124>
1000093c4: 340000b5    	cbz	w21, 0x1000093d8 <_alignString__pureZstrformat_u18+0xac>
1000093c8: 71017abf    	cmp	w21, #0x5e
1000093cc: 540005a0    	b.eq	0x100009480 <_alignString__pureZstrformat_u18+0x154>
1000093d0: 7100f2bf    	cmp	w21, #0x3c
1000093d4: 54000be1    	b.ne	0x100009550 <_alignString__pureZstrformat_u18+0x224>
1000093d8: aa1703e0    	mov	x0, x23
1000093dc: aa1903e1    	mov	x1, x25
1000093e0: 97fffdfa    	bl	0x100008bc8 <_nsuRepeatChar>
1000093e4: 394002c8    	ldrb	w8, [x22]
1000093e8: 350003c8    	cbnz	w8, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
1000093ec: aa0003f7    	mov	x23, x0
1000093f0: aa0103f5    	mov	x21, x1
1000093f4: 8b130000    	add	x0, x0, x19
1000093f8: 97fff992    	bl	0x100007a40 <_rawNewString>
1000093fc: aa0003f8    	mov	x24, x0
100009400: aa0103f6    	mov	x22, x1
100009404: f100067f    	cmp	x19, #0x1
100009408: 540000eb    	b.lt	0x100009424 <_alignString__pureZstrformat_u18+0xf8>
10000940c: 8b1802c8    	add	x8, x22, x24
100009410: 91002100    	add	x0, x8, #0x8
100009414: 91000662    	add	x2, x19, #0x1
100009418: aa1403e1    	mov	x1, x20
10000941c: 94000859    	bl	0x10000b580 <_strlen+0x10000b580>
100009420: 8b130318    	add	x24, x24, x19
100009424: f10006ff    	cmp	x23, #0x1
100009428: 540000eb    	b.lt	0x100009444 <_alignString__pureZstrformat_u18+0x118>
10000942c: 8b1802c8    	add	x8, x22, x24
100009430: 91002100    	add	x0, x8, #0x8
100009434: 910022a1    	add	x1, x21, #0x8
100009438: 910006e2    	add	x2, x23, #0x1
10000943c: 94000851    	bl	0x10000b580 <_strlen+0x10000b580>
100009440: 8b170318    	add	x24, x24, x23
100009444: a9005bf8    	stp	x24, x22, [sp]
100009448: b5000bf5    	cbnz	x21, 0x1000095c4 <_alignString__pureZstrformat_u18+0x298>
10000944c: 14000005    	b	0x100009460 <_alignString__pureZstrformat_u18+0x134>
100009450: 910003e0    	mov	x0, sp
100009454: aa1303e1    	mov	x1, x19
100009458: aa1803e2    	mov	x2, x24
10000945c: 97fff85e    	bl	0x1000075d4 <_eqcopy___system_u2636>
100009460: a94007e0    	ldp	x0, x1, [sp]
100009464: a9457bfd    	ldp	x29, x30, [sp, #0x50]
100009468: a9444ff4    	ldp	x20, x19, [sp, #0x40]
10000946c: a94357f6    	ldp	x22, x21, [sp, #0x30]
100009470: a9425ff8    	ldp	x24, x23, [sp, #0x20]
100009474: a94167fa    	ldp	x26, x25, [sp, #0x10]
100009478: 910183ff    	add	sp, sp, #0x60
10000947c: d65f03c0    	ret
100009480: d341ff38    	lsr	x24, x25, #1
100009484: aa1703e0    	mov	x0, x23
100009488: aa1803e1    	mov	x1, x24
10000948c: 97fffdcf    	bl	0x100008bc8 <_nsuRepeatChar>
100009490: 394002c8    	ldrb	w8, [x22]
100009494: 35fffe68    	cbnz	w8, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
100009498: aa0003fa    	mov	x26, x0
10000949c: aa0103f5    	mov	x21, x1
1000094a0: cb180321    	sub	x1, x25, x24
1000094a4: aa1703e0    	mov	x0, x23
1000094a8: 97fffdc8    	bl	0x100008bc8 <_nsuRepeatChar>
1000094ac: 394002c8    	ldrb	w8, [x22]
1000094b0: 35fffd88    	cbnz	w8, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
1000094b4: aa0003f8    	mov	x24, x0
1000094b8: aa0103f7    	mov	x23, x1
1000094bc: 8b130348    	add	x8, x26, x19
1000094c0: 8b000100    	add	x0, x8, x0
1000094c4: 97fff95f    	bl	0x100007a40 <_rawNewString>
1000094c8: aa0003f9    	mov	x25, x0
1000094cc: aa0103f6    	mov	x22, x1
1000094d0: f100075f    	cmp	x26, #0x1
1000094d4: 540000eb    	b.lt	0x1000094f0 <_alignString__pureZstrformat_u18+0x1c4>
1000094d8: 8b1902c8    	add	x8, x22, x25
1000094dc: 91002100    	add	x0, x8, #0x8
1000094e0: 910022a1    	add	x1, x21, #0x8
1000094e4: 91000742    	add	x2, x26, #0x1
1000094e8: 94000826    	bl	0x10000b580 <_strlen+0x10000b580>
1000094ec: 8b1a0339    	add	x25, x25, x26
1000094f0: f100067f    	cmp	x19, #0x1
1000094f4: 540000eb    	b.lt	0x100009510 <_alignString__pureZstrformat_u18+0x1e4>
1000094f8: 8b1902c8    	add	x8, x22, x25
1000094fc: 91002100    	add	x0, x8, #0x8
100009500: 91000662    	add	x2, x19, #0x1
100009504: aa1403e1    	mov	x1, x20
100009508: 9400081e    	bl	0x10000b580 <_strlen+0x10000b580>
10000950c: 8b130339    	add	x25, x25, x19
100009510: f100071f    	cmp	x24, #0x1
100009514: 540000eb    	b.lt	0x100009530 <_alignString__pureZstrformat_u18+0x204>
100009518: 8b1902c8    	add	x8, x22, x25
10000951c: 91002100    	add	x0, x8, #0x8
100009520: 910022e1    	add	x1, x23, #0x8
100009524: 91000702    	add	x2, x24, #0x1
100009528: 94000816    	bl	0x10000b580 <_strlen+0x10000b580>
10000952c: 8b180339    	add	x25, x25, x24
100009530: a9005bf9    	stp	x25, x22, [sp]
100009534: b40000b7    	cbz	x23, 0x100009548 <_alignString__pureZstrformat_u18+0x21c>
100009538: 39401ee8    	ldrb	w8, [x23, #0x7]
10000953c: 37300068    	tbnz	w8, #0x6, 0x100009548 <_alignString__pureZstrformat_u18+0x21c>
100009540: aa1703e0    	mov	x0, x23
100009544: 97fff20b    	bl	0x100005d70 <_deallocShared>
100009548: b50003f5    	cbnz	x21, 0x1000095c4 <_alignString__pureZstrformat_u18+0x298>
10000954c: 17ffffc5    	b	0x100009460 <_alignString__pureZstrformat_u18+0x134>
100009550: aa1703e0    	mov	x0, x23
100009554: aa1903e1    	mov	x1, x25
100009558: 97fffd9c    	bl	0x100008bc8 <_nsuRepeatChar>
10000955c: 394002c8    	ldrb	w8, [x22]
100009560: 35fff808    	cbnz	w8, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
100009564: aa0003f8    	mov	x24, x0
100009568: aa0103f5    	mov	x21, x1
10000956c: 8b130000    	add	x0, x0, x19
100009570: 97fff934    	bl	0x100007a40 <_rawNewString>
100009574: aa0003f7    	mov	x23, x0
100009578: aa0103f6    	mov	x22, x1
10000957c: f100071f    	cmp	x24, #0x1
100009580: 540000eb    	b.lt	0x10000959c <_alignString__pureZstrformat_u18+0x270>
100009584: 8b1702c8    	add	x8, x22, x23
100009588: 91002100    	add	x0, x8, #0x8
10000958c: 910022a1    	add	x1, x21, #0x8
100009590: 91000702    	add	x2, x24, #0x1
100009594: 940007fb    	bl	0x10000b580 <_strlen+0x10000b580>
100009598: 8b1802f7    	add	x23, x23, x24
10000959c: f100067f    	cmp	x19, #0x1
1000095a0: 540000eb    	b.lt	0x1000095bc <_alignString__pureZstrformat_u18+0x290>
1000095a4: 8b1702c8    	add	x8, x22, x23
1000095a8: 91002100    	add	x0, x8, #0x8
1000095ac: 91000662    	add	x2, x19, #0x1
1000095b0: aa1403e1    	mov	x1, x20
1000095b4: 940007f3    	bl	0x10000b580 <_strlen+0x10000b580>
1000095b8: 8b1302f7    	add	x23, x23, x19
1000095bc: a9005bf7    	stp	x23, x22, [sp]
1000095c0: b4fff515    	cbz	x21, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
1000095c4: 39401ea8    	ldrb	w8, [x21, #0x7]
1000095c8: 3737f4c8    	tbnz	w8, #0x6, 0x100009460 <_alignString__pureZstrformat_u18+0x134>
1000095cc: aa1503e0    	mov	x0, x21
1000095d0: 97fff1e8    	bl	0x100005d70 <_deallocShared>
1000095d4: 17ffffa3    	b	0x100009460 <_alignString__pureZstrformat_u18+0x134>

00000001000095d8 <_formatFloat__add95carry_u719>:
1000095d8: d10243ff    	sub	sp, sp, #0x90
1000095dc: 6d0323e9    	stp	d9, d8, [sp, #0x30]
1000095e0: a90467fa    	stp	x26, x25, [sp, #0x40]
1000095e4: a9055ff8    	stp	x24, x23, [sp, #0x50]
1000095e8: a90657f6    	stp	x22, x21, [sp, #0x60]
1000095ec: a9074ff4    	stp	x20, x19, [sp, #0x70]
1000095f0: a9087bfd    	stp	x29, x30, [sp, #0x80]
1000095f4: 910203fd    	add	x29, sp, #0x80
1000095f8: aa0203f5    	mov	x21, x2
1000095fc: aa0103e8    	mov	x8, x1
100009600: 1e604008    	fmov	d8, d0
100009604: aa0003f3    	mov	x19, x0
100009608: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000960c: 91012000    	add	x0, x0, #0x48
100009610: f9400009    	ldr	x9, [x0]
100009614: d63f0120    	blr	x9
100009618: aa0003f4    	mov	x20, x0
10000961c: f9400841    	ldr	x1, [x2, #0x10]
100009620: aa0803e0    	mov	x0, x8
100009624: 528005c2    	mov	w2, #0x2e               ; =46
100009628: 97fffd17    	bl	0x100008a84 <_nsuformatBiggestFloat>
10000962c: a90107e0    	stp	x0, x1, [sp, #0x10]
100009630: 39400288    	ldrb	w8, [x20]
100009634: 35001e08    	cbnz	w8, 0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
100009638: 1e602108    	fcmp	d8, #0.0
10000963c: 5400050a    	b.ge	0x1000096dc <_formatFloat__add95carry_u719+0x104>
100009640: 394012a8    	ldrb	w8, [x21, #0x4]
100009644: 34001508    	cbz	w8, 0x1000098e4 <_formatFloat__add95carry_u719+0x30c>
100009648: f0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000964c: 9104c108    	add	x8, x8, #0x130
100009650: 3dc00100    	ldr	q0, [x8]
100009654: 3d8003e0    	str	q0, [sp]
100009658: f9400fe8    	ldr	x8, [sp, #0x18]
10000965c: 39c02100    	ldrsb	w0, [x8, #0x8]
100009660: 97fff9a5    	bl	0x100007cf4 <_nimCharToStr>
100009664: aa0003e2    	mov	x2, x0
100009668: aa0103e3    	mov	x3, x1
10000966c: 910003e0    	mov	x0, sp
100009670: aa0203e1    	mov	x1, x2
100009674: aa0303e2    	mov	x2, x3
100009678: 97fff9b2    	bl	0x100007d40 <_eqsink___system_u2642>
10000967c: a94163e8    	ldp	x8, x24, [sp, #0x10]
100009680: d1000916    	sub	x22, x8, #0x2
100009684: d1000500    	sub	x0, x8, #0x1
100009688: 97fff912    	bl	0x100007ad0 <_mnewString>
10000968c: aa0103e2    	mov	x2, x1
100009690: a90207e0    	stp	x0, x1, [sp, #0x20]
100009694: b7f807b6    	tbnz	x22, #0x3f, 0x100009788 <_formatFloat__add95carry_u719+0x1b0>
100009698: d2800017    	mov	x23, #0x0               ; =0
10000969c: 91002718    	add	x24, x24, #0x9
1000096a0: 39401c48    	ldrb	w8, [x2, #0x7]
1000096a4: 36300088    	tbz	w8, #0x6, 0x1000096b4 <_formatFloat__add95carry_u719+0xdc>
1000096a8: 910083e0    	add	x0, sp, #0x20
1000096ac: 97fff929    	bl	0x100007b50 <_nimPrepareStrMutationImpl__system_u2387>
1000096b0: f94017e2    	ldr	x2, [sp, #0x28]
1000096b4: 38776b08    	ldrb	w8, [x24, x23]
1000096b8: 8b170049    	add	x9, x2, x23
1000096bc: 39002128    	strb	w8, [x9, #0x8]
1000096c0: eb1702df    	cmp	x22, x23
1000096c4: 540002c0    	b.eq	0x10000971c <_formatFloat__add95carry_u719+0x144>
1000096c8: f94017e2    	ldr	x2, [sp, #0x28]
1000096cc: 910006f7    	add	x23, x23, #0x1
1000096d0: 39401c48    	ldrb	w8, [x2, #0x7]
1000096d4: 3737fea8    	tbnz	w8, #0x6, 0x1000096a8 <_formatFloat__add95carry_u719+0xd0>
1000096d8: 17fffff7    	b	0x1000096b4 <_formatFloat__add95carry_u719+0xdc>
1000096dc: 39400aa8    	ldrb	w8, [x21, #0x2]
1000096e0: 7100b51f    	cmp	w8, #0x2d
1000096e4: 54000241    	b.ne	0x10000972c <_formatFloat__add95carry_u719+0x154>
1000096e8: 394012a8    	ldrb	w8, [x21, #0x4]
1000096ec: 34000fc8    	cbz	w8, 0x1000098e4 <_formatFloat__add95carry_u719+0x30c>
1000096f0: 5280001a    	mov	w26, #0x0               ; =0
1000096f4: f0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
1000096f8: 9104c108    	add	x8, x8, #0x130
1000096fc: 3dc00100    	ldr	q0, [x8]
100009700: 3d8003e0    	str	q0, [sp]
100009704: f94006a8    	ldr	x8, [x21, #0x8]
100009708: cb000108    	sub	x8, x8, x0
10000970c: cb3a4101    	sub	x1, x8, w26, uxtw
100009710: f100043f    	cmp	x1, #0x1
100009714: 5400054a    	b.ge	0x1000097bc <_formatFloat__add95carry_u719+0x1e4>
100009718: 1400004f    	b	0x100009854 <_formatFloat__add95carry_u719+0x27c>
10000971c: a9420be8    	ldp	x8, x2, [sp, #0x20]
100009720: 39400289    	ldrb	w9, [x20]
100009724: 34000389    	cbz	w9, 0x100009794 <_formatFloat__add95carry_u719+0x1bc>
100009728: 140000b3    	b	0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
10000972c: 1e602108    	fcmp	d8, #0.0
100009730: 540000e1    	b.ne	0x10000974c <_formatFloat__add95carry_u719+0x174>
100009734: 1e6e1000    	fmov	d0, #1.00000000
100009738: 1e681800    	fdiv	d0, d0, d8
10000973c: d2effe09    	mov	x9, #0x7ff0000000000000 ; =9218868437227405312
100009740: 9e670121    	fmov	d1, x9
100009744: 1e612000    	fcmp	d0, d1
100009748: 54fff7c1    	b.ne	0x100009640 <_formatFloat__add95carry_u719+0x68>
10000974c: 13001d00    	sxtb	w0, w8
100009750: 97fff969    	bl	0x100007cf4 <_nimCharToStr>
100009754: aa0003e2    	mov	x2, x0
100009758: aa0103f6    	mov	x22, x1
10000975c: 910043e0    	add	x0, sp, #0x10
100009760: aa0203e1    	mov	x1, x2
100009764: aa1603e2    	mov	x2, x22
100009768: d2800003    	mov	x3, #0x0                ; =0
10000976c: 97fff90d    	bl	0x100007ba0 <_insert__system_u8463>
100009770: b4fff696    	cbz	x22, 0x100009640 <_formatFloat__add95carry_u719+0x68>
100009774: 39401ec8    	ldrb	w8, [x22, #0x7]
100009778: 3737f648    	tbnz	w8, #0x6, 0x100009640 <_formatFloat__add95carry_u719+0x68>
10000977c: aa1603e0    	mov	x0, x22
100009780: 97fff17c    	bl	0x100005d70 <_deallocShared>
100009784: 17ffffaf    	b	0x100009640 <_formatFloat__add95carry_u719+0x68>
100009788: aa0003e8    	mov	x8, x0
10000978c: 39400289    	ldrb	w9, [x20]
100009790: 35001329    	cbnz	w9, 0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
100009794: 910043e0    	add	x0, sp, #0x10
100009798: aa0803e1    	mov	x1, x8
10000979c: 97fff969    	bl	0x100007d40 <_eqsink___system_u2642>
1000097a0: 5280003a    	mov	w26, #0x1               ; =1
1000097a4: f9400be0    	ldr	x0, [sp, #0x10]
1000097a8: f94006a8    	ldr	x8, [x21, #0x8]
1000097ac: cb000108    	sub	x8, x8, x0
1000097b0: cb3a4101    	sub	x1, x8, w26, uxtw
1000097b4: f100043f    	cmp	x1, #0x1
1000097b8: 540004eb    	b.lt	0x100009854 <_formatFloat__add95carry_u719+0x27c>
1000097bc: 52800600    	mov	w0, #0x30               ; =48
1000097c0: 97fffd02    	bl	0x100008bc8 <_nsuRepeatChar>
1000097c4: 39400288    	ldrb	w8, [x20]
1000097c8: 35001168    	cbnz	w8, 0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
1000097cc: aa0003f9    	mov	x25, x0
1000097d0: aa0103f6    	mov	x22, x1
1000097d4: f9400be8    	ldr	x8, [sp, #0x10]
1000097d8: 8b000100    	add	x0, x8, x0
1000097dc: 97fff899    	bl	0x100007a40 <_rawNewString>
1000097e0: aa0003f8    	mov	x24, x0
1000097e4: aa0103f7    	mov	x23, x1
1000097e8: f100073f    	cmp	x25, #0x1
1000097ec: 540000eb    	b.lt	0x100009808 <_formatFloat__add95carry_u719+0x230>
1000097f0: 8b1802e8    	add	x8, x23, x24
1000097f4: 91002100    	add	x0, x8, #0x8
1000097f8: 910022c1    	add	x1, x22, #0x8
1000097fc: 91000722    	add	x2, x25, #0x1
100009800: 94000760    	bl	0x10000b580 <_strlen+0x10000b580>
100009804: 8b190318    	add	x24, x24, x25
100009808: f9400bf9    	ldr	x25, [sp, #0x10]
10000980c: f100073f    	cmp	x25, #0x1
100009810: 5400010b    	b.lt	0x100009830 <_formatFloat__add95carry_u719+0x258>
100009814: f9400fe8    	ldr	x8, [sp, #0x18]
100009818: 8b1802e9    	add	x9, x23, x24
10000981c: 91002120    	add	x0, x9, #0x8
100009820: 91002101    	add	x1, x8, #0x8
100009824: 91000722    	add	x2, x25, #0x1
100009828: 94000756    	bl	0x10000b580 <_strlen+0x10000b580>
10000982c: 8b180338    	add	x24, x25, x24
100009830: 910043e0    	add	x0, sp, #0x10
100009834: aa1803e1    	mov	x1, x24
100009838: aa1703e2    	mov	x2, x23
10000983c: 97fff941    	bl	0x100007d40 <_eqsink___system_u2642>
100009840: b40000b6    	cbz	x22, 0x100009854 <_formatFloat__add95carry_u719+0x27c>
100009844: 39401ec8    	ldrb	w8, [x22, #0x7]
100009848: 37300068    	tbnz	w8, #0x6, 0x100009854 <_formatFloat__add95carry_u719+0x27c>
10000984c: aa1603e0    	mov	x0, x22
100009850: 97fff148    	bl	0x100005d70 <_deallocShared>
100009854: 340003fa    	cbz	w26, 0x1000098d0 <_formatFloat__add95carry_u719+0x2f8>
100009858: f94003e8    	ldr	x8, [sp]
10000985c: f9400be9    	ldr	x9, [sp, #0x10]
100009860: 8b080120    	add	x0, x9, x8
100009864: 97fff877    	bl	0x100007a40 <_rawNewString>
100009868: aa0003f7    	mov	x23, x0
10000986c: aa0103f6    	mov	x22, x1
100009870: f94003f8    	ldr	x24, [sp]
100009874: f100071f    	cmp	x24, #0x1
100009878: 5400010b    	b.lt	0x100009898 <_formatFloat__add95carry_u719+0x2c0>
10000987c: f94007e8    	ldr	x8, [sp, #0x8]
100009880: 8b1702c9    	add	x9, x22, x23
100009884: 91002120    	add	x0, x9, #0x8
100009888: 91002101    	add	x1, x8, #0x8
10000988c: 91000702    	add	x2, x24, #0x1
100009890: 9400073c    	bl	0x10000b580 <_strlen+0x10000b580>
100009894: 8b1802f7    	add	x23, x23, x24
100009898: f9400bf8    	ldr	x24, [sp, #0x10]
10000989c: f100071f    	cmp	x24, #0x1
1000098a0: 5400010b    	b.lt	0x1000098c0 <_formatFloat__add95carry_u719+0x2e8>
1000098a4: f9400fe8    	ldr	x8, [sp, #0x18]
1000098a8: 8b1702c9    	add	x9, x22, x23
1000098ac: 91002120    	add	x0, x9, #0x8
1000098b0: 91002101    	add	x1, x8, #0x8
1000098b4: 91000702    	add	x2, x24, #0x1
1000098b8: 94000732    	bl	0x10000b580 <_strlen+0x10000b580>
1000098bc: 8b170317    	add	x23, x24, x23
1000098c0: 910043e0    	add	x0, sp, #0x10
1000098c4: aa1703e1    	mov	x1, x23
1000098c8: aa1603e2    	mov	x2, x22
1000098cc: 97fff91d    	bl	0x100007d40 <_eqsink___system_u2642>
1000098d0: f94007e0    	ldr	x0, [sp, #0x8]
1000098d4: b4000080    	cbz	x0, 0x1000098e4 <_formatFloat__add95carry_u719+0x30c>
1000098d8: 39401c08    	ldrb	w8, [x0, #0x7]
1000098dc: 37300048    	tbnz	w8, #0x6, 0x1000098e4 <_formatFloat__add95carry_u719+0x30c>
1000098e0: 97fff124    	bl	0x100005d70 <_deallocShared>
1000098e4: 394006a8    	ldrb	w8, [x21, #0x1]
1000098e8: 528007c9    	mov	w9, #0x3e               ; =62
1000098ec: 7100011f    	cmp	w8, #0x0
1000098f0: 1a880128    	csel	w8, w9, w8, eq
1000098f4: f94006a2    	ldr	x2, [x21, #0x8]
1000098f8: 39c002a4    	ldrsb	w4, [x21]
1000098fc: a94107e0    	ldp	x0, x1, [sp, #0x10]
100009900: 13001d03    	sxtb	w3, w8
100009904: 97fffe8a    	bl	0x10000932c <_alignString__pureZstrformat_u18>
100009908: 39400288    	ldrb	w8, [x20]
10000990c: 35000748    	cbnz	w8, 0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
100009910: aa0003f7    	mov	x23, x0
100009914: aa0103f6    	mov	x22, x1
100009918: 394062a8    	ldrb	w8, [x21, #0x18]
10000991c: 51010508    	sub	w8, w8, #0x41
100009920: 7100651f    	cmp	w8, #0x19
100009924: 54000388    	b.hi	0x100009994 <_formatFloat__add95carry_u719+0x3bc>
100009928: aa1703e0    	mov	x0, x23
10000992c: aa1603e1    	mov	x1, x22
100009930: 97fffcce    	bl	0x100008c68 <_nsuToUpperAsciiStr>
100009934: 39400288    	ldrb	w8, [x20]
100009938: 350005e8    	cbnz	w8, 0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
10000993c: aa0003f7    	mov	x23, x0
100009940: aa0103f5    	mov	x21, x1
100009944: aa1303e0    	mov	x0, x19
100009948: aa1703e1    	mov	x1, x23
10000994c: 97fff683    	bl	0x100007358 <_prepareAdd>
100009950: f10006ff    	cmp	x23, #0x1
100009954: 5400014b    	b.lt	0x10000997c <_formatFloat__add95carry_u719+0x3a4>
100009958: a9402269    	ldp	x9, x8, [x19]
10000995c: 8b090108    	add	x8, x8, x9
100009960: 91002100    	add	x0, x8, #0x8
100009964: 910022a1    	add	x1, x21, #0x8
100009968: 910006e2    	add	x2, x23, #0x1
10000996c: 94000705    	bl	0x10000b580 <_strlen+0x10000b580>
100009970: f9400268    	ldr	x8, [x19]
100009974: 8b170108    	add	x8, x8, x23
100009978: f9000268    	str	x8, [x19]
10000997c: b4000295    	cbz	x21, 0x1000099cc <_formatFloat__add95carry_u719+0x3f4>
100009980: 39401ea8    	ldrb	w8, [x21, #0x7]
100009984: 37300248    	tbnz	w8, #0x6, 0x1000099cc <_formatFloat__add95carry_u719+0x3f4>
100009988: aa1503e0    	mov	x0, x21
10000998c: 97fff0f9    	bl	0x100005d70 <_deallocShared>
100009990: 1400000f    	b	0x1000099cc <_formatFloat__add95carry_u719+0x3f4>
100009994: aa1303e0    	mov	x0, x19
100009998: aa1703e1    	mov	x1, x23
10000999c: 97fff66f    	bl	0x100007358 <_prepareAdd>
1000099a0: f10006ff    	cmp	x23, #0x1
1000099a4: 5400014b    	b.lt	0x1000099cc <_formatFloat__add95carry_u719+0x3f4>
1000099a8: a9402269    	ldp	x9, x8, [x19]
1000099ac: 8b090108    	add	x8, x8, x9
1000099b0: 91002100    	add	x0, x8, #0x8
1000099b4: 910022c1    	add	x1, x22, #0x8
1000099b8: 910006e2    	add	x2, x23, #0x1
1000099bc: 940006f1    	bl	0x10000b580 <_strlen+0x10000b580>
1000099c0: f9400268    	ldr	x8, [x19]
1000099c4: 8b170108    	add	x8, x8, x23
1000099c8: f9000268    	str	x8, [x19]
1000099cc: b40000b6    	cbz	x22, 0x1000099e0 <_formatFloat__add95carry_u719+0x408>
1000099d0: 39401ec8    	ldrb	w8, [x22, #0x7]
1000099d4: 37300068    	tbnz	w8, #0x6, 0x1000099e0 <_formatFloat__add95carry_u719+0x408>
1000099d8: aa1603e0    	mov	x0, x22
1000099dc: 97fff0e5    	bl	0x100005d70 <_deallocShared>
1000099e0: f9400fe0    	ldr	x0, [sp, #0x18]
1000099e4: b4000080    	cbz	x0, 0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
1000099e8: 39401c08    	ldrb	w8, [x0, #0x7]
1000099ec: 37300048    	tbnz	w8, #0x6, 0x1000099f4 <_formatFloat__add95carry_u719+0x41c>
1000099f0: 97fff0e0    	bl	0x100005d70 <_deallocShared>
1000099f4: a9487bfd    	ldp	x29, x30, [sp, #0x80]
1000099f8: a9474ff4    	ldp	x20, x19, [sp, #0x70]
1000099fc: a94657f6    	ldp	x22, x21, [sp, #0x60]
100009a00: a9455ff8    	ldp	x24, x23, [sp, #0x50]
100009a04: a94467fa    	ldp	x26, x25, [sp, #0x40]
100009a08: 6d4323e9    	ldp	d9, d8, [sp, #0x30]
100009a0c: 910243ff    	add	sp, sp, #0x90
100009a10: d65f03c0    	ret

0000000100009a14 <_formatValue__add95carry_u709>:
100009a14: d0000002    	adrp	x2, 0x10000b000 <_bench__add95carry_u844+0x104>
100009a18: 91234042    	add	x2, x2, #0x8d0
100009a1c: 52800021    	mov	w1, #0x1                ; =1
100009a20: 17fffeee    	b	0x1000095d8 <_formatFloat__add95carry_u719>

0000000100009a24 <_formatValue__add95carry_u756>:
100009a24: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100009a28: a9014ff4    	stp	x20, x19, [sp, #0x10]
100009a2c: a9027bfd    	stp	x29, x30, [sp, #0x20]
100009a30: 910083fd    	add	x29, sp, #0x20
100009a34: aa0003f3    	mov	x19, x0
100009a38: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100009a3c: 91012000    	add	x0, x0, #0x48
100009a40: f9400008    	ldr	x8, [x0]
100009a44: d63f0100    	blr	x8
100009a48: aa0003f6    	mov	x22, x0
100009a4c: aa0103e0    	mov	x0, x1
100009a50: 97ffe931    	bl	0x100003f14 <_dollar___systemZdollars_u8>
100009a54: 394002c8    	ldrb	w8, [x22]
100009a58: 35000328    	cbnz	w8, 0x100009abc <_formatValue__add95carry_u756+0x98>
100009a5c: aa0003f5    	mov	x21, x0
100009a60: aa0103f4    	mov	x20, x1
100009a64: aa1303e0    	mov	x0, x19
100009a68: aa1503e1    	mov	x1, x21
100009a6c: 97fff63b    	bl	0x100007358 <_prepareAdd>
100009a70: f10006bf    	cmp	x21, #0x1
100009a74: 5400014b    	b.lt	0x100009a9c <_formatValue__add95carry_u756+0x78>
100009a78: a9402269    	ldp	x9, x8, [x19]
100009a7c: 8b090108    	add	x8, x8, x9
100009a80: 91002100    	add	x0, x8, #0x8
100009a84: 91002281    	add	x1, x20, #0x8
100009a88: 910006a2    	add	x2, x21, #0x1
100009a8c: 940006bd    	bl	0x10000b580 <_strlen+0x10000b580>
100009a90: f9400268    	ldr	x8, [x19]
100009a94: 8b150108    	add	x8, x8, x21
100009a98: f9000268    	str	x8, [x19]
100009a9c: b4000114    	cbz	x20, 0x100009abc <_formatValue__add95carry_u756+0x98>
100009aa0: 39401e88    	ldrb	w8, [x20, #0x7]
100009aa4: 373000c8    	tbnz	w8, #0x6, 0x100009abc <_formatValue__add95carry_u756+0x98>
100009aa8: aa1403e0    	mov	x0, x20
100009aac: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100009ab0: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100009ab4: a8c357f6    	ldp	x22, x21, [sp], #0x30
100009ab8: 17fff0ae    	b	0x100005d70 <_deallocShared>
100009abc: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100009ac0: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100009ac4: a8c357f6    	ldp	x22, x21, [sp], #0x30
100009ac8: d65f03c0    	ret

0000000100009acc <_formatValue__add95carry_u774>:
100009acc: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100009ad0: a9014ff4    	stp	x20, x19, [sp, #0x10]
100009ad4: a9027bfd    	stp	x29, x30, [sp, #0x20]
100009ad8: 910083fd    	add	x29, sp, #0x20
100009adc: aa0003f3    	mov	x19, x0
100009ae0: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100009ae4: 91012000    	add	x0, x0, #0x48
100009ae8: f9400008    	ldr	x8, [x0]
100009aec: d63f0100    	blr	x8
100009af0: aa0003f6    	mov	x22, x0
100009af4: aa0103e0    	mov	x0, x1
100009af8: aa0203e1    	mov	x1, x2
100009afc: 528001e2    	mov	w2, #0xf                ; =15
100009b00: 52800783    	mov	w3, #0x3c               ; =60
100009b04: 52800404    	mov	w4, #0x20               ; =32
100009b08: 97fffe09    	bl	0x10000932c <_alignString__pureZstrformat_u18>
100009b0c: 394002c8    	ldrb	w8, [x22]
100009b10: 35000328    	cbnz	w8, 0x100009b74 <_formatValue__add95carry_u774+0xa8>
100009b14: aa0003f5    	mov	x21, x0
100009b18: aa0103f4    	mov	x20, x1
100009b1c: aa1303e0    	mov	x0, x19
100009b20: aa1503e1    	mov	x1, x21
100009b24: 97fff60d    	bl	0x100007358 <_prepareAdd>
100009b28: f10006bf    	cmp	x21, #0x1
100009b2c: 5400014b    	b.lt	0x100009b54 <_formatValue__add95carry_u774+0x88>
100009b30: a9402269    	ldp	x9, x8, [x19]
100009b34: 8b090108    	add	x8, x8, x9
100009b38: 91002100    	add	x0, x8, #0x8
100009b3c: 91002281    	add	x1, x20, #0x8
100009b40: 910006a2    	add	x2, x21, #0x1
100009b44: 9400068f    	bl	0x10000b580 <_strlen+0x10000b580>
100009b48: f9400268    	ldr	x8, [x19]
100009b4c: 8b150108    	add	x8, x8, x21
100009b50: f9000268    	str	x8, [x19]
100009b54: b4000114    	cbz	x20, 0x100009b74 <_formatValue__add95carry_u774+0xa8>
100009b58: 39401e88    	ldrb	w8, [x20, #0x7]
100009b5c: 373000c8    	tbnz	w8, #0x6, 0x100009b74 <_formatValue__add95carry_u774+0xa8>
100009b60: aa1403e0    	mov	x0, x20
100009b64: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100009b68: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100009b6c: a8c357f6    	ldp	x22, x21, [sp], #0x30
100009b70: 17fff080    	b	0x100005d70 <_deallocShared>
100009b74: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100009b78: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100009b7c: a8c357f6    	ldp	x22, x21, [sp], #0x30
100009b80: d65f03c0    	ret

0000000100009b84 <_formatValue__add95carry_u785>:
100009b84: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
100009b88: a9014ff4    	stp	x20, x19, [sp, #0x10]
100009b8c: a9027bfd    	stp	x29, x30, [sp, #0x20]
100009b90: 910083fd    	add	x29, sp, #0x20
100009b94: aa0003f3    	mov	x19, x0
100009b98: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100009b9c: 91012000    	add	x0, x0, #0x48
100009ba0: f9400008    	ldr	x8, [x0]
100009ba4: d63f0100    	blr	x8
100009ba8: aa0003f6    	mov	x22, x0
100009bac: aa0103e0    	mov	x0, x1
100009bb0: aa0203e1    	mov	x1, x2
100009bb4: 52800322    	mov	w2, #0x19               ; =25
100009bb8: 52800783    	mov	w3, #0x3c               ; =60
100009bbc: 52800404    	mov	w4, #0x20               ; =32
100009bc0: 97fffddb    	bl	0x10000932c <_alignString__pureZstrformat_u18>
100009bc4: 394002c8    	ldrb	w8, [x22]
100009bc8: 35000328    	cbnz	w8, 0x100009c2c <_formatValue__add95carry_u785+0xa8>
100009bcc: aa0003f5    	mov	x21, x0
100009bd0: aa0103f4    	mov	x20, x1
100009bd4: aa1303e0    	mov	x0, x19
100009bd8: aa1503e1    	mov	x1, x21
100009bdc: 97fff5df    	bl	0x100007358 <_prepareAdd>
100009be0: f10006bf    	cmp	x21, #0x1
100009be4: 5400014b    	b.lt	0x100009c0c <_formatValue__add95carry_u785+0x88>
100009be8: a9402269    	ldp	x9, x8, [x19]
100009bec: 8b090108    	add	x8, x8, x9
100009bf0: 91002100    	add	x0, x8, #0x8
100009bf4: 91002281    	add	x1, x20, #0x8
100009bf8: 910006a2    	add	x2, x21, #0x1
100009bfc: 94000661    	bl	0x10000b580 <_strlen+0x10000b580>
100009c00: f9400268    	ldr	x8, [x19]
100009c04: 8b150108    	add	x8, x8, x21
100009c08: f9000268    	str	x8, [x19]
100009c0c: b4000114    	cbz	x20, 0x100009c2c <_formatValue__add95carry_u785+0xa8>
100009c10: 39401e88    	ldrb	w8, [x20, #0x7]
100009c14: 373000c8    	tbnz	w8, #0x6, 0x100009c2c <_formatValue__add95carry_u785+0xa8>
100009c18: aa1403e0    	mov	x0, x20
100009c1c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100009c20: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100009c24: a8c357f6    	ldp	x22, x21, [sp], #0x30
100009c28: 17fff052    	b	0x100005d70 <_deallocShared>
100009c2c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
100009c30: a9414ff4    	ldp	x20, x19, [sp, #0x10]
100009c34: a8c357f6    	ldp	x22, x21, [sp], #0x30
100009c38: d65f03c0    	ret

0000000100009c3c <_formatInt__add95carry_u804>:
100009c3c: d10283ff    	sub	sp, sp, #0xa0
100009c40: a9046ffc    	stp	x28, x27, [sp, #0x40]
100009c44: a90567fa    	stp	x26, x25, [sp, #0x50]
100009c48: a9065ff8    	stp	x24, x23, [sp, #0x60]
100009c4c: a90757f6    	stp	x22, x21, [sp, #0x70]
100009c50: a9084ff4    	stp	x20, x19, [sp, #0x80]
100009c54: a9097bfd    	stp	x29, x30, [sp, #0x90]
100009c58: 910243fd    	add	x29, sp, #0x90
100009c5c: aa0203f3    	mov	x19, x2
100009c60: aa0103f6    	mov	x22, x1
100009c64: aa0003f7    	mov	x23, x0
100009c68: f0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
100009c6c: 91012000    	add	x0, x0, #0x48
100009c70: f9400008    	ldr	x8, [x0]
100009c74: d63f0100    	blr	x8
100009c78: f90017e0    	str	x0, [sp, #0x28]
100009c7c: f10002ff    	cmp	x23, #0x0
100009c80: da9756f4    	cneg	x20, x23, mi
100009c84: 39400c48    	ldrb	w8, [x2, #0x3]
100009c88: 340002e8    	cbz	w8, 0x100009ce4 <_formatInt__add95carry_u804+0xa8>
100009c8c: d2800018    	mov	x24, #0x0               ; =0
100009c90: 5280000d    	mov	w13, #0x0               ; =0
100009c94: 39406268    	ldrb	w8, [x19, #0x18]
100009c98: d000000c    	adrp	x12, 0x10000b000 <_bench__add95carry_u844+0x104>
100009c9c: 9124818c    	add	x12, x12, #0x920
100009ca0: 51016108    	sub	w8, w8, #0x58
100009ca4: 7100811f    	cmp	w8, #0x20
100009ca8: 54000268    	b.hi	0x100009cf4 <_formatInt__add95carry_u804+0xb8>
100009cac: d0000009    	adrp	x9, 0x10000b000 <_bench__add95carry_u844+0x104>
100009cb0: 9122a129    	add	x9, x9, #0x8a8
100009cb4: 1000008a    	adr	x10, 0x100009cc4 <_formatInt__add95carry_u804+0x88>
100009cb8: 3868692b    	ldrb	w11, [x9, x8]
100009cbc: 8b0b094a    	add	x10, x10, x11, lsl #2
100009cc0: d61f0140    	br	x10
100009cc4: d000000c    	adrp	x12, 0x10000b000 <_bench__add95carry_u844+0x104>
100009cc8: 9124c18c    	add	x12, x12, #0x930
100009ccc: 5280002d    	mov	w13, #0x1               ; =1
100009cd0: 52800058    	mov	w24, #0x2               ; =2
100009cd4: b90027ed    	str	w13, [sp, #0x24]
100009cd8: f9000fec    	str	x12, [sp, #0x18]
100009cdc: b5000137    	cbnz	x23, 0x100009d00 <_formatInt__add95carry_u804+0xc4>
100009ce0: 1400006c    	b	0x100009e90 <_formatInt__add95carry_u804+0x254>
100009ce4: 5280000d    	mov	w13, #0x0               ; =0
100009ce8: d2800018    	mov	x24, #0x0               ; =0
100009cec: d000000c    	adrp	x12, 0x10000b000 <_bench__add95carry_u844+0x104>
100009cf0: 9124818c    	add	x12, x12, #0x920
100009cf4: b90027ed    	str	w13, [sp, #0x24]
100009cf8: f9000fec    	str	x12, [sp, #0x18]
100009cfc: b4000cb7    	cbz	x23, 0x100009e90 <_formatInt__add95carry_u804+0x254>
100009d00: a900e3f7    	stp	x23, x24, [sp, #0x8]
100009d04: f0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100009d08: 9104c108    	add	x8, x8, #0x130
100009d0c: 3dc00100    	ldr	q0, [x8]
100009d10: 3d800fe0    	str	q0, [sp, #0x30]
100009d14: 5280083b    	mov	w27, #0x41              ; =65
100009d18: 52800c3c    	mov	w28, #0x61              ; =97
100009d1c: 1280013a    	mov	w26, #-0xa              ; =-10
100009d20: 52800615    	mov	w21, #0x30              ; =48
100009d24: 14000004    	b	0x100009d34 <_formatInt__add95carry_u804+0xf8>
100009d28: eb16029f    	cmp	x20, x22
100009d2c: aa1903f4    	mov	x20, x25
100009d30: 540004c3    	b.lo	0x100009dc8 <_formatInt__add95carry_u804+0x18c>
100009d34: 9ad60a99    	udiv	x25, x20, x22
100009d38: 9b16d328    	msub	x8, x25, x22, x20
100009d3c: 39406269    	ldrb	w9, [x19, #0x18]
100009d40: 7101e13f    	cmp	w9, #0x78
100009d44: 1a9b0389    	csel	w9, w28, w27, eq
100009d48: f100291f    	cmp	x8, #0xa
100009d4c: 1a89b3e9    	csel	w9, wzr, w9, lt
100009d50: 1a9ab2aa    	csel	w10, w21, w26, lt
100009d54: 0b080128    	add	w8, w9, w8
100009d58: 0b080148    	add	w8, w10, w8
100009d5c: 13001d00    	sxtb	w0, w8
100009d60: 97fff7e5    	bl	0x100007cf4 <_nimCharToStr>
100009d64: f94017e8    	ldr	x8, [sp, #0x28]
100009d68: 39400108    	ldrb	w8, [x8]
100009d6c: 35002948    	cbnz	w8, 0x10000a294 <_formatInt__add95carry_u804+0x658>
100009d70: aa0003f8    	mov	x24, x0
100009d74: aa0103f7    	mov	x23, x1
100009d78: 9100c3e0    	add	x0, sp, #0x30
100009d7c: aa1803e1    	mov	x1, x24
100009d80: 97fff576    	bl	0x100007358 <_prepareAdd>
100009d84: f100071f    	cmp	x24, #0x1
100009d88: 5400014b    	b.lt	0x100009db0 <_formatInt__add95carry_u804+0x174>
100009d8c: a94323e9    	ldp	x9, x8, [sp, #0x30]
100009d90: 8b090108    	add	x8, x8, x9
100009d94: 91002100    	add	x0, x8, #0x8
100009d98: 910022e1    	add	x1, x23, #0x8
100009d9c: 91000702    	add	x2, x24, #0x1
100009da0: 940005f8    	bl	0x10000b580 <_strlen+0x10000b580>
100009da4: f9401be8    	ldr	x8, [sp, #0x30]
100009da8: 8b180108    	add	x8, x8, x24
100009dac: f9001be8    	str	x8, [sp, #0x30]
100009db0: b4fffbd7    	cbz	x23, 0x100009d28 <_formatInt__add95carry_u804+0xec>
100009db4: 39401ee8    	ldrb	w8, [x23, #0x7]
100009db8: 3737fb88    	tbnz	w8, #0x6, 0x100009d28 <_formatInt__add95carry_u804+0xec>
100009dbc: aa1703e0    	mov	x0, x23
100009dc0: 97ffefec    	bl	0x100005d70 <_deallocShared>
100009dc4: 17ffffd9    	b	0x100009d28 <_formatInt__add95carry_u804+0xec>
100009dc8: f9401be9    	ldr	x9, [sp, #0x30]
100009dcc: f100013f    	cmp	x9, #0x0
100009dd0: 9a89a528    	cinc	x8, x9, lt
100009dd4: f100093f    	cmp	x9, #0x2
100009dd8: a940e3f7    	ldp	x23, x24, [sp, #0x8]
100009ddc: 5400062b    	b.lt	0x100009ea0 <_formatInt__add95carry_u804+0x264>
100009de0: d2800014    	mov	x20, #0x0               ; =0
100009de4: 9341fd15    	asr	x21, x8, #1
100009de8: 528000f6    	mov	w22, #0x7               ; =7
100009dec: 1400000e    	b	0x100009e24 <_formatInt__add95carry_u804+0x1e8>
100009df0: 8b140109    	add	x9, x8, x20
100009df4: 3940212a    	ldrb	w10, [x9, #0x8]
100009df8: f9401beb    	ldr	x11, [sp, #0x30]
100009dfc: 8b0b0108    	add	x8, x8, x11
100009e00: 38766908    	ldrb	w8, [x8, x22]
100009e04: 39002128    	strb	w8, [x9, #0x8]
100009e08: a94323e9    	ldp	x9, x8, [sp, #0x30]
100009e0c: 8b090108    	add	x8, x8, x9
100009e10: 3836690a    	strb	w10, [x8, x22]
100009e14: 91000694    	add	x20, x20, #0x1
100009e18: d10006d6    	sub	x22, x22, #0x1
100009e1c: eb1402bf    	cmp	x21, x20
100009e20: 54000400    	b.eq	0x100009ea0 <_formatInt__add95carry_u804+0x264>
100009e24: f9401fe8    	ldr	x8, [sp, #0x38]
100009e28: 39401d09    	ldrb	w9, [x8, #0x7]
100009e2c: 36300089    	tbz	w9, #0x6, 0x100009e3c <_formatInt__add95carry_u804+0x200>
100009e30: 9100c3e0    	add	x0, sp, #0x30
100009e34: 97fff747    	bl	0x100007b50 <_nimPrepareStrMutationImpl__system_u2387>
100009e38: f9401fe8    	ldr	x8, [sp, #0x38]
100009e3c: 39401d09    	ldrb	w9, [x8, #0x7]
100009e40: 3637fd89    	tbz	w9, #0x6, 0x100009df0 <_formatInt__add95carry_u804+0x1b4>
100009e44: 9100c3e0    	add	x0, sp, #0x30
100009e48: 97fff742    	bl	0x100007b50 <_nimPrepareStrMutationImpl__system_u2387>
100009e4c: f9401fe8    	ldr	x8, [sp, #0x38]
100009e50: 17ffffe8    	b	0x100009df0 <_formatInt__add95carry_u804+0x1b4>
100009e54: d000000c    	adrp	x12, 0x10000b000 <_bench__add95carry_u844+0x104>
100009e58: 9125018c    	add	x12, x12, #0x940
100009e5c: 5280002d    	mov	w13, #0x1               ; =1
100009e60: 52800058    	mov	w24, #0x2               ; =2
100009e64: b90027ed    	str	w13, [sp, #0x24]
100009e68: f9000fec    	str	x12, [sp, #0x18]
100009e6c: b5fff4b7    	cbnz	x23, 0x100009d00 <_formatInt__add95carry_u804+0xc4>
100009e70: 14000008    	b	0x100009e90 <_formatInt__add95carry_u804+0x254>
100009e74: d000000c    	adrp	x12, 0x10000b000 <_bench__add95carry_u844+0x104>
100009e78: 9125418c    	add	x12, x12, #0x950
100009e7c: 5280002d    	mov	w13, #0x1               ; =1
100009e80: 52800058    	mov	w24, #0x2               ; =2
100009e84: b90027ed    	str	w13, [sp, #0x24]
100009e88: f9000fec    	str	x12, [sp, #0x18]
100009e8c: b5fff3b7    	cbnz	x23, 0x100009d00 <_formatInt__add95carry_u804+0xc4>
100009e90: f0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
100009e94: 91048108    	add	x8, x8, #0x120
100009e98: 3dc00100    	ldr	q0, [x8]
100009e9c: 3d800fe0    	str	q0, [sp, #0x30]
100009ea0: 39401268    	ldrb	w8, [x19, #0x4]
100009ea4: 34000728    	cbz	w8, 0x100009f88 <_formatInt__add95carry_u804+0x34c>
100009ea8: b7f800b7    	tbnz	x23, #0x3f, 0x100009ebc <_formatInt__add95carry_u804+0x280>
100009eac: 39400a68    	ldrb	w8, [x19, #0x2]
100009eb0: 7100b51f    	cmp	w8, #0x2d
100009eb4: 1a9f07e8    	cset	w8, ne
100009eb8: 14000002    	b	0x100009ec0 <_formatInt__add95carry_u804+0x284>
100009ebc: 52800028    	mov	w8, #0x1                ; =1
100009ec0: f9400669    	ldr	x9, [x19, #0x8]
100009ec4: f9401bea    	ldr	x10, [sp, #0x30]
100009ec8: cb284128    	sub	x8, x9, w8, uxtw
100009ecc: 8b0a0309    	add	x9, x24, x10
100009ed0: cb090101    	sub	x1, x8, x9
100009ed4: f100043f    	cmp	x1, #0x1
100009ed8: 5400058b    	b.lt	0x100009f88 <_formatInt__add95carry_u804+0x34c>
100009edc: aa1703fa    	mov	x26, x23
100009ee0: aa1803f5    	mov	x21, x24
100009ee4: 52800600    	mov	w0, #0x30               ; =48
100009ee8: 97fffb38    	bl	0x100008bc8 <_nsuRepeatChar>
100009eec: f94017e8    	ldr	x8, [sp, #0x28]
100009ef0: 39400108    	ldrb	w8, [x8]
100009ef4: 35001d08    	cbnz	w8, 0x10000a294 <_formatInt__add95carry_u804+0x658>
100009ef8: aa0003f9    	mov	x25, x0
100009efc: aa0103f6    	mov	x22, x1
100009f00: f9401be8    	ldr	x8, [sp, #0x30]
100009f04: 8b000100    	add	x0, x8, x0
100009f08: 97fff6ce    	bl	0x100007a40 <_rawNewString>
100009f0c: aa0003f8    	mov	x24, x0
100009f10: aa0103f7    	mov	x23, x1
100009f14: f100073f    	cmp	x25, #0x1
100009f18: 540000eb    	b.lt	0x100009f34 <_formatInt__add95carry_u804+0x2f8>
100009f1c: 8b1802e8    	add	x8, x23, x24
100009f20: 91002100    	add	x0, x8, #0x8
100009f24: 910022c1    	add	x1, x22, #0x8
100009f28: 91000722    	add	x2, x25, #0x1
100009f2c: 94000595    	bl	0x10000b580 <_strlen+0x10000b580>
100009f30: 8b190318    	add	x24, x24, x25
100009f34: f9401bf4    	ldr	x20, [sp, #0x30]
100009f38: f100069f    	cmp	x20, #0x1
100009f3c: 5400010b    	b.lt	0x100009f5c <_formatInt__add95carry_u804+0x320>
100009f40: f9401fe8    	ldr	x8, [sp, #0x38]
100009f44: 8b1802e9    	add	x9, x23, x24
100009f48: 91002120    	add	x0, x9, #0x8
100009f4c: 91002101    	add	x1, x8, #0x8
100009f50: 91000682    	add	x2, x20, #0x1
100009f54: 9400058b    	bl	0x10000b580 <_strlen+0x10000b580>
100009f58: 8b180298    	add	x24, x20, x24
100009f5c: 9100c3e0    	add	x0, sp, #0x30
100009f60: aa1803e1    	mov	x1, x24
100009f64: aa1703e2    	mov	x2, x23
100009f68: 97fff776    	bl	0x100007d40 <_eqsink___system_u2642>
100009f6c: aa1503f8    	mov	x24, x21
100009f70: aa1a03f7    	mov	x23, x26
100009f74: b40000b6    	cbz	x22, 0x100009f88 <_formatInt__add95carry_u804+0x34c>
100009f78: 39401ec8    	ldrb	w8, [x22, #0x7]
100009f7c: 37300068    	tbnz	w8, #0x6, 0x100009f88 <_formatInt__add95carry_u804+0x34c>
100009f80: aa1603e0    	mov	x0, x22
100009f84: 97ffef7b    	bl	0x100005d70 <_deallocShared>
100009f88: b7f80237    	tbnz	x23, #0x3f, 0x100009fcc <_formatInt__add95carry_u804+0x390>
100009f8c: 39400a69    	ldrb	w9, [x19, #0x2]
100009f90: f9401be8    	ldr	x8, [sp, #0x30]
100009f94: 7100b53f    	cmp	w9, #0x2d
100009f98: 54000361    	b.ne	0x10000a004 <_formatInt__add95carry_u804+0x3c8>
100009f9c: 8b180100    	add	x0, x8, x24
100009fa0: 97fff6a8    	bl	0x100007a40 <_rawNewString>
100009fa4: aa0003f6    	mov	x22, x0
100009fa8: aa0103f5    	mov	x21, x1
100009fac: b94027e8    	ldr	w8, [sp, #0x24]
100009fb0: 340004c8    	cbz	w8, 0x10000a048 <_formatInt__add95carry_u804+0x40c>
100009fb4: 8b1602a8    	add	x8, x21, x22
100009fb8: 91002100    	add	x0, x8, #0x8
100009fbc: f9400fe8    	ldr	x8, [sp, #0x18]
100009fc0: 91002101    	add	x1, x8, #0x8
100009fc4: b2400302    	orr	x2, x24, #0x1
100009fc8: 1400001e    	b	0x10000a040 <_formatInt__add95carry_u804+0x404>
100009fcc: f9401be8    	ldr	x8, [sp, #0x30]
100009fd0: b2400317    	orr	x23, x24, #0x1
100009fd4: 8b0802e0    	add	x0, x23, x8
100009fd8: 97fff69a    	bl	0x100007a40 <_rawNewString>
100009fdc: aa0103f5    	mov	x21, x1
100009fe0: 8b000028    	add	x8, x1, x0
100009fe4: 528005a9    	mov	w9, #0x2d               ; =45
100009fe8: 79001109    	strh	w9, [x8, #0x8]
100009fec: 91000416    	add	x22, x0, #0x1
100009ff0: b94027e8    	ldr	w8, [sp, #0x24]
100009ff4: 340002a8    	cbz	w8, 0x10000a048 <_formatInt__add95carry_u804+0x40c>
100009ff8: 8b1602a8    	add	x8, x21, x22
100009ffc: 91002100    	add	x0, x8, #0x8
10000a000: 1400000d    	b	0x10000a034 <_formatInt__add95carry_u804+0x3f8>
10000a004: b2400317    	orr	x23, x24, #0x1
10000a008: 8b0802e0    	add	x0, x23, x8
10000a00c: 97fff68d    	bl	0x100007a40 <_rawNewString>
10000a010: aa0103f5    	mov	x21, x1
10000a014: 39400a68    	ldrb	w8, [x19, #0x2]
10000a018: 91002029    	add	x9, x1, #0x8
10000a01c: 38206928    	strb	w8, [x9, x0]
10000a020: 91000416    	add	x22, x0, #0x1
10000a024: 8b160120    	add	x0, x9, x22
10000a028: 3900001f    	strb	wzr, [x0]
10000a02c: b94027e8    	ldr	w8, [sp, #0x24]
10000a030: 340000c8    	cbz	w8, 0x10000a048 <_formatInt__add95carry_u804+0x40c>
10000a034: f9400fe8    	ldr	x8, [sp, #0x18]
10000a038: 91002101    	add	x1, x8, #0x8
10000a03c: aa1703e2    	mov	x2, x23
10000a040: 94000550    	bl	0x10000b580 <_strlen+0x10000b580>
10000a044: 8b1802d6    	add	x22, x22, x24
10000a048: f9401bf4    	ldr	x20, [sp, #0x30]
10000a04c: f100069f    	cmp	x20, #0x1
10000a050: 5400010b    	b.lt	0x10000a070 <_formatInt__add95carry_u804+0x434>
10000a054: f9401fe8    	ldr	x8, [sp, #0x38]
10000a058: 8b1602a9    	add	x9, x21, x22
10000a05c: 91002120    	add	x0, x9, #0x8
10000a060: 91002101    	add	x1, x8, #0x8
10000a064: 91000682    	add	x2, x20, #0x1
10000a068: 94000546    	bl	0x10000b580 <_strlen+0x10000b580>
10000a06c: 8b160296    	add	x22, x20, x22
10000a070: 9100c3e0    	add	x0, sp, #0x30
10000a074: aa1603e1    	mov	x1, x22
10000a078: aa1503e2    	mov	x2, x21
10000a07c: 97fff731    	bl	0x100007d40 <_eqsink___system_u2642>
10000a080: 39400668    	ldrb	w8, [x19, #0x1]
10000a084: 7100f11f    	cmp	w8, #0x3c
10000a088: 540002c1    	b.ne	0x10000a0e0 <_formatInt__add95carry_u804+0x4a4>
10000a08c: f9401bf4    	ldr	x20, [sp, #0x30]
10000a090: f9400668    	ldr	x8, [x19, #0x8]
10000a094: eb08029f    	cmp	x20, x8
10000a098: 54000fea    	b.ge	0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a09c: 39400275    	ldrb	w21, [x19]
10000a0a0: 9100c3e0    	add	x0, sp, #0x30
10000a0a4: 52800021    	mov	w1, #0x1                ; =1
10000a0a8: 97fff4ac    	bl	0x100007358 <_prepareAdd>
10000a0ac: a94323e9    	ldp	x9, x8, [sp, #0x30]
10000a0b0: 8b090108    	add	x8, x8, x9
10000a0b4: 39002115    	strb	w21, [x8, #0x8]
10000a0b8: a94327e8    	ldp	x8, x9, [sp, #0x30]
10000a0bc: 91000508    	add	x8, x8, #0x1
10000a0c0: f9001be8    	str	x8, [sp, #0x30]
10000a0c4: 8b080128    	add	x8, x9, x8
10000a0c8: 3900211f    	strb	wzr, [x8, #0x8]
10000a0cc: 91000694    	add	x20, x20, #0x1
10000a0d0: f9400668    	ldr	x8, [x19, #0x8]
10000a0d4: eb08029f    	cmp	x20, x8
10000a0d8: 54fffe2b    	b.lt	0x10000a09c <_formatInt__add95carry_u804+0x460>
10000a0dc: 1400006e    	b	0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a0e0: f9400669    	ldr	x9, [x19, #0x8]
10000a0e4: f9401bea    	ldr	x10, [sp, #0x30]
10000a0e8: cb0a0136    	sub	x22, x9, x10
10000a0ec: 7101791f    	cmp	w8, #0x5e
10000a0f0: 540007e1    	b.ne	0x10000a1ec <_formatInt__add95carry_u804+0x5b0>
10000a0f4: f10002df    	cmp	x22, #0x0
10000a0f8: 9a96a6c8    	cinc	x8, x22, lt
10000a0fc: 9341fd17    	asr	x23, x8, #1
10000a100: 39c00260    	ldrsb	w0, [x19]
10000a104: aa1703e1    	mov	x1, x23
10000a108: 97fffab0    	bl	0x100008bc8 <_nsuRepeatChar>
10000a10c: f94017e8    	ldr	x8, [sp, #0x28]
10000a110: 39400108    	ldrb	w8, [x8]
10000a114: 35000c08    	cbnz	w8, 0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a118: aa0003f8    	mov	x24, x0
10000a11c: aa0103f5    	mov	x21, x1
10000a120: 39c00260    	ldrsb	w0, [x19]
10000a124: cb1702c1    	sub	x1, x22, x23
10000a128: 97fffaa8    	bl	0x100008bc8 <_nsuRepeatChar>
10000a12c: f94017e8    	ldr	x8, [sp, #0x28]
10000a130: 39400108    	ldrb	w8, [x8]
10000a134: 35000b08    	cbnz	w8, 0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a138: aa0003f6    	mov	x22, x0
10000a13c: aa0103f3    	mov	x19, x1
10000a140: f9401be8    	ldr	x8, [sp, #0x30]
10000a144: 8b180009    	add	x9, x0, x24
10000a148: 8b080120    	add	x0, x9, x8
10000a14c: 97fff63d    	bl	0x100007a40 <_rawNewString>
10000a150: aa0003f7    	mov	x23, x0
10000a154: aa0103f4    	mov	x20, x1
10000a158: f100071f    	cmp	x24, #0x1
10000a15c: 540000eb    	b.lt	0x10000a178 <_formatInt__add95carry_u804+0x53c>
10000a160: 8b170288    	add	x8, x20, x23
10000a164: 91002100    	add	x0, x8, #0x8
10000a168: 910022a1    	add	x1, x21, #0x8
10000a16c: 91000702    	add	x2, x24, #0x1
10000a170: 94000504    	bl	0x10000b580 <_strlen+0x10000b580>
10000a174: 8b1802f7    	add	x23, x23, x24
10000a178: f9401bf8    	ldr	x24, [sp, #0x30]
10000a17c: f100071f    	cmp	x24, #0x1
10000a180: 5400010b    	b.lt	0x10000a1a0 <_formatInt__add95carry_u804+0x564>
10000a184: f9401fe8    	ldr	x8, [sp, #0x38]
10000a188: 8b170289    	add	x9, x20, x23
10000a18c: 91002120    	add	x0, x9, #0x8
10000a190: 91002101    	add	x1, x8, #0x8
10000a194: 91000702    	add	x2, x24, #0x1
10000a198: 940004fa    	bl	0x10000b580 <_strlen+0x10000b580>
10000a19c: 8b170317    	add	x23, x24, x23
10000a1a0: f10006df    	cmp	x22, #0x1
10000a1a4: 540000eb    	b.lt	0x10000a1c0 <_formatInt__add95carry_u804+0x584>
10000a1a8: 8b170288    	add	x8, x20, x23
10000a1ac: 91002100    	add	x0, x8, #0x8
10000a1b0: 91002261    	add	x1, x19, #0x8
10000a1b4: 910006c2    	add	x2, x22, #0x1
10000a1b8: 940004f2    	bl	0x10000b580 <_strlen+0x10000b580>
10000a1bc: 8b1602f7    	add	x23, x23, x22
10000a1c0: 9100c3e0    	add	x0, sp, #0x30
10000a1c4: aa1703e1    	mov	x1, x23
10000a1c8: aa1403e2    	mov	x2, x20
10000a1cc: 97fff6dd    	bl	0x100007d40 <_eqsink___system_u2642>
10000a1d0: b40000b3    	cbz	x19, 0x10000a1e4 <_formatInt__add95carry_u804+0x5a8>
10000a1d4: 39401e68    	ldrb	w8, [x19, #0x7]
10000a1d8: 37300068    	tbnz	w8, #0x6, 0x10000a1e4 <_formatInt__add95carry_u804+0x5a8>
10000a1dc: aa1303e0    	mov	x0, x19
10000a1e0: 97ffeee4    	bl	0x100005d70 <_deallocShared>
10000a1e4: b5000515    	cbnz	x21, 0x10000a284 <_formatInt__add95carry_u804+0x648>
10000a1e8: 1400002b    	b	0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a1ec: f10006df    	cmp	x22, #0x1
10000a1f0: 5400052b    	b.lt	0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a1f4: 39c00260    	ldrsb	w0, [x19]
10000a1f8: aa1603e1    	mov	x1, x22
10000a1fc: 97fffa73    	bl	0x100008bc8 <_nsuRepeatChar>
10000a200: f94017e8    	ldr	x8, [sp, #0x28]
10000a204: 39400108    	ldrb	w8, [x8]
10000a208: 35000468    	cbnz	w8, 0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a20c: aa0003f6    	mov	x22, x0
10000a210: aa0103f5    	mov	x21, x1
10000a214: f9401be8    	ldr	x8, [sp, #0x30]
10000a218: 8b000100    	add	x0, x8, x0
10000a21c: 97fff609    	bl	0x100007a40 <_rawNewString>
10000a220: aa0003f4    	mov	x20, x0
10000a224: aa0103f3    	mov	x19, x1
10000a228: f10006df    	cmp	x22, #0x1
10000a22c: 540000eb    	b.lt	0x10000a248 <_formatInt__add95carry_u804+0x60c>
10000a230: 8b140268    	add	x8, x19, x20
10000a234: 91002100    	add	x0, x8, #0x8
10000a238: 910022a1    	add	x1, x21, #0x8
10000a23c: 910006c2    	add	x2, x22, #0x1
10000a240: 940004d0    	bl	0x10000b580 <_strlen+0x10000b580>
10000a244: 8b160294    	add	x20, x20, x22
10000a248: f9401bf6    	ldr	x22, [sp, #0x30]
10000a24c: f10006df    	cmp	x22, #0x1
10000a250: 5400010b    	b.lt	0x10000a270 <_formatInt__add95carry_u804+0x634>
10000a254: f9401fe8    	ldr	x8, [sp, #0x38]
10000a258: 8b140269    	add	x9, x19, x20
10000a25c: 91002120    	add	x0, x9, #0x8
10000a260: 91002101    	add	x1, x8, #0x8
10000a264: 910006c2    	add	x2, x22, #0x1
10000a268: 940004c6    	bl	0x10000b580 <_strlen+0x10000b580>
10000a26c: 8b1402d4    	add	x20, x22, x20
10000a270: 9100c3e0    	add	x0, sp, #0x30
10000a274: aa1403e1    	mov	x1, x20
10000a278: aa1303e2    	mov	x2, x19
10000a27c: 97fff6b1    	bl	0x100007d40 <_eqsink___system_u2642>
10000a280: b40000b5    	cbz	x21, 0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a284: 39401ea8    	ldrb	w8, [x21, #0x7]
10000a288: 37300068    	tbnz	w8, #0x6, 0x10000a294 <_formatInt__add95carry_u804+0x658>
10000a28c: aa1503e0    	mov	x0, x21
10000a290: 97ffeeb8    	bl	0x100005d70 <_deallocShared>
10000a294: a94307e0    	ldp	x0, x1, [sp, #0x30]
10000a298: a9497bfd    	ldp	x29, x30, [sp, #0x90]
10000a29c: a9484ff4    	ldp	x20, x19, [sp, #0x80]
10000a2a0: a94757f6    	ldp	x22, x21, [sp, #0x70]
10000a2a4: a9465ff8    	ldp	x24, x23, [sp, #0x60]
10000a2a8: a94567fa    	ldp	x26, x25, [sp, #0x50]
10000a2ac: a9446ffc    	ldp	x28, x27, [sp, #0x40]
10000a2b0: 910283ff    	add	sp, sp, #0xa0
10000a2b4: d65f03c0    	ret

000000010000a2b8 <_formatValue__add95carry_u796>:
10000a2b8: a9bd57f6    	stp	x22, x21, [sp, #-0x30]!
10000a2bc: a9014ff4    	stp	x20, x19, [sp, #0x10]
10000a2c0: a9027bfd    	stp	x29, x30, [sp, #0x20]
10000a2c4: 910083fd    	add	x29, sp, #0x20
10000a2c8: aa0003f3    	mov	x19, x0
10000a2cc: d0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000a2d0: 91012000    	add	x0, x0, #0x48
10000a2d4: f9400008    	ldr	x8, [x0]
10000a2d8: d63f0100    	blr	x8
10000a2dc: aa0003f6    	mov	x22, x0
10000a2e0: b0000002    	adrp	x2, 0x10000b000 <_bench__add95carry_u844+0x104>
10000a2e4: 9123e042    	add	x2, x2, #0x8f8
10000a2e8: aa0103e0    	mov	x0, x1
10000a2ec: 52800141    	mov	w1, #0xa                ; =10
10000a2f0: 97fffe53    	bl	0x100009c3c <_formatInt__add95carry_u804>
10000a2f4: 394002c8    	ldrb	w8, [x22]
10000a2f8: 35000328    	cbnz	w8, 0x10000a35c <_formatValue__add95carry_u796+0xa4>
10000a2fc: aa0003f5    	mov	x21, x0
10000a300: aa0103f4    	mov	x20, x1
10000a304: aa1303e0    	mov	x0, x19
10000a308: aa1503e1    	mov	x1, x21
10000a30c: 97fff413    	bl	0x100007358 <_prepareAdd>
10000a310: f10006bf    	cmp	x21, #0x1
10000a314: 5400014b    	b.lt	0x10000a33c <_formatValue__add95carry_u796+0x84>
10000a318: a9402269    	ldp	x9, x8, [x19]
10000a31c: 8b090108    	add	x8, x8, x9
10000a320: 91002100    	add	x0, x8, #0x8
10000a324: 91002281    	add	x1, x20, #0x8
10000a328: 910006a2    	add	x2, x21, #0x1
10000a32c: 94000495    	bl	0x10000b580 <_strlen+0x10000b580>
10000a330: f9400268    	ldr	x8, [x19]
10000a334: 8b150108    	add	x8, x8, x21
10000a338: f9000268    	str	x8, [x19]
10000a33c: b4000114    	cbz	x20, 0x10000a35c <_formatValue__add95carry_u796+0xa4>
10000a340: 39401e88    	ldrb	w8, [x20, #0x7]
10000a344: 373000c8    	tbnz	w8, #0x6, 0x10000a35c <_formatValue__add95carry_u796+0xa4>
10000a348: aa1403e0    	mov	x0, x20
10000a34c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
10000a350: a9414ff4    	ldp	x20, x19, [sp, #0x10]
10000a354: a8c357f6    	ldp	x22, x21, [sp], #0x30
10000a358: 17ffee86    	b	0x100005d70 <_deallocShared>
10000a35c: a9427bfd    	ldp	x29, x30, [sp, #0x20]
10000a360: a9414ff4    	ldp	x20, x19, [sp, #0x10]
10000a364: a8c357f6    	ldp	x22, x21, [sp], #0x30
10000a368: d65f03c0    	ret

000000010000a36c <_rand__add95carry_u183>:
10000a36c: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
10000a370: a9017bfd    	stp	x29, x30, [sp, #0x10]
10000a374: 910043fd    	add	x29, sp, #0x10
10000a378: aa0003f3    	mov	x19, x0
10000a37c: d0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000a380: 91012000    	add	x0, x0, #0x48
10000a384: f9400008    	ldr	x8, [x0]
10000a388: d63f0100    	blr	x8
10000a38c: aa0003f4    	mov	x20, x0
10000a390: 6f00e400    	movi.2d	v0, #0000000000000000
10000a394: ad000260    	stp	q0, q0, [x19]
10000a398: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a39c: 97fffb97    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a3a0: 39400288    	ldrb	w8, [x20]
10000a3a4: 35000228    	cbnz	w8, 0x10000a3e8 <_rand__add95carry_u183+0x7c>
10000a3a8: f9000260    	str	x0, [x19]
10000a3ac: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a3b0: 97fffb92    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a3b4: 39400288    	ldrb	w8, [x20]
10000a3b8: 35000188    	cbnz	w8, 0x10000a3e8 <_rand__add95carry_u183+0x7c>
10000a3bc: f9000660    	str	x0, [x19, #0x8]
10000a3c0: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a3c4: 97fffb8d    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a3c8: 39400288    	ldrb	w8, [x20]
10000a3cc: 350000e8    	cbnz	w8, 0x10000a3e8 <_rand__add95carry_u183+0x7c>
10000a3d0: f9000a60    	str	x0, [x19, #0x10]
10000a3d4: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a3d8: 97fffb88    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a3dc: 39400288    	ldrb	w8, [x20]
10000a3e0: 35000048    	cbnz	w8, 0x10000a3e8 <_rand__add95carry_u183+0x7c>
10000a3e4: f9000e60    	str	x0, [x19, #0x18]
10000a3e8: a9417bfd    	ldp	x29, x30, [sp, #0x10]
10000a3ec: a8c24ff4    	ldp	x20, x19, [sp], #0x20
10000a3f0: d65f03c0    	ret

000000010000a3f4 <_pluseq___add95carry_u461>:
10000a3f4: f9400028    	ldr	x8, [x1]
10000a3f8: a9402809    	ldp	x9, x10, [x0]
10000a3fc: 8b090108    	add	x8, x8, x9
10000a400: f9000008    	str	x8, [x0]
10000a404: a9402c29    	ldp	x9, x11, [x1]
10000a408: eb09011f    	cmp	x8, x9
10000a40c: 9a8b2568    	cinc	x8, x11, lo
10000a410: 8b0a0108    	add	x8, x8, x10
10000a414: f9000408    	str	x8, [x0, #0x8]
10000a418: a940a829    	ldp	x9, x10, [x1, #0x8]
10000a41c: eb09011f    	cmp	x8, x9
10000a420: 9a8a2548    	cinc	x8, x10, lo
10000a424: a9412809    	ldp	x9, x10, [x0, #0x10]
10000a428: 8b090108    	add	x8, x8, x9
10000a42c: f9000808    	str	x8, [x0, #0x10]
10000a430: a9412c29    	ldp	x9, x11, [x1, #0x10]
10000a434: eb09011f    	cmp	x8, x9
10000a438: 9a8b2568    	cinc	x8, x11, lo
10000a43c: 8b0a0108    	add	x8, x8, x10
10000a440: f9000c08    	str	x8, [x0, #0x18]
10000a444: d65f03c0    	ret

000000010000a448 <_add256_asm__add95carry_u162>:
10000a448: a9402408    	ldp	x8, x9, [x0]
10000a44c: f940002a    	ldr	x10, [x1]
10000a450: ab080148    	adds	x8, x10, x8
10000a454: f9000008    	str	x8, [x0]
10000a458: f940042a    	ldr	x10, [x1, #0x8]
10000a45c: ba0a012a    	adcs	x10, x9, x10
10000a460: a9412408    	ldp	x8, x9, [x0, #0x10]
10000a464: f900040a    	str	x10, [x0, #0x8]
10000a468: f940082a    	ldr	x10, [x1, #0x10]
10000a46c: ba0a010a    	adcs	x10, x8, x10
10000a470: f900080a    	str	x10, [x0, #0x10]
10000a474: f9400c2a    	ldr	x10, [x1, #0x18]
10000a478: 9a0a012a    	adc	x10, x9, x10
10000a47c: f9000c0a    	str	x10, [x0, #0x18]
10000a480: d65f03c0    	ret

000000010000a484 <_add_intrinsics__add95carry_u504>:
10000a484: f9400028    	ldr	x8, [x1]
10000a488: a9402809    	ldp	x9, x10, [x0]
10000a48c: ab080128    	adds	x8, x9, x8
10000a490: f9000008    	str	x8, [x0]
10000a494: f9400428    	ldr	x8, [x1, #0x8]
10000a498: ba080148    	adcs	x8, x10, x8
10000a49c: f9000408    	str	x8, [x0, #0x8]
10000a4a0: f9400828    	ldr	x8, [x1, #0x10]
10000a4a4: a9412809    	ldp	x9, x10, [x0, #0x10]
10000a4a8: ba080128    	adcs	x8, x9, x8
10000a4ac: f9000808    	str	x8, [x0, #0x10]
10000a4b0: f9400c28    	ldr	x8, [x1, #0x18]
10000a4b4: 9a080148    	adc	x8, x10, x8
10000a4b8: f9000c08    	str	x8, [x0, #0x18]
10000a4bc: d65f03c0    	ret

000000010000a4c0 <_add_via_u128__add95carry_u532>:
10000a4c0: f9400028    	ldr	x8, [x1]
10000a4c4: a9402809    	ldp	x9, x10, [x0]
10000a4c8: ab080128    	adds	x8, x9, x8
10000a4cc: f9000008    	str	x8, [x0]
10000a4d0: f9400428    	ldr	x8, [x1, #0x8]
10000a4d4: ba1f0149    	adcs	x9, x10, xzr
10000a4d8: 1a9f37ea    	cset	w10, hs
10000a4dc: ab080128    	adds	x8, x9, x8
10000a4e0: f9000408    	str	x8, [x0, #0x8]
10000a4e4: f9400828    	ldr	x8, [x1, #0x10]
10000a4e8: a9412c09    	ldp	x9, x11, [x0, #0x10]
10000a4ec: ba0a0129    	adcs	x9, x9, x10
10000a4f0: 1a9f37ea    	cset	w10, hs
10000a4f4: ab080128    	adds	x8, x9, x8
10000a4f8: f9000808    	str	x8, [x0, #0x10]
10000a4fc: f9400c28    	ldr	x8, [x1, #0x18]
10000a500: 9a0a0169    	adc	x9, x11, x10
10000a504: 8b080128    	add	x8, x9, x8
10000a508: f9000c08    	str	x8, [x0, #0x18]
10000a50c: d65f03c0    	ret

000000010000a510 <_add256_pure__add95carry_u82>:
10000a510: f9400028    	ldr	x8, [x1]
10000a514: a9402809    	ldp	x9, x10, [x0]
10000a518: 8b080128    	add	x8, x9, x8
10000a51c: f9000008    	str	x8, [x0]
10000a520: a940242b    	ldp	x11, x9, [x1]
10000a524: eb0b011f    	cmp	x8, x11
10000a528: 8b090148    	add	x8, x10, x9
10000a52c: 9a882508    	cinc	x8, x8, lo
10000a530: f9000408    	str	x8, [x0, #0x8]
10000a534: a940a42a    	ldp	x10, x9, [x1, #0x8]
10000a538: eb0a011f    	cmp	x8, x10
10000a53c: a9412808    	ldp	x8, x10, [x0, #0x10]
10000a540: 8b090108    	add	x8, x8, x9
10000a544: 9a882508    	cinc	x8, x8, lo
10000a548: f9000808    	str	x8, [x0, #0x10]
10000a54c: a941242b    	ldp	x11, x9, [x1, #0x10]
10000a550: eb0b011f    	cmp	x8, x11
10000a554: 8b090148    	add	x8, x10, x9
10000a558: 9a882508    	cinc	x8, x8, lo
10000a55c: f9000c08    	str	x8, [x0, #0x18]
10000a560: d65f03c0    	ret

000000010000a564 <_add256_pure2__add95carry_u129>:
10000a564: f9400028    	ldr	x8, [x1]
10000a568: a9402809    	ldp	x9, x10, [x0]
10000a56c: 8b080128    	add	x8, x9, x8
10000a570: f9000008    	str	x8, [x0]
10000a574: f9400029    	ldr	x9, [x1]
10000a578: eb09011f    	cmp	x8, x9
10000a57c: 9a8a2548    	cinc	x8, x10, lo
10000a580: f9000408    	str	x8, [x0, #0x8]
10000a584: f9400429    	ldr	x9, [x1, #0x8]
10000a588: 8b090108    	add	x8, x8, x9
10000a58c: f9000408    	str	x8, [x0, #0x8]
10000a590: f9400429    	ldr	x9, [x1, #0x8]
10000a594: eb09011f    	cmp	x8, x9
10000a598: a9412408    	ldp	x8, x9, [x0, #0x10]
10000a59c: 9a882508    	cinc	x8, x8, lo
10000a5a0: f9000808    	str	x8, [x0, #0x10]
10000a5a4: f940082a    	ldr	x10, [x1, #0x10]
10000a5a8: 8b0a0108    	add	x8, x8, x10
10000a5ac: f9000808    	str	x8, [x0, #0x10]
10000a5b0: f940082a    	ldr	x10, [x1, #0x10]
10000a5b4: eb0a011f    	cmp	x8, x10
10000a5b8: 9a892528    	cinc	x8, x9, lo
10000a5bc: f9000c08    	str	x8, [x0, #0x18]
10000a5c0: f9400c29    	ldr	x9, [x1, #0x18]
10000a5c4: 8b090108    	add	x8, x8, x9
10000a5c8: f9000c08    	str	x8, [x0, #0x18]
10000a5cc: d65f03c0    	ret

000000010000a5d0 <_addcarry_via128__add95carry_u20>:
10000a5d0: ab224068    	adds	x8, x3, w2, uxtw
10000a5d4: 1a9f37e9    	cset	w9, hs
10000a5d8: ab040108    	adds	x8, x8, x4
10000a5dc: f9000008    	str	x8, [x0]
10000a5e0: 1a893528    	cinc	w8, w9, hs
10000a5e4: 12000108    	and	w8, w8, #0x1
10000a5e8: 39000028    	strb	w8, [x1]
10000a5ec: d65f03c0    	ret

000000010000a5f0 <_add_via_addcarry128__add95carry_u582>:
10000a5f0: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
10000a5f4: 910003fd    	mov	x29, sp
10000a5f8: aa0003e8    	mov	x8, x0
10000a5fc: d0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000a600: 91012000    	add	x0, x0, #0x48
10000a604: f9400009    	ldr	x9, [x0]
10000a608: d63f0120    	blr	x9
10000a60c: 3940000b    	ldrb	w11, [x0]
10000a610: f940010a    	ldr	x10, [x8]
10000a614: f9400029    	ldr	x9, [x1]
10000a618: 8b090149    	add	x9, x10, x9
10000a61c: 350002cb    	cbnz	w11, 0x10000a674 <_add_via_addcarry128__add95carry_u582+0x84>
10000a620: eb0a013f    	cmp	x9, x10
10000a624: 1a9f27ea    	cset	w10, lo
10000a628: f9000109    	str	x9, [x8]
10000a62c: f9400429    	ldr	x9, [x1, #0x8]
10000a630: a940b10b    	ldp	x11, x12, [x8, #0x8]
10000a634: ab0a016a    	adds	x10, x11, x10
10000a638: 1a9f37eb    	cset	w11, hs
10000a63c: ab090149    	adds	x9, x10, x9
10000a640: f9000509    	str	x9, [x8, #0x8]
10000a644: f9400829    	ldr	x9, [x1, #0x10]
10000a648: ba0b018a    	adcs	x10, x12, x11
10000a64c: 1a9f37eb    	cset	w11, hs
10000a650: ab090149    	adds	x9, x10, x9
10000a654: f9000909    	str	x9, [x8, #0x10]
10000a658: f9400d09    	ldr	x9, [x8, #0x18]
10000a65c: f9400c2a    	ldr	x10, [x1, #0x18]
10000a660: 9a0b0129    	adc	x9, x9, x11
10000a664: 8b0a0129    	add	x9, x9, x10
10000a668: f9000d09    	str	x9, [x8, #0x18]
10000a66c: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000a670: d65f03c0    	ret
10000a674: f9000109    	str	x9, [x8]
10000a678: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000a67c: d65f03c0    	ret

000000010000a680 <_main__add95carry_u181>:
10000a680: a9ba6ffc    	stp	x28, x27, [sp, #-0x60]!
10000a684: a90167fa    	stp	x26, x25, [sp, #0x10]
10000a688: a9025ff8    	stp	x24, x23, [sp, #0x20]
10000a68c: a90357f6    	stp	x22, x21, [sp, #0x30]
10000a690: a9044ff4    	stp	x20, x19, [sp, #0x40]
10000a694: a9057bfd    	stp	x29, x30, [sp, #0x50]
10000a698: 910143fd    	add	x29, sp, #0x50
10000a69c: d10943ff    	sub	sp, sp, #0x250
10000a6a0: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a6a4: f9400908    	ldr	x8, [x8, #0x10]
10000a6a8: f9400108    	ldr	x8, [x8]
10000a6ac: f81a03a8    	stur	x8, [x29, #-0x60]
10000a6b0: d0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000a6b4: 91012000    	add	x0, x0, #0x48
10000a6b8: f9400008    	ldr	x8, [x0]
10000a6bc: d63f0100    	blr	x8
10000a6c0: aa0003f4    	mov	x20, x0
10000a6c4: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a6c8: 97fffacc    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a6cc: 39400288    	ldrb	w8, [x20]
10000a6d0: 35001f88    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a6d4: f90083e0    	str	x0, [sp, #0x100]
10000a6d8: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a6dc: 97fffac7    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a6e0: 39400288    	ldrb	w8, [x20]
10000a6e4: 35001ee8    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a6e8: f90087e0    	str	x0, [sp, #0x108]
10000a6ec: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a6f0: 97fffac2    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a6f4: 39400288    	ldrb	w8, [x20]
10000a6f8: 35001e48    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a6fc: f9008be0    	str	x0, [sp, #0x110]
10000a700: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a704: 97fffabd    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a708: 39400288    	ldrb	w8, [x20]
10000a70c: 35001da8    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a710: f9008fe0    	str	x0, [sp, #0x118]
10000a714: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a718: 97fffab8    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a71c: 39400288    	ldrb	w8, [x20]
10000a720: 35001d08    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a724: f90073e0    	str	x0, [sp, #0xe0]
10000a728: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a72c: 97fffab3    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a730: 39400288    	ldrb	w8, [x20]
10000a734: 35001c68    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a738: f90077e0    	str	x0, [sp, #0xe8]
10000a73c: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a740: 97fffaae    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a744: 39400288    	ldrb	w8, [x20]
10000a748: 35001bc8    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a74c: f9007be0    	str	x0, [sp, #0xf0]
10000a750: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000a754: 97fffaa9    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000a758: 39400288    	ldrb	w8, [x20]
10000a75c: 35001b28    	cbnz	w8, 0x10000aac0 <_main__add95carry_u181+0x440>
10000a760: f9007fe0    	str	x0, [sp, #0xf8]
10000a764: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a768: 91050108    	add	x8, x8, #0x140
10000a76c: 3dc00100    	ldr	q0, [x8]
10000a770: 3c9803a0    	stur	q0, [x29, #-0x80]
10000a774: 910403e0    	add	x0, sp, #0x100
10000a778: 97ffe541    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a77c: aa0103f3    	mov	x19, x1
10000a780: 39400288    	ldrb	w8, [x20]
10000a784: 35001948    	cbnz	w8, 0x10000aaac <_main__add95carry_u181+0x42c>
10000a788: a9394fa0    	stp	x0, x19, [x29, #-0x70]
10000a78c: d10203a0    	sub	x0, x29, #0x80
10000a790: 52800041    	mov	w1, #0x2                ; =2
10000a794: 97fff485    	bl	0x1000079a8 <_echoBinSafe>
10000a798: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a79c: 91054108    	add	x8, x8, #0x150
10000a7a0: 3dc00100    	ldr	q0, [x8]
10000a7a4: 3c9603a0    	stur	q0, [x29, #-0xa0]
10000a7a8: 910383e0    	add	x0, sp, #0xe0
10000a7ac: 97ffe534    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a7b0: aa0103f5    	mov	x21, x1
10000a7b4: 39400288    	ldrb	w8, [x20]
10000a7b8: 35001708    	cbnz	w8, 0x10000aa98 <_main__add95carry_u181+0x418>
10000a7bc: a93757a0    	stp	x0, x21, [x29, #-0x90]
10000a7c0: d10283a0    	sub	x0, x29, #0xa0
10000a7c4: 52800041    	mov	w1, #0x2                ; =2
10000a7c8: 97fff478    	bl	0x1000079a8 <_echoBinSafe>
10000a7cc: d0000000    	adrp	x0, 0x10000c000 <_strlen+0x10000c000>
10000a7d0: 91058000    	add	x0, x0, #0x160
10000a7d4: 52800021    	mov	w1, #0x1                ; =1
10000a7d8: 97fff474    	bl	0x1000079a8 <_echoBinSafe>
10000a7dc: ad4807e0    	ldp	q0, q1, [sp, #0x100]
10000a7e0: ad0607e0    	stp	q0, q1, [sp, #0xc0]
10000a7e4: 910303e0    	add	x0, sp, #0xc0
10000a7e8: 910383e1    	add	x1, sp, #0xe0
10000a7ec: 97ffff02    	bl	0x10000a3f4 <_pluseq___add95carry_u461>
10000a7f0: 39400288    	ldrb	w8, [x20]
10000a7f4: 35001528    	cbnz	w8, 0x10000aa98 <_main__add95carry_u181+0x418>
10000a7f8: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a7fc: 9105c108    	add	x8, x8, #0x170
10000a800: 3dc00100    	ldr	q0, [x8]
10000a804: 3c9403a0    	stur	q0, [x29, #-0xc0]
10000a808: 910303e0    	add	x0, sp, #0xc0
10000a80c: 97ffe51c    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a810: aa0103f6    	mov	x22, x1
10000a814: 39400288    	ldrb	w8, [x20]
10000a818: 35001368    	cbnz	w8, 0x10000aa84 <_main__add95carry_u181+0x404>
10000a81c: a9355ba0    	stp	x0, x22, [x29, #-0xb0]
10000a820: d10303a0    	sub	x0, x29, #0xc0
10000a824: 52800041    	mov	w1, #0x2                ; =2
10000a828: 97fff460    	bl	0x1000079a8 <_echoBinSafe>
10000a82c: ad4807e0    	ldp	q0, q1, [sp, #0x100]
10000a830: ad0507e0    	stp	q0, q1, [sp, #0xa0]
10000a834: 910283e0    	add	x0, sp, #0xa0
10000a838: 910383e1    	add	x1, sp, #0xe0
10000a83c: 97ffff03    	bl	0x10000a448 <_add256_asm__add95carry_u162>
10000a840: 39400288    	ldrb	w8, [x20]
10000a844: 35001208    	cbnz	w8, 0x10000aa84 <_main__add95carry_u181+0x404>
10000a848: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a84c: 91060108    	add	x8, x8, #0x180
10000a850: 3dc00100    	ldr	q0, [x8]
10000a854: 3c9203a0    	stur	q0, [x29, #-0xe0]
10000a858: 910283e0    	add	x0, sp, #0xa0
10000a85c: 97ffe508    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a860: aa0103f7    	mov	x23, x1
10000a864: 39400288    	ldrb	w8, [x20]
10000a868: 35001048    	cbnz	w8, 0x10000aa70 <_main__add95carry_u181+0x3f0>
10000a86c: a9335fa0    	stp	x0, x23, [x29, #-0xd0]
10000a870: d10383a0    	sub	x0, x29, #0xe0
10000a874: 52800041    	mov	w1, #0x2                ; =2
10000a878: 97fff44c    	bl	0x1000079a8 <_echoBinSafe>
10000a87c: ad4807e0    	ldp	q0, q1, [sp, #0x100]
10000a880: ad0407e0    	stp	q0, q1, [sp, #0x80]
10000a884: 910203e0    	add	x0, sp, #0x80
10000a888: 910383e1    	add	x1, sp, #0xe0
10000a88c: 97fffefe    	bl	0x10000a484 <_add_intrinsics__add95carry_u504>
10000a890: 39400288    	ldrb	w8, [x20]
10000a894: 35000ee8    	cbnz	w8, 0x10000aa70 <_main__add95carry_u181+0x3f0>
10000a898: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a89c: 91064108    	add	x8, x8, #0x190
10000a8a0: 3dc00100    	ldr	q0, [x8]
10000a8a4: 3c9003a0    	stur	q0, [x29, #-0x100]
10000a8a8: 910203e0    	add	x0, sp, #0x80
10000a8ac: 97ffe4f4    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a8b0: aa0103f8    	mov	x24, x1
10000a8b4: 39400288    	ldrb	w8, [x20]
10000a8b8: 35000d28    	cbnz	w8, 0x10000aa5c <_main__add95carry_u181+0x3dc>
10000a8bc: a93163a0    	stp	x0, x24, [x29, #-0xf0]
10000a8c0: d10403a0    	sub	x0, x29, #0x100
10000a8c4: 52800041    	mov	w1, #0x2                ; =2
10000a8c8: 97fff438    	bl	0x1000079a8 <_echoBinSafe>
10000a8cc: ad4807e0    	ldp	q0, q1, [sp, #0x100]
10000a8d0: ad0307e0    	stp	q0, q1, [sp, #0x60]
10000a8d4: 910183e0    	add	x0, sp, #0x60
10000a8d8: 910383e1    	add	x1, sp, #0xe0
10000a8dc: 97fffef9    	bl	0x10000a4c0 <_add_via_u128__add95carry_u532>
10000a8e0: 39400288    	ldrb	w8, [x20]
10000a8e4: 35000bc8    	cbnz	w8, 0x10000aa5c <_main__add95carry_u181+0x3dc>
10000a8e8: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a8ec: 91068108    	add	x8, x8, #0x1a0
10000a8f0: 3dc00100    	ldr	q0, [x8]
10000a8f4: 3d8063e0    	str	q0, [sp, #0x180]
10000a8f8: 910183e0    	add	x0, sp, #0x60
10000a8fc: 97ffe4e0    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a900: aa0103f9    	mov	x25, x1
10000a904: 39400288    	ldrb	w8, [x20]
10000a908: 35000a08    	cbnz	w8, 0x10000aa48 <_main__add95carry_u181+0x3c8>
10000a90c: a91967e0    	stp	x0, x25, [sp, #0x190]
10000a910: 910603e0    	add	x0, sp, #0x180
10000a914: 52800041    	mov	w1, #0x2                ; =2
10000a918: 97fff424    	bl	0x1000079a8 <_echoBinSafe>
10000a91c: ad4807e0    	ldp	q0, q1, [sp, #0x100]
10000a920: ad0207e0    	stp	q0, q1, [sp, #0x40]
10000a924: 910103e0    	add	x0, sp, #0x40
10000a928: 910383e1    	add	x1, sp, #0xe0
10000a92c: 97fffef9    	bl	0x10000a510 <_add256_pure__add95carry_u82>
10000a930: 39400288    	ldrb	w8, [x20]
10000a934: 350008a8    	cbnz	w8, 0x10000aa48 <_main__add95carry_u181+0x3c8>
10000a938: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a93c: 9106c108    	add	x8, x8, #0x1b0
10000a940: 3dc00100    	ldr	q0, [x8]
10000a944: 3d805be0    	str	q0, [sp, #0x160]
10000a948: 910103e0    	add	x0, sp, #0x40
10000a94c: 97ffe4cc    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a950: aa0103fa    	mov	x26, x1
10000a954: 39400288    	ldrb	w8, [x20]
10000a958: 350006e8    	cbnz	w8, 0x10000aa34 <_main__add95carry_u181+0x3b4>
10000a95c: a9176be0    	stp	x0, x26, [sp, #0x170]
10000a960: 910583e0    	add	x0, sp, #0x160
10000a964: 52800041    	mov	w1, #0x2                ; =2
10000a968: 97fff410    	bl	0x1000079a8 <_echoBinSafe>
10000a96c: ad4807e0    	ldp	q0, q1, [sp, #0x100]
10000a970: ad0107e0    	stp	q0, q1, [sp, #0x20]
10000a974: 910083e0    	add	x0, sp, #0x20
10000a978: 910383e1    	add	x1, sp, #0xe0
10000a97c: 97fffefa    	bl	0x10000a564 <_add256_pure2__add95carry_u129>
10000a980: 39400288    	ldrb	w8, [x20]
10000a984: 35000588    	cbnz	w8, 0x10000aa34 <_main__add95carry_u181+0x3b4>
10000a988: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a98c: 91070108    	add	x8, x8, #0x1c0
10000a990: 3dc00100    	ldr	q0, [x8]
10000a994: 3d8053e0    	str	q0, [sp, #0x140]
10000a998: 910083e0    	add	x0, sp, #0x20
10000a99c: 97ffe4b8    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a9a0: aa0103fb    	mov	x27, x1
10000a9a4: 39400288    	ldrb	w8, [x20]
10000a9a8: 350003c8    	cbnz	w8, 0x10000aa20 <_main__add95carry_u181+0x3a0>
10000a9ac: a9156fe0    	stp	x0, x27, [sp, #0x150]
10000a9b0: 910503e0    	add	x0, sp, #0x140
10000a9b4: 52800041    	mov	w1, #0x2                ; =2
10000a9b8: 97fff3fc    	bl	0x1000079a8 <_echoBinSafe>
10000a9bc: ad4807e0    	ldp	q0, q1, [sp, #0x100]
10000a9c0: ad0007e0    	stp	q0, q1, [sp]
10000a9c4: 910003e0    	mov	x0, sp
10000a9c8: 910383e1    	add	x1, sp, #0xe0
10000a9cc: 97ffff09    	bl	0x10000a5f0 <_add_via_addcarry128__add95carry_u582>
10000a9d0: 39400288    	ldrb	w8, [x20]
10000a9d4: 35000268    	cbnz	w8, 0x10000aa20 <_main__add95carry_u181+0x3a0>
10000a9d8: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000a9dc: 91074108    	add	x8, x8, #0x1d0
10000a9e0: 3dc00100    	ldr	q0, [x8]
10000a9e4: 3d804be0    	str	q0, [sp, #0x120]
10000a9e8: 910003e0    	mov	x0, sp
10000a9ec: 97ffe4a4    	bl	0x100003c7c <_dollar___add95carry_u320>
10000a9f0: aa0103fc    	mov	x28, x1
10000a9f4: 39400288    	ldrb	w8, [x20]
10000a9f8: 350000a8    	cbnz	w8, 0x10000aa0c <_main__add95carry_u181+0x38c>
10000a9fc: a91373e0    	stp	x0, x28, [sp, #0x130]
10000aa00: 910483e0    	add	x0, sp, #0x120
10000aa04: 52800041    	mov	w1, #0x2                ; =2
10000aa08: 97fff3e8    	bl	0x1000079a8 <_echoBinSafe>
10000aa0c: b40000bc    	cbz	x28, 0x10000aa20 <_main__add95carry_u181+0x3a0>
10000aa10: 39401f88    	ldrb	w8, [x28, #0x7]
10000aa14: 37300068    	tbnz	w8, #0x6, 0x10000aa20 <_main__add95carry_u181+0x3a0>
10000aa18: aa1c03e0    	mov	x0, x28
10000aa1c: 97ffecd5    	bl	0x100005d70 <_deallocShared>
10000aa20: b40000bb    	cbz	x27, 0x10000aa34 <_main__add95carry_u181+0x3b4>
10000aa24: 39401f68    	ldrb	w8, [x27, #0x7]
10000aa28: 37300068    	tbnz	w8, #0x6, 0x10000aa34 <_main__add95carry_u181+0x3b4>
10000aa2c: aa1b03e0    	mov	x0, x27
10000aa30: 97ffecd0    	bl	0x100005d70 <_deallocShared>
10000aa34: b40000ba    	cbz	x26, 0x10000aa48 <_main__add95carry_u181+0x3c8>
10000aa38: 39401f48    	ldrb	w8, [x26, #0x7]
10000aa3c: 37300068    	tbnz	w8, #0x6, 0x10000aa48 <_main__add95carry_u181+0x3c8>
10000aa40: aa1a03e0    	mov	x0, x26
10000aa44: 97ffeccb    	bl	0x100005d70 <_deallocShared>
10000aa48: b40000b9    	cbz	x25, 0x10000aa5c <_main__add95carry_u181+0x3dc>
10000aa4c: 39401f28    	ldrb	w8, [x25, #0x7]
10000aa50: 37300068    	tbnz	w8, #0x6, 0x10000aa5c <_main__add95carry_u181+0x3dc>
10000aa54: aa1903e0    	mov	x0, x25
10000aa58: 97ffecc6    	bl	0x100005d70 <_deallocShared>
10000aa5c: b40000b8    	cbz	x24, 0x10000aa70 <_main__add95carry_u181+0x3f0>
10000aa60: 39401f08    	ldrb	w8, [x24, #0x7]
10000aa64: 37300068    	tbnz	w8, #0x6, 0x10000aa70 <_main__add95carry_u181+0x3f0>
10000aa68: aa1803e0    	mov	x0, x24
10000aa6c: 97ffecc1    	bl	0x100005d70 <_deallocShared>
10000aa70: b40000b7    	cbz	x23, 0x10000aa84 <_main__add95carry_u181+0x404>
10000aa74: 39401ee8    	ldrb	w8, [x23, #0x7]
10000aa78: 37300068    	tbnz	w8, #0x6, 0x10000aa84 <_main__add95carry_u181+0x404>
10000aa7c: aa1703e0    	mov	x0, x23
10000aa80: 97ffecbc    	bl	0x100005d70 <_deallocShared>
10000aa84: b40000b6    	cbz	x22, 0x10000aa98 <_main__add95carry_u181+0x418>
10000aa88: 39401ec8    	ldrb	w8, [x22, #0x7]
10000aa8c: 37300068    	tbnz	w8, #0x6, 0x10000aa98 <_main__add95carry_u181+0x418>
10000aa90: aa1603e0    	mov	x0, x22
10000aa94: 97ffecb7    	bl	0x100005d70 <_deallocShared>
10000aa98: b40000b5    	cbz	x21, 0x10000aaac <_main__add95carry_u181+0x42c>
10000aa9c: 39401ea8    	ldrb	w8, [x21, #0x7]
10000aaa0: 37300068    	tbnz	w8, #0x6, 0x10000aaac <_main__add95carry_u181+0x42c>
10000aaa4: aa1503e0    	mov	x0, x21
10000aaa8: 97ffecb2    	bl	0x100005d70 <_deallocShared>
10000aaac: b40000b3    	cbz	x19, 0x10000aac0 <_main__add95carry_u181+0x440>
10000aab0: 39401e68    	ldrb	w8, [x19, #0x7]
10000aab4: 37300068    	tbnz	w8, #0x6, 0x10000aac0 <_main__add95carry_u181+0x440>
10000aab8: aa1303e0    	mov	x0, x19
10000aabc: 97ffecad    	bl	0x100005d70 <_deallocShared>
10000aac0: f85a03a8    	ldur	x8, [x29, #-0x60]
10000aac4: d0000009    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
10000aac8: f9400929    	ldr	x9, [x9, #0x10]
10000aacc: f9400129    	ldr	x9, [x9]
10000aad0: eb08013f    	cmp	x9, x8
10000aad4: 54000121    	b.ne	0x10000aaf8 <_main__add95carry_u181+0x478>
10000aad8: 910943ff    	add	sp, sp, #0x250
10000aadc: a9457bfd    	ldp	x29, x30, [sp, #0x50]
10000aae0: a9444ff4    	ldp	x20, x19, [sp, #0x40]
10000aae4: a94357f6    	ldp	x22, x21, [sp, #0x30]
10000aae8: a9425ff8    	ldp	x24, x23, [sp, #0x20]
10000aaec: a94167fa    	ldp	x26, x25, [sp, #0x10]
10000aaf0: a8c66ffc    	ldp	x28, x27, [sp], #0x60
10000aaf4: d65f03c0    	ret
10000aaf8: 94000284    	bl	0x10000b508 <_strlen+0x10000b508>

000000010000aafc <_warmup__add95carry_u684>:
10000aafc: d10183ff    	sub	sp, sp, #0x60
10000ab00: 6d0323e9    	stp	d9, d8, [sp, #0x30]
10000ab04: a9044ff4    	stp	x20, x19, [sp, #0x40]
10000ab08: a9057bfd    	stp	x29, x30, [sp, #0x50]
10000ab0c: 910143fd    	add	x29, sp, #0x50
10000ab10: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000ab14: f9400908    	ldr	x8, [x8, #0x10]
10000ab18: f9400108    	ldr	x8, [x8]
10000ab1c: f90017e8    	str	x8, [sp, #0x28]
10000ab20: d0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000ab24: 91012000    	add	x0, x0, #0x48
10000ab28: f9400008    	ldr	x8, [x0]
10000ab2c: d63f0100    	blr	x8
10000ab30: aa0003f3    	mov	x19, x0
10000ab34: 97fff87b    	bl	0x100008d20 <_cpuTime__pureZtimes_u5240>
10000ab38: 39400268    	ldrb	w8, [x19]
10000ab3c: 35000c08    	cbnz	w8, 0x10000acbc <_warmup__add95carry_u684+0x1c0>
10000ab40: 1e604008    	fmov	d8, d0
10000ab44: d2800008    	mov	x8, #0x0                ; =0
10000ab48: 52800f74    	mov	w20, #0x7b              ; =123
10000ab4c: d29dc129    	mov	x9, #0xee09             ; =60937
10000ab50: f2b70469    	movk	x9, #0xb823, lsl #16
10000ab54: f2dc11e9    	movk	x9, #0xe08f, lsl #32
10000ab58: f2e047c9    	movk	x9, #0x23e, lsl #48
10000ab5c: 5280390a    	mov	w10, #0x1c8             ; =456
10000ab60: d2835deb    	mov	x11, #0x1aef            ; =6895
10000ab64: f2a2072b    	movk	x11, #0x1039, lsl #16
10000ab68: f2d982cb    	movk	x11, #0xcc16, lsl #32
10000ab6c: f2f4c3eb    	movk	x11, #0xa61f, lsl #48
10000ab70: 528062ac    	mov	w12, #0x315             ; =789
10000ab74: 5294600d    	mov	w13, #0xa300            ; =41728
10000ab78: 72a23c2d    	movk	w13, #0x11e1, lsl #16
10000ab7c: 9b087d0e    	mul	x14, x8, x8
10000ab80: 9bc97dcf    	umulh	x15, x14, x9
10000ab84: d342fdef    	lsr	x15, x15, #2
10000ab88: 9b0ab9ee    	msub	x14, x15, x10, x14
10000ab8c: 8b1401ce    	add	x14, x14, x20
10000ab90: 9b4b7dcf    	smulh	x15, x14, x11
10000ab94: 8b0e01ef    	add	x15, x15, x14
10000ab98: 9349fdf0    	asr	x16, x15, #9
10000ab9c: 8b4ffe0f    	add	x15, x16, x15, lsr #63
10000aba0: 9b0cb9f4    	msub	x20, x15, x12, x14
10000aba4: 91000508    	add	x8, x8, #0x1
10000aba8: eb0d011f    	cmp	x8, x13
10000abac: 54fffe81    	b.ne	0x10000ab7c <_warmup__add95carry_u684+0x80>
10000abb0: 97fff85c    	bl	0x100008d20 <_cpuTime__pureZtimes_u5240>
10000abb4: 39400268    	ldrb	w8, [x19]
10000abb8: 35000828    	cbnz	w8, 0x10000acbc <_warmup__add95carry_u684+0x1c0>
10000abbc: 1e604009    	fmov	d9, d0
10000abc0: 52800ea0    	mov	w0, #0x75               ; =117
10000abc4: 97fff39f    	bl	0x100007a40 <_rawNewString>
10000abc8: a90087e0    	stp	x0, x1, [sp, #0x8]
10000abcc: 910023e0    	add	x0, sp, #0x8
10000abd0: 52800101    	mov	w1, #0x8                ; =8
10000abd4: 97fff1e1    	bl	0x100007358 <_prepareAdd>
10000abd8: a940a3e9    	ldp	x9, x8, [sp, #0x8]
10000abdc: 8b090108    	add	x8, x8, x9
10000abe0: b0000009    	adrp	x9, 0x10000b000 <_bench__add95carry_u844+0x104>
10000abe4: f9454d29    	ldr	x9, [x9, #0xa98]
10000abe8: f9000509    	str	x9, [x8, #0x8]
10000abec: 3900411f    	strb	wzr, [x8, #0x10]
10000abf0: f94007e8    	ldr	x8, [sp, #0x8]
10000abf4: 91002108    	add	x8, x8, #0x8
10000abf8: f90007e8    	str	x8, [sp, #0x8]
10000abfc: 1e683920    	fsub	d0, d9, d8
10000ac00: 910023e0    	add	x0, sp, #0x8
10000ac04: 97fffb84    	bl	0x100009a14 <_formatValue__add95carry_u709>
10000ac08: 39400268    	ldrb	w8, [x19]
10000ac0c: 35000588    	cbnz	w8, 0x10000acbc <_warmup__add95carry_u684+0x1c0>
10000ac10: 910023e0    	add	x0, sp, #0x8
10000ac14: 52800161    	mov	w1, #0xb                ; =11
10000ac18: 97fff1d0    	bl	0x100007358 <_prepareAdd>
10000ac1c: a940a3e9    	ldp	x9, x8, [sp, #0x8]
10000ac20: 8b090108    	add	x8, x8, x9
10000ac24: b0000009    	adrp	x9, 0x10000b000 <_bench__add95carry_u844+0x104>
10000ac28: f9455929    	ldr	x9, [x9, #0xab0]
10000ac2c: f9000509    	str	x9, [x8, #0x8]
10000ac30: 528e8d89    	mov	w9, #0x746c             ; =29804
10000ac34: 72a00409    	movk	w9, #0x20, lsl #16
10000ac38: b9001109    	str	w9, [x8, #0x10]
10000ac3c: f94007e8    	ldr	x8, [sp, #0x8]
10000ac40: 91002d08    	add	x8, x8, #0xb
10000ac44: f90007e8    	str	x8, [sp, #0x8]
10000ac48: 910023e0    	add	x0, sp, #0x8
10000ac4c: aa1403e1    	mov	x1, x20
10000ac50: 97fffb75    	bl	0x100009a24 <_formatValue__add95carry_u756>
10000ac54: 39400268    	ldrb	w8, [x19]
10000ac58: 35000328    	cbnz	w8, 0x10000acbc <_warmup__add95carry_u684+0x1c0>
10000ac5c: 910023e0    	add	x0, sp, #0x8
10000ac60: 528006a1    	mov	w1, #0x35               ; =53
10000ac64: 97fff1bd    	bl	0x100007358 <_prepareAdd>
10000ac68: a940cfe8    	ldp	x8, x19, [sp, #0x8]
10000ac6c: b0000009    	adrp	x9, 0x10000b000 <_bench__add95carry_u844+0x104>
10000ac70: 912b2129    	add	x9, x9, #0xac8
10000ac74: 8b08026a    	add	x10, x19, x8
10000ac78: ad400520    	ldp	q0, q1, [x9]
10000ac7c: 3c808140    	stur	q0, [x10, #0x8]
10000ac80: 3c818141    	stur	q1, [x10, #0x18]
10000ac84: 3dc00920    	ldr	q0, [x9, #0x20]
10000ac88: 3c828140    	stur	q0, [x10, #0x28]
10000ac8c: f842e129    	ldur	x9, [x9, #0x2e]
10000ac90: f8036149    	stur	x9, [x10, #0x36]
10000ac94: 9100d508    	add	x8, x8, #0x35
10000ac98: a901cfe8    	stp	x8, x19, [sp, #0x18]
10000ac9c: 910063e0    	add	x0, sp, #0x18
10000aca0: 52800021    	mov	w1, #0x1                ; =1
10000aca4: 97fff341    	bl	0x1000079a8 <_echoBinSafe>
10000aca8: b40000b3    	cbz	x19, 0x10000acbc <_warmup__add95carry_u684+0x1c0>
10000acac: 39401e68    	ldrb	w8, [x19, #0x7]
10000acb0: 37300068    	tbnz	w8, #0x6, 0x10000acbc <_warmup__add95carry_u684+0x1c0>
10000acb4: aa1303e0    	mov	x0, x19
10000acb8: 97ffec2e    	bl	0x100005d70 <_deallocShared>
10000acbc: f94017e8    	ldr	x8, [sp, #0x28]
10000acc0: d0000009    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
10000acc4: f9400929    	ldr	x9, [x9, #0x10]
10000acc8: f9400129    	ldr	x9, [x9]
10000accc: eb08013f    	cmp	x9, x8
10000acd0: 540000c1    	b.ne	0x10000ace8 <_warmup__add95carry_u684+0x1ec>
10000acd4: a9457bfd    	ldp	x29, x30, [sp, #0x50]
10000acd8: a9444ff4    	ldp	x20, x19, [sp, #0x40]
10000acdc: 6d4323e9    	ldp	d9, d8, [sp, #0x30]
10000ace0: 910183ff    	add	sp, sp, #0x60
10000ace4: d65f03c0    	ret
10000ace8: 94000208    	bl	0x10000b508 <_strlen+0x10000b508>

000000010000acec <_report__add95carry_u762>:
10000acec: d10243ff    	sub	sp, sp, #0x90
10000acf0: a9036ffc    	stp	x28, x27, [sp, #0x30]
10000acf4: a90467fa    	stp	x26, x25, [sp, #0x40]
10000acf8: a9055ff8    	stp	x24, x23, [sp, #0x50]
10000acfc: a90657f6    	stp	x22, x21, [sp, #0x60]
10000ad00: a9074ff4    	stp	x20, x19, [sp, #0x70]
10000ad04: a9087bfd    	stp	x29, x30, [sp, #0x80]
10000ad08: 910203fd    	add	x29, sp, #0x80
10000ad0c: aa0703f3    	mov	x19, x7
10000ad10: aa0603f4    	mov	x20, x6
10000ad14: aa0503f7    	mov	x23, x5
10000ad18: aa0403f6    	mov	x22, x4
10000ad1c: aa0303f8    	mov	x24, x3
10000ad20: aa0203f9    	mov	x25, x2
10000ad24: aa0103fa    	mov	x26, x1
10000ad28: aa0003fb    	mov	x27, x0
10000ad2c: d0000008    	adrp	x8, 0x10000c000 <_strlen+0x10000c000>
10000ad30: f9400908    	ldr	x8, [x8, #0x10]
10000ad34: f9400108    	ldr	x8, [x8]
10000ad38: f90017e8    	str	x8, [sp, #0x28]
10000ad3c: d0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000ad40: 91012000    	add	x0, x0, #0x48
10000ad44: f9400008    	ldr	x8, [x0]
10000ad48: d63f0100    	blr	x8
10000ad4c: aa0003f5    	mov	x21, x0
10000ad50: 52801260    	mov	w0, #0x93               ; =147
10000ad54: 97fff33b    	bl	0x100007a40 <_rawNewString>
10000ad58: a90087e0    	stp	x0, x1, [sp, #0x8]
10000ad5c: 910023e0    	add	x0, sp, #0x8
10000ad60: aa1b03e1    	mov	x1, x27
10000ad64: aa1a03e2    	mov	x2, x26
10000ad68: 97fffb59    	bl	0x100009acc <_formatValue__add95carry_u774>
10000ad6c: 394002a8    	ldrb	w8, [x21]
10000ad70: 35000a88    	cbnz	w8, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000ad74: 910023e0    	add	x0, sp, #0x8
10000ad78: 52800021    	mov	w1, #0x1                ; =1
10000ad7c: 97fff177    	bl	0x100007358 <_prepareAdd>
10000ad80: a940a3e9    	ldp	x9, x8, [sp, #0x8]
10000ad84: 8b090108    	add	x8, x8, x9
10000ad88: 5280041a    	mov	w26, #0x20              ; =32
10000ad8c: 7900111a    	strh	w26, [x8, #0x8]
10000ad90: f94007e8    	ldr	x8, [sp, #0x8]
10000ad94: 91000508    	add	x8, x8, #0x1
10000ad98: f90007e8    	str	x8, [sp, #0x8]
10000ad9c: 910023e0    	add	x0, sp, #0x8
10000ada0: aa1903e1    	mov	x1, x25
10000ada4: aa1803e2    	mov	x2, x24
10000ada8: 97fffb77    	bl	0x100009b84 <_formatValue__add95carry_u785>
10000adac: 394002a8    	ldrb	w8, [x21]
10000adb0: 35000888    	cbnz	w8, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000adb4: 910023e0    	add	x0, sp, #0x8
10000adb8: 52800021    	mov	w1, #0x1                ; =1
10000adbc: 97fff167    	bl	0x100007358 <_prepareAdd>
10000adc0: a940a3e9    	ldp	x9, x8, [sp, #0x8]
10000adc4: 8b090108    	add	x8, x8, x9
10000adc8: 7900111a    	strh	w26, [x8, #0x8]
10000adcc: f94007e8    	ldr	x8, [sp, #0x8]
10000add0: 91000508    	add	x8, x8, #0x1
10000add4: f90007e8    	str	x8, [sp, #0x8]
10000add8: aa1703e0    	mov	x0, x23
10000addc: aa1603e1    	mov	x1, x22
10000ade0: 97fff875    	bl	0x100008fb4 <_minus___stdZmonotimes_u58>
10000ade4: 394002a8    	ldrb	w8, [x21]
10000ade8: 350006c8    	cbnz	w8, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000adec: f9400bb6    	ldr	x22, [x29, #0x10]
10000adf0: aa1603e2    	mov	x2, x22
10000adf4: 97fff7f7    	bl	0x100008dd0 <_ntDivDuration>
10000adf8: 394002a8    	ldrb	w8, [x21]
10000adfc: 35000628    	cbnz	w8, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000ae00: 97fff7d2    	bl	0x100008d48 <_inNanoseconds__pureZtimes_u878>
10000ae04: 394002a8    	ldrb	w8, [x21]
10000ae08: 350005c8    	cbnz	w8, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000ae0c: aa0003e1    	mov	x1, x0
10000ae10: 910023e0    	add	x0, sp, #0x8
10000ae14: 97fffd29    	bl	0x10000a2b8 <_formatValue__add95carry_u796>
10000ae18: 394002a8    	ldrb	w8, [x21]
10000ae1c: 35000528    	cbnz	w8, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000ae20: 910023e0    	add	x0, sp, #0x8
10000ae24: 52800081    	mov	w1, #0x4                ; =4
10000ae28: 97fff14c    	bl	0x100007358 <_prepareAdd>
10000ae2c: a940a3e9    	ldp	x9, x8, [sp, #0x8]
10000ae30: 8b090108    	add	x8, x8, x9
10000ae34: 3900311f    	strb	wzr, [x8, #0xc]
10000ae38: 528dc409    	mov	w9, #0x6e20             ; =28192
10000ae3c: 72a40e69    	movk	w9, #0x2073, lsl #16
10000ae40: b9000909    	str	w9, [x8, #0x8]
10000ae44: f94007e8    	ldr	x8, [sp, #0x8]
10000ae48: 91001108    	add	x8, x8, #0x4
10000ae4c: f90007e8    	str	x8, [sp, #0x8]
10000ae50: cb140268    	sub	x8, x19, x20
10000ae54: 9ad60d01    	sdiv	x1, x8, x22
10000ae58: 910023e0    	add	x0, sp, #0x8
10000ae5c: 97fffd17    	bl	0x10000a2b8 <_formatValue__add95carry_u796>
10000ae60: 394002a8    	ldrb	w8, [x21]
10000ae64: 350002e8    	cbnz	w8, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000ae68: 910023e0    	add	x0, sp, #0x8
10000ae6c: 528000c1    	mov	w1, #0x6                ; =6
10000ae70: 97fff13a    	bl	0x100007358 <_prepareAdd>
10000ae74: a940a3e9    	ldp	x9, x8, [sp, #0x8]
10000ae78: 8b090108    	add	x8, x8, x9
10000ae7c: 528d6c69    	mov	w9, #0x6b63             ; =27491
10000ae80: 72a00e69    	movk	w9, #0x73, lsl #16
10000ae84: b800b109    	stur	w9, [x8, #0xb]
10000ae88: 528e8409    	mov	w9, #0x7420             ; =29728
10000ae8c: 72ac6d29    	movk	w9, #0x6369, lsl #16
10000ae90: b9000909    	str	w9, [x8, #0x8]
10000ae94: a940cfe8    	ldp	x8, x19, [sp, #0x8]
10000ae98: 91001908    	add	x8, x8, #0x6
10000ae9c: a901cfe8    	stp	x8, x19, [sp, #0x18]
10000aea0: 910063e0    	add	x0, sp, #0x18
10000aea4: 52800021    	mov	w1, #0x1                ; =1
10000aea8: 97fff2c0    	bl	0x1000079a8 <_echoBinSafe>
10000aeac: b40000b3    	cbz	x19, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000aeb0: 39401e68    	ldrb	w8, [x19, #0x7]
10000aeb4: 37300068    	tbnz	w8, #0x6, 0x10000aec0 <_report__add95carry_u762+0x1d4>
10000aeb8: aa1303e0    	mov	x0, x19
10000aebc: 97ffebad    	bl	0x100005d70 <_deallocShared>
10000aec0: f94017e8    	ldr	x8, [sp, #0x28]
10000aec4: d0000009    	adrp	x9, 0x10000c000 <_strlen+0x10000c000>
10000aec8: f9400929    	ldr	x9, [x9, #0x10]
10000aecc: f9400129    	ldr	x9, [x9]
10000aed0: eb08013f    	cmp	x9, x8
10000aed4: 54000121    	b.ne	0x10000aef8 <_report__add95carry_u762+0x20c>
10000aed8: a9487bfd    	ldp	x29, x30, [sp, #0x80]
10000aedc: a9474ff4    	ldp	x20, x19, [sp, #0x70]
10000aee0: a94657f6    	ldp	x22, x21, [sp, #0x60]
10000aee4: a9455ff8    	ldp	x24, x23, [sp, #0x50]
10000aee8: a94467fa    	ldp	x26, x25, [sp, #0x40]
10000aeec: a9436ffc    	ldp	x28, x27, [sp, #0x30]
10000aef0: 910243ff    	add	sp, sp, #0x90
10000aef4: d65f03c0    	ret
10000aef8: 94000184    	bl	0x10000b508 <_strlen+0x10000b508>

000000010000aefc <_bench__add95carry_u844>:
10000aefc: d102c3ff    	sub	sp, sp, #0xb0
10000af00: a9056ffc    	stp	x28, x27, [sp, #0x50]
10000af04: a90667fa    	stp	x26, x25, [sp, #0x60]
10000af08: a9075ff8    	stp	x24, x23, [sp, #0x70]
10000af0c: a90857f6    	stp	x22, x21, [sp, #0x80]
10000af10: a9094ff4    	stp	x20, x19, [sp, #0x90]
10000af14: a90a7bfd    	stp	x29, x30, [sp, #0xa0]
10000af18: 910283fd    	add	x29, sp, #0xa0
10000af1c: d0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000af20: 91012000    	add	x0, x0, #0x48
10000af24: f9400008    	ldr	x8, [x0]
10000af28: d63f0100    	blr	x8
10000af2c: aa0003f3    	mov	x19, x0
10000af30: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000af34: 97fff8b1    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000af38: 39400268    	ldrb	w8, [x19]
10000af3c: 35002088    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000af40: aa0003f4    	mov	x20, x0
10000af44: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000af48: 97fff8ac    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000af4c: 39400268    	ldrb	w8, [x19]
10000af50: 35001fe8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000af54: aa0003f5    	mov	x21, x0
10000af58: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000af5c: 97fff8a7    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000af60: 39400268    	ldrb	w8, [x19]
10000af64: 35001f48    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000af68: aa0003f6    	mov	x22, x0
10000af6c: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000af70: 97fff8a2    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000af74: 39400268    	ldrb	w8, [x19]
10000af78: 35001ea8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000af7c: aa0003f7    	mov	x23, x0
10000af80: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000af84: 97fff89d    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000af88: 39400268    	ldrb	w8, [x19]
10000af8c: 35001e08    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000af90: f9001be0    	str	x0, [sp, #0x30]
10000af94: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000af98: 97fff898    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000af9c: 39400268    	ldrb	w8, [x19]
10000afa0: 35001d68    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000afa4: f9001fe0    	str	x0, [sp, #0x38]
10000afa8: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000afac: 97fff893    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000afb0: 39400268    	ldrb	w8, [x19]
10000afb4: 35001cc8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000afb8: f90023e0    	str	x0, [sp, #0x40]
10000afbc: 92f00000    	mov	x0, #0x7fffffffffffffff ; =9223372036854775807
10000afc0: 97fff88e    	bl	0x1000091f8 <_rand__pureZrandom_u146>
10000afc4: 39400268    	ldrb	w8, [x19]
10000afc8: 35001c28    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000afcc: f90027e0    	str	x0, [sp, #0x48]
10000afd0: 97fff7e9    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000afd4: 39400268    	ldrb	w8, [x19]
10000afd8: 35001ba8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000afdc: aa0003f8    	mov	x24, x0
10000afe0: 94000162    	bl	0x10000b568 <_strlen+0x10000b568>
10000afe4: 39400268    	ldrb	w8, [x19]
10000afe8: 35001b28    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000afec: aa0003f9    	mov	x25, x0
10000aff0: 9400015e    	bl	0x10000b568 <_strlen+0x10000b568>
10000aff4: 39400268    	ldrb	w8, [x19]
10000aff8: 35001aa8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000affc: aa0003fa    	mov	x26, x0
10000b000: 97fff7dd    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b004: 39400268    	ldrb	w8, [x19]
10000b008: 35001a28    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b00c: aa0003e5    	mov	x5, x0
10000b010: 5288481b    	mov	w27, #0x4240            ; =16960
10000b014: 72a001fb    	movk	w27, #0xf, lsl #16
10000b018: f90003fb    	str	x27, [sp]
10000b01c: 90000001    	adrp	x1, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b020: 912c8021    	add	x1, x1, #0xb20
10000b024: 90000003    	adrp	x3, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b028: 912d0063    	add	x3, x3, #0xb40
10000b02c: 52800240    	mov	w0, #0x12               ; =18
10000b030: 52800102    	mov	w2, #0x8                ; =8
10000b034: aa1803e4    	mov	x4, x24
10000b038: aa1903e6    	mov	x6, x25
10000b03c: aa1a03e7    	mov	x7, x26
10000b040: 97ffff2b    	bl	0x10000acec <_report__add95carry_u762>
10000b044: 39400268    	ldrb	w8, [x19]
10000b048: 35001828    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b04c: a90157f4    	stp	x20, x21, [sp, #0x10]
10000b050: a9025ff6    	stp	x22, x23, [sp, #0x20]
10000b054: 97fff7c8    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b058: 39400268    	ldrb	w8, [x19]
10000b05c: 35001788    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b060: aa0003f8    	mov	x24, x0
10000b064: 94000141    	bl	0x10000b568 <_strlen+0x10000b568>
10000b068: 39400268    	ldrb	w8, [x19]
10000b06c: 35001708    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b070: aa0003f9    	mov	x25, x0
10000b074: 5288481a    	mov	w26, #0x4240            ; =16960
10000b078: 72a001fa    	movk	w26, #0xf, lsl #16
10000b07c: 910043e0    	add	x0, sp, #0x10
10000b080: 9100c3e1    	add	x1, sp, #0x30
10000b084: 97fffcf1    	bl	0x10000a448 <_add256_asm__add95carry_u162>
10000b088: 39400268    	ldrb	w8, [x19]
10000b08c: 35001608    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b090: f100075a    	subs	x26, x26, #0x1
10000b094: 54ffff41    	b.ne	0x10000b07c <_bench__add95carry_u844+0x180>
10000b098: 94000134    	bl	0x10000b568 <_strlen+0x10000b568>
10000b09c: 39400268    	ldrb	w8, [x19]
10000b0a0: 35001568    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b0a4: aa0003fa    	mov	x26, x0
10000b0a8: 97fff7b3    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b0ac: 39400268    	ldrb	w8, [x19]
10000b0b0: 350014e8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b0b4: aa0003e5    	mov	x5, x0
10000b0b8: f90003fb    	str	x27, [sp]
10000b0bc: 90000001    	adrp	x1, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b0c0: 912c8021    	add	x1, x1, #0xb20
10000b0c4: 90000003    	adrp	x3, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b0c8: 912d6063    	add	x3, x3, #0xb58
10000b0cc: 52800240    	mov	w0, #0x12               ; =18
10000b0d0: 52800102    	mov	w2, #0x8                ; =8
10000b0d4: aa1803e4    	mov	x4, x24
10000b0d8: aa1903e6    	mov	x6, x25
10000b0dc: aa1a03e7    	mov	x7, x26
10000b0e0: 97ffff03    	bl	0x10000acec <_report__add95carry_u762>
10000b0e4: 39400268    	ldrb	w8, [x19]
10000b0e8: 35001328    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b0ec: 97fff7a2    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b0f0: 39400268    	ldrb	w8, [x19]
10000b0f4: 350012c8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b0f8: aa0003f8    	mov	x24, x0
10000b0fc: 9400011b    	bl	0x10000b568 <_strlen+0x10000b568>
10000b100: 39400268    	ldrb	w8, [x19]
10000b104: 35001248    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b108: aa0003f9    	mov	x25, x0
10000b10c: 94000117    	bl	0x10000b568 <_strlen+0x10000b568>
10000b110: 39400268    	ldrb	w8, [x19]
10000b114: 350011c8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b118: aa0003fa    	mov	x26, x0
10000b11c: 97fff796    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b120: 39400268    	ldrb	w8, [x19]
10000b124: 35001148    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b128: aa0003e5    	mov	x5, x0
10000b12c: f90003fb    	str	x27, [sp]
10000b130: 90000001    	adrp	x1, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b134: 912c8021    	add	x1, x1, #0xb20
10000b138: 90000003    	adrp	x3, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b13c: 912dc063    	add	x3, x3, #0xb70
10000b140: 52800240    	mov	w0, #0x12               ; =18
10000b144: 52800142    	mov	w2, #0xa                ; =10
10000b148: aa1803e4    	mov	x4, x24
10000b14c: aa1903e6    	mov	x6, x25
10000b150: aa1a03e7    	mov	x7, x26
10000b154: 97fffee6    	bl	0x10000acec <_report__add95carry_u762>
10000b158: 39400268    	ldrb	w8, [x19]
10000b15c: 35000f88    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b160: 97fff785    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b164: 39400268    	ldrb	w8, [x19]
10000b168: 35000f28    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b16c: aa0003f8    	mov	x24, x0
10000b170: 940000fe    	bl	0x10000b568 <_strlen+0x10000b568>
10000b174: 39400268    	ldrb	w8, [x19]
10000b178: 35000ea8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b17c: aa0003f9    	mov	x25, x0
10000b180: 940000fa    	bl	0x10000b568 <_strlen+0x10000b568>
10000b184: 39400268    	ldrb	w8, [x19]
10000b188: 35000e28    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b18c: aa0003fa    	mov	x26, x0
10000b190: 97fff779    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b194: 39400268    	ldrb	w8, [x19]
10000b198: 35000da8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b19c: aa0003e5    	mov	x5, x0
10000b1a0: f90003fb    	str	x27, [sp]
10000b1a4: 90000001    	adrp	x1, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b1a8: 912c8021    	add	x1, x1, #0xb20
10000b1ac: 90000003    	adrp	x3, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b1b0: 912e2063    	add	x3, x3, #0xb88
10000b1b4: 52800240    	mov	w0, #0x12               ; =18
10000b1b8: 52800162    	mov	w2, #0xb                ; =11
10000b1bc: aa1803e4    	mov	x4, x24
10000b1c0: aa1903e6    	mov	x6, x25
10000b1c4: aa1a03e7    	mov	x7, x26
10000b1c8: 97fffec9    	bl	0x10000acec <_report__add95carry_u762>
10000b1cc: 39400268    	ldrb	w8, [x19]
10000b1d0: 35000be8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b1d4: 97fff768    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b1d8: 39400268    	ldrb	w8, [x19]
10000b1dc: 35000b88    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b1e0: aa0003f8    	mov	x24, x0
10000b1e4: 940000e1    	bl	0x10000b568 <_strlen+0x10000b568>
10000b1e8: 39400268    	ldrb	w8, [x19]
10000b1ec: 35000b08    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b1f0: aa0003f9    	mov	x25, x0
10000b1f4: 940000dd    	bl	0x10000b568 <_strlen+0x10000b568>
10000b1f8: 39400268    	ldrb	w8, [x19]
10000b1fc: 35000a88    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b200: aa0003fa    	mov	x26, x0
10000b204: 97fff75c    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b208: 39400268    	ldrb	w8, [x19]
10000b20c: 35000a08    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b210: aa0003e5    	mov	x5, x0
10000b214: f90003fb    	str	x27, [sp]
10000b218: 90000001    	adrp	x1, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b21c: 912c8021    	add	x1, x1, #0xb20
10000b220: 90000003    	adrp	x3, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b224: 912e8063    	add	x3, x3, #0xba0
10000b228: 52800240    	mov	w0, #0x12               ; =18
10000b22c: 52800102    	mov	w2, #0x8                ; =8
10000b230: aa1803e4    	mov	x4, x24
10000b234: aa1903e6    	mov	x6, x25
10000b238: aa1a03e7    	mov	x7, x26
10000b23c: 97fffeac    	bl	0x10000acec <_report__add95carry_u762>
10000b240: 39400268    	ldrb	w8, [x19]
10000b244: 35000848    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b248: 97fff74b    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b24c: 39400268    	ldrb	w8, [x19]
10000b250: 350007e8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b254: aa0003f8    	mov	x24, x0
10000b258: 940000c4    	bl	0x10000b568 <_strlen+0x10000b568>
10000b25c: 39400268    	ldrb	w8, [x19]
10000b260: 35000768    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b264: aa0003f9    	mov	x25, x0
10000b268: 940000c0    	bl	0x10000b568 <_strlen+0x10000b568>
10000b26c: 39400268    	ldrb	w8, [x19]
10000b270: 350006e8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b274: aa0003fa    	mov	x26, x0
10000b278: 97fff73f    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b27c: 39400268    	ldrb	w8, [x19]
10000b280: 35000668    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b284: aa0003e5    	mov	x5, x0
10000b288: f90003fb    	str	x27, [sp]
10000b28c: 90000001    	adrp	x1, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b290: 912c8021    	add	x1, x1, #0xb20
10000b294: 90000003    	adrp	x3, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b298: 912ee063    	add	x3, x3, #0xbb8
10000b29c: 52800240    	mov	w0, #0x12               ; =18
10000b2a0: 52800162    	mov	w2, #0xb                ; =11
10000b2a4: aa1803e4    	mov	x4, x24
10000b2a8: aa1903e6    	mov	x6, x25
10000b2ac: aa1a03e7    	mov	x7, x26
10000b2b0: 97fffe8f    	bl	0x10000acec <_report__add95carry_u762>
10000b2b4: 39400268    	ldrb	w8, [x19]
10000b2b8: 350004a8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b2bc: a90157f4    	stp	x20, x21, [sp, #0x10]
10000b2c0: a9025ff6    	stp	x22, x23, [sp, #0x20]
10000b2c4: 97fff72c    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b2c8: 39400268    	ldrb	w8, [x19]
10000b2cc: 35000408    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b2d0: aa0003f4    	mov	x20, x0
10000b2d4: 940000a5    	bl	0x10000b568 <_strlen+0x10000b568>
10000b2d8: 39400268    	ldrb	w8, [x19]
10000b2dc: 35000388    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b2e0: aa0003f5    	mov	x21, x0
10000b2e4: 52884816    	mov	w22, #0x4240            ; =16960
10000b2e8: 72a001f6    	movk	w22, #0xf, lsl #16
10000b2ec: 910043e0    	add	x0, sp, #0x10
10000b2f0: 9100c3e1    	add	x1, sp, #0x30
10000b2f4: 97fffcbf    	bl	0x10000a5f0 <_add_via_addcarry128__add95carry_u582>
10000b2f8: f10006d6    	subs	x22, x22, #0x1
10000b2fc: 54ffff81    	b.ne	0x10000b2ec <_bench__add95carry_u844+0x3f0>
10000b300: 9400009a    	bl	0x10000b568 <_strlen+0x10000b568>
10000b304: 39400268    	ldrb	w8, [x19]
10000b308: 35000228    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b30c: aa0003f6    	mov	x22, x0
10000b310: 97fff719    	bl	0x100008f74 <_getMonoTime__stdZmonotimes_u10>
10000b314: 39400268    	ldrb	w8, [x19]
10000b318: 350001a8    	cbnz	w8, 0x10000b34c <_bench__add95carry_u844+0x450>
10000b31c: aa0003e5    	mov	x5, x0
10000b320: f90003fb    	str	x27, [sp]
10000b324: 90000001    	adrp	x1, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b328: 912c8021    	add	x1, x1, #0xb20
10000b32c: 90000003    	adrp	x3, 0x10000b000 <_bench__add95carry_u844+0x104>
10000b330: 912f4063    	add	x3, x3, #0xbd0
10000b334: 52800240    	mov	w0, #0x12               ; =18
10000b338: 52800262    	mov	w2, #0x13               ; =19
10000b33c: aa1403e4    	mov	x4, x20
10000b340: aa1503e6    	mov	x6, x21
10000b344: aa1603e7    	mov	x7, x22
10000b348: 97fffe69    	bl	0x10000acec <_report__add95carry_u762>
10000b34c: a94a7bfd    	ldp	x29, x30, [sp, #0xa0]
10000b350: a9494ff4    	ldp	x20, x19, [sp, #0x90]
10000b354: a94857f6    	ldp	x22, x21, [sp, #0x80]
10000b358: a9475ff8    	ldp	x24, x23, [sp, #0x70]
10000b35c: a94667fa    	ldp	x26, x25, [sp, #0x60]
10000b360: a9456ffc    	ldp	x28, x27, [sp, #0x50]
10000b364: 9102c3ff    	add	sp, sp, #0xb0
10000b368: d65f03c0    	ret

000000010000b36c <_PreMainInner>:
10000b36c: 17fff7e2    	b	0x1000092f4 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatspureatsrandomdotnim_Init000>

000000010000b370 <_PreMain>:
10000b370: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
10000b374: 910003fd    	mov	x29, sp
10000b378: 97fff52a    	bl	0x100008820 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatssystemdotnim_Init000>
10000b37c: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000b380: 17fff7dd    	b	0x1000092f4 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatspureatsrandomdotnim_Init000>

000000010000b384 <_NimMainInner>:
10000b384: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
10000b388: a9017bfd    	stp	x29, x30, [sp, #0x10]
10000b38c: 910043fd    	add	x29, sp, #0x10
10000b390: b0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000b394: 91012000    	add	x0, x0, #0x48
10000b398: f9400008    	ldr	x8, [x0]
10000b39c: d63f0100    	blr	x8
10000b3a0: aa0003f3    	mov	x19, x0
10000b3a4: 97fffcb7    	bl	0x10000a680 <_main__add95carry_u181>
10000b3a8: 39400268    	ldrb	w8, [x19]
10000b3ac: 350001a8    	cbnz	w8, 0x10000b3e0 <_NimMainInner+0x5c>
10000b3b0: 97fffdd3    	bl	0x10000aafc <_warmup__add95carry_u684>
10000b3b4: 39400268    	ldrb	w8, [x19]
10000b3b8: 35000148    	cbnz	w8, 0x10000b3e0 <_NimMainInner+0x5c>
10000b3bc: b0000000    	adrp	x0, 0x10000c000 <_strlen+0x10000c000>
10000b3c0: 91078000    	add	x0, x0, #0x1e0
10000b3c4: 52800021    	mov	w1, #0x1                ; =1
10000b3c8: 97fff178    	bl	0x1000079a8 <_echoBinSafe>
10000b3cc: b0000000    	adrp	x0, 0x10000c000 <_strlen+0x10000c000>
10000b3d0: 9107c000    	add	x0, x0, #0x1f0
10000b3d4: 52800021    	mov	w1, #0x1                ; =1
10000b3d8: 97fff174    	bl	0x1000079a8 <_echoBinSafe>
10000b3dc: 97fffec8    	bl	0x10000aefc <_bench__add95carry_u844>
10000b3e0: a9417bfd    	ldp	x29, x30, [sp, #0x10]
10000b3e4: a8c24ff4    	ldp	x20, x19, [sp], #0x20
10000b3e8: 17fff4f4    	b	0x1000087b8 <_nimTestErrorFlag>

000000010000b3ec <_NimMainModule>:
10000b3ec: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
10000b3f0: a9017bfd    	stp	x29, x30, [sp, #0x10]
10000b3f4: 910043fd    	add	x29, sp, #0x10
10000b3f8: b0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000b3fc: 91012000    	add	x0, x0, #0x48
10000b400: f9400008    	ldr	x8, [x0]
10000b404: d63f0100    	blr	x8
10000b408: aa0003f3    	mov	x19, x0
10000b40c: 97fffc9d    	bl	0x10000a680 <_main__add95carry_u181>
10000b410: 39400268    	ldrb	w8, [x19]
10000b414: 350001a8    	cbnz	w8, 0x10000b448 <_NimMainModule+0x5c>
10000b418: 97fffdb9    	bl	0x10000aafc <_warmup__add95carry_u684>
10000b41c: 39400268    	ldrb	w8, [x19]
10000b420: 35000148    	cbnz	w8, 0x10000b448 <_NimMainModule+0x5c>
10000b424: b0000000    	adrp	x0, 0x10000c000 <_strlen+0x10000c000>
10000b428: 91078000    	add	x0, x0, #0x1e0
10000b42c: 52800021    	mov	w1, #0x1                ; =1
10000b430: 97fff15e    	bl	0x1000079a8 <_echoBinSafe>
10000b434: b0000000    	adrp	x0, 0x10000c000 <_strlen+0x10000c000>
10000b438: 9107c000    	add	x0, x0, #0x1f0
10000b43c: 52800021    	mov	w1, #0x1                ; =1
10000b440: 97fff15a    	bl	0x1000079a8 <_echoBinSafe>
10000b444: 97fffeae    	bl	0x10000aefc <_bench__add95carry_u844>
10000b448: a9417bfd    	ldp	x29, x30, [sp, #0x10]
10000b44c: a8c24ff4    	ldp	x20, x19, [sp], #0x20
10000b450: 17fff4da    	b	0x1000087b8 <_nimTestErrorFlag>

000000010000b454 <_NimMain>:
10000b454: a9be4ff4    	stp	x20, x19, [sp, #-0x20]!
10000b458: a9017bfd    	stp	x29, x30, [sp, #0x10]
10000b45c: 910043fd    	add	x29, sp, #0x10
10000b460: 97fff4f0    	bl	0x100008820 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatssystemdotnim_Init000>
10000b464: 97fff7a4    	bl	0x1000092f4 <_atmdotdotatsdotdotatsdotdotatsdotchoosenimatstoolchainsatsnimminus2dot2dot0atslibatspureatsrandomdotnim_Init000>
10000b468: b0000020    	adrp	x0, 0x100010000 <_allocator__system_u7104>
10000b46c: 91012000    	add	x0, x0, #0x48
10000b470: f9400008    	ldr	x8, [x0]
10000b474: d63f0100    	blr	x8
10000b478: aa0003f3    	mov	x19, x0
10000b47c: 97fffc81    	bl	0x10000a680 <_main__add95carry_u181>
10000b480: 39400268    	ldrb	w8, [x19]
10000b484: 350001a8    	cbnz	w8, 0x10000b4b8 <_NimMain+0x64>
10000b488: 97fffd9d    	bl	0x10000aafc <_warmup__add95carry_u684>
10000b48c: 39400268    	ldrb	w8, [x19]
10000b490: 35000148    	cbnz	w8, 0x10000b4b8 <_NimMain+0x64>
10000b494: b0000000    	adrp	x0, 0x10000c000 <_strlen+0x10000c000>
10000b498: 91078000    	add	x0, x0, #0x1e0
10000b49c: 52800021    	mov	w1, #0x1                ; =1
10000b4a0: 97fff142    	bl	0x1000079a8 <_echoBinSafe>
10000b4a4: b0000000    	adrp	x0, 0x10000c000 <_strlen+0x10000c000>
10000b4a8: 9107c000    	add	x0, x0, #0x1f0
10000b4ac: 52800021    	mov	w1, #0x1                ; =1
10000b4b0: 97fff13e    	bl	0x1000079a8 <_echoBinSafe>
10000b4b4: 97fffe92    	bl	0x10000aefc <_bench__add95carry_u844>
10000b4b8: a9417bfd    	ldp	x29, x30, [sp, #0x10]
10000b4bc: a8c24ff4    	ldp	x20, x19, [sp], #0x20
10000b4c0: 17fff4be    	b	0x1000087b8 <_nimTestErrorFlag>

000000010000b4c4 <_main>:
10000b4c4: a9bf7bfd    	stp	x29, x30, [sp, #-0x10]!
10000b4c8: 910003fd    	mov	x29, sp
10000b4cc: 90000048    	adrp	x8, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000b4d0: f9025901    	str	x1, [x8, #0x4b0]
10000b4d4: 90000048    	adrp	x8, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000b4d8: b904a900    	str	w0, [x8, #0x4a8]
10000b4dc: 90000048    	adrp	x8, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000b4e0: f9025d02    	str	x2, [x8, #0x4b8]
10000b4e4: 97ffffdc    	bl	0x10000b454 <_NimMain>
10000b4e8: 90000048    	adrp	x8, 0x100013000 <_allocator__system_u7104$tlv$init+0x2ef8>
10000b4ec: 91108108    	add	x8, x8, #0x420
10000b4f0: b9400100    	ldr	w0, [x8]
10000b4f4: a8c17bfd    	ldp	x29, x30, [sp], #0x10
10000b4f8: d65f03c0    	ret

Disassembly of section __TEXT,__stubs:

000000010000b4fc <__stubs>:
10000b4fc: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b500: f9400210    	ldr	x16, [x16]
10000b504: d61f0200    	br	x16
10000b508: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b50c: f9400610    	ldr	x16, [x16, #0x8]
10000b510: d61f0200    	br	x16
10000b514: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b518: f9401610    	ldr	x16, [x16, #0x28]
10000b51c: d61f0200    	br	x16
10000b520: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b524: f9401a10    	ldr	x16, [x16, #0x30]
10000b528: d61f0200    	br	x16
10000b52c: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b530: f9401e10    	ldr	x16, [x16, #0x38]
10000b534: d61f0200    	br	x16
10000b538: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b53c: f9402210    	ldr	x16, [x16, #0x40]
10000b540: d61f0200    	br	x16
10000b544: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b548: f9402610    	ldr	x16, [x16, #0x48]
10000b54c: d61f0200    	br	x16
10000b550: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b554: f9402a10    	ldr	x16, [x16, #0x50]
10000b558: d61f0200    	br	x16
10000b55c: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b560: f9402e10    	ldr	x16, [x16, #0x58]
10000b564: d61f0200    	br	x16
10000b568: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b56c: f9403210    	ldr	x16, [x16, #0x60]
10000b570: d61f0200    	br	x16
10000b574: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b578: f9403610    	ldr	x16, [x16, #0x68]
10000b57c: d61f0200    	br	x16
10000b580: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b584: f9403a10    	ldr	x16, [x16, #0x70]
10000b588: d61f0200    	br	x16
10000b58c: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b590: f9403e10    	ldr	x16, [x16, #0x78]
10000b594: d61f0200    	br	x16
10000b598: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b59c: f9404210    	ldr	x16, [x16, #0x80]
10000b5a0: d61f0200    	br	x16
10000b5a4: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b5a8: f9404610    	ldr	x16, [x16, #0x88]
10000b5ac: d61f0200    	br	x16
10000b5b0: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b5b4: f9404a10    	ldr	x16, [x16, #0x90]
10000b5b8: d61f0200    	br	x16
10000b5bc: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b5c0: f9404e10    	ldr	x16, [x16, #0x98]
10000b5c4: d61f0200    	br	x16
10000b5c8: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b5cc: f9405210    	ldr	x16, [x16, #0xa0]
10000b5d0: d61f0200    	br	x16
10000b5d4: b0000010    	adrp	x16, 0x10000c000 <_strlen+0x10000c000>
10000b5d8: f9405610    	ldr	x16, [x16, #0xa8]
10000b5dc: d61f0200    	br	x16
