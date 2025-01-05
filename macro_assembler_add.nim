import
  macros,
  ./macro_assembler_arm64

# #############################################

type
  Word = uint64
  Carry = uint8
  Limbs[N: static int] = array[N, Word]

func wordsRequired(bits: int): int {.compileTime.} =
  ## Compute the number of limbs required
  ## from the announced bit length
  (bits + 64 - 1) div 64

type
  BigInt[bits: static int] {.byref.} = object
    ## BigInt
    ## Enforce-passing by reference otherwise uint128 are passed by stack
    ## which causes issue with the inline assembly
    limbs: array[bits.wordsRequired, Word]

macro add_gen[N: static int](carry: var Carry, r_PIR: var Limbs[N], a_PIR, b_PIR: Limbs[N]): untyped =
  ## Generate a multiprecision addition
  result = newStmtList()

  var ctx = init(Assembler_arm64, Word)
  let
    # MemOffsettable is the better constraint but
    # with ARM64 we cannot generate array offsets from it due to inline ASM auto-bracketings
    r = asmArray(r_PIR, N, PointerInReg, asmInputOutputEarlyClobber, memIndirect = memWrite)
    a = asmArray(a_PIR, N, PointerInReg, asmInput, memIndirect = memRead)
    b = asmArray(b_PIR, N, PointerInReg, asmInput, memIndirect = memRead)

    u0Sym = ident"u0"
    u1Sym = ident"u1"
    v0Sym = ident"v0"
    v1Sym = ident"v1"

  var # Swappable registers to break dependency chains
    u0 = asmValue(u0Sym, Reg, asmOutputEarlyClobber)
    u1 = asmValue(u1Sym, Reg, asmOutputEarlyClobber)
    v0 = asmValue(v0Sym, Reg, asmOutputEarlyClobber)
    v1 = asmValue(v1Sym, Reg, asmOutputEarlyClobber)

  # Prologue
  result.add quote do:
    var `u0sym`{.noinit.}, `u1sym`{.noinit.}: Word
    var `v0sym`{.noinit.}, `v1sym`{.noinit.}: Word

  # Algorithm
  doAssert N >= 2
  ctx.ldp u0, u1, a[0]
  ctx.ldp v0, v1, b[0]

  for i in 0 ..< N:
    if i == 0:
      ctx.adds u0, u0, v0
    elif i == N-1:
      ctx.adc u0, u0, v0
    else:
      ctx.adcs u0, u0, v0
    ctx.str u0, r[i]

    # Next iteration
    if i != N-1:
      swap(u0, u1)
      swap(v0, v1)
      ctx.ldr u1, a[i+1]
      ctx.ldr v1, b[i+1]

  ctx.setToCarryFlag(carry)

  # Codegen
  result.add ctx.generate()

func add_asm*(r: var Limbs, a, b: Limbs): Carry =
  add_gen(result, r, a, b)

func `+=`(a: var BigInt, b: BigInt) {.inline.}=
  discard a.limbs.add_asm(a.limbs, b.limbs)


# #############################################
import random

randomize(1234)

proc rand(T: typedesc[BigInt]): T =
  for i in 0 ..< result.limbs.len:
    result.limbs[i] = uint64(rand(high(int)))

proc main() =
  block:
    let a = BigInt[128](limbs: [high(uint64), 0])
    let b = BigInt[128](limbs: [1'u64, 0])

    echo "a:        ", a
    echo "b:        ", b
    echo "------------------------------------------------------"

    var a1 = a
    a1 += b
    echo a1
    echo "======================================================"

  block:
    let a = rand(BigInt[256])
    let b = rand(BigInt[256])

    echo "a:        ", a
    echo "b:        ", b
    echo "------------------------------------------------------"

    var a1 = a
    a1 += b
    echo a1
    echo "======================================================"

  block:
    let a = rand(BigInt[384])
    let b = rand(BigInt[384])

    echo "a:        ", a
    echo "b:        ", b
    echo "------------------------------------------------------"

    var a1 = a
    a1 += b
    echo a1

main()
