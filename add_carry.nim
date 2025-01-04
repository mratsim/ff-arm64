func wordsRequired(bits: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (bits + 64 - 1) div 64

type
  # Note: a custom bycopy type for limbs is probably
  #       useful for optimization in particular for aliasing.
  BigInt[bits: static int] = object
    limbs: array[bits.wordsRequired, uint64]

  Carry = uint64

  uint128 {.importc: "unsigned __int128".} = object

  CarryFlag = enum
    cfFalse
    cfTrue

# #######################################################

func builtin_addcll(x, y: uint64, carryIn: uint64, carryOut: var uint64): uint64 {.importc: "__builtin_addcll", nodecl.}

func addcarry_via128(sum: var uint64, carryOut: var CarryFlag, carryIn: CarryFlag, a, b: uint64) =
  var tmp {.noinit.}: uint128
  {.emit: [tmp, " = (unsigned __int128)", carryIn, " + (unsigned __int128)",a," + (unsigned __int128)",b,";"].}
  {.emit: [sum, " = (NU64)(", tmp, "& (NU64)0xffffffffffffffff);"].}
  {.emit: [carryOut, " = (",CarryFlag,")((", tmp, ">> 64) & 1);"].}

# #######################################################

func add_intrinsics(a: var BigInt, b: BigInt) {.noinline.}=
  var carry: Carry
  for i in 0 ..< a.limbs.len:
    a.limbs[i] = builtin_addcll(a.limbs[i], b.limbs[i], carry, carry)

func `+=`(a: var BigInt, b: BigInt) {.noinline.}=
  # no-inline needed otherwise the compiler multiplies
  # by the number of iterations in the benchmark
  var carry: bool
  for i in 0 ..< a.limbs.len:
    a.limbs[i] += b.limbs[i] + uint64(carry)
    carry = a.limbs[i] < b.limbs[i]

func add_via_u128(a: var BigInt, b: BigInt) {.noinline.}=
  var tmp {.noinit.}: uint128
  {.emit:[tmp, " = (unsigned __int128)0;"].}
  for i in 0 ..< a.limbs.len:
    {.emit:[tmp, " += (unsigned __int128)", a.limbs[i], " + (unsigned __int128)", b.limbs[i], ";"].}
    {.emit:[a.limbs[i], " = (NU64)", tmp, ";"].}
    {.emit:[tmp, " >>= 64;"].}

func add_via_addcarry128(a: var BigInt, b: BigInt) {.noinline.}=
  var carry: CarryFlag
  for i in 0 ..< a.limbs.len:
    addcarry_via128(a.limbs[i], carry, carry, a.limbs[i], b.limbs[i])

func add256_pure(a: var BigInt[256], b: BigInt[256]) {.noinline.}=
  a.limbs[0] += b.limbs[0]
  a.limbs[1] += b.limbs[1] + uint64(a.limbs[0] < b.limbs[0])
  a.limbs[2] += b.limbs[2] + uint64(a.limbs[1] < b.limbs[1])
  a.limbs[3] += b.limbs[3] + uint64(a.limbs[2] < b.limbs[2])

func add256_pure2(a: var BigInt[256], b: BigInt[256]) {.noinline.}=
  a.limbs[0] += b.limbs[0]
  a.limbs[1] += uint64(a.limbs[0] < b.limbs[0])
  a.limbs[1] += b.limbs[1]
  a.limbs[2] += uint64(a.limbs[1] < b.limbs[1])
  a.limbs[2] += b.limbs[2]
  a.limbs[3] += uint64(a.limbs[2] < b.limbs[2])
  a.limbs[3] += b.limbs[3]

func add256_asm(a: var BigInt[256], b: BigInt[256]) {.noinline.}=
  var a0, a1: uint64
  var b0: uint64

  # If we use a memory operand we cannot use array access syntax on arm64
  # as the 'm' modifier which avoids brackets is unavailable:
  # https://developer.arm.com/documentation/101754/0616/armclang-Reference/armclang-Inline-Assembler/Inline-assembly-constraint-strings/Constraint-codes-common-to-AArch32-state-and-AArch64-state?lang=en
  # so we need to store the address directly in register

  asm """
    ldp %[a0], %[a1], [%[a]]
    ldr %[b0], [%[b]]
    adds %[a0], %[b0], %[a0]
    str %[a0], [%[a]]

    ldr     %[b0], [%[b], #8]
    adcs    %[b0], %[a1], %[b0]
    ldp     %[a0], %[a1], [%[a], #16]
    str     %[b0], [%[a], #8]

    ldr     %[b0], [%[b], #16]
    adcs    %[b0], %[a0], %[b0]
    str     %[b0], [%[a], #16]
    
    ldr     %[b0], [%[b], #24]
    adc     %[b0], %[a1], %[b0]
    str     %[b0], [%[a], #24]

    : [a0] "=&r" (`a0`), [a1] "=&r" (`a1`), [b0] "=&r" (`b0`), [a_mem] "+m" (`a_p0->limbs[0]`)
    : [a] "r" (`&a_p0->limbs[0]`), [b] "r"(`&b_p1->limbs[0]`), [b_mem] "m" (`b_p1->limbs[0]`)
    : "cc"
  """


# ######################################################
import random, times, std/monotimes, strformat
import ./timers

proc rand(T: typedesc[BigInt]): T =
  for i in 0 ..< result.limbs.len:
    result.limbs[i] = uint64(rand(high(int)))

proc main() =
  let a = rand(BigInt[256])
  let b = rand(BigInt[256])

  echo "a:        ", a
  echo "b:        ", b
  echo "------------------------------------------------------"

  var a1 = a
  a1 += b
  echo "pure: ", a1

  var a2 = a
  a2.add256_asm(b)
  echo "assembly: ",a2

  var a3 = a
  a3.add_intrinsics(b)
  echo "intrinsics: ",a3

  var a4 = a
  a4.add_via_u128(b)
  echo "via u128: ",a4

  var a5 = a
  a5.add256_pure(b)
  echo "unrolled pure Nim: ",a5

  var a6 = a
  a6.add256_pure2(b)
  echo "unrolled pure Nim v2: ",a6

  var a7 = a
  a7.add_via_addcarry128(b)
  echo "addcarry128: ",a7

main()

# warmup
proc warmup*() =
  # Warmup - make sure cpu is on max perf
  let start = cpuTime()
  var foo = 123
  for i in 0 ..< 300_000_000:
    foo += i*i mod 456
    foo = foo mod 789

  # Compiler shouldn't optimize away the results as cpuTime rely on sideeffects
  let stop = cpuTime()
  echo &"Warmup: {stop - start:>4.4f} s, result {foo} (displayed to avoid compiler optimizing warmup away)"

warmup()


echo "\n⚠️ Measurements are approximate and use the CPU nominal clock: Turbo-Boost and overclocking will skew them."
echo "==========================================================================================================\n"

proc report(op, impl: string, start, stop: MonoTime, startClk, stopClk: int64, iters: int) =
  echo &"{op:<15} {impl:<25} {inNanoseconds((stop-start) div iters):>9} ns {(stopClk - startClk) div iters:>9} ticks"


proc bench() =
  const Iters = 1_000_000

  let a = rand(BigInt[256])
  let b = rand(BigInt[256])

  block:
    var a1 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a1 += b
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Pure Nim", start, stop, startClk, stopClk, Iters)

  block:
    var a2 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a2.add256_asm(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Assembly", start, stop, startClk, stopClk, Iters)

  block:
    var a3 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a3.add_intrinsics(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Intrinsics", start, stop, startClk, stopClk, Iters)

  block:
    var a4 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a4.add_via_u128(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "via uint128", start, stop, startClk, stopClk, Iters)

  block:
    var a5 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a5.add256_pure(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "unrolled", start, stop, startClk, stopClk, Iters)

  block:
    var a6 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a6.add256_pure2(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "unrolled v2", start, stop, startClk, stopClk, Iters)

  block:
    var a7 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a7.add_via_addcarry128(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "add_via_addcarry128", start, stop, startClk, stopClk, Iters)

bench()
