/-
Hardware differential test: every trusted binding against its Lean model, on
edge cases and random inputs. Usage: hw_diff [random-cases-per-binding] [seed]
Exits non-zero on the first mismatch.
-/
import SimdModels.Trusted

open SimdModels

def next (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13); let x := x ^^^ (x >>> 7); x ^^^ (x <<< 17)

/-- Edge values: all-zero, all-one, single bits, runs, alternating patterns. -/
def edges64 : Array UInt64 := Id.run do
  let mut a : Array UInt64 := #[0, 0xFFFFFFFFFFFFFFFF, 0xAAAAAAAAAAAAAAAA, 0x5555555555555555,
    0x00000000FFFFFFFF, 0xFFFFFFFF00000000, 0x0123456789ABCDEF, 0x8000000000000001]
  for i in [0:64] do
    a := a.push ((1 : UInt64) <<< i.toUInt64)
    a := a.push (~~~((1 : UInt64) <<< i.toUInt64))
    a := a.push (((1 : UInt64) <<< i.toUInt64) - 1)
  return a

def fail (name : String) (x y : UInt64) (got want : UInt64) : IO Unit := do
  IO.eprintln s!"MISMATCH {name}: inputs {x} {y}: hardware {got}, model {want}"
  IO.Process.exit 1

def packBuf24 (x y z : UInt64) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 24
  for k in [0:8] do b := b.push (x >>> (k * 8).toUInt64).toUInt8
  for k in [0:8] do b := b.push (y >>> (k * 8).toUInt64).toUInt8
  for k in [0:8] do b := b.push (z >>> (k * 8).toUInt64).toUInt8
  return b

def check (x y : UInt64) : IO Unit := do
  let c := x.toUInt32
  if crc32c_u8 c y.toUInt8 != Model.crc32c_u8 c y.toUInt8 then
    fail "crc32c_u8" x y (crc32c_u8 c y.toUInt8).toUInt64 (Model.crc32c_u8 c y.toUInt8).toUInt64
  if crc32c_u16 c y.toUInt16 != Model.crc32c_u16 c y.toUInt16 then
    fail "crc32c_u16" x y (crc32c_u16 c y.toUInt16).toUInt64 (Model.crc32c_u16 c y.toUInt16).toUInt64
  if crc32c_u32 c y.toUInt32 != Model.crc32c_u32 c y.toUInt32 then
    fail "crc32c_u32" x y (crc32c_u32 c y.toUInt32).toUInt64 (Model.crc32c_u32 c y.toUInt32).toUInt64
  if crc32c_u64 c y != Model.crc32c_u64 c y then
    fail "crc32c_u64" x y (crc32c_u64 c y).toUInt64 (Model.crc32c_u64 c y).toUInt64
  if clmulLo x y != Model.clmulLo x y then fail "clmulLo" x y (clmulLo x y) (Model.clmulLo x y)
  if clmulHi x y != Model.clmulHi x y then fail "clmulHi" x y (clmulHi x y) (Model.clmulHi x y)
  let buf := packBuf24 x y (next (x ^^^ y))
  let off : Nat := (x ^^^ (y >>> 17)).toNat % 17
  if h : buf.size = 24 ∧ off ≤ 16 then
    have hs : buf.size < USize.size := by have := Model.usize_size_gt; omega
    have hu : off.toUSize.toNat = off := by
      have := Model.usize_size_gt; exact USize.toNat_ofNat_of_lt' (by omega)
    have hb : off.toUSize.toNat + 8 ≤ buf.size := by omega
    let got := loadU64LE buf off.toUSize hs hb
    let want := Model.loadU64LE buf off.toUSize hs hb
    if got != want then fail "loadU64LE" x y got want

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 1000000
  let seed := (args[1]? >>= String.toNat?).getD 1
  let es := edges64
  for x in es do
    for y in es do
      check x y
  let mut s : UInt64 := 0x9E3779B97F4A7C15 ^^^ seed.toUInt64
  for _ in [0:n] do
    s := next s; let x := s
    s := next s; let y := s
    check x y
  IO.println s!"OK: 7 bindings agree with their models on {es.size * es.size} edge pairs and {n} random pairs each (seed {seed})"
