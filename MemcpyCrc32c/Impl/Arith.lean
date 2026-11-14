/-
CRC arithmetic with abseil's semantics: `ExtendCrc32cByZeroes`, `ConcatCrc32c`,
`RemoveCrc32cPrefix`, `RemoveCrc32cSuffix`. Core-only executable definitions;
the proofs against the spec are in `MemcpyCrc32c.Arith`.

abseil implements these with tables of `X^(2^k)` powers; here the same
multiplications modulo `G` are done by square-and-multiply, which is
O(log n) word operations. Table-driven variants for the hot path come later
and will be proven equal to these.
-/
import MemcpyCrc32c.Impl.Reference

namespace Crc32c

/-! ### Multiplication and powers modulo `G` on reflected 32-bit words -/

/-- `acc + a * b` modulo `G`, consuming `n` coefficients of `b` from `X^0` up. -/
def mulMod.go : Nat → UInt32 → UInt32 → UInt32 → UInt32
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
    mulMod.go n (stepBit a) (b <<< 1) (if b &&& 0x80000000 = 0x80000000 then acc ^^^ a else acc)

/-- Product modulo `G` of two reflected 32-bit polynomials. -/
def mulMod (a b : UInt32) : UInt32 := mulMod.go 32 a b 0

/-- `a ^ n` modulo `G`, by square-and-multiply: O(log n) multiplications. -/
def powMod (a : UInt32) (n : Nat) : UInt32 :=
  if n = 0 then 0x80000000
  else
    let h := powMod a (n / 2)
    let sq := mulMod h h
    if n % 2 = 1 then mulMod sq a else sq
termination_by n
decreasing_by omega

/-- `X^8`, reflected. -/
def x8 : UInt32 := 0x00800000

/-- `X^(-8)` modulo `G`, reflected. Checked by `stepByte_xInv8`. -/
def xInv8 : UInt32 := 0xFDE39562

/-- Extend an unconditioned state over `n` zero bytes: multiply by `X^(8n)`. -/
def extendZeroesRaw (s : UInt32) (n : Nat) : UInt32 := mulMod s (powMod x8 n)

/-- Inverse of `extendZeroesRaw`: multiply by `X^(-8n)`. -/
def unextendZeroesRaw (s : UInt32) (n : Nat) : UInt32 := mulMod s (powMod xInv8 n)

/-- `absl::ExtendCrc32cByZeroes`. -/
def extendZeroes (c : UInt32) (n : Nat) : UInt32 :=
  extendZeroesRaw (c ^^^ 0xFFFFFFFF) n ^^^ 0xFFFFFFFF

/-- `absl::ConcatCrc32c`. -/
def concat (lhsCrc rhsCrc : UInt32) (rhsLen : Nat) : UInt32 :=
  extendZeroesRaw lhsCrc rhsLen ^^^ rhsCrc

/-- `absl::RemoveCrc32cPrefix`. -/
def removePrefix (crcA crcAB : UInt32) (lenB : Nat) : UInt32 := concat crcA crcAB lenB

/-- `absl::RemoveCrc32cSuffix`. -/
def removeSuffix (fullCrc suffixCrc : UInt32) (suffixLen : Nat) : UInt32 :=
  unextendZeroesRaw (fullCrc ^^^ suffixCrc) suffixLen

end Crc32c
