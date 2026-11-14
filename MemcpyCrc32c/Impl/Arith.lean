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

/-- Unboxed `UInt32`-counted loop for `mulMod.go` (Clang `-O3` fully unrolls `n = 32`
into branchless register code with zero `Nat` boxing or stack spills). -/
def mulModU32 (n a b acc : UInt32) : UInt32 :=
  if _h : n = 0 then acc
  else
    mulModU32 (n - 1) (stepBit a) (b <<< 1)
      (if b &&& 0x80000000 = 0x80000000 then acc ^^^ a else acc)
termination_by n.toNat
decreasing_by
  have hn : n.toNat ≠ 0 := fun h0 => _h (by rw [← n.ofNat_toNat, h0]; rfl)
  have hle : 1#32 ≤ n.toBitVec := BitVec.le_def.mpr (by show 1 ≤ n.toNat; omega)
  have hsub : (n - 1).toNat = n.toNat - 1 := by
    show (n.toBitVec - 1#32).toNat = n.toNat - 1
    rw [BitVec.toNat_sub_of_le hle]; rfl
  omega

/-- Product modulo `G` of two reflected 32-bit polynomials. -/
@[inline] def mulMod (a b : UInt32) : UInt32 := mulModU32 32 a b 0

/-- Tail-recursive `acc * a ^ n` modulo `G` on an unboxed 64-bit exponent. -/
def powModU64 (a acc : UInt32) (n : UInt64) : UInt32 :=
  if _h : n = 0 then acc
  else powModU64 (mulMod a a) (if n &&& 1 = 1 then mulMod acc a else acc) (n >>> 1)
termination_by n.toNat
decreasing_by
  have hn : n.toNat ≠ 0 := fun h0 => _h (by rw [← n.ofNat_toNat, h0]; rfl)
  have hs : (n >>> 1).toNat = n.toNat / 2 := by
    rw [UInt64.toNat_shiftRight]; rfl
  omega

/-- Tail-recursive `acc * a ^ n` modulo `G` for arbitrary `Nat` exponents. -/
def powMod.go (a acc : UInt32) (n : @& Nat) : UInt32 :=
  if n = 0 then acc
  else powMod.go (mulMod a a) (if n % 2 = 1 then mulMod acc a else acc) (n / 2)
termination_by n
decreasing_by omega

/-- `a ^ n` modulo `G`, by square-and-multiply: O(log n) multiplications, using an
unboxed `UInt64` loop whenever `n < 2^64`. -/
@[inline] def powMod (a : UInt32) (n : @& Nat) : UInt32 :=
  if n ≤ 0xFFFFFFFFFFFFFFFF then powModU64 a 0x80000000 n.toUInt64
  else powMod.go a 0x80000000 n

/-- `X^8`, reflected. -/
@[inline] def x8 : UInt32 := 0x00800000

/-- `X^(-8)` modulo `G`, reflected. Checked by `stepByte_xInv8`. -/
@[inline] def xInv8 : UInt32 := 0xFDE39562

/-- Extend an unconditioned state over `n` zero bytes: multiply by `X^(8n)`. -/
@[inline] def extendZeroesRaw (s : UInt32) (n : @& Nat) : UInt32 := mulMod s (powMod x8 n)

/-- Inverse of `extendZeroesRaw`: multiply by `X^(-8n)`. -/
@[inline] def unextendZeroesRaw (s : UInt32) (n : @& Nat) : UInt32 := mulMod s (powMod xInv8 n)

/-- `absl::ExtendCrc32cByZeroes`. -/
def extendZeroes (c : UInt32) (n : @& Nat) : UInt32 :=
  extendZeroesRaw (c ^^^ 0xFFFFFFFF) n ^^^ 0xFFFFFFFF

/-- `absl::ConcatCrc32c`. -/
def concat (lhsCrc rhsCrc : UInt32) (rhsLen : @& Nat) : UInt32 :=
  extendZeroesRaw lhsCrc rhsLen ^^^ rhsCrc

/-- `absl::RemoveCrc32cPrefix`. -/
def removePrefix (crcA crcAB : UInt32) (lenB : @& Nat) : UInt32 := concat crcA crcAB lenB

/-- `absl::RemoveCrc32cSuffix`. -/
def removeSuffix (fullCrc suffixCrc : UInt32) (suffixLen : @& Nat) : UInt32 :=
  unextendZeroesRaw (fullCrc ^^^ suffixCrc) suffixLen

end Crc32c
