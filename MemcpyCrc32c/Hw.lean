/-
Links the hardware CRC32C and carry-less-multiply instruction models
(`lean-simd-models`) to this project's reference and residue ring `Q`:
- `CRC32C` across all four operand widths: 8-bit (`stepByte`), 16-bit (`stepU16`),
  32-bit (`stepU32`), and 64-bit (`stepWord`);
- 64-bit carry-less multiply (`clmulLo`, `clmulHi`) on zero-extended 32-bit
  residues (`polyR_clmulLo_toUInt64`) and 128-bit reflected accumulators
  (`R128_clmul`).

Kernel-only proofs.
-/
import MemcpyCrc32c.Portable
import SimdModels.Semantics
import SimdModels.Trusted

namespace Crc32c
open Polynomial

/-- The manuals' constant `0x1EDC6F41` and this project's term-by-term `G`
are the same polynomial. -/
theorem G_eq_castagnoli : G = SimdModels.castagnoli := by
  have h : (0x82F63B78#32 : BitVec 32) = (SimdModels.Model.crc32cPoly).reverse := by decide
  rw [G_eq, SimdModels.castagnoli, h, SimdModels.polyR_reverse]

theorem model_crc32c_u64_eq (c : UInt32) (w : UInt64) :
    SimdModels.Model.crc32c_u64 c w = stepWord c w := by
  apply P_injective
  show polyR (SimdModels.Model.crc32c 64 c.toBitVec w.toBitVec) = _
  rw [SimdModels.crc32c_spec, ← G_eq_castagnoli]
  apply modByMonic_eq_of_π_eq (degree_P_lt _)
  rw [π_P_stepWord]
  simp

theorem model_crc32c_u32_eq (c : UInt32) (v : UInt32) :
    SimdModels.Model.crc32c_u32 c v = stepU32 c v := by
  apply P_injective
  show polyR (SimdModels.Model.crc32c 32 c.toBitVec v.toBitVec) = _
  rw [SimdModels.crc32c_spec, ← G_eq_castagnoli]
  apply modByMonic_eq_of_π_eq (degree_P_lt _)
  rw [π_P_stepU32]
  simp

theorem model_crc32c_u16_eq (c : UInt32) (v : UInt16) :
    SimdModels.Model.crc32c_u16 c v = stepU16 c v := by
  apply P_injective
  show polyR (SimdModels.Model.crc32c 16 c.toBitVec v.toBitVec) = _
  rw [SimdModels.crc32c_spec, ← G_eq_castagnoli]
  apply modByMonic_eq_of_π_eq (degree_P_lt _)
  rw [π_P_stepU16]
  simp

theorem model_crc32c_u8_eq (c : UInt32) (b : UInt8) :
    SimdModels.Model.crc32c_u8 c b = stepByte c b := by
  apply P_injective
  show polyR (SimdModels.Model.crc32c 8 c.toBitVec b.toBitVec) = _
  rw [SimdModels.crc32c_spec, ← G_eq_castagnoli]
  apply modByMonic_eq_of_π_eq (degree_P_lt _)
  rw [π_P_stepByte]
  simp

/-- The trusted 64-bit CRC32C instruction binding absorbs one little-endian 64-bit word. -/
theorem crc32c_u64_eq (c : UInt32) (w : UInt64) : SimdModels.crc32c_u64 c w = stepWord c w :=
  model_crc32c_u64_eq c w

/-- The trusted 32-bit CRC32C instruction binding absorbs one little-endian 32-bit word. -/
theorem crc32c_u32_eq (c : UInt32) (v : UInt32) : SimdModels.crc32c_u32 c v = stepU32 c v :=
  model_crc32c_u32_eq c v

/-- The trusted 16-bit CRC32C instruction binding absorbs one little-endian 16-bit halfword. -/
theorem crc32c_u16_eq (c : UInt32) (v : UInt16) : SimdModels.crc32c_u16 c v = stepU16 c v :=
  model_crc32c_u16_eq c v

/-- The trusted 8-bit CRC32C instruction binding absorbs one byte. -/
theorem crc32c_u8_eq (c : UInt32) (b : UInt8) : SimdModels.crc32c_u8 c b = stepByte c b :=
  model_crc32c_u8_eq c b

/-- The trusted byte load binding is definitionally equal to `ByteArray.uget`. -/
@[simp] theorem loadU8_eq_uget (a : ByteArray) (i : USize) (h : i.toNat < a.size) :
    SimdModels.loadU8 a i h = a.uget i h := rfl

/-- The trusted unaligned little-endian 64-bit load binding is definitionally
equal to `load64`. -/
@[simp] theorem loadU64LE_eq_load64 (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) : SimdModels.loadU64LE a i hs h = load64 a i hs h := rfl

theorem clmulLo_eq_model (x y : UInt64) :
    SimdModels.clmulLo x y = SimdModels.Model.clmulLo x y := rfl

theorem clmulHi_eq_model (x y : UInt64) :
    SimdModels.clmulHi x y = SimdModels.Model.clmulHi x y := rfl

/-! ### Carry-less multiply bridge lemmas -/

theorem polyN_toUInt64 (u : UInt32) :
    polyN u.toUInt64.toBitVec = polyN u.toBitVec := by
  have h : u.toUInt64.toBitVec = u.toBitVec.setWidth 64 := by simp
  ext k
  rw [h, SimdModels.coeff_polyN', SimdModels.coeff_polyN', BitVec.getLsbD_setWidth]
  by_cases hk : k < 64
  · simp [hk]
  · simp [hk, BitVec.getLsbD_of_ge u.toBitVec k (by omega)]

/-- Carry-less product of two zero-extended 32-bit words has degree `≤ 62`, so
its high 64-bit half is identically zero. -/
theorem clmulHi_toUInt64_eq_zero (a b : UInt32) :
    SimdModels.clmulHi a.toUInt64 b.toUInt64 = 0 := by
  rw [clmulHi_eq_model]
  have hspec := SimdModels.clmul_spec a.toUInt64 b.toUInt64
  rw [polyN_toUInt64, polyN_toUInt64] at hspec
  have ha := SimdModels.natDegree_polyN_le a.toBitVec
  have hb := SimdModels.natDegree_polyN_le b.toBitVec
  have hdeg : (polyN a.toBitVec * polyN b.toBitVec).natDegree ≤ 62 :=
    le_trans Polynomial.natDegree_mul_le (by omega)
  have hlo := SimdModels.natDegree_polyN_le (SimdModels.Model.clmulLo a.toUInt64 b.toUInt64).toBitVec
  have hzero : polyN (SimdModels.Model.clmulHi a.toUInt64 b.toUInt64).toBitVec =
      polyN (0 : BitVec 64) := by
    rw [SimdModels.polyN_zero]
    ext i
    have hc := congrArg (fun p => p.coeff (i + 64)) hspec
    rw [coeff_add, coeff_mul_X_pow',
      coeff_eq_zero_of_natDegree_lt (by omega : (polyN (SimdModels.Model.clmulLo a.toUInt64 b.toUInt64).toBitVec).natDegree < i + 64),
      coeff_eq_zero_of_natDegree_lt (by omega : (polyN a.toBitVec * polyN b.toBitVec).natDegree < i + 64),
      zero_add] at hc
    simpa [coeff_zero] using hc
  exact UInt64.toBitVec_inj.mp (SimdModels.polyN_injective hzero)

/-- Reflected view of the low 64-bit carry-less product of two zero-extended
32-bit words: `X * P a * P b`. -/
theorem polyR_clmulLo_toUInt64 (a b : UInt32) :
    polyR (SimdModels.clmulLo a.toUInt64 b.toUInt64).toBitVec = X * P a * P b := by
  have h := SimdModels.clmul_spec_reflected a.toUInt64 b.toUInt64
  rw [← clmulLo_eq_model, ← clmulHi_eq_model, clmulHi_toUInt64_eq_zero,
    show polyR (0 : UInt64).toBitVec = 0 from polyR_zero,
    add_zero, polyR_toUInt64, polyR_toUInt64] at h
  have h' : polyR (SimdModels.clmulLo a.toUInt64 b.toUInt64).toBitVec * X ^ 64 =
      (X * P a * P b) * X ^ 64 := by
    linear_combination h
  ext k
  have hc := congrArg (fun p => p.coeff (k + 64)) h'
  simpa [coeff_mul_X_pow'] using hc

/-- Residue of a 16-byte (128-bit) little-endian block `(lo, hi)` in `Q`. -/
noncomputable def R128 (lo hi : UInt64) : Q :=
  R lo * π X ^ 64 + R hi

theorem R128_xor (a0 a1 b0 b1 : UInt64) :
    R128 (a0 ^^^ b0) (a1 ^^^ b1) = R128 a0 a1 + R128 b0 b1 := by
  unfold R128
  rw [R_xor, R_xor]
  ring

/-- Reflected residue of a full 64×64→128 carry-less multiply (`clmulLo`, `clmulHi`). -/
theorem R128_clmul (x k : UInt64) :
    R128 (SimdModels.clmulLo x k) (SimdModels.clmulHi x k) = R x * (π X * R k) := by
  have h0 := SimdModels.clmul_spec_reflected x k
  rw [← clmulLo_eq_model, ← clmulHi_eq_model] at h0
  have h := congrArg π h0
  simp only [map_add, map_mul, map_pow] at h
  unfold R128 R
  linear_combination h

end Crc32c
