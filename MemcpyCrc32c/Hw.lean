/-
Links the hardware CRC32C instruction models (`lean-simd-models`) to this
project's reference: the instruction on a 64-bit operand is `stepWord`, and on
an 8-bit operand is `stepByte`. Kernel-only proofs.
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

theorem model_crc32c_u8_eq (c : UInt32) (b : UInt8) :
    SimdModels.Model.crc32c_u8 c b = stepByte c b := by
  apply P_injective
  show polyR (SimdModels.Model.crc32c 8 c.toBitVec b.toBitVec) = _
  rw [SimdModels.crc32c_spec, ← G_eq_castagnoli]
  apply modByMonic_eq_of_π_eq (degree_P_lt _)
  rw [π_P_stepByte]
  simp

/-- The trusted 64-bit CRC32C instruction binding absorbs one little-endian word. -/
theorem crc32c_u64_eq (c : UInt32) (w : UInt64) : SimdModels.crc32c_u64 c w = stepWord c w :=
  model_crc32c_u64_eq c w

/-- The trusted 8-bit CRC32C instruction binding absorbs one byte. -/
theorem crc32c_u8_eq (c : UInt32) (b : UInt8) : SimdModels.crc32c_u8 c b = stepByte c b :=
  model_crc32c_u8_eq c b

end Crc32c
