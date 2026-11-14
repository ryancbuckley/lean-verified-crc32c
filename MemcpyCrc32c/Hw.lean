/-
Links the hardware CRC32C instruction models (`lean-simd-models`) to this
project's reference across all four operand widths: 8-bit (`stepByte`), 16-bit
(`stepU16`), 32-bit (`stepU32`), and 64-bit (`stepWord`). Kernel-only proofs.
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

end Crc32c
