/-
Axiom audit for the headline theorems. Every theorem audited here is checked at
build time to depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), with zero `bv_decide` or `native_decide`
axioms.
-/
import MemcpyCrc32c.Vectors
import MemcpyCrc32c.PolyAlgebra
import MemcpyCrc32c.ZeroPolyMinimal
import MemcpyCrc32c.Portable
import MemcpyCrc32c.CApi
import MemcpyCrc32c.ErrorDetection
import SimdModels

open Crc32c

/-- info: 'Crc32c.extend_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extend_eq_spec
/-- info: 'Crc32c.crc32c_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32c_eq_spec
/-- info: 'Crc32c.extend_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extend_append
/-- info: 'Crc32c.concat_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_spec
/-- info: 'Crc32c.removePrefix_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms removePrefix_spec
/-- info: 'Crc32c.removeSuffix_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms removeSuffix_spec
/-- info: 'Crc32c.extendZeroes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendZeroes_spec
/-- info: 'Crc32c.Spec.extend_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_append
/-- info: 'Crc32c.Spec.concat_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.concat_spec
/-- info: 'Crc32c.Spec.removePrefix_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.removePrefix_spec
/-- info: 'Crc32c.Spec.removeSuffix_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.removeSuffix_spec
/-- info: 'Crc32c.Spec.extendZeroes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extendZeroes_spec
/-- info: 'Crc32c.check_123456789' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_123456789
/-- info: 'Crc32c.rfc3720_iscsi_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rfc3720_iscsi_read
/-- info: 'Crc32c.zeroes_u64max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms zeroes_u64max
/-- info: 'Crc32c.modByMonic_add_zeroPoly_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms modByMonic_add_zeroPoly_mul

-- Generator structure, Frobenius invariance, and certified zero polynomials.
/-- info: 'Crc32c.even_card_support_of_dvd_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms even_card_support_of_dvd_G
/-- info: 'Crc32c.G_eq_mul_P31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G_eq_mul_P31
/-- info: 'Crc32c.irreducible_X_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms irreducible_X_add_one
/-- info: 'Crc32c.irreducible_P31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms irreducible_P31
/-- info: 'Crc32c.orderOf_root_P31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orderOf_root_P31
/-- info: 'Crc32c.squarefree_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squarefree_G
/-- info: 'Crc32c.orderOf_π_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orderOf_π_X
/-- info: 'Crc32c.dvd_X_pow_add_X_pow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dvd_X_pow_add_X_pow_iff
/-- info: 'Crc32c.dvd_expand_two_pow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dvd_expand_two_pow_iff
/-- info: 'Crc32c.zero2_mersenne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero2_mersenne
/-- info: 'Crc32c.zero2_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero2_minimal
/-- info: 'Crc32c.zero2_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero2_unique
/-- info: 'Crc32c.zero4_5275' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero4_5275
/-- info: 'Crc32c.zero4_5275_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero4_5275_minimal
/-- info: 'Crc32c.zero4_5275_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero4_5275_unique
/-- info: 'Crc32c.zero6_209' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_209
/-- info: 'Crc32c.zero6_209_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_209_minimal
/-- info: 'Crc32c.zero6_209_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_209_unique
/-- info: 'Crc32c.zero6_word64_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_word64_minimal
/-- info: 'Crc32c.zero6_word64_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_word64_unique
/-- info: 'Crc32c.zero6_290' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_290
/-- info: 'Crc32c.zero6_290_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_290_minimal
/-- info: 'Crc32c.zero6_290_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero6_290_unique
/-- info: 'Crc32c.zero8_79' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero8_79
/-- info: 'Crc32c.zero8_79_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero8_79_minimal
/-- info: 'Crc32c.zero8_79_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero8_79_unique

-- Error-detection & Castagnoli / Koopman Hamming-distance bounds.
/-- info: 'Crc32c.dvd_codewordError_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dvd_codewordError_iff
/-- info: 'Crc32c.Spec.extend_eq_iff_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_eq_iff_dvd
/-- info: 'Crc32c.Spec.extend_detects_odd_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_detects_odd_errors
/-- info: 'Crc32c.Spec.extend_detects_burst32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_detects_burst32
/-- info: 'Crc32c.Spec.extend_ne_of_burst4Bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_ne_of_burst4Bytes
/-- info: 'Crc32c.Spec.extend_hd4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_hd4
/-- info: 'Crc32c.Spec.extend_hd6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_hd6
/-- info: 'Crc32c.Spec.extend_hd8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_hd8
/-- info: 'Crc32c.Spec.extend_hd10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_hd10
/-- info: 'Crc32c.Spec.extend_payload_hd4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_payload_hd4
/-- info: 'Crc32c.Spec.extend_payload_hd6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_payload_hd6
/-- info: 'Crc32c.Spec.extend_payload_hd8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_payload_hd8
/-- info: 'Crc32c.Spec.extend_payload_hd10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.extend_payload_hd10
/-- info: 'Crc32c.computeCrc32c_detects_odd_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms computeCrc32c_detects_odd_errors
/-- info: 'Crc32c.computeCrc32c_hd4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms computeCrc32c_hd4
/-- info: 'Crc32c.computeCrc32c_hd6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms computeCrc32c_hd6
/-- info: 'Crc32c.computeCrc32c_hd8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms computeCrc32c_hd8
/-- info: 'Crc32c.computeCrc32c_hd10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms computeCrc32c_hd10
/-- info: 'Crc32c.memcpyCrc32c_sector_hd6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memcpyCrc32c_sector_hd6

-- Phase 2: pure kernel proofs as well (no `bv_decide` axioms).
/-- info: 'Crc32c.rawExtendPortable_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExtendPortable_eq
/-- info: 'Crc32c.extendPortable_eq_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendPortable_eq_extend
/-- info: 'Crc32c.extendPortable_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendPortable_eq_spec

-- Phase 3: instruction-model semantics, V128 views, Intel SDM equivalence, and link to reference.
/-- info: 'SimdModels.crc32c_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.crc32c_spec
/-- info: 'SimdModels.clmul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.clmul_spec
/-- info: 'SimdModels.clmul_spec_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.clmul_spec_reflected
/-- info: 'SimdModels.V128.ofHalves_lo_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.V128.ofHalves_lo_hi
/-- info: 'SimdModels.V128.lane8_vextq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.V128.lane8_vextq
/-- info: 'SimdModels.V128.lane8_vld1q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.V128.lane8_vld1q
/-- info: 'SimdModels.clmulepi64_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.clmulepi64_spec
/-- info: 'SimdModels.clmulepi64_spec_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.clmulepi64_spec_reflected
/-- info: 'SimdModels.IntelSdm.crc32_u8_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.IntelSdm.crc32_u8_eq
/-- info: 'SimdModels.IntelSdm.crc32_u16_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.IntelSdm.crc32_u16_eq
/-- info: 'SimdModels.IntelSdm.crc32_u32_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.IntelSdm.crc32_u32_eq
/-- info: 'SimdModels.IntelSdm.crc32_u64_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.IntelSdm.crc32_u64_eq
/-- info: 'SimdModels.IntelSdm.crc32_r64_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.IntelSdm.crc32_r64_eq
/-- info: 'SimdModels.IntelSdm.clmulepi64_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SimdModels.IntelSdm.clmulepi64_eq
/-- info: 'Crc32c.G_eq_castagnoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G_eq_castagnoli
/-- info: 'Crc32c.crc32c_u64_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32c_u64_eq
/-- info: 'Crc32c.crc32c_u32_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32c_u32_eq
/-- info: 'Crc32c.crc32c_u16_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32c_u16_eq
/-- info: 'Crc32c.crc32c_u8_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crc32c_u8_eq
/-- info: 'Crc32c.loadU8_eq_uget' does not depend on any axioms -/
#guard_msgs in #print axioms loadU8_eq_uget
/-- info: 'Crc32c.loadU64LE_eq_load64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms loadU64LE_eq_load64
/-- info: 'Crc32c.polyR_clmulLo_toUInt64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms polyR_clmulLo_toUInt64
/-- info: 'Crc32c.R128_clmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R128_clmul

-- Phase 4 (AArch64 / x86-64 hybrid hardware-CRC + CLMUL kernel). Rests on the
-- trusted bindings in `SimdModels.Trusted`, which `#print axioms` cannot show.
/-- info: 'Crc32c.π_P_hwMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms π_P_hwMul
/-- info: 'Crc32c.hwFold3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwFold3_spec
/-- info: 'Crc32c.hwFold6_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwFold6_eq
/-- info: 'Crc32c.rawExtendHw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExtendHw_eq
/-- info: 'Crc32c.extendHw_eq_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendHw_eq_extend
/-- info: 'Crc32c.extendHw_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendHw_eq_spec

-- Phase 5: theorem 6 (`memcpyCrc32c_spec`) for each path.
/-- info: 'Crc32c.memcpyCrc32cPortable_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memcpyCrc32cPortable_spec
/-- info: 'Crc32c.memcpyCrc32cHw_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memcpyCrc32cHw_spec

-- Dispatched public entry points. `memcpyCrc32c_spec` is the headline theorem.
/-- info: 'Crc32c.extendCrc32c_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendCrc32c_eq_spec
/-- info: 'Crc32c.computeCrc32c_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms computeCrc32c_eq_spec
/-- info: 'Crc32c.memcpyCrc32c_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memcpyCrc32c_spec
/-- info: 'Crc32c.memcpyCrc32cK_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memcpyCrc32cK_spec

-- Phase 6: entry points behind the C++ wrapper.
/-- info: 'Crc32c.extendRaw_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendRaw_spec
/-- info: 'Crc32c.extendHwRaw_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendHwRaw_spec
/-- info: 'Crc32c.extendPortableRaw_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extendPortableRaw_spec
