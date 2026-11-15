/-
Axiom audit for the headline theorems. The build output of this file is the
record quoted in each phase report.

Every Phase 1, Phase 2, Phase 3, and Phase 4 theorem depends only on Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero
`bv_decide` or `native_decide` axioms.
-/
import MemcpyCrc32c.Vectors
import MemcpyCrc32c.Portable
import MemcpyCrc32c.CApi
import SimdModels

open Crc32c

#print axioms extend_eq_spec
#print axioms crc32c_eq_spec
#print axioms extend_append
#print axioms concat_spec
#print axioms removePrefix_spec
#print axioms removeSuffix_spec
#print axioms extendZeroes_spec
#print axioms Spec.extend_append
#print axioms Spec.concat_spec
#print axioms Spec.removePrefix_spec
#print axioms Spec.removeSuffix_spec
#print axioms Spec.extendZeroes_spec
#print axioms check_123456789
#print axioms rfc3720_iscsi_read
#print axioms zeroes_u64max
#print axioms zero6_209
#print axioms zero6_290
#print axioms zero4_5275
#print axioms modByMonic_add_zeroPoly_mul

-- Phase 2: pure kernel proofs as well (no `bv_decide` axioms).
#print axioms rawExtendPortable_eq
#print axioms extendPortable_eq_extend
#print axioms extendPortable_eq_spec

-- Phase 3: instruction-model semantics, V128 views, Intel SDM equivalence, and link to reference.
#print axioms SimdModels.crc32c_spec
#print axioms SimdModels.clmul_spec
#print axioms SimdModels.clmul_spec_reflected
#print axioms SimdModels.V128.ofHalves_lo_hi
#print axioms SimdModels.V128.lane8_vextq
#print axioms SimdModels.V128.lane8_vld1q
#print axioms SimdModels.clmulepi64_spec
#print axioms SimdModels.clmulepi64_spec_reflected
#print axioms SimdModels.IntelSdm.crc32_u8_eq
#print axioms SimdModels.IntelSdm.crc32_u16_eq
#print axioms SimdModels.IntelSdm.crc32_u32_eq
#print axioms SimdModels.IntelSdm.crc32_u64_eq
#print axioms SimdModels.IntelSdm.crc32_r64_eq
#print axioms SimdModels.IntelSdm.clmulepi64_eq
#print axioms G_eq_castagnoli
#print axioms crc32c_u64_eq
#print axioms crc32c_u32_eq
#print axioms crc32c_u16_eq
#print axioms crc32c_u8_eq
#print axioms loadU8_eq_uget
#print axioms loadU64LE_eq_load64
#print axioms polyR_clmulLo_toUInt64
#print axioms R128_clmul

-- Phase 4 (AArch64 / x86-64 hybrid hardware-CRC + CLMUL kernel). Rests on the
-- trusted bindings in `SimdModels.Trusted`, which `#print axioms` cannot show.
#print axioms π_P_hwMul
#print axioms hwFold3_spec
#print axioms hwFold6_eq
#print axioms rawExtendHw_eq
#print axioms extendHw_eq_extend
#print axioms extendHw_eq_spec

-- Phase 5: theorem 6 (`memcpyCrc32c_spec`) for each path.
#print axioms memcpyCrc32cPortable_spec
#print axioms memcpyCrc32cHw_spec

-- Dispatched public entry points. `memcpyCrc32c_spec` is the headline theorem.
#print axioms extendCrc32c_eq_spec
#print axioms computeCrc32c_eq_spec
#print axioms memcpyCrc32c_spec
#print axioms memcpyCrc32cK_spec

-- Phase 6: entry points behind the C++ wrapper.
#print axioms extendRaw_spec
#print axioms extendHwRaw_spec
#print axioms extendPortableRaw_spec
