/-
Axiom audit for the headline theorems. The build output of this file is the
record quoted in each phase report.

Every Phase 1 and Phase 2 theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), with zero `bv_decide` or
`native_decide` axioms.
-/
import MemcpyCrc32c.Vectors
import MemcpyCrc32c.Portable
import MemcpyCrc32c.Hw

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

-- Phase 3: instruction-model semantics and their link to the reference.
#print axioms SimdModels.crc32c_spec
#print axioms SimdModels.clmul_spec
#print axioms G_eq_castagnoli
#print axioms crc32c_u64_eq
#print axioms crc32c_u8_eq
