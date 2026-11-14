/-
Axiom audit for the headline theorems. The build output of this file is the
record quoted in each phase report.
-/
import MemcpyCrc32c.Vectors
import MemcpyCrc32c.ZeroPoly

open Crc32c

#print axioms extend_eq_spec
#print axioms crc32c_eq_spec
#print axioms extend_append
#print axioms concat_spec
#print axioms removePrefix_spec
#print axioms removeSuffix_spec
#print axioms extendZeroes_spec
#print axioms check_123456789
#print axioms zeroes_u64max
#print axioms zero6_209
#print axioms zero4_5275
#print axioms modByMonic_add_zeroPoly_mul
