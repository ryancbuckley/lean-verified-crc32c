/-
Shard 2 of 4 for `zero4_5275_minimal`: outer iterations `0..772` of `resHi`.
-/
import MemcpyCrc32c.ZeroMin.Deg5275Table

namespace Crc32c.ZeroMin.Deg5275

set_option maxRecDepth 2000000

theorem hi_c0 : loop2n inTable 2147483648 112 (resHi.drop 0) = true := by decide +kernel
theorem hi_c1 : loop2n inTable 2147483648 118 (resHi.drop 112) = true := by decide +kernel
theorem hi_c2 : loop2n inTable 2147483648 123 (resHi.drop 230) = true := by decide +kernel
theorem hi_c3 : loop2n inTable 2147483648 131 (resHi.drop 353) = true := by decide +kernel
theorem hi_c4 : loop2n inTable 2147483648 139 (resHi.drop 484) = true := by decide +kernel
theorem hi_c5 : loop2n inTable 2147483648 149 (resHi.drop 623) = true := by decide +kernel

end Crc32c.ZeroMin.Deg5275
