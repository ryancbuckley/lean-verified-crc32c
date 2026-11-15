/-
Shard 0 of 4 for `zero4_5275_minimal`: outer iterations `0..772` of `resLo`.
-/
import MemcpyCrc32c.ZeroMin.Deg5275Table

namespace Crc32c.ZeroMin.Deg5275

set_option maxRecDepth 2000000

theorem lo_c0 : loop2n inTable 2147483648 112 (resLo.drop 0) = true := by decide +kernel
theorem lo_c1 : loop2n inTable 2147483648 118 (resLo.drop 112) = true := by decide +kernel
theorem lo_c2 : loop2n inTable 2147483648 123 (resLo.drop 230) = true := by decide +kernel
theorem lo_c3 : loop2n inTable 2147483648 131 (resLo.drop 353) = true := by decide +kernel
theorem lo_c4 : loop2n inTable 2147483648 139 (resLo.drop 484) = true := by decide +kernel
theorem lo_c5 : loop2n inTable 2147483648 149 (resLo.drop 623) = true := by decide +kernel

end Crc32c.ZeroMin.Deg5275
