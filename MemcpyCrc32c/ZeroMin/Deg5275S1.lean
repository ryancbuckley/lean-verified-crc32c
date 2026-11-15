/-
Shard 1 of 4 for `zero4_5275_minimal`: outer iterations `772..2637` of `resLo`.
-/
import MemcpyCrc32c.ZeroMin.Deg5275Table

namespace Crc32c.ZeroMin.Deg5275

set_option maxRecDepth 2000000

theorem lo_c6 : loop2n inTable 2147483648 163 (resLo.drop 772) = true := by decide +kernel
theorem lo_c7 : loop2n inTable 2147483648 180 (resLo.drop 935) = true := by decide +kernel
theorem lo_c8 : loop2n inTable 2147483648 204 (resLo.drop 1115) = true := by decide +kernel
theorem lo_c9 : loop2n inTable 2147483648 242 (resLo.drop 1319) = true := by decide +kernel
theorem lo_c10 : loop2n inTable 2147483648 315 (resLo.drop 1561) = true := by decide +kernel
theorem lo_c11 : loop2n inTable 2147483648 761 (resLo.drop 1876) = true := by decide +kernel

end Crc32c.ZeroMin.Deg5275
