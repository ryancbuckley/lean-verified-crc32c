/-
Shard 3 of 4 for `zero4_5275_minimal`: outer iterations `772..2637` of `resHi`.
-/
import MemcpyCrc32c.ZeroMin.Deg5275Table

namespace Crc32c.ZeroMin.Deg5275

set_option maxRecDepth 2000000

theorem hi_c6 : loop2n inTable 2147483648 163 (resHi.drop 772) = true := by decide +kernel
theorem hi_c7 : loop2n inTable 2147483648 180 (resHi.drop 935) = true := by decide +kernel
theorem hi_c8 : loop2n inTable 2147483648 204 (resHi.drop 1115) = true := by decide +kernel
theorem hi_c9 : loop2n inTable 2147483648 242 (resHi.drop 1319) = true := by decide +kernel
theorem hi_c10 : loop2n inTable 2147483648 315 (resHi.drop 1561) = true := by decide +kernel
theorem hi_c11 : loop2n inTable 2147483648 761 (resHi.drop 1876) = true := by decide +kernel

end Crc32c.ZeroMin.Deg5275
