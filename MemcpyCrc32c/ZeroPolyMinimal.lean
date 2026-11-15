/-
Exhaustive, kernel-checked minimality and uniqueness theorems (`decide +kernel`,
zero `native_decide`) for sparse multiples of the Castagnoli CRC32C generator `G`
("zero polynomials", after Chorba):

- **Weight `< 4` (`2` terms, `MemcpyCrc32c.PolyAlgebra`):**
  `zero2_minimal`, `zero2_unique` — minimal degree `2^31 - 1 = 2147483647`,
  uniquely achieved by `X^2147483647 + 1`.
- **Weight `< 6` (`≤ 4` terms, `MemcpyCrc32c.ZeroMin.Deg5275`):**
  `zero4_5275_minimal`, `zero4_5275_unique` — minimal degree `5275`, uniquely
  achieved by `X^5275 + X^4508 + X^2751 + 1`.
- **Weight `< 8` (`≤ 6` terms, `MemcpyCrc32c.ZeroMin.Deg209`):**
  `zero6_209_minimal`, `zero6_209_unique` — minimal degree `209`, uniquely
  achieved by `X^209 + X^144 + X^54 + X^39 + X^14 + 1`; plus
  `zero6_word64_minimal` and `zero6_word64_unique` for 64-bit word-aligned
  polynomials `Z(X^64)` (degree `64 * 209 = 13376`).
- **Weight `< 8` with leading gap `≥ 128` (`MemcpyCrc32c.ZeroMin.Deg290`):**
  `zero6_290_minimal`, `zero6_290_unique` — minimal degree `290`, uniquely
  achieved by `X^290 + X^136 + X^113 + X^107 + X^32 + 1`.
- **Weight `< 10` (`≤ 8` terms, `MemcpyCrc32c.ZeroMin.Deg79`):**
  `zero8_79_minimal`, `zero8_79_unique` — minimal degree `79`, uniquely
  achieved by `X^79 + X^75 + X^71 + X^58 + X^18 + X^12 + X + 1`.
-/
import MemcpyCrc32c.ZeroMin.Deg209
import MemcpyCrc32c.ZeroMin.Deg290
import MemcpyCrc32c.ZeroMin.Deg79
import MemcpyCrc32c.ZeroMin.Deg5275
