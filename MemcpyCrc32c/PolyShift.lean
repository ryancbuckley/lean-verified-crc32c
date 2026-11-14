/-
How word shifts act on the reflected polynomial view. The lemmas live in the
`lean-simd-models` package; this file re-exports them.
-/
import MemcpyCrc32c.Poly
import SimdModels.PolyShift

namespace Crc32c
export SimdModels (polyR_shiftLeft_add_shiftRight polyR_setWidth_shiftLeft)
end Crc32c
