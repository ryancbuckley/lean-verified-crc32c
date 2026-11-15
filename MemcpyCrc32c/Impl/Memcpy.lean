/-
`MemcpyCrc32c`: copy `n` bytes and return the CRC32C of the copied bytes.
Core-only executable code; theorem 6 of the brief is proven for each path in
`MemcpyCrc32c.Memcpy`.

First version: the copy is Lean core's `ByteArray.copySlice` (a `memmove` in
the runtime, in place when `dst` is not shared) and the CRC is computed over
the source by the proven kernels. The two are not yet interleaved; whether
interleaving them is worth a trusted store primitive is decided by
measurement.

Bounds are proof arguments, so there is no out-of-bounds behaviour to define:
no panic, no truncation, and `dst` never grows.
-/
import MemcpyCrc32c.Impl.Hw

namespace Crc32c

/-- Copy `src[sOff, sOff + n)` to `dst[dOff, dOff + n)` and return the new
destination with `absl::ExtendCrc32c init` of the copied bytes. Portable path. -/
def memcpyCrc32cPortable (dst : ByteArray) (dOff : Nat) (src : @& ByteArray) (sOff n : Nat)
    (init : UInt32) (hs : sOff + n ≤ src.size) (_hd : dOff + n ≤ dst.size) :
    ByteArray × UInt32 :=
  let r := rawExtendPortable (init ^^^ 0xFFFFFFFF) src sOff n hs ^^^ 0xFFFFFFFF
  (src.copySlice sOff dst dOff n, r)

/-- As `memcpyCrc32cPortable`, on the hardware path. Callers must dispatch here
only on CPUs that have the instructions. -/
def memcpyCrc32cHw (dst : ByteArray) (dOff : Nat) (src : @& ByteArray) (sOff n : Nat)
    (init : UInt32) (hs : sOff + n ≤ src.size) (_hd : dOff + n ≤ dst.size) :
    ByteArray × UInt32 :=
  let r := rawExtendHw (init ^^^ 0xFFFFFFFF) src sOff n hs ^^^ 0xFFFFFFFF
  (src.copySlice sOff dst dOff n, r)

end Crc32c
