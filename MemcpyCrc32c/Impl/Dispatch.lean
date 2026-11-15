/-
Runtime dispatch: the public entry points. Each picks the hardware path when
the CPU has the instructions and the portable path otherwise. Core-only
executable code; proven in `MemcpyCrc32c.Dispatch`.
-/
import MemcpyCrc32c.Impl.Memcpy

namespace Crc32c

/-- Whether this CPU has the CRC32C and carry-less-multiply instructions.
Evaluated once, when the program starts. -/
def hwAvailable : Bool := SimdModels.cpuHasCrcClmul ()

/-- `absl::ExtendCrc32c`: extend the CRC32C `c` by the bytes of `a`. -/
def extendCrc32c (c : UInt32) (a : @& ByteArray) : UInt32 :=
  if hwAvailable then extendHw c a else extendPortable c a

/-- `absl::ComputeCrc32c`. -/
def computeCrc32c (a : @& ByteArray) : UInt32 := extendCrc32c 0 a

/-- `absl::MemcpyCrc32c`: copy `src[sOff, sOff + n)` to `dst[dOff, dOff + n)`
and return the new destination with `ExtendCrc32c init` of the copied bytes. -/
def memcpyCrc32c (dst : ByteArray) (dOff : Nat) (src : @& ByteArray) (sOff n : Nat)
    (init : UInt32) (hs : sOff + n ≤ src.size) (hd : dOff + n ≤ dst.size) :
    ByteArray × UInt32 :=
  if hwAvailable then memcpyCrc32cHw dst dOff src sOff n init hs hd
  else memcpyCrc32cPortable dst dOff src sOff n init hs hd

end Crc32c
