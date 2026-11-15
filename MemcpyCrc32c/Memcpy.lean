/-
Theorem 6 of the brief, `memcpyCrc32c_spec`, for each path: the destination is
exactly `src.copySlice sOff dst dOff n`, and the returned value is
`extend init` of the copied bytes. Kernel-only proofs.
-/
import MemcpyCrc32c.HwKernel
import MemcpyCrc32c.Impl.Memcpy

namespace Crc32c

theorem extend_extract (init : UInt32) (src : ByteArray) (sOff n : Nat) :
    extend init (src.extract sOff (sOff + n)) =
      rawExtend (init ^^^ 0xFFFFFFFF) (bytes src sOff (sOff + n)) ^^^ 0xFFFFFFFF := by
  rw [extend, bytes_extract]

/-- Theorem 6, portable path. -/
theorem memcpyCrc32cPortable_spec (dst : ByteArray) (dOff : Nat) (src : ByteArray) (sOff n : Nat)
    (init : UInt32) (hs : sOff + n ≤ src.size) (hd : dOff + n ≤ dst.size) :
    memcpyCrc32cPortable dst dOff src sOff n init hs hd =
      (src.copySlice sOff dst dOff n, extend init (src.extract sOff (sOff + n))) := by
  rw [memcpyCrc32cPortable, rawExtendPortable_eq, extend_extract]

/-- Theorem 6, hardware path. -/
theorem memcpyCrc32cHw_spec (dst : ByteArray) (dOff : Nat) (src : ByteArray) (sOff n : Nat)
    (init : UInt32) (hs : sOff + n ≤ src.size) (hd : dOff + n ≤ dst.size) :
    memcpyCrc32cHw dst dOff src sOff n init hs hd =
      (src.copySlice sOff dst dOff n, extend init (src.extract sOff (sOff + n))) := by
  rw [memcpyCrc32cHw, rawExtendHw_eq, extend_extract]

/-- The copy never changes the destination's size. -/
theorem size_copySlice_of_le (dst : ByteArray) (dOff : Nat) (src : ByteArray) (sOff n : Nat)
    (hs : sOff + n ≤ src.size) (hd : dOff + n ≤ dst.size) :
    (src.copySlice sOff dst dOff n).size = dst.size := by
  simp [ByteArray.copySlice, ByteArray.size, ← ByteArray.size_data] at *
  omega

end Crc32c
