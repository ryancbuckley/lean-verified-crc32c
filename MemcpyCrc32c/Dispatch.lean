/-
Correctness of runtime dispatch. Every path equals the spec, so the dispatched
entry points do too, whatever the CPU-feature test answers. The test is
`opaque`, so these proofs cannot depend on its value. Kernel-only proofs.
-/
import MemcpyCrc32c.Memcpy
import MemcpyCrc32c.Impl.Dispatch

namespace Crc32c

/-- Dispatch is correct: `extendCrc32c` is the reference on every input. -/
theorem extendCrc32c_eq_extend (c : UInt32) (a : ByteArray) : extendCrc32c c a = extend c a := by
  unfold extendCrc32c
  split
  · exact extendHw_eq_extend c a
  · exact extendPortable_eq_extend c a

/-- The dispatched CRC satisfies the polynomial spec. -/
theorem extendCrc32c_eq_spec (c : UInt32) (a : ByteArray) : extendCrc32c c a = Spec.extend c a := by
  rw [extendCrc32c_eq_extend, extend_eq_spec]

theorem computeCrc32c_eq_spec (a : ByteArray) : computeCrc32c a = Spec.crc32c a :=
  extendCrc32c_eq_spec 0 a

/-- Theorem 6, the headline: `memcpyCrc32c` copies exactly and returns the
spec CRC of the copied bytes, on every path. -/
theorem memcpyCrc32c_spec (dst : ByteArray) (dOff : Nat) (src : ByteArray) (sOff n : Nat)
    (init : UInt32) (hs : sOff + n ≤ src.size) (hd : dOff + n ≤ dst.size) :
    memcpyCrc32c dst dOff src sOff n init hs hd =
      (src.copySlice sOff dst dOff n, Spec.extend init (src.extract sOff (sOff + n))) := by
  unfold memcpyCrc32c
  split
  · rw [memcpyCrc32cHw_spec, extend_eq_spec]
  · rw [memcpyCrc32cPortable_spec, extend_eq_spec]

end Crc32c
