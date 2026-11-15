/-
Correctness of the C++ wrapper's entry points: each returns the spec CRC of
the first `len` bytes. Kernel-only proofs.
-/
import MemcpyCrc32c.Dispatch
import MemcpyCrc32c.Impl.CApi

namespace Crc32c

theorem extendHwRaw_spec (c : UInt32) (a : ByteArray) (len : USize)
    (hs : a.size < USize.size) (h : len.toNat ≤ a.size) :
    extendHwRaw c a len hs h = Spec.extend c (a.extract 0 len.toNat) := by
  have e := extend_extract c a 0 len.toNat
  rw [Nat.zero_add] at e
  have z : (0 : USize).toNat = 0 := by simp
  rw [← extend_eq_spec, e, extendHwRaw_eq_rawExtendHwUSize]
  simp only [rawExtendHwUSize_eq, z, Nat.zero_add]

theorem extendPortableRaw_spec (c : UInt32) (a : ByteArray) (len : USize)
    (hs : a.size < USize.size) (h : len.toNat ≤ a.size) :
    extendPortableRaw c a len hs h = Spec.extend c (a.extract 0 len.toNat) := by
  have e := extend_extract c a 0 len.toNat
  rw [Nat.zero_add] at e
  have z : (0 : USize).toNat = 0 := by simp
  rw [← extend_eq_spec, e]
  simp only [extendPortableRaw, rawExtendPortableUSize_eq, z, Nat.zero_add]

theorem extendRaw_spec (c : UInt32) (a : ByteArray) (len : USize) (hs : a.size < USize.size)
    (h : len.toNat ≤ a.size) :
    extendRaw c a len hs h = Spec.extend c (a.extract 0 len.toNat) := by
  unfold extendRaw
  split
  · exact extendHwRaw_spec c a len hs h
  · exact extendPortableRaw_spec c a len hs h

end Crc32c
