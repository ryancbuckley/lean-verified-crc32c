/-
The hardware-CRC path: the CPU's CRC32C instruction over three interleaved
streams, written in Lean against the trusted bindings of `lean-simd-models`.
Core-only executable code; proven equal to the reference in
`MemcpyCrc32c.HwKernel`.

The instruction has a three-cycle latency and a one-cycle throughput, so three
independent streams run in the time of one. The three stream CRCs are then
combined with the Phase 1 arithmetic (`mulMod` by `X^(8·L)`).

Callers must dispatch here only on CPUs that have the instructions.
-/
import MemcpyCrc32c.Impl.Portable
import SimdModels.Trusted

namespace Crc32c
open SimdModels (crc32c_u8 crc32c_u64)

/-- Bytewise loop over `a[i, stop)` with the 8-bit CRC32C instruction. -/
def hwBytes (a : @& ByteArray) (i stop : USize) (hstop : stop.toNat ≤ a.size)
    (s : UInt32) : UInt32 :=
  if hlt : i < stop then
    hwBytes a (i + 1) stop hstop (crc32c_u8 s (a.uget i (by rw [USize.lt_iff_toNat_lt] at hlt; omega)))
  else s
termination_by stop.toNat - i.toNat
decreasing_by
  rw [USize.lt_iff_toNat_lt] at hlt
  have := stop.toNat_lt_size
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  omega

/-- Single stream over `a[i, fin)`: whole words with the 64-bit instruction,
then the remaining bytes. -/
def hwLoop (a : @& ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) (s : UInt32) : UInt32 :=
  if h : 8 ≤ fin - i then
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have h' : 8 ≤ fin.toNat - i.toNat := by
      have := USize.le_iff_toNat_le.mp h
      have e8 : (8 : USize).toNat = 8 := by simp
      rw [hsub, e8] at this; exact this
    have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
    hwLoop a hs (i + 8) fin (by omega) hfin (crc32c_u64 s (load64 a i hs (by omega)))
  else hwBytes a i fin hfin s
termination_by fin.toNat - i.toNat
decreasing_by omega

/-- Three interleaved streams `a[i + r·L, stop + r·L)` for `r = 0, 1, 2`,
advanced in lockstep, then combined. With `stop - i = L` at entry the result
is the CRC state over the `3·L` contiguous bytes from `i`. -/
def hwFold3 (a : @& ByteArray) (hs : a.size < USize.size) (i stop L L2 : USize)
    (_hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 8 = 0)
    (hL2 : L2.toNat = 2 * L.toNat) (hL : stop.toNat + 2 * L.toNat ≤ a.size)
    (s0 s1 s2 : UInt32) : UInt32 :=
  if hlt : i < stop then
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have hlt' : i.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp hlt
    have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
    have hi1 : (i + L).toNat = i.toNat + L.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
      rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
    hwFold3 a hs (i + 8) stop L L2 (by omega) (by omega) hL2 hL
      (crc32c_u64 s0 (load64 a i hs (by omega)))
      (crc32c_u64 s1 (load64 a (i + L) hs (by omega)))
      (crc32c_u64 s2 (load64 a (i + L2) hs (by omega)))
  else
    let f := powModU64 x64 0x80000000 (L / 8).toUInt64
    mulMod (mulMod s0 f ^^^ s1) f ^^^ s2
termination_by stop.toNat - i.toNat
decreasing_by omega

/-- Fast entry once `a.size < USize.size` is established. Inputs of 4 KiB and
more are split into three streams. -/
@[inline] def rawExtendHwUSize (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) : UInt32 :=
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  if h3 : 4096 ≤ ulen then
    have e4096 : (4096 : USize).toNat = 4096 := by simp
    have h3' : 4096 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h3; omega
    have e24 : (24 : USize).toNat = 24 := by simp
    have e8 : (8 : USize).toNat = 8 := by simp
    have e3 : (3 : USize).toNat = 3 := by simp
    have e2 : (2 : USize).toNat = 2 := by simp
    let ws := ulen / 24
    have hws : ws.toNat = ulen.toNat / 24 := by rw [USize.toNat_div, e24]
    let L := ws * 8
    have hL : L.toNat = ws.toNat * 8 := by
      rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
    let L2 := 2 * L
    have hL2 : L2.toNat = 2 * L.toNat := by
      rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
    let L3 := 3 * L
    have hL3 : L3.toNat = 3 * L.toNat := by
      rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
    have hstop : (uoff + L).toNat = uoff.toNat + L.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have htail : (uoff + L3).toNat = uoff.toNat + 3 * L.toNat := by
      rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
    let s3 := hwFold3 a hs uoff (uoff + L) L L2 (by omega) (by omega) hL2 (by omega) s 0 0
    hwLoop a hs (uoff + L3) (uoff + ulen) (by omega) (by omega) s3
  else
    hwLoop a hs uoff (uoff + ulen) (by omega) (by omega) s

/-- Unconditioned CRC32C state update over `a[off, off + len)`, hardware-CRC path. -/
@[inline] def rawExtendHw (s : UInt32) (a : @& ByteArray) (off len : @& Nat)
    (h : off + len ≤ a.size) : UInt32 :=
  if hsmall : a.size ≤ 0x7FFFFFFF then
    have hs : a.size < USize.size := by have := usize_size_gt; omega
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    rawExtendHwUSize s a hs off.toUSize len.toUSize (by omega)
  else
    -- Buffers over 2 GiB take the portable path, which handles the full range.
    rawExtendPortableCold s a off len h

/-- `absl::ExtendCrc32c`, hardware-CRC path. -/
def extendHw (c : UInt32) (a : @& ByteArray) : UInt32 :=
  rawExtendHw (c ^^^ 0xFFFFFFFF) a 0 a.size (by omega) ^^^ 0xFFFFFFFF

end Crc32c
