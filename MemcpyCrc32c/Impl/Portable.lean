/-
The portable CRC32C path: plain `UInt64` word operations, no lookup tables and
no carry-less multiply. Core-only executable code; proven equal to the
reference in `MemcpyCrc32c.Portable`.

The kernel is Chorba-style reduction by the 6-term zero polynomial
`Z = X^209 + X^144 + X^54 + X^39 + X^14 + 1` (`zero6_209`). Adding `v · Z`
cancels a message word `v` and re-injects it 65, 155, 170, 195 and 209 bits
later in the stream, which lands in the next four words. Those four pending
words are the whole state, so the loop reads memory and never writes it.
-/
import MemcpyCrc32c.Impl.Reference

namespace Crc32c

theorem usize_add_toNat (i : USize) (k : Nat) (h : i.toNat + k < USize.size) :
    (i + USize.ofNat k).toNat = i.toNat + k := by
  rw [USize.toNat_add, USize.toNat_ofNat_of_lt' (by omega)]; exact Nat.mod_eq_of_lt h

/-- A little-endian 64-bit word from its bytes. -/
@[inline] def word64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- Unaligned little-endian 64-bit load at byte offset `i`. -/
@[inline] def load64 (a : @& ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) : UInt64 :=
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := usize_add_toNat i 3 (by omega)
  have h4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
  have h5 : (i + 5).toNat = i.toNat + 5 := usize_add_toNat i 5 (by omega)
  have h6 : (i + 6).toNat = i.toNat + 6 := usize_add_toNat i 6 (by omega)
  have h7 : (i + 7).toNat = i.toNat + 7 := usize_add_toNat i 7 (by omega)
  word64 (a.uget i (by omega)) (a.uget (i + 1) (by omega)) (a.uget (i + 2) (by omega))
    (a.uget (i + 3) (by omega)) (a.uget (i + 4) (by omega)) (a.uget (i + 5) (by omega))
    (a.uget (i + 6) (by omega)) (a.uget (i + 7) (by omega))

/-- Absorb the eight bytes of a little-endian word, bit at a time. -/
def stepWord (s : UInt32) (w : UInt64) : UInt32 :=
  let s := stepByte s w.toUInt8
  let s := stepByte s (w >>> 8).toUInt8
  let s := stepByte s (w >>> 16).toUInt8
  let s := stepByte s (w >>> 24).toUInt8
  let s := stepByte s (w >>> 32).toUInt8
  let s := stepByte s (w >>> 40).toUInt8
  let s := stepByte s (w >>> 48).toUInt8
  stepByte s (w >>> 56).toUInt8

/-- Bytewise reference loop over `a[i, stop)`. -/
def bytesLoop (a : @& ByteArray) (i stop : USize) (hstop : stop.toNat ≤ a.size)
    (s : UInt32) : UInt32 :=
  if hlt : i < stop then
    bytesLoop a (i + 1) stop hstop (stepByte s (a.uget i (by rw [USize.lt_iff_toNat_lt] at hlt; omega)))
  else s
termination_by stop.toNat - i.toNat
decreasing_by
  rw [USize.lt_iff_toNat_lt] at hlt
  have := stop.toNat_lt_size
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  omega

/-- The reduction loop. Words `a[i, stop)` are folded into the four pending
words; then the last four words and the tail bytes `a[stop + 32, fin)` are
finished with the reference. -/
def fold209 (a : @& ByteArray) (hs : a.size < USize.size) (i stop fin : USize)
    (_hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 8 = 0)
    (hstop : stop.toNat + 32 ≤ fin.toNat) (hfin : fin.toNat ≤ a.size)
    (n1 n2 n3 n4 : UInt64) : UInt32 :=
  if hlt : i < stop then
    have hlt' : i.toNat < stop.toNat := USize.lt_iff_toNat_lt.mp hlt
    have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
    let v := load64 a i hs (by omega) ^^^ n1
    fold209 a hs (i + 8) stop fin (by omega) (by omega) hstop hfin
      (n2 ^^^ (v <<< 1))
      (n3 ^^^ (v >>> 63) ^^^ (v <<< 27) ^^^ (v <<< 42))
      (n4 ^^^ (v >>> 37) ^^^ (v >>> 22) ^^^ (v <<< 3) ^^^ (v <<< 17))
      ((v >>> 61) ^^^ (v >>> 47))
  else
    have h8 : (stop + 8).toNat = stop.toNat + 8 := usize_add_toNat stop 8 (by omega)
    have h16 : (stop + 16).toNat = stop.toNat + 16 := usize_add_toNat stop 16 (by omega)
    have h24 : (stop + 24).toNat = stop.toNat + 24 := usize_add_toNat stop 24 (by omega)
    have h32 : (stop + 32).toNat = stop.toNat + 32 := usize_add_toNat stop 32 (by omega)
    let s := stepWord 0 (load64 a stop hs (by omega) ^^^ n1)
    let s := stepWord s (load64 a (stop + 8) hs (by omega) ^^^ n2)
    let s := stepWord s (load64 a (stop + 16) hs (by omega) ^^^ n3)
    let s := stepWord s (load64 a (stop + 24) hs (by omega) ^^^ n4)
    bytesLoop a (stop + 32) fin hfin s
termination_by stop.toNat - i.toNat
decreasing_by omega

/-- Unconditioned CRC32C state update over `a[off, off + len)`, portable path. -/
def rawExtendPortable (s : UInt32) (a : @& ByteArray) (off len : Nat)
    (h : off + len ≤ a.size) : UInt32 :=
  if hs : a.size < USize.size then
    if h40 : 40 ≤ len then
      fold209 a hs off.toUSize (off + (len / 8 - 4) * 8).toUSize (off + len).toUSize
        (by rw [USize.toNat_ofNat_of_lt' (by omega), USize.toNat_ofNat_of_lt' (by omega)]; omega)
        (by rw [USize.toNat_ofNat_of_lt' (by omega), USize.toNat_ofNat_of_lt' (by omega)]; omega)
        (by rw [USize.toNat_ofNat_of_lt' (by omega), USize.toNat_ofNat_of_lt' (by omega)]; omega)
        (by rw [USize.toNat_ofNat_of_lt' (by omega)]; omega)
        s.toUInt64 0 0 0
    else
      bytesLoop a off.toUSize (off + len).toUSize
        (by rw [USize.toNat_ofNat_of_lt' (by omega)]; omega) s
  else
    -- Unreachable on any real platform: byte arrays are smaller than the address space.
    rawExtend s ((a.extract off (off + len)).data.toList)

/-- `absl::ExtendCrc32c`, portable path. -/
def extendPortable (c : UInt32) (a : @& ByteArray) : UInt32 :=
  rawExtendPortable (c ^^^ 0xFFFFFFFF) a 0 a.size (by omega) ^^^ 0xFFFFFFFF

end Crc32c
