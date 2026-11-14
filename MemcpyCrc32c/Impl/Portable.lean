/-
The portable CRC32C path: plain `UInt64` word operations and no carry-less
multiply. Lookup tables are used only for the last 32 to 39 bytes and for
inputs shorter than 40 bytes. Core-only executable code; proven equal to the
reference in `MemcpyCrc32c.Portable`.

The kernel is Chorba-style reduction by the 6-term zero polynomial
`Z = X^209 + X^144 + X^54 + X^39 + X^14 + 1` (`zero6_209`). Adding `v · Z`
cancels a message word `v` and re-injects it 65, 155, 170, 195 and 209 bits
later in the stream, which lands in the next four words. Those four pending
words are the whole state, so the loop reads memory and never writes it.
-/
import MemcpyCrc32c.Impl.Reference

namespace Crc32c

theorem usize_size_gt : 0x80000000 ≤ USize.size := by
  rcases System.Platform.numBits_eq with h | h <;> simp [USize.size, h]

theorem usize_ofNat_lt_8 (k : Nat) (hk : k < 8) : (USize.ofNat k).toNat < 8 := by
  have := usize_size_gt
  rw [USize.toNat_ofNat_of_lt' (by omega)]
  exact hk

theorem usize_add_toNat (i : USize) (k : Nat) (h : i.toNat + k < USize.size) :
    (i + USize.ofNat k).toNat = i.toNat + k := by
  rw [USize.toNat_add, USize.toNat_ofNat_of_lt' (by omega)]; exact Nat.mod_eq_of_lt h

/-- A little-endian 32-bit word from its bytes. -/
@[inline] def word32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- A little-endian 64-bit word from its bytes. -/
@[inline] def word64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- Unaligned little-endian 32-bit load at byte offset `i`. -/
@[inline] def load32 (a : @& ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 4 ≤ a.size) : UInt32 :=
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := usize_add_toNat i 3 (by omega)
  word32 (a.uget i (by omega)) (a.uget (i + 1) (by omega))
    (a.uget (i + 2) (by omega)) (a.uget (i + 3) (by omega))

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

/-- Entry `m` of the packed 8 KiB slicing-by-8 table. -/
def sliceTableEntry (m : Fin 8192) : UInt8 :=
  let idx := m.val / 4
  let shift := ((m.val % 4) * 8).toUInt32
  let entry := rawExtend 0 (UInt8.ofNat (idx % 256) :: List.replicate (7 - idx / 256) 0)
  (entry >>> shift).toUInt8

/-- Packed 8 KiB slicing-by-8 table, computed from the bitwise reference at
start-up: the 4 little-endian bytes at `4 * (256 * k + b)` store the `UInt32`
state after byte `b` followed by `7 - k` zero bytes (half the L1 footprint of a
boxed `Array UInt32`, with byte lane `k` at offset `1024 * k` so every lookup
merges into a single unboxed 32-bit load). -/
def sliceTableBytes : ByteArray :=
  ByteArray.mk (Array.ofFn sliceTableEntry)

theorem sliceTableBytes_size : sliceTableBytes.size = 8192 := by
  simp [sliceTableBytes, ByteArray.size]

theorem sliceTableBytes_uget (j : USize) (h : j.toNat < sliceTableBytes.size) :
    sliceTableBytes.uget j h = sliceTableEntry ⟨j.toNat, by simpa [sliceTableBytes_size] using h⟩ := by
  have key : ∀ {n : Nat} (f : Fin n → UInt8) (h' : j.toNat < (ByteArray.mk (Array.ofFn f)).size),
      (ByteArray.mk (Array.ofFn f)).uget j h' = f ⟨j.toNat, by simpa [ByteArray.size] using h'⟩ := by
    intro n f h'; simp [ByteArray.uget]
  exact key sliceTableEntry h

/-- Table lookup for byte lane `k` (`0 ≤ k < 8`): byte `b` followed by `7 - k` zero bytes. -/
@[inline] def tbl (k : USize) (hk : k.toNat < 8) (b : UInt8) : UInt32 :=
  have hs : 8192 < USize.size := by have := usize_size_gt; omega
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hb : b.toUSize.toNat = b.toNat := by simp
  have h1024 : (1024 : USize).toNat = 1024 := by simp
  have h4 : (4 : USize).toNat = 4 := by simp
  have hm1 : (k * 1024).toNat = k.toNat * 1024 := by
    rw [USize.toNat_mul, h1024]; exact Nat.mod_eq_of_lt (by omega)
  have hm2 : (b.toUSize * 4).toNat = b.toNat * 4 := by
    rw [USize.toNat_mul, hb, h4]; exact Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)
  let base : USize := k * 1024 + b.toUSize * 4
  have hbase : base.toNat = k.toNat * 1024 + b.toNat * 4 := by
    rw [USize.toNat_add, hm1, hm2]; exact Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)
  have h1 : (base + 1).toNat = base.toNat + 1 := usize_add_toNat base 1 (by have := b.toNat_lt; omega)
  have h2 : (base + 2).toNat = base.toNat + 2 := usize_add_toNat base 2 (by have := b.toNat_lt; omega)
  have h3 : (base + 3).toNat = base.toNat + 3 := usize_add_toNat base 3 (by have := b.toNat_lt; omega)
  word32
    (sliceTableBytes.uget base (by rw [sliceTableBytes_size]; have := b.toNat_lt; omega))
    (sliceTableBytes.uget (base + 1) (by rw [sliceTableBytes_size]; have := b.toNat_lt; omega))
    (sliceTableBytes.uget (base + 2) (by rw [sliceTableBytes_size]; have := b.toNat_lt; omega))
    (sliceTableBytes.uget (base + 3) (by rw [sliceTableBytes_size]; have := b.toNat_lt; omega))

/-- `stepByte` by table lookup. -/
@[inline] def stepByteT (s : UInt32) (b : UInt8) : UInt32 :=
  tbl 7 (usize_ofNat_lt_8 7 (by omega)) (s.toUInt8 ^^^ b) ^^^ (s >>> 8)

/-- Slicing-by-8 step on two 32-bit halves `lo` and `hi`. -/
@[inline] def stepWordT32 (lo hi : UInt32) : UInt32 :=
  tbl 0 (usize_ofNat_lt_8 0 (by omega)) lo.toUInt8 ^^^
    tbl 1 (usize_ofNat_lt_8 1 (by omega)) (lo >>> 8).toUInt8 ^^^
    tbl 2 (usize_ofNat_lt_8 2 (by omega)) (lo >>> 16).toUInt8 ^^^
    tbl 3 (usize_ofNat_lt_8 3 (by omega)) (lo >>> 24).toUInt8 ^^^
    tbl 4 (usize_ofNat_lt_8 4 (by omega)) hi.toUInt8 ^^^
    tbl 5 (usize_ofNat_lt_8 5 (by omega)) (hi >>> 8).toUInt8 ^^^
    tbl 6 (usize_ofNat_lt_8 6 (by omega)) (hi >>> 16).toUInt8 ^^^
    tbl 7 (usize_ofNat_lt_8 7 (by omega)) (hi >>> 24).toUInt8

/-- `stepWord 0 w` by slicing-by-8. -/
@[inline] def stepWordT0 (w : UInt64) : UInt32 :=
  stepWordT32 w.toUInt32 (w >>> 32).toUInt32

/-- `stepWord` by slicing-by-8. -/
@[inline] def stepWordT (s : UInt32) (w : UInt64) : UInt32 :=
  stepWordT32 (w.toUInt32 ^^^ s) (w >>> 32).toUInt32

/-- Table-driven bytewise loop over `a[i, stop)`. -/
def bytesLoop (a : @& ByteArray) (i stop : USize) (hstop : stop.toNat ≤ a.size)
    (s : UInt32) : UInt32 :=
  if hlt : i < stop then
    bytesLoop a (i + 1) stop hstop (stepByteT s (a.uget i (by rw [USize.lt_iff_toNat_lt] at hlt; omega)))
  else s
termination_by stop.toNat - i.toNat
decreasing_by
  rw [USize.lt_iff_toNat_lt] at hlt
  have := stop.toNat_lt_size
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by omega)
  omega

/-- Slicing-by-8 over `a[i, fin)`: whole words (loaded as two 32-bit halves so
LLVM emits clean 32/64-bit loads without byte-unpacking), then remaining bytes.
Used for short inputs. -/
def sliceLoop (a : @& ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) (s : UInt32) : UInt32 :=
  if h : 8 ≤ fin - i then
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have h' : 8 ≤ fin.toNat - i.toNat := by
      have := USize.le_iff_toNat_le.mp h
      have e8 : (8 : USize).toNat = 8 := by simp
      rw [hsub, e8] at this; exact this
    have h4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
    have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
    let lo := load32 a i hs (by omega) ^^^ s
    let hiw := load32 a (i + 4) hs (by omega)
    sliceLoop a hs (i + 8) fin (by omega) hfin (stepWordT32 lo hiw)
  else bytesLoop a i fin hfin s
termination_by fin.toNat - i.toNat
decreasing_by omega

/-- The reduction loop. Words `a[i, stop)` are folded into the four pending
words; then the last four words and the tail bytes `a[stop + 32, fin)` are
finished by table lookup. -/
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
    let s := stepWordT0 (load64 a stop hs (by omega) ^^^ n1)
    let s := stepWordT s (load64 a (stop + 8) hs (by omega) ^^^ n2)
    let s := stepWordT s (load64 a (stop + 16) hs (by omega) ^^^ n3)
    let s := stepWordT s (load64 a (stop + 24) hs (by omega) ^^^ n4)
    bytesLoop a (stop + 32) fin hfin s
termination_by stop.toNat - i.toNat
decreasing_by omega

/-- Fast unboxed `USize` entry once `a.size < USize.size` is established. -/
@[inline] def rawExtendPortableUSize (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) : UInt32 :=
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  if h40 : 40 ≤ ulen then
    have e40 : (40 : USize).toNat = 40 := by simp
    have h40' : 40 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h40; omega
    have e8 : (8 : USize).toNat = 8 := by simp
    have e4 : (4 : USize).toNat = 4 := by simp
    let nw := ulen / 8
    have hnw : nw.toNat = ulen.toNat / 8 := by rw [USize.toNat_div, e8]
    let body := (nw - 4) * 8
    have hsub : (nw - 4).toNat = nw.toNat - 4 := by
      rw [USize.toNat_sub_of_le nw 4 (USize.le_iff_toNat_le.mpr (by omega)), e4]
    have hbody : body.toNat = (ulen.toNat / 8 - 4) * 8 := by
      rw [USize.toNat_mul, hsub, hnw, e8]; exact Nat.mod_eq_of_lt (by omega)
    have hstop : (uoff + body).toNat = uoff.toNat + body.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    fold209 a hs uoff (uoff + body) (uoff + ulen)
      (by omega) (by omega) (by omega) (by omega) s.toUInt64 0 0 0
  else
    sliceLoop a hs uoff (uoff + ulen) (by omega) (by omega) s

/-- Cold path for buffers larger than 2 GiB (`a.size > 0x7FFFFFFF`). Outlined so
the hot `≤ 2 GiB` fast path in `rawExtendPortable` / `extendPortable` has zero
callee-saved register spills across `USize.size` / `ByteArray.extract` calls. -/
@[noinline] def rawExtendPortableCold (s : UInt32) (a : @& ByteArray) (off len : @& Nat)
    (h : off + len ≤ a.size) : UInt32 :=
  if hs : a.size < USize.size then
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    rawExtendPortableUSize s a hs off.toUSize len.toUSize (by omega)
  else
    -- Unreachable on any real platform: byte arrays are smaller than the address space.
    rawExtend s ((a.extract off (off + len)).data.toList)

/-- Unconditioned CRC32C state update over `a[off, off + len)`, portable path.
Checks `a.size ≤ 0x7FFFFFFF` first as an immediate scalar comparison (avoiding
both `lean_obj_once` and GMP `lean_nat_big_lt` on `USize.size = 2^64`), while
still handling ≥ 2 GiB buffers on 64-bit platforms via `rawExtendPortableCold`. -/
@[inline] def rawExtendPortable (s : UInt32) (a : @& ByteArray) (off len : @& Nat)
    (h : off + len ≤ a.size) : UInt32 :=
  if hsmall : a.size ≤ 0x7FFFFFFF then
    have hs : a.size < USize.size := by have := usize_size_gt; omega
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    rawExtendPortableUSize s a hs off.toUSize len.toUSize (by omega)
  else
    rawExtendPortableCold s a off len h

/-- `absl::ExtendCrc32c`, portable path. -/
def extendPortable (c : UInt32) (a : @& ByteArray) : UInt32 :=
  rawExtendPortable (c ^^^ 0xFFFFFFFF) a 0 a.size (by omega) ^^^ 0xFFFFFFFF

end Crc32c
