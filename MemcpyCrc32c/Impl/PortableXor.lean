/-
Scratch-buffer Chorba kernel for large inputs on the portable path. Core-only
executable code; proven against the spec in `MemcpyCrc32c.PortableXor`.

It reduces by the word-aligned zero polynomial `Z(X^64)` for
`Z = X^209 + X^144 + X^54 + X^39 + X^14 + 1`: cancelling a 64-bit word re-injects
it, unshifted, 65, 155, 170, 195 and 209 words later. So with `v[j]` the word at
position `j` after all earlier cancellations,

    v[j] = in[j] ^ v[j-65] ^ v[j-155] ^ v[j-170] ^ v[j-195] ^ v[j-209],

which needs no shifts and has no short loop-carried dependency, but needs the
last 209 values of `v`. They live in an 18 KiB scratch byte array that the
loops update in place through `storeU64LE` / `storeU64x4LE`:

    words [0, 212)      the last 212 values of `v` before the current chunk
    words [212, 2260)   up to 2048 values of `v` for the current chunk

After each chunk its last 212 words are moved to the front. The final 209 input
words cannot be cancelled this way (their re-injections would land past the end
of the input); they are combined with the pending re-injections in place and
handed to the proven register kernel `rawExtendPortableReg`.
-/
import MemcpyCrc32c.Impl.Portable

namespace Crc32c
open SimdModels

theorem usize_sub_toNat (o : USize) (k : Nat) (hk : k ≤ o.toNat) (hk' : k < 0x80000000) :
    (o - USize.ofNat k).toNat = o.toNat - k := by
  have := usize_size_gt
  have e : (USize.ofNat k).toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  rw [USize.toNat_sub_of_le o _ (USize.le_iff_toNat_le.mpr (by omega)), e]

/-- The scratch buffer, zeroed. A shared constant: the first store copies it. -/
def xorZeroBuf : ByteArray := ⟨Array.replicate 18080 0⟩

theorem xorZeroBuf_size : xorZeroBuf.size = 18080 := by
  simp [xorZeroBuf, ByteArray.size]

/-- `in ^ v[-65] ^ v[-155] ^ v[-170] ^ v[-195] ^ v[-209]` for the word at byte
offset `o` of the scratch buffer and the input word at `a[q, q + 8)`. -/
@[inline] def xorTaps (a : @& ByteArray) (hs : a.size < USize.size) (q : USize)
    (hq : q.toNat + 8 ≤ a.size) (buf : @& ByteArray) (hb : buf.size = 18080) (o : USize)
    (ho1 : 1672 ≤ o.toNat) (ho2 : o.toNat + 8 ≤ 18080) : UInt64 :=
  have hbs : buf.size < USize.size := by have := usize_size_gt; omega
  have e1 : (o - 520).toNat = o.toNat - 520 := usize_sub_toNat o 520 (by omega) (by omega)
  have e2 : (o - 1240).toNat = o.toNat - 1240 := usize_sub_toNat o 1240 (by omega) (by omega)
  have e3 : (o - 1360).toNat = o.toNat - 1360 := usize_sub_toNat o 1360 (by omega) (by omega)
  have e4 : (o - 1560).toNat = o.toNat - 1560 := usize_sub_toNat o 1560 (by omega) (by omega)
  have e5 : (o - 1672).toNat = o.toNat - 1672 := usize_sub_toNat o 1672 (by omega) (by omega)
  load64 a q hs hq ^^^ loadU64LE buf (o - 520) hbs (by omega) ^^^
    loadU64LE buf (o - 1240) hbs (by omega) ^^^ loadU64LE buf (o - 1360) hbs (by omega) ^^^
    loadU64LE buf (o - 1560) hbs (by omega) ^^^ loadU64LE buf (o - 1672) hbs (by omega)

/-- One word at a time over scratch bytes `[o, oEnd)`. -/
def xorLoop1 (a : @& ByteArray) (hs : a.size < USize.size) (buf : ByteArray) (q o oEnd : USize)
    (hb : buf.size = 18080) (ho : 1696 ≤ o.toNat) (_hle : o.toNat ≤ oEnd.toNat)
    (hal : (oEnd.toNat - o.toNat) % 8 = 0) (hEnd : oEnd.toNat ≤ 18080)
    (hq : q.toNat + (oEnd.toNat - o.toNat) ≤ a.size) : { b : ByteArray // b.size = 18080 } :=
  if h : o < oEnd then
    have hlt : o.toNat < oEnd.toNat := USize.lt_iff_toNat_lt.mp h
    have hus := usize_size_gt
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have eo : (o + 8).toNat = o.toNat + 8 := usize_add_toNat o 8 (by omega)
    have eq : (q + 8).toNat = q.toNat + 8 := usize_add_toNat q 8 (by omega)
    let v := xorTaps a hs q (by omega) buf hb o (by omega) (by omega)
    xorLoop1 a hs (storeU64LE buf o v (by omega)) (q + 8) (o + 8) oEnd
      (by rw [storeU64LE, Model.size_storeU64LE]; exact hb) (by omega) (by omega) (by omega) hEnd
      (by omega)
  else ⟨buf, hb⟩
termination_by oEnd.toNat - o.toNat
decreasing_by omega

/-- Four words at a time over scratch bytes `[o, oEnd)`, then `xorLoop1` for
the last one to three. -/
def xorLoop4 (a : @& ByteArray) (hs : a.size < USize.size) (buf : ByteArray) (q o oEnd : USize)
    (hb : buf.size = 18080) (ho : 1696 ≤ o.toNat) (hle : o.toNat ≤ oEnd.toNat)
    (hal : (oEnd.toNat - o.toNat) % 8 = 0) (hEnd : oEnd.toNat ≤ 18080)
    (hq : q.toNat + (oEnd.toNat - o.toNat) ≤ a.size) : { b : ByteArray // b.size = 18080 } :=
  have hd : (oEnd - o).toNat = oEnd.toNat - o.toNat :=
    USize.toNat_sub_of_le oEnd o (USize.le_iff_toNat_le.mpr hle)
  if h : 32 ≤ oEnd - o then
    have h32 : 32 ≤ oEnd.toNat - o.toNat := by
      have := USize.le_iff_toNat_le.mp h
      have e : (32 : USize).toNat = 32 := by simp
      omega
    have hus := usize_size_gt
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have eo8 : (o + 8).toNat = o.toNat + 8 := usize_add_toNat o 8 (by omega)
    have eo16 : (o + 16).toNat = o.toNat + 16 := usize_add_toNat o 16 (by omega)
    have eo24 : (o + 24).toNat = o.toNat + 24 := usize_add_toNat o 24 (by omega)
    have eo32 : (o + 32).toNat = o.toNat + 32 := usize_add_toNat o 32 (by omega)
    have eq8 : (q + 8).toNat = q.toNat + 8 := usize_add_toNat q 8 (by omega)
    have eq16 : (q + 16).toNat = q.toNat + 16 := usize_add_toNat q 16 (by omega)
    have eq24 : (q + 24).toNat = q.toNat + 24 := usize_add_toNat q 24 (by omega)
    have eq32 : (q + 32).toNat = q.toNat + 32 := usize_add_toNat q 32 (by omega)
    let v0 := xorTaps a hs q (by omega) buf hb o (by omega) (by omega)
    let v1 := xorTaps a hs (q + 8) (by omega) buf hb (o + 8) (by omega) (by omega)
    let v2 := xorTaps a hs (q + 16) (by omega) buf hb (o + 16) (by omega) (by omega)
    let v3 := xorTaps a hs (q + 24) (by omega) buf hb (o + 24) (by omega) (by omega)
    xorLoop4 a hs (storeU64x4LE buf o v0 v1 v2 v3 (by omega)) (q + 32) (o + 32) oEnd
      (by rw [storeU64x4LE, Model.size_storeU64x4LE]; exact hb) (by omega) (by omega) (by omega)
      hEnd (by omega)
  else xorLoop1 a hs buf q o oEnd hb ho hle hal hEnd hq
termination_by oEnd.toNat - o.toNat
decreasing_by omega

/-- Move scratch bytes `[sh, sh + 1696)` to `[0, 1696)`, front to back. -/
def moveHist (buf : ByteArray) (sh t : USize) (hb : buf.size = 18080) (hsh : sh.toNat ≤ 16384)
    (ht : t.toNat ≤ 1696) (hal : t.toNat % 32 = 0) : { b : ByteArray // b.size = 18080 } :=
  if h : t < 1696 then
    have hlt : t.toNat < 1696 := by
      have := USize.lt_iff_toNat_lt.mp h
      have e : (1696 : USize).toNat = 1696 := by simp
      omega
    have hus := usize_size_gt
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have hbs : buf.size < USize.size := by omega
    have es : (sh + t).toNat = sh.toNat + t.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have e8 : (sh + t + 8).toNat = sh.toNat + t.toNat + 8 :=
      (usize_add_toNat (sh + t) 8 (by omega)).trans (by omega)
    have e16 : (sh + t + 16).toNat = sh.toNat + t.toNat + 16 :=
      (usize_add_toNat (sh + t) 16 (by omega)).trans (by omega)
    have e24 : (sh + t + 24).toNat = sh.toNat + t.toNat + 24 :=
      (usize_add_toNat (sh + t) 24 (by omega)).trans (by omega)
    have et : (t + 32).toNat = t.toNat + 32 := usize_add_toNat t 32 (by omega)
    let w0 := loadU64LE buf (sh + t) hbs (by omega)
    let w1 := loadU64LE buf (sh + t + 8) hbs (by omega)
    let w2 := loadU64LE buf (sh + t + 16) hbs (by omega)
    let w3 := loadU64LE buf (sh + t + 24) hbs (by omega)
    moveHist (storeU64x4LE buf t w0 w1 w2 w3 (by omega)) sh (t + 32)
      (by rw [storeU64x4LE, Model.size_storeU64x4LE]; exact hb) hsh (by omega) (by omega)
  else ⟨buf, hb⟩
termination_by 1696 - t.toNat
decreasing_by omega

/-- Words in the next chunk: at most 2048. -/
@[inline] def chunkWords (rem : USize) : USize := if rem < 2048 then rem else 2048

theorem chunkWords_spec (rem : USize) (h0 : rem ≠ 0) :
    0 < (chunkWords rem).toNat ∧ (chunkWords rem).toNat ≤ 2048 ∧
      (chunkWords rem).toNat ≤ rem.toNat := by
  have e2048 : (2048 : USize).toNat = 2048 := by simp
  have hpos : 0 < rem.toNat := by
    rcases Nat.eq_zero_or_pos rem.toNat with hz | hp
    · exact absurd (USize.toNat_inj.mp (by simpa using hz)) h0
    · exact hp
  unfold chunkWords
  split
  · next hlt => have := USize.lt_iff_toNat_lt.mp hlt; omega
  · next hge => have := USize.le_iff_toNat_le.mp (USize.not_lt.mp hge); omega

/-- Reduce `rem` input words starting at `a[q]`, a chunk of at most 2048 at a time. -/
def xorChunks (a : @& ByteArray) (hs : a.size < USize.size) (buf : ByteArray) (q rem : USize)
    (hb : buf.size = 18080) (hq : q.toNat + 8 * rem.toNat ≤ a.size) :
    { b : ByteArray // b.size = 18080 } :=
  if h0 : rem = 0 then ⟨buf, hb⟩
  else
    have hk := chunkWords_spec rem h0
    have hus := usize_size_gt
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have e8 : (8 : USize).toNat = 8 := by simp
    have e1696 : (1696 : USize).toNat = 1696 := by simp
    have ek8 : (8 * chunkWords rem).toNat = 8 * (chunkWords rem).toNat := by
      rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
    have eEnd : (1696 + 8 * chunkWords rem).toNat = 1696 + 8 * (chunkWords rem).toNat := by
      rw [USize.toNat_add, ek8, e1696]; exact Nat.mod_eq_of_lt (by omega)
    have eq : (q + 8 * chunkWords rem).toNat = q.toNat + 8 * (chunkWords rem).toNat := by
      rw [USize.toNat_add, ek8]; exact Nat.mod_eq_of_lt (by omega)
    have er : (rem - chunkWords rem).toNat = rem.toNat - (chunkWords rem).toNat :=
      USize.toNat_sub_of_le rem _ (USize.le_iff_toNat_le.mpr hk.2.2)
    let b1 := xorLoop4 a hs buf q 1696 (1696 + 8 * chunkWords rem) hb (by omega) (by omega)
      (by omega) (by omega) (by omega)
    let b2 := moveHist b1.1 (8 * chunkWords rem) 0 b1.2 (by omega) (by simp) (by simp)
    xorChunks a hs b2.1 (q + 8 * chunkWords rem) (rem - chunkWords rem) b2.2 (by omega)
termination_by rem.toNat
decreasing_by omega

/-- `x ^^^ w` if `c`, else `x`. The tail loop's re-injections that are still
pending for a given word. -/
@[inline] def condXor (c : Bool) (x w : UInt64) : UInt64 := if c then x ^^^ w else x

/-- The last 209 input words, each with its pending re-injections, written in
place over scratch words `[0, 209)`. `o` is the byte offset of the current word. -/
def xorTail (a : @& ByteArray) (hs : a.size < USize.size) (buf : ByteArray) (q o : USize)
    (hb : buf.size = 18080) (ho : o.toNat ≤ 1672) (hal : o.toNat % 8 = 0)
    (hq : q.toNat + (1672 - o.toNat) ≤ a.size) : { b : ByteArray // b.size = 18080 } :=
  if h : o < 1672 then
    have hlt : o.toNat < 1672 := by
      have := USize.lt_iff_toNat_lt.mp h
      have e : (1672 : USize).toNat = 1672 := by simp
      omega
    have hus := usize_size_gt
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have hbs : buf.size < USize.size := by omega
    have e24 : (o + 24).toNat = o.toNat + 24 := usize_add_toNat o 24 (by omega)
    have e136 : (o + 136).toNat = o.toNat + 136 := usize_add_toNat o 136 (by omega)
    have e336 : (o + 336).toNat = o.toNat + 336 := usize_add_toNat o 336 (by omega)
    have e456 : (o + 456).toNat = o.toNat + 456 := usize_add_toNat o 456 (by omega)
    have e1176 : (o + 1176).toNat = o.toNat + 1176 := usize_add_toNat o 1176 (by omega)
    have eo : (o + 8).toNat = o.toNat + 8 := usize_add_toNat o 8 (by omega)
    have eq : (q + 8).toNat = q.toNat + 8 := usize_add_toNat q 8 (by omega)
    let x := condXor (o < 520) (condXor (o < 1240) (condXor (o < 1360) (condXor (o < 1560)
      (load64 a q hs (by omega) ^^^ loadU64LE buf (o + 24) hbs (by omega))
      (loadU64LE buf (o + 136) hbs (by omega))) (loadU64LE buf (o + 336) hbs (by omega)))
      (loadU64LE buf (o + 456) hbs (by omega))) (loadU64LE buf (o + 1176) hbs (by omega))
    xorTail a hs (storeU64LE buf o x (by omega)) (q + 8) (o + 8)
      (by rw [storeU64LE, Model.size_storeU64LE]; exact hb) (by omega) (by omega) (by omega)
  else ⟨buf, hb⟩
termination_by 1672 - o.toNat
decreasing_by omega

/-- Unconditioned CRC32C state update over `a[uoff, uoff + ulen)` for inputs of at
least 418 words, by the scratch-buffer kernel. -/
def rawExtendXor (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size) (uoff ulen : USize)
    (h : uoff.toNat + ulen.toNat ≤ a.size) (hbig : 3344 ≤ ulen.toNat) : UInt32 :=
  have hus := usize_size_gt
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have e8 : (8 : USize).toNat = 8 := by simp
  have e209 : (209 : USize).toNat = 209 := by simp
  let nw := ulen / 8
  have hnw : nw.toNat = ulen.toNat / 8 := by rw [USize.toNat_div, e8]
  let body := nw - 209
  have hbody : body.toNat = ulen.toNat / 8 - 209 := by
    rw [USize.toNat_sub_of_le nw 209 (USize.le_iff_toNat_le.mpr (by omega)), e209, hnw]
  have eb8 : (8 * body).toNat = 8 * body.toNat := by
    rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
  have eqt : (uoff + 8 * body).toNat = uoff.toNat + 8 * body.toNat := by
    rw [USize.toNat_add, eb8]; exact Nat.mod_eq_of_lt (by omega)
  have en8 : (8 * nw).toNat = 8 * nw.toNat := by
    rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
  have ew : (uoff + 8 * nw).toNat = uoff.toNat + 8 * nw.toNat := by
    rw [USize.toNat_add, en8]; exact Nat.mod_eq_of_lt (by omega)
  have efin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have e24 : (24 : USize).toNat = 24 := by simp
  have e0 : (0 : USize).toNat = 0 := by simp
  have e1672 : (1672 : USize).toNat = 1672 := by simp
  let b0 := storeU64LE xorZeroBuf 24 s.toUInt64 (by rw [xorZeroBuf_size, e24]; omega)
  have hb0 : b0.size = 18080 := by
    show (storeU64LE xorZeroBuf 24 s.toUInt64 _).size = 18080
    rw [storeU64LE, Model.size_storeU64LE]; exact xorZeroBuf_size
  let b1 := xorChunks a hs b0 uoff body hb0 (by omega)
  let b2 := xorTail a hs b1.1 (uoff + 8 * body) 0 b1.2 (by omega) (by simp) (by omega)
  have hb2s : b2.1.size < USize.size := by have := b2.2; omega
  let c := rawExtendPortableReg 0 b2.1 hb2s 0 1672 (by have := b2.2; omega)
  bytesLoop a (uoff + 8 * nw) (uoff + ulen) (by omega) c

/-- Unconditioned CRC32C state update over `a[uoff, uoff + ulen)`, once
`a.size < USize.size` is established: the scratch-buffer kernel from 16 KiB up
(where it is faster on the machines measured), the register kernels below. -/
@[inline] def rawExtendPortableUSize (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) : UInt32 :=
  if hx : 16384 ≤ ulen then
    rawExtendXor s a hs uoff ulen h (by
      have := USize.le_iff_toNat_le.mp hx
      have e : (16384 : USize).toNat = 16384 := by simp
      omega)
  else rawExtendPortableReg s a hs uoff ulen h

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
