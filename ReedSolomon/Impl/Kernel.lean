/-
PROTOTYPE (unproven). Reed–Solomon erasure coding over GF(2^8) with the field
polynomial `x^8 + x^4 + x^3 + x^2 + 1` (0x11D). Core-only executable code.

Shards are byte strings of a common length `L`, stored back to back in one
`ByteArray`. Shard `i` of a stripe is the value at the point `i` (the byte `i`
read as a field element) of a polynomial of degree `< k` over GF(2^8), one
polynomial per byte position. The single operation is

    interp xs ys L data : given the shards at the `k` points `xs`,
                          produce the shards at the points `ys`.

Encoding is `xs = 0..k-1`, `ys = k..n-1`; reconstruction is `xs =` any `k`
surviving shard numbers, `ys =` the missing ones.

The hot loop multiplies 8 bytes by one field constant with two carry-less
multiplies: the even bytes and the odd bytes of a word are spread into 16-bit
lanes, so the 15-bit products `byte * c` do not overlap. Products are
accumulated unreduced over the `k` input shards and reduced once per output
word (four more carry-less multiplies).
-/
import SimdModels.Trusted
import ReedSolomon.Impl.Gf

namespace ReedSolomon
open SimdModels
open SimdModels.Model (usize_add_toNat size_storeU64x4LE)

/-! ### The word kernel -/

def laneMask : UInt64 := 0x00FF00FF00FF00FF

/-- Reduce four 15-bit products in 16-bit lanes modulo the field polynomial. -/
@[inline] def red (a : UInt64) : UInt64 :=
  let t := clmulLo ((a >>> 8) &&& laneMask) 0x1d
  let u := clmulLo ((t >>> 8) &&& laneMask) 0x1d
  (a ^^^ t ^^^ u) &&& laneMask

/-- Reduce the even-byte and odd-byte accumulators and interleave them. -/
@[inline] def pack (e o : UInt64) : UInt64 := red e ||| (red o <<< 8)

@[inline] def mulE (x c : UInt64) : UInt64 := clmulLo (x &&& laneMask) c
@[inline] def mulO (x c : UInt64) : UInt64 := clmulLo ((x >>> 8) &&& laneMask) c

/-- One 32-byte block of one output shard: accumulate `c[i] * shard i` over the
input shards `i, i+1, …, k-1` (`p` is the byte offset of the block in shard `i`,
`cp` the offset of `c[i]`), then reduce and store at `dst`. -/
def block (data coef : @& ByteArray) (out : ByteArray) (hs : data.size < USize.size)
    (L k i p cp dst : USize) (hi : i.toNat < k.toNat)
    (hd : k.toNat * L.toNat ≤ data.size)
    (hp : ∃ w, p.toNat = i.toNat * L.toNat + w ∧ w + 32 ≤ L.toNat)
    (hc : cp.toNat + (k.toNat - i.toNat) ≤ coef.size) (hcs : coef.size < USize.size)
    (hdst : dst.toNat + 32 ≤ out.size)
    (e0 o0 e1 o1 e2 o2 e3 o3 : UInt64) : { b : ByteArray // b.size = out.size } :=
  have hin : p.toNat + 32 ≤ data.size ∧ (i.toNat + 1) * L.toNat ≤ data.size := by
    obtain ⟨w, h1, h2⟩ := hp
    have : (i.toNat + 1) * L.toNat ≤ k.toNat * L.toNat := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul] at this ⊢
    omega
  have a1 : (p + 8).toNat = p.toNat + 8 := usize_add_toNat p 8 (by omega)
  have a2 : (p + 16).toNat = p.toNat + 16 := usize_add_toNat p 16 (by omega)
  have a3 : (p + 24).toNat = p.toNat + 24 := usize_add_toNat p 24 (by omega)
  let c := (loadU8 coef cp (by omega)).toUInt64
  let x0 := loadU64LE data p hs (by omega)
  let x1 := loadU64LE data (p + 8) hs (by omega)
  let x2 := loadU64LE data (p + 16) hs (by omega)
  let x3 := loadU64LE data (p + 24) hs (by omega)
  let e0 := e0 ^^^ mulE x0 c
  let o0 := o0 ^^^ mulO x0 c
  let e1 := e1 ^^^ mulE x1 c
  let o1 := o1 ^^^ mulO x1 c
  let e2 := e2 ^^^ mulE x2 c
  let o2 := o2 ^^^ mulO x2 c
  let e3 := e3 ^^^ mulE x3 c
  let o3 := o3 ^^^ mulO x3 c
  have ei : (i + 1).toNat = i.toNat + 1 := usize_add_toNat i 1 (by have := k.toNat_lt_size; omega)
  if h' : i + 1 < k then
    have h : i.toNat + 1 < k.toNat := by rw [← ei]; exact USize.lt_iff_toNat_lt.mp h'
    have ec : (cp + 1).toNat = cp.toNat + 1 := usize_add_toNat cp 1 (by omega)
    have hL : (i.toNat + 2) * L.toNat ≤ data.size := by
      have : (i.toNat + 2) * L.toNat ≤ k.toNat * L.toNat := Nat.mul_le_mul_right _ h
      omega
    have ep : (p + L).toNat = p.toNat + L.toNat := by
      obtain ⟨w, h1, h2⟩ := hp
      rw [USize.toNat_add]
      apply Nat.mod_eq_of_lt
      show _ < USize.size
      rw [Nat.add_mul] at hL
      omega
    block data coef out hs L k (i + 1) (p + L) (cp + 1) dst (by rw [ei]; omega) hd
      (by obtain ⟨w, h1, h2⟩ := hp
          exact ⟨w, by rw [ep, ei, h1, Nat.add_mul]; omega, h2⟩)
      (by rw [ec, ei]; omega) hcs hdst e0 o0 e1 o1 e2 o2 e3 o3
  else
    ⟨storeU64x4LE out dst (pack e0 o0) (pack e1 o1) (pack e2 o2) (pack e3 o3) hdst,
      size_storeU64x4LE ..⟩
termination_by k.toNat - i.toNat
decreasing_by rw [ei]; omega

/-- The 32-byte block at offset `w` of the output shards `j, …, r-1`
(`cp = j * k` is the coefficient row, `dst = j * L + w` the output offset). -/
def col (data coef : @& ByteArray) (out : ByteArray) (hs : data.size < USize.size)
    (L k r w j cp dst : USize) (hk : 0 < k.toNat) (hd : k.toNat * L.toNat ≤ data.size)
    (hw : w.toNat + 32 ≤ L.toNat) (hcs : coef.size < USize.size) (hos : out.size < USize.size)
    (hj : j.toNat < r.toNat) (hcp : cp.toNat = j.toNat * k.toNat)
    (hc : r.toNat * k.toNat ≤ coef.size) (hdp : dst.toNat = j.toNat * L.toNat + w.toNat)
    (ho : r.toNat * L.toNat ≤ out.size) : { b : ByteArray // b.size = out.size } :=
  have h1 : (j.toNat + 1) * k.toNat ≤ r.toNat * k.toNat := Nat.mul_le_mul_right _ hj
  have h2 : (j.toNat + 1) * L.toNat ≤ r.toNat * L.toNat := Nat.mul_le_mul_right _ hj
  let o := block data coef out hs L k 0 w cp dst hk hd ⟨w.toNat, by simp, hw⟩
    (by rw [Nat.add_mul] at h1; simp; omega) hcs (by rw [Nat.add_mul] at h2; omega)
    0 0 0 0 0 0 0 0
  have ej : (j + 1).toNat = j.toNat + 1 := usize_add_toNat j 1 (by have := r.toNat_lt_size; omega)
  if h' : j + 1 < r then
    have h : j.toNat + 1 < r.toNat := by rw [← ej]; exact USize.lt_iff_toNat_lt.mp h'
    have h3 : (j.toNat + 2) * k.toNat ≤ r.toNat * k.toNat := Nat.mul_le_mul_right _ h
    have h4 : (j.toNat + 2) * L.toNat ≤ r.toNat * L.toNat := Nat.mul_le_mul_right _ h
    have ec : (cp + k).toNat = cp.toNat + k.toNat := by
      rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; show _ < USize.size
      rw [Nat.add_mul] at h3; omega
    have ed : (dst + L).toNat = dst.toNat + L.toNat := by
      rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; show _ < USize.size
      rw [Nat.add_mul] at h4; omega
    let o2 := col data coef o.1 hs L k r w (j + 1) (cp + k) (dst + L) hk hd hw hcs
      (by rw [o.2]; exact hos) (by rw [ej]; exact h) (by rw [ec, ej, hcp, Nat.add_mul]; omega) hc
      (by rw [ed, ej, hdp, Nat.add_mul]; omega) (by rw [o.2]; exact ho)
    ⟨o2.1, o2.2.trans o.2⟩
  else o
termination_by r.toNat - j.toNat
decreasing_by rw [ej]; omega

/-- All 32-byte blocks `[w, wEnd)` of every output shard. -/
def cols (data coef : @& ByteArray) (out : ByteArray) (hs : data.size < USize.size)
    (L k r w wEnd : USize) (hk : 0 < k.toNat) (hr : 0 < r.toNat)
    (hd : k.toNat * L.toNat ≤ data.size) (hc : r.toNat * k.toNat ≤ coef.size)
    (hcs : coef.size < USize.size) (hw : wEnd.toNat ≤ L.toNat)
    (hal : (wEnd.toNat - w.toNat) % 32 = 0) (ho : r.toNat * L.toNat ≤ out.size)
    (hos : out.size < USize.size) : { b : ByteArray // b.size = out.size } :=
  if h' : w < wEnd then
    have h : w.toNat < wEnd.toNat := USize.lt_iff_toNat_lt.mp h'
    have ew : (w + 32).toNat = w.toNat + 32 :=
      usize_add_toNat w 32 (by have := wEnd.toNat_lt_size; omega)
    let o := col data coef out hs L k r w 0 0 w hk hd (by omega) hcs hos hr (by simp) hc
      (by simp) ho
    let o2 := cols data coef o.1 hs L k r (w + 32) wEnd hk hr hd hc hcs hw (by omega)
      (by rw [o.2]; exact ho) (by rw [o.2]; exact hos)
    ⟨o2.1, o2.2.trans o.2⟩
  else ⟨out, rfl⟩
termination_by wEnd.toNat - w.toNat
decreasing_by rw [ew]; omega

/-- Byte-at-a-time fallback for byte positions `[w0, L)` of every output shard. -/
def tailBytes (data coef : ByteArray) (out : ByteArray) (L k r w0 : Nat) : ByteArray := Id.run do
  let mut out := out
  for j in [0:r] do
    for w in [w0:L] do
      let mut acc : UInt8 := 0
      for i in [0:k] do
        acc := acc ^^^ gfMul coef[j * k + i]! data[i * L + w]!
      out := out.set! (j * L + w) acc
  return out

/-- Apply an `r × k` coefficient matrix to `k` shards of length `L`. The result
overwrites the first `r * L` bytes of `out` (in place if `out` is unshared).
Returns the input unchanged if the sizes are inconsistent. -/
def apply (coef : ByteArray) (k r L : Nat) (data : ByteArray) (out : ByteArray) : ByteArray :=
  let wEnd := L / 32 * 32
  if h : data.size < USize.size ∧ coef.size < USize.size ∧ 0 < k.toUSize.toNat ∧
      0 < r.toUSize.toNat ∧ k.toUSize.toNat * L.toUSize.toNat ≤ data.size ∧
      r.toUSize.toNat * k.toUSize.toNat ≤ coef.size ∧
      wEnd.toUSize.toNat ≤ L.toUSize.toNat ∧ wEnd.toUSize.toNat % 32 = 0 ∧
      r.toUSize.toNat * L.toUSize.toNat ≤ out.size ∧ out.size < USize.size ∧
      k * L = data.size then
    let o := cols data coef out h.1 L.toUSize k.toUSize r.toUSize 0 wEnd.toUSize h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.1 h.2.2.2.2.2.2.1 (by simpa using h.2.2.2.2.2.2.2.1)
      h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1
    tailBytes data coef o.1 L k r wEnd
  else data

/-- `n` zero bytes, by doubling (core has no `ByteArray.replicate`). -/
def zeros (n : Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ⟨#[0]⟩
  while b.size < n do b := b ++ b
  return b.extract 0 n

/-- Shards at the points `ys` from the `xs.size` shards of length `L` at the
points `xs`. -/
def interp (xs ys : ByteArray) (L : Nat) (data : ByteArray) : ByteArray :=
  apply (coeffs xs ys) xs.size ys.size L data (zeros (ys.size * L))

/-- The portable path of the C library (`cxx/leanrs.cc`): `r` output shards of
length `L` from the `k` input shards stored back to back in `data`, for the
row-major `r × k` coefficient matrix `coef`. Uses the carry-less-multiply
kernel when the CPU has it, the byte-at-a-time code otherwise. -/
@[export leanrs_apply_portable_lean]
def applyPortable (coef data : ByteArray) (k r L : USize) : ByteArray :=
  if cpuHasCrcClmul () then apply coef k.toNat r.toNat L.toNat data (zeros (r.toNat * L.toNat))
  else tailBytes data coef (zeros (r.toNat * L.toNat)) L.toNat k.toNat r.toNat 0

end ReedSolomon
