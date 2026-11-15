/-
The hardware-CRC + carry-less-multiply path, written in Lean against the eight
trusted data-path bindings of `lean-simd-models` (`crc32c_u8/16/32/64`,
`clmulLo`, `clmulHi`, `loadU8`, `loadU64LE`). Core-only executable code; proven
equal to the reference in `MemcpyCrc32c.HwKernel`.

Three length regimes keep every pipeline fed without wasting setup work on
short buffers:
- `< 96 B`: inline leaf path — 2×-unrolled `crc32c_u64` (16 B/iter) followed by
  a loop-free `8/4/2/1`-byte hardware tail (`crc32c_u64/u32/u16/u8`), with
  multi-stream helpers outlined so short calls have zero register spills.
- `96 B .. 767 B`: three interleaved `crc32c_u64` streams (48 B/iter), combined
  in hardware via `hwMul` (`clmulLo` + `crc32c_u64`) and a 2 KiB table lookup.
- `≥ 768 B`: six interleaved streams (`384 B/iter`) — three 64-byte `crc32c_u64`
  streams on the integer CRC unit in parallel with three 64-byte multi-block
  `clmulLo`/`clmulHi` dot-product folding streams on the SIMD units, finished
  with `crc32c_u64`, tree-combined via `hwMul`, and completed via the 3-stream
  or single-stream tail.

All module-level constants and tables are computed with portable scalar
arithmetic (`powMod`/`mulMod`), so module initialization never executes
hardware CRC or carry-less-multiply instructions. Callers must dispatch to
`extendHw` / `rawExtendHw` only on CPUs that support the instructions.
-/
import MemcpyCrc32c.Impl.HwCombine

namespace Crc32c
open SimdModels (crc32c_u8 crc32c_u16 crc32c_u32 crc32c_u64 clmulLo clmulHi loadU8 loadU64LE)

/-! ### 16-byte / 64-byte load, CRC, and carry-less-multiply folding helpers -/

/-- Absorb 16 little-endian bytes (`p` and `p + 8`) with two `crc32c_u64` steps. -/
@[inline] def crc128 (a : @& ByteArray) (hs : a.size < USize.size) (p : USize)
    (hp : p.toNat + 16 ≤ a.size) (s : UInt32) : UInt32 :=
  have hp8 : (p + 8).toNat = p.toNat + 8 := usize_add_toNat p 8 (by omega)
  have hb0 : p.toNat + 8 ≤ a.size := by omega
  have hb1 : (p + 8).toNat + 8 ≤ a.size := by omega
  let w0 := loadU64LE a p hs hb0
  let w1 := loadU64LE a (p + 8) hs hb1
  crc32c_u64 (crc32c_u64 s w0) w1

/-- Absorb 64 little-endian bytes (`p .. p + 64`) with four `crc128` steps (`8 × crc32c_u64`). -/
@[inline] def crc512 (a : @& ByteArray) (hs : a.size < USize.size) (p : USize)
    (hp : p.toNat + 64 ≤ a.size) (s : UInt32) : UInt32 :=
  have hp16 : (p + 16).toNat = p.toNat + 16 := usize_add_toNat p 16 (by omega)
  have hp32 : (p + 32).toNat = p.toNat + 32 := usize_add_toNat p 32 (by omega)
  have hp48 : (p + 48).toNat = p.toNat + 48 := usize_add_toNat p 48 (by omega)
  let s := crc128 a hs p (by omega) s
  let s := crc128 a hs (p + 16) (by omega) s
  let s := crc128 a hs (p + 32) (by omega) s
  crc128 a hs (p + 48) (by omega) s

/-- Load the high 64-bit half (`p + 8`) of a 16-byte block at `p`. -/
@[inline] def load64Hi (a : @& ByteArray) (hs : a.size < USize.size) (p : USize)
    (hp : p.toNat + 16 ≤ a.size) : UInt64 :=
  have hp8 : (p + 8).toNat = p.toNat + 8 := usize_add_toNat p 8 (by omega)
  loadU64LE a (p + 8) hs (by omega)

/-- Load all eight 64-bit little-endian words of a 64-byte chunk `a[p, p + 64)`
and pass them unboxed to continuation `k`. Inlined before LCNF tail-call lowering,
so recursive tail calls inside `k` compile to flat C `goto _start` loops with zero
closures and zero duplicate bounds proofs. -/
@[inline] def withBlock512 {α : Type} (a : @& ByteArray) (hs : a.size < USize.size) (p : USize)
    (hp : p.toNat + 64 ≤ a.size)
    (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  have hp16 : (p + 16).toNat = p.toNat + 16 := usize_add_toNat p 16 (by omega)
  have hp32 : (p + 32).toNat = p.toNat + 32 := usize_add_toNat p 32 (by omega)
  have hp48 : (p + 48).toNat = p.toNat + 48 := usize_add_toNat p 48 (by omega)
  k (loadU64LE a p hs (by omega))
    (load64Hi a hs p (by omega))
    (loadU64LE a (p + 16) hs (by omega))
    (load64Hi a hs (p + 16) (by omega))
    (loadU64LE a (p + 32) hs (by omega))
    (load64Hi a hs (p + 32) (by omega))
    (loadU64LE a (p + 48) hs (by omega))
    (load64Hi a hs (p + 48) (by omega))

/-- Low 64-bit half of folding `(lo, hi)` forward onto `nlo` with constants `(k1, k2)`. -/
@[inline] def fold128Lo (lo hi nlo k1 k2 : UInt64) : UInt64 :=
  nlo ^^^ clmulLo lo k1 ^^^ clmulLo hi k2

/-- High 64-bit half of folding `(lo, hi)` forward onto `nhi` with constants `(k1, k2)`. -/
@[inline] def fold128Hi (lo hi nhi k1 k2 : UInt64) : UInt64 :=
  nhi ^^^ clmulHi lo k1 ^^^ clmulHi hi k2

/-- Low 64-bit half of reducing four 128-bit blocks `(w0,w1)`, `(w2,w3)`, `(w4,w5)`, `(u0,u1)`
to a single 128-bit residue at the end of a 64-byte chunk. -/
@[inline] def init512Lo (w0 w1 w2 w3 w4 w5 u0 : UInt64) : UInt64 :=
  let u0 := fold128Lo w0 w1 u0 kFold384_1 kFold384_2
  let u0 := fold128Lo w2 w3 u0 kFold256_1 kFold256_2
  fold128Lo w4 w5 u0 kFold128_1 kFold128_2

/-- High 64-bit half of reducing four 128-bit blocks `(w0,w1)`, `(w2,w3)`, `(w4,w5)`, `(u0,u1)`
to a single 128-bit residue at the end of a 64-byte chunk. -/
@[inline] def init512Hi (w0 w1 w2 w3 w4 w5 u1 : UInt64) : UInt64 :=
  let u1 := fold128Hi w0 w1 u1 kFold384_1 kFold384_2
  let u1 := fold128Hi w2 w3 u1 kFold256_1 kFold256_2
  fold128Hi w4 w5 u1 kFold128_1 kFold128_2

/-- Low 64-bit half of advancing `(x0, x1)` across a 64-byte chunk `(w0..w7)` (`512` bits). -/
@[inline] def fold512Lo (x0 x1 w0 w1 w2 w3 w4 w5 w6 : UInt64) : UInt64 :=
  init512Lo w0 w1 w2 w3 w4 w5 (fold128Lo x0 x1 w6 kFold512_1 kFold512_2)

/-- High 64-bit half of advancing `(x0, x1)` across a 64-byte chunk `(w0..w7)` (`512` bits). -/
@[inline] def fold512Hi (x0 x1 w0 w1 w2 w3 w4 w5 w7 : UInt64) : UInt64 :=
  init512Hi w0 w1 w2 w3 w4 w5 (fold128Hi x0 x1 w7 kFold512_1 kFold512_2)

/-- Reduce a 128-bit reflected accumulator `(lo, hi)` to its 32-bit CRC residue. -/
@[inline] def finish128 (lo hi : UInt64) : UInt32 :=
  crc32c_u64 (crc32c_u64 0 lo) hi

/-! ### Single-stream loop (`16 B/iter`) and loop-free `8/4/2/1` hardware tail -/

/-- Absorb at most 1 remaining byte (`fin - i ≤ 1`) with `crc32c_u8`. -/
@[inline] def hwTail1 (a : @& ByteArray) (i fin : USize) (hfin : fin.toNat ≤ a.size)
    (s : UInt32) : UInt32 :=
  if h1 : i < fin then
    crc32c_u8 s (loadU8 a i (by have := USize.lt_iff_toNat_lt.mp h1; omega))
  else s

/-- Absorb `< 4` remaining bytes via optional `crc32c_u16` + `hwTail1`. -/
@[inline] def hwTail2 (a : @& ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) (s : UInt32) : UInt32 :=
  if h2 : 2 ≤ fin - i then
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have h2' : 2 ≤ fin.toNat - i.toNat := by
      have := USize.le_iff_toNat_le.mp h2
      have e2 : (2 : USize).toNat = 2 := by simp
      omega
    have hi2 : (i + 2).toNat = i.toNat + 2 := usize_add_toNat i 2 (by omega)
    have hb : i.toNat + 2 ≤ a.size := by omega
    hwTail1 a (i + 2) fin hfin (crc32c_u16 s (load16 a i hs hb))
  else
    hwTail1 a i fin hfin s

/-- Absorb `< 8` remaining bytes via optional `crc32c_u32` + `hwTail2`. -/
@[inline] def hwTail4 (a : @& ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) (s : UInt32) : UInt32 :=
  if h4 : 4 ≤ fin - i then
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have h4' : 4 ≤ fin.toNat - i.toNat := by
      have := USize.le_iff_toNat_le.mp h4
      have e4 : (4 : USize).toNat = 4 := by simp
      omega
    have hi4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat i 4 (by omega)
    have hle : (i + 4).toNat ≤ fin.toNat := by omega
    have hb : i.toNat + 4 ≤ a.size := by omega
    hwTail2 a hs (i + 4) fin hle hfin (crc32c_u32 s (load32 a i hs hb))
  else
    hwTail2 a hs i fin hi hfin s

/-- Absorb `< 16` remaining bytes via optional `crc32c_u64` + `hwTail4`. -/
@[inline] def hwTail8 (a : @& ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) (s : UInt32) : UInt32 :=
  if h8 : 8 ≤ fin - i then
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have h8' : 8 ≤ fin.toNat - i.toNat := by
      have := USize.le_iff_toNat_le.mp h8
      have e8 : (8 : USize).toNat = 8 := by simp
      omega
    have hi8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
    have hle : (i + 8).toNat ≤ fin.toNat := by omega
    have hb : i.toNat + 8 ≤ a.size := by omega
    hwTail4 a hs (i + 8) fin hle hfin (crc32c_u64 s (loadU64LE a i hs hb))
  else
    hwTail4 a hs i fin hi hfin s

/-- Single stream over `a[i, fin)`: 16 bytes per iteration (`ldp` + two `crc32c_u64`),
then loop-free `8/4/2/1` tail. -/
def hwLoop (a : @& ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) (s : UInt32) : UInt32 :=
  if h16 : 16 ≤ fin - i then
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have h16' : 16 ≤ fin.toNat - i.toNat := by
      have := USize.le_iff_toNat_le.mp h16
      have e16 : (16 : USize).toNat = 16 := by simp
      omega
    have hi16 : (i + 16).toNat = i.toNat + 16 := usize_add_toNat i 16 (by omega)
    have hle : (i + 16).toNat ≤ fin.toNat := by omega
    have hb : i.toNat + 16 ≤ a.size := by omega
    hwLoop a hs (i + 16) fin hle hfin (crc128 a hs i hb s)
  else
    hwTail8 a hs i fin hi hfin s
termination_by fin.toNat - i.toNat
decreasing_by omega

/-! ### Three-stream `CRC32CX` kernel (`48 B/iter`) -/

/-- Three interleaved `crc32c_u64` streams `a[i + r·L, stop + r·L)` (`r = 0, 1, 2`),
16 bytes per stream per iteration (`48 B/iter`), combined via `combine3`. -/
def hwFold3 (a : @& ByteArray) (hs : a.size < USize.size) (i stop ws L L2 : USize)
    (_hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 16 = 0)
    (hL2 : L2.toNat = 2 * L.toNat) (hL : stop.toNat + 2 * L.toNat ≤ a.size)
    (s0 s1 s2 : UInt32) : UInt32 :=
  if hlt : i < stop then
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have h16le : i.toNat + 16 ≤ stop.toNat := by
      have := USize.lt_iff_toNat_lt.mp hlt; omega
    have h16 : (i + 16).toNat = i.toNat + 16 := usize_add_toNat i 16 (by omega)
    have hi1 : (i + L).toNat = i.toNat + L.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
      rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
    have hle : (i + 16).toNat ≤ stop.toNat := by omega
    have hal' : (stop.toNat - (i + 16).toNat) % 16 = 0 := by omega
    have hb0 : i.toNat + 16 ≤ a.size := by omega
    have hb1 : (i + L).toNat + 16 ≤ a.size := by omega
    have hb2 : (i + L2).toNat + 16 ≤ a.size := by omega
    hwFold3 a hs (i + 16) stop ws L L2 hle hal' hL2 hL
      (crc128 a hs i hb0 s0)
      (crc128 a hs (i + L) hb1 s1)
      (crc128 a hs (i + L2) hb2 s2)
  else
    combine3 ws s0 s1 s2
termination_by stop.toNat - i.toNat
decreasing_by omega

/-- Three-stream `CRC32CX` range update (`48 B/iter` + `hwLoop` tail) for `96 ≤ ulen`. -/
@[inline] def rawExtendHw3 (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) (h96 : 96 ≤ ulen) : UInt32 :=
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have e96 : (96 : USize).toNat = 96 := by simp
  have h96' : 96 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h96; omega
  have e48 : (48 : USize).toNat = 48 := by simp
  have e16 : (16 : USize).toNat = 16 := by simp
  have e3 : (3 : USize).toNat = 3 := by simp
  have e2 : (2 : USize).toNat = 2 := by simp
  have hblocks : (ulen / 48).toNat = ulen.toNat / 48 := by rw [USize.toNat_div, e48]
  have hL : (ulen / 48 * 16).toNat = (ulen / 48).toNat * 16 := by
    rw [USize.toNat_mul, e16]; exact Nat.mod_eq_of_lt (by omega)
  have hL2 : (2 * (ulen / 48 * 16)).toNat = 2 * (ulen / 48 * 16).toNat := by
    rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hL3 : (3 * (ulen / 48 * 16)).toNat = 3 * (ulen / 48 * 16).toNat := by
    rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
  have hstop : (uoff + ulen / 48 * 16).toNat = uoff.toNat + (ulen / 48 * 16).toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have htail : (uoff + 3 * (ulen / 48 * 16)).toNat = uoff.toNat + 3 * (ulen / 48 * 16).toNat := by
    rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
  have hle_f3 : uoff.toNat ≤ (uoff + ulen / 48 * 16).toNat := by omega
  have hal_f3 : ((uoff + ulen / 48 * 16).toNat - uoff.toNat) % 16 = 0 := by omega
  have hL_f3 : (uoff + ulen / 48 * 16).toNat + 2 * (ulen / 48 * 16).toNat ≤ a.size := by omega
  have hle_tail : (uoff + 3 * (ulen / 48 * 16)).toNat ≤ (uoff + ulen).toNat := by omega
  have hfin_sz : (uoff + ulen).toNat ≤ a.size := by omega
  let blocks := ulen / 48
  let ws := blocks * 2
  let L := blocks * 16
  let L2 := 2 * L
  let L3 := 3 * L
  let s3 := hwFold3 a hs uoff (uoff + L) ws L L2 hle_f3 hal_f3 hL2 hL_f3 s 0 0
  hwLoop a hs (uoff + L3) (uoff + ulen) hle_tail hfin_sz s3

/-! ### Six-stream hybrid `3 × CRC32CX + 3 × PMULL` dot-product kernel (`384 B/iter`) -/

/-- Inner loop for `hwFold6`: advances three `crc32c_u64` streams (`r = 0, 1, 2`)
and three 64-byte `clmulLo`/`clmulHi` dot-product streams (`r = 3, 4, 5`) by 64 bytes
each per iteration (`384 B/iter`). Updating each `(lo, hi)` accumulator once per
64-byte chunk hides the GPR↔SIMD cross-domain latency behind 24 `CRC32CX` instructions
and multiplies memory words directly from SIMD loads without GPR round-trips. -/
def hwFold6Loop (a : @& ByteArray) (hs : a.size < USize.size)
    (i stop ws L L2 L3 L4 L5 : USize)
    (_hi : i.toNat ≤ stop.toNat) (hal : (stop.toNat - i.toNat) % 64 = 0)
    (hL2 : L2.toNat = 2 * L.toNat) (hL3 : L3.toNat = 3 * L.toNat)
    (hL4 : L4.toNat = 4 * L.toNat) (hL5 : L5.toNat = 5 * L.toNat)
    (hL : stop.toNat + 5 * L.toNat ≤ a.size)
    (s0 s1 s2 : UInt32)
    (a0 a1 b0 b1 c0 c1 : UInt64) : UInt32 :=
  if hlt : i < stop then
    have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
    have h64le : i.toNat + 64 ≤ stop.toNat := by
      have := USize.lt_iff_toNat_lt.mp hlt; omega
    have h64 : (i + 64).toNat = i.toNat + 64 := usize_add_toNat i 64 (by omega)
    have hi1 : (i + L).toNat = i.toNat + L.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hi2 : (i + L2).toNat = i.toNat + 2 * L.toNat := by
      rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
    have hi3 : (i + L3).toNat = i.toNat + 3 * L.toNat := by
      rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
    have hi4 : (i + L4).toNat = i.toNat + 4 * L.toNat := by
      rw [USize.toNat_add, hL4]; exact Nat.mod_eq_of_lt (by omega)
    have hi5 : (i + L5).toNat = i.toNat + 5 * L.toNat := by
      rw [USize.toNat_add, hL5]; exact Nat.mod_eq_of_lt (by omega)
    have hle : (i + 64).toNat ≤ stop.toNat := by omega
    have hal' : (stop.toNat - (i + 64).toNat) % 64 = 0 := by omega
    have hc0 : i.toNat + 64 ≤ a.size := by omega
    have hc1 : (i + L).toNat + 64 ≤ a.size := by omega
    have hc2 : (i + L2).toNat + 64 ≤ a.size := by omega
    have hc3 : (i + L3).toNat + 64 ≤ a.size := by omega
    have hc4 : (i + L4).toNat + 64 ≤ a.size := by omega
    have hc5 : (i + L5).toNat + 64 ≤ a.size := by omega
    let ns0 := crc512 a hs i hc0 s0
    let ns1 := crc512 a hs (i + L) hc1 s1
    let ns2 := crc512 a hs (i + L2) hc2 s2
    withBlock512 a hs (i + L3) hc3 fun w30 w31 w32 w33 w34 w35 w36 w37 =>
    withBlock512 a hs (i + L4) hc4 fun w40 w41 w42 w43 w44 w45 w46 w47 =>
    withBlock512 a hs (i + L5) hc5 fun w50 w51 w52 w53 w54 w55 w56 w57 =>
    hwFold6Loop a hs (i + 64) stop ws L L2 L3 L4 L5 hle hal' hL2 hL3 hL4 hL5 hL
      ns0 ns1 ns2
      (fold512Lo a0 a1 w30 w31 w32 w33 w34 w35 w36)
      (fold512Hi a0 a1 w30 w31 w32 w33 w34 w35 w37)
      (fold512Lo b0 b1 w40 w41 w42 w43 w44 w45 w46)
      (fold512Hi b0 b1 w40 w41 w42 w43 w44 w45 w47)
      (fold512Lo c0 c1 w50 w51 w52 w53 w54 w55 w56)
      (fold512Hi c0 c1 w50 w51 w52 w53 w54 w55 w57)
  else
    let s3 := finish128 a0 a1
    let s4 := finish128 b0 b1
    let s5 := finish128 c0 c1
    combine6 ws s0 s1 s2 s3 s4 s5
termination_by stop.toNat - i.toNat
decreasing_by omega

/-- Six-stream hybrid entry over `blocks * 384` contiguous bytes starting at `uoff`
(`1 ≤ blocks`, `L = blocks * 64` bytes per stream, `ws = blocks * 8` words per stream). -/
@[noinline] def hwFold6 (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size)
    (uoff blocks : USize) (hb : 1 ≤ blocks.toNat)
    (h : uoff.toNat + blocks.toNat * 384 ≤ a.size) : UInt32 :=
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have e64 : (64 : USize).toNat = 64 := by simp
  have e8 : (8 : USize).toNat = 8 := by simp
  have e5 : (5 : USize).toNat = 5 := by simp
  have e4 : (4 : USize).toNat = 4 := by simp
  have e3 : (3 : USize).toNat = 3 := by simp
  have e2 : (2 : USize).toNat = 2 := by simp
  have hL : (blocks * 64).toNat = blocks.toNat * 64 := by
    rw [USize.toNat_mul, e64]; exact Nat.mod_eq_of_lt (by omega)
  have hL2 : (2 * (blocks * 64)).toNat = 2 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e2]; exact Nat.mod_eq_of_lt (by omega)
  have hL3 : (3 * (blocks * 64)).toNat = 3 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e3]; exact Nat.mod_eq_of_lt (by omega)
  have hL4 : (4 * (blocks * 64)).toNat = 4 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e4]; exact Nat.mod_eq_of_lt (by omega)
  have hL5 : (5 * (blocks * 64)).toNat = 5 * (blocks * 64).toNat := by
    rw [USize.toNat_mul, e5]; exact Nat.mod_eq_of_lt (by omega)
  have hu64 : (uoff + 64).toNat = uoff.toNat + 64 := usize_add_toNat uoff 64 (by omega)
  have hstop : (uoff + blocks * 64).toNat = uoff.toNat + (blocks * 64).toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hp2 : (uoff + 2 * (blocks * 64)).toNat = uoff.toNat + 2 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL2]; exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (uoff + 3 * (blocks * 64)).toNat = uoff.toNat + 3 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL3]; exact Nat.mod_eq_of_lt (by omega)
  have hp4 : (uoff + 4 * (blocks * 64)).toNat = uoff.toNat + 4 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL4]; exact Nat.mod_eq_of_lt (by omega)
  have hp5 : (uoff + 5 * (blocks * 64)).toNat = uoff.toNat + 5 * (blocks * 64).toNat := by
    rw [USize.toNat_add, hL5]; exact Nat.mod_eq_of_lt (by omega)
  have hle : (uoff + 64).toNat ≤ (uoff + blocks * 64).toNat := by omega
  have hal : ((uoff + blocks * 64).toNat - (uoff + 64).toNat) % 64 = 0 := by omega
  have hLend : (uoff + blocks * 64).toNat + 5 * (blocks * 64).toNat ≤ a.size := by omega
  have hc0 : uoff.toNat + 64 ≤ a.size := by omega
  have hc1 : (uoff + blocks * 64).toNat + 64 ≤ a.size := by omega
  have hc2 : (uoff + 2 * (blocks * 64)).toNat + 64 ≤ a.size := by omega
  have hc3 : (uoff + 3 * (blocks * 64)).toNat + 64 ≤ a.size := by omega
  have hc4 : (uoff + 4 * (blocks * 64)).toNat + 64 ≤ a.size := by omega
  have hc5 : (uoff + 5 * (blocks * 64)).toNat + 64 ≤ a.size := by omega
  let ws := blocks * 8
  let L := blocks * 64
  let L2 := 2 * L
  let L3 := 3 * L
  let L4 := 4 * L
  let L5 := 5 * L
  let s0 := crc512 a hs uoff hc0 s
  let s1 := crc512 a hs (uoff + L) hc1 0
  let s2 := crc512 a hs (uoff + L2) hc2 0
  withBlock512 a hs (uoff + L3) hc3 fun w30 w31 w32 w33 w34 w35 w36 w37 =>
  withBlock512 a hs (uoff + L4) hc4 fun w40 w41 w42 w43 w44 w45 w46 w47 =>
  withBlock512 a hs (uoff + L5) hc5 fun w50 w51 w52 w53 w54 w55 w56 w57 =>
  hwFold6Loop a hs (uoff + 64) (uoff + L) ws L L2 L3 L4 L5
    hle hal hL2 hL3 hL4 hL5 hLend s0 s1 s2
    (init512Lo w30 w31 w32 w33 w34 w35 w36)
    (init512Hi w30 w31 w32 w33 w34 w35 w37)
    (init512Lo w40 w41 w42 w43 w44 w45 w46)
    (init512Hi w40 w41 w42 w43 w44 w45 w47)
    (init512Lo w50 w51 w52 w53 w54 w55 w56)
    (init512Hi w50 w51 w52 w53 w54 w55 w57)

/-! ### Multi-stream and top-level dispatch -/

/-- Outlined multi-stream handler for `96 ≤ ulen`, keeping `< 96 B` calls in
`rawExtendHwUSize` / `extendHw` free of callee-saved register spills. -/
@[noinline] def rawExtendHwMulti (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) (h96 : 96 ≤ ulen) : UInt32 :=
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  if h768 : 768 ≤ ulen then
    have e768 : (768 : USize).toNat = 768 := by simp
    have h768' : 768 ≤ ulen.toNat := by have := USize.le_iff_toNat_le.mp h768; omega
    have e384 : (384 : USize).toNat = 384 := by simp
    have hblocks : (ulen / 384).toNat = ulen.toNat / 384 := by rw [USize.toNat_div, e384]
    have hcons : (ulen / 384 * 384).toNat = (ulen / 384).toNat * 384 := by
      rw [USize.toNat_mul, e384]; exact Nat.mod_eq_of_lt (by omega)
    have htail : (uoff + ulen / 384 * 384).toNat = uoff.toNat + (ulen / 384).toNat * 384 := by
      rw [USize.toNat_add, hcons]; exact Nat.mod_eq_of_lt (by omega)
    have hrem : (ulen - ulen / 384 * 384).toNat = ulen.toNat - (ulen / 384).toNat * 384 := by
      rw [USize.toNat_sub_of_le ulen (ulen / 384 * 384)
        (USize.le_iff_toNat_le.mpr (by omega)), hcons]
    have hb1 : 1 ≤ (ulen / 384).toNat := by omega
    have hb_sz : uoff.toNat + (ulen / 384).toNat * 384 ≤ a.size := by omega
    have hrem_sz : (uoff + ulen / 384 * 384).toNat + (ulen - ulen / 384 * 384).toNat ≤ a.size := by omega
    have hle_tail : (uoff + ulen / 384 * 384).toNat ≤ (uoff + ulen).toNat := by omega
    have hfin_sz : (uoff + ulen).toNat ≤ a.size := by omega
    let blocks := ulen / 384
    let consumed := blocks * 384
    let rem := ulen - consumed
    let s6 := hwFold6 s a hs uoff blocks hb1 hb_sz
    if hrem96 : 96 ≤ rem then
      rawExtendHw3 s6 a hs (uoff + consumed) rem hrem_sz hrem96
    else
      hwLoop a hs (uoff + consumed) (uoff + ulen) hle_tail hfin_sz s6
  else
    rawExtendHw3 s a hs uoff ulen h h96

/-- Fast entry once `a.size < USize.size` is established. -/
@[inline] def rawExtendHwUSize (s : UInt32) (a : @& ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) : UInt32 :=
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have hfin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  if h96 : 96 ≤ ulen then
    rawExtendHwMulti s a hs uoff ulen h h96
  else
    have hle : uoff.toNat ≤ (uoff + ulen).toNat := by omega
    have hfin_sz : (uoff + ulen).toNat ≤ a.size := by omega
    hwLoop a hs uoff (uoff + ulen) hle hfin_sz s

/-- Unconditioned CRC32C state update over `a[off, off + len)`, hardware path. -/
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

/-- `absl::ExtendCrc32c`, hardware CRC + carry-less-multiply path. -/
def extendHw (c : UInt32) (a : @& ByteArray) : UInt32 :=
  rawExtendHw (c ^^^ 0xFFFFFFFF) a 0 a.size (by omega) ^^^ 0xFFFFFFFF

end Crc32c
