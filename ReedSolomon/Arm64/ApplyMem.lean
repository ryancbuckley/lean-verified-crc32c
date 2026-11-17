/-
Memory-level lemmas for the machine-code proof of `leanrs_apply`
(`cxx/leanrs_apply_arm64.S`).

The routine reads a table, two pointer arrays and `k` input shards, and writes
`r` output shards. `Setup` states what the initial memory `m0` must contain and
that no output shard overlaps anything read or another output shard. `Good pre
m` is the invariant every intermediate memory `m` satisfies: output shard `j`
holds its final bytes `B j` on the prefix `[0, pre j)`, and every other byte of
memory is as in `m0`.
-/
import ReedSolomon.Arm64.Lanes

namespace ReedSolomon.Arm64MC
open SimdModels SimdModels.Arm64
open Crc32c.Arm64MC.Copy (toNat_add_nat u64_ext add_add_nat writeSlot64_apply word64_byte vec w8)

/-! ### Reads assembled from bytes -/

theorem readU64_of_bytes (m : Mem) (p : UInt64) (b : Nat → UInt8) (off : Nat)
    (h : ∀ j < 8, m.readU8 (p + j.toUInt64) = some (b (off + j))) :
    m.readU64LE p = some (w8 b off) := by
  have r0 : m.readU8 p = some (b (off + 0)) := by simpa [Nat.toUInt64] using h 0 (by omega)
  have r1 : m.readU8 (p + 1) = some (b (off + 1)) := h 1 (by omega)
  have r2 : m.readU8 (p + 2) = some (b (off + 2)) := h 2 (by omega)
  have r3 : m.readU8 (p + 3) = some (b (off + 3)) := h 3 (by omega)
  have r4 : m.readU8 (p + 4) = some (b (off + 4)) := h 4 (by omega)
  have r5 : m.readU8 (p + 5) = some (b (off + 5)) := h 5 (by omega)
  have r6 : m.readU8 (p + 6) = some (b (off + 6)) := h 6 (by omega)
  have r7 : m.readU8 (p + 7) = some (b (off + 7)) := h 7 (by omega)
  simp only [Mem.readU64LE, w8, r0, r1, r2, r3, r4, r5, r6, r7, Option.bind_eq_bind,
    Option.bind_some]

theorem readV128_of_bytes (m : Mem) (p : UInt64) (b : Nat → UInt8) (off : Nat)
    (h : ∀ j < 16, m.readU8 (p + j.toUInt64) = some (b (off + j))) :
    m.readV128LE p = some (vec b off) := by
  have h1 := readU64_of_bytes m p b off fun j hj => h j (by omega)
  have h2 := readU64_of_bytes m (p + 8) b (off + 8) fun j hj => by
    have := h (8 + j) (by omega)
    rw [← add_add_nat] at this
    rw [show off + 8 + j = off + (8 + j) by omega]; exact this
  simp only [Mem.readV128LE, h1, h2, vec, Option.bind_eq_bind, Option.bind_some]

/-- Two memories that agree on eight bytes give the same 64-bit read. -/
theorem readU64_congr {m m' : Mem} (p : UInt64) (h : ∀ j < 8, m (p + j.toUInt64) = m' (p + j.toUInt64)) :
    m.readU64LE p = m'.readU64LE p := by
  have r0 : m p = m' p := by simpa [Nat.toUInt64] using h 0 (by omega)
  have r1 : m (p + 1) = m' (p + 1) := h 1 (by omega)
  have r2 : m (p + 2) = m' (p + 2) := h 2 (by omega)
  have r3 : m (p + 3) = m' (p + 3) := h 3 (by omega)
  have r4 : m (p + 4) = m' (p + 4) := h 4 (by omega)
  have r5 : m (p + 5) = m' (p + 5) := h 5 (by omega)
  have r6 : m (p + 6) = m' (p + 6) := h 6 (by omega)
  have r7 : m (p + 7) = m' (p + 7) := h 7 (by omega)
  simp only [Mem.readU64LE, Mem.readU8, r0, r1, r2, r3, r4, r5, r6, r7]

/-! ### A 16-byte store, pointwise -/

/-- The memory after a 16-byte store of `v` at `p` into writable bytes. -/
def st16 (m : Mem) (p : UInt64) (v : V128) : Mem :=
  (m.writeSlot64 p (V128.lo64 v)).writeSlot64 (p + 8) (V128.lane64 v 1)

theorem st16_vec_apply (m : Mem) (p : UInt64) (b : Nat → UInt8) (off : Nat) (a : UInt64)
    (hp : p.toNat + 16 ≤ 2 ^ 64) :
    st16 m p (vec b off) a =
      if p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 16 then
        some (.rw, b (off + (a.toNat - p.toNat)))
      else m a := by
  have h8 : (p + 8).toNat = p.toNat + 8 := toNat_add_nat p 8 (by omega)
  rw [st16, writeSlot64_apply _ _ _ _ (by omega), writeSlot64_apply _ _ _ _ (by omega), h8]
  simp only [vec, lo64_ofHalves_simp, lane64_one_simp, hi64_ofHalves_simp]
  by_cases hhi : p.toNat + 8 ≤ a.toNat ∧ a.toNat < p.toNat + 8 + 8
  · rw [if_pos hhi, if_pos (by omega)]
    have := word64_byte (fun i => b (off + 8 + i)) (a.toNat - (p.toNat + 8)) (by omega)
    rw [show off + (a.toNat - p.toNat) = off + 8 + (a.toNat - (p.toNat + 8)) by omega, ← this]; rfl
  · rw [if_neg hhi]
    by_cases hlo : p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 8
    · rw [if_pos hlo, if_pos (by omega)]
      have := word64_byte (fun i => b (off + i)) (a.toNat - p.toNat) (by omega)
      rw [← this]; rfl
    · rw [if_neg hlo, if_neg (by omega)]

/-! ### The setting -/

/-- The memory preconditions of `leanrs_apply`.

* `tab` holds the `32 * k * r` table bytes `T`; `inP` and `outP` hold the `k`
  input pointers `src` and the `r` output pointers `dst`;
* input shard `i` holds the `L` bytes `D i`, output shard `j` is `L` writable bytes;
* nothing wraps around the address space;
* no output shard overlaps the table, a pointer array, an input shard or
  another output shard. -/
structure Setup (m0 : Mem) (tab inP outP : UInt64) (k r L : Nat) (T : Nat → UInt8)
    (src dst : Nat → UInt64) (D : Nat → Nat → UInt8) : Prop where
  tabR : ∀ t < 32 * k * r, m0.readU8 (tab + t.toUInt64) = some (T t)
  inR : ∀ i < k, m0.readU64LE (inP + (8 * i).toUInt64) = some (src i)
  outR : ∀ j < r, m0.readU64LE (outP + (8 * j).toUInt64) = some (dst j)
  dataR : ∀ i < k, ∀ t < L, m0.readU8 (src i + t.toUInt64) = some (D i t)
  outW : ∀ j < r, ∀ t < L, ∃ x, m0 (dst j + t.toUInt64) = some (.rw, x)
  tabB : tab.toNat + 32 * k * r ≤ 2 ^ 64
  inB : inP.toNat + 8 * k ≤ 2 ^ 64
  outB : outP.toNat + 8 * r ≤ 2 ^ 64
  srcB : ∀ i < k, (src i).toNat + L ≤ 2 ^ 64
  dstB : ∀ j < r, (dst j).toNat + L ≤ 2 ^ 64
  tabD : ∀ j < r, tab.toNat + 32 * k * r ≤ (dst j).toNat ∨ (dst j).toNat + L ≤ tab.toNat
  inD : ∀ j < r, inP.toNat + 8 * k ≤ (dst j).toNat ∨ (dst j).toNat + L ≤ inP.toNat
  outD : ∀ j < r, outP.toNat + 8 * r ≤ (dst j).toNat ∨ (dst j).toNat + L ≤ outP.toNat
  srcD : ∀ i < k, ∀ j < r, (src i).toNat + L ≤ (dst j).toNat ∨ (dst j).toNat + L ≤ (src i).toNat
  dstD : ∀ j < r, ∀ j' < r, j ≠ j' →
    (dst j).toNat + L ≤ (dst j').toNat ∨ (dst j').toNat + L ≤ (dst j).toNat

/-- `a` lies inside an output shard. -/
def InOut (dst : Nat → UInt64) (r L : Nat) (a : UInt64) : Prop :=
  ∃ j < r, (dst j).toNat ≤ a.toNat ∧ a.toNat < (dst j).toNat + L

/-- The invariant on intermediate memories: output shard `j` holds `B j` on
`[0, pre j)`, and all other bytes (permissions included) are as in `m0`. -/
structure Good (m0 : Mem) (dst : Nat → UInt64) (r L : Nat) (B : Nat → Nat → UInt8)
    (pre : Nat → Nat) (m : Mem) : Prop where
  outside : ∀ a, ¬ InOut dst r L a → m a = m0 a
  inside : ∀ j < r, ∀ t < L, m (dst j + t.toUInt64) =
    if t < pre j then some (.rw, B j t) else m0 (dst j + t.toUInt64)

variable {m0 : Mem} {tab inP outP : UInt64} {k r L : Nat} {T : Nat → UInt8}
  {src dst : Nat → UInt64} {D : Nat → Nat → UInt8} {B : Nat → Nat → UInt8}
  {pre : Nat → Nat} {m : Mem}

theorem good_init : Good m0 dst r L B (fun _ => 0) m0 :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => by simp⟩

theorem Good.congr (hg : Good m0 dst r L B pre m) {pre' : Nat → Nat}
    (h : ∀ j < r, pre j = pre' j) : Good m0 dst r L B pre' m :=
  ⟨hg.outside, fun j hj t ht => by rw [hg.inside j hj t ht, h j hj]⟩

/-- A range that every output shard avoids contains no output byte. -/
theorem not_inOut {p : UInt64} {n t : Nat} (ht : t < n) (hp : p.toNat + n ≤ 2 ^ 64)
    (hd : ∀ j < r, p.toNat + n ≤ (dst j).toNat ∨ (dst j).toNat + L ≤ p.toNat) :
    ¬ InOut dst r L (p + t.toUInt64) := by
  rintro ⟨j, hj, h1, h2⟩
  rw [toNat_add_nat _ _ (by omega)] at h1 h2
  have := hd j hj; omega

section
variable (hs : Setup m0 tab inP outP k r L T src dst D) (hg : Good m0 dst r L B pre m)
include hs hg

theorem rdIn {i : Nat} (hi : i < k) : m.readU64LE (inP + (8 * i).toUInt64) = some (src i) := by
  rw [← hs.inR i hi]
  refine readU64_congr _ fun j hj => ?_
  rw [add_add_nat]
  exact hg.outside _ (not_inOut (n := 8 * k) (by omega) hs.inB hs.inD)

theorem rdOut {j : Nat} (hj : j < r) : m.readU64LE (outP + (8 * j).toUInt64) = some (dst j) := by
  rw [← hs.outR j hj]
  refine readU64_congr _ fun i hi => ?_
  rw [add_add_nat]
  exact hg.outside _ (not_inOut (n := 8 * r) (by omega) hs.outB hs.outD)

theorem rdTab {t : Nat} (ht : t + 16 ≤ 32 * k * r) :
    m.readV128LE (tab + t.toUInt64) = some (vec T t) := by
  refine readV128_of_bytes _ _ _ _ fun j hj => ?_
  rw [add_add_nat, ← hs.tabR (t + j) (by omega)]
  unfold Mem.readU8
  rw [hg.outside _ (not_inOut (n := 32 * k * r) (by omega) hs.tabB hs.tabD)]

theorem rdData {i : Nat} (hi : i < k) {off : Nat} (ho : off + 16 ≤ L) :
    m.readV128LE (src i + off.toUInt64) = some (vec (D i) off) := by
  refine readV128_of_bytes _ _ _ _ fun j hj => ?_
  rw [add_add_nat, ← hs.dataR i hi (off + j) (by omega)]
  unfold Mem.readU8
  rw [hg.outside _ (not_inOut (n := L) (by omega) (hs.srcB i hi) (hs.srcD i hi))]

theorem good_isRW {j : Nat} (hj : j < r) : m.isRWRange (dst j) L := by
  refine ⟨by have : UInt64.size = 2 ^ 64 := rfl; have := hs.dstB j hj; omega, fun t ht => ?_⟩
  rw [hg.inside j hj t ht]
  split
  · exact ⟨_, rfl⟩
  · exact hs.outW j hj t ht

/-- A 16-byte store into an output shard succeeds. -/
theorem write16 {j : Nat} (hj : j < r) {off : Nat} (ho : off + 16 ≤ L) (v : V128) :
    m.writeV128LE (dst j + off.toUInt64) v = some (st16 m (dst j + off.toUInt64) v) := by
  have hrw := good_isRW hs hg hj
  have h8 : dst j + off.toUInt64 + 8 = dst j + (off + 8).toUInt64 := by
    rw [← add_add_nat]; rfl
  simp only [Mem.writeV128LE, st16, h8, Mem.writeU64LE_of_isRWRange hrw off (by omega),
    Option.bind_eq_bind, Option.bind_some,
    Mem.writeU64LE_of_isRWRange (Mem.writeSlot64_isRWRange hrw _ _) (off + 8) (by omega)]

/-- Storing the next 16 final bytes at or below the end of a shard's prefix
extends that prefix. -/
theorem good_st16 {j : Nat} (hj : j < r) {off : Nat} (ho : off + 16 ≤ L) (hop : off ≤ pre j) :
    Good m0 dst r L B (fun j' => if j' = j then max (pre j') (off + 16) else pre j')
      (st16 m (dst j + off.toUInt64) (vec (B j) off)) := by
  have hb := hs.dstB j hj
  have hA : (dst j + off.toUInt64).toNat = (dst j).toNat + off := toNat_add_nat _ _ (by omega)
  refine ⟨fun a ha => ?_, fun j' hj' t ht => ?_⟩
  · rw [st16_vec_apply _ _ _ _ _ (by omega), hA, if_neg, hg.outside a ha]
    exact fun h => ha ⟨j, hj, by omega, by omega⟩
  · have hb' := hs.dstB j' hj'
    have hA' : (dst j' + t.toUInt64).toNat = (dst j').toNat + t := toNat_add_nat _ _ (by omega)
    rw [st16_vec_apply _ _ _ _ _ (by omega), hA, hA']
    by_cases hjj : j' = j
    · subst hjj
      rw [if_pos rfl]
      by_cases hin : off ≤ t ∧ t < off + 16
      · rw [if_pos (by omega), if_pos (by omega)]
        congr 3; omega
      · rw [if_neg (by omega), hg.inside j' hj' t ht]
        by_cases hp : t < pre j'
        · rw [if_pos hp, if_pos (by omega)]
        · rw [if_neg hp, if_neg (by omega)]
    · rw [if_neg hjj, if_neg, hg.inside j' hj' t ht]
      have := hs.dstD j hj j' hj' (Ne.symm hjj); omega

end

end ReedSolomon.Arm64MC
