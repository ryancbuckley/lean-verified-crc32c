/-
Memory-level lemmas for the machine-code proof of `leancrc32c_copy_large`
(`cxx/leancrc32c_copy_arm64.S`): reading 16-byte vectors from the source and
writing them to the destination, phrased over a "prefix patched" memory.

`patch m0 dst b w` is the initial memory `m0` with the first `w` destination
bytes replaced by the source bytes `b`. Every store the routine performs
extends that prefix (or rewrites bytes inside it with the same values), so the
whole proof carries one invariant: `s.mem = patch m0 dst b w`.
-/
import SimdModels.Arm64Lemmas
import Mathlib.Tactic

namespace Crc32c.Arm64MC.Copy
open SimdModels SimdModels.Arm64

theorem u64_ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem toNat_add_nat (p : UInt64) (i : Nat) (h : p.toNat + i < 2 ^ 64) :
    (p + i.toUInt64).toNat = p.toNat + i := by
  simp only [UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Byte `j` of a little-endian word assembled from eight bytes. -/
theorem word64_byte (c : Nat → UInt8) (j : Nat) (hj : j < 8) :
    (Model.word64 (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) >>> (8 * j).toUInt64).toUInt8
      = c j := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases j <;>
    simp [Model.word64, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, Nat.toUInt64] <;>
    (interval_cases i <;> simp)

/-! ### Pointwise description of an 8-byte store -/

theorem writeSlot64_apply (m : Mem) (p : UInt64) (v : UInt64) (a : UInt64)
    (hp : p.toNat + 8 ≤ 2 ^ 64) :
    (m.writeSlot64 p v) a =
      if p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 8 then
        some (.rw, (v >>> (8 * (a.toNat - p.toNat)).toUInt64).toUInt8)
      else m a := by
  by_cases hin : p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 8
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < 8 ∧ a = p + j.toUInt64 :=
      ⟨a.toNat - p.toNat, by omega, u64_ext (by rw [toNat_add_nat _ _ (by omega)]; omega)⟩
    have hsub : (p + j.toUInt64).toNat - p.toNat = j := by
      rw [toNat_add_nat _ _ (by omega)]; omega
    rw [hsub]
    interval_cases j <;> simp [Mem.writeSlot64, Mem.putRWByte, Nat.toUInt64]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]
    have hsz : UInt64.size = 2 ^ 64 := rfl
    exact Mem.writeSlot64_outside m p a v (by omega) (by omega)

/-! ### The copy setting and the prefix-patched memory -/

/-- The memory preconditions of the copy: `n` readable source bytes `b`, `n`
writable destination bytes, no address wraparound, and no overlap. -/
structure Setup (m0 : Mem) (src dst : UInt64) (b : Nat → UInt8) (n : Nat) : Prop where
  hs : src.toNat + n ≤ 2 ^ 64
  hd : dst.toNat + n ≤ 2 ^ 64
  disj : src.toNat + n ≤ dst.toNat ∨ dst.toNat + n ≤ src.toNat
  rd : ∀ i < n, m0.readU8 (src + i.toUInt64) = some (b i)
  rw : ∀ i < n, ∃ x, m0 (dst + i.toUInt64) = some (.rw, x)

/-- `m0` with the first `w` destination bytes replaced by the source bytes. -/
def patch (m0 : Mem) (dst : UInt64) (b : Nat → UInt8) (w : Nat) : Mem :=
  fun a => if dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + w then
    some (.rw, b (a.toNat - dst.toNat)) else m0 a

theorem patch_zero (m0 : Mem) (dst : UInt64) (b : Nat → UInt8) : patch m0 dst b 0 = m0 := by
  funext a; simp [patch]

variable {m0 : Mem} {src dst : UInt64} {b : Nat → UInt8} {n : Nat}

theorem patch_isRW (h : Setup m0 src dst b n) (w : Nat) :
    (patch m0 dst b w).isRWRange dst n := by
  refine ⟨by have : UInt64.size = 2 ^ 64 := rfl; have := h.hd; omega, fun k hk => ?_⟩
  unfold patch
  split
  · exact ⟨_, rfl⟩
  · exact h.rw k hk

theorem patch_read (h : Setup m0 src dst b n) {w : Nat} (hw : w ≤ n) {i : Nat} (hi : i < n) :
    (patch m0 dst b w).readU8 (src + i.toUInt64) = some (b i) := by
  have hA : (src + i.toUInt64).toNat = src.toNat + i := toNat_add_nat _ _ (by have := h.hs; omega)
  have hne : ¬ (dst.toNat ≤ (src + i.toUInt64).toNat ∧ (src + i.toUInt64).toNat < dst.toNat + w) := by
    rw [hA]; have := h.disj; omega
  have := h.rd i hi
  simp only [Mem.readU8, patch, hne, ↓reduceIte] at this ⊢
  exact this

/-- Eight consecutive source bytes as a little-endian word. -/
def w8 (b : Nat → UInt8) (k : Nat) : UInt64 :=
  Model.word64 (b (k + 0)) (b (k + 1)) (b (k + 2)) (b (k + 3)) (b (k + 4)) (b (k + 5))
    (b (k + 6)) (b (k + 7))

/-- Sixteen consecutive source bytes as a vector register value. -/
def vec (b : Nat → UInt8) (k : Nat) : V128 := V128.ofHalves (w8 b k) (w8 b (k + 8))

theorem add_add_nat (p : UInt64) (i j : Nat) :
    p + i.toUInt64 + j.toUInt64 = p + (i + j).toUInt64 := by
  rw [UInt64.add_assoc]; congr 1
  apply UInt64.eq_of_toBitVec_eq
  simp [Nat.toUInt64, UInt64.ofNat, BitVec.ofNat_add]

theorem load8 (h : Setup m0 src dst b n) {w : Nat} (hw : w ≤ n) {off : Nat} (ho : off + 8 ≤ n) :
    (patch m0 dst b w).readU64LE (src + off.toUInt64) = some (w8 b off) := by
  have r (j : Nat) (hj : j < 8) :
      (patch m0 dst b w).readU8 (src + off.toUInt64 + j.toUInt64) = some (b (off + j)) := by
    rw [add_add_nat]; exact patch_read h hw (by omega)
  have r0 : (patch m0 dst b w).readU8 (src + off.toUInt64) = some (b (off + 0)) := by
    simpa [Nat.toUInt64] using r 0 (by omega)
  have r1 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 1) = some (b (off + 1)) := r 1 (by omega)
  have r2 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 2) = some (b (off + 2)) := r 2 (by omega)
  have r3 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 3) = some (b (off + 3)) := r 3 (by omega)
  have r4 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 4) = some (b (off + 4)) := r 4 (by omega)
  have r5 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 5) = some (b (off + 5)) := r 5 (by omega)
  have r6 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 6) = some (b (off + 6)) := r 6 (by omega)
  have r7 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 7) = some (b (off + 7)) := r 7 (by omega)
  simp only [Mem.readU64LE, w8, r0, r1, r2, r3, r4, r5, r6, r7, Option.bind_eq_bind,
    Option.bind_some]

theorem store8 (h : Setup m0 src dst b n) {w : Nat} {off : Nat} (how : off ≤ w)
    (ho : off + 8 ≤ n) :
    (patch m0 dst b w).writeU64LE (dst + off.toUInt64) (w8 b off) =
      some (patch m0 dst b (max w (off + 8))) := by
  have hd := h.hd
  have hA : (dst + off.toUInt64).toNat = dst.toNat + off := toNat_add_nat _ _ (by omega)
  rw [Mem.writeU64LE_of_isRWRange (patch_isRW h w) off ho]
  congr 1
  funext a
  rw [writeSlot64_apply _ _ _ _ (by omega), hA]
  by_cases hin : dst.toNat + off ≤ a.toNat ∧ a.toNat < dst.toNat + off + 8
  · have hnew : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 8) := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    simp only [patch]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hnew)]
    have hb := word64_byte (fun i => b (off + i)) (a.toNat - (dst.toNat + off)) (by omega)
    rw [show a.toNat - dst.toNat = off + (a.toNat - (dst.toNat + off)) by omega]
    rw [← hb]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]
    simp only [patch]
    by_cases hold : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + w
    · have hnew : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 8) := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hold), ite_eq_left_of_eq_true _ _ (eq_true hnew)]
    · have hnew : ¬ (dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 8)) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hold), ite_eq_right_of_eq_false _ _ (eq_false hnew)]

theorem load16 (h : Setup m0 src dst b n) {w : Nat} (hw : w ≤ n) {off : Nat} (ho : off + 16 ≤ n) :
    (patch m0 dst b w).readV128LE (src + off.toUInt64) = some (vec b off) := by
  have h8 : src + off.toUInt64 + 8 = src + (off + 8).toUInt64 := by
    rw [← add_add_nat]; rfl
  simp only [Mem.readV128LE, h8, load8 h hw (show off + 8 ≤ n by omega),
    load8 h hw (show off + 8 + 8 ≤ n by omega), vec]
  rfl

theorem store16 (h : Setup m0 src dst b n) {w : Nat} {off : Nat} (how : off ≤ w)
    (ho : off + 16 ≤ n) :
    (patch m0 dst b w).writeV128LE (dst + off.toUInt64) (vec b off) =
      some (patch m0 dst b (max w (off + 16))) := by
  have h8 : dst + off.toUInt64 + 8 = dst + (off + 8).toUInt64 := by
    rw [← add_add_nat]; rfl
  simp only [Mem.writeV128LE, vec, lo64_ofHalves_simp, lane64_one_simp, hi64_ofHalves_simp, h8,
    store8 h how (show off + 8 ≤ n by omega), Option.bind_eq_bind, Option.bind_some,
    store8 h (show off + 8 ≤ max w (off + 8) by omega) (show off + 8 + 8 ≤ n by omega)]
  rw [show max (max w (off + 8)) (off + 8 + 8) = max w (off + 16) by omega]

/-- A 32-byte source block read as a register pair. -/
theorem load32 (h : Setup m0 src dst b n) {w : Nat} (hw : w ≤ n) {off : Nat} (ho : off + 32 ≤ n) :
    (patch m0 dst b w).readV128LE (src + off.toUInt64) = some (vec b off) ∧
    (patch m0 dst b w).readV128LE (src + off.toUInt64 + 16) = some (vec b (off + 16)) := by
  refine ⟨load16 h hw (by omega), ?_⟩
  rw [show src + off.toUInt64 + 16 = src + (off + 16).toUInt64 by rw [← add_add_nat]; rfl]
  exact load16 h hw (by omega)

/-- Storing a 32-byte block at or below the end of the copied prefix extends the prefix. -/
theorem store32 (h : Setup m0 src dst b n) {w : Nat} {off : Nat} (how : off ≤ w)
    (ho : off + 32 ≤ n) :
    ((patch m0 dst b w).writeV128LE (dst + off.toUInt64) (vec b off)).bind
        (fun m1 => m1.writeV128LE (dst + off.toUInt64 + 16) (vec b (off + 16))) =
      some (patch m0 dst b (max w (off + 32))) := by
  rw [store16 h how (by omega), Option.bind_some,
    show dst + off.toUInt64 + 16 = dst + (off + 16).toUInt64 by rw [← add_add_nat]; rfl,
    store16 h (show off + 16 ≤ max w (off + 16) by omega) (by omega)]
  rw [show max (max w (off + 16)) (off + 16 + 16) = max w (off + 32) by omega]

/-! ### 4-byte and 1-byte accesses (for `leancrc32c_copy_small`) -/

/-- Byte `j` of a little-endian 32-bit word assembled from four bytes. -/
theorem word32_byte (c : Nat → UInt8) (j : Nat) (hj : j < 4) :
    (((c 0).toUInt32 ||| ((c 1).toUInt32 <<< 8) ||| ((c 2).toUInt32 <<< 16) |||
        ((c 3).toUInt32 <<< 24)) >>> (8 * j).toUInt32).toUInt8 = c j := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases j <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, Nat.toUInt32] <;>
    (interval_cases i <;> simp)

theorem writeSlot32_apply (m : Mem) (p : UInt64) (v : UInt32) (a : UInt64)
    (hp : p.toNat + 4 ≤ 2 ^ 64) :
    (m.writeSlot32 p v) a =
      if p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 4 then
        some (.rw, (v >>> (8 * (a.toNat - p.toNat)).toUInt32).toUInt8)
      else m a := by
  by_cases hin : p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 4
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ a = p + j.toUInt64 :=
      ⟨a.toNat - p.toNat, by omega, u64_ext (by rw [toNat_add_nat _ _ (by omega)]; omega)⟩
    have hsub : (p + j.toUInt64).toNat - p.toNat = j := by
      rw [toNat_add_nat _ _ (by omega)]; omega
    rw [hsub]
    interval_cases j <;> simp [Mem.writeSlot32, Mem.putRWByte, Nat.toUInt64, Nat.toUInt32]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]
    have hsz : UInt64.size = 2 ^ 64 := rfl
    exact Mem.writeSlot32_outside m p a v (by omega) (by omega)

/-- Four consecutive source bytes as a little-endian word. -/
def w4 (b : Nat → UInt8) (k : Nat) : UInt32 :=
  (b (k + 0)).toUInt32 ||| ((b (k + 1)).toUInt32 <<< 8) ||| ((b (k + 2)).toUInt32 <<< 16) |||
    ((b (k + 3)).toUInt32 <<< 24)

theorem load4 (h : Setup m0 src dst b n) {w : Nat} (hw : w ≤ n) {off : Nat} (ho : off + 4 ≤ n) :
    (patch m0 dst b w).readU32LE (src + off.toUInt64) = some (w4 b off) := by
  have r (j : Nat) (hj : j < 4) :
      (patch m0 dst b w).readU8 (src + off.toUInt64 + j.toUInt64) = some (b (off + j)) := by
    rw [add_add_nat]; exact patch_read h hw (by omega)
  have r0 : (patch m0 dst b w).readU8 (src + off.toUInt64) = some (b (off + 0)) := by
    simpa [Nat.toUInt64] using r 0 (by omega)
  have r1 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 1) = some (b (off + 1)) := r 1 (by omega)
  have r2 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 2) = some (b (off + 2)) := r 2 (by omega)
  have r3 : (patch m0 dst b w).readU8 (src + off.toUInt64 + 3) = some (b (off + 3)) := r 3 (by omega)
  simp only [Mem.readU32LE, w4, r0, r1, r2, r3, Option.bind_eq_bind, Option.bind_some]

theorem store4 (h : Setup m0 src dst b n) {w : Nat} {off : Nat} (how : off ≤ w)
    (ho : off + 4 ≤ n) :
    (patch m0 dst b w).writeU32LE (dst + off.toUInt64) (w4 b off) =
      some (patch m0 dst b (max w (off + 4))) := by
  have hd := h.hd
  have hA : (dst + off.toUInt64).toNat = dst.toNat + off := toNat_add_nat _ _ (by omega)
  rw [Mem.writeU32LE_of_isRWRange (patch_isRW h w) off ho]
  congr 1
  funext a
  rw [writeSlot32_apply _ _ _ _ (by omega), hA]
  by_cases hin : dst.toNat + off ≤ a.toNat ∧ a.toNat < dst.toNat + off + 4
  · have hnew : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 4) := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    simp only [patch]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hnew)]
    have hb := word32_byte (fun i => b (off + i)) (a.toNat - (dst.toNat + off)) (by omega)
    rw [show a.toNat - dst.toNat = off + (a.toNat - (dst.toNat + off)) by omega]
    rw [← hb]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]
    simp only [patch]
    by_cases hold : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + w
    · have hnew : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 4) := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hold), ite_eq_left_of_eq_true _ _ (eq_true hnew)]
    · have hnew : ¬ (dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 4)) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hold), ite_eq_right_of_eq_false _ _ (eq_false hnew)]

theorem store1 (h : Setup m0 src dst b n) {w : Nat} {off : Nat} (how : off ≤ w)
    (ho : off + 1 ≤ n) :
    (patch m0 dst b w).writeU8 (dst + off.toUInt64) (b off) =
      some (patch m0 dst b (max w (off + 1))) := by
  have hd := h.hd
  have hA : (dst + off.toUInt64).toNat = dst.toNat + off := toNat_add_nat _ _ (by omega)
  obtain ⟨x, hx⟩ := (patch_isRW h w).2 off (by omega)
  rw [Mem.writeU8_eq_putRWByte hx]
  congr 1
  funext a
  simp only [Mem.putRWByte, patch]
  by_cases ha : a = dst + off.toUInt64
  · subst ha
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hA, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    congr 3; omega
  · have hne : a.toNat ≠ dst.toNat + off := fun hh => ha (u64_ext (by rw [hA]; exact hh))
    rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]
    by_cases hold : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + w
    · have hnew : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 1) := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hold), ite_eq_left_of_eq_true _ _ (eq_true hnew)]
    · have hnew : ¬ (dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + max w (off + 1)) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hold), ite_eq_right_of_eq_false _ _ (eq_false hnew)]

end Crc32c.Arm64MC.Copy
