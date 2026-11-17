/-
The field GF(2^8) = GF(2)[X] / (X^8 + X^4 + X^3 + X^2 + 1), and the proof that
the byte arithmetic of `ReedSolomon.Impl.Kernel` (`^^^`, `gfMulX`, `gfMul`,
`gfInv`) is its arithmetic under `ofByte`, which reads bit `i` of a byte as the
coefficient of `X^i`.
-/
import ReedSolomon.Impl.Kernel
import SimdModels.Semantics
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot

namespace ReedSolomon
open Polynomial SimdModels

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The field polynomial (0x11D). -/
def P8 : (ZMod 2)[X] := X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1

private theorem two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  ext n; cases n <;> simp; decide

private theorem four_eq_zero_poly : (4 : (ZMod 2)[X]) = 0 := by
  rw [show (4 : (ZMod 2)[X]) = 2 * 2 by norm_num, two_eq_zero_poly, mul_zero]

/-- A statement about every byte, from its 256 instances. -/
private theorem forall_byte {p : UInt8 → Prop} (h : ∀ i : Fin 256, p (UInt8.ofFin i))
    (a : UInt8) : p a := h a.toFin

theorem P8_natDegree : P8.natDegree = 8 := by unfold P8; compute_degree!

theorem P8_monic : P8.Monic := by unfold P8; monicity!

/-- `gcd(P8, X^16 + X) = 1`: `P8` has no factor of degree 1, 2 or 4. -/
private theorem bezout16 :
    (X ^ 14 + X ^ 9 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * P8 +
      (X ^ 6 + X ^ 2 + 1) * (X ^ 16 + X) = 1 := by
  unfold P8; ring_nf; simp [two_eq_zero_poly, four_eq_zero_poly]

/-- `gcd(P8, X^8 + X) = 1`: `P8` has no factor of degree 3. -/
private theorem bezout8 :
    (X ^ 5 + X ^ 3 + 1) * P8 + (X ^ 5 + X ^ 3 + X) * (X ^ 8 + X) = 1 := by
  unfold P8; ring_nf; simp [two_eq_zero_poly]

/-- No irreducible polynomial of degree 1 to 4 divides `P8`: in the field with
`2^d` elements its root `α` satisfies `α^(2^d) = α`, so `α^16 = α` or
`α^8 = α`, and the Bézout identities above then give `0 = 1`. -/
private theorem no_small_factor {q : (ZMod 2)[X]} (hq : Irreducible q) (hdvd : q ∣ P8)
    (h1 : 0 < q.natDegree) (h4 : q.natDegree ≤ 4) : False := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have : Fact (Irreducible q) := ⟨hq⟩
  let K := AdjoinRoot q
  let pb := AdjoinRoot.powerBasis hq0
  let fK : Fintype K := Fintype.ofEquiv (Fin pb.dim → ZMod 2) pb.basis.equivFun.symm.toEquiv
  have hcard : @Fintype.card K fK = 2 ^ q.natDegree := by
    rw [@Fintype.card_congr _ _ fK _ pb.basis.equivFun.toEquiv, Fintype.card_fun,
      ZMod.card, Fintype.card_fin]
    simp [pb, AdjoinRoot.powerBasis_dim]
  let α : K := AdjoinRoot.root q
  have h11 : (1 : K) + 1 = 0 := by
    rw [← map_one (AdjoinRoot.mk q), ← map_add, CharTwo.add_self_eq_zero, map_zero]
  have hαα : α + α = 0 := by rw [← mul_one α, ← mul_add, h11, mul_zero]
  have hpow : α ^ 2 ^ q.natDegree = α := by
    rw [← hcard]; exact @FiniteField.pow_card K _ fK α
  have hP : aeval α P8 = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.mpr hdvd
  have key : α ^ 16 = α ∨ α ^ 8 = α := by
    have hd : q.natDegree = 1 ∨ q.natDegree = 2 ∨ q.natDegree = 3 ∨ q.natDegree = 4 := by omega
    rcases hd with h | h | h | h <;> rw [h] at hpow
    · left
      have e : α ^ 16 = (((α ^ 2 ^ 1) ^ 2 ^ 1) ^ 2 ^ 1) ^ 2 ^ 1 := by ring
      rw [e, hpow, hpow, hpow, hpow]
    · left
      have e : α ^ 16 = (α ^ 2 ^ 2) ^ 2 ^ 2 := by ring
      rw [e, hpow, hpow]
    · right; simpa using hpow
    · left; simpa using hpow
  rcases key with h | h
  · have := congrArg (aeval α) bezout16
    simp only [map_add, map_mul, hP, mul_zero, zero_add, map_pow, aeval_X, h, hαα, map_one] at this
    exact zero_ne_one this
  · have := congrArg (aeval α) bezout8
    simp only [map_add, map_mul, hP, mul_zero, zero_add, map_pow, aeval_X, h, hαα, map_one] at this
    exact zero_ne_one this

theorem irreducible_P8 : Irreducible P8 := by
  rw [P8_monic.irreducible_iff_natDegree']
  refine ⟨fun h => by have := P8_natDegree; rw [h] at this; simp at this, ?_⟩
  intro f g _ hg hfg hmem
  rw [P8_natDegree] at hmem
  obtain ⟨hpos, hle⟩ := Finset.mem_Ioc.mp hmem
  have hnu : ¬ IsUnit g := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨q, hq, hqg⟩ := WfDvdMonoid.exists_irreducible_factor hnu hg.ne_zero
  have hqd : q.natDegree ≤ g.natDegree := natDegree_le_of_dvd hqg hg.ne_zero
  have hq1 : 0 < q.natDegree := by
    by_contra h0
    exact hq.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree hq.ne_zero]; simp; omega))
  exact no_small_factor hq (hqg.trans ⟨f, by rw [← hfg, mul_comm]⟩) hq1 (by simpa using hqd.trans hle)

instance : Fact (Irreducible P8) := ⟨irreducible_P8⟩

/-- GF(2^8). -/
abbrev GF256 := AdjoinRoot P8

/-- A byte as a field element: bit `i` is the coefficient of `X^i`. -/
def ofByte (b : UInt8) : GF256 := AdjoinRoot.mk P8 (polyN b.toBitVec)

/-- The field element `X`. -/
abbrev gen : GF256 := AdjoinRoot.root P8

theorem ofByte_zero : ofByte 0 = 0 := by
  show AdjoinRoot.mk P8 (polyN (0 : BitVec 8)) = 0
  rw [polyN_zero, map_zero]

theorem ofByte_xor (a b : UInt8) : ofByte (a ^^^ b) = ofByte a + ofByte b := by
  show AdjoinRoot.mk P8 (polyN (a.toBitVec ^^^ b.toBitVec)) = _
  rw [polyN_xor, map_add]; rfl

theorem ofByte_injective : Function.Injective ofByte := by
  intro a b h
  have hd : P8 ∣ polyN a.toBitVec - polyN b.toBitVec := by
    rw [← AdjoinRoot.mk_eq_mk]; exact h
  have hlt : (polyN a.toBitVec - polyN b.toBitVec).degree < P8.degree := by
    rw [degree_eq_natDegree P8_monic.ne_zero, P8_natDegree]
    exact (degree_sub_le _ _).trans_lt (max_lt (degree_polyN_lt _) (degree_polyN_lt _))
  have h0 := eq_zero_of_dvd_of_degree_lt hd hlt
  exact UInt8.toBitVec_inj.mp (polyN_injective (sub_eq_zero.mp h0))

theorem gf_add_self (x : GF256) : x + x = 0 := by
  have h11 : (1 : GF256) + 1 = 0 := by
    rw [← map_one (AdjoinRoot.mk P8), ← map_add, CharTwo.add_self_eq_zero, map_zero]
  rw [← mul_one x, ← mul_add, h11, mul_zero]

/-- `X^8 = X^4 + X^3 + X^2 + 1` in the field. -/
theorem gen_pow_eight : gen ^ 8 = ofByte 0x1d := by
  have h : AdjoinRoot.mk P8 P8 = 0 := AdjoinRoot.mk_self
  have e : polyN (0x1d : UInt8).toBitVec = X ^ 4 + X ^ 3 + X ^ 2 + 1 := by
    ext k
    rw [coeff_polyN]
    simp only [coeff_add, coeff_X_pow, coeff_one]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp
  have hs : gen ^ 8 + ofByte 0x1d = 0 := by
    rw [ofByte, e, ← h]
    show AdjoinRoot.root P8 ^ 8 + _ = _
    rw [← AdjoinRoot.mk_X, ← map_pow, ← map_add]
    congr 1; unfold P8; ring
  calc gen ^ 8 = gen ^ 8 + (ofByte 0x1d + ofByte 0x1d) := by rw [gf_add_self, add_zero]
    _ = ofByte 0x1d := by rw [← add_assoc, hs, zero_add]

/-- Splitting off the top bit: `X * a = (a <<< 1) + a₇ X^8`. -/
private theorem X_mul_polyN (a : BitVec 8) :
    X * polyN a = polyN (a <<< 1) + if a.getLsbD 7 then X ^ 8 else 0 := by
  ext k
  rcases k with _ | k
  · simp [coeff_polyN']; split <;> simp
  · rw [coeff_X_mul, coeff_add, coeff_polyN, coeff_polyN]
    by_cases h8 : k = 7
    · subst h8; cases a.getLsbD 7 <;> simp
    · have : (if a.getLsbD 7 then (X : (ZMod 2)[X]) ^ 8 else 0).coeff (k + 1) = 0 := by
        split <;> simp; omega
      rw [this, add_zero]
      by_cases hk : k < 7
      · simp [show k + 1 < 8 by omega, show k < 8 by omega]
      · simp [show ¬ k + 1 < 8 by omega, show ¬ k < 8 by omega]

theorem ofByte_gfMulX (a : UInt8) : ofByte (gfMulX a) = gen * ofByte a := by
  have hx := congrArg (AdjoinRoot.mk P8) (X_mul_polyN a.toBitVec)
  rw [map_mul, AdjoinRoot.mk_X, map_add] at hx
  have hbit : (a &&& 0x80 == 0) = !a.toBitVec.getLsbD 7 :=
    forall_byte (p := fun a => (a &&& 0x80 == 0) = !a.toBitVec.getLsbD 7) (by decide +kernel) a
  unfold gfMulX
  rw [ofByte_xor]
  show _ = gen * AdjoinRoot.mk P8 (polyN a.toBitVec)
  rw [hx, hbit]
  congr 1
  cases a.toBitVec.getLsbD 7
  · simp [ofByte_zero]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, map_pow, AdjoinRoot.mk_X]
    exact gen_pow_eight.symm

/-- Splitting off the bottom bit: `b = b₀ + X * (b >>> 1)`. -/
private theorem polyN_shiftRight_one (b : BitVec 8) :
    polyN b = (if b.getLsbD 0 then (1 : (ZMod 2)[X]) else 0) + X * polyN (b >>> 1) := by
  ext k
  rcases k with _ | k
  · simp [coeff_polyN']; split <;> simp
  · rw [coeff_add, coeff_X_mul, coeff_polyN', coeff_polyN']
    have : (if b.getLsbD 0 then (1 : (ZMod 2)[X]) else 0).coeff (k + 1) = 0 := by
      split <;> simp [coeff_one]
    rw [this, zero_add]; simp [Nat.add_comm]

private theorem ofByte_shiftRight_one (b : UInt8) :
    ofByte b = (if b &&& 1 == 0 then (0 : GF256) else 1) + gen * ofByte (b >>> 1) := by
  have hbit : (b &&& 1 == 0) = !b.toBitVec.getLsbD 0 :=
    forall_byte (p := fun b => (b &&& 1 == 0) = !b.toBitVec.getLsbD 0) (by decide +kernel) b
  have hs : (b >>> 1).toBitVec = b.toBitVec >>> 1 :=
    forall_byte (p := fun b => (b >>> 1).toBitVec = b.toBitVec >>> 1) (by decide +kernel) b
  have h := congrArg (AdjoinRoot.mk P8) (polyN_shiftRight_one b.toBitVec)
  rw [map_add, map_mul, AdjoinRoot.mk_X] at h
  rw [ofByte, h, hbit, ofByte, hs]
  cases b.toBitVec.getLsbD 0 <;> simp

theorem ofByte_gfMulLoop (n : Nat) (a b r : UInt8) (hb : b.toNat < 2 ^ n) :
    ofByte (gfMulLoop n a b r) = ofByte r + ofByte a * ofByte b := by
  induction n generalizing a b r with
  | zero =>
    have : b = 0 := UInt8.toNat_inj.mp (by simpa using hb)
    simp [gfMulLoop, this, ofByte_zero]
  | succ n ih =>
    have hb' : (b >>> 1).toNat < 2 ^ n := by
      rw [UInt8.toNat_shiftRight]
      show b.toNat >>> 1 < 2 ^ n
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_succ] at *; omega
    rw [gfMulLoop, ih _ _ _ hb', ofByte_gfMulX, ofByte_shiftRight_one b]
    split
    · simp; ring
    · rw [ofByte_xor]; ring

/-- Byte multiplication is field multiplication. -/
theorem ofByte_gfMul (a b : UInt8) : ofByte (gfMul a b) = ofByte a * ofByte b := by
  rw [gfMul, ofByte_gfMulLoop 8 a b 0 (by have := b.toNat_lt; omega), ofByte_zero, zero_add]

theorem ofByte_one : ofByte 1 = 1 := by
  have e : polyN (1 : UInt8).toBitVec = 1 := by
    ext k
    rw [coeff_polyN, coeff_one]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp
  rw [ofByte, e, map_one]

theorem ofByte_gfPow (a : UInt8) (n : Nat) : ofByte (gfPow a n) = ofByte a ^ n := by
  induction n with
  | zero => simp [gfPow, ofByte_one]
  | succ n ih => rw [gfPow, ofByte_gfMul, ih, pow_succ, mul_comm]

/-- The field has 256 elements, so every nonzero element has order dividing 255. -/
theorem pow_255 (x : GF256) (hx : x ≠ 0) : x ^ 255 = 1 := by
  let pb := AdjoinRoot.powerBasis P8_monic.ne_zero
  let fK : Fintype GF256 := Fintype.ofEquiv (Fin pb.dim → ZMod 2) pb.basis.equivFun.symm.toEquiv
  have hcard : @Fintype.card GF256 fK = 2 ^ 8 := by
    rw [@Fintype.card_congr _ _ fK _ pb.basis.equivFun.toEquiv, Fintype.card_fun,
      ZMod.card, Fintype.card_fin]
    simp [pb, AdjoinRoot.powerBasis_dim, P8_natDegree]
  have h := @FiniteField.pow_card_sub_one_eq_one GF256 _ fK x hx
  rwa [hcard] at h

theorem ofByte_gfPowSq (a : UInt8) (n : Nat) : ofByte (gfPowSq a n) = ofByte a ^ n := by
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rw [gfPowSq]
    split
    · subst_vars; simp [ofByte_one]
    · have e : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      have hlt : n / 2 < n := by omega
      dsimp only
      split
      · rename_i h1
        rw [ofByte_gfMul, ih _ hlt, ofByte_gfMul, ← sq, ← pow_mul]
        conv_rhs => rw [e, h1, pow_succ, mul_comm]
      · rename_i h1
        rw [ih _ hlt, ofByte_gfMul, ← sq, ← pow_mul]
        conv_rhs => rw [e, show n % 2 = 0 by omega, Nat.add_zero]

/-- Byte inversion (`a^254`) is field inversion, with `0⁻¹ = 0`. -/
theorem ofByte_gfInv (a : UInt8) : ofByte (gfInv a) = (ofByte a)⁻¹ := by
  rw [gfInv, ofByte_gfPowSq]
  by_cases h : ofByte a = 0
  · rw [h, inv_zero, zero_pow (by norm_num)]
  · exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact pow_255 _ h)

end

end ReedSolomon
