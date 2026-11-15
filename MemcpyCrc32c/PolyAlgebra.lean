/-
Algebraic structure of the Castagnoli generator `G`:
- Complete prime factorization `G = (X + 1) * P31` in `GF(2)[X]`, where `P31` is
  an irreducible (and primitive) polynomial of prime degree 31.
- Exact multiplicative order `orderOf (π X) = 2^31 - 1 = 2147483647` (the 8th
  Mersenne prime), giving the exact classification, minimality, and uniqueness
  of 2-term zero polynomials (`zero2_minimal`, `zero2_unique`).
- Squarefreeness of `G` and Frobenius invariance `G ∣ p(X^(2^k)) ↔ G ∣ p(X)`,
  which transfers sparse-multiple bounds directly to word-aligned `Z(X^64)`
  Chorba polynomials.
-/
import MemcpyCrc32c.ZeroPoly
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.RingTheory.Polynomial.Content

namespace Crc32c
open Polynomial

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ### Helper lemmas over `(ZMod 2)[X]` -/

private theorem two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  ext n; cases n <;> simp; decide

private theorem mersenne31_eq : 2 ^ 31 - 1 = 2147483647 := by norm_num

private theorem eq_one_of_natDegree_eq_zero {u : (ZMod 2)[X]} (hd : u.natDegree = 0)
    (hu0 : u ≠ 0) : u = 1 := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
  have hc0 : u.coeff 0 ≠ 0 := fun h =>
    hu0 (by rw [Polynomial.eq_C_of_natDegree_eq_zero hd, h, map_zero])
  have hc1 : u.coeff 0 = 1 := by generalize u.coeff 0 = c at hc0; revert c; decide
  rw [hc1, map_one]

/-! ### The degree-31 irreducible factor `P31` and prime factorization of `G` -/

/-- `G / (X + 1)`: the degree-31 irreducible factor of the Castagnoli generator. -/
def P31 : (ZMod 2)[X] :=
  X^31 + X^30 + X^29 + X^28 + X^26 + X^24 + X^23 + X^21 + X^20 + X^18 +
    X^13 + X^10 + X^8 + X^5 + X^4 + X^3 + X^2 + X + 1

/-- Factorization of the Castagnoli generator: `G(X) = (X + 1) · P31(X)`. -/
theorem G_eq_mul_P31 : G = (X + 1) * P31 := by
  unfold G P31
  ring_nf
  simp [two_eq_zero_poly]

theorem P31_dvd_G : P31 ∣ G := ⟨X + 1, by rw [G_eq_mul_P31, mul_comm]⟩

theorem X_add_one_dvd_G : (X + 1 : (ZMod 2)[X]) ∣ G := ⟨P31, G_eq_mul_P31⟩

theorem P31_degree : P31.degree = 31 := by
  have hG := G_degree
  rw [G_eq_mul_P31] at hG
  have h1 : (X + 1 : (ZMod 2)[X]).degree = 1 := degree_X_add_C 1
  have hne2 : P31 ≠ 0 := fun h => by rw [h, mul_zero] at hG; simp at hG
  rw [degree_mul, h1] at hG
  cases hd : P31.degree with
  | bot => exact absurd (degree_eq_bot.mp hd) hne2
  | coe n =>
    rw [hd] at hG
    have hn : 1 + n = 32 := WithBot.coe_inj.mp hG
    have : n = 31 := by omega
    subst this; rfl

theorem P31_natDegree : P31.natDegree = 31 :=
  natDegree_eq_of_degree_eq_some P31_degree

theorem P31_monic : P31.Monic := by
  have hne : P31 ≠ 0 := fun h => by have := P31_natDegree; simp [h] at this
  have hlc : P31.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  rw [Monic.def]
  generalize P31.leadingCoeff = c at hlc
  revert c; decide

theorem eval_one_P31 : P31.eval 1 = 1 := by
  simp [P31]; decide

theorem irreducible_X_add_one : Irreducible (X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_eq_one
  simpa using degree_X_add_C (1 : ZMod 2)

/-- `2^31 - 1 = 2147483647` is prime (Euler, 1772), certified via Lucas–Lehmer. -/
theorem prime_mersenne_31 : (2 ^ 31 - 1).Prime := by
  simpa [mersenne] using lucas_lehmer_sufficiency 31 (by simp) (by norm_num)

theorem isUnit_π_X : IsUnit (π X) := by
  have h : IsUnit (π X ^ 8) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact π_P_xInv8)
  exact (isUnit_pow_iff (by norm_num)).mp h

theorem π_X_pow_mersenne : π X ^ (2 ^ 31 - 1) = 1 := by
  have h : powMod x1 (2 ^ 31 - 1) = 0x80000000 := by decide +kernel
  rw [π_X_pow, h, P_one, map_one]

theorem π_X_ne_one : π X ≠ 1 := by
  intro h
  have h' : π X = π 1 := by simpa using h
  have eq := eq_of_π_eq (by rw [degree_X]; decide) (by rw [degree_one]; decide) h'
  have hc := congrArg (fun p => p.coeff 1) eq
  simp only [coeff_X_one, coeff_one] at hc
  exact one_ne_zero hc

/-- The multiplicative order of `X` modulo `G` is `2^31 - 1 = 2147483647`. -/
theorem orderOf_π_X : orderOf (π X) = 2 ^ 31 - 1 := by
  have hdvd : orderOf (π X) ∣ 2 ^ 31 - 1 := orderOf_dvd_of_pow_eq_one π_X_pow_mersenne
  rcases prime_mersenne_31.eq_one_or_self_of_dvd _ hdvd with h1 | hself
  · exact absurd (orderOf_eq_one_iff.mp h1) π_X_ne_one
  · exact hself

/-- `P31` is irreducible over `GF(2)`. Because `P31 ∣ X^(2^31 - 1) - 1` and both
`31` and `2^31 - 1` are prime, any proper irreducible factor of degree `d < 31`
would satisfy `gcd(2^d - 1, 2^31 - 1) = 2^gcd(d, 31) - 1 = 1`, forcing `X ≡ 1`
and contradicting `P31(1) = 1`. -/
theorem irreducible_P31 : Irreducible P31 := by
  have hne : P31 ≠ 0 := P31_monic.ne_zero
  have hnu : ¬ IsUnit P31 := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, P31_degree]; decide
  obtain ⟨q, hq, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hne
  have hq0 : q ≠ 0 := hq.ne_zero
  have hd_le : q.natDegree ≤ 31 := by
    rw [← P31_natDegree]; exact Polynomial.natDegree_le_of_dvd hdvd hne
  have hd_pos : 0 < q.natDegree := by
    by_contra h0
    have hdeg0 : q.natDegree = 0 := by omega
    rw [eq_one_of_natDegree_eq_zero hdeg0 hq0] at hq
    exact hq.not_isUnit isUnit_one
  by_cases hd31 : q.natDegree = 31
  · obtain ⟨u, hu⟩ := hdvd
    have hu0 : u ≠ 0 := right_ne_zero_of_mul (hu ▸ hne)
    have hdeg := Polynomial.natDegree_mul hq0 hu0
    rw [← hu, P31_natDegree, hd31] at hdeg
    have hu1 : u = 1 := eq_one_of_natDegree_eq_zero (by omega) hu0
    rwa [hu, hu1, mul_one]
  · exfalso
    have hd_lt : q.natDegree < 31 := by omega
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
    have hG0 : G.eval₂ (AdjoinRoot.of q) α = 0 := by
      rw [← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.mpr (dvd_trans hdvd P31_dvd_G)
    let φ : Q →+* K := AdjoinRoot.lift (AdjoinRoot.of q) α hG0
    have hα_m : α ^ (2 ^ 31 - 1) = 1 := by
      have hroot : φ (π X) = α := AdjoinRoot.lift_root hG0
      rw [← hroot, ← map_pow, π_X_pow_mersenne, map_one]
    have hα0 : α ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num)] at hα_m
      exact zero_ne_one hα_m
    have hα_d : α ^ (2 ^ q.natDegree - 1) = 1 := by
      rw [← hcard]
      exact @FiniteField.pow_card_sub_one_eq_one K _ fK α hα0
    have hgcd_dvd : orderOf α ∣ Nat.gcd (2 ^ q.natDegree - 1) (2 ^ 31 - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hα_d) (orderOf_dvd_of_pow_eq_one hα_m)
    have hcop : Nat.Coprime q.natDegree 31 := by
      rw [Nat.coprime_comm]
      exact (show Nat.Prime 31 by decide).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt hd_pos hd_lt)
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hcop.gcd_eq_one] at hgcd_dvd
    have hα1 : α = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd_dvd)
    have hmk : AdjoinRoot.mk q (X + 1) = 0 := by
      rw [map_add, AdjoinRoot.mk_X, map_one]
      change α + 1 = 0
      rw [hα1, h11]
    have hdvd1 : q ∣ X + 1 := AdjoinRoot.mk_eq_zero.mp hmk
    have hx1_ne : (X + 1 : (ZMod 2)[X]) ≠ 0 := by
      intro h; have := degree_X_add_C (1 : ZMod 2); simp [h] at this
    have hdeg_x1 : (X + 1 : (ZMod 2)[X]).natDegree = 1 := natDegree_X_add_C 1
    have hd1 : q.natDegree ≤ 1 := hdeg_x1 ▸ Polynomial.natDegree_le_of_dvd hdvd1 hx1_ne
    have hqd1 : q.natDegree = 1 := by omega
    obtain ⟨w, hw⟩ := hdvd1
    have hw0 : w ≠ 0 := right_ne_zero_of_mul (by rwa [← hw])
    have hm := Polynomial.natDegree_mul hq0 hw0
    rw [← hw, hdeg_x1, hqd1] at hm
    have hw1 : w = 1 := eq_one_of_natDegree_eq_zero (by omega) hw0
    rw [hw1, mul_one] at hw
    rw [← hw] at hdvd
    obtain ⟨t, ht⟩ := hdvd
    have hev := congrArg (eval 1) ht
    rw [eval_one_P31, eval_mul, eval_add, eval_X, eval_one] at hev
    have : (1 + 1 : ZMod 2) = 0 := rfl
    rw [this, zero_mul] at hev
    exact one_ne_zero hev

theorem isCoprime_X_add_one_P31 : IsCoprime (X + 1 : (ZMod 2)[X]) P31 := by
  refine (irreducible_X_add_one.coprime_iff_not_dvd).mpr fun hdvd => ?_
  obtain ⟨t, ht⟩ := hdvd
  have hev := congrArg (eval 1) ht
  rw [eval_one_P31, eval_mul, eval_add, eval_X, eval_one] at hev
  have : (1 + 1 : ZMod 2) = 0 := rfl
  rw [this, zero_mul] at hev
  exact one_ne_zero hev

/-- `P31` is primitive: `X` has multiplicative order `2^31 - 1` modulo `P31`, so
it generates the whole unit group of the field `GF(2)[X]/(P31)`. -/
theorem orderOf_root_P31 : orderOf (AdjoinRoot.root P31) = 2 ^ 31 - 1 := by
  have hG0 : G.eval₂ (AdjoinRoot.of P31) (AdjoinRoot.root P31) = 0 := by
    rw [← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.mpr P31_dvd_G
  have hpow : AdjoinRoot.root P31 ^ (2 ^ 31 - 1) = 1 := by
    have hroot : AdjoinRoot.lift (AdjoinRoot.of P31) _ hG0 (π X) = AdjoinRoot.root P31 :=
      AdjoinRoot.lift_root hG0
    rw [← hroot, ← map_pow, π_X_pow_mersenne, map_one]
  rcases prime_mersenne_31.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h1 | h
  · exfalso
    have hα1 := orderOf_eq_one_iff.mp h1
    have hmk : AdjoinRoot.mk P31 (X + 1) = 0 := by
      rw [map_add, AdjoinRoot.mk_X, map_one, hα1,
        ← map_one (AdjoinRoot.mk P31), ← map_add, CharTwo.add_self_eq_zero, map_zero]
    have hx1_ne : (X + 1 : (ZMod 2)[X]) ≠ 0 := by
      intro h; have := degree_X_add_C (1 : ZMod 2); simp [h] at this
    have hle := Polynomial.natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp hmk) hx1_ne
    have hdeg_x1 : (X + 1 : (ZMod 2)[X]).natDegree = 1 := natDegree_X_add_C 1
    rw [P31_natDegree, hdeg_x1] at hle
    omega
  · exact h

/-- `G` is squarefree in `GF(2)[X]`. -/
theorem squarefree_G : Squarefree G := by
  rw [G_eq_mul_P31, squarefree_mul_iff]
  exact ⟨isCoprime_X_add_one_P31.isRelPrime, irreducible_X_add_one.squarefree,
    irreducible_P31.squarefree⟩

/-! ### Exact classification, minimality, and uniqueness of 2-term multiples -/

/-- `G ∣ X^n + 1` iff `n` is a multiple of `2^31 - 1`. -/
theorem dvd_X_pow_add_one_iff (n : Nat) : G ∣ X ^ n + 1 ↔ (2 ^ 31 - 1) ∣ n := by
  rw [← AdjoinRoot.mk_eq_zero, ← π, map_add, map_pow, map_one, ← orderOf_π_X,
    orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    have := congrArg (· + 1) h
    simpa only [add_assoc, Q_add_self, add_zero, zero_add] using this
  · intro h
    rw [h]
    exact Q_add_self 1

/-- `G ∣ X^a + X^b` (for `b ≤ a`) iff `2^31 - 1` divides `a - b`. -/
theorem dvd_X_pow_add_X_pow_iff {a b : Nat} (h : b ≤ a) :
    G ∣ X ^ a + X ^ b ↔ (2 ^ 31 - 1) ∣ (a - b) := by
  have hfac : (X ^ a + X ^ b : (ZMod 2)[X]) = X ^ b * (X ^ (a - b) + 1) := by
    rw [mul_add, mul_one, ← pow_add, Nat.add_sub_of_le h]
  have hequiv : G ∣ X ^ a + X ^ b ↔ G ∣ X ^ (a - b) + 1 := by
    rw [hfac, ← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.mk_eq_zero, ← π, map_mul, map_pow,
      (isUnit_π_X.pow b).mul_right_eq_zero]
  rw [hequiv, dvd_X_pow_add_one_iff]

/-- **Minimality of `zero2_mersenne`.** Every nonzero multiple of `G` with fewer
than four terms has degree at least `2^31 - 1 = 2147483647`. -/
theorem zero2_minimal {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 4) : 2 ^ 31 - 1 ≤ p.natDegree := by
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
  have hpos : 0 < p.support.card := Finset.card_pos.mpr (support_nonempty.mpr hp)
  have hcard2 : p.support.card = 2 := by omega
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp hcard2
  have hp_eq : p = X ^ a + X ^ b := by
    rw [as_sum_support_X_pow p, hsupp, Finset.sum_pair hab]
  wlog hba : b ≤ a generalizing a b
  · rw [add_comm] at hp_eq
    rw [Finset.pair_comm] at hsupp
    exact this b a hab.symm hsupp hp_eq (by omega)
  have hlt : b < a := lt_of_le_of_ne hba (Ne.symm hab)
  have hdvd := (dvd_X_pow_add_X_pow_iff hba).mp (hp_eq ▸ hG)
  have hle_sub : 2 ^ 31 - 1 ≤ a - b := Nat.le_of_dvd (by omega) hdvd
  have ha_le : a ≤ p.natDegree := le_natDegree_of_mem_supp a (by rw [hsupp]; simp)
  omega

/-- **Uniqueness of `zero2_mersenne`.** `X^2147483647 + 1` is the unique nonzero
multiple of `G` of degree at most `2^31 - 1` with fewer than four terms. -/
theorem zero2_unique {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 4) (hd : p.natDegree ≤ 2 ^ 31 - 1) :
    p = X ^ 2147483647 + 1 := by
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
  have hpos : 0 < p.support.card := Finset.card_pos.mpr (support_nonempty.mpr hp)
  have hcard2 : p.support.card = 2 := by omega
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp hcard2
  have hp_eq : p = X ^ a + X ^ b := by
    rw [as_sum_support_X_pow p, hsupp, Finset.sum_pair hab]
  wlog hba : b ≤ a generalizing a b
  · rw [add_comm] at hp_eq
    rw [Finset.pair_comm] at hsupp
    exact this b a hab.symm hsupp hp_eq (by omega)
  have hlt : b < a := lt_of_le_of_ne hba (Ne.symm hab)
  have hdvd := (dvd_X_pow_add_X_pow_iff hba).mp (hp_eq ▸ hG)
  have hle_sub : 2 ^ 31 - 1 ≤ a - b := Nat.le_of_dvd (by omega) hdvd
  have ha_le : a ≤ p.natDegree := le_natDegree_of_mem_supp a (by rw [hsupp]; simp)
  rw [mersenne31_eq] at hle_sub hd
  have hb0 : b = 0 := by omega
  have haM : a = 2147483647 := by omega
  rw [hp_eq, hb0, pow_zero]
  exact congrArg (· + 1) (congrArg (X ^ ·) haM)

/-! ### Frobenius invariance and word-aligned `Z(X^(2^k))` zero polynomials -/

private theorem frobenius_zmod2 : frobenius (ZMod 2) 2 = RingHom.id (ZMod 2) := by
  ext x; revert x; decide

/-- Over `GF(2)`, substituting `X ↦ X^(2^k)` equals raising to the `2^k`-th power. -/
theorem expand_two_pow_eq_pow (k : Nat) (p : (ZMod 2)[X]) :
    expand (ZMod 2) (2 ^ k) p = p ^ (2 ^ k) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, expand_mul, ih (expand (ZMod 2) 2 p)]
    have h2 : expand (ZMod 2) 2 p = p ^ 2 := by
      have := map_frobenius_expand (p := 2) p
      simpa [frobenius_zmod2] using this
    rw [h2, ← pow_mul, mul_comm]

/-- Because `G` is squarefree, `G ∣ p^2 ↔ G ∣ p`. -/
theorem dvd_sq_iff (p : (ZMod 2)[X]) : G ∣ p ^ 2 ↔ G ∣ p := by
  constructor
  · intro h
    rw [G_eq_mul_P31] at h ⊢
    have h1 : (X + 1 : (ZMod 2)[X]) ∣ p :=
      irreducible_X_add_one.prime.dvd_of_dvd_pow ((dvd_mul_right (X + 1) P31).trans h)
    have h2 : P31 ∣ p :=
      irreducible_P31.prime.dvd_of_dvd_pow ((dvd_mul_left P31 (X + 1)).trans h)
    exact isCoprime_X_add_one_P31.mul_dvd h1 h2
  · intro h
    rw [sq]
    exact dvd_mul_of_dvd_left h p

/-- Frobenius invariance: `G ∣ p(X^(2^k)) ↔ G ∣ p(X)`. -/
theorem dvd_expand_two_pow_iff (k : Nat) (p : (ZMod 2)[X]) :
    G ∣ expand (ZMod 2) (2 ^ k) p ↔ G ∣ p := by
  rw [expand_two_pow_eq_pow]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, dvd_sq_iff, ih]

/-- Every polynomial whose support lies in multiples of `m > 0` is `expand m q`
for `q = contract m P`, preserving support cardinality and scaling degree by `m`. -/
theorem eq_expand_contract_of_dvd_support {m : Nat} (hm : 0 < m) {P : (ZMod 2)[X]}
    (hsupp : ∀ s ∈ P.support, m ∣ s) :
    expand (ZMod 2) m (P.contract m) = P := by
  ext n
  rw [coeff_expand hm]
  split_ifs with h
  · rw [coeff_contract hm.ne', Nat.div_mul_cancel h]
  · symm
    by_contra hne
    exact h (hsupp n (mem_support_iff.mpr hne))

theorem card_support_expand {m : Nat} (hm : 0 < m) (p : (ZMod 2)[X]) :
    (expand (ZMod 2) m p).support.card = p.support.card := by
  have heq : (expand (ZMod 2) m p).support = p.support.map ⟨(· * m), mul_left_injective₀ hm.ne'⟩ := by
    ext n
    simp only [mem_support_iff, Finset.mem_map, Function.Embedding.coeFn_mk]
    rw [coeff_expand hm]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [mul_comm m k, Nat.mul_div_cancel _ hm]
      exact ⟨fun hne => ⟨k, hne, rfl⟩, fun ⟨k', hk', heq⟩ => by
        have := mul_left_injective₀ hm.ne' heq; subst this; exact hk'⟩
    · simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
      intro k _ rfl
      exact h ⟨k, mul_comm k m⟩
  rw [heq, Finset.card_map]

end

end Crc32c
