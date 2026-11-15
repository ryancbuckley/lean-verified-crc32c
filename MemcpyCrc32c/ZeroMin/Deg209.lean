/-
Minimality and uniqueness of the 6-term zero polynomial `zero6_209` (degree 209),
together with its 64-bit word-aligned Chorba counterpart `Z(X^64)`.

By `even_card_support_of_dvd_G`, every multiple of `G` has an even number of
terms, so `< 8` terms is equivalent to `≤ 6` terms (`2`, `4`, or `6`). Using a
middle-exponent pigeonhole split on `1..208 = (1..104) ++ (105..208)`, any
5-element sublist `[a, b, c, d, e]` has either `[a, b, c]` in the lower half or
`[c, d, e]` in the upper half, cutting the 3-term probe count by more than 4×
(`2 × C(104, 3) = 364,208` probes instead of `C(208, 3) = 1,478,184`).
-/
import MemcpyCrc32c.ZeroMin.XorLemmas

namespace Crc32c
open Polynomial
open scoped List

namespace ZeroMin.Deg209
open ZeroMin

def tableKeys : List Nat := 0 :: pairSums (resNat 208 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg209_residues%" : term =>
  return toExpr (resNat 208 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg209_trie%" : term =>
  return (Trie.build 32 tableKeys).toExpr

open Lean Elab Term in
elab "deg209_bits_lo%" : term =>
  return mkRawNatLit (bitset (· % 131072) tableKeys)

open Lean Elab Term in
elab "deg209_bits_hi%" : term =>
  return mkRawNatLit (bitset (· / 32768) tableKeys)

set_option maxRecDepth 1000000

def resL : List Nat := deg209_residues%
def table : Trie := deg209_trie%
def bitsLo : Nat := deg209_bits_lo%
def bitsHi : Nat := deg209_bits_hi%

noncomputable def inTable (v : Nat) : Bool :=
  inTable17 bitsLo bitsHi table v

theorem resL_eq : resL = resNat 208 (stepBit 0x80000000) := by decide +kernel

theorem resL_eq_map : resL = (List.range' 1 208).map fun i => (ρ i).toNat := by
  rw [resL_eq, ← resNat_ρ]; rfl

theorem inTable_zero : inTable 0 = true := by decide +kernel
theorem pairsIn_resL : pairsIn inTable resL = true := by decide +kernel
theorem loop1_resL : loop1 inTable 2147483648 resL = true := by decide +kernel
theorem loop2_resL : loop2 inTable 2147483648 resL = true := by decide +kernel

/-! Middle-split 3-term probes on `resL.take 104` and `resL.drop 104` -/

def resLo : List Nat := resL.take 104
def resHi : List Nat := resL.drop 104

theorem lo_c0 : loop3n inTable 2147483648 20 (resLo.drop 0) = true := by decide +kernel
theorem lo_c1 : loop3n inTable 2147483648 30 (resLo.drop 20) = true := by decide +kernel
theorem lo_c2 : loop3n inTable 2147483648 54 (resLo.drop 50) = true := by decide +kernel

theorem hi_c0 : loop3n inTable 2147483648 20 (resHi.drop 0) = true := by decide +kernel
theorem hi_c1 : loop3n inTable 2147483648 30 (resHi.drop 20) = true := by decide +kernel
theorem hi_c2 : loop3n inTable 2147483648 54 (resHi.drop 50) = true := by decide +kernel

private theorem chunk_step (l : List Nat) (j n : Nat)
    (h1 : loop3n inTable 2147483648 n (l.drop j) = true)
    (h2 : loop3 inTable 2147483648 (l.drop (j + n)) = true) :
    loop3 inTable 2147483648 (l.drop j) = true :=
  loop3n_drop h1 (by rwa [List.drop_drop])

theorem loop3_resLo : loop3 inTable 2147483648 resLo = true :=
  chunk_step resLo 0 20 lo_c0 (chunk_step resLo 20 30 lo_c1
    (chunk_step resLo 50 54 lo_c2 (by rfl)))

theorem loop3_resHi : loop3 inTable 2147483648 resHi = true :=
  chunk_step resHi 0 20 hi_c0 (chunk_step resHi 20 30 hi_c1
    (chunk_step resHi 50 54 hi_c2 (by rfl)))

theorem no_relation (us : List Nat) (hs : us <+ resL) (hl : us.length ≤ 5) :
    2147483648 ^^^ us.foldr (· ^^^ ·) 0 ≠ 0 := by
  have H1 := loop1_spec loop1_resL
  have H2 := loop2_spec loop2_resL
  have H3L := loop3_spec loop3_resLo
  have H3H := loop3_spec loop3_resHi
  have HP := pairsIn_spec pairsIn_resL
  have H0 := inTable_zero
  intro h
  match us, hs, hl, h with
  | [], _, _, h => simp at h
  | [a], hs, _, h =>
    have := H1 a (List.singleton_sublist.mp hs)
    simp only [List.foldr, Nat.xor_zero] at h
    rw [h, H0] at this; cases this
  | [a, b], hs, _, h =>
    have := H2 a b hs
    simp only [List.foldr, Nat.xor_zero, ← Nat.xor_assoc] at h
    rw [h, H0] at this; cases this
  | [a, b, c], hs, _, h =>
    have ha : a ∈ resL := hs.subset (by simp)
    have hbc : [b, c] <+ resL := (List.sublist_cons_self a [b, c]).trans hs
    have h1 := H1 a ha
    have h2 := HP b c hbc
    have eq : 2147483648 ^^^ a = b ^^^ c :=
      xor_eq_of_eq_zero (by simp only [List.foldr, Nat.xor_zero] at h ⊢; ac_rfl) h
    rw [eq, h2] at h1; cases h1
  | [a, b, c, d], hs, _, h =>
    have h1 := H2 a b ((List.sublist_append_left [a, b] [c, d]).trans hs)
    have h2 := HP c d ((List.sublist_append_right [a, b] [c, d]).trans hs)
    have eq : 2147483648 ^^^ a ^^^ b = c ^^^ d :=
      xor_eq_of_eq_zero (by simp only [List.foldr, Nat.xor_zero] at h ⊢; ac_rfl) h
    rw [eq, h2] at h1; cases h1
  | [a, b, c, d, e], hs, _, h =>
    have hs_split : [a, b, c, d, e] <+ resLo ++ resHi := by
      simpa [resLo, resHi, List.take_append_drop] using hs
    rcases sublist5_split hs_split with ⟨habc, hde⟩ | ⟨hab, hcde⟩
    · simp only [resLo, resHi, List.take_append_drop] at hde
      have h1 := H3L a b c habc
      have h2 := HP d e hde
      have eq : 2147483648 ^^^ a ^^^ b ^^^ c = d ^^^ e :=
        xor_eq_of_eq_zero (by simp only [List.foldr, Nat.xor_zero] at h ⊢; ac_rfl) h
      rw [eq, h2] at h1; cases h1
    · simp only [resLo, resHi, List.take_append_drop] at hab
      have h1 := H3H c d e hcde
      have h2 := HP a b hab
      have eq : 2147483648 ^^^ c ^^^ d ^^^ e = a ^^^ b :=
        xor_eq_of_eq_zero (by simp only [List.foldr, Nat.xor_zero] at h ⊢; ac_rfl) h
      rw [eq, h2] at h1; cases h1
  | _ :: _ :: _ :: _ :: _ :: _ :: _, _, hl, _ => simp at hl; omega

/-! ### Uniqueness certificate at degree 209 -/

def target209 : Nat := ((0x80000000 : UInt32) ^^^ ρ 209).toNat

def inW209 (x : Nat) : Bool :=
  Nat.beq x (ρ 14).toNat || Nat.beq x (ρ 39).toNat ||
    Nat.beq x (ρ 54).toNat || Nat.beq x (ρ 144).toNat

theorem target209_not_in : inTable target209 = false := by decide +kernel
theorem uniq209_loop : loop2_uniq inTable inW209 target209 resL = true := by decide +kernel
theorem filter_w209 :
    (List.range' 1 208).filter (fun i => inW209 (ρ i).toNat) = [14, 39, 54, 144] := by
  decide +kernel

end ZeroMin.Deg209

open ZeroMin ZeroMin.Deg209 in
/-- **Minimality of `zero6_209`.** Every nonzero multiple of `G` with fewer than
eight terms (equivalently, at most six terms, since every multiple of `G` has
even weight) has degree at least 209. -/
theorem zero6_209_minimal {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 8) : 209 ≤ p.natDegree := by
  by_contra hd
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
  obtain ⟨m, ts, _, hpw, hlen, hmem, hxor⟩ := exists_shifted_relation hp hG
  have hsub : ts <+ List.range' 1 208 :=
    sublist_range_of_pairwise_lt hpw fun t ht => by
      obtain ⟨h1, _, hle⟩ := hmem t ht
      exact ⟨h1, by omega⟩
  refine no_relation (ts.map fun i => (ρ i).toNat) ?_ (by simp; omega) hxor
  rw [resL_eq_map]
  exact hsub.map _

open ZeroMin ZeroMin.Deg209 in
/-- **Uniqueness of `zero6_209`.** `X^209 + X^144 + X^54 + X^39 + X^14 + 1` is
the unique nonzero multiple of `G` of degree at most 209 with fewer than eight
terms. -/
theorem zero6_209_unique {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 8) (hd : p.natDegree ≤ 209) :
    p = X ^ 209 + X ^ 144 + X ^ 54 + X ^ 39 + X ^ 14 + 1 := by
  obtain ⟨h0_mem, hdeg⟩ := zero_mem_and_natDegree_eq_of_minimal hp hd fun m _ hm =>
    zero6_209_minimal (shiftDown_ne_zero hp hm) (dvd_shiftDown_of_dvd hG hm)
      (by rwa [card_support_shiftDown hm])
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
  obtain ⟨ts, hsub, hcard, _, hp_eq, hxor⟩ :=
    exists_interior_relation (by omega) hp hG h0_mem hdeg
  have hts_even : ts.length = 0 ∨ ts.length = 2 ∨ ts.length = 4 := by omega
  change target209 ^^^ (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0 at hxor
  have HP := pairsIn_spec pairsIn_resL
  have HU := loop2_uniq_spec uniq209_loop
  rcases hts_even with h0 | h2 | h4
  · rw [List.length_eq_zero_iff.mp h0] at hxor
    have hxor0 := foldr_map_xor0 (fun i => (ρ i).toNat) target209 hxor
    have := target209_not_in; rw [hxor0, inTable_zero] at this; cases this
  · obtain ⟨t1, t2, hts⟩ := List.length_eq_two.mp h2
    have hus : [(ρ t1).toNat, (ρ t2).toNat] <+ resL := by
      rw [resL_eq_map]; simpa [hts] using hsub.map (fun i => (ρ i).toNat)
    rw [hts] at hxor
    have heq := foldr_map_xor2_eq (fun i => (ρ i).toNat) target209 hxor
    have := target209_not_in; rw [heq, HP _ _ hus] at this; cases this
  · match ts, h4 with
    | [t1, t2, t3, t4], _ =>
      have hus : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ resL := by
        rw [resL_eq_map]; simpa using hsub.map (fun i => (ρ i).toNat)
      have h12 : [(ρ t1).toNat, (ρ t2).toNat] <+ resL :=
        (List.sublist_append_left [(ρ t1).toNat, (ρ t2).toNat] _).trans hus
      have h34 : [(ρ t3).toNat, (ρ t4).toNat] <+ resL :=
        (List.sublist_append_right [(ρ t1).toNat, (ρ t2).toNat] _).trans hus
      have eqL := foldr_map_xor4_left (fun i => (ρ i).toNat) target209 hxor
      have eqR := foldr_map_xor4_right (fun i => (ρ i).toNat) target209 hxor
      obtain ⟨hw1, hw2⟩ := HU _ _ h12 (eqL ▸ HP _ _ h34)
      obtain ⟨hw3, hw4⟩ := HU _ _ h34 (eqR ▸ HP _ _ h12)
      have hts_eq : [t1, t2, t3, t4] = [14, 39, 54, 144] := by
        refine eq_of_sublist_of_all_inW hsub ?_ filter_w209 rfl
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> assumption
      rw [hts_eq] at hp_eq
      simp only [List.map, List.sum_cons, List.sum_nil, add_zero] at hp_eq
      rw [hp_eq]; ring

/-- **Minimality of word-aligned 64-bit zero polynomials.** By Frobenius
invariance (`G ∣ p(X^64) ↔ G ∣ p(X)`), every nonzero multiple of `G` with fewer
than eight terms whose exponents are multiples of 64 has degree at least
`64 * 209 = 13376`. -/
theorem zero6_word64_minimal {P : (ZMod 2)[X]} (hP : P ≠ 0) (hG : G ∣ P)
    (halign : ∀ s ∈ P.support, 64 ∣ s) (hw : P.support.card < 8) :
    64 * 209 ≤ P.natDegree := by
  have h64 : 0 < (64 : Nat) := by norm_num
  have hexp : expand (ZMod 2) 64 (P.contract 64) = P :=
    eq_expand_contract_of_dvd_support h64 halign
  have hq0 : P.contract 64 ≠ 0 := fun h => hP (by rw [← hexp, h, map_zero])
  have hGq : G ∣ P.contract 64 := by
    have hG' : G ∣ expand (ZMod 2) (2 ^ 6) (P.contract 64) := by
      change G ∣ expand (ZMod 2) 64 (P.contract 64)
      rwa [hexp]
    exact (dvd_expand_two_pow_iff 6 _).mp hG'
  have hcard : (P.contract 64).support.card < 8 := by
    rwa [← card_support_expand h64, hexp]
  have hmin := zero6_209_minimal hq0 hGq hcard
  have hdeg : P.natDegree = (P.contract 64).natDegree * 64 := by
    conv_lhs => rw [← hexp]
    exact natDegree_expand 64 (P.contract 64)
  omega

/-- **Uniqueness of word-aligned 64-bit `zero6_209`.** `Z(X^64)` for
`Z = X^209 + X^144 + X^54 + X^39 + X^14 + 1` is the unique nonzero multiple of
`G` of degree at most `64 * 209 = 13376` with fewer than eight 64-bit-aligned
monomials. -/
theorem zero6_word64_unique {P : (ZMod 2)[X]} (hP : P ≠ 0) (hG : G ∣ P)
    (halign : ∀ s ∈ P.support, 64 ∣ s) (hw : P.support.card < 8)
    (hd : P.natDegree ≤ 64 * 209) :
    P = expand (ZMod 2) 64 (X ^ 209 + X ^ 144 + X ^ 54 + X ^ 39 + X ^ 14 + 1) := by
  have h64 : 0 < (64 : Nat) := by norm_num
  have hexp : expand (ZMod 2) 64 (P.contract 64) = P :=
    eq_expand_contract_of_dvd_support h64 halign
  have hq0 : P.contract 64 ≠ 0 := fun h => hP (by rw [← hexp, h, map_zero])
  have hGq : G ∣ P.contract 64 := by
    have hG' : G ∣ expand (ZMod 2) (2 ^ 6) (P.contract 64) := by
      change G ∣ expand (ZMod 2) 64 (P.contract 64)
      rwa [hexp]
    exact (dvd_expand_two_pow_iff 6 _).mp hG'
  have hcard : (P.contract 64).support.card < 8 := by
    rwa [← card_support_expand h64, hexp]
  have hdeg : P.natDegree = (P.contract 64).natDegree * 64 := by
    conv_lhs => rw [← hexp]
    exact natDegree_expand 64 (P.contract 64)
  have hq_eq := zero6_209_unique hq0 hGq hcard (by omega)
  rw [← hexp, hq_eq]

end Crc32c
