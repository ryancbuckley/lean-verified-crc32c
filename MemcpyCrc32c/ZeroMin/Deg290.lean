/-
Minimality and uniqueness of the 6-term zero polynomial `zero6_290`:
`X^290 + X^136 + X^113 + X^107 + X^32 + 1` has the least degree of any nonzero
multiple of `G` with fewer than eight terms whose leading gap is at least 128
(two 64-bit words, enabling the zero-shift `n1' = n2` update in the 5-word
portable Chorba loop), and it is unique at degree 290.

After dividing out `X^m` via `shiftDown`, `zero6_209_minimal` forces the
normalized degree `E` into `209..289` with `0 ∈ support`. Splitting `E` at 270
separates the only two weight-6 multiples of `G` in `209..289` whose lower
exponents are `≤ 161` (`E = 209` with `d = 144`, and `E = 266` with `d = 143`)
from the range where `143` and `144` satisfy `d + 128 ≤ E`:
- Band 1 (`209 ≤ E ≤ 270`): all four interior exponents lie in `1..142`.
- Band 2 (`271 ≤ E ≤ 289`): all four interior exponents lie in `1..161`.
-/
import MemcpyCrc32c.ZeroMin.Deg209
import MemcpyCrc32c.ZeroMin.Deg290Cert

namespace Crc32c
open Polynomial
open scoped List

namespace ZeroMin.Deg290
open ZeroMin

theorem pairwise_of_sublist {α : Type*} {R : α → α → Prop} {l₁ l₂ : List α}
    (hs : l₁ <+ l₂) (hp : l₂.Pairwise R) : l₁.Pairwise R := by
  induction hs with
  | slnil => exact .nil
  | cons _ _ ih => exact ih (List.pairwise_cons.mp hp).2
  | cons_cons _ hs ih =>
    exact List.pairwise_cons.mpr ⟨fun x hx => (List.pairwise_cons.mp hp).1 x (hs.subset hx),
      ih (List.pairwise_cons.mp hp).2⟩

theorem gap_shiftDown {p : (ZMod 2)[X]} {m : Nat} (hp : p ≠ 0)
    (hm : ∀ s ∈ p.support, m ≤ s)
    (hgap : ∀ s ∈ p.support, s ≠ p.natDegree → s + 128 ≤ p.natDegree) :
    ∀ k ∈ (shiftDown m p).support, k ≠ (shiftDown m p).natDegree →
      k + 128 ≤ (shiftDown m p).natDegree := by
  intro k hk hne
  have hdeg := natDegree_shiftDown_add hp hm
  have hkm : k + m ∈ p.support := by
    rw [← support_shiftDown_map hm]
    exact Finset.mem_map.mpr ⟨k, hk, rfl⟩
  have hg := hgap (k + m) hkm (by omega)
  omega

theorem htgt_eq_lem (E : Nat) :
    ((0x80000000 : UInt32) ^^^ ρ E).toNat = 2147483648 ^^^ (ρ E).toNat :=
  UInt32.toNat_xor _ _

theorem mem_map_xor_of_eq {c E n k : Nat} {targets : List Nat}
    (ht : targets = (resNat n (ρ k)).map (Nat.xor c))
    (hlo : k ≤ E) (hhi : E < k + n) :
    c ^^^ (ρ E).toNat ∈ targets := by
  rw [ht, resNat_ρ, List.map_map]
  exact List.mem_map.mpr ⟨E, List.mem_range'_1.mpr ⟨hlo, hhi⟩, rfl⟩

theorem mem_targetsAll {E : Nat} (hE_lo : 209 ≤ E) (hE_hi : E ≤ 289) :
    2147483648 ^^^ (ρ E).toNat ∈ targetsAll :=
  mem_map_xor_of_eq targetsAll_eq hE_lo (by omega)

theorem mem_targetsB1 {E : Nat} (hE_lo : 209 ≤ E) (hE270 : E ≤ 270) :
    2147483648 ^^^ (ρ E).toNat ∈ targetsB1 :=
  mem_map_xor_of_eq targetsB1_eq hE_lo (by omega)

theorem mem_targetsB2 {E : Nat} (hE271 : ¬ E ≤ 270) (hE_hi : E ≤ 289) :
    2147483648 ^^^ (ρ E).toNat ∈ targetsB2 :=
  mem_map_xor_of_eq targetsB2_eq (by omega) (by omega)

theorem case4_b1 {E t1 t2 t3 t4 : Nat}
    (htgt_b1 : 2147483648 ^^^ (ρ E).toNat ∈ targetsB1)
    (hus : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ res142)
    (hxor : (2147483648 ^^^ (ρ E).toNat) ^^^
      ([t1, t2, t3, t4].map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0) : False := by
  have hs_split : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+
      res142Lo ++ res142Hi := by
    rw [res142Lo, res142Hi, List.take_append_drop]; exact hus
  rcases sublist4_split hs_split with ⟨h12, h34⟩ | ⟨h12, h34⟩
  · rw [res142Lo, res142Hi, List.take_append_drop] at h34
    have hf := bandLoop_spec band1_lo _ htgt_b1 _ _ h12
    have ht := pairsIn_spec pairsIn_res142 _ _ h34
    have eq := foldr_map_xor4_left (fun i => (ρ i).toNat) (2147483648 ^^^ (ρ E).toNat) hxor
    rw [eq, ht] at hf; cases hf
  · rw [res142Lo, res142Hi, List.take_append_drop] at h12
    have hf := bandLoop_spec band1_hi _ htgt_b1 _ _ h34
    have ht := pairsIn_spec pairsIn_res142 _ _ h12
    have eq := foldr_map_xor4_right (fun i => (ρ i).toNat) (2147483648 ^^^ (ρ E).toNat) hxor
    rw [eq, ht] at hf; cases hf

theorem case4_b2 {E t1 t2 t3 t4 : Nat}
    (htgt_b2 : 2147483648 ^^^ (ρ E).toNat ∈ targetsB2)
    (hus161 : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ res161)
    (hus162 : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ res162)
    (hxor : (2147483648 ^^^ (ρ E).toNat) ^^^
      ([t1, t2, t3, t4].map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0) : False := by
  have hs_split : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+
      res161Lo ++ res161Hi := by
    rw [res161Lo, res161Hi, List.take_append_drop]; exact hus161
  rcases sublist4_split hs_split with ⟨h12, _⟩ | ⟨_, h34⟩
  · have h34_162 : [(ρ t3).toNat, (ρ t4).toNat] <+ res162 :=
      (List.sublist_append_right [(ρ t1).toNat, (ρ t2).toNat] _).trans hus162
    have hf := bandLoop_spec band2_lo _ htgt_b2 _ _ h12
    have ht := pairsIn_spec pairsIn_res162 _ _ h34_162
    have eq := foldr_map_xor4_left (fun i => (ρ i).toNat) (2147483648 ^^^ (ρ E).toNat) hxor
    rw [eq, ht] at hf; cases hf
  · have h12_162 : [(ρ t1).toNat, (ρ t2).toNat] <+ res162 :=
      (List.sublist_append_left [(ρ t1).toNat, (ρ t2).toNat] _).trans hus162
    have hf := bandLoop_spec band2_hi _ htgt_b2 _ _ h34
    have ht := pairsIn_spec pairsIn_res162 _ _ h12_162
    have eq := foldr_map_xor4_right (fun i => (ρ i).toNat) (2147483648 ^^^ (ρ E).toNat) hxor
    rw [eq, ht] at hf; cases hf

/-- Helper over opaque parameters `q` and `E`. -/
theorem zero6_290_minimal_aux {q : (ZMod 2)[X]} {E : Nat}
    (hq0 : q ≠ 0) (hGq : G ∣ q) (hq_card : q.support.card < 8)
    (h0_mem : 0 ∈ q.support) (hdeg : q.natDegree = E)
    (hE_lo : 209 ≤ E) (hE_hi : E ≤ 289)
    (hq_gap : ∀ k ∈ q.support, k ≠ E → k + 128 ≤ E) : False := by
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hGq
  obtain ⟨ts, hsubE, hcard, hts_supp, _, hxor⟩ :=
    exists_interior_relation (by omega) hq0 hGq h0_mem hdeg
  have hpw : ts.Pairwise (· < ·) := pairwise_of_sublist hsubE List.pairwise_lt_range'
  have ht_gap : ∀ t ∈ ts, 1 ≤ t ∧ t + 128 ≤ E := fun t ht => by
    have hr := List.mem_range'_1.mp (hsubE.subset ht)
    exact ⟨hr.1, hq_gap t (hts_supp t ht) (by omega)⟩
  have hts_even : ts.length = 0 ∨ ts.length = 2 ∨ ts.length = 4 := by omega
  have htgt_all := mem_targetsAll hE_lo hE_hi
  have Hshort := loop1_spec no_short_290 _ htgt_all
  rw [Nat.zero_xor] at Hshort
  rw [htgt_eq_lem E] at hxor
  rcases hts_even with h0 | h2 | h4
  · rw [List.length_eq_zero_iff.mp h0] at hxor
    have hxor0 := foldr_map_xor0 (fun i => (ρ i).toNat) (2147483648 ^^^ (ρ E).toNat) hxor
    rw [hxor0, inTable162_zero] at Hshort; cases Hshort
  · obtain ⟨t1, t2, hts⟩ := List.length_eq_two.mp h2
    have hsub162 : ts <+ List.range' 1 162 :=
      sublist_range_of_pairwise_lt hpw fun t ht =>
        ⟨(ht_gap t ht).1, by have := (ht_gap t ht).2; omega⟩
    have hus : [(ρ t1).toNat, (ρ t2).toNat] <+ res162 := by
      rw [res162_eq_map]; simpa [hts] using hsub162.map (fun i => (ρ i).toNat)
    rw [hts] at hxor
    have heq := foldr_map_xor2_eq (fun i => (ρ i).toNat) (2147483648 ^^^ (ρ E).toNat) hxor
    rw [heq, pairsIn_spec pairsIn_res162 _ _ hus] at Hshort; cases Hshort
  · match ts, h4 with
    | [t1, t2, t3, t4], _ =>
      by_cases hE270 : E ≤ 270
      · have hsub142 : [t1, t2, t3, t4] <+ List.range' 1 142 :=
          sublist_range_of_pairwise_lt hpw fun t ht =>
            ⟨(ht_gap t ht).1, by have := (ht_gap t ht).2; omega⟩
        have hus : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ res142 := by
          rw [res142_eq_map]; exact hsub142.map (fun i => (ρ i).toNat)
        exact case4_b1 (mem_targetsB1 hE_lo hE270) hus hxor
      · have hsub161 : [t1, t2, t3, t4] <+ List.range' 1 161 :=
          sublist_range_of_pairwise_lt hpw fun t ht =>
            ⟨(ht_gap t ht).1, by have := (ht_gap t ht).2; omega⟩
        have hsub162 : [t1, t2, t3, t4] <+ List.range' 1 162 :=
          sublist_range_of_pairwise_lt hpw fun t ht =>
            ⟨(ht_gap t ht).1, by have := (ht_gap t ht).2; omega⟩
        have hus161 : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ res161 := by
          rw [res161_eq_map]; exact hsub161.map (fun i => (ρ i).toNat)
        have hus162 : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ res162 := by
          rw [res162_eq_map]; exact hsub162.map (fun i => (ρ i).toNat)
        exact case4_b2 (mem_targetsB2 hE270 hE_hi) hus161 hus162 hxor

end ZeroMin.Deg290

open ZeroMin ZeroMin.Deg290 in
/-- **Minimality of `zero6_290`.** Every nonzero multiple of `G` with fewer than
eight terms whose non-leading exponents are at distance at least 128 from the
degree has degree at least 290. -/
theorem zero6_290_minimal {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 8)
    (hgap : ∀ s ∈ p.support, s ≠ p.natDegree → s + 128 ≤ p.natDegree) :
    290 ≤ p.natDegree := by
  by_contra hd
  obtain ⟨m, hm_mem, hm_le⟩ : ∃ m ∈ p.support, ∀ s ∈ p.support, m ≤ s :=
    ⟨p.support.min' (support_nonempty.mpr hp), Finset.min'_mem _ _,
      fun s hs => Finset.min'_le _ s hs⟩
  have hq0 : shiftDown m p ≠ 0 := shiftDown_ne_zero hp hm_le
  have hGq : G ∣ shiftDown m p := dvd_shiftDown_of_dvd hG hm_le
  have hq_card : (shiftDown m p).support.card < 8 := by rwa [card_support_shiftDown hm_le]
  have hq_gap := gap_shiftDown hp hm_le hgap
  have hE_lo : 209 ≤ (shiftDown m p).natDegree := zero6_209_minimal hq0 hGq hq_card
  have hdeg_add : (shiftDown m p).natDegree + m = p.natDegree := natDegree_shiftDown_add hp hm_le
  have h0_mem : 0 ∈ (shiftDown m p).support := by
    rw [mem_support_iff, coeff_shiftDown hm_le, zero_add]
    exact mem_support_iff.mp hm_mem
  exact zero6_290_minimal_aux hq0 hGq hq_card h0_mem rfl hE_lo (by omega)
    fun k hk hne => hq_gap k hk hne

open ZeroMin ZeroMin.Deg290 in
/-- **Uniqueness of `zero6_290`.** `X^290 + X^136 + X^113 + X^107 + X^32 + 1` is
the unique nonzero multiple of `G` of degree at most 290 with fewer than eight
terms and leading gap at least 128. -/
theorem zero6_290_unique {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 8)
    (hgap : ∀ s ∈ p.support, s ≠ p.natDegree → s + 128 ≤ p.natDegree)
    (hd : p.natDegree ≤ 290) :
    p = X ^ 290 + X ^ 136 + X ^ 113 + X ^ 107 + X ^ 32 + 1 := by
  obtain ⟨h0_mem, hdeg⟩ := zero_mem_and_natDegree_eq_of_minimal hp hd fun m _ hm =>
    zero6_290_minimal (shiftDown_ne_zero hp hm) (dvd_shiftDown_of_dvd hG hm)
      (by rwa [card_support_shiftDown hm]) (gap_shiftDown hp hm hgap)
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
  obtain ⟨ts, hsubE, hcard, hts_supp, hp_eq, hxor⟩ :=
    exists_interior_relation (by omega) hp hG h0_mem hdeg
  have hpw : ts.Pairwise (· < ·) := pairwise_of_sublist hsubE List.pairwise_lt_range'
  have hsub162 : ts <+ List.range' 1 162 :=
    sublist_range_of_pairwise_lt hpw fun t ht => by
      have hr := List.mem_range'_1.mp (hsubE.subset ht)
      have hg := hgap t (hts_supp t ht) (by omega)
      exact ⟨hr.1, by omega⟩
  have hts_even : ts.length = 0 ∨ ts.length = 2 ∨ ts.length = 4 := by omega
  change target290 ^^^ (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0 at hxor
  have HP := pairsIn_spec pairsIn_res162
  have HU := loop2_uniq_spec uniq290_loop
  rcases hts_even with h0 | h2 | h4
  · rw [List.length_eq_zero_iff.mp h0] at hxor
    have hxor0 := foldr_map_xor0 (fun i => (ρ i).toNat) target290 hxor
    have := target290_not_in; rw [hxor0, inTable162_zero] at this; cases this
  · obtain ⟨t1, t2, hts⟩ := List.length_eq_two.mp h2
    have hus : [(ρ t1).toNat, (ρ t2).toNat] <+ res162 := by
      rw [res162_eq_map]; simpa [hts] using hsub162.map (fun i => (ρ i).toNat)
    rw [hts] at hxor
    have heq := foldr_map_xor2_eq (fun i => (ρ i).toNat) target290 hxor
    have := target290_not_in; rw [heq, HP _ _ hus] at this; cases this
  · match ts, h4 with
    | [t1, t2, t3, t4], _ =>
      have hus : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat] <+ res162 := by
        rw [res162_eq_map]; simpa using hsub162.map (fun i => (ρ i).toNat)
      have h12 : [(ρ t1).toNat, (ρ t2).toNat] <+ res162 :=
        (List.sublist_append_left [(ρ t1).toNat, (ρ t2).toNat] _).trans hus
      have h34 : [(ρ t3).toNat, (ρ t4).toNat] <+ res162 :=
        (List.sublist_append_right [(ρ t1).toNat, (ρ t2).toNat] _).trans hus
      have eqL := foldr_map_xor4_left (fun i => (ρ i).toNat) target290 hxor
      have eqR := foldr_map_xor4_right (fun i => (ρ i).toNat) target290 hxor
      obtain ⟨hw1, hw2⟩ := HU _ _ h12 (eqL ▸ HP _ _ h34)
      obtain ⟨hw3, hw4⟩ := HU _ _ h34 (eqR ▸ HP _ _ h12)
      have hts_eq : [t1, t2, t3, t4] = [32, 107, 113, 136] := by
        refine eq_of_sublist_of_all_inW hsub162 ?_ filter_w290 rfl
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> assumption
      rw [hts_eq] at hp_eq
      simp only [List.map, List.sum_cons, List.sum_nil, add_zero] at hp_eq
      rw [hp_eq]; ring

end Crc32c
