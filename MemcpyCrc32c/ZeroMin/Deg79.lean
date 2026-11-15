/-
Minimality and uniqueness of the 8-term zero polynomial `zero8_79`:
`X^79 + X^75 + X^71 + X^58 + X^18 + X^12 + X + 1` has the least degree of any
nonzero multiple of `G` with fewer than ten terms (hence CRC32C achieves
Hamming distance 10 up to codeword degree 78), and it is unique at degree 79.

Multiples with `< 8` terms already have degree `≥ 209 > 79` (`zero6_209_minimal`),
and odd weights are impossible (`even_card_support_of_dvd_G`), leaving only exact
8-term multiples (`k = 7` positive shifts in `1..78`). Splitting `1..78` into
`1..39` and `40..78` reduces the 4-term probes against the `C(78, 3) = 76,076`
3-sum table to `2 × C(39, 4) = 164,502`.
-/
import MemcpyCrc32c.ZeroMin.Deg209

namespace Crc32c
open Polynomial
open scoped List

namespace ZeroMin.Deg79
open ZeroMin

def tableKeys : List Nat := tripleSums (resNat 78 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg79_residues%" : term =>
  return toExpr (resNat 78 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg79_trie%" : term =>
  return (Trie.build 32 tableKeys).toExpr

open Lean Elab Term in
elab "deg79_bits_lo%" : term =>
  return mkRawNatLit (bitset (· % 262144) tableKeys)

open Lean Elab Term in
elab "deg79_bits_hi%" : term =>
  return mkRawNatLit (bitset (· / 16384) tableKeys)

set_option maxRecDepth 1500000

def resL : List Nat := deg79_residues%
def table : Trie := deg79_trie%
def bitsLo : Nat := deg79_bits_lo%
def bitsHi : Nat := deg79_bits_hi%

noncomputable def inTable (v : Nat) : Bool :=
  inTable18 bitsLo bitsHi table v

theorem resL_eq : resL = resNat 78 (stepBit 0x80000000) := by decide +kernel

theorem resL_eq_map : resL = (List.range' 1 78).map fun i => (ρ i).toNat := by
  rw [resL_eq, ← resNat_ρ]; rfl

theorem triplesIn_resL : triplesIn inTable resL = true := by decide +kernel

def resLo : List Nat := resL.take 39
def resHi : List Nat := resL.drop 39

theorem lo_c0 : loop4n inTable 2147483648 12 (resLo.drop 0) = true := by decide +kernel
theorem lo_c1 : loop4n inTable 2147483648 27 (resLo.drop 12) = true := by decide +kernel

theorem hi_c0 : loop4n inTable 2147483648 12 (resHi.drop 0) = true := by decide +kernel
theorem hi_c1 : loop4n inTable 2147483648 27 (resHi.drop 12) = true := by decide +kernel

private theorem chunk_step (l : List Nat) (j n : Nat)
    (h1 : loop4n inTable 2147483648 n (l.drop j) = true)
    (h2 : loop4 inTable 2147483648 (l.drop (j + n)) = true) :
    loop4 inTable 2147483648 (l.drop j) = true :=
  loop4n_drop h1 (by rwa [List.drop_drop])

theorem loop4_resLo : loop4 inTable 2147483648 resLo = true :=
  chunk_step resLo 0 12 lo_c0 (chunk_step resLo 12 27 lo_c1 (by rfl))

theorem loop4_resHi : loop4 inTable 2147483648 resHi = true :=
  chunk_step resHi 0 12 hi_c0 (chunk_step resHi 12 27 hi_c1 (by rfl))

/-! ### Uniqueness certificate at degree 79 -/

def target79 : Nat := ((0x80000000 : UInt32) ^^^ ρ 79).toNat

def inW79 (x : Nat) : Bool :=
  Nat.beq x (ρ 1).toNat || Nat.beq x (ρ 12).toNat || Nat.beq x (ρ 18).toNat ||
    Nat.beq x (ρ 58).toNat || Nat.beq x (ρ 71).toNat || Nat.beq x (ρ 75).toNat

theorem uniq79_loop : loop3_uniq inTable inW79 target79 resL = true := by decide +kernel

theorem filter_w79 :
    (List.range' 1 78).filter (fun i => inW79 (ρ i).toNat) = [1, 12, 18, 58, 71, 75] := by
  decide +kernel

end ZeroMin.Deg79

open ZeroMin ZeroMin.Deg79 in
/-- **Minimality of `zero8_79`.** Every nonzero multiple of `G` with fewer than
ten terms has degree at least 79. -/
theorem zero8_79_minimal {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 10) : 79 ≤ p.natDegree := by
  by_contra hd
  by_cases hw8 : p.support.card < 8
  · have := zero6_209_minimal hp hG hw8; omega
  · obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
    have hcard8 : p.support.card = 8 := by omega
    obtain ⟨m, ts, _, hpw, hlen, hmem, hxor⟩ := exists_shifted_relation hp hG
    have hts7 : ts.length = 7 := by omega
    have hsub : ts <+ List.range' 1 78 :=
      sublist_range_of_pairwise_lt hpw fun t ht => by
        obtain ⟨h1, _, hle⟩ := hmem t ht
        exact ⟨h1, by omega⟩
    match ts, hts7 with
    | [t1, t2, t3, t4, t5, t6, t7], _ =>
      have hus : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat,
          (ρ t5).toNat, (ρ t6).toNat, (ρ t7).toNat] <+ resL := by
        rw [resL_eq_map]; simpa using hsub.map (fun i => (ρ i).toNat)
      have hs_split : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat, (ρ t4).toNat,
          (ρ t5).toNat, (ρ t6).toNat, (ρ t7).toNat] <+ resLo ++ resHi := by
        simpa [resLo, resHi, List.take_append_drop] using hus
      have HT := triplesIn_spec triplesIn_resL
      rcases sublist7_split hs_split with ⟨h14, h57⟩ | ⟨h13, h47⟩
      · simp only [resLo, resHi, List.take_append_drop] at h57
        have hf := loop4_spec loop4_resLo _ _ _ _ h14
        have ht := HT _ _ _ h57
        have eq := foldr_map_xor7_left (fun i => (ρ i).toNat) 2147483648 hxor
        rw [eq, ht] at hf; cases hf
      · simp only [resLo, resHi, List.take_append_drop] at h13
        have hf := loop4_spec loop4_resHi _ _ _ _ h47
        have ht := HT _ _ _ h13
        have eq := foldr_map_xor7_right (fun i => (ρ i).toNat) 2147483648 hxor
        rw [eq, ht] at hf; cases hf

open ZeroMin ZeroMin.Deg79 in
/-- **Uniqueness of `zero8_79`.** `X^79 + X^75 + X^71 + X^58 + X^18 + X^12 + X + 1`
is the unique nonzero multiple of `G` of degree at most 79 with fewer than ten
terms. -/
theorem zero8_79_unique {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 10) (hd : p.natDegree ≤ 79) :
    p = X ^ 79 + X ^ 75 + X ^ 71 + X ^ 58 + X ^ 18 + X ^ 12 + X + 1 := by
  obtain ⟨h0_mem, hdeg⟩ := zero_mem_and_natDegree_eq_of_minimal hp hd fun m _ hm =>
    zero8_79_minimal (shiftDown_ne_zero hp hm) (dvd_shiftDown_of_dvd hG hm)
      (by rwa [card_support_shiftDown hm])
  have hw8 : ¬ p.support.card < 8 := fun h => by
    have := zero6_209_minimal hp hG h; omega
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
  have hcard8 : p.support.card = 8 := by omega
  obtain ⟨ts, hsub, hcard, _, hp_eq, hxor⟩ :=
    exists_interior_relation (by omega) hp hG h0_mem hdeg
  have hts6 : ts.length = 6 := by omega
  change target79 ^^^ (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0 at hxor
  have HT := triplesIn_spec triplesIn_resL
  have HU := loop3_uniq_spec uniq79_loop
  match ts, hts6 with
  | [t1, t2, t3, t4, t5, t6], _ =>
    have hus : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat,
        (ρ t4).toNat, (ρ t5).toNat, (ρ t6).toNat] <+ resL := by
      rw [resL_eq_map]; simpa using hsub.map (fun i => (ρ i).toNat)
    have h13 : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat] <+ resL :=
      (List.sublist_append_left [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat] _).trans hus
    have h46 : [(ρ t4).toNat, (ρ t5).toNat, (ρ t6).toNat] <+ resL :=
      (List.sublist_append_right [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat] _).trans hus
    have eqL := foldr_map_xor6_left (fun i => (ρ i).toNat) target79 hxor
    have eqR := foldr_map_xor6_right (fun i => (ρ i).toNat) target79 hxor
    obtain ⟨hw1, hw2, hw3⟩ := HU _ _ _ h13 (eqL ▸ HT _ _ _ h46)
    obtain ⟨hw4, hw5, hw6⟩ := HU _ _ _ h46 (eqR ▸ HT _ _ _ h13)
    have hts_eq : [t1, t2, t3, t4, t5, t6] = [1, 12, 18, 58, 71, 75] := by
      refine eq_of_sublist_of_all_inW hsub ?_ filter_w79 rfl
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    rw [hts_eq] at hp_eq
    simp only [List.map, List.sum_cons, List.sum_nil, add_zero, pow_one] at hp_eq
    rw [hp_eq]; ring

end Crc32c
