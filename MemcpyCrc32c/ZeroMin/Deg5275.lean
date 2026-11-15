/-
Minimality and uniqueness of the 4-term zero polynomial `zero4_5275`:
`X^5275 + X^4508 + X^2751 + 1` has the least degree of any nonzero multiple of
`G` with fewer than six terms (hence CRC32C achieves Hamming distance 6 up to
codeword degree 5274, i.e., 5,243 payload bits + 32 CRC bits), and it is unique
at degree 5275.

Multiples with `< 4` terms already have degree `≥ 2^31 - 1 > 5275` (`zero2_minimal`),
and odd weights are impossible (`even_card_support_of_dvd_G`), leaving only exact
4-term multiples (`k = 3` positive shifts in `1..5274`). Splitting `1..5274` into
`1..2637` and `2638..5274` reduces the 2-term probes against the 5,275-entry
singleton table to `2 × C(2637, 2) = 6,951,132`, checked in parallel across
`Deg5275S0..S3`.
-/
import MemcpyCrc32c.ZeroMin.Deg5275S0
import MemcpyCrc32c.ZeroMin.Deg5275S1
import MemcpyCrc32c.ZeroMin.Deg5275S2
import MemcpyCrc32c.ZeroMin.Deg5275S3
import MemcpyCrc32c.ZeroMin.XorLemmas

set_option maxRecDepth 2000000

namespace Crc32c
open Polynomial
open scoped List

namespace ZeroMin.Deg5275
open ZeroMin

set_option maxRecDepth 2000000

private theorem chunk_step (l : List Nat) (j n : Nat)
    (h1 : loop2n inTable 2147483648 n (l.drop j) = true)
    (h2 : loop2 inTable 2147483648 (l.drop (j + n)) = true) :
    loop2 inTable 2147483648 (l.drop j) = true :=
  loop2n_drop h1 (by rwa [List.drop_drop])

theorem loop2_resLo : loop2 inTable 2147483648 resLo = true :=
  chunk_step resLo 0 112 lo_c0 (chunk_step resLo 112 118 lo_c1
  (chunk_step resLo 230 123 lo_c2 (chunk_step resLo 353 131 lo_c3
  (chunk_step resLo 484 139 lo_c4 (chunk_step resLo 623 149 lo_c5
  (chunk_step resLo 772 163 lo_c6 (chunk_step resLo 935 180 lo_c7
  (chunk_step resLo 1115 204 lo_c8 (chunk_step resLo 1319 242 lo_c9
  (chunk_step resLo 1561 315 lo_c10 (chunk_step resLo 1876 761 lo_c11 (by rfl))))))))))))

theorem loop2_resHi : loop2 inTable 2147483648 resHi = true :=
  chunk_step resHi 0 112 hi_c0 (chunk_step resHi 112 118 hi_c1
  (chunk_step resHi 230 123 hi_c2 (chunk_step resHi 353 131 hi_c3
  (chunk_step resHi 484 139 hi_c4 (chunk_step resHi 623 149 hi_c5
  (chunk_step resHi 772 163 hi_c6 (chunk_step resHi 935 180 hi_c7
  (chunk_step resHi 1115 204 hi_c8 (chunk_step resHi 1319 242 hi_c9
  (chunk_step resHi 1561 315 hi_c10 (chunk_step resHi 1876 761 hi_c11 (by rfl))))))))))))

theorem ρ_toNat_inj_of_lt {i j : Nat} (hi : i < 2 ^ 31 - 1) (hj : j < 2 ^ 31 - 1)
    (heq : (ρ i).toNat = (ρ j).toNat) : i = j := by
  have hρ : ρ i = ρ j := UInt32.toNat_inj.mp heq
  have hπ : π X ^ i = π X ^ j := by rw [← π_P_ρ, ← π_P_ρ, hρ]
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi heq.symm hρ.symm hπ.symm (by omega)).symm
  have hdvdG : G ∣ X ^ j + X ^ i := by
    rw [← AdjoinRoot.mk_eq_zero, ← π, map_add, map_pow, map_pow, ← hπ, Q_add_self]
  have hdvd := (dvd_X_pow_add_X_pow_iff hij).mp hdvdG
  have hsub0 : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

end ZeroMin.Deg5275

open ZeroMin ZeroMin.Deg5275 in
/-- **Minimality of `zero4_5275`.** Every nonzero multiple of `G` with fewer than
six terms has degree at least 5275. -/
theorem zero4_5275_minimal {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 6) : 5275 ≤ p.natDegree := by
  by_contra hd
  by_cases hw4 : p.support.card < 4
  · have := zero2_minimal hp hG hw4; omega
  · obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
    have hcard4 : p.support.card = 4 := by omega
    obtain ⟨m, ts, _, hpw, hlen, hmem, hxor⟩ := exists_shifted_relation hp hG
    have hts3 : ts.length = 3 := by omega
    have hsub : ts <+ List.range' 1 5274 :=
      sublist_range_of_pairwise_lt hpw fun t ht => by
        obtain ⟨h1, _, hle⟩ := hmem t ht
        exact ⟨h1, by omega⟩
    match ts, hts3 with
    | [t1, t2, t3], _ =>
      have hus : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat] <+ resL := by
        rw [resL_eq_map]; simpa using hsub.map (fun i => (ρ i).toNat)
      have hs_split : [(ρ t1).toNat, (ρ t2).toNat, (ρ t3).toNat] <+ resLo ++ resHi := by
        simpa [resLo, resHi, List.take_append_drop] using hus
      have HL := listIn_spec listIn_resL
      rcases sublist3_split hs_split with ⟨h12, h3⟩ | ⟨h1, h23⟩
      · simp only [resLo, resHi, List.take_append_drop] at h3
        have hf := loop2_spec loop2_resLo _ _ h12
        have ht := HL _ h3
        have eq := foldr_map_xor3_left (fun i => (ρ i).toNat) 2147483648 hxor
        rw [eq, ht] at hf; cases hf
      · simp only [resLo, resHi, List.take_append_drop] at h1
        have hf := loop2_spec loop2_resHi _ _ h23
        have ht := HL _ h1
        have eq := foldr_map_xor3_right (fun i => (ρ i).toNat) 2147483648 hxor
        rw [eq, ht] at hf; cases hf

open ZeroMin ZeroMin.Deg5275 in
/-- **Uniqueness of `zero4_5275`.** `X^5275 + X^4508 + X^2751 + 1` is the unique
nonzero multiple of `G` of degree at most 5275 with fewer than six terms. -/
theorem zero4_5275_unique {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card < 6) (hd : p.natDegree ≤ 5275) :
    p = X ^ 5275 + X ^ 4508 + X ^ 2751 + 1 := by
  obtain ⟨h0_mem, hdeg⟩ := zero_mem_and_natDegree_eq_of_minimal hp hd fun m _ hm =>
    zero4_5275_minimal (shiftDown_ne_zero hp hm) (dvd_shiftDown_of_dvd hG hm)
      (by rwa [card_support_shiftDown hm])
  have hw4 : ¬ p.support.card < 4 := fun h => by
    have := zero2_minimal hp hG h; omega
  obtain ⟨k, hk⟩ := even_card_support_of_dvd_G hG
  have hcard4 : p.support.card = 4 := by omega
  obtain ⟨ts, hsub, hcard, _, hp_eq, hxor⟩ :=
    exists_interior_relation (by omega) hp hG h0_mem hdeg
  have hts2 : ts.length = 2 := by omega
  change target5275 ^^^ (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0 at hxor
  have HL := listIn_spec listIn_resL
  have HU := loop1_uniq_spec uniq5275_loop
  match ts, hts2 with
  | [t1, t2], _ =>
    have hus : [(ρ t1).toNat, (ρ t2).toNat] <+ resL := by
      rw [resL_eq_map]; simpa using hsub.map (fun i => (ρ i).toNat)
    have h1_mem : (ρ t1).toNat ∈ resL := hus.subset (by simp)
    have h2_mem : (ρ t2).toNat ∈ resL := hus.subset (by simp)
    have eq1 := foldr_map_xor2_left (fun i => (ρ i).toNat) target5275 hxor
    have eq2 := foldr_map_xor2_right (fun i => (ρ i).toNat) target5275 hxor
    have hw1 : inW5275 (ρ t1).toNat = true := HU _ h1_mem (eq1 ▸ HL _ h2_mem)
    have hw2 : inW5275 (ρ t2).toNat = true := HU _ h2_mem (eq2 ▸ HL _ h1_mem)
    have hus_filt : [(ρ t1).toNat, (ρ t2).toNat] <+ resL.filter inW5275 := by
      have hall : ∀ u ∈ [(ρ t1).toNat, (ρ t2).toNat], inW5275 u = true := by
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> assumption
      rw [← List.filter_eq_self.mpr hall]
      exact hus.filter _
    rw [filter_resL_w5275] at hus_filt
    obtain ⟨heq1, heq2'⟩ := sublist_pair_eq hus_filt
    have hr1 := List.mem_range'_1.mp (hsub.subset (show t1 ∈ [t1, t2] by simp))
    have hr2 := List.mem_range'_1.mp (hsub.subset (show t2 ∈ [t1, t2] by simp))
    have ht1 : t1 = 2751 := ρ_toNat_inj_of_lt (by omega) (by norm_num) heq1
    have ht2 : t2 = 4508 := ρ_toNat_inj_of_lt (by omega) (by norm_num) heq2'
    subst ht1 ht2
    simp only [List.map, List.sum_cons, List.sum_nil, add_zero] at hp_eq
    rw [hp_eq]; ring

end Crc32c
