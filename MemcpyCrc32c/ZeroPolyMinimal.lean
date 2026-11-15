/-
Minimality of the 6-term zero polynomial `zero6_209`: every nonzero multiple of
`G` with at most six terms has degree at least 209.

The proof is an exhaustive meet-in-the-middle search run inside the kernel
(`decide +kernel`, no `native_decide`). After dividing out a power of `X`, a
counterexample is a relation `1 + X^t₁ + ⋯ + X^tₖ ≡ 0 (mod G)` with
`1 ≤ t₁ < ⋯ < tₖ ≤ 208` and `k ≤ 5`. Splitting the exponents three-and-two, it
is enough that no `1 + X^a + X^b + X^c` (and no `1 + X^a + X^b`, `1 + X^a`)
lands in the set of sums of at most two residues `X^i mod G`.

The membership test `inTable` is a lookup table built by untrusted
elaboration-time code and spliced in as literals. Nothing about how it was
built is assumed: the kernel checks that it accepts every two-term sum and
rejects every probe, and the proof uses only those two facts.
-/
import MemcpyCrc32c.ZeroPoly
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

namespace Crc32c
open Polynomial

namespace ZeroMin
open scoped List

/-! ### Residues `X^i mod G` as reflected words -/

/-- `n` successive residues `s, s·X, s·X², …` as natural numbers. -/
def resNat : Nat → UInt32 → List Nat
  | 0, _ => []
  | n + 1, s => s.toNat :: resNat n (stepBit s)

/-- `X^i mod G`, reflected. -/
def ρ (i : Nat) : UInt32 := stepBit^[i] 0x80000000

theorem π_P_ρ (i : Nat) : π (P (ρ i)) = π X ^ i := by
  induction i with
  | zero => simp [ρ, P_one]
  | succ i ih => rw [ρ, Function.iterate_succ_apply', π_P_stepBit, ← ρ, ih, pow_succ]

theorem resNat_ρ (n k : Nat) :
    resNat n (ρ k) = (List.range' k n).map fun i => (ρ i).toNat := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h : stepBit (ρ k) = ρ (k + 1) := by rw [ρ, ρ, Function.iterate_succ_apply']
    rw [resNat, h, ih, List.range'_succ, List.map_cons]

/-! ### The lookup table (untrusted construction, kernel-checked use) -/

/-- Binary trie on the bits of a key, least significant first, with path
compression at the leaves. -/
inductive Trie where
  | nil
  | tip (k : Nat)
  | node (l r : Trie)

/-- Trie membership, written with the raw recursor and `Nat` primitives so that
kernel evaluation is cheap. -/
noncomputable def Trie.mem (t : Trie) : Nat → Bool :=
  Trie.rec (fun _ => false) (fun k' k => Nat.beq k k')
    (fun _ _ ihl ihr k =>
      cond (Nat.beq (Nat.land k 1) 0) (ihl (Nat.shiftRight k 1)) (ihr (Nat.shiftRight k 1))) t

/-- Elaboration-time trie construction. Untrusted. -/
def Trie.build : Nat → List Nat → Trie
  | _, [] => .nil
  | _, [k] => .tip k
  | 0, k :: _ => .tip k
  | n + 1, ks =>
    .node (Trie.build n ((ks.filter (· % 2 = 0)).map (· / 2)))
      (Trie.build n ((ks.filter (· % 2 = 1)).map (· / 2)))

def Trie.toExpr : Trie → Lean.Expr
  | .nil => .const ``Trie.nil []
  | .tip k => .app (.const ``Trie.tip []) (Lean.mkRawNatLit k)
  | .node l r => Lean.mkApp2 (.const ``Trie.node []) l.toExpr r.toExpr

/-- Sums of two distinct entries. Elaboration-time only. -/
def pairSums : List Nat → List Nat
  | [] => []
  | a :: rest => rest.map (a ^^^ ·) ++ pairSums rest

/-- The table keys: `0` and all `X^a + X^b` with `1 ≤ a < b ≤ 208`. -/
def tableKeys : List Nat := 0 :: pairSums (resNat 208 (stepBit 0x80000000))

def bitset (h : Nat → Nat) (ks : List Nat) : Nat :=
  ks.foldl (fun b k => b ||| (1 <<< h k)) 0

open Lean Elab Term in
elab "zero_min_residues%" : term =>
  return toExpr (resNat 208 (stepBit 0x80000000))

open Lean Elab Term in
elab "zero_min_trie%" : term =>
  return (Trie.build 32 tableKeys).toExpr

open Lean Elab Term in
elab "zero_min_bits_lo%" : term =>
  return mkRawNatLit (bitset (· % 131072) tableKeys)

open Lean Elab Term in
elab "zero_min_bits_hi%" : term =>
  return mkRawNatLit (bitset (· / 32768) tableKeys)

set_option maxRecDepth 1000000

/-- `X^1, …, X^208 mod G`, reflected, as literals. -/
def resL : List Nat := zero_min_residues%

def table : Trie := zero_min_trie%

/-- Bitset of the low 17 bits of every table key. -/
def bitsLo : Nat := zero_min_bits_lo%

/-- Bitset of the high 17 bits of every table key. -/
def bitsHi : Nat := zero_min_bits_hi%

noncomputable def bitAt (b h : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight b h) 1) 1

/-- The membership test: two bitset prefilters, then the exact trie. -/
noncomputable def inTable (v : Nat) : Bool :=
  cond (bitAt bitsLo (Nat.land v 131071))
    (cond (bitAt bitsHi (Nat.shiftRight v 15)) (table.mem v) false) false

/-! ### Kernel-evaluated loops -/

/-- `inTable (acc + e)` fails for every `e` in the list. -/
noncomputable def loop1 (l : List Nat) : Nat → Bool :=
  List.rec (fun _ => true) (fun e _ ih acc => cond (inTable (Nat.xor acc e)) false (ih acc)) l

noncomputable def loop2 (l : List Nat) : Nat → Bool :=
  List.rec (fun _ => true)
    (fun d rest ih acc => cond (loop1 rest (Nat.xor acc d)) (ih acc) false) l

/-- The first `n` outer iterations of the three-term loop. -/
noncomputable def loop3n (n : Nat) : List Nat → Bool :=
  Nat.rec (fun _ => true)
    (fun _ ih l => List.casesOn l true
      (fun c rest => cond (loop2 rest (Nat.xor 2147483648 c)) (ih rest) false)) n

noncomputable def loop3 (l : List Nat) : Bool :=
  List.rec true (fun c rest ih => cond (loop2 rest (Nat.xor 2147483648 c)) ih false) l

/-- `inTable (a + b)` holds for every `b` in the list. -/
noncomputable def allIn (l : List Nat) (a : Nat) : Bool :=
  List.rec true (fun b _ ih => cond (inTable (Nat.xor a b)) ih false) l

noncomputable def pairsIn (l : List Nat) : Bool :=
  List.rec true (fun a rest ih => cond (allIn rest a) ih false) l

theorem resL_eq : resL = resNat 208 (stepBit 0x80000000) := by decide +kernel

/-- The table accepts `0` … -/
theorem inTable_zero : inTable 0 = true := by decide +kernel

/-- … and every two-term sum. -/
theorem pairsIn_resL : pairsIn resL = true := by decide +kernel

/-- No `1 + X^a` is in the table. -/
theorem loop1_resL : loop1 resL 2147483648 = true := by decide +kernel

/-- No `1 + X^a + X^b` is in the table. -/
theorem loop2_resL : loop2 resL 2147483648 = true := by decide +kernel

/-! No `1 + X^a + X^b + X^c` is in the table: about 1.5 million probes, split by
the smallest exponent into chunks so that each kernel run stays small. -/

theorem chunk0 : loop3n 5 (resL.drop 0) = true := by decide +kernel
theorem chunk1 : loop3n 5 (resL.drop 5) = true := by decide +kernel
theorem chunk2 : loop3n 5 (resL.drop 10) = true := by decide +kernel
theorem chunk3 : loop3n 6 (resL.drop 15) = true := by decide +kernel
theorem chunk4 : loop3n 6 (resL.drop 21) = true := by decide +kernel
theorem chunk5 : loop3n 7 (resL.drop 27) = true := by decide +kernel
theorem chunk6 : loop3n 7 (resL.drop 34) = true := by decide +kernel
theorem chunk7 : loop3n 8 (resL.drop 41) = true := by decide +kernel
theorem chunk8 : loop3n 9 (resL.drop 49) = true := by decide +kernel
theorem chunk9 : loop3n 10 (resL.drop 58) = true := by decide +kernel
theorem chunk10 : loop3n 12 (resL.drop 68) = true := by decide +kernel
theorem chunk11 : loop3n 15 (resL.drop 80) = true := by decide +kernel
theorem chunk12 : loop3n 21 (resL.drop 95) = true := by decide +kernel
theorem chunk13 : loop3n 45 (resL.drop 116) = true := by decide +kernel
theorem chunk14 : loop3n 47 (resL.drop 161) = true := by decide +kernel

theorem loop3n_drop {n : Nat} {l : List Nat} (h1 : loop3n n l = true)
    (h2 : loop3 (l.drop n) = true) : loop3 l = true := by
  induction n generalizing l with
  | zero => simpa using h2
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons c rest =>
      have e1 : loop3n (n + 1) (c :: rest) =
          cond (loop2 rest (Nat.xor 2147483648 c)) (loop3n n rest) false := rfl
      have e2 : loop3 (c :: rest) =
          cond (loop2 rest (Nat.xor 2147483648 c)) (loop3 rest) false := rfl
      rw [e1] at h1
      rw [e2]
      cases hc : loop2 rest (Nat.xor 2147483648 c) with
      | false => rw [hc] at h1; cases h1
      | true =>
        rw [hc] at h1
        exact ih h1 (by simpa using h2)

theorem chunk_step (j n : Nat) (h1 : loop3n n (resL.drop j) = true)
    (h2 : loop3 (resL.drop (j + n)) = true) : loop3 (resL.drop j) = true :=
  loop3n_drop h1 (by rwa [List.drop_drop])

theorem loop3_resL : loop3 resL = true :=
  chunk_step 0 5 chunk0 (chunk_step 5 5 chunk1 (chunk_step 10 5 chunk2 (chunk_step 15 6 chunk3 (chunk_step 21 6 chunk4 (chunk_step 27 7 chunk5 (chunk_step 34 7 chunk6 (chunk_step 41 8 chunk7 (chunk_step 49 9 chunk8 (chunk_step 58 10 chunk9 (chunk_step 68 12 chunk10 (chunk_step 80 15 chunk11 (chunk_step 95 21 chunk12 (chunk_step 116 45 chunk13 (chunk_step 161 47 chunk14 (by rfl)))))))))))))))

/-! ### What the loops establish -/

theorem loop1_spec {l : List Nat} {acc : Nat} (h : loop1 l acc = true) :
    ∀ e ∈ l, inTable (acc ^^^ e) = false := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e1 : loop1 (x :: l) acc = cond (inTable (acc ^^^ x)) false (loop1 l acc) := rfl
    rw [e1] at h
    cases hx : inTable (acc ^^^ x) with
    | true => simp [hx] at h
    | false =>
      simp only [hx, Bool.cond_false] at h
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hx
      · exact ih h e he

theorem loop2_spec {l : List Nat} {acc : Nat} (h : loop2 l acc = true) :
    ∀ d e, [d, e] <+ l → inTable (acc ^^^ d ^^^ e) = false := by
  induction l with
  | nil => intro d e hs; simp at hs
  | cons x l ih =>
    have e1 : loop2 (x :: l) acc = cond (loop1 l (acc ^^^ x)) (loop2 l acc) false := rfl
    rw [e1] at h
    cases hx : loop1 l (acc ^^^ x) with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro d e hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h d e hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact loop1_spec hx e (List.singleton_sublist.mp hs)

theorem loop3_spec {l : List Nat} (h : loop3 l = true) :
    ∀ c d e, [c, d, e] <+ l → inTable (2147483648 ^^^ c ^^^ d ^^^ e) = false := by
  induction l with
  | nil => intro c d e hs; simp at hs
  | cons x l ih =>
    have e1 : loop3 (x :: l) = cond (loop2 l (2147483648 ^^^ x)) (loop3 l) false := rfl
    rw [e1] at h
    cases hx : loop2 l (2147483648 ^^^ x) with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro c d e hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h c d e hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact loop2_spec hx d e hs

theorem allIn_spec {l : List Nat} {a : Nat} (h : allIn l a = true) :
    ∀ b ∈ l, inTable (a ^^^ b) = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e1 : allIn (x :: l) a = cond (inTable (a ^^^ x)) (allIn l a) false := rfl
    rw [e1] at h
    cases hx : inTable (a ^^^ x) with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hx
      · exact ih h b hb

theorem pairsIn_spec {l : List Nat} (h : pairsIn l = true) :
    ∀ a b, [a, b] <+ l → inTable (a ^^^ b) = true := by
  induction l with
  | nil => intro a b hs; simp at hs
  | cons x l ih =>
    have e1 : pairsIn (x :: l) = cond (allIn l x) (pairsIn l) false := rfl
    rw [e1] at h
    cases hx : allIn l x with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro a b hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h a b hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact allIn_spec hx b (List.singleton_sublist.mp hs)

/-! ### No short relation among the residues -/

theorem eq_of_xor_eq_zero {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  have := congrArg (· ^^^ y) h
  simpa [Nat.xor_assoc] using this

/-- `1` plus at most five of the residues `X^1, …, X^208` is never zero. -/
theorem no_relation (us : List Nat) (hs : us <+ resL) (hl : us.length ≤ 5) :
    2147483648 ^^^ us.foldr (· ^^^ ·) 0 ≠ 0 := by
  have H1 := loop1_spec loop1_resL
  have H2 := loop2_spec loop2_resL
  have H3 := loop3_spec loop3_resL
  have HP := pairsIn_spec pairsIn_resL
  have H0 := inTable_zero
  intro h
  match us, hs, hl, h with
  | [], _, _, h => simp at h
  | [a], hs, _, h =>
    have := H1 a (List.singleton_sublist.mp hs)
    simp only [List.foldr, Nat.xor_zero] at h
    rw [h, H0] at this
    cases this
  | [a, b], hs, _, h =>
    have := H2 a b hs
    simp only [List.foldr, Nat.xor_zero, ← Nat.xor_assoc] at h
    rw [h, H0] at this
    cases this
  | [a, b, c], hs, _, h =>
    have := H3 a b c hs
    simp only [List.foldr, Nat.xor_zero, ← Nat.xor_assoc] at h
    rw [h, H0] at this
    cases this
  | [a, b, c, d], hs, _, h =>
    have h1 := H2 a b ((List.sublist_append_left [a, b] [c, d]).trans hs)
    have h2 := HP c d ((List.sublist_append_right [a, b] [c, d]).trans hs)
    simp only [List.foldr, Nat.xor_zero] at h
    have e : 2147483648 ^^^ a ^^^ b = c ^^^ d :=
      eq_of_xor_eq_zero (by simpa only [Nat.xor_assoc] using h)
    rw [e, h2] at h1
    cases h1
  | [a, b, c, d, e], hs, _, h =>
    have h1 := H3 a b c ((List.sublist_append_left [a, b, c] [d, e]).trans hs)
    have h2 := HP d e ((List.sublist_append_right [a, b, c] [d, e]).trans hs)
    simp only [List.foldr, Nat.xor_zero] at h
    have e' : 2147483648 ^^^ a ^^^ b ^^^ c = d ^^^ e :=
      eq_of_xor_eq_zero (by simpa only [Nat.xor_assoc] using h)
    rw [e', h2] at h1
    cases h1
  | _ :: _ :: _ :: _ :: _ :: _ :: _, _, hl, _ => simp at hl; omega

/-! ### From polynomials to the search -/

theorem resL_eq_map : resL = (List.range' 1 208).map fun i => (ρ i).toNat := by
  rw [resL_eq, ← resNat_ρ]; rfl

theorem π_P_foldr (ts : List Nat) :
    π (P ((ts.map ρ).foldr (· ^^^ ·) 0)) = (ts.map fun t => π X ^ t).sum := by
  induction ts with
  | nil => simp [P_zero]
  | cons t ts ih => simp [P_xor, π_P_ρ, ih]

theorem toNat_foldr (ts : List Nat) :
    ((ts.map ρ).foldr (· ^^^ ·) 0).toNat =
      (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [UInt32.toNat_xor, ih]

/-- No relation `1 + X^t₁ + ⋯ + X^tₖ ≡ 0 (mod G)` with `1 ≤ t₁ < ⋯ < tₖ ≤ 208`, `k ≤ 5`. -/
theorem no_relation_π (ts : List Nat) (hs : ts <+ List.range' 1 208) (hl : ts.length ≤ 5) :
    1 + (ts.map fun t => π X ^ t).sum ≠ 0 := by
  intro h
  have h1 : (0x80000000 : UInt32) ^^^ (ts.map ρ).foldr (· ^^^ ·) 0 = 0 := by
    apply eq_of_π_P
    rw [P_xor, map_add, P_one, map_one, π_P_foldr, P_zero, map_zero]
    exact h
  have h2 := congrArg UInt32.toNat h1
  rw [UInt32.toNat_xor, toNat_foldr] at h2
  refine no_relation (ts.map fun i => (ρ i).toNat) ?_ (by simpa using hl) h2
  rw [resL_eq_map]
  exact hs.map _

theorem isUnit_π_X : IsUnit (π X) := by
  have h : IsUnit (π X ^ 8) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact π_P_xInv8)
  exact (isUnit_pow_iff (by norm_num)).mp h

end ZeroMin

open ZeroMin in
/-- **Minimality of `zero6_209`.** Every nonzero multiple of `G` with at most six
terms has degree at least 209. Together with `zero6_209` (a six-term multiple
of degree exactly 209) and `eval_one_G` (multiples of `G` have an even number of
terms), `X^209 + X^144 + X^54 + X^39 + X^14 + 1` has the least degree of any
nonzero multiple of `G` with fewer than eight terms. -/
theorem zero6_209_minimal {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p)
    (hw : p.support.card ≤ 6) : 209 ≤ p.natDegree := by
  by_contra hd
  have hd : p.natDegree < 209 := by omega
  have h0 : π p = 0 := by
    obtain ⟨q, rfl⟩ := hG
    simp [π_G]
  -- over `ZMod 2`, `p` is the sum of the monomials in its support
  have hsum : p = ∑ s ∈ p.support, (X : (ZMod 2)[X]) ^ s := by
    conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hc : p.coeff s = 1 := by
      have hne := mem_support_iff.mp hs
      generalize p.coeff s = c at hne
      revert c; decide
    rw [hc]; simp
  have hnd : (p.support.sort).Nodup := Finset.sort_nodup ..
  have hle : (p.support.sort).Pairwise (· ≤ ·) := Finset.pairwise_sort ..
  have hlen : (p.support.sort).length ≤ 6 := by rwa [Finset.length_sort]
  have hmem : ∀ s ∈ p.support.sort, s < 209 := fun s hs =>
    lt_of_le_of_lt (le_natDegree_of_mem_supp s ((Finset.mem_sort _).mp hs)) hd
  have hπ : ((p.support.sort).map fun s => π X ^ s).sum = 0 := by
    rw [← List.sum_toFinset _ hnd, Finset.sort_toFinset, ← h0]
    conv_rhs => rw [hsum]
    simp [map_sum]
  have hne : p.support.sort ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [Finset.length_sort] at this
    simp [hp] at this
  obtain ⟨m, rest, hl⟩ := List.exists_cons_of_ne_nil hne
  rw [hl] at hnd hle hlen hmem hπ
  have hlt : ∀ e ∈ rest, m < e := fun e he =>
    lt_of_le_of_ne ((List.pairwise_cons.mp hle).1 e he)
      (fun h => (List.nodup_cons.mp hnd).1 (h ▸ he))
  -- divide out `X^m`
  have hfac : ((m :: rest).map fun s => π X ^ s).sum =
      π X ^ m * (1 + ((rest.map (· - m)).map fun t => π X ^ t).sum) := by
    rw [List.map_cons, List.sum_cons, mul_add, mul_one, List.map_map, ← List.sum_map_mul_left]
    congr 2
    apply List.map_congr_left
    intro e he
    have := hlt e he
    simp only [Function.comp_apply, ← pow_add]
    congr 1; omega
  rw [hfac, (isUnit_π_X.pow m).mul_right_eq_zero] at hπ
  refine no_relation_π (rest.map (· - m)) ?_ (by simp at hlen ⊢; omega) hπ
  -- the shifted exponents are strictly increasing and lie in `1..208`
  have hpw : (rest.map (· - m)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    have h1 : rest.Pairwise (· < ·) :=
      ((List.pairwise_cons.mp hle).2.and (List.nodup_cons.mp hnd).2).imp
        fun h => lt_of_le_of_ne h.1 h.2
    refine h1.imp_of_mem fun {a b} ha hb hab => ?_
    have := hlt a ha
    omega
  refine List.sublist_of_subperm_of_pairwise
    (List.subperm_of_subset (hpw.imp ne_of_lt) ?_) hpw List.pairwise_lt_range'
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  have := hlt e he
  have := hmem e (List.mem_cons_of_mem _ he)
  rw [List.mem_range'_1]
  omega

end Crc32c
