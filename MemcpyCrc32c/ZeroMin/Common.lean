/-
Shared infrastructure for kernel-checked zero-polynomial minimality and
uniqueness proofs (`MemcpyCrc32c.ZeroMin.*`):
- Reflected residues `ρ i = X^i mod G` and their correspondence with `Q`.
- Untrusted elaboration-time binary trie and bitset builders paired with
  kernel-reduced membership tests (`Trie.mem`, `inTable16`, `inTable18`).
- Generic kernel-evaluated search loops (`loop1..loop4`, `pairsIn`, `triplesIn`,
  `loop1_uniq..loop3_uniq`) and their soundness theorems.
- Shared polynomial-support normalization (`shiftDown`, `extractInterior`,
  middle-split sublist pigeonhole lemmas).
-/
import MemcpyCrc32c.PolyAlgebra
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

theorem eq_of_xor_eq_zero {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  have := congrArg (· ^^^ y) h
  simpa [Nat.xor_assoc] using this

theorem xor_eq_of_eq_zero {lhs rhs expr : Nat} (heq : lhs ^^^ rhs = expr) (h : expr = 0) :
    lhs = rhs :=
  eq_of_xor_eq_zero (heq.trans h)

/-! ### Lookup table (untrusted construction, kernel-checked use) -/

/-- Binary trie on the bits of a key, least significant first, with path
compression at the leaves. -/
inductive Trie where
  | nil
  | tip (k : Nat)
  | node (l r : Trie)

/-- Trie membership, written with the raw recursor and `Nat` primitives so that
kernel evaluation stays fast. -/
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

/-- Sums of three distinct entries. Elaboration-time only. -/
def tripleSums : List Nat → List Nat
  | [] => []
  | a :: rest => (pairSums rest).map (a ^^^ ·) ++ tripleSums rest

def bitset (h : Nat → Nat) (ks : List Nat) : Nat :=
  ks.foldl (fun b k => b ||| (1 <<< h k)) 0

noncomputable def bitAt (b h : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight b h) 1) 1

/-- Membership test with two disjoint 16-bit (`65536`-bit) bitset prefilters. -/
noncomputable def inTable16 (bitsLo bitsHi : Nat) (t : Trie) (v : Nat) : Bool :=
  cond (bitAt bitsLo (Nat.land v 65535))
    (cond (bitAt bitsHi (Nat.shiftRight v 16)) (t.mem v) false) false

/-- Membership test with two 17-bit (`131072`-bit) bitset prefilters. -/
noncomputable def inTable17 (bitsLo bitsHi : Nat) (t : Trie) (v : Nat) : Bool :=
  cond (bitAt bitsLo (Nat.land v 131071))
    (cond (bitAt bitsHi (Nat.shiftRight v 15)) (t.mem v) false) false

/-- Membership test with two 18-bit (`262144`-bit) bitset prefilters. -/
noncomputable def inTable18 (bitsLo bitsHi : Nat) (t : Trie) (v : Nat) : Bool :=
  cond (bitAt bitsLo (Nat.land v 262143))
    (cond (bitAt bitsHi (Nat.shiftRight v 14)) (t.mem v) false) false

/-! ### Generic kernel-evaluated search loops -/

/-- `inT (acc ^^^ e)` is `false` for every `e ∈ l`. Note `acc` precedes `l` so
`List.rec` uses motive `Bool` rather than `Nat → Bool`. -/
noncomputable def loop1 (inT : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true (fun e _ ih => cond (inT (Nat.xor acc e)) false ih) l

noncomputable def loop2 (inT : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true (fun d rest ih => cond (loop1 inT (Nat.xor acc d) rest) ih false) l

noncomputable def loop2n (inT : Nat → Bool) (acc : Nat) (n : Nat) : List Nat → Bool :=
  Nat.rec (fun _ => true)
    (fun _ ih l => List.casesOn l true
      (fun d rest => cond (loop1 inT (Nat.xor acc d) rest) (ih rest) false)) n

noncomputable def loop3 (inT : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true (fun c rest ih => cond (loop2 inT (Nat.xor acc c) rest) ih false) l

noncomputable def loop3n (inT : Nat → Bool) (acc : Nat) (n : Nat) : List Nat → Bool :=
  Nat.rec (fun _ => true)
    (fun _ ih l => List.casesOn l true
      (fun c rest => cond (loop2 inT (Nat.xor acc c) rest) (ih rest) false)) n

noncomputable def loop4 (inT : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true (fun b rest ih => cond (loop3 inT (Nat.xor acc b) rest) ih false) l

noncomputable def loop4n (inT : Nat → Bool) (acc : Nat) (n : Nat) : List Nat → Bool :=
  Nat.rec (fun _ => true)
    (fun _ ih l => List.casesOn l true
      (fun b rest => cond (loop3 inT (Nat.xor acc b) rest) (ih rest) false)) n

/-- Every `a ∈ l` satisfies `inT a = true`. -/
noncomputable def listIn (inT : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun a _ ih => cond (inT a) ih false) l

/-- Every `b ∈ l` satisfies `inT (a ^^^ b) = true`. -/
noncomputable def allIn (inT : Nat → Bool) (a : Nat) (l : List Nat) : Bool :=
  List.rec true (fun b _ ih => cond (inT (Nat.xor a b)) ih false) l

/-- Every 2-element sublist `[a, b] <+ l` satisfies `inT (a ^^^ b) = true`. -/
noncomputable def pairsIn (inT : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun a rest ih => cond (allIn inT a rest) ih false) l

noncomputable def pairsInAcc (inT : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true (fun b rest ih => cond (allIn inT (Nat.xor acc b) rest) ih false) l

/-- Every 3-element sublist `[a, b, c] <+ l` satisfies `inT (a ^^^ b ^^^ c) = true`. -/
noncomputable def triplesIn (inT : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun a rest ih => cond (pairsInAcc inT a rest) ih false) l

/-- Uniqueness loop (1-term): rejects `acc ^^^ e` for every `e ∈ l` with `inW e = false`. -/
noncomputable def loop1_uniq (inT inW : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true (fun e _ ih => cond (inW e) ih (cond (inT (Nat.xor acc e)) false ih)) l

/-- Uniqueness loop (2-term): rejects `acc ^^^ d ^^^ e` unless both `inW d` and `inW e`. -/
noncomputable def loop2_uniq (inT inW : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true
    (fun d rest ih =>
      cond (cond (inW d) (loop1_uniq inT inW (Nat.xor acc d) rest)
        (loop1 inT (Nat.xor acc d) rest)) ih false) l

/-- Uniqueness loop (3-term): rejects `acc ^^^ c ^^^ d ^^^ e` unless `inW` holds on all three. -/
noncomputable def loop3_uniq (inT inW : Nat → Bool) (acc : Nat) (l : List Nat) : Bool :=
  List.rec true
    (fun c rest ih =>
      cond (cond (inW c) (loop2_uniq inT inW (Nat.xor acc c) rest)
        (loop2 inT (Nat.xor acc c) rest)) ih false) l

/-! ### Soundness of the kernel loops -/

theorem loop2n_drop {inT : Nat → Bool} {acc n : Nat} {l : List Nat}
    (h1 : loop2n inT acc n l = true) (h2 : loop2 inT acc (l.drop n) = true) :
    loop2 inT acc l = true := by
  induction n generalizing l with
  | zero => simpa using h2
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons d rest =>
      have e1 : loop2n inT acc (n + 1) (d :: rest) =
          cond (loop1 inT (acc ^^^ d) rest) (loop2n inT acc n rest) false := rfl
      have e2 : loop2 inT acc (d :: rest) =
          cond (loop1 inT (acc ^^^ d) rest) (loop2 inT acc rest) false := rfl
      rw [e1] at h1; rw [e2]
      cases hc : loop1 inT (acc ^^^ d) rest with
      | false => rw [hc] at h1; cases h1
      | true => rw [hc] at h1; exact ih h1 (by simpa using h2)

theorem loop3n_drop {inT : Nat → Bool} {acc n : Nat} {l : List Nat}
    (h1 : loop3n inT acc n l = true) (h2 : loop3 inT acc (l.drop n) = true) :
    loop3 inT acc l = true := by
  induction n generalizing l with
  | zero => simpa using h2
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons c rest =>
      have e1 : loop3n inT acc (n + 1) (c :: rest) =
          cond (loop2 inT (acc ^^^ c) rest) (loop3n inT acc n rest) false := rfl
      have e2 : loop3 inT acc (c :: rest) =
          cond (loop2 inT (acc ^^^ c) rest) (loop3 inT acc rest) false := rfl
      rw [e1] at h1; rw [e2]
      cases hc : loop2 inT (acc ^^^ c) rest with
      | false => rw [hc] at h1; cases h1
      | true => rw [hc] at h1; exact ih h1 (by simpa using h2)

theorem loop4n_drop {inT : Nat → Bool} {acc n : Nat} {l : List Nat}
    (h1 : loop4n inT acc n l = true) (h2 : loop4 inT acc (l.drop n) = true) :
    loop4 inT acc l = true := by
  induction n generalizing l with
  | zero => simpa using h2
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons b rest =>
      have e1 : loop4n inT acc (n + 1) (b :: rest) =
          cond (loop3 inT (acc ^^^ b) rest) (loop4n inT acc n rest) false := rfl
      have e2 : loop4 inT acc (b :: rest) =
          cond (loop3 inT (acc ^^^ b) rest) (loop4 inT acc rest) false := rfl
      rw [e1] at h1; rw [e2]
      cases hc : loop3 inT (acc ^^^ b) rest with
      | false => rw [hc] at h1; cases h1
      | true => rw [hc] at h1; exact ih h1 (by simpa using h2)

theorem loop1_spec {inT : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : loop1 inT acc l = true) : ∀ e ∈ l, inT (acc ^^^ e) = false := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e1 : loop1 inT acc (x :: l) = cond (inT (acc ^^^ x)) false (loop1 inT acc l) := rfl
    rw [e1] at h
    cases hx : inT (acc ^^^ x) with
    | true => simp [hx] at h
    | false =>
      simp only [hx, Bool.cond_false] at h
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hx
      · exact ih h e he

theorem loop2_spec {inT : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : loop2 inT acc l = true) : ∀ d e, [d, e] <+ l → inT (acc ^^^ d ^^^ e) = false := by
  induction l with
  | nil => intro d e hs; simp at hs
  | cons x l ih =>
    have e1 : loop2 inT acc (x :: l) =
        cond (loop1 inT (acc ^^^ x) l) (loop2 inT acc l) false := rfl
    rw [e1] at h
    cases hx : loop1 inT (acc ^^^ x) l with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro d e hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h d e hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact loop1_spec hx e (List.singleton_sublist.mp hs)

theorem loop3_spec {inT : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : loop3 inT acc l = true) :
    ∀ c d e, [c, d, e] <+ l → inT (acc ^^^ c ^^^ d ^^^ e) = false := by
  induction l with
  | nil => intro c d e hs; simp at hs
  | cons x l ih =>
    have e1 : loop3 inT acc (x :: l) =
        cond (loop2 inT (acc ^^^ x) l) (loop3 inT acc l) false := rfl
    rw [e1] at h
    cases hx : loop2 inT (acc ^^^ x) l with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro c d e hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h c d e hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact loop2_spec hx d e hs

theorem loop4_spec {inT : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : loop4 inT acc l = true) :
    ∀ b c d e, [b, c, d, e] <+ l → inT (acc ^^^ b ^^^ c ^^^ d ^^^ e) = false := by
  induction l with
  | nil => intro b c d e hs; simp at hs
  | cons x l ih =>
    have e1 : loop4 inT acc (x :: l) =
        cond (loop3 inT (acc ^^^ x) l) (loop4 inT acc l) false := rfl
    rw [e1] at h
    cases hx : loop3 inT (acc ^^^ x) l with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro b c d e hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h b c d e hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact loop3_spec hx c d e hs

theorem listIn_spec {inT : Nat → Bool} {l : List Nat} (h : listIn inT l = true) :
    ∀ a ∈ l, inT a = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e1 : listIn inT (x :: l) = cond (inT x) (listIn inT l) false := rfl
    rw [e1] at h
    cases hx : inT x with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact ih h a ha

theorem allIn_spec {inT : Nat → Bool} {a : Nat} {l : List Nat}
    (h : allIn inT a l = true) : ∀ b ∈ l, inT (a ^^^ b) = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e1 : allIn inT a (x :: l) = cond (inT (a ^^^ x)) (allIn inT a l) false := rfl
    rw [e1] at h
    cases hx : inT (a ^^^ x) with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hx
      · exact ih h b hb

theorem pairsIn_spec {inT : Nat → Bool} {l : List Nat} (h : pairsIn inT l = true) :
    ∀ a b, [a, b] <+ l → inT (a ^^^ b) = true := by
  induction l with
  | nil => intro a b hs; simp at hs
  | cons x l ih =>
    have e1 : pairsIn inT (x :: l) = cond (allIn inT x l) (pairsIn inT l) false := rfl
    rw [e1] at h
    cases hx : allIn inT x l with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro a b hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h a b hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact allIn_spec hx b (List.singleton_sublist.mp hs)

theorem pairsInAcc_spec {inT : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : pairsInAcc inT acc l = true) : ∀ b c, [b, c] <+ l → inT (acc ^^^ b ^^^ c) = true := by
  induction l with
  | nil => intro b c hs; simp at hs
  | cons x l ih =>
    have e1 : pairsInAcc inT acc (x :: l) =
        cond (allIn inT (acc ^^^ x) l) (pairsInAcc inT acc l) false := rfl
    rw [e1] at h
    cases hx : allIn inT (acc ^^^ x) l with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro b c hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h b c hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact allIn_spec hx c (List.singleton_sublist.mp hs)

theorem triplesIn_spec {inT : Nat → Bool} {l : List Nat} (h : triplesIn inT l = true) :
    ∀ a b c, [a, b, c] <+ l → inT (a ^^^ b ^^^ c) = true := by
  induction l with
  | nil => intro a b c hs; simp at hs
  | cons x l ih =>
    have e1 : triplesIn inT (x :: l) =
        cond (pairsInAcc inT x l) (triplesIn inT l) false := rfl
    rw [e1] at h
    cases hx : pairsInAcc inT x l with
    | false => simp [hx] at h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro a b c hs
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h a b c hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact pairsInAcc_spec hx b c hs

theorem loop1_uniq_spec {inT inW : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : loop1_uniq inT inW acc l = true) :
    ∀ e ∈ l, inT (acc ^^^ e) = true → inW e = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e1 : loop1_uniq inT inW acc (x :: l) =
        cond (inW x) (loop1_uniq inT inW acc l)
          (cond (inT (acc ^^^ x)) false (loop1_uniq inT inW acc l)) := rfl
    rw [e1] at h
    cases hwx : inW x with
    | true =>
      simp only [hwx, Bool.cond_true] at h
      intro e he ht
      rcases List.mem_cons.mp he with rfl | he
      · exact hwx
      · exact ih h e he ht
    | false =>
      simp only [hwx, Bool.cond_false] at h
      cases htx : inT (acc ^^^ x) with
      | true => simp [htx] at h
      | false =>
        simp only [htx, Bool.cond_false] at h
        intro e he ht
        rcases List.mem_cons.mp he with rfl | he
        · rw [htx] at ht; cases ht
        · exact ih h e he ht

theorem loop2_uniq_spec {inT inW : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : loop2_uniq inT inW acc l = true) :
    ∀ d e, [d, e] <+ l → inT (acc ^^^ d ^^^ e) = true → inW d = true ∧ inW e = true := by
  induction l with
  | nil => intro d e hs; simp at hs
  | cons x l ih =>
    have e1 : loop2_uniq inT inW acc (x :: l) =
        cond (cond (inW x) (loop1_uniq inT inW (acc ^^^ x) l) (loop1 inT (acc ^^^ x) l))
          (loop2_uniq inT inW acc l) false := rfl
    rw [e1] at h
    cases hstep : cond (inW x) (loop1_uniq inT inW (acc ^^^ x) l) (loop1 inT (acc ^^^ x) l) with
    | false => rw [hstep] at h; cases h
    | true =>
      simp only [hstep, Bool.cond_true] at h
      intro d e hs ht
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h d e hs ht
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        have he := List.singleton_sublist.mp hs
        cases hwx : inW d with
        | true =>
          rw [hwx, Bool.cond_true] at hstep
          exact ⟨rfl, loop1_uniq_spec hstep e he ht⟩
        | false =>
          rw [hwx, Bool.cond_false] at hstep
          rw [loop1_spec hstep e he] at ht
          cases ht

theorem loop3_uniq_spec {inT inW : Nat → Bool} {acc : Nat} {l : List Nat}
    (h : loop3_uniq inT inW acc l = true) :
    ∀ c d e, [c, d, e] <+ l → inT (acc ^^^ c ^^^ d ^^^ e) = true →
      inW c = true ∧ inW d = true ∧ inW e = true := by
  induction l with
  | nil => intro c d e hs; simp at hs
  | cons x l ih =>
    have e1 : loop3_uniq inT inW acc (x :: l) =
        cond (cond (inW x) (loop2_uniq inT inW (acc ^^^ x) l) (loop2 inT (acc ^^^ x) l))
          (loop3_uniq inT inW acc l) false := rfl
    rw [e1] at h
    cases hstep : cond (inW x) (loop2_uniq inT inW (acc ^^^ x) l) (loop2 inT (acc ^^^ x) l) with
    | false => rw [hstep] at h; cases h
    | true =>
      simp only [hstep, Bool.cond_true] at h
      intro c d e hs ht
      rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, hs⟩
      · exact ih h c d e hs ht
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        cases hwx : inW c with
        | true =>
          rw [hwx, Bool.cond_true] at hstep
          obtain ⟨hd, he⟩ := loop2_uniq_spec hstep d e hs ht
          exact ⟨rfl, hd, he⟩
        | false =>
          rw [hwx, Bool.cond_false] at hstep
          rw [loop2_spec hstep d e hs] at ht
          cases ht

/-! ### Middle-exponent sublist pigeonhole splits -/

theorem sublist3_split {α : Type*} {a b c : α} {l₁ l₂ : List α}
    (hs : [a, b, c] <+ l₁ ++ l₂) :
    ([a, b] <+ l₁ ∧ c ∈ l₁ ++ l₂) ∨ (a ∈ l₁ ++ l₂ ∧ [b, c] <+ l₂) := by
  have ha : a ∈ l₁ ++ l₂ := hs.subset (by simp)
  have hc : c ∈ l₁ ++ l₂ := hs.subset (by simp)
  obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp hs
  match u with
  | [] =>
    simp only [List.nil_append] at huv; subst huv
    exact Or.inr ⟨ha, (List.sublist_cons_self a [b, c]).trans hv⟩
  | [x] =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj huv
    exact Or.inr ⟨ha, hv⟩
  | x :: y :: rest =>
    obtain ⟨rfl, huv'⟩ := List.cons.inj huv
    obtain ⟨rfl, _⟩ := List.cons.inj huv'
    exact Or.inl ⟨(List.sublist_append_left [a, b] rest).trans hu, hc⟩

theorem sublist4_split {α : Type*} {a b c d : α} {l₁ l₂ : List α}
    (hs : [a, b, c, d] <+ l₁ ++ l₂) :
    ([a, b] <+ l₁ ∧ [c, d] <+ l₁ ++ l₂) ∨ ([a, b] <+ l₁ ++ l₂ ∧ [c, d] <+ l₂) := by
  have hcd : [c, d] <+ l₁ ++ l₂ := (List.sublist_append_right [a, b] [c, d]).trans hs
  have hab : [a, b] <+ l₁ ++ l₂ := (List.sublist_append_left [a, b] [c, d]).trans hs
  obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp hs
  match u with
  | [] =>
    simp only [List.nil_append] at huv; subst huv
    exact Or.inr ⟨hab, (List.sublist_append_right [a, b] [c, d]).trans hv⟩
  | [x] =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj huv
    exact Or.inr ⟨hab, (List.sublist_cons_self b [c, d]).trans hv⟩
  | x :: y :: rest =>
    obtain ⟨rfl, huv'⟩ := List.cons.inj huv
    obtain ⟨rfl, _⟩ := List.cons.inj huv'
    exact Or.inl ⟨(List.sublist_append_left [a, b] rest).trans hu, hcd⟩

theorem sublist5_split {α : Type*} {a b c d e : α} {l₁ l₂ : List α}
    (hs : [a, b, c, d, e] <+ l₁ ++ l₂) :
    ([a, b, c] <+ l₁ ∧ [d, e] <+ l₁ ++ l₂) ∨ ([a, b] <+ l₁ ++ l₂ ∧ [c, d, e] <+ l₂) := by
  have hde : [d, e] <+ l₁ ++ l₂ := (List.sublist_append_right [a, b, c] [d, e]).trans hs
  have hab : [a, b] <+ l₁ ++ l₂ := (List.sublist_append_left [a, b] [c, d, e]).trans hs
  obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp hs
  match u with
  | [] =>
    simp only [List.nil_append] at huv; subst huv
    exact Or.inr ⟨hab, (List.sublist_append_right [a, b] [c, d, e]).trans hv⟩
  | [x] =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj huv
    exact Or.inr ⟨hab, (List.sublist_cons_self b [c, d, e]).trans hv⟩
  | [x, y] =>
    obtain ⟨rfl, huv1⟩ := List.cons.inj huv
    obtain ⟨rfl, rfl⟩ := List.cons.inj huv1
    exact Or.inr ⟨hab, hv⟩
  | x :: y :: z :: rest =>
    obtain ⟨rfl, huv1⟩ := List.cons.inj huv
    obtain ⟨rfl, huv2⟩ := List.cons.inj huv1
    obtain ⟨rfl, _⟩ := List.cons.inj huv2
    exact Or.inl ⟨(List.sublist_append_left [a, b, c] rest).trans hu, hde⟩

theorem sublist7_split {α : Type*} {x1 x2 x3 x4 x5 x6 x7 : α} {l₁ l₂ : List α}
    (hs : [x1, x2, x3, x4, x5, x6, x7] <+ l₁ ++ l₂) :
    ([x1, x2, x3, x4] <+ l₁ ∧ [x5, x6, x7] <+ l₁ ++ l₂) ∨
      ([x1, x2, x3] <+ l₁ ++ l₂ ∧ [x4, x5, x6, x7] <+ l₂) := by
  have hr : [x5, x6, x7] <+ l₁ ++ l₂ :=
    (List.sublist_append_right [x1, x2, x3, x4] [x5, x6, x7]).trans hs
  have hl : [x1, x2, x3] <+ l₁ ++ l₂ :=
    (List.sublist_append_left [x1, x2, x3] [x4, x5, x6, x7]).trans hs
  obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp hs
  match u with
  | [] =>
    simp only [List.nil_append] at huv; subst huv
    exact Or.inr ⟨hl, (List.sublist_append_right [x1, x2, x3] [x4, x5, x6, x7]).trans hv⟩
  | [a] =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj huv
    exact Or.inr ⟨hl, (List.sublist_append_right [x2, x3] [x4, x5, x6, x7]).trans hv⟩
  | [a, b] =>
    obtain ⟨rfl, h1⟩ := List.cons.inj huv
    obtain ⟨rfl, rfl⟩ := List.cons.inj h1
    exact Or.inr ⟨hl, (List.sublist_cons_self x3 [x4, x5, x6, x7]).trans hv⟩
  | [a, b, c] =>
    obtain ⟨rfl, h1⟩ := List.cons.inj huv
    obtain ⟨rfl, h2⟩ := List.cons.inj h1
    obtain ⟨rfl, rfl⟩ := List.cons.inj h2
    exact Or.inr ⟨hl, hv⟩
  | a :: b :: c :: d :: rest =>
    obtain ⟨rfl, h1⟩ := List.cons.inj huv
    obtain ⟨rfl, h2⟩ := List.cons.inj h1
    obtain ⟨rfl, h3⟩ := List.cons.inj h2
    obtain ⟨rfl, _⟩ := List.cons.inj h3
    exact Or.inl ⟨(List.sublist_append_left [x1, x2, x3, x4] rest).trans hu, hr⟩

/-! ### Polynomial support normalization (`shiftDown` and exponent lists) -/

/-- Factor `X^m` out of `p` when every exponent in `p.support` is at least `m`. -/
noncomputable def shiftDown (m : Nat) (p : (ZMod 2)[X]) : (ZMod 2)[X] :=
  ∑ s ∈ p.support, (X : (ZMod 2)[X]) ^ (s - m)

theorem X_pow_mul_shiftDown {m : Nat} {p : (ZMod 2)[X]} (hm : ∀ s ∈ p.support, m ≤ s) :
    (X : (ZMod 2)[X]) ^ m * shiftDown m p = p := by
  unfold shiftDown
  rw [Finset.mul_sum]
  conv_rhs => rw [as_sum_support_X_pow p]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← pow_add, Nat.add_sub_of_le (hm s hs)]

theorem coeff_shiftDown {m : Nat} {p : (ZMod 2)[X]} (hm : ∀ s ∈ p.support, m ≤ s) (k : Nat) :
    (shiftDown m p).coeff k = p.coeff (k + m) := by
  unfold shiftDown
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  by_cases hk : k + m ∈ p.support
  · rw [Finset.sum_eq_single (k + m)]
    · simp only [Nat.add_sub_cancel, ↓reduceIte]
      have hne := mem_support_iff.mp hk
      generalize p.coeff (k + m) = c at hne
      revert c; decide
    · intro s hs hne
      have hle := hm s hs
      have : k ≠ s - m := by omega
      simp [this]
    · intro habs; exact absurd hk habs
  · have hk0 : p.coeff (k + m) = 0 := notMem_support_iff.mp hk
    rw [hk0, Finset.sum_eq_zero]
    intro s hs
    have hle := hm s hs
    have : k ≠ s - m := fun heq => hk (by rwa [heq, Nat.sub_add_cancel hle])
    simp [this]

theorem support_shiftDown_map {m : Nat} {p : (ZMod 2)[X]} (hm : ∀ s ∈ p.support, m ≤ s) :
    (shiftDown m p).support.map ⟨(· + m), add_left_injective m⟩ = p.support := by
  ext s
  simp only [Finset.mem_map, mem_support_iff, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rwa [← coeff_shiftDown hm k]
  · intro hs
    have hle := hm s (mem_support_iff.mpr hs)
    refine ⟨s - m, ?_, Nat.sub_add_cancel hle⟩
    rwa [coeff_shiftDown hm, Nat.sub_add_cancel hle]

theorem card_support_shiftDown {m : Nat} {p : (ZMod 2)[X]} (hm : ∀ s ∈ p.support, m ≤ s) :
    (shiftDown m p).support.card = p.support.card := by
  rw [← support_shiftDown_map hm, Finset.card_map]

theorem shiftDown_ne_zero {m : Nat} {p : (ZMod 2)[X]} (hp : p ≠ 0)
    (hm : ∀ s ∈ p.support, m ≤ s) : shiftDown m p ≠ 0 := by
  intro h0
  apply hp
  rw [← X_pow_mul_shiftDown hm, h0, mul_zero]

theorem dvd_shiftDown_of_dvd {m : Nat} {p : (ZMod 2)[X]} (hG : G ∣ p)
    (hm : ∀ s ∈ p.support, m ≤ s) : G ∣ shiftDown m p := by
  rw [← AdjoinRoot.mk_eq_zero, ← π]
  have h0 : π ((X : (ZMod 2)[X]) ^ m * shiftDown m p) = 0 := by
    rw [X_pow_mul_shiftDown hm]
    exact AdjoinRoot.mk_eq_zero.mpr hG
  rw [map_mul, map_pow] at h0
  exact (isUnit_π_X.pow m).mul_right_eq_zero.mp h0

theorem natDegree_shiftDown_add {m : Nat} {p : (ZMod 2)[X]} (hp : p ≠ 0)
    (hm : ∀ s ∈ p.support, m ≤ s) : (shiftDown m p).natDegree + m = p.natDegree := by
  have hxm : ((X : (ZMod 2)[X]) ^ m) ≠ 0 := pow_ne_zero m X_ne_zero
  have hmul := Polynomial.natDegree_mul hxm (shiftDown_ne_zero hp hm)
  rw [X_pow_mul_shiftDown hm, natDegree_X_pow] at hmul
  omega

/-- Extract a strictly increasing list of positive shifted exponents from a
nonzero multiple of `G`. -/
theorem exists_shifted_relation {p : (ZMod 2)[X]} (hp : p ≠ 0) (hG : G ∣ p) :
    ∃ (m : Nat) (ts : List Nat),
      m ∈ p.support ∧
      ts.Pairwise (· < ·) ∧
      ts.length + 1 = p.support.card ∧
      (∀ t ∈ ts, 1 ≤ t ∧ t + m ∈ p.support ∧ t + m ≤ p.natDegree) ∧
      (2147483648 ^^^ (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0) := by
  have h0 : π p = 0 := AdjoinRoot.mk_eq_zero.mpr hG
  have hnd : (p.support.sort).Nodup := Finset.sort_nodup ..
  have hle : (p.support.sort).Pairwise (· ≤ ·) := Finset.pairwise_sort ..
  have hcard : (p.support.sort).length = p.support.card := Finset.length_sort ..
  have hπ : ((p.support.sort).map fun s => π X ^ s).sum = 0 := by
    rw [← List.sum_toFinset _ hnd, Finset.sort_toFinset, ← h0]
    conv_rhs => rw [as_sum_support_X_pow p]
    simp [map_sum]
  have hne : p.support.sort ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [hcard] at this
    simp [hp] at this
  obtain ⟨m, rest, hl⟩ := List.exists_cons_of_ne_nil hne
  have hm_mem : m ∈ p.support :=
    (Finset.mem_sort _).mp (hl ▸ List.mem_cons_self ..)
  rw [hl] at hnd hle hcard hπ
  have hlt : ∀ e ∈ rest, m < e := fun e he =>
    lt_of_le_of_ne ((List.pairwise_cons.mp hle).1 e he)
      (fun h => (List.nodup_cons.mp hnd).1 (h ▸ he))
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
  refine ⟨m, rest.map (· - m), hm_mem, ?_, by simp [← hcard], ?_, ?_⟩
  · rw [List.pairwise_map]
    have h1 : rest.Pairwise (· < ·) :=
      ((List.pairwise_cons.mp hle).2.and (List.nodup_cons.mp hnd).2).imp
        fun h => lt_of_le_of_ne h.1 h.2
    refine h1.imp_of_mem fun {a b} ha _ hab => ?_
    have := hlt a ha
    omega
  · intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    have hmlt := hlt e he
    have he_supp : e ∈ p.support :=
      (Finset.mem_sort _).mp (hl ▸ List.mem_cons_of_mem _ he)
    exact ⟨by omega, by rwa [Nat.sub_add_cancel (le_of_lt hmlt)],
      by rw [Nat.sub_add_cancel (le_of_lt hmlt)]; exact le_natDegree_of_mem_supp e he_supp⟩
  · have h1 : (0x80000000 : UInt32) ^^^ ((rest.map (· - m)).map ρ).foldr (· ^^^ ·) 0 = 0 := by
      apply eq_of_π_P
      rw [P_xor, map_add, P_one, map_one, π_P_foldr, P_zero, map_zero]
      exact hπ
    have h2 := congrArg UInt32.toNat h1
    rwa [UInt32.toNat_xor, toNat_foldr] at h2

theorem sublist_range_of_pairwise_lt {ts : List Nat} {N : Nat}
    (hpw : ts.Pairwise (· < ·)) (hmem : ∀ t ∈ ts, 1 ≤ t ∧ t ≤ N) :
    ts <+ List.range' 1 N := by
  refine List.sublist_of_subperm_of_pairwise
    (List.subperm_of_subset (hpw.imp ne_of_lt) ?_) hpw List.pairwise_lt_range'
  intro t ht
  obtain ⟨h1, hN⟩ := hmem t ht
  rw [List.mem_range'_1]
  omega

/-- Given `0 ∈ p.support` and `p.natDegree = D > 0` for a multiple `p` of `G`,
extract the strictly increasing interior exponents `1 ≤ t₁ < ⋯ < tᵣ ≤ D - 1`
together with both the polynomial decomposition and the XOR relation. -/
theorem exists_interior_relation {p : (ZMod 2)[X]} {D : Nat} (hD : 0 < D)
    (hp : p ≠ 0) (hG : G ∣ p) (h0_mem : 0 ∈ p.support) (hdeg : p.natDegree = D) :
    ∃ ts : List Nat,
      ts <+ List.range' 1 (D - 1) ∧
      ts.length + 2 = p.support.card ∧
      (∀ t ∈ ts, t ∈ p.support) ∧
      p = X ^ D + (ts.map fun t => (X : (ZMod 2)[X]) ^ t).sum + 1 ∧
      ((0x80000000 ^^^ ρ D).toNat ^^^ (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0) := by
  have hD_mem : D ∈ p.support := hdeg ▸ natDegree_mem_support_of_nonzero hp
  let S := (p.support.erase 0).erase D
  let ts := S.sort
  have hnd : ts.Nodup := Finset.sort_nodup ..
  have hle : ts.Pairwise (· ≤ ·) := Finset.pairwise_sort ..
  have hpw : ts.Pairwise (· < ·) :=
    (hle.and hnd).imp fun h => lt_of_le_of_ne h.1 h.2
  have hD_in_e0 : D ∈ p.support.erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, hD_mem⟩
  have hcard : ts.length + 2 = p.support.card := by
    have c1 : S.card + 1 = (p.support.erase 0).card := Finset.card_erase_add_one hD_in_e0
    have c2 : (p.support.erase 0).card + 1 = p.support.card := Finset.card_erase_add_one h0_mem
    have c3 : ts.length = S.card := Finset.length_sort ..
    omega
  have hts_supp : ∀ t ∈ ts, t ∈ p.support := fun t ht => by
    have hS : t ∈ S := (Finset.mem_sort _).mp ht
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hS)
  have hsub : ts <+ List.range' 1 (D - 1) := by
    refine sublist_range_of_pairwise_lt hpw fun t ht => ?_
    have hS : t ∈ S := (Finset.mem_sort _).mp ht
    have hneD : t ≠ D := (Finset.mem_erase.mp hS).1
    have hne0 : t ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hS)).1
    have hleD : t ≤ D := hdeg ▸ le_natDegree_of_mem_supp t (hts_supp t ht)
    exact ⟨by omega, by omega⟩
  have hp_eq : p = X ^ D + (ts.map fun t => (X : (ZMod 2)[X]) ^ t).sum + 1 := by
    have hsum_ts : (ts.map fun t => (X : (ZMod 2)[X]) ^ t).sum = ∑ s ∈ S, (X : (ZMod 2)[X]) ^ s := by
      rw [← List.sum_toFinset _ hnd, Finset.sort_toFinset]
    rw [hsum_ts]
    conv_lhs => rw [as_sum_support_X_pow p]
    rw [← Finset.add_sum_erase _ _ h0_mem, ← Finset.add_sum_erase _ _ hD_in_e0, pow_zero]
    ring
  have hxor : (0x80000000 ^^^ ρ D).toNat ^^^ (ts.map fun i => (ρ i).toNat).foldr (· ^^^ ·) 0 = 0 := by
    have hπ0 : π p = 0 := AdjoinRoot.mk_eq_zero.mpr hG
    rw [hp_eq] at hπ0
    simp only [map_add, map_pow, map_one, List.map_map, map_list_sum, Function.comp_def] at hπ0
    have hword : (0x80000000 ^^^ ρ D) ^^^ (ts.map ρ).foldr (· ^^^ ·) 0 = 0 := by
      apply eq_of_π_P
      rw [P_xor, P_xor, map_add, map_add, P_one, map_one, π_P_ρ, π_P_foldr, P_zero, map_zero]
      have hcomm : (1 : Q) + π X ^ D + (ts.map fun x => π X ^ x).sum =
          π X ^ D + (ts.map fun t => π X ^ t).sum + 1 := by ring
      rw [hcomm]; exact hπ0
    have hn := congrArg UInt32.toNat hword
    rwa [UInt32.toNat_xor, toNat_foldr] at hn
  exact ⟨ts, hsub, hcard, hts_supp, hp_eq, hxor⟩

theorem zero_mem_and_natDegree_eq_of_minimal {p : (ZMod 2)[X]} {D : Nat}
    (hp : p ≠ 0) (hd : p.natDegree ≤ D)
    (hmin : ∀ m ∈ p.support, (∀ s ∈ p.support, m ≤ s) → D ≤ (shiftDown m p).natDegree) :
    0 ∈ p.support ∧ p.natDegree = D := by
  let m := p.support.min' (support_nonempty.mpr hp)
  have hm_mem : m ∈ p.support := Finset.min'_mem _ _
  have hm_le : ∀ s ∈ p.support, m ≤ s := fun s hs => Finset.min'_le _ s hs
  have hD_le : D ≤ (shiftDown m p).natDegree := hmin m hm_mem hm_le
  have hdeg_add : (shiftDown m p).natDegree + m = p.natDegree := natDegree_shiftDown_add hp hm_le
  have hm0 : m = 0 := by omega
  exact ⟨hm0 ▸ hm_mem, by omega⟩

theorem eq_of_sublist_of_all_inW {ts ws : List Nat} {N : Nat} {inW : Nat → Bool}
    (hsub : ts <+ List.range' 1 N)
    (hW : ∀ t ∈ ts, inW (ρ t).toNat = true)
    (hfilt : (List.range' 1 N).filter (fun i => inW (ρ i).toNat) = ws)
    (hlen : ts.length = ws.length) : ts = ws := by
  have h1 : ts <+ (List.range' 1 N).filter (fun i => inW (ρ i).toNat) := by
    rw [← List.filter_eq_self.mpr hW]
    exact hsub.filter _
  rw [hfilt] at h1
  exact h1.eq_of_length hlen

end ZeroMin

end Crc32c
