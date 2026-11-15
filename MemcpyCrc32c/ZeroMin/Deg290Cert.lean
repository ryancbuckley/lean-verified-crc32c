/-
Kernel-evaluated lookup tables and search certificates for `zero6_290_minimal`
and `zero6_290_unique`. Separated from `Deg290.lean` so that the `decide +kernel`
certificates are cached independently of the polynomial-algebra wrapper proofs.
-/
import MemcpyCrc32c.ZeroMin.Common

namespace Crc32c.ZeroMin.Deg290
open ZeroMin
open scoped List

def keys142 : List Nat := 0 :: pairSums (resNat 142 (stepBit 0x80000000))
def keys162 : List Nat := 0 :: pairSums (resNat 162 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg290_res142%" : term =>
  return toExpr (resNat 142 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg290_res161%" : term =>
  return toExpr (resNat 161 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg290_res162%" : term =>
  return toExpr (resNat 162 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg290_trie142%" : term => return (Trie.build 32 keys142).toExpr
open Lean Elab Term in
elab "deg290_b142_lo%" : term => return mkRawNatLit (bitset (· % 65536) keys142)
open Lean Elab Term in
elab "deg290_b142_hi%" : term => return mkRawNatLit (bitset (· / 65536) keys142)

open Lean Elab Term in
elab "deg290_trie162%" : term => return (Trie.build 32 keys162).toExpr
open Lean Elab Term in
elab "deg290_b162_lo%" : term => return mkRawNatLit (bitset (· % 65536) keys162)
open Lean Elab Term in
elab "deg290_b162_hi%" : term => return mkRawNatLit (bitset (· / 65536) keys162)

set_option maxRecDepth 1000000

def res142 : List Nat := deg290_res142%
def res161 : List Nat := deg290_res161%
def res162 : List Nat := deg290_res162%

def res142Lo : List Nat := res142.take 71
def res142Hi : List Nat := res142.drop 71
def res161Lo : List Nat := res161.take 80
def res161Hi : List Nat := res161.drop 80

def table142 : Trie := deg290_trie142%
def b142Lo : Nat := deg290_b142_lo%
def b142Hi : Nat := deg290_b142_hi%

def table162 : Trie := deg290_trie162%
def b162Lo : Nat := deg290_b162_lo%
def b162Hi : Nat := deg290_b162_hi%

noncomputable def inTable142 (v : Nat) : Bool := inTable16 b142Lo b142Hi table142 v
noncomputable def inTable162 (v : Nat) : Bool := inTable16 b162Lo b162Hi table162 v

theorem res142_eq : res142 = resNat 142 (stepBit 0x80000000) := by decide +kernel
theorem res161_eq : res161 = resNat 161 (stepBit 0x80000000) := by decide +kernel
theorem res162_eq : res162 = resNat 162 (stepBit 0x80000000) := by decide +kernel

theorem res142_eq_map : res142 = (List.range' 1 142).map fun i => (ρ i).toNat := by
  rw [res142_eq, ← resNat_ρ]; rfl

theorem res161_eq_map : res161 = (List.range' 1 161).map fun i => (ρ i).toNat := by
  rw [res161_eq, ← resNat_ρ]; rfl

theorem res162_eq_map : res162 = (List.range' 1 162).map fun i => (ρ i).toNat := by
  rw [res162_eq, ← resNat_ρ]; rfl

theorem inTable142_zero : inTable142 0 = true := by decide +kernel
theorem pairsIn_res142 : pairsIn inTable142 res142 = true := by decide +kernel

theorem inTable162_zero : inTable162 0 = true := by decide +kernel
theorem pairsIn_res162 : pairsIn inTable162 res162 = true := by decide +kernel

/-- Check `loop2 inT t l` for every target `t ∈ targets`. -/
noncomputable def bandLoop (inT : Nat → Bool) (l : List Nat) (targets : List Nat) : Bool :=
  List.rec true (fun t _ ih => cond (loop2 inT t l) ih false) targets

theorem bandLoop_spec {inT : Nat → Bool} {l targets : List Nat}
    (h : bandLoop inT l targets = true) :
    ∀ t ∈ targets, ∀ a b, [a, b] <+ l → inT (t ^^^ a ^^^ b) = false := by
  induction targets with
  | nil => simp
  | cons x ts ih =>
    have e1 : bandLoop inT l (x :: ts) = cond (loop2 inT x l) (bandLoop inT l ts) false := rfl
    rw [e1] at h
    cases hx : loop2 inT x l with
    | false => rw [hx] at h; cases h
    | true =>
      simp only [hx, Bool.cond_true] at h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact loop2_spec hx
      · exact ih h t ht

open Lean Elab Term in
elab "deg290_targets_all%" : term =>
  return toExpr ((resNat 81 (ρ 209)).map (Nat.xor 2147483648))

open Lean Elab Term in
elab "deg290_targets_b1%" : term =>
  return toExpr ((resNat 62 (ρ 209)).map (Nat.xor 2147483648))

open Lean Elab Term in
elab "deg290_targets_b2%" : term =>
  return toExpr ((resNat 19 (ρ 271)).map (Nat.xor 2147483648))

def targetsAll : List Nat := deg290_targets_all%
def targetsB1 : List Nat := deg290_targets_b1%
def targetsB2 : List Nat := deg290_targets_b2%

theorem targetsAll_eq : targetsAll = (resNat 81 (ρ 209)).map (Nat.xor 2147483648) := by decide +kernel
theorem targetsB1_eq : targetsB1 = (resNat 62 (ρ 209)).map (Nat.xor 2147483648) := by decide +kernel
theorem targetsB2_eq : targetsB2 = (resNat 19 (ρ 271)).map (Nat.xor 2147483648) := by decide +kernel

theorem no_short_290 : loop1 inTable162 0 targetsAll = true := by decide +kernel

theorem band1_lo : bandLoop inTable142 res142Lo targetsB1 = true := by decide +kernel
theorem band1_hi : bandLoop inTable142 res142Hi targetsB1 = true := by decide +kernel

theorem band2_lo : bandLoop inTable162 res161Lo targetsB2 = true := by decide +kernel
theorem band2_hi : bandLoop inTable162 res161Hi targetsB2 = true := by decide +kernel

def target290 : Nat := ((0x80000000 : UInt32) ^^^ ρ 290).toNat

def inW290 (x : Nat) : Bool :=
  Nat.beq x (ρ 32).toNat || Nat.beq x (ρ 107).toNat ||
    Nat.beq x (ρ 113).toNat || Nat.beq x (ρ 136).toNat

theorem target290_not_in : inTable162 target290 = false := by decide +kernel
theorem uniq290_loop : loop2_uniq inTable162 inW290 target290 res162 = true := by decide +kernel
theorem filter_w290 :
    (List.range' 1 162).filter (fun i => inW290 (ρ i).toNat) = [32, 107, 113, 136] := by
  decide +kernel

end Crc32c.ZeroMin.Deg290
