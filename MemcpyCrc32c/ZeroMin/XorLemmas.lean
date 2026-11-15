/-
Pure `Nat` XOR `foldr` rearrangement lemmas over abstract elements, avoiding
`simp` / `ac_rfl` unfolding of concrete `ρ k` or `target*` expressions.
-/
import MemcpyCrc32c.ZeroMin.Common

namespace Crc32c.ZeroMin
open scoped List

theorem sublist_pair_eq {α : Type*} {a b c d : α} (h : [a, b] <+ [c, d]) :
    a = c ∧ b = d := by
  have heq : [a, b] = [c, d] := h.eq_of_length rfl
  exact ⟨(List.cons.inj heq).1, (List.cons.inj (List.cons.inj heq).2).1⟩

theorem foldr_map_xor0 {α : Type*} (f : α → Nat) (k : Nat)
    (h : k ^^^ ([].map f).foldr (· ^^^ ·) 0 = 0) : k = 0 := by
  simpa using h

theorem foldr_map_xor2_eq {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 : α}
    (h : k ^^^ ([t1, t2].map f).foldr (· ^^^ ·) 0 = 0) :
    k = f t1 ^^^ f t2 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]) h

theorem foldr_map_xor2_left {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 : α}
    (h : k ^^^ ([t1, t2].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t1 = f t2 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor2_right {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 : α}
    (h : k ^^^ ([t1, t2].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t2 = f t1 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor3_left {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 : α}
    (h : k ^^^ ([t1, t2, t3].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t1 ^^^ f t2 = f t3 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor3_right {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 : α}
    (h : k ^^^ ([t1, t2, t3].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t2 ^^^ f t3 = f t1 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor4_left {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 t4 : α}
    (h : k ^^^ ([t1, t2, t3, t4].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t1 ^^^ f t2 = f t3 ^^^ f t4 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor4_right {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 t4 : α}
    (h : k ^^^ ([t1, t2, t3, t4].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t3 ^^^ f t4 = f t1 ^^^ f t2 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor6_left {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 t4 t5 t6 : α}
    (h : k ^^^ ([t1, t2, t3, t4, t5, t6].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t1 ^^^ f t2 ^^^ f t3 = f t4 ^^^ f t5 ^^^ f t6 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor6_right {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 t4 t5 t6 : α}
    (h : k ^^^ ([t1, t2, t3, t4, t5, t6].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t4 ^^^ f t5 ^^^ f t6 = f t1 ^^^ f t2 ^^^ f t3 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor7_left {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 t4 t5 t6 t7 : α}
    (h : k ^^^ ([t1, t2, t3, t4, t5, t6, t7].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t1 ^^^ f t2 ^^^ f t3 ^^^ f t4 = f t5 ^^^ f t6 ^^^ f t7 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

theorem foldr_map_xor7_right {α : Type*} (f : α → Nat) (k : Nat) {t1 t2 t3 t4 t5 t6 t7 : α}
    (h : k ^^^ ([t1, t2, t3, t4, t5, t6, t7].map f).foldr (· ^^^ ·) 0 = 0) :
    k ^^^ f t4 ^^^ f t5 ^^^ f t6 ^^^ f t7 = f t1 ^^^ f t2 ^^^ f t3 :=
  xor_eq_of_eq_zero (by simp only [List.map, List.foldr, Nat.xor_zero]; ac_rfl) h

end Crc32c.ZeroMin
