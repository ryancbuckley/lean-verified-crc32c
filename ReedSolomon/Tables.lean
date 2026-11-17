/-
The coefficient and table builders of `ReedSolomon.Impl.Gf` are correct:
* `ofByte_lagrange`: `lagrange` computes the spec's Lagrange coefficient;
* `tables_isTable`: `tables xs ys` is a table in the sense of the machine-code
  theorem (`ReedSolomon.Arm64MC.IsTable`), for the coefficients `lagrange`.
-/
import ReedSolomon.Field
import ReedSolomon.Spec
import ReedSolomon.Arm64.ApplySpec

namespace ReedSolomon
open Finset

noncomputable section

theorem gf_sub_eq_add (a b : GF256) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (gf_add_self b)]

/-- The points of a byte string, as field elements. -/
def pts (xs : ByteArray) : Fin xs.size → GF256 := fun i => ofByte xs[i]

theorem lagNumDen_spec (xs : ByteArray) (s : Nat) (y : UInt8) (t : Nat) :
    ofByte (lagNumDen xs s y t).1 =
        ∏ u ∈ range t, (if u = s then 1 else ofByte y + ofByte xs[u]!) ∧
      ofByte (lagNumDen xs s y t).2 =
        ∏ u ∈ range t, (if u = s then 1 else ofByte xs[s]! + ofByte xs[u]!) := by
  induction t with
  | zero => simp [lagNumDen, ofByte_one]
  | succ t ih =>
    rw [prod_range_succ, prod_range_succ, ← ih.1, ← ih.2]
    by_cases h : t = s
    · simp [lagNumDen, h]
    · simp [lagNumDen, h, ofByte_gfMul, ofByte_xor]

/-- `lagrange` is the Lagrange coefficient of the spec. -/
theorem ofByte_lagrange (xs : ByteArray) (s : Fin xs.size) (y : UInt8) :
    ofByte (lagrange xs s y) = lagrangeCoeff (pts xs) s (ofByte y) := by
  obtain ⟨hn, hd⟩ := lagNumDen_spec xs s y xs.size
  have hR : lagrangeCoeff (pts xs) s (ofByte y) = ∏ u ∈ range xs.size,
      (if u = s.val then 1 else (ofByte xs[s.val]! + ofByte xs[u]!)⁻¹ * (ofByte y + ofByte xs[u]!)) := by
    rw [Finset.prod_range (fun u => if u = s.val then (1 : GF256) else
        (ofByte xs[s.val]! + ofByte xs[u]!)⁻¹ * (ofByte y + ofByte xs[u]!)), lagrangeCoeff,
      ← Finset.mul_prod_erase univ _ (mem_univ s)]
    simp only [ite_true, one_mul]
    refine prod_congr rfl fun t ht => ?_
    have hts : t ≠ s := ne_of_mem_erase ht
    have hts' : t.val ≠ s.val := fun e => hts (Fin.ext e)
    simp only [hts', ite_false, pts, gf_sub_eq_add, getElem!_pos xs t.val t.isLt,
      getElem!_pos xs s.val s.isLt, Fin.getElem_fin]
  rw [hR, lagrange, ofByte_gfMul, ofByte_gfInv, hn, hd, ← prod_inv_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun u _ => ?_
  by_cases h : u = s.val
  · simp [h]
  · simp only [h, ite_false]; ring

end

private theorem getElem!_ofFn {n : Nat} (f : Fin n → UInt8) (t : Nat) (h : t < n) :
    (⟨Array.ofFn f⟩ : ByteArray)[t]! = f ⟨t, h⟩ := by
  have h' : t < (⟨Array.ofFn f⟩ : ByteArray).size := by
    show t < (Array.ofFn f).size; simpa using h
  rw [getElem!_pos _ t h']
  show (Array.ofFn f)[t]'(by simpa using h) = _
  simp

private theorem toUInt8_toNat (v : UInt8) : v.toNat.toUInt8 = v := by simp

theorem coeffs_get (xs ys : ByteArray) {j i : Nat} (hj : j < ys.size) (hi : i < xs.size) :
    (coeffs xs ys)[xs.size * j + i]! = lagrange xs i ys[j]! := by
  have hlt : xs.size * j + i < ys.size * xs.size := by
    have := Nat.mul_le_mul_left xs.size (show j + 1 ≤ ys.size by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; rw [Nat.mul_comm ys.size]; omega
  rw [coeffs, getElem!_ofFn _ _ hlt]
  dsimp only
  have e1 : (xs.size * j + i) % xs.size = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod_of_lt hi]
  have e2 : (xs.size * j + i) / xs.size = j := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  rw [e1, e2]

theorem size_coeffs (xs ys : ByteArray) : (coeffs xs ys).size = ys.size * xs.size :=
  Array.size_ofFn

/-- `tables xs ys` holds the split-nibble products of the coefficients
`lagrange xs i ys[j]`, laid out as `leanrs_apply` reads them. -/
theorem tables_isTable (xs ys : ByteArray) :
    Arm64MC.IsTable (fun t => (tables xs ys)[t]!) xs.size ys.size
      (fun j i => lagrange xs i ys[j]!) := by
  intro j hj i hi v hv
  have hn : xs.size * j + i < (coeffs xs ys).size := by
    rw [size_coeffs]
    have := Nat.mul_le_mul_left xs.size (show j + 1 ≤ ys.size by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; rw [Nat.mul_comm ys.size]; omega
  have e1 : 32 * xs.size * j + 32 * i + v.toNat = 32 * (xs.size * j + i) + v.toNat := by ring
  have e2 : 32 * xs.size * j + 32 * i + 16 + v.toNat = 32 * (xs.size * j + i) + (16 + v.toNat) := by
    ring
  constructor
  · dsimp only
    rw [e1, tables, tablesOf, getElem!_ofFn _ _ (by omega)]
    dsimp only
    rw [show (32 * (xs.size * j + i) + v.toNat) / 32 = xs.size * j + i by omega,
      show (32 * (xs.size * j + i) + v.toNat) % 32 = v.toNat by omega, if_pos hv,
      coeffs_get xs ys hj hi, toUInt8_toNat]
  · dsimp only
    rw [e2, tables, tablesOf, getElem!_ofFn _ _ (by omega)]
    dsimp only
    rw [show (32 * (xs.size * j + i) + (16 + v.toNat)) / 32 = xs.size * j + i by omega,
      show (32 * (xs.size * j + i) + (16 + v.toNat)) % 32 = 16 + v.toNat by omega,
      if_neg (by omega), coeffs_get xs ys hj hi, show 16 + v.toNat - 16 = v.toNat by omega,
      toUInt8_toNat]

theorem size_tables (xs ys : ByteArray) :
    (tables xs ys).size = 32 * xs.size * ys.size := by
  show (Array.ofFn _).size = _
  rw [Array.size_ofFn, size_coeffs]; ring

/-! ### End to end: the machine code with the proven tables -/

open Arm64MC in
/-- `leanrs_apply` run on the table `tables xs ys` computes Reed–Solomon shards.

From any state at the routine's entry with the registers and memory as
`Setup` requires, where the table bytes at `X0` are `tables xs ys` (so
`k = xs.size` inputs and `r = ys.size` outputs) and input shard `i` holds the
bytes `D i`, execution returns with byte `t` of output shard `j` equal to the
shard at the point `ys[j]` of the stripe whose shards at the points `xs` are
the input bytes at position `t`; nothing outside the output shards changes and
the callee-saved registers are preserved.

So with `xs` the data points and `ys` the parity points the routine encodes,
and with `xs` any `k` distinct surviving points and `ys` the lost ones it
reconstructs them (`shardAt_reconstruct`, `data_reconstruct`). -/
theorem apply_mc_rs {code : UInt64 → Option UInt32} {base : UInt64} {s : SimdModels.Arm64.ArmState}
    {inP outP : UInt64} {L : Nat} {src dst : Nat → UInt64} {D : Nat → Nat → UInt8}
    (xs ys : ByteArray) (hc : ApplyLoaded code base)
    (hs : Setup s.mem s.regs.x0 inP outP xs.size ys.size L (fun t => (tables xs ys)[t]!) src dst D)
    (hk : 0 < xs.size) (hr : 0 < ys.size) (hL : 64 ≤ L) (hL64 : L < 2 ^ 64)
    (hpc : s.pc = base) (hx1 : s.regs.x1 = inP) (hx2 : s.regs.x2 = outP)
    (hx3 : s.regs.x3 = xs.size.toUInt64) (hx4 : s.regs.x4 = ys.size.toUInt64)
    (hx5 : s.regs.x5 = L.toUInt64) :
    ∃ steps s', SimdModels.Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      (∀ (j : Fin ys.size), ∀ t < L, ∃ b, s'.mem (dst j + t.toUInt64) = some (.rw, b) ∧
        ofByte b = shardAt (pts xs) (fun i => ofByte (D i t)) (pts ys j)) ∧
      (∀ a : UInt64, ¬ InOut dst ys.size L a → s'.mem a = s.mem a) ∧
      Crc32c.Arm64MC.CalleeSaved s s' :=
  apply_mc_shards (cf := fun j i => lagrange xs i ys[j]!)
    (fun j i => by
      rw [ofByte_lagrange xs i, getElem!_pos ys j.val j.isLt]; rfl)
    hc hs (tables_isTable xs ys) hk hr hL hL64 hpc rfl hx1 hx2 hx3 hx4 hx5

end ReedSolomon
