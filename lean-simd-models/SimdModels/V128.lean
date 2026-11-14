/-
128-bit SIMD register lemmas (`V128`): quadword and lane decompositions, byte
shift (`vextq`), XOR (`veorq`), and GF(2) polynomial semantics for `PMULL`,
`PMULL2`, and `PCLMULQDQ` across all immediate selectors. Kernel-only proofs.
-/
import SimdModels.Semantics

namespace SimdModels
open Polynomial

/-! ### Layer 1: `V128` halves and lane relationships -/

theorem V128.lo64_ofHalves (lo hi : UInt64) : V128.lo64 (V128.ofHalves lo hi) = lo := by
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [V128.lo64, V128.ofHalves, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi',
    decide_true, Bool.true_and]
  simp [hi']

theorem V128.hi64_ofHalves (lo hi : UInt64) : V128.hi64 (V128.ofHalves lo hi) = hi := by
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [V128.hi64, V128.ofHalves, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hi', decide_true, Bool.true_and]
  simp [show ¬ 64 + i < 64 by omega]

theorem V128.ofHalves_lo_hi (v : V128) : V128.ofHalves (V128.lo64 v) (V128.hi64 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [V128.ofHalves, V128.lo64, V128.hi64, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  by_cases h64 : i < 64
  · simp [h64]
  · simp [h64, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]

theorem V128.lane64_zero (v : V128) : V128.lane64 v 0 = V128.lo64 v := by
  simp [V128.lane64, V128.lo64]

theorem V128.lane64_one (v : V128) : V128.lane64 v 1 = V128.hi64 v := by
  simp [V128.lane64, V128.hi64]

theorem V128.lanes64_eq (v : V128) : V128.lanes64 v = [V128.lo64 v, V128.hi64 v] := by
  simp [V128.lanes64, List.ofFn_succ, V128.lane64_zero, V128.lane64_one]

/-- Every 16-bit lane is the little-endian pair of two adjacent 8-bit lanes. -/
theorem V128.lane16_eq_lane8 (v : V128) (i : Fin 8) :
    V128.lane16 v i =
      (V128.lane8 v ⟨2 * i.val, by omega⟩).toUInt16 |||
        ((V128.lane8 v ⟨2 * i.val + 1, by omega⟩).toUInt16 <<< 8) := by
  rw [← UInt16.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have e16 : ∀ b : UInt8, b.toUInt16.toBitVec = b.toBitVec.setWidth 16 := fun _ => by simp
  have esh : ∀ x : UInt16, (x <<< 8).toBitVec = x.toBitVec <<< 8 := fun _ => by simp
  rw [UInt16.toBitVec_or, esh, e16, e16]
  simp only [V128.lane16, V128.lane8, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
  by_cases h8 : k < 8
  · simp [h8, show 8 * (2 * i.val) + k = 16 * i.val + k by omega]
  · simp [h8, show k - 8 < 8 by omega, show k - 8 < 16 by omega,
      show 8 * (2 * i.val + 1) + (k - 8) = 16 * i.val + k by omega]

/-- Every 32-bit lane is the little-endian pair of two adjacent 16-bit lanes. -/
theorem V128.lane32_eq_lane16 (v : V128) (i : Fin 4) :
    V128.lane32 v i =
      (V128.lane16 v ⟨2 * i.val, by omega⟩).toUInt32 |||
        ((V128.lane16 v ⟨2 * i.val + 1, by omega⟩).toUInt32 <<< 16) := by
  rw [← UInt32.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have e32 : ∀ b : UInt16, b.toUInt32.toBitVec = b.toBitVec.setWidth 32 := fun _ => by simp
  have esh : ∀ x : UInt32, (x <<< 16).toBitVec = x.toBitVec <<< 16 := fun _ => by simp
  rw [UInt32.toBitVec_or, esh, e32, e32]
  simp only [V128.lane32, V128.lane16, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
  by_cases h16 : k < 16
  · simp [h16, show 16 * (2 * i.val) + k = 32 * i.val + k by omega]
  · simp [h16, show k - 16 < 16 by omega, show k - 16 < 32 by omega,
      show 16 * (2 * i.val + 1) + (k - 16) = 32 * i.val + k by omega]

/-- Every 64-bit lane is the little-endian pair of two adjacent 32-bit lanes. -/
theorem V128.lane64_eq_lane32 (v : V128) (i : Fin 2) :
    V128.lane64 v i =
      (V128.lane32 v ⟨2 * i.val, by omega⟩).toUInt64 |||
        ((V128.lane32 v ⟨2 * i.val + 1, by omega⟩).toUInt64 <<< 32) := by
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have e64 : ∀ b : UInt32, b.toUInt64.toBitVec = b.toBitVec.setWidth 64 := fun _ => by simp
  have esh : ∀ x : UInt64, (x <<< 32).toBitVec = x.toBitVec <<< 32 := fun _ => by simp
  rw [UInt64.toBitVec_or, esh, e64, e64]
  simp only [V128.lane64, V128.lane32, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
  by_cases h32 : k < 32
  · simp [h32, show 32 * (2 * i.val) + k = 64 * i.val + k by omega]
  · simp [h32, show k - 32 < 32 by omega, show k - 32 < 64 by omega,
      show 32 * (2 * i.val + 1) + (k - 32) = 64 * i.val + k by omega]

/-! ### Layer 2 & 3: Vector instruction semantics -/

theorem V128.lane8_veorq (a b : V128) (i : Fin 16) :
    V128.lane8 (Model.veorq a b) i = V128.lane8 a i ^^^ V128.lane8 b i := by
  rw [← UInt8.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [Model.veorq, V128.lane8, hk]

theorem V128.lane8_vextq (a b : V128) (imm i : Fin 16) :
    V128.lane8 (Model.vextq a b imm) i =
      if h : imm.val + i.val < 16 then
        V128.lane8 a ⟨imm.val + i.val, h⟩
      else
        V128.lane8 b ⟨imm.val + i.val - 16, by omega⟩ := by
  split_ifs with h
  · rw [← UInt8.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [Model.vextq, V128.lane8, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, hk, decide_true, Bool.true_and]
    have h1 : 8 * i.val + k < 128 := by omega
    have heq : 8 * imm.val + (8 * i.val + k) = 8 * (imm.val + i.val) + k := by omega
    simp only [h1, decide_true, Bool.true_and, heq]
    exact if_pos (by omega)
  · rw [← UInt8.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [Model.vextq, V128.lane8, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, hk, decide_true, Bool.true_and]
    have h1 : 8 * i.val + k < 128 := by omega
    have heq : 8 * imm.val + (8 * i.val + k) - 128 = 8 * (imm.val + i.val - 16) + k := by omega
    simp only [h1, decide_true, Bool.true_and, heq]
    exact if_neg (by omega)

theorem polyN_ofHalves (lo hi : UInt64) :
    polyN (V128.ofHalves lo hi) = polyN lo.toBitVec + polyN hi.toBitVec * X ^ 64 := by
  rw [V128.ofHalves, polyN_append]
  ring

theorem polyR_ofHalves (lo hi : UInt64) :
    polyR (V128.ofHalves lo hi) = polyR lo.toBitVec * X ^ 64 + polyR hi.toBitVec := by
  rw [polyR_halves]
  have hlo : (V128.ofHalves lo hi).setWidth 64 = lo.toBitVec :=
    congrArg UInt64.toBitVec (V128.lo64_ofHalves lo hi)
  have hhi : ((V128.ofHalves lo hi) >>> 64).setWidth 64 = hi.toBitVec :=
    congrArg UInt64.toBitVec (V128.hi64_ofHalves lo hi)
  rw [hlo, hhi]

theorem polyN_veorq (a b : V128) : polyN (Model.veorq a b) = polyN a + polyN b :=
  polyN_xor a b

theorem polyR_veorq (a b : V128) : polyR (Model.veorq a b) = polyR a + polyR b :=
  polyR_xor a b

theorem vmull_p64_spec (a b : V128) :
    polyN (Model.vmull_p64 a b) = polyN (V128.lo64 a).toBitVec * polyN (V128.lo64 b).toBitVec :=
  polynomialMult_spec _ _

theorem vmull_high_p64_spec (a b : V128) :
    polyN (Model.vmull_high_p64 a b) =
      polyN (V128.hi64 a).toBitVec * polyN (V128.hi64 b).toBitVec :=
  polynomialMult_spec _ _

theorem clmulepi64_spec (a b : V128) (imm8 : UInt8) :
    polyN (Model.clmulepi64 a b imm8) =
      polyN (if imm8.toBitVec.getLsbD 0 then (V128.hi64 a).toBitVec else (V128.lo64 a).toBitVec) *
        polyN (if imm8.toBitVec.getLsbD 4 then (V128.hi64 b).toBitVec else (V128.lo64 b).toBitVec) :=
  polynomialMult_spec _ _

theorem clmulepi64_spec_reflected (a b : V128) (imm8 : UInt8) :
    polyR (Model.clmulepi64 a b imm8) =
      X * (polyR (if imm8.toBitVec.getLsbD 0 then (V128.hi64 a).toBitVec else (V128.lo64 a).toBitVec) *
        polyR (if imm8.toBitVec.getLsbD 4 then (V128.hi64 b).toBitVec else (V128.lo64 b).toBitVec)) := by
  unfold Model.clmulepi64
  set s1 := if imm8.toBitVec.getLsbD 0 then (V128.hi64 a).toBitVec else (V128.lo64 a).toBitVec
  set s2 := if imm8.toBitVec.getLsbD 4 then (V128.hi64 b).toBitVec else (V128.lo64 b).toBitVec
  have h := clmul_spec_reflected ⟨s1⟩ ⟨s2⟩
  simpa only [Model.clmulLo, Model.clmulHi, ← polyR_halves] using h

theorem clmulepi64_00_eq_vmull_p64 (a b : V128) :
    Model.clmulepi64 a b 0x00 = Model.vmull_p64 a b := rfl

theorem clmulepi64_11_eq_vmull_high_p64 (a b : V128) :
    Model.clmulepi64 a b 0x11 = Model.vmull_high_p64 a b := rfl

end SimdModels
