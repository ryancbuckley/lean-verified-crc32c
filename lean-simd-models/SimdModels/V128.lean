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
    have hlt : 8 * (imm.val + i.val) + k < 128 := by omega
    simp [h1, heq, hlt]
  · rw [← UInt8.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [Model.vextq, V128.lane8, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, hk, decide_true, Bool.true_and]
    have h1 : 8 * i.val + k < 128 := by omega
    have hnlt : ¬ 8 * imm.val + (8 * i.val + k) < 128 := by omega
    have heq : 8 * imm.val + (8 * i.val + k) - 128 = 8 * (imm.val + i.val - 16) + k := by omega
    simp [h1, hnlt, heq]

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

/-! ### Unaligned 64-bit / 128-bit memory load lemmas (`loadU64LE`, `vld1q`) -/

theorem V128.lane8_ofHalves (lo hi : UInt64) (k : Fin 16) :
    V128.lane8 (V128.ofHalves lo hi) k =
      if k.val < 8 then ⟨(lo.toBitVec >>> (8 * k.val)).setWidth 8⟩
      else ⟨(hi.toBitVec >>> (8 * (k.val - 8))).setWidth 8⟩ := by
  split_ifs with hk
  · rw [← UInt8.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [V128.lane8, V128.ofHalves, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
    simp [show 8 * k.val + j < 64 by omega]
  · rw [← UInt8.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [V128.lane8, V128.ofHalves, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
    simp [show ¬ 8 * k.val + j < 64 by omega,
      show 8 * k.val + j - 64 = 8 * (k.val - 8) + j by omega]

theorem V128.lo64_vld1q (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 16 ≤ a.size) :
    V128.lo64 (Model.vld1q a i hs h) = Model.loadU64LE a i hs (by omega) := by
  unfold Model.vld1q
  exact V128.lo64_ofHalves _ _

theorem V128.hi64_vld1q (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 16 ≤ a.size) :
    have _ : (i + 8).toNat = i.toNat + 8 := Model.usize_add_toNat i 8 (by omega)
    V128.hi64 (Model.vld1q a i hs h) = Model.loadU64LE a (i + 8) hs (by omega) := by
  unfold Model.vld1q
  exact V128.hi64_ofHalves _ _

private theorem getLsbD_byte_in_u64 (b : UInt8) (m r j : Nat)
    (hm : m < 8) (hr : r < 8) (hj : j < 8) :
    ((b.toUInt64 <<< (8 * m).toUInt64).toBitVec).getLsbD (8 * r + j) =
      (decide (m = r) && b.toBitVec.getLsbD (8 * r + j - 8 * m)) := by
  have e64 : b.toUInt64.toBitVec = b.toBitVec.setWidth 64 := by simp
  have esh : (b.toUInt64 <<< (8 * m).toUInt64).toBitVec = b.toUInt64.toBitVec <<< (8 * m) := by
    simp [Nat.mod_eq_of_lt (show 8 * m < 64 by omega)]
  have hidx : 8 * r + j < 64 := by omega
  rw [esh, e64, BitVec.getLsbD_shiftLeft]
  simp only [hidx, decide_true, Bool.true_and, BitVec.getLsbD_setWidth]
  by_cases heq : m = r
  · subst heq
    simp [show ¬ 8 * m + j < 8 * m by omega, show j < 64 by omega]
  · by_cases hlt : m < r
    · simp [heq, show ¬ 8 * r + j < 8 * m by omega, show 8 * r + j - 8 * m < 64 by omega,
        BitVec.getLsbD_of_ge b.toBitVec (8 * r + j - 8 * m) (by omega)]
    · simp [heq, show 8 * r + j < 8 * m by omega]

private theorem word64_byte (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (r : Nat) (hr : r < 8) :
    (⟨((Model.word64 b0 b1 b2 b3 b4 b5 b6 b7).toBitVec >>> (8 * r)).setWidth 8⟩ : UInt8) =
      match r with
      | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
      | 4 => b4 | 5 => b5 | 6 => b6 | _ => b7 := by
  rw [← UInt8.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb0 : b0.toUInt64 = b0.toUInt64 <<< (8 * 0).toUInt64 := by simp
  unfold Model.word64
  rw [hb0]
  have lhs_eq :
      (((b0.toUInt64 <<< (8 * 0).toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
        (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)).toBitVec >>> (8 * r)).setWidth 8).getLsbD j =
      (((b0.toUInt64 <<< (8 * 0).toUInt64 ||| (b1.toUInt64 <<< (8 * 1).toUInt64) |||
        (b2.toUInt64 <<< (8 * 2).toUInt64) ||| (b3.toUInt64 <<< (8 * 3).toUInt64) |||
        (b4.toUInt64 <<< (8 * 4).toUInt64) ||| (b5.toUInt64 <<< (8 * 5).toUInt64) |||
        (b6.toUInt64 <<< (8 * 6).toUInt64) ||| (b7.toUInt64 <<< (8 * 7).toUInt64)).toBitVec >>>
        (8 * r)).setWidth 8).getLsbD j := rfl
  rw [lhs_eq]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and,
    UInt64.toBitVec_or, BitVec.getLsbD_or,
    getLsbD_byte_in_u64 _ 0 r j (by omega) hr hj,
    getLsbD_byte_in_u64 _ 1 r j (by omega) hr hj,
    getLsbD_byte_in_u64 _ 2 r j (by omega) hr hj,
    getLsbD_byte_in_u64 _ 3 r j (by omega) hr hj,
    getLsbD_byte_in_u64 _ 4 r j (by omega) hr hj,
    getLsbD_byte_in_u64 _ 5 r j (by omega) hr hj,
    getLsbD_byte_in_u64 _ 6 r j (by omega) hr hj,
    getLsbD_byte_in_u64 _ 7 r j (by omega) hr hj]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem uget_eq (a : ByteArray) (j : USize) (n : Nat) (hj : j.toNat = n)
    (h : j.toNat < a.size) : a.uget j h = a[n]'(hj ▸ h) := by
  subst hj; rfl

theorem loadU64LE_byte (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) (r : Nat) (hr : r < 8) :
    (⟨((Model.loadU64LE a i hs h).toBitVec >>> (8 * r)).setWidth 8⟩ : UInt8) =
      a[i.toNat + r]'(by omega) := by
  have h1 : (i + 1).toNat = i.toNat + 1 := Model.usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := Model.usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := Model.usize_add_toNat i 3 (by omega)
  have h4 : (i + 4).toNat = i.toNat + 4 := Model.usize_add_toNat i 4 (by omega)
  have h5 : (i + 5).toNat = i.toNat + 5 := Model.usize_add_toNat i 5 (by omega)
  have h6 : (i + 6).toNat = i.toNat + 6 := Model.usize_add_toNat i 6 (by omega)
  have h7 : (i + 7).toNat = i.toNat + 7 := Model.usize_add_toNat i 7 (by omega)
  unfold Model.loadU64LE
  dsimp only
  rw [word64_byte _ _ _ _ _ _ _ _ r hr]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using uget_eq a i i.toNat rfl (by omega)
  · exact uget_eq a (i + 1) (i.toNat + 1) h1 (by omega)
  · exact uget_eq a (i + 2) (i.toNat + 2) h2 (by omega)
  · exact uget_eq a (i + 3) (i.toNat + 3) h3 (by omega)
  · exact uget_eq a (i + 4) (i.toNat + 4) h4 (by omega)
  · exact uget_eq a (i + 5) (i.toNat + 5) h5 (by omega)
  · exact uget_eq a (i + 6) (i.toNat + 6) h6 (by omega)
  · exact uget_eq a (i + 7) (i.toNat + 7) h7 (by omega)

/-- Lane `k` (`0 ≤ k < 16`) of an unaligned 128-bit load `vld1q` at byte offset
`i` equals `a[i + k]`. -/
theorem V128.lane8_vld1q (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 16 ≤ a.size) (k : Fin 16) :
    V128.lane8 (Model.vld1q a i hs h) k = a[i.toNat + k.val]'(by omega) := by
  have h8 : (i + 8).toNat = i.toNat + 8 := Model.usize_add_toNat i 8 (by omega)
  unfold Model.vld1q
  rw [V128.lane8_ofHalves]
  split_ifs with hk
  · exact loadU64LE_byte a i hs (by omega) k.val hk
  · rw [loadU64LE_byte a (i + 8) hs (by omega) (k.val - 8) (by omega)]
    congr 1
    omega

end SimdModels
