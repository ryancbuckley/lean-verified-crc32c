/-
Algebraic, flag/condition, vector-lane, memory-permission, stack-slot, and
step/relocation lemmas for `SimdModels.Arm64` (Phase 7).

All proofs are kernel-checked without `bv_decide`.
-/
import SimdModels.Arm64
import SimdModels.V128

namespace SimdModels.Arm64

private theorem u64_ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem usize_le_u64 : USize.size ≤ 2 ^ 64 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [USize.size, h]

/-! ### `UInt64` / `UInt32` XOR AC instances for `ac_rfl` -/

instance : Std.Associative (· ^^^ · : UInt64 → UInt64 → UInt64) where
  assoc a b c := by
    rw [← UInt64.toBitVec_inj]
    simp [BitVec.xor_assoc]

instance : Std.Commutative (· ^^^ · : UInt64 → UInt64 → UInt64) where
  comm a b := by
    rw [← UInt64.toBitVec_inj]
    simp [BitVec.xor_comm]

instance : Std.Associative (· ^^^ · : UInt32 → UInt32 → UInt32) where
  assoc a b c := by
    rw [← UInt32.toBitVec_inj]
    simp [BitVec.xor_assoc]

instance : Std.Commutative (· ^^^ · : UInt32 → UInt32 → UInt32) where
  comm a b := by
    rw [← UInt32.toBitVec_inj]
    simp [BitVec.xor_comm]

/-! ### `V128.ofHalves` and Neon vector instruction rewrite lemmas -/

@[simp] theorem lo64_ofHalves_simp (lo hi : UInt64) :
    V128.lo64 (V128.ofHalves lo hi) = lo :=
  V128.lo64_ofHalves lo hi

@[simp] theorem hi64_ofHalves_simp (lo hi : UInt64) :
    V128.hi64 (V128.ofHalves lo hi) = hi :=
  V128.hi64_ofHalves lo hi

@[simp] theorem lane64_zero_simp (v : V128) :
    V128.lane64 v 0 = V128.lo64 v :=
  V128.lane64_zero v

@[simp] theorem lane64_one_simp (v : V128) :
    V128.lane64 v 1 = V128.hi64 v :=
  V128.lane64_one v

@[simp] theorem veorq_ofHalves (a0 a1 b0 b1 : UInt64) :
    Model.veorq (V128.ofHalves a0 a1) (V128.ofHalves b0 b1) =
      V128.ofHalves (a0 ^^^ b0) (a1 ^^^ b1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Model.veorq, V128.ofHalves, BitVec.getLsbD_xor, BitVec.getLsbD_append]
  by_cases h64 : i < 64 <;> simp [h64]

@[simp] theorem veor8b_ofHalves (a0 a1 b0 b1 : UInt64) :
    veor8b (V128.ofHalves a0 a1) (V128.ofHalves b0 b1) =
      V128.ofHalves (a0 ^^^ b0) 0 := by
  simp [veor8b]

@[simp] theorem veor3q_ofHalves (a0 a1 b0 b1 c0 c1 : UInt64) :
    veor3q (V128.ofHalves a0 a1) (V128.ofHalves b0 b1) (V128.ofHalves c0 c1) =
      V128.ofHalves ((a0 ^^^ b0) ^^^ c0) ((a1 ^^^ b1) ^^^ c1) := by
  simp [veor3q]

@[simp] theorem zip2_2d_ofHalves (a0 a1 b0 b1 : UInt64) :
    zip2_2d (V128.ofHalves a0 a1) (V128.ofHalves b0 b1) =
      V128.ofHalves a1 b1 := by
  simp [zip2_2d]

@[simp] theorem insLane64_zero_ofHalves (a0 a1 v : UInt64) :
    insLane64 (V128.ofHalves a0 a1) 0 v = V128.ofHalves v a1 := by
  simp [insLane64]

@[simp] theorem insLane64_one_ofHalves (a0 a1 v : UInt64) :
    insLane64 (V128.ofHalves a0 a1) 1 v = V128.ofHalves a0 v := by
  simp [insLane64]

@[simp] theorem vextq_8_ofHalves (a0 a1 b0 b1 : UInt64) :
    Model.vextq (V128.ofHalves a0 a1) (V128.ofHalves b0 b1) 8 =
      V128.ofHalves a1 b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he8 : (8 : Fin 16).val = 8 := rfl
  simp only [Model.vextq, he8, V128.ofHalves, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  by_cases h64 : i < 64
  · simp [h64, show 8 * 8 + i < 128 by omega, show ¬ 8 * 8 + i < 64 by omega,
      show 8 * 8 + i - 64 = i by omega]
  · simp [h64, show ¬ 8 * 8 + i < 128 by omega, show ¬ 64 ≤ i - 64 by omega,
      show 8 * 8 + i - 128 = i - 64 by omega]

@[simp] theorem vmull_p64_ofHalves (a0 a1 b0 b1 : UInt64) :
    Model.vmull_p64 (V128.ofHalves a0 a1) (V128.ofHalves b0 b1) =
      V128.ofHalves (Model.clmulLo a0 b0) (Model.clmulHi a0 b0) := by
  unfold Model.vmull_p64
  rw [V128.lo64_ofHalves, V128.lo64_ofHalves]
  have h := V128.ofHalves_lo_hi (Model.polynomialMult a0.toBitVec b0.toBitVec)
  simpa [Model.clmulLo, Model.clmulHi, V128.lo64, V128.hi64] using h.symm

/-! ### `AddWithCarry`, `SUBS`/`CMP`, `TST`, and `ConditionHolds` lemmas -/

private theorem bitvec64_not_toNat (y : BitVec 64) :
    (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := by
  rw [BitVec.toNat_not]

private theorem addWithCarry_sub64_fst_bv (x y : UInt64) :
    (addWithCarry x.toBitVec (~~~y.toBitVec) true).1 = (x - y).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toBitVec.toNat < 2 ^ 64 := x.toBitVec.isLt
  have hy : y.toBitVec.toNat < 2 ^ 64 := y.toBitVec.isLt
  simp only [addWithCarry, ↓reduceIte, bitvec64_not_toNat, BitVec.toNat_ofNat,
    UInt64.toBitVec_sub, BitVec.toNat_sub]
  congr 1
  omega

@[simp] theorem addWithCarry_sub64_fst (x y : UInt64) :
    (⟨(addWithCarry x.toBitVec (~~~y.toBitVec) true).1⟩ : UInt64) = x - y := by
  rw [addWithCarry_sub64_fst_bv]

private theorem sub64_flags_z (x y : UInt64) :
    (addWithCarry x.toBitVec (~~~y.toBitVec) true).2.z = (x == y) := by
  have hfst := addWithCarry_sub64_fst_bv x y
  have hz : (addWithCarry x.toBitVec (~~~y.toBitVec) true).2.z =
      ((addWithCarry x.toBitVec (~~~y.toBitVec) true).1 == 0#64) := rfl
  rw [hz, hfst]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : (x - y).toBitVec ≠ 0#64 := by
      intro h0
      apply hxy
      have hadd := congrArg (· + y.toBitVec) h0
      simp only [BitVec.zero_add, UInt64.toBitVec_sub, BitVec.sub_add_cancel] at hadd
      exact UInt64.eq_of_toBitVec_eq hadd
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hxy]

private theorem sub64_flags_c (x y : UInt64) :
    (addWithCarry x.toBitVec (~~~y.toBitVec) true).2.c = decide (y ≤ x) := by
  have hx : x.toNat < 2 ^ 64 := x.toBitVec.isLt
  have hy : y.toNat < 2 ^ 64 := y.toBitVec.isLt
  simp only [addWithCarry, ↓reduceIte, bitvec64_not_toNat, BitVec.toNat_ofNat]
  change decide ((x.toNat + (2 ^ 64 - 1 - y.toNat) + 1) % 2 ^ 64 !=
      x.toNat + (2 ^ 64 - 1 - y.toNat) + 1) = decide (y.toNat ≤ x.toNat)
  by_cases hle : y.toNat ≤ x.toNat
  · have hsum : x.toNat + (2 ^ 64 - 1 - y.toNat) + 1 = 2 ^ 64 + (x.toNat - y.toNat) := by omega
    have hlt : x.toNat - y.toNat < 2 ^ 64 := by omega
    have hmod : (2 ^ 64 + (x.toNat - y.toNat)) % 2 ^ 64 = x.toNat - y.toNat := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
    rw [hsum, hmod]
    simp [hle]
  · have hlt : x.toNat + (2 ^ 64 - 1 - y.toNat) + 1 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    simp [hle]

@[simp] theorem conditionHolds_eq_sub64 (x y : UInt64) :
    conditionHolds 0 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = (x == y) := by
  simp [conditionHolds, sub64_flags_z]

@[simp] theorem conditionHolds_ne_sub64 (x y : UInt64) :
    conditionHolds 1 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = (x != y) := by
  simp [conditionHolds, sub64_flags_z, bne]

@[simp] theorem conditionHolds_hs_sub64 (x y : UInt64) :
    conditionHolds 2 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (y ≤ x) := by
  simp [conditionHolds, sub64_flags_c]

@[simp] theorem conditionHolds_lo_sub64 (x y : UInt64) :
    conditionHolds 3 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (x < y) := by
  have h2 := conditionHolds_hs_sub64 x y
  have hrel : conditionHolds 3 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 =
      !conditionHolds 2 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 := rfl
  rw [hrel, h2]
  change (!decide (y.toNat ≤ x.toNat)) = decide (x.toNat < y.toNat)
  by_cases h : y.toNat ≤ x.toNat
  · simp [h, show ¬ x.toNat < y.toNat by omega]
  · simp [h, show x.toNat < y.toNat by omega]

@[simp] theorem conditionHolds_hi_sub64 (x y : UInt64) :
    conditionHolds 8 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (y < x) := by
  have hdef : conditionHolds 8 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 =
      ((addWithCarry x.toBitVec (~~~y.toBitVec) true).2.c &&
        !(addWithCarry x.toBitVec (~~~y.toBitVec) true).2.z) := rfl
  rw [hdef, sub64_flags_c, sub64_flags_z]
  by_cases hxy : x = y
  · subst hxy
    change (decide (x.toNat ≤ x.toNat) && !(x == x)) = decide (x.toNat < x.toNat)
    simp
  · have hne_nat : x.toNat ≠ y.toNat := fun h => hxy (u64_ext h)
    change (decide (y.toNat ≤ x.toNat) && !(x == y)) = decide (y.toNat < x.toNat)
    by_cases hle : y.toNat ≤ x.toNat
    · simp [hle, hxy, show y.toNat < x.toNat by omega]
    · simp [hle, show ¬ y.toNat < x.toNat by omega]

@[simp] theorem conditionHolds_ls_sub64 (x y : UInt64) :
    conditionHolds 9 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 = decide (x ≤ y) := by
  have h8 := conditionHolds_hi_sub64 x y
  have hrel : conditionHolds 9 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 =
      !conditionHolds 8 (addWithCarry x.toBitVec (~~~y.toBitVec) true).2 := rfl
  rw [hrel, h8]
  change (!decide (y.toNat < x.toNat)) = decide (x.toNat ≤ y.toNat)
  by_cases h : y.toNat < x.toNat
  · simp [h, show ¬ x.toNat ≤ y.toNat by omega]
  · simp [h, show x.toNat ≤ y.toNat by omega]

@[simp] theorem conditionHolds_eq_pstate (n z c v : Bool) :
    conditionHolds 0 { n, z, c, v } = z := rfl

@[simp] theorem conditionHolds_ne_pstate (n z c v : Bool) :
    conditionHolds 1 { n, z, c, v } = !z := rfl

/-! ### `UBFM` (`LSL`, `LSR`, `UBFIZ`) simplification lemmas -/

private theorem mask_lsb_of_lt {w : Nat} (m i : Nat) (hm : m < w) (hi : i < w) :
    (((BitVec.ofNat w 1) <<< m) - BitVec.ofNat w 1).getLsbD i = decide (i < m) := by
  have hw : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hm_pow : 2 ^ m < 2 ^ w := Nat.pow_lt_pow_right (by omega) hm
  have h1 : (BitVec.ofNat w 1 <<< m).toNat = 2 ^ m := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
    simpa [Nat.shiftLeft_eq] using Nat.mod_eq_of_lt hm_pow
  have hle : BitVec.ofNat w 1 ≤ BitVec.ofNat w 1 <<< m := by
    rw [BitVec.le_def, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
    exact Nat.one_le_two_pow
  have hval : (((BitVec.ofNat w 1) <<< m) - BitVec.ofNat w 1).toNat = 2 ^ m - 1 := by
    rw [BitVec.toNat_sub_of_le hle, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  rw [BitVec.getLsbD_eq_getElem hi]
  change (((BitVec.ofNat w 1) <<< m) - BitVec.ofNat w 1).toNat.testBit i = decide (i < m)
  rw [hval, Nat.testBit_two_pow_sub_one]

@[simp] theorem evalUbfm_lsr64 (x : UInt64) (k : Nat) (hk : k < 64) :
    (⟨evalUbfm x.toBitVec k 63⟩ : UInt64) = x >>> k.toUInt64 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [← UInt64.toBitVec_inj]
    change (x.toBitVec >>> (0 : Nat)) &&& BitVec.allOnes 64 = (x >>> (0 : UInt64)).toBitVec
    rw [BitVec.ushiftRight_zero, BitVec.and_allOnes]
    simp
  · rw [← UInt64.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hmod : (k.toUInt64.toBitVec % 64).toNat = k := by
      rw [BitVec.toNat_umod]
      change (k % 2 ^ 64) % 64 = k
      omega
    have hrhs : (x >>> k.toUInt64).toBitVec = x.toBitVec >>> k := by
      change x.toBitVec >>> (k.toUInt64.toBitVec % 64) = x.toBitVec >>> k
      rw [BitVec.ushiftRight_eq', hmod]
    rw [hrhs]
    unfold evalUbfm
    have hnfull : ¬ 63 - k + 1 ≥ 64 := by omega
    simp only [show 63 ≥ k by omega, hnfull, ↓reduceIte, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, mask_lsb_of_lt (63 - k + 1) i (by omega) hi]
    by_cases hi2 : i < 63 - k + 1
    · simp [hi2]
    · simp [hi2, BitVec.getLsbD_of_ge x.toBitVec (k + i) (by omega)]

@[simp] theorem evalUbfm_lsr32 (x : UInt32) (k : Nat) (hk : k < 32) :
    (⟨evalUbfm x.toBitVec k 31⟩ : UInt32) = x >>> k.toUInt32 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [← UInt32.toBitVec_inj]
    change (x.toBitVec >>> (0 : Nat)) &&& BitVec.allOnes 32 = (x >>> (0 : UInt32)).toBitVec
    rw [BitVec.ushiftRight_zero, BitVec.and_allOnes]
    simp
  · rw [← UInt32.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hmod : (k.toUInt32.toBitVec % 32).toNat = k := by
      rw [BitVec.toNat_umod]
      change (k % 2 ^ 32) % 32 = k
      omega
    have hrhs : (x >>> k.toUInt32).toBitVec = x.toBitVec >>> k := by
      change x.toBitVec >>> (k.toUInt32.toBitVec % 32) = x.toBitVec >>> k
      rw [BitVec.ushiftRight_eq', hmod]
    rw [hrhs]
    unfold evalUbfm
    have hnfull : ¬ 31 - k + 1 ≥ 32 := by omega
    simp only [show 31 ≥ k by omega, hnfull, ↓reduceIte, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, mask_lsb_of_lt (31 - k + 1) i (by omega) hi]
    by_cases hi2 : i < 31 - k + 1
    · simp [hi2]
    · simp [hi2, BitVec.getLsbD_of_ge x.toBitVec (k + i) (by omega)]

/-- A64 `LSL Xd, Xn, #sh` (`0 < sh < 64`) is encoded as `UBFM Xd, Xn, #(64 - sh), #(63 - sh)`,
so `s + 1 = r`. -/
@[simp] theorem evalUbfm_lsl64 (x : UInt64) (r s : Nat)
    (hsr : s + 1 = r) (hr : r < 64) :
    (⟨evalUbfm x.toBitVec r s⟩ : UInt64) = x <<< (64 - r).toUInt64 := by
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmod : ((64 - r).toUInt64.toBitVec % 64).toNat = 64 - r := by
    rw [BitVec.toNat_umod]
    change ((64 - r) % 2 ^ 64) % 64 = 64 - r
    omega
  have hrhs : (x <<< (64 - r).toUInt64).toBitVec = x.toBitVec <<< (64 - r) := by
    change x.toBitVec <<< ((64 - r).toUInt64.toBitVec % 64) = x.toBitVec <<< (64 - r)
    rw [BitVec.shiftLeft_eq', hmod]
  rw [hrhs]
  unfold evalUbfm
  simp only [show ¬ s ≥ r by omega, ↓reduceIte, show ¬ s + 1 ≥ 64 by omega,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  by_cases hsh : i < 64 - r
  · simp [hsh]
  · rw [mask_lsb_of_lt (s + 1) (i - (64 - r)) (by omega) (by omega)]
    simp [hsh, show i - (64 - r) < s + 1 by omega]

@[simp] theorem evalUbfm_ubfiz32_64 (x : UInt64) (r : Nat)
    (hr1 : 31 < r) (hr2 : r < 64) :
    (⟨evalUbfm x.toBitVec r 31⟩ : UInt64) = x.toUInt32.toUInt64 <<< (64 - r).toUInt64 := by
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e32 : x.toUInt32.toUInt64.toBitVec = (x.toBitVec.setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    change x.toBitVec.toNat % 2 ^ 32 = x.toBitVec.toNat % 2 ^ 32 % 2 ^ 64
    omega
  have hmod : ((64 - r).toUInt64.toBitVec % 64).toNat = 64 - r := by
    rw [BitVec.toNat_umod]
    change ((64 - r) % 2 ^ 64) % 64 = 64 - r
    omega
  have hrhs : (x.toUInt32.toUInt64 <<< (64 - r).toUInt64).toBitVec =
      ((x.toBitVec.setWidth 32).setWidth 64) <<< (64 - r) := by
    change x.toUInt32.toUInt64.toBitVec <<< ((64 - r).toUInt64.toBitVec % 64) = _
    rw [BitVec.shiftLeft_eq', hmod, e32]
  rw [hrhs]
  unfold evalUbfm
  simp only [show ¬ (31 : Nat) ≥ r by omega, ↓reduceIte, show ¬ (32 : Nat) ≥ 64 by decide,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  by_cases hsh : i < 64 - r
  · simp [hsh]
  · have hj : i - (64 - r) < 64 := by omega
    rw [mask_lsb_of_lt 32 (i - (64 - r)) (by decide) hj]
    simp [hsh, hj, Bool.and_comm]

/-! ### Permissioned memory: read-only slices, invariance under writes, and stack slots -/

namespace Mem

/-- `[base, base + bs.size)` is mapped `.ro` with exact byte contents `bs` (no wraparound). -/
def hasROBytes (m : Mem) (base : UInt64) (bs : ByteArray) : Prop :=
  base.toNat + bs.size ≤ UInt64.size ∧
  ∀ k (hk : k < bs.size), m (base + k.toUInt64) = some (.ro, bs[k])

/-- `[lo, lo + len)` is mapped `.rw` (writable stack memory, no wraparound). -/
def isRWRange (m : Mem) (lo : UInt64) (len : Nat) : Prop :=
  lo.toNat + len ≤ UInt64.size ∧
  ∀ k < len, ∃ b, m (lo + k.toUInt64) = some (.rw, b)

theorem uint64_add_nat_assoc (base : UInt64) (a b : Nat)
    (h : base.toNat + a + b < UInt64.size) :
    base + a.toUInt64 + b.toUInt64 = base + (a + b).toUInt64 := by
  apply u64_ext
  have : UInt64.size = 2 ^ 64 := rfl
  simp only [UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem hasROBytes_readU8 {m : Mem} {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) (off : Nat) (hoff : off < bs.size) :
    m.readU8 (base + off.toUInt64) = some bs[off] := by
  rcases hro with ⟨_, hbytes⟩
  simp [readU8, hbytes off hoff]

private theorem uget_eq_getElem (bs : ByteArray) (j : USize) (n : Nat) (hj : j.toNat = n)
    (h : j.toNat < bs.size) : bs.uget j h = bs[n]'(hj ▸ h) := by
  subst hj; rfl

theorem hasROBytes_readU8_model {m : Mem} {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) (i : USize) (hi : i.toNat < bs.size) :
    m.readU8 (base + i.toUInt64) = some (Model.loadU8 bs i hi) := by
  have heq : i.toUInt64 = i.toNat.toUInt64 := u64_ext (by
    rw [USize.toNat_toUInt64]
    simp [Nat.toUInt64])
  rw [heq, hasROBytes_readU8 hro i.toNat hi]
  rfl

theorem hasROBytes_readU16LE {m : Mem} {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) (off : Nat) (hoff : off + 2 ≤ bs.size) :
    m.readU16LE (base + off.toUInt64) =
      some (bs[off].toUInt16 ||| (bs[off + 1].toUInt16 <<< 8)) := by
  have hb := hro.1
  have h1 : base + off.toUInt64 + 1 = base + (off + 1).toUInt64 := by
    simpa using uint64_add_nat_assoc base off 1 (by omega)
  simp only [readU16LE, Option.bind_eq_bind, Option.bind, h1,
    hasROBytes_readU8 hro off (by omega),
    hasROBytes_readU8 hro (off + 1) (by omega)]

theorem hasROBytes_readU32LE {m : Mem} {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) (off : Nat) (hoff : off + 4 ≤ bs.size) :
    m.readU32LE (base + off.toUInt64) =
      some (bs[off].toUInt32 ||| (bs[off + 1].toUInt32 <<< 8) |||
        (bs[off + 2].toUInt32 <<< 16) ||| (bs[off + 3].toUInt32 <<< 24)) := by
  have hb := hro.1
  have h1 : base + off.toUInt64 + 1 = base + (off + 1).toUInt64 := by
    simpa using uint64_add_nat_assoc base off 1 (by omega)
  have h2 : base + off.toUInt64 + 2 = base + (off + 2).toUInt64 := by
    simpa using uint64_add_nat_assoc base off 2 (by omega)
  have h3 : base + off.toUInt64 + 3 = base + (off + 3).toUInt64 := by
    simpa using uint64_add_nat_assoc base off 3 (by omega)
  simp only [readU32LE, Option.bind_eq_bind, Option.bind, h1, h2, h3,
    hasROBytes_readU8 hro off (by omega),
    hasROBytes_readU8 hro (off + 1) (by omega),
    hasROBytes_readU8 hro (off + 2) (by omega),
    hasROBytes_readU8 hro (off + 3) (by omega)]

theorem hasROBytes_readU64LE {m : Mem} {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) (hs : bs.size < USize.size)
    (i : USize) (hi : i.toNat + 8 ≤ bs.size) :
    m.readU64LE (base + i.toUInt64) = some (Model.loadU64LE bs i hs hi) := by
  have hb := hro.1
  have heq : i.toUInt64 = i.toNat.toUInt64 := u64_ext (by
    rw [USize.toNat_toUInt64]
    simp [Nat.toUInt64])
  rw [heq]
  have h1 : base + i.toNat.toUInt64 + 1 = base + (i.toNat + 1).toUInt64 := by
    simpa using uint64_add_nat_assoc base i.toNat 1 (by omega)
  have h2 : base + i.toNat.toUInt64 + 2 = base + (i.toNat + 2).toUInt64 := by
    simpa using uint64_add_nat_assoc base i.toNat 2 (by omega)
  have h3 : base + i.toNat.toUInt64 + 3 = base + (i.toNat + 3).toUInt64 := by
    simpa using uint64_add_nat_assoc base i.toNat 3 (by omega)
  have h4 : base + i.toNat.toUInt64 + 4 = base + (i.toNat + 4).toUInt64 := by
    simpa using uint64_add_nat_assoc base i.toNat 4 (by omega)
  have h5 : base + i.toNat.toUInt64 + 5 = base + (i.toNat + 5).toUInt64 := by
    simpa using uint64_add_nat_assoc base i.toNat 5 (by omega)
  have h6 : base + i.toNat.toUInt64 + 6 = base + (i.toNat + 6).toUInt64 := by
    simpa using uint64_add_nat_assoc base i.toNat 6 (by omega)
  have h7 : base + i.toNat.toUInt64 + 7 = base + (i.toNat + 7).toUInt64 := by
    simpa using uint64_add_nat_assoc base i.toNat 7 (by omega)
  have us1 : (i + 1).toNat = i.toNat + 1 := Model.usize_add_toNat i 1 (by omega)
  have us2 : (i + 2).toNat = i.toNat + 2 := Model.usize_add_toNat i 2 (by omega)
  have us3 : (i + 3).toNat = i.toNat + 3 := Model.usize_add_toNat i 3 (by omega)
  have us4 : (i + 4).toNat = i.toNat + 4 := Model.usize_add_toNat i 4 (by omega)
  have us5 : (i + 5).toNat = i.toNat + 5 := Model.usize_add_toNat i 5 (by omega)
  have us6 : (i + 6).toNat = i.toNat + 6 := Model.usize_add_toNat i 6 (by omega)
  have us7 : (i + 7).toNat = i.toNat + 7 := Model.usize_add_toNat i 7 (by omega)
  have u0 := uget_eq_getElem bs i i.toNat rfl (by omega)
  have u1 := uget_eq_getElem bs (i + 1) (i.toNat + 1) us1 (by omega)
  have u2 := uget_eq_getElem bs (i + 2) (i.toNat + 2) us2 (by omega)
  have u3 := uget_eq_getElem bs (i + 3) (i.toNat + 3) us3 (by omega)
  have u4 := uget_eq_getElem bs (i + 4) (i.toNat + 4) us4 (by omega)
  have u5 := uget_eq_getElem bs (i + 5) (i.toNat + 5) us5 (by omega)
  have u6 := uget_eq_getElem bs (i + 6) (i.toNat + 6) us6 (by omega)
  have u7 := uget_eq_getElem bs (i + 7) (i.toNat + 7) us7 (by omega)
  simp only [readU64LE, Model.loadU64LE, Option.bind_eq_bind, Option.bind,
    h1, h2, h3, h4, h5, h6, h7,
    hasROBytes_readU8 hro i.toNat (by omega),
    hasROBytes_readU8 hro (i.toNat + 1) (by omega),
    hasROBytes_readU8 hro (i.toNat + 2) (by omega),
    hasROBytes_readU8 hro (i.toNat + 3) (by omega),
    hasROBytes_readU8 hro (i.toNat + 4) (by omega),
    hasROBytes_readU8 hro (i.toNat + 5) (by omega),
    hasROBytes_readU8 hro (i.toNat + 6) (by omega),
    hasROBytes_readU8 hro (i.toNat + 7) (by omega),
    u0, u1, u2, u3, u4, u5, u6, u7]

theorem hasROBytes_readV128LE {m : Mem} {base : UInt64} {bs : ByteArray}
    (hro : m.hasROBytes base bs) (hs : bs.size < USize.size)
    (i : USize) (hi : i.toNat + 16 ≤ bs.size) :
    have _ : (i + 8).toNat = i.toNat + 8 := Model.usize_add_toNat i 8 (by omega)
    m.readV128LE (base + i.toUInt64) =
      some (V128.ofHalves (Model.loadU64LE bs i hs (by omega))
        (Model.loadU64LE bs (i + 8) hs (by omega))) := by
  intro h8
  have hb := hro.1
  have hus : USize.size ≤ 2 ^ 64 := usize_le_u64
  have heq1 : i.toUInt64 = i.toNat.toUInt64 := u64_ext (by
    rw [USize.toNat_toUInt64]
    simp [Nat.toUInt64])
  have heq2 : (i + 8).toUInt64 = (i.toNat + 8).toUInt64 := u64_ext (by
    rw [USize.toNat_toUInt64, h8]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega)
  have hadd : base + i.toUInt64 + 8 = base + (i + 8).toUInt64 := by
    rw [heq1, heq2]
    simpa using uint64_add_nat_assoc base i.toNat 8 (by omega)
  simp only [readV128LE, Option.bind_eq_bind, Option.bind, hadd,
    hasROBytes_readU64LE hro hs i (by omega),
    hasROBytes_readU64LE hro hs (i + 8) (by omega)]

/-- Every successful `writeU8` preserves all `.ro` bytes without any address
disjointness arithmetic, because `writeU8` requires `Perm.rw` at the target! -/
theorem writeU8_preserves_ro {m m' : Mem} {waddr a : UInt64} {wb b : UInt8}
    (hw : m.writeU8 waddr wb = some m') (hro : m a = some (.ro, b)) :
    m' a = some (.ro, b) := by
  unfold writeU8 at hw
  split at hw
  · rename_i old hold
    cases hw
    by_cases heq : a = waddr
    · subst heq; rw [hro] at hold; cases hold
    · simp [heq, hro]
  · cases hw

/-- Every successful `writeU8` preserves all unmapped (`none`) guard bytes! -/
theorem writeU8_preserves_none {m m' : Mem} {waddr a : UInt64} {wb : UInt8}
    (hw : m.writeU8 waddr wb = some m') (hnone : m a = none) :
    m' a = none := by
  unfold writeU8 at hw
  split at hw
  · rename_i old hold
    cases hw
    by_cases heq : a = waddr
    · subst heq; rw [hnone] at hold; cases hold
    · simp [heq, hnone]
  · cases hw

/-- Total 1-byte `.rw` update helper so symbolic execution avoids existential splits. -/
def putRWByte (m : Mem) (addr : UInt64) (b : UInt8) : Mem :=
  fun a => if a = addr then some (.rw, b) else m a

/-- Total 4-byte little-endian `.rw` slot update. -/
def writeSlot32 (m : Mem) (addr : UInt64) (v : UInt32) : Mem :=
  (((m.putRWByte addr v.toUInt8).putRWByte (addr + 1) (v >>> 8).toUInt8).putRWByte
    (addr + 2) (v >>> 16).toUInt8).putRWByte (addr + 3) (v >>> 24).toUInt8

/-- Total 8-byte little-endian `.rw` slot update. -/
def writeSlot64 (m : Mem) (addr : UInt64) (v : UInt64) : Mem :=
  (((((((m.putRWByte addr v.toUInt8).putRWByte (addr + 1) (v >>> 8).toUInt8).putRWByte
    (addr + 2) (v >>> 16).toUInt8).putRWByte (addr + 3) (v >>> 24).toUInt8).putRWByte
    (addr + 4) (v >>> 32).toUInt8).putRWByte (addr + 5) (v >>> 40).toUInt8).putRWByte
    (addr + 6) (v >>> 48).toUInt8).putRWByte (addr + 7) (v >>> 56).toUInt8

theorem writeU8_eq_putRWByte {m : Mem} {addr : UInt64} {old b : UInt8}
    (hrw : m addr = some (.rw, old)) :
    m.writeU8 addr b = some (m.putRWByte addr b) := by
  unfold writeU8 putRWByte
  simp [hrw]

theorem putRWByte_isRWRange {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (addr : UInt64) (b : UInt8) :
    (m.putRWByte addr b).isRWRange lo len := by
  refine ⟨hrw.1, fun k hk => ?_⟩
  by_cases h : lo + k.toUInt64 = addr
  · exact ⟨b, by simp [putRWByte, h]⟩
  · obtain ⟨old, hold⟩ := hrw.2 k hk
    exact ⟨old, by simp [putRWByte, h, hold]⟩

@[simp] theorem writeSlot32_isRWRange {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (addr : UInt64) (v : UInt32) :
    (m.writeSlot32 addr v).isRWRange lo len := by
  unfold writeSlot32
  exact putRWByte_isRWRange (putRWByte_isRWRange (putRWByte_isRWRange
    (putRWByte_isRWRange hrw _ _) _ _) _ _) _ _

@[simp] theorem writeSlot64_isRWRange {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (addr : UInt64) (v : UInt64) :
    (m.writeSlot64 addr v).isRWRange lo len := by
  unfold writeSlot64
  exact putRWByte_isRWRange (putRWByte_isRWRange (putRWByte_isRWRange (putRWByte_isRWRange
    (putRWByte_isRWRange (putRWByte_isRWRange (putRWByte_isRWRange
      (putRWByte_isRWRange hrw _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _

theorem writeU32LE_of_isRWRange {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32) :
    m.writeU32LE (lo + off.toUInt64) v = some (m.writeSlot32 (lo + off.toUInt64) v) := by
  have hb := hrw.1
  let base := lo + off.toUInt64
  have stepRW : ∀ (m1 : Mem) (h1 : m1.isRWRange lo len) (d : Nat) (_ : d < 4) (b : UInt8),
      m1.writeU8 (base + d.toUInt64) b = some (m1.putRWByte (base + d.toUInt64) b) := by
    intro m1 h1 d hd b
    have heq := uint64_add_nat_assoc lo off d (by omega)
    obtain ⟨old, hold⟩ := h1.2 (off + d) (by omega)
    change m1.writeU8 (lo + off.toUInt64 + d.toUInt64) b = _
    rw [heq]
    exact writeU8_eq_putRWByte hold
  have s0 : m.writeU8 base v.toUInt8 = some (m.putRWByte base v.toUInt8) := by
    simpa [base] using stepRW m hrw 0 (by omega) v.toUInt8
  let m1 := m.putRWByte base v.toUInt8
  have hrw1 : m1.isRWRange lo len := putRWByte_isRWRange hrw _ _
  have s1 : m1.writeU8 (base + 1) (v >>> 8).toUInt8 =
      some (m1.putRWByte (base + 1) (v >>> 8).toUInt8) := by
    simpa using stepRW m1 hrw1 1 (by omega) (v >>> 8).toUInt8
  let m2 := m1.putRWByte (base + 1) (v >>> 8).toUInt8
  have hrw2 : m2.isRWRange lo len := putRWByte_isRWRange hrw1 _ _
  have s2 : m2.writeU8 (base + 2) (v >>> 16).toUInt8 =
      some (m2.putRWByte (base + 2) (v >>> 16).toUInt8) := by
    simpa using stepRW m2 hrw2 2 (by omega) (v >>> 16).toUInt8
  let m3 := m2.putRWByte (base + 2) (v >>> 16).toUInt8
  have hrw3 : m3.isRWRange lo len := putRWByte_isRWRange hrw2 _ _
  have s3 : m3.writeU8 (base + 3) (v >>> 24).toUInt8 =
      some (m3.putRWByte (base + 3) (v >>> 24).toUInt8) := by
    simpa using stepRW m3 hrw3 3 (by omega) (v >>> 24).toUInt8
  change m.writeU32LE base v = some (m.writeSlot32 base v)
  simp [writeU32LE, writeSlot32, m1, m2, m3] at s0 s1 s2 s3 ⊢
  simp [s0, s1, s2, s3]

theorem writeU64LE_of_isRWRange {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64) :
    m.writeU64LE (lo + off.toUInt64) v = some (m.writeSlot64 (lo + off.toUInt64) v) := by
  have hb := hrw.1
  let base := lo + off.toUInt64
  have stepRW : ∀ (m1 : Mem) (h1 : m1.isRWRange lo len) (d : Nat) (_ : d < 8) (b : UInt8),
      m1.writeU8 (base + d.toUInt64) b = some (m1.putRWByte (base + d.toUInt64) b) := by
    intro m1 h1 d hd b
    have heq := uint64_add_nat_assoc lo off d (by omega)
    obtain ⟨old, hold⟩ := h1.2 (off + d) (by omega)
    change m1.writeU8 (lo + off.toUInt64 + d.toUInt64) b = _
    rw [heq]
    exact writeU8_eq_putRWByte hold
  have s0 : m.writeU8 base v.toUInt8 = some (m.putRWByte base v.toUInt8) := by
    simpa [base] using stepRW m hrw 0 (by omega) v.toUInt8
  let m1 := m.putRWByte base v.toUInt8
  have hrw1 := putRWByte_isRWRange hrw base v.toUInt8
  have s1 : m1.writeU8 (base + 1) (v >>> 8).toUInt8 =
      some (m1.putRWByte (base + 1) (v >>> 8).toUInt8) := by
    simpa using stepRW m1 hrw1 1 (by omega) (v >>> 8).toUInt8
  let m2 := m1.putRWByte (base + 1) (v >>> 8).toUInt8
  have hrw2 := putRWByte_isRWRange hrw1 (base + 1) (v >>> 8).toUInt8
  have s2 : m2.writeU8 (base + 2) (v >>> 16).toUInt8 =
      some (m2.putRWByte (base + 2) (v >>> 16).toUInt8) := by
    simpa using stepRW m2 hrw2 2 (by omega) (v >>> 16).toUInt8
  let m3 := m2.putRWByte (base + 2) (v >>> 16).toUInt8
  have hrw3 := putRWByte_isRWRange hrw2 (base + 2) (v >>> 16).toUInt8
  have s3 : m3.writeU8 (base + 3) (v >>> 24).toUInt8 =
      some (m3.putRWByte (base + 3) (v >>> 24).toUInt8) := by
    simpa using stepRW m3 hrw3 3 (by omega) (v >>> 24).toUInt8
  let m4 := m3.putRWByte (base + 3) (v >>> 24).toUInt8
  have hrw4 := putRWByte_isRWRange hrw3 (base + 3) (v >>> 24).toUInt8
  have s4 : m4.writeU8 (base + 4) (v >>> 32).toUInt8 =
      some (m4.putRWByte (base + 4) (v >>> 32).toUInt8) := by
    simpa using stepRW m4 hrw4 4 (by omega) (v >>> 32).toUInt8
  let m5 := m4.putRWByte (base + 4) (v >>> 32).toUInt8
  have hrw5 := putRWByte_isRWRange hrw4 (base + 4) (v >>> 32).toUInt8
  have s5 : m5.writeU8 (base + 5) (v >>> 40).toUInt8 =
      some (m5.putRWByte (base + 5) (v >>> 40).toUInt8) := by
    simpa using stepRW m5 hrw5 5 (by omega) (v >>> 40).toUInt8
  let m6 := m5.putRWByte (base + 5) (v >>> 40).toUInt8
  have hrw6 := putRWByte_isRWRange hrw5 (base + 5) (v >>> 40).toUInt8
  have s6 : m6.writeU8 (base + 6) (v >>> 48).toUInt8 =
      some (m6.putRWByte (base + 6) (v >>> 48).toUInt8) := by
    simpa using stepRW m6 hrw6 6 (by omega) (v >>> 48).toUInt8
  let m7 := m6.putRWByte (base + 6) (v >>> 48).toUInt8
  have hrw7 := putRWByte_isRWRange hrw6 (base + 6) (v >>> 48).toUInt8
  have s7 : m7.writeU8 (base + 7) (v >>> 56).toUInt8 =
      some (m7.putRWByte (base + 7) (v >>> 56).toUInt8) := by
    simpa using stepRW m7 hrw7 7 (by omega) (v >>> 56).toUInt8
  change m.writeU64LE base v = some (m.writeSlot64 base v)
  simp [writeU64LE, writeSlot64, m1, m2, m3, m4, m5, m6, m7] at s0 s1 s2 s3 s4 s5 s6 s7 ⊢
  simp [s0, s1, s2, s3, s4, s5, s6, s7]

private theorem addr_ne_add (addr : UInt64) (i j : UInt64)
    (h : addr.toNat + 8 ≤ UInt64.size) (hi : i.toNat < 8) (hj : j.toNat < 8)
    (hne : i.toNat ≠ j.toNat) :
    addr + i ≠ addr + j := by
  intro heq
  have : UInt64.size = 2 ^ 64 := rfl
  have hi' : (addr + i).toNat = addr.toNat + i.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hj' : (addr + j).toNat = addr.toNat + j.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have := congrArg UInt64.toNat heq
  omega

private theorem u32_byte_shift (v : UInt32) (m k : Nat) (hm : m < 4) (hk : k < 32) :
    (((v >>> (8 * m).toUInt32).toUInt8.toUInt32 <<< (8 * m).toUInt32).toBitVec).getLsbD k =
      (decide (8 * m ≤ k ∧ k < 8 * m + 8) && v.toBitVec.getLsbD k) := by
  have hm_sh : ((8 * m).toUInt32.toBitVec % 32).toNat = 8 * m := by
    rw [BitVec.toNat_umod]
    change ((8 * m) % 2 ^ 32) % 32 = 8 * m
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have eshl : ∀ u : UInt32, (u <<< (8 * m).toUInt32).toBitVec = u.toBitVec <<< (8 * m) := by
    intro u
    change u.toBitVec <<< ((8 * m).toUInt32.toBitVec % 32) = _
    rw [BitVec.shiftLeft_eq', hm_sh]
  have eshr : (v >>> (8 * m).toUInt32).toBitVec = v.toBitVec >>> (8 * m) := by
    change v.toBitVec >>> ((8 * m).toUInt32.toBitVec % 32) = _
    rw [BitVec.ushiftRight_eq', hm_sh]
  have e8 : ∀ u : UInt32, u.toUInt8.toUInt32.toBitVec = (u.toBitVec.setWidth 8).setWidth 32 := by
    intro u
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    change u.toBitVec.toNat % 2 ^ 8 = u.toBitVec.toNat % 2 ^ 8 % 2 ^ 32
    omega
  rw [eshl, e8, eshr, BitVec.getLsbD_shiftLeft]
  simp only [hk, decide_true, Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases hlo : k < 8 * m
  · simp [hlo, show ¬ 8 * m ≤ k by omega]
  · by_cases hhi : k < 8 * m + 8
    · simp [hlo, hhi, show 8 * m ≤ k by omega, show k - 8 * m < 32 by omega,
        show k - 8 * m < 8 by omega, show 8 * m + (k - 8 * m) = k by omega]
    · simp [hlo, hhi, show ¬ k - 8 * m < 8 by omega]

private theorem reassemble_u32 (v : UInt32) :
    v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8) |||
      ((v >>> 16).toUInt8.toUInt32 <<< 16) ||| ((v >>> 24).toUInt8.toUInt32 <<< 24) = v := by
  rw [← UInt32.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have b0 : (v.toUInt8.toUInt32.toBitVec).getLsbD k =
      (decide (0 ≤ k ∧ k < 8) && v.toBitVec.getLsbD k) := by
    simpa [show (8 * 0).toUInt32 = (0 : UInt32) from rfl] using u32_byte_shift v 0 k (by omega) hk
  have b1 := u32_byte_shift v 1 k (by omega) hk
  have b2 := u32_byte_shift v 2 k (by omega) hk
  have b3 := u32_byte_shift v 3 k (by omega) hk
  change (((v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8) |||
      ((v >>> 16).toUInt8.toUInt32 <<< 16) ||| ((v >>> 24).toUInt8.toUInt32 <<< 24)).toBitVec).getLsbD k) = _
  rw [UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_or]
  simp only [BitVec.getLsbD_or]
  rw [b0]
  rw [show (((v >>> 8).toUInt8.toUInt32 <<< 8).toBitVec).getLsbD k = _ from b1]
  rw [show (((v >>> 16).toUInt8.toUInt32 <<< 16).toBitVec).getLsbD k = _ from b2]
  rw [show (((v >>> 24).toUInt8.toUInt32 <<< 24).toBitVec).getLsbD k = _ from b3]
  by_cases h8 : k < 8
  · simp [h8, show ¬ 8 ≤ k by omega, show ¬ 16 ≤ k by omega, show ¬ 24 ≤ k by omega]
  · by_cases h16 : k < 16
    · simp [h8, h16, show 8 ≤ k by omega, show ¬ 16 ≤ k by omega, show ¬ 24 ≤ k by omega]
    · by_cases h24 : k < 24
      · simp [h8, h16, h24, show 16 ≤ k by omega, show ¬ 24 ≤ k by omega]
      · simp [h8, h16, h24, show 24 ≤ k by omega, show k < 8 * 3 + 8 by omega]

private theorem u64_byte_shift (v : UInt64) (m k : Nat) (hm : m < 8) (hk : k < 64) :
    (((v >>> (8 * m).toUInt64).toUInt8.toUInt64 <<< (8 * m).toUInt64).toBitVec).getLsbD k =
      (decide (8 * m ≤ k ∧ k < 8 * m + 8) && v.toBitVec.getLsbD k) := by
  have hm_sh : ((8 * m).toUInt64.toBitVec % 64).toNat = 8 * m := by
    rw [BitVec.toNat_umod]
    change ((8 * m) % 2 ^ 64) % 64 = 8 * m
    omega
  have eshl : ∀ u : UInt64, (u <<< (8 * m).toUInt64).toBitVec = u.toBitVec <<< (8 * m) := by
    intro u
    change u.toBitVec <<< ((8 * m).toUInt64.toBitVec % 64) = _
    rw [BitVec.shiftLeft_eq', hm_sh]
  have eshr : (v >>> (8 * m).toUInt64).toBitVec = v.toBitVec >>> (8 * m) := by
    change v.toBitVec >>> ((8 * m).toUInt64.toBitVec % 64) = _
    rw [BitVec.ushiftRight_eq', hm_sh]
  have e8 : ∀ u : UInt64, u.toUInt8.toUInt64.toBitVec = (u.toBitVec.setWidth 8).setWidth 64 := by
    intro u
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    change u.toBitVec.toNat % 2 ^ 8 = u.toBitVec.toNat % 2 ^ 8 % 2 ^ 64
    omega
  rw [eshl, e8, eshr, BitVec.getLsbD_shiftLeft]
  simp only [hk, decide_true, Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases hlo : k < 8 * m
  · simp [hlo, show ¬ 8 * m ≤ k by omega]
  · by_cases hhi : k < 8 * m + 8
    · simp [hlo, hhi, show 8 * m ≤ k by omega, show k - 8 * m < 64 by omega,
        show k - 8 * m < 8 by omega, show 8 * m + (k - 8 * m) = k by omega]
    · simp [hlo, hhi, show ¬ k - 8 * m < 8 by omega]

private theorem reassemble_u64 (v : UInt64) :
    Model.word64 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
      (v >>> 32).toUInt8 (v >>> 40).toUInt8 (v >>> 48).toUInt8 (v >>> 56).toUInt8 = v := by
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have b0 : (v.toUInt8.toUInt64.toBitVec).getLsbD k =
      (decide (0 ≤ k ∧ k < 8) && v.toBitVec.getLsbD k) := by
    simpa [show (8 * 0).toUInt64 = (0 : UInt64) from rfl] using u64_byte_shift v 0 k (by omega) hk
  have b1 := u64_byte_shift v 1 k (by omega) hk
  have b2 := u64_byte_shift v 2 k (by omega) hk
  have b3 := u64_byte_shift v 3 k (by omega) hk
  have b4 := u64_byte_shift v 4 k (by omega) hk
  have b5 := u64_byte_shift v 5 k (by omega) hk
  have b6 := u64_byte_shift v 6 k (by omega) hk
  have b7 := u64_byte_shift v 7 k (by omega) hk
  unfold Model.word64
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  rw [b0]
  rw [show (((v >>> 8).toUInt8.toUInt64 <<< 8).toBitVec).getLsbD k = _ from b1]
  rw [show (((v >>> 16).toUInt8.toUInt64 <<< 16).toBitVec).getLsbD k = _ from b2]
  rw [show (((v >>> 24).toUInt8.toUInt64 <<< 24).toBitVec).getLsbD k = _ from b3]
  rw [show (((v >>> 32).toUInt8.toUInt64 <<< 32).toBitVec).getLsbD k = _ from b4]
  rw [show (((v >>> 40).toUInt8.toUInt64 <<< 40).toBitVec).getLsbD k = _ from b5]
  rw [show (((v >>> 48).toUInt8.toUInt64 <<< 48).toBitVec).getLsbD k = _ from b6]
  rw [show (((v >>> 56).toUInt8.toUInt64 <<< 56).toBitVec).getLsbD k = _ from b7]
  rcases (by omega :
    k < 8 ∨ (8 ≤ k ∧ k < 16) ∨ (16 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 32) ∨
    (32 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 48) ∨ (48 ≤ k ∧ k < 56) ∨ (56 ≤ k ∧ k < 64)) with
    h | h | h | h | h | h | h | h
  · simp [show k < 8 by omega, show ¬ 8 ≤ k by omega, show ¬ 16 ≤ k by omega,
      show ¬ 24 ≤ k by omega, show ¬ 32 ≤ k by omega, show ¬ 40 ≤ k by omega,
      show ¬ 48 ≤ k by omega, show ¬ 56 ≤ k by omega]
  · simp [show ¬ k < 8 by omega, show 8 ≤ k ∧ k < 16 by omega, show ¬ 16 ≤ k by omega,
      show ¬ 24 ≤ k by omega, show ¬ 32 ≤ k by omega, show ¬ 40 ≤ k by omega,
      show ¬ 48 ≤ k by omega, show ¬ 56 ≤ k by omega]
  · simp [show ¬ k < 8 by omega, show ¬ k < 16 by omega, show 16 ≤ k ∧ k < 24 by omega,
      show ¬ 24 ≤ k by omega, show ¬ 32 ≤ k by omega, show ¬ 40 ≤ k by omega,
      show ¬ 48 ≤ k by omega, show ¬ 56 ≤ k by omega]
  · simp [show ¬ k < 8 by omega, show ¬ k < 16 by omega, show ¬ k < 24 by omega,
      show 24 ≤ k ∧ k < 32 by omega, show ¬ 32 ≤ k by omega, show ¬ 40 ≤ k by omega,
      show ¬ 48 ≤ k by omega, show ¬ 56 ≤ k by omega]
  · simp [show ¬ k < 8 by omega, show ¬ k < 16 by omega, show ¬ k < 24 by omega,
      show ¬ k < 32 by omega, show 32 ≤ k ∧ k < 40 by omega, show ¬ 40 ≤ k by omega,
      show ¬ 48 ≤ k by omega, show ¬ 56 ≤ k by omega]
  · simp [show ¬ k < 8 by omega, show ¬ k < 16 by omega, show ¬ k < 24 by omega,
      show ¬ k < 32 by omega, show ¬ k < 40 by omega, show 40 ≤ k ∧ k < 48 by omega,
      show ¬ 48 ≤ k by omega, show ¬ 56 ≤ k by omega]
  · simp [show ¬ k < 8 by omega, show ¬ k < 16 by omega, show ¬ k < 24 by omega,
      show ¬ k < 32 by omega, show ¬ k < 40 by omega, show ¬ k < 48 by omega,
      show 48 ≤ k ∧ k < 56 by omega, show ¬ 56 ≤ k by omega]
  · simp [show ¬ k < 8 by omega, show ¬ k < 16 by omega, show ¬ k < 24 by omega,
      show ¬ k < 32 by omega, show ¬ k < 40 by omega, show ¬ k < 48 by omega,
      show ¬ k < 56 by omega, show 56 ≤ k ∧ k < 64 by omega]

theorem readU32LE_writeSlot32_same (m : Mem) (addr : UInt64) (v : UInt32)
    (h : addr.toNat + 8 ≤ UInt64.size) :
    (m.writeSlot32 addr v).readU32LE addr = some v := by
  have ne (i j : UInt64)
      (hij : decide (i.toNat < 8 ∧ j.toNat < 8 ∧ i.toNat ≠ j.toNat) = true := by decide) :
      addr + i ≠ addr + j := by
    have hp := of_decide_eq_true hij
    exact addr_ne_add addr i j h hp.1 hp.2.1 hp.2.2
  have b0 : (m.writeSlot32 addr v).readU8 addr = some v.toUInt8 := by
    simp only [readU8, writeSlot32, putRWByte,
      show addr ≠ addr + 1 by simp,
      show addr ≠ addr + 2 by simp,
      show addr ≠ addr + 3 by simp, ↓reduceIte]
  have b1 : (m.writeSlot32 addr v).readU8 (addr + 1) = some (v >>> 8).toUInt8 := by
    simp only [readU8, writeSlot32, putRWByte, ne 1 2, ne 1 3, ↓reduceIte]
  have b2 : (m.writeSlot32 addr v).readU8 (addr + 2) = some (v >>> 16).toUInt8 := by
    simp only [readU8, writeSlot32, putRWByte, ne 2 3, ↓reduceIte]
  have b3 : (m.writeSlot32 addr v).readU8 (addr + 3) = some (v >>> 24).toUInt8 := by
    simp only [readU8, writeSlot32, putRWByte, ↓reduceIte]
  simp only [readU32LE, Option.bind_eq_bind, Option.bind, b0, b1, b2, b3, reassemble_u32]

theorem readU64LE_writeSlot64_same (m : Mem) (addr : UInt64) (v : UInt64)
    (h : addr.toNat + 8 ≤ UInt64.size) :
    (m.writeSlot64 addr v).readU64LE addr = some v := by
  have ne (i j : UInt64)
      (hij : decide (i.toNat < 8 ∧ j.toNat < 8 ∧ i.toNat ≠ j.toNat) = true := by decide) :
      addr + i ≠ addr + j := by
    have hp := of_decide_eq_true hij
    exact addr_ne_add addr i j h hp.1 hp.2.1 hp.2.2
  have b0 : (m.writeSlot64 addr v).readU8 addr = some v.toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte,
      show addr ≠ addr + 1 by simp,
      show addr ≠ addr + 2 by simp,
      show addr ≠ addr + 3 by simp,
      show addr ≠ addr + 4 by simp,
      show addr ≠ addr + 5 by simp,
      show addr ≠ addr + 6 by simp,
      show addr ≠ addr + 7 by simp, ↓reduceIte]
  have b1 : (m.writeSlot64 addr v).readU8 (addr + 1) = some (v >>> 8).toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte,
      ne 1 2, ne 1 3, ne 1 4, ne 1 5, ne 1 6, ne 1 7, ↓reduceIte]
  have b2 : (m.writeSlot64 addr v).readU8 (addr + 2) = some (v >>> 16).toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte,
      ne 2 3, ne 2 4, ne 2 5, ne 2 6, ne 2 7, ↓reduceIte]
  have b3 : (m.writeSlot64 addr v).readU8 (addr + 3) = some (v >>> 24).toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte,
      ne 3 4, ne 3 5, ne 3 6, ne 3 7, ↓reduceIte]
  have b4 : (m.writeSlot64 addr v).readU8 (addr + 4) = some (v >>> 32).toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte, ne 4 5, ne 4 6, ne 4 7, ↓reduceIte]
  have b5 : (m.writeSlot64 addr v).readU8 (addr + 5) = some (v >>> 40).toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte, ne 5 6, ne 5 7, ↓reduceIte]
  have b6 : (m.writeSlot64 addr v).readU8 (addr + 6) = some (v >>> 48).toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte, ne 6 7, ↓reduceIte]
  have b7 : (m.writeSlot64 addr v).readU8 (addr + 7) = some (v >>> 56).toUInt8 := by
    simp only [readU8, writeSlot64, putRWByte, ↓reduceIte]
  simp only [readU64LE, Option.bind_eq_bind, Option.bind, b0, b1, b2, b3, b4, b5, b6, b7,
    reassemble_u64]

theorem writeSlot32_outside (m : Mem) (waddr a : UInt64) (v : UInt32)
    (hw : waddr.toNat + 4 ≤ UInt64.size)
    (hout : a.toNat < waddr.toNat ∨ waddr.toNat + 4 ≤ a.toNat) :
    (m.writeSlot32 waddr v) a = m a := by
  have ne (d : UInt64) (hd : decide (d.toNat < 4) = true := by decide) : a ≠ waddr + d := by
    intro heq; subst heq
    have hd' := of_decide_eq_true hd
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (waddr + d).toNat = waddr.toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [writeSlot32, putRWByte,
    show a ≠ waddr by simpa using ne 0,
    ne 1, ne 2, ne 3, ↓reduceIte]

theorem writeSlot64_outside (m : Mem) (waddr a : UInt64) (v : UInt64)
    (hw : waddr.toNat + 8 ≤ UInt64.size)
    (hout : a.toNat < waddr.toNat ∨ waddr.toNat + 8 ≤ a.toNat) :
    (m.writeSlot64 waddr v) a = m a := by
  have ne (d : UInt64) (hd : decide (d.toNat < 8) = true := by decide) : a ≠ waddr + d := by
    intro heq; subst heq
    have hd' := of_decide_eq_true hd
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (waddr + d).toNat = waddr.toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [writeSlot64, putRWByte,
    show a ≠ waddr by simpa using ne 0,
    ne 1, ne 2, ne 3, ne 4, ne 5, ne 6, ne 7, ↓reduceIte]

theorem readU32LE_writeSlot64_disjoint (m : Mem) (waddr raddr : UInt64) (v : UInt64)
    (hw : waddr.toNat + 8 ≤ UInt64.size) (hr : raddr.toNat + 4 ≤ UInt64.size)
    (hdisj : raddr.toNat + 4 ≤ waddr.toNat ∨ waddr.toNat + 8 ≤ raddr.toNat) :
    (m.writeSlot64 waddr v).readU32LE raddr = m.readU32LE raddr := by
  have eqd (d : UInt64) (hd : decide (d.toNat < 4) = true := by decide) :
      (m.writeSlot64 waddr v).readU8 (raddr + d) = m.readU8 (raddr + d) := by
    have hd' := of_decide_eq_true hd
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (raddr + d).toNat = raddr.toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp [readU8, writeSlot64_outside m waddr (raddr + d) v hw (by omega)]
  have e0 : (m.writeSlot64 waddr v).readU8 raddr = m.readU8 raddr := by simpa using eqd 0
  simp only [readU32LE, e0, eqd 1, eqd 2, eqd 3]

theorem readU64LE_writeSlot64_disjoint (m : Mem) (waddr raddr : UInt64) (v : UInt64)
    (hw : waddr.toNat + 8 ≤ UInt64.size) (hr : raddr.toNat + 8 ≤ UInt64.size)
    (hdisj : raddr.toNat + 8 ≤ waddr.toNat ∨ waddr.toNat + 8 ≤ raddr.toNat) :
    (m.writeSlot64 waddr v).readU64LE raddr = m.readU64LE raddr := by
  have eqd (d : UInt64) (hd : decide (d.toNat < 8) = true := by decide) :
      (m.writeSlot64 waddr v).readU8 (raddr + d) = m.readU8 (raddr + d) := by
    have hd' := of_decide_eq_true hd
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (raddr + d).toNat = raddr.toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp [readU8, writeSlot64_outside m waddr (raddr + d) v hw (by omega)]
  have e0 : (m.writeSlot64 waddr v).readU8 raddr = m.readU8 raddr := by simpa using eqd 0
  simp only [readU64LE, e0, eqd 1, eqd 2, eqd 3, eqd 4, eqd 5, eqd 6, eqd 7]

theorem readU64LE_writeSlot32_disjoint (m : Mem) (waddr raddr : UInt64) (v : UInt32)
    (hw : waddr.toNat + 4 ≤ UInt64.size) (hr : raddr.toNat + 8 ≤ UInt64.size)
    (hdisj : raddr.toNat + 8 ≤ waddr.toNat ∨ waddr.toNat + 4 ≤ raddr.toNat) :
    (m.writeSlot32 waddr v).readU64LE raddr = m.readU64LE raddr := by
  have eqd (d : UInt64) (hd : decide (d.toNat < 8) = true := by decide) :
      (m.writeSlot32 waddr v).readU8 (raddr + d) = m.readU8 (raddr + d) := by
    have hd' := of_decide_eq_true hd
    have : UInt64.size = 2 ^ 64 := rfl
    have ht : (raddr + d).toNat = raddr.toNat + d.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp [readU8, writeSlot32_outside m waddr (raddr + d) v hw (by omega)]
  have e0 : (m.writeSlot32 waddr v).readU8 raddr = m.readU8 raddr := by simpa using eqd 0
  simp only [readU64LE, e0, eqd 1, eqd 2, eqd 3, eqd 4, eqd 5, eqd 6, eqd 7]

/-- `.ro` facts, `hasROBytes`, and `none` guard bytes are preserved under
`writeSlot32` and `writeSlot64` whenever those slot writes came from `isRWRange`! -/
theorem putRWByte_preserves_ro_of_rw {m : Mem} {waddr a : UInt64} {old wb b : UInt8}
    (hrw : m waddr = some (.rw, old)) (hro : m a = some (.ro, b)) :
    (m.putRWByte waddr wb) a = some (.ro, b) :=
  writeU8_preserves_ro (writeU8_eq_putRWByte hrw) hro

theorem putRWByte_preserves_none_of_rw {m : Mem} {waddr a : UInt64} {old wb : UInt8}
    (hrw : m waddr = some (.rw, old)) (hnone : m a = none) :
    (m.putRWByte waddr wb) a = none :=
  writeU8_preserves_none (writeU8_eq_putRWByte hrw) hnone

theorem writeSlot32_preserves_ro {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32)
    {a : UInt64} {b : UInt8} (hro : m a = some (.ro, b)) :
    (m.writeSlot32 (lo + off.toUInt64) v) a = some (.ro, b) := by
  have hb := hrw.1
  let base := lo + off.toUInt64
  have rwAt : ∀ (m1 : Mem) (h1 : m1.isRWRange lo len) (d : Nat) (_ : d < 4),
      ∃ old, m1 (base + d.toUInt64) = some (.rw, old) := by
    intro m1 h1 d hd
    have heq := uint64_add_nat_assoc lo off d (by omega)
    simpa [base, heq] using h1.2 (off + d) (by omega)
  obtain ⟨o0, ho0⟩ := rwAt m hrw 0 (by omega)
  let m1 := m.putRWByte base v.toUInt8
  have hrw1 := putRWByte_isRWRange hrw base v.toUInt8
  obtain ⟨o1, ho1⟩ := rwAt m1 hrw1 1 (by omega)
  let m2 := m1.putRWByte (base + 1) (v >>> 8).toUInt8
  have hrw2 := putRWByte_isRWRange hrw1 (base + 1) (v >>> 8).toUInt8
  obtain ⟨o2, ho2⟩ := rwAt m2 hrw2 2 (by omega)
  let m3 := m2.putRWByte (base + 2) (v >>> 16).toUInt8
  have hrw3 := putRWByte_isRWRange hrw2 (base + 2) (v >>> 16).toUInt8
  obtain ⟨o3, ho3⟩ := rwAt m3 hrw3 3 (by omega)
  have r0 : m1 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho0) hro
  have r1 : m2 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho1) r0
  have r2 : m3 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho2) r1
  exact putRWByte_preserves_ro_of_rw (by simpa using ho3) r2

theorem writeSlot64_preserves_ro {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64)
    {a : UInt64} {b : UInt8} (hro : m a = some (.ro, b)) :
    (m.writeSlot64 (lo + off.toUInt64) v) a = some (.ro, b) := by
  have hb := hrw.1
  let base := lo + off.toUInt64
  have rwAt : ∀ (m1 : Mem) (h1 : m1.isRWRange lo len) (d : Nat) (_ : d < 8),
      ∃ old, m1 (base + d.toUInt64) = some (.rw, old) := by
    intro m1 h1 d hd
    have heq := uint64_add_nat_assoc lo off d (by omega)
    simpa [base, heq] using h1.2 (off + d) (by omega)
  obtain ⟨o0, ho0⟩ := rwAt m hrw 0 (by omega)
  let m1 := m.putRWByte base v.toUInt8
  have hrw1 := putRWByte_isRWRange hrw base v.toUInt8
  obtain ⟨o1, ho1⟩ := rwAt m1 hrw1 1 (by omega)
  let m2 := m1.putRWByte (base + 1) (v >>> 8).toUInt8
  have hrw2 := putRWByte_isRWRange hrw1 (base + 1) (v >>> 8).toUInt8
  obtain ⟨o2, ho2⟩ := rwAt m2 hrw2 2 (by omega)
  let m3 := m2.putRWByte (base + 2) (v >>> 16).toUInt8
  have hrw3 := putRWByte_isRWRange hrw2 (base + 2) (v >>> 16).toUInt8
  obtain ⟨o3, ho3⟩ := rwAt m3 hrw3 3 (by omega)
  let m4 := m3.putRWByte (base + 3) (v >>> 24).toUInt8
  have hrw4 := putRWByte_isRWRange hrw3 (base + 3) (v >>> 24).toUInt8
  obtain ⟨o4, ho4⟩ := rwAt m4 hrw4 4 (by omega)
  let m5 := m4.putRWByte (base + 4) (v >>> 32).toUInt8
  have hrw5 := putRWByte_isRWRange hrw4 (base + 4) (v >>> 32).toUInt8
  obtain ⟨o5, ho5⟩ := rwAt m5 hrw5 5 (by omega)
  let m6 := m5.putRWByte (base + 5) (v >>> 40).toUInt8
  have hrw6 := putRWByte_isRWRange hrw5 (base + 5) (v >>> 40).toUInt8
  obtain ⟨o6, ho6⟩ := rwAt m6 hrw6 6 (by omega)
  let m7 := m6.putRWByte (base + 6) (v >>> 48).toUInt8
  have hrw7 := putRWByte_isRWRange hrw6 (base + 6) (v >>> 48).toUInt8
  obtain ⟨o7, ho7⟩ := rwAt m7 hrw7 7 (by omega)
  have r0 : m1 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho0) hro
  have r1 : m2 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho1) r0
  have r2 : m3 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho2) r1
  have r3 : m4 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho3) r2
  have r4 : m5 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho4) r3
  have r5 : m6 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho5) r4
  have r6 : m7 a = some (.ro, b) := putRWByte_preserves_ro_of_rw (by simpa using ho6) r5
  exact putRWByte_preserves_ro_of_rw (by simpa using ho7) r6

theorem writeSlot32_preserves_hasROBytes {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32)
    {base : UInt64} {bs : ByteArray} (hro : m.hasROBytes base bs) :
    (m.writeSlot32 (lo + off.toUInt64) v).hasROBytes base bs :=
  ⟨hro.1, fun k hk => writeSlot32_preserves_ro hrw off hoff v (hro.2 k hk)⟩

theorem writeSlot64_preserves_hasROBytes {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64)
    {base : UInt64} {bs : ByteArray} (hro : m.hasROBytes base bs) :
    (m.writeSlot64 (lo + off.toUInt64) v).hasROBytes base bs :=
  ⟨hro.1, fun k hk => writeSlot64_preserves_ro hrw off hoff v (hro.2 k hk)⟩

theorem writeSlot32_preserves_none {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32)
    {a : UInt64} (hnone : m a = none) :
    (m.writeSlot32 (lo + off.toUInt64) v) a = none := by
  have hb := hrw.1
  let base := lo + off.toUInt64
  have rwAt : ∀ (m1 : Mem) (h1 : m1.isRWRange lo len) (d : Nat) (_ : d < 4),
      ∃ old, m1 (base + d.toUInt64) = some (.rw, old) := by
    intro m1 h1 d hd
    have heq := uint64_add_nat_assoc lo off d (by omega)
    simpa [base, heq] using h1.2 (off + d) (by omega)
  obtain ⟨o0, ho0⟩ := rwAt m hrw 0 (by omega)
  let m1 := m.putRWByte base v.toUInt8
  have hrw1 := putRWByte_isRWRange hrw base v.toUInt8
  obtain ⟨o1, ho1⟩ := rwAt m1 hrw1 1 (by omega)
  let m2 := m1.putRWByte (base + 1) (v >>> 8).toUInt8
  have hrw2 := putRWByte_isRWRange hrw1 (base + 1) (v >>> 8).toUInt8
  obtain ⟨o2, ho2⟩ := rwAt m2 hrw2 2 (by omega)
  let m3 := m2.putRWByte (base + 2) (v >>> 16).toUInt8
  have hrw3 := putRWByte_isRWRange hrw2 (base + 2) (v >>> 16).toUInt8
  obtain ⟨o3, ho3⟩ := rwAt m3 hrw3 3 (by omega)
  have r0 : m1 a = none := putRWByte_preserves_none_of_rw (by simpa using ho0) hnone
  have r1 : m2 a = none := putRWByte_preserves_none_of_rw (by simpa using ho1) r0
  have r2 : m3 a = none := putRWByte_preserves_none_of_rw (by simpa using ho2) r1
  exact putRWByte_preserves_none_of_rw (by simpa using ho3) r2

theorem writeSlot64_preserves_none {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64)
    {a : UInt64} (hnone : m a = none) :
    (m.writeSlot64 (lo + off.toUInt64) v) a = none := by
  have hb := hrw.1
  let base := lo + off.toUInt64
  have rwAt : ∀ (m1 : Mem) (h1 : m1.isRWRange lo len) (d : Nat) (_ : d < 8),
      ∃ old, m1 (base + d.toUInt64) = some (.rw, old) := by
    intro m1 h1 d hd
    have heq := uint64_add_nat_assoc lo off d (by omega)
    simpa [base, heq] using h1.2 (off + d) (by omega)
  obtain ⟨o0, ho0⟩ := rwAt m hrw 0 (by omega)
  let m1 := m.putRWByte base v.toUInt8
  have hrw1 := putRWByte_isRWRange hrw base v.toUInt8
  obtain ⟨o1, ho1⟩ := rwAt m1 hrw1 1 (by omega)
  let m2 := m1.putRWByte (base + 1) (v >>> 8).toUInt8
  have hrw2 := putRWByte_isRWRange hrw1 (base + 1) (v >>> 8).toUInt8
  obtain ⟨o2, ho2⟩ := rwAt m2 hrw2 2 (by omega)
  let m3 := m2.putRWByte (base + 2) (v >>> 16).toUInt8
  have hrw3 := putRWByte_isRWRange hrw2 (base + 2) (v >>> 16).toUInt8
  obtain ⟨o3, ho3⟩ := rwAt m3 hrw3 3 (by omega)
  let m4 := m3.putRWByte (base + 3) (v >>> 24).toUInt8
  have hrw4 := putRWByte_isRWRange hrw3 (base + 3) (v >>> 24).toUInt8
  obtain ⟨o4, ho4⟩ := rwAt m4 hrw4 4 (by omega)
  let m5 := m4.putRWByte (base + 4) (v >>> 32).toUInt8
  have hrw5 := putRWByte_isRWRange hrw4 (base + 4) (v >>> 32).toUInt8
  obtain ⟨o5, ho5⟩ := rwAt m5 hrw5 5 (by omega)
  let m6 := m5.putRWByte (base + 5) (v >>> 40).toUInt8
  have hrw6 := putRWByte_isRWRange hrw5 (base + 5) (v >>> 40).toUInt8
  obtain ⟨o6, ho6⟩ := rwAt m6 hrw6 6 (by omega)
  let m7 := m6.putRWByte (base + 6) (v >>> 48).toUInt8
  have hrw7 := putRWByte_isRWRange hrw6 (base + 6) (v >>> 48).toUInt8
  obtain ⟨o7, ho7⟩ := rwAt m7 hrw7 7 (by omega)
  have r0 : m1 a = none := putRWByte_preserves_none_of_rw (by simpa using ho0) hnone
  have r1 : m2 a = none := putRWByte_preserves_none_of_rw (by simpa using ho1) r0
  have r2 : m3 a = none := putRWByte_preserves_none_of_rw (by simpa using ho2) r1
  have r3 : m4 a = none := putRWByte_preserves_none_of_rw (by simpa using ho3) r2
  have r4 : m5 a = none := putRWByte_preserves_none_of_rw (by simpa using ho4) r3
  have r5 : m6 a = none := putRWByte_preserves_none_of_rw (by simpa using ho5) r4
  have r6 : m7 a = none := putRWByte_preserves_none_of_rw (by simpa using ho6) r5
  exact putRWByte_preserves_none_of_rw (by simpa using ho7) r6

/-- Read-only 8-byte constant at `addr` (survives every `.rw` stack write!). -/
def hasROU64 (m : Mem) (addr val : UInt64) : Prop :=
  addr.toNat + 8 ≤ UInt64.size ∧
  ∀ d : Nat, d < 8 → m (addr + d.toUInt64) = some (.ro, (val >>> (8 * d).toUInt64).toUInt8)

/-- Read-only 4-byte constant at `addr` (survives every `.rw` stack write!). -/
def hasROU32 (m : Mem) (addr : UInt64) (val : UInt32) : Prop :=
  addr.toNat + 4 ≤ UInt64.size ∧
  ∀ d : Nat, d < 4 → m (addr + d.toUInt64) = some (.ro, (val >>> (8 * d).toUInt32).toUInt8)

theorem hasROU64_readU64LE {m : Mem} {addr val : UInt64} (h : m.hasROU64 addr val) :
    m.readU64LE addr = some val := by
  have b (d : Nat) (hd : d < 8) : m.readU8 (addr + d.toUInt64) =
      some (val >>> (8 * d).toUInt64).toUInt8 := by
    simp [readU8, h.2 d hd]
  have b0 : m.readU8 addr = some val.toUInt8 := by simpa using b 0 (by omega)
  have b1 : m.readU8 (addr + 1) = some (val >>> 8).toUInt8 := by simpa using b 1 (by omega)
  have b2 : m.readU8 (addr + 2) = some (val >>> 16).toUInt8 := by simpa using b 2 (by omega)
  have b3 : m.readU8 (addr + 3) = some (val >>> 24).toUInt8 := by simpa using b 3 (by omega)
  have b4 : m.readU8 (addr + 4) = some (val >>> 32).toUInt8 := by simpa using b 4 (by omega)
  have b5 : m.readU8 (addr + 5) = some (val >>> 40).toUInt8 := by simpa using b 5 (by omega)
  have b6 : m.readU8 (addr + 6) = some (val >>> 48).toUInt8 := by simpa using b 6 (by omega)
  have b7 : m.readU8 (addr + 7) = some (val >>> 56).toUInt8 := by simpa using b 7 (by omega)
  simp only [readU64LE, Option.bind_eq_bind, Option.bind, b0, b1, b2, b3, b4, b5, b6, b7,
    reassemble_u64]

theorem hasROU32_readU32LE {m : Mem} {addr : UInt64} {val : UInt32} (h : m.hasROU32 addr val) :
    m.readU32LE addr = some val := by
  have b (d : Nat) (hd : d < 4) : m.readU8 (addr + d.toUInt64) =
      some (val >>> (8 * d).toUInt32).toUInt8 := by
    simp [readU8, h.2 d hd]
  have b0 : m.readU8 addr = some val.toUInt8 := by simpa using b 0 (by omega)
  have b1 : m.readU8 (addr + 1) = some (val >>> 8).toUInt8 := by simpa using b 1 (by omega)
  have b2 : m.readU8 (addr + 2) = some (val >>> 16).toUInt8 := by simpa using b 2 (by omega)
  have b3 : m.readU8 (addr + 3) = some (val >>> 24).toUInt8 := by simpa using b 3 (by omega)
  simp only [readU32LE, Option.bind_eq_bind, Option.bind, b0, b1, b2, b3, reassemble_u32]

theorem writeSlot32_preserves_hasROU64 {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32)
    {addr val : UInt64} (h : m.hasROU64 addr val) :
    (m.writeSlot32 (lo + off.toUInt64) v).hasROU64 addr val :=
  ⟨h.1, fun d hd => writeSlot32_preserves_ro hrw off hoff v (h.2 d hd)⟩

theorem writeSlot64_preserves_hasROU64 {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64)
    {addr val : UInt64} (h : m.hasROU64 addr val) :
    (m.writeSlot64 (lo + off.toUInt64) v).hasROU64 addr val :=
  ⟨h.1, fun d hd => writeSlot64_preserves_ro hrw off hoff v (h.2 d hd)⟩

theorem writeSlot32_preserves_hasROU32 {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len) (v : UInt32)
    {addr : UInt64} {val : UInt32} (h : m.hasROU32 addr val) :
    (m.writeSlot32 (lo + off.toUInt64) v).hasROU32 addr val :=
  ⟨h.1, fun d hd => writeSlot32_preserves_ro hrw off hoff v (h.2 d hd)⟩

theorem writeSlot64_preserves_hasROU32 {m : Mem} {lo : UInt64} {len : Nat}
    (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len) (v : UInt64)
    {addr : UInt64} {val : UInt32} (h : m.hasROU32 addr val) :
    (m.writeSlot64 (lo + off.toUInt64) v).hasROU32 addr val :=
  ⟨h.1, fun d hd => writeSlot64_preserves_ro hrw off hoff v (h.2 d hd)⟩

end Mem

/-! ### Multi-step execution (`run`) and Mach-O GOT load pair lemmas -/

@[simp] theorem RegFile.get_set_same (r : RegFile) (rd : RegIdx) (hrd : rd.val ≠ 31) (v : UInt64) :
    (r.set rd v).get rd = v := by
  rcases rd with ⟨rv, hlt⟩
  change rv ≠ 31 at hrd
  rcases (by omega :
    rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 ∨ rv = 5 ∨ rv = 6 ∨ rv = 7 ∨
    rv = 8 ∨ rv = 9 ∨ rv = 10 ∨ rv = 11 ∨ rv = 12 ∨ rv = 13 ∨ rv = 14 ∨ rv = 15 ∨
    rv = 16 ∨ rv = 17 ∨ rv = 18 ∨ rv = 19 ∨ rv = 20 ∨ rv = 21 ∨ rv = 22 ∨ rv = 23 ∨
    rv = 24 ∨ rv = 25 ∨ rv = 26 ∨ rv = 27 ∨ rv = 28 ∨ rv = 29 ∨ rv = 30) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem RegFile.set_set_same (r : RegFile) (rd : RegIdx) (v1 v2 : UInt64) :
    (r.set rd v1).set rd v2 = r.set rd v2 := by
  rcases rd with ⟨rv, hlt⟩
  rcases (by omega :
    rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 ∨ rv = 5 ∨ rv = 6 ∨ rv = 7 ∨
    rv = 8 ∨ rv = 9 ∨ rv = 10 ∨ rv = 11 ∨ rv = 12 ∨ rv = 13 ∨ rv = 14 ∨ rv = 15 ∨
    rv = 16 ∨ rv = 17 ∨ rv = 18 ∨ rv = 19 ∨ rv = 20 ∨ rv = 21 ∨ rv = 22 ∨ rv = 23 ∨
    rv = 24 ∨ rv = 25 ∨ rv = 26 ∨ rv = 27 ∨ rv = 28 ∨ rv = 29 ∨ rv = 30 ∨ rv = 31) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem run_zero (code : UInt64 → Option UInt32) (s : ArmState) :
    run code 0 s = some s := rfl

theorem run_succ (code : UInt64 → Option UInt32) (n : Nat) (s : ArmState) :
    run code (n + 1) s = (step code s).bind (run code n) := rfl

theorem run_one (code : UInt64 → Option UInt32) (s : ArmState) :
    run code 1 s = step code s := by
  simp [run, Option.bind_eq_bind]

theorem run_add (code : UInt64 → Option UInt32) (m n : Nat) (s : ArmState) :
    run code (m + n) s = (run code m s).bind (run code n) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add, run_succ, run_succ]
    cases step code s with
    | none => rfl
    | some s' => exact ih s'

theorem step_of_decoded {code : UInt64 → Option UInt32} {s : ArmState}
    {w : UInt32} {ins : Instr}
    (hfetch : code s.pc = some w) (hdec : decode w = some ins) :
    step code s = execInstr s ins := by
  simp [step, hfetch, hdec]

/-- A 2-instruction Mach-O `ARM64_RELOC_GOT_LOAD_PAGE21` + `PAGEOFF12` pair at
`pairAddr` resolving `X[rd]` (`rd < 31`) to `symAddr`, supporting **both**:
1. Unrelaxed GOT indirection: `adrp rd, pageOff` + `ldr rd, [rd, #off]` where
   the `.ro` GOT slot holds `symAddr`, and
2. Apple `ld` static GOT relaxation: `adrp rd, pageOff` + `add rd, rd, #off`
   computing `symAddr` directly without a memory read. -/
def GotPairAt (code : UInt64 → Option UInt32) (m : Mem)
    (pairAddr symAddr : UInt64) (rd : RegIdx) : Prop :=
  rd.val ≠ 31 ∧
  ∃ w0 w1 : UInt32,
    code pairAddr = some w0 ∧
    code (pairAddr + 4) = some w1 ∧
    ∃ pageOff off : UInt64,
      decode w0 = some (.adrp rd pageOff) ∧
      ((decode w1 = some (.ldrUImm .x64 rd rd off) ∧
          m.hasROU64 (((pairAddr &&& 0xFFFFFFFFFFFFF000) + pageOff) + off) symAddr) ∨
       (decode w1 = some (.addSubImm true false false rd rd off) ∧
          ((pairAddr &&& 0xFFFFFFFFFFFFF000) + pageOff) + off = symAddr))

theorem GotPairAt.preserves_writeSlot64 {code : UInt64 → Option UInt32} {m : Mem}
    {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 8 ≤ len)
    (v : UInt64) {pairAddr symAddr : UInt64} {rd : RegIdx}
    (hg : GotPairAt code m pairAddr symAddr rd) :
    GotPairAt code (m.writeSlot64 (lo + off.toUInt64) v) pairAddr symAddr rd := by
  rcases hg with ⟨hrd, w0, w1, hc0, hc1, pOff, oOff, hd0, hcases⟩
  refine ⟨hrd, w0, w1, hc0, hc1, pOff, oOff, hd0, ?_⟩
  rcases hcases with ⟨hd1, hro⟩ | ⟨hd1, heq⟩
  · exact Or.inl ⟨hd1, Mem.writeSlot64_preserves_hasROU64 hrw off hoff v hro⟩
  · exact Or.inr ⟨hd1, heq⟩

theorem GotPairAt.preserves_writeSlot32 {code : UInt64 → Option UInt32} {m : Mem}
    {lo : UInt64} {len : Nat} (hrw : m.isRWRange lo len) (off : Nat) (hoff : off + 4 ≤ len)
    (v : UInt32) {pairAddr symAddr : UInt64} {rd : RegIdx}
    (hg : GotPairAt code m pairAddr symAddr rd) :
    GotPairAt code (m.writeSlot32 (lo + off.toUInt64) v) pairAddr symAddr rd := by
  rcases hg with ⟨hrd, w0, w1, hc0, hc1, pOff, oOff, hd0, hcases⟩
  refine ⟨hrd, w0, w1, hc0, hc1, pOff, oOff, hd0, ?_⟩
  rcases hcases with ⟨hd1, hro⟩ | ⟨hd1, heq⟩
  · exact Or.inl ⟨hd1, Mem.writeSlot32_preserves_hasROU64 hrw off hoff v hro⟩
  · exact Or.inr ⟨hd1, heq⟩

theorem run_gotPair {code : UInt64 → Option UInt32} {s : ArmState}
    {symAddr : UInt64} {rd : RegIdx}
    (hg : GotPairAt code s.mem s.pc symAddr rd) :
    run code 2 s = some { (s.setX rd symAddr) with pc := s.pc + 8 } := by
  rcases hg with ⟨hrd, w0, w1, hc0, hc1, pageOff, off, hd0, hcases⟩
  have hrd_beq : (rd.val == 31) = false := beq_false_of_ne hrd
  have step1 : step code s =
      some { (s.setX rd ((s.pc &&& 0xFFFFFFFFFFFFF000) + pageOff)) with pc := s.pc + 4 } := by
    rw [step_of_decoded hc0 hd0]
    rfl
  let s1 : ArmState := { (s.setX rd ((s.pc &&& 0xFFFFFFFFFFFFF000) + pageOff)) with pc := s.pc + 4 }
  have hmem : s1.mem = s.mem := rfl
  have hget : s1.getXSP rd = (s.pc &&& 0xFFFFFFFFFFFFF000) + pageOff := by
    simp [s1, ArmState.getXSP, hrd_beq, ArmState.setX, RegFile.get_set_same _ _ hrd]
  have hset2 : ∀ v, (s1.setX rd v).nextPC = { (s.setX rd v) with pc := s.pc + 8 } := by
    intro v
    have hpc : s.pc + 4 + 4 = s.pc + 8 := by
      rw [UInt64.add_assoc]; rfl
    simp [s1, ArmState.setX, ArmState.nextPC, hpc]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_add, run_one, step1]
  change run code 1 s1 = _
  rw [run_one]
  rcases hcases with ⟨hd1, hro⟩ | ⟨hd1, heq⟩
  · have hc1' : code s1.pc = some w1 := hc1
    rw [step_of_decoded hc1' hd1]
    simp only [execInstr, Option.bind_eq_bind, Option.bind, hget, hmem,
      Mem.hasROU64_readU64LE hro, hset2]
  · have hc1' : code s1.pc = some w1 := hc1
    rw [step_of_decoded hc1' hd1]
    simp only [execInstr, ↓reduceIte, Bool.false_eq_true, hget, heq, ArmState.setXSP,
      hrd_beq, hset2]

end SimdModels.Arm64
