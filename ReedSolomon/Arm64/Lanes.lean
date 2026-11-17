/-
Byte-lane view of the vector operations used by `leanrs_apply`
(`cxx/leanrs_apply_arm64.S`): what `AND`, `USHR #4`, `TBL`, `MOVI` and `EOR3`
do to each of the 16 bytes of a register, and from that what one
"multiply and accumulate" step of the routine computes.
-/
import MemcpyCrc32c.Arm64.CopyMem

namespace ReedSolomon.Arm64MC
open SimdModels SimdModels.Arm64
open Crc32c.Arm64MC.Copy (word64_byte vec w8)

/-! ### Lanes of a vector built from bytes -/

private theorem shr_byte (lo : UInt64) (n : Nat) (hn : n < 64) :
    (⟨(lo.toBitVec >>> n).setWidth 8⟩ : UInt8) = (lo >>> n.toUInt64).toUInt8 := by
  apply UInt8.eq_of_toBitVec_eq
  simp [Nat.toUInt64, Nat.mod_eq_of_lt hn]

theorem lane8_ofLanes8 (f : Fin 16 → UInt8) (k : Fin 16) :
    V128.lane8 (Model.ofLanes8 f) k = f k := by
  rw [Model.ofLanes8, V128.lane8_ofHalves]
  obtain ⟨k, hk⟩ := k
  dsimp only
  split
  · rename_i h
    rw [shr_byte _ _ (by omega)]
    exact word64_byte (fun i => f ⟨i % 16, Nat.mod_lt _ (by decide)⟩) k h |>.trans
      (by congr 1; exact Fin.ext (Nat.mod_eq_of_lt hk))
  · rename_i h
    rw [shr_byte _ _ (by omega)]
    exact word64_byte (fun i => f ⟨(i + 8) % 16, Nat.mod_lt _ (by decide)⟩) (k - 8) (by omega)
      |>.trans (by congr 1; exact Fin.ext (by simp; omega))

/-- A vector is determined by its sixteen byte lanes. -/
theorem lane8_ext {a b : V128} (h : ∀ k, V128.lane8 a k = V128.lane8 b k) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun x : UInt8 => x.toBitVec.getLsbD (i % 8)) (h ⟨i / 8, by omega⟩)
  simp only [V128.lane8, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at this
  have e : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  simpa [e, Nat.mod_lt i (show 0 < 8 by decide)] using this

theorem eq_ofLanes8 {a : V128} {f : Fin 16 → UInt8} (h : ∀ k, V128.lane8 a k = f k) :
    a = Model.ofLanes8 f :=
  lane8_ext fun k => by rw [h, lane8_ofLanes8]

theorem lane8_vandq (a b : V128) (k : Fin 16) :
    V128.lane8 (Model.vandq a b) k = V128.lane8 a k &&& V128.lane8 b k := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Model.vandq, V128.lane8, hi]

theorem lane8_veor3q (a b c : V128) (k : Fin 16) :
    V128.lane8 (veor3q a b c) k = V128.lane8 a k ^^^ V128.lane8 b k ^^^ V128.lane8 c k := by
  rw [veor3q, V128.lane8_veorq, V128.lane8_veorq]

theorem lane8_vshrq_4 (a : V128) (k : Fin 16) :
    V128.lane8 (Model.vshrq_n_u8 a 4) k = V128.lane8 a k >>> 4 := by
  rw [Model.vshrq_n_u8, lane8_ofLanes8]; rfl

theorem lane8_vdupq (c : UInt8) (k : Fin 16) : V128.lane8 (Model.vdupq_n_u8 c) k = c := by
  rw [Model.vdupq_n_u8, lane8_ofLanes8]

theorem lane8_vqtbl1q (t idx : V128) (k : Fin 16) :
    V128.lane8 (Model.vqtbl1q_u8 t idx) k =
      if h : (V128.lane8 idx k).toNat < 16 then V128.lane8 t ⟨(V128.lane8 idx k).toNat, h⟩
      else 0 := by
  rw [Model.vqtbl1q_u8, lane8_ofLanes8]

/-- Sixteen consecutive bytes of `b` as a register: lane `k` is `b (off + k)`. -/
theorem lane8_vec (b : Nat → UInt8) (off : Nat) (k : Fin 16) :
    V128.lane8 (vec b off) k = b (off + k.val) := by
  have : vec b off = Model.ofLanes8 fun i => b (off + i.val) := rfl
  rw [this, lane8_ofLanes8]

/-! ### One multiply-and-accumulate step

`acc ^= lo[x & 15] ^ hi[x >> 4]`, as the routine computes it: the low nibbles
`x & 15` and the high nibbles `x >> 4` index the two 16-byte tables. -/

/-- The value the routine leaves in an accumulator after one input:
`EOR3 acc, acc, TBL(lo, x AND 0x0f), TBL(hi, x USHR 4)`. -/
def mulStep (acc lo hi x : V128) : V128 :=
  veor3q acc (Model.vqtbl1q_u8 lo (Model.vandq x (Model.vdupq_n_u8 15)))
    (Model.vqtbl1q_u8 hi (Model.vshrq_n_u8 x 4))

private theorem and15_lt (x : UInt8) : (x &&& 15).toNat < 16 := by
  rw [UInt8.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem shr4_lt (x : UInt8) : (x >>> 4).toNat < 16 := by
  rw [UInt8.toNat_shiftRight]
  have := x.toNat_lt
  show x.toNat >>> 4 < 16
  rw [Nat.shiftRight_eq_div_pow]; omega

theorem lane8_mulStep (acc lo hi x : V128) (k : Fin 16) :
    V128.lane8 (mulStep acc lo hi x) k =
      V128.lane8 acc k ^^^
        V128.lane8 lo ⟨(V128.lane8 x k &&& 15).toNat, and15_lt _⟩ ^^^
        V128.lane8 hi ⟨(V128.lane8 x k >>> 4).toNat, shr4_lt _⟩ := by
  rw [mulStep, lane8_veor3q, lane8_vqtbl1q, lane8_vqtbl1q]
  simp only [lane8_vandq, lane8_vdupq, lane8_vshrq_4]
  simp only [and15_lt, shr4_lt, dite_true]

end ReedSolomon.Arm64MC
