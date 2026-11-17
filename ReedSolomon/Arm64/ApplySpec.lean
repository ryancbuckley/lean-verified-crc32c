/-
What `leanrs_apply` computes, in three steps:

1. `accV_eq_vec`: the accumulators of `ReedSolomon/Arm64/Apply.lean` hold, byte
   for byte, the XOR over the inputs of two table lookups (`lookupAcc`).
2. `lookupAcc_eq_dot`: if the table holds the split-nibble products of
   coefficients `cf j i` (`IsTable`), those lookups are field multiplications,
   so each output byte is the GF(2^8) dot product of a matrix row with the
   input bytes at that position.
3. `apply_mc_spec`: the machine-code theorem. `apply_mc_shards` specialises it:
   if the coefficients are the Lagrange coefficients of the points `xs` at the
   points `ys`, each output shard is the Reed–Solomon shard at `ys j` of the
   stripe whose shards at `xs` are the inputs (`ReedSolomon.shardAt`).
-/
import ReedSolomon.Arm64.Apply
import ReedSolomon.Field
import ReedSolomon.Spec

namespace ReedSolomon.Arm64MC
open SimdModels Crc32c.Arm64MC
open Crc32c.Arm64MC.Copy (vec)

/-! ### Step 1: accumulators as bytewise table lookups -/

/-- Byte `t` of an output row whose tables start at `t0`, after `i` inputs:
the XOR of `lo[x & 15] ^ hi[x >> 4]` over the inputs' bytes `x` at position `t`. -/
def lookupAcc (T : Nat → UInt8) (D : Nat → Nat → UInt8) (t0 t : Nat) : Nat → UInt8
  | 0 => 0
  | i + 1 => lookupAcc T D t0 t i ^^^ T (t0 + 32 * i + (D i t &&& 15).toNat) ^^^
      T (t0 + 32 * i + 16 + (D i t >>> 4).toNat)

theorem lane8_accV (T : Nat → UInt8) (D : Nat → Nat → UInt8) (t0 o : Nat) (l : Fin 16) (i : Nat) :
    V128.lane8 (accV T D t0 o i) l = lookupAcc T D t0 (o + l.val) i := by
  induction i with
  | zero => rw [accV, lane8_vdupq, lookupAcc]
  | succ i ih => rw [accV, lane8_mulStep, ih, lookupAcc, lane8_vec, lane8_vec, lane8_vec]

theorem accV_eq_vec (T : Nat → UInt8) (D : Nat → Nat → UInt8) (t0 o i : Nat) :
    accV T D t0 o i = vec (fun t => lookupAcc T D t0 t i) o :=
  lane8_ext fun l => by rw [lane8_accV, lane8_vec]

/-! ### Step 2: table lookups as field multiplication -/

/-- The table holds, for the coefficient `cf j i` of output row `j` and input
`i`, its products with every low nibble and with every high nibble. -/
def IsTable (T : Nat → UInt8) (k r : Nat) (cf : Nat → Nat → UInt8) : Prop :=
  ∀ j < r, ∀ i < k, ∀ v : UInt8, v.toNat < 16 →
    T (32 * k * j + 32 * i + v.toNat) = gfMul (cf j i) v ∧
    T (32 * k * j + 32 * i + 16 + v.toNat) = gfMul (cf j i) (v <<< 4)

private theorem forall_byte {p : UInt8 → Prop} (h : ∀ i : Fin 256, p (UInt8.ofFin i))
    (a : UInt8) : p a := h a.toFin

private theorem nibbles (x : UInt8) :
    (x &&& (15 : UInt8)).toNat < 16 ∧ (x >>> (4 : UInt8)).toNat < 16 ∧
      (x &&& (15 : UInt8)) ^^^ ((x >>> (4 : UInt8)) <<< (4 : UInt8)) = x :=
  forall_byte (p := fun x : UInt8 => (x &&& (15 : UInt8)).toNat < 16 ∧
    (x >>> (4 : UInt8)).toNat < 16 ∧
    (x &&& (15 : UInt8)) ^^^ ((x >>> (4 : UInt8)) <<< (4 : UInt8)) = x) (by decide +kernel) x

/-- The two lookups for a byte `x` XOR to `c * x`. -/
theorem lookup_mul {T : Nat → UInt8} {k r : Nat} {cf : Nat → Nat → UInt8} (hT : IsTable T k r cf)
    {j i : Nat} (hj : j < r) (hi : i < k) (x : UInt8) :
    T (32 * k * j + 32 * i + (x &&& 15).toNat) ^^^ T (32 * k * j + 32 * i + 16 + (x >>> 4).toNat)
      = gfMul (cf j i) x := by
  obtain ⟨h1, h2, h3⟩ := nibbles x
  rw [(hT j hj i hi _ h1).1, (hT j hj i hi _ h2).2]
  apply ofByte_injective
  rw [ofByte_xor, ofByte_gfMul, ofByte_gfMul, ofByte_gfMul, ← mul_add, ← ofByte_xor, h3]

/-- The GF(2^8) dot product of row `j` of the matrix with the input bytes at
position `t`, over the first `i` inputs. -/
def dot (cf : Nat → Nat → UInt8) (D : Nat → Nat → UInt8) (j t : Nat) : Nat → UInt8
  | 0 => 0
  | i + 1 => dot cf D j t i ^^^ gfMul (cf j i) (D i t)

theorem lookupAcc_eq_dot {T : Nat → UInt8} {k r : Nat} {cf : Nat → Nat → UInt8}
    (hT : IsTable T k r cf) (D : Nat → Nat → UInt8) {j : Nat} (hj : j < r) (t : Nat) :
    ∀ i ≤ k, lookupAcc T D (32 * k * j) t i = dot cf D j t i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [lookupAcc, dot, ih (by omega), UInt8.xor_assoc, lookup_mul hT hj (by omega)]

theorem ofByte_dot (cf : Nat → Nat → UInt8) (D : Nat → Nat → UInt8) (j t i : Nat) :
    ofByte (dot cf D j t i) = ∑ n ∈ Finset.range i, ofByte (cf j n) * ofByte (D n t) := by
  induction i with
  | zero => simp [dot, ofByte_zero]
  | succ i ih => rw [dot, ofByte_xor, ih, ofByte_gfMul, Finset.sum_range_succ]

/-! ### Step 3: the machine-code theorem -/

section
variable {code : UInt64 → Option UInt32} {base : UInt64}
  {tab inP outP : UInt64} {k r L : Nat} {T : Nat → UInt8}
  {src dst : Nat → UInt64} {D : Nat → Nat → UInt8}

/-- Machine-code specification of `leanrs_apply` (117 instructions).

From any state `s` at the routine's entry with `X0 = tab`, `X1 = in`,
`X2 = out`, `X3 = k ≥ 1`, `X4 = r ≥ 1`, `X5 = L ≥ 64`, where memory is laid out
as `Setup` says (table bytes `T`, `k` input pointers to shards holding `D i`,
`r` output pointers to writable shards that overlap nothing the routine reads
and not each other) and the table holds the split-nibble products of the
coefficients `cf` (`IsTable`), execution terminates at the return address with:
- byte `t` of output shard `j` equal to the GF(2^8) dot product
  `cf j 0 * D 0 t + … + cf j (k-1) * D (k-1) t` (`dot`), for every `j < r`, `t < L`;
- every byte outside the output shards unchanged, permissions included;
- `CalleeSaved s s'`: `SP`, `X19..X30` and `D8..D15` preserved (AAPCS64).

Since the model's `step` fails on a read of an unmapped byte or a write to a
non-writable one, termination also shows the routine stays inside the memory
`Setup` describes. -/
theorem apply_mc_spec {s : Arm64.ArmState} {cf : Nat → Nat → UInt8}
    (hc : ApplyLoaded code base) (hs : Setup s.mem tab inP outP k r L T src dst D)
    (hT : IsTable T k r cf) (hk : 0 < k) (hr : 0 < r) (hL : 64 ≤ L) (hL64 : L < 2 ^ 64)
    (hpc : s.pc = base) (hx0 : s.regs.x0 = tab) (hx1 : s.regs.x1 = inP)
    (hx2 : s.regs.x2 = outP) (hx3 : s.regs.x3 = k.toUInt64) (hx4 : s.regs.x4 = r.toUInt64)
    (hx5 : s.regs.x5 = L.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      (∀ j < r, ∀ t < L, s'.mem (dst j + t.toUInt64) = some (.rw, dot cf D j t k)) ∧
      (∀ a : UInt64, ¬ InOut dst r L a → s'.mem a = s.mem a) ∧
      CalleeSaved s s' := by
  obtain ⟨n, s', hrun, hpc', hg, hcs⟩ :=
    apply_mc_core (B := fun j t => lookupAcc T D (32 * k * j) t k) hc hs hk hr hL hL64
      (fun j _ o _ => accV_eq_vec T D (32 * k * j) o k) hpc hx0 hx1 hx2 hx3 hx4 hx5
  refine ⟨n, s', hrun, hpc', fun j hj t ht => ?_, hg.outside, hcs⟩
  rw [hg.inside j hj t ht, if_pos ht, lookupAcc_eq_dot hT D hj t k (Nat.le_refl _)]

/-- `leanrs_apply` computes Reed–Solomon shards: if the matrix entries are the
Lagrange coefficients of the points `xs` at the points `ys`, then byte `t` of
output shard `j` is the shard at `ys j` of the stripe whose shards at the
points `xs` are the input bytes at position `t`. With `xs` the data points and
`ys` the parity points this is encoding; with `xs` any `k` surviving points and
`ys` the lost ones it is reconstruction (`ReedSolomon.shardAt_reconstruct`). -/
theorem apply_mc_shards {s : Arm64.ArmState} {cf : Nat → Nat → UInt8}
    {xs : Fin k → GF256} {ys : Fin r → GF256}
    (hcf : ∀ (j : Fin r) (i : Fin k), ofByte (cf j i) = lagrangeCoeff xs i (ys j))
    (hc : ApplyLoaded code base) (hs : Setup s.mem tab inP outP k r L T src dst D)
    (hT : IsTable T k r cf) (hk : 0 < k) (hr : 0 < r) (hL : 64 ≤ L) (hL64 : L < 2 ^ 64)
    (hpc : s.pc = base) (hx0 : s.regs.x0 = tab) (hx1 : s.regs.x1 = inP)
    (hx2 : s.regs.x2 = outP) (hx3 : s.regs.x3 = k.toUInt64) (hx4 : s.regs.x4 = r.toUInt64)
    (hx5 : s.regs.x5 = L.toUInt64) :
    ∃ steps s', Arm64.run code steps s = some s' ∧
      s'.pc = s.regs.x30 ∧
      (∀ (j : Fin r), ∀ t < L, ∃ b, s'.mem (dst j + t.toUInt64) = some (.rw, b) ∧
        ofByte b = shardAt xs (fun i => ofByte (D i t)) (ys j)) ∧
      (∀ a : UInt64, ¬ InOut dst r L a → s'.mem a = s.mem a) ∧
      CalleeSaved s s' := by
  obtain ⟨n, s', hrun, hpc', hout, hrest, hcs⟩ :=
    apply_mc_spec hc hs hT hk hr hL hL64 hpc hx0 hx1 hx2 hx3 hx4 hx5
  refine ⟨n, s', hrun, hpc', fun j t ht => ⟨_, hout j j.isLt t ht, ?_⟩, hrest, hcs⟩
  rw [ofByte_dot, shardAt_eq_sum, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [hcf j i]

end

end ReedSolomon.Arm64MC
