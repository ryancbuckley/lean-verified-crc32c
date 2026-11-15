/-
End-to-end error-detection guarantees for CRC32C (`Spec.extend`, `Spec.crc32c`,
`extendCrc32c`, `computeCrc32c`, and `memcpyCrc32c`), connecting bit-level
buffer/digest corruptions directly to the algebraic and zero-polynomial
theorems in `MemcpyCrc32c.PolyAlgebra` and `MemcpyCrc32c.ZeroPolyMinimal`:

1. **Exact algebraic characterization (`dvd_codewordError_iff`):**
   For equal-length buffers `a` and `b` and any initial state `init`, a
   received pair `(b, c')` passes the CRC check `Spec.extend init b = c'` if
   and only if `G` divides the codeword error polynomial
   `(msgPoly a.data.toList + msgPoly b.data.toList) * X^32 + P (Spec.extend init a ^^^ c')`,
   whose number of nonzero terms equals the exact bit-level Hamming distance
   `byteArrayBitDist a b + crcBitDist (Spec.extend init a) c'`.

2. **Length-independent guarantees (any buffer size):**
   - Any **odd** number of bit flips across payload + CRC is always detected
     (`Spec.extend_detects_odd_errors`).
   - Any contiguous **32-bit burst** across payload + CRC (and in particular any
     corruption confined to a 4-byte window in the payload) is always detected
     (`Spec.extend_detects_burst32`, `Spec.extend_ne_of_burst4Bytes`).

3. **Hamming-distance guarantees (payload + 32-bit CRC), at Koopman's published
   lengths rounded down to whole bytes.** Only detection is proven here; that the
   limits cannot be raised follows informally from the zero polynomials in
   `MemcpyCrc32c.ZeroPoly`:
   - **HD = 4** (`1..3` bit flips): up to `8 * a.size + 32 ≤ 2^31 - 1`
     (`a.size ≤ 268,435,451` bytes, `2,147,483,615` data bits).
   - **HD = 6** (`1..5` bit flips): up to `8 * a.size + 32 ≤ 5275`
     (`a.size ≤ 655` bytes, `5,243` data bits — covering 512-byte sectors).
   - **HD = 8** (`1..7` bit flips): up to `8 * a.size + 32 ≤ 209`
     (`a.size ≤ 22` bytes, `177` data bits).
   - **HD = 10** (`1..9` bit flips): up to `8 * a.size + 32 ≤ 79`
     (`a.size ≤ 5` bytes, `47` data bits; `a.size ≤ 9` bytes payload-only).
-/
import MemcpyCrc32c.Dispatch
import MemcpyCrc32c.ZeroPolyMinimal

namespace Crc32c
open Polynomial

/-! ### Bit-level Hamming weight and Hamming distance -/

/-- Number of set bits (`1`-bits) in a `w`-bit vector. -/
def popcount {w : Nat} (v : BitVec w) : Nat :=
  (List.range w).countP fun i => v.getLsbD i

/-- Bit-level Hamming distance between two `w`-bit vectors: the number of bit
positions `0 ≤ i < w` at which `a` and `b` differ. -/
def bitDist {w : Nat} (a b : BitVec w) : Nat :=
  (List.range w).countP fun i => a.getLsbD i != b.getLsbD i

/-- Bit-level Hamming distance between two byte lists. -/
def bytesBitDist : List UInt8 → List UInt8 → Nat
  | [], [] => 0
  | a :: as, b :: bs => bitDist a.toBitVec b.toBitVec + bytesBitDist as bs
  | a :: as, [] => bitDist a.toBitVec 0 + bytesBitDist as []
  | [], b :: bs => bitDist 0 b.toBitVec + bytesBitDist [] bs

/-- Bit-level Hamming distance between two `ByteArray` buffers. -/
def byteArrayBitDist (a b : ByteArray) : Nat :=
  bytesBitDist a.data.toList b.data.toList

/-- Bit-level Hamming distance between two 32-bit CRC digests. -/
def crcBitDist (c₁ c₂ : UInt32) : Nat :=
  bitDist c₁.toBitVec c₂.toBitVec

private theorem toList_length_eq_size (a : ByteArray) : a.data.toList.length = a.size := by
  rw [Array.length_toList, ByteArray.size_data]

theorem bitDist_eq_popcount_xor {w : Nat} (a b : BitVec w) :
    bitDist a b = popcount (a ^^^ b) := by
  unfold bitDist popcount
  refine List.countP_congr fun i _ => ?_
  rw [BitVec.getLsbD_xor]

@[simp] theorem popcount_zero {w : Nat} : popcount (0 : BitVec w) = 0 := by
  simp [popcount]

@[simp] theorem bitDist_self {w : Nat} (a : BitVec w) : bitDist a a = 0 := by
  simp [bitDist]

@[simp] theorem crcBitDist_self (c : UInt32) : crcBitDist c c = 0 :=
  bitDist_self c.toBitVec

theorem bitDist_eq_zero_iff {w : Nat} {a b : BitVec w} : bitDist a b = 0 ↔ a = b := by
  unfold bitDist
  rw [List.countP_eq_zero]
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi' := h i (List.mem_range.mpr hi)
    cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp [ha, hb] at hi' ⊢
  · rintro rfl i _
    simp

theorem crcBitDist_eq_zero_iff {c₁ c₂ : UInt32} : crcBitDist c₁ c₂ = 0 ↔ c₁ = c₂ := by
  rw [crcBitDist, bitDist_eq_zero_iff, UInt32.toBitVec_inj]

theorem bytesBitDist_eq_zero_iff {as bs : List UInt8} (hlen : as.length = bs.length) :
    bytesBitDist as bs = 0 ↔ as = bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [bytesBitDist]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [bytesBitDist, Nat.add_eq_zero_iff, bitDist_eq_zero_iff, UInt8.toBitVec_inj,
        ih hlen', List.cons.injEq]

theorem byteArrayBitDist_eq_zero_iff {a b : ByteArray} (hlen : a.size = b.size) :
    byteArrayBitDist a b = 0 ↔ a = b := by
  have hlenL : a.data.toList.length = b.data.toList.length := by
    rw [toList_length_eq_size, toList_length_eq_size, hlen]
  rw [byteArrayBitDist, bytesBitDist_eq_zero_iff hlenL]
  constructor
  · intro h
    exact ByteArray.ext (Array.toList_inj.mp h)
  · rintro rfl; rfl

@[simp] theorem byteArrayBitDist_self (a : ByteArray) : byteArrayBitDist a a = 0 :=
  (byteArrayBitDist_eq_zero_iff rfl).mpr rfl

/-! ### Polynomial support cardinality equals bit-level Hamming weight -/

private theorem card_range_filter (n : Nat) (f : Nat → Bool) :
    ((Finset.range n).filter (fun i => f i)).card = (List.range n).countP f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.countP_append,
      List.countP_singleton, ← ih]
    by_cases h : f n = true
    · have hnot : n ∉ (Finset.range n).filter (fun i => f i) := by simp
      simp [h, Finset.card_insert_of_notMem hnot]
    · simp [h]

theorem card_support_polyR {w : Nat} (v : BitVec w) :
    (polyR v).support.card = popcount v := by
  have hsupp : (polyR v).support = (Finset.range w).filter (fun k => v.getLsbD (w - 1 - k)) := by
    ext k
    simp only [mem_support_iff, coeff_polyR, Finset.mem_filter, Finset.mem_range]
    by_cases hk : k < w
    · cases hv : v.getLsbD (w - 1 - k) <;> simp [hk]
    · simp [hk]
  have hbij : ((Finset.range w).filter (fun k => v.getLsbD (w - 1 - k))).card =
      ((Finset.range w).filter (fun i => v.getLsbD i)).card := by
    refine Finset.card_bij (fun k _ => w - 1 - k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
      omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨w - 1 - i, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show w - 1 - (w - 1 - i) = i by omega]
      exact hi.2
  rw [hsupp, hbij, card_range_filter]
  rfl

theorem card_support_P_xor (c₁ c₂ : UInt32) :
    (P (c₁ ^^^ c₂)).support.card = crcBitDist c₁ c₂ := by
  change (polyR (c₁.toBitVec ^^^ c₂.toBitVec)).support.card = bitDist c₁.toBitVec c₂.toBitVec
  rw [card_support_polyR, bitDist_eq_popcount_xor]

/-- Non-overlapping bit ranges add in support cardinality. -/
theorem card_support_mul_X_pow_add {p q : (ZMod 2)[X]} {m : Nat} (hp : p.degree < m) :
    (q * X ^ m + p).support.card = q.support.card + p.support.card := by
  have hp_zero : ∀ k, m ≤ k → p.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast hk))
  have hsupp : (q * X ^ m + p).support =
      q.support.map ⟨(· + m), add_left_injective m⟩ ∪ p.support := by
    ext k
    simp only [mem_support_iff, coeff_add, coeff_mul_X_pow', Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    by_cases hk : m ≤ k
    · simp only [hk, ↓reduceIte, hp_zero k hk, add_zero]
      constructor
      · intro hne
        exact Or.inl ⟨k - m, hne, Nat.sub_add_cancel hk⟩
      · rintro (⟨a, ha, rfl⟩ | hp_ne)
        · rwa [Nat.add_sub_cancel]
        · exact absurd rfl hp_ne
    · simp only [hk, ↓reduceIte, zero_add]
      constructor
      · exact Or.inr
      · rintro (⟨a, _, rfl⟩ | hp_ne)
        · omega
        · exact hp_ne
  have hdisj : Disjoint (q.support.map ⟨(· + m), add_left_injective m⟩) p.support := by
    rw [Finset.disjoint_left]
    rintro k hk hp_mem
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hk
    obtain ⟨a, _, rfl⟩ := hk
    exact (mem_support_iff.mp hp_mem) (hp_zero (a + m) (by omega))
  rw [hsupp, Finset.card_union_of_disjoint hdisj, Finset.card_map]

theorem degree_msgPoly_lt (bs : List UInt8) : (msgPoly bs).degree < ↑(8 * bs.length) := by
  induction bs with
  | nil => simp [msgPoly]
  | cons b bs ih =>
    rw [degree_lt_iff_coeff_zero] at ih ⊢
    intro k hk
    simp only [List.length_cons] at hk
    simp only [msgPoly, coeff_add, coeff_mul_X_pow']
    rw [ih k (by omega), add_zero]
    have hge : 8 * bs.length ≤ k := by omega
    simp only [hge, ↓reduceIte, coeff_polyR]
    simp; omega

theorem card_support_msgPoly_add {as bs : List UInt8} (hlen : as.length = bs.length) :
    (msgPoly as + msgPoly bs).support.card = bytesBitDist as bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [msgPoly, bytesBitDist]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hrew : msgPoly (a :: as) + msgPoly (b :: bs) =
          polyR (a.toBitVec ^^^ b.toBitVec) * X ^ (8 * as.length) + (msgPoly as + msgPoly bs) := by
        simp only [msgPoly, ← hlen', polyR_xor]
        ring
      have hdeg : (msgPoly as + msgPoly bs).degree < ↑(8 * as.length) :=
        lt_of_le_of_lt (degree_add_le _ _)
          (max_lt (degree_msgPoly_lt as) (hlen' ▸ degree_msgPoly_lt bs))
      rw [hrew, card_support_mul_X_pow_add hdeg, card_support_polyR, ← bitDist_eq_popcount_xor,
        ih hlen', bytesBitDist]

/-! ### Codeword error polynomial and exact CRC32C collision equivalence -/

/-- The polynomial representing the bit-level difference between transmitted
codeword `(a, c)` and received codeword `(b, c')`. -/
noncomputable def codewordError (a b : ByteArray) (c c' : UInt32) : (ZMod 2)[X] :=
  (msgPoly a.data.toList + msgPoly b.data.toList) * X ^ 32 + P (c ^^^ c')

theorem card_support_codewordError {a b : ByteArray} (hlen : a.size = b.size) (c c' : UInt32) :
    (codewordError a b c c').support.card = byteArrayBitDist a b + crcBitDist c c' := by
  have hlenL : a.data.toList.length = b.data.toList.length := by
    rw [toList_length_eq_size, toList_length_eq_size, hlen]
  unfold codewordError
  rw [card_support_mul_X_pow_add (degree_P_lt _), card_support_msgPoly_add hlenL,
    card_support_P_xor]
  rfl

theorem degree_codewordError_lt {a b : ByteArray} (hlen : a.size = b.size) (c c' : UInt32) :
    (codewordError a b c c').degree < ↑(8 * a.size + 32) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  unfold codewordError
  rw [coeff_add, coeff_mul_X_pow']
  have hp0 : (P (c ^^^ c')).coeff k = 0 :=
    coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (degree_P_lt _) (by exact_mod_cast (show 32 ≤ k by omega)))
  have hk32 : 32 ≤ k := by omega
  simp only [hp0, add_zero, hk32, ↓reduceIte, coeff_add]
  have ha0 : (msgPoly a.data.toList).coeff (k - 32) = 0 := by
    have := (degree_lt_iff_coeff_zero _ _).mp (degree_msgPoly_lt a.data.toList) (k - 32)
    rw [toList_length_eq_size] at this
    exact this (by omega)
  have hb0 : (msgPoly b.data.toList).coeff (k - 32) = 0 := by
    have := (degree_lt_iff_coeff_zero _ _).mp (degree_msgPoly_lt b.data.toList) (k - 32)
    rw [toList_length_eq_size, ← hlen] at this
    exact this (by omega)
  rw [ha0, hb0, add_zero]

theorem natDegree_codewordError_lt {a b : ByteArray} (hlen : a.size = b.size) {c c' : UInt32}
    (hne : codewordError a b c c' ≠ 0) :
    (codewordError a b c c').natDegree < 8 * a.size + 32 :=
  (natDegree_lt_iff_degree_lt hne).mpr (degree_codewordError_lt hlen c c')

/-- **Fundamental CRC32C error-detection equivalence.** For equal-length buffers
`a` and `b` and any initial state `init`, `Spec.extend init b = c'` holds if and
only if `G` divides `codewordError a b (Spec.extend init a) c'`. -/
theorem dvd_codewordError_iff (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) :
    Spec.extend init b = c' ↔ G ∣ codewordError a b (Spec.extend init a) c' := by
  rw [← extend_eq_spec init a, ← extend_eq_spec init b, ← AdjoinRoot.mk_eq_zero, ← π]
  unfold codewordError
  rw [map_add, map_mul, map_pow, map_add, P_xor, map_add]
  have hsum : π (msgPoly a.data.toList) * π X ^ 32 + π (msgPoly b.data.toList) * π X ^ 32 =
      π (P (extend init a)) + π (P (extend init b)) := by
    rw [π_P_extend, π_P_extend, hlen]
    linear_combination
      -Q_add_self ((π (P init) + F) * π X ^ (8 * b.size)) - Q_add_self F
  have hrew : (π (msgPoly a.data.toList) + π (msgPoly b.data.toList)) * π X ^ 32 +
      (π (P (extend init a)) + π (P c')) = π (P (extend init b)) + π (P c') := by
    rw [add_mul, hsum]
    linear_combination Q_add_self (π (P (extend init a)))
  rw [hrew]
  constructor
  · rintro rfl; exact Q_add_self _
  · intro h0
    apply eq_of_π_P
    have := congrArg (· + π (P c')) h0
    simpa only [add_assoc, Q_add_self, add_zero, zero_add] using this

/-- **Payload-only CRC32C collision equivalence.** Two equal-length buffers have
the same `Spec.extend` digest if and only if `G` divides the difference of their
message polynomials. -/
theorem Spec.extend_eq_iff_dvd (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size) :
    Spec.extend init a = Spec.extend init b ↔
      G ∣ msgPoly a.data.toList + msgPoly b.data.toList := by
  have heq : Spec.extend init a = Spec.extend init b ↔
      Spec.extend init b = Spec.extend init a := eq_comm
  rw [heq, dvd_codewordError_iff init hlen (Spec.extend init a)]
  unfold codewordError
  rw [UInt32.xor_self, P_zero, add_zero, ← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.mk_eq_zero, ← π,
    map_mul, map_pow, (isUnit_π_X.pow 32).mul_left_eq_zero]

/-! ### Length-independent error-detection theorems -/

/-- **Odd-weight error detection (full codeword, arbitrary length).** Any odd
number of bit flips across payload + 32-bit CRC is always detected by
`Spec.extend`, regardless of buffer length or initial state. -/
theorem Spec.extend_detects_odd_errors (init : UInt32) {a b : ByteArray}
    (hlen : a.size = b.size) (c' : UInt32)
    (hodd : Odd (byteArrayBitDist a b + crcBitDist (Spec.extend init a) c')) :
    Spec.extend init b ≠ c' := by
  intro heq
  have hdvd := (dvd_codewordError_iff init hlen c').mp heq
  rw [← card_support_codewordError hlen (Spec.extend init a) c'] at hodd
  exact not_odd_card_support_of_dvd_G hdvd hodd

/-- **Odd-weight error detection (payload only, arbitrary length).** -/
theorem Spec.extend_payload_detects_odd_errors (init : UInt32) {a b : ByteArray}
    (hlen : a.size = b.size) (hodd : Odd (byteArrayBitDist a b)) :
    Spec.extend init a ≠ Spec.extend init b := by
  intro heq
  exact Spec.extend_detects_odd_errors init hlen (Spec.extend init a)
    (by simpa using hodd) heq.symm

/-- **32-bit burst-error detection (full codeword, arbitrary length).** Any
nonzero codeword corruption confined to a window of at most 32 consecutive bits
(`codewordError = X^m * B` with `B ≠ 0` and `B.degree < 32`) is always detected,
at any buffer size. -/
theorem Spec.extend_detects_burst32 (init : UInt32) {a b : ByteArray}
    (hlen : a.size = b.size) (c' : UInt32) {m : Nat} {B : (ZMod 2)[X]}
    (hB0 : B ≠ 0) (hBdeg : B.degree < 32)
    (hburst : codewordError a b (Spec.extend init a) c' = X ^ m * B) :
    Spec.extend init b ≠ c' := by
  intro heq
  have hdvd := (dvd_codewordError_iff init hlen c').mp heq
  rw [hburst, ← AdjoinRoot.mk_eq_zero, ← π, map_mul, map_pow,
    (isUnit_π_X.pow m).mul_right_eq_zero] at hdvd
  have hd0 : (0 : (ZMod 2)[X]).degree < 32 := by
    rw [degree_zero]; exact WithBot.bot_lt_coe 32
  have hB_eq : B = 0 := eq_of_π_eq hBdeg hd0 (by simpa using hdvd)
  exact hB0 hB_eq

/-- **4-byte payload burst detection (arbitrary length).** If two buffers differ
only within a contiguous slice of at most 4 bytes (`≤ 32` bits) at any offset,
their CRC32C digests are guaranteed to differ. -/
theorem Spec.extend_ne_of_burst4Bytes (init : UInt32) {a b : ByteArray}
    {pfx mid₁ mid₂ sfx : List UInt8}
    (ha : a.data.toList = pfx ++ mid₁ ++ sfx)
    (hb : b.data.toList = pfx ++ mid₂ ++ sfx)
    (hmid_len : mid₁.length = mid₂.length)
    (hmid_le : mid₁.length ≤ 4)
    (hmid_ne : mid₁ ≠ mid₂) :
    Spec.extend init a ≠ Spec.extend init b := by
  have hlen : a.size = b.size := by
    have h1 := congrArg List.length ha
    have h2 := congrArg List.length hb
    rw [toList_length_eq_size] at h1 h2
    simp_all
  intro heq
  have hdvd := (Spec.extend_eq_iff_dvd init hlen).mp heq
  have hdiff : msgPoly a.data.toList + msgPoly b.data.toList =
      X ^ (8 * sfx.length) * (msgPoly mid₁ + msgPoly mid₂) := by
    rw [ha, hb, msgPoly_append, msgPoly_append, msgPoly_append, msgPoly_append]
    have h1 := CharTwo.add_self_eq_zero (msgPoly pfx * X ^ (8 * mid₁.length) * X ^ (8 * sfx.length))
    have h2 := CharTwo.add_self_eq_zero (msgPoly sfx)
    rw [← hmid_len]
    linear_combination h1 + h2
  rw [hdiff, ← AdjoinRoot.mk_eq_zero, ← π, map_mul, map_pow,
    (isUnit_π_X.pow (8 * sfx.length)).mul_right_eq_zero] at hdvd
  have hdeg_lt : (msgPoly mid₁ + msgPoly mid₂).degree < 32 := by
    have hm1 := degree_msgPoly_lt mid₁
    have hm2 := hmid_len ▸ degree_msgPoly_lt mid₂
    have hle : (↑(8 * mid₁.length) : WithBot ℕ) ≤ 32 := by exact_mod_cast (show 8 * mid₁.length ≤ 32 by omega)
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt (lt_of_lt_of_le hm1 hle) (lt_of_lt_of_le hm2 hle))
  have hd0 : (0 : (ZMod 2)[X]).degree < 32 := by
    rw [degree_zero]; exact WithBot.bot_lt_coe 32
  have hzero : msgPoly mid₁ + msgPoly mid₂ = 0 :=
    eq_of_π_eq hdeg_lt hd0 (by simpa using hdvd)
  have hcard0 : bytesBitDist mid₁ mid₂ = 0 := by
    rw [← card_support_msgPoly_add hmid_len, hzero, support_zero, Finset.card_empty]
  exact hmid_ne ((bytesBitDist_eq_zero_iff hmid_len).mp hcard0)

/-! ### Exact Castagnoli / Koopman Hamming-distance bounds (full codeword) -/

private theorem codewordError_ne_zero_of_pos {a b : ByteArray} (hlen : a.size = b.size)
    {c c' : UInt32} (hpos : 0 < byteArrayBitDist a b + crcBitDist c c') :
    codewordError a b c c' ≠ 0 := by
  rw [← card_support_codewordError hlen c c'] at hpos
  exact support_nonempty.mp (Finset.card_pos.mp hpos)

/-- **Hamming Distance 4 (full codeword):** `Spec.extend` detects all 1-, 2-,
and 3-bit corruptions across payload + 32-bit CRC whenever
`8 * a.size + 32 ≤ 2^31 - 1` (`a.size ≤ 268,435,451` bytes, `2,147,483,615`
payload bits). -/
theorem Spec.extend_hd4 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 2 ^ 31 - 1)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (Spec.extend init a) c')
    (hd : byteArrayBitDist a b + crcBitDist (Spec.extend init a) c' < 4) :
    Spec.extend init b ≠ c' := by
  intro heq
  have hne := codewordError_ne_zero_of_pos hlen hpos
  have hdvd := (dvd_codewordError_iff init hlen c').mp heq
  have hcard : (codewordError a b (Spec.extend init a) c').support.card < 4 := by
    rwa [card_support_codewordError hlen]
  have hmin := zero2_minimal hne hdvd hcard
  have hlt := natDegree_codewordError_lt hlen hne
  omega

/-- **Hamming Distance 6 (full codeword):** `Spec.extend` detects all `1..5`-bit
corruptions across payload + 32-bit CRC whenever `8 * a.size + 32 ≤ 5275`
(`a.size ≤ 655` bytes, `5,243` payload bits — covering 512-byte storage sectors). -/
theorem Spec.extend_hd6 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 5275)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (Spec.extend init a) c')
    (hd : byteArrayBitDist a b + crcBitDist (Spec.extend init a) c' < 6) :
    Spec.extend init b ≠ c' := by
  intro heq
  have hne := codewordError_ne_zero_of_pos hlen hpos
  have hdvd := (dvd_codewordError_iff init hlen c').mp heq
  have hcard : (codewordError a b (Spec.extend init a) c').support.card < 6 := by
    rwa [card_support_codewordError hlen]
  have hmin := zero4_5275_minimal hne hdvd hcard
  have hlt := natDegree_codewordError_lt hlen hne
  omega

/-- **Hamming Distance 8 (full codeword):** `Spec.extend` detects all `1..7`-bit
corruptions across payload + 32-bit CRC whenever `8 * a.size + 32 ≤ 209`
(`a.size ≤ 22` bytes, `177` payload bits). -/
theorem Spec.extend_hd8 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 209)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (Spec.extend init a) c')
    (hd : byteArrayBitDist a b + crcBitDist (Spec.extend init a) c' < 8) :
    Spec.extend init b ≠ c' := by
  intro heq
  have hne := codewordError_ne_zero_of_pos hlen hpos
  have hdvd := (dvd_codewordError_iff init hlen c').mp heq
  have hcard : (codewordError a b (Spec.extend init a) c').support.card < 8 := by
    rwa [card_support_codewordError hlen]
  have hmin := zero6_209_minimal hne hdvd hcard
  have hlt := natDegree_codewordError_lt hlen hne
  omega

/-- **Hamming Distance 10 (full codeword):** `Spec.extend` detects all `1..9`-bit
corruptions across payload + 32-bit CRC whenever `8 * a.size + 32 ≤ 79`
(`a.size ≤ 5` bytes, `47` payload bits). -/
theorem Spec.extend_hd10 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 79)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (Spec.extend init a) c')
    (hd : byteArrayBitDist a b + crcBitDist (Spec.extend init a) c' < 10) :
    Spec.extend init b ≠ c' := by
  intro heq
  have hne := codewordError_ne_zero_of_pos hlen hpos
  have hdvd := (dvd_codewordError_iff init hlen c').mp heq
  have hcard : (codewordError a b (Spec.extend init a) c').support.card < 10 := by
    rwa [card_support_codewordError hlen]
  have hmin := zero8_79_minimal hne hdvd hcard
  have hlt := natDegree_codewordError_lt hlen hne
  omega

/-! ### Payload-only collision bounds (`8 * a.size ≤ D`, gaining 32 bits) -/

private theorem payloadError_ne_zero_and_lt {a b : ByteArray} (hlen : a.size = b.size)
    (hab : a ≠ b) :
    msgPoly a.data.toList + msgPoly b.data.toList ≠ 0 ∧
      (msgPoly a.data.toList + msgPoly b.data.toList).natDegree < 8 * a.size := by
  have hlenL : a.data.toList.length = b.data.toList.length := by
    rw [toList_length_eq_size, toList_length_eq_size, hlen]
  have hpos : 0 < byteArrayBitDist a b :=
    Nat.pos_of_ne_zero fun h0 => hab ((byteArrayBitDist_eq_zero_iff hlen).mp h0)
  rw [byteArrayBitDist, ← card_support_msgPoly_add hlenL] at hpos
  have hne : msgPoly a.data.toList + msgPoly b.data.toList ≠ 0 :=
    support_nonempty.mp (Finset.card_pos.mp hpos)
  have hdeg : (msgPoly a.data.toList + msgPoly b.data.toList).degree < ↑(8 * a.size) := by
    have ha := degree_msgPoly_lt a.data.toList
    have hb := degree_msgPoly_lt b.data.toList
    rw [toList_length_eq_size] at ha
    rw [toList_length_eq_size, ← hlen] at hb
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt ha hb)
  exact ⟨hne, (natDegree_lt_iff_degree_lt hne).mpr hdeg⟩

theorem Spec.extend_payload_hd4 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (hab : a ≠ b) (hsize : 8 * a.size ≤ 2 ^ 31 - 1) (hd : byteArrayBitDist a b < 4) :
    Spec.extend init a ≠ Spec.extend init b := by
  intro heq
  obtain ⟨hne, hlt⟩ := payloadError_ne_zero_and_lt hlen hab
  have hdvd := (Spec.extend_eq_iff_dvd init hlen).mp heq
  have hlenL : a.data.toList.length = b.data.toList.length := by
    rw [toList_length_eq_size, toList_length_eq_size, hlen]
  have hmin := zero2_minimal hne hdvd (by rwa [card_support_msgPoly_add hlenL])
  omega

theorem Spec.extend_payload_hd6 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (hab : a ≠ b) (hsize : 8 * a.size ≤ 5275) (hd : byteArrayBitDist a b < 6) :
    Spec.extend init a ≠ Spec.extend init b := by
  intro heq
  obtain ⟨hne, hlt⟩ := payloadError_ne_zero_and_lt hlen hab
  have hdvd := (Spec.extend_eq_iff_dvd init hlen).mp heq
  have hlenL : a.data.toList.length = b.data.toList.length := by
    rw [toList_length_eq_size, toList_length_eq_size, hlen]
  have hmin := zero4_5275_minimal hne hdvd (by rwa [card_support_msgPoly_add hlenL])
  omega

theorem Spec.extend_payload_hd8 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (hab : a ≠ b) (hsize : 8 * a.size ≤ 209) (hd : byteArrayBitDist a b < 8) :
    Spec.extend init a ≠ Spec.extend init b := by
  intro heq
  obtain ⟨hne, hlt⟩ := payloadError_ne_zero_and_lt hlen hab
  have hdvd := (Spec.extend_eq_iff_dvd init hlen).mp heq
  have hlenL : a.data.toList.length = b.data.toList.length := by
    rw [toList_length_eq_size, toList_length_eq_size, hlen]
  have hmin := zero6_209_minimal hne hdvd (by rwa [card_support_msgPoly_add hlenL])
  omega

theorem Spec.extend_payload_hd10 (init : UInt32) {a b : ByteArray} (hlen : a.size = b.size)
    (hab : a ≠ b) (hsize : 8 * a.size ≤ 79) (hd : byteArrayBitDist a b < 10) :
    Spec.extend init a ≠ Spec.extend init b := by
  intro heq
  obtain ⟨hne, hlt⟩ := payloadError_ne_zero_and_lt hlen hab
  have hdvd := (Spec.extend_eq_iff_dvd init hlen).mp heq
  have hlenL : a.data.toList.length = b.data.toList.length := by
    rw [toList_length_eq_size, toList_length_eq_size, hlen]
  have hmin := zero8_79_minimal hne hdvd (by rwa [card_support_msgPoly_add hlenL])
  omega

/-! ### Compiled implementation entry-point corollaries (`computeCrc32c`, `memcpyCrc32c`) -/

theorem computeCrc32c_detects_odd_errors {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hodd : Odd (byteArrayBitDist a b + crcBitDist (computeCrc32c a) c')) :
    computeCrc32c b ≠ c' := by
  rw [computeCrc32c_eq_spec] at hodd ⊢
  exact Spec.extend_detects_odd_errors 0 hlen c' hodd

theorem computeCrc32c_hd4 {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 2 ^ 31 - 1)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (computeCrc32c a) c')
    (hd : byteArrayBitDist a b + crcBitDist (computeCrc32c a) c' < 4) :
    computeCrc32c b ≠ c' := by
  rw [computeCrc32c_eq_spec] at hpos hd ⊢
  exact Spec.extend_hd4 0 hlen c' hsize hpos hd

theorem computeCrc32c_hd6 {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 5275)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (computeCrc32c a) c')
    (hd : byteArrayBitDist a b + crcBitDist (computeCrc32c a) c' < 6) :
    computeCrc32c b ≠ c' := by
  rw [computeCrc32c_eq_spec] at hpos hd ⊢
  exact Spec.extend_hd6 0 hlen c' hsize hpos hd

theorem computeCrc32c_hd8 {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 209)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (computeCrc32c a) c')
    (hd : byteArrayBitDist a b + crcBitDist (computeCrc32c a) c' < 8) :
    computeCrc32c b ≠ c' := by
  rw [computeCrc32c_eq_spec] at hpos hd ⊢
  exact Spec.extend_hd8 0 hlen c' hsize hpos hd

theorem computeCrc32c_hd10 {a b : ByteArray} (hlen : a.size = b.size)
    (c' : UInt32) (hsize : 8 * a.size + 32 ≤ 79)
    (hpos : 0 < byteArrayBitDist a b + crcBitDist (computeCrc32c a) c')
    (hd : byteArrayBitDist a b + crcBitDist (computeCrc32c a) c' < 10) :
    computeCrc32c b ≠ c' := by
  rw [computeCrc32c_eq_spec] at hpos hd ⊢
  exact Spec.extend_hd10 0 hlen c' hsize hpos hd

private theorem extract_copySlice_eq (dst : ByteArray) (dOff : Nat) (src : ByteArray)
    (sOff n : Nat) (hs : sOff + n ≤ src.size) (hdst : dOff + n ≤ dst.size) :
    (src.copySlice sOff dst dOff n).extract dOff (dOff + n) = src.extract sOff (sOff + n) := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract]
  have hs' : sOff + n ≤ src.data.size := by rwa [ByteArray.size_data]
  have hdst' : dOff + n ≤ dst.data.size := by rwa [ByteArray.size_data]
  have hcsize : (src.copySlice sOff dst dOff n).data.size = dst.data.size := by
    rw [ByteArray.size_data, ByteArray.size_data]
    exact size_copySlice_of_le dst dOff src sOff n hs hdst
  apply Array.ext
  · simp [Array.size_extract, hcsize]; omega
  · intro i hi1 hi2
    rw [Array.size_extract] at hi2
    have hin : i < n := by omega
    rw [Array.getElem_extract, Array.getElem_extract]
    simp only [ByteArray.copySlice]
    have hs1 : (dst.data.extract 0 dOff).size = dOff := by simp [Array.size_extract]; omega
    have hs2 : (src.data.extract sOff (sOff + n)).size = n := by simp [Array.size_extract]; omega
    rw [Array.getElem_append_left (by simp [hs1, hs2]; omega)]
    rw [Array.getElem_append_right (by simp [hs1])]
    rw [Array.getElem_extract]
    congr 1
    omega

/-- End-to-end `memcpyCrc32c` sector integrity (`HD = 6`, up to 655 bytes):
if `memcpyCrc32c` copies `n` bytes (`8 * n + 32 ≤ 5275`) and a memory/transit
corruption flips `1..5` bits across the copied `n`-byte slice `corrupted` and
digest `c'`, `extendCrc32c init corrupted ≠ c'`. -/
theorem memcpyCrc32c_sector_hd6 (dst : ByteArray) (dOff : Nat) (src : ByteArray)
    (sOff n : Nat) (init : UInt32) (hs : sOff + n ≤ src.size) (hdst : dOff + n ≤ dst.size)
    (corrupted : ByteArray) (c' : UInt32)
    (hlen : corrupted.size = n) (hsize : 8 * n + 32 ≤ 5275)
    (hpos : 0 < byteArrayBitDist ((memcpyCrc32c dst dOff src sOff n init hs hdst).1.extract dOff (dOff + n)) corrupted +
      crcBitDist (memcpyCrc32c dst dOff src sOff n init hs hdst).2 c')
    (hd : byteArrayBitDist ((memcpyCrc32c dst dOff src sOff n init hs hdst).1.extract dOff (dOff + n)) corrupted +
      crcBitDist (memcpyCrc32c dst dOff src sOff n init hs hdst).2 c' < 6) :
    extendCrc32c init corrupted ≠ c' := by
  rw [memcpyCrc32c_spec] at hpos hd
  rw [extract_copySlice_eq dst dOff src sOff n hs hdst] at hpos hd
  have hsrc_size : (src.extract sOff (sOff + n)).size = n := by
    rw [← ByteArray.size_data, ByteArray.data_extract, Array.size_extract, ByteArray.size_data]
    omega
  have hsrc_len : (src.extract sOff (sOff + n)).size = corrupted.size := by
    rw [hsrc_size, hlen]
  rw [extendCrc32c_eq_spec]
  exact Spec.extend_hd6 init hsrc_len c' (by rw [hsrc_size]; exact hsize) hpos hd

end Crc32c
