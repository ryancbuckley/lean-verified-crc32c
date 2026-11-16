/-
Proof that the scratch-buffer portable kernel (`MemcpyCrc32c.Impl.PortableXor`)
computes `rawExtend`.
-/
import MemcpyCrc32c.Portable
import MemcpyCrc32c.PolyAlgebra
import MemcpyCrc32c.Impl.PortableXor

namespace Crc32c
open Polynomial SimdModels

/-! ### Bytes and words of a byte array, as total functions -/

/-- Byte `p` of `a`, or `0` past the end. -/
def bt (a : ByteArray) (p : Nat) : UInt8 := a.data.toList.getD p 0

/-- The little-endian 64-bit word at byte offset `p`. -/
def wdAt (a : ByteArray) (p : Nat) : UInt64 :=
  Model.word64 (bt a p) (bt a (p + 1)) (bt a (p + 2)) (bt a (p + 3))
    (bt a (p + 4)) (bt a (p + 5)) (bt a (p + 6)) (bt a (p + 7))

/-- The little-endian 64-bit word at word index `k` (bytes `[8k, 8k + 8)`). -/
def wd (a : ByteArray) (k : Nat) : UInt64 := wdAt a (8 * k)

theorem bt_eq_getElem (a : ByteArray) (p : Nat) (h : p < a.size) : bt a p = a[p] := by
  have hl : p < a.data.toList.length := by rw [Array.length_toList, ByteArray.size_data]; exact h
  simp only [bt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  rfl

theorem loadU64LE_eq_word64 (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) :
    loadU64LE a i hs h = wdAt a i.toNat := by
  have h1 : (i + 1).toNat = i.toNat + 1 := Model.usize_add_toNat i 1 (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := Model.usize_add_toNat i 2 (by omega)
  have h3 : (i + 3).toNat = i.toNat + 3 := Model.usize_add_toNat i 3 (by omega)
  have h4 : (i + 4).toNat = i.toNat + 4 := Model.usize_add_toNat i 4 (by omega)
  have h5 : (i + 5).toNat = i.toNat + 5 := Model.usize_add_toNat i 5 (by omega)
  have h6 : (i + 6).toNat = i.toNat + 6 := Model.usize_add_toNat i 6 (by omega)
  have h7 : (i + 7).toNat = i.toNat + 7 := Model.usize_add_toNat i 7 (by omega)
  unfold loadU64LE Model.loadU64LE wdAt
  simp only [uget_eq a i i.toNat rfl, uget_eq a (i + 1) _ h1, uget_eq a (i + 2) _ h2,
    uget_eq a (i + 3) _ h3, uget_eq a (i + 4) _ h4, uget_eq a (i + 5) _ h5,
    uget_eq a (i + 6) _ h6, uget_eq a (i + 7) _ h7,
    bt_eq_getElem a _ (show i.toNat < a.size by omega),
    bt_eq_getElem a _ (show i.toNat + 1 < a.size by omega),
    bt_eq_getElem a _ (show i.toNat + 2 < a.size by omega),
    bt_eq_getElem a _ (show i.toNat + 3 < a.size by omega),
    bt_eq_getElem a _ (show i.toNat + 4 < a.size by omega),
    bt_eq_getElem a _ (show i.toNat + 5 < a.size by omega),
    bt_eq_getElem a _ (show i.toNat + 6 < a.size by omega),
    bt_eq_getElem a _ (show i.toNat + 7 < a.size by omega)]

/-- A load at a word-aligned offset reads that word. -/
theorem loadU64LE_eq_wd (a : ByteArray) (i : USize) (hs : a.size < USize.size)
    (h : i.toNat + 8 ≤ a.size) (k : Nat) (hk : i.toNat = 8 * k) :
    loadU64LE a i hs h = wd a k := by
  rw [loadU64LE_eq_word64, hk]; rfl

/-! ### Bytes and words after a store -/

theorem getD_splice (l bs : List UInt8) (i p : Nat) (h : i + bs.length ≤ l.length) :
    (l.take i ++ bs ++ l.drop (i + bs.length)).getD p 0 =
      if i ≤ p ∧ p < i + bs.length then bs.getD (p - i) 0 else l.getD p 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_append,
    List.length_take, List.getElem?_take, List.getElem?_drop]
  have hmin : min i l.length = i := by omega
  rw [hmin]
  by_cases h1 : p < i
  · simp [h1, show p < i + bs.length by omega]
  · by_cases h2 : p < i + bs.length
    · simp [h1, h2, show i ≤ p by omega, show p - i < bs.length by omega]
    · have e : i + bs.length + (p - (i + bs.length)) = p := by omega
      simp [h2, e]

theorem bt_storeBytes (a : ByteArray) (i : Nat) (bs : List UInt8) (h : i + bs.length ≤ a.size)
    (p : Nat) :
    bt (Model.storeBytes a i bs) p =
      if i ≤ p ∧ p < i + bs.length then bs.getD (p - i) 0 else bt a p := by
  have hl : a.data.toList.length = a.size := by rw [Array.length_toList, ByteArray.size_data]
  simp only [bt, Model.storeBytes]
  exact getD_splice a.data.toList bs i p (by omega)

theorem ifp {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ifn {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem wd_storeU64LE (buf : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + 8 ≤ buf.size)
    (k : Nat) (hk : i.toNat = 8 * k) (k' : Nat) :
    wd (storeU64LE buf i v h) k' = if k' = k then v else wd buf k' := by
  have hb (p : Nat) := bt_storeBytes buf (8 * k) (Model.leBytes v)
    (by rw [Model.length_leBytes, ← hk]; exact h) p
  simp only [Model.length_leBytes] at hb
  unfold storeU64LE Model.storeU64LE wd wdAt
  rw [hk]
  by_cases hkk : k' = k
  · subst hkk
    rw [ifp rfl]
    simp only [hb]
    simp [Model.leBytes]
    exact word64_bytes v
  · rw [ifn hkk]
    have ne (r : Nat) (hr : r < 8) : ¬ (8 * k ≤ 8 * k' + r ∧ 8 * k' + r < 8 * k + 8) := by omega
    have n0 := ne 0 (by omega)
    simp only [Nat.add_zero] at n0
    simp only [hb, n0, ne 1 (by omega), ne 2 (by omega), ne 3 (by omega), ne 4 (by omega),
      ne 5 (by omega), ne 6 (by omega), ne 7 (by omega), ↓reduceIte]

theorem getD_append' (l1 l2 : List UInt8) (n : Nat) :
    (l1 ++ l2).getD n 0 = if n < l1.length then l1.getD n 0 else l2.getD (n - l1.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

/-- Byte `r` of word `c` of a four-word splice. -/
theorem getD_four (B0 B1 B2 B3 : List UInt8) (h0 : B0.length = 8) (h1 : B1.length = 8)
    (h2 : B2.length = 8) (c r : Nat) (hc : c < 4) (hr : r < 8) :
    (B0 ++ B1 ++ B2 ++ B3).getD (8 * c + r) 0 =
      (if c = 0 then B0 else if c = 1 then B1 else if c = 2 then B2 else B3).getD r 0 := by
  have l01 : (B0 ++ B1).length = 16 := by rw [List.length_append, h0, h1]
  have l012 : (B0 ++ B1 ++ B2).length = 24 := by rw [List.length_append, l01, h2]
  rw [getD_append', l012]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · rw [ifp (by omega), getD_append', l01, ifp (by omega), getD_append', h0, ifp (by omega)]
    simp
  · rw [ifp (by omega), getD_append', l01, ifp (by omega), getD_append', h0, ifn (by omega)]
    simp
  · rw [ifp (by omega), getD_append', l01, ifn (by omega)]
    simp
  · rw [ifn (by omega)]
    simp

theorem word64_leBytes (v : UInt64) :
    Model.word64 ((Model.leBytes v).getD 0 0) ((Model.leBytes v).getD 1 0)
      ((Model.leBytes v).getD 2 0) ((Model.leBytes v).getD 3 0) ((Model.leBytes v).getD 4 0)
      ((Model.leBytes v).getD 5 0) ((Model.leBytes v).getD 6 0) ((Model.leBytes v).getD 7 0) = v :=
  word64_bytes v

theorem wd_storeU64x4LE (buf : ByteArray) (i : USize) (v0 v1 v2 v3 : UInt64)
    (h : i.toNat + 32 ≤ buf.size) (k : Nat) (hk : i.toNat = 8 * k) (k' : Nat) :
    wd (storeU64x4LE buf i v0 v1 v2 v3 h) k' =
      if k' = k then v0 else if k' = k + 1 then v1 else if k' = k + 2 then v2
      else if k' = k + 3 then v3 else wd buf k' := by
  have hlen : (Model.leBytes v0 ++ Model.leBytes v1 ++ Model.leBytes v2 ++
      Model.leBytes v3).length = 32 := rfl
  have hb (p : Nat) := bt_storeBytes buf (8 * k)
    (Model.leBytes v0 ++ Model.leBytes v1 ++ Model.leBytes v2 ++ Model.leBytes v3)
    (by rw [hlen, ← hk]; exact h) p
  rw [hlen] at hb
  unfold storeU64x4LE Model.storeU64x4LE wd wdAt
  rw [hk]
  by_cases hin : k ≤ k' ∧ k' < k + 4
  · obtain ⟨c, hc, rfl⟩ : ∃ c, c < 4 ∧ k' = k + c := ⟨k' - k, by omega, by omega⟩
    have hbyte (r : Nat) (hr : r < 8) :
        bt (Model.storeBytes buf (8 * k) (Model.leBytes v0 ++ Model.leBytes v1 ++
          Model.leBytes v2 ++ Model.leBytes v3)) (8 * (k + c) + r) =
        (if c = 0 then Model.leBytes v0 else if c = 1 then Model.leBytes v1
          else if c = 2 then Model.leBytes v2 else Model.leBytes v3).getD r 0 := by
      rw [hb, ifp (by omega), show 8 * (k + c) + r - 8 * k = 8 * c + r by omega]
      exact getD_four _ _ _ _ rfl rfl rfl c r hc hr
    have hb0 := hbyte 0 (by omega)
    simp only [Nat.add_zero] at hb0
    rw [hb0, hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega), hbyte 4 (by omega),
      hbyte 5 (by omega), hbyte 6 (by omega), hbyte 7 (by omega)]
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
    · simpa using word64_leBytes v0
    · simpa using word64_leBytes v1
    · simpa using word64_leBytes v2
    · simpa using word64_leBytes v3
  · rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]
    have ne (r : Nat) (hr : r < 8) :
        ¬ (8 * k ≤ 8 * k' + r ∧ 8 * k' + r < 8 * k + 32) := by omega
    have n0 := ne 0 (by omega)
    simp only [Nat.add_zero] at n0
    simp only [hb, n0, ne 1 (by omega), ne 2 (by omega), ne 3 (by omega), ne 4 (by omega),
      ne 5 (by omega), ne 6 (by omega), ne 7 (by omega), ↓reduceIte]

/-! ### The word-aligned zero polynomial `Z(X^64)` -/

set_option maxRecDepth 8192 in
/-- `G ∣ Z(X^64)`, by Frobenius invariance. (The recursion limit is for comparing
two definitionally equal instance paths on `X ^ 209`, not for any computation.) -/
theorem zero6_word64 (k : Nat) (hk : k = 2 ^ 6) :
    G ∣ expand (ZMod 2) k (X ^ 209 + X ^ 144 + X ^ 54 + X ^ 39 + X ^ 14 + 1) := by
  subst hk; exact (dvd_expand_two_pow_iff 6 _).mpr zero6_209

/-- `Z(X^k) ≡ 0 (mod G)` for `k = 64`. Stated with `k` so that no large literal
exponent is ever unfolded. -/
theorem π_zero6_word64 (k : Nat) (hk : k = 2 ^ 6) :
    π X ^ (k * 209) + π X ^ (k * 144) + π X ^ (k * 54) + π X ^ (k * 39) + π X ^ (k * 14) + 1
      = (0 : Q) := by
  have := AdjoinRoot.mk_eq_zero.mpr (zero6_word64 k hk)
  simp only [map_add, map_pow, map_one, expand_X, ← pow_mul] at this
  exact this

/-! ### Cancelling one word

`V` is the sequence of cancelled words so far, shifted by 212 (`V (j + 212)` is
the word cancelled at position `j`) and zero from the current position on.
`taps V i` is what the cancellations so far have re-injected into word `i`. -/

/-- The re-injections into word `i`: the words cancelled 65, 155, 170, 195 and 209 earlier. -/
def taps (V : Nat → UInt64) (i : Nat) : UInt64 :=
  V (i + 147) ^^^ V (i + 57) ^^^ V (i + 42) ^^^ V (i + 17) ^^^ V (i + 3)

/-- The residue of the message with words `[0, j)` cancelled: the remaining
words `[j, nw)`, each with its pending re-injections. -/
noncomputable def Ψ (inw : Nat → UInt64) (nw j : Nat) (V : Nat → UInt64) : Q :=
  ∑ i ∈ Finset.Ico j nw, R (inw i ^^^ taps V i) * π X ^ (64 * (nw - 1 - i))

theorem R_ite (c : Prop) [Decidable c] (v : UInt64) : R (if c then v else 0) = if c then R v else 0 := by
  split
  · rfl
  · exact R_zero

/-- Cancelling word `j` (possible while its last re-injection, 209 words on,
is still inside the input) does not change the residue. -/
theorem Ψ_step (inw : Nat → UInt64) (nw j : Nat) (V : Nat → UInt64) (hj : j + 209 < nw)
    (hV : V (j + 212) = 0) :
    Ψ inw nw (j + 1) (Function.update V (j + 212) (inw j ^^^ taps V j)) = Ψ inw nw j V := by
  set v := inw j ^^^ taps V j with hv
  have hV' (k : Nat) : Function.update V (j + 212) v k = V k ^^^ (if k = j + 212 then v else 0) := by
    by_cases hk : k = j + 212
    · subst hk; simp [hV]
    · simp [hk]
  have hterm (i : Nat) :
      R (inw i ^^^ taps (Function.update V (j + 212) v) i) * π X ^ (64 * (nw - 1 - i)) =
        R (inw i ^^^ taps V i) * π X ^ (64 * (nw - 1 - i)) +
        ((if i = j + 65 then R v * π X ^ (64 * (nw - 1 - i)) else 0) +
         (if i = j + 155 then R v * π X ^ (64 * (nw - 1 - i)) else 0) +
         (if i = j + 170 then R v * π X ^ (64 * (nw - 1 - i)) else 0) +
         (if i = j + 195 then R v * π X ^ (64 * (nw - 1 - i)) else 0) +
         (if i = j + 209 then R v * π X ^ (64 * (nw - 1 - i)) else 0)) := by
    have c1 : (i + 147 = j + 212) = (i = j + 65) := by apply propext; omega
    have c2 : (i + 57 = j + 212) = (i = j + 155) := by apply propext; omega
    have c3 : (i + 42 = j + 212) = (i = j + 170) := by apply propext; omega
    have c4 : (i + 17 = j + 212) = (i = j + 195) := by apply propext; omega
    have c5 : (i + 3 = j + 212) = (i = j + 209) := by apply propext; omega
    simp only [taps, hV', R_xor, R_ite, c1, c2, c3, c4, c5]
    split_ifs <;> ring
  have hsum (p : Nat) (hp : p ∈ Finset.Ico (j + 1) nw) :
      ∑ i ∈ Finset.Ico (j + 1) nw, (if i = p then R v * π X ^ (64 * (nw - 1 - i)) else 0) =
        R v * π X ^ (64 * (nw - 1 - p)) := by
    rw [Finset.sum_ite_eq' (Finset.Ico (j + 1) nw) p (fun i => R v * π X ^ (64 * (nw - 1 - i)))]
    exact ifp hp
  have m1 : j + 65 ∈ Finset.Ico (j + 1) nw := Finset.mem_Ico.mpr (by omega)
  have m2 : j + 155 ∈ Finset.Ico (j + 1) nw := Finset.mem_Ico.mpr (by omega)
  have m3 : j + 170 ∈ Finset.Ico (j + 1) nw := Finset.mem_Ico.mpr (by omega)
  have m4 : j + 195 ∈ Finset.Ico (j + 1) nw := Finset.mem_Ico.mpr (by omega)
  have m5 : j + 209 ∈ Finset.Ico (j + 1) nw := Finset.mem_Ico.mpr (by omega)
  obtain ⟨m, hm⟩ : ∃ m, nw = j + 210 + m := ⟨nw - (j + 210), by omega⟩
  have e0 : 64 * (nw - 1 - j) = 64 * m + 64 * 209 := by omega
  have e1 : 64 * (nw - 1 - (j + 65)) = 64 * m + 64 * 144 := by omega
  have e2 : 64 * (nw - 1 - (j + 155)) = 64 * m + 64 * 54 := by omega
  have e3 : 64 * (nw - 1 - (j + 170)) = 64 * m + 64 * 39 := by omega
  have e4 : 64 * (nw - 1 - (j + 195)) = 64 * m + 64 * 14 := by omega
  have e5 : 64 * (nw - 1 - (j + 209)) = 64 * m := by omega
  unfold Ψ
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hsum _ m1, hsum _ m2, hsum _ m3, hsum _ m4, hsum _ m5,
    Finset.sum_eq_sum_Ico_succ_bot (show j < nw by omega), ← hv, e0, e1, e2, e3, e4, e5]
  have hZ := π_zero6_word64 64 rfl
  have h2 := Q_add_self (R v * π X ^ (64 * m) *
    (π X ^ (64 * 144) + π X ^ (64 * 54) + π X ^ (64 * 39) + π X ^ (64 * 14) + 1))
  simp only [pow_add]
  linear_combination (-(R v * π X ^ (64 * m))) * hZ + h2

/-! ### The program's word computations, in terms of words -/

theorem xor_taps_assoc (x a b c d e : UInt64) :
    x ^^^ a ^^^ b ^^^ c ^^^ d ^^^ e = x ^^^ (a ^^^ b ^^^ c ^^^ d ^^^ e) := by
  simp only [UInt64.xor_assoc]

theorem xorTaps_eq (a : ByteArray) (hs : a.size < USize.size) (q : USize)
    (hq : q.toNat + 8 ≤ a.size) (buf : ByteArray) (hb : buf.size = 18080) (o : USize)
    (ho1 : 1672 ≤ o.toNat) (ho2 : o.toNat + 8 ≤ 18080) (m : Nat) (hm : o.toNat = 8 * m) :
    xorTaps a hs q hq buf hb o ho1 ho2 =
      wdAt a q.toNat ^^^ (wd buf (m - 65) ^^^ wd buf (m - 155) ^^^ wd buf (m - 170) ^^^
        wd buf (m - 195) ^^^ wd buf (m - 209)) := by
  have hbs : buf.size < USize.size := by have := usize_size_gt; omega
  have e1 : (o - 520).toNat = 8 * (m - 65) :=
    (usize_sub_toNat o 520 (by omega) (by omega)).trans (by omega)
  have e2 : (o - 1240).toNat = 8 * (m - 155) :=
    (usize_sub_toNat o 1240 (by omega) (by omega)).trans (by omega)
  have e3 : (o - 1360).toNat = 8 * (m - 170) :=
    (usize_sub_toNat o 1360 (by omega) (by omega)).trans (by omega)
  have e4 : (o - 1560).toNat = 8 * (m - 195) :=
    (usize_sub_toNat o 1560 (by omega) (by omega)).trans (by omega)
  have e5 : (o - 1672).toNat = 8 * (m - 209) :=
    (usize_sub_toNat o 1672 (by omega) (by omega)).trans (by omega)
  unfold xorTaps load64
  dsimp only
  rw [loadU64LE_eq_word64 a q hs hq,
    loadU64LE_eq_wd buf (o - 520) hbs _ _ e1, loadU64LE_eq_wd buf (o - 1240) hbs _ _ e2,
    loadU64LE_eq_wd buf (o - 1360) hbs _ _ e3, loadU64LE_eq_wd buf (o - 1560) hbs _ _ e4,
    loadU64LE_eq_wd buf (o - 1672) hbs _ _ e5]
  exact xor_taps_assoc _ _ _ _ _ _

/-- The scratch words `W` hold the cancelled words: the first `212 + c` of them
are `V` from index `base` on, and `V` is zero from there on. -/
def Rep (W : Nat → UInt64) (base c : Nat) (V : Nat → UInt64) : Prop :=
  (∀ i < 212 + c, W i = V (base + i)) ∧ ∀ k, base + 212 + c ≤ k → V k = 0

/-- One cancellation: the new word is the input word with its pending
re-injections, read from the scratch words, and is stored after them. -/
theorem rep_step (inw : Nat → UInt64) (nw base c : Nat) (W V : Nat → UInt64)
    (hrep : Rep W base c V) (hj : base + c + 209 < nw) :
    Rep (Function.update W (212 + c) (inw (base + c) ^^^
        (W (c + 147) ^^^ W (c + 57) ^^^ W (c + 42) ^^^ W (c + 17) ^^^ W (c + 3))))
      base (c + 1)
      (Function.update V (base + c + 212) (inw (base + c) ^^^ taps V (base + c))) ∧
    Ψ inw nw (base + c + 1)
      (Function.update V (base + c + 212) (inw (base + c) ^^^ taps V (base + c))) =
      Ψ inw nw (base + c) V := by
  have htap : W (c + 147) ^^^ W (c + 57) ^^^ W (c + 42) ^^^ W (c + 17) ^^^ W (c + 3) =
      taps V (base + c) := by
    unfold taps
    rw [hrep.1 _ (by omega), hrep.1 _ (by omega), hrep.1 _ (by omega), hrep.1 _ (by omega),
      hrep.1 _ (by omega)]
    simp only [Nat.add_assoc]
  rw [htap]
  refine ⟨⟨fun i hi => ?_, fun k hk => ?_⟩, Ψ_step inw nw (base + c) V hj (hrep.2 _ (by omega))⟩
  · by_cases h : i = 212 + c
    · subst h
      rw [Function.update_self, show base + (212 + c) = base + c + 212 by omega,
        Function.update_self]
    · rw [Function.update_of_ne h, Function.update_of_ne (by omega), hrep.1 i (by omega)]
  · rw [Function.update_of_ne (by omega)]
    exact hrep.2 k (by omega)

/-- The five taps of scratch word `212 + m`, read from the scratch words. -/
def wtaps (W : Nat → UInt64) (m : Nat) : UInt64 :=
  W (m + 147) ^^^ W (m + 57) ^^^ W (m + 42) ^^^ W (m + 17) ^^^ W (m + 3)

theorem rep_step' (inw : Nat → UInt64) (nw base c : Nat) (W V : Nat → UInt64)
    (hrep : Rep W base c V) (hj : base + c + 209 < nw) :
    ∃ V', Rep (Function.update W (212 + c) (inw (base + c) ^^^ wtaps W c)) base (c + 1) V' ∧
      Ψ inw nw (base + c + 1) V' = Ψ inw nw (base + c) V :=
  ⟨_, rep_step inw nw base c W V hrep hj⟩

theorem wtaps_update (W : Nat → UInt64) (p m : Nat) (v : UInt64) (h : m + 147 < p) :
    wtaps (Function.update W p v) m = wtaps W m := by
  unfold wtaps
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]

/-- Four cancellations whose taps are all read before any of the four words is stored. -/
theorem rep_step4 (inw : Nat → UInt64) (nw base c : Nat) (W V : Nat → UInt64)
    (hrep : Rep W base c V) (hj : base + c + 212 < nw) :
    ∃ V', Rep (fun i =>
        if i = 212 + c then inw (base + c) ^^^ wtaps W c
        else if i = 212 + c + 1 then inw (base + c + 1) ^^^ wtaps W (c + 1)
        else if i = 212 + c + 2 then inw (base + c + 2) ^^^ wtaps W (c + 2)
        else if i = 212 + c + 3 then inw (base + c + 3) ^^^ wtaps W (c + 3)
        else W i) base (c + 4) V' ∧
      Ψ inw nw (base + c + 4) V' = Ψ inw nw (base + c) V := by
  obtain ⟨V1, r1, p1⟩ := rep_step' inw nw base c W V hrep (by omega)
  obtain ⟨V2, r2, p2⟩ := rep_step' inw nw base (c + 1) _ V1 r1 (by omega)
  obtain ⟨V3, r3, p3⟩ := rep_step' inw nw base (c + 2) _ V2 r2 (by omega)
  obtain ⟨V4, r4, p4⟩ := rep_step' inw nw base (c + 3) _ V3 r3 (by omega)
  refine ⟨V4, ?_, p4.trans (p3.trans (p2.trans p1))⟩
  convert r4 using 1
  funext i
  rw [wtaps_update _ _ _ _ (by omega), wtaps_update _ _ _ _ (by omega),
    wtaps_update _ _ _ _ (by omega), wtaps_update _ _ _ _ (by omega),
    wtaps_update _ _ _ _ (by omega), wtaps_update _ _ _ _ (by omega)]
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | omega

/-! ### The cancellation loops -/

/-- Input word `i` of the range starting at byte `uo`. -/
def inwOf (a : ByteArray) (uo : Nat) (i : Nat) : UInt64 := wdAt a (uo + 8 * i)

theorem xorLoop1_spec (a : ByteArray) (hs : a.size < USize.size) (uo nw base : Nat) :
    ∀ (n : Nat) (buf : ByteArray) (q o oEnd : USize) (hb : buf.size = 18080)
      (ho : 1696 ≤ o.toNat) (hle : o.toNat ≤ oEnd.toNat)
      (hal : (oEnd.toNat - o.toNat) % 8 = 0) (hEnd : oEnd.toNat ≤ 18080)
      (hq : q.toNat + (oEnd.toNat - o.toNat) ≤ a.size) (c cEnd : Nat) (V : Nat → UInt64),
      oEnd.toNat - o.toNat = n → o.toNat = 8 * (212 + c) → oEnd.toNat = 8 * (212 + cEnd) →
      q.toNat = uo + 8 * (base + c) → Rep (wd buf) base c V → base + cEnd + 209 ≤ nw →
      ∃ V', Rep (wd (xorLoop1 a hs buf q o oEnd hb ho hle hal hEnd hq).1) base cEnd V' ∧
        Ψ (inwOf a uo) nw (base + cEnd) V' = Ψ (inwOf a uo) nw (base + c) V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro buf q o oEnd hb ho hle hal hEnd hq c cEnd V hn hoc hec hqc hrep hnw
    rw [xorLoop1]
    by_cases h : o < oEnd
    · have hlt : o.toNat < oEnd.toNat := USize.lt_iff_toNat_lt.mp h
      have hus := usize_size_gt
      have eo : (o + 8).toNat = o.toNat + 8 := usize_add_toNat o 8 (by omega)
      have eq : (q + 8).toNat = q.toNat + 8 := usize_add_toNat q 8 (by omega)
      simp only [h, ↓reduceDIte]
      have hv : xorTaps a hs q (by omega) buf hb o (by omega) (by omega) =
          inwOf a uo (base + c) ^^^ wtaps (wd buf) c := by
        rw [xorTaps_eq a hs q (by omega) buf hb o (by omega) (by omega) (212 + c) hoc, hqc,
          show 212 + c - 65 = c + 147 by omega, show 212 + c - 155 = c + 57 by omega,
          show 212 + c - 170 = c + 42 by omega, show 212 + c - 195 = c + 17 by omega,
          show 212 + c - 209 = c + 3 by omega]
        rfl
      obtain ⟨V1, r1, p1⟩ := rep_step' (inwOf a uo) nw base c (wd buf) V hrep (by omega)
      have hW : wd (storeU64LE buf o (xorTaps a hs q (by omega) buf hb o (by omega) (by omega))
          (by omega)) = Function.update (wd buf) (212 + c)
            (inwOf a uo (base + c) ^^^ wtaps (wd buf) c) := by
        funext i
        rw [wd_storeU64LE buf o _ _ (212 + c) hoc i, Function.update_apply, hv]
      rw [← hW] at r1
      obtain ⟨V', r', p'⟩ := ih (oEnd.toNat - (o + 8).toNat) (by omega) _ (q + 8) (o + 8) oEnd
        _ (by omega) (by omega) (by omega) hEnd (by omega) (c + 1) cEnd V1 rfl (by omega) hec
        (by omega) r1 hnw
      exact ⟨V', r', p'.trans p1⟩
    · have heq : c = cEnd := by
        have : ¬ o.toNat < oEnd.toNat := fun hh => h (USize.lt_iff_toNat_lt.mpr hh)
        omega
      subst heq
      simp only [h, ↓reduceDIte]
      exact ⟨V, hrep, rfl⟩

theorem xorTaps_inw (a : ByteArray) (hs : a.size < USize.size) (uo : Nat) (q : USize)
    (hq : q.toNat + 8 ≤ a.size) (buf : ByteArray) (hb : buf.size = 18080) (o : USize)
    (ho1 : 1672 ≤ o.toNat) (ho2 : o.toNat + 8 ≤ 18080) (base m : Nat)
    (hom : o.toNat = 8 * (212 + m)) (hqm : q.toNat = uo + 8 * (base + m)) :
    xorTaps a hs q hq buf hb o ho1 ho2 = inwOf a uo (base + m) ^^^ wtaps (wd buf) m := by
  rw [xorTaps_eq a hs q hq buf hb o ho1 ho2 (212 + m) hom, hqm,
    show 212 + m - 65 = m + 147 by omega, show 212 + m - 155 = m + 57 by omega,
    show 212 + m - 170 = m + 42 by omega, show 212 + m - 195 = m + 17 by omega,
    show 212 + m - 209 = m + 3 by omega]
  rfl

theorem xorLoop4_spec (a : ByteArray) (hs : a.size < USize.size) (uo nw base : Nat) :
    ∀ (n : Nat) (buf : ByteArray) (q o oEnd : USize) (hb : buf.size = 18080)
      (ho : 1696 ≤ o.toNat) (hle : o.toNat ≤ oEnd.toNat)
      (hal : (oEnd.toNat - o.toNat) % 8 = 0) (hEnd : oEnd.toNat ≤ 18080)
      (hq : q.toNat + (oEnd.toNat - o.toNat) ≤ a.size) (c cEnd : Nat) (V : Nat → UInt64),
      oEnd.toNat - o.toNat = n → o.toNat = 8 * (212 + c) → oEnd.toNat = 8 * (212 + cEnd) →
      q.toNat = uo + 8 * (base + c) → Rep (wd buf) base c V → base + cEnd + 209 ≤ nw →
      ∃ V', Rep (wd (xorLoop4 a hs buf q o oEnd hb ho hle hal hEnd hq).1) base cEnd V' ∧
        Ψ (inwOf a uo) nw (base + cEnd) V' = Ψ (inwOf a uo) nw (base + c) V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro buf q o oEnd hb ho hle hal hEnd hq c cEnd V hn hoc hec hqc hrep hnw
    have hd : (oEnd - o).toNat = oEnd.toNat - o.toNat :=
      USize.toNat_sub_of_le oEnd o (USize.le_iff_toNat_le.mpr hle)
    have e32 : (32 : USize).toNat = 32 := by simp
    rw [xorLoop4]
    by_cases h : 32 ≤ oEnd - o
    · have h32 : 32 ≤ oEnd.toNat - o.toNat := by
        have := USize.le_iff_toNat_le.mp h; omega
      have hus := usize_size_gt
      have eo8 : (o + 8).toNat = o.toNat + 8 := usize_add_toNat o 8 (by omega)
      have eo16 : (o + 16).toNat = o.toNat + 16 := usize_add_toNat o 16 (by omega)
      have eo24 : (o + 24).toNat = o.toNat + 24 := usize_add_toNat o 24 (by omega)
      have eo32 : (o + 32).toNat = o.toNat + 32 := usize_add_toNat o 32 (by omega)
      have eq8 : (q + 8).toNat = q.toNat + 8 := usize_add_toNat q 8 (by omega)
      have eq16 : (q + 16).toNat = q.toNat + 16 := usize_add_toNat q 16 (by omega)
      have eq24 : (q + 24).toNat = q.toNat + 24 := usize_add_toNat q 24 (by omega)
      have eq32 : (q + 32).toNat = q.toNat + 32 := usize_add_toNat q 32 (by omega)
      simp only [h, ↓reduceDIte]
      have hv0 := xorTaps_inw a hs uo q (by omega) buf hb o (by omega) (by omega) base c hoc hqc
      have hv1 := xorTaps_inw a hs uo (q + 8) (by omega) buf hb (o + 8) (by omega) (by omega)
        base (c + 1) (by omega) (by omega)
      have hv2 := xorTaps_inw a hs uo (q + 16) (by omega) buf hb (o + 16) (by omega) (by omega)
        base (c + 2) (by omega) (by omega)
      have hv3 := xorTaps_inw a hs uo (q + 24) (by omega) buf hb (o + 24) (by omega) (by omega)
        base (c + 3) (by omega) (by omega)
      obtain ⟨V4, r4, p4⟩ := rep_step4 (inwOf a uo) nw base c (wd buf) V hrep (by omega)
      have hW : wd (storeU64x4LE buf o
          (xorTaps a hs q (by omega) buf hb o (by omega) (by omega))
          (xorTaps a hs (q + 8) (by omega) buf hb (o + 8) (by omega) (by omega))
          (xorTaps a hs (q + 16) (by omega) buf hb (o + 16) (by omega) (by omega))
          (xorTaps a hs (q + 24) (by omega) buf hb (o + 24) (by omega) (by omega))
          (by omega)) = fun i =>
            if i = 212 + c then inwOf a uo (base + c) ^^^ wtaps (wd buf) c
            else if i = 212 + c + 1 then inwOf a uo (base + c + 1) ^^^ wtaps (wd buf) (c + 1)
            else if i = 212 + c + 2 then inwOf a uo (base + c + 2) ^^^ wtaps (wd buf) (c + 2)
            else if i = 212 + c + 3 then inwOf a uo (base + c + 3) ^^^ wtaps (wd buf) (c + 3)
            else wd buf i := by
        funext i
        rw [wd_storeU64x4LE buf o _ _ _ _ _ (212 + c) hoc i, hv0, hv1, hv2, hv3]
        simp only [Nat.add_assoc]
      rw [← hW] at r4
      obtain ⟨V', r', p'⟩ := ih (oEnd.toNat - (o + 32).toNat) (by omega) _ (q + 32) (o + 32) oEnd
        _ (by omega) (by omega) (by omega) hEnd (by omega) (c + 4) cEnd V4 rfl (by omega) hec
        (by omega) r4 hnw
      exact ⟨V', r', p'.trans p4⟩
    · simp only [h, ↓reduceDIte]
      exact xorLoop1_spec a hs uo nw base _ buf q o oEnd hb ho hle hal hEnd hq c cEnd V rfl
        hoc hec hqc hrep hnw

/-! ### Moving the history to the front -/

theorem moveHist_spec (sh : USize) (k : Nat) (hk : sh.toNat = 8 * k) (W0 : Nat → UInt64) :
    ∀ (n : Nat) (buf : ByteArray) (t : USize) (hb : buf.size = 18080) (hsh : sh.toNat ≤ 16384)
      (ht : t.toNat ≤ 1696) (hal : t.toNat % 32 = 0) (tw : Nat),
      1696 - t.toNat = n → t.toNat = 8 * tw →
      (∀ i, wd buf i = if i < tw then W0 (k + i) else W0 i) →
      ∀ i, wd (moveHist buf sh t hb hsh ht hal).1 i = if i < 212 then W0 (k + i) else W0 i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro buf t hb hsh ht hal tw hn htw hinv
    rw [moveHist]
    have e1696 : (1696 : USize).toNat = 1696 := by simp
    by_cases h : t < 1696
    · have hlt : t.toNat < 1696 := by have := USize.lt_iff_toNat_lt.mp h; omega
      have hus := usize_size_gt
      have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
      have hbs : buf.size < USize.size := by omega
      have es : (sh + t).toNat = 8 * (k + tw) := by
        rw [USize.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
      have e8 : (sh + t + 8).toNat = 8 * (k + tw + 1) :=
        (usize_add_toNat (sh + t) 8 (by omega)).trans (by omega)
      have e16 : (sh + t + 16).toNat = 8 * (k + tw + 2) :=
        (usize_add_toNat (sh + t) 16 (by omega)).trans (by omega)
      have e24 : (sh + t + 24).toNat = 8 * (k + tw + 3) :=
        (usize_add_toNat (sh + t) 24 (by omega)).trans (by omega)
      have et : (t + 32).toNat = t.toNat + 32 := usize_add_toNat t 32 (by omega)
      simp only [h, ↓reduceDIte]
      refine ih (1696 - (t + 32).toNat) (by omega) _ (t + 32) _ hsh (by omega) (by omega)
        (tw + 4) rfl (by omega) ?_
      intro i
      rw [wd_storeU64x4LE buf t _ _ _ _ _ tw htw i,
        loadU64LE_eq_wd buf (sh + t) hbs _ _ es, loadU64LE_eq_wd buf (sh + t + 8) hbs _ _ e8,
        loadU64LE_eq_wd buf (sh + t + 16) hbs _ _ e16,
        loadU64LE_eq_wd buf (sh + t + 24) hbs _ _ e24,
        hinv (k + tw), hinv (k + tw + 1), hinv (k + tw + 2), hinv (k + tw + 3), hinv i,
        ifn (show ¬ k + tw < tw by omega), ifn (show ¬ k + tw + 1 < tw by omega),
        ifn (show ¬ k + tw + 2 < tw by omega), ifn (show ¬ k + tw + 3 < tw by omega)]
      split_ifs <;> first | rfl | (exfalso; omega) | (subst_vars; rfl)
    · have heq : tw = 212 := by
        have : ¬ t.toNat < 1696 := fun hh => h (USize.lt_iff_toNat_lt.mpr (by omega))
        omega
      subst heq
      simp only [h, ↓reduceDIte]
      exact hinv

/-! ### All chunks -/

theorem xorChunks_spec (a : ByteArray) (hs : a.size < USize.size) (uo nw : Nat) :
    ∀ (n : Nat) (buf : ByteArray) (q rem : USize) (hb : buf.size = 18080)
      (hq : q.toNat + 8 * rem.toNat ≤ a.size) (base : Nat) (V : Nat → UInt64),
      rem.toNat = n → q.toNat = uo + 8 * base → Rep (wd buf) base 0 V →
      base + rem.toNat + 209 ≤ nw →
      ∃ V', Rep (wd (xorChunks a hs buf q rem hb hq).1) (base + rem.toNat) 0 V' ∧
        Ψ (inwOf a uo) nw (base + rem.toNat) V' = Ψ (inwOf a uo) nw base V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro buf q rem hb hq base V hn hqb hrep hnw
    rw [xorChunks]
    by_cases h0 : rem = 0
    · subst h0
      simp only [↓reduceDIte]
      exact ⟨V, by simpa using hrep, by simp⟩
    · simp only [h0, ↓reduceDIte]
      have hk := chunkWords_spec rem h0
      have hus := usize_size_gt
      have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
      have e8 : (8 : USize).toNat = 8 := by simp
      have e1696 : (1696 : USize).toNat = 1696 := by simp
      have ek8 : (8 * chunkWords rem).toNat = 8 * (chunkWords rem).toNat := by
        rw [USize.toNat_mul, e8]; exact Nat.mod_eq_of_lt (by omega)
      have eEnd : (1696 + 8 * chunkWords rem).toNat = 8 * (212 + (chunkWords rem).toNat) := by
        rw [USize.toNat_add, ek8, e1696, Nat.mod_eq_of_lt (by omega)]; omega
      have eq : (q + 8 * chunkWords rem).toNat = uo + 8 * (base + (chunkWords rem).toNat) := by
        rw [USize.toNat_add, ek8, Nat.mod_eq_of_lt (by omega)]; omega
      have er : (rem - chunkWords rem).toNat = rem.toNat - (chunkWords rem).toNat :=
        USize.toNat_sub_of_le rem _ (USize.le_iff_toNat_le.mpr hk.2.2)
      obtain ⟨V1, r1, p1⟩ := xorLoop4_spec a hs uo nw base _ buf q 1696
        (1696 + 8 * chunkWords rem) hb (by omega) (by omega) (by omega) (by omega) (by omega)
        0 (chunkWords rem).toNat V rfl (by omega) eEnd (by omega) hrep (by omega)
      have hm := moveHist_spec (8 * chunkWords rem) (chunkWords rem).toNat ek8
        (wd (xorLoop4 a hs buf q 1696 (1696 + 8 * chunkWords rem) hb (by omega) (by omega)
          (by omega) (by omega) (by omega)).1) _ _ 0
        (xorLoop4 a hs buf q 1696 (1696 + 8 * chunkWords rem) hb (by omega) (by omega)
          (by omega) (by omega) (by omega)).2 (by omega) (by simp) (by simp) 0 rfl (by simp)
        (fun i => by simp)
      have r2 : Rep (wd (moveHist (xorLoop4 a hs buf q 1696 (1696 + 8 * chunkWords rem) hb
          (by omega) (by omega) (by omega) (by omega) (by omega)).1 (8 * chunkWords rem) 0
          (xorLoop4 a hs buf q 1696 (1696 + 8 * chunkWords rem) hb (by omega) (by omega)
          (by omega) (by omega) (by omega)).2 (by omega) (by simp) (by simp)).1)
          (base + (chunkWords rem).toNat) 0 V1 := by
        refine ⟨fun i hi => ?_, fun k' hk' => r1.2 k' (by omega)⟩
        rw [hm i, ifp (by omega), r1.1 _ (by omega)]
        congr 1; omega
      obtain ⟨V', r', p'⟩ := ih (rem - chunkWords rem).toNat (by omega) _ (q + 8 * chunkWords rem)
        (rem - chunkWords rem) _ (by omega) (base + (chunkWords rem).toNat) V1 rfl eq r2
        (by omega)
      have e : base + (chunkWords rem).toNat + (rem - chunkWords rem).toNat = base + rem.toNat := by
        omega
      rw [e] at r' p'
      exact ⟨V', r', p'.trans p1⟩

/-! ### The tail -/

theorem condXor_eq (c : Prop) [Decidable c] (x w v : UInt64) (h1 : c → w = v)
    (h2 : ¬ c → v = 0) : condXor (decide c) x w = x ^^^ v := by
  unfold condXor
  by_cases hc : c
  · simp [hc, h1 hc]
  · simp [hc, h2 hc]

theorem xor_tail_perm (x a b c d e : UInt64) :
    x ^^^ a ^^^ b ^^^ c ^^^ d ^^^ e = x ^^^ (e ^^^ d ^^^ c ^^^ b ^^^ a) := by
  ac_rfl

theorem xorTail_spec (a : ByteArray) (hs : a.size < USize.size) (uo body : Nat)
    (V : Nat → UInt64) (hV : ∀ k, body + 212 ≤ k → V k = 0) :
    ∀ (n : Nat) (buf : ByteArray) (q o : USize) (hb : buf.size = 18080) (ho : o.toNat ≤ 1672)
      (hal : o.toNat % 8 = 0) (hq : q.toNat + (1672 - o.toNat) ≤ a.size) (t : Nat),
      1672 - o.toNat = n → o.toNat = 8 * t → q.toNat = uo + 8 * (body + t) →
      (∀ i, t ≤ i → i < 212 → wd buf i = V (body + i)) →
      (∀ i < t, wd buf i = inwOf a uo (body + i) ^^^ taps V (body + i)) →
      ∀ i < 209, wd (xorTail a hs buf q o hb ho hal hq).1 i =
        inwOf a uo (body + i) ^^^ taps V (body + i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro buf q o hb ho hal hq t hn hot hqt hhist hdone
    rw [xorTail]
    have e1672 : (1672 : USize).toNat = 1672 := by simp
    by_cases h : o < 1672
    · have hlt : o.toNat < 1672 := by have := USize.lt_iff_toNat_lt.mp h; omega
      have hus := usize_size_gt
      have hbs : buf.size < USize.size := by omega
      have e24 : (o + 24).toNat = 8 * (t + 3) :=
        (usize_add_toNat o 24 (by omega)).trans (by omega)
      have e136 : (o + 136).toNat = 8 * (t + 17) :=
        (usize_add_toNat o 136 (by omega)).trans (by omega)
      have e336 : (o + 336).toNat = 8 * (t + 42) :=
        (usize_add_toNat o 336 (by omega)).trans (by omega)
      have e456 : (o + 456).toNat = 8 * (t + 57) :=
        (usize_add_toNat o 456 (by omega)).trans (by omega)
      have e1176 : (o + 1176).toNat = 8 * (t + 147) :=
        (usize_add_toNat o 1176 (by omega)).trans (by omega)
      have eo : (o + 8).toNat = o.toNat + 8 := usize_add_toNat o 8 (by omega)
      have eq : (q + 8).toNat = q.toNat + 8 := usize_add_toNat q 8 (by omega)
      have c1560 : o < 1560 ↔ t < 195 := by
        rw [USize.lt_iff_toNat_lt, show (1560 : USize).toNat = 1560 by simp]; omega
      have c1360 : o < 1360 ↔ t < 170 := by
        rw [USize.lt_iff_toNat_lt, show (1360 : USize).toNat = 1360 by simp]; omega
      have c1240 : o < 1240 ↔ t < 155 := by
        rw [USize.lt_iff_toNat_lt, show (1240 : USize).toNat = 1240 by simp]; omega
      have c520 : o < 520 ↔ t < 65 := by
        rw [USize.lt_iff_toNat_lt, show (520 : USize).toNat = 520 by simp]; omega
      simp only [h, ↓reduceDIte]
      have hx : condXor (o < 520) (condXor (o < 1240) (condXor (o < 1360) (condXor (o < 1560)
          (load64 a q hs (by omega) ^^^ loadU64LE buf (o + 24) hbs (by omega))
          (loadU64LE buf (o + 136) hbs (by omega))) (loadU64LE buf (o + 336) hbs (by omega)))
          (loadU64LE buf (o + 456) hbs (by omega))) (loadU64LE buf (o + 1176) hbs (by omega)) =
          inwOf a uo (body + t) ^^^ taps V (body + t) := by
        rw [condXor_eq (o < 520) _ _ (V (body + (t + 147)))
            (fun hc => by
              rw [loadU64LE_eq_wd buf (o + 1176) hbs _ _ e1176]
              exact hhist _ (by omega) (by have := c520.mp hc; omega))
            (fun hc => hV _ (by have := mt c520.mpr hc; omega)),
          condXor_eq (o < 1240) _ _ (V (body + (t + 57)))
            (fun hc => by
              rw [loadU64LE_eq_wd buf (o + 456) hbs _ _ e456]
              exact hhist _ (by omega) (by have := c1240.mp hc; omega))
            (fun hc => hV _ (by have := mt c1240.mpr hc; omega)),
          condXor_eq (o < 1360) _ _ (V (body + (t + 42)))
            (fun hc => by
              rw [loadU64LE_eq_wd buf (o + 336) hbs _ _ e336]
              exact hhist _ (by omega) (by have := c1360.mp hc; omega))
            (fun hc => hV _ (by have := mt c1360.mpr hc; omega)),
          condXor_eq (o < 1560) _ _ (V (body + (t + 17)))
            (fun hc => by
              rw [loadU64LE_eq_wd buf (o + 136) hbs _ _ e136]
              exact hhist _ (by omega) (by have := c1560.mp hc; omega))
            (fun hc => hV _ (by have := mt c1560.mpr hc; omega))]
        unfold load64
        rw [loadU64LE_eq_word64 a q hs (by omega), loadU64LE_eq_wd buf (o + 24) hbs _ _ e24,
          hhist _ (by omega) (by omega), hqt, xor_tail_perm]
        unfold inwOf taps
        simp only [Nat.add_assoc]
      refine ih (1672 - (o + 8).toNat) (by omega) _ (q + 8) (o + 8) _ (by omega) (by omega)
        (by omega) (t + 1) rfl (by omega) (by omega) ?_ ?_
      · intro i hi1 hi2
        rw [wd_storeU64LE buf o _ _ t hot i, ifn (by omega)]
        exact hhist i (by omega) hi2
      · intro i hi
        rw [wd_storeU64LE buf o _ _ t hot i]
        by_cases hit : i = t
        · subst hit
          rw [ifp rfl, hx]
        · rw [ifn hit]
          exact hdone i (by omega)
    · have heq : t = 209 := by
        have : ¬ o.toNat < 1672 := fun hh => h (USize.lt_iff_toNat_lt.mpr (by omega))
        omega
      subst heq
      simp only [h, ↓reduceDIte]
      exact hdone

/-! ### Words and the message polynomial -/

theorem msgPoly_words (a : ByteArray) (hs : a.size < USize.size) :
    ∀ (n p : Nat), p + 8 * n ≤ a.size →
      π (msgPoly (bytes a p (p + 8 * n))) =
        ∑ i ∈ Finset.range n, R (wdAt a (p + 8 * i)) * π X ^ (64 * (n - 1 - i)) := by
  intro n
  induction n with
  | zero =>
    intro p _
    rw [bytes_of_le a (by omega)]
    simp [msgPoly]
  | succ n ih =>
    intro p hp
    have hpu : p.toUSize.toNat = p := USize.toNat_ofNat_of_lt' (by omega)
    have hm := msgPoly_bytes_load a p.toUSize hs (8 * n) (by omega)
    have hl : load64 a p.toUSize hs (by omega) = wdAt a p := by
      unfold load64; rw [loadU64LE_eq_word64, hpu]
    simp only [hpu, hl] at hm
    rw [show p + 8 * (n + 1) = p + 8 + 8 * n by omega, hm, map_add, map_mul, map_pow,
      ih (p + 8) (by omega), Finset.sum_range_succ']
    have e0 : 64 * (n + 1 - 1 - 0) = 8 * (8 * n) := by omega
    have hsum : ∑ i ∈ Finset.range n, R (wdAt a (p + 8 + 8 * i)) * π X ^ (64 * (n - 1 - i)) =
        ∑ i ∈ Finset.range n,
          R (wdAt a (p + 8 * (i + 1))) * π X ^ (64 * (n + 1 - 1 - (i + 1))) :=
      Finset.sum_congr rfl fun i _ => by
        rw [show p + 8 + 8 * i = p + 8 * (i + 1) by omega,
          show n + 1 - 1 - (i + 1) = n - 1 - i by omega]
    rw [hsum, Nat.mul_zero, Nat.add_zero, e0, add_comm]
    rfl

theorem bt_xorZeroBuf (p : Nat) : bt xorZeroBuf p = 0 := by
  simp only [bt, xorZeroBuf, Array.toList_replicate, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split <;> rfl

theorem wd_xorZeroBuf (k : Nat) : wd xorZeroBuf k = 0 := by
  simp only [wd, wdAt, bt_xorZeroBuf]
  rfl

/-! ### The kernel computes `rawExtend` -/

theorem rawExtendXor_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) (hbig : 3344 ≤ ulen.toNat) :
    rawExtendXor s a hs uoff ulen h hbig =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + ulen.toNat)) := by
  have hus := usize_size_gt
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have e8 : (8 : USize).toNat = 8 := by simp
  have e209 : (209 : USize).toNat = 209 := by simp
  have e24 : (24 : USize).toNat = 24 := by simp
  have e0 : (0 : USize).toNat = 0 := by simp
  have e1672 : (1672 : USize).toNat = 1672 := by simp
  have hnw : (ulen / 8).toNat = ulen.toNat / 8 := by rw [USize.toNat_div, e8]
  have hbody : (ulen / 8 - 209).toNat = ulen.toNat / 8 - 209 := by
    rw [USize.toNat_sub_of_le _ 209 (USize.le_iff_toNat_le.mpr (by omega)), e209, hnw]
  have eb8 : (8 * (ulen / 8 - 209)).toNat = 8 * (ulen.toNat / 8 - 209) := by
    rw [USize.toNat_mul, e8, hbody]; exact Nat.mod_eq_of_lt (by omega)
  have eqt : (uoff + 8 * (ulen / 8 - 209)).toNat = uoff.toNat + 8 * (ulen.toNat / 8 - 209) := by
    rw [USize.toNat_add, eb8]; exact Nat.mod_eq_of_lt (by omega)
  have en8 : (8 * (ulen / 8)).toNat = 8 * (ulen.toNat / 8) := by
    rw [USize.toNat_mul, e8, hnw]; exact Nat.mod_eq_of_lt (by omega)
  have ew : (uoff + 8 * (ulen / 8)).toNat = uoff.toNat + 8 * (ulen.toNat / 8) := by
    rw [USize.toNat_add, en8]; exact Nat.mod_eq_of_lt (by omega)
  have efin : (uoff + ulen).toNat = uoff.toNat + ulen.toNat := by
    rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  -- names for the quantities of the proof
  obtain ⟨nw, hnwN⟩ : ∃ nw, ulen.toNat / 8 = nw := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, ulen.toNat = 8 * nw + r := ⟨ulen.toNat - 8 * nw, by omega⟩
  obtain ⟨m, hmN⟩ : ∃ m, nw = m + 1 := ⟨nw - 1, by omega⟩
  rw [hnwN] at hnw hbody eb8 eqt en8 ew
  -- the seeded scratch buffer
  let V0 : Nat → UInt64 := fun k => if k = 3 then s.toUInt64 else 0
  have hb0 : (storeU64LE xorZeroBuf 24 s.toUInt64
      (by rw [xorZeroBuf_size, e24]; omega)).size = 18080 := by
    rw [storeU64LE, Model.size_storeU64LE]; exact xorZeroBuf_size
  have rep0 : Rep (wd (storeU64LE xorZeroBuf 24 s.toUInt64
      (by rw [xorZeroBuf_size, e24]; omega))) 0 0 V0 := by
    refine ⟨fun i _ => ?_, fun k hk => ifn (by omega)⟩
    rw [wd_storeU64LE xorZeroBuf 24 _ _ 3 (by rw [e24]) i, wd_xorZeroBuf, Nat.zero_add]
  -- all chunks, then the tail
  obtain ⟨V1, r1, p1⟩ := xorChunks_spec a hs uoff.toNat nw _ _ uoff (ulen / 8 - 209) hb0
    (by omega) 0 V0 rfl (by omega) rep0 (by omega)
  simp only [hbody, Nat.zero_add] at r1 p1
  have htail := xorTail_spec a hs uoff.toNat (nw - 209) V1 (fun k hk => r1.2 k (by omega))
    _ _ (uoff + 8 * (ulen / 8 - 209)) 0
    (xorChunks a hs _ uoff (ulen / 8 - 209) hb0 (by omega)).2 (by omega) (by simp)
    (by omega) 0 rfl (by simp) (by omega) (fun i _ hi => r1.1 i (by omega))
    (fun i hi => absurd hi (by omega))
  -- unfold the program down to `rawExtend`s
  unfold rawExtendXor
  dsimp only
  rw [bytesLoop_eq a hs (uoff + ulen) (by omega) _ _ _ rfl, rawExtendPortableReg_eq, ew, efin,
    e0, e1672]
  generalize xorTail a hs _ (uoff + 8 * (ulen / 8 - 209)) 0 _ _ _ _ = T at htail ⊢
  have hTs : T.1.size < USize.size := by have := T.2; omega
  -- the tail words are the residue after all cancellations
  have hT : π (msgPoly (bytes T.1 0 (0 + 1672))) = Ψ (inwOf a uoff.toNat) nw (nw - 209) V1 := by
    have hw := msgPoly_words T.1 hTs 209 0 (by have := T.2; omega)
    rw [show 0 + 8 * 209 = 0 + 1672 from rfl] at hw
    rw [hw]
    unfold Ψ
    rw [Finset.sum_Ico_eq_sum_range, show nw - (nw - 209) = 209 by omega]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [Nat.zero_add, show wdAt T.1 (8 * i) = wd T.1 i from rfl, htail i hi',
      show 209 - 1 - i = nw - 1 - (nw - 209 + i) by omega]
  -- before any cancellation: the input words, with the state folded into the first
  have h0 : Ψ (inwOf a uoff.toNat) nw 0 V0 =
      π (msgPoly (bytes a uoff.toNat (uoff.toNat + 8 * nw))) + R s.toUInt64 * π X ^ (64 * m) := by
    have htaps (i : Nat) : taps V0 i = if i = 0 then s.toUInt64 else 0 := by
      simp only [taps, V0]
      rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]
      by_cases hi : i = 0
      · subst hi; simp
      · rw [ifn (by omega), ifn hi]; simp
    unfold Ψ
    rw [msgPoly_words a hs nw uoff.toNat (by omega), ← Finset.range_eq_Ico,
      Finset.sum_congr rfl (fun i _ => by
        rw [htaps i, R_xor, R_ite, add_mul, ite_mul, zero_mul]),
      Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range nw) 0
        (fun i => R s.toUInt64 * π X ^ (64 * (nw - 1 - i))),
      ifp (Finset.mem_range.mpr (by omega)), show nw - 1 - 0 = m by omega]
    rfl
  have hRs : R s.toUInt64 = π (P s) * π X ^ 32 := by
    show π (polyR s.toUInt64.toBitVec) = _
    rw [polyR_toUInt64, map_mul, map_pow]
  have hsplit := bytes_append a (i := uoff.toNat) (m := uoff.toNat + 8 * nw)
    (j := uoff.toNat + ulen.toNat) (by omega) (by omega) (by omega)
  have hlen1 := length_bytes a (uoff.toNat + 8 * nw) (uoff.toNat + ulen.toNat) (by omega)
  have hlen2 := length_bytes a uoff.toNat (uoff.toNat + ulen.toNat) (by omega)
  apply eq_of_π_P
  rw [π_P_rawExtend, π_P_rawExtend, π_P_rawExtend, hT, p1, h0, hRs, hlen1, hlen2, ← hsplit,
    msgPoly_append, hlen1, P_zero, map_zero, zero_mul, zero_add,
    show uoff.toNat + ulen.toNat - (uoff.toNat + 8 * nw) = r by omega,
    show uoff.toNat + ulen.toNat - uoff.toNat = 8 * (m + 1) + r by omega, hmN]
  simp only [map_add, map_mul, map_pow]
  ring

/-! ### `fast_eq_ref` for the portable path -/

theorem rawExtendPortableUSize_eq (s : UInt32) (a : ByteArray) (hs : a.size < USize.size)
    (uoff ulen : USize) (h : uoff.toNat + ulen.toNat ≤ a.size) :
    rawExtendPortableUSize s a hs uoff ulen h =
      rawExtend s (bytes a uoff.toNat (uoff.toNat + ulen.toNat)) := by
  unfold rawExtendPortableUSize
  split
  · exact rawExtendXor_eq s a hs uoff ulen h _
  · exact rawExtendPortableReg_eq s a hs uoff ulen h

/-- The portable path computes the reference update on any in-bounds range. -/
theorem rawExtendPortable_eq (s : UInt32) (a : ByteArray) (off len : Nat)
    (h : off + len ≤ a.size) :
    rawExtendPortable s a off len h = rawExtend s (bytes a off (off + len)) := by
  unfold rawExtendPortable rawExtendPortableCold
  by_cases hsmall : a.size ≤ 0x7FFFFFFF
  · have hs : a.size < USize.size := by have := usize_size_gt; omega
    have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
    have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
    simp only [hsmall, ↓reduceDIte, rawExtendPortableUSize_eq, ho, hl]
  · simp only [hsmall, ↓reduceDIte]
    by_cases hs : a.size < USize.size
    · have ho : off.toUSize.toNat = off := USize.toNat_ofNat_of_lt' (by omega)
      have hl : len.toUSize.toNat = len := USize.toNat_ofNat_of_lt' (by omega)
      simp only [hs, ↓reduceDIte, rawExtendPortableUSize_eq, ho, hl]
    · simp only [hs, ↓reduceDIte, bytes_extract]

/-- `fast_eq_ref`, portable path: equal to the bitwise reference on every input. -/
theorem extendPortable_eq_extend (c : UInt32) (a : ByteArray) : extendPortable c a = extend c a := by
  simp [extendPortable, extend, rawExtendPortable_eq, bytes_whole]

/-- The portable path satisfies the polynomial spec. -/
theorem extendPortable_eq_spec (c : UInt32) (a : ByteArray) :
    extendPortable c a = Spec.extend c a := by
  rw [extendPortable_eq_extend, extend_eq_spec]

end Crc32c
