import Shenzhen.Integer

structure IOData where
  n : UInt8
  le : n ≤ 100 := by decide

instance : Inhabited IOData :=
  ⟨{ n := 0 }⟩

instance : Coe IOData UInt8 :=
  ⟨(·.n)⟩

instance instOfNatIOData : OfNat IOData n where
  ofNat :=
    if h : n.toUInt8 ≤ 100 then { n := n.toUInt8, le := h }
    else panic! "In `instOfNatIOData`: argument is not ≤ 100!"

theorem UInt8.bitVec_not_msb_iff {n : UInt8} : n.toBitVec.msb = false ↔ n < 128 := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt, toNat_toBitVec]
  rw [UInt8.lt_iff_toNat_lt, show 2 ^ 8 = 2 * 128 by decide]
  rw [Nat.mul_lt_mul_left (by decide)]
  rfl

theorem UInt8.toInt8_le {a b : UInt8} (ha : a < 128) (hb : b < 128) : a.toInt8 ≤ b.toInt8 ↔ a ≤ b := by
  simp only [Int8.le_iff_toBitVec_sle, le_iff_toBitVec_le, toBitVec_toInt8]
  rw [BitVec.sle_eq_decide, decide_eq_true_eq, BitVec.le_def]
  have {x : Nat} (hx : x < 128) : 2 * x < 2 ^ 8 := by
    rwa [show 2 ^ 8 = 2 * 128 by decide,
         Nat.mul_lt_mul_left (by decide)]
  rw [BitVec.toInt_eq_toNat_of_lt (this ha),
      BitVec.toInt_eq_toNat_of_lt (this hb)]
  rw [Int.ofNat_le]

def IOData.toInteger : IOData → Integer
| ⟨n, le⟩ =>
  have : n < 128 := UInt8.lt_of_le_of_lt le (by decide)
  have pf₁ := by
    refine Int16.le_trans ?_ (show 100 ≤ 999 by decide)
    rwa [show 100 = (UInt8.toInt8 100).toInt16 by decide,
        Int8.toInt16_le, UInt8.toInt8_le this (by decide)]
  have pf₂ := by
    apply Int16.le_trans (show -999 ≤ 0 by decide)
    rw [show 0 = (UInt8.toInt8 0).toInt16 by decide,
        Int8.toInt16_le,
        UInt8.toInt8_le (by decide) this]
    apply UInt8.zero_le
  ⟨n.toInt8.toInt16, pf₁, pf₂⟩

instance : Coe IOData Integer :=
  ⟨IOData.toInteger⟩
