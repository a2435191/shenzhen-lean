module

public import Shenzhen.Integer
import Shenzhen.Util

public structure SimpleIOData where
  n : UInt8
  le : n ≤ 100 := by decide
deriving DecidableEq

namespace SimpleIOData
public section

instance : Repr SimpleIOData where
  reprPrec x prec := reprPrec x.n prec

instance : ReprAtom SimpleIOData :=
  .mk

instance : ToString SimpleIOData :=
  ⟨(toString ·.n)⟩

instance : Inhabited SimpleIOData :=
  ⟨{ n := 0 }⟩

instance : Coe SimpleIOData UInt8 :=
  ⟨(·.n)⟩

def ofNat (n : Nat) (h : n ≤ 100) :=
  mk (UInt8.ofNat n) <| by
    apply (UInt8.le_ofNat_iff (by decide)).mpr
    rwa [UInt8.toNat_ofNat_of_lt' (by grind only)]

instance {n} : OfNat SimpleIOData n where
  ofNat :=
    if h : n ≤ 100 then .ofNat n h
    else panic! "In `instOfNatSimpleIOData`: argument is not ≤ 100!"

/-- Clamp negative values to `(0 : Nat)`. -/
@[inline] def clampToNat : SimpleIOData → Nat
| { n, .. } => n.toNat

end
end SimpleIOData

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

namespace SimpleIOData
public section

def toInteger : SimpleIOData → Integer
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

instance : Coe SimpleIOData Integer :=
  ⟨toInteger⟩

@[inline] instance : LE SimpleIOData where
  le x y := x.n ≤ y.n

@[inline] instance : DecidableLE SimpleIOData :=
  fun x y => if h : x.n ≤ y.n then .isTrue h else .isFalse h

@[inline] instance : Max SimpleIOData :=
  maxOfLe

end
end SimpleIOData

/-- Cast an `Integer` to `SimpleIOData` by clamping its value between `0` and `100`, inclusive. -/
public def Integer.toSimpleIOData : Integer → SimpleIOData
| { n, .. } =>
  let n' := Clamp.clamp n 0 100
  ⟨n'.toUInt16.toUInt8, by
    rw [show (100 : UInt8) = (100 : UInt16).toUInt8 by decide]
    apply UInt16.toUInt8_le.mpr
    apply UInt16.le_trans (b := n'.toUInt16)
    · rw [UInt16.le_iff_toNat_le, UInt16.toNat_mod]
      apply Nat.mod_le
    · apply Int16.toUInt16_le
      · exact Clamp.lo_le_clamp (by decide)
      · exact Clamp.clamp_le_hi (by decide)⟩
