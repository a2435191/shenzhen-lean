import Shenzhen.Util
import Mathlib.Tactic.DeriveFintype
import Lean

deriving instance Fintype for UInt16
deriving instance Fintype for Int16

structure Integer where
  n : Int16
  le : n ≤ 999 := by decide
  ge : -999 ≤ n := by decide
deriving DecidableEq, BEq, Fintype

namespace Integer

instance : Repr Integer where
  reprPrec x prec := reprPrec x.n prec

instance : ReprAtom Integer :=
  .mk

instance : ToString Integer :=
  ⟨(toString ·.n)⟩

instance : Inhabited Integer :=
  ⟨{ n := 0 }⟩

instance : Coe Integer Int16 :=
  ⟨(·.n)⟩

open Int16

def ofInt (n : Int) (h₁ : n ≤ 999) (h₂ : -999 ≤ n) :=
  have : Int16.ofInt n ≤ .ofInt 999 ∧ Int16.ofInt (-999) ≤ .ofInt n := by
    constructor <;> (
      apply (Int16.ofInt_le_iff_le ..).mpr
      all_goals first | trivial | grind only)
  Integer.mk (.ofInt n) this.left this.right

instance {n} : OfNat Integer n where
  ofNat :=
    if h : n ≤ 999 then
      have := Nat.lt_of_le_of_lt h (by decide)
      have h₁ :=
        @ofNat_le_iff_le n 999 this (by decide)|>.mpr h
      have h₂ := Int16.le_trans (b := 0) (by decide) <|
        zero_le_ofNat_of_lt this
      ⟨Int16.ofNat n, h₁, h₂⟩
    else panic! "In `instOfNatInteger`: argument is > 999!"

/-- Clamp negative values to `(0 : Nat)`. -/
@[inline] def clampToNat : Integer → Nat
| { n, .. } => n.toNatClampNeg

/-- Lift a binary operation on `Int16`s to `Integer`s by clamping the result
to `[-999, 999]`. -/
@[inline, specialize]
private def liftOp (f : Int16 → Int16 → Int16) : Integer → Integer → Integer
| ⟨a, _, _⟩, ⟨b, _, _⟩ => ⟨
  Clamp.clamp (f a b) (-999) 999,
  Clamp.clamp_le_hi (by decide), Clamp.lo_le_clamp (by decide)⟩

instance : Add Integer := ⟨Integer.liftOp Int16.add⟩
instance : Sub Integer := ⟨Integer.liftOp Int16.sub⟩
instance : Mul Integer := ⟨Integer.liftOp Int16.mul⟩

/-- The `not` operation. -/
instance : Complement Integer where
  complement
  | ⟨0, _, _⟩ => 100
  | _ => 0

end Integer

namespace Int16

theorem eq_minValue_iff_dvd_toInt {a : Int16} : (a = .minValue ∨ a = 0) ↔ 2^15 ∣ a.toInt := by
  constructor
  · rintro (h|h) <;> (rw [h]; decide)
  · intro ⟨k, hk⟩
    have hk_lt : k < 1 := by
      apply Int.lt_of_mul_lt_mul_left (a := 2^15) ?_ (by decide)
      rw [show (2^15: Int) * 1 = 32767 + 1 by decide]
      apply Int.lt_add_one_of_le
      rw [←hk]
      apply toInt_le
    have hk_ge : k ≥ -1 := by
      refine Int.not_lt.mp fun hn => ?_
      refine absurd (le_toInt a) (Int.not_le_of_gt ?_)
      rw [hk]
      exact Int.mul_lt_mul_of_pos_left hn (by decide)

    match k with
    | -1 =>
      left
      rwa [show (2^15: Int) * (-1) = (-2^15: Int16).toInt by decide,
           toInt_inj
      ] at hk
    | 0 =>
      right
      rwa [show (2^15: Int) * 0 = (0: Int16).toInt by decide,
           toInt_inj
      ] at hk

theorem toInt_neg' {a : Int16} (ha : a ≠ .minValue) : (-a).toInt = -(a.toInt) := by
  rw [toInt_neg, Int.neg_bmod]
  simp only [Nat.reducePow, Int.cast_ofNat_Int, toInt_bmod]
  simp only [show (65536: Int) = 2 * 2^15 by decide,
            @Int.mul_dvd_mul_iff_left 2 _ _ (by decide)]
  simp only [←eq_minValue_iff_dvd_toInt, ha, false_or]
  split <;> simp_all

theorem mod_lt_of_pos (a : Int16) {b : Int16} (hb : b > 0) : a % b < b := by
  rw [lt_iff_toInt_lt, toInt_mod]
  apply Int.tmod_lt_of_pos
  rwa [←toInt_zero, ←lt_iff_toInt_lt]

theorem lt_mod_of_pos (a : Int16) {b : Int16} (hb : b > 0) : -b < a % b := by
  rw [lt_iff_toInt_lt,
      @toInt_neg' b (by intro; simp_all),
      toInt_mod]
  apply Int.lt_tmod_of_pos
  rwa [←toInt_zero, ←lt_iff_toInt_lt]

theorem neg_le_neg_iff {a b : Int16} (ha : a ≠ .minValue) (hb : b ≠ .minValue) : -a ≤ -b ↔ b ≤ a := by
  rw [le_iff_toInt_le, le_iff_toInt_le]
  rw [toInt_neg' ha, toInt_neg' hb]
  simp

end Int16

namespace Integer

open Int16

/-- `dgt` stands for "digit get." It preserves sign. -/
def dgt (acc target : Integer) : Integer :=
  have h₁ {n : Int16} : n % 10 ≤ 999 :=
    Int16.le_of_lt (Int16.lt_of_lt_of_le (mod_lt_of_pos n (by decide)) (by decide))
  have h₂ {n : Int16} : -999 ≤ n % 10 :=
    Int16.le_of_lt (Int16.lt_of_le_of_lt (by decide) (lt_mod_of_pos n (by decide)))

  match target with
  | ⟨0, _, _⟩ => ⟨acc.n % 10, h₁, h₂⟩
  | ⟨1, _, _⟩ => ⟨(acc.n / 10) % 10, h₁, h₂⟩
  | ⟨2, _, _⟩ => ⟨(acc.n / 100) % 10, h₁, h₂⟩ -- TODO: remove unnecessary % 10 call. Requires work to show bounds
  | _ => 0

/-- `dst` stands for "digit set" -/
def dst (_acc _target _new : Integer) : Integer :=
  -- In case `new` is outside [-9, 9]
  -- let newDigit := new.n % 10 -- with the same sign as `new`
  panic! "`dst` is unimplemented!" -- TODO

-- Just for entering literals
instance : Neg Integer where
  neg
  | ⟨n, le, ge⟩ =>
    have : n ≠ minValue := by
      intro hn
      rw [hn] at ge
      contradiction
    {
      n := -n,
      le := show -n ≤ - -999 from -- this hint speeds up elaboration significantly
        (neg_le_neg_iff this (by decide)).mpr ge,
      ge :=
        (neg_le_neg_iff (by decide) this).mpr le
    }

instance : LT Integer :=
  ⟨(·.n < ·.n)⟩

instance : DecidableLT Integer :=
  fun ⟨a, _, _⟩ ⟨b, _, _⟩ =>
    if h : a < b then .isTrue h
    else .isFalse h

open Lean in
instance : ToExpr Integer where
  toTypeExpr := mkConst ``Integer
  toExpr
  | { n, .. } =>
    let pf₁ := -- n ≤ 999
      mkDecideLEProof (toExpr n) (toExpr (999 : Int16))
    let pf₂ := -- -999 ≤ n
      mkDecideLEProof (toExpr (-999 : Int16)) (toExpr n)
    mkApp3 (mkConst ``Integer.mk) (toExpr n) pf₁ pf₂
where
  /-- Makes a proof for `a ≤ b` using `decide`, where `a b : Int16`. -/
  mkDecideLEProof (a b : Expr) : Expr :=
    Meta.mkDecideProof'
      (mkApp4 (mkConst ``LE.le [0]) (mkConst ``Int16) (mkConst ``instLEInt16) a b)
      (mkApp2 (mkConst ``Int16.decLe) a b)

elab "test_Integer.instToExpr" sign:("-" noWs)? x:num : term =>
  let n : Int := (if sign.isSome then -1 else 1) * x.getNat
  if h : n ≤ 999 ∧ -999 ≤ n then
    return Lean.ToExpr.toExpr (Integer.ofInt n h.left h.right)
  else throwError "invalid literal provided"

/-- error: invalid literal provided -/
#guard_msgs in
#check test_Integer.instToExpr -1103

/-- info: { n := -999, le := ⋯, ge := ⋯ } : Integer -/
#guard_msgs in
#check test_Integer.instToExpr -999

/-- info: { n := -15, le := ⋯, ge := ⋯ } : Integer -/
#guard_msgs in
#check test_Integer.instToExpr -15

/-- info: { n := 0, le := ⋯, ge := ⋯ } : Integer -/
#guard_msgs in
#check test_Integer.instToExpr 0

/-- info: { n := 37, le := ⋯, ge := ⋯ } : Integer -/
#guard_msgs in
#check test_Integer.instToExpr 37

/-- info: { n := 999, le := ⋯, ge := ⋯ } : Integer -/
#guard_msgs in
#check test_Integer.instToExpr 999

/-- error: invalid literal provided -/
#guard_msgs in
#check test_Integer.instToExpr 8314
