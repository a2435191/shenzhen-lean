module

import all Shenzhen.IntLemmas
public import Shenzhen.Util

import Lean
public import Lean.Elab.Term.TermElabM

public structure Integer where
  n : Int16
  le : n ≤ 999 := by decide
  ge : -999 ≤ n := by decide
deriving DecidableEq, BEq

namespace Integer
public section

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

private lemma n_ne_minValue {x : Integer} : x.n ≠ .minValue := fun hn =>
  have := hn ▸ x.ge
  by contradiction

private lemma n_ne_minValue' {n : Int16} (le : n ≤ 999) (ge : -999 ≤ n) : n ≠ .minValue :=
  @n_ne_minValue ⟨n, le, ge⟩

@[inline] instance : LT Integer :=
  ⟨(·.n < ·.n)⟩

instance : DecidableLT Integer :=
  fun x y => decidable_of_bool (x.n < y.n) decide_eq_true_iff

@[inline] instance : LE Integer :=
  ⟨(·.n ≤ ·.n)⟩

instance : DecidableLE Integer :=
  fun x y => decidable_of_bool (x.n ≤ y.n) decide_eq_true_iff

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
private def clampLiftOp (f : Int16 → Int16 → Int16) : Integer → Integer → Integer
| ⟨a, _, _⟩, ⟨b, _, _⟩ => ⟨
  Clamp.clamp (f a b) (-999) 999,
  Clamp.clamp_le_hi (by decide), Clamp.lo_le_clamp (by decide)⟩

@[inline] def add := clampLiftOp Int16.add
@[inline] def sub := clampLiftOp Int16.sub
@[inline] def mul := clampLiftOp Int16.mul

instance : Add Integer := ⟨add⟩
instance : Sub Integer := ⟨sub⟩
instance : Mul Integer := ⟨mul⟩

/-- The `not` operation sends `0` to `100` and all other numbers to `0`. -/
@[inline] def not : Integer → Integer
| 0 => 100
| _ => 0

-- Just for entering literals
@[inline] def neg : Integer → Integer
| ⟨n, le, ge⟩ =>
  {
    n := -n,
    le := show -n ≤ - -999 from -- this hint speeds up elaboration significantly
      (neg_le_neg_iff (n_ne_minValue' le ge) (by decide)).mpr ge,
    ge :=
      (neg_le_neg_iff (by decide) (n_ne_minValue' le ge)).mpr le
  }

instance : Neg Integer := ⟨neg⟩

/-- `Integer` division has the same semantics as `Int16.div` -/
@[inline] def div (a b : Integer) : Integer :=
  have := by
    constructor
    all_goals rw [le_iff_toInt_le, toInt_div_of_ne_left _ _ n_ne_minValue]
    case' left =>
      show -999 ≤ _
      apply And.left ∘ Int.natAbs_le_iff.mp
    case' right =>
      show _ ≤ 999
      apply And.right ∘ Int.natAbs_le_iff.mp
    all_goals
      apply Nat.le_trans (Int.natAbs_tdiv_le_natAbs ..)
      rw [Int.natAbs_le_iff]
      show toInt (-999) ≤ _ ∧ _ ≤ toInt 999
      repeat rw [←Int16.le_iff_toInt_le]
      exact ⟨a.ge, a.le⟩
  ⟨a.n / b.n, And.right this, And.left this⟩

instance : Div Integer :=
  ⟨div⟩

@[inline] def abs (x : Integer) : Integer :=
  if x ≥ 0 then x else -x

@[inline] def remainder (a b : Integer) : Integer :=
  if b = 0 then 0 else
    letI rem := abs (a - (a / b) * b) -- TODO : use native mod here instead of `-` and `*` which require runtime truncation
    if a < 0 then -rem else rem

-- TODO : mod (as in MC4010)

/-- `getDigit x i` returns the
`i`th (zero-indexed) base-`10` digit from the right of `x`, preserving the sign of `x`.
If `i ∉ {0, 1, 2}`, returns zero. -/
@[inline] def getDigit (x i : Integer) : Integer :=
  match i with
  | 0 => remainder x 10
  | 1 => remainder (x / 10) 10
  | 2 => x / 100
  | _ => 0

/-- `setDigit x i d` returns `x` with its `i`th digit set to `d.abs % 10`, following the conventions of `dgt`.
Additionally, the sign of the returned value is the same as the sign of `d` for
`i ∈ {0, 1, 2}`. Otherwise, if `i ∉ {0, 1, 2}`, `setDigit` returns `x` unchanged. -/
@[inline] def setDigit (x i d : Integer) : Integer :=
  letI digit := abs (remainder d 10)
  letI sign := if d ≥ 0 then 1 else -1
  letI x' := abs x
  letI toReplace := getDigit x' i
  sign * match i with
    | 0 => x' - toReplace + digit
    | 1 => x' - toReplace * 10 + digit * 10
    | 2 => x' - toReplace * 100 + digit * 100
    | _ => 0

end

open Lean in
public instance : ToExpr Integer where
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
