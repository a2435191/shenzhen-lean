import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

/-! `CommRing` instance for `Fin` -/
namespace Fin

theorem add_assoc {a b c : Fin n} : a + b + c = a + (b + c) := by
  simp [Fin.add_def]
  congr 1
  apply Nat.add_assoc

theorem neg_add_cancel {a : Fin n} : -a + a = ⟨0, a.pos⟩ := by
  simp [Fin.neg_def, Fin.add_def, Nat.sub_add_cancel (Nat.le_of_lt a.is_lt)]

theorem add_comm {a b : Fin n} : a + b = b + a := by
  simp only [add_def]
  congr 2
  apply Nat.add_comm

instance [NeZero n] : AddCommGroup (Fin n) where
  add_assoc _ _ _ := add_assoc
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := neg_add_cancel
  add_comm _ _ := add_comm
  sub_eq_add_neg := Fin.sub_eq_add_neg

theorem left_distrib {a b c : Fin n} : a * (b + c) = a * b + a * c := by
  simp [Fin.mul_def, Fin.add_def]
  congr 1
  apply Nat.mul_add

theorem right_distrib {a b c : Fin n} : (a + b) * c = a * c + b * c := by
  simp [Fin.mul_def, Fin.add_def]
  congr 1
  apply Nat.add_mul

instance [NeZero n] : CommRing (Fin n) where
  left_distrib _ _ _ := left_distrib
  right_distrib _ _ _ := right_distrib
  zero_mul := Fin.zero_mul
  mul_zero := Fin.mul_zero
  mul_assoc := Fin.mul_assoc
  one_mul := Fin.one_mul
  mul_one := Fin.mul_one
  mul_comm := Fin.mul_comm

instance instNeZero (x : Fin n := by assumption) : NeZero n :=
  ⟨Nat.ne_of_lt' x.pos⟩

theorem add_sub_cancel {a b : Fin n} : a + (b - a) = b :=
  have := instNeZero
  _root_.add_sub_cancel a b

/-- Find the smallest `j > i` s.t. `p j = true`, or `none` if no such `j` exists. -/
@[specialize] def nextFinIdx? (i : Fin n) (p : Fin n → Bool) : Option (Fin n) :=
  if h : i.val + 1 < n then
    letI iSucc := mk (i + 1) h
    if p iSucc then some iSucc else nextFinIdx? iSucc p
  else none
termination_by n - i.val

theorem nextFinIdx?_eq {i : Fin n} : nextFinIdx? i p = find? fun j => j > i && p j := by
  match n with
  | 0 => exact i.elim0
  | n' + 1 =>
    induction i using reverseInduction with
    | last =>
      convert_to none = none
      · simp [nextFinIdx?]
      · simp [le_last]
      · rfl
    | cast i' ih =>
      have : i'.castSucc.val + 1 < n' + 1 := by
        simp
      unfold nextFinIdx?
      simp only [this, dite_true]
      split_ifs with h
      · refine (find?_eq_some_iff.mpr ⟨?_, ?_⟩).symm
        · exact Bool.and_eq_true_iff.mpr ⟨by simp [lt_def], h⟩
        · intro ⟨j, hj₁⟩ hj₂
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt]
          left
          simpa [le_def, Nat.lt_succ_iff] using hj₂
      · show i'.succ.nextFinIdx? p = _
        simp_rw [ih, lt_def, val_succ, val_castSucc]
        congr 1
        funext j
        if h₁ : i'.val + 1 < j.val then
          have : i'.val < j.val := by omega
          simp only [h₁, this]
        else if h₂ : j.val ≤ i'.val then
          have this₁ : ¬(i'.val + 1 < j) := by omega
          have this₂ : ¬(i'.val < j) := by omega
          simp_rw [this₁, this₂]
        else
          have : j.val = i' + 1 := by omega
          simp_rw [this, lt_self_iff_false, Nat.lt_succ_self,
                   decide_false, Bool.false_and,
                   decide_true, Bool.true_and]
          symm
          simp only [val_castSucc, Bool.not_eq_true] at h
          convert h
end Fin

@[always_inline]
def Fin.succ' : Fin n → Fin n
| ⟨k, lt⟩ => ⟨(k + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt lt)⟩

instance BitVec.instFintype : Fintype (BitVec n) :=
  Fintype.ofSurjective BitVec.ofFin fun bv => ⟨bv.toFin, rfl⟩

namespace Clamp

variable {α : Type u} [LE α] [DecidableLE α]

@[reducible, inline]
def clamp (x lo hi : α) :=
  if x ≤ lo then lo else if x ≥ hi then hi else x

variable [@Std.Refl α (· ≤ ·)] [@Std.Total α (· ≤ ·)]
variable {x lo hi : α}

theorem clamp_le_hi (h : lo ≤ hi) : clamp x lo hi ≤ hi := by
  unfold clamp
  split
  · exact h
  · split
    · apply Std.Refl.refl
    · have := Std.Total.total (r := (· ≤ ·)) x hi
      apply this.resolve_right
      assumption

theorem lo_le_clamp (h : lo ≤ hi) : lo ≤ clamp x lo hi := by
  unfold clamp
  split
  · apply Std.Refl.refl
  · split
    · exact h
    · have := Std.Total.total (r := (· ≤ ·)) lo x
      apply this.resolve_right
      assumption

/-! Instances for use with `Integer` and `SimpleIOData` -/

instance : @Std.Refl Int16 LE.le :=
  ⟨Int16.le_refl⟩

instance : @Std.Total Int16 LE.le where
  total a b := (Int16.le_or_lt a b).imp_right Int16.le_of_lt

end Clamp

namespace Lean.Meta

/-! Bring some functions out of the `MetaM` monad. -/

/-- Returns `Decidable.decide p`, where `inst : Decidable p`. -/
def mkDecide' (p inst : Expr) : Expr :=
  mkApp2 (mkConst ``Decidable.decide) p inst

/-- Returns a proof for `p : Prop` using `decide p`, where
  `inst : Decidable p`. -/
def mkDecideProof' (p inst : Expr) : Expr :=
  -- folowing `Meta.mkDecideProof`
  let decP := mkDecide' p inst
  let decEqTrue := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) decP (mkConst ``true)
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  let h := Meta.mkExpectedPropHint h decEqTrue
  mkApp3 (mkConst ``of_decide_eq_true) p inst h

def mkListLit' (type : Expr) (xs : List Expr) (u := levelZero) : Expr :=
  xs.foldr (init := .app (mkConst ``List.nil [u]) type) fun expr acc =>
    mkApp3 (mkConst ``List.cons [u]) type expr acc

def mkArrayLit' (type : Expr) (xs : List Expr) (u := levelZero) : Expr :=
  mkApp2 (mkConst ``List.toArray [u]) type (mkListLit' type xs u)

local instance instDecidableArraySizeEq.{u} {α : Type u} {arr : Array α} {n : Nat} : Decidable (arr.size = n) :=
  inferInstance

def mkVector (type : Expr) (xs : List Expr) (u := levelZero) : Expr :=
  let arrExpr := mkArrayLit' type xs u
  let nExpr := mkNatLit xs.length
  mkApp4 (mkConst ``Vector.mk [u]) type nExpr arrExpr <|
    mkDecideProof'
      (mkNatEq
        (mkApp2 (mkConst ``Array.size [u]) type arrExpr)
        nExpr)
      (mkApp3 (mkConst ``instDecidableArraySizeEq [u]) type arrExpr nExpr)

end Lean.Meta

-- def a : Nat → Nat := id
-- def b : Nat → Nat := Nat.succ
-- def c : Nat → Nat := Nat.pred

-- open Lean in
-- elab "test " : term => do
--   let arr := #[``a, ``b, ``c]
--   return Meta.mkArrayLit'
--     (←mkArrow Nat.mkType Nat.mkType)
--     (arr.toList.map mkConst)

-- #eval (test).map (· 35)

@[inline] def Array.mapFinIdx' (as : Array α) (f : Fin as.size → α → β) : Array β :=
  as.mapFinIdx fun i a h => f ⟨i, h⟩ a

@[inline] def Array.zipFinIdx (as : Array α) : Array (Fin as.size × α) :=
  as.mapFinIdx fun i a h => ⟨⟨i, h⟩, a⟩

@[inline] def Vector.mapFinIdx' (xs : Vector α n) (f : Fin n → α → β) : Vector β n :=
  xs.mapFinIdx fun i a h => f ⟨i, h⟩ a

@[inline] def Vector.zipFinIdx (xs: Vector α n) : Vector (α × Fin n) n :=
  xs.mapFinIdx fun i a h => ⟨a, i, h⟩
