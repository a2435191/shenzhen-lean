module

import Batteries.Data.Fin.Basic
import Batteries.Data.Fin.Lemmas
import Batteries.Tactic.Lemma

public import Lean.Expr
import Lean.Meta.AppBuilder

/-- `n` spaces -/
public def String.whitespace (n : Nat) : String :=
  String.pushn "" ' ' n

namespace Fin

/-- Find the smallest `j > i` s.t. `p j = true`, or `none` if no such `j` exists. -/
@[specialize]
public def nextFinIdx? (i : Fin n) (p : Fin n → Bool) : Option (Fin n) :=
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
      symm; simp [nextFinIdx?, ←Fin.not_le, le_last]
    | cast i' ih =>
      unfold nextFinIdx?
      simp only [val_castSucc, Nat.add_lt_add_iff_right, is_lt, reduceDIte]
      rw [Fin.succ] at ih
      rw [ih]
      simp only [lt_def, val_castSucc]
      split
      · symm
        simp only [find?_eq_some_iff, Bool.and_eq_true,
                   decide_eq_true_eq, Bool.and_eq_false_imp]
        refine ⟨⟨Nat.lt_succ_self _, ‹_›⟩, fun j h₁ h₂ => ?_⟩
        exfalso
        simp [lt_def] at h₁ h₂
        omega
      · congr 1; funext j
        match Nat.lt_trichotomy (i' + 1) j with
        | .inl h => simp [h]; omega
        | .inr (.inl h) => simp [h] at *; intro; assumption
        | .inr (.inr h) => congr 2; apply propext; omega

@[always_inline]
public def succ' : Fin n → Fin n
| ⟨k, lt⟩ => ⟨(k + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt lt)⟩

end Fin

namespace Clamp
public section

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

end
end Clamp

-- TODO move this to its own file
namespace Lean.Meta

/-! Bring some functions out of the `MetaM` monad. -/

/-- Returns `Decidable.decide p`, where `inst : Decidable p`. -/
def mkDecide' (p inst : Expr) : Expr :=
  mkApp2 (mkConst ``Decidable.decide) p inst

/-- Returns a proof for `p : Prop` using `decide p`, where
  `inst : Decidable p`. -/
public def mkDecideProof' (p inst : Expr) : Expr :=
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

public def mkVector (type : Expr) (xs : List Expr) (u := levelZero) : Expr :=
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

public section

@[inline, simp] def Array.mapFinIdx' (as : Array α) (f : Fin as.size → α → β) : Array β :=
  as.mapFinIdx fun i a h => f ⟨i, h⟩ a

@[inline, simp] def Array.zipFinIdx (as : Array α) : Array (Fin as.size × α) :=
  as.mapFinIdx fun i a h => ⟨⟨i, h⟩, a⟩

@[inline, simp] def Vector.mapFinIdx' (xs : Vector α n) (f : Fin n → α → β) : Vector β n :=
  xs.mapFinIdx fun i a h => f ⟨i, h⟩ a

@[inline, simp] def Vector.zipFinIdx  (xs: Vector α n) : Vector (α × Fin n) n :=
  xs.mapFinIdx fun i a h => ⟨a, i, h⟩

@[inline, simp] def Vector.findSome?FinIdx (xs : Vector α n) (f : Fin n → α → Option β) : Option (β × Fin n) :=
  xs.zipFinIdx.findSome? fun (a, i) => (·, i) <$> f i a

theorem Vector.countP_map_le_countP
    {v : Vector α n} {f : α → β} {p : α → Bool} {q : β → Bool}
    (hf : ∀ a, q (f a) → p a) : (v.map f).countP q ≤ v.countP p := by
  rw [Vector.countP_map]
  apply Vector.countP_mono_left
  intros; apply hf; assumption
