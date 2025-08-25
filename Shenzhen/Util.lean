import Mathlib.Data.Fintype.Basic

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

def mkVector (type : Expr) (xs : List Expr) (n : Nat) (u := levelZero) : Expr :=
  let arrExpr := mkArrayLit' type xs u
  let nExpr := mkNatLit n
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
