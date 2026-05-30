module

public import Lean.Expr
import Lean.Meta.AppBuilder

/-! # Utils for meta-phase stuff -/

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

def mkListLit' (type : Expr) (xs : List Expr) (u := Level.zero) : Expr :=
  xs.foldr (init := .app (mkConst ``List.nil [u]) type) fun expr acc =>
    mkApp3 (mkConst ``List.cons [u]) type expr acc

def mkArrayLit' (type : Expr) (xs : List Expr) (u := Level.zero) : Expr :=
  mkApp2 (mkConst ``List.toArray [u]) type (mkListLit' type xs u)

public instance instDecidableArraySizeEq.{u} {α : Type u} {arr : Array α} {n : Nat} : Decidable (arr.size = n) :=
  inferInstance

public def mkVector (type : Expr) (xs : List Expr) (u := Level.zero) : Expr :=
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
