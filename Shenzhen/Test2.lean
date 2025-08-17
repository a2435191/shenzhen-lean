import Lean

open Lean
private def List.toExprAux [ToExpr α] (consFn : Expr) : List α → Expr → Expr
  | [],    e => e
  | a::as, e => toExprAux consFn as (mkApp2 consFn (toExpr a) e)

instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (List α) where
  toTypeExpr := mkApp (mkConst ``List [toLevel.{u}]) (toTypeExpr α)
  toExpr l :=
    let nilFn := mkApp (mkConst ``List.nil [toLevel.{u}]) (toTypeExpr α)
    let consFn := mkApp (mkConst ``List.cons [toLevel.{u}]) (toTypeExpr α)
    List.toExprAux consFn l.reverse nilFn

instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (Array α) where
  toTypeExpr := mkApp (mkConst ``Array [toLevel.{u}]) (toTypeExpr α)
  toExpr a := mkApp2 (mkConst ``List.toArray [toLevel.{u}]) (toTypeExpr α) (toExpr a.toList)

#eval Array.range 100
