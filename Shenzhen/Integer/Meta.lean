module

public import Lean.Elab.Term.TermElabM

public import Shenzhen.Integer
public import Shenzhen.Util.Meta

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
