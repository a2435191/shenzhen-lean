module

public import Lean.ToExpr
public import Shenzhen.Instruction
public import Shenzhen.Line
public import Shenzhen.Integer
public import Shenzhen.Meta

public section

/-! This file is where all the `ToExpr` instances live. -/

open Lean

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

deriving instance ToExpr for ConditionalFlag
deriving instance ToExpr for Instruction.Reg
deriving instance ToExpr for Instruction.RegOrInt
deriving instance ToExpr for Instruction

-- Needed for the derived instances for e.g. `MCParser.Line`,
-- and `instToExprOptionOfToLevel` only allows a type with one universe level
-- (`Instruction` has four)
open Lean in
instance
    [ToLevel.{u}] [ToLevel.{v}] [ToLevel.{w}] [ToLevel.{x}]
    {Λ : Type u} {ρ : Type v} {ξ : Type w} {ι : Type x}
    [ToExpr Λ] [ToExpr ρ] [ToExpr ξ] [ToExpr ι]
    : ToExpr (Option (Instruction Λ ρ ξ ι)) :=
  let levels := [toLevel.{u}, toLevel.{v}, toLevel.{w}, toLevel.{x}]
  let typeExpr := mkApp4 (mkConst ``Instruction levels)
                    (toTypeExpr Λ) (toTypeExpr ρ) (toTypeExpr ξ) (toTypeExpr ι)
  let maxLevel := Level.mkNaryMax levels
  { toTypeExpr := typeExpr,
    toExpr
    | none => .app (mkConst ``Option.none [maxLevel]) typeExpr
    | some i => mkApp2 (mkConst ``Option.some [maxLevel]) typeExpr (toExpr i) }

-- elab "test" : term =>
--   let x : Option (Instruction String Unit (Fin 2) (Fin 2)) := some .nop
--   return Lean.ToExpr.toExpr x

-- #eval test

deriving instance ToExpr for MCParser.Line

deriving instance ToExpr for MC.Chip.AccReg
