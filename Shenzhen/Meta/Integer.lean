module

public meta import Shenzhen.Integer -- TODO: move the code we use for meta into its own file so this is faster

local elab "test_Integer.instToExpr" sign:("-" noWs)? x:num : term =>
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
