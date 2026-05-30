module

public import Lean.Elab.Term.TermElabM

import Shenzhen.Instruction
import Shenzhen.MC4000
import Shenzhen.Line
public meta import Shenzhen.Compile
public meta import Shenzhen.MCParser

namespace MCParser

elab "line(" e:line ")" : term => elabLine e none

elab "mc(" e:sepBy(line, "\n", linebreak) ")" : term => do
  let lines ← e.getElems.mapM (elabLine · none)
  Lean.Meta.mkArrayLit (←Lean.Elab.Term.mkConst ``MC4000.Line) lines.toList

-- #eval mc(
--   slp 1
--   slp 2
--   slx x0
--   slp p0
-- )


-- #check #[
--   line(nop),
--   line(mov 0 x1),
--   line(jmp lbl),
--   line(slp p0),
--   line(slx x0),
--   line(add x1),
--   line(jmp labeleeeeeee3)
-- ]

/--
error: `slx` only works with XBus registers
-/
#guard_msgs in
#check line(slx p0)

/-- Invoke the microchip compiler to turn MC-series source code into an initial
chip state. This happens at Lean compile time.

If you want this to happen at runtime, just use the functions in `Compile.lean`
directly. -/
elab "mcc(" e:sepBy(line, "\n", linebreak) ")" : term => do
  match e.getElems.mapM parseLine with
  | .error e => throw e
  | .ok lines =>
    match Compile.compile lines with
    | .error e => throwError toString e
    | .ok compiled => return Lean.ToExpr.toExpr compiled


-- #eval mcc(
--     slx x0
--     teq x0 p1
--   + add 50
--     tgt acc 100
--   + mov 0 acc
--     mov acc p1)
