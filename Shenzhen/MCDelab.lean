import Shenzhen.Instruction
import Shenzhen.Compile
import Shenzhen.Line
import Shenzhen.MCParser

open Lean.PrettyPrinter

@[app_unexpander MCParser.Line.mk]
def unexpandLine : Unexpander
| `($_mk $lbl:term $cond:term $instr:term $comment:term) =>
  dbg_trace comment
  `(0)
| _ => throw ()

def str := "heyyyyy"
-- #check line(here: @nop # hi)
#check show MC4000.Line from { label := "whee", condition := .pos, instruction := some .nop, comment := str }
