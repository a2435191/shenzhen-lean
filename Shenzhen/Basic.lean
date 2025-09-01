import Shenzhen.Board
import Shenzhen.Compile
import Shenzhen.Examples
import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.MC4000
import Shenzhen.MCParser
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.XBusEffects

open Compile
open MCParser
open MC4000






#eval
  let m := 3
  --                           mov p0 x1
  let instr : Instruction 3 := .mov (.simpleIO 0) (.xBus 1)
  let mfx := instructionEffects instr
  --              values on connected simple I/O line: p0  p1
  let fx := mfx |> InstructionEffects.run (.init m) #v[35, 69]
  return fx
