import Shenzhen.Board
import Shenzhen.Compile
import Shenzhen.Examples
import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.MC4000
import Shenzhen.MCParser
import Shenzhen.PinState
import Shenzhen.SimpleIOData
import Shenzhen.Util

open Compile
open MCParser

open MC4000
abbrev PrevSimpleIOIn :=
  Vector SimpleIOData numSimpleIOPins

@[reducible] def InstructionEffects (m : Nat) :=
  ReaderT PrevSimpleIOIn
    $ StateT (State m)
    $ PinState.XBus XBus Integer

def InstructionEffects.run {m} (initState : State m)
    (prevSimpleIOIn : PrevSimpleIOIn) (fx : InstructionEffects m Unit) :  PinState.XBus XBus Integer (State m) :=
  fx prevSimpleIOIn initState <&> Prod.snd

@[inline]
def setSimpleIOOut {m} (pin : SimpleIO) (val : SimpleIOData) : InstructionEffects m Unit :=
  modify fun state => { state with
    simpleIOOut := Vector.set state.simpleIOOut pin val }

@[inline]
def readRI {m} : Instruction.RegOrInt InternalReg XBus SimpleIO → InstructionEffects m Integer
| .int n => return n
| .null => return 0
| .internal .acc => do return (←get).acc
| .simpleIO pin => do
  setSimpleIOOut pin 0
  let prevSimpleIO ← read
  return prevSimpleIO[pin]
| .xBus pin => fun _ state =>
  .readXBus pin fun d => return (d, state)

/-- Set `acc` to `f acc [value in ri]`. -/
@[specialize, inline]
def modifyAcc {m} (ri : Instruction.RegOrInt InternalReg XBus SimpleIO) (f : Integer → Integer → Integer)
    : InstructionEffects m Unit := do
  let n ← readRI ri
  modify fun state => { state with acc := f state.acc n }

@[specialize, inline]
def modifyAccByRel {m} (ri₁ ri₂ : Instruction.RegOrInt InternalReg XBus SimpleIO) (f : Integer → Integer → Bool)
    : InstructionEffects m Unit := do
  let a ← readRI ri₁
  let b ← readRI ri₂
  modify (State.setCondIff (f a b))

/-- Get a function to the next state after executing `instr`, possibly with
pin reads/a pin write. -/
def instructionEffects {m} (instr : Instruction m) : InstructionEffects m Unit := do
  -- increment the ip separately
  match instr with | .jmp _ => return; | _ => modify State.incIp;
  match instr with
  | .nop => return
  | .slp ri => do
    let n ← readRI ri
    modify ({ · with sleep := n.clampToNat })
  | .slx pin =>
    fun _ state => .peekXBus pin <| return ((), state)
  | .jmp lbl => modify ({ · with ip := lbl })
  | .mov ri r => do
    let n ← readRI ri
    match r with
    | .null => return
    | .internal .acc => modify ({· with acc := n })
    | .simpleIO pin => setSimpleIOOut pin n.toSimpleIOData
    | .xBus pin => fun _ state => .writeXBus pin n ((), state)
  | .add ri => modifyAcc ri Add.add
  | .sub ri => modifyAcc ri Sub.sub
  | .mul ri => modifyAcc ri Mul.mul
  | .not => modify fun state => { state with acc := ~~~state.acc }
  | .dgt ri => modifyAcc ri Integer.dgt
  | .dst ri₁ ri₂ => do
    let target ← readRI ri₁
    let new ← readRI ri₂
    modify fun state => { state with acc := Integer.dst state.acc target new }
  | .teq ri₁ ri₂ => modifyAccByRel ri₁ ri₂ (· = ·)
  | .tlt ri₁ ri₂ => modifyAccByRel ri₁ ri₂ (· < ·)
  | .tgt ri₁ ri₂ => modifyAccByRel ri₁ ri₂ (· > ·)
  | .tcp ri₁ ri₂ => do
    let a ← readRI ri₁
    let b ← readRI ri₂
    modify ({ · with cond := ⟨a > b, a < b⟩ })

instance {m} : ToString (State m) where
  toString
  | { acc, cond := c, ip, sleep, simpleIOOut } =>
    let condStr := match c with
      | ⟨true, false⟩ => "+"
      | ⟨false, true⟩ => "-"
      | ⟨false, false⟩ => "none"
      | ⟨true, true⟩ => "?both true?"
    s!"[acc = {acc}; ip = {ip}; sleep = {sleep}; \
    cond = {condStr}; simpleIOOut = ({simpleIOOut[0]}, {simpleIOOut[1]})]"

#eval
  let m := 3
  --                           mov p0 x1
  let instr : Instruction 3 := .mov (.simpleIO 0) (.xBus 1)
  let mfx := instructionEffects instr
  --              values on connected simple I/O line: p0  p1
  let fx := mfx |> InstructionEffects.run (.init m) #v[35, 69]
  return fx
