module

import Shenzhen.Compile
import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.MC.Chip
import Shenzhen.MC.Chips
import Shenzhen.Elab.MCParser
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.IOEffects
import Shenzhen.Notation

open MC
open Instruction
open SimpleIOData

def dumb {n : Nat} (i : Nat) (hn : n ≠ 0 := by decide) : Fin n :=
  @Fin.ofNat n ⟨hn⟩ i

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
@[reducible]
def lightController : Board 4 :=
  let inputs : Array SimpleIOData := #[0, 0, 100, 0]
  let touch : Chip :=
    let flagsAndInstrs := inputs.flatMap fun (x : SimpleIOData) => #[
      (.none, .mov (.int x) (.simpleIO (show Fin 2 from 0))), -- TODO fix this hack
      (.none, .slp (.int 1))]
    Chip.mk' (τ := Chip.MC4000) flagsAndInstrs (by simp [flagsAndInstrs])
  let chip₁ := MC4000.ofCompiled mcc(
      teq acc 0
    + teq p0 100
    + mov 1 x1
    - mov 0 x1
      mov p0 acc
      slp 1)
  let chip₂ := MC4000.ofCompiled mcc(
      slx x0
      teq x0 p1
    + add 50
      tgt acc 100
    + mov 0 acc
      mov acc p1)
  let light := MC4000.ofCompiled mcc(
    mov p1 acc
    slp 1)
  {
    chips := #v[touch, chip₁, chip₂, light],
    simpleIOConns := .ofEdges [(⟨0, dumb 0⟩, ⟨1, dumb 0⟩), (⟨2, dumb 1⟩, ⟨3, dumb 1⟩)]
    xBusConns := .ofEdges [(⟨1, dumb 1⟩, ⟨2, dumb 0⟩)]
  }

def rep (n : ℕ) (f : α → α) : α → α :=
  match n with
  | 0 => id
  | k + 1 => rep k f ∘ f

def init :=
  lightController.initialStates

instance {τ : PartType} : ToString τ.InternalRegState :=
  τ.inst₂

-- TODO turn back to `#eval` after cleaning up `sorry`s
#eval! show IO Unit from do
  let states := rep 8 (Chip.advanceTick lightController) init
  for s in states do
    println! s!"{s.toString}\n"

#eval! show IO Unit from do
  let (success, states) := Chip.advanceTimeUnit lightController init 50
  if success then println!"Not stuck\n" else println! "Stuck!\n"
  for s in states do
    println! s!"{s.toString}\n"
