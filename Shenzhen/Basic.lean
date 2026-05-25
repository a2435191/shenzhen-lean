import Shenzhen.Compile
import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.MC4000
import Shenzhen.MCParser
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.IOEffects

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
@[reducible]
def lightController : Board 4 :=
  let inputs : Array SimpleIOData := #[0, 0, 100, 0]
  let touch :=
    let flagsAndInstrs := inputs.flatMap fun x => #[
      (.none, .mov (.int x) (.simpleIO 0)),
      (.none, .slp (.int 1))]
    MC4000.mk' flagsAndInstrs (by simp [flagsAndInstrs])
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
    simpleIOConns := .symmetrize fun
      | (0, 0), (1, 0) | (2, 1), (3, 1) => true
      | _, _ => false
    xBusConns := .symmetrize fun
      | ⟨1, 1⟩, ⟨2, 0⟩ => true
      | _, _ => false
  }

def rep (n : ℕ) (f : α → α) : α → α :=
  match n with
  | 0 => id
  | k + 1 => rep k f ∘ f

def init :=
  lightController.initialStates

set_option maxRecDepth 5000 in
#reduce rep 8 (MC4000.advanceTick lightController) init

#reduce MC4000.advanceTimeUnit lightController init 50
