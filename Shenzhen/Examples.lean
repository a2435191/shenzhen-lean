import Shenzhen.Board
import Shenzhen.Compile
import Shenzhen.MC4000
import Shenzhen.MCParser

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
@[reducible]
def lightController : Board :=
  let inputs : Array SimpleIOData := #[0, 0, 100, 0]
  let touch :=
    let instrs := inputs.flatMap fun x => #[
      (.none, .mov (.int x) (.simpleIO 0)),
      (.none, .slp (.int 1))]
    MC4000.mk' instrs
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
    simpleIOConns := #v[#v[#[(1, 0)], #[]], #v[#[(0, 0)], #[]], #v[#[], #[(3, 1)]], #v[#[], #[(2, 1)]]],
    xBusConns := #v[#v[#[], #[]], #v[#[], #[(2, 0)]], #v[#[(1, 1)], #[]], #v[#[], #[]]]
  }
