-- import Shenzhen.Board
import Shenzhen.Compile
-- import Shenzhen.Examples
import Shenzhen.Instruction
import Shenzhen.Integer
import Shenzhen.MC4000
import Shenzhen.MCParser
import Shenzhen.SimpleIOData
import Shenzhen.Util
import Shenzhen.XBusEffects
structure Conns (χ : Type u) (ψ : Type v) where
  edges : Array (List (χ × ψ)) -- each edge is `(chip, pin)`
  nontrivial : ∀ edge ∈ edges, edge.length ≥ 2 := by decide
  nodupChips : ∀ edge ∈ edges, List.Nodup (edge.unzip.fst) := by decide
  disjoint : ∀ i j : Fin edges.size, i ≠ j → ∀ x ∈ edges[i], x ∉ edges[j] := by decide
deriving Repr

namespace Conns

instance : Inhabited (Conns χ ψ) :=
  ⟨#[], nofun, nofun, nofun⟩

-- TODO: cache this result ahead of time in `Board` in a `Std.HashMap` or something
/-- Get the index of the neighbors to `(chip, pin)`, including `(chip, pin)` itself. -/
def edgeIdx [DecidableEq χ] [DecidableEq ψ] (conns : Conns χ ψ) (chip : χ) (pin : ψ) : Option (Fin (conns.edges.size)) :=
  conns.edges.findFinIdx? ((chip, pin) ∈ ·)

end Conns

-- for now, just MC4000s
structure Board where
  {n : Nat}
  chips : Vector MC4000 n
  simpleIOConns : Conns (Fin n) MC4000.SimpleIO
  xBusConns : Conns (Fin n) MC4000.XBus
deriving Repr

structure Board.States (b : Board) where
  chipStates : Vector ((m : Nat) × MC4000.State.InstructionEffects m Unit) b.n
  h : ∀ i : Fin b.n, chipStates[i].1 = b.chips[i].m
  simpleIOByEdge : Vector SimpleIOData b.simpleIOConns.edges.size

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
    simpleIOConns := { edges := #[[(0, 0), (1, 0)], [(2, 1), (3, 1)]] },
    xBusConns := { edges := #[[(1, 1), (2, 0)]] }
  }

open MC4000 MC4000.State in
#eval
  let m := 3
  --                           mov p0 x1
  let instr : Instruction 3 := .mov (.simpleIO 0) (.xBus 1)
  let mfx := instructionEffects instr
  --              values on connected simple I/O line: p0  p1
  let fx := mfx |> InstructionEffects.run' (.init m) #v[35, 69]
  return fx

-- def resolveXBus (fx : MC4000.State.Instru)

/-- Step a board's states one cycle, which is the time it takes to complete a single `nop` instruction. -/
def step (board : Board) (states : board.States) : board.States :=
  let chipStates := (states.chipStates).mapFinIdx fun i ⟨m, fx⟩ hi =>
    let := fx.run' sorry <| Vector.ofFn fun j =>
      let edgeIdx := board.simpleIOConns.edgeIdx ⟨i, hi⟩ j
      (states.simpleIOByEdge.get <$> edgeIdx).getD 0
    ()
  sorry
