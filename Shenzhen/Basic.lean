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

variable [DecidableEq χ] [DecidableEq ψ]

-- TODO: cache this result ahead of time in `Board` in a `Std.HashMap` or something
/-- Get the index of the neighbors to `(chip, pin)`, including `(chip, pin)` itself. -/
def edgeIdx (conns : Conns χ ψ) (chip : χ) (pin : ψ) : Option (Fin (conns.edges.size)) :=
  conns.edges.findFinIdx? ((chip, pin) ∈ ·)

-- TODO: compute this result ahead of time
def areConnected (conns : Conns χ ψ) : χ × ψ → χ × ψ → Bool
| u, v => conns.edges.any fun edge => u ∈ edge && v ∈ edge

end Conns

-- for now, just MC4000s
structure Board where
  {n : Nat}
  chips : Vector MC4000 n
  simpleIOConns : Conns (Fin n) MC4000.SimpleIO
  xBusConns : Conns (Fin n) MC4000.XBus
deriving Repr

structure Board.State where
  m : Nat
  xBusEffects : XBusEffects MC4000.XBus Integer (MC4000.State m)

structure Board.States (b : Board) where
  states : Vector Board.State b.n
  hm : ∀ i : Fin b.n, states[i].m = b.chips[i].m
  simpleIOByEdge : Vector SimpleIOData b.simpleIOConns.edges.size

/-- This is the "Touch Activated Light Controller" on page `CSM_TD_100650` of the manual.
For now (TODO), the input and output are simulated by more `MC4000`s. -/
@[reducible]
def lightController : Board :=
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
    simpleIOConns := { edges := #[[(0, 0), (1, 0)], [(2, 1), (3, 1)]] },
    xBusConns := { edges := #[[(1, 1), (2, 0)]] }
  }
