module

import Shenzhen.Notation
import Batteries.Data.List.Basic

public section

structure Conns.Node (nChips : ℕ) (nPins : Fin nChips → ℕ) where
  /-- Which chip -/
  i : Fin nChips
  /-- Which pin on chip `i` -/
  j : Fin (nPins i)
deriving BEq

structure Conns (nChips : ℕ) (nPins : Fin nChips → ℕ) where
  private mk ::
  /-- Are two pins connected? -/
  connected : Conns.Node nChips nPins → Conns.Node nChips nPins → Bool

namespace Conns

variable {nChips : ℕ} {nPins : Fin nChips → ℕ}

/-- All neighbors of a node, as a list -/
def neighbors (conns : Conns nChips nPins) : Node nChips nPins → List (Node nChips nPins) := fun v =>
  (List.finRange nChips).flatMap fun i' =>
    (List.finRange (nPins i'))
      |>.map (fun j' => ⟨i', j'⟩)
      |>.filter (conns.connected v)

/-- Create a `Conns` out of a list of (undirected) edges. This function does *not*
  compute the transitive closure. -/
def ofEdges (edges : List (Node nChips nPins × Node nChips nPins)) : Conns nChips nPins where
  connected u v := edges.contains (u, v) || edges.contains (v, u)
