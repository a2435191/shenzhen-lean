module

import Shenzhen.Notation
import Batteries.Data.List.Basic

public section

structure Conns (nChips : ℕ) (pinType : Type) where
  private mk ::
  /-- Are two nodes connected? -/
  connected : (Fin nChips × pinType) → (Fin nChips × pinType) → Bool

namespace Conns

/-- All neighbors of a node, as a list -/
def neighbors {n m} (conns : Conns n (Fin m)) (i : Fin n) (j : Fin m) : List (Fin n × Fin m) :=
  (List.finRange n).product (List.finRange m)|>.filter (conns.connected (i, j))

/-- Create a `Conns` out of a list of (undirected) edges. This function does *not*
  compute the transitive closure. -/
def ofEdges [BEq pinType] (edges : List ((Fin nChips × pinType) × (Fin nChips × pinType))) : Conns nChips pinType where
  connected u v := edges.contains (u, v) || edges.contains (v, u)
