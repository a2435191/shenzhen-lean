module

import Shenzhen.Notation
import Batteries.Data.List.Basic

public section

structure Conns (Pin : Type u) where
  private mk ::
  /-- Are two pins connected? -/
  connected : Pin → Pin → Bool

namespace Conns

/-- All neighbors of a node, as a list -/
def neighbors (conns : Conns Pin) (allPins : List Pin) : Pin → List Pin := fun p =>
  allPins.filter (conns.connected p)

/-- Create a `Conns` out of a list of (undirected) edges. This function does *not*
  compute the transitive closure. -/
def ofEdges [BEq Pin] (edges : List (Pin × Pin)) : Conns Pin where
  connected u v := edges.contains (u, v) || edges.contains (v, u)
