import Shenzhen.Notation
import Batteries.Data.List.Basic

structure Conns (nChips : ℕ) (pinType : Type) where
  connected : (Fin nChips × pinType) → (Fin nChips × pinType) → Bool

namespace Conns

def symmetrize (conns : Conns n c) : Conns n c :=
  ⟨fun a b => conns.connected a b || conns.connected b a⟩

def neighbors {n m} (conns : Conns n (Fin m)) (i : Fin n) (j : Fin m) : List (Fin n × Fin m) :=
  (List.finRange n).product (List.finRange m)|>.filter (conns.connected (i, j))
