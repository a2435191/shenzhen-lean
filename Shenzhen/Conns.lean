import Shenzhen.Notation
import Batteries.Data.List.Basic

abbrev Conns (nChips : ℕ) (connType : Type) :=
  (Fin nChips × connType) → (Fin nChips × connType) → Bool

def Conns.neighbors {n m} (conns : Conns n (Fin m)) (i : Fin n) (j : Fin m) : List (Fin n × Fin m) :=
  (List.finRange n).product (List.finRange m)|>.filter (conns (i, j))
