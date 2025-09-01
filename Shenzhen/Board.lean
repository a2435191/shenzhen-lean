import Shenzhen.MC4000

abbrev Conns (numChips numPins : Nat) :=
  Vector (Vector (Array (Fin numChips × Fin numPins)) numPins) numChips

-- for now, just MC4000s
structure Board where
  {n : Nat}
  chips : Vector MC4000 n
  simpleIOConns : Conns n MC4000.numSimpleIOPins
  xBusConns : Conns n MC4000.numXBusPins
deriving Repr
