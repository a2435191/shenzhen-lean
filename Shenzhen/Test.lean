/- MWE -/
abbrev A := Nat -- the specific type doesn't matter as long as they're the same
abbrev B := Nat

-- can also replace `T` with e.g. `Prod`,
-- and `Option` with e.g. `Array`
structure T (α β : Type)

structure S where
  x : Option (T A S)
  y : (T B S)
