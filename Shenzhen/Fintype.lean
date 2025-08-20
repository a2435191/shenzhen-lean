import Mathlib.Data.Fintype.Basic

instance : Fintype (BitVec n) :=
  Fintype.ofSurjective BitVec.ofFin fun bv => ⟨bv.toFin, rfl⟩
