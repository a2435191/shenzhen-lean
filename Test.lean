import Mathlib.Tactic.Convert
inductive Program (δ : Type u) : Type u → Type (u + 1)
| pure (val : α) : Program δ α
/-- Waiting on a value from input. -/
| read (next : Program δ (δ → α)) : Program δ α

def Program.map (f : α → β) : Program δ α → Program δ β
| .pure a => .pure (f a)
| .read next => .read (map (f ∘ ·) next)

def Program.eval (data : Unit → δ) : Program δ α → Program δ α
| .pure val => .pure val
| .read next => .map (· (data ())) next

instance : Functor (Program δ) where
  map := .map



-- instance : Applicative (Program δ) where
--   pure := .pure
--   seq := sorry

-- structure Program (δ : Type u) (α : Type v) where
--   arity : Nat
--   toFun : Vector δ arity → α

-- namespace Program

-- def pure (a : α) : Program δ α where
--   arity := 0
--   toFun _ := a

-- def seq (mf : Program δ (α → β)) (mx : Unit → Program δ α) : Program δ β :=
--   let ⟨n, f⟩ := mf
--   let ⟨m, xFun⟩ := mx ()
--   ⟨m + n, fun v =>
--     letI v₁ : Vector δ n := (v.extract 0 n).cast (by omega)
--     letI v₂ : Vector δ m := (v.extract n).cast (by omega)
--     f v₁ (xFun v₂)⟩

-- instance : Applicative (Program δ) where
--   pure := .pure
--   seq := .seq

-- instance : LawfulFunctor (Program δ) where
--   map_const := by intros; rfl
--   id_map := by
--     simp [Functor.map, seq, pure]
--   comp_map := by
--     simp [Functor.map, seq, pure]
