/-- `IOEffects ξ δ α` represents a value of type `α`, possibly delayed until reads, writes, or peeks from XBus pins happen.
  - `ξ` is the type of *X*Bus pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`). -/
inductive IOEffects (ξ : Type u) (δ : Type v) (α : Type w)
/-- Just return a value without doing any XBus effects. -/
| pure (a : α)
/-- `read pin next` represents a computation delayed until a value `d`
  from `pin` can be read; then `next d` is the result of the computation. -/
| read (pin : ξ) (next : δ → IOEffects ξ δ α)
/-- `d` is some data to be thereafter written out of `outPin`, and `next ()` is returned after the write. -/
| write (outPin : ξ) (d : δ) (next : Unit → IOEffects ξ δ α)
/-- `poll pin next` represents a computation delayed until the value
  from XBus pin `pin` arrives; then `next ()` is the result thereafter.
  This is used to implement the `slx` operation. -/
| poll (pin : ξ) (next : Unit → IOEffects ξ δ α)

-- TODO: vary `δ` depending on the pin type
namespace IOEffects

instance [Inhabited α] : Inhabited (IOEffects ξ δ α) :=
  ⟨pure default⟩

@[simp]
def map (f : α → β) : IOEffects ξ δ α → IOEffects ξ δ β
| pure a => pure (f a)
| .read p next => .read p fun d => map f (next d)
| .write p d next => .write p d fun () => map f (next ())
| .poll p next => .poll p fun () => map f (next ())

instance : Pure (IOEffects ξ δ) where
  pure := .pure

instance : Functor (IOEffects ξ δ) where
  map := map

@[simp]
def seq (mf : IOEffects ξ δ (α → β)) (mx : Unit → IOEffects ξ δ α) : IOEffects ξ δ β :=
  match mf with
  | pure f => f <$> mx ()
  | .read p next => .read p fun d => seq (next d) mx
  | .write p d next => .write p d fun () => seq (next ()) mx
  | .poll p next => .poll p fun () => seq (next ()) mx

instance : Seq (IOEffects ξ δ) where
  seq := seq

/-- You really should not be using data-dependent effects, as none of the instructions require them.
  But creating this `Monad` instance allows the use of `do` notation. -/
@[simp]
def bind (mx : IOEffects ξ δ α) (f : α → IOEffects ξ δ β) : IOEffects ξ δ β :=
  match mx with
  | pure a => f a
  | .read p next => .read p fun d => bind (next d) f
  | .write p d next => .write p d fun () => bind (next ()) f
  | .poll p next => .poll p fun () => bind (next ()) f

instance : Monad (IOEffects ξ δ) where
  bind := bind

#reduce
  let M := IOEffects (Fin 2) Nat
  let mx : M (Nat × Nat) :=
    -- waiting on two reads
    .read 0 fun d₁ => .read 0 fun d₂ => pure (d₁, d₂)
  let my x : M Unit :=
    .write 0 x fun () => .pure ()
  let ms : M (Nat × Nat) := do
    let (a, b) ← mx
    my a
    my b
    return (a, b)
  ms

section

-- TODO: make this local
attribute [simp] Functor.map Seq.seq Bind.bind Pure.pure

theorem id_map (x : IOEffects ξ δ α) : id <$> x = x := by
  induction x <;> try rfl
  all_goals
    simp; rename_i ih; funext; apply ih

theorem bind_pure_comp (f : α → β) (x : IOEffects ξ δ α) : x >>= (fun a => pure (f a)) = f <$> x := by
  induction x
  all_goals
    simp <;> rename_i ih <;> funext <;> apply ih

instance : LawfulMonad (IOEffects ξ δ) where
  map_const := rfl
  id_map := id_map
  seqLeft_eq x y := by
    simp [SeqLeft.seqLeft]
    induction x
    all_goals
      first | apply bind_pure_comp | rename_i ih; funext; simp [ih]
  seqRight_eq x y := by
    simp [SeqRight.seqRight]
    induction x
    all_goals
      first | symm; apply id_map | rename_i ih; funext; simp [ih]
  pure_seq f x := by simp [Seq.seq]
  bind_pure_comp := bind_pure_comp
  bind_map f x := by
    induction f <;> simp <;> (rename_i ih; funext; apply ih)
  pure_bind := by simp
  bind_assoc x f g := by
    induction x <;> simp <;> (rename_i ih; funext; apply ih)

end

end IOEffects
