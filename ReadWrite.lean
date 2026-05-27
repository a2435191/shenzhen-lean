/-! An experiment I had about making write effects leaf nodes, i.e.
  there can only be one write and it must happen at the end of the instruction's
  effects. For now kept as reference -/

-- `ReadWrite δ α`
-- `δ`: type of data, like `Integer` or `SimpleIOData`
inductive ReadWrite (δ : Type) : Type v → Type _
| pure (a : α)                      : ReadWrite δ α
| write (d : δ) (a : α)             : ReadWrite δ α
| read (next : ReadWrite δ (δ → α)) : ReadWrite δ α

namespace ReadWrite

def map (f : α → β) : ReadWrite δ α → ReadWrite δ β
  | .pure a => .pure (f a)
  | .write d a => .write d (f a)
  | .read next => .read <| map (f ∘ ·) next

@[simp]
theorem sizeOf_map_eq_sizeOf {f : α → β} {x : ReadWrite δ α} : sizeOf (map f x) = sizeOf x := by
  induction x generalizing β <;> simp_all [map]

def _root_.Function.swap (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

def writeIfNotAlreadyWritten (toWrite : δ) : ReadWrite δ α → ReadWrite δ α
  | .pure a => .write toWrite a
  | .write written a => .write written a
  | .read next => .read (writeIfNotAlreadyWritten toWrite next)

-- Get `f ← mf`, then apply it to `a ← (ma ())`. If `f` and `x` both write, keep the write from `f`.
def seq (mf : ReadWrite δ (α → β)) (ma : Unit → ReadWrite δ α) : ReadWrite δ β :=
  match mf with
  | .pure f => map f (ma ())
  | .write d f => writeIfNotAlreadyWritten d (map f (ma ()))
  | .read nextF => .read (seq (map Function.swap nextF) ma)
termination_by sizeOf mf

instance : Applicative (ReadWrite δ) where
  pure := pure
  map := map
  seq := seq

theorem map_writeIfNotAlreadyWritten {d : δ} {f : α → β} {x : ReadWrite δ α}
    : map f (writeIfNotAlreadyWritten d x) = writeIfNotAlreadyWritten d (map f x) := by
  cases x <;> try rfl
  simp only [writeIfNotAlreadyWritten, map, read.injEq]
  apply map_writeIfNotAlreadyWritten

/-- The fundamental property of `writeIfNotAlreadyWritten`. -/
theorem writeIfNotAlreadyWritten_idempotent {x : ReadWrite δ α}
    : writeIfNotAlreadyWritten d' (writeIfNotAlreadyWritten d x) = writeIfNotAlreadyWritten d x := by
  match x with
  | .pure _ | .write .. => rfl
  | .read next =>
    simp only [writeIfNotAlreadyWritten, read.injEq]
    apply writeIfNotAlreadyWritten_idempotent

variable {α β δ}

theorem map_pure (f : α → β) (x : α) : map f (pure (δ := δ) x) = pure (f x) :=
  rfl

theorem comp_map {α β γ} (g : α → β) (h : β → γ) (a : ReadWrite δ α)
    : map (h ∘ g) a = map h (map g a) := by
  induction a generalizing β γ
  · rfl
  · simp [map]
  · rename_i ih
    simp only [map] at ⊢ ih
    congr 1
    apply ih (g ∘ ·) (h ∘ ·)

theorem pure_seq (g : α → β) (a : ReadWrite δ α) : (pure g).seq (fun _ => a) = map g a := by
  cases a <;> simp [seq]

theorem seq_pure {α β} (g : ReadWrite δ (α → β)) (a : α)
    : seq g (fun _ => pure a) = map (· a) g := by
  cases g
  · simp [seq, map]
  · simp [seq, map, writeIfNotAlreadyWritten]
  · rename_i next
    simp only [seq, map]
    congr 1
    rw [seq_pure, ←comp_map]
    rfl

theorem seq_writeIfNotAlreadyWritten {α β} {d : δ} {g : ReadWrite δ (α → β)} {x : ReadWrite δ α}
    : seq (writeIfNotAlreadyWritten d g) (fun _ => x) = writeIfNotAlreadyWritten d (seq g fun _ => x) := by
  cases g
  · simp [writeIfNotAlreadyWritten, seq]
  · simp [writeIfNotAlreadyWritten, seq, writeIfNotAlreadyWritten_idempotent]
  · simp only [writeIfNotAlreadyWritten, seq]
    rw [map_writeIfNotAlreadyWritten, seq_writeIfNotAlreadyWritten]

theorem map_seq_r {α β γ} {f : β → γ} {g : ReadWrite δ (α → β)} {a : ReadWrite δ α}
    : map f (seq g fun _ => a) = seq (map (f ∘ ·) g) fun _ => a := by
  cases g
  · simp [pure_seq, map_pure, comp_map]
  · simp [seq, map_writeIfNotAlreadyWritten, map, comp_map]
  · simp only [map, seq]
    congr 1
    rw [map_seq_r, ←comp_map, ←comp_map]
    rfl

theorem seq_assoc {α β γ} (a : ReadWrite δ α) (g : ReadWrite δ (α → β)) (h : ReadWrite δ (β → γ)) :
    seq h (fun _ => seq g fun _ => a) = ((map Function.comp h).seq fun _ => g).seq fun _ => a := by
  cases h <;> simp only [seq, map]
  · simp [map_seq_r]
  · rw [seq_writeIfNotAlreadyWritten, map_seq_r]
  · rw [map_seq_r, ←comp_map, seq_assoc]
    simp only [←comp_map]
    rfl

instance : LawfulApplicative (ReadWrite δ) where
  map_const := rfl
  id_map a := by
    induction a <;> try rfl
    simpa! [Functor.map]
  map_pure f x := rfl

  seqLeft_eq a b := rfl
  seqRight_eq a b := rfl
  pure_seq := pure_seq
  seq_pure := seq_pure
  seq_assoc := seq_assoc
