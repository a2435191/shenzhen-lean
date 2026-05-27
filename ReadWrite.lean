/-! An experiment I had about making write effects leaf nodes, i.e.
  there can only be one write and it must happen at the end of the instruction's
  effects. For now kept as reference -/

-- `ReadWrite δ α`
-- `δ`: type of data, like `Integer` or `SimpleIOData`
inductive ReadWrite (δ : Type) : Type v → Type _
| pure (a : α)                        : ReadWrite δ α
| write (d : δ) (a : α)               : ReadWrite δ α
| sleep (n : Nat) (h : n ≠ 0) (a : α) : ReadWrite δ α -- we probably don't
| read (next : ReadWrite δ (δ → α))   : ReadWrite δ α

namespace ReadWrite

def map (f : α → β) : ReadWrite δ α → ReadWrite δ β
  | .pure a => .pure (f a)
  | .write d a => .write d (f a)
  | .sleep n h a => .sleep n h (f a)
  | .read next => .read <| map (f ∘ ·) next

@[simp]
theorem sizeOf_map_eq_sizeOf {f : α → β} {x : ReadWrite δ α} : sizeOf (map f x) = sizeOf x := by
  induction x generalizing β <;> simp_all [map]

def _root_.Function.swap (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

/-- `deepWrite d x` writes `d` at the terminal constructor of `x`, as long
  as the terminal constructor is `pure`. -/
def tryDeepWrite (toWrite : δ) : ReadWrite δ α → ReadWrite δ α
  | .pure a => .write toWrite a
  | .write written a => .write written a
  | .sleep n h a => .sleep n h a
  | .read next => .read (tryDeepWrite toWrite next)

/-- Like `tryDeepWrite` but for `sleep`. "deep" as in deepest (i.e. terminal) constructor, not
  as in "deep sleep" -/
def tryDeepSleep (n : Nat) (h : n ≠ 0) : ReadWrite δ α → ReadWrite δ α
  | .pure a => .sleep n h a
  | .write written a => .write written a
  | .sleep n h a => .sleep n h a -- We can't add the `n`s or anything without losing the lawful property
  | .read next => .read (tryDeepSleep n h next)

-- Get `f ← mf`, then apply it to `a ← (ma ())`. If `f` and `x` both write, keep the write from `f`.
def seq (mf : ReadWrite δ (α → β)) (ma : Unit → ReadWrite δ α) : ReadWrite δ β :=
  match mf with
  | .pure f => map f (ma ())
  | .write d f => tryDeepWrite d (map f (ma ()))
  | .sleep n h f => tryDeepSleep n h (map f (ma ()))
  | .read nextF => .read (seq (map Function.swap nextF) ma)
termination_by sizeOf mf

instance : Applicative (ReadWrite δ) where
  pure := pure
  map := map
  seq := seq

theorem map_tryDeepWrite {d : δ} {f : α → β} {x : ReadWrite δ α}
    : map f (tryDeepWrite d x) = tryDeepWrite d (map f x) := by
  cases x <;> try rfl
  simp only [tryDeepWrite, map, read.injEq]
  apply map_tryDeepWrite

theorem map_tryDeepSleep {f : α → β} {x : ReadWrite δ α}
    : map f (tryDeepSleep n h x) = tryDeepSleep n h (map f x) := by
  cases x <;> try rfl
  simp only [tryDeepSleep, map, read.injEq]
  apply map_tryDeepSleep

/-- The fundamental property of `tryDeepWrite`. -/
theorem tryDeepWrite_idempotent {x : ReadWrite δ α}
    : tryDeepWrite d' (tryDeepWrite d x) = tryDeepWrite d x := by
  match x with
  | .pure _ | .write .. | .sleep .. => rfl
  | .read next =>
    simp only [tryDeepWrite, read.injEq]
    apply tryDeepWrite_idempotent

variable {α β δ}

theorem map_pure (f : α → β) (x : α) : map f (pure (δ := δ) x) = pure (f x) :=
  rfl

theorem comp_map {α β γ} (g : α → β) (h : β → γ) (a : ReadWrite δ α)
    : map (h ∘ g) a = map h (map g a) := by
  induction a generalizing β γ
  · rfl
  · simp [map]
  · rfl
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
  · simp [seq, map, tryDeepWrite]
  · simp only [seq, map, tryDeepSleep]
  · rename_i next
    simp only [seq, map]
    congr 1
    rw [seq_pure, ←comp_map]
    rfl

theorem tryDeepWrite_tryDeepSleep_idempotent : tryDeepWrite d (tryDeepSleep n h x) = tryDeepSleep n h x := by
  induction x <;> simp only [tryDeepWrite, tryDeepSleep]
  congr

theorem tryDeepSleep_tryDeepWrite_idempotent : tryDeepSleep n h (tryDeepWrite d x) = tryDeepWrite d x := by
  induction x <;> simp only [tryDeepSleep, tryDeepWrite]
  congr

theorem tryDeepSleep_idempotent : tryDeepSleep n' h' x = tryDeepSleep n h (tryDeepSleep n' h' x) := by
  induction x <;> simp only [tryDeepSleep]
  congr

theorem seq_tryDeepWrite {α β} {d : δ} {g : ReadWrite δ (α → β)} {x : ReadWrite δ α}
    : seq (tryDeepWrite d g) (fun _ => x) = tryDeepWrite d (seq g fun _ => x) := by
  cases g
  · simp [tryDeepWrite, seq]
  · simp [tryDeepWrite, seq, tryDeepWrite_idempotent]
  · simp [tryDeepWrite, seq, ←map_tryDeepSleep, ←map_tryDeepWrite, tryDeepWrite_tryDeepSleep_idempotent]
  · simp only [tryDeepWrite, seq]
    rw [map_tryDeepWrite, seq_tryDeepWrite]

theorem seq_tryDeepSleep {α β} {g : ReadWrite δ (α → β)} {x : ReadWrite δ α}
    : seq (tryDeepSleep n h g) (fun _ => x) = tryDeepSleep n h (seq g fun _ => x) := by
  cases g
  · simp [tryDeepSleep, seq]
  · simp [tryDeepSleep, seq, tryDeepSleep_tryDeepWrite_idempotent]
  · simp [tryDeepSleep, seq, ←tryDeepSleep_idempotent]
  · simp only [tryDeepSleep, seq]
    rw [map_tryDeepSleep, seq_tryDeepSleep]

theorem map_seq_r {α β γ} {f : β → γ} {g : ReadWrite δ (α → β)} {a : ReadWrite δ α}
    : map f (seq g fun _ => a) = seq (map (f ∘ ·) g) fun _ => a := by
  cases g
  · simp [pure_seq, map_pure, comp_map]
  · simp [seq, map_tryDeepWrite, map, comp_map]
  · simp [seq, map, map_tryDeepSleep, comp_map]
  · simp only [map, seq]
    congr 1
    rw [map_seq_r, ←comp_map, ←comp_map]
    rfl

theorem seq_assoc {α β γ} (a : ReadWrite δ α) (g : ReadWrite δ (α → β)) (h : ReadWrite δ (β → γ)) :
    seq h (fun _ => seq g fun _ => a) = ((map Function.comp h).seq fun _ => g).seq fun _ => a := by
  cases h <;> simp only [seq, map]
  · simp [map_seq_r]
  · rw [seq_tryDeepWrite, map_seq_r]
  · rw [map_seq_r, seq_tryDeepSleep]
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
