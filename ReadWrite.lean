/-! An experiment I had about making write effects leaf nodes, i.e.
  there can only be one write and it must happen at the end of the instruction's
  effects. For now kept as reference -/

-- `ReadWrite δ α`
-- `δ`: type of data, like `Integer` or `SimpleIOData`
inductive ReadWrite (δ : Type) : Type v → Type _
| pure (a : α)                        : ReadWrite δ α
| write (d : δ) (a : α)               : ReadWrite δ α
| sleep (n : Nat) (h : n ≠ 0) (a : α) : ReadWrite δ α
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

/-- Apply the terminal constructor `ofPure` to states that have `.pure` as their terminal constructor. -/
def tryDeep (ofPure : {τ : Type u} → τ → ReadWrite δ τ) : ReadWrite δ α → ReadWrite δ α
  | .pure a => ofPure a
  | .read next => .read (tryDeep ofPure next)
  | other => other

-- Get `f ← mf`, then apply it to `a ← (ma ())`. If `f` and `x` both write, keep the write from `f`.
def seq (mf : ReadWrite δ (α → β)) (ma : Unit → ReadWrite δ α) : ReadWrite δ β :=
  match mf with
  | .pure f => map f (ma ())
  | .write d f => tryDeep (.write d) (map f (ma ()))
  | .sleep n h f => tryDeep (.sleep n h) (map f (ma ()))
  | .read nextF => .read (seq (map Function.swap nextF) ma)
termination_by sizeOf mf

instance : Applicative (ReadWrite δ) where
  pure := pure
  map := map
  seq := seq

section

variable {α β : Type u} {f : α → β} {ofPure ofPure' : ∀ {τ : Type u}, τ → ReadWrite δ τ} {x : ReadWrite δ α}

theorem map_tryDeep {α : Type u} {β : Type u} {x : ReadWrite δ α} {f : α → β}
  (map_ofPure : ∀ {τ τ' : Type u} (t : τ) (h : τ → τ'), map h (ofPure t) = ofPure (h t))
    : map f (tryDeep ofPure x) = tryDeep ofPure (map f x) := by
  induction x generalizing β <;> try rfl
  · simp [tryDeep, map, map_ofPure]
  · simp only [tryDeep, map]
    rename_i ih
    rw [ih]

theorem tryDeep_of_not_pure
    (hx : match x with | .pure _ | .read _ => False | _ => True) : tryDeep ofPure x = x := by
  cases x <;> (try rfl) <;> contradiction

theorem tryDeep_idempotent
    (hf : ∀ {α'} (a : α'), tryDeep ofPure' (ofPure a) = ofPure a)
    : tryDeep ofPure' (tryDeep ofPure x) = tryDeep ofPure x := by
  induction x <;> try rfl
  · simp only [tryDeep]
    apply hf
  · simp only [tryDeep]
    rename_i next ih
    rw [ih]

theorem tryDeep_idempotent'
    (hf : ∀ {α'} (a : α'), match ofPure a with | .pure _ | .read _ => False | _ => True)
    : tryDeep ofPure' (tryDeep ofPure x) = tryDeep ofPure x :=
  tryDeep_idempotent fun {α'} a => tryDeep_of_not_pure (by grind)

theorem seq_tryDeep {α : Type u} {β} {g : ReadWrite δ (α → β)} {x : ReadWrite δ α}
    (hseq_ofPure : ∀ {τ τ' : Type u} (t : ReadWrite δ τ) (h : τ → τ'), ((ofPure h).seq fun _ => t) = tryDeep ofPure (map h t))
    (hmap : ∀ {τ τ' : Type u} (t : τ) (h : τ → τ'), map h (ofPure t) = ofPure (h t))
    : seq (tryDeep ofPure g) (fun _ => x) = tryDeep ofPure (seq g fun _ => x) := by
  cases g
  · simp only [tryDeep, seq]; apply hseq_ofPure
  · simp [tryDeep, seq, tryDeep_idempotent]
  · simp [tryDeep, seq, tryDeep_idempotent]
  · simp only [tryDeep, seq]
    rw [map_tryDeep hmap, seq_tryDeep] <;> assumption

end

section

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
  · simp [seq, map, tryDeep]
  · simp [seq, map, tryDeep]
  · rename_i next
    simp only [seq, map]
    congr 1
    rw [seq_pure, ←comp_map]
    rfl

theorem map_seq_r {α β γ : Type u} {f : β → γ} {g : ReadWrite δ (α → β)} {a : ReadWrite δ α}
    : map f (seq g fun _ => a) = seq (map (f ∘ ·) g) fun _ => a := by
  cases g
  · simp [pure_seq, map_pure, comp_map]
  · simp [seq, map, map_tryDeep, comp_map]
  · simp [seq, map, map_tryDeep, comp_map]
  · simp only [map, seq]
    congr 1
    rw [map_seq_r, ←comp_map, ←comp_map]
    rfl

theorem seq_assoc {α β γ : Type u} (a : ReadWrite δ α) (g : ReadWrite δ (α → β)) (h : ReadWrite δ (β → γ)) :
    seq h (fun _ => seq g fun _ => a) = ((map Function.comp h).seq fun _ => g).seq fun _ => a := by
  cases h <;> simp only [seq, map]
  · simp [map_seq_r]
  · simp [seq_tryDeep, map_seq_r, map, seq]
  · simp [seq_tryDeep, map_seq_r, map, seq]
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
