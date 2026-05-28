/-! An experiment I had about making write effects leaf nodes, i.e.
  there can only be one write and it must happen at the end of the instruction's
  effects. For now kept as reference -/

-- `ReadWrite δ α`
-- `Nat` represents read/written data, like `Integer` or `SimpleIOData`.
inductive ReadWrite : Type v → Type _
| pure (a : α)                        : ReadWrite α
| write (a : α)               : ReadWrite α
| sleep (n : Nat) (h : n ≠ 0) (a : α) : ReadWrite α
| read (next : ReadWrite (Nat → Nat × α))   : ReadWrite α

#check show ReadWrite String from
  .read <| .read <| .write sorry
namespace ReadWrite

def map (f : α → β) : ReadWrite α → ReadWrite β
  | .pure a => .pure (f a)
  | .write a => .write (f a)
  | .sleep n h a => .sleep n h (f a)
  | .read next => .read <| map (fun g d => ((g d).1, f (g d).2)) next

@[simp]
theorem sizeOf_map_eq_sizeOf {f : α → β} {x : ReadWrite α} : sizeOf (map f x) = sizeOf x := by
  induction x generalizing β <;> simp_all [map]

def _root_.Function.swap (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

/-- Apply the terminal constructor `ofPure` to states that have `.pure` as their terminal constructor. -/
def tryDeep (ofPure : {τ : Type u} → τ → ReadWrite τ) : ReadWrite α → ReadWrite α
  | .pure a => ofPure a
  | .read next => .read (tryDeep ofPure next)
  | other => other

-- Get `f ← mf`, then apply it to `a ← (ma ())`. If `f` and `x` both write, keep the write from `f`.
def seq (mf : ReadWrite (α → β)) (ma : Unit → ReadWrite α) : ReadWrite β :=
  match mf with
  | .pure f => map f (ma ())
  | .write f => tryDeep .write (map f (ma ()))
  | .sleep n h f => tryDeep (.sleep n h) (map f (ma ()))
  | .read nextF => .read (seq (map (fun f a d => ((f d).1, (f d).2 a)) nextF) ma)
termination_by sizeOf mf

instance : Applicative ReadWrite where
  pure := pure
  map := map
  seq := seq

section

variable {α β : Type u} {f : α → β} {ofPure ofPure' : ∀ {τ : Type u}, τ → ReadWrite τ} {x : ReadWrite α}

theorem map_tryDeep {α : Type u} {β : Type u} {x : ReadWrite α} {f : α → β}
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

theorem seq_tryDeep {α : Type u} {β} {g : ReadWrite (α → β)} {x : ReadWrite α}
    (hseq_ofPure : ∀ {τ τ' : Type u} (t : ReadWrite τ) (h : τ → τ'), ((ofPure h).seq fun _ => t) = tryDeep ofPure (map h t))
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

theorem map_pure (f : α → β) (x : α) : map f (pure x) = pure (f x) :=
  rfl

theorem comp_map {α β γ} (g : α → β) (h : β → γ) (a : ReadWrite α)
    : map (h ∘ g) a = map h (map g a) := by
  induction a generalizing β γ
  · rfl
  · simp [map]
  · rfl
  · rename_i next ih
    simp only [map] at ⊢ ih
    congr 1
    exact ih (fun g_1 d => ((g_1 d).fst, g (g_1 d).snd)) (fun (g : Nat → Nat × β) d => ((g d).fst, h (g d).snd))

theorem pure_seq (g : α → β) (a : ReadWrite α) : (pure g).seq (fun _ => a) = map g a := by
  cases a <;> simp [seq]

theorem seq_pure {α β} (g : ReadWrite (α → β)) (a : α)
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

theorem map_seq_r {α β γ : Type u} {f : β → γ} {g : ReadWrite (α → β)} {a : ReadWrite α}
    : map f (seq g fun _ => a) = seq (map (f ∘ ·) g) fun _ => a := by
  cases g
  · simp [pure_seq, map_pure, comp_map]
  · simp [seq, map, map_tryDeep, comp_map]
  · simp [seq, map, map_tryDeep, comp_map]
  · simp only [map, seq]
    congr 1
    rw [map_seq_r, ←comp_map, ←comp_map]
    rfl

theorem seq_assoc {α β γ : Type u} (a : ReadWrite α) (g : ReadWrite (α → β)) (h : ReadWrite (β → γ)) :
    seq h (fun _ => seq g fun _ => a) = ((map Function.comp h).seq fun _ => g).seq fun _ => a := by
  cases h <;> simp only [seq, map]
  · simp [map_seq_r]
  · simp [seq_tryDeep, map_seq_r, map, seq]
  · simp [seq_tryDeep, map_seq_r, map, seq]
  · rw [map_seq_r, ←comp_map, seq_assoc]
    simp only [←comp_map]
    rfl

instance : LawfulApplicative ReadWrite where
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
