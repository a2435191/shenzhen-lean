import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- `IOEffects ξ ι α` represents a value of type `α`, possibly delayed until sleep, or reads/writes/peeks from XBus pins happen.
  We also record reads and writes from simple I/O pins, although they don't block.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*/O pins.-/
inductive IOEffects (ξ : Type u) (ι : Type v) : Type x → Type (max u v _)
/-- Just return a value immediately, without doing any effects. -/
| pure (a : α) : IOEffects _ _ α
/-- `xBusRead pin next` represents a computation delayed until a value `d`
  from `pin` can be read; then `next d` is the result of the computation. -/
| xBusRead (pin : ξ) (next : IOEffects ξ ι (Integer → α)) : IOEffects _ _ α
/-- `d` is some data to be thereafter written out of `outPin`, and `next ()` is returned after the write. -/
| xBusWrite (outPin : ξ) (d : Integer) (next : IOEffects ξ ι α) : IOEffects _ _ α
/-- `xBusPoll pin next` represents a computation delayed until the value
  from XBus pin `pin` arrives (but without consuming the value);
  then `next ()` is the result thereafter.
  This is used to implement the `slx` instruction. -/
| xBusPoll (pin : ξ) (next : IOEffects ξ ι α) : IOEffects _ _ α
| simpleIORead (pin : ι) (next : IOEffects ξ ι (SimpleIOData → α)) : IOEffects _ _ α
| simpleIOWrite (outPin : ι) (d : SimpleIOData) (next : IOEffects ξ ι α) : IOEffects _ _ α
/-- Wait for `n` time units. -/
| sleep (n : Nat) (h : n ≠ 0) (next : IOEffects ξ ι α) : IOEffects _ _ α

namespace IOEffects

instance [Inhabited α] : Inhabited (IOEffects ξ ι α) :=
  ⟨pure default⟩

@[simp]
instance : Pure (IOEffects ξ ι) where
  pure := .pure

@[simp]
def map (f : α → β) : IOEffects ξ ι α → IOEffects ξ ι β
  | .pure a => .pure (f a)
  | .xBusRead pin next => .xBusRead pin (map (f ∘ ·) next)
  | .xBusWrite pin d next => .xBusWrite pin d (map f next)
  | .xBusPoll pin next => .xBusPoll pin (map f next)
  | .simpleIORead pin next => .simpleIORead pin (map (f ∘ ·) next)
  | .simpleIOWrite pin d next => .simpleIOWrite pin d (map f next)
  | .sleep n h next => .sleep n h (map f next)

instance : Functor (IOEffects ξ ι) where
  map := map

@[simp, reducible]
def _root_.Function.swap {α β γ} (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

@[simp] -- simp needed for decreasing proof in `seq` and decreasing proofs for lawful applicative theorems below
theorem sizeOf_map_eq_sizeOf {f : α → β} {fx : IOEffects ξ ι α} : sizeOf (map f fx) = sizeOf fx := by
  induction fx generalizing β <;> simp_all [map]

@[simp]
def seq (mf : IOEffects ξ ι (α → β)) (mx : Unit → IOEffects ξ ι α) : IOEffects ξ ι β :=
  match mf with
  | .pure f => f <$> mx ()
  | .xBusRead pin nextF => .xBusRead pin (seq (map Function.swap nextF) mx)
  | .xBusWrite pin d nextF => .xBusWrite pin d (seq nextF mx)
  | .xBusPoll pin nextF => .xBusPoll pin (seq nextF mx)
  | .simpleIORead pin nextF => .simpleIORead pin (seq (map Function.swap nextF) mx)
  | .simpleIOWrite pin d nextF => .simpleIOWrite pin d (seq nextF mx)
  | .sleep n h nextF => .sleep n h (seq nextF mx)
termination_by sizeOf mf
decreasing_by all_goals simp [sizeOf_map_eq_sizeOf, show ∀ n, 0 < 1 + n by omega]

instance : Applicative (IOEffects ξ ι) where
  seq := seq

section

-- TODO: make this local
attribute [simp] Functor.map Seq.seq Bind.bind Pure.pure

private theorem id_map (x : IOEffects ξ ι α) : id <$> x = x := by
  induction x
  all_goals first | rfl | simp; rename_i ih; funext; apply ih

theorem _root_.Function.comp_assoc {f : γ → δ} {g : β → γ} {h : α → β} : (f ∘ g) ∘ h = f ∘ (g ∘ h) :=
  rfl

private theorem comp_map (g : α → β) (h : β → γ) (x : IOEffects ξ ι α) : (h ∘ g) <$> x = h <$> g <$> x := by
  induction x generalizing β γ
  <;> simp_all
  <;> (rename_i ih; exact ih (h := fun x => h ∘ x) (g := fun x => g ∘ x))

private theorem comp_map' {α β γ : Type u} {x : IOEffects ξ ι α} {f : β → γ} {g : α → β} : map f (map g x) = map (f ∘ g) x :=
  (comp_map ..).symm

private theorem seq_pure (g : IOEffects ξ ι (α → β)) (x : α)
    : g.seq (fun _ => pure x) = g.map (fun h => h x) := by
  cases g
  all_goals first
    | (simp; done)
    | (unfold seq; congr; apply seq_pure)
    | (unfold seq; congr; rw [seq_pure, comp_map']; rfl)

private theorem seq_map_r {f : α → β} {mh : IOEffects ξ ι (β → γ)} {x : IOEffects ξ ι α}
    : (mh.seq fun () => map f x) = (map (· ∘ f) mh).seq fun () => x := by
  cases mh <;> first
    | simp [comp_map']; done
    | simp only [seq, map, comp_map', xBusRead.injEq, true_and]; rw [seq_map_r, comp_map']; rfl
    | simp only [seq, map, xBusWrite.injEq, true_and]; rw [seq_map_r]

private theorem seq_map_l {α β γ : Type u} {f : α → β} {mx : IOEffects ξ ι α} {mg : IOEffects ξ ι (β → γ)}
    : ((map (· ∘ f) mg).seq fun () => mx) = ((map Function.comp mg).seq fun _ => pure f).seq fun () => mx := by
  cases mg
  all_goals congr 3; simp only [comp_map', seq_pure]; rfl

private theorem map_seq_r {f : β → γ} {mg : IOEffects ξ ι (α → β)} {x : IOEffects ξ ι α}
    : map f (mg.seq fun () => x) = (map (Function.comp f) mg).seq fun () => x := by
  cases mg <;> first
    | simp [comp_map']; done
    | simp only [seq, map]; rw [map_seq_r]; simp only [comp_map']; rfl
    | simp only [seq, map]; rw [map_seq_r]

private theorem seq_assoc (x : IOEffects ξ ι α) (g : IOEffects ξ ι (α → β)) (h : IOEffects ξ ι (β → γ))
    : h.seq (fun _ => g.seq fun _ => x) = ((h.map Function.comp).seq fun _ => g).seq fun _ => x := by
  cases h <;> first
    | simp [map_seq_r]; done
    | simp only [seq, map, comp_map']; rw [seq_assoc]; simp only [comp_map', map_seq_r]; rfl
    | simp only [seq, map]; rw [seq_assoc]

instance : LawfulApplicative (IOEffects ξ ι) where
  map_const := rfl
  id_map := id_map
  seqLeft_eq x y := rfl
  seqRight_eq x y := rfl
  pure_seq f x := by simp
  map_pure := by simp
  seq_pure := seq_pure
  seq_assoc := seq_assoc

end

def sleepOne : IOEffects ξ ι α → IOEffects ξ ι α
| .sleep 1 _ next => next
| .sleep (k + 2) _ next => .sleep (k + 1) (Nat.succ_ne_zero _) next
| fx => fx

abbrev isSleep : IOEffects ξ ι α → Bool
| .sleep .. => true
| _ => false

end IOEffects
