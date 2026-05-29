import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- `Reads ξ ι α` wraps a value of type `α` in zero or more XBus or simple I/O reads. -/
inductive IOEffects.Reads (ξ : Type u) (ι : Type v) : Type x → Type _
/-- Just return a value immediately, without doing any reads. -/
| pure (a : α) : Reads ξ ι α
/-- `xBusRead pin next` represents a computation delayed until a value `pin` can be read;
  then `next` is the result of the computation as a function on the value read (possibly
  wrapped in more reads). -/
| xBusRead (pin : ξ) (next : Reads ξ ι (Integer → α)) : Reads ξ ι α
| simpleIORead (pin : ι) (next : Reads ξ ι (SimpleIOData → α)) : Reads ξ ι α

/-- `IOEffects ξ ι α` represents a value of type `α`, possibly delayed until sleep, or reads/writes/peeks from XBus pins happen.
  We also record reads and writes from simple I/O pins, although they don't block.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*/O pins.-/
inductive IOEffects (ξ : Type u) (ι : Type v) (α : Type x)
/-- Just do zero or more reads. -/
| ofReads : IOEffects.Reads ξ ι α → IOEffects ξ ι α
/-- We would like to be able to write data out of a pin (but only once, and after any reads happen).
  `reads` represents some data (`Integer`) to be thereafter written out of `outPin`, and
  the state (`α`) after the write. Both are wrapped in the same reads (and can depend on the values read). -/
| xBusWrite (outPin : ξ) (reads : IOEffects.Reads ξ ι (Integer × α))
/-- `xBusPoll pin next` represents a computation delayed until the value
  from XBus pin `pin` arrives (but without consuming the value);
  then `next` is the (pure) result thereafter.
  This is used to implement the `slx` instruction. -/
| xBusPoll (pin : ξ) (reads : IOEffects.Reads ξ ι α)
/-- Like `xBusWrite` but for a simple I/O write. -/
| simpleIOWrite (outPin : ι) (reads : IOEffects.Reads ξ ι (SimpleIOData × α))
/-- Wait for some number of time units, represented as a `Nat`. See also `xBusWrite`. -/
| sleep (reads : IOEffects.Reads ξ ι (Nat × α))

namespace IOEffects

def pure (a : α) : IOEffects ξ ι α :=
  .ofReads (.pure a)

instance [Inhabited α] : Inhabited (IOEffects ξ ι α) :=
  ⟨pure default⟩

def Reads.map (f : α → β) : Reads ξ ι α → Reads ξ ι β
  | .pure a => .pure (f a)
  | .xBusRead p next => .xBusRead p (map (f ∘ ·) next)
  | .simpleIORead p next => .simpleIORead p (map (f ∘ ·) next)

def _root_.Prod.mapSnd (f : α → β) : σ × α → σ × β :=
  Prod.map id f

def Reads.mapSnd (f : α → β) : Reads ξ ι (σ × α) → Reads ξ ι (σ × β) :=
  Reads.map fun (s, a) => (s, f a)

def map (f : α → β) : IOEffects ξ ι α → IOEffects ξ ι β
  | .ofReads reads => .ofReads (reads.map f)
  | .xBusWrite p reads => .xBusWrite p (reads.mapSnd f)
  | .xBusPoll p reads => .xBusPoll p (reads.map f)
  | .simpleIOWrite p reads => .simpleIOWrite p (reads.mapSnd f)
  | .sleep reads => .sleep (reads.mapSnd f)

def _root_.Function.swap (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

@[simp]
theorem Reads.sizeOf_map_eq_sizeOf {x : Reads ξ ι α} {f : α → β} : sizeOf (map f x) = sizeOf x := by
  induction x generalizing β
  all_goals first | rfl | rename_i ih; simp [map, ih]

/-- Thinking of `Reads` as a linked list, Append the effects of `ma ()` after the effects of `mf` -/
def Reads.seq (mf : Reads ξ ι (α → β)) (ma : Unit → Reads ξ ι α) : Reads ξ ι β :=
  match mf with
  | .pure f => map f (ma ())
  | .xBusRead pin next => .xBusRead pin (seq (map Function.swap next) ma)
  | .simpleIORead pin next => .simpleIORead pin (seq (map Function.swap next) ma)
termination_by sizeOf mf

private def seqReads (mf : Reads ξ ι (α → β)) (ma : IOEffects ξ ι α) : IOEffects ξ ι β :=
  match ma with
  | .ofReads reads => .ofReads (mf.seq fun () => reads)
  | .xBusWrite p reads => .xBusWrite p ((mf.map Prod.mapSnd).seq fun () => reads)
  | .xBusPoll p reads => .xBusPoll p (mf.seq fun () => reads)
  | .simpleIOWrite p reads => .simpleIOWrite p ((mf.map Prod.mapSnd).seq fun () => reads)
  | .sleep reads => .sleep ((mf.map Prod.mapSnd).seq fun () => reads)

/-- If `mf` and `ma ()` are both leaf effects, ignore the leaf effects of the latter. -/
def seq (mf : IOEffects ξ ι (α → β)) (ma : Unit → IOEffects ξ ι α) : IOEffects ξ ι β :=
  match mf with
  | .ofReads rf => seqReads rf (ma ())
  | .xBusWrite p reads => .xBusWrite p sorry
  | .xBusPoll pin reads => sorry
  | .simpleIOWrite p reads => sorry
  | .sleep reads => sorry

instance : Applicative (IOEffects ξ ι) where
  map := map
  pure := pure
  seq := seq
