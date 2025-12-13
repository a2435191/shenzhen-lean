import Shenzhen.Instruction

/-- `Read?` represents a value of type `α`, possibly delayed until one or two reads from XBus pins happen.
  - `ξ` is the type of *X*Bus pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`). -/
inductive XBusEffects.Read? (ξ : Type u) (δ : Type v) (α : Type w)
/-- Just return a value without reading anything. -/
| none (a : α)
/-- `read₁ pin next` represents a computation delayed until a value `d`
  from XBus pin `pin` can be read; then `next d` is the result of the computation. -/
| read₁ (pin : ξ) (ofData : δ → α)
/-- `read₂ pin₁ pin₂ next` represents a computation delayed until values `d₁` and `d₂` (in that order)
  from XBus pins `pin₁` and `pin₂`, respectively, can be read; then `next d₁ d₂` is the result of the computation. -/
| read₂ (pin₁ pin₂ : ξ) (ofData : δ → δ → α)
deriving Inhabited

/-- `XBusEffects` represents a value of type `α`, possibly delayed until one or two reads from XBus pins happen.
  - `ξ` is the type of *X*Bus pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`).

  The constructors guarantee that effects are either zero, one, or two reads, optionally followed by
  a single write; or alternatively a poll operation that waits for incoming data on a pin and does nothing with it. -/
inductive XBusEffects (ξ : Type u) (δ : Type v) (α : Type w)
/-- Don't do a write or poll, just read from zero, one, or two pins. -/
| ofRead? : XBusEffects.Read? ξ δ α → XBusEffects ξ δ α
/-- Get `(d, a)` after reading zero, one, or two pins, where `d` is some data to be
  thereafter written out of `outPin`, and `a` is returned after the write. -/
| write (outPin : ξ) : XBusEffects.Read? ξ δ (δ × α) → XBusEffects ξ δ α
/-- `poll pin next` represents a computation delayed until the value
  from XBus pin `pin` arrives; then `next` is the (pure) result.
  This is used to implement the `slx` operation. -/
| poll (pin : ξ) (a : α)
deriving Inhabited

namespace XBusEffects

namespace Read?

def pure (a : α) : Read? ξ δ α :=
  .none a

def map (f : α → β) : Read? ξ δ α → Read? ξ δ β
| .none a => .none (f a)
| .read₁ pin next => .read₁ pin (f ∘ next)
| .read₂ pin₁ pin₂ next => .read₂ pin₁ pin₂ (f <| next · ·)

instance : Pure (Read? ξ δ) := ⟨pure⟩

instance : Functor (Read? ξ δ) where
  map := map

/-- Map all types across `Read?`. Note that the function for `δ` must take new to old. -/
def map₃ (f : ξ → ξ') (gInv : δ' → δ) (h : α → α') : Read? ξ δ α → Read? ξ' δ' α'
| .none a => .none (h a)
| .read₁ pin next => .read₁ (f pin) (h ∘ next ∘ gInv)
| .read₂ pin₁ pin₂ next => .read₂ (f pin₁) (f pin₂) fun d₁ d₂ => h (next (gInv d₁) (gInv d₂))

@[reducible, simp] def isRead₂ : Read? ξ δ α → Prop
| .read₂ .. => True
| _ => False

/-- Sequence two `Read?`s, given that they both read at most once. -/
def seq (r₁ : Read? ξ δ α) (r₂ : Read? ξ δ β) (h₁ : ¬r₁.isRead₂) (h₂ : ¬r₂.isRead₂) : Read? ξ δ (α × β) :=
  match r₁, r₂ with
  | .read₂ .., _ | _, read₂ .. => by exfalso; simp at h₁ h₂
  | .none a, .none b => .none (a, b)
  | .none a, .read₁ q nextB => .read₁ q (a, nextB ·)
  | .read₁ p nextA, .none b => .read₁ p (nextA ·, b)
  | .read₁ p nextA, .read₁ q nextB => .read₂ p q (nextA ·, nextB ·)

end Read?

/-- Return some `α` without any XBus I/O: don't read, write, or poll. -/
def pure (a : α) : XBusEffects ξ δ α :=
  .ofRead? (.none a)

def map (f : α → β) : XBusEffects ξ δ α → XBusEffects ξ δ β
| .ofRead? r => .ofRead? (f <$> r)
| .write out r => .write out <| (fun (d, a) => (d, f a)) <$> r
| .poll pin a => .poll pin (f a)

instance : Pure (XBusEffects ξ δ) where
  pure := .pure

instance : Functor (XBusEffects ξ δ) where
  map := map

/-- Map all types across `XBusEffects`. Note that both directions are required for `δ ↔ δ'`. -/
def map₃ (f : ξ → ξ') (g : δ → δ') (gInv : δ' → δ) (h : α → α') : XBusEffects ξ δ α → XBusEffects ξ' δ' α'
| .ofRead? r => .ofRead? (r.map₃ f gInv h)
| .write out r => .write (f out) (r.map₃ f gInv (Prod.map g h))
| .poll pin a => .poll (f pin) (h a)

def clearData (dummy : Nat) [OfNat δ dummy] : XBusEffects ξ δ α → XBusEffects ξ Unit α :=
  map₃ id (fun _ => ()) (fun () => OfNat.ofNat dummy) id

variable [ToString ξ] [ToString α]

instance : ToString (Read? ξ Unit α) where
  toString
  | .none a => s!".none {a}"
  | .read₁ pin next => s!".read₁ {pin} {next ()}"
  | .read₂ pin₁ pin₂ next => s!".read₂ {pin₁} {pin₂} {next () ()}"

instance : ToString (XBusEffects ξ Unit α) where
  toString
  | .ofRead? r => s!".ofRead? <| {r}"
  | .write out r => s!".write {out} <| {r}"
  | .poll pin a => s!".poll {pin} {a}"

def clearToString (dummy := 37) [OfNat δ dummy] : XBusEffects ξ δ α → String :=
  toString ∘ clearData (OfNat.ofNat dummy)

variable [ToString δ]
instance : ToString (Read? ξ δ α) where
  toString
  | .none a => s!".none {a}"
  | .read₁ pin _ => s!".read₁ {pin} …"
  | .read₂ pin₁ pin₂ _ => s!".read₂ {pin₁} {pin₂} …"

instance : ToString (XBusEffects ξ δ α) where
  toString
  | .ofRead? r => s!".ofRead? <| {r}"
  | .write out r => s!".write {out} <| {r}"
  | .poll pin a => s!".poll {pin} {a}"


end XBusEffects
