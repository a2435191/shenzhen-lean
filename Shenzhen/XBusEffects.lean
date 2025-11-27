import Shenzhen.Instruction

/-- `XBusEffects.Basic` wraps values of type `α` in a functor that
  records pin read and write actions within a chip with XBus pins.
  - `ξ` is the type of *X*Bus pins.
  - `δ` is the type of *d*ata read over XBus pins (probably `Integer`).
  The constructors guarantee that effects are any amount of reads, optionally followed by
  a single write. -/
inductive XBusEffects.Basic (ξ : Type u) (δ : Type v) (α : Type w)
-- /-- Wrap a value in `XBusEffects` without signaling the need for a read or write. -/
| pure (next : α)
-- /-- `write pin d a` represents some data `d` being written to
--  XBus pin `pin`. Then `a` is the (pure) state after performing the write. -/
| write (pin : ξ) (d : δ) (next : α)
deriving Inhabited

-- Pure, write, and any further read(s), but not a peek, may happen after a read.
-- All other operations are terminal.
-- [P]ure, [W]rite, [R]ead, p[E]ek

/-- Like `XBusEffects.Basic` but includes a separate `peek` operation (that cannot be composed with reads or writes). -/
inductive XBusEffects.WithRead (ξ : Type u) (δ : Type v) (α : Type w)
| basic : XBusEffects.Basic ξ δ α → XBusEffects.WithRead ξ δ α

inductive XBusEffects (ξ : Type u) (δ : Type v) (α : Type w)
/-- `read pin next` represents a computation delayed until a value `d`
 from XBus pin `pin` can be read; then `next d` is the result of the computation. -/
| read (pin : ξ) (next : δ → XBusEffects ξ δ α)
/-- `peek pin next` represents a computation delayed until the value
  from XBus pin `pin` is known; then `next` is the (pure) state after performing the peek.
  This is used to implement the `slx` operation. -/
| peek (pin : ξ) (next : α)

deriving Inhabited

namespace XBusEffects.WithRead

-- Lift the constructors of `Basic` to `WithRead`

def pure (a : α) : WithRead ξ δ α :=
  basic (.pure a)

def write (pin : ξ) (d : δ) (a : α) :=
  basic (.write pin d a)

/-- If there's not already been a write, write `toWrite` out of `pinToWrite`.
    Otherwise, keep the old write and ignore `pin` and `d`. -/
def writeIfNotAlreadyWritten (pinToWrite : ξ) (toWrite : δ) : WithRead ξ δ α → WithRead ξ δ α
| .pure a => .write pinToWrite toWrite a
| .write writtenPin written a => .write writtenPin written a
| .read readPin next =>
  .read readPin fun readData =>
    writeIfNotAlreadyWritten pinToWrite toWrite (next readData)

def bind : WithRead ξ δ α → (α → WithRead ξ δ β) → WithRead ξ δ β
| .pure a, f => f a
| .read pin next, f => .read pin fun d => bind (next d) f
| .write pin d a, f =>
  -- if `f` does a write, clobber the existing write
  writeIfNotAlreadyWritten pin d (f a)

end WithRead

-- Lift the constructors of `WithRead` to `XBusEffects`

def pure (a : α) : XBusEffects ξ δ α :=
  .readWrite (.pure a)

def write : ξ → δ → α → XBusEffects ξ δ α
| pin, d, a => .readWrite (.write pin d a)

def read : ξ → (δ → WithRead ξ δ α) → XBusEffects ξ δ α
| pin, next => .readWrite (.read pin next)

def bind : XBusEffects ξ δ α → (α → XBusEffects ξ δ β) → XBusEffects ξ δ β
| .readWrite rw, f => .readWrite <| rw.bind fun a => sorry
| .peek pin a, f => sorry

instance : Monad (XBusEffects ξ δ) where
  pure := pure
  bind := bind

@[inline] def isPure : XBusEffects ξ δ α → Bool
| .pure _ => true
| _ => false

instance [ToString ξ] [ToString δ] [ToString α] [OfNat δ 37] : ToString (XBusEffects ξ δ α) :=
  ⟨go⟩
where
  go
  | .pure a => s!".pure ({toString a})"
  | .write pin d next => s!".write {pin} {d} ({next})"
  | .read pin next => s!".read {pin} (fun | 37 => {go (next 37)} | ⋯)"
  | .peek pin next => s!".peek {pin} ({next})"

end XBusEffects
