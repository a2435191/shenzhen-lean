import Shenzhen.Integer
import Shenzhen.SimpleIOData

/-- `IOEffects ξ ι α` represents a value of type `α`, possibly delayed until sleep, or reads/writes/peeks from XBus pins happen.
  We also record reads and writes from simple I/O pins, although they don't block.
  - `ξ` is the type of *X*Bus pins.
  - `ι` is the type of simple *I*/O pins.-/
inductive IOEffects (ξ : Type u) (ι : Type v) : Type x → Type _
/-- Just return a value immediately, without doing any effects.
  This is a final state (no more effects after this point, i.e.
  no constructor parameters of type `IOEffects`). -/
| pure (a : α)                                                     : IOEffects ξ ι α
/-- Read a value (possibly blocking) from pin `pin`, and then do
  something with it. That function
  (the `Integer → α` part) is wrapped in another `IOEffects`
  representing the next state. -/
| xBusRead (pin : ξ) (next : IOEffects ξ ι (Integer → α))          : IOEffects ξ ι α
/-- `d` is some data to be thereafter written out of `outPin`
  (also blocking), and `next` is the state immediately after
  the write.
  Note that this is a final state since `next` is pure. -/
| xBusWrite (outPin : ξ) (d : Integer) (next : α)                  : IOEffects ξ ι α
/-- Wait until the value from XBus pin `pin` arrives,but don't
  consume the value). Then `next` is the state after the value
  arrives. This is used to implement the `slx` instruction.

  Note that this is a final state. -/
| xBusPoll (pin : ξ) (next : α)                                    : IOEffects ξ ι α
/-- Like `xBusRead` but non-blocking. -/
| simpleIORead (pin : ι) (next : IOEffects ξ ι (SimpleIOData → α)) : IOEffects ξ ι α
/-- Like `xBusWrite` but non-blocking. Note that this is a
  final state. -/
| simpleIOWrite (outPin : ι) (d : SimpleIOData) (next : α)         : IOEffects ξ ι α
/-- Wait for `n` time units. `n ≠ 0` because `pure` already exists.
  `next` is the (pure) state after we are done waiting, so
  this is a final state. -/
| sleep (n : Nat) (h : n ≠ 0) (next : α)                           : IOEffects ξ ι α

namespace IOEffects

/-! ## Misc. functions -/

instance [Inhabited α] : Inhabited (IOEffects ξ ι α) :=
  ⟨.pure default⟩

/-- In `sleep` or `xBusPoll` state -/
abbrev isSleep : IOEffects ξ ι α → Bool
| .sleep .. | .xBusPoll .. => true
| _ => false

/-- Advance `.sleep` states by one time unit. Leave `.xBusPoll` states alone. -/
def advanceSleep (fx : IOEffects ξ ι α) (h : fx.isSleep = true) : IOEffects ξ ι α :=
  match fx with
  | .xBusPoll .. => fx
  | .sleep 1 _ next => .pure next
  | .sleep (k + 2) _ next => .sleep (k + 1) (Nat.succ_ne_zero _) next

/-! ## `map` and `seq` -/

@[simp]
def map (f : α → β) : IOEffects ξ ι α → IOEffects ξ ι β
  | .pure a => .pure (f a)
  | .xBusRead p next => .xBusRead p (map (f ∘ ·) next)         -- recurse
  | .xBusWrite p d a => .xBusWrite p d (f a)
  | .xBusPoll p a => .xBusPoll p (f a)
  | .simpleIORead p next => .simpleIORead p (map (f ∘ ·) next) -- recurse
  | .simpleIOWrite p d a => .simpleIOWrite p d (f a)
  | .sleep n h a => .sleep n h (f a)

/-! Needed for proof of termination of `seq` below -/
@[simp]
theorem sizeOf_map_eq_sizeOf {f : α → β} {x : IOEffects ξ ι α} : sizeOf (map f x) = sizeOf x := by
  induction x generalizing β <;> simp_all [map]

/-- Apply the final constructor `ofPure` to states that have `.pure` as their final constructor. -/
def tryDeep (ofPure : {τ : Type u} → τ → IOEffects ξ ι τ) : IOEffects ξ ι α → IOEffects ξ ι α
  | .pure a => ofPure a
  -- Non-final constructors just recurse
  | .xBusRead pin next => .xBusRead pin (tryDeep ofPure next)
  | .simpleIORead pin next => .simpleIORead pin (tryDeep ofPure next)
  -- All non-`pure` final constructors ignore
  | other => other

/-- Get `f ← mf`, then apply it to `a ← (ma ())`. If `f` and `x` both write, keep the write from `f`. -/
@[simp]
def seq (mf : IOEffects ξ ι (α → β)) (ma : Unit → IOEffects ξ ι α) : IOEffects ξ ι β :=
  match mf with
  | .pure f => map f (ma ())
  -- Non-pure final constructors
  | .xBusWrite p d f =>
    -- i.e. prefer the state structure from `ma`, but if it's pure at the end
    -- make it a write with `p` and `d`
    tryDeep (.xBusWrite p d) (map f (ma ()))
  | .simpleIOWrite p d f => tryDeep (.simpleIOWrite p d) (map f (ma ()))
  | .xBusPoll p f => tryDeep (.xBusPoll p) (map f (ma ()))
  | .sleep n h f => tryDeep (.sleep n h) (map f (ma ()))
  -- The recursive a.k.a. non-final a.k.a. read constructors just recurse.
  -- I think the best way to do this is map `Function.swap` across `next` first
  | .xBusRead pin next => .xBusRead pin (seq (map Function.swap next) ma)
  | .simpleIORead pin next => .simpleIORead pin (seq (map Function.swap next) ma)
termination_by sizeOf mf -- hint

/-! ## Now we prove `seq` and `map` are lawful
  This approach was tested in `ReadWrite.lean`. Avoid the notation for `seq`, `pure`, and `bind`
  here because unfolding it proofs is annoying. -/

/-! ### First, helper theorems showing `tryDeep` respects `seq` and `map` and is idempotent. -/
section

variable {α β : Type u} {f : α → β} {ofPure ofPure' : ∀ {τ : Type u}, τ → IOEffects ξ ι τ} {x : IOEffects ξ ι α}

theorem map_tryDeep
  (map_ofPure : ∀ {τ τ' : Type u} (t : τ) (h : τ → τ'), map h (ofPure t) = ofPure (h t))
    : map f (tryDeep ofPure x) = tryDeep ofPure (map f x) := by
  induction x generalizing β
  all_goals first
    | rfl -- non-pure final constructors
    | simp [tryDeep, map, map_ofPure]; done -- pure
    | simp only [map, tryDeep]; rename_i ih; rw [ih] -- reads

theorem tryDeep_idempotent
    (hf : ∀ {α'} (a : α'), tryDeep ofPure' (ofPure a) = ofPure a)
    : tryDeep ofPure' (tryDeep ofPure x) = tryDeep ofPure x := by
  induction x
  all_goals first
    | rfl -- non-pure final constructors
    | simp only [tryDeep]; apply hf; done -- pure
    | simp only [tryDeep]; rename_i _ ih; rw [ih] -- reads

theorem seq_tryDeep {α} {β} {g : IOEffects ξ ι (α → β)} {x : IOEffects ξ ι α}
    (hseq_ofPure : ∀ {τ τ' : Type u} (t : IOEffects ξ ι τ) (h : τ → τ'), ((ofPure h).seq fun _ => t) = tryDeep ofPure (map h t))
    (hmap : ∀ {τ τ' : Type u} (t : τ) (h : τ → τ'), map h (ofPure t) = ofPure (h t))
    : seq (tryDeep ofPure g) (fun _ => x) = tryDeep ofPure (seq g fun _ => x) := by
  -- can't use induction tactic because `g` is parametrized by `α → β`, a function type
  cases g
  all_goals first
    | simp [tryDeep, seq, tryDeep_idempotent]; done -- non-pure final constructors
    | simp only [tryDeep, seq]; apply hseq_ofPure -- pure
    | simp only [tryDeep, seq]; rw [map_tryDeep hmap, seq_tryDeep] <;> assumption -- reads (recurse)

end
