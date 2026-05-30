module

public import Shenzhen.Integer
public import Shenzhen.Integer.Meta

public section

inductive ConditionalFlag | none | pos | neg | once
deriving Repr, Inhabited

structure ConditionalState (numInstr : Nat) where
  /-- Whether an instruction has been executed already. Used
  to implement the `@` conditional (`ConditionalFlag.once`). -/
  hasRun : Vector Bool numInstr
  posEnabled : Bool
  negEnabled : Bool
deriving Repr

def ConditionalState.boolFlags : ConditionalState m → Bool × Bool
| ⟨_, pos, neg⟩ => (pos, neg)

def ConditionalFlag.isEnabled
    (flag : ConditionalFlag) (cond : ConditionalState m)
    (ip : Fin m) : Bool :=
  match flag with
  | .none => true
  | .pos => cond.posEnabled
  | .neg => cond.negEnabled
  | .once => !cond.hasRun[ip]

inductive Pin (ξ : Type u) (ι : Type v)
| xBus (pin : ξ) | simpleIO (pin : ι)
deriving Repr, DecidableEq, BEq

end

namespace Instruction
public section

inductive Reg (ρ : Type v) (ξ : Type w) (ι : Type x)
/-- An internal chip register, like `acc` or `dat`. -/
| internal : ρ → Reg ..
/-- An XBus pin register. -/
| xBus : ξ → Reg ..
/-- A simple I/O pin register. -/
| simpleIO : ι → Reg ..
/-- The `null` pseudo-register. -/
| null
deriving Repr

@[inline] def Reg.pin? : Reg ρ ξ ι → Option (Pin ξ ι)
| .xBus x => some (.xBus x)
| .simpleIO i => some (.simpleIO i)
| .null | .internal _ => none

@[inline] def Reg.ofPin : Pin ξ ι → Reg ρ ξ ι
| .xBus x => .xBus x
| .simpleIO i => .simpleIO i

inductive RegOrInt (ρ : Type v) (ξ : Type w) (ι : Type x)
/-- A reference to a register. -/
| reg : Reg ρ ξ ι → RegOrInt ..
/-- An integer literal. -/
| int : Integer → RegOrInt ..
deriving Repr

namespace RegOrInt

@[inline] def pin? : RegOrInt ρ ξ ι → Option (Pin ξ ι)
| .reg r => r.pin?
| .int _ => none

@[inline] def ofPin : Pin ξ ι → RegOrInt ρ ξ ι :=
  fun p => .reg (.ofPin p)

-- Some convenience constructors so I don't have to type `.reg (.internal .acc)` all the time

@[inline, expose, match_pattern] def internal : ρ → RegOrInt ρ ξ ι :=
  .reg ∘ .internal

@[inline, expose, match_pattern] def xBus : ξ → RegOrInt ρ ξ ι :=
  .reg ∘ .xBus

@[inline, expose, match_pattern] def simpleIO : ι → RegOrInt ρ ξ ι :=
  .reg ∘ .simpleIO

@[inline, expose, match_pattern] def null : RegOrInt ρ ξ ι :=
  .reg .null

end RegOrInt

/-! Notation to make writing `Instruction` easier. -/

set_option hygiene false
local notation "R" => Instruction.Reg ρ ξ ι
local notation "R/I" => Instruction.RegOrInt ρ ξ ι

/-- All of the MC-series instructions.
Type parameters:
- `Λ` is for *l*abels
- `ρ` is for (internal chip) *r*egisters
- `ξ` is for *X*bus pins
- `ι` is for *I*O pins. -/
inductive _root_.Instruction (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x)
-- Basic instructions
| nop
| mov : R/I → R → Instruction ..
| jmp : Λ → Instruction ..
| slp : R/I → Instruction ..
| slx : ξ → Instruction ..
-- Arithmetic instructions
| add : R/I → Instruction ..
| sub : R/I → Instruction ..
| mul : R/I → Instruction ..
| not
| dgt : R/I → Instruction ..
| dst : R/I → R/I → Instruction ..
-- Test instructions
| teq : R/I → R/I → Instruction ..
| tgt : R/I → R/I → Instruction ..
| tlt : R/I → R/I → Instruction ..
| tcp : R/I → R/I → Instruction ..
-- Undocumented instruction
-- | gen : ι → R/I → R/I → Instruction .. -- TODO: add this back in
deriving Inhabited, Repr

-- TODO: remove this dead code
def mapΛ (instr : Instruction (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x))
    (f : Λ → Λ') : Instruction Λ' ρ ξ ι :=
  match instr with
  | .jmp l => .jmp (f l)
  | .nop => .nop
  | .mov x y => .mov x y
  | .slp x => .slp x | .slx x => .slx x
  | .add x => .add x | .sub x => .sub x | .mul x => .mul x | .not => .not
  | .dgt x => .dgt x | .dst x y => .dst x y
  | .teq x y => .teq x y | .tgt x y => .tgt x y | .tlt x y => .tlt x y | .tcp x y => .tcp x y

open Instruction in
@[specialize] def mapΛM {m : Type u → Type v} [Functor m] [Pure m]
    {Λ : Type u} {Λ' : Type u} {ρ : Type u} {ξ : Type u} {ι : Type u}
    (f : Λ → m Λ') (instr : Instruction Λ ρ ξ ι)
    : m (Instruction Λ' ρ ξ ι) :=
  match instr with
  | .jmp l => jmp <$> f l
  | .nop => pure <| nop
  | .mov x y => pure <| mov x y
  | .slp x => pure <| slp x | .slx x => pure <| slx x
  | .add x => pure <| add x | .sub x => pure <| sub x | .mul x => pure <| mul x | .not => pure <| not
  | .dgt x => pure <| dgt x | .dst x y => pure <| dst x y
  | .teq x y => pure <| teq x y | .tgt x y => pure <| tgt x y | .tlt x y => pure <| tlt x y | .tcp x y => pure <| tcp x y
