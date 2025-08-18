import Shenzhen.Integer

structure ConditionalState where
  posEnabled : Bool
  negEnabled : Bool
deriving Repr

inductive Pin (ξ : Type u) (ι : Type v)
| xBus (pin : ξ) | simpleIO (pin : ι)
deriving Repr

namespace Instruction

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
| .xBus i => some (.xBus i)
| .simpleIO i => some (.simpleIO i)
| .null | .internal _ => none

inductive RegOrInt (ρ : Type v) (ξ : Type w) (ι : Type x)
/-- A reference to a register. -/
| reg : Reg ρ ξ ι → RegOrInt ..
/-- An integer literal. -/
| int : Integer → RegOrInt ..
deriving Repr

@[inline] def RegOrInt.pin? : RegOrInt ρ ξ ι → Option (Pin ξ ι)
| .reg r => r.pin?
| .int _ => none

namespace Notation

/-! Notation to make writing `Instruction` easier. -/

set_option hygiene false
scoped notation "R" => Instruction.Reg ρ ξ ι
scoped notation "R/I" => Instruction.RegOrInt ρ ξ ι

end Instruction.Notation

open Instruction.Notation in
/-- All of the MC-series instructions.
Type parameters:
- `Λ` is for *l*abels
- `ρ` is for (internal chip) *r*egisters
- `ξ` is for *X*bus pins
- `ι` is for *I*O pins. -/
inductive Instruction (Λ : Type u) (ρ : Type v) (ξ : Type w) (ι : Type x)
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

/-- Count the maximum number of pins this instruction could read from/write to. -/
@[reducible]
def Instruction.numArgs : Instruction Λ ρ ξ ι → Nat
| .nop | .jmp _ | .slx _ | .not => 0
| .slp _ | .add _ | .sub _ | .mul _ | .dgt _ => 1
| .mov .. | .dst .. | .teq .. | .tgt .. | .tlt .. | .tcp .. => 2

@[inline]
def Instruction.arg : (instr : Instruction Λ ρ ξ ι) → Fin instr.numArgs → RegOrInt ρ ξ ι
| .nop | .jmp _ | .slx _ | .not =>
  Fin.elim0
| .slp x | .add x | .sub x | .mul x | .dgt x =>
  fun | 0 => x
| .dst x y | .teq x y | .tgt x y | .tlt x y | .tcp x y =>
  fun | 0 => x
      | 1 => y
| .mov x y =>
  fun | 0 => x
      | 1 => .reg y

@[reducible]
def Instruction.FnType.{u}
    (σ : Type u) (δ : Type u) {Λ : Type u} {ξ : Type u} {ρ : Type u} {ι : Type u} : Instruction Λ ρ ξ ι → Type u
| .nop | .not => σ
| .mov .. => δ → Reg ρ ξ ι → σ
| .jmp .. => Λ → σ
| .slx _ => ξ → σ
| .slp _ | .add _ | .sub _ | .mul _ | .dgt _ => δ → σ
| .dst .. | .teq .. | .tgt .. | .tlt .. | .tcp .. => δ → δ → σ
