-- https://jaredkrinke.itch.io/sic-1

namespace SIC1

@[reducible] def Index := UInt8
@[reducible] def Data := Int8

namespace Index

@[match_pattern, simp] def max  : Index := 252

@[match_pattern, simp] def «in» : Index := 253

@[match_pattern, simp] def out  : Index := 254

@[match_pattern, simp] def halt : Index := 255

end Index

abbrev Mem.size := 256
@[simp] abbrev Mem.accessibleSize := 253

deriving instance Repr for ByteArray

structure Mem where
  bytes : ByteArray
  hsize : bytes.size = Mem.accessibleSize := by decide
deriving Repr

namespace Mem

/-- All zeroes -/
def default : Mem where
  bytes := ⟨Array.replicate accessibleSize 0⟩
  hsize := by simp [ByteArray.size]

instance : Inhabited Mem := ⟨default⟩

end Mem

/-- Possibly read from `IN`. -/
inductive ProgramIO.Read? (α : Type u)
/-- Don't read any value from `IN`. -/
| none (a : α)
/-- Wait on a value from `IN`. -/
| readIn (ofData : Data → α)
deriving Inhabited

/-- Halt or write to `OUT` or read from `IN`. -/
inductive ProgramIO (α : Type u)
/-- Don't write anything, just possibly read from `IN`. -/
| justRead : ProgramIO.Read? α → ProgramIO α
/-- After possibly reading from `IN`, write some `Data` to `OUT` and return some `α`. -/
| writeOut : ProgramIO.Read? (Data × α) → ProgramIO α
/-- Halt the program. -/
| halted
deriving Inhabited

namespace ProgramIO

@[simp]
def Read?.map (f : α → β) : Read? α → Read? β
| .none a => .none (f a)
| .readIn g => .readIn (f ∘ g)

instance : Functor Read? where
  map := .map

theorem Read?.map_eq : Read?.map f mx = f <$> mx := rfl

instance : LawfulFunctor Read? where
  map_const := rfl
  id_map := by intros; dsimp [Functor.map]; split <;> rfl
  comp_map := by intros; dsimp [Functor.map]; split <;> rfl

@[simp]
def Read?.seq : Read? (α → β) → (Unit → Read? α) → Read? β :=
  fun mf mx =>
    let mx := mx ()
    match mf, mx with
    | .none f, .none x => .none (f x)
    | .none f, .readIn xNext => .readIn (f ∘ xNext)
    | .readIn fNext, .none x => .readIn (fNext · x)
    | .readIn fNext, .readIn xNext =>
      .readIn fun d => fNext d (xNext d)

instance : Applicative Read? where
  pure := .none
  seq := .seq

theorem Read?.pure_eq : Read?.none a = pure a := rfl
theorem Read?.seq_eq : Read?.seq mf mx = mf <*> (mx ()) := rfl

instance : LawfulApplicative Read? where
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := by
    intros
    dsimp [Seq.seq, Functor.map, pure]
    split <;> simp_all
  map_pure := by intros; rfl
  seq_pure := by
    intros
    dsimp [Seq.seq, Functor.map, pure]
    split <;> simp_all <;> funext; dsimp
  seq_assoc := by
    intros
    simp only [Seq.seq, Functor.map, Read?.seq, Read?.map]
    (repeat' split at *)
    <;> simp_all only [
      Read?.readIn.injEq, Read?.none.injEq,
      Function.comp_apply, reduceCtorEq]
    <;> (rename_i h; rewrite [←h]; rfl)

instance : Functor ProgramIO where
  map f
  | .justRead r => .justRead (f <$> r)
  | .writeOut r => .writeOut ((fun (d, a) => (d, f a)) <$> r)
  | .halted => .halted

instance : LawfulFunctor ProgramIO where
  map_const := rfl
  id_map := by
    intros
    dsimp [Functor.map]
    (repeat' split) <;> rfl
  comp_map := by
    intros
    dsimp [Functor.map]
    (repeat' split) <;> rfl

def _root_.Applicative.map₂ [Applicative m] (ma : m α) (mb : m β) (f : α → β → γ) : m γ :=
  f <$> ma <*> mb

instance : Applicative ProgramIO where
  pure a := .justRead (.none a)
  seq mf ma := match mf with
    | .halted => .halted
    | .justRead rf =>
      match ma () with
      | .halted => .halted
      | .justRead ra => .justRead (rf <*> ra)
      | .writeOut ra => .writeOut <|
        Applicative.map₂ rf ra fun f (d, a) => (d, f a)
    | .writeOut rf =>
      match ma () with
      | .halted => .halted
      | .justRead ra => .writeOut <|
        Applicative.map₂ rf ra fun (d, f) a => (d, f a)
      | .writeOut ra => .writeOut <|
        -- Overwrite the previously written data
        Applicative.map₂ rf ra fun (_, f) (d, a) => (d, f a)

section

variable {α : Type u} {β : Type v}

def prodMapR : Data × (α → β) → α → Data × β :=
  fun (d, f) a => (d, f a)

theorem eq_prodMapR : (fun x a => (x.1, x.2 a)) = @prodMapR α β :=
  rfl

def prodMapL : (α → β) → Data × α → Data × β :=
  fun f (d, a) => (d, f a)

theorem eq_prodMapL : (fun x a => (a.1, x a.2)) = @prodMapL α β :=
  rfl

def prodMap' : Data × (α → β) → Data × α → Data × β :=
  fun (_, f) (d, a) => (d, f a)

theorem eq_prodMap' : (fun x a => (a.1, x.2 a.2)) = @prodMap' α β :=
  rfl

end

instance : LawfulApplicative ProgramIO where
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := by
    rintro α β f (mx|mx)
    all_goals dsimp [pure, Seq.seq, Functor.map, -Read?.seq]
    all_goals
      congr
      -- We already showed this in the `LawfulApplicative ProgramIO.Read?` instance
      show pure _ <*> mx = _ <$> mx
      apply pure_seq
  map_pure := by intros; rfl
  seq_pure := by
    rintro α β (mf|mf) a
    all_goals
      dsimp [pure, Seq.seq, Functor.map, -Read?.seq, -Read?.map]
      <;> (congr 1; show _ <*> pure a = _ <$> mf)
    · apply seq_pure
    · rw [seq_pure]
      dsimp [Functor.map] <;> (repeat' split at *) <;> simp_all
      <;> (rename_i h; rw [←h]) <;> rfl
  seq_assoc := by
    simp only [Seq.seq, Functor.map, Applicative.map₂]
    rintro α β γ (ma|ma) (mf|mf) (mg|mg) <;> try rfl
    all_goals
      (simp only <;> congr 1)
      simp only [Read?.map_eq, Read?.seq_eq]
      try simp only [eq_prodMapR, eq_prodMapL, eq_prodMap']
    any_goals rw [←seq_assoc]
    all_goals
      repeat rw [←pure_seq]
      simp only [seq_assoc, map_pure, seq_pure]
      simp only [pure_seq, Functor.map_map]
      rfl

end ProgramIO

structure State where
  mem : Mem
  idx : Index
deriving Inhabited, Repr

namespace Mem

def getByte (mem : Mem) (idx : Index) : Data :=
  if h : idx.toNat < Mem.accessibleSize then
    (mem.bytes.get idx.toNat (mem.hsize ▸ h)).toInt8
  else 0

theorem le_max_iff {i : Index} : i ≤ .max ↔ i < 253 := by
  rw [Index.max, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt]
  exact Nat.lt_add_one_iff.symm

def setByte (mem : Mem) (i : Index) (val : Data) (h : i ≤ .max := by decide) : Mem where
  bytes := mem.bytes.set i.toNat val.toUInt8 <| by
    rwa [mem.hsize, show accessibleSize = UInt8.toNat 253 by rfl,
        ←UInt8.lt_iff_toNat_lt, ←le_max_iff]
  hsize := by
    rw [ByteArray.size, ByteArray.set, Array.size_set,
        ←ByteArray.size, mem.hsize]

instance : ToString Mem where
  toString | { bytes, .. } => toString bytes

end Mem

def State.step : State → ProgramIO State
| ⟨mem, instrAddress⟩ =>
  let a : Index := Int8.toUInt8 (mem.getByte instrAddress)
  let b : Index := Int8.toUInt8 (mem.getByte (instrAddress + 1))
  let c : Index := Int8.toUInt8 (mem.getByte (instrAddress + 2))

  let memAB : ProgramIO.Read? (Data × Data) :=
    match a, b with
    | .in, .in =>
      /- erratum #4: reading from `@IN` multiple times
        only consumes a single input -/
      .readIn fun x => (x, x)
    | .in, _ =>
      .readIn (·, mem.getByte b)
    | _, .in =>
      .readIn (mem.getByte a, ·)
    | _, _ =>
      .none (mem.getByte a, mem.getByte b)

  let memAB.apply {α : Type} (fn : Data → Index → α) : ProgramIO.Read? α :=
    memAB <&> fun (memA, memB) =>
      let res := memA - memB
      let instrAddress' := if res ≤ 0 then c else instrAddress + 3
      fn res instrAddress'

  -- Write `res := mem[A] - mem[B]` to address `A`
  if h : a ≤ .max then
    .justRead <| memAB.apply fun res instrAddress' =>
      ⟨mem.setByte a res h, instrAddress'⟩
  else
    match a with
    | .halt => .halted
    | .in =>
      .justRead <| memAB.apply fun _ instrAddress' =>
        ⟨mem, instrAddress'⟩
    | .out =>
      .writeOut <| memAB.apply fun res instrAddress' =>
        ⟨res, mem, instrAddress'⟩
    | _ => unreachable!

def State.eval (inputs : List Data) (init : State) (maxIters : Nat := 1024) : List Data :=
  (go inputs [] maxIters init).reverse
where go (inputs acc : List Data) fuel (state : State) :=
  match fuel with
  | 0 =>
    acc
  | k + 1 =>
    let io := state.step
    match io with
    | .halted => acc
    | .justRead (.none state') => go inputs acc k state'
    | .justRead (.readIn next) =>
      match inputs with
      | [] => acc
      | inp :: inputs' => go inputs' acc k (next inp)
    | .writeOut (.none (d, state')) => go inputs (d :: acc) k state'
    | .writeOut (.readIn next) =>
      match inputs with
      | [] => acc
      | inp :: inputs' =>
        let (d, state') := next inp
        go inputs' (d :: acc) k state'

def Mem.ofList (bytes : List Data) (h : bytes.length ≤ Index.max.toNat + 1 := by decide) : Mem :=
  bytes
    |>.mapFinIdx (fun i b hi => (b, Fin.mk i hi))
    |>.foldl (init := .default) fun mem (d, i) =>
      have : i ≤ Index.max.toNat := Nat.le_of_lt_succ <| calc
        _ < bytes.length := i.is_lt
        _ ≤ Index.max.toNat + 1 := h
      let i := UInt8.ofFin (i.castLT (Nat.lt_of_le_of_lt this (by decide)))
      have : i ≤ Index.max := by
        simp [UInt8.le_iff_toFin_le, i]
        exact this
      mem.setByte i d this

def Mem.ofString? (s : String) : Option Mem := do
  let bytes ← s.splitOn "\t"
    |>.mapM (fun
      | String.mk [c₁, c₂] => do
        let d₁ ← toDigit c₁.toUpper
        let d₂ ← toDigit c₂.toUpper
        (16 * d₁ + d₂).toInt8
      | _ => none)
  if h : bytes.length ≤ Index.max.toNat + 1 then
    return ofList bytes h
  else none
where
  toDigit c : Option Index :=
    if '0' ≤ c && c ≤ '9' then
      some (c.toUInt8 - '0'.toUInt8)
    else if 'A' ≤ c && c ≤ 'F' then
      some (c.toUInt8 - 'A'.toUInt8 + 10)
    else none

def prog :=
  "00	fd	03	00	fd	06	fe	00	09	00	00	00	00	00	00	00"
  |> Mem.ofString?
  |> Option.get!

instance [ToString α] : ToString (ProgramIO.Read? α) where
  toString
  | .none a => s!".none {a}"
  | .readIn f => s!".readIn fun | 37 => {f 37} | _ => …"

instance [ToString α] : ToString (ProgramIO α) where
  toString
  | .halted => ".halted"
  | .writeOut r => s!".writeOut <| {r}"
  | .justRead r => s!".justRead <| {r}"

instance : ToString State where
  toString | { mem, idx } => s!"⟨{mem}, {idx}⟩"

#eval do
  let initialState := State.mk prog 0
  let inputs := [1, 1, 1, 2, 1, -1, 11, 25, 82, 17]
  let result := State.eval inputs initialState
  return result
