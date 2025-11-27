import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

/-! `CommRing` instance for `Fin` -/
namespace Fin

theorem add_assoc {a b c : Fin n} : a + b + c = a + (b + c) := by
  simp [Fin.add_def]
  congr 1
  apply Nat.add_assoc

theorem neg_add_cancel {a : Fin n} : -a + a = ⟨0, a.pos⟩ := by
  simp [Fin.neg_def, Fin.add_def, Nat.sub_add_cancel (Nat.le_of_lt a.is_lt)]

theorem add_comm {a b : Fin n} : a + b = b + a := by
  simp only [add_def]
  congr 2
  apply Nat.add_comm

instance [NeZero n] : AddCommGroup (Fin n) where
  add_assoc _ _ _ := add_assoc
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := neg_add_cancel
  add_comm _ _ := add_comm
  sub_eq_add_neg := Fin.sub_eq_add_neg

theorem left_distrib {a b c : Fin n} : a * (b + c) = a * b + a * c := by
  simp [Fin.mul_def, Fin.add_def]
  congr 1
  apply Nat.mul_add

theorem right_distrib {a b c : Fin n} : (a + b) * c = a * c + b * c := by
  simp [Fin.mul_def, Fin.add_def]
  congr 1
  apply Nat.add_mul

instance [NeZero n] : CommRing (Fin n) where
  left_distrib _ _ _ := left_distrib
  right_distrib _ _ _ := right_distrib
  zero_mul := Fin.zero_mul
  mul_zero := Fin.mul_zero
  mul_assoc := Fin.mul_assoc
  one_mul := Fin.one_mul
  mul_one := Fin.mul_one
  mul_comm := Fin.mul_comm

instance instNeZero (x : Fin n := by assumption) : NeZero n :=
  ⟨Nat.ne_of_lt' x.pos⟩

theorem add_sub_cancel {a b : Fin n} : a + (b - a) = b :=
  have := instNeZero
  _root_.add_sub_cancel a b

end Fin

namespace Vector
@[specialize] def nextFinIdx? (vec : Vector α n) (i : Fin n) (p : Fin n → α → Bool) : Option (Fin n) :=
  (go 0).1
where go (δ : Fin (n + 1)) : { o : Option (Fin n) // o.isSome ↔ ∃ k : Fin δ.rev, p (i + k.castLE δ.rev.is_le) vec[i + k.castLE δ.rev.is_le] } :=
  if h : δ = Fin.last n then ⟨none, by simp; intro ⟨_, h'⟩; simp [h] at h'⟩
  else
    have := Fin.val_lt_last h -- for termination proof
    let castδ : Fin n := ⟨δ, this⟩
    let j := i + castδ
    if h' : p j vec[j] then ⟨j, by simp; sorry⟩ else
      let ⟨next, hnext⟩ := go castδ.succ
      ⟨next, sorry⟩

-- #check
-- #check Int.add_sub
-- lemma nextFinIdx?_isSome_iff {i : Fin n} : (nextFinIdx? v i p).isSome ↔ ∃ j : Fin n, p j v[j] := by
--   suffices h : ∀ δ : Fin (n + 1), (nextFinIdx?.go v i p δ.rev).isSome ↔
--       ∃ k : Fin δ, p (i + k.castLE δ.is_le) v[i + k.castLE δ.is_le] from by
--     convert h ⟨n, Nat.lt_add_one n⟩ using 1
--     rw [nextFinIdx?, Bool.coe_iff_coe]
--     congr
--     · exact (Fin.rev_last n).symm
--     · constructor
--       · rintro ⟨j, hj⟩
--         use j - i
--         simpa [Fin.add_sub_cancel]
--       · rintro ⟨k, hk⟩
--         use i + k
--         simpa using hk
--   rintro ⟨δ, hδ⟩
--   induction δ with
--   | zero => simp [nextFinIdx?.go]
--   | succ k ih =>
--     unfold nextFinIdx?.go
--     split <;> rename_i h
--     · simp [Fin.rev_eq_iff] at h
--     · have := Fin.val_lt_last h
--       simp only
--       let castδ := Fin.mk (Fin.rev ⟨k + 1, hδ⟩) this
--       refold_let castδ
--       have hδ' : k < n + 1 := Nat.lt_of_succ_lt hδ
--       have : castδ.succ = Fin.rev ⟨k, hδ'⟩ := by
--         simp [castδ, Fin.rev]
--         omega
--       simp [this] at *
--       split
--       · simp only [Option.isSome_some, true_iff]
--         use ⟨castδ, sorry⟩
--         simp_all
--       · simp [ih hδ']

--         sorry
-- @[specialize, inline] def nextFinIdx (vec : Vector α n) (i : Fin n) (p : Fin n → α → Bool)
--     (h : ∃ j : Fin n, p j vec[j]) : Fin n :=
--   (vec.nextFinIdx? i p).get <| by
--     sorry

end Vector

@[always_inline]
def Fin.succ' : Fin n → Fin n
| ⟨k, lt⟩ => ⟨(k + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt lt)⟩

instance BitVec.instFintype : Fintype (BitVec n) :=
  Fintype.ofSurjective BitVec.ofFin fun bv => ⟨bv.toFin, rfl⟩

namespace Clamp

variable {α : Type u} [LE α] [DecidableLE α]

@[reducible, inline]
def clamp (x lo hi : α) :=
  if x ≤ lo then lo else if x ≥ hi then hi else x

variable [@Std.Refl α (· ≤ ·)] [@Std.Total α (· ≤ ·)]
variable {x lo hi : α}

theorem clamp_le_hi (h : lo ≤ hi) : clamp x lo hi ≤ hi := by
  unfold clamp
  split
  · exact h
  · split
    · apply Std.Refl.refl
    · have := Std.Total.total (r := (· ≤ ·)) x hi
      apply this.resolve_right
      assumption

theorem lo_le_clamp (h : lo ≤ hi) : lo ≤ clamp x lo hi := by
  unfold clamp
  split
  · apply Std.Refl.refl
  · split
    · exact h
    · have := Std.Total.total (r := (· ≤ ·)) lo x
      apply this.resolve_right
      assumption

/-! Instances for use with `Integer` and `SimpleIOData` -/

instance : @Std.Refl Int16 LE.le :=
  ⟨Int16.le_refl⟩

instance : @Std.Total Int16 LE.le where
  total a b := (Int16.le_or_lt a b).imp_right Int16.le_of_lt

end Clamp

namespace Lean.Meta

/-! Bring some functions out of the `MetaM` monad. -/

/-- Returns `Decidable.decide p`, where `inst : Decidable p`. -/
def mkDecide' (p inst : Expr) : Expr :=
  mkApp2 (mkConst ``Decidable.decide) p inst

/-- Returns a proof for `p : Prop` using `decide p`, where
  `inst : Decidable p`. -/
def mkDecideProof' (p inst : Expr) : Expr :=
  -- folowing `Meta.mkDecideProof`
  let decP := mkDecide' p inst
  let decEqTrue := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) decP (mkConst ``true)
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  let h := Meta.mkExpectedPropHint h decEqTrue
  mkApp3 (mkConst ``of_decide_eq_true) p inst h

def mkListLit' (type : Expr) (xs : List Expr) (u := levelZero) : Expr :=
  xs.foldr (init := .app (mkConst ``List.nil [u]) type) fun expr acc =>
    mkApp3 (mkConst ``List.cons [u]) type expr acc

def mkArrayLit' (type : Expr) (xs : List Expr) (u := levelZero) : Expr :=
  mkApp2 (mkConst ``List.toArray [u]) type (mkListLit' type xs u)

local instance instDecidableArraySizeEq.{u} {α : Type u} {arr : Array α} {n : Nat} : Decidable (arr.size = n) :=
  inferInstance

def mkVector (type : Expr) (xs : List Expr) (u := levelZero) : Expr :=
  let arrExpr := mkArrayLit' type xs u
  let nExpr := mkNatLit xs.length
  mkApp4 (mkConst ``Vector.mk [u]) type nExpr arrExpr <|
    mkDecideProof'
      (mkNatEq
        (mkApp2 (mkConst ``Array.size [u]) type arrExpr)
        nExpr)
      (mkApp3 (mkConst ``instDecidableArraySizeEq [u]) type arrExpr nExpr)

end Lean.Meta

-- def a : Nat → Nat := id
-- def b : Nat → Nat := Nat.succ
-- def c : Nat → Nat := Nat.pred

-- open Lean in
-- elab "test " : term => do
--   let arr := #[``a, ``b, ``c]
--   return Meta.mkArrayLit'
--     (←mkArrow Nat.mkType Nat.mkType)
--     (arr.toList.map mkConst)

-- #eval (test).map (· 35)
