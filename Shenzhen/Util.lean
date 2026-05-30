module

import Batteries.Data.Fin.Basic
import Batteries.Data.Fin.Lemmas
import Batteries.Tactic.Lemma

/-- `n` spaces -/
@[expose] public def String.whitespace (n : Nat) : String :=
  String.pushn "" ' ' n

namespace Fin

/-- Find the smallest `j > i` s.t. `p j = true`, or `none` if no such `j` exists. -/
@[specialize]
public def nextFinIdx? (i : Fin n) (p : Fin n → Bool) : Option (Fin n) :=
  if h : i.val + 1 < n then
    letI iSucc := mk (i + 1) h
    if p iSucc then some iSucc else nextFinIdx? iSucc p
  else none
termination_by n - i.val

theorem nextFinIdx?_eq {i : Fin n} : nextFinIdx? i p = find? fun j => j > i && p j := by
  match n with
  | 0 => exact i.elim0
  | n' + 1 =>
    induction i using reverseInduction with
    | last =>
      symm; simp [nextFinIdx?, ←Fin.not_le, le_last]
    | cast i' ih =>
      unfold nextFinIdx?
      simp only [val_castSucc, Nat.add_lt_add_iff_right, is_lt, reduceDIte]
      rw [Fin.succ] at ih
      rw [ih]
      simp only [lt_def, val_castSucc]
      split
      · symm
        simp only [find?_eq_some_iff, Bool.and_eq_true,
                   decide_eq_true_eq, Bool.and_eq_false_imp]
        refine ⟨⟨Nat.lt_succ_self _, ‹_›⟩, fun j h₁ h₂ => ?_⟩
        exfalso
        simp [lt_def] at h₁ h₂
        omega
      · congr 1; funext j
        match Nat.lt_trichotomy (i' + 1) j with
        | .inl h => simp [h]; omega
        | .inr (.inl h) => simp [h] at *; intro; assumption
        | .inr (.inr h) => congr 2; apply propext; omega

@[always_inline]
public def succ' : Fin n → Fin n
| ⟨k, lt⟩ => ⟨(k + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt lt)⟩

end Fin

namespace Clamp
public section

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

end
end Clamp

public section

@[inline, simp] def Array.mapFinIdx' (as : Array α) (f : Fin as.size → α → β) : Array β :=
  as.mapFinIdx fun i a h => f ⟨i, h⟩ a

@[inline, simp] def Array.zipFinIdx (as : Array α) : Array (Fin as.size × α) :=
  as.mapFinIdx fun i a h => ⟨⟨i, h⟩, a⟩

@[inline, simp] def Vector.mapFinIdx' (xs : Vector α n) (f : Fin n → α → β) : Vector β n :=
  xs.mapFinIdx fun i a h => f ⟨i, h⟩ a

@[inline, simp] def Vector.zipFinIdx  (xs: Vector α n) : Vector (α × Fin n) n :=
  xs.mapFinIdx fun i a h => ⟨a, i, h⟩

@[inline, simp] def Vector.findSome?FinIdx (xs : Vector α n) (f : Fin n → α → Option β) : Option (β × Fin n) :=
  xs.zipFinIdx.findSome? fun (a, i) => (·, i) <$> f i a

theorem Vector.countP_map_le_countP
    {v : Vector α n} {f : α → β} {p : α → Bool} {q : β → Bool}
    (hf : ∀ a, q (f a) → p a) : (v.map f).countP q ≤ v.countP p := by
  rw [Vector.countP_map]
  apply Vector.countP_mono_left
  intros; apply hf; assumption
