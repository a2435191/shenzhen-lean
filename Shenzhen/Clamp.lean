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
