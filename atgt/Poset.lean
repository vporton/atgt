import Mathlib.Data.Ordmap.Ordset

universe u v u2 v2

instance {u} : Coe (SemilatticeInf u) (PartialOrder u) where
    coe s := s.toPartialOrder

/- TODO: Should be in `Ordset`, instead. -/
def is_least{u}(s: PartialOrder u)(a: u) := ∀ x, a ≤ x

/- TODO: Should be in `Ordset`, instead. -/
def meet{u}(s: PartialOrder u)(a b: u) := ∃ c, c ≤ a ∧ c ≤ b ∧ ¬ (is_least s c)

theorem meet_comm{u}(s: PartialOrder u)(a b: u) : meet s a b ↔ meet s b a := by
    simp [meet]
    tauto

/- TODO: Should be in `Ordset`, instead. -/
theorem meet_as_inf {u}
  (s : SemilatticeInf u) (a b : u) :
  @meet _ s a b ↔
  ¬ @is_least u s (a ⊓ b) :=
by
  constructor
  · intro h
    rcases h with ⟨c, hc₁, hc₂, hnot⟩
    intro hleast
    apply hnot
    intro x
    have := hleast x
    have hcab : c ≤ a ⊓ b :=
      le_inf hc₁ hc₂
    exact le_trans hcab this
  · intro h
    refine ⟨a ⊓ b, inf_le_left, inf_le_right, ?_⟩
    exact h

-- def separator {s: PartialOrder u} (a b: Type u) := { x: a | ¬ meet s x b }
