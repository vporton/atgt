import Mathlib.Data.Ordmap.Ordset

universe u v u2 v2

instance {u} : Coe (SemilatticeInf u) (PartialOrder u) where
    coe s := s.toPartialOrder

/- TODO: Should be in `Ordset`, instead. -/
def is_least {α : Type u} [PartialOrder α] (a : α) := ∀ x, a ≤ x

/- TODO: Should be in `Ordset`, instead. -/
def meet {α : Type u} [PartialOrder α] (a b : α) := ∃ c, c ≤ a ∧ c ≤ b ∧ ¬ (is_least c)

theorem meet_comm {α : Type u} [PartialOrder α] (a b : α) : meet a b ↔ meet b a := by
    simp [meet]
    tauto

/- TODO: Should be in `Ordset`, instead. -/
theorem meet_as_inf {α : Type u}
  [s : SemilatticeInf α] (a b : α) :
  meet a b ↔
  ¬ is_least (a ⊓ b) :=
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

def separator {α : Type u} [PartialOrder α] (a : α) := { x : α | ¬ meet x a }

prefix:80 "⋆" => separator

def Ordset.is_separable {α : Type u} [PartialOrder α] (a b : α) := a ≠ b → separator a ≠ separator b
