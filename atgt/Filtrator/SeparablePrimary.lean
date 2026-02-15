import atgt.Filtrator.Separable
import atgt.AlternativePrimaryFiltrators

namespace StrongSeparability

universe u

variable {α : Type u}

/-- Separator membership is preserved by order isomorphism. -/
lemma orderIso_mem_separator_iff {β γ : Type u} [BooleanAlgebra β] [BooleanAlgebra γ]
    (e : β ≃o γ) (x a : β) :
    x ∈ separator a ↔ e x ∈ separator (e a) := by
  constructor
  · intro hx
    rcases hx with ⟨c, hcx, hca, hnot⟩
    refine ⟨e c, (e.map_rel_iff).2 hcx, (e.map_rel_iff).2 hca, ?_⟩
    intro hleast
    apply hnot
    intro y
    exact (e.map_rel_iff).1 (hleast (e y))
  · intro hx
    rcases hx with ⟨c, hcx, hca, hnot⟩
    refine ⟨e.symm c, ?_, ?_, ?_⟩
    · simpa using (e.symm.map_rel_iff).2 hcx
    · simpa using (e.symm.map_rel_iff).2 hca
    intro hleast
    apply hnot
    intro y
    exact (e.symm.map_rel_iff).1 (hleast (e.symm y))

/-- Strong separability is invariant under order isomorphism. -/
lemma isStronglySeparable_of_orderIso {β γ : Type u} [BooleanAlgebra β] [BooleanAlgebra γ]
    (e : β ≃o γ) (hβ : IsStronglySeparable β) :
    IsStronglySeparable γ := by
  intro a b hsub
  have hsub' : separator (e.symm a) ⊆ separator (e.symm b) := by
    intro x hx
    have hx' : e x ∈ separator a := by
      simpa using (orderIso_mem_separator_iff (e := e) (x := x) (a := e.symm a)).1 hx
    have hy' : e x ∈ separator b := hsub hx'
    exact
      (orderIso_mem_separator_iff (e := e) (x := x) (a := e.symm b)).2 (by simpa using hy')
  have hle : e.symm a ≤ e.symm b := hβ (e.symm a) (e.symm b) hsub'
  exact (e.symm.map_rel_iff).1 hle

/-- Proposition 579 core step with the correct assumption locus:
the core type is boolean, so the boolean-core order is strongly separable. -/
theorem primary_imp_booleanStronglySeparableCore [Filtrator α] [Filtrator.Primary α]
    [BooleanAlgebra (Filtrator.subset (α := α))] :
    @IsStronglySeparable (Filtrator.supset (α := α)) (Filtrator.suporder (α := α)) := by
  sorry

end StrongSeparability

export StrongSeparability
  (primary_imp_booleanStronglySeparableCore)
