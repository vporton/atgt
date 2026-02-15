import atgt.Filtrator.Separable
import atgt.AlternativePrimaryFiltrators

namespace StrongSeparability

universe u

variable {α : Type u}

/-- Separator membership is preserved by order isomorphism. -/
lemma orderIso_mem_separator_iff {β γ : Type u} [PartialOrder β] [PartialOrder γ]
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
lemma isStronglySeparable_of_orderIso {β γ : Type u} [PartialOrder β] [PartialOrder γ]
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
theorem primary_imp_booleanStronglySeparableCore [Filtrator.Primary α]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := α))]
    (hcoreOrder :
      Bcore.toPartialOrder = Filtrator.suborder (α := α)) :
    @IsStronglySeparable (Filtrator.supset (α := α)) (Filtrator.suporder (α := α)) := by
  letI : PartialOrder (Filtrator.subset (α := α)) := Bcore.toPartialOrder
  have hstar_free :
      Filtrator.strongly_star_separable
        (AlternativePrimaryFiltrators.PrincipalConstructions.freeStar_filtrator
          (α := Filtrator.subset (α := α))) :=
    AlternativePrimaryFiltrators.PrincipalConstructions.freeStar_filtrator_strongly_star_separable
      (α := Filtrator.subset (α := α))
  have hstrong_free :
      IsStronglySeparable
        (AlternativePrimaryFiltrators.FreeStar (α := Filtrator.subset (α := α))) :=
    strongly_star_separable_imp_stronglySeparable hstar_free
  let e_filters_freeStar :
      PosetFilter (U := (inferInstance : PartialOrder (Filtrator.subset (α := α)))) ≃o
        AlternativePrimaryFiltrators.FreeStar (α := Filtrator.subset (α := α)) :=
    ((AlternativePrimaryFiltrators.filterSetOrderIsoPosetFilter
      (α := Filtrator.subset (α := α))).symm.trans
      (AlternativePrimaryFiltrators.freeStarOrderIsoFilterSet
        (α := Filtrator.subset (α := α))).symm)
  have hstrong_filters :
      IsStronglySeparable
        (PosetFilter (U := Bcore.toPartialOrder)) :=
    isStronglySeparable_of_orderIso (e := e_filters_freeStar.symm) hstrong_free
  have hstrong_filters_suborder :
      IsStronglySeparable (PosetFilter (Filtrator.suborder (α := α))) := by
    exact hcoreOrder ▸ hstrong_filters
  have hstrong_core : IsStronglySeparable α :=
    isStronglySeparable_of_orderIso
      (e := ((Filtrator.Primary.to_filters_iso (α := α)).toRelIso).symm)
      hstrong_filters_suborder
  simpa [Filtrator.supset, Filtrator.suporder] using hstrong_core

end StrongSeparability

export StrongSeparability
  (primary_imp_booleanStronglySeparableCore)
