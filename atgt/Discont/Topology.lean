import atgt.Discont.Limit
import atgt.Funcoid.Topology

open Filter Topology
open scoped Topology

universe u

section

variable {baseα : Type*} {α: Set baseα} [TopologicalSpace α]

theorem neighborhoodFuncoid_idempotent :
    (neighborhoodFuncoid (inferInstance : TopologicalSpace α)) ∘
      (neighborhoodFuncoid (inferInstance : TopologicalSpace α)) =
    neighborhoodFuncoid (inferInstance : TopologicalSpace α) := by
  have hrel :
      relComp
          (neighborhoodRel (inferInstance : TopologicalSpace α))
          (neighborhoodRel (inferInstance : TopologicalSpace α)) =
        neighborhoodRel (inferInstance : TopologicalSpace α) := by
    funext x z
    apply propext
    constructor
    · intro hxz
      rcases hxz with ⟨y, hxy, hyz⟩
      intro U hU hxU
      exact hyz U hU (hxy U hU hxU)
    · intro hxz
      exact ⟨z, hxz, by
        intro U hU hzU
        exact hzU⟩
  calc
    (neighborhoodFuncoid (inferInstance : TopologicalSpace α)) ∘
        (neighborhoodFuncoid (inferInstance : TopologicalSpace α))
      = principalFuncoid
          (relComp
            (neighborhoodRel (inferInstance : TopologicalSpace α))
            (neighborhoodRel (inferInstance : TopologicalSpace α))) := by
            simpa [neighborhoodFuncoid] using
              (principalFuncoid_comp
                (r := neighborhoodRel (inferInstance : TopologicalSpace α))
                (s := neighborhoodRel (inferInstance : TopologicalSpace α))).symm
    _ = neighborhoodFuncoid (inferInstance : TopologicalSpace α) := by
          simp [neighborhoodFuncoid, hrel]

theorem tendstotop_iff_fcd
    {baseα : Type*} {α: Set baseα} {baseβ : Type*} {β: Set baseβ}
    (x : α) (y : β)
    [TopologicalSpace α] [d: TopologicalSpace β]
    (f : α → β) :
    Filter.Tendsto f (nhds x) (nhds y) ↔
      point_limitOfFunction
        (neighborhoodFuncoid d) f
        (Filtrator.ofMathlibFilter (nhds x)) y := by
  sorry

end
