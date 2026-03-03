import atgt.Discont.Limit
import atgt.Funcoid.Topology
import Mathlib.Topology.AlexandrovDiscrete

open Filter Topology
open scoped Topology

universe u

section

variable {α : Type u} [TopologicalSpace α]

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

-- theorem tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid
--     (x y : α) :
--     Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) ↔
--       IsFunctionLimit (neighborhoodFuncoid (inferInstance : TopologicalSpace α))
--         f (z.fwd (Filtrator.ofMathlibFilter (nhds x))) y := by
--   sorry

end
