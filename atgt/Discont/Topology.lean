import atgt.Discont.Limit
import atgt.Funcoid.Topology
import Mathlib.Topology.AlexandrovDiscrete

open Filter Topology
open scoped Topology

universe u

section

variable {α : Type u} [TopologicalSpace α]

lemma neighborhoodFuncoid_fwd_singleton_eq_nhdsKer (y : α) :
    (neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α) =
      nhdsKer ({y} : Set α) := by
  ext z
  simp [neighborhoodFuncoid, principalFuncoid, relImage, neighborhoodRel,
    specializes_iff_forall_open]

lemma principal_neighborhoodFuncoid_fwd_singleton_le_nhds (y : α) :
    Filter.principal
      ((neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α)) ≤
      nhds y := by
  rw [neighborhoodFuncoid_fwd_singleton_eq_nhdsKer]
  intro s hs
  rcases mem_nhds_iff.mp hs with ⟨u, hu_sub, hu_open, hyu⟩
  exact (nhdsKer_minimal (s := ({y} : Set α)) (t := u)
    (by
      intro z hz
      have hz' : z = y := by simpa using hz
      simpa [hz'] using hyu) hu_open).trans hu_sub

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

theorem isFuncoidLimit_neighborhoodFuncoid_imp_tendsto_id_nhds
    (x y : α) :
    IsFuncoidLimit (neighborhoodFuncoid (inferInstance : TopologicalSpace α))
      (Filtrator.ofMathlibFilter (nhds x)) y →
    Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) := by
  intro hlim
  have hxy_principal :
      nhds x ≤ Filter.principal
        ((neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α)) := by
    simpa [IsFuncoidLimit, Funcoid.fwd_set, le_principal_iff_subset] using hlim
  have hxy : nhds x ≤ nhds y :=
    le_trans hxy_principal (principal_neighborhoodFuncoid_fwd_singleton_le_nhds (y := y))
  simpa [Filter.Tendsto] using hxy

theorem tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid_of_fwd_singleton_mem_nhds
    (x y : α)
    (hmem :
      (neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α) ∈ nhds y) :
    Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) ↔
      IsFuncoidLimit (neighborhoodFuncoid (inferInstance : TopologicalSpace α))
        (Filtrator.ofMathlibFilter (nhds x)) y := by
  constructor
  · intro ht
    have hxy : nhds x ≤ nhds y := by
      simpa [Filter.Tendsto] using ht
    have hy_principal :
        nhds y ≤
          Filter.principal
            ((neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α)) :=
      (le_principal_iff).2 hmem
    have hx_principal :
        nhds x ≤
          Filter.principal
            ((neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α)) :=
      le_trans hxy hy_principal
    simpa [IsFuncoidLimit, Funcoid.fwd_set, le_principal_iff_subset] using hx_principal
  · intro hlim
    exact isFuncoidLimit_neighborhoodFuncoid_imp_tendsto_id_nhds (x := x) (y := y) hlim

theorem tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid_of_self_le_fwd_set
    (x y : α)
    (hself :
      Filtrator.ofMathlibFilter (nhds y) ≤
        Funcoid.fwd_set (neighborhoodFuncoid (inferInstance : TopologicalSpace α)) ({y} : Set α)) :
    Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) ↔
      IsFuncoidLimit (neighborhoodFuncoid (inferInstance : TopologicalSpace α))
        (Filtrator.ofMathlibFilter (nhds x)) y := by
  have hmem :
      (neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α) ∈ nhds y := by
    simpa [Funcoid.fwd_set, le_principal_iff_subset] using hself
  exact tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid_of_fwd_singleton_mem_nhds
    (x := x) (y := y) hmem

theorem tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid
    [AlexandrovDiscrete α] (x y : α) :
    Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) ↔
      IsFuncoidLimit (neighborhoodFuncoid (inferInstance : TopologicalSpace α))
        (Filtrator.ofMathlibFilter (nhds x)) y := by
  refine
    tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid_of_fwd_singleton_mem_nhds
      (x := x) (y := y) ?_
  have hker : nhdsKer ({y} : Set α) ∈ nhds y := by
    have hle : nhds y ≤ Filter.principal (nhdsKer ({y} : Set α)) := by
      exact le_of_eq (principal_nhdsKer_singleton y).symm
    exact (le_principal_iff).1 hle
  simpa [neighborhoodFuncoid_fwd_singleton_eq_nhdsKer] using hker

-- theorem tendsto_id_nhds_iff_isBinaryRelationLimit_neighborhoodRel
--     [AlexandrovDiscrete α] (x y : α) :
--     Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) ↔
--       IsBinaryRelationLimit (neighborhoodRel (inferInstance : TopologicalSpace α))
--         (Filtrator.ofMathlibFilter (nhds x)) y := by
--   simpa [IsBinaryRelationLimit, neighborhoodFuncoid] using
--     tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid (x := x) (y := y)

-- theorem tendsto_id_nhds_iff_isBinaryRelationLimit_neighborhoodRel_of_fwd_singleton_mem_nhds
--     (x y : α)
--     (hmem :
--       (neighborhoodFuncoid (inferInstance : TopologicalSpace α)).fwd ({y} : Set α) ∈ nhds y) :
--     Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) ↔
--       IsBinaryRelationLimit (neighborhoodRel (inferInstance : TopologicalSpace α))
--         (Filtrator.ofMathlibFilter (nhds x)) y := by
--   simpa [IsBinaryRelationLimit, neighborhoodFuncoid] using
--     tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid_of_fwd_singleton_mem_nhds
--       (x := x) (y := y) hmem

-- theorem tendsto_id_nhds_iff_isBinaryRelationLimit_neighborhoodRel_of_self_le_fwd_set
--     (x y : α)
--     (hself :
--       Filtrator.ofMathlibFilter (nhds y) ≤
--         Funcoid.fwd_set (neighborhoodFuncoid (inferInstance : TopologicalSpace α)) ({y} : Set α)) :
--     Filter.Tendsto (fun z : α => z) (nhds x) (nhds y) ↔
--       IsBinaryRelationLimit (neighborhoodRel (inferInstance : TopologicalSpace α))
--         (Filtrator.ofMathlibFilter (nhds x)) y := by
--   simpa [IsBinaryRelationLimit, neighborhoodFuncoid] using
--     tendsto_id_nhds_iff_isFuncoidLimit_neighborhoodFuncoid_of_self_le_fwd_set
--       (x := x) (y := y) hself

end
