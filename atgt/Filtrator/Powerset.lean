import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.RelIso.Basic
import atgt.Filtrator
import atgt.Filtrator.Primary

/-!
# Powerset filtrators

Definition 460: a primary filtrator over a poset order-isomorphic to a powerset is called a
powerset filtrator.
-/

/-- Mathlib orders `Set U` by inclusion (`⊆`); this alias exposes it explicitly. -/
def setPartialOrder (U : Type*) : PartialOrder (Set U) := inferInstance

namespace Filtrator

universe u v

variable {α : Type u}

abbrev FilterOnPowerset (α: Type*) := PosetFilter (setPartialOrder α)

-- TODO: This seems unneeded, but used in GeneralizedFilterBase.
abbrev FiltratorOnPowerset.Primary {base: Type u} {U: Set base} :
    Type u := Filtrator.Primary.{u, u} (base := Set base) (Set.powerset U)

-- /-- Canonical filtrator structure on powerset filters. -/
-- instance FiltratorOnPowerset {base: Type*} {U: Set base}
--     : FiltratorOnPowerset.Primary (U := U) := {
--       subset := Set.powerset U
--       is_primary := sorry
--       core := sorry
--     }

namespace FilterCorrespondence

/-- Convert a `FilterOnPowerset` to a Mathlib `Filter`. -/
def toMathlibFilter (F : FilterOnPowerset α) : Filter α where
  sets := F.elements
  univ_sets := by
    rcases F.non_empty with ⟨s, hs⟩
    have hs' : s ∈ F.carrier := by
      simpa [F.carrier_eq_elements] using hs
    have huniv' : (Set.univ : Set α) ∈ F.carrier := F.upper' (Set.subset_univ s) hs'
    simpa [F.carrier_eq_elements] using huniv'
  sets_of_superset := by
    intro s t hs hst
    have hs' : s ∈ F.carrier := by
      simpa [F.carrier_eq_elements] using hs
    have ht' : t ∈ F.carrier := F.upper' hst hs'
    simpa [F.carrier_eq_elements] using ht'
  inter_sets := by
    intro s t hs ht
    rcases F.cap_elements hs ht with ⟨u, hu, hus, hut⟩
    have hu' : u ∈ F.carrier := by
      simpa [F.carrier_eq_elements] using hu
    have hint' : s ∩ t ∈ F.carrier := by
      refine F.upper' ?_ hu'
      intro x hx
      exact ⟨hus hx, hut hx⟩
    simpa [F.carrier_eq_elements] using hint'

/-- Convert a Mathlib `Filter` to a `FilterOnPowerset`. -/
def ofMathlibFilter (F : Filter α) : FilterOnPowerset α where
  elements := F.sets
  non_empty := ⟨Set.univ, F.univ_sets⟩
  cap_elements := by
    intro s t hs ht
    exact ⟨s ∩ t, F.inter_sets hs ht, Set.inter_subset_left, Set.inter_subset_right⟩
  carrier := F.sets
  upper' := by
    intro s t hst hs
    exact F.sets_of_superset hs hst
  carrier_eq_elements := rfl

@[simp]
theorem toMathlibFilter_ofMathlibFilter (F : Filter α) :
    toMathlibFilter (ofMathlibFilter (α := α) F) = F := by
  ext s
  rfl

@[simp]
theorem ofMathlibFilter_toMathlibFilter (F : FilterOnPowerset α) :
    ofMathlibFilter (α := α) (toMathlibFilter F) = F := by
  ext
  rfl

/-- One-to-one correspondence between `FilterOnPowerset α` and Mathlib `Filter α`. -/
def equivMathlibFilter : FilterOnPowerset α ≃ Filter α where
  toFun := toMathlibFilter
  invFun := ofMathlibFilter (α := α)
  left_inv := ofMathlibFilter_toMathlibFilter (α := α)
  right_inv := toMathlibFilter_ofMathlibFilter (α := α)

theorem toMathlibFilter_bijective :
    Function.Bijective (toMathlibFilter (α := α)) :=
  equivMathlibFilter (α := α).bijective

/-- `FilterOnPowerset α` inherits binary infimum from Mathlib filters via the equivalence. -/
instance instSemilatticeInfFilterOnPowerset (α : Type*) :
    SemilatticeInf (FilterOnPowerset α) where
  inf F G := ofMathlibFilter (α := α) (toMathlibFilter F ⊓ toMathlibFilter G)
  inf_le_left := by
    intro F G
    change F.elements ⊆ (ofMathlibFilter (α := α) (toMathlibFilter F ⊓ toMathlibFilter G)).elements
    intro s hs
    exact (inf_le_left : toMathlibFilter F ⊓ toMathlibFilter G ≤ toMathlibFilter F) hs
  inf_le_right := by
    intro F G
    change G.elements ⊆ (ofMathlibFilter (α := α) (toMathlibFilter F ⊓ toMathlibFilter G)).elements
    intro s hs
    exact (inf_le_right : toMathlibFilter F ⊓ toMathlibFilter G ≤ toMathlibFilter G) hs
  le_inf := by
    intro F G H hFG hFH
    change (ofMathlibFilter (α := α) (toMathlibFilter G ⊓ toMathlibFilter H)).elements ⊆ F.elements
    intro s hs
    exact
      (le_inf
        (show toMathlibFilter F ≤ toMathlibFilter G from hFG)
        (show toMathlibFilter F ≤ toMathlibFilter H from hFH)) hs

end FilterCorrespondence

export FilterCorrespondence (toMathlibFilter ofMathlibFilter equivMathlibFilter toMathlibFilter_bijective)

end Filtrator

-- export Filtrator (FiltratorOnPowerset)
