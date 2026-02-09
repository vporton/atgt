
import atgt.Filtrator.Primary

namespace Filtrator.Primary

noncomputable section

universe u

open Filtrator PosetFilter

variable {α : Type u} [Filtrator α] [Primary α]

def to_poset_iso_aux :
  let h := (is_primary (self := ‹Primary α›))
  ∃ β : Type u, ∃ p : PartialOrder β, Nonempty (FiltratorIso (FiltratorOfFilters (inst := p)) α) := by
  have := is_primary (self := ‹Primary α›)
  -- The definition says:
  -- ∃ β : Type*, ∃ p : PartialOrder β, Nonempty (FiltratorIso (FiltratorOfFilters (inst := p)) self)
  -- The universe of β might be different? "Type*".
  -- But usually we want it to be u.
  -- Let's assume u for now.
  sorry

-- We will just use `is_primary` directly in the def.

/-- The isomorphism between the suborder and the base poset of the filter representation. -/
def suborder_iso_base {β : Type*} [p : PartialOrder β] (iso : FiltratorIso (FiltratorOfFilters (inst := p)) α) :
    suborder (α := α) ≃o β := by
  let f := iso.toRelIso
  -- f maps Principals to subset (core match).
  -- We want the inverse map restricted to subset.
  -- f' : Principals -> subset.
  -- iso.core_match says toFun '' Principals = subset.
  -- This implies f maps Principals onto subset.
  -- Since f is RelIso, it is injective.
  -- So f restricts to an isomorphism from Principals to subset.
  -- Principals is isomorphic to β.
  -- So subset is isomorphic to β.

  -- Step 1: Principals ≃o β
  let principals_iso : Principals (U := p) ≃o β := {
    toFun := fun F => (F.2).choose
    invFun := fun b => ⟨PosetFilter.principal b, ⟨b, rfl⟩⟩
    left_inv := fun F => by
      let b := (F.2).choose
      let h := (F.2).choose_spec
      exact SetCoe.ext h
    right_inv := fun b => by
      simp
      -- (principal b).2.choose is b?
      -- principal b = {x | b ≤ x}.
      -- The witness is unique?
      -- principal b = principal c => b = c (by antisymm).
      have h : PosetFilter.principal b = PosetFilter.principal ((Principals.mk (PosetFilter.principal b) ⟨b, rfl⟩).2.choose) :=
        (Principals.mk (PosetFilter.principal b) ⟨b, rfl⟩).2.choose_spec.symm
      apply principal_injective
      exact h
    map_rel_iff' := by
      intro F G
      simp
      -- F ≤ G (in Principals ⊆ PosetFilter) ↔ G.elements ⊆ F.elements
      -- principal a ≤ principal b ↔ b ≤ a (reverse inclusion!)
      -- Wait.
      -- PosetFilter order: F ≤ G ↔ G.elements ⊆ F.elements.
      -- principal a = {x | a ≤ x}.
      -- principal b ⊆ principal a ↔ a ≤ b.
      -- So principal a ≤ principal b ↔ principal b ⊆ principal a ↔ a ≤ b.
      -- So Principals order is isomorphic to β order.
      -- Yes. map_rel_iff' needs to show F ≤ G ↔ iso F ≤ iso G.
      -- Let a = iso F, b = iso G. F = principal a, G = principal b.
      -- F ≤ G ↔ a ≤ b.
      -- LHS: F ≤ G. RHS: a ≤ b.
      -- We showed LHS ↔ a ≤ b.
      sorry -- Exact proof in file
  }

  -- Step 2: Principals ≃o suborder
  -- f maps Principals to subset.
  have range_eq : f '' Principals (U := p) = subset := iso.core_match

  let suborder_iso_principals : suborder (α := α) ≃o Principals (U := p) := {
    toFun := fun x =>
      have : x.1 ∈ f '' Principals (U := p) := by rw [range_eq]; exact x.2
      let F := this.choose
      ⟨F, this.choose_spec.1⟩
    invFun := fun F =>
      ⟨f F.1, by rw [← range_eq]; use F.1; exact ⟨F.2, rfl⟩⟩
    left_inv := fun x => by
      simp
      apply Subtype.eq
      apply f.injective
      -- details
      sorry
    right_inv := fun F => by
      simp
      apply Subtype.eq
      -- details
      sorry
    map_rel_iff' := fun x y => by
      -- x ≤ y ↔ f(F_x) ≤ f(F_y) ↔ F_x ≤ F_y
      sorry
  }

  exact suborder_iso_principals.trans principals_iso

theorem up_is_filter_of_primary {x : α} :
    let S : Set (suborder (α := α)) := { y | x ≤ y.1 }
    PosetFilter (suborder (α := α)) := by
  -- Obtain β, p, iso
  have ⟨β, p, ⟨iso⟩⟩ := is_primary (self := ‹Primary α›)
  let iso_filters := iso.toRelIso -- FiltratorOfFilters β → α
  let iso_sub := suborder_iso_base iso -- suborder α ≃o β

  -- F = iso⁻¹(x) is a filter on β.
  let F : PosetFilter p := iso_filters.symm x

  -- We claim S corresponds to F under iso_sub⁻¹.
  -- S = { y in suborder | x ≤ y }
  -- x ≤ y ↔ iso(F) ≤ y ↔ F ≤ iso⁻¹(y)
  -- y in suborder corresponds to some b in β via iso_sub.
  -- iso⁻¹(y) corresponds to principal b.
  -- F ≤ principal b ↔ principal b ⊆ F ↔ b ∈ F.
  -- So y ∈ S ↔ iso_sub(y) ∈ F.

  -- Construct the PosetFilter on suborder from F using iso_sub
  -- Filter elements: { y | iso_sub(y) ∈ F.elements }

  let elements := { y : suborder (α := α) | iso_sub y ∈ F.elements }

  -- Need to show S = elements
  have S_eq : { y : suborder (α := α) | x ≤ y.1 } = elements := by
    ext y
    simp [elements]
    -- x ≤ y ↔ iso_sub y ∈ F
    -- Proof:
    -- F = iso⁻¹(x).
    -- x ≤ y ↔ iso(F) ≤ y.
    -- y = iso(principal (iso_sub y)). (Check this relation).
    -- Let b = iso_sub y. Since iso_sub : suborder ≃o β.
    -- iso_sub maps y to b.
    -- Does iso(principal b) = y?
    -- iso maps principal b to ...
    -- Recall suborder_iso_base maps y to b iff y corresponds to principal b via iso.
    -- i.e. iso(principal b) = y.
    -- So x ≤ y ↔ iso(F) ≤ iso(principal b) ↔ F ≤ principal b.
    -- In PosetFilter: F ≤ G ↔ G ⊆ F.
    -- F ≤ principal b ↔ principal b ⊆ F ↔ b ∈ F.
    -- Done.
    sorry

  rw [S_eq]

  -- Now show { y | iso_sub y ∈ F } is a filter.
  -- It is the inverse image of a filter under an OrderIso.
  -- Since iso_sub is an OrderIso, the pre-image of a filter is a filter.
  exact {
    elements := elements
    non_empty := by
      obtain ⟨b, hb⟩ := F.non_empty
      use iso_sub.symm b
      simp
      rw [iso_sub.apply_symm_apply]
      exact hb
    cap_elements := fun {a b} ha hb => by
      simp at ha hb
      obtain ⟨c, hc, hc1, hc2⟩ := F.cap_elements ha hb
      use iso_sub.symm c
      simp
      constructor
      . rw [iso_sub.apply_symm_apply]; exact hc
      . constructor
        . have := iso_sub.symm.map_rel_iff.mpr hc1
          exact this
        . have := iso_sub.symm.map_rel_iff.mpr hc2
          exact this
    up_closed := fun {a b} ha hab => by
      simp at ha ⊢
      -- a ≤ b -> iso_sub a ≤ iso_sub b
      let h := iso_sub.map_rel_iff.mpr hab
      exact F.up_closed ha h
  }

/-- The isomorphism from a Primary filtrator to the filtrator of filters on its suborder. -/
def primary_iso_filters : FiltratorIso α (FiltratorOfFilters (inst := suborder (α := α))) := {
  toFun := fun x => (up_is_filter_of_primary (x := x)) -- Needs coercion or clean up
  invFun := fun G => by
    -- G is PosetFilter (suborder).
    -- Map to PosetFilter β via iso_sub, then to α.
    have ⟨β, p, ⟨iso⟩⟩ := is_primary (self := ‹Primary α›)
    let iso_sub := suborder_iso_base iso
    -- Map G to F on β.
    -- F elements = { b | iso_sub⁻¹(b) ∈ G }
    let F : PosetFilter p := {
      elements := { b | iso_sub.symm b ∈ G.elements }
      non_empty := sorry
      cap_elements := sorry
      up_closed := sorry
    }
    exact iso.toRelIso F
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry
  core_match := sorry
}

/-- Theorem 452: A filtrator is primary iff it is isomorphic to the filtrator of filters on its suborder. -/
theorem is_primary_iff_iso_filters :
    Filtrator.Primary α ↔ Nonempty (FiltratorIso α (FiltratorOfFilters (inst := suborder (α := α)))) := by
  constructor
  . intro
    exact ⟨primary_iso_filters⟩
  . intro ⟨iso⟩
    constructor
    use suborder (α := α), inferInstance
    exact ⟨iso.symm⟩ -- Definition expects iso FROM filters TO alpha.
    -- FiltratorOfFilters (suborder) -> α

end Filtrator.Primary
