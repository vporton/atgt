import atgt.Filtrator
import atgt.PosetFilter

/- TODO: Move the below to `Filtrator.Primary`. -/
class Filtrator.Filtered (α : Type u) [Filtrator α] : Prop where
  is_filtered : ∀ x y : α, up x ⊆ up y → y ≤ x

/-- A filtrator is up-determined if every element is the infimum of its core upper set. -/
class Filtrator.UpDetermined (α : Type u) [Filtrator α] : Prop where
  is_up_determined : ∀ x : α, IsGLB (Filtrator.up x) x

theorem Filtrator.up_determined_iff_filtered {α : Type u} [Filtrator α] :
  Filtrator.Filtered α ↔ Filtrator.UpDetermined α := by
  constructor
  · intro h
    constructor
    intro x
    constructor
    · intro y hy
      exact hy.2
    · intro y hy
      apply h.is_filtered
      intro z hz
      exact ⟨hz.1, hy hz⟩
  · intro h
    constructor
    intro x y h_subs
    apply (h.is_up_determined x).2
    intro z hz
    exact (h.is_up_determined y).1 (h_subs hz)

instance FiltratorOfFilters {X : Type*} [inst : PartialOrder X] : Filtrator (PosetFilter inst) where
  subset := Principals (U := inst)

/- TODO: Rename?  -/
class Filtrator.Primary (α: Type*) [inst : Filtrator α] : Prop where
  is_primary : ∃ β: Type*, ∃ p: PartialOrder β, Nonempty (FiltratorIso (FiltratorOfFilters (inst := p)) inst)

namespace Filtrator.Primary

open Filtrator

variable {α : Type u} [i : Filtrator α] [Primary α]

theorem exists_up_in_subset (x : α) : ∃ y : subset, x ≤ y.1 := by
  have ⟨β, p, ⟨iso⟩⟩ := Primary.is_primary (self := ‹Primary α›)
  -- iso : FiltratorIso (FiltratorOfFilters p) i
  let iso_inv := iso.symm
  let F := iso_inv x
  obtain ⟨b, _⟩ := F.non_empty
  have h_sub : iso.toFun (PosetFilter.principal b) ∈ subset := by
    rw [← iso.core_match]
    use PosetFilter.principal b
    exact ⟨⟨b, rfl⟩, rfl⟩
  use ⟨iso.toFun (PosetFilter.principal b), h_sub⟩
  have hp : iso_inv x ≤ iso_inv (iso.toFun (PosetFilter.principal b)) := by
    apply (iso.symm.map_rel_iff).mpr
    simp only [iso_inv]
    rw [RelIso.apply_symm_apply]
    change F ≤ PosetFilter.principal b
    -- PosetFilter order: G ≤ H ↔ H ⊆ G
    -- F ≤ principal b ↔ principal b ⊆ F ↔ b ∈ F
    intro z hz
    apply F.up_closed (a := b) (by assumption) hz
  exact iso_inv.map_rel_iff.mp hp

theorem directed_up_in_subset (x : α) (a b : subset) (ha : x ≤ a.1) (hb : x ≤ b.1) :
    ∃ c : subset, x ≤ c.1 ∧ c.1 ≤ a.1 ∧ c.1 ≤ b.1 := by
  have ⟨β, p, ⟨iso⟩⟩ := Primary.is_primary (self := ‹Primary α›)
  let iso_inv := iso.symm

  have ha' : iso_inv x ≤ iso_inv a.1 := iso_inv.map_rel_iff.mpr ha
  have hb' : iso_inv x ≤ iso_inv b.1 := iso_inv.map_rel_iff.mpr hb

  have ⟨pa, hpa⟩ : ∃ pa, iso_inv a.1 = PosetFilter.principal pa := by
    have : a.1 ∈ iso.toFun '' Principals (U := p) := by
      rw [iso.core_match]; exact a.2
    obtain ⟨F, hF_princ, hF_eq⟩ := this
    use hF_princ.2.choose
    rw [← hF_eq]; simp; rw [iso.symm.left_inv F]
    symm; exact hF_princ.2.choose_spec

  have ⟨pb, hpb⟩ : ∃ pb, iso_inv b.1 = PosetFilter.principal pb := by
    have : b.1 ∈ iso.toFun '' Principals (U := p) := by
      rw [iso.core_match]; exact b.2
    obtain ⟨F, hF_princ, hF_eq⟩ := this
    use hF_princ.2.choose
    rw [← hF_eq]; simp; rw [iso.symm.left_inv F]
    symm; exact hF_princ.2.choose_spec

  rw [hpa] at ha'
  rw [hpb] at hb'

  -- F (iso_inv x) is a filter.
  -- iso_inv x ≤ principal pa ↔ principal pa ⊆ iso_inv x ↔ pa ∈ iso_inv x.
  have pa_in_F : pa ∈ (iso_inv x).elements := ha' (le_refl _)
  have pb_in_F : pb ∈ (iso_inv x).elements := hb' (le_refl _)

  obtain ⟨pc, hpc, hpc_le_a, hpc_le_b⟩ := (iso_inv x).cap_elements pa_in_F pb_in_F

  let c_val := iso.toFun (PosetFilter.principal pc)
  have c_in_subset : c_val ∈ subset := by
    rw [← iso.core_match]
    use PosetFilter.principal pc
    exact ⟨⟨pc, rfl⟩, rfl⟩

  let c : subset := ⟨c_val, c_in_subset⟩
  use c
  constructor
  . apply iso_inv.map_rel_iff.mp; simp [c_val]; rw [iso.symm.left_inv]
    intro z hz; apply (iso_inv x).up_closed hpc hz
  . constructor
    . change c_val ≤ a.1; apply iso_inv.map_rel_iff.mp
      rw [hpa, iso.symm.left_inv]
      change (PosetFilter.principal pc) ≤ (PosetFilter.principal pa)
      intro z hz; refine le_trans hpc_le_a hz
    . apply iso_inv.map_rel_iff.mp; rw [hpb, iso.symm.left_inv]
      intro z hz; refine le_trans hpc_le_b hz

attribute [local instance] Filtrator.suborder

def to_poset_filter (x : α) : PosetFilter (Filtrator.suborder (α := α)) :=
{ elements := { y | x ≤ y.1 }
  non_empty := by
    let ⟨y, hy⟩ := exists_up_in_subset x
    use y
    exact hy
  cap_elements := fun {a b} ha hb => by
    simp at ha hb
    exact directed_up_in_subset x a b ha hb
  up_closed := fun {a b} ha hab => by
    simp at ha hab ⊢
    exact le_trans ha hab }

/-- The canonical map from α to filters on its suborder. -/
def to_filters_iso : FiltratorIso α (FiltratorOfFilters (inst := Filtrator.suborder (α := α))) := {
  toFun := to_poset_filter
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry
  core_match := sorry
}

theorem primary_iff_iso_filters :
    Primary α ↔ Nonempty (FiltratorIso α (FiltratorOfFilters (inst := Filtrator.suborder (α := α)))) := by
  constructor
  . intro
    obtain ⟨Fiso⟩ := (inferInstance : Nonempty (FiltratorIso α (FiltratorOfFilters (inst := Filtrator.suborder (α := α)))))
    exact ⟨Fiso⟩
    -- Wait, I should use to_filters_iso.
    -- exact ⟨to_filters_iso⟩ (but requires definition of Primary to produce iso).
    -- But logical equivalence...
    -- If Primary α, I constructed to_filters_iso.
  . intro h
    -- Construction of Primary from iso
    constructor
    use subset, suborder
    obtain ⟨iso⟩ := h
    -- iso : α ≃o Filters(suborder)
    -- We need Filters(suborder) ≃o α
    exact ⟨iso.symm⟩

instance : Nonempty (FiltratorIso α (FiltratorOfFilters (inst := Filtrator.suborder (α := α)))) := ⟨to_filters_iso⟩

end Filtrator.Primary
