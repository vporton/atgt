import Mathlib.Data.Set.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.Set
import Mathlib.Order.Defs.Unbundled
import atgt.Poset
import atgt.PosetFilter

universe u

namespace AlternativePrimaryFiltrators

variable {α : Type u}

def IsFilterSet [PartialOrder α] (F : Set α) : Prop :=
  Set.Nonempty F ∧
    ∀ a b : α, (a ∈ F ∧ b ∈ F) ↔ ∃ z : α, z ∈ F ∧ z ≤ a ∧ z ≤ b

def IsIdealSet [PartialOrder α] (F : Set α) : Prop :=
  Set.Nonempty F ∧
    ∀ a b : α, (a ∈ F ∧ b ∈ F) ↔ ∃ z : α, z ∈ F ∧ a ≤ z ∧ b ≤ z

def IsFreeStar [PartialOrder α] (F : Set α) : Prop :=
  F ≠ Set.univ ∧
    ∀ a b : α, (a ∉ F ∧ b ∉ F) ↔ ∃ z : α, z ∈ F ∧ a ≤ z ∧ b ≤ z

def IsMixer [PartialOrder α] (F : Set α) : Prop :=
  F ≠ Set.univ ∧
    ∀ a b : α, (a ∉ F ∧ b ∉ F) ↔ ∃ z : α, z ∈ F ∧ z ≤ a ∧ z ≤ b

-- This duplicates `PosetFilter`, but introduced here for uniformity.
class FilterSet [PartialOrder α] where
  elements: Set α
  non_side: Set.Nonempty elements
  main: ∀ a b : α, (a ∈ elements ∧ b ∈ elements) ↔ ∃ z : α, z ∈ elements ∧ z ≤ a ∧ z ≤ b

class FreeStar [PartialOrder α] where
  elements: Set α
  non_side: elements ≠ Set.univ
  main: ∀ a b : α, (a ∉ elements ∧ b ∉ elements) ↔ ∃ z : α, z ∈ elements ∧ a ≤ z ∧ b ≤ z

def posetFilter_to_filterSet [P: PartialOrder α] (F : PosetFilter P) : FilterSet (α := α) := {
  elements := F.elements
  non_side := F.non_empty
  main := by
    intro a b
    constructor
    · intro hab
      rcases F.cap_elements hab.1 hab.2 with ⟨z, hz, hza, hzb⟩
      exact ⟨z, hz, hza, hzb⟩
    · intro h
      rcases h with ⟨z, hz, hza, hzb⟩
      have hz_carrier : z ∈ F.carrier := by
        simpa [F.carrier_eq_elements] using hz
      have ha_carrier : a ∈ F.carrier := F.upper' hza hz_carrier
      have hb_carrier : b ∈ F.carrier := F.upper' hzb hz_carrier
      exact ⟨by simpa [F.carrier_eq_elements] using ha_carrier,
        by simpa [F.carrier_eq_elements] using hb_carrier⟩
}

def filterSet_to_freeStar [P: BooleanAlgebra α] (F : FilterSet (α := α)): FreeStar (α := α) := {
  elements := ((·ᶜ) '' F.elements)ᶜ
  non_side := sorry
  main := sorry
}

lemma exists_not_mem_of_ne_univ {F : Set α} (hne : F ≠ Set.univ) : ∃ x : α, x ∉ F := by
  classical
  by_contra h
  apply hne
  ext x
  constructor
  · intro hx
    trivial
  · intro _
    by_contra hx
    exact h ⟨x, hx⟩

theorem filter_upperSet [PartialOrder α] {F : Set α} (h : IsFilterSet F) : IsUpperSet F := by
  intro a b hle ha
  rcases h.1 with ⟨x, hx⟩
  rcases (h.2 a x).1 ⟨ha, hx⟩ with ⟨z, hz, hza, hzx⟩
  have hw : ∃ w : α, w ∈ F ∧ w ≤ b ∧ w ≤ x := ⟨z, hz, le_trans hza hle, hzx⟩
  exact ((h.2 b x).2 hw).1

theorem ideal_lowerSet [PartialOrder α] {F : Set α} (h : IsIdealSet F) : IsLowerSet F := by
  intro a b hba ha
  rcases h.1 with ⟨x, hx⟩
  rcases (h.2 a x).1 ⟨ha, hx⟩ with ⟨z, hz, haz, hxz⟩
  have hw : ∃ w : α, w ∈ F ∧ b ≤ w ∧ x ≤ w := ⟨z, hz, le_trans hba haz, hxz⟩
  exact ((h.2 b x).2 hw).1

theorem freeStar_upperSet [PartialOrder α] {F : Set α} (h : IsFreeStar F) : IsUpperSet F := by
  intro a b hle ha
  by_contra hb
  rcases exists_not_mem_of_ne_univ (hne := h.1) with ⟨x, hx⟩
  rcases (h.2 x b).1 ⟨hx, hb⟩ with ⟨z, hz, hxz, hbz⟩
  have haz : a ≤ z := le_trans hle hbz
  have hw : ∃ w : α, w ∈ F ∧ a ≤ w ∧ x ≤ w := ⟨z, hz, haz, hxz⟩
  exact ((h.2 a x).2 hw).1 ha

theorem mixer_lowerSet [PartialOrder α] {F : Set α} (h : IsMixer F) : IsLowerSet F := by
  intro a b hba ha
  by_contra hb
  rcases exists_not_mem_of_ne_univ (hne := h.1) with ⟨x, hx⟩
  rcases (h.2 x b).1 ⟨hx, hb⟩ with ⟨z, hz, hzx, hzb⟩
  have hza : z ≤ a := le_trans hzb hba
  have hw : ∃ w : α, w ∈ F ∧ w ≤ a ∧ w ≤ x := ⟨z, hz, hza, hzx⟩
  exact ((h.2 a x).2 hw).1 ha

section Semilattices

variable {F : Set α}

theorem filter_inf_mem_iff [SemilatticeInf α] (h : IsFilterSet F) (a b : α) :
    a ⊓ b ∈ F ↔ a ∈ F ∧ b ∈ F := by
  have hupper : IsUpperSet F := filter_upperSet h
  constructor
  · intro hab
    exact ⟨hupper inf_le_left hab, hupper inf_le_right hab⟩
  · intro hab
    rcases (h.2 a b).1 hab with ⟨z, hz, hza, hzb⟩
    exact hupper (le_inf hza hzb) hz

theorem ideal_sup_mem_iff [SemilatticeSup α] (h : IsIdealSet F) (a b : α) :
    a ⊔ b ∈ F ↔ a ∈ F ∧ b ∈ F := by
  have hlower : IsLowerSet F := ideal_lowerSet h
  constructor
  · intro hab
    exact ⟨hlower (le_sup_left) hab, hlower (le_sup_right) hab⟩
  · intro hab
    rcases (h.2 a b).1 hab with ⟨z, hz, haz, hbz⟩
    exact hlower (sup_le haz hbz) hz

theorem freeStar_sup_not_mem_iff [SemilatticeSup α] (h : IsFreeStar F) (a b : α) :
    a ⊔ b ∉ F ↔ a ∉ F ∧ b ∉ F := by
  constructor
  · intro hab
    rcases (h.2 (a ⊔ b) (a ⊔ b)).1 ⟨hab, hab⟩ with ⟨z, hz, hsz, _⟩
    have hw : ∃ w : α, w ∈ F ∧ a ≤ w ∧ b ≤ w := ⟨z, hz, le_trans le_sup_left hsz, le_trans le_sup_right hsz⟩
    exact (h.2 a b).2 hw
  · intro hab
    rcases (h.2 a b).1 hab with ⟨z, hz, haz, hbz⟩
    have hsupz : a ⊔ b ≤ z := sup_le haz hbz
    have hw : ∃ w : α, w ∈ F ∧ a ⊔ b ≤ w ∧ a ⊔ b ≤ w := ⟨z, hz, hsupz, hsupz⟩
    exact ((h.2 (a ⊔ b) (a ⊔ b)).2 hw).1

theorem freeStar_sup_mem_iff [SemilatticeSup α] (h : IsFreeStar F) (a b : α) :
    a ⊔ b ∈ F ↔ a ∈ F ∨ b ∈ F := by
  constructor
  · intro hab
    by_contra h_or
    have h_not : a ∉ F ∧ b ∉ F := by
      simpa [not_or] using h_or
    exact (freeStar_sup_not_mem_iff h a b).2 h_not hab
  · intro hab
    by_contra hsup
    have h_not : a ∉ F ∧ b ∉ F := (freeStar_sup_not_mem_iff h a b).1 hsup
    cases hab with
    | inl ha => exact h_not.1 ha
    | inr hb => exact h_not.2 hb

theorem mixer_inf_not_mem_iff [SemilatticeInf α] (h : IsMixer F) (a b : α) :
    a ⊓ b ∉ F ↔ a ∉ F ∧ b ∉ F := by
  constructor
  · intro hab
    rcases (h.2 (a ⊓ b) (a ⊓ b)).1 ⟨hab, hab⟩ with ⟨z, hz, hzs, _⟩
    have hw : ∃ w : α, w ∈ F ∧ w ≤ a ∧ w ≤ b := ⟨z, hz, le_trans hzs inf_le_left, le_trans hzs inf_le_right⟩
    exact (h.2 a b).2 hw
  · intro hab
    rcases (h.2 a b).1 hab with ⟨z, hz, hza, hzb⟩
    have hzinf : z ≤ a ⊓ b := le_inf hza hzb
    have hw : ∃ w : α, w ∈ F ∧ w ≤ a ⊓ b ∧ w ≤ a ⊓ b := ⟨z, hz, hzinf, hzinf⟩
    exact ((h.2 (a ⊓ b) (a ⊓ b)).2 hw).1

theorem mixer_inf_mem_iff [SemilatticeInf α] (h : IsMixer F) (a b : α) :
    a ⊓ b ∈ F ↔ a ∈ F ∨ b ∈ F := by
  constructor
  · intro hab
    by_contra h_or
    have h_not : a ∉ F ∧ b ∉ F := by
      simpa [not_or] using h_or
    exact (mixer_inf_not_mem_iff h a b).2 h_not hab
  · intro hab
    by_contra hinf
    have h_not : a ∉ F ∧ b ∉ F := (mixer_inf_not_mem_iff h a b).1 hinf
    cases hab with
    | inl ha => exact h_not.1 ha
    | inr hb => exact h_not.2 hb

theorem filter_upper_inf_mem_of_pair
    [SemilatticeInf α] (h : IsFilterSet F) :
    IsUpperSet F ∧ ∀ a b : α, a ∈ F ∧ b ∈ F → a ⊓ b ∈ F := by
  refine ⟨filter_upperSet h, ?_⟩
  intro a b hab
  exact (filter_inf_mem_iff h a b).2 hab

theorem ideal_lower_sup_mem_of_pair
    [SemilatticeSup α] (h : IsIdealSet F) :
    IsLowerSet F ∧ ∀ a b : α, a ∈ F ∧ b ∈ F → a ⊔ b ∈ F := by
  refine ⟨ideal_lowerSet h, ?_⟩
  intro a b hab
  exact (ideal_sup_mem_iff h a b).2 hab

theorem freeStar_upper_sup_imp_or
    [SemilatticeSup α] (h : IsFreeStar F) :
    IsUpperSet F ∧ F ≠ Set.univ ∧ ∀ a b : α, a ⊔ b ∈ F → a ∈ F ∨ b ∈ F := by
  refine ⟨freeStar_upperSet h, h.1, ?_⟩
  intro a b hab
  exact (freeStar_sup_mem_iff h a b).1 hab

theorem mixer_lower_inf_imp_or
    [SemilatticeInf α] (h : IsMixer F) :
    IsLowerSet F ∧ F ≠ Set.univ ∧ ∀ a b : α, a ⊓ b ∈ F → a ∈ F ∨ b ∈ F := by
  refine ⟨mixer_lowerSet h, h.1, ?_⟩
  intro a b hab
  exact (mixer_inf_mem_iff h a b).1 hab

end Semilattices

namespace GeneralDiagram

universe v

variable {β : Type v}

def push (e : α ≃ β) (X : Set α) : Set β := e '' X

def pull (e : α ≃ β) (Y : Set β) : Set α := e.symm '' Y

@[simp] theorem mem_push_iff (e : α ≃ β) {X : Set α} {b : β} :
    b ∈ push e X ↔ e.symm b ∈ X := by
  constructor
  · intro hb
    rcases hb with ⟨a, ha, rfl⟩
    simpa using ha
  · intro hb
    exact ⟨e.symm b, hb, by simp⟩

@[simp] theorem mem_pull_iff (e : α ≃ β) {Y : Set β} {a : α} :
    a ∈ pull e Y ↔ e a ∈ Y := by
  constructor
  · intro ha
    rcases ha with ⟨b, hb, rfl⟩
    simpa using hb
  · intro ha
    exact ⟨e a, ha, by simp⟩

theorem push_compl (e : α ≃ β) (X : Set α) :
    push e (Xᶜ) = (push e X)ᶜ := by
  ext b
  simp

theorem pull_compl (e : α ≃ β) (Y : Set β) :
    pull e (Yᶜ) = (pull e Y)ᶜ := by
  ext a
  simp

theorem pull_push (e : α ≃ β) (X : Set α) :
    pull e (push e X) = X := by
  ext a
  simp

theorem push_pull (e : α ≃ β) (Y : Set β) :
    push e (pull e Y) = Y := by
  ext b
  simp

theorem general_diagram_commutative (e : α ≃ β) :
    (∀ X : Set α, push e (Xᶜ) = (push e X)ᶜ) ∧
      (∀ Y : Set β, pull e (Yᶜ) = (pull e Y)ᶜ) := by
  exact ⟨push_compl e, pull_compl e⟩

theorem general_diagram_cycles_identity (e : α ≃ β) :
    (∀ X : Set α, pull e (push e X) = X) ∧
      (∀ Y : Set β, push e (pull e Y) = Y) := by
  exact ⟨pull_push e, push_pull e⟩

end GeneralDiagram

export GeneralDiagram
  (push pull push_compl pull_compl pull_push push_pull
    general_diagram_commutative general_diagram_cycles_identity)

namespace SpecialDiagrams

universe v

variable {β : Type v}

theorem dual_diagram_commutative (X : Set α) :
    push (OrderDual.toDual : α ≃ αᵒᵈ) (Xᶜ) =
      (push (OrderDual.toDual : α ≃ αᵒᵈ) X)ᶜ := by
  exact push_compl (OrderDual.toDual : α ≃ αᵒᵈ) X

theorem dual_diagram_cycles_identity :
    (∀ X : Set α, pull (OrderDual.toDual : α ≃ αᵒᵈ)
      (push (OrderDual.toDual : α ≃ αᵒᵈ) X) = X) ∧
      (∀ Y : Set αᵒᵈ, push (OrderDual.toDual : α ≃ αᵒᵈ)
        (pull (OrderDual.toDual : α ≃ αᵒᵈ) Y) = Y) := by
  exact general_diagram_cycles_identity (OrderDual.toDual : α ≃ αᵒᵈ)

theorem boolean_compl_diagram_commutative [BooleanAlgebra α] (X : Set α) :
    push (OrderIso.compl α).toEquiv (Xᶜ) =
      (push (OrderIso.compl α).toEquiv X)ᶜ := by
  exact push_compl (OrderIso.compl α).toEquiv X

theorem boolean_compl_diagram_cycles_identity [BooleanAlgebra α] :
    (∀ X : Set α, pull (OrderIso.compl α).toEquiv (push (OrderIso.compl α).toEquiv X) = X) ∧
      (∀ Y : Set α, push (OrderIso.compl α).toEquiv (pull (OrderIso.compl α).toEquiv Y) = Y) := by
  exact general_diagram_cycles_identity (OrderIso.compl α).toEquiv

end SpecialDiagrams

export SpecialDiagrams
  (dual_diagram_commutative dual_diagram_cycles_identity
    boolean_compl_diagram_commutative boolean_compl_diagram_cycles_identity)

namespace PrincipalConstructions

def principalIdeal [PartialOrder α] (a : α) : Set α := Set.Iic a

def principalUpper [PartialOrder α] (a : α) : Set α := Set.Ici a

def principalLower [PartialOrder α] (a : α) : Set α := Set.Iic a

def IsPrincipalIdeal [PartialOrder α] (F : Set α) : Prop := ∃ a : α, F = principalIdeal a

def IsPrincipalUpperSet [PartialOrder α] (F : Set α) : Prop := ∃ a : α, F = principalUpper a

def IsPrincipalLowerSet [PartialOrder α] (F : Set α) : Prop := ∃ a : α, F = principalLower a

def IsPrincipalFreeStar [PartialOrder α] (S : Set α) : Prop := IsFreeStar S ∧ IsPrincipalUpperSet S

def IsPrincipalMixer [PartialOrder α] (S : Set α) : Prop := IsMixer S ∧ IsPrincipalLowerSet S

def idealFiltrator [PartialOrder α] : Set (Set α) × Set (Set α) :=
  ({F : Set α | IsIdealSet F}, {F : Set α | IsPrincipalIdeal F})

def freeStarFiltrator [PartialOrder α] : Set (Set α) × Set (Set α) :=
  ({F : Set α | IsFreeStar F}, {F : Set α | IsPrincipalFreeStar F})

def mixerFiltrator [PartialOrder α] : Set (Set α) × Set (Set α) :=
  ({F : Set α | IsMixer F}, {F : Set α | IsPrincipalMixer F})

theorem mem_principalIdeal_iff [PartialOrder α] {a x : α} :
    x ∈ principalIdeal a ↔ x ≤ a := Iff.rfl

theorem principalIdeal_generated [PartialOrder α] (a : α) :
    principalIdeal a = {x : α | x ≤ a} := rfl

theorem ideal_principal_iff_generated [PartialOrder α] {F : Set α} :
    IsPrincipalIdeal F ↔ ∃ a : α, F = {x : α | x ≤ a} := by
  constructor
  · intro h
    rcases h with ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · intro h
    rcases h with ⟨a, ha⟩
    exact ⟨a, ha⟩

theorem principalUpper_iff_exists_least_mem [PartialOrder α] {F : Set α}
    (hF : IsUpperSet F) :
    IsPrincipalUpperSet F ↔ ∃ z : α, z ∈ F ∧ ∀ p : α, p ∈ F → z ≤ p := by
  constructor
  · intro h
    rcases h with ⟨z, rfl⟩
    refine ⟨z, le_rfl, ?_⟩
    intro p hp
    exact hp
  · intro h
    rcases h with ⟨z, hz, hmin⟩
    refine ⟨z, ?_⟩
    ext p
    constructor
    · intro hp
      exact hmin p hp
    · intro hp
      exact hF hp hz

theorem principalLower_iff_exists_greatest_mem [PartialOrder α] {F : Set α}
    (hF : IsLowerSet F) :
    IsPrincipalLowerSet F ↔ ∃ z : α, z ∈ F ∧ ∀ p : α, p ∈ F → p ≤ z := by
  constructor
  · intro h
    rcases h with ⟨z, rfl⟩
    refine ⟨z, le_rfl, ?_⟩
    intro p hp
    exact hp
  · intro h
    rcases h with ⟨z, hz, hmax⟩
    refine ⟨z, ?_⟩
    ext p
    constructor
    · intro hp
      exact hmax p hp
    · intro hp
      exact hF hp hz

theorem principalFreeStar_iff_exists_least_mem [PartialOrder α] {S : Set α}
    (hS : IsFreeStar S) :
    IsPrincipalFreeStar S ↔ ∃ z : α, z ∈ S ∧ ∀ p : α, p ∈ S → z ≤ p := by
  constructor
  · intro h
    exact (principalUpper_iff_exists_least_mem (hF := freeStar_upperSet hS)).1 h.2
  · intro h
    refine ⟨hS, ?_⟩
    exact (principalUpper_iff_exists_least_mem (hF := freeStar_upperSet hS)).2 h

theorem principalMixer_iff_exists_greatest_mem [PartialOrder α] {S : Set α}
    (hS : IsMixer S) :
    IsPrincipalMixer S ↔ ∃ z : α, z ∈ S ∧ ∀ p : α, p ∈ S → p ≤ z := by
  constructor
  · intro h
    exact (principalLower_iff_exists_greatest_mem (hF := mixer_lowerSet hS)).1 h.2
  · intro h
    refine ⟨hS, ?_⟩
    exact (principalLower_iff_exists_greatest_mem (hF := mixer_lowerSet hS)).2 h

end PrincipalConstructions

export PrincipalConstructions
  (principalIdeal principalUpper principalLower
    IsPrincipalIdeal IsPrincipalUpperSet IsPrincipalLowerSet IsPrincipalFreeStar IsPrincipalMixer
    idealFiltrator freeStarFiltrator mixerFiltrator
    mem_principalIdeal_iff principalIdeal_generated ideal_principal_iff_generated
    principalUpper_iff_exists_least_mem principalLower_iff_exists_greatest_mem
    principalFreeStar_iff_exists_least_mem principalMixer_iff_exists_greatest_mem)

namespace StarrishPosets

def IsFreeStarLike [SemilatticeSup α] (S : Set α) : Prop :=
  IsUpperSet S ∧ ∀ x y : α, x ⊔ y ∈ S → x ∈ S ∨ y ∈ S

def IsStarrish (α : Type u) [SemilatticeSup α] : Prop :=
  ∀ a : α, IsFreeStarLike (⋆a)

def atoms [SemilatticeSup α] (a : α) : Set α := {c : α | a ∈ ⋆c}

def IsCompletelyStarrish (α : Type u) [CompleteLattice α] : Prop :=
  ∀ a : α, IsFreeStarLike (⋆a) ∧ ∀ T : Set α, sSup T ∈ ⋆a ↔ ∃ x ∈ T, x ∈ ⋆a

theorem distributiveLattice_isStarrish (α : Type u) [DistribLattice α] :
    IsStarrish α := by
  intro a
  refine ⟨?_, ?_⟩
  · intro x y hxy hx
    have hx_meet : meet x a := by
      simpa [separator] using hx
    exact meet_mono_left hxy hx_meet
  · intro x y hxy
    have hxy_notleast : ¬ is_least ((x ⊔ y) ⊓ a) := (meet_as_inf (x ⊔ y) a).1 hxy
    have hxy_or : ¬ is_least (x ⊓ a) ∨ ¬ is_least (y ⊓ a) := by
      by_contra h
      push_neg at h
      have hleast_sup : is_least ((x ⊓ a) ⊔ (y ⊓ a)) := by
        intro t
        exact sup_le (h.1 t) (h.2 t)
      exact hxy_notleast (by simpa [inf_sup_right] using hleast_sup)
    rcases hxy_or with hx_notleast | hy_notleast
    · exact Or.inl ((meet_as_inf x a).2 hx_notleast)
    · exact Or.inr ((meet_as_inf y a).2 hy_notleast)

theorem atoms_sup_eq_union [SemilatticeSup α]
    (hstar : IsStarrish α) (a b : α) :
    atoms (a ⊔ b) = atoms a ∪ atoms b := by
  ext c
  rcases hstar c with ⟨hupper, hsup_imp_or⟩
  constructor
  · intro hc
    exact hsup_imp_or a b hc
  · intro hc
    cases hc with
    | inl ha => exact hupper (le_sup_left : a ≤ a ⊔ b) ha
    | inr hb => exact hupper (le_sup_right : b ≤ a ⊔ b) hb

theorem completelyStarrish_imp_starrish [CompleteLattice α]
    (h : IsCompletelyStarrish α) : IsStarrish α := by
  intro a
  exact (h a).1

theorem atoms_sSup_eq_iUnion_atoms [CompleteLattice α]
    (h : IsCompletelyStarrish α) (T : Set α) :
    atoms (sSup T) = ⋃ x ∈ T, atoms x := by
  ext c
  constructor
  · intro hc
    rcases ((h c).2 T).1 hc with ⟨x, hxT, hxc⟩
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hxT, hxc⟩⟩
  · intro hc
    rcases Set.mem_iUnion.1 hc with ⟨x, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hxT, hxc⟩
    exact ((h c).2 T).2 ⟨x, hxT, hxc⟩

theorem completeDistribLattice_isCompletelyStarrish (α : Type u) [CompleteDistribLattice α] :
    IsCompletelyStarrish α := by
  intro a
  refine ⟨(distributiveLattice_isStarrish α a), ?_⟩
  intro T
  constructor
  · intro hsSup
    by_contra h
    push_neg at h
    have hleast_x : ∀ x ∈ T, is_least (x ⊓ a) := by
      intro x hx
      apply not_not.mp
      intro hx_notleast
      exact (h x hx) ((meet_as_inf x a).2 hx_notleast)
    have hleast_sup : is_least (sSup T ⊓ a) := by
      intro t
      rw [sSup_inf_eq]
      refine iSup₂_le ?_
      intro x hx
      exact hleast_x x hx t
    exact ((meet_as_inf (sSup T) a).1 hsSup) hleast_sup
  · intro hmem
    rcases hmem with ⟨x, hxT, hxmem⟩
    exact meet_mono_left (le_sSup hxT) hxmem

end StarrishPosets

export StarrishPosets
  (IsFreeStarLike IsStarrish atoms IsCompletelyStarrish
    distributiveLattice_isStarrish atoms_sup_eq_union
    completelyStarrish_imp_starrish atoms_sSup_eq_iUnion_atoms
    completeDistribLattice_isCompletelyStarrish)

end AlternativePrimaryFiltrators
