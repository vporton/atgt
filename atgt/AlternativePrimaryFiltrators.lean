import Mathlib.Data.Set.Basic
import Mathlib.Order.Lattice

universe u

namespace AlternativePrimaryFiltrators

variable {α : Type u}

def IsUpperSet [Preorder α] (F : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ∈ F → a ≤ b → b ∈ F

def IsLowerSet [Preorder α] (F : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ∈ F → b ≤ a → b ∈ F

def IsFilterSet [Preorder α] (F : Set α) : Prop :=
  Set.Nonempty F ∧
    ∀ a b : α, (a ∈ F ∧ b ∈ F) ↔ ∃ z : α, z ∈ F ∧ z ≤ a ∧ z ≤ b

def IsIdealSet [Preorder α] (F : Set α) : Prop :=
  Set.Nonempty F ∧
    ∀ a b : α, (a ∈ F ∧ b ∈ F) ↔ ∃ z : α, z ∈ F ∧ a ≤ z ∧ b ≤ z

def IsFreeStar [Preorder α] (F : Set α) : Prop :=
  F ≠ Set.univ ∧
    ∀ a b : α, (a ∉ F ∧ b ∉ F) ↔ ∃ z : α, z ∈ F ∧ a ≤ z ∧ b ≤ z

def IsMixer [Preorder α] (F : Set α) : Prop :=
  F ≠ Set.univ ∧
    ∀ a b : α, (a ∉ F ∧ b ∉ F) ↔ ∃ z : α, z ∈ F ∧ z ≤ a ∧ z ≤ b

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

theorem filter_upperSet [Preorder α] {F : Set α} (h : IsFilterSet F) : IsUpperSet F := by
  intro a b ha hab
  rcases h.1 with ⟨x, hx⟩
  rcases (h.2 a x).1 ⟨ha, hx⟩ with ⟨z, hz, hza, hzx⟩
  have hw : ∃ w : α, w ∈ F ∧ w ≤ b ∧ w ≤ x := ⟨z, hz, le_trans hza hab, hzx⟩
  exact ((h.2 b x).2 hw).1

theorem ideal_lowerSet [Preorder α] {F : Set α} (h : IsIdealSet F) : IsLowerSet F := by
  intro a b ha hba
  rcases h.1 with ⟨x, hx⟩
  rcases (h.2 a x).1 ⟨ha, hx⟩ with ⟨z, hz, haz, hxz⟩
  have hw : ∃ w : α, w ∈ F ∧ b ≤ w ∧ x ≤ w := ⟨z, hz, le_trans hba haz, hxz⟩
  exact ((h.2 b x).2 hw).1

theorem freeStar_upperSet [Preorder α] {F : Set α} (h : IsFreeStar F) : IsUpperSet F := by
  intro a b ha hab
  by_contra hb
  rcases exists_not_mem_of_ne_univ (hne := h.1) with ⟨x, hx⟩
  rcases (h.2 x b).1 ⟨hx, hb⟩ with ⟨z, hz, hxz, hbz⟩
  have haz : a ≤ z := le_trans hab hbz
  have hw : ∃ w : α, w ∈ F ∧ a ≤ w ∧ x ≤ w := ⟨z, hz, haz, hxz⟩
  exact ((h.2 a x).2 hw).1 ha

theorem mixer_lowerSet [Preorder α] {F : Set α} (h : IsMixer F) : IsLowerSet F := by
  intro a b ha hba
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
    exact ⟨hupper hab inf_le_left, hupper hab inf_le_right⟩
  · intro hab
    rcases (h.2 a b).1 hab with ⟨z, hz, hza, hzb⟩
    exact hupper hz (le_inf hza hzb)

theorem ideal_sup_mem_iff [SemilatticeSup α] (h : IsIdealSet F) (a b : α) :
    a ⊔ b ∈ F ↔ a ∈ F ∧ b ∈ F := by
  have hlower : IsLowerSet F := ideal_lowerSet h
  constructor
  · intro hab
    exact ⟨hlower hab le_sup_left, hlower hab le_sup_right⟩
  · intro hab
    rcases (h.2 a b).1 hab with ⟨z, hz, haz, hbz⟩
    exact hlower hz (sup_le haz hbz)

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

end AlternativePrimaryFiltrators
