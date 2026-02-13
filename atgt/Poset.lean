import Mathlib.Data.Ordmap.Ordset
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.Hom.Basic

universe u v u2 v2

instance {α: Type*} : Coe (SemilatticeInf α) (PartialOrder α) where
    coe s := s.toPartialOrder

/- TODO: Should be in `Ordset`, instead. -/
def is_least {α : Type*} [PartialOrder α] (a: α) := ∀ x, a ≤ x

/- TODO: Should be in `Ordset`, instead. -/
def meet {α : Type*}[PartialOrder α] (a b : α) := ∃ c, c ≤ a ∧ c ≤ b ∧ ¬ (is_least c)

theorem meet_comm {α : Type*} [PartialOrder α] (a b : α) : meet a b ↔ meet b a := by
    simp [meet]
    tauto

theorem meet_mono_left {α : Type*} [PartialOrder α] {a b c : α} (h : a ≤ b) : meet a c → meet b c := by
    intro h_meet
    rcases h_meet with ⟨d, hd_a, hd_c, hd_not_least⟩
    exact ⟨d, le_trans hd_a h, hd_c, hd_not_least⟩

theorem meet_mono_right {α : Type*} [PartialOrder α] {a b c : α} (h : b ≤ c) : meet a b → meet a c := by
    intro h_meet
    rcases h_meet with ⟨d, hd_a, hd_b, hd_not_least⟩
    exact ⟨d, hd_a, le_trans hd_b h, hd_not_least⟩

/- TODO: Should be in `Ordset`, instead. -/
theorem meet_as_inf {α : Type u}
  [s : SemilatticeInf α] (a b : α) :
  meet a b ↔
  ¬ is_least (a ⊓ b) :=
by
  constructor
  · intro h
    rcases h with ⟨c, hc₁, hc₂, hnot⟩
    intro hleast
    apply hnot
    intro x
    have := hleast x
    have hcab : c ≤ a ⊓ b :=
      le_inf hc₁ hc₂
    exact le_trans hcab this
  · intro h
    exact ⟨a ⊓ b, inf_le_left, inf_le_right, h⟩

def separator {α : Type u} [PartialOrder α] (a : α) := { x : α | meet x a }

prefix:80 "⋆" => separator

def IsSeparable (α : Type u) [PartialOrder α] := ∀ a b : α, separator a = separator b → a = b

def IsStronglySeparable (α : Type u) [PartialOrder α] := ∀ a b : α, separator a ⊆ separator b → a ≤ b

theorem le_imp_separator_subset {α : Type u} [PartialOrder α] {a b : α} (h : a ≤ b) :
    separator a ⊆ separator b := by
  intro x hx
  change meet x b
  exact meet_mono_right h hx

namespace SeparableStronglySeparable

theorem stronglySeparable_imp_separable {α : Type u} [PartialOrder α]
    (h : IsStronglySeparable α) : IsSeparable α := by
  intro a b h_eq
  have hab_sub : separator a ⊆ separator b := by
    simp [h_eq]
  have hba_sub : separator b ⊆ separator a := by
    simp [h_eq]
  have hab : a ≤ b := h a b hab_sub
  have hba : b ≤ a := h b a hba_sub
  exact le_antisymm hab hba

end SeparableStronglySeparable

export SeparableStronglySeparable (stronglySeparable_imp_separable)

namespace SemilatticeSeparableStronglySeparable

theorem separable_imp_stronglySeparable {α : Type u} [SemilatticeInf α]
    (h : IsSeparable α) : IsStronglySeparable α := by
  intro a b h_sub
  by_contra h_not_le
  have h_ne_inf : a ≠ a ⊓ b := by
    intro h_eq
    apply h_not_le
    calc
      a = a ⊓ b := h_eq
      _ ≤ b := inf_le_right
  have h_sep_ne : separator a ≠ separator (a ⊓ b) := by
    intro h_eq
    exact h_ne_inf (h a (a ⊓ b) h_eq)
  have h_inf_sub : separator (a ⊓ b) ⊆ separator a :=
    le_imp_separator_subset (a := a ⊓ b) (b := a) inf_le_left
  have h_not_sub : ¬ separator a ⊆ separator (a ⊓ b) := by
    intro h_sub'
    exact h_sep_ne (Set.Subset.antisymm h_sub' h_inf_sub)
  rcases Set.not_subset.mp h_not_sub with ⟨x, hx_sep_a, hx_not_sep_inf⟩
  let y := x ⊓ a
  have hy_not_least : ¬ is_least y := by
    have hx_not_least : ¬ is_least (x ⊓ a) := (meet_as_inf x a).1 hx_sep_a
    exact hx_not_least
  have hy_sep_a : y ∈ separator a := by
    refine ⟨y, le_rfl, ?_, hy_not_least⟩
    simp [y]
  have hy_not_sep_b : y ∉ separator b := by
    intro hy_sep_b
    have hyb_not_least : ¬ is_least (y ⊓ b) := (meet_as_inf y b).1 hy_sep_b
    have hxab_not_least : ¬ is_least (x ⊓ (a ⊓ b)) := by
      have heq : y ⊓ b = x ⊓ (a ⊓ b) := by
        simp [y]
        exact inf_assoc x a b
      exact heq ▸ hyb_not_least
    have hx_sep_inf : x ∈ separator (a ⊓ b) := (meet_as_inf x (a ⊓ b)).2 hxab_not_least
    exact hx_not_sep_inf hx_sep_inf
  exact hy_not_sep_b (h_sub hy_sep_a)

theorem separable_iff_stronglySeparable {α : Type u} [SemilatticeInf α] :
    IsSeparable α ↔ IsStronglySeparable α := by
  constructor
  · intro h_sep
    exact separable_imp_stronglySeparable h_sep
  · intro h_strong
    exact stronglySeparable_imp_separable h_strong

end SemilatticeSeparableStronglySeparable

export SemilatticeSeparableStronglySeparable
  (separable_imp_stronglySeparable separable_iff_stronglySeparable)

theorem isStronglySeparable_iff_star_orderEmbedding {α : Type u} [PartialOrder α] :
    IsStronglySeparable α ↔
      ∃ f : α ↪o Set α, (f : α → Set α) = separator := by
  constructor
  · intro h
    have map_rel : ∀ a b : α, separator a ≤ separator b ↔ a ≤ b := by
      intro a b
      constructor
      · intro h_sub
        have h_subset : separator a ⊆ separator b := (Set.le_iff_subset.mpr h_sub)
        exact h a b h_subset
      · intro hab
        exact Set.le_iff_subset.mpr (le_imp_separator_subset hab)
    let f := OrderEmbedding.ofMapLEIff (fun a => separator a) map_rel
    refine ⟨f, ?_⟩
    rfl
  · intro ⟨f, hf⟩ a b h_sub
    have hle : f a ≤ f b := by
      have h_sub_le : separator a ≤ separator b := h_sub
      have hfa : f a = separator a := congrFun hf a
      have hfb : f b = separator b := congrFun hf b
      simpa [hfa, hfb] using h_sub_le
    exact (OrderEmbedding.le_iff_le f).mp hle
