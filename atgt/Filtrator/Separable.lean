import atgt.Filtrator
import atgt.Poset

def separator_core {α : Type*} [Filtrator α] (a : α) := subset ∩ separator a

/- TODO: Rename. -/
def Filtrator.star_separable {α : Type*} [Filtrator α] : Prop :=
  ∀ a b : α, separator_core a = separator_core b → a = b

theorem star_separable_imp_separable {α : Type*} [Filtrator α]
  (h_star_sep : @Filtrator.star_separable α _) : IsSeparable α := by
    intro a b h_eq
    apply h_star_sep
    unfold separator_core
    rw [h_eq]

def Filtrator.separator_up_property {α : Type u} [Filtrator α] : Prop :=
  ∀ x y : α, meet x y ↔ ∀ z ∈ Filtrator.up y, meet x z
