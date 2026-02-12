import atgt.Filtrator
import atgt.Filtrator.Powerset
import atgt.Poset

def separator_core {α : Type*} [PartialOrder α] (F : Filtrator α) (a : α) := F.subset ∩ separator a

def Filtrator.of_subset {α : Type*} [PartialOrder α] (s : Set α) : Filtrator α :=
  { subset := s }

/- TODO: Rename. -/
def Filtrator.star_separable {α : Type*} (F : Filtrator α) : Prop :=
  ∀ a b : α, separator_core F a = separator_core F b → a = b

def has_separation_subset (α : Type*) [PartialOrder α] : Prop :=
  ∃ s : Set α, Filtrator.star_separable (Filtrator.of_subset s)

theorem star_separable_imp_separable {α : Type*} {F : Filtrator α}
  (h_star_sep : Filtrator.star_separable F) : IsSeparable α := by
    intro a b h_eq
    apply h_star_sep
    have h_core_eq : separator_core F a = separator_core F b := by
      simp [separator_core, h_eq]
    exact h_core_eq

lemma is_separable_imp_star_sep {α : Type*} [PartialOrder α]
  (h_sep : IsSeparable α) : Filtrator.star_separable (Filtrator.of_subset (Set.univ : Set α)) := by
  intro a b h_eq
  have h_sep_eq : separator a = separator b := by
    simpa [separator_core, Filtrator.of_subset, Set.univ_inter] using h_eq
  apply h_sep
  exact h_sep_eq

lemma star_sep_imp_has_subset {α : Type*} [PartialOrder α]
  (h : Filtrator.star_separable (Filtrator.of_subset (Set.univ : Set α))) : has_separation_subset α :=
  ⟨Set.univ, h⟩

theorem is_separable_implies_has_subset {α : Type*} [PartialOrder α] (h : IsSeparable α) :
    has_separation_subset α :=
  star_sep_imp_has_subset (is_separable_imp_star_sep h)

theorem has_subset_implies_is_separable {α : Type*} [PartialOrder α]
  (h : has_separation_subset α) : IsSeparable α := by
  rcases h with ⟨s, h_star⟩
  intro a b h_eq
  have h_core_eq : separator_core (Filtrator.of_subset s) a = separator_core (Filtrator.of_subset s) b := by
    calc
      separator_core (Filtrator.of_subset s) a = s ∩ separator a := by
        simp [separator_core, Filtrator.of_subset]
      _ = s ∩ separator b := congrArg (fun t => s ∩ t) h_eq
      _ = separator_core (Filtrator.of_subset s) b := by
        simp [separator_core, Filtrator.of_subset]
  apply h_star a b h_core_eq

theorem is_separable_iff_has_subset {α : Type*} [PartialOrder α] :
    IsSeparable α ↔ has_separation_subset α := by
  constructor
  · apply is_separable_implies_has_subset
  · apply has_subset_implies_is_separable

def Filtrator.separator_up_property {α : Type u} [Filtrator α] : Prop :=
  ∀ x y : α, meet x y ↔ ∀ z ∈ Filtrator.up y, meet x z

namespace StrongSeparability

universe u v

variable {α : Type u}

/-- "A is strongly separable" interpreted in the boolean-lattice order on `α`. -/
abbrev BooleanStronglySeparable (α : Type u) [BooleanAlgebra α] : Prop :=
  IsStronglySeparable α

/-- Boolean lattices are strongly separable (order-theoretic form used by Proposition 579). -/
theorem boolean_imp_stronglySeparable [BooleanAlgebra α] : BooleanStronglySeparable α := by
  intro a b h_sub
  by_contra h_not_le
  let x : α := a ⊓ bᶜ
  have hx_ne_bot : x ≠ ⊥ := by
    intro hx_bot
    have hdisj : Disjoint a bᶜ := by
      exact disjoint_iff.mpr (by simpa [x] using hx_bot)
    have hab : a ≤ b := by
      have hle : a ≤ (bᶜ)ᶜ := (le_compl_iff_disjoint_right).2 hdisj
      simpa using hle
    exact h_not_le hab
  have hx_not_least : ¬ is_least x := by
    intro hleast
    exact hx_ne_bot (le_antisymm (hleast ⊥) (bot_le : (⊥ : α) ≤ x))
  have hx_sep_a : x ∈ separator a := by
    change meet x a
    exact (meet_as_inf x a).2 (by simpa [x] using hx_not_least)
  have hx_not_sep_b : x ∉ separator b := by
    intro hx_sep_b
    change meet x b at hx_sep_b
    have hx_inf_b_not_least : ¬ is_least (x ⊓ b) := (meet_as_inf x b).1 hx_sep_b
    have hx_inf_b_eq_bot : x ⊓ b = ⊥ := by
      simp [x, inf_left_comm, inf_comm]
    have hleast_bot : is_least (⊥ : α) := by
      intro y
      exact (bot_le : (⊥ : α) ≤ y)
    exact hx_inf_b_not_least (hx_inf_b_eq_bot ▸ hleast_bot)
  exact hx_not_sep_b (h_sub hx_sep_a)

variable [Filtrator α]

/-- 1⇒2 in Proposition 579 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/-- 2⇒3 in Proposition 579 tuple. -/
theorem two_imp_three [Filtrator.Primary α] [BooleanAlgebra α] :
    BooleanStronglySeparable α := by
  exact boolean_imp_stronglySeparable (α := α)

/-- 1⇒3 in Proposition 579 tuple. -/
theorem one_imp_three [Filtrator.Powerset.{u, v} α] [BooleanAlgebra α] :
    BooleanStronglySeparable α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α)

end StrongSeparability

export StrongSeparability (two_imp_three one_imp_three)
