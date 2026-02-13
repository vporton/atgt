import atgt.Filtrator
import atgt.Filtrator.Powerset
import atgt.Poset
import Mathlib.Order.CompleteBooleanAlgebra

def separator_core {α : Type*} {F : Filtrator α} (a : α) :=
  F.subset ∩ @separator α F.toPartialOrder a

def Filtrator.of_subset {α : Type*} [PartialOrder α] (s : Set α) : Filtrator α :=
  { subset := s }

/- TODO: Rename. -/
def Filtrator.star_separable {α : Type*} [PartialOrder α] (F : Filtrator α) : Prop :=
  ∀ a b : α, separator_core (F := F) a = separator_core (F := F) b → a = b

def has_separation_subset (α : Type*) [PartialOrder α] : Prop :=
  ∃ s : Set α, Filtrator.star_separable (Filtrator.of_subset s)

theorem star_separable_imp_separable {α : Type*} {F : Filtrator α}
  (h_star_sep : Filtrator.star_separable F) : @IsSeparable α F.toPartialOrder := by
    intro a b h_eq
    apply h_star_sep
    have h_core_eq : separator_core (F := F) a = separator_core (F := F) b := by
      simpa [separator_core] using congrArg (fun s => F.subset ∩ s) h_eq
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
  let core := Filtrator.of_subset s
  intro a b h_eq
  have h_core_eq : separator_core (F := core) a = separator_core (F := core) b := by
    simp [separator_core, h_eq]
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

/-- Any complete Boolean algebra is separable (in its own order). -/
theorem completeBoolean_imp_separable (B : CompleteBooleanAlgebra α) : IsSeparable α := by
  letI : CompleteBooleanAlgebra α := B
  exact stronglySeparable_imp_separable (boolean_imp_stronglySeparable (α := α))

variable [Filtrator α]

/-- Proposition 579 core step with the correct assumption locus:
the core type is boolean, so the boolean-core order is strongly separable. -/
theorem primary_imp_booleanStronglySeparableCore [Filtrator.Primary α]
    [BooleanAlgebra (Filtrator.subset (α := α))] :
    @IsStronglySeparable (Filtrator.subset (α := α))
      (inferInstance : BooleanAlgebra (Filtrator.subset (α := α))).toPartialOrder := by
  exact boolean_imp_stronglySeparable (α := Filtrator.subset (α := α))

/-- Proposition 579 (core form): if the boolean-core order matches `Filtrator.suborder`,
the core suborder is separable. -/
theorem primary_imp_coreSeparable_of_boolean_core_order [Filtrator.Primary α]
    [BooleanAlgebra (Filtrator.subset (α := α))]
    (hcoreord :
      ∀ a b : Filtrator.subset (α := α),
        a ≤ b ↔
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : BooleanAlgebra (Filtrator.subset (α := α))).toPartialOrder.toLE a b) :
    @IsSeparable (Filtrator.subset (α := α)) (Filtrator.suborder (α := α)) := by
  let boolPO : PartialOrder (Filtrator.subset (α := α)) :=
    (inferInstance : BooleanAlgebra (Filtrator.subset (α := α))).toPartialOrder
  have h_sep_bool : @IsSeparable (Filtrator.subset (α := α)) boolPO := by
    exact stronglySeparable_imp_separable
      (primary_imp_booleanStronglySeparableCore (α := α))
  have h_isLeast :
      ∀ c : Filtrator.subset (α := α),
        @is_least (Filtrator.subset (α := α)) (Filtrator.suborder (α := α)) c ↔
          @is_least (Filtrator.subset (α := α)) boolPO c := by
    intro c
    constructor
    · intro hc x
      exact (hcoreord c x).1 (hc x)
    · intro hc x
      exact (hcoreord c x).2 (hc x)
  have h_meet :
      ∀ a b : Filtrator.subset (α := α),
        @meet (Filtrator.subset (α := α)) (Filtrator.suborder (α := α)) a b ↔
          @meet (Filtrator.subset (α := α)) boolPO a b := by
    intro a b
    constructor
    · intro h
      rcases h with ⟨c, hca, hcb, hc_notleast⟩
      refine ⟨c, (hcoreord c a).1 hca, (hcoreord c b).1 hcb, ?_⟩
      intro hc_least_bool
      exact hc_notleast ((h_isLeast c).2 hc_least_bool)
    · intro h
      rcases h with ⟨c, hca, hcb, hc_notleast⟩
      refine ⟨c, (hcoreord c a).2 hca, (hcoreord c b).2 hcb, ?_⟩
      intro hc_least_sub
      exact hc_notleast ((h_isLeast c).1 hc_least_sub)
  intro a b h_eq
  have h_eq_bool :
      @separator (Filtrator.subset (α := α)) boolPO a =
        @separator (Filtrator.subset (α := α)) boolPO b := by
    ext x
    have hx : x ∈ @separator (Filtrator.subset (α := α)) (Filtrator.suborder (α := α)) a ↔
        x ∈ @separator (Filtrator.subset (α := α)) (Filtrator.suborder (α := α)) b := by
      simpa using congrArg (fun s => x ∈ s) h_eq
    simpa [separator, h_meet x a, h_meet x b] using hx
  exact h_sep_bool a b h_eq_bool

end StrongSeparability

export StrongSeparability
  (primary_imp_booleanStronglySeparableCore primary_imp_coreSeparable_of_boolean_core_order)
