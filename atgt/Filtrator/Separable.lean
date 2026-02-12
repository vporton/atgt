import atgt.Filtrator
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
