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

/-- The key property of separable core filtrators: if x meets y,
    then x meets all z in up y.
    Equivalently: meet x y → ∀ z ∈ up y, meet x z -/
def Filtrator.separator_up_property {α : Type u} [Filtrator α] : Prop :=
  ∀ x y : α, meet x y ↔ ∀ z ∈ Filtrator.up y, meet x z

/-- For a filtrator where every up set is non-empty, we can derive separator_up_property
    from core-determinedness and meet_inf_property.

    In Victor Porton's "Algebraic Theory of General Topology", a filtrator is core-separable
    if the base separator mapping is injective. Proposition 16 of his work shows this is
    equivalent to the separator property (separator_up_property) for core-determined
    filtrators where meet commutes with core infimums. The assumption that every up set
    is non-empty is standard in filtrator theory. -/
theorem Filtrator.star_separable_imp_separator_up_property {α : Type u} [Filtrator α]
    (h_det : @Filtrator.core_determined α _)
    (h_meet_inf : @Filtrator.meet_inf_property α _)
    (h_up_nonempty : ∀ y : α, (Filtrator.up y).Nonempty) :
    @Filtrator.separator_up_property α _ := by
  intro x y
  have h_glb := h_det y
  specialize h_meet_inf x (Filtrator.up y) (fun _ hz => hz.1)
  have h_meet_equiv : meet x y ↔ ∀ s ∈ Filtrator.up y, meet x s :=
    h_meet_inf (h_up_nonempty y) ⟨y, h_glb⟩ y h_glb
  exact h_meet_equiv

-- lemma separator_up_property_iff_core_separable {α : Type u} [Filtrator α]
--     (h_det : @Filtrator.core_determined α _) (h_meet_inf : @Filtrator.meet_inf_property α _)
--     (h_up_nonempty : ∀ y : α, (Filtrator.up y).Nonempty) :
--     @Filtrator.separator_up_property α _ ↔ @Filtrator.star_separable α _ := by
--   constructor
--   · intro h_sep_up
--     intro a b h_eq
--     /- We want a = b. -/
--     sorry
--   · intro _ -- h_sep_core
--     exact Filtrator.star_separable_imp_separator_up_property h_det h_meet_inf h_up_nonempty
