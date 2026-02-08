import Mathlib.Data.Ordmap.Ordset
import Mathlib.Order.Bounds.Basic
import atgt.Poset
import Mathlib.Order.Bounds.Defs

open Atgt

class Filtrator (α : Type*) extends PartialOrder α where
  subset : Set α

export Filtrator (subset)

variable {α : Type*} [Filtrator α]

def Filtrator.suporder {α : Type*} [Filtrator α] : PartialOrder α := inferInstance

def Filtrator.suborder {α : Type*} [Filtrator α] : PartialOrder (subset : Set α) :=
  Subtype.partialOrder (· ∈ (subset : Set α))

def Filtrator.supset {α : Type u} [Filtrator α] := α

variable {α : Type*} [Filtrator α]

def Filtrator.up {α : Type u} [Filtrator α] (x: α) := { y ∈ subset | x ≤ y }

def Filtrator.separable_core {α : Type u} [Filtrator α] : Prop :=
  ∀ a b : α, base_separator (subset) a = base_separator (subset) b → a = b

/-- The key property of separable core filtrators: if x doesn't meet y,
    then there exists z in up y such that x doesn't meet z.
    Equivalently: separator y ⊆ ⋃{separator z | z ∈ up y} -/
def Filtrator.separator_up_property {α : Type u} [Filtrator α] : Prop :=
  ∀ x y : α, x ∈ separator y → ∃ z ∈ Filtrator.up y, x ∈ separator z

/-- For a filtrator with separator_up_property, meet with y is equivalent to meeting all elements in up y -/
theorem Filtrator.meet_iff_forall_up {α : Type u} [F : Filtrator α]
    (h_sep_up : F.separator_up_property) (x y : α) :
    meet x y ↔ ∀ z ∈ Filtrator.up y, meet x z := by
  constructor
  · intro h z hz
    exact Atgt.meet_mono_right hz.2 h
  · intro h
    by_contra h_neg
    /- h_neg : ¬meet x y means x ∈ separator y
       h : ∀ z ∈ up y, meet x z (so x ∉ separator z for all z ∈ up y)

       By separator_up_property: x ∈ separator y → ∃ z ∈ up y, x ∈ separator z
       This gives us z ∈ up y with x ∈ separator z, i.e., ¬meet x z.
       But h says meet x z for all such z. Contradiction! -/
    have h_in_sep : x ∈ separator y := h_neg
    obtain ⟨z, hz_up, hz_sep⟩ := h_sep_up x y h_in_sep
    have h_meet_z : meet x z := h z hz_up
    exact hz_sep h_meet_z

/-- A filtrator is core-determined if every element is the infimum of its core upper set. -/
def Filtrator.core_determined {α : Type u} [Filtrator α] : Prop :=
  ∀ x : α, IsGLB (Filtrator.up x) x

/-- The property that meet commutes with infimums from the core. -/
def Filtrator.meet_inf_property {α : Type u} [Filtrator α] : Prop :=
  ∀ x : α, ∀ S : Set α, S ⊆ subset → S.Nonempty → (∃ i, IsGLB S i) →
    (∀ i, IsGLB S i → (meet x i ↔ ∀ s ∈ S, meet x s))

/-- For a filtrator where every up set is non-empty, we can derive separator_up_property
    from core-determinedness and meet_inf_property.

    In Victor Porton's "Algebraic Theory of General Topology", a filtrator is core-separable
    if the base separator mapping is injective. Proposition 16 of his work shows this is
    equivalent to the separator property (separator_up_property) for core-determined
    filtrators where meet commutes with core infimums. The assumption that every up set
    is non-empty is standard in filtrator theory. -/
theorem Filtrator.separable_core_imp_separator_up_property {α : Type u} [Filtrator α]
    (h_det : @Filtrator.core_determined α _)
    (h_meet_inf : @Filtrator.meet_inf_property α _)
    (h_up_nonempty : ∀ y : α, (Filtrator.up y).Nonempty) :
    @Filtrator.separator_up_property α _ := by
  intro x y hx
  -- hx : x ∈ separator y, i.e., ¬ meet x y
  -- We want: ∃ z ∈ up y, x ∈ separator z
  by_contra h_neg
  -- h_neg : ∀ z ∈ up y, x ∉ separator z, i.e., ∀ z ∈ up y, meet x z
  simp [separator] at hx h_neg
  have h_glb := h_det y
  specialize h_meet_inf x (Filtrator.up y) (fun _ hz => hz.1)
  -- Use the non-emptiness assumption
  have h_meet_equiv : meet x y ↔ ∀ s ∈ Filtrator.up y, meet x s :=
    h_meet_inf (h_up_nonempty y) ⟨y, h_glb⟩ y h_glb
  rw [h_meet_equiv] at hx
  exact hx h_neg
