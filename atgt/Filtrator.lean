import Mathlib.Data.Ordmap.Ordset
import atgt.Poset

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
