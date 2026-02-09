import Mathlib.Data.Ordmap.Ordset
import Mathlib.Order.Bounds.Basic
import atgt.Poset
import Mathlib.Order.Bounds.Defs

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

/-- A filtrator is core-determined if every element is the infimum of its core upper set. -/
def Filtrator.core_determined {α : Type u} [Filtrator α] : Prop :=
  ∀ x : α, IsGLB (Filtrator.up x) x

/-- The property that meet commutes with infimums from the core. -/
def Filtrator.meet_inf_property {α : Type u} [Filtrator α] : Prop :=
  ∀ x : α, ∀ S : Set α, S ⊆ subset → S.Nonempty → (∃ i, IsGLB S i) →
    (∀ i, IsGLB S i → (meet x i ↔ ∀ s ∈ S, meet x s))
