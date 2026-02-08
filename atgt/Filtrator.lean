import Mathlib.Data.Ordmap.Ordset
import atgt.Poset

class Filtrator (α : Type*) extends PartialOrder α where
  subset : Set α

export Filtrator (subset)

variable {α : Type*} [Filtrator α]

def Filtrator.suborder {α : Type*} [Filtrator α] : PartialOrder (subset : Set α) :=
  Subtype.partialOrder (· ∈ (subset : Set α))

def Filtrator.supset {α : Type u} [Filtrator α] := α

variable {α : Type*} [Filtrator α]

def Filtrator.up {α : Type u} [Filtrator α] (x: α): Set α :=
  { y | x ≤ y }

def Filtrator.separable_core {α : Type u} [Filtrator α] : Prop :=
  ∀ a b : α, base_separator (subset) a = base_separator (subset) b → a = b
