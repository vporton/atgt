import Mathlib.Data.Ordmap.Ordset
import atgt.Poset

structure Filtrator (α : Type u) where
  order : PartialOrder α
  subset : Set α

def Filtrator.supset {α : Type u} (F : Filtrator α) := α

def Filtrator.suborder {α : Type u} (F : Filtrator α) : PartialOrder F.subset :=
  @Subtype.partialOrder α F.order F.subset

def Filtrator.up {α : Type u} (F : Filtrator α) (x: α): Set α :=
  letI : PartialOrder α := F.order
  { y | x ≤ y }

def Filtrator.separable_core {α : Type u} (F : Filtrator α) : Prop :=
  ∀ a b : α, @base_separator α F.subset F.order a = @base_separator α F.subset F.order b → a = b
