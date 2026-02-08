import Mathlib.Data.Ordmap.Ordset

structure Filtrator (α : Type u) where
  order : PartialOrder α
  subset : Set α

def Filtrator.suborder (α : Type u) (F : Filtrator α) : PartialOrder F.subset :=
  @Subtype.partialOrder α F.order F.subset
