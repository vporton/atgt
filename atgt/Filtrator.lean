import Mathlib.Data.Ordmap.Ordset

structure Filtrator (α : Type u) where
  order : PartialOrder α
  subset : Set α
