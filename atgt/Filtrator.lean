import Mathlib.Data.Ordmap.Ordset
import Mathlib.Order.Bounds.Basic
import atgt.Poset
import Mathlib.Order.Bounds.Defs

class Filtrator (α : Type*) extends PartialOrder α where
  subset : Set α

export Filtrator (subset)

def Filtrator.suporder {α : Type*} [Filtrator α] : PartialOrder α := inferInstance

def Filtrator.suborder {α : Type*} [Filtrator α] : PartialOrder (subset : Set α) :=
  Subtype.partialOrder (· ∈ (subset : Set α))

def Filtrator.supset {α : Type u} [Filtrator α] := α

-- variable {α : Type*} [Filtrator α]

def Filtrator.up {α : Type u} [Filtrator α] (x: α) := { y ∈ subset | x ≤ y }

/- For simplicity, I define it only for semilattices. In the book it's more general. -/
def Filtrator.binary_meet_closed {α : Type u} [Filtrator α] [SemilatticeInf α] : Prop :=
  ∀ x y : α, x ∈ subset → y ∈ subset → x ⊓ y ∈ subset

structure FiltratorIso {α β : Type*} (a: Filtrator α) (b: Filtrator β) extends RelIso a.suporder.le b.suporder.le where
  core_match: toFun '' a.subset = b.subset
