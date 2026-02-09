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

class Filtrator.Filtered (α : Type u) [Filtrator α] : Prop where
  is_filtered : ∀ x y : α, up x ⊆ up y → y ≤ x

/-- A filtrator is up-determined if every element is the infimum of its core upper set. -/
theorem Filtrator.up_determined_iff_filtered {α : Type u} [Filtrator α] :
  Filtrator.Filtered α ↔ ∀ x : α, IsGLB (Filtrator.up x) x := by
  constructor
  · intro h x
    constructor
    · intro y hy
      exact hy.2
    · intro y hy
      apply h.is_filtered
      intro z hz
      exact ⟨hz.1, hy hz⟩
  · intro h
    constructor
    intro x y h_subs
    apply (h x).2
    intro z hz
    exact (h y).1 (h_subs hz)

/- For simplicity, I define it only for semilattices. In the book it's more general. -/
def Filtrator.binary_meet_closed {α : Type u} [Filtrator α] [SemilatticeInf α] : Prop :=
  ∀ x y : α, x ∈ subset → y ∈ subset → x ⊓ y ∈ subset
