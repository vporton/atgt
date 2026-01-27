import Mathlib.Data.Ordmap.Ordset

universe u

structure PosetFilterBase{u}(A: PartialOrder u) where
  elements: Set u
  order: PartialOrder u
  non_empty: elements ≠ ∅
  cap_elements {x y} : ∃ z ∈ elements, (z ≤ x ∧ z ≤ y)

structure PosetFilter{u}(A: PartialOrder u) extends PosetFilterBase A where
  up_closed {x y} : x ∈ elements → x ≤ y → y ∈ elements
