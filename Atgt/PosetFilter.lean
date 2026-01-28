import Mathlib.Data.Ordmap.Ordset

universe u

structure PosetFilterBase{u}(U: PartialOrder u) where
  elements: Set u
  order: PartialOrder u
  non_empty: elements ≠ ∅
  cap_elements {x y} : ∃ z ∈ elements, (z ≤ x ∧ z ≤ y)

structure PosetFilter{u}(U: PartialOrder u) extends PosetFilterBase U where
  up_closed {x y} : x ∈ elements → x ≤ y → y ∈ elements

def close_filter_base{u}(U: PartialOrder u)(B: PosetFilterBase U): PosetFilter  :=
  { elements := { x | ∃ y: B.elements, x ≤ y }
    order := B.order
    non_empty :=
      have ne: (elements ⊇ B.elements) := by simp
      show elements ≠ ∅ from by trans
    cap_elements := sorry
    up_closed := sorry }
