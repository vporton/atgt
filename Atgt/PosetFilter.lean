import Mathlib.Data.Ordmap.Ordset

universe u

structure PosetFilterBase{u}(U: PartialOrder u) where
  elements: Set u
  non_empty: Set.Nonempty elements
  cap_elements {x y} : ∃ z ∈ elements, (z ≤ x ∧ z ≤ y)

structure PosetFilter{u}(U: PartialOrder u) extends PosetFilterBase U where
  up_closed {x y} : x ∈ elements → x ≤ y → y ∈ elements

def close_filter_base (U : PartialOrder u)
  (B : PosetFilterBase U) : PosetFilter U :=
{ elements :=
    { y | ∃ x ∈ B.elements, x ≤ y }

  non_empty := by
    rcases B.non_empty with ⟨x, hx⟩
    exact ⟨x, x, hx, le_rfl⟩

  cap_elements := by
    intro x y
    rcases B.cap_elements (x := x) (y := y) with ⟨z, hz, hzx, hzy⟩
    refine ⟨z, ?_, hzx, hzy⟩
    exact ⟨z, hz, le_rfl⟩

  up_closed := by
    intro x y hx hxy
    rcases hx with ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx.trans hxy⟩
}
