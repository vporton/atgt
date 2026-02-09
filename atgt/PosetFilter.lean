import Mathlib.Data.Ordmap.Ordset

universe u

structure PosetFilterBase{u}(U: PartialOrder u) where
  elements: Set u
  non_empty: Set.Nonempty elements
  cap_elements {x y} : x ∈ elements → y ∈ elements → ∃ z ∈ elements, (z ≤ x ∧ z ≤ y)

@[ext]
lemma PosetFilterBase.ext_elements {U : PartialOrder u}
  (F G : PosetFilterBase U)
  (h : F.elements = G.elements) : F = G := by
  cases F
  cases G
  cases h
  rfl

structure PosetFilter{u}(U: PartialOrder u) extends PosetFilterBase U where
  up_closed {x y} : x ∈ elements → x ≤ y → y ∈ elements

@[ext]
lemma PosetFilter.ext {U : PartialOrder u}
  (F G : PosetFilter U)
  (h : F.toPosetFilterBase = G.toPosetFilterBase) : F = G := by
  cases F
  cases G
  cases h
  rfl

def PosetFilter.principal {u} {U : PartialOrder u} (a : u) : PosetFilter U where
  elements := { x | a ≤ x }
  non_empty := ⟨a, le_rfl⟩
  cap_elements {x y} (hx : a ≤ x) (hy : a ≤ y) := ⟨a, le_rfl, hx, hy⟩
  up_closed {x y} (hx : a ≤ x) (hxy : x ≤ y) := hx.trans hxy

def close_filter_base {U : PartialOrder u}
  (B : PosetFilterBase U) : PosetFilter U :=
{ elements :=
    { y | ∃ x ∈ B.elements, x ≤ y }

  non_empty := by
    rcases B.non_empty with ⟨x, hx⟩
    exact ⟨x, x, hx, le_rfl⟩

  cap_elements := by
    intro x y hx hy
    rcases hx with ⟨x0, hx0, hx0_le_x⟩
    rcases hy with ⟨y0, hy0, hy0_le_y⟩
    rcases B.cap_elements hx0 hy0 with ⟨z, hz, hz_le_x0, hz_le_y0⟩
    refine ⟨z, ?_, hz_le_x0.trans hx0_le_x, hz_le_y0.trans hy0_le_y⟩
    exact ⟨z, hz, le_rfl⟩

  up_closed := by
    intro x y hx hxy
    rcases hx with ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx.trans hxy⟩
}

instance (U : PartialOrder u) : LE (PosetFilter U) :=
  ⟨fun F G => G.elements ⊆ F.elements⟩

instance (U : PartialOrder u) : PartialOrder (PosetFilter U) where
  le F G := G.elements ⊆ F.elements

  le_refl F := by
    intro x hx; exact hx

  le_trans F G H hFG hGH := by
    intro x hx
    exact hFG (hGH hx)

  le_antisymm F G hFG hGF := by
    apply PosetFilter.ext
    apply PosetFilterBase.ext_elements
    exact Set.Subset.antisymm hGF hFG
