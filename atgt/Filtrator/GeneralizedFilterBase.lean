import atgt.Filtrator.Primary

/-!
# Generalized filter bases

Section 5.17 (Definitions 570/571 and Theorem 572) formalized for primary filtrators.
-/

namespace Filtrator.Primary

universe u

variable {α : Type u} [Filtrator α] [Primary α]

/-- Definition 570: a generalized filter base is a filter base on the core of a primary filtrator. -/
abbrev GeneralizedFilterBase (α : Type u) [Filtrator α] [Primary α] :=
  PosetFilterBase (Filtrator.suborder (α := α))

/--
Definition 571: a generalized filter base of `F` is a generalized filter base whose closure is
`up F` (as a filter on the core suborder).
-/
structure GeneralizedFilterBaseOf (F : α) where
  base : GeneralizedFilterBase α
  closes_to : close_filter_base base = to_poset_filter (α := α) F

/-- Theorem 572 (core equivalence): order form. -/
theorem le_iff_exists_base_le {F : α} (S : GeneralizedFilterBaseOf (α := α) F)
    (K : (subset : Set α)) :
    F ≤ K.1 ↔ ∃ L ∈ S.base.elements, L ≤ K := by
  constructor
  · intro hFK
    have hmem : K ∈ (close_filter_base S.base).elements := by
      simpa [S.closes_to] using (show K ∈ (to_poset_filter (α := α) F).elements from hFK)
    simpa [close_filter_base] using hmem
  · intro h
    have hmem : K ∈ (close_filter_base S.base).elements := by
      simpa [close_filter_base] using h
    simpa [S.closes_to] using (show K ∈ (close_filter_base S.base).elements from hmem)

/-- Theorem 572 (core equivalence): `K ∈ up F ↔ ∃ L ∈ S, K ∈ up L`. -/
theorem mem_up_iff_exists_mem_up {F : α} (S : GeneralizedFilterBaseOf (α := α) F)
    (K : (subset : Set α)) :
    K.1 ∈ Filtrator.up F ↔ ∃ L ∈ S.base.elements, K.1 ∈ Filtrator.up L.1 := by
  constructor
  · intro hK
    rcases (le_iff_exists_base_le (S := S) (K := K)).1 hK.2 with ⟨L, hL, hLK⟩
    exact ⟨L, hL, ⟨K.2, hLK⟩⟩
  · intro hK
    rcases hK with ⟨L, hL, hLK⟩
    exact ⟨K.2, (le_iff_exists_base_le (S := S) (K := K)).2 ⟨L, hL, hLK.2⟩⟩

end Filtrator.Primary
