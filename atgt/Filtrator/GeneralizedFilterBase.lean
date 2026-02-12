import atgt.Filtrator.Primary
import atgt.Filtrator.Powerset

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

/-- Corollary 573: for a generalized filter base of `F`, bottom is in the base iff `F = ⊥`. -/
theorem bot_mem_base_iff_eq_bot {F : α} [OrderBot α]
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F) :
    (⟨⊥, hbot⟩ : (subset : Set α)) ∈ S.base.elements ↔ F = ⊥ := by
  constructor
  · intro hmem
    have hFle : F ≤ (⟨⊥, hbot⟩ : (subset : Set α)).1 := by
      exact (le_iff_exists_base_le (S := S) (K := ⟨⊥, hbot⟩)).2 ⟨⟨⊥, hbot⟩, hmem, le_rfl⟩
    exact le_antisymm hFle bot_le
  · intro hFbot
    rcases (le_iff_exists_base_le (S := S) (K := ⟨⊥, hbot⟩)).1 (hFbot ▸ le_rfl) with
      ⟨L, hL, hLbot⟩
    have hEq : L = ⟨⊥, hbot⟩ := by
      apply Subtype.ext
      exact le_antisymm hLbot bot_le
    exact hEq ▸ hL

/-- Theorem 574: if the generalized base has no bottom element, then `F ≠ ⊥`. -/
theorem ne_bot_of_base_has_no_bot {F : α} [OrderBot α]
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hno_bot : ∀ K : (subset : Set α), K ∈ S.base.elements → K.1 ≠ ⊥) :
    F ≠ ⊥ := by
  intro hFbot
  have hmem_bot : (⟨⊥, hbot⟩ : (subset : Set α)) ∈ S.base.elements :=
    (bot_mem_base_iff_eq_bot (hbot := hbot) (S := S)).2 hFbot
  exact (hno_bot ⟨⊥, hbot⟩ hmem_bot) rfl

/--
Corollary 575 (binary-meet version): if every pair of base elements has a nontrivial meet,
then `F ≠ ⊥`.
-/
theorem ne_bot_of_pairwise_meet {F : α} [OrderBot α] [SemilatticeInf α]
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hpair :
      ∀ K L : (subset : Set α),
        K ∈ S.base.elements → L ∈ S.base.elements → meet K.1 L.1) :
    F ≠ ⊥ := by
  apply ne_bot_of_base_has_no_bot (hbot := hbot) (S := S)
  intro K hK hKbot
  have hKK : meet K.1 K.1 := hpair K K hK hK
  rcases hKK with ⟨c, hcK, _, hnotleast⟩
  apply hnotleast
  intro x
  have hcbot : c ≤ (⊥ : α) := by simpa [hKbot] using hcK
  exact le_trans hcbot bot_le

/--
Theorem 576 (development-level consequence): powerset filtrators are prefiltered.
This is the currently formalized consequence available from the existing hierarchy.
-/
theorem prefiltered_of_powerset (α : Type u) [Filtrator α] [Filtrator.Powerset α] :
    Filtrator.PreFiltered α := by
  exact filtered_imp_prefiltered α (Filtrator.primary_imp_filtered (α := α))

end Filtrator.Primary
