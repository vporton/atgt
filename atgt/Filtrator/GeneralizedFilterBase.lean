import atgt.Filtrator.Primary
import atgt.Filtrator.Powerset

/-!
# Generalized filter bases

Section 5.17 (Definitions 570/571 and implication tuples 572-576), formalized in the current
Lean development.
-/

namespace Filtrator.Primary

universe u v

/-- Definition 570: a generalized filter base is a filter base on the core of a primary filtrator. -/
abbrev GeneralizedFilterBase (α : Type u) [Filtrator α] [Filtrator.Primary α] :=
  PosetFilterBase (Filtrator.suborder (α := α))

/--
Definition 571: a generalized filter base of `F` is a generalized filter base whose closure is
`up F` (as a filter on the core suborder).
-/
structure GeneralizedFilterBaseOf {α : Type u} [Filtrator α] [Filtrator.Primary α] (F : α) where
  base : GeneralizedFilterBase α
  closes_to : close_filter_base base = to_poset_filter (α := α) F

/-- Theorem 572 (core equivalence): order form. -/
theorem le_iff_exists_base_le {α : Type u} [Filtrator α] [Filtrator.Primary α] {F : α}
    (S : GeneralizedFilterBaseOf (α := α) F)
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

namespace Tuple572

variable {α : Type u} [Filtrator α]

/-- 1⇒2 in Theorem 572 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/-- 2⇒3 in Theorem 572 tuple. -/
theorem mem_up_iff_exists_mem_up [Filtrator.Primary α] {F : α}
    (S : GeneralizedFilterBaseOf (α := α) F) (K : (subset : Set α)) :
    K.1 ∈ Filtrator.up F ↔ ∃ L ∈ S.base.elements, K.1 ∈ Filtrator.up L.1 := by
  constructor
  · intro hK
    rcases (le_iff_exists_base_le (S := S) (K := K)).1 hK.2 with ⟨L, hL, hLK⟩
    exact ⟨L, hL, ⟨K.2, hLK⟩⟩
  · intro hK
    rcases hK with ⟨L, hL, hLK⟩
    exact ⟨K.2, (le_iff_exists_base_le (S := S) (K := K)).2 ⟨L, hL, hLK.2⟩⟩

/-- 1⇒3 in Theorem 572 tuple. -/
theorem powerset_imp_mem_up_iff_exists_mem_up [Filtrator.Powerset.{u, v} α] {F : α}
    (S : GeneralizedFilterBaseOf (α := α) F) (K : (subset : Set α)) :
    K.1 ∈ Filtrator.up F ↔ ∃ L ∈ S.base.elements, K.1 ∈ Filtrator.up L.1 := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact mem_up_iff_exists_mem_up (S := S) (K := K)

end Tuple572

export Tuple572 (mem_up_iff_exists_mem_up powerset_imp_mem_up_iff_exists_mem_up)

namespace Tuple573

variable {α : Type u} [Filtrator α] [OrderBot α]

/-- 1⇒2 in Corollary 573 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/-- 2⇒3 in Corollary 573 tuple. -/
theorem bot_mem_base_iff_eq_bot [Filtrator.Primary α] {F : α}
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

/-- 1⇒3 in Corollary 573 tuple. -/
theorem powerset_imp_bot_mem_base_iff_eq_bot [Filtrator.Powerset.{u, v} α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F) :
    (⟨⊥, hbot⟩ : (subset : Set α)) ∈ S.base.elements ↔ F = ⊥ := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact bot_mem_base_iff_eq_bot (hbot := hbot) (S := S)

end Tuple573

export Tuple573 (bot_mem_base_iff_eq_bot powerset_imp_bot_mem_base_iff_eq_bot)

namespace Tuple574

variable {α : Type u} [Filtrator α] [OrderBot α]

/-- 1⇒2 in Theorem 574 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/-- 2⇒3 in Theorem 574 tuple. -/
theorem ne_bot_of_base_has_no_bot [Filtrator.Primary α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hno_bot : ∀ K : (subset : Set α), K ∈ S.base.elements → K.1 ≠ ⊥) :
    F ≠ ⊥ := by
  intro hFbot
  have hmem_bot : (⟨⊥, hbot⟩ : (subset : Set α)) ∈ S.base.elements :=
    (bot_mem_base_iff_eq_bot (hbot := hbot) (S := S)).2 hFbot
  exact (hno_bot ⟨⊥, hbot⟩ hmem_bot) rfl

/-- 1⇒3 in Theorem 574 tuple. -/
theorem powerset_imp_ne_bot_of_base_has_no_bot [Filtrator.Powerset.{u, v} α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hno_bot : ∀ K : (subset : Set α), K ∈ S.base.elements → K.1 ≠ ⊥) :
    F ≠ ⊥ := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact ne_bot_of_base_has_no_bot (hbot := hbot) (S := S) hno_bot

end Tuple574

export Tuple574 (ne_bot_of_base_has_no_bot powerset_imp_ne_bot_of_base_has_no_bot)

namespace Tuple575

variable {α : Type u} [Filtrator α] [OrderBot α]

/-- 1⇒2 in Corollary 575 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/-- 2⇒3 in Corollary 575 tuple. -/
theorem ne_bot_of_pairwise_meet [Filtrator.Primary α] {F : α}
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

/-- 1⇒3 in Corollary 575 tuple. -/
theorem powerset_imp_ne_bot_of_pairwise_meet [Filtrator.Powerset.{u, v} α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hpair :
      ∀ K L : (subset : Set α),
        K ∈ S.base.elements → L ∈ S.base.elements → meet K.1 L.1) :
    F ≠ ⊥ := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact ne_bot_of_pairwise_meet (hbot := hbot) (S := S) hpair

end Tuple575

export Tuple575 (ne_bot_of_pairwise_meet powerset_imp_ne_bot_of_pairwise_meet)

namespace Tuple576

variable (α : Type u) [Filtrator α]

/-- 1⇒2 in Theorem 576 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/--
2⇒3 in Theorem 576 tuple.
In this development, the available formal consequence is prefilteredness.
-/
theorem prefiltered_of_primary [Filtrator.Primary α] : Filtrator.PreFiltered α := by
  exact filtered_imp_prefiltered α (Filtrator.primary_imp_filtered (α := α))

/-- 1⇒3 in Theorem 576 tuple (development-level consequence). -/
theorem prefiltered_of_powerset [Filtrator.Powerset.{u, v} α] : Filtrator.PreFiltered α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact prefiltered_of_primary α

end Tuple576

export Tuple576 (prefiltered_of_primary prefiltered_of_powerset)

end Filtrator.Primary
