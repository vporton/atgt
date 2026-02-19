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
abbrev GeneralizedFilterBase (α : Type u) [Filtrator.Primary α] :=
  PosetFilterBase (Filtrator.suborder (α := α))

/--
Definition 571: a generalized filter base of `F` is a generalized filter base whose closure is
`up F` (as a filter on the core suborder).
-/
structure GeneralizedFilterBaseOf {α : Type u} [Filtrator.Primary α] (F : α) where
  base : GeneralizedFilterBase α
  closes_to : close_filter_base base = to_poset_filter (α := α) F

/-- Theorem 572 (core equivalence): order form. -/
theorem le_iff_exists_base_le {α : Type u} [Filtrator.Primary α] {F : α}
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

namespace CoreEquivalence

variable {α : Type u}

/-- 1⇒2 in Theorem 572 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

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

end CoreEquivalence

export CoreEquivalence (mem_up_iff_exists_mem_up powerset_imp_mem_up_iff_exists_mem_up)

namespace BotInBaseCharacterization

variable {α : Type u}

/-- 1⇒2 in Corollary 573 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Corollary 573 tuple. -/
theorem bot_mem_base_iff_eq_bot [Filtrator.Primary α] [OrderBot α] {F : α}
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
theorem powerset_imp_bot_mem_base_iff_eq_bot [Filtrator.Powerset.{u, v} α] [OrderBot α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F) :
    (⟨⊥, hbot⟩ : (subset : Set α)) ∈ S.base.elements ↔ F = ⊥ := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact bot_mem_base_iff_eq_bot (hbot := hbot) (S := S)

end BotInBaseCharacterization

export BotInBaseCharacterization (bot_mem_base_iff_eq_bot powerset_imp_bot_mem_base_iff_eq_bot)

namespace NoBotBase

variable {α : Type u}

/-- 1⇒2 in Theorem 574 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Theorem 574 tuple. -/
theorem ne_bot_of_base_has_no_bot [Filtrator.Primary α] [OrderBot α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hno_bot : ∀ K : (subset : Set α), K ∈ S.base.elements → K.1 ≠ ⊥) :
    F ≠ ⊥ := by
  intro hFbot
  have hmem_bot : (⟨⊥, hbot⟩ : (subset : Set α)) ∈ S.base.elements :=
    (bot_mem_base_iff_eq_bot (hbot := hbot) (S := S)).2 hFbot
  exact (hno_bot ⟨⊥, hbot⟩ hmem_bot) rfl

/-- 1⇒3 in Theorem 574 tuple. -/
theorem powerset_imp_ne_bot_of_base_has_no_bot [Filtrator.Powerset.{u, v} α] [OrderBot α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hno_bot : ∀ K : (subset : Set α), K ∈ S.base.elements → K.1 ≠ ⊥) :
    F ≠ ⊥ := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact ne_bot_of_base_has_no_bot (hbot := hbot) (S := S) hno_bot

end NoBotBase

export NoBotBase (ne_bot_of_base_has_no_bot powerset_imp_ne_bot_of_base_has_no_bot)

namespace PairwiseMeetNoBot

variable {α : Type u}

/-- 1⇒2 in Corollary 575 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Corollary 575 tuple. -/
theorem ne_bot_of_pairwise_meet [Filtrator.Primary α] [OrderBot α] {F : α}
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
theorem powerset_imp_ne_bot_of_pairwise_meet [Filtrator.Powerset.{u, v} α] [OrderBot α] {F : α}
    (hbot : (⊥ : α) ∈ subset) (S : GeneralizedFilterBaseOf (α := α) F)
    (hpair :
      ∀ K L : (subset : Set α),
        K ∈ S.base.elements → L ∈ S.base.elements → meet K.1 L.1) :
    F ≠ ⊥ := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact ne_bot_of_pairwise_meet (hbot := hbot) (S := S) hpair

end PairwiseMeetNoBot

export PairwiseMeetNoBot (ne_bot_of_pairwise_meet powerset_imp_ne_bot_of_pairwise_meet)

namespace Prefilteredness

variable (α : Type u)

/-- 1⇒2 in Theorem 576 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

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

end Prefilteredness

export Prefilteredness (prefiltered_of_primary prefiltered_of_powerset)

section Atomicity

variable {α : Type u}

private theorem posetFilter_isAtomic_of_boolean (δ : Type u) [BooleanAlgebra δ] :
    let botPF : OrderBot (PosetFilter (U := (inferInstance : PartialOrder δ))) :=
      { bot := PosetFilter.principal (U := (inferInstance : PartialOrder δ)) (⊥ : δ)
        bot_le := by
          intro F x _
          exact (bot_le : (⊥ : δ) ≤ x) }
    @IsAtomic (PosetFilter (U := (inferInstance : PartialOrder δ)))
      (inferInstance : PartialOrder (PosetFilter (U := (inferInstance : PartialOrder δ))))
      botPF := by
  let U : PartialOrder δ := (inferInstance : PartialOrder δ)
  let botPF : OrderBot (PosetFilter (U := U)) := {
    bot := PosetFilter.principal (U := U) (⊥ : δ)
    bot_le := by
      intro F x hx
      exact (bot_le : (⊥ : δ) ≤ x) }
  letI : OrderBot (PosetFilter (U := U)) := botPF
  refine IsAtomic.of_isChain_bounded ?_
  intro c hc hne hbot
  let L : PosetFilter (U := U) := {
    elements := {x : δ | ∃ F ∈ c, x ∈ F.elements}
    non_empty := by
      rcases hne with ⟨F, hF⟩
      rcases F.non_empty with ⟨x, hx⟩
      exact ⟨x, ⟨F, hF, hx⟩⟩
    cap_elements := by
      intro x y hx hy
      rcases hx with ⟨F, hF, hxF⟩
      rcases hy with ⟨G, hG, hyG⟩
      rcases hc.total hF hG with hFG | hGF
      · have hyF : y ∈ F.elements := hFG hyG
        rcases F.cap_elements hxF hyF with ⟨z, hz, hzx, hzy⟩
        exact ⟨z, ⟨F, hF, hz⟩, hzx, hzy⟩
      · have hxG : x ∈ G.elements := hGF hxF
        rcases G.cap_elements hxG hyG with ⟨z, hz, hzx, hzy⟩
        exact ⟨z, ⟨G, hG, hz⟩, hzx, hzy⟩
    carrier := {x : δ | ∃ F ∈ c, x ∈ F.elements}
    upper' := by
      intro x y hxy hx
      rcases hx with ⟨F, hF, hxF⟩
      have hxF' : x ∈ F.carrier := by
        simpa [F.carrier_eq_elements] using hxF
      have hyF' : y ∈ F.carrier := F.upper' hxy hxF'
      exact ⟨F, hF, by simpa [F.carrier_eq_elements] using hyF'⟩
    carrier_eq_elements := rfl }
  have hL_ne_bot : L ≠ (⊥ : PosetFilter (U := U)) := by
    intro hLbot
    have hbot_mem_L : (⊥ : δ) ∈ L.elements := by
      have hbot_mem_bot : (⊥ : δ) ∈ (⊥ : PosetFilter (U := U)).elements := by
        change (⊥ : δ) ≤ (⊥ : δ)
        exact le_rfl
      simpa [hLbot] using hbot_mem_bot
    rcases hbot_mem_L with ⟨F, hF, hbotF⟩
    have hF_eq_bot : F = (⊥ : PosetFilter (U := U)) := by
      apply PosetFilter.ThroughEquiv.ext
      ext x
      constructor
      · intro hxF
        change (⊥ : δ) ≤ x
        exact bot_le
      · intro _
        have hbotF' : (⊥ : δ) ∈ F.carrier := by
          simpa [F.carrier_eq_elements] using hbotF
        have hxF' : x ∈ F.carrier := F.upper' (bot_le : (⊥ : δ) ≤ x) hbotF'
        simpa [F.carrier_eq_elements] using hxF'
    exact hbot (hF_eq_bot ▸ hF)
  have hL_lower : L ∈ lowerBounds c := by
    intro F hF x hxF
    exact ⟨F, hF, hxF⟩
  exact ⟨L, hL_ne_bot, hL_lower⟩

/-- Core-bottom membership criterion for `up x`, via Corollary 573 (`genbase-corr`). -/
lemma core_bot_mem_to_poset_filter_iff_eq_bot [Filtrator.Primary α] [OrderBot α]
    (hbot : (⊥ : α) ∈ subset) (x : α) :
    (⟨⊥, hbot⟩ : (subset : Set α)) ∈ (Filtrator.Primary.to_poset_filter (α := α) x).elements ↔ x = ⊥ := by
  let S : GeneralizedFilterBaseOf (α := α) x := {
    base := (Filtrator.Primary.to_poset_filter (α := α) x).toPosetFilterBase
    closes_to := by
      simpa using (PosetFilter.close_filter_base_toPosetFilterBase_eq_self
        (U := Filtrator.suborder (α := α))
        (Filtrator.Primary.to_poset_filter (α := α) x)) }
  simpa [S] using bot_mem_base_iff_eq_bot (hbot := hbot) (S := S)

/-- Theorem 576 (`filt-atomic`): primary filtrator over a boolean core is atomic. -/
theorem primary_imp_booleanAtomicCore [Filtrator.Primary α]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := α))]
    [OrderBot α]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := α)) :
    IsAtomic α := by
  letI : PartialOrder (Filtrator.subset (α := α)) := Bcore.toPartialOrder
  letI : OrderBot (PosetFilter (U := Bcore.toPartialOrder)) := {
    bot := PosetFilter.principal (U := Bcore.toPartialOrder) (⊥ : Filtrator.subset (α := α))
    bot_le := by
      intro F x hx
      exact (show @LE.le (Filtrator.subset (α := α)) Bcore.toLE
        (@Bot.bot (Filtrator.subset (α := α)) Bcore.toBot) x from Bcore.bot_le x) }
  have hAtomic_core_filters :
      IsAtomic (PosetFilter (U := Bcore.toPartialOrder)) :=
    posetFilter_isAtomic_of_boolean (δ := Filtrator.subset (α := α))
  let e_core :
      α ≃o PosetFilter (U := Bcore.toPartialOrder) :=
    ((Filtrator.Primary.to_filters_iso (α := α)).toRelIso.trans
      (PosetFilter.castOrderIso (h := hcoreOrder.symm)))
  have hAtomic_core : IsAtomic α := by
    exact (OrderIso.isAtomic_iff e_core).2 hAtomic_core_filters
  exact hAtomic_core

end Atomicity

end Filtrator.Primary
