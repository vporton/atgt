import atgt.Filtrator.Primary
import atgt.Filtrator.Powerset
import atgt.AlternativePrimaryFiltrators
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# More advanced properties of filters (Section 5.8)

This file adds Theorem 516 and the implication tuples Corollary 517 / Corollary 518
(from volume-1, pp. 85-86), in the current development vocabulary.
-/

universe u v

/--
Corollary-517 condition (3), rendered in the current formal vocabulary:
for every nonempty family `S`, its supremum exists and the upper set of this supremum is the
intersection of upper sets of elements of `S`.
-/
def NonemptyInfUpInter (α : Type u) [Filtrator α] : Prop :=
  ∀ S : Set α, S.Nonempty →
    ∃ d : α, IsLUB S d ∧ Filtrator.up d = {x : α | ∀ s ∈ S, x ∈ Filtrator.up s}

/--
Lemma 512 (p. 85), in the form used for filters:
if an order embedding sends some `d : α` to the infimum of `f '' S` in a complete lattice,
then `d` is the infimum of `S`.
-/
theorem lemma512 {α : Type u} {β : Type v}
    [PartialOrder α] [CompleteLattice β]
    (f : α ↪o β) (S : Set α)
    (h : ∃ d : α, IsGLB (f '' S) (f d)) :
    ∃ d : α, IsGLB S d ∧ sInf (f '' S) = f d := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, ?_, hd.sInf_eq⟩
  refine ⟨?_, ?_⟩
  · intro a ha
    exact f.le_iff_le.mp (hd.1 ⟨a, ha, rfl⟩)
  · intro z hz
    apply f.le_iff_le.mp
    apply hd.2
    intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    exact f.monotone (hz ha)

/--
Theorem 515 (p. 85), filter side in the current framework:
for every nonempty bounded-above family `S`, its supremum exists and the upper set
of this supremum is the intersection of upper sets of elements of `S`.
-/
theorem theorem515 {α : Type u}
    [SemilatticeInf α] [Filtrator.Primary α] :
    (∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) →
    Filtrator.binary_meet_closed (α := α) →
    ∀ S : Set α, S.Nonempty → BddAbove S →
      ∃ d : α, IsLUB S d ∧ Filtrator.up d = {x : α | ∀ s ∈ S, x ∈ Filtrator.up s} := by
  intro hord h_closed S hS hBdd
  have h_nonempty : ∀ a : α, Set.Nonempty (Filtrator.up a) := by
    intro a
    rcases Filtrator.Primary.exists_up_in_subset (α := α) a with ⟨y, hy⟩
    exact ⟨y.1, y.2, hy⟩
  have h_bin_closed_iff :=
    Filtrator.binary_meet_closed_iff_up_filters
      (α := α) (h_nonempty := h_nonempty) (hord := hord)
  have h_exists_concrete_up :
      ∀ F : PosetFilter (Filtrator.suborder (α := α)),
        ∃ d : α, Filtrator.Primary.to_poset_filter (α := α) d = F := by
    intro F
    exact Filtrator.Primary.exists_to_poset_filter_eq (α := α) F
  have h_filtered : Filtrator.Filtered α := Filtrator.primary_imp_filtered (α := α)
  let T : Set (subset : Set α) := {y | ∀ s ∈ S, s ≤ y.1}
  have hT_nonempty : Set.Nonempty T := by
    rcases hBdd with ⟨u, hu⟩
    rcases h_nonempty u with ⟨x, hx⟩
    refine ⟨⟨x, hx.1⟩, ?_⟩
    intro s hs
    exact le_trans (hu hs) hx.2
  let F : PosetFilter (Filtrator.suborder (α := α)) := {
    elements := T
    non_empty := hT_nonempty
    cap_elements := by
      intro a b ha hb
      let c0 : α := a.1 ⊓ b.1
      have hc0 : c0 ∈ subset := h_closed a.1 b.1 a.2 b.2
      refine ⟨⟨c0, hc0⟩, ?_, ?_, ?_⟩
      · intro s hs
        have hsa' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE s a.1 :=
          (hord s a.1).1 (ha s hs)
        have hsb' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE s b.1 :=
          (hord s b.1).1 (hb s hs)
        have hsc' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE s c0 :=
          le_inf hsa' hsb'
        exact (hord s c0).2 hsc'
      · exact (hord c0 a.1).2 inf_le_left
      · exact (hord c0 b.1).2 inf_le_right
    carrier := T
    upper' := by
      intro a b hab ha s hs
      exact le_trans (ha s hs) hab
    carrier_eq_elements := rfl
  }
  rcases h_exists_concrete_up F with ⟨d, hdF⟩
  have hd_char : ∀ x : α, x ∈ subset → (d ≤ x ↔ ∀ s ∈ S, s ≤ x) := by
    intro x hxsub
    constructor
    · intro hdx
      have hx_to : (⟨x, hxsub⟩ : subset) ∈ (Filtrator.Primary.to_poset_filter (α := α) d).elements := by
        simpa [Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hdx
      have hx_F : (⟨x, hxsub⟩ : subset) ∈ F.elements := by simpa [hdF] using hx_to
      simpa [F, T] using hx_F
    · intro hxall
      have hx_F : (⟨x, hxsub⟩ : subset) ∈ F.elements := by
        simpa [F, T] using hxall
      have hx_to : (⟨x, hxsub⟩ : subset) ∈ (Filtrator.Primary.to_poset_filter (α := α) d).elements := by
        simpa [hdF] using hx_F
      simpa [Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hx_to
  refine ⟨d, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s hs
      have h_up_sub : Filtrator.up d ⊆ Filtrator.up s := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        exact (hd_char x hx.1).1 hx.2 s hs
      exact (Filtrator.Primary.order_determined (α := α) s d).2 h_up_sub
    · intro z hz
      have h_up_sub : Filtrator.up z ⊆ Filtrator.up d := by
        intro x hx
        have hxall : ∀ s ∈ S, s ≤ x := by
          intro s hs
          exact le_trans (hz hs) hx.2
        exact ⟨hx.1, (hd_char x hx.1).2 hxall⟩
      exact (Filtrator.Primary.order_determined (α := α) d z).2 h_up_sub
  · ext x
    constructor
    · intro hx
      refine ?_
      intro s hs
      exact ⟨hx.1, (hd_char x hx.1).1 hx.2 s hs⟩
    · intro hx
      rcases hS with ⟨s0, hs0⟩
      have hxsub : x ∈ subset := (hx s0 hs0).1
      have hxall : ∀ s ∈ S, s ≤ x := by
        intro s hs
        exact (hx s hs).2
      exact ⟨hxsub, (hd_char x hxsub).2 hxall⟩

/--
Theorem 516 (pp. 85-86), formalized in the present framework as the meet-side statement
used by Corollaries 517/518.
-/
theorem theorem516 {α : Type u}
    [SemilatticeInf α]
    [hTop : @OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Primary α] :
    (∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) →
    NonemptyInfUpInter α := by
  intro hord S hS
  have hTopSub : (⊤ : α) ∈ subset := by
    rcases Filtrator.Primary.exists_up_in_subset (α := α) (⊤ : α) with ⟨y, hy⟩
    have hy_top_semilat :
        @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE y.1 ⊤ :=
      @OrderTop.le_top α _ hTop y.1
    have hy_top : y.1 ≤ (⊤ : α) := (hord y.1 ⊤).2 hy_top_semilat
    have hyEq : y.1 = (⊤ : α) := le_antisymm hy_top hy
    exact hyEq ▸ y.2
  let T : Set (subset : Set α) := {y | ∀ s ∈ S, s ≤ y.1}
  have hT_nonempty : Set.Nonempty T := by
    refine ⟨⟨⊤, hTopSub⟩, ?_⟩
    intro s hs
    have hs_top_semilat :
        @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE s ⊤ :=
      @OrderTop.le_top α _ hTop s
    exact (hord s ⊤).2 hs_top_semilat
  let F : PosetFilter (Filtrator.suborder (α := α)) := {
    elements := T
    non_empty := hT_nonempty
    cap_elements := by
      intro a b ha hb
      let x0 : α := a.1 ⊓ b.1
      have hx0a : x0 ≤ a.1 := by
        exact (hord x0 a.1).2 (by simp [x0, inf_le_left])
      have hx0b : x0 ≤ b.1 := by
        exact (hord x0 b.1).2 (by simp [x0, inf_le_right])
      rcases Filtrator.Primary.directed_up_in_subset (α := α) x0 a b hx0a hx0b with
        ⟨c, hcx0, hca, hcb⟩
      refine ⟨c, ?_, hca, hcb⟩
      intro s hs
      have hsx0' :
          @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE s x0 := by
        have hsa' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE s a.1 :=
          (hord s a.1).1 (ha s hs)
        have hsb' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE s b.1 :=
          (hord s b.1).1 (hb s hs)
        simpa [x0] using (le_inf hsa' hsb')
      have hsx0 : s ≤ x0 := (hord s x0).2 hsx0'
      exact le_trans hsx0 hcx0
    carrier := T
    upper' := by
      intro a b hab ha s hs
      exact le_trans (ha s hs) hab
    carrier_eq_elements := rfl
  }
  rcases Filtrator.Primary.exists_to_poset_filter_eq (α := α) F with ⟨d, hdF⟩
  have hd_char : ∀ x : α, x ∈ subset → (d ≤ x ↔ ∀ s ∈ S, s ≤ x) := by
    intro x hxsub
    constructor
    · intro hdx
      have hx_to : (⟨x, hxsub⟩ : subset) ∈ (Filtrator.Primary.to_poset_filter (α := α) d).elements := by
        simpa [Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hdx
      have hx_F : (⟨x, hxsub⟩ : subset) ∈ F.elements := by simpa [hdF] using hx_to
      simpa [F, T] using hx_F
    · intro hxall
      have hx_F : (⟨x, hxsub⟩ : subset) ∈ F.elements := by
        simpa [F, T] using hxall
      have hx_to : (⟨x, hxsub⟩ : subset) ∈ (Filtrator.Primary.to_poset_filter (α := α) d).elements := by
        simpa [hdF] using hx_F
      simpa [Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hx_to
  refine ⟨d, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s hs
      have h_up_sub : Filtrator.up d ⊆ Filtrator.up s := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        exact (hd_char x hx.1).1 hx.2 s hs
      exact (Filtrator.Primary.order_determined (α := α) s d).2 h_up_sub
    · intro z hz
      have hz' : ∀ s ∈ S, s ≤ z := hz
      have h_up_sub : Filtrator.up z ⊆ Filtrator.up d := by
        intro x hx
        have hxall : ∀ s ∈ S, s ≤ x := by
          intro s hs
          exact le_trans (hz' s hs) hx.2
        exact ⟨hx.1, (hd_char x hx.1).2 hxall⟩
      exact (Filtrator.Primary.order_determined (α := α) d z).2 h_up_sub
  · ext x
    constructor
    · intro hx s hs
      exact ⟨hx.1, (hd_char x hx.1).1 hx.2 s hs⟩
    · intro hx
      rcases hS with ⟨s0, hs0⟩
      have hxsub : x ∈ subset := (hx s0 hs0).1
      have hxall : ∀ s ∈ S, s ≤ x := by
        intro s hs
        exact (hx s hs).2
      exact ⟨hxsub, (hd_char x hxsub).2 hxall⟩

namespace PrimaryMeetTopInfimumTuple

variable {α : Type u}

/-- 1⇒2 in Corollary 517 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Corollary 517 tuple. -/
theorem two_imp_three
    [SemilatticeInf α]
    [@OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Primary α]
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) :
    NonemptyInfUpInter α := by
  exact theorem516 (α := α) hord

/-- 1⇒3 in Corollary 517 tuple. -/
theorem one_imp_three
    [SemilatticeInf α]
    [@OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Powerset.{u, v} α] :
    (∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) →
    NonemptyInfUpInter α := by
  intro hord
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α) hord

end PrimaryMeetTopInfimumTuple

export PrimaryMeetTopInfimumTuple (two_imp_three one_imp_three)

namespace PrimaryMeetTopCompleteLatticeTuple

variable {α : Type u}

/- TODO: Rename below. -/

/-- 1⇒2 in Corollary 518 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Corollary 518 tuple. -/
noncomputable def two_imp_three
    [SemilatticeInf α]
    [hTop : @OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [hBot : @OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Primary α] :
    (∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) →
    CompleteLattice α := by
  intro hord
  classical
  let sSupFun : Set α → α := fun S =>
    if hS : S.Nonempty then
      Classical.choose (theorem516 (α := α) hord S hS)
    else
      ⊥
  letI : SupSet α := ⟨sSupFun⟩
  refine completeLatticeOfSup α ?_
  intro S
  by_cases hS : S.Nonempty
  · have hsSup :
      sSup S = Classical.choose (theorem516 (α := α) hord S hS) := by
      change sSupFun S = Classical.choose (theorem516 (α := α) hord S hS)
      simp [sSupFun, hS]
    exact hsSup ▸ (Classical.choose_spec (theorem516 (α := α) hord S hS)).1
  · have hSEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hSEmpty
    have hsSupEmpty : sSup (∅ : Set α) = (⊥ : α) := by
      change sSupFun (∅ : Set α) = (⊥ : α)
      simp [sSupFun]
    have hIsLubEmpty : IsLUB (∅ : Set α) (⊥ : α) := by
      refine ⟨?_, ?_⟩
      · intro a ha
        exact False.elim ha
      · intro z hz
        have hbot_semilat :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE ⊥ z :=
          @OrderBot.bot_le α _ hBot z
        exact (hord (⊥ : α) z).2 hbot_semilat
    exact hsSupEmpty ▸ hIsLubEmpty

/-- 1⇒3 in Corollary 518 tuple. -/
noncomputable def one_imp_three
    [SemilatticeInf α]
    [@OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [@OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Powerset.{u, v} α] :
    (∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) →
    CompleteLattice α := by
  intro hord
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α) hord

end PrimaryMeetTopCompleteLatticeTuple

export PrimaryMeetTopCompleteLatticeTuple (two_imp_three one_imp_three)

/--
Theorem 530 (`f-inf-assc`) rendered in the current vocabulary:
left-sup distributes over arbitrary infimum.
-/
def SupSInfAssoc (α : Type u) [CompleteLattice α] : Prop :=
  ∀ a : α, ∀ S : Set α, a ⊔ sInf S = sInf ((fun x : α => a ⊔ x) '' S)

namespace FilterInfAssociativity

variable {α : Type u}

/-- 1⇒2 in Theorem 530 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Theorem 530 tuple (development-level complete-distributive form). -/
theorem two_imp_three
    [Filtrator α] [Filtrator.Primary α] [CompleteDistribLattice α] :
    SupSInfAssoc α := by
  intro a S
  simpa [sInf_image] using (sup_sInf_eq (a := a) (s := S))

/-- 1⇒3 in Theorem 530 tuple. -/
theorem one_imp_three
    [Filtrator.Powerset.{u, v} α] [CompleteDistribLattice α] :
    SupSInfAssoc α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α)

end FilterInfAssociativity

export FilterInfAssociativity (two_imp_three one_imp_three)

namespace FilterAlsoDistributive

variable {α : Type u}

/-- 1⇒2 in Corollary 531 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Corollary 531 tuple: the filter lattice is distributive. -/
noncomputable def two_imp_three
    [Filtrator α] [Filtrator.Primary α] [DistribLattice α] :
    DistribLattice α := by
  infer_instance

/-- 1⇒3 in Corollary 531 tuple. -/
noncomputable def one_imp_three
    [Filtrator.Powerset.{u, v} α] [DistribLattice α] :
    DistribLattice α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α)

end FilterAlsoDistributive

export FilterAlsoDistributive (two_imp_three one_imp_three)

/--
Core-join alignment (`correct joining` style): if `d` is a least upper bound of a family of
core elements (with the core/suborder order), then `d.1` is a least upper bound of the
corresponding family in the ambient order.
-/
def Filtrator.CoreJoinAligned (α : Type u) [Filtrator α] : Prop :=
  ∀ S : Set (subset : Set α), ∀ d : (subset : Set α),
    IsLUB S d → IsLUB (Subtype.val '' S) d.1

namespace FilteredJoinClosedCore

variable {α : Type u}

/-- 1⇒2 in Theorem 534 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Theorem 534 tuple. -/
lemma two_imp_three [Filtrator.Primary α] : Filtrator.Filtered α :=
  Filtrator.primary_imp_filtered (α := α)

/-- 3⇒4 in Theorem 534 tuple. -/
lemma three_imp_four [Filtrator α] [Filtrator.Filtered α] : Filtrator.CoreJoinAligned α := by
  intro S d hd
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with ⟨s, hs, rfl⟩
    exact hd.1 hs
  · intro a ha
    have h_up_sub : Filtrator.up a ⊆ Filtrator.up d.1 := by
      intro c hc
      have hc_upper_core : ∀ s ∈ S, s ≤ (⟨c, hc.1⟩ : (subset : Set α)) := by
        intro s hs
        have hs_le_a : s.1 ≤ a := ha ⟨s, hs, rfl⟩
        exact show s.1 ≤ c from le_trans hs_le_a hc.2
      have hd_le_c : d ≤ (⟨c, hc.1⟩ : (subset : Set α)) := hd.2 hc_upper_core
      exact ⟨hc.1, hd_le_c⟩
    exact (Filtrator.Filtered.is_filtered (α := α) a d.1 h_up_sub)

/-- 2⇒4 in Theorem 534 tuple. -/
theorem two_imp_four [Filtrator.Primary α] : Filtrator.CoreJoinAligned α := by
  letI : Filtrator.Filtered α := two_imp_three (α := α)
  exact three_imp_four (α := α)

/-- 1⇒4 in Theorem 534 tuple. -/
theorem one_imp_four [Filtrator.Powerset.{u, v} α] : Filtrator.CoreJoinAligned α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_four (α := α)

end FilteredJoinClosedCore

export FilteredJoinClosedCore
  (three_imp_four two_imp_four one_imp_four)
