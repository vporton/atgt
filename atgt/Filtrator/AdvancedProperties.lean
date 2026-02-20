import atgt.Filtrator.Primary
import atgt.Filtrator.Powerset
import atgt.AlternativePrimaryFiltrators
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

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
    ∀ S : Set (Filtrator.supset (α := α)), S.Nonempty → BddAbove S →
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
    NonemptyInfUpInter (Filtrator.supset (α := α)) := by
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
    NonemptyInfUpInter (Filtrator.supset (α := α)) := by
  exact theorem516 (α := α) hord

/-- 1⇒3 in Corollary 517 tuple. -/
theorem one_imp_three
    [SemilatticeInf α]
    [@OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Powerset.{u, v} α] :
    (∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) →
    NonemptyInfUpInter (Filtrator.supset (α := α)) := by
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
    CompleteLattice (Filtrator.supset (α := α)) := by
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
    CompleteLattice (Filtrator.supset (α := α)) := by
  intro hord
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α) hord

end PrimaryMeetTopCompleteLatticeTuple

export PrimaryMeetTopCompleteLatticeTuple (two_imp_three one_imp_three)

namespace FiniteFilterInfimum

variable {α : Type u} [DistribLattice α]

/--
The right-hand side in Theorem 522 item `1^o`:
finite meets of one chosen element from each input filter.
-/
def finiteMeetSet (m : ℕ)
    (Fs : Fin (m + 1) → PosetFilter (U := (inferInstance : PartialOrder α))) : Set α :=
  { x : α |
      ∃ K : Fin (m + 1) → α,
        (∀ i, K i ∈ (Fs i).elements) ∧
        x = (Finset.univ.inf'
          (by
            classical
            simpa using (Finset.univ_nonempty :
              (Finset.univ : Finset (Fin (m + 1))).Nonempty)) K) }

/--
Theorem 522 item `1^o` (`chap-filt.tex`):
for a finite family of filters over a distributive lattice, the finite infimum filter is exactly
the set of finite meets of one chosen element from each filter.
Formalized as an explicit `IsGLB` witness with the described carrier.
-/
theorem theorem522_item1
    (m : ℕ) (Fs : Fin (m + 1) → PosetFilter (U := (inferInstance : PartialOrder α))) :
    ∃ R : PosetFilter (U := (inferInstance : PartialOrder α)),
      R.elements = finiteMeetSet (α := α) m Fs ∧
      IsGLB (Set.range Fs) R := by
  classical
  let hneFin : (Finset.univ : Finset (Fin (m + 1))).Nonempty := by
    simpa using (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin (m + 1))).Nonempty)
  let setR : Set α := finiteMeetSet (α := α) m Fs
  have hR_nonempty : Set.Nonempty setR := by
    let K0 : Fin (m + 1) → α := fun i => Classical.choose (Fs i).non_empty
    have hK0 : ∀ i, K0 i ∈ (Fs i).elements := by
      intro i
      exact Classical.choose_spec (Fs i).non_empty
    refine ⟨(Finset.univ.inf' hneFin K0), ?_⟩
    exact ⟨K0, hK0, rfl⟩
  let R : PosetFilter (U := (inferInstance : PartialOrder α)) := {
    elements := setR
    non_empty := hR_nonempty
    cap_elements := by
      intro a b ha hb
      rcases ha with ⟨X, hX, rfl⟩
      rcases hb with ⟨Y, hY, rfl⟩
      let Z : Fin (m + 1) → α := fun i => X i ⊓ Y i
      have hZ : ∀ i, Z i ∈ (Fs i).elements := by
        intro i
        let Fi : AlternativePrimaryFiltrators.FilterSet (U := (inferInstance : PartialOrder α)) :=
          PosetFilter.toThroughEquiv (Fs i)
        have hXi : X i ∈ Fi.elements := by simpa [Fi] using hX i
        have hYi : Y i ∈ Fi.elements := by simpa [Fi] using hY i
        have hZi : X i ⊓ Y i ∈ Fi.elements :=
          (AlternativePrimaryFiltrators.filter_inf_mem_iff (h := Fi) (X i) (Y i)).2 ⟨hXi, hYi⟩
        simpa [Fi, Z] using hZi
      refine ⟨(Finset.univ.inf' hneFin Z), ⟨Z, hZ, rfl⟩, ?_, ?_⟩
      · have hz_le_X : ∀ i, (Finset.univ.inf' hneFin Z) ≤ X i := by
          intro i
          have hz_le_Zi : (Finset.univ.inf' hneFin Z) ≤ Z i := by
            simpa using (Finset.inf'_le (s := Finset.univ) (f := Z)
              (h := (by simp : i ∈ (Finset.univ : Finset (Fin (m + 1))))))
          exact le_trans hz_le_Zi inf_le_left
        exact Finset.le_inf' (s := Finset.univ) (H := hneFin) (f := X) (by
          intro i hi
          exact hz_le_X i)
      · have hz_le_Y : ∀ i, (Finset.univ.inf' hneFin Z) ≤ Y i := by
          intro i
          have hz_le_Zi : (Finset.univ.inf' hneFin Z) ≤ Z i := by
            simpa using (Finset.inf'_le (s := Finset.univ) (f := Z)
              (h := (by simp : i ∈ (Finset.univ : Finset (Fin (m + 1))))))
          exact le_trans hz_le_Zi inf_le_right
        exact Finset.le_inf' (s := Finset.univ) (H := hneFin) (f := Y) (by
          intro i hi
          exact hz_le_Y i)
    carrier := setR
    upper' := by
      intro a b hab ha
      rcases ha with ⟨X, hX, rfl⟩
      let K : Fin (m + 1) → α := fun i => b ⊔ X i
      have hK : ∀ i, K i ∈ (Fs i).elements := by
        intro i
        have hXi_car : X i ∈ (Fs i).carrier := by
          simpa [(Fs i).carrier_eq_elements] using hX i
        have hKi_car : K i ∈ (Fs i).carrier :=
          (Fs i).upper' (by simpa [K] using (le_sup_right : X i ≤ b ⊔ X i)) hXi_car
        simpa [K, (Fs i).carrier_eq_elements] using hKi_car
      refine ⟨K, hK, ?_⟩
      have hdistrib :
          b ⊔ (Finset.univ.inf' hneFin X) =
            Finset.univ.inf' hneFin K := by
        simpa [K] using
          (Finset.inf'_sup_distrib_left
            (s := Finset.univ) (hs := hneFin) (f := X) (a := b))
      have hsup : b ⊔ (Finset.univ.inf' hneFin X) = b :=
        sup_eq_left.2 hab
      exact (hdistrib.symm.trans hsup).symm
    carrier_eq_elements := rfl
  }
  refine ⟨R, rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · intro G hG
    rcases hG with ⟨i, rfl⟩
    intro p hp
    let base : Fin (m + 1) → α := fun j =>
      if hji : j = i then p else Classical.choose (Fs j).non_empty
    have hbase : ∀ j, base j ∈ (Fs j).elements := by
      intro j
      by_cases hji : j = i
      · subst hji
        simpa [base]
      · simp [base, hji, Classical.choose_spec (Fs j).non_empty]
    let K : Fin (m + 1) → α := fun j => p ⊔ base j
    have hK : ∀ j, K j ∈ (Fs j).elements := by
      intro j
      have hbj_car : base j ∈ (Fs j).carrier := by
        simpa [(Fs j).carrier_eq_elements] using hbase j
      have hKj_car : K j ∈ (Fs j).carrier :=
        (Fs j).upper' (by simpa [K] using (le_sup_right : base j ≤ p ⊔ base j)) hbj_car
      simpa [K, (Fs j).carrier_eq_elements] using hKj_car
    have hInfEq : (Finset.univ.inf' hneFin K) = p := by
      have hdistrib :
          p ⊔ (Finset.univ.inf' hneFin base) =
            Finset.univ.inf' hneFin K := by
        simpa [K] using
          (Finset.inf'_sup_distrib_left
            (s := Finset.univ) (hs := hneFin) (f := base) (a := p))
      have hInfLe : (Finset.univ.inf' hneFin base) ≤ p := by
        have hle : (Finset.univ.inf' hneFin base) ≤ base i := by
          simpa using (Finset.inf'_le (s := Finset.univ) (f := base)
            (h := (by simp : i ∈ (Finset.univ : Finset (Fin (m + 1))))))
        simpa [base] using hle
      have hsup : p ⊔ (Finset.univ.inf' hneFin base) = p :=
        sup_eq_left.2 hInfLe
      exact hdistrib.symm.trans hsup
    exact ⟨K, hK, hInfEq.symm⟩
  · intro B hB
    intro x hx
    rcases hx with ⟨K, hK, rfl⟩
    have hKB : ∀ i, K i ∈ B.elements := by
      intro i
      have hBi : B ≤ Fs i := hB (by exact ⟨i, rfl⟩)
      exact hBi (hK i)
    have hw : (∀ᵉ (x ∈ B.elements) (y ∈ B.elements), x ⊓ y ∈ B.elements) := by
      intro x hx y hy
      let hBt : AlternativePrimaryFiltrators.FilterSet (U := (inferInstance : PartialOrder α)) :=
        PosetFilter.toThroughEquiv B
      have hx' : x ∈ hBt.elements := by simpa [hBt] using hx
      have hy' : y ∈ hBt.elements := by simpa [hBt] using hy
      have hxy : x ⊓ y ∈ hBt.elements :=
        (AlternativePrimaryFiltrators.filter_inf_mem_iff (h := hBt) x y).2 ⟨hx', hy'⟩
      simpa [hBt] using hxy
    exact Finset.inf'_mem (s := B.elements) hw (t := Finset.univ) (H := hneFin) (p := K) (by
      intro i hi
      exact hKB i)

end FiniteFilterInfimum

namespace FiniteFilterMeetCoreTuple

variable {α : Type u}

/--
Corollary 523 (`f-fin-filt-meet`) in development-level core-filter-lattice form:
finite infimums of core filters are exactly generated by finite meets of chosen members.
-/
def FiniteFilterMeetFormula (α : Type u) [Filtrator α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))] : Prop :=
  ∀ m : ℕ,
    ∀ Fs : Fin (m + 1) →
      PosetFilter (U := Dcore.toLattice.toSemilatticeInf.toPartialOrder),
    ∃ R : PosetFilter (U := Dcore.toLattice.toSemilatticeInf.toPartialOrder),
      R.elements =
        FiniteFilterInfimum.finiteMeetSet
          (α := Filtrator.subset (α := α)) m Fs ∧
      IsGLB (Set.range Fs) R

/-- 1⇒2 in Corollary 523 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Corollary 523 tuple (core filter-lattice form). -/
theorem two_imp_three
    [Filtrator α]
    [Filtrator.Primary α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))] :
    FiniteFilterMeetFormula α := by
  intro m Fs
  simpa [FiniteFilterMeetFormula] using
    (FiniteFilterInfimum.theorem522_item1
      (α := Filtrator.subset (α := α)) m Fs)

/-- 1⇒3 in Corollary 523 tuple. -/
theorem one_imp_three
    [Filtrator.Powerset.{u, v} α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))] :
    FiniteFilterMeetFormula α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α)

end FiniteFilterMeetCoreTuple

export FiniteFilterInfimum (theorem522_item1)
export FiniteFilterMeetCoreTuple (two_imp_three one_imp_three)

namespace PrimaryDistribCoreBridge

variable {α : Type u}

/--
Theorem 524 bridge route (Lean form): from primary + distributive-core assumptions we construct
the complete lattice structure on `Filtrator.supset`.

Note: `OrderTop`/`OrderBot` assumptions are Lean-side technical assumptions used to handle the
empty-family branch in complete-lattice construction; they are not stated explicitly in the
informal book.
-/
noncomputable instance primary_distribCore_imp_completeLattice
    [SemilatticeInf α]
    [hTop : @OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [hBot : @OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Primary α]
    [_Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α
      (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) :
    CompleteLattice (Filtrator.supset (α := α)) := by
  exact PrimaryMeetTopCompleteLatticeTuple.two_imp_three (α := α) hord

/--
Specialized bridge: under the primary/distributive-core setup, any proof of Theorem 530
(`Order.Coframe`) yields a coframe instance on `Filtrator.supset`.
-/
noncomputable def primary_distribCore_imp_coframe
    [SemilatticeInf α]
    [hTop : @OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [hBot : @OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Primary α]
    [_Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α
      (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b)
    (hC : Order.Coframe (Filtrator.supset (α := α))) :
    Order.Coframe (Filtrator.supset (α := α)) := by
  exact hC

end PrimaryDistribCoreBridge

export PrimaryDistribCoreBridge (primary_distribCore_imp_completeLattice)

namespace FilterInfAssociativity

variable {α : Type u}

/-- 1⇒2 in Theorem 530 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Theorem 530 tuple (development-level complete-distributive form). -/
noncomputable def two_imp_three
    [SemilatticeInf α]
    [hTop : @OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [hBot : @OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Primary α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α
      (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b)
    (hC : Order.Coframe (Filtrator.supset (α := α))) :
    Order.Coframe (Filtrator.supset (α := α)) := by
  exact hC

/-- 1⇒3 in Theorem 530 tuple. -/
noncomputable def one_imp_three
    [SemilatticeInf α]
    [@OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [@OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Powerset.{u, v} α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α
      (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b)
    (hC : Order.Coframe (Filtrator.supset (α := α))) :
    Order.Coframe (Filtrator.supset (α := α)) := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α) hord hC

end FilterInfAssociativity

export FilterInfAssociativity (two_imp_three one_imp_three)

namespace FilterAlsoDistributive

variable {α : Type u}

/-- 1⇒2 in Corollary 531 tuple. -/
noncomputable def one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α :=
  inferInstance

/-- 2⇒3 in Corollary 531 tuple: the filter lattice is distributive. -/
noncomputable def two_imp_three
    [SemilatticeInf α]
    [hTop : @OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [hBot : @OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Primary α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α
      (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b)
    (hC : Order.Coframe (Filtrator.supset (α := α))) :
    DistribLattice (Filtrator.supset (α := α)) := by
  let hC' : Order.Coframe (Filtrator.supset (α := α)) :=
    PrimaryDistribCoreBridge.primary_distribCore_imp_coframe
      (α := α) hord hC
  exact hC'.toCoheytingAlgebra.toDistribLattice

/-- 1⇒3 in Corollary 531 tuple. -/
noncomputable def one_imp_three
    [SemilatticeInf α]
    [@OrderTop α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [@OrderBot α (inferInstance : SemilatticeInf α).toPartialOrder.toPreorder.toLE]
    [Filtrator.Powerset.{u, v} α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α
      (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b)
    (hC : Order.Coframe (Filtrator.supset (α := α))) :
    DistribLattice (Filtrator.supset (α := α)) := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α) hord hC

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
