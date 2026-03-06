import atgt.Filtrator.Primary
import atgt.Filtrator.Powerset
import atgt.AlternativePrimaryFiltrators
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.BooleanAlgebra

set_option linter.unnecessarySimpa false

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

-- /--
-- Lemma 512 (p. 85), in the form used for filters:
-- if an order embedding sends some `d : α` to the infimum of `f '' S` in a complete lattice,
-- then `d` is the infimum of `S`.
-- -/
-- theorem lemma512 {α : Type u} {β : Type v}
--     [PartialOrder α] [CompleteLattice β]
--     (f : α ↪o β) (S : Set α)
--     (h : ∃ d : α, IsGLB (f '' S) (f d)) :
--     ∃ d : α, IsGLB S d ∧ sInf (f '' S) = f d := by
--   rcases h with ⟨d, hd⟩
--   refine ⟨d, ?_, hd.sInf_eq⟩
--   refine ⟨?_, ?_⟩
--   · intro a ha
--     exact f.le_iff_le.mp (hd.1 ⟨a, ha, rfl⟩)
--   · intro z hz
--     apply f.le_iff_le.mp
--     apply hd.2
--     intro y hy
--     rcases hy with ⟨a, ha, rfl⟩
--     exact f.monotone (hz ha)

/--
Theorem 515 (p. 85), filter side in the current framework:
for every nonempty bounded-above family `S`, its supremum exists and the upper set
of this supremum is the intersection of upper sets of elements of `S`.
-/
theorem theorem515 {α : Type u} {A : Set α}
    [Filtrator.Primary A]
    [SemilatticeInf (Filtrator.subset (α := α))] :
    (Filtrator.suborder (α := α) =
      (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder) →
    ∀ S : Set (Filtrator.supset (α := α)), S.Nonempty → BddAbove S →
      ∃ m : Filtrator.supset (α := α),
        (Filtrator.up (α := α) m = Set.sInter (Filtrator.up '' S) ∧ IsLUB S m) := by
  intro hcoreord S hS hBdd
  have hcoreord_fun :
      ∀ x y : Filtrator.subset (α := α),
        x.1 ≤ y.1 ↔
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE
            x y := by
    intro x y
    let h_le_eq :=
      congrArg (fun o => o.toLE) hcoreord
    have h_eq :
        @LE.le (Filtrator.subset (α := α))
          (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE x y =
          @LE.le (Filtrator.subset (α := α))
            (Filtrator.suborder (α := α)).toLE x y := by
      dsimp [LE.le]
      simp [h_le_eq]
    have h_sub :
        @LE.le (Filtrator.subset (α := α))
          (Filtrator.suborder (α := α)).toLE x y ↔ x.1 ≤ y.1 := by
      simp [Filtrator.suborder, Subtype.coe_le_coe]
    have h_le_iff :
        @LE.le (Filtrator.subset (α := α))
          (Filtrator.suborder (α := α)).toLE x y ↔
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE x y := by
      simpa [h_eq] using Iff.rfl
    refine h_sub.symm.trans h_le_iff
  let T : Set (subset : Set α) := {y | ∀ s ∈ S, s ≤ y.1}
  have hT_nonempty : Set.Nonempty T := by
    rcases hBdd with ⟨u, hu⟩
    rcases Filtrator.Primary.exists_up_in_subset (α := A) u with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    intro s hs
    exact le_trans (hu hs) hy
  let F : PosetFilter (Filtrator.suborder (α := α)) := {
    elements := T
    non_empty := hT_nonempty
    cap_elements := by
      intro a b ha hb
      let c0 : Filtrator.subset (α := α) := a ⊓ b
      have hc0a' :
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE
            c0 a := by
        simpa [c0] using (inf_le_left : c0 ≤ a)
      have hc0b' :
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE
            c0 b := by
        simpa [c0] using (inf_le_right : c0 ≤ b)
      have hc0a : c0.1 ≤ a.1 := (hcoreord_fun c0 a).mpr hc0a'
      have hc0b : c0.1 ≤ b.1 := (hcoreord_fun c0 b).mpr hc0b'
      refine ⟨c0, ?_, hc0a, hc0b⟩
      intro s hs
      have hsa : s ≤ a.1 := ha s hs
      have hsb : s ≤ b.1 := hb s hs
      let Fs : PosetFilter (Filtrator.suborder (α := α)) :=
        Filtrator.Primary.to_poset_filter (α := A) s
      have ha_mem : a ∈ Fs.elements := by
        simpa [Fs, Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hsa
      have hb_mem : b ∈ Fs.elements := by
        simpa [Fs, Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hsb
      rcases Fs.cap_elements ha_mem hb_mem with ⟨z, hzmem, hza, hzb⟩
      have hza' :
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE
            z a :=
        (hcoreord_fun z a).mp hza
      have hzb' :
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE
            z b :=
        (hcoreord_fun z b).mp hzb
      have hzc0' :
          @LE.le (Filtrator.subset (α := α))
            (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder.toLE
            z c0 := by
        exact le_inf hza' hzb'
      have hzc0 :
          z.1 ≤ c0.1 := (hcoreord_fun z c0).mpr hzc0'
      have hc0_mem : c0 ∈ Fs.elements := Fs.upper' hzc0 hzmem
      simpa [Fs, Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hc0_mem
    carrier := T
    upper' := by
      intro a b hab ha s hs
      exact le_trans (ha s hs) hab
    carrier_eq_elements := rfl
  }
  rcases Filtrator.Primary.exists_to_poset_filter_eq (α := A) F with ⟨d, hdF⟩
  have hd_char : ∀ x : α, x ∈ subset → (d ≤ x ↔ ∀ s ∈ S, s ≤ x) := by
    intro x hxsub
    constructor
    · intro hdx
      have hx_to :
          (⟨x, hxsub⟩ : subset) ∈
            (Filtrator.Primary.to_poset_filter (α := A) d).elements := by
        simpa [Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hdx
      have hx_F : (⟨x, hxsub⟩ : subset) ∈ F.elements := by
        simpa [hdF] using hx_to
      simpa [F, T] using hx_F
    · intro hxall
      have hx_F : (⟨x, hxsub⟩ : subset) ∈ F.elements := by
        simpa [F, T] using hxall
      have hx_to :
          (⟨x, hxsub⟩ : subset) ∈
            (Filtrator.Primary.to_poset_filter (α := A) d).elements := by
        simpa [hdF] using hx_F
      simpa [Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using hx_to
  refine ⟨d, ?_⟩
  constructor
  · ext x
    constructor
    · intro hx
      refine Set.mem_sInter.2 ?_
      intro t ht
      rcases ht with ⟨s, hs, rfl⟩
      exact ⟨hx.1, (hd_char x hx.1).1 hx.2 s hs⟩
    · intro hx
      rcases hS with ⟨s0, hs0⟩
      have hx0 : x ∈ Filtrator.up s0 := by
        exact (Set.mem_sInter.1 hx) (Filtrator.up s0) ⟨s0, hs0, rfl⟩
      have hxsub : x ∈ subset := hx0.1
      have hxall : ∀ s ∈ S, s ≤ x := by
        intro s hs
        exact ((Set.mem_sInter.1 hx) (Filtrator.up s) ⟨s, hs, rfl⟩).2
      exact ⟨hxsub, (hd_char x hxsub).2 hxall⟩
  · refine ⟨?_, ?_⟩
    · intro s hs
      have h_up_sub : Filtrator.up d ⊆ Filtrator.up s := by
        intro x hx
        refine ⟨hx.1, (hd_char x hx.1).1 hx.2 s hs⟩
      exact (Filtrator.Primary.order_determined (α := A) s d).2 h_up_sub
    · intro z hz
      have hz' : ∀ s ∈ S, s ≤ z := hz
      have h_up_sub : Filtrator.up z ⊆ Filtrator.up d := by
        intro x hx
        have hxall : ∀ s ∈ S, s ≤ x := by
          intro s hs
          exact le_trans (hz' s hs) hx.2
        exact ⟨hx.1, (hd_char x hx.1).2 hxall⟩
      exact (Filtrator.Primary.order_determined (α := A) d z).2 h_up_sub

/--
From Theorem 515, plus top/bottom in the filtrator order, we obtain arbitrary suprema.
-/
noncomputable def theorem515_completeSemilatticeSup
    {α : Type u} {A : Set α}
    [Filtrator.Primary A]
    [SemilatticeInf (Filtrator.subset (α := α))]
    [OrderTop α]
    [OrderBot α]
    (hcoreord :
      Filtrator.suborder (α := α) =
        (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder) :
    CompleteSemilatticeSup (Filtrator.supset (α := α)) := by
  classical
  let sSupFun : Set α → α := fun S =>
    if hS : S.Nonempty then
      Classical.choose
        (theorem515 (α := α) hcoreord S hS ⟨⊤, by intro s hs; exact le_top⟩)
    else
      ⊥
  letI : SupSet α := ⟨sSupFun⟩
  refine { le_sSup := ?_, sSup_le := ?_ }
  · intro S a ha
    by_cases hS : S.Nonempty
    · let h515 := theorem515 (α := α) hcoreord S hS ⟨⊤, by intro s hs; exact le_top⟩
      have hsSup : sSup S = Classical.choose h515 := by
        change sSupFun S = Classical.choose h515
        simp [sSupFun, hS]
      exact hsSup ▸ (Classical.choose_spec h515).2.1 ha
    · exact False.elim (hS ⟨a, ha⟩)
  · intro S z hz
    by_cases hS : S.Nonempty
    · let h515 := theorem515 (α := α) hcoreord S hS ⟨⊤, by intro s hs; exact le_top⟩
      have hsSup : sSup S = Classical.choose h515 := by
        change sSupFun S = Classical.choose h515
        simp [sSupFun, hS]
      exact hsSup ▸ (Classical.choose_spec h515).2.2 hz
    · have hSEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
      subst hSEmpty
      have hsSupEmpty : sSup (∅ : Set α) = (⊥ : α) := by
        change sSupFun (∅ : Set α) = (⊥ : α)
        simp [sSupFun]
      exact hsSupEmpty ▸ bot_le

/--
Any `CompleteSemilatticeSup` is a complete lattice (Mathlib constructor),
so Theorem 515 also yields a complete lattice under the same assumptions.
-/
noncomputable def theorem515_completeLattice
    {α : Type u} {A : Set α}
    [Filtrator.Primary A]
    [SemilatticeInf (Filtrator.subset (α := α))]
    [OrderTop α]
    [OrderBot α]
    (hcoreord :
      Filtrator.suborder (α := α) =
        (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder) :
    CompleteLattice (Filtrator.supset (α := α)) := by
  letI : CompleteSemilatticeSup (Filtrator.supset (α := α)) :=
    theorem515_completeSemilatticeSup (α := α) hcoreord
  exact completeLatticeOfCompleteSemilatticeSup (Filtrator.supset (α := α))

/--
Theorem 516 (pp. 85-86), formalized in the present framework as the meet-side statement
used by Corollaries 517/518.
-/
theorem theorem516 {α : Type u} {A : Set α}
    [Filtrator.Primary A]
    [SemilatticeInf (Filtrator.subset (α := α))]
    [OrderTop α] :
    (Filtrator.suborder (α := α) =
      (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder) →
    NonemptyInfUpInter (Filtrator.supset (α := α)) := by
  intro hcoreord S hS
  have hBdd : BddAbove S := ⟨⊤, by intro s hs; exact le_top⟩
  rcases theorem515 (α := α) hcoreord S hS hBdd with ⟨d, hUpEq, hLub⟩
  refine ⟨d, hLub, ?_⟩
  ext x
  constructor
  · intro hx s hs
    have hxInter : x ∈ Set.sInter (Filtrator.up '' S) := hUpEq ▸ hx
    exact hxInter (Filtrator.up s) ⟨s, hs, rfl⟩
  · intro hx
    have hxInter : x ∈ Set.sInter (Filtrator.up '' S) := by
      intro A hA
      rcases hA with ⟨s, hs, rfl⟩
      exact hx s hs
    exact hUpEq.symm ▸ hxInter

namespace PrimaryMeetTopCompleteLatticeTuple

variable {α : Type u} {A : Set α}

/- TODO: Rename below. -/

/-- 1⇒2 in Corollary 518 tuple. -/
noncomputable def one_imp_two [FiltratorOnPowerset.Primary (U := A)] : Filtrator.Primary (Set.powerset A) :=
  inferInstance

/-- 2⇒3 in Corollary 518 tuple. -/
noncomputable instance two_imp_three
    [Filtrator.Primary A]
    [SemilatticeInf (Filtrator.subset (α := α))]
    [OrderTop α]
    [OrderBot α]
    (hcoreord :
      Filtrator.suborder (α := α) =
        (inferInstance : SemilatticeInf (Filtrator.subset (α := α))).toPartialOrder) :
    CompleteLattice (Filtrator.supset (α := α)) := by
  exact theorem515_completeLattice (α := α) hcoreord

/-- 1⇒3 in Corollary 518 tuple. -/
noncomputable instance one_imp_three
    [FiltratorOnPowerset.Primary (U := A)] :
    CompleteLattice (FiltratorOnPowerset.Primary (U := A)) := by
  letI : Filtrator.Primary (Set.powerset A) := one_imp_two (A := A)
  sorry

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
  · intro B hB x hx
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

namespace ArbitraryFilterInfimum

variable {α : Type u} [DistribLattice α]

/--
The right-hand side in theorem `distr-meet` (`chap-filt.tex`): finite meets of elements drawn from
the union of a nonempty family of filters.
-/
noncomputable def finiteMeetGeneratedSet
    (S : Set (PosetFilter (U := (inferInstance : PartialOrder α)))) : Set α := by
  classical
  exact
    { x : α |
      ∃ t : Finset α, ∃ ht : t.Nonempty,
        ((t : Set α) ⊆ ⋃ F ∈ S, F.elements) ∧
        x = t.inf' ht id }

/-- Finite meets generated from an arbitrary carrier set. -/
noncomputable def finiteMeetFromSet (U : Set α) : Set α := by
  classical
  exact
    { x : α |
      ∃ t : Finset α, ∃ ht : t.Nonempty,
        ((t : Set α) ⊆ U) ∧
        x = t.inf' ht id }

lemma finiteMeetGeneratedSet_eq_finiteMeetFromSet
    (S : Set (PosetFilter (U := (inferInstance : PartialOrder α)))) :
    finiteMeetGeneratedSet (α := α) S =
      finiteMeetFromSet (α := α) (⋃ F ∈ S, F.elements) := by
  rfl

lemma inf'_mem_filter
    (F : PosetFilter (U := (inferInstance : PartialOrder α)))
    {t : Finset α} (ht : t.Nonempty)
    (hmem : ∀ x ∈ t, x ∈ F.elements) :
    t.inf' ht id ∈ F.elements := by
  have hinf_mem : ∀ {z w : α}, z ∈ F.elements → w ∈ F.elements → z ⊓ w ∈ F.elements := by
    intro z w hz hw
    rcases F.cap_elements hz hw with ⟨u, hu, huz, huw⟩
    have hu_car : u ∈ F.carrier := by
      simpa [F.carrier_eq_elements] using hu
    have hzw_car : z ⊓ w ∈ F.carrier :=
      F.upper' (le_inf huz huw) hu_car
    simpa [F.carrier_eq_elements] using hzw_car
  have hclosed : (∀ᵉ (z ∈ F.elements) (w ∈ F.elements), z ⊓ w ∈ F.elements) := by
    intro z hz w hw
    exact hinf_mem hz hw
  exact Finset.inf'_mem (s := F.elements) hclosed (t := t) (H := ht) (p := id) (by
    intro i hi
    exact hmem i hi)

lemma finiteMeetFromSet_inter_filter
    (A : PosetFilter (U := (inferInstance : PartialOrder α)))
    (U : Set α) :
    finiteMeetFromSet (α := α) (A.elements ∩ U) =
      A.elements ∩ finiteMeetFromSet (α := α) U := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨t, ht, ht_sub, rfl⟩
    refine ⟨?_, ?_⟩
    · exact inf'_mem_filter (α := α) A ht (by
        intro y hy
        exact (ht_sub hy).1)
    · exact ⟨t, ht, (by
        intro y hy
        exact (ht_sub hy).2), rfl⟩
  · intro hx
    rcases hx with ⟨hxA, hxU⟩
    rcases hxU with ⟨t, ht, ht_sub, rfl⟩
    refine ⟨t, ht, ?_, rfl⟩
    intro y hy
    refine ⟨?_, ht_sub hy⟩
    have hxy : t.inf' ht id ≤ y := Finset.inf'_le (s := t) (f := id) (h := hy)
    have hxA_car : t.inf' ht id ∈ A.carrier := by
      simpa [A.carrier_eq_elements] using hxA
    have hy_car : y ∈ A.carrier := A.upper' hxy hxA_car
    simpa [A.carrier_eq_elements] using hy_car

lemma finiteMeetGeneratedSet_eq_of_union_eq
    {S T : Set (PosetFilter (U := (inferInstance : PartialOrder α)))}
    (hU : (⋃ F ∈ S, F.elements) = (⋃ F ∈ T, F.elements)) :
    finiteMeetGeneratedSet (α := α) S =
      finiteMeetGeneratedSet (α := α) T := by
  rw [finiteMeetGeneratedSet_eq_finiteMeetFromSet,
    finiteMeetGeneratedSet_eq_finiteMeetFromSet, hU]

/--
Theorem `distr-meet`, item `1` (`chap-filt.tex`): for a nonempty family of filters over a
distributive lattice, their infimum filter is exactly the set of finite meets of elements picked
from the union of the family.
-/
theorem theorem_distr_meet
    (S : Set (PosetFilter (U := (inferInstance : PartialOrder α))))
    (hS : S.Nonempty) :
    ∃ R : PosetFilter (U := (inferInstance : PartialOrder α)),
      R.elements = finiteMeetGeneratedSet (α := α) S ∧
      IsGLB S R := by
  classical
  let setR : Set α := finiteMeetGeneratedSet (α := α) S
  have hR_nonempty : Set.Nonempty setR := by
    rcases hS with ⟨F, hF⟩
    rcases F.non_empty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    refine ⟨{x}, by simp, ?_, by simp⟩
    intro y hy
    have hyx : y = x := by simpa using hy
    subst hyx
    exact Set.mem_iUnion.2 ⟨F, Set.mem_iUnion.2 ⟨hF, hx⟩⟩
  let R : PosetFilter (U := (inferInstance : PartialOrder α)) := {
    elements := setR
    non_empty := hR_nonempty
    cap_elements := by
      intro a b ha hb
      rcases ha with ⟨ta, hta, hta_sub, rfl⟩
      rcases hb with ⟨tb, htb, htb_sub, rfl⟩
      let tc : Finset α := ta ∪ tb
      have htc : tc.Nonempty := by
        rcases hta with ⟨x, hx⟩
        exact ⟨x, by simpa [tc] using (Finset.mem_union.2 (Or.inl hx))⟩
      have htc_sub : (tc : Set α) ⊆ ⋃ F ∈ S, F.elements := by
        intro x hx
        have hx' : x ∈ ta ∨ x ∈ tb := by
          simpa [tc] using (show x ∈ ta ∪ tb from hx)
        cases hx' with
        | inl hxa => exact hta_sub hxa
        | inr hxb => exact htb_sub hxb
      refine ⟨tc.inf' htc id, ⟨tc, htc, htc_sub, rfl⟩, ?_, ?_⟩
      · refine Finset.le_inf' (s := ta) (H := hta) (f := id) ?_
        intro x hx
        have hxtc : x ∈ tc := by
          simpa [tc] using (Finset.mem_union.2 (Or.inl hx))
        exact Finset.inf'_le (s := tc) (f := id) (h := hxtc)
      · refine Finset.le_inf' (s := tb) (H := htb) (f := id) ?_
        intro x hx
        have hxtc : x ∈ tc := by
          simpa [tc] using (Finset.mem_union.2 (Or.inr hx))
        exact Finset.inf'_le (s := tc) (f := id) (h := hxtc)
    carrier := setR
    upper' := by
      intro a b hab ha
      rcases ha with ⟨ta, hta, hta_sub, rfl⟩
      let tb : Finset α := ta.image (fun x => b ⊔ x)
      have htb : tb.Nonempty := by
        simpa [tb] using hta.image (fun x => b ⊔ x)
      have htb_sub : (tb : Set α) ⊆ ⋃ F ∈ S, F.elements := by
        intro y hy
        rcases Finset.mem_image.1 (by simpa [tb] using hy) with ⟨x, hx, rfl⟩
        rcases Set.mem_iUnion.1 (hta_sub hx) with ⟨F, hmemF⟩
        rcases Set.mem_iUnion.1 hmemF with ⟨hF, hxF⟩
        have hx_car : x ∈ F.carrier := by
          simpa [F.carrier_eq_elements] using hxF
        have hbx_car : b ⊔ x ∈ F.carrier :=
          F.upper' (by simpa using (le_sup_right : x ≤ b ⊔ x)) hx_car
        have hbx : b ⊔ x ∈ F.elements := by
          simpa [F.carrier_eq_elements] using hbx_car
        exact Set.mem_iUnion.2 ⟨F, Set.mem_iUnion.2 ⟨hF, hbx⟩⟩
      refine ⟨tb, htb, htb_sub, ?_⟩
      have hdistrib :
          b ⊔ ta.inf' hta id =
            ta.inf' hta (fun x => b ⊔ x) := by
        simpa using
          (Finset.inf'_sup_distrib_left (s := ta) (hs := hta) (f := id) (a := b))
      have hmap :
          ta.inf' hta (fun x => b ⊔ x) =
            tb.inf' htb id := by
        simpa [tb] using
          (Finset.inf'_comp_eq_image
            (s := ta) (f := fun x => b ⊔ x) (hs := hta) (g := id))
      have hsup : b ⊔ ta.inf' hta id = b :=
        sup_eq_left.2 hab
      exact ((hdistrib.trans hmap).symm.trans hsup).symm
    carrier_eq_elements := rfl
  }
  refine ⟨R, rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · intro F hF p hp
    refine ⟨{p}, by simp, ?_, by simp⟩
    intro y hy
    have hy_p : y = p := by simpa using hy
    subst hy_p
    exact Set.mem_iUnion.2 ⟨F, Set.mem_iUnion.2 ⟨hF, hp⟩⟩
  · intro B hB x hx
    rcases hx with ⟨t, ht, ht_sub, rfl⟩
    have htB : ∀ z ∈ t, z ∈ B.elements := by
      intro z hz
      rcases Set.mem_iUnion.1 (ht_sub hz) with ⟨F, hFz⟩
      rcases Set.mem_iUnion.1 hFz with ⟨hF, hzF⟩
      exact (hB hF) hzF
    have hinf_mem : ∀ {z w : α}, z ∈ B.elements → w ∈ B.elements → z ⊓ w ∈ B.elements := by
      intro z w hz hw
      rcases B.cap_elements hz hw with ⟨u, hu, huz, huw⟩
      have hu_car : u ∈ B.carrier := by
        simpa [B.carrier_eq_elements] using hu
      have hzw_car : z ⊓ w ∈ B.carrier :=
        B.upper' (le_inf huz huw) hu_car
      simpa [B.carrier_eq_elements] using hzw_car
    have hclosed : (∀ᵉ (z ∈ B.elements) (w ∈ B.elements), z ⊓ w ∈ B.elements) := by
      intro z hz w hw
      exact hinf_mem hz hw
    exact Finset.inf'_mem (s := B.elements) hclosed (t := t) (H := ht) (p := id) (by
      intro i hi
      exact htB i hi)

end ArbitraryFilterInfimum

namespace FiniteFilterMeetCoreTuple

variable {α : Type u} {A : Set α}

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
noncomputable def one_imp_two [FiltratorOnPowerset.Primary (U := A)] : Filtrator.Primary (Set.powerset A) :=
  inferInstance

/-- 2⇒3 in Corollary 523 tuple (core filter-lattice form). -/
theorem two_imp_three
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))] :
    FiniteFilterMeetFormula α := by
  intro m Fs
  simpa [FiniteFilterMeetFormula] using
    (FiniteFilterInfimum.theorem522_item1
      (α := Filtrator.subset (α := α)) m Fs)

/-- 1⇒3 in Corollary 523 tuple. -/
theorem one_imp_three
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))] :
    FiniteFilterMeetFormula α := by
  sorry

end FiniteFilterMeetCoreTuple

export FiniteFilterInfimum (theorem522_item1)
export FiniteFilterMeetCoreTuple (two_imp_three one_imp_three)

namespace PrimaryDistribCoreBridge

variable {α : Type u} {A : Set α}

/-- The canonical order isomorphism from a primary filtrator to filters on its core suborder. -/
noncomputable def toPosetFilterOrderIso [Filtrator.Primary A] :
    α ≃o PosetFilter (Filtrator.suborder (α := α)) where
  toEquiv := (Filtrator.Primary.to_filters_iso (α := A)).toRelIso.toEquiv
  map_rel_iff' := by
    intro x y
    exact (Filtrator.Primary.to_filters_iso (α := A)).toRelIso.map_rel_iff

@[simp]
lemma toPosetFilterOrderIso_apply [Filtrator.Primary A] (x : α) :
    toPosetFilterOrderIso (α := α) (A := A) x =
      Filtrator.Primary.to_poset_filter (α := A) x := by
  simpa [toPosetFilterOrderIso] using
    (Filtrator.Primary.to_filters_iso_eq_to_poset_filter (α := A) x)

lemma to_poset_filter_injective [Filtrator.Primary A] :
    Function.Injective (Filtrator.Primary.to_poset_filter (α := A)) := by
  intro x y hxy
  have hxy' :
      toPosetFilterOrderIso (α := α) (A := A) x =
        toPosetFilterOrderIso (α := α) (A := A) y := by
    simpa using hxy
  exact (toPosetFilterOrderIso (α := α) (A := A)).injective hxy'

/-- `to_poset_filter` cast to an explicitly provided core order. -/
noncomputable def toFilterInOrder
    [Filtrator.Primary A]
    (U : PartialOrder (Filtrator.subset (α := α)))
    (hU : Filtrator.suborder (α := α) = U)
    (x : α) : PosetFilter (U := U) :=
  PosetFilter.castOrderIso hU (Filtrator.Primary.to_poset_filter (α := A) x)

lemma mem_toFilterInOrder_elements_iff
    [Filtrator.Primary A]
    (U : PartialOrder (Filtrator.subset (α := α)))
    (hU : Filtrator.suborder (α := α) = U)
    (x : α) (z : Filtrator.subset (α := α)) :
    z ∈ (toFilterInOrder (α := α) U hU x).elements ↔ x ≤ z.1 := by
  cases hU
  change z ∈ (Filtrator.Primary.to_poset_filter (α := A) x).elements ↔ x ≤ z.1
  simp [Filtrator.Primary.to_poset_filter, Filtrator.up_suborder]

/-- `to_poset_filter` with codomain typed by the distributive-core order (via a provided order
identification). -/
noncomputable def toCoreFilter
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder)
    (x : α) :
    PosetFilter (U := Dcore.toLattice.toSemilatticeInf.toPartialOrder) :=
  toFilterInOrder (α := α)
    (U := Dcore.toLattice.toSemilatticeInf.toPartialOrder) hcoreord x

/-- Canonical order isomorphism `α ≃o` core filters typed with the distributive-core order. -/
noncomputable def toCoreFilterOrderIso
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder) :
    α ≃o PosetFilter (U := Dcore.toLattice.toSemilatticeInf.toPartialOrder) :=
  (toPosetFilterOrderIso (α := α) (A := A)).trans (PosetFilter.castOrderIso hcoreord)

@[simp]
lemma toCoreFilterOrderIso_apply
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder)
    (x : α) :
    toCoreFilterOrderIso (α := α) hcoreord x = toCoreFilter (α := α) hcoreord x := by
  simp [toCoreFilterOrderIso, toCoreFilter, toFilterInOrder, toPosetFilterOrderIso_apply]

lemma toCoreFilter_injective
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder) :
    Function.Injective (toCoreFilter (α := α) hcoreord) := by
  intro x y hxy
  have hxy' :
      toCoreFilterOrderIso (α := α) hcoreord x =
        toCoreFilterOrderIso (α := α) hcoreord y := by
    simpa [toCoreFilterOrderIso_apply] using hxy
  exact (toCoreFilterOrderIso (α := α) hcoreord).injective hxy'

lemma mem_toCoreFilter_elements_iff
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder)
    (x : α) (z : Filtrator.subset (α := α)) :
    z ∈ (toCoreFilter (α := α) hcoreord x).elements ↔ x ≤ z.1 := by
  simpa [toCoreFilter] using
    mem_toFilterInOrder_elements_iff
      (α := α) (U := Dcore.toLattice.toSemilatticeInf.toPartialOrder) hcoreord x z

lemma toCoreFilter_sInf_elements_nonempty
    [Filtrator.Primary A]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    [InfSet α]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder)
    (S : Set α) (hS : S.Nonempty)
    (hsInf : IsGLB S (sInf S)) :
    (toCoreFilter (α := α) hcoreord (sInf S)).elements =
      ArbitraryFilterInfimum.finiteMeetGeneratedSet
        (α := Filtrator.subset (α := α))
        ((toCoreFilterOrderIso (α := α) hcoreord) '' S) := by
  let e := toCoreFilterOrderIso (α := α) hcoreord
  have hImgNonempty : (e '' S).Nonempty := hS.image e
  rcases ArbitraryFilterInfimum.theorem_distr_meet
      (α := Filtrator.subset (α := α))
      (S := e '' S) hImgNonempty with
    ⟨R, hRset, hRglb⟩
  have hglb_alpha : IsGLB S (e.symm R) := (e.isGLB_image).1 hRglb
  have hsInf_eq : sInf S = e.symm R := hsInf.unique hglb_alpha
  have hER : e (sInf S) = R := by
    simpa [hsInf_eq]
  have htoCore : toCoreFilter (α := α) hcoreord (sInf S) = R := by
    simpa [e, toCoreFilterOrderIso_apply] using hER
  calc
    (toCoreFilter (α := α) hcoreord (sInf S)).elements = R.elements := by
      simpa [htoCore]
    _ = ArbitraryFilterInfimum.finiteMeetGeneratedSet
          (α := Filtrator.subset (α := α)) (e '' S) := hRset
    _ = ArbitraryFilterInfimum.finiteMeetGeneratedSet
          (α := Filtrator.subset (α := α))
          ((toCoreFilterOrderIso (α := α) hcoreord) '' S) := by
      rfl

/-- Nonempty-family distributivity in the filter lattice (Theorem 530, item 3) via core-filters. -/
lemma sup_sInf_eq_image_nonempty
    [Filtrator.Primary A]
    [OrderTop α]
    [OrderBot α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder)
    (a : α) (S : Set α) (hS : S.Nonempty) :
    letI : CompleteLattice (Filtrator.supset (α := α)) :=
      PrimaryMeetTopCompleteLatticeTuple.two_imp_three (α := α) hcoreord
    a ⊔ sInf S = sInf ((fun x => a ⊔ x) '' S) := by
  letI : CompleteLattice (Filtrator.supset (α := α)) :=
    PrimaryMeetTopCompleteLatticeTuple.two_imp_three (α := α) hcoreord
  let e := toCoreFilterOrderIso (α := α) hcoreord
  let A : PosetFilter (U := Dcore.toLattice.toSemilatticeInf.toPartialOrder) :=
    toCoreFilter (α := α) hcoreord a
  let U : Set (Filtrator.subset (α := α)) := ⋃ F ∈ (e '' S), F.elements
  have h_toCore_sup :
      ∀ p q : α,
        (toCoreFilter (α := α) hcoreord (p ⊔ q)).elements =
          (toCoreFilter (α := α) hcoreord p).elements ∩
            (toCoreFilter (α := α) hcoreord q).elements := by
    intro p q
    ext z
    constructor
    · intro hz
      have hz_pq : p ⊔ q ≤ z.1 := (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).1 hz
      refine ⟨?_, ?_⟩
      · exact (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).2
          (le_trans (le_sup_left : p ≤ p ⊔ q) hz_pq)
      · exact (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).2
          (le_trans (le_sup_right : q ≤ p ⊔ q) hz_pq)
    · intro hz
      rcases hz with ⟨hzp, hzq⟩
      have hzp' : p ≤ z.1 := (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).1 hzp
      have hzq' : q ≤ z.1 := (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).1 hzq
      exact (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).2 (sup_le hzp' hzq')
  have h_union_toCore_image_sup :
      ∀ a0 : α, ∀ S0 : Set α,
        (⋃ F ∈ (toCoreFilterOrderIso (α := α) hcoreord '' ((fun x => a0 ⊔ x) '' S0)), F.elements) =
          (toCoreFilter (α := α) hcoreord a0).elements ∩
            (⋃ F ∈ ((toCoreFilterOrderIso (α := α) hcoreord) '' S0), F.elements) := by
    intro a0 S0
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨F, hF⟩
      rcases Set.mem_iUnion.1 hF with ⟨hFS, hzF⟩
      rcases hFS with ⟨u, huS, rfl⟩
      rcases huS with ⟨x, hxS, rfl⟩
      have hz_ax : z ∈ (toCoreFilter (α := α) hcoreord (a0 ⊔ x)).elements := by
        simpa [toCoreFilterOrderIso_apply] using hzF
      have haz : a0 ≤ z.1 := by
        have hzax_le : a0 ⊔ x ≤ z.1 :=
          (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).1 hz_ax
        exact le_trans (le_sup_left : a0 ≤ a0 ⊔ x) hzax_le
      have hzx : x ≤ z.1 := by
        have hzax_le : a0 ⊔ x ≤ z.1 :=
          (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).1 hz_ax
        exact le_trans (le_sup_right : x ≤ a0 ⊔ x) hzax_le
      refine ⟨(mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).2 haz, ?_⟩
      refine Set.mem_iUnion.2 ⟨toCoreFilterOrderIso (α := α) hcoreord x, ?_⟩
      refine Set.mem_iUnion.2 ⟨⟨x, hxS, rfl⟩, ?_⟩
      simpa [toCoreFilterOrderIso_apply] using
        ((mem_toCoreFilter_elements_iff (α := α) hcoreord x z).2 hzx)
    · intro hz
      rcases hz with ⟨hza, hzU⟩
      rcases Set.mem_iUnion.1 hzU with ⟨F, hF⟩
      rcases Set.mem_iUnion.1 hF with ⟨hFS, hzF⟩
      rcases hFS with ⟨x, hxS, rfl⟩
      have hzF_core : z ∈ (toCoreFilter (α := α) hcoreord x).elements := by
        simpa [toCoreFilterOrderIso_apply] using hzF
      have haz' : a0 ≤ z.1 := (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).1 hza
      have hzx' : x ≤ z.1 := (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).1 hzF_core
      have hzax_le : a0 ⊔ x ≤ z.1 := sup_le haz' hzx'
      have hzax : z ∈ (toCoreFilter (α := α) hcoreord (a0 ⊔ x)).elements :=
        (mem_toCoreFilter_elements_iff (α := α) hcoreord _ _).2 hzax_le
      refine Set.mem_iUnion.2 ⟨toCoreFilterOrderIso (α := α) hcoreord (a0 ⊔ x), ?_⟩
      refine Set.mem_iUnion.2 ⟨⟨a0 ⊔ x, ⟨x, hxS, rfl⟩, rfl⟩, ?_⟩
      simpa [toCoreFilterOrderIso_apply] using hzax
  have hSsup : ((fun x => a ⊔ x) '' S).Nonempty := hS.image (fun x => a ⊔ x)
  have hUnion :
      (⋃ F ∈ (e '' ((fun x => a ⊔ x) '' S)), F.elements) = A.elements ∩ U := by
    simpa [A, U, e] using
      h_union_toCore_image_sup a S
  have hLeftElems :
      (toCoreFilter (α := α) hcoreord (a ⊔ sInf S)).elements =
        A.elements ∩
          ArbitraryFilterInfimum.finiteMeetGeneratedSet
            (α := Filtrator.subset (α := α)) (e '' S) := by
    calc
      (toCoreFilter (α := α) hcoreord (a ⊔ sInf S)).elements =
          (toCoreFilter (α := α) hcoreord a).elements ∩
            (toCoreFilter (α := α) hcoreord (sInf S)).elements := by
        simpa [e] using
          h_toCore_sup a (sInf S)
      _ = A.elements ∩
          ArbitraryFilterInfimum.finiteMeetGeneratedSet
            (α := Filtrator.subset (α := α)) (e '' S) := by
        simpa [A, e] using congrArg
          (fun T => (toCoreFilter (α := α) hcoreord a).elements ∩ T)
          (toCoreFilter_sInf_elements_nonempty (α := α)
            hcoreord S hS (by simpa using (isGLB_sInf (s := S) : IsGLB S (sInf S))))
  have hRightElems :
      (toCoreFilter (α := α) hcoreord (sInf ((fun x => a ⊔ x) '' S))).elements =
        A.elements ∩
          ArbitraryFilterInfimum.finiteMeetGeneratedSet
            (α := Filtrator.subset (α := α)) (e '' S) := by
    calc
      (toCoreFilter (α := α) hcoreord (sInf ((fun x => a ⊔ x) '' S))).elements =
          ArbitraryFilterInfimum.finiteMeetGeneratedSet
            (α := Filtrator.subset (α := α)) (e '' ((fun x => a ⊔ x) '' S)) := by
        simpa [e] using
          toCoreFilter_sInf_elements_nonempty (α := α)
            hcoreord
            ((fun x => a ⊔ x) '' S) hSsup
            (by
              simpa using
                (isGLB_sInf (s := ((fun x => a ⊔ x) '' S)) :
                  IsGLB ((fun x => a ⊔ x) '' S) (sInf ((fun x => a ⊔ x) '' S)))
            )
      _ = ArbitraryFilterInfimum.finiteMeetFromSet (α := Filtrator.subset (α := α))
            (⋃ F ∈ (e '' ((fun x => a ⊔ x) '' S)), F.elements) := by
        simpa using
          (ArbitraryFilterInfimum.finiteMeetGeneratedSet_eq_finiteMeetFromSet
            (α := Filtrator.subset (α := α))
            (S := e '' ((fun x => a ⊔ x) '' S)))
      _ = ArbitraryFilterInfimum.finiteMeetFromSet (α := Filtrator.subset (α := α))
            (A.elements ∩ U) := by
        simpa [Set.image_image, Function.comp] using
          congrArg
            (ArbitraryFilterInfimum.finiteMeetFromSet (α := Filtrator.subset (α := α)))
            hUnion
      _ = A.elements ∩
            ArbitraryFilterInfimum.finiteMeetFromSet (α := Filtrator.subset (α := α)) U := by
        simpa using
          (ArbitraryFilterInfimum.finiteMeetFromSet_inter_filter
            (α := Filtrator.subset (α := α)) A U)
      _ = A.elements ∩
            ArbitraryFilterInfimum.finiteMeetGeneratedSet
              (α := Filtrator.subset (α := α)) (e '' S) := by
        have hFU :
            ArbitraryFilterInfimum.finiteMeetFromSet (α := Filtrator.subset (α := α)) U =
              ArbitraryFilterInfimum.finiteMeetGeneratedSet
                (α := Filtrator.subset (α := α)) (e '' S) := by
          simpa [U] using
            (ArbitraryFilterInfimum.finiteMeetGeneratedSet_eq_finiteMeetFromSet
              (α := Filtrator.subset (α := α)) (S := e '' S)).symm
        simpa [hFU]
  have hEqCore :
      toCoreFilter (α := α) hcoreord (a ⊔ sInf S) =
        toCoreFilter (α := α) hcoreord (sInf ((fun x => a ⊔ x) '' S)) := by
    exact PosetFilter.ThroughEquiv.ext _ _ (hLeftElems.trans hRightElems.symm)
  exact toCoreFilter_injective (α := α) hcoreord hEqCore

/--
Theorem 524 bridge route (Lean form): from primary + distributive-core assumptions we construct
the complete lattice structure on `Filtrator.supset`.

Note: `OrderTop`/`OrderBot` assumptions are Lean-side technical assumptions used to handle the
empty-family branch in complete-lattice construction; they are not stated explicitly in the
informal book.
-/
noncomputable instance primary_distribCore_imp_completeLattice
    [Filtrator.Primary A]
    [OrderTop α]
    [OrderBot α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder) :
    CompleteLattice (Filtrator.supset (α := α)) := by
  exact PrimaryMeetTopCompleteLatticeTuple.two_imp_three (α := α) hcoreord

/--
Specialized bridge (Theorem 530 route): under the primary/distributive-core setup with
core-order alignment, we construct a coframe instance on `Filtrator.supset`.
-/
noncomputable instance primary_distribCore_imp_coframe
    [F: Filtrator.Primary A]
    [top: OrderTop α]
    [OrderBot α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder) :
    Order.Coframe (Filtrator.supset (α := α)) := by
  letI : CompleteLattice (Filtrator.supset (α := α)) :=
    primary_distribCore_imp_completeLattice (α := α) hcoreord
  exact Order.Coframe.ofMinimalAxioms {
    toCompleteLattice := inferInstance
    iInf_sup_le_sup_sInf := by
      intro a s
      by_cases hS : s.Nonempty
      · have hEq :
          a ⊔ sInf s = sInf ((fun x => a ⊔ x) '' s) := by
          simpa using sup_sInf_eq_image_nonempty (α := α) hcoreord a s hS
        exact le_of_eq (by
          calc
            ⨅ b ∈ s, a ⊔ b = sInf ((fun x => a ⊔ x) '' s) := by
              simpa using (sInf_image (s := s) (f := fun x => a ⊔ x)).symm
            _ = a ⊔ sInf s := hEq.symm)
      · have hsEmpty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
        subst hsEmpty
        simp
  }

end PrimaryDistribCoreBridge

export PrimaryDistribCoreBridge (primary_distribCore_imp_completeLattice)

namespace FilterInfAssociativity

variable {α : Type u} {A : Set α}

/-- 1⇒2 in Theorem 530 tuple. -/
noncomputable def one_imp_two [FiltratorOnPowerset.Primary (U := A)] : Filtrator.Primary (Set.powerset A) :=
  inferInstance

/-- 2⇒3 in Theorem 530 tuple (development-level complete-distributive form). -/
noncomputable instance two_imp_three
    [Filtrator.Primary A]
    [OrderTop α]
    [OrderBot α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder) :
    Order.Coframe (Filtrator.supset (α := α)) := by
  exact PrimaryDistribCoreBridge.primary_distribCore_imp_coframe
    (α := α) hcoreord

/-- 1⇒3 in Theorem 530 tuple. -/
noncomputable instance one_imp_three
    [FiltratorOnPowerset.Primary (U := A)]
    :
    Order.Coframe (FiltratorOnPowerset.Primary (U := A)) := by
  letI : FiltratorOnPowerset.Primary (U := A) := one_imp_two (A := A)
  sorry

end FilterInfAssociativity

export FilterInfAssociativity (two_imp_three one_imp_three)

namespace FilterAlsoDistributive

variable {α : Type u} {A : Set α}

/-- 1⇒2 in Corollary 531 tuple. -/
noncomputable def one_imp_two [FiltratorOnPowerset.Primary (U := A)] : Filtrator.Primary (Set.powerset A) :=
  inferInstance

/-- 2⇒3 in Corollary 531 tuple: the filter lattice is distributive. -/
noncomputable instance two_imp_three
    [Filtrator.Primary A]
    [OrderTop α]
    [OrderBot α]
    [Dcore : DistribLattice (Filtrator.subset (α := α))]
    (hcoreord : Filtrator.suborder (α := α) =
      Dcore.toLattice.toSemilatticeInf.toPartialOrder) :
    DistribLattice (Filtrator.supset (α := α)) := by
  let hC' : Order.Coframe (Filtrator.supset (α := α)) :=
    PrimaryDistribCoreBridge.primary_distribCore_imp_coframe
      (α := α) hcoreord
  exact hC'.toCoheytingAlgebra.toDistribLattice

/-- 1⇒3 in Corollary 531 tuple. -/
noncomputable instance one_imp_three
    [FiltratorOnPowerset.Primary (U := A)] :
    DistribLattice (FiltratorOnPowerset.Primary (U := A)) := by
  letI : FiltratorOnPowerset.Primary (U := A) := one_imp_two (A := A)
  sorry

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

variable {α : Type u} {A : Set α}

/-- 1⇒2 in Theorem 534 tuple. -/
noncomputable def one_imp_two [FiltratorOnPowerset.Primary (U := A)] : Filtrator.Primary (Set.powerset A) :=
  inferInstance

/-- 2⇒3 in Theorem 534 tuple. -/
lemma two_imp_three [Filtrator.Primary A] : Filtrator.Filtered α :=
  Filtrator.primary_imp_filtered (α := A)

/-- 3⇒4 in Theorem 534 tuple. -/
instance three_imp_four [Filtrator α] [Filtrator.Filtered α] : Filtrator.CoreJoinAligned α := by
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
instance two_imp_four [Filtrator.Primary A] : Filtrator.CoreJoinAligned α := by
  letI : Filtrator.Filtered α := two_imp_three (α := α)
  exact three_imp_four (α := α)

/-- 1⇒4 in Theorem 534 tuple. -/
instance one_imp_four [FiltratorOnPowerset.Primary (U := A)] : Filtrator.CoreJoinAligned (Set α) := by
  letI : FiltratorOnPowerset.Primary (U := A) := one_imp_two (A := A)
  sorry

end FilteredJoinClosedCore

export FilteredJoinClosedCore
  (three_imp_four two_imp_four one_imp_four)

-- TODO: not needed because of the below
noncomputable instance instDistribFilterOnPowerset {baseα: Type*} (α : Set baseα)
    [FiltratorOnPowerset.Primary (U := α)] :
    DistribLattice (FiltratorOnPowerset.Primary (U := α)) :=
  FilterAlsoDistributive.one_imp_three

-- FIXME: Uncomment.
-- instance instCoframeFilterOnPowerset {baseα: Type*} (α : Set baseα)
--     [F: FiltratorOnPowerset.Primary (U := α)] :
--     Order.Coframe (FiltratorOnPowerset.Primary (U := α)) :=
--   PrimaryDistribCoreBridge.primary_distribCore_imp_coframe
--     (Dcore := sorry)
--     (F := F)
--     (top := Filtrator.Primary.TopOfPrimaryFiltrator)
