import atgt.PointfreeFuncoid.Core
import atgt.AlternativePrimaryFiltrators
import atgt.Filtrator.AdvancedProperties

/-!
Section 20.6 (Specifying funcoids by functions or relations on atomic filters),
items 1650--1654 in the current development style.

Theorem 1650 is provided in a separator-bridge form: the atomic-source part is formalized
directly, while the destination-side `sSup` separator step is represented as a hypothesis.
-/

universe u v

namespace PointfreeFuncoid

/-- `sSup` of values `⟨f⟩ a` over atoms under `x` (Theorem 1650 target expression). -/
def atomicSupImage
    {α : Type u} {β : Type v}
    [X : PartialOrder α] [Y : PartialOrder β]
    [OrderBot α] [CompleteLattice β]
    (f : PointfreeFuncoid X Y) (x : α) : β :=
  sSup {z : β | ∃ a ∈ atoms x, z = f.fwd a}

theorem atomicSupSeparatorBridge
    {α : Type u} {β : Type v}
    [X : PartialOrder α]
    [OrderBot α] [CompleteDistribLattice β]
    (f : PointfreeFuncoid X (inferInstance : PartialOrder β))
    (x : α) :
    ∀ y : β,
      meet y (f.atomicSupImage x) ↔
        ∃ a ∈ atoms x, meet y (f.fwd a) := by
  intro y
  let S : Set β := {z : β | ∃ a ∈ atoms x, z = f.fwd a}
  have hstar : AlternativePrimaryFiltrators.IsCompletelyStarrish β :=
    AlternativePrimaryFiltrators.completeDistribLattice_isCompletelyStarrish β
  calc
    meet y (f.atomicSupImage x) ↔ f.atomicSupImage x ∈ separator y := by
      simp [separator, meet_comm]
    _ ↔ ∃ z ∈ S, z ∈ separator y := by
      simpa [PointfreeFuncoid.atomicSupImage, S] using (hstar y).2 S
    _ ↔ ∃ a ∈ atoms x, meet y (f.fwd a) := by
      constructor
      · rintro ⟨z, ⟨a, ha, rfl⟩, hz⟩
        exact ⟨a, ha, (meet_comm y (f.fwd a)).2 hz⟩
      · rintro ⟨a, ha, hyfa⟩
        exact ⟨f.fwd a, ⟨a, ha, rfl⟩, (meet_comm y (f.fwd a)).1 hyfa⟩

/--
Formula (25) in Theorem 1654, item 1: continuation of a function on atoms to `⟨f⟩`.
-/
def fwdContinuationFromAtoms1654
    {α : Type u} {β : Type v}
    [Filtrator α] [Filtrator β]
    [OrderBot α] [CompleteLattice β]
    (A : α → β)
    (f : PointfreeFuncoid (Filtrator.suporder (α := α)) (Filtrator.suporder (α := β))) : Prop :=
  ∀ x : α,
    f.fwd x = sSup {z : β | ∃ a ∈ atoms x, z = A a}

/--
Condition (24) in Theorem 1654, item 1, in the present vocabulary.
-/
def atomicFunctionCondition1654
    {α : Type u} {β : Type v}
    [Filtrator α]
    [OrderBot α]
    [CompleteLattice β]
    (A : α → β) : Prop :=
  ∀ a : α, IsAtom a →
    A a ≤ sInf {z : β | ∃ x ∈ Filtrator.up a,
      z = sSup {w : β | ∃ u ∈ atoms x, w = A u}}

/--
Formula (27) in Theorem 1654, item 2: continuation of a relation on atoms to `suprel f`.
-/
def relContinuationFromAtoms1654
    {α : Type u} {β : Type v}
    [X : PartialOrder α] [Y : PartialOrder β]
    [OrderBot α] [OrderBot β]
    (δ : α → β → Prop)
    (f : PointfreeFuncoid X Y) : Prop :=
  ∀ x : α, ∀ y : β,
    f.funcoid_rel x y ↔
      ∃ a ∈ atoms x, ∃ b ∈ atoms y, δ a b

/--
Condition (26) in Theorem 1654, item 2, in the present vocabulary.
-/
def atomicRelationCondition1654
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    [OrderBot α] [OrderBot β]
    (δ : α → β → Prop) : Prop :=
  ∀ a : α, ∀ b : β, IsAtom a → IsAtom b →
    (∀ X' ∈ Filtrator.up a, ∀ Y' ∈ Filtrator.up b,
      ∃ x ∈ atoms X', ∃ y ∈ atoms Y', δ x y) →
      δ a b

end PointfreeFuncoid

namespace PointfreeFuncoid.AtomicSpecification

/-- Source-side item of Proposition 1651. -/
theorem proposition1651_left
    {α : Type u} {β : Type v}
    [X : PartialOrder α] [Y : PartialOrder β]
    [OrderBot α] [IsAtomic α]
    (f : PointfreeFuncoid X Y) (x : α) (y : β) :
    f.funcoid_rel x y ↔ ∃ a ∈ atoms x, f.funcoid_rel a y := by
  constructor
  · intro hxy
    have hbwdx : meet (f.bwd y) x := (f.rev x y).1 hxy
    rcases hbwdx with ⟨c, hcbwd, hcx, hc_notleast⟩
    have hc_ne_bot : c ≠ (⊥ : α) := by
      intro hc_bot
      apply hc_notleast
      intro t
      simp [hc_bot]
    rcases (eq_bot_or_exists_atom_le (α := α) c) with hc_bot | ⟨a, ha_atom, ha_le_c⟩
    · exact False.elim (hc_ne_bot hc_bot)
    · have ha_notleast : ¬ is_least a := by
        intro ha_least
        exact ha_atom.ne_bot (le_antisymm (ha_least ⊥) bot_le)
      have hbwd_a : meet (f.bwd y) a :=
        ⟨a, le_trans ha_le_c hcbwd, le_rfl, ha_notleast⟩
      refine ⟨a, ⟨le_trans ha_le_c hcx, ha_atom⟩, ?_⟩
      exact (f.rev a y).2 hbwd_a
  · rintro ⟨a, ha, hay⟩
    have hbwd_a : meet (f.bwd y) a := (f.rev a y).1 hay
    have hbwd_x : meet (f.bwd y) x := meet_mono_right ha.1 hbwd_a
    exact (f.rev x y).2 hbwd_x

/-- Destination-side item of Proposition 1651. -/
theorem proposition1651_right
    {α : Type u} {β : Type v}
    [X : PartialOrder α] [Y : PartialOrder β]
    [OrderBot β] [IsAtomic β]
    (f : PointfreeFuncoid X Y) (x : α) (y : β) :
    f.funcoid_rel x y ↔ ∃ b ∈ atoms y, f.funcoid_rel x b := by
  constructor
  · intro hxy
    have hyx : f.inv.funcoid_rel y x := (f.funcoid_rel_comm x y).1 hxy
    rcases (proposition1651_left (f := f.inv) (x := y) (y := x)).1 hyx with
      ⟨b, hb, hbx⟩
    refine ⟨b, hb, ?_⟩
    exact (f.funcoid_rel_comm x b).2 hbx
  · rintro ⟨b, hb, hxb⟩
    have hbx : f.inv.funcoid_rel b x := (f.funcoid_rel_comm x b).1 hxb
    have hyx : f.inv.funcoid_rel y x :=
      (proposition1651_left (f := f.inv) (x := y) (y := x)).2 ⟨b, hb, hbx⟩
    exact (f.funcoid_rel_comm x y).2 hyx

/-- Proposition 1651 (both items together). -/
theorem proposition1651
    {α : Type u} {β : Type v}
    [X : PartialOrder α] [Y : PartialOrder β]
    [OrderBot α] [IsAtomic α]
    [OrderBot β] [IsAtomic β]
    (f : PointfreeFuncoid X Y) (x : α) (y : β) :
    (f.funcoid_rel x y ↔ ∃ a ∈ atoms x, f.funcoid_rel a y) ∧
      (f.funcoid_rel x y ↔ ∃ b ∈ atoms y, f.funcoid_rel x b) := by
  exact ⟨proposition1651_left (f := f) (x := x) (y := y),
    proposition1651_right (f := f) (x := x) (y := y)⟩

/-- Corollary 1652. -/
theorem corollary1652
    {α : Type u} {β : Type v}
    [X : PartialOrder α] [Y : PartialOrder β]
    [OrderBot α] [IsAtomic α]
    [OrderBot β] [IsAtomic β]
    (f : PointfreeFuncoid X Y) (x : α) (y : β) :
    f.funcoid_rel x y ↔ ∃ a ∈ atoms x, ∃ b ∈ atoms y, f.funcoid_rel a b := by
  constructor
  · intro hxy
    rcases (proposition1651_left (f := f) (x := x) (y := y)).1 hxy with ⟨a, ha, hay⟩
    rcases (proposition1651_right (f := f) (x := a) (y := y)).1 hay with ⟨b, hb, hab⟩
    exact ⟨a, ha, b, hb, hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    have hay : f.funcoid_rel a y :=
      (proposition1651_right (f := f) (x := a) (y := y)).2 ⟨b, hb, hab⟩
    exact (proposition1651_left (f := f) (x := x) (y := y)).2 ⟨a, ha, hay⟩

/--
Corollary 1653 (uniqueness form):
if two pointfree funcoids agree on every atom value, then they are equal.
-/
theorem corollary1653
    {α : Type u} {β : Type v}
    [X : PartialOrder α] [Y : PartialOrder β]
    [OrderBot α] [IsAtomic α]
    (h_sep_src : IsSeparable α)
    (h_sep_dst : IsSeparable β)
    (f g : PointfreeFuncoid X Y)
    (h_atoms : ∀ a : α, IsAtom a → f.fwd a = g.fwd a) :
    f = g := by
  apply PointfreeFuncoid.sep_fwd f g h_sep_src
  funext x
  apply h_sep_dst
  ext y
  have hrelxy : f.funcoid_rel x y ↔ g.funcoid_rel x y := by
    calc
      f.funcoid_rel x y ↔ ∃ a ∈ atoms x, f.funcoid_rel a y :=
        proposition1651_left (f := f) (x := x) (y := y)
      _ ↔ ∃ a ∈ atoms x, g.funcoid_rel a y := by
        constructor
        · rintro ⟨a, ha, hay⟩
          refine ⟨a, ha, ?_⟩
          have hfg : f.fwd a = g.fwd a := h_atoms a ha.2
          simpa [PointfreeFuncoid.funcoid_rel, hfg] using hay
        · rintro ⟨a, ha, hay⟩
          refine ⟨a, ha, ?_⟩
          have hfg : f.fwd a = g.fwd a := h_atoms a ha.2
          simpa [PointfreeFuncoid.funcoid_rel, hfg] using hay
      _ ↔ g.funcoid_rel x y :=
        (proposition1651_left (f := g) (x := x) (y := y)).symm
  simpa [separator, PointfreeFuncoid.funcoid_rel, meet_comm] using hrelxy

/--
Theorem 1650 in separator-bridge form:
once the destination-side `sSup` separator bridge is available, the value equation follows.
-/
theorem theorem1650
    {α : Type u} {β : Type v}
    [X : PartialOrder α]
    [OrderBot α] [IsAtomic α]
    [CompleteDistribLattice β]
    (h_sep_dst : IsSeparable β)
    (f : PointfreeFuncoid X (inferInstance : PartialOrder β))
    (x : α)
    :
    f.fwd x = f.atomicSupImage x := by
  apply h_sep_dst
  ext y
  have hsrc :
      meet y (f.fwd x) ↔ ∃ a ∈ atoms x, meet y (f.fwd a) := by
    simpa [PointfreeFuncoid.funcoid_rel, meet_comm] using
      (proposition1651_left (f := f) (x := x) (y := y))
  have hbridge := PointfreeFuncoid.atomicSupSeparatorBridge (f := f) x
  exact hsrc.trans (hbridge y).symm

lemma separable_of_primary_boolean_core
    {α : Type u}
    [Filtrator.Primary α]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := α))]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := α)) :
    IsSeparable α := by
  have hstrong : IsStronglySeparable α := by
    simpa [Filtrator.supset, Filtrator.suporder] using
      (primary_imp_booleanStronglySeparableCore
        (α := α) (Bcore := Bcore) (hcoreOrder := hcoreOrder))
  exact stronglySeparable_imp_separable hstrong

lemma filterSet_meet_of_forall_not_compl
    {δ : Type u}
    [B : BooleanAlgebra δ]
    (F G : AlternativePrimaryFiltrators.FilterSet (U := B.toPartialOrder))
    (hnot : ∀ a ∈ G.elements, aᶜ ∉ F.elements) :
    meet F G := by
  let Fp : PosetFilter (U := B.toPartialOrder) := PosetFilter.ThroughEquiv.toPosetFilter F
  let Gp : PosetFilter (U := B.toPartialOrder) := PosetFilter.ThroughEquiv.toPosetFilter G
  let Bfg : PosetFilterBase (U := B.toPartialOrder) := {
    elements := {x : δ | ∃ s ∈ Fp.elements, ∃ t ∈ Gp.elements, x = s ⊓ t}
    non_empty := by
      rcases Fp.non_empty with ⟨s, hs⟩
      rcases Gp.non_empty with ⟨t, ht⟩
      exact ⟨s ⊓ t, ⟨s, hs, t, ht, rfl⟩⟩
    cap_elements := by
      intro x y hx hy
      rcases hx with ⟨sx, hsx, tx, htx, rfl⟩
      rcases hy with ⟨sy, hsy, ty, hty, rfl⟩
      rcases Fp.cap_elements hsx hsy with ⟨s, hs, hs_le_sx, hs_le_sy⟩
      rcases Gp.cap_elements htx hty with ⟨t, ht, ht_le_tx, ht_le_ty⟩
      refine ⟨s ⊓ t, ⟨s, hs, t, ht, rfl⟩, ?_, ?_⟩
      · exact inf_le_inf hs_le_sx ht_le_tx
      · exact inf_le_inf hs_le_sy ht_le_ty }
  let Cpf : PosetFilter (U := B.toPartialOrder) := close_filter_base Bfg
  let C : AlternativePrimaryFiltrators.FilterSet (U := B.toPartialOrder) := PosetFilter.toThroughEquiv Cpf
  have hC_mem (x : δ) :
      x ∈ C.elements ↔
        ∃ s t, (s ∈ F.elements ∧ t ∈ G.elements) ∧ s ⊓ t ≤ x := by
    simp [C, Cpf, Bfg, Fp, Gp, close_filter_base, PosetFilter.toThroughEquiv,
      PosetFilter.ThroughEquiv.toPosetFilter]
  have hC_le_F : C ≤ F := by
    intro x hxF
    rcases G.non_empty with ⟨t, ht⟩
    exact (hC_mem x).2 ⟨x, t, ⟨hxF, ht⟩, inf_le_left⟩
  have hC_le_G : C ≤ G := by
    intro x hxG
    rcases F.non_empty with ⟨s, hs⟩
    exact (hC_mem x).2 ⟨s, x, ⟨hs, hxG⟩, inf_le_right⟩
  have hC_not_least : ¬ is_least C := by
    intro hleastC
    have hC_le_bot :
        C ≤ AlternativePrimaryFiltrators.PrincipalConstructions.filterSet_principal
          δ (⊥ : δ) := hleastC _
    have hbot_mem : (⊥ : δ) ∈ C.elements := by
      exact hC_le_bot (by
        simp [AlternativePrimaryFiltrators.PrincipalConstructions.filterSet_principal,
          PosetFilter.toThroughEquiv, PosetFilter.principal])
    rcases (hC_mem (⊥ : δ)).1 hbot_mem with ⟨s, t, hst_mem, hst_le_bot⟩
    rcases hst_mem with ⟨hsF, htG⟩
    have hst_eq_bot : s ⊓ t = (⊥ : δ) := le_antisymm hst_le_bot bot_le
    have hs_disj : Disjoint s t := disjoint_iff.mpr hst_eq_bot
    have hs_le_compl : s ≤ tᶜ := (le_compl_iff_disjoint_right).2 hs_disj
    have hupperF : IsUpperSet F.elements := AlternativePrimaryFiltrators.filter_upperSet F
    have htcompl_mem_F : tᶜ ∈ F.elements := hupperF hs_le_compl hsF
    exact (hnot t htG) htcompl_mem_F
  exact ⟨C, hC_le_F, hC_le_G, hC_not_least⟩

/-- `separator_up_property` holds for primary filtrators over boolean lattices.
This is a consequence of filters on a boolean lattice being determined by their
upper sets in the core: if `F` meets every principal filter in `G`, then `F` meets `G`. -/
lemma separator_up_of_primary_boolean_core
    {γ : Type u}
    [F : Filtrator.Primary γ]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := γ))]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := γ)) :
    F.toFiltrator.separator_up_property := by
  intro x y
  constructor
  · intro hxy z hz
    exact meet_mono_right hz.2 hxy
  · intro hall
    letI : PartialOrder (Filtrator.subset (α := γ)) := Bcore.toPartialOrder
    let Fx_sub : PosetFilter (U := Filtrator.suborder (α := γ)) :=
      Filtrator.Primary.to_poset_filter (α := γ) x
    let Fy_sub : PosetFilter (U := Filtrator.suborder (α := γ)) :=
      Filtrator.Primary.to_poset_filter (α := γ) y
    let Fx_core : PosetFilter (U := Bcore.toPartialOrder) :=
      PosetFilter.castOrderIso (h := hcoreOrder.symm) Fx_sub
    let Fy_core : PosetFilter (U := Bcore.toPartialOrder) :=
      PosetFilter.castOrderIso (h := hcoreOrder.symm) Fy_sub
    let Fx_fs : AlternativePrimaryFiltrators.FilterSet (U := Bcore.toPartialOrder) :=
      PosetFilter.toThroughEquiv Fx_core
    let Fy_fs : AlternativePrimaryFiltrators.FilterSet (U := Bcore.toPartialOrder) :=
      PosetFilter.toThroughEquiv Fy_core
    have hnot_compl :
        ∀ a : Filtrator.subset (α := γ), a ∈ Fy_fs.elements → aᶜ ∉ Fx_fs.elements := by
      intro a haFy
      have haFy_core : a ∈ Fy_core.elements := by
        simpa [Fy_fs] using haFy
      have hle_core :
          Fy_core ≤ PosetFilter.principal (U := Bcore.toPartialOrder) a :=
        (le_principal_iff_subset (F := Fy_core) (x := a)).2 haFy_core
      have hle_sub :
          Fy_sub ≤ PosetFilter.principal (U := Filtrator.suborder (α := γ)) a := by
        have hle_core_cast :
            PosetFilter.castOrderIso (h := hcoreOrder.symm) Fy_sub ≤
              PosetFilter.castOrderIso (h := hcoreOrder.symm)
                (PosetFilter.principal (U := Filtrator.suborder (α := γ)) a) := by
          simpa [Fy_core, PosetFilter.castOrderIso_principal (h := hcoreOrder.symm) a] using hle_core
        exact (PosetFilter.castOrderIso (h := hcoreOrder.symm)).map_rel_iff.1 hle_core_cast
      have haFy_sub : a ∈ Fy_sub.elements :=
        (le_principal_iff_subset (F := Fy_sub) (x := a)).1 hle_sub
      have hya : y ≤ a.1 := by
        simpa [Fy_sub, Filtrator.Primary.to_poset_filter, Filtrator.up_suborder] using haFy_sub
      have hmeet_xa : meet x a.1 := hall a.1 ⟨a.2, hya⟩
      have hsep_princ_sub :
          PosetFilter.principal (U := Filtrator.suborder (α := γ)) a ∈
            separator Fx_sub := by
        exact (principal_core_separator_iff_meet (b := x) (y := a)).2 hmeet_xa
      have hsep_princ_core :
          PosetFilter.principal (U := Bcore.toPartialOrder) a ∈
            separator Fx_core := by
        have hcast :=
          (StrongSeparability.orderIso_mem_separator_iff
            (e := PosetFilter.castOrderIso (h := hcoreOrder.symm))
            (x := PosetFilter.principal (U := Filtrator.suborder (α := γ)) a)
            (a := Fx_sub)).1 hsep_princ_sub
        simpa [Fx_core, PosetFilter.castOrderIso_principal (h := hcoreOrder.symm) a] using hcast
      have hsep_princ_fs :
          AlternativePrimaryFiltrators.PrincipalConstructions.filterSet_principal
            (Filtrator.subset (α := γ)) a ∈
              separator Fx_fs := by
        exact
          (StrongSeparability.orderIso_mem_separator_iff
            (e := AlternativePrimaryFiltrators.filterSetOrderIsoPosetFilter
              (α := Filtrator.subset (α := γ)))
            (x := AlternativePrimaryFiltrators.PrincipalConstructions.filterSet_principal
              (Filtrator.subset (α := γ)) a)
            (a := Fx_fs)).2 (by
              simpa [Fx_fs,
                AlternativePrimaryFiltrators.PrincipalConstructions.filterSet_principal,
                PosetFilter.toThroughEquiv, PosetFilter.principal] using hsep_princ_core)
      exact
        (AlternativePrimaryFiltrators.PrincipalConstructions.filterSet_principal_mem_separator_iff_not_compl_mem
          (α := Filtrator.subset (α := γ)) a Fx_fs).1 hsep_princ_fs
    have hmeet_fs : meet Fx_fs Fy_fs :=
      filterSet_meet_of_forall_not_compl (F := Fx_fs) (G := Fy_fs) hnot_compl
    have hsep_fy_fs : Fy_fs ∈ separator Fx_fs := by
      simpa [separator, meet_comm] using hmeet_fs
    have hsep_fy_core : Fy_core ∈ separator Fx_core := by
      exact
        (StrongSeparability.orderIso_mem_separator_iff
          (e := AlternativePrimaryFiltrators.filterSetOrderIsoPosetFilter
            (α := Filtrator.subset (α := γ)))
          (x := Fy_fs) (a := Fx_fs)).1 (by
            simpa [Fy_fs, Fx_fs] using hsep_fy_fs)
    have hsep_fy_sub : Fy_sub ∈ separator Fx_sub := by
      exact
        (StrongSeparability.orderIso_mem_separator_iff
          (e := PosetFilter.castOrderIso (h := hcoreOrder.symm))
          (x := Fy_sub) (a := Fx_sub)).2 (by
            simpa [Fy_core, Fx_core] using hsep_fy_core)
    have hsep_yx : y ∈ separator x := by
      have hsep_filters :
          Filtrator.Primary.to_filters_iso.toRelIso y ∈
            separator (Filtrator.Primary.to_filters_iso.toRelIso x) := by
        simpa [Fy_sub, Fx_sub,
          Filtrator.Primary.to_filters_iso_eq_to_poset_filter (α := γ) y,
          Filtrator.Primary.to_filters_iso_eq_to_poset_filter (α := γ) x] using hsep_fy_sub
      exact
        (StrongSeparability.orderIso_mem_separator_iff
          (e := Filtrator.Primary.to_filters_iso.toRelIso)
          (x := y) (a := x)).2 hsep_filters
    have hmeet_yx : meet y x := by
      simpa [separator] using hsep_yx
    exact (meet_comm y x).1 hmeet_yx

/-- Theorem 1654, item `\ref{pf-at-f}`, proof step `2^o` (reverse inequality):
for an atom `a` that is a core element, the right-hand side of condition (24)
is bounded above by `A a`. -/
lemma theorem1654_item1_item2_reverse
    {α : Type u} {β : Type v}
    [Filtrator α]
    [OrderBot α]
    [CompleteLattice β]
    (A : α → β)
    (a : α)
    (ha_atom : IsAtom a)
    (ha_core : a ∈ (Filtrator.subset : Set α)) :
    sInf {z : β | ∃ x ∈ Filtrator.up a,
      z = sSup {w : β | ∃ u ∈ atoms x, w = A u}} ≤ A a := by
  let S : Set β := {w : β | ∃ u ∈ atoms a, w = A u}
  have hS : sSup S = A a := by
    apply le_antisymm
    · refine sSup_le ?_
      intro w hw
      rcases hw with ⟨u, hu, rfl⟩
      rcases (IsAtom.le_iff ha_atom).1 hu.1 with hu_bot | hu_eq
      · exact False.elim (hu.2.ne_bot hu_bot)
      · simp [hu_eq]
    · exact le_sSup ⟨a, ⟨le_rfl, ha_atom⟩, rfl⟩
  refine sInf_le ?_
  refine ⟨a, ⟨ha_core, le_rfl⟩, ?_⟩
  simpa [S] using hS.symm

/-- Theorem 1654, item `\ref{pf-at-f}`, proof step `2^o` as an equality:
combining condition (24) with the reverse inequality on atomic core elements. -/
lemma theorem1654_item1_atom_core_value
    {α : Type u} {β : Type v}
    [Filtrator α]
    [OrderBot α]
    [CompleteLattice β]
    (A : α → β)
    (hA_cond : PointfreeFuncoid.atomicFunctionCondition1654 (A := A))
    (a : α)
    (ha_atom : IsAtom a)
    (ha_core : a ∈ (Filtrator.subset : Set α)) :
    A a = sInf {z : β | ∃ x ∈ Filtrator.up a,
      z = sSup {w : β | ∃ u ∈ atoms x, w = A u}} := by
  apply le_antisymm
  · exact hA_cond a ha_atom
  · exact theorem1654_item1_item2_reverse (A := A) (a := a) ha_atom ha_core

/-- Core-order/ambient-order alignment for core elements under the identified core order. -/
lemma core_order_le_iff_ambient
    {γ : Type u}
    [Filtrator γ]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := γ))]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := γ))
    (a b : Filtrator.subset (α := γ)) :
    (@LE.le (Filtrator.subset (α := γ)) Bcore.toPartialOrder.toLE a b) ↔ a.1 ≤ b.1 := by
  constructor
  · intro hab
    have hab_sub :
        @LE.le (Filtrator.subset (α := γ))
          (Filtrator.suborder (α := γ)).toLE a b := by
      simpa [hcoreOrder] using hab
    exact hab_sub
  · intro hab
    have hab_sub :
        @LE.le (Filtrator.subset (α := γ))
          (Filtrator.suborder (α := γ)).toLE a b := hab
    simpa [hcoreOrder] using hab_sub

/-- Coercion behavior of core bottom: for primary filtrators over boolean cores,
the core bottom coerces to the ambient bottom. -/
lemma core_bot_coe_eq_bot
    {γ : Type u}
    [Filtrator.Primary γ]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := γ))]
    [OrderBot γ]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := γ)) :
    ((⊥ : Filtrator.subset (α := γ)).1 : γ) = (⊥ : γ) := by
  let hFiltered : Filtrator.Filtered γ := Filtrator.primary_imp_filtered (α := γ)
  let botCore : Filtrator.subset (α := γ) := (⊥ : Filtrator.subset (α := γ))
  have h_up_sub : Filtrator.up (⊥ : γ) ⊆ Filtrator.up botCore.1 := by
    intro y hy
    have hbot_le_sub :
        @LE.le (Filtrator.subset (α := γ)) Bcore.toPartialOrder.toLE
          botCore ⟨y, hy.1⟩ := Bcore.bot_le ⟨y, hy.1⟩
    have hbot_le_ambient : botCore.1 ≤ y :=
      (core_order_le_iff_ambient (hcoreOrder := hcoreOrder)
        (a := botCore) (b := ⟨y, hy.1⟩)).1 hbot_le_sub
    exact ⟨hy.1, hbot_le_ambient⟩
  have hbotCore_le_bot : botCore.1 ≤ (⊥ : γ) :=
    hFiltered.is_filtered (⊥ : γ) botCore.1 h_up_sub
  exact le_antisymm hbotCore_le_bot bot_le

noncomputable def atoms_ambient
    [F: Filtrator α]
    [bot: OrderBot α]
    (X : Filtrator.subset (α := α)) :
    Set (Filtrator.supset (α := α)) :=
  atoms (ord := Filtrator.suporder (F := F)) X

/-- Coercion behavior of core join under join-closed-core alignment:
if ambient joins exist, coercion of core join equals ambient join. -/
lemma core_sup_coe_eq_sup
    {γ : Type u}
    [Filtrator γ]
    [Supγ : SemilatticeSup γ]
    [Bcore : DistribLattice (Filtrator.subset (α := γ))]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := γ))
    (hJoinAligned : Filtrator.CoreJoinAligned γ)
    (hord :
      ∀ a b : γ,
        a ≤ b ↔ @LE.le γ Supγ.toPartialOrder.toLE a b)
    (I J : Filtrator.subset (α := γ)) :
    ((I ⊔ J).1 : γ) = I.1 ⊔ J.1 := by
  have hcore_lub :
      IsLUB ({I, J} : Set (Filtrator.subset (α := γ))) (I ⊔ J) := by
    have hcore_lub_B :
        @IsLUB (Filtrator.subset (α := γ)) Bcore.toPartialOrder.toLE
          ({I, J} : Set (Filtrator.subset (α := γ))) (I ⊔ J) := by
      simpa using (isLUB_pair (a := I) (b := J))
    simpa [hcoreOrder] using hcore_lub_B
  have hamb_lub :
      IsLUB (Subtype.val '' ({I, J} : Set (Filtrator.subset (α := γ))) : Set γ)
        ((I ⊔ J).1 : γ) :=
    hJoinAligned ({I, J} : Set (Filtrator.subset (α := γ))) (I ⊔ J) hcore_lub
  have himage_pair :
      (Subtype.val '' ({I, J} : Set (Filtrator.subset (α := γ))) : Set γ) = {I.1, J.1} := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      rcases hs with rfl | rfl <;> simp
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨I, by simp, rfl⟩
      · exact ⟨J, by simp, rfl⟩
  have hsup_lub :
      IsLUB (Subtype.val '' ({I, J} : Set (Filtrator.subset (α := γ))) : Set γ)
        (I.1 ⊔ J.1) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx' : x = I.1 ∨ x = J.1 := by
        simpa [himage_pair] using hx
      rcases hx' with rfl | rfl
      · exact (hord I.1 (I.1 ⊔ J.1)).2 (@le_sup_left γ Supγ I.1 J.1)
      · exact (hord J.1 (I.1 ⊔ J.1)).2 (@le_sup_right γ Supγ I.1 J.1)
    · intro z hz
      have hI : I.1 ≤ z := hz (himage_pair.symm ▸ (by simp : I.1 ∈ ({I.1, J.1} : Set γ)))
      have hJ : J.1 ≤ z := hz (himage_pair.symm ▸ (by simp : J.1 ∈ ({I.1, J.1} : Set γ)))
      have hI' :
          @LE.le γ Supγ.toPartialOrder.toLE I.1 z :=
        (hord I.1 z).1 hI
      have hJ' :
          @LE.le γ Supγ.toPartialOrder.toLE J.1 z :=
        (hord J.1 z).1 hJ
      have hsup' :
          @LE.le γ Supγ.toPartialOrder.toLE (I.1 ⊔ J.1) z :=
        @sup_le γ Supγ I.1 J.1 z hI' hJ'
      exact (hord (I.1 ⊔ J.1) z).2 hsup'
  exact hamb_lub.unique hsup_lub

/-- Ambient-atom version of Theorem 496 (`atoms-join`) on core joins, under a
coercion-to-ambient-join compatibility hypothesis. -/
lemma atoms_coreJoin_eq_union_ambient
    {γ : Type u}
    [D : DistribLattice γ]
    [hTop : @OrderTop γ D.toLattice.toSemilatticeInf.toPartialOrder.toPreorder.toLE]
    [hBot : @OrderBot γ D.toLattice.toSemilatticeInf.toPartialOrder.toPreorder.toLE]
    [F : Filtrator.Primary γ]
    [Bcore : DistribLattice (Filtrator.subset (α := γ))]
    [OrderBot γ]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := γ))
    (hord : ∀ a b : γ, a ≤ b ↔ @LE.le γ
      D.toPartialOrder.toLE a b)
    (hCL : Nonempty (CompleteLattice (Filtrator.supset (α := γ))) :=
      ⟨primary_distribCore_imp_completeLattice (α := γ) hord⟩)
    (I J : Filtrator.subset (α := γ)) :
    atoms_ambient (@Max.max (Filtrator.subset (α := γ))
      (SemilatticeSup.toMax (α := Filtrator.subset (α := γ))) I J) =
      atoms_ambient I ∪ atoms_ambient J := by
  let _ := hCL
  let IJ : Filtrator.subset (α := γ) := @Max.max (Filtrator.subset (α := γ))
    (SemilatticeSup.toMax (α := Filtrator.subset (α := γ))) I J
  have hFiltered : Filtrator.Filtered γ := Filtrator.primary_imp_filtered (α := γ)
  have hJoinAligned : Filtrator.CoreJoinAligned γ :=
    FilteredJoinClosedCore.three_imp_four (α := γ)
  have h_core_sup_coe : (IJ.1 : γ) = I.1 ⊔ J.1 := by
    simpa [IJ] using (core_sup_coe_eq_sup
      (γ := γ) (Supγ := D.toSemilatticeSup) (Bcore := Bcore)
      (hcoreOrder := hcoreOrder) (hJoinAligned := hJoinAligned) (hord := hord)
      I J)
  have hbot_eq : (⊥ : γ) = hBot.bot := by
    apply le_antisymm
    · exact bot_le
    · exact (hord hBot.bot (⊥ : γ)).2 (hBot.bot_le (⊥ : γ))
  have hAtom_iff :
      ∀ x : γ, IsAtom x ↔ @IsAtom γ
        D.toLattice.toSemilatticeInf.toPartialOrder.toPreorder hBot x := by
    intro x
    constructor
    · intro hx
      have hx' :
          x ≠ (⊥ : γ) ∧ ∀ b : γ, b ≠ (⊥ : γ) → b ≤ x → x ≤ b :=
        (isAtom_iff_le_of_ge (a := x)).1 hx
      refine
        (@isAtom_iff_le_of_ge γ
          D.toLattice.toSemilatticeInf.toPartialOrder.toPreorder hBot x).2 ?_
      refine ⟨?_, ?_⟩
      · intro hxbot
        apply hx'.1
        simpa [hbot_eq] using hxbot
      · intro b hb_ne hbx
        have hb_ne' : b ≠ (⊥ : γ) := by
          intro hb0
          apply hb_ne
          simpa [hbot_eq] using hb0
        have hbx' : b ≤ x := (hord b x).2 hbx
        exact (hord x b).1 (hx'.2 b hb_ne' hbx')
    · intro hx
      have hx' :
          x ≠ hBot.bot ∧
            ∀ b : γ, b ≠ hBot.bot →
              @LE.le γ D.toLattice.toSemilatticeInf.toPartialOrder.toLE b x →
              @LE.le γ D.toLattice.toSemilatticeInf.toPartialOrder.toLE x b :=
        (@isAtom_iff_le_of_ge γ
          D.toLattice.toSemilatticeInf.toPartialOrder.toPreorder hBot x).1 hx
      refine (isAtom_iff_le_of_ge (a := x)).2 ?_
      refine ⟨?_, ?_⟩
      · intro hxbot
        apply hx'.1
        simpa [hbot_eq] using hxbot
      · intro b hb_ne hbx
        have hb_ne' : b ≠ hBot.bot := by
          intro hb0
          apply hb_ne
          simpa [hbot_eq] using hb0
        have hbx' :
            @LE.le γ D.toLattice.toSemilatticeInf.toPartialOrder.toLE b x :=
          (hord b x).1 hbx
        exact (hord x b).2 (hx'.2 b hb_ne' hbx')
  have hatoms_eq :
      ∀ a : γ, atoms a =
        @atoms γ D.toLattice.toSemilatticeInf.toPartialOrder hBot a := by
    intro a
    ext x
    constructor
    · intro hx
      exact ⟨(hord x a).1 hx.1, (hAtom_iff x).1 hx.2⟩
    · intro hx
      exact ⟨(hord x a).2 hx.1, (hAtom_iff x).2 hx.2⟩
  have h_atoms_sup_eq_union :
      @atoms γ D.toLattice.toSemilatticeInf.toPartialOrder hBot (I.1 ⊔ J.1) =
        @atoms γ D.toLattice.toSemilatticeInf.toPartialOrder hBot I.1 ∪
          @atoms γ D.toLattice.toSemilatticeInf.toPartialOrder hBot J.1 := by
    simpa using
      (AlternativePrimaryFiltrators.atoms_sup_eq_union
        (α := γ)
        (AlternativePrimaryFiltrators.distributiveLattice_isStarrish γ)
        I.1 J.1)
  calc
    atoms_ambient IJ = atoms (IJ.1 : γ) := by
      simp [atoms_ambient]
    _ = atoms (I.1 ⊔ J.1) := by
      simpa [h_core_sup_coe]
    _ = @atoms γ D.toLattice.toSemilatticeInf.toPartialOrder hBot (I.1 ⊔ J.1) := by
      simpa using (hatoms_eq (I.1 ⊔ J.1))
    _ = @atoms γ D.toLattice.toSemilatticeInf.toPartialOrder hBot I.1 ∪
          @atoms γ D.toLattice.toSemilatticeInf.toPartialOrder hBot J.1 :=
      h_atoms_sup_eq_union
    _ = atoms I.1 ∪ atoms J.1 := by
      simpa [hatoms_eq I.1, hatoms_eq J.1]
    _ = atoms_ambient I ∪ atoms_ambient J := by
      simp [atoms_ambient]

/-- Existence witness for Theorem 1654, item 2 (`\ref{pf-at-r}`):
construct a funcoid whose relation on atoms matches the given `δ`.
The construction follows the book proof: lift `δ` to a core relation
`δ'(X, Y) ↔ ∃ x ∈ atoms X, ∃ y ∈ atoms Y, δ x y`, verify the core conditions
(⊥ and ⊔ preservation), apply theorem 1618 (`pf-cont`), and bridge from
`relContinuationFromCore` to `relContinuationFromAtoms1654` via corollary 1652
and the atomic relation condition. -/
lemma theorem1654_item2_exists
    {α : Type u} {β : Type v}
    [X : Filtrator.Primary α] [Y : Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    [OrderBot α] [OrderBot β]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (δ : α → β → Prop)
    (hδ_cond : PointfreeFuncoid.atomicRelationCondition1654 (δ := δ)) :
    ∃ f : PointfreeFuncoid (Filtrator.suporder (α := α)) (Filtrator.suporder (α := β)),
      PointfreeFuncoid.relContinuationFromAtoms1654 (δ := δ) f := by
  /-
  Proof outline (following the book proof of Theorem 1654, item \ref{pf-at-r}):
  1. Define the core relation δ'(x, y) := ∃ a ∈ atoms x, ∃ b ∈ atoms y, δ a b.
  2. Verify core conditions for δ':
     - ¬ δ'(⊥_core, Y) and ¬ δ'(X, ⊥_core) (atoms of core-⊥ is empty)
     - δ'((I ⊔ J)_core, K) ↔ δ'(I, K) ∨ δ'(J, K) (atoms distributes over core-⊔)
     - similarly for the right argument
  3. Apply theorem 1618 (pf-cont) to obtain ∃!f with relContinuationFromCore(δ', f).
  4. Bridge: for atoms a, b:
     f.funcoid_rel a b ↔ ∀X'∈up a, ∀Y'∈up b, δ' X' Y'
                        ↔ ∀X'∈up a, ∀Y'∈up b, (∃x∈atoms X', ∃y∈atoms Y', δ x y)
                        ↔ δ a b  (by atomicRelationCondition1654 + trivial reverse)
  5. Use corollary 1652 to extend to all elements:
     f.funcoid_rel x y ↔ ∃a∈atoms x, ∃b∈atoms y, f.funcoid_rel a b
                        ↔ ∃a∈atoms x, ∃b∈atoms y, δ a b
  -/
  sorry

/-- Existence witness for Theorem 1654, item 1 (`\ref{pf-at-f}`):
construct a funcoid whose forward function on atoms matches the given function `A`.
The construction follows the book proof: define `α'` on core by
`α'(X) = ⊔{A(a) | a ∈ atoms X}`, show it preserves ⊥ and ⊔,
apply theorem 1618 (`pf-cont`), and verify the continuation property. -/
lemma theorem1654_item1_exists
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    [OrderBot α]
    [CompleteLattice β]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (A : α → β)
    (hA_cond : PointfreeFuncoid.atomicFunctionCondition1654 (A := A)) :
    ∃ f : PointfreeFuncoid (Filtrator.suporder (α := α)) (Filtrator.suporder (α := β)),
      PointfreeFuncoid.fwdContinuationFromAtoms1654 (A := A) f := by
  have h_item2 :
      ∀ a : α, IsAtom a → a ∈ (Filtrator.subset : Set α) →
        A a =
          sInf {z : β | ∃ x ∈ Filtrator.up a,
            z = sSup {w : β | ∃ u ∈ atoms x, w = A u}} := by
    intro a ha_atom ha_core
    exact theorem1654_item1_atom_core_value
      (A := A) (hA_cond := hA_cond) (a := a) ha_atom ha_core
  -- Item `2^o` from the book proof is formalized above; item `1^o` remains.
  have _ := h_item2
  sorry

/--
Theorem 1654, item 1 (`\ref{pf-at-f}`): existence and uniqueness of a pointfree funcoid
whose forward function on atoms matches the given function `A`.
Existence is constructed via theorem 1618 (`pf-cont`).
-/
theorem theorem1654_item1
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    [OrderBot α]
    [CompleteLattice β]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (A : α → β)
    (hA_cond : PointfreeFuncoid.atomicFunctionCondition1654 (A := A)) :
    ∃! f : PointfreeFuncoid (Filtrator.suporder (α := α)) (Filtrator.suporder (α := β)),
      PointfreeFuncoid.fwdContinuationFromAtoms1654 (A := A) f := by
  have h_sep_src : IsSeparable α :=
    separable_of_primary_boolean_core
      (α := α) (Bcore := Bsrc) h_src_core_order
  rcases theorem1654_item1_exists h_src_core_order h_dst_core_order A hA_cond with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  have hfg : f = g := by
    apply PointfreeFuncoid.sep_fwd f g h_sep_src
    funext x
    exact (hf x).trans (hg x).symm
  exact hfg.symm

/--
Theorem 1654, item 2 (`\ref{pf-at-r}`): existence and uniqueness of a pointfree funcoid
whose relation on atoms matches the given relation `δ`.
Existence is constructed via theorem 1618 (`pf-cont`) by lifting `δ` to a core relation
`δ'(X, Y) ↔ ∃ x ∈ atoms X, ∃ y ∈ atoms Y, δ x y`.
-/
theorem theorem1654_item2
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    [OrderBot α] [OrderBot β]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (δ : α → β → Prop)
    (hδ_cond : PointfreeFuncoid.atomicRelationCondition1654 (δ := δ)) :
    ∃! f : PointfreeFuncoid (Filtrator.suporder (α := α)) (Filtrator.suporder (α := β)),
      PointfreeFuncoid.relContinuationFromAtoms1654 (δ := δ) f := by
  have h_sep_src : IsSeparable α :=
    separable_of_primary_boolean_core
      (α := α) (Bcore := Bsrc) h_src_core_order
  have h_sep_dst : IsSeparable β :=
    separable_of_primary_boolean_core
      (α := β) (Bcore := Bdst) h_dst_core_order
  rcases theorem1654_item2_exists h_src_core_order h_dst_core_order δ hδ_cond with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  have hfg : f = g := by
    apply PointfreeFuncoid.sep_rel f g h_sep_src h_sep_dst
    funext x y
    exact propext ((hf x y).trans (hg x y).symm)
  exact hfg.symm

end PointfreeFuncoid.AtomicSpecification

export PointfreeFuncoid
  (atomicSupImage atomicSupSeparatorBridge
    fwdContinuationFromAtoms1654 atomicFunctionCondition1654
    relContinuationFromAtoms1654 atomicRelationCondition1654)

export PointfreeFuncoid.AtomicSpecification
  (theorem1650 proposition1651_left proposition1651_right proposition1651
    corollary1652 corollary1653
    theorem1654_item1 theorem1654_item2)
