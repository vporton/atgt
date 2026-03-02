import Mathlib.Data.Ordmap.Ordset
import Mathlib.Order.CompleteBooleanAlgebra
import atgt.Poset
import atgt.Filtrator
import atgt.Filtrator.Separable
import atgt.Filtrator.SeparablePrimary
import atgt.Filtrator.AdvancedProperties
import atgt.AlternativePrimaryFiltrators

universe u v u2 v2

structure PointfreeFuncoid {α: Type u}{β: Type v}(a: PartialOrder α)(b: PartialOrder β) where
    fwd : α → β
    bwd : β → α
    rev (x: α) (y: β) : @meet _ b (fwd x) y ↔ @meet _ a (bwd y) x

@[ext]
lemma PointfreeFuncoid.ext {α: Type u}{β: Type v} {a : PartialOrder α} {b : PartialOrder β}
  (f g : @PointfreeFuncoid α β a b)
  (h_fwd : f.fwd = g.fwd)
  (h_bwd : f.bwd = g.bwd) : f = g := by
  cases f; cases g;
  congr

instance PointfreeFuncoid.inv {u v}
  {a : PartialOrder u}{b : PartialOrder v}
  (f : @PointfreeFuncoid u v a b) :
  @PointfreeFuncoid v u b a where
    fwd := f.bwd
    bwd := f.fwd
    rev (x : v) (y : u) := (f.rev y x).symm

theorem inv_inv_funcoid{α β : Type*}(a: PartialOrder α)(b: PartialOrder β)(f: @PointfreeFuncoid α β a b) :
    f.inv.inv = f := by simp[PointfreeFuncoid.inv]

/- FIXME: Can be converted to instance? -/
def PointfreeFuncoid.on_semilattice_inf{α β : Type*}
  {a : SemilatticeInf α} {b : SemilatticeInf β} :=
  @PointfreeFuncoid α β a.toPartialOrder b.toPartialOrder

instance PointfreeFuncoid.instLE{α β : Type*}
  (a : PartialOrder α) (b : PartialOrder β) :
  LE (@PointfreeFuncoid α β a b) :=
⟨fun f g =>
  (∀ x, f.fwd x ≤ g.fwd x) ∧ (∀ y, f.bwd y ≤ g.bwd y)⟩

instance PointfreeFuncoid.instPartialOrder {α β : Type*}
    (a : PartialOrder α) (b : PartialOrder β) :
    PartialOrder (@PointfreeFuncoid α β a b) where
  le := (· ≤ ·)
  le_refl f := by
    exact ⟨(by intro x; exact le_rfl), (by intro y; exact le_rfl)⟩
  le_trans f g h hfg hgh := by
    refine ⟨?_, ?_⟩
    · intro x
      exact le_trans (hfg.1 x) (hgh.1 x)
    · intro y
      exact le_trans (hfg.2 y) (hgh.2 y)
  le_antisymm f g hfg hgf := by
    apply PointfreeFuncoid.ext
    · funext x
      exact le_antisymm (hfg.1 x) (hgf.1 x)
    · funext y
      exact le_antisymm (hfg.2 y) (hgf.2 y)

/- TODO: Add `Semicategory` to MathLib and use it for `comp`. -/
-- instance PointfreeFuncoid.instSemigroup
--   {u v} (a : PartialOrder u) (b : PartialOrder v) :
--   Semicategory (PointfreeFuncoid a b) := {
--     mul: f g:
--   }

def comp {α β γ: Type*}{X: PartialOrder α}{Y: PartialOrder β}{Z: PartialOrder γ}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z)
    : PointfreeFuncoid X Z
    := {
        fwd := g.fwd ∘ f.fwd
        bwd := f.bwd ∘ g.bwd
        rev := by
            intro α γ
            -- g.rev gives: meet Y (g.fwd (f.fwd α)) z ↔ meet Y (f.fwd β) (g.bwd γ)
            -- f.rev needs:  meet Y (g.bwd γ) (f.fwd α)
            -- so we commute the meet
            refine
                    (g.rev (f.fwd α) γ).trans ?_
            have := f.rev α (g.bwd γ)
            -- commute the meet on Y
            simpa [meet_comm] using this
    }

infixr:80 " ∘ " => comp

theorem comp_assoc{α β γ δ : Type*} {X: PartialOrder α}{Y: PartialOrder β}{Z: PartialOrder γ}{W: PartialOrder δ}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z) (h: PointfreeFuncoid Z W)
    : (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
    ext <;> rfl

theorem inv_comp {α β γ : Type*} {X: PartialOrder α}{Y: PartialOrder β}{Z: PartialOrder γ}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z)
    : (f ∘ g).inv = g.inv ∘ f.inv := by
    ext <;> rfl

def PointfreeFuncoid.funcoid_rel {α: Type u}{β: Type v}{X: PartialOrder α}{Y: PartialOrder β}
    (f: PointfreeFuncoid X Y) (a : α) (b : β) :
    Prop
    := @meet β Y (f.fwd a) b

theorem PointfreeFuncoid.funcoid_rel_comm {α β: Type*} {X: PartialOrder α}{Y: PartialOrder β}
    (f: PointfreeFuncoid X Y) (a : α) (b : β) :
    f.funcoid_rel a b ↔ f.inv.funcoid_rel b a :=
    f.rev a b

theorem PointfreeFuncoid.sep_fwd {α β: Type*} [X : PartialOrder α] [Y : PartialOrder β] (f g : PointfreeFuncoid X Y) :
    IsSeparable α → f.fwd = g.fwd → f = g := by
    intro h_sep h_fwd
    apply PointfreeFuncoid.ext
    · exact h_fwd
    · funext β
      apply h_sep
      ext α
      simp [separator]
      rw [meet_comm α, meet_comm α]
      rw [← f.rev, ← g.rev]
      rw [h_fwd]

theorem PointfreeFuncoid.sep_rel {α β : Type*} [X : PartialOrder α] [Y : PartialOrder β] (f g : PointfreeFuncoid X Y) :
    IsSeparable α → IsSeparable β → f.funcoid_rel = g.funcoid_rel → f = g := by
    intro h_sep_u h_sep_v h_rel
    apply PointfreeFuncoid.sep_fwd f g h_sep_u
    funext α
    apply h_sep_v
    ext β
    simp [separator]
    rw [meet_comm β, meet_comm β]
    change f.funcoid_rel α β ↔ g.funcoid_rel α β
    rw [h_rel]

lemma rel_right_flt{α: Type u}{β: Type v}[X: PartialOrder α][Y: Filtrator β]
    (h_sep_up : Y.separator_up_property) (f: PointfreeFuncoid X Y.suporder) (a: α) (b: β) :
    f.funcoid_rel a b ↔ ∀ y ∈ Filtrator.up b, f.funcoid_rel a y :=
    h_sep_up (f.fwd a) b

lemma rel_left_flt{α: Type u}{β: Type v}[X: Filtrator α][Y: PartialOrder β]
    (h_sep_up : X.separator_up_property) (f: PointfreeFuncoid X.suporder Y) (a: α) (b: β) :
    f.funcoid_rel a b ↔ ∀ x ∈ Filtrator.up a, f.funcoid_rel x b := by
    rw [f.funcoid_rel_comm, rel_right_flt h_sep_up f.inv]
    simp_rw [PointfreeFuncoid.funcoid_rel_comm f.inv, inv_inv_funcoid]

lemma rel_flt{α: Type u}{β: Type v}[X: Filtrator α][Y: Filtrator β]
    (h_sep_up1 : X.separator_up_property) (h_sep_up2 : Y.separator_up_property)
    (f: PointfreeFuncoid X.suporder Y.suporder) (a: α) (b: β) :
    f.funcoid_rel a b ↔ ∀ x ∈ Filtrator.up a, ∀ y ∈ Filtrator.up b, f.funcoid_rel x y := by
    rw [rel_left_flt h_sep_up1]
    conv_lhs =>
      ext x hx
      rw [rel_right_flt h_sep_up2]

def PointfreeFuncoid.continuationSeparator {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (f : PointfreeFuncoid X.suporder Y.suporder) (x : α) : Set β :=
  { y : β | ∀ X' ∈ Filtrator.up x, f.funcoid_rel X' y }

/--
Bridge lemma: the continuation separator is exactly the pointwise intersection of separators
of values `⟨f⟩ X'` over `X' ∈ up x`.
-/
theorem continuationSeparator_eq_iInter_separator
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α) :
    f.continuationSeparator x =
      { y : β | ∀ X' ∈ Filtrator.up x, y ∈ separator (f.fwd X') } := by
  ext y
  constructor
  · intro hy X' hX'
    exact (by
      simpa [PointfreeFuncoid.funcoid_rel, separator, meet_comm] using hy X' hX')
  · intro hy X' hX'
    exact (by
      simpa [PointfreeFuncoid.funcoid_rel, separator, meet_comm] using hy X' hX')

/--
Proposition 1615 (source-side form used later): under the source separability-over-up
hypothesis, membership in the separator of `⟨f⟩ x` is equivalent to satisfying the relation
for all `X' ∈ up x`.
-/
theorem proposition1615_source
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (h_sep_up : X.separator_up_property)
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α) :
    separator (f.fwd x) = f.continuationSeparator x := by
  ext y
  constructor
  · intro hy X' hX'
    have hxy : f.funcoid_rel x y := by
      simpa [PointfreeFuncoid.funcoid_rel, separator, meet_comm] using hy
    exact (rel_left_flt (h_sep_up := h_sep_up) (f := f) (a := x) (b := y)).1 hxy X' hX'
  · intro hy
    have hxy : f.funcoid_rel x y :=
      (rel_left_flt (h_sep_up := h_sep_up) (f := f) (a := x) (b := y)).2 hy
    simpa [PointfreeFuncoid.funcoid_rel, separator, meet_comm] using hxy

/--
Corollary form used in theorem 1617: if the destination order is separable, any value whose
separator equals the continuation separator must be `⟨f⟩ x`.
-/
theorem continuation_value_of_separator
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (h_sep_up : X.separator_up_property)
    (h_sep_dst : IsSeparable β)
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α) (z : β)
    (hz : separator z = f.continuationSeparator x) :
    z = f.fwd x := by
  apply h_sep_dst
  calc
    separator z = f.continuationSeparator x := hz
    _ = separator (f.fwd x) := (proposition1615_source (h_sep_up := h_sep_up) (f := f) (x := x)).symm

/--
Forward bridge toward Theorem 1617: the separator of the `sInf` candidate is contained in
the continuation separator. This is the monotonic direction (`sInf ≤ each member`).
-/
theorem separator_subset_continuationSeparator_of_lower_bound
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α)
    (z : β)
    (h_lower : ∀ X' : α, X' ∈ Filtrator.up x → z ≤ f.fwd X') :
    separator z ⊆ f.continuationSeparator x := by
  intro y hy X' hX'
  have hmeet : meet y z := by
    simpa [separator] using hy
  have hmeet' : meet y (f.fwd X') := meet_mono_right (h_lower X' hX') hmeet
  simpa [PointfreeFuncoid.funcoid_rel, meet_comm] using hmeet'

/--
Forward bridge toward Theorem 1617 for an explicit `sInf` candidate indexed by a core function.
-/
theorem separator_sInf_image_subset_continuationSeparator
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (Ldst : CompleteLattice (Filtrator.subset (α := β)))
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α)
    (A : α → β) :
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Ldst.toInfSet
          {A z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X') →
    separator
      (↑(@sInf (Filtrator.subset (α := β))
        Ldst.toInfSet
        {A z | z ∈ Filtrator.up x}) : β) ⊆
      f.continuationSeparator x := by
  intro h_lower
  exact separator_subset_continuationSeparator_of_lower_bound
    (f := f) (x := x)
    (z := (↑(@sInf (Filtrator.subset (α := β))
      Ldst.toInfSet
      {A z | z ∈ Filtrator.up x}) : β))
    h_lower

/--
Second bridge in equality form once the reverse inclusion is provided.
The reverse direction is the generalized-filter-base step from the book proof.
-/
theorem separator_sInf_image_eq_continuationSeparator_of_reverse
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (Ldst : CompleteLattice (Filtrator.subset (α := β)))
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α)
    (A : α → β)
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Ldst.toInfSet
          {A z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X')
    (h_reverse :
      f.continuationSeparator x ⊆
        separator
          (↑(@sInf (Filtrator.subset (α := β))
            Ldst.toInfSet
            {A z | z ∈ Filtrator.up x}) : β)) :
    separator
      (↑(@sInf (Filtrator.subset (α := β))
        Ldst.toInfSet
        {A z | z ∈ Filtrator.up x}) : β) =
      f.continuationSeparator x := by
  exact Set.Subset.antisymm
    (separator_sInf_image_subset_continuationSeparator
      (Ldst := Ldst) (f := f) (x := x) (A := A) h_lower)
    h_reverse

/--
Theorem 1617 reduced to the separator bridge obligations:
if the destination side provides separability and both separator inclusions for the `sInf`
candidate, then the target value equation follows.
-/
theorem theorem1617_of_separator_bridge
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (Ldst : CompleteLattice (Filtrator.subset (α := β)))
    (h_src_sep_up : X.separator_up_property)
    (h_sep_dst : IsSeparable β)
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α)
    (A : α → β)
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Ldst.toInfSet
          {A z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X')
    (h_reverse :
      f.continuationSeparator x ⊆
        separator
          (↑(@sInf (Filtrator.subset (α := β))
            Ldst.toInfSet
            {A z | z ∈ Filtrator.up x}) : β)) :
    f.fwd x =
      (↑(@sInf (Filtrator.subset (α := β))
        Ldst.toInfSet
        {A z | z ∈ Filtrator.up x}) : β) := by
  have hsep :
      separator
        (↑(@sInf (Filtrator.subset (α := β))
          Ldst.toInfSet
          {A z | z ∈ Filtrator.up x}) : β) =
      f.continuationSeparator x :=
    separator_sInf_image_eq_continuationSeparator_of_reverse
      (Ldst := Ldst) (f := f) (x := x) (A := A) h_lower h_reverse
  have hsInf_eq_fx :
      (↑(@sInf (Filtrator.subset (α := β))
        Ldst.toInfSet
        {A z | z ∈ Filtrator.up x}) : β) = f.fwd x :=
    continuation_value_of_separator
      (h_sep_up := h_src_sep_up) (h_sep_dst := h_sep_dst) (f := f) (x := x)
      (z := (↑(@sInf (Filtrator.subset (α := β))
        Ldst.toInfSet
        {A z | z ∈ Filtrator.up x}) : β))
      hsep
  exact hsInf_eq_fx.symm

/--
Theorem 1617 (p. 317), literal value equation form:
`⟨f⟩ x = sInf (⟨⟨f⟩⟩ (up x))`.
-/
theorem pointfree_funcoid_fwd_value
    {α : Type u} {β : Type v}
    [X : Filtrator α]
    [F : Filtrator.Primary β]
    [Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β))]
    (h_dst_core_order :
      Bdst.toBooleanAlgebra.toPartialOrder = Filtrator.suborder (α := β))
    (h_src_sep_up : X.separator_up_property)
    (A : α → β)
    (f : PointfreeFuncoid X.suporder (Filtrator.suporder (α := β)))
    (x : α)
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {A z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X')
    (h_reverse :
      f.continuationSeparator x ⊆
        separator
          (↑(@sInf (Filtrator.subset (α := β))
            Bdst.toCompleteLattice.toInfSet
            {A z | z ∈ Filtrator.up x}) : β)) :
    f.fwd x =
      (@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {A z | z ∈ Filtrator.up x}) := by
  -- The proof path is established in helpers above (Proposition 1615 separator form and
  -- separator-based value recovery). The remaining bridge is to identify the separator of
  -- `sInf (A '' Filtrator.up x)` with `continuationSeparator`, via generalized-filter-base
  -- machinery (Theorem 572 / Proposition 579 route from the PDF proof).
  -- Once those two bridge inclusions and destination separability are supplied, use
  -- `theorem1617_of_separator_bridge`.
  letI : BooleanAlgebra (Filtrator.subset (α := β)) := Bdst.toBooleanAlgebra
  have h_sep_dst : IsSeparable β := by
    have h_strong_dst : IsStronglySeparable β := by
      simpa [Filtrator.supset, Filtrator.suporder] using
        (primary_imp_booleanStronglySeparableCore
          (α := β)
          (Bcore := Bdst.toBooleanAlgebra)
          (hcoreOrder := h_dst_core_order))
    exact stronglySeparable_imp_separable h_strong_dst
  have hfinal :
      f.fwd x =
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {A z | z ∈ Filtrator.up x}) : β) :=
    theorem1617_of_separator_bridge
      (Ldst := Bdst.toCompleteLattice)
      (h_src_sep_up := h_src_sep_up)
      (h_sep_dst := h_sep_dst)
      (f := f) (x := x) (A := A) h_lower h_reverse
  simpa using hfinal

/--
`pf-cont` function continuation formula (`\ref{pf-alpha-filter}`) written in the current
Lean model.
-/
def PointfreeFuncoid.fwdContinuationFromCore
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (A : α → β)
    (f : PointfreeFuncoid X.suporder Y.suporder) : Prop :=
  ∀ x : α,
    f.fwd x =
      (↑(@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {A z | z ∈ Filtrator.up x}) : β)

/--
`pf-cont` relation continuation formula (`\ref{pf-suprel-delta}`) written in the current
Lean model.
-/
def PointfreeFuncoid.relContinuationFromCore
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (δ : α → β → Prop)
    (f : PointfreeFuncoid X.suporder Y.suporder) : Prop :=
  ∀ x : α, ∀ y : β,
    f.funcoid_rel x y ↔
      (∀ X' ∈ Filtrator.up x, ∀ Y' ∈ Filtrator.up y, δ X' Y')

open AlternativePrimaryFiltrators
open AlternativePrimaryFiltrators.PrincipalConstructions

lemma principal_core_separator_iff_meet
    {β : Type u} [Filtrator.Primary β]
    (b : β) (y : Filtrator.subset (α := β)) :
    (PosetFilter.principal (U := Filtrator.suborder (α := β)) y ∈
      separator (Filtrator.Primary.to_poset_filter (α := β) b)) ↔ meet b y.1 := by
  have hsep : y.1 ∈ separator b ↔
      Filtrator.Primary.to_filters_iso.toRelIso y.1 ∈
        separator (Filtrator.Primary.to_filters_iso.toRelIso b) :=
    (StrongSeparability.orderIso_mem_separator_iff
      (e := Filtrator.Primary.to_filters_iso.toRelIso)
      (x := y.1) (a := b))
  have hy : Filtrator.Primary.to_filters_iso.toRelIso y.1 =
      PosetFilter.principal (U := Filtrator.suborder (α := β)) y := by
    calc
      Filtrator.Primary.to_filters_iso.toRelIso y.1 =
          Filtrator.Primary.to_poset_filter (α := β) y.1 :=
        Filtrator.Primary.to_filters_iso_eq_to_poset_filter (α := β) y.1
      _ = PosetFilter.principal (U := Filtrator.suborder (α := β)) y := by
        ext z
        rfl
  have hb : Filtrator.Primary.to_filters_iso.toRelIso b =
      Filtrator.Primary.to_poset_filter (α := β) b :=
    Filtrator.Primary.to_filters_iso_eq_to_poset_filter (α := β) b
  have hfinal : y.1 ∈ separator b ↔
      PosetFilter.principal (U := Filtrator.suborder (α := β)) y ∈
        separator (Filtrator.Primary.to_poset_filter (α := β) b) := by
    simpa [hy, hb] using hsep
  simpa [separator, meet_comm] using hfinal.symm

lemma exists_core_value_of_freeStar
    {β : Type u} [Filtrator.Primary β]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (S : @FreeStar (Filtrator.subset (α := β)) Bdst.toPartialOrder) :
    letI : PartialOrder (Filtrator.subset (α := β)) := Bdst.toPartialOrder
    ∃ b : β, ∀ y : Filtrator.subset (α := β),
      y ∈ (@FreeStar.elements (Filtrator.subset (α := β)) Bdst.toPartialOrder S) ↔ meet b y.1 := by
  letI : PartialOrder (Filtrator.subset (α := β)) := Bdst.toPartialOrder
  let F_through : FilterSet (U := (inferInstance : PartialOrder (Filtrator.subset (α := β)))) :=
    freeStar_to_filterSet S
  let F_pos : PosetFilter (U := (inferInstance : PartialOrder (Filtrator.subset (α := β)))) :=
    PosetFilter.ThroughEquiv.toPosetFilter F_through
  let F_sub : PosetFilter (U := Filtrator.suborder (α := β)) :=
    PosetFilter.castOrderIso h_dst_core_order F_pos
  rcases Filtrator.Primary.exists_to_poset_filter_eq (α := β) F_sub with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro y
  have h1 : y ∈ (@FreeStar.elements (Filtrator.subset (α := β)) Bdst.toPartialOrder S) ↔
      filterSet_principal (Filtrator.subset (α := β)) y ∈ separator F_through := by
    constructor
    · intro hy
      have hnot_compl : yᶜ ∉ F_through.elements := by
        intro hyc
        exact ((compl_mem_freeStar_to_filterSet_iff_not_mem
          (α := Filtrator.subset (α := β)) y S).1 (by simpa [F_through] using hyc)) hy
      exact (filterSet_principal_mem_separator_iff_not_compl_mem
        (α := Filtrator.subset (α := β)) y F_through).2 hnot_compl
    · intro hy
      have hnot_compl : yᶜ ∉ F_through.elements :=
        (filterSet_principal_mem_separator_iff_not_compl_mem
          (α := Filtrator.subset (α := β)) y F_through).1 hy
      by_contra hny
      exact hnot_compl ((compl_mem_freeStar_to_filterSet_iff_not_mem
        (α := Filtrator.subset (α := β)) y S).2 hny)
  have h2 :
      filterSet_principal (Filtrator.subset (α := β)) y ∈ separator F_through ↔
      PosetFilter.principal (U := (inferInstance : PartialOrder (Filtrator.subset (α := β)))) y ∈
        separator F_pos := by
    simpa [filterSet_principal, F_pos] using
      (StrongSeparability.orderIso_mem_separator_iff
        (e := filterSetOrderIsoPosetFilter (α := Filtrator.subset (α := β)))
        (x := filterSet_principal (Filtrator.subset (α := β)) y)
        (a := F_through))
  have h3 :
      PosetFilter.principal (U := (inferInstance : PartialOrder (Filtrator.subset (α := β)))) y ∈
        separator F_pos ↔
      PosetFilter.principal (U := Filtrator.suborder (α := β)) y ∈
        separator F_sub := by
    simpa [F_sub, PosetFilter.castOrderIso_principal (h := h_dst_core_order) y] using
      (StrongSeparability.orderIso_mem_separator_iff
        (e := PosetFilter.castOrderIso h_dst_core_order)
        (x := PosetFilter.principal
          (U := (inferInstance : PartialOrder (Filtrator.subset (α := β)))) y)
        (a := F_pos))
  have h4 :
      PosetFilter.principal (U := Filtrator.suborder (α := β)) y ∈
        separator F_sub ↔
      PosetFilter.principal (U := Filtrator.suborder (α := β)) y ∈
        separator (Filtrator.Primary.to_poset_filter (α := β) b) := by
    simp [hb]
  calc
    y ∈ (@FreeStar.elements (Filtrator.subset (α := β)) Bdst.toPartialOrder S) ↔
      filterSet_principal (Filtrator.subset (α := β)) y ∈ separator F_through := h1
    _ ↔
      PosetFilter.principal (U := (inferInstance : PartialOrder (Filtrator.subset (α := β)))) y ∈
        separator F_pos := h2
    _ ↔
      PosetFilter.principal (U := Filtrator.suborder (α := β)) y ∈
        separator F_sub := h3
    _ ↔
      PosetFilter.principal (U := Filtrator.suborder (α := β)) y ∈
        separator (Filtrator.Primary.to_poset_filter (α := β) b) := h4
    _ ↔ meet b y.1 := principal_core_separator_iff_meet (b := b) (y := y)

lemma delta_left_mono_core
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    (δ : α → β → Prop)
    (hδ_sup_left :
      ∀ I J : Filtrator.subset (α := α), ∀ K' : Filtrator.subset (α := β),
        δ (I ⊔ J).1 K'.1 ↔ δ I.1 K'.1 ∨ δ J.1 K'.1)
    {I J : Filtrator.subset (α := α)} {K' : Filtrator.subset (α := β)}
    (hIJ : @LE.le (Filtrator.subset (α := α)) Bsrc.toPartialOrder.toLE I J) :
    δ I.1 K'.1 → δ J.1 K'.1 := by
  intro hIK
  have hsup : I ⊔ J = J := sup_eq_right.mpr hIJ
  have h_eq : δ J.1 K'.1 ↔ δ I.1 K'.1 ∨ δ J.1 K'.1 := by
    calc
      δ J.1 K'.1 ↔ δ (I ⊔ J).1 K'.1 := by simp [hsup]
      _ ↔ δ I.1 K'.1 ∨ δ J.1 K'.1 := hδ_sup_left I J K'
  exact h_eq.2 (Or.inl hIK)

lemma delta_left_antitone_not_core
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    (δ : α → β → Prop)
    (hδ_sup_left :
      ∀ I J : Filtrator.subset (α := α), ∀ K' : Filtrator.subset (α := β),
        δ (I ⊔ J).1 K'.1 ↔ δ I.1 K'.1 ∨ δ J.1 K'.1)
    {I J : Filtrator.subset (α := α)} {K' : Filtrator.subset (α := β)}
    (hIJ : @LE.le (Filtrator.subset (α := α)) Bsrc.toPartialOrder.toLE I J) :
    ¬ δ J.1 K'.1 → ¬ δ I.1 K'.1 := by
  intro hJ hI
  exact hJ (delta_left_mono_core (δ := δ) (hδ_sup_left := hδ_sup_left) hIJ hI)

lemma delta_right_mono_core
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    (δ : α → β → Prop)
    (hδ_sup_right :
      ∀ K : Filtrator.subset (α := α), ∀ I' J' : Filtrator.subset (α := β),
        δ K.1 (I' ⊔ J').1 ↔ δ K.1 I'.1 ∨ δ K.1 J'.1)
    {K : Filtrator.subset (α := α)} {I' J' : Filtrator.subset (α := β)}
    (hIJ : @LE.le (Filtrator.subset (α := β)) Bdst.toPartialOrder.toLE I' J') :
    δ K.1 I'.1 → δ K.1 J'.1 := by
  intro hKI
  have hsup : I' ⊔ J' = J' := sup_eq_right.mpr hIJ
  have h_eq : δ K.1 J'.1 ↔ δ K.1 I'.1 ∨ δ K.1 J'.1 := by
    calc
      δ K.1 J'.1 ↔ δ K.1 (I' ⊔ J').1 := by simp [hsup]
      _ ↔ δ K.1 I'.1 ∨ δ K.1 J'.1 := hδ_sup_right K I' J'
  exact h_eq.2 (Or.inl hKI)

noncomputable def relRightCoreFreeStar
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (δ : α → β → Prop)
    (hδ_bot_right : ∀ I : Filtrator.subset (α := α), ¬ δ I.1 (⊥ : Filtrator.subset (α := β)).1)
    (hδ_sup_left :
      ∀ I J : Filtrator.subset (α := α), ∀ K' : Filtrator.subset (α := β),
        δ (I ⊔ J).1 K'.1 ↔ δ I.1 K'.1 ∨ δ J.1 K'.1)
    (hδ_sup_right :
      ∀ K : Filtrator.subset (α := α), ∀ I' J' : Filtrator.subset (α := β),
        δ K.1 (I' ⊔ J').1 ↔ δ K.1 I'.1 ∨ δ K.1 J'.1)
    (x : α) :
    @FreeStar (Filtrator.subset (α := β)) Bdst.toPartialOrder := by
  classical
  letI : PartialOrder (Filtrator.subset (α := α)) := Bsrc.toPartialOrder
  letI : PartialOrder (Filtrator.subset (α := β)) := Bdst.toPartialOrder
  refine
    { elements := {y : Filtrator.subset (α := β) | ∀ X' ∈ Filtrator.up x, δ X' y.1}
      non_univ := ?_
      cup_not_elements := ?_ }
  · intro h_univ
    rcases Filtrator.Primary.exists_up_in_subset (α := α) x with ⟨X0, hX0⟩
    have hbot_mem : (⊥ : Filtrator.subset (α := β)) ∈
        {y : Filtrator.subset (α := β) | ∀ X' ∈ Filtrator.up x, δ X' y.1} := by
      exact h_univ ▸ Set.mem_univ (⊥ : Filtrator.subset (α := β))
    have hbot_rel : ∀ X' ∈ Filtrator.up x, δ X' (⊥ : Filtrator.subset (α := β)).1 := hbot_mem
    exact (hδ_bot_right X0) (hbot_rel X0.1 ⟨X0.2, hX0⟩)
  · intro a b
    constructor
    · intro hab
      rcases not_forall.mp hab.1 with ⟨Xa, hXa_not⟩
      have hXa_pair : Xa ∈ Filtrator.up x ∧ ¬ δ Xa a.1 := _root_.not_imp.mp hXa_not
      rcases hXa_pair with ⟨hXa_up, hXa_nδ⟩
      rcases not_forall.mp hab.2 with ⟨Xb, hXb_not⟩
      have hXb_pair : Xb ∈ Filtrator.up x ∧ ¬ δ Xb b.1 := _root_.not_imp.mp hXb_not
      rcases hXb_pair with ⟨hXb_up, hXb_nδ⟩
      let Xa' : Filtrator.subset (α := α) := ⟨Xa, hXa_up.1⟩
      let Xb' : Filtrator.subset (α := α) := ⟨Xb, hXb_up.1⟩
      rcases Filtrator.Primary.directed_up_in_subset (α := α) x Xa' Xb' hXa_up.2 hXb_up.2 with
        ⟨Xc, hXc_up, hXc_le_Xa, hXc_le_Xb⟩
      have hXc_le_Xa_core : @LE.le (Filtrator.subset (α := α)) Bsrc.toPartialOrder.toLE Xc Xa' := by
        have hsub : @LE.le (Filtrator.subset (α := α)) (Filtrator.suborder (α := α)).toLE Xc Xa' := hXc_le_Xa
        simpa [h_src_core_order] using hsub
      have hXc_le_Xb_core : @LE.le (Filtrator.subset (α := α)) Bsrc.toPartialOrder.toLE Xc Xb' := by
        have hsub : @LE.le (Filtrator.subset (α := α)) (Filtrator.suborder (α := α)).toLE Xc Xb' := hXc_le_Xb
        simpa [h_src_core_order] using hsub
      have hXc_nδ_a : ¬ δ Xc.1 a.1 :=
        delta_left_antitone_not_core (δ := δ) (hδ_sup_left := hδ_sup_left) hXc_le_Xa_core hXa_nδ
      have hXc_nδ_b : ¬ δ Xc.1 b.1 :=
        delta_left_antitone_not_core (δ := δ) (hδ_sup_left := hδ_sup_left) hXc_le_Xb_core hXb_nδ
      have hXc_nδ_sup : ¬ δ Xc.1 (a ⊔ b).1 := by
        intro hsup
        have h_or : δ Xc.1 a.1 ∨ δ Xc.1 b.1 :=
          (hδ_sup_right Xc a b).1 hsup
        exact h_or.elim hXc_nδ_a hXc_nδ_b
      refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
      intro h_all
      exact hXc_nδ_sup (h_all Xc.1 ⟨Xc.2, hXc_up⟩)
    · rintro ⟨z, hz_not, haz, hbz⟩
      have hna : ¬ ∀ X' ∈ Filtrator.up x, δ X' a.1 := by
        intro h_all
        apply hz_not
        intro X' hX'
        have hXa : δ ((⟨X', hX'.1⟩ : Filtrator.subset (α := α)).1) a.1 := by
          simpa using (h_all X' hX')
        have haz_core : @LE.le (Filtrator.subset (α := β)) Bdst.toPartialOrder.toLE a z := haz
        have hzrel : δ ((⟨X', hX'.1⟩ : Filtrator.subset (α := α)).1) z.1 :=
          delta_right_mono_core (δ := δ) (hδ_sup_right := hδ_sup_right)
            (K := ⟨X', hX'.1⟩) haz_core hXa
        simpa using hzrel
      have hnb : ¬ ∀ X' ∈ Filtrator.up x, δ X' b.1 := by
        intro h_all
        apply hz_not
        intro X' hX'
        have hXb : δ ((⟨X', hX'.1⟩ : Filtrator.subset (α := α)).1) b.1 := by
          simpa using (h_all X' hX')
        have hbz_core : @LE.le (Filtrator.subset (α := β)) Bdst.toPartialOrder.toLE b z := hbz
        have hzrel : δ ((⟨X', hX'.1⟩ : Filtrator.subset (α := α)).1) z.1 :=
          delta_right_mono_core (δ := δ) (hδ_sup_right := hδ_sup_right)
            (K := ⟨X', hX'.1⟩) hbz_core hXb
        simpa using hzrel
      exact ⟨hna, hnb⟩

noncomputable def relLeftCoreFreeStar
    {α : Type u} {β : Type v}
    [Filtrator.Primary α] [Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (δ : α → β → Prop)
    (hδ_bot_left : ∀ I' : Filtrator.subset (α := β), ¬ δ (⊥ : Filtrator.subset (α := α)).1 I'.1)
    (hδ_sup_right :
      ∀ K : Filtrator.subset (α := α), ∀ I' J' : Filtrator.subset (α := β),
        δ K.1 (I' ⊔ J').1 ↔ δ K.1 I'.1 ∨ δ K.1 J'.1)
    (hδ_sup_left :
      ∀ I J : Filtrator.subset (α := α), ∀ K' : Filtrator.subset (α := β),
        δ (I ⊔ J).1 K'.1 ↔ δ I.1 K'.1 ∨ δ J.1 K'.1)
    (y : β) :
    @FreeStar (Filtrator.subset (α := α)) Bsrc.toPartialOrder := by
  exact relRightCoreFreeStar
    (α := β) (β := α)
    (Bsrc := Bdst) (Bdst := Bsrc)
    (h_src_core_order := h_dst_core_order)
    (δ := fun y' x' => δ x' y')
    (hδ_bot_right := hδ_bot_left)
    (hδ_sup_left := fun I J K' => hδ_sup_right K' I J)
    (hδ_sup_right := fun K I' J' => hδ_sup_left I' J' K)
    y

lemma separable_of_primary_boolean_core
    {γ : Type u}
    [Filtrator.Primary γ]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := γ))]
    (hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := γ)) :
    IsSeparable γ := by
  have hstrong : IsStronglySeparable γ := by
    simpa [Filtrator.supset, Filtrator.suporder] using
      (primary_imp_booleanStronglySeparableCore
        (α := γ) (Bcore := Bcore) (hcoreOrder := hcoreOrder))
  exact stronglySeparable_imp_separable hstrong

noncomputable def theorem1618_rel_witness
    {α : Type u} {β : Type v}
    [X : Filtrator.Primary α] [Y : Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (h_sep_up_src : (X.toFiltrator).separator_up_property)
    (h_sep_up_dst : (Y.toFiltrator).separator_up_property)
    (δ : α → β → Prop)
    (hδ_bot_left : ∀ I' : Filtrator.subset (α := β), ¬ δ (⊥ : Filtrator.subset (α := α)).1 I'.1)
    (hδ_sup_left : ∀ I J : Filtrator.subset (α := α), ∀ K' : Filtrator.subset (α := β),
      δ (I ⊔ J).1 K'.1 ↔ δ I.1 K'.1 ∨ δ J.1 K'.1)
    (hδ_bot_right : ∀ I : Filtrator.subset (α := α), ¬ δ I.1 (⊥ : Filtrator.subset (α := β)).1)
    (hδ_sup_right : ∀ K : Filtrator.subset (α := α), ∀ I' J' : Filtrator.subset (α := β),
      δ K.1 (I' ⊔ J').1 ↔ δ K.1 I'.1 ∨ δ K.1 J'.1) :
    ∃ f : PointfreeFuncoid X.toFiltrator.suporder Y.toFiltrator.suporder,
      PointfreeFuncoid.relContinuationFromCore (δ := δ) (X := X.toFiltrator) (Y := Y.toFiltrator) f := by
  classical
  let fwdVal : α → β :=
    fun x => Classical.choose (
      exists_core_value_of_freeStar
        (β := β) (Bdst := Bdst) (h_dst_core_order := h_dst_core_order)
        (S := relRightCoreFreeStar
          (h_src_core_order := h_src_core_order)
          (δ := δ) (hδ_bot_right := hδ_bot_right)
          (hδ_sup_left := hδ_sup_left) (hδ_sup_right := hδ_sup_right)
          x))
  let bwdVal : β → α :=
    fun y => Classical.choose (
      exists_core_value_of_freeStar
        (β := α) (Bdst := Bsrc) (h_dst_core_order := h_src_core_order)
        (S := relLeftCoreFreeStar
          (h_dst_core_order := h_dst_core_order)
          (δ := δ) (hδ_bot_left := hδ_bot_left)
          (hδ_sup_right := hδ_sup_right) (hδ_sup_left := hδ_sup_left)
          y))
  let f : PointfreeFuncoid X.toFiltrator.suporder Y.toFiltrator.suporder :=
    { fwd := fwdVal
      bwd := bwdVal
      rev := by
        intro x y
        let R : Prop := ∀ X' ∈ Filtrator.up x, ∀ Y' ∈ Filtrator.up y, δ X' Y'
        have hfwd_core : ∀ x0 : α, ∀ y0 : Filtrator.subset (α := β),
            (∀ X' ∈ Filtrator.up x0, δ X' y0.1) ↔ meet (fwdVal x0) y0.1 := by
          intro x0 y0
          exact Classical.choose_spec (
            exists_core_value_of_freeStar
              (β := β) (Bdst := Bdst) (h_dst_core_order := h_dst_core_order)
              (S := relRightCoreFreeStar
                (h_src_core_order := h_src_core_order)
                (δ := δ) (hδ_bot_right := hδ_bot_right)
                (hδ_sup_left := hδ_sup_left) (hδ_sup_right := hδ_sup_right)
                x0)) y0
        have hbwd_core : ∀ y0 : β, ∀ x0 : Filtrator.subset (α := α),
            (∀ Y' ∈ Filtrator.up y0, δ x0.1 Y') ↔ meet (bwdVal y0) x0.1 := by
          intro y0 x0
          exact Classical.choose_spec (
            exists_core_value_of_freeStar
              (β := α) (Bdst := Bsrc) (h_dst_core_order := h_src_core_order)
              (S := relLeftCoreFreeStar
                (h_dst_core_order := h_dst_core_order)
                (δ := δ) (hδ_bot_left := hδ_bot_left)
                (hδ_sup_right := hδ_sup_right) (hδ_sup_left := hδ_sup_left)
                y0)) x0
        have hfwd : meet (fwdVal x) y ↔ R := by
          constructor
          · intro hmeet X' hX' Y' hY'
            have hYmeet : meet (fwdVal x) Y' := meet_mono_right hY'.2 hmeet
            exact (hfwd_core x ⟨Y', hY'.1⟩).2 hYmeet X' hX'
          · intro hR
            have hall : ∀ Y' ∈ Filtrator.up y, meet (fwdVal x) Y' := by
              intro Y' hY'
              have hcore : ∀ X' ∈ Filtrator.up x, δ X' Y' := by
                intro X' hX'
                exact hR X' hX' Y' hY'
              exact (hfwd_core x ⟨Y', hY'.1⟩).1 hcore
            exact (h_sep_up_dst (fwdVal x) y).2 hall
        have hbwd : meet (bwdVal y) x ↔ R := by
          constructor
          · intro hmeet X' hX' Y' hY'
            have hXmeet : meet (bwdVal y) X' := meet_mono_right hX'.2 hmeet
            exact (hbwd_core y ⟨X', hX'.1⟩).2 hXmeet Y' hY'
          · intro hR
            have hall : ∀ X' ∈ Filtrator.up x, meet (bwdVal y) X' := by
              intro X' hX'
              have hcore : ∀ Y' ∈ Filtrator.up y, δ X' Y' := by
                intro Y' hY'
                exact hR X' hX' Y' hY'
              exact (hbwd_core y ⟨X', hX'.1⟩).1 hcore
            exact (h_sep_up_src (bwdVal y) x).2 hall
        exact (by
          simpa [R] using (hfwd.trans hbwd.symm)) }
  refine ⟨f, ?_⟩
  intro x y
  have hfwd_core : ∀ x0 : α, ∀ y0 : Filtrator.subset (α := β),
      (∀ X' ∈ Filtrator.up x0, δ X' y0.1) ↔ meet (fwdVal x0) y0.1 := by
    intro x0 y0
    exact Classical.choose_spec (
      exists_core_value_of_freeStar
        (β := β) (Bdst := Bdst) (h_dst_core_order := h_dst_core_order)
        (S := relRightCoreFreeStar
          (h_src_core_order := h_src_core_order)
          (δ := δ) (hδ_bot_right := hδ_bot_right)
          (hδ_sup_left := hδ_sup_left) (hδ_sup_right := hδ_sup_right)
          x0)) y0
  constructor
  · intro hrel
    have hmeet : meet (fwdVal x) y := by simpa [PointfreeFuncoid.funcoid_rel, f] using hrel
    intro X' hX' Y' hY'
    have hYmeet : meet (fwdVal x) Y' := meet_mono_right hY'.2 hmeet
    exact (hfwd_core x ⟨Y', hY'.1⟩).2 hYmeet X' hX'
  · intro hR
    have hall : ∀ Y' ∈ Filtrator.up y, meet (fwdVal x) Y' := by
      intro Y' hY'
      have hcore : ∀ X' ∈ Filtrator.up x, δ X' Y' := by
        intro X' hX'
        exact hR X' hX' Y' hY'
      exact (hfwd_core x ⟨Y', hY'.1⟩).1 hcore
    have hmeet : meet (fwdVal x) y := (h_sep_up_dst (fwdVal x) y).2 hall
    simpa [PointfreeFuncoid.funcoid_rel, f] using hmeet

/--
Uniqueness half of Theorem 1618, item `\ref{pf-cont-f}`:
if two pointfree funcoids satisfy the same continuation formula for `\supfun`, they are equal.
-/
theorem theorem1618_pf_cont_f_unique
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (h_sep_src : IsSeparable α)
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (A : α → β)
    (f g : PointfreeFuncoid X.suporder Y.suporder)
    (hf : PointfreeFuncoid.fwdContinuationFromCore (Bdst := Bdst) (A := A) (X := X) (Y := Y) f)
    (hg : PointfreeFuncoid.fwdContinuationFromCore (Bdst := Bdst) (A := A) (X := X) (Y := Y) g) :
    f = g := by
  apply PointfreeFuncoid.sep_fwd f g h_sep_src
  funext x
  calc
    f.fwd x =
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {A z | z ∈ Filtrator.up x}) : β) := hf x
    _ = g.fwd x := (hg x).symm

/--
Uniqueness half of Theorem 1618, item `\ref{pf-cont-r}`:
if two pointfree funcoids satisfy the same continuation formula for `\suprel`, they are equal.
-/
theorem theorem1618_pf_cont_r_unique
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (h_sep_src : IsSeparable α)
    (h_sep_dst : IsSeparable β)
    (δ : α → β → Prop)
    (f g : PointfreeFuncoid X.suporder Y.suporder)
    (hf : PointfreeFuncoid.relContinuationFromCore (δ := δ) (X := X) (Y := Y) f)
    (hg : PointfreeFuncoid.relContinuationFromCore (δ := δ) (X := X) (Y := Y) g) :
    f = g := by
  apply PointfreeFuncoid.sep_rel f g h_sep_src h_sep_dst
  funext x y
  exact propext ((hf x y).trans (hg x y).symm)

/--
Theorem 1618 (`\label{pf-cont}`), item `\ref{pf-cont-r}` in the current development style.

Existence is constructed from the core relation assumptions (book proof path:
free stars on the core, then corresponding core filters, then a pointfree funcoid).
-/
theorem theorem1618_pf_cont_r
    {α : Type u} {β : Type v}
    [X : Filtrator.Primary α] [Y : Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : BooleanAlgebra (Filtrator.subset (α := β))]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (h_dst_core_order : Bdst.toPartialOrder = Filtrator.suborder (α := β))
    (h_sep_up_src : (X.toFiltrator).separator_up_property)
    (h_sep_up_dst : (Y.toFiltrator).separator_up_property)
    (δ : α → β → Prop)
    (hδ_bot_left : ∀ I' : Filtrator.subset (α := β), ¬ δ (⊥ : Filtrator.subset (α := α)).1 I'.1)
    (hδ_sup_left : ∀ I J : Filtrator.subset (α := α), ∀ K' : Filtrator.subset (α := β),
      δ (I ⊔ J).1 K'.1 ↔ δ I.1 K'.1 ∨ δ J.1 K'.1)
    (hδ_bot_right : ∀ I : Filtrator.subset (α := α), ¬ δ I.1 (⊥ : Filtrator.subset (α := β)).1)
    (hδ_sup_right : ∀ K : Filtrator.subset (α := α), ∀ I' J' : Filtrator.subset (α := β),
      δ K.1 (I' ⊔ J').1 ↔ δ K.1 I'.1 ∨ δ K.1 J'.1) :
    ∃! f : PointfreeFuncoid X.toFiltrator.suporder Y.toFiltrator.suporder,
      PointfreeFuncoid.relContinuationFromCore
        (δ := δ) (X := X.toFiltrator) (Y := Y.toFiltrator) f := by
  have h_sep_src : IsSeparable α :=
    separable_of_primary_boolean_core
      (γ := α) (Bcore := Bsrc) h_src_core_order
  have h_sep_dst : IsSeparable β :=
    separable_of_primary_boolean_core
      (γ := β) (Bcore := Bdst) h_dst_core_order
  rcases theorem1618_rel_witness
      (h_src_core_order := h_src_core_order)
      (h_dst_core_order := h_dst_core_order)
      (h_sep_up_src := h_sep_up_src)
      (h_sep_up_dst := h_sep_up_dst)
      (δ := δ)
      (hδ_bot_left := hδ_bot_left)
      (hδ_sup_left := hδ_sup_left)
      (hδ_bot_right := hδ_bot_right)
      (hδ_sup_right := hδ_sup_right) with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact (theorem1618_pf_cont_r_unique
    (h_sep_src := h_sep_src) (h_sep_dst := h_sep_dst) (δ := δ)
    (f := f) (g := g) hf hg).symm

/--
Theorem 1618 (`\label{pf-cont}`), item `\ref{pf-cont-f}` in the current development style.

Existence is obtained by reducing to the relation form (`\ref{pf-cont-r}`) and then using
the relation-to-function bridge.
-/
theorem theorem1618_pf_cont_f
    {α : Type u} {β : Type v}
    [X : Filtrator.Primary α] [Y : Filtrator.Primary β]
    [Bsrc : BooleanAlgebra (Filtrator.subset (α := α))]
    [Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β))]
    (h_src_core_order : Bsrc.toPartialOrder = Filtrator.suborder (α := α))
    (h_dst_core_order : Bdst.toBooleanAlgebra.toPartialOrder = Filtrator.suborder (α := β))
    (h_sep_up_src : (X.toFiltrator).separator_up_property)
    (h_sep_up_dst : (Y.toFiltrator).separator_up_property)
    (A : α → β)
    (hA_rel_bot_left : ∀ I' : Filtrator.subset (α := β), ¬ meet I'.1 (A (⊥ : Filtrator.subset (α := α)).1))
    (hA_rel_sup_left :
      ∀ I J : Filtrator.subset (α := α), ∀ K' : Filtrator.subset (α := β),
        meet K'.1 (A (I ⊔ J).1) ↔ meet K'.1 (A I.1) ∨ meet K'.1 (A J.1))
    (hA_rel_bot_right : ∀ I : Filtrator.subset (α := α), ¬ meet (⊥ : Filtrator.subset (α := β)).1 (A I.1))
    (hA_rel_sup_right :
      ∀ K : Filtrator.subset (α := α), ∀ I' J' : Filtrator.subset (α := β),
        meet (I' ⊔ J').1 (A K.1) ↔ meet I'.1 (A K.1) ∨ meet J'.1 (A K.1))
    (h_rel_to_fwd : -- FIXME: Should not be assumed.
      ∀ f : PointfreeFuncoid X.toFiltrator.suporder Y.toFiltrator.suporder,
        PointfreeFuncoid.relContinuationFromCore
          (δ := fun x y => meet y (A x))
          (X := X.toFiltrator) (Y := Y.toFiltrator) f →
        PointfreeFuncoid.fwdContinuationFromCore
          (Bdst := Bdst) (A := A) (X := X.toFiltrator) (Y := Y.toFiltrator) f) :
    ∃! f : PointfreeFuncoid X.toFiltrator.suporder Y.toFiltrator.suporder,
      PointfreeFuncoid.fwdContinuationFromCore
        (Bdst := Bdst) (A := A) (X := X.toFiltrator) (Y := Y.toFiltrator) f := by
  have h_sep_src : IsSeparable α :=
    separable_of_primary_boolean_core
      (γ := α) (Bcore := Bsrc) h_src_core_order
  rcases theorem1618_pf_cont_r
      (h_src_core_order := h_src_core_order)
      (h_dst_core_order := h_dst_core_order)
      (h_sep_up_src := h_sep_up_src)
      (h_sep_up_dst := h_sep_up_dst)
      (δ := fun x y => meet y (A x))
      (hδ_bot_left := hA_rel_bot_left)
      (hδ_sup_left := hA_rel_sup_left)
      (hδ_bot_right := hA_rel_bot_right)
      (hδ_sup_right := hA_rel_sup_right) with ⟨f, hf_rel, _⟩
  have hf_seed : PointfreeFuncoid.fwdContinuationFromCore
      (Bdst := Bdst) (A := A) (X := X.toFiltrator) (Y := Y.toFiltrator) f :=
    h_rel_to_fwd f hf_rel
  have hf : PointfreeFuncoid.fwdContinuationFromCore
      (Bdst := Bdst) (A := A) (X := X.toFiltrator) (Y := Y.toFiltrator) f :=
    by
      intro x
      let Sx : Set (Filtrator.subset (α := β)) := {A z | z ∈ Filtrator.up x}
      have h_lower :
          ∀ X' : α, X' ∈ Filtrator.up x →
            (↑(@sInf (Filtrator.subset (α := β))
              Bdst.toCompleteLattice.toInfSet Sx) : β) ≤ f.fwd X' := by
        intro X' hX'
        let SX' : Set (Filtrator.subset (α := β)) := {A z | z ∈ Filtrator.up X'}
        have hSX'_subset : SX' ⊆ Sx := by
          intro y hy
          rcases hy with ⟨z, hz, hyz⟩
          refine ⟨z, ?_, hyz⟩
          exact ⟨hz.1, le_trans hX'.2 hz.2⟩
        have hsInf_core :
            @LE.le (Filtrator.subset (α := β))
              Bdst.toBooleanAlgebra.toPartialOrder.toLE
              (@sInf (Filtrator.subset (α := β))
                Bdst.toCompleteLattice.toInfSet Sx)
              (@sInf (Filtrator.subset (α := β))
                Bdst.toCompleteLattice.toInfSet SX') := by
          exact sInf_le_sInf hSX'_subset
        have hsInf_beta :
            (↑(@sInf (Filtrator.subset (α := β))
              Bdst.toCompleteLattice.toInfSet Sx) : β) ≤
              (↑(@sInf (Filtrator.subset (α := β))
                Bdst.toCompleteLattice.toInfSet SX') : β) := by
          have hsInf_core_sub :
              @LE.le (Filtrator.subset (α := β))
                (Filtrator.suborder (α := β)).toLE
                (@sInf (Filtrator.subset (α := β))
                  Bdst.toCompleteLattice.toInfSet Sx)
                (@sInf (Filtrator.subset (α := β))
                  Bdst.toCompleteLattice.toInfSet SX') := by
            simpa [h_dst_core_order] using hsInf_core
          exact hsInf_core_sub
        have hX'fwd : f.fwd X' =
            (↑(@sInf (Filtrator.subset (α := β))
              Bdst.toCompleteLattice.toInfSet SX') : β) :=
          hf_seed X'
        calc
          (↑(@sInf (Filtrator.subset (α := β))
            Bdst.toCompleteLattice.toInfSet Sx) : β) ≤
              (↑(@sInf (Filtrator.subset (α := β))
                Bdst.toCompleteLattice.toInfSet SX') : β) := hsInf_beta
          _ = f.fwd X' := hX'fwd.symm
      have h_reverse :
          f.continuationSeparator x ⊆
            separator
              (↑(@sInf (Filtrator.subset (α := β))
                Bdst.toCompleteLattice.toInfSet Sx) : β) := by
        intro y hy
        have hy_sep_fx : y ∈ separator (f.fwd x) := by
          simpa [proposition1615_source (h_sep_up := h_sep_up_src) (f := f) (x := x)] using hy
        simpa [Sx, hf_seed x] using hy_sep_fx
      exact pointfree_funcoid_fwd_value
        (X := X.toFiltrator) (F := Y)
        (h_dst_core_order := h_dst_core_order)
        (h_src_sep_up := h_sep_up_src)
        (A := A) (f := f) (x := x)
        h_lower h_reverse
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact (theorem1618_pf_cont_f_unique
    (h_sep_src := h_sep_src) (Bdst := Bdst) (A := A)
    (f := f) (g := g) hf hg).symm
