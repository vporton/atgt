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
  (∀ x, f.fwd x ≤ g.fwd x) ∧ (∀ y, g.bwd y ≤ f.bwd y)⟩

/- TODO: `instLE` is a partial order. -/

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
Forward bridge toward Theorem 1617 for the explicit `sInf` candidate, assuming the expected
lower-bound property in the ambient order.
-/
theorem separator_sInf_image_subset_continuationSeparator
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α) :
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {f.fwd z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X') →
    separator
      (↑(@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {f.fwd z | z ∈ Filtrator.up x}) : β) ⊆
      f.continuationSeparator x := by
  intro h_lower
  exact separator_subset_continuationSeparator_of_lower_bound
    (f := f) (x := x)
    (z := (↑(@sInf (Filtrator.subset (α := β))
      Bdst.toCompleteLattice.toInfSet
      {f.fwd z | z ∈ Filtrator.up x}) : β))
    h_lower

/--
Second bridge in equality form once the reverse inclusion is provided.
The reverse direction is the generalized-filter-base step from the book proof.
-/
theorem separator_sInf_image_eq_continuationSeparator_of_reverse
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α)
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {f.fwd z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X')
    (h_reverse :
      f.continuationSeparator x ⊆
        separator
          (↑(@sInf (Filtrator.subset (α := β))
            Bdst.toCompleteLattice.toInfSet
            {f.fwd z | z ∈ Filtrator.up x}) : β)) :
    separator
      (↑(@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {f.fwd z | z ∈ Filtrator.up x}) : β) =
      f.continuationSeparator x := by
  exact Set.Subset.antisymm
    (separator_sInf_image_subset_continuationSeparator
      (Bdst := Bdst) (f := f) (x := x) h_lower)
    h_reverse

/--
Theorem 1617 reduced to the separator bridge obligations:
if the destination side provides separability and both separator inclusions for the `sInf`
candidate, then the target value equation follows.
-/
theorem theorem1617_of_separator_bridge
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    [SemilatticeInf α]
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (h_src_sep_up : X.separator_up_property)
    (h_sep_dst : IsSeparable β)
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α)
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {f.fwd z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X')
    (h_reverse :
      f.continuationSeparator x ⊆
        separator
          (↑(@sInf (Filtrator.subset (α := β))
            Bdst.toCompleteLattice.toInfSet
            {f.fwd z | z ∈ Filtrator.up x}) : β)) :
    f.fwd x =
      (↑(@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {f.fwd z | z ∈ Filtrator.up x}) : β) := by
  have hsep :
      separator
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {f.fwd z | z ∈ Filtrator.up x}) : β) =
      f.continuationSeparator x :=
    separator_sInf_image_eq_continuationSeparator_of_reverse
      (Bdst := Bdst) (f := f) (x := x) h_lower h_reverse
  have hsInf_eq_fx :
      (↑(@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {f.fwd z | z ∈ Filtrator.up x}) : β) = f.fwd x :=
    continuation_value_of_separator
      (h_sep_up := h_src_sep_up) (h_sep_dst := h_sep_dst) (f := f) (x := x)
      (z := (↑(@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {f.fwd z | z ∈ Filtrator.up x}) : β))
      hsep
  exact hsInf_eq_fx.symm

/--
Theorem 1617 (p. 317), literal value equation form:
`⟨f⟩ x = sInf (⟨⟨f⟩⟩ (up x))`.
-/
theorem pointfree_funcoid_fwd_value
    {α : Type u} {β : Type v}
    [X : Filtrator α]
    [SemilatticeInf α]
    [F: Filtrator.Primary β]
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (h_dst_core_order :
      Bdst.toBooleanAlgebra.toPartialOrder = Filtrator.suborder (α := β))
    (h_src_binary_meet_closed : Filtrator.binary_meet_closed (α := α))
    (h_src_sep_up : X.separator_up_property)
    (h_src_up_nonempty : ∀ x : α, Set.Nonempty (Filtrator.up x))
    (f : PointfreeFuncoid X.suporder (Filtrator.suporder (α := β)))
    (x : α)
    (h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {f.fwd z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X')
    (h_reverse :
      f.continuationSeparator x ⊆
        separator
          (↑(@sInf (Filtrator.subset (α := β))
            Bdst.toCompleteLattice.toInfSet
            {f.fwd z | z ∈ Filtrator.up x}) : β)) :
    f.fwd x =
      (@sInf (Filtrator.subset (α := β))
        Bdst.toCompleteLattice.toInfSet
        {f.fwd z | z ∈ Filtrator.up x}) := by
  have _ := h_src_binary_meet_closed
  have _ := h_src_up_nonempty
  have h_src_sep_up' := h_src_sep_up
  -- The proof path is established in helpers above (Proposition 1615 separator form and
  -- separator-based value recovery). The remaining bridge is to identify the separator of
  -- `sInf (f.fwd '' Filtrator.up x)` with `continuationSeparator`, via generalized-filter-base
  -- machinery (Theorem 572 / Proposition 579 route from the PDF proof).
  -- Once those two bridge inclusions and destination separability are supplied, use
  -- `theorem1617_of_separator_bridge`.
  letI : CompleteBooleanAlgebra (Filtrator.subset (α := β)) := Bdst
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
          {f.fwd z | z ∈ Filtrator.up x}) : β) :=
    theorem1617_of_separator_bridge
      (Bdst := Bdst)
      (h_src_sep_up := h_src_sep_up')
      (h_sep_dst := h_sep_dst)
      (f := f) (x := x) h_lower h_reverse
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
Theorem 1618 (`\label{pf-cont}`), item `\ref{pf-cont-f}` in the current development style.

Existence is represented as an input hypothesis, and the theorem upgrades it to `∃!`.
-/
theorem theorem1618_pf_cont_f
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β]
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (A : α → β)
    (hA_bot : A ⊥ = ⊥)
    (hA_sup : ∀ I J : α, A (I ⊔ J) = A I ⊔ A J)
    (h_sep_src : IsSeparable α) :
    (∃ f : PointfreeFuncoid X.suporder Y.suporder,
      PointfreeFuncoid.fwdContinuationFromCore
        (Bdst := Bdst) (A := A) (X := X) (Y := Y) f) →
    ∃! f : PointfreeFuncoid X.suporder Y.suporder,
      PointfreeFuncoid.fwdContinuationFromCore
        (Bdst := Bdst) (A := A) (X := X) (Y := Y) f := by
  have _ := hA_bot
  have _ := hA_sup
  intro h_exists
  rcases h_exists with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact (theorem1618_pf_cont_f_unique
    (h_sep_src := h_sep_src) (Bdst := Bdst) (A := A)
    (f := f) (g := g) hf hg).symm

/--
Theorem 1618 (`\label{pf-cont}`), item `\ref{pf-cont-r}` in the current development style.

Existence is represented as an input hypothesis, and the theorem upgrades it to `∃!`.
-/
theorem theorem1618_pf_cont_r
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β]
    (δ : α → β → Prop)
    (hδ_bot_left : ∀ I' : β, ¬ δ ⊥ I')
    (hδ_sup_left : ∀ I J : α, ∀ K' : β, δ (I ⊔ J) K' ↔ δ I K' ∨ δ J K')
    (hδ_bot_right : ∀ I : α, ¬ δ I ⊥)
    (hδ_sup_right : ∀ K : α, ∀ I' J' : β, δ K (I' ⊔ J') ↔ δ K I' ∨ δ K J')
    (h_sep_src : IsSeparable α)
    (h_sep_dst : IsSeparable β) :
    (∃ f : PointfreeFuncoid X.suporder Y.suporder,
      PointfreeFuncoid.relContinuationFromCore
        (δ := δ) (X := X) (Y := Y) f) →
    ∃! f : PointfreeFuncoid X.suporder Y.suporder,
      PointfreeFuncoid.relContinuationFromCore
        (δ := δ) (X := X) (Y := Y) f := by
  have _ := hδ_bot_left
  have _ := hδ_sup_left
  have _ := hδ_bot_right
  have _ := hδ_sup_right
  intro h_exists
  rcases h_exists with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact (theorem1618_pf_cont_r_unique
    (h_sep_src := h_sep_src) (h_sep_dst := h_sep_dst) (δ := δ)
    (f := f) (g := g) hf hg).symm

/-!
Section 20.5 (Domain and range of a pointfree funcoid), items 1635--1648.
-/

def PointfreeFuncoid.identity {α : Type u}
    (X : PartialOrder α) : PointfreeFuncoid X X where
  fwd := id
  bwd := id
  rev x y := by
    simpa using (meet_comm x y)

def PointfreeFuncoid.restrictedIdentity {α : Type u}
    {X : SemilatticeInf α} (a : α) :
    PointfreeFuncoid X.toPartialOrder X.toPartialOrder where
  fwd x := a ⊓ x
  bwd y := a ⊓ y
  rev x y := by
    constructor <;> intro h
    · have h' : ¬ is_least ((a ⊓ x) ⊓ y) := (meet_as_inf (a ⊓ x) y).1 h
      exact (meet_as_inf (a ⊓ y) x).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')
    · have h' : ¬ is_least ((a ⊓ y) ⊓ x) := (meet_as_inf (a ⊓ y) x).1 h
      exact (meet_as_inf (a ⊓ x) y).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')

theorem restrictedIdentity_rev {α : Type u}
    {X : SemilatticeInf α} (a x y : α) :
    meet ((PointfreeFuncoid.restrictedIdentity (X := X) a).fwd x) y ↔
      meet ((PointfreeFuncoid.restrictedIdentity (X := X) a).bwd y) x :=
  (PointfreeFuncoid.restrictedIdentity (X := X) a).rev x y

theorem restrictedIdentity_inv {α : Type u}
    {X : SemilatticeInf α} (a : α) :
    (PointfreeFuncoid.restrictedIdentity (X := X) a).inv =
      (PointfreeFuncoid.restrictedIdentity (X := X) a) := by
  ext <;> rfl

theorem funcoid_rel_restrictedIdentity {α : Type u}
    {X : SemilatticeInf α} (a x y : α) :
    (PointfreeFuncoid.restrictedIdentity (X := X) a).funcoid_rel x y ↔
      meet a (x ⊓ y) := by
  change meet (a ⊓ x) y ↔ meet a (x ⊓ y)
  constructor <;> intro h
  · have h' : ¬ is_least ((a ⊓ x) ⊓ y) := (meet_as_inf (a ⊓ x) y).1 h
    exact (meet_as_inf a (x ⊓ y)).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')
  · have h' : ¬ is_least (a ⊓ (x ⊓ y)) := (meet_as_inf a (x ⊓ y)).1 h
    exact (meet_as_inf (a ⊓ x) y).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')

def PointfreeFuncoid.restrict {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : PartialOrder β}
    (f : PointfreeFuncoid X.toPartialOrder Y) (a : α) :
    PointfreeFuncoid X.toPartialOrder Y :=
  (PointfreeFuncoid.restrictedIdentity (X := X) a) ∘ f

def PointfreeFuncoid.image {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α] (f : PointfreeFuncoid X Y) : β :=
  f.fwd ⊤

def PointfreeFuncoid.domain {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop β] (f : PointfreeFuncoid X Y) : α :=
  f.inv.image

@[simp] theorem PointfreeFuncoid.image_eq_fwd_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α] (f : PointfreeFuncoid X Y) :
    f.image = f.fwd ⊤ := rfl

@[simp] theorem PointfreeFuncoid.domain_eq_bwd_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop β] (f : PointfreeFuncoid X Y) :
    f.domain = f.bwd ⊤ := rfl

lemma meet_iff_not_is_least_of_le_right {α : Type u}
    [PartialOrder α] {a b : α} (h : a ≤ b) :
    meet a b ↔ ¬ is_least a := by
  constructor
  · intro hmeet hleast
    rcases hmeet with ⟨c, hca, _, hnotleast⟩
    apply hnotleast
    intro x
    exact le_trans hca (hleast x)
  · intro hnotleast
    exact ⟨a, le_rfl, h, hnotleast⟩

theorem PointfreeFuncoid.fwd_monotone_of_stronglySeparable
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    (f : PointfreeFuncoid X Y)
    (h_dst_strong : IsStronglySeparable β) :
    Monotone f.fwd := by
  intro x z hxz
  apply h_dst_strong
  intro y hy
  have hxy : meet (f.fwd x) y := (meet_comm y (f.fwd x)).1 hy
  have hbwdx : meet (f.bwd y) x := (f.rev x y).1 hxy
  have hbwdz : meet (f.bwd y) z := meet_mono_right hxz hbwdx
  have hzy : meet (f.fwd z) y := (f.rev z y).2 hbwdz
  exact (meet_comm y (f.fwd z)).2 hzy

theorem PointfreeFuncoid.bwd_monotone_of_stronglySeparable
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    (f : PointfreeFuncoid X Y)
    (h_src_strong : IsStronglySeparable α) :
    Monotone f.bwd := by
  simpa [PointfreeFuncoid.inv] using
    (PointfreeFuncoid.fwd_monotone_of_stronglySeparable (f := f.inv) h_src_strong)

theorem image_ge_fwd {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α]
    (h_dst_strong : IsStronglySeparable β)
    (f : PointfreeFuncoid X Y) (x : α) :
    f.image ≥ f.fwd x := by
  exact (PointfreeFuncoid.fwd_monotone_of_stronglySeparable (f := f) h_dst_strong) (le_top : x ≤ ⊤)

theorem fwd_domain_eq_image
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α] [OrderTop β]
    (h_src_strong : IsStronglySeparable α)
    (h_dst_sep : IsSeparable β)
    (f : PointfreeFuncoid X Y) :
    f.fwd (f.domain) = f.image := by
  have hmono_bwd : Monotone f.bwd :=
    PointfreeFuncoid.bwd_monotone_of_stronglySeparable (f := f) h_src_strong
  apply h_dst_sep
  ext y
  constructor
  · intro hy
    have hy' : meet (f.fwd (f.domain)) y := (meet_comm y (f.fwd (f.domain))).1 hy
    have hbwd_dom : meet (f.bwd y) (f.domain) := (f.rev (f.domain) y).1 hy'
    have hy_le_dom : f.bwd y ≤ f.domain := by
      simpa [PointfreeFuncoid.domain] using hmono_bwd (le_top : y ≤ (⊤ : β))
    have h_notleast : ¬ is_least (f.bwd y) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := f.domain) hy_le_dom).1 hbwd_dom
    have hbwd_top : meet (f.bwd y) (⊤ : α) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := (⊤ : α)) le_top).2 h_notleast
    have himage' : meet (f.fwd (⊤ : α)) y := (f.rev (⊤ : α) y).2 hbwd_top
    exact (meet_comm y (f.fwd (⊤ : α))).2 (by simpa [PointfreeFuncoid.image] using himage')
  · intro hy
    have hy' : meet (f.fwd (⊤ : α)) y := by
      simpa [PointfreeFuncoid.image] using (meet_comm y (f.fwd (⊤ : α))).1 hy
    have hbwd_top : meet (f.bwd y) (⊤ : α) := (f.rev (⊤ : α) y).1 hy'
    have hy_le_dom : f.bwd y ≤ f.domain := by
      simpa [PointfreeFuncoid.domain] using hmono_bwd (le_top : y ≤ (⊤ : β))
    have h_notleast : ¬ is_least (f.bwd y) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := (⊤ : α)) le_top).1 hbwd_top
    have hbwd_dom : meet (f.bwd y) (f.domain) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := f.domain) hy_le_dom).2 h_notleast
    have hdom' : meet (f.fwd (f.domain)) y := (f.rev (f.domain) y).2 hbwd_dom
    exact (meet_comm y (f.fwd (f.domain))).2 hdom'

theorem fwd_eq_fwd_inf_domain
    {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : PartialOrder β}
    [OrderTop β]
    (h_src_sep : IsSeparable α)
    (h_dst_sep : IsSeparable β)
    (f : PointfreeFuncoid X.toPartialOrder Y) (x : α) :
    f.fwd x = f.fwd (x ⊓ f.domain) := by
  have h_src_strong : IsStronglySeparable α :=
    separable_imp_stronglySeparable h_src_sep
  have hmono_bwd : Monotone f.bwd :=
    PointfreeFuncoid.bwd_monotone_of_stronglySeparable (f := f) h_src_strong
  apply h_dst_sep
  ext y
  constructor
  · intro hy
    have hy' : meet (f.fwd x) y := (meet_comm y (f.fwd x)).1 hy
    have hbwd_x : meet (f.bwd y) x := (f.rev x y).1 hy'
    have hy_le_dom : f.bwd y ≤ f.domain := by
      simpa [PointfreeFuncoid.domain] using hmono_bwd (le_top : y ≤ (⊤ : β))
    rcases hbwd_x with ⟨c, hcy, hcx, hnotleast⟩
    have hcd : c ≤ f.domain := le_trans hcy hy_le_dom
    have hbwd_xd : meet (f.bwd y) (x ⊓ f.domain) :=
      ⟨c, hcy, le_inf hcx hcd, hnotleast⟩
    have hxy' : meet (f.fwd (x ⊓ f.domain)) y := (f.rev (x ⊓ f.domain) y).2 hbwd_xd
    exact (meet_comm y (f.fwd (x ⊓ f.domain))).2 hxy'
  · intro hy
    have hy' : meet (f.fwd (x ⊓ f.domain)) y := (meet_comm y (f.fwd (x ⊓ f.domain))).1 hy
    have hbwd_xd : meet (f.bwd y) (x ⊓ f.domain) := (f.rev (x ⊓ f.domain) y).1 hy'
    have hbwd_x : meet (f.bwd y) x := meet_mono_right inf_le_left hbwd_xd
    have hxy' : meet (f.fwd x) y := (f.rev x y).2 hbwd_x
    exact (meet_comm y (f.fwd x)).2 hxy'

theorem meet_domain_iff_fwd_not_least
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop β]
    (f : PointfreeFuncoid X Y) (x : α) :
    meet x (f.domain) ↔ ¬ is_least (f.fwd x) := by
  constructor
  · intro hx
    have hdomx : meet (f.bwd (⊤ : β)) x := by
      simpa [PointfreeFuncoid.domain] using (meet_comm x (f.bwd (⊤ : β))).1 hx
    have htop : meet (f.fwd x) (⊤ : β) := (f.rev x (⊤ : β)).2 hdomx
    exact (meet_iff_not_is_least_of_le_right (a := f.fwd x) (b := (⊤ : β)) le_top).1 htop
  · intro hnotleast
    have htop : meet (f.fwd x) (⊤ : β) :=
      (meet_iff_not_is_least_of_le_right (a := f.fwd x) (b := (⊤ : β)) le_top).2 hnotleast
    have hdomx : meet (f.bwd (⊤ : β)) x := (f.rev x (⊤ : β)).1 htop
    exact (meet_comm x (f.bwd (⊤ : β))).2 (by simpa [PointfreeFuncoid.domain] using hdomx)

def IsSeparatorAtomistic (α : Type u) [CompleteLattice α] : Prop :=
  ∀ x : α, x = sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a x}

theorem domain_eq_sSup_atoms_fwd_ne_bot
    {α : Type u} {β : Type v}
    {Y : PartialOrder β}
    [CompleteLattice α] [OrderTop β] [OrderBot β]
    (h_atomistic : IsSeparatorAtomistic α)
    (f : PointfreeFuncoid (inferInstance : PartialOrder α) Y) :
    f.domain =
      sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ f.fwd a ≠ (⊥ : β)} := by
  have hdom :
      f.domain =
        sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a f.domain} :=
    h_atomistic f.domain
  have hset :
      {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a f.domain} =
      {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ f.fwd a ≠ (⊥ : β)} := by
    ext a
    constructor
    · intro ha
      refine ⟨ha.1, ?_⟩
      have h_notleast : ¬ is_least (f.fwd a) :=
        (meet_domain_iff_fwd_not_least (f := f) (x := a)).1 ha.2
      intro hbot
      apply h_notleast
      intro z
      exact hbot ▸ bot_le
    · intro ha
      refine ⟨ha.1, ?_⟩
      have h_notleast : ¬ is_least (f.fwd a) := by
        intro hleast
        exact ha.2 (le_antisymm (hleast ⊥) bot_le)
      exact (meet_domain_iff_fwd_not_least (f := f) (x := a)).2 h_notleast
  have hsSup :
      sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a f.domain} =
        sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ f.fwd a ≠ (⊥ : β)} :=
    congrArg sSup hset
  exact hdom.trans hsSup

theorem domain_restrict
    {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : PartialOrder β}
    [OrderTop β]
    (f : PointfreeFuncoid X.toPartialOrder Y) (a : α) :
    (f.restrict a).domain = a ⊓ f.domain := by
  rfl
