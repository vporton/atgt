import Mathlib.Data.Ordmap.Ordset
import Mathlib.Order.CompleteBooleanAlgebra
import atgt.Poset
import atgt.Filtrator
import atgt.Filtrator.Separable
import atgt.Filtrator.AdvancedProperties

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

theorem inv_inv_funcoid{u v}(a: PartialOrder u)(b: PartialOrder v)(f: @PointfreeFuncoid u v a b) :
    f.inv.inv = f := by simp[PointfreeFuncoid.inv]

/- FIXME: Can be converted to instance? -/
def PointfreeFuncoid.on_semilattice_inf
  {a : SemilatticeInf u} {b : SemilatticeInf v} :=
  @PointfreeFuncoid u v a.toPartialOrder b.toPartialOrder

instance PointfreeFuncoid.instLE
  {u v} (a : PartialOrder u) (b : PartialOrder v) :
  LE (@PointfreeFuncoid u v a b) :=
⟨fun f g =>
  (∀ x, f.fwd x ≤ g.fwd x) ∧ (∀ y, g.bwd y ≤ f.bwd y)⟩

/- TODO: `instLE` is a partial order. -/

/- TODO: Add `Semicategory` to MathLib and use it for `comp`. -/
-- instance PointfreeFuncoid.instSemigroup
--   {u v} (a : PartialOrder u) (b : PartialOrder v) :
--   Semicategory (PointfreeFuncoid a b) := {
--     mul: f g:
--   }

def comp {X: PartialOrder x}{Y: PartialOrder y}{Z: PartialOrder z}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z)
    : PointfreeFuncoid X Z
    := {
        fwd := g.fwd ∘ f.fwd
        bwd := f.bwd ∘ g.bwd
        rev := by
            intro x z
            -- g.rev gives: meet Y (g.fwd (f.fwd x)) z ↔ meet Y (f.fwd x) (g.bwd z)
            -- f.rev needs:  meet Y (g.bwd z) (f.fwd x)
            -- so we commute the meet
            refine
                    (g.rev (f.fwd x) z).trans ?_
            have := f.rev x (g.bwd z)
            -- commute the meet on Y
            simpa [meet_comm] using this
    }

infixr:80 " ∘ " => comp

theorem comp_assoc {X: PartialOrder u}{Y: PartialOrder v}{Z: PartialOrder w}{W: PartialOrder u2}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z) (h: PointfreeFuncoid Z W)
    : (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
    ext <;> rfl

theorem inv_comp {X: PartialOrder u}{Y: PartialOrder v}{Z: PartialOrder w}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z)
    : (f ∘ g).inv = g.inv ∘ f.inv := by
    ext <;> rfl

def PointfreeFuncoid.funcoid_rel {α: Type u}{β: Type v}{X: PartialOrder α}{Y: PartialOrder β}
    (f: PointfreeFuncoid X Y) (a : α) (b : β) :
    Prop
    := @meet β Y (f.fwd a) b

theorem PointfreeFuncoid.funcoid_rel_comm {X: PartialOrder u}{Y: PartialOrder v}
    (f: PointfreeFuncoid X Y) (a : u) (b : v) :
    f.funcoid_rel a b ↔ f.inv.funcoid_rel b a :=
    f.rev a b

theorem PointfreeFuncoid.sep_fwd {u v : Type _} [X : PartialOrder u] [Y : PartialOrder v] (f g : PointfreeFuncoid X Y) :
    IsSeparable u → f.fwd = g.fwd → f = g := by
    intro h_sep h_fwd
    apply PointfreeFuncoid.ext
    · exact h_fwd
    · funext y
      apply h_sep
      ext x
      simp [separator]
      rw [meet_comm x, meet_comm x]
      rw [← f.rev, ← g.rev]
      rw [h_fwd]

theorem PointfreeFuncoid.sep_rel {u v : Type _} [X : PartialOrder u] [Y : PartialOrder v] (f g : PointfreeFuncoid X Y) :
    IsSeparable u → IsSeparable v → f.funcoid_rel = g.funcoid_rel → f = g := by
    intro h_sep_u h_sep_v h_rel
    apply PointfreeFuncoid.sep_fwd f g h_sep_u
    funext x
    apply h_sep_v
    ext y
    simp [separator]
    rw [meet_comm y, meet_comm y]
    change f.funcoid_rel x y ↔ g.funcoid_rel x y
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
FIXME:
-/
theorem theorem1617
    {α : Type u} {β : Type v}
    [X : Filtrator α] [Y : Filtrator β]
    [SemilatticeInf α]
    [F: Filtrator.Primary β]
    (Bdst : CompleteBooleanAlgebra (Filtrator.subset (α := β)))
    (h_src_binary_meet_closed : Filtrator.binary_meet_closed (α := α))
    (h_src_sep_up : X.separator_up_property)
    (h_src_up_nonempty : ∀ x : α, Set.Nonempty (Filtrator.up x))
    (f : PointfreeFuncoid X.suporder Y.suporder)
    (x : α) :
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
  have h_sep_dst : IsSeparable β := by
    sorry
  have h_lower :
      ∀ X' : α, X' ∈ Filtrator.up x →
        (↑(@sInf (Filtrator.subset (α := β))
          Bdst.toCompleteLattice.toInfSet
          {f.fwd z | z ∈ Filtrator.up x}) : β) ≤ f.fwd X' := by
    sorry
  have h_reverse :
      f.continuationSeparator x ⊆
        separator
          (↑(@sInf (Filtrator.subset (α := β))
            Bdst.toCompleteLattice.toInfSet
            {f.fwd z | z ∈ Filtrator.up x}) : β) := by
    sorry
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
