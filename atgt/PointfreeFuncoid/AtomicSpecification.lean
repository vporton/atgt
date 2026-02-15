import atgt.PointfreeFuncoid.Core
import atgt.AlternativePrimaryFiltrators

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

/-- `separator_up_property` holds for primary filtrators over boolean lattices.
This is a consequence of filters on a boolean lattice being determined by their
upper sets in the core: if `F` meets every principal filter in `G`, then `F` meets `G`. -/
lemma separator_up_of_primary_boolean_core
    {γ : Type u}
    [F : Filtrator.Primary γ]
    [Bcore : BooleanAlgebra (Filtrator.subset (α := γ))]
    (_hcoreOrder : Bcore.toPartialOrder = Filtrator.suborder (α := γ)) :
    F.toFiltrator.separator_up_property := by
  sorry

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
