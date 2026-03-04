import atgt.Funcoid
import atgt.Filtrator.Powerset
import atgt.Filtrator

universe u v w

def IsFuncoidLimit {α: Type u} {β: Type v} (d: Funcoid α β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  F ≤ Funcoid.fwd_set d ({x} : Set α)

def IsLimitPointOfSet {α : Type u}
    (d : Funcoid α α) (s : Set α) (x : OrderDual α) : Prop :=
  IsFuncoidLimit d (PosetFilter.principal s) (OrderDual.ofDual x)

def IsFwdContinuation1618 {α : Type u} {β : Type v}
    (A : Set α → Set β) (f : Funcoid α β) : Prop :=
  ∀ s : Set α,
    Funcoid.fwd_set f s =
      PosetFilter.principal (sInf {t : Set β | ∃ u : Set α, s ⊆ u ∧ t = A u})

def limitPointsOfSet {α : Type u}
    (d : Funcoid α α)
    (s : Set α) :=
  {y : α | IsLimitPointOfSet d s y}

theorem isLimitPointOfSet_empty
    {α : Type u}
    (d : Funcoid α α)
    (x : OrderDual α) :
    IsLimitPointOfSet d (∅ : Set α) x := by
  unfold IsLimitPointOfSet IsFuncoidLimit Funcoid.fwd_set
  intro s hs
  simp [PosetFilter.principal]

theorem limitPointsOfSet_empty_eq_univ
    {α : Type u}
    (d : Funcoid α α) :
    limitPointsOfSet d (∅ : Set α) = (Set.univ : Set (OrderDual α)) := by
  ext x
  simp [limitPointsOfSet, isLimitPointOfSet_empty]

theorem isLimitPointOfSet_union_iff
    {α : Type u}
    (d : Funcoid α α)
    (A B : Set α)
    (x : OrderDual α) :
    IsLimitPointOfSet d (A ∪ B) x ↔
      IsLimitPointOfSet d A x ∧ IsLimitPointOfSet d B x := by
  unfold IsLimitPointOfSet IsFuncoidLimit Funcoid.fwd_set
  constructor
  · intro h
    constructor
    · intro s hs  a ha
      exact h hs (Or.inl ha)
    · intro s hs b hb
      exact h hs (Or.inr hb)
  · intro h s hs z hz
    cases hz with
    | inl hzA => exact h.1 hs hzA
    | inr hzB => exact h.2 hs hzB

theorem limitPointsOfSet_union_eq_inter
    {α : Type u}
    (d : Funcoid α α)
    (A B : Set α) :
    limitPointsOfSet d (A ∪ B) =
      limitPointsOfSet d A ∩ limitPointsOfSet d B := by
  ext x
  simp [limitPointsOfSet, isLimitPointOfSet_union_iff]

/--
Proposition 10 (assumed existence/uniqueness statement in this development):
for reflexive `d`, there exists a unique OrderDual pointfree funcoid whose forward continuation
equals `limitPointsOfSet d`.

FIXME: The requirement to be reflexive seems superfluous.
-/
noncomputable def limitPointFuncoid_existsUnique_of_reflexive -- FIXME: Rename.
    {α : Type u}
    (d : Funcoid α α)
    (h : ∃! f : Funcoid α (OrderDual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f) :
    Funcoid α (OrderDual α) :=
  Classical.choose (ExistsUnique.exists h)

noncomputable def limitPointFuncoid {α : Type u}
    (d : Funcoid α α) :
    (h : ∃! f : Funcoid α (OrderDual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f) →
    Funcoid α (OrderDual α) :=
  limitPointFuncoid_existsUnique_of_reflexive d

theorem limitPointFuncoid_isContinuation
    {α : Type u}
    (d : Funcoid α α)
    (h : ∃! f : Funcoid α (OrderDual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f) :
    IsFwdContinuation1618 (limitPointsOfSet d) (limitPointFuncoid (d := d) h) :=
  Classical.choose_spec (ExistsUnique.exists h)

theorem limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (h : ∃! f : Funcoid α (OrderDual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f)
    (s : Set α) :
    Funcoid.fwd_set (limitPointFuncoid (d := d) h) s =
      PosetFilter.principal
        (sInf {t : Set (OrderDual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u}) :=
  (limitPointFuncoid_isContinuation d h) s

theorem limitPointFuncoid_fwd_set_eq_principal_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (h : ∃! f : Funcoid α (OrderDual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f)
    (s : Set α) :
    Funcoid.fwd_set (limitPointFuncoid (d := d) h) s =
      PosetFilter.principal
        (sInf {t : Set (OrderDual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u}) := by
  simpa using limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet (d := d) (h := h) (s := s)

noncomputable def limitOfFuncoid {α β: Type*} (d: Funcoid β β)
    (h : ∃! g : Funcoid β (OrderDual β), IsFwdContinuation1618 (limitPointsOfSet d) g)
    (f: Funcoid α β) :=
  ((limitPointFuncoid (d := d) h) ∘ f).image

noncomputable def limitOfRestrictedFuncoid
    {α: Type u} {β: Type v}
    (d: Funcoid β β)
    (h : ∃! g : Funcoid β (OrderDual β), IsFwdContinuation1618 (limitPointsOfSet d) g)
    (f: Funcoid α β)
    (a: Filtrator.FilterOnPowerset α) :=
  ((limitPointFuncoid (d := d) h) ∘ f).fwd a

noncomputable def restrictFuncoidViaOrderEq
    {α: Type u} {β: Type v}
    (f: Funcoid α β)
    (hsrcOrder :
      (SemilatticeInf.toPartialOrder
        (self := (inferInstance : SemilatticeInf (Filtrator.FilterOnPowerset α)))) =
      (inferInstance : PartialOrder (Filtrator.FilterOnPowerset α)))
    (a : Filtrator.FilterOnPowerset α) :
    Funcoid α β := by
  let hfTy :
      Funcoid α β =
        PointfreeFuncoid
          ((inferInstance : SemilatticeInf (Filtrator.FilterOnPowerset α)).toPartialOrder)
          (inferInstance : PartialOrder (Filtrator.FilterOnPowerset β)) := by
    simpa [Funcoid] using
      congrArg
        (fun X : PartialOrder (Filtrator.FilterOnPowerset α) =>
          PointfreeFuncoid X (inferInstance : PartialOrder (Filtrator.FilterOnPowerset β)))
        hsrcOrder.symm
  let fSemi :
      PointfreeFuncoid
        ((inferInstance : SemilatticeInf (Filtrator.FilterOnPowerset α)).toPartialOrder)
        (inferInstance : PartialOrder (Filtrator.FilterOnPowerset β)) :=
    cast hfTy f
  exact cast hfTy.symm (PointfreeFuncoid.restrict fSemi a)

lemma limitOfRestrictedFuncoid_eq
    {α: Type u} {β: Type v}
    (d: Funcoid β β)
    (h : ∃! g : Funcoid β (OrderDual β), IsFwdContinuation1618 (limitPointsOfSet d) g)
    (f: Funcoid α β)
    (hsrcOrder :
      (SemilatticeInf.toPartialOrder
        (self := (inferInstance : SemilatticeInf (Filtrator.FilterOnPowerset α)))) =
      (inferInstance : PartialOrder (Filtrator.FilterOnPowerset α)))
    (a: Filtrator.FilterOnPowerset α) :
    limitOfRestrictedFuncoid d h f a =
      limitOfFuncoid d h (restrictFuncoidViaOrderEq f hsrcOrder a) := by
  cases hsrcOrder
  simp [limitOfRestrictedFuncoid, limitOfFuncoid, restrictFuncoidViaOrderEq,
    PointfreeFuncoid.image, PointfreeFuncoid.restrict, PointfreeFuncoid.restrictedIdentity, comp]

noncomputable def IsBinaryRelationLimit {α β: Type*} (d: Funcoid β β)
    (h : ∃! g : Funcoid β (OrderDual β), IsFwdContinuation1618 (limitPointsOfSet d) g)
    (f: α → β → Prop) (a: Filtrator.FilterOnPowerset α) :=
  limitOfRestrictedFuncoid d h (principalFuncoid f) a

noncomputable def IsFunctionLimit {α β: Type*} (d: Funcoid β β)
    (h : ∃! g : Funcoid β (OrderDual β), IsFwdContinuation1618 (limitPointsOfSet d) g)
    (f: α → β) (a: Filtrator.FilterOnPowerset α) :=
  limitOfRestrictedFuncoid d h (principalFuncoidOfFunction f) a
