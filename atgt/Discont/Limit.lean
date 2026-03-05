import atgt.Funcoid
import atgt.Filtrator.Powerset
import atgt.Filtrator

universe u v w

-- There are two kinds of limits:
-- * "point limits" (with "dual funcoid" L that I don't define explicitly)
-- * "filter limits" (with arbitrary funcoid d)

namespace PointLimits

def IsFuncoidLimit {baseα baseβ : Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid α β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  F ≤ Funcoid.fwd_set d ({x} : Set α)

def IsLimitPointOfFilter {baseα : Type u} {α: Set baseα}
    (d : Funcoid α α) (s : FilterOnPowerset α) (x: α) : Prop :=
  IsFuncoidLimit d s x

def limitPointsOfFilter {baseα : Type u} {α: Set baseα}
    (d : Funcoid α α)
    (s : FilterOnPowerset α) :=
  {y : α | IsLimitPointOfFilter d s y}

end PointLimits

namespace FilterLimits

noncomputable def filt_limitOfFuncoid {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: Funcoid α β) :=
  (d ∘ f).image -- FIXME: Define it without `limitPointFuncoid`

noncomputable def filt_limitOfRestrictedFuncoid
    {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ}
    (d: Funcoid β β)
    (f: Funcoid α β)
    (a: Filtrator.FilterOnPowerset α) :=
  (d ∘ f).fwd a

-- FIXME
noncomputable def restrictFuncoidViaOrderEq
    {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ}
    (f: Funcoid α β)
    (hsrcOrder : -- FIXME: Deduce it rather than assume.
      (SemilatticeInf.toPartialOrder
        (self := (inferInstance : SemilatticeInf (FilterOnPowerset α)))) =
      (inferInstance : PartialOrder (FilterOnPowerset α)))
    (a : FilterOnPowerset α) :
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

-- FIXME
lemma filt_limitOfRestrictedFuncoid_eq
    {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ}
    (d: Funcoid β β)
    (f: Funcoid α β)
    (hsrcOrder :
      (SemilatticeInf.toPartialOrder
        (self := (inferInstance : SemilatticeInf (Filtrator.FilterOnPowerset α)))) =
      (inferInstance : PartialOrder (Filtrator.FilterOnPowerset α)))
    (a: Filtrator.FilterOnPowerset α) :
    filt_limitOfRestrictedFuncoid d f a =
      filt_limitOfFuncoid d (restrictFuncoidViaOrderEq f hsrcOrder a) := by
  cases hsrcOrder
  simp [filt_limitOfRestrictedFuncoid, filt_limitOfFuncoid, restrictFuncoidViaOrderEq,
    PointfreeFuncoid.image, PointfreeFuncoid.restrict, PointfreeFuncoid.restrictedIdentity, comp]

noncomputable def filt_IsBinaryRelationLimit {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: α → β → Prop) (a: FilterOnPowerset α) :=
  filt_limitOfRestrictedFuncoid d (principalFuncoid f) a

noncomputable def filt_IsFunctionLimit {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: α → β) (a: Filtrator.FilterOnPowerset α) :=
  filt_limitOfRestrictedFuncoid d (principalFuncoidOfFunction f) a

end FilterLimits
