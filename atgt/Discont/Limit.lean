import atgt.Funcoid
import atgt.Filtrator.Powerset
import atgt.Filtrator

universe u v w

-- There are two kinds of limits:
-- * "point limits" (with "dual funcoid" L that I don't define explicitly)
-- * "filter limits" (with arbitrary funcoid d)

namespace PointLimits

def IsLimitPointOfFilter {baseα baseβ : Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid α β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  F ≤ Funcoid.fwd_set d ({x} : Set α)

def limitPointsOfFilter {baseα : Type u} {α: Set baseα}
    (d : Funcoid α α)
    (s : FilterOnPowerset α) :=
  {y : α | IsLimitPointOfFilter d s y}

def point_limitOfFuncoid {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: Funcoid α β) :=
  limitPointsOfFilter d f.image

def point_limitOfRestrictedFuncoid
    {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ}
    (d: Funcoid β β)
    (f: Funcoid α β)
    (a: Filtrator.FilterOnPowerset α) :=
  limitPointsOfFilter d (f.fwd a)

theorem point_limitOfRestrictedFuncoid_eq {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ}
    (d: Funcoid β β) (f: Funcoid α β) (a: Filtrator.FilterOnPowerset α) :
  point_limitOfRestrictedFuncoid d f a = point_limitOfFuncoid d (PointfreeFuncoid.restrict f a) := sorry

def point_limitOfBinaryRelation {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: α → β → Prop) (a: FilterOnPowerset α) :=
  point_limitOfRestrictedFuncoid d (principalFuncoid f) a

def point_limitOfFunction {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: α → β) (a: Filtrator.FilterOnPowerset α) :=
  point_limitOfRestrictedFuncoid d (principalFuncoidOfFunction f) a

end PointLimits

namespace FilterLimits

def filt_limitOfFuncoid {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: Funcoid α β) :=
  (d ∘ f).image

def filt_limitOfRestrictedFuncoid
    {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ}
    (d: Funcoid β β)
    (f: Funcoid α β)
    (a: Filtrator.FilterOnPowerset α) :=
  (d ∘ f).fwd a

theorem filt_limitOfRestrictedFuncoid_eq {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ}
    (d: Funcoid β β) (f: Funcoid α β) (a: Filtrator.FilterOnPowerset α) :
  filt_limitOfRestrictedFuncoid d f a = filt_limitOfFuncoid d (PointfreeFuncoid.restrict f a) := sorry

def filt_limitOfBinaryRelation {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: α → β → Prop) (a: FilterOnPowerset α) :=
  filt_limitOfRestrictedFuncoid d (principalFuncoid f) a

def filt_limitOfFunction {baseα baseβ: Type*} {α: Set baseα} {β: Set baseβ} (d: Funcoid β β)
    (f: α → β) (a: Filtrator.FilterOnPowerset α) :=
  filt_limitOfRestrictedFuncoid d (principalFuncoidOfFunction f) a

end FilterLimits
