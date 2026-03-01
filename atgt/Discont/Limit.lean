import atgt.Funcoid
import atgt.Filtrator.Powerset
import atgt.Filtrator

universe u v w

def IsFuncoidLimit {α: Type u} {β: Type v} (d: Funcoid α β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  F ≤ Funcoid.fwd_set d ({x} : Set α)

abbrev dual (α : Type u) := OrderDual α

def IsLimitPointOfSet {α : Type u}
    (d : Funcoid α α) (s : Set α) (x : dual α) : Prop :=
  IsFuncoidLimit d (PosetFilter.principal s) (OrderDual.ofDual x)

def IsFwdContinuation1618 {α : Type u} {β : Type v}
    (A : Set α → Set β) (f : Funcoid α β) : Prop :=
  ∀ s : Set α,
    f.fwd s = sInf {t : Set β | ∃ u : Set α, s ⊆ u ∧ t = A u}

def limitPointsOfSet {α : Type u}
    (d : Funcoid α α)
    (s : Set α) :=
  {y : α | IsLimitPointOfSet d s y}

class HasLimitPointContinuation {α : Type u}
    (d : Funcoid α α) : Prop where
  existsUnique :
    ∃! f : Funcoid α (dual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f

noncomputable def limitPointFuncoid {α : Type u}
    (d : Funcoid α α)
    (_hRefl : PointfreeFuncoid.IsReflexive d)
    [hCont : HasLimitPointContinuation d] :
    Funcoid α (dual α) :=
  Classical.choose (ExistsUnique.exists hCont.existsUnique)

theorem limitPointFuncoid_isContinuation
    {α : Type u}
    (d : Funcoid α α)
    (hRefl : PointfreeFuncoid.IsReflexive d)
    [hCont : HasLimitPointContinuation d] :
    IsFwdContinuation1618 (limitPointsOfSet d) (limitPointFuncoid d hRefl) :=
  Classical.choose_spec (ExistsUnique.exists hCont.existsUnique)

theorem limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (hRefl : PointfreeFuncoid.IsReflexive d)
    [hCont : HasLimitPointContinuation d]
    (s : Set α) :
    (limitPointFuncoid d hRefl).fwd s =
      sInf {t : Set (dual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u} :=
  (limitPointFuncoid_isContinuation d hRefl) s

theorem limitPointFuncoid_fwd_set_eq_principal_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (hRefl : PointfreeFuncoid.IsReflexive d)
    [hCont : HasLimitPointContinuation d]
    (s : Set α) :
    (limitPointFuncoid d hRefl).fwd_set s =
      PosetFilter.principal
        (sInf {t : Set (dual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u}) := by
  simp [Funcoid.fwd_set, limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet]

theorem self_is_limitPoint_singleton
    {α : Type u}
    {d : Funcoid α α}
    (hRefl : PointfreeFuncoid.IsReflexive d)
    (x : α) :
    IsLimitPointOfSet d ({x} : Set α) (OrderDual.toDual x) := by
  change IsFuncoidLimit d (PosetFilter.principal ({x} : Set α)) x
  unfold IsFuncoidLimit Funcoid.fwd_set
  rw [principals_le_iff]
  have hIdLe : PointfreeFuncoid.identity (setPartialOrder α) ≤ d := hRefl
  have hx :
      (PointfreeFuncoid.identity (setPartialOrder α)).fwd ({x} : Set α) ≤
        d.fwd ({x} : Set α) :=
    hIdLe.1 ({x} : Set α)
  simpa [PointfreeFuncoid.identity] using hx

def limitOfFuncoid {α β: Type*} (d: Funcoid β β) (f: Funcoid α β)
    (hRefl : PointfreeFuncoid.IsReflexive d)
    [hCont : HasLimitPointContinuation d]
    := (f ∘ (limitPointFuncoid d hRefl)).image

-- def IsBinaryRelationLimit {α β: Type*} (d: Funcoid α β) (f: α → β → Prop) (x: β) :=
--   limitOfFuncoid d (principalFuncoid f) x

-- def IsFunctionLimit {α β: Type*} (d: Funcoid α β) (f: α → β) (x: β) :=
--   limitOfFuncoid d (principalFuncoidOfFunction f) x
