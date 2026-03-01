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
    (s : Set α) : Set (dual α) :=
  {y : dual α | IsLimitPointOfSet d s y}

noncomputable def limitPointFuncoid {α : Type u}
    (d : Funcoid α α)
    (_hRefl : PointfreeFuncoid.IsReflexive d)
    (hCont : ∃! f : Funcoid α (dual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f) :
    Funcoid α (dual α) :=
  Classical.choose (ExistsUnique.exists hCont)

theorem limitPointFuncoid_isContinuation
    {α : Type u}
    (d : Funcoid α α)
    (hRefl : PointfreeFuncoid.IsReflexive d)
    (hCont : ∃! f : Funcoid α (dual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f) :
    IsFwdContinuation1618 (limitPointsOfSet d) (limitPointFuncoid d hRefl hCont) :=
  Classical.choose_spec (ExistsUnique.exists hCont)

theorem limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (hRefl : PointfreeFuncoid.IsReflexive d)
    (hCont : ∃! f : Funcoid α (dual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f)
    (s : Set α) :
    (limitPointFuncoid d hRefl hCont).fwd s =
      sInf {t : Set (dual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u} :=
  (limitPointFuncoid_isContinuation d hRefl hCont) s

theorem limitPointFuncoid_fwd_set_eq_principal_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (hRefl : PointfreeFuncoid.IsReflexive d)
    (hCont : ∃! f : Funcoid α (dual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f)
    (s : Set α) :
    (limitPointFuncoid d hRefl hCont).fwd_set s =
      PosetFilter.principal
        (sInf {t : Set (dual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u}) := by
  simp [Funcoid.fwd_set, limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet,
    d, hRefl, hCont, s]

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

-- def IsBinaryRelationLimit {α: Type u} {β: Type v} (d: α → β → Prop) (F: Filtrator.FilterOnPowerset β) (x: α) :=
--   IsFuncoidLimit (principalFuncoid d) F x

-- def IsFunctionLimit {α: Type u} {β: Type v} (d: α → β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
--   IsFuncoidLimit (principalFuncoidOfFunction d) F x
