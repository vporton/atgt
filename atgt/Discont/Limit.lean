import atgt.Funcoid
import atgt.Filtrator.Powerset
import atgt.Filtrator

universe u v w

def IsFuncoidLimit {α: Type u} {β: Type v} (d: Funcoid α β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  F ≤ Funcoid.fwd_set d ({x} : Set α)

abbrev dual (α : Type u) := OrderDual α -- TODO: superfluous

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

theorem isLimitPointOfSet_empty
    {α : Type u}
    (d : Funcoid α α)
    (x : dual α) :
    IsLimitPointOfSet d (∅ : Set α) x := by
  unfold IsLimitPointOfSet IsFuncoidLimit Funcoid.fwd_set
  rw [principals_le_iff]
  simp

theorem limitPointsOfSet_empty_eq_univ
    {α : Type u}
    (d : Funcoid α α) :
    limitPointsOfSet d (∅ : Set α) = (Set.univ : Set (dual α)) := by
  ext x
  simp [limitPointsOfSet, isLimitPointOfSet_empty]

theorem isLimitPointOfSet_union_iff
    {α : Type u}
    (d : Funcoid α α)
    (A B : Set α)
    (x : dual α) :
    IsLimitPointOfSet d (A ∪ B) x ↔
      IsLimitPointOfSet d A x ∧ IsLimitPointOfSet d B x := by
  unfold IsLimitPointOfSet IsFuncoidLimit Funcoid.fwd_set
  rw [principals_le_iff, principals_le_iff, principals_le_iff]
  simp [Set.union_subset_iff]

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
for reflexive `d`, there exists a unique dual pointfree funcoid whose forward continuation
equals `limitPointsOfSet d`.

FIXME: The requirement to be reflexive seems superfluous.
-/
axiom limitPointFuncoid_existsUnique_of_reflexive -- FIXME: Rename.
    {α : Type u}
    (d : Funcoid α α) :
    ∃! f : Funcoid α (dual α),
      IsFwdContinuation1618 (limitPointsOfSet d) f

noncomputable instance limitPointFuncoid {α : Type u}
    (d : Funcoid α α) :
    PointfreeFuncoid (setPartialOrder α) (setPartialOrder (dual α)) :=
  Classical.choose (ExistsUnique.exists (limitPointFuncoid_existsUnique_of_reflexive d))

theorem limitPointFuncoid_isContinuation
    {α : Type u}
    (d : Funcoid α α) :
    IsFwdContinuation1618 (limitPointsOfSet d) (limitPointFuncoid (d := d)) :=
  Classical.choose_spec (ExistsUnique.exists (limitPointFuncoid_existsUnique_of_reflexive d))

theorem limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (s : Set α) :
    (limitPointFuncoid (d := d)).fwd s =
      sInf {t : Set (dual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u} :=
  (limitPointFuncoid_isContinuation d) s

theorem limitPointFuncoid_fwd_set_eq_principal_sInf_limitPointsOfSet
    {α : Type u}
    (d : Funcoid α α)
    (s : Set α) :
    Funcoid.fwd_set (limitPointFuncoid (d := d)) s =
      PosetFilter.principal
        (sInf {t : Set (dual α) | ∃ u : Set α, s ⊆ u ∧ t = limitPointsOfSet d u}) := by
  simp [Funcoid.fwd_set, limitPointFuncoid_fwd_eq_sInf_limitPointsOfSet]

def limitOfFuncoid {α β: Type*} (d: Funcoid β β) (f: Funcoid α β)
    :=
  let g : Funcoid α (dual β) := (limitPointFuncoid (d := d)) ∘ f
  g.image

-- FIXME
-- def limitOfRestrictedFuncoid {α: Type u} {β: Type v} (d: Funcoid β β) (f: Funcoid α β) (a: α) :=
--   limitOfFuncoid d ((PointfreeFuncoid.restrict f) a)

-- FIXME
-- def IsBinaryRelationLimit {α β: Type*} (d: Funcoid β β) (f: α → β → Prop) (x: β) :=
--   limitOfFuncoid d (principalFuncoid f) x

-- def IsFunctionLimit {α β: Type*} (d: Funcoid β β) (f: α → β) (x: β) :=
--   limitOfFuncoid d (principalFuncoidOfFunction f) x
