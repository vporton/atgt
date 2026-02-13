import atgt.Filtrator.Primary
import atgt.Filtrator.Powerset
import Mathlib.Order.CompleteLattice.Basic

/-!
# More advanced properties of filters (Section 5.8)

This file adds Theorem 516 and the implication tuples Corollary 517 / Corollary 518
(from volume-1, pp. 85-86), in the current development vocabulary.
-/

universe u v

/--
Corollary-517 condition (3), rendered in the current formal vocabulary:
for every nonempty family `S`, its infimum exists and the upper set of this infimum is the
intersection of upper sets of elements of `S`.
-/
def NonemptyInfUpInter (α : Type u) [Filtrator α] : Prop :=
  ∀ S : Set α, S.Nonempty →
    ∃ d : α, IsGLB S d ∧ Filtrator.up d = {x : α | ∀ s ∈ S, x ∈ Filtrator.up s}

/--
Lemma 512 (p. 85), in the form used for filters:
if an order embedding sends some `d : α` to the infimum of `f '' S` in a complete lattice,
then `d` is the infimum of `S`.
-/
theorem lemma512 {α : Type u} {β : Type v}
    [PartialOrder α] [CompleteLattice β]
    (f : α ↪o β) (S : Set α)
    (h : ∃ d : α, IsGLB (f '' S) (f d)) :
    ∃ d : α, IsGLB S d ∧ sInf (f '' S) = f d := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, ?_, hd.sInf_eq⟩
  refine ⟨?_, ?_⟩
  · intro a ha
    exact f.le_iff_le.mp (hd.1 ⟨a, ha, rfl⟩)
  · intro z hz
    apply f.le_iff_le.mp
    apply hd.2
    intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    exact f.monotone (hz ha)

/--
Theorem 515 (p. 85), filter side in the current framework:
for every nonempty bounded-above family `S`, its infimum exists and the upper set
of this infimum is the intersection of upper sets of elements of `S`.
-/
theorem theorem515 {α : Type u}
    [Filtrator α] [SemilatticeInf α] [Filtrator.Primary α] :
    ∀ S : Set α, S.Nonempty → BddAbove S →
      ∃ d : α, IsGLB S d ∧ Filtrator.up d = {x : α | ∀ s ∈ S, x ∈ Filtrator.up s} := by
  sorry

/--
Theorem 516 (pp. 85-86), formalized in the present framework as the meet-side statement
used by Corollaries 517/518.
-/
theorem theorem516 {α : Type u}
    [Filtrator α] [SemilatticeInf α] [OrderTop α] [Filtrator.Primary α] :
    NonemptyInfUpInter α := by
  sorry

namespace PrimaryMeetTopInfimumTuple

variable {α : Type u} [Filtrator α]

/-- 1⇒2 in Corollary 517 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/-- 2⇒3 in Corollary 517 tuple. -/
theorem two_imp_three [SemilatticeInf α] [OrderTop α] [Filtrator.Primary α] : NonemptyInfUpInter α := by
  exact theorem516 (α := α)

/-- 1⇒3 in Corollary 517 tuple. -/
theorem one_imp_three [SemilatticeInf α] [OrderTop α] [Filtrator.Powerset.{u, v} α] :
    NonemptyInfUpInter α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α)

end PrimaryMeetTopInfimumTuple

export PrimaryMeetTopInfimumTuple (two_imp_three one_imp_three)

namespace PrimaryMeetTopCompleteLatticeTuple

variable {α : Type u} [Filtrator α]

/- TODO: Rename below. -/

/-- 1⇒2 in Corollary 518 tuple. -/
lemma one_imp_two [Filtrator.Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  exact Filtrator.Powerset.primary (α := α)

/-- 2⇒3 in Corollary 518 tuple. -/
noncomputable def two_imp_three [SemilatticeInf α] [OrderTop α] [Filtrator.Primary α] :
    CompleteLattice α := by
  classical
  let sInfFun : Set α → α := fun S =>
    if hS : S.Nonempty then
      Classical.choose (theorem516 (α := α) S hS)
    else
      ⊤
  letI : InfSet α := ⟨sInfFun⟩
  refine completeLatticeOfInf α ?_
  intro S
  by_cases hS : S.Nonempty
  · have hsInf :
      sInf S = Classical.choose (theorem516 (α := α) S hS) := by
      change sInfFun S = Classical.choose (theorem516 (α := α) S hS)
      simp [sInfFun, hS]
    exact hsInf ▸ (Classical.choose_spec (theorem516 (α := α) S hS)).1
  · have hSEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hSEmpty
    have hsInfEmpty : sInf (∅ : Set α) = (⊤ : α) := by
      change sInfFun (∅ : Set α) = (⊤ : α)
      simp [sInfFun]
    exact hsInfEmpty ▸ (isGLB_empty : IsGLB (∅ : Set α) (⊤ : α))

/-- 1⇒3 in Corollary 518 tuple. -/
noncomputable def one_imp_three [SemilatticeInf α] [OrderTop α] [Filtrator.Powerset.{u, v} α] :
    CompleteLattice α := by
  letI : Filtrator.Primary.{u, v} α := one_imp_two (α := α)
  exact two_imp_three (α := α)

end PrimaryMeetTopCompleteLatticeTuple

export PrimaryMeetTopCompleteLatticeTuple (two_imp_three one_imp_three)
