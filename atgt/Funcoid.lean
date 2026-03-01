import atgt.PointfreeFuncoid
import atgt.Filtrator.Powerset
import atgt.PosetFilter

universe u v w

-- class Funcoid
--     (α: Type u) (β: Type w)
--     -- {a: PartialOrder α} {b: PartialOrder β}
--     -- [Filtrator.Powerset α] [Filtrator.Powerset β]
--   extends PointfreeFuncoid (setPartialOrder α) (setPartialOrder β)

abbrev Funcoid (α: Type u) (β: Type w) := PointfreeFuncoid (setPartialOrder α) (setPartialOrder β)

def relImage
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (A : Set α) : Set β :=
  {y : β | ∃ x ∈ A, r x y}

def relPreimage
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (B : Set β) : Set α :=
  {x : α | ∃ y ∈ B, r x y}

def relComp
    {α : Type u} {β : Type v} {γ : Type w}
    (r : α → β → Prop) (s : β → γ → Prop) : α → γ → Prop :=
  fun x z => ∃ y, r x y ∧ s y z

lemma meet_set_iff_nonempty
    {α : Type u}
    (A B : Set α) :
    meet A B ↔ (A ∩ B).Nonempty := by
  constructor
  · intro hAB
    by_contra hEmpty
    have hLeast : is_least (A ⊓ B) := by
      intro X
      have hEq : A ⊓ B = (∅ : Set α) :=
        Set.not_nonempty_iff_eq_empty.mp hEmpty
      simp [hEq]
    exact ((meet_as_inf A B).1 hAB) hLeast
  · intro hNonempty
    apply (meet_as_inf A B).2
    intro hLeast
    rcases hNonempty with ⟨x, hx⟩
    have hxEmpty : x ∈ (∅ : Set α) := hLeast ∅ hx
    simp at hxEmpty

def principalFuncoid
    {α : Type u} {β : Type v}
    (r : α → β → Prop) :
    PointfreeFuncoid (setPartialOrder α) (setPartialOrder β) where
  fwd := relImage r
  bwd := relPreimage r
  rev A B := by
    constructor
    · intro hMeet
      have hImg : (relImage r A ∩ B).Nonempty :=
        (meet_set_iff_nonempty (A := relImage r A) (B := B)).1 hMeet
      rcases hImg with ⟨y, hyImg, hyB⟩
      rcases hyImg with ⟨x, hxA, hxy⟩
      have hxPre : x ∈ relPreimage r B := ⟨y, hyB, hxy⟩
      exact (meet_set_iff_nonempty (A := relPreimage r B) (B := A)).2 ⟨x, hxPre, hxA⟩
    · intro hMeet
      have hPre : (relPreimage r B ∩ A).Nonempty :=
        (meet_set_iff_nonempty (A := relPreimage r B) (B := A)).1 hMeet
      rcases hPre with ⟨x, hxPre, hxA⟩
      rcases hxPre with ⟨y, hyB, hxy⟩
      have hyImg : y ∈ relImage r A := ⟨x, hxA, hxy⟩
      exact (meet_set_iff_nonempty (A := relImage r A) (B := B)).2 ⟨y, hyImg, hyB⟩

def principalFuncoidOfFunction
    {α : Type u} {β : Type v}
    (f : α → β) :
    PointfreeFuncoid (setPartialOrder α) (setPartialOrder β) :=
  principalFuncoid (fun x y => f x = y)

lemma principalFuncoid_fwd_singleton
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (x : α) :
    (principalFuncoid r).fwd ({x} : Set α) = relImage r ({x} : Set α) := rfl

lemma principalFuncoid_rel_singleton_singleton
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (x : α) (y : β) :
    (principalFuncoid r).funcoid_rel ({x} : Set α) ({y} : Set β) ↔ r x y := by
  constructor
  · intro h
    have hNE : (relImage r ({x} : Set α) ∩ ({y} : Set β)).Nonempty :=
      (meet_set_iff_nonempty (A := relImage r ({x} : Set α)) (B := ({y} : Set β))).1 h
    rcases hNE with ⟨y', hyImg, hySingleton⟩
    have hyEq : y' = y := by simpa using hySingleton
    rcases hyImg with ⟨x', hxSingleton, hx'y'⟩
    have hxEq : x' = x := by simpa using hxSingleton
    simpa [hxEq, hyEq] using hx'y'
  · intro hxy
    have hyImg : y ∈ relImage r ({x} : Set α) := ⟨x, by simp, hxy⟩
    exact (meet_set_iff_nonempty (A := relImage r ({x} : Set α)) (B := ({y} : Set β))).2
      ⟨y, hyImg, by simp⟩

theorem principalFuncoid_rel_iff_meet_graph_prod
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (x : Set α) (y : Set β) :
    (principalFuncoid r).funcoid_rel x y ↔
      meet ({p : α × β | r p.1 p.2}) (x ×ˢ y) := by
  constructor
  · intro h
    have hNE : (relImage r x ∩ y).Nonempty :=
      (meet_set_iff_nonempty (A := relImage r x) (B := y)).1 h
    rcases hNE with ⟨b, hbImg, hby⟩
    rcases hbImg with ⟨a, hax, hab⟩
    exact (meet_set_iff_nonempty (A := {p : α × β | r p.1 p.2}) (B := x ×ˢ y)).2
      ⟨(a, b), by simpa using hab, ⟨hax, hby⟩⟩
  · intro h
    have hNE : ({p : α × β | r p.1 p.2} ∩ (x ×ˢ y)).Nonempty :=
      (meet_set_iff_nonempty (A := {p : α × β | r p.1 p.2}) (B := x ×ˢ y)).1 h
    rcases hNE with ⟨⟨a, b⟩, hab, hxy⟩
    have hbImg : b ∈ relImage r x := ⟨a, hxy.1, by simpa using hab⟩
    exact (meet_set_iff_nonempty (A := relImage r x) (B := y)).2
      ⟨b, hbImg, hxy.2⟩

lemma principalFuncoidOfFunction_rel_singleton_singleton
    {α : Type u} {β : Type v}
    (f : α → β) (x : α) (y : β) :
    (principalFuncoidOfFunction f).funcoid_rel ({x} : Set α) ({y} : Set β) ↔ f x = y := by
  simpa [principalFuncoidOfFunction] using
    principalFuncoid_rel_singleton_singleton (r := fun a b => f a = b) x y

theorem principalFuncoid_comp
    {α : Type u} {β : Type v} {γ : Type w}
    (r : α → β → Prop) (s : β → γ → Prop) :
    principalFuncoid (relComp r s) =
      (principalFuncoid r) ∘ (principalFuncoid s) := by
  apply PointfreeFuncoid.ext
  · funext A
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x, hxA, hxz⟩
      rcases hxz with ⟨y, hxy, hyz⟩
      exact ⟨y, ⟨x, hxA, hxy⟩, hyz⟩
    · intro hz
      rcases hz with ⟨y, hyImg, hyz⟩
      rcases hyImg with ⟨x, hxA, hxy⟩
      exact ⟨x, hxA, ⟨y, hxy, hyz⟩⟩
  · funext C
    ext x
    constructor
    · intro hx
      rcases hx with ⟨z, hzC, hxz⟩
      rcases hxz with ⟨y, hxy, hyz⟩
      exact ⟨y, ⟨z, hzC, hyz⟩, hxy⟩
    · intro hx
      rcases hx with ⟨y, hyPre, hxy⟩
      rcases hyPre with ⟨z, hzC, hyz⟩
      exact ⟨z, hzC, ⟨y, hxy, hyz⟩⟩

abbrev FilterFuncoid (α : Type u) (β : Type v) :=
  PointfreeFuncoid
    (Filtrator.suporder (α := PosetFilter (setPartialOrder α)))
    (Filtrator.suporder (α := PosetFilter (setPartialOrder β)))

namespace Funcoid

def fwd_set {α β : Type*} (f : FilterFuncoid α β) (x : Set α)
    : Filtrator.FilterOnPowerset β :=
  (PointfreeFuncoid.fwd f) (PosetFilter.principal x)

def bwd_set {α β : Type*} (f : FilterFuncoid α β) (y : Set β)
    : Filtrator.FilterOnPowerset α :=
  (PointfreeFuncoid.bwd f) (PosetFilter.principal y)
end Funcoid

export Funcoid (fwd_set bwd_set)

lemma fcd_bwd_set_inv {α β : Type*} (f : FilterFuncoid α β) (x : Set α)
    : (Funcoid.fwd_set f) x = (Funcoid.bwd_set f.inv) x
  := sorry

lemma fcd_fwd_set_inv {α β : Type*} (f : FilterFuncoid α β) (y : Set β)
    : (Funcoid.bwd_set f) y = (Funcoid.fwd_set f.inv) y
  := sorry
