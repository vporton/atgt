import atgt.PointfreeFuncoid
import atgt.Filtrator.Powerset
import atgt.PosetFilter

universe u v w t

-- TODO: This seems unneeded, because I can deal without introducing dual funcoid L.
-- def Funcoid.Primary
--     {baseα : Type u} (α: Set baseα) {baseβ : Type v} (β: Set baseβ)
--     [X: Filtrator.FiltratorOnPowerset.Primary (U := α)] [Y: Filtrator.FiltratorOnPowerset.Primary (U := β)] :=
--   PointfreeFuncoid X.suporder Y.suporder

-- -- FIXME: Should have principals, not sets, as cores.
-- /-- A (non-pointfree) funcoid is pointfree on filters over powersets. -/
-- def Funcoid
--     {baseα : Type u} (α: Set baseα) {baseβ : Type v} (β: Set baseβ) :=
--   Funcoid.Primary
--     (X := Filtrator.FiltratorOnPowerset (U := α))
--     (Y := Filtrator.FiltratorOnPowerset (U := β))
--     α β

def Funcoid
    {baseα : Type u} (α: Set baseα) {baseβ : Type v} (β: Set baseβ) :=
  PointfreeFuncoid
    (inferInstance: PartialOrder (Filtrator.FilterOnPowerset α))
    (inferInstance: PartialOrder (Filtrator.FilterOnPowerset β))

def relImage
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (A : Set α) : Set β :=
  {y : β | ∃ x ∈ A, r x y}

def relPreimage
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (B : Set β) : Set α :=
  {x : α | ∃ y ∈ B, r x y}

-- FIXME: Exchange arguments.
def relComp
    {α : Type u} {β : Type v} {γ : Type w}
    (r : α → β → Prop) (s : β → γ → Prop) : α → γ → Prop :=
  fun x z => ∃ y, r x y ∧ s y z

lemma relImage_mono
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    {A A' : Set α}
    (hAA' : A ⊆ A') :
    relImage r A ⊆ relImage r A' := by
  intro y hy
  rcases hy with ⟨x, hxA, hxy⟩
  exact ⟨x, hAA' hxA, hxy⟩

lemma relPreimage_mono
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    {B B' : Set β}
    (hBB' : B ⊆ B') :
    relPreimage r B ⊆ relPreimage r B' := by
  intro x hx
  rcases hx with ⟨y, hyB, hxy⟩
  exact ⟨y, hBB' hyB, hxy⟩

lemma relImage_relComp
    {α : Type u} {β : Type v} {γ : Type w}
    (r : α → β → Prop) (s : β → γ → Prop) (A : Set α) :
    relImage (relComp r s) A = relImage s (relImage r A) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, hxA, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hxA, hxy⟩, hyz⟩
  · intro hz
    rcases hz with ⟨y, hyImg, hyz⟩
    rcases hyImg with ⟨x, hxA, hxy⟩
    exact ⟨x, hxA, y, hxy, hyz⟩

lemma relPreimage_relComp
    {α : Type u} {β : Type v} {γ : Type w}
    (r : α → β → Prop) (s : β → γ → Prop) (C : Set γ) :
    relPreimage (relComp r s) C = relPreimage r (relPreimage s C) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨z, hzC, y, hxy, hyz⟩
    exact ⟨y, ⟨z, hzC, hyz⟩, hxy⟩
  · intro hx
    rcases hx with ⟨y, hyPre, hxy⟩
    rcases hyPre with ⟨z, hzC, hyz⟩
    exact ⟨z, hzC, y, hxy, hyz⟩

lemma relImage_inter_nonempty_iff_preimage_inter_nonempty
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (A : Set α) (B : Set β) :
    (relImage r A ∩ B).Nonempty ↔ (A ∩ relPreimage r B).Nonempty := by
  constructor
  · rintro ⟨y, hyImg, hyB⟩
    rcases hyImg with ⟨x, hxA, hxy⟩
    exact ⟨x, hxA, ⟨y, hyB, hxy⟩⟩
  · rintro ⟨x, hxA, y, hyB, hxy⟩
    exact ⟨y, ⟨x, hxA, hxy⟩, hyB⟩

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

namespace Funcoid

def fwd_set {baseα baseβ : Type*} {α: Set baseα} {β: Set baseβ} (f : Funcoid α β) (x : Set α)
    : Filtrator.FilterOnPowerset β :=
  (PointfreeFuncoid.fwd f) (PosetFilter.principal x)

def bwd_set {α β : Type*} (f : Funcoid α β) (y : Set β)
    : Filtrator.FilterOnPowerset α :=
  (PointfreeFuncoid.bwd f) (PosetFilter.principal y)
end Funcoid

export Funcoid (fwd_set bwd_set)

lemma fcd_bwd_set_inv {α β : Type*} (f : Funcoid α β) (x : Set α)
    : (Funcoid.fwd_set f) x = (Funcoid.bwd_set f.inv) x
  := rfl

lemma fcd_fwd_set_inv {α β : Type*} (f : Funcoid α β) (y : Set β)
    : (Funcoid.bwd_set f) y = (Funcoid.fwd_set f.inv) y
  := rfl

def Funcoid.funcoid_rel_set (f: Funcoid α β) (a: Set α) (b: Set β) :=
  PointfreeFuncoid.funcoid_rel f (PosetFilter.principal a) (PosetFilter.principal b)

def relImageFilterBase
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (F : Filtrator.FilterOnPowerset α) :
    PosetFilterBase (setPartialOrder β) where
  elements := {Y : Set β | ∃ X ∈ F.elements, Y = relImage r X}
  non_empty := by
    rcases F.non_empty with ⟨X, hX⟩
    exact ⟨relImage r X, ⟨X, hX, rfl⟩⟩
  cap_elements := by
    intro Y1 Y2 hY1 hY2
    rcases hY1 with ⟨X1, hX1, rfl⟩
    rcases hY2 with ⟨X2, hX2, rfl⟩
    rcases F.cap_elements hX1 hX2 with ⟨X3, hX3, hX3X1, hX3X2⟩
    refine ⟨relImage r X3, ⟨X3, hX3, rfl⟩, ?_, ?_⟩
    · exact relImage_mono r hX3X1
    · exact relImage_mono r hX3X2

def relPreimageFilterBase
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (G : Filtrator.FilterOnPowerset β) :
    PosetFilterBase (setPartialOrder α) where
  elements := {X : Set α | ∃ Y ∈ G.elements, X = relPreimage r Y}
  non_empty := by
    rcases G.non_empty with ⟨Y, hY⟩
    exact ⟨relPreimage r Y, ⟨Y, hY, rfl⟩⟩
  cap_elements := by
    intro X1 X2 hX1 hX2
    rcases hX1 with ⟨Y1, hY1, rfl⟩
    rcases hX2 with ⟨Y2, hY2, rfl⟩
    rcases G.cap_elements hY1 hY2 with ⟨Y3, hY3, hY3Y1, hY3Y2⟩
    refine ⟨relPreimage r Y3, ⟨Y3, hY3, rfl⟩, ?_, ?_⟩
    · exact relPreimage_mono r hY3Y1
    · exact relPreimage_mono r hY3Y2

def relImageFilter
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (F : Filtrator.FilterOnPowerset α) :
    Filtrator.FilterOnPowerset β :=
  close_filter_base (relImageFilterBase r F)

def relPreimageFilter
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (G : Filtrator.FilterOnPowerset β) :
    Filtrator.FilterOnPowerset α :=
  close_filter_base (relPreimageFilterBase r G)

lemma mem_relImageFilter_iff
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (F : Filtrator.FilterOnPowerset α)
    (Y : Set β) :
    Y ∈ (relImageFilter r F).elements ↔
      ∃ X ∈ F.elements, relImage r X ⊆ Y := by
  constructor
  · intro hY
    change Y ∈ (close_filter_base (relImageFilterBase r F)).elements at hY
    rcases hY with ⟨Z, hZ, hZY⟩
    rcases hZ with ⟨X, hX, rfl⟩
    exact ⟨X, hX, hZY⟩
  · rintro ⟨X, hX, hXY⟩
    change Y ∈ (close_filter_base (relImageFilterBase r F)).elements
    exact ⟨relImage r X, ⟨X, hX, rfl⟩, hXY⟩

lemma mem_relPreimageFilter_iff
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (G : Filtrator.FilterOnPowerset β)
    (X : Set α) :
    X ∈ (relPreimageFilter r G).elements ↔
      ∃ Y ∈ G.elements, relPreimage r Y ⊆ X := by
  constructor
  · intro hX
    change X ∈ (close_filter_base (relPreimageFilterBase r G)).elements at hX
    rcases hX with ⟨W, hW, hWX⟩
    rcases hW with ⟨Y, hY, rfl⟩
    exact ⟨Y, hY, hWX⟩
  · rintro ⟨Y, hY, hYX⟩
    change X ∈ (close_filter_base (relPreimageFilterBase r G)).elements
    exact ⟨relPreimage r Y, ⟨Y, hY, rfl⟩, hYX⟩

lemma meet_filter_iff_pairwise_inter_nonempty
    {α : Type u}
    (F G : Filtrator.FilterOnPowerset α) :
    meet F G ↔ ∀ A ∈ F.elements, ∀ B ∈ G.elements, (A ∩ B).Nonempty := by
  constructor
  · rintro ⟨H, hHF, hHG, hHnotleast⟩ A hA B hB
    have hAH : A ∈ H.elements := hHF hA
    have hBH : B ∈ H.elements := hHG hB
    rcases H.cap_elements hAH hBH with ⟨C, hC, hCA, hCB⟩
    have hCne : C ≠ (∅ : Set α) := by
      intro hCempty
      have hEmptyMem : (∅ : Set α) ∈ H.elements := by simpa [hCempty] using hC
      have hLeast : is_least H := by
        intro K S hS
        have hEmptyCar : (∅ : Set α) ∈ H.carrier := by
          simpa [H.carrier_eq_elements] using hEmptyMem
        have hSCar : S ∈ H.carrier := by
          have hEmptySub : (∅ : Set α) ⊆ S := Set.empty_subset S
          exact H.upper' hEmptySub hEmptyCar
        simpa [H.carrier_eq_elements] using hSCar
      exact hHnotleast hLeast
    rcases Set.nonempty_iff_ne_empty.mpr hCne with ⟨x, hxC⟩
    exact ⟨x, hCA hxC, hCB hxC⟩
  · intro hPair
    let B : PosetFilterBase (setPartialOrder α) := {
      elements := {S : Set α | ∃ A ∈ F.elements, ∃ C ∈ G.elements, S = A ∩ C}
      non_empty := by
        rcases F.non_empty with ⟨A, hA⟩
        rcases G.non_empty with ⟨C, hC⟩
        exact ⟨A ∩ C, ⟨A, hA, C, hC, rfl⟩⟩
      cap_elements := by
        intro S1 S2 hS1 hS2
        rcases hS1 with ⟨A1, hA1, C1, hC1, rfl⟩
        rcases hS2 with ⟨A2, hA2, C2, hC2, rfl⟩
        rcases F.cap_elements hA1 hA2 with ⟨A3, hA3, hA3A1, hA3A2⟩
        rcases G.cap_elements hC1 hC2 with ⟨C3, hC3, hC3C1, hC3C2⟩
        refine ⟨A3 ∩ C3, ⟨A3, hA3, C3, hC3, rfl⟩, ?_, ?_⟩
        · intro x hx
          exact ⟨hA3A1 hx.1, hC3C1 hx.2⟩
        · intro x hx
          exact ⟨hA3A2 hx.1, hC3C2 hx.2⟩
    }
    let H : Filtrator.FilterOnPowerset α := close_filter_base B
    refine ⟨H, ?_, ?_, ?_⟩
    · intro A hA
      rcases G.non_empty with ⟨C0, hC0⟩
      refine ⟨A ∩ C0, ?_, by intro x hx; exact hx.1⟩
      exact ⟨A, hA, C0, hC0, rfl⟩
    · intro C hC
      rcases F.non_empty with ⟨A0, hA0⟩
      refine ⟨A0 ∩ C, ?_, by intro x hx; exact hx.2⟩
      exact ⟨A0, hA0, C, hC, rfl⟩
    · intro hLeast
      have hHleEmpty : H ≤ PosetFilter.principal (U := setPartialOrder α) (∅ : Set α) := hLeast _
      have hEmptyMem : (∅ : Set α) ∈ H.elements :=
        (le_principal_iff_subset (F := H) (x := (∅ : Set α))).1 hHleEmpty
      rcases hEmptyMem with ⟨S, hS, hSEmpty⟩
      rcases hS with ⟨A, hA, C, hC, hSAC⟩
      have hNotNE : ¬ (A ∩ C).Nonempty := by
        rw [Set.not_nonempty_iff_eq_empty]
        exact Set.Subset.antisymm (by simpa [hSAC] using hSEmpty) (Set.empty_subset (A ∩ C))
      exact hNotNE (hPair A hA C hC)

lemma meet_principal_iff_nonempty_inter
    {α : Type u}
    (A B : Set α) :
    meet
      (PosetFilter.principal (U := setPartialOrder α) A)
      (PosetFilter.principal (U := setPartialOrder α) B) ↔
      (A ∩ B).Nonempty := by
  constructor
  · intro h
    have hPair :=
      (meet_filter_iff_pairwise_inter_nonempty
        (F := PosetFilter.principal (U := setPartialOrder α) A)
        (G := PosetFilter.principal (U := setPartialOrder α) B)).1 h
    exact hPair A (by exact Set.Subset.rfl) B (by exact Set.Subset.rfl)
  · intro hAB
    apply (meet_filter_iff_pairwise_inter_nonempty
      (F := PosetFilter.principal (U := setPartialOrder α) A)
      (G := PosetFilter.principal (U := setPartialOrder α) B)).2
    intro A' hA' B' hB'
    rcases hAB with ⟨x, hxA, hxB⟩
    exact ⟨x, hA' hxA, hB' hxB⟩

lemma relImageFilter_principal
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (A : Set α) :
    relImageFilter r (PosetFilter.principal A) =
      PosetFilter.principal (relImage r A) := by
  apply PosetFilter.ext
  apply PosetFilterBase.ext_elements
  ext Y
  constructor
  · intro hY
    rcases (mem_relImageFilter_iff (r := r) (F := PosetFilter.principal A) (Y := Y)).1 hY with
      ⟨X, hX, hXY⟩
    exact Set.Subset.trans (relImage_mono r hX) hXY
  · intro hY
    exact (mem_relImageFilter_iff (r := r) (F := PosetFilter.principal A) (Y := Y)).2
      ⟨A, Set.Subset.rfl, hY⟩

lemma relPreimageFilter_principal
    {α : Type u} {β : Type v}
    (r : α → β → Prop)
    (B : Set β) :
    relPreimageFilter r (PosetFilter.principal B) =
      PosetFilter.principal (relPreimage r B) := by
  apply PosetFilter.ext
  apply PosetFilterBase.ext_elements
  ext X
  constructor
  · intro hX
    rcases (mem_relPreimageFilter_iff (r := r) (G := PosetFilter.principal B) (X := X)).1 hX with
      ⟨Y, hY, hYX⟩
    exact Set.Subset.trans (relPreimage_mono r hY) hYX
  · intro hX
    exact (mem_relPreimageFilter_iff (r := r) (G := PosetFilter.principal B) (X := X)).2
      ⟨B, Set.Subset.rfl, hX⟩

def principalFuncoid
    {α : Type u} {β : Type v}
    (r : α → β → Prop) :
    Funcoid α β where
  fwd := relImageFilter r
  bwd := relPreimageFilter r
  rev := by
    intro F G
    constructor
    · intro hFG
      apply (meet_filter_iff_pairwise_inter_nonempty
        (F := relPreimageFilter r G) (G := F)).2
      intro X hX A hA
      rcases (mem_relPreimageFilter_iff (r := r) (G := G) (X := X)).1 hX with
        ⟨B, hB, hBX⟩
      have hPair :=
        (meet_filter_iff_pairwise_inter_nonempty
          (F := relImageFilter r F) (G := G)).1 hFG
      have hImgNE : (relImage r A ∩ B).Nonempty := by
        have hImgMem : relImage r A ∈ (relImageFilter r F).elements :=
          (mem_relImageFilter_iff (r := r) (F := F) (Y := relImage r A)).2
            ⟨A, hA, Set.Subset.rfl⟩
        exact hPair (relImage r A) hImgMem B hB
      have hPreNE : (A ∩ relPreimage r B).Nonempty :=
        (relImage_inter_nonempty_iff_preimage_inter_nonempty r A B).1 hImgNE
      have hSubset : A ∩ relPreimage r B ⊆ A ∩ X := by
        intro x hx
        exact ⟨hx.1, hBX hx.2⟩
      simpa [Set.inter_comm] using hPreNE.mono hSubset
    · intro hGF
      apply (meet_filter_iff_pairwise_inter_nonempty
        (F := relImageFilter r F) (G := G)).2
      intro Y hY B hB
      rcases (mem_relImageFilter_iff (r := r) (F := F) (Y := Y)).1 hY with
        ⟨A, hA, hAY⟩
      have hPair :=
        (meet_filter_iff_pairwise_inter_nonempty
          (F := relPreimageFilter r G) (G := F)).1 hGF
      have hPreNE : (relPreimage r B ∩ A).Nonempty := by
        have hPreMem : relPreimage r B ∈ (relPreimageFilter r G).elements :=
          (mem_relPreimageFilter_iff (r := r) (G := G) (X := relPreimage r B)).2
            ⟨B, hB, Set.Subset.rfl⟩
        exact hPair (relPreimage r B) hPreMem A hA
      have hImgNE : (relImage r A ∩ B).Nonempty := by
        have hSwap : (A ∩ relPreimage r B).Nonempty := by
          simpa [Set.inter_comm] using hPreNE
        exact (relImage_inter_nonempty_iff_preimage_inter_nonempty r A B).2 hSwap
      have hSubset : relImage r A ∩ B ⊆ Y ∩ B := by
        intro y hy
        exact ⟨hAY hy.1, hy.2⟩
      exact hImgNE.mono hSubset

def principalFuncoidOfFunction
    {α : Type u} {β : Type v}
    (f : α → β) :
    Funcoid α β :=
  principalFuncoid (fun x y => f x = y)

lemma principalFuncoid_fwd_singleton
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (x : α) :
    (Funcoid.fwd_set (principalFuncoid r)) ({x} : Set α) =
      PosetFilter.principal (relImage r ({x} : Set α)) := by
  simpa [Funcoid.fwd_set, principalFuncoid] using
    relImageFilter_principal (r := r) ({x} : Set α)

lemma principalFuncoid_rel_singleton_singleton
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (x : α) (y : β) :
    (principalFuncoid r).funcoid_rel (PosetFilter.principal ({x} : Set α)) (PosetFilter.principal ({y} : Set β)) ↔ r x y :=
  calc
    (principalFuncoid r).funcoid_rel
        (PosetFilter.principal ({x} : Set α))
        (PosetFilter.principal ({y} : Set β))
      ↔ meet (PosetFilter.principal (relImage r ({x} : Set α)))
          (PosetFilter.principal ({y} : Set β)) := by
            simp [PointfreeFuncoid.funcoid_rel, principalFuncoid, relImageFilter_principal]
    _ ↔ (relImage r ({x} : Set α) ∩ ({y} : Set β)).Nonempty :=
      meet_principal_iff_nonempty_inter (relImage r ({x} : Set α)) ({y} : Set β)
    _ ↔ r x y := by
      constructor
      · rintro ⟨z, hzImg, hzSingleton⟩
        have hzEq : z = y := by simpa using hzSingleton
        rcases hzImg with ⟨x', hxSingleton, hxz⟩
        have hxEq : x' = x := by simpa using hxSingleton
        simpa [hxEq, hzEq] using hxz
      · intro hxy
        exact ⟨y, ⟨x, by simp, hxy⟩, by simp⟩

theorem principalFuncoid_rel_iff_meet_graph_prod
    {α : Type u} {β : Type v}
    (r : α → β → Prop) (x : Set α) (y : Set β) :
    (principalFuncoid r).funcoid_rel_set x y ↔
      meet ({p : α × β | r p.1 p.2}) (x ×ˢ y) := by
  calc
    (principalFuncoid r).funcoid_rel_set x y
      ↔ meet (PosetFilter.principal (relImage r x)) (PosetFilter.principal y) := by
          simp [Funcoid.funcoid_rel_set, PointfreeFuncoid.funcoid_rel,
            principalFuncoid, relImageFilter_principal]
    _ ↔ (relImage r x ∩ y).Nonempty :=
      meet_principal_iff_nonempty_inter (relImage r x) y
    _ ↔ ({p : α × β | r p.1 p.2} ∩ (x ×ˢ y)).Nonempty := by
      constructor
      · rintro ⟨b, hbImg, hby⟩
        rcases hbImg with ⟨a, hax, hab⟩
        exact ⟨(a, b), by simpa using hab, ⟨hax, hby⟩⟩
      · rintro ⟨⟨a, b⟩, hab, hxy⟩
        exact ⟨b, ⟨a, hxy.1, by simpa using hab⟩, hxy.2⟩
    _ ↔ meet ({p : α × β | r p.1 p.2}) (x ×ˢ y) :=
      (meet_set_iff_nonempty (A := {p : α × β | r p.1 p.2}) (B := x ×ˢ y)).symm

lemma principalFuncoidOfFunction_rel_singleton_singleton
    {α : Type u} {β : Type v}
    (f : α → β) (x : α) (y : β) :
    (principalFuncoidOfFunction f).funcoid_rel_set ({x} : Set α) ({y} : Set β) ↔ f x = y := by
  simpa [principalFuncoidOfFunction, Funcoid.funcoid_rel_set] using
    principalFuncoid_rel_singleton_singleton (r := fun a b => f a = b) x y

theorem principalFuncoid_comp
    {α : Type u} {β : Type v} {γ : Type w}
    (s : β → γ → Prop) (r : α → β → Prop) :
    principalFuncoid (relComp r s) =
      (principalFuncoid s) ∘ (principalFuncoid r) := by
  apply PointfreeFuncoid.ext
  · funext F
    apply PosetFilter.ext
    apply PosetFilterBase.ext_elements
    ext Z
    constructor
    · intro hZ
      rcases (mem_relImageFilter_iff (r := relComp r s) (F := F) (Y := Z)).1 hZ with
        ⟨A, hAF, hAZ⟩
      have hAImgMem : relImage r A ∈ (relImageFilter r F).elements :=
        (mem_relImageFilter_iff (r := r) (F := F) (Y := relImage r A)).2
          ⟨A, hAF, Set.Subset.rfl⟩
      have hAImgSub : relImage s (relImage r A) ⊆ Z := by
        calc
          relImage s (relImage r A) = relImage (relComp r s) A :=
            (relImage_relComp r s A).symm
          _ ⊆ Z := hAZ
      exact (mem_relImageFilter_iff (r := s) (F := relImageFilter r F) (Y := Z)).2
        ⟨relImage r A, hAImgMem, hAImgSub⟩
    · intro hZ
      rcases (mem_relImageFilter_iff (r := s) (F := relImageFilter r F) (Y := Z)).1 hZ with
        ⟨B, hBMem, hBZ⟩
      rcases (mem_relImageFilter_iff (r := r) (F := F) (Y := B)).1 hBMem with
        ⟨A, hAF, hAB⟩
      have hAZ : relImage (relComp r s) A ⊆ Z := by
        calc
          relImage (relComp r s) A = relImage s (relImage r A) :=
            relImage_relComp r s A
          _ ⊆ relImage s B := relImage_mono s hAB
          _ ⊆ Z := hBZ
      exact (mem_relImageFilter_iff (r := relComp r s) (F := F) (Y := Z)).2
        ⟨A, hAF, hAZ⟩
  · funext G
    apply PosetFilter.ext
    apply PosetFilterBase.ext_elements
    ext X
    constructor
    · intro hX
      rcases (mem_relPreimageFilter_iff (r := relComp r s) (G := G) (X := X)).1 hX with
        ⟨C, hCG, hCX⟩
      have hCPreMem : relPreimage s C ∈ (relPreimageFilter s G).elements :=
        (mem_relPreimageFilter_iff (r := s) (G := G) (X := relPreimage s C)).2
          ⟨C, hCG, Set.Subset.rfl⟩
      have hCPreSub : relPreimage r (relPreimage s C) ⊆ X := by
        calc
          relPreimage r (relPreimage s C) = relPreimage (relComp r s) C :=
            (relPreimage_relComp r s C).symm
          _ ⊆ X := hCX
      exact (mem_relPreimageFilter_iff (r := r) (G := relPreimageFilter s G) (X := X)).2
        ⟨relPreimage s C, hCPreMem, hCPreSub⟩
    · intro hX
      rcases (mem_relPreimageFilter_iff (r := r) (G := relPreimageFilter s G) (X := X)).1 hX with
        ⟨B, hBMem, hBX⟩
      rcases (mem_relPreimageFilter_iff (r := s) (G := G) (X := B)).1 hBMem with
        ⟨C, hCG, hCB⟩
      have hCX : relPreimage (relComp r s) C ⊆ X := by
        calc
          relPreimage (relComp r s) C = relPreimage r (relPreimage s C) :=
            relPreimage_relComp r s C
          _ ⊆ relPreimage r B := relPreimage_mono r hCB
          _ ⊆ X := hBX
      exact (mem_relPreimageFilter_iff (r := relComp r s) (G := G) (X := X)).2
        ⟨C, hCG, hCX⟩
