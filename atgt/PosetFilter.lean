import Mathlib.Data.Ordmap.Ordset
import Mathlib.Order.Lattice

universe u

structure PosetFilterBase{α: Type*}(U: PartialOrder α) where
  elements: Set α
  non_empty: Set.Nonempty elements
  cap_elements {x y: α} : x ∈ elements → y ∈ elements → ∃ z ∈ elements, (z ≤ x ∧ z ≤ y)

@[ext]
lemma PosetFilterBase.ext_elements{α: Type*} {U : PartialOrder α}
  (F G : PosetFilterBase U)
  (h : F.elements = G.elements) : F = G := by
  cases F
  cases G
  cases h
  rfl

structure PosetFilter{α: Type*}(U: PartialOrder α) extends PosetFilterBase U, UpperSet α where
  carrier_eq_elements : carrier = elements

@[ext]
lemma PosetFilter.ext {α: Type*} {U : PartialOrder α}
  (F G : PosetFilter U)
  (h : F.toPosetFilterBase = G.toPosetFilterBase) : F = G := by
  cases F with
  | mk Fbase Fup hF =>
    cases G with
    | mk Gbase Gup hG =>
      cases h
      have hUp : Fup = Gup := by
        cases Fup with
        | mk Fcarrier Fupper =>
          cases Gup with
          | mk Gcarrier Gupper =>
            dsimp at hF hG
            have hcarrier : Fcarrier = Gcarrier := by
              calc
                Fcarrier = Fbase.elements := hF
                _ = Gcarrier := hG.symm
            cases hcarrier
            have hupper : Fupper = Gupper := Subsingleton.elim _ _
            cases hupper
            rfl
      cases hUp
      rfl

structure PosetFilter.ThroughEquiv{α: Type*}(U: PartialOrder α) where
  elements: Set α
  non_empty: Set.Nonempty elements
  cap_elements {x y: α} : x ∈ elements ∧ y ∈ elements ↔ ∃ z ∈ elements, (z ≤ x ∧ z ≤ y)

@[ext]
lemma PosetFilter.ThroughEquiv.ext_elements {α: Type*} {U : PartialOrder α}
  (F G : PosetFilter.ThroughEquiv U)
  (h : F.elements = G.elements) : F = G := by
  cases F
  cases G
  cases h
  rfl

@[ext]
lemma PosetFilter.ThroughEquiv.ext {α: Type*} {U : PartialOrder α}
  (F G : PosetFilter U)
  (h : F.elements = G.elements) : F = G := by
  have hbase : F.toPosetFilterBase = G.toPosetFilterBase := by
    apply PosetFilterBase.ext_elements
    calc
      F.toPosetFilterBase.elements = F.elements := rfl
      _ = G.elements := h
      _ = G.toPosetFilterBase.elements := rfl
  exact PosetFilter.ext F G hbase

def PosetFilter.toThroughEquiv {α : Type*} {U : PartialOrder α} (F : PosetFilter U) :
    PosetFilter.ThroughEquiv U where
  elements := F.elements
  non_empty := F.non_empty
  cap_elements := by
    intro x y
    constructor
    · intro hxy
      exact F.cap_elements hxy.1 hxy.2
    · intro hxy
      rcases hxy with ⟨z, hz, hzx, hzy⟩
      constructor
      · have hz' : z ∈ F.carrier := by
          simpa [F.carrier_eq_elements] using hz
        have hx' : x ∈ F.carrier := F.upper' hzx hz'
        simpa [F.carrier_eq_elements] using hx'
      · have hz' : z ∈ F.carrier := by
          simpa [F.carrier_eq_elements] using hz
        have hy' : y ∈ F.carrier := F.upper' hzy hz'
        simpa [F.carrier_eq_elements] using hy'

def PosetFilter.ThroughEquiv.toPosetFilter {α : Type*} {U : PartialOrder α}
    (F : PosetFilter.ThroughEquiv U) : PosetFilter U where
  elements := F.elements
  non_empty := F.non_empty
  cap_elements := by
    intro x y hx hy
    exact (F.cap_elements).1 ⟨hx, hy⟩
  carrier := F.elements
  upper' := by
    intro x y hxy hx
    have hxy_mem : x ∈ F.elements ∧ y ∈ F.elements :=
      (F.cap_elements).2 ⟨x, hx, le_rfl, hxy⟩
    exact hxy_mem.2
  carrier_eq_elements := rfl

@[simp]
lemma PosetFilter.ThroughEquiv.toPosetFilter_toThroughEquiv {α : Type*} {U : PartialOrder α}
    (F : PosetFilter U) :
    PosetFilter.ThroughEquiv.toPosetFilter (PosetFilter.toThroughEquiv F) = F := by
  apply PosetFilter.ThroughEquiv.ext
  rfl

@[simp]
lemma PosetFilter.toThroughEquiv_toPosetFilter {α : Type*} {U : PartialOrder α}
    (F : PosetFilter.ThroughEquiv U) :
    PosetFilter.toThroughEquiv (PosetFilter.ThroughEquiv.toPosetFilter F) = F := by
  apply PosetFilter.ThroughEquiv.ext_elements
  rfl

lemma PosetFilter.toThroughEquiv_leftInverse {α : Type*} {U : PartialOrder α} :
    Function.LeftInverse
      (PosetFilter.ThroughEquiv.toPosetFilter (U := U))
      (PosetFilter.toThroughEquiv (U := U)) := by
  intro F
  exact PosetFilter.ThroughEquiv.toPosetFilter_toThroughEquiv (U := U) F

lemma PosetFilter.toThroughEquiv_rightInverse {α : Type*} {U : PartialOrder α} :
    Function.RightInverse
      (PosetFilter.ThroughEquiv.toPosetFilter (U := U))
      (PosetFilter.toThroughEquiv (U := U)) := by
  intro F
  exact PosetFilter.toThroughEquiv_toPosetFilter (U := U) F

lemma PosetFilter.toThroughEquiv_bijective {α : Type*} {U : PartialOrder α} :
    Function.Bijective (PosetFilter.toThroughEquiv (U := U)) := by
  refine ⟨?_, ?_⟩
  · exact (PosetFilter.toThroughEquiv_leftInverse (U := U)).injective
  · exact (PosetFilter.toThroughEquiv_rightInverse (U := U)).surjective

lemma PosetFilter.ThroughEquiv.toPosetFilter_bijective {α : Type*} {U : PartialOrder α} :
    Function.Bijective (PosetFilter.ThroughEquiv.toPosetFilter (U := U)) := by
  refine ⟨?_, ?_⟩
  · exact (PosetFilter.toThroughEquiv_rightInverse (U := U)).injective
  · exact (PosetFilter.toThroughEquiv_leftInverse (U := U)).surjective

@[simp]
lemma PosetFilter.mem_carrier_iff_mem_elements {α : Type*} {U : PartialOrder α} (F : PosetFilter U) (x : α) :
    x ∈ F.carrier ↔ x ∈ F.elements := by
  simp [F.carrier_eq_elements]

def PosetFilter.principal {α: Type*} {U : PartialOrder α} (a : α) : PosetFilter U := by
  letI : PartialOrder α := U
  refine
    { elements := { x | a ≤ x }
      non_empty := ⟨a, le_rfl⟩
      cap_elements := ?_
      carrier := { x | a ≤ x }
      upper' := ?_
      carrier_eq_elements := rfl }
  · intro x y hx hy
    exact ⟨a, le_rfl, hx, hy⟩
  · intro x y hxy hx
    exact le_trans hx hxy

def Principals {α: Type*}{U : PartialOrder α} : Set (PosetFilter U) := { PosetFilter.principal a | a : α }

def close_filter_base{α: Type*} {U : PartialOrder α}
  (B : PosetFilterBase U) : PosetFilter U := by
  letI : PartialOrder α := U
  refine
    { elements := { y | ∃ x ∈ B.elements, x ≤ y }
      non_empty := ?_
      cap_elements := ?_
      carrier := { y | ∃ x ∈ B.elements, x ≤ y }
      upper' := ?_
      carrier_eq_elements := rfl }
  · rcases B.non_empty with ⟨x, hx⟩
    exact ⟨x, x, hx, le_rfl⟩
  · intro x y hx hy
    rcases hx with ⟨x0, hx0, hx0_le_x⟩
    rcases hy with ⟨y0, hy0, hy0_le_y⟩
    rcases B.cap_elements hx0 hy0 with ⟨z, hz, hz_le_x0, hz_le_y0⟩
    refine ⟨z, ?_, le_trans hz_le_x0 hx0_le_x, le_trans hz_le_y0 hy0_le_y⟩
    exact ⟨z, hz, le_rfl⟩
  · intro x y hx hxy
    rcases hxy with ⟨z, hz, hzx⟩
    exact ⟨z, hz, le_trans hzx hx⟩

instance {α: Type*}(U : PartialOrder α) : LE (PosetFilter U) :=
  ⟨fun F G => G.elements ⊆ F.elements⟩

instance {α: Type*}(U : PartialOrder α) : PartialOrder (PosetFilter U) where
  le F G := G.elements ⊆ F.elements

  le_refl F := by
    intro x hx; exact hx

  le_trans F G H hFG hGH := by
    intro x hx
    exact hFG (hGH hx)

  le_antisymm F G hFG hGF := by
    apply PosetFilter.ext
    apply PosetFilterBase.ext_elements
    exact Set.Subset.antisymm hGF hFG

def PosetFilter.castOrderIso {α : Type*} {U V : PartialOrder α}
    (h : U = V) : PosetFilter U ≃o PosetFilter V where
  toEquiv :=
    { toFun := fun F => h ▸ F
      invFun := fun G => h.symm ▸ G
      left_inv := by
        intro F
        cases h
        rfl
      right_inv := by
        intro G
        cases h
        rfl }
  map_rel_iff' := by
    intro F G
    cases h
    rfl

@[simp]
lemma PosetFilter.castOrderIso_principal {α : Type*} {U V : PartialOrder α}
    (h : U = V) (x : α) :
    PosetFilter.castOrderIso h (PosetFilter.principal (U := U) x) =
      PosetFilter.principal (U := V) x := by
  cases h
  rfl

lemma le_principal_iff_subset {α: Type*}{U : PartialOrder α} (F : PosetFilter U) (x : α) : F ≤ PosetFilter.principal x ↔ x ∈ F.elements := by
  letI : PartialOrder α := U
  constructor
  . intro h
    change (PosetFilter.principal x).elements ⊆ F.elements at h
    apply h
    exact le_rfl
  . intro h
    change (PosetFilter.principal x).elements ⊆ F.elements
    intro y hy
    have hx : x ∈ F.carrier := by
      simpa [F.carrier_eq_elements] using h
    have hy' : y ∈ F.carrier := F.upper' hy hx
    simpa [F.carrier_eq_elements] using hy'

lemma principals_le_iff {α: Type*}{U : PartialOrder α} (x y : α) : PosetFilter.principal x ≤ PosetFilter.principal (U := U) y ↔ x ≤ y := by
  rw [le_principal_iff_subset]
  rfl

lemma principal_injective {α: Type*}{U : PartialOrder α} : Function.Injective (PosetFilter.principal (U := U)) := by
  intro x y h
  apply le_antisymm
  · rw [← principals_le_iff]
    simp [h]
  · rw [← principals_le_iff]
    simp [h]

namespace FilterBaseMeet

variable {α : Type u} [SemilatticeInf α]

/-- The set `⟨a⊓⟩* S = { a ⊓ s | s ∈ S.elements } on a meet-semilattice `α` inherits the filter-base
structure from `S`. This is Proposition 425: meeting every element of a filter base with a fixed element
again yields a filter base. -/
def meet_filter_base_set (a : α) (S : PosetFilterBase (U := (inferInstance : PartialOrder α))) : Set α :=
  { x | ∃ s ∈ S.elements, x = a ⊓ s }

lemma meet_filter_base_set_nonempty (a : α) (S : PosetFilterBase (U := (inferInstance : PartialOrder α))) :
    Set.Nonempty (meet_filter_base_set a S) := by
  rcases S.non_empty with ⟨s, hs⟩
  refine ⟨a ⊓ s, ⟨s, hs, rfl⟩⟩

lemma meet_filter_base_set_cap {a : α} (S : PosetFilterBase (U := (inferInstance : PartialOrder α)))
    {x y : α}
    (hx : x ∈ meet_filter_base_set a S)
    (hy : y ∈ meet_filter_base_set a S) :
    ∃ z ∈ meet_filter_base_set a S, z ≤ x ∧ z ≤ y := by
  rcases hx with ⟨sx, hsx, rfl⟩
  rcases hy with ⟨sy, hsy, rfl⟩
  rcases S.cap_elements hsx hsy with ⟨sz, hsz, hsz_le_sx, hsz_le_sy⟩
  use a ⊓ sz
  constructor
  · exact ⟨sz, hsz, rfl⟩
  constructor
  · have : a ⊓ sz ≤ a ⊓ sx := inf_le_inf le_rfl hsz_le_sx
    exact this
  · have : a ⊓ sz ≤ a ⊓ sy := inf_le_inf le_rfl hsz_le_sy
    exact this

/- Proposition 425: meeting each element of a filter base with `a : α` yields another filter base. -/
def meet_filter_base (a : α)
    (S : PosetFilterBase (U := (inferInstance : PartialOrder α))) : PosetFilterBase (U := (inferInstance : PartialOrder α)) where
  elements := meet_filter_base_set a S
  non_empty := meet_filter_base_set_nonempty a S
  cap_elements := meet_filter_base_set_cap S

end FilterBaseMeet

export FilterBaseMeet (meet_filter_base)
