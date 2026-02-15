import Mathlib.Data.Set.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.Set
import Mathlib.Order.Defs.Unbundled
import atgt.Poset
import atgt.PosetFilter
import atgt.Filtrator.Separable
import atgt.Filtrator.Primary

universe u

namespace AlternativePrimaryFiltrators

variable {α : Type u}

abbrev FilterSet [U: PartialOrder α] := PosetFilter.ThroughEquiv U

abbrev FilterSet.ext_elements [U: PartialOrder α] := @PosetFilter.ThroughEquiv.ext_elements α U

structure IdealSet [PartialOrder α] where
  elements: Set α
  non_empty: Set.Nonempty elements
  cup_elements {a b : α} :
      a ∈ elements ∧ b ∈ elements ↔ ∃ z : α, z ∈ elements ∧ a ≤ z ∧ b ≤ z

@[ext]
lemma IdealSet.ext [PartialOrder α] (F G : IdealSet (α := α))
    (h : F.elements = G.elements) : F = G := by
  cases F
  cases G
  cases h
  rfl

structure FreeStar [PartialOrder α] where
  elements: Set α
  non_univ: elements ≠ Set.univ
  cup_not_elements {a b : α} :
      a ∉ elements ∧ b ∉ elements ↔ ∃ z : α, z ∉ elements ∧ a ≤ z ∧ b ≤ z

@[ext]
lemma FreeStar.ext [PartialOrder α] (F G : FreeStar (α := α))
    (h : F.elements = G.elements) : F = G := by
  cases F
  cases G
  cases h
  rfl

structure Mixer [PartialOrder α] where
  elements: Set α
  non_univ: elements ≠ Set.univ
  cap_not_elements {a b : α} :
      a ∉ elements ∧ b ∉ elements ↔ ∃ z : α, z ∉ elements ∧ z ≤ a ∧ z ≤ b

@[ext]
lemma Mixer.ext [PartialOrder α] (F G : Mixer (α := α))
    (h : F.elements = G.elements) : F = G := by
  cases F
  cases G
  cases h
  rfl

instance [PartialOrder α] : LE (FreeStar (α := α)) where
  le F G := F.elements ⊆ G.elements

instance [PartialOrder α] : PartialOrder (FreeStar (α := α)) where
  le := (· ≤ ·)
  le_refl F := by
    intro x hx
    exact hx
  le_trans F G H hFG hGH := by
    intro x hxF
    exact hGH (hFG hxF)
  le_antisymm F G hFG hGF := by
    apply FreeStar.ext
    exact Set.Subset.antisymm hFG hGF

instance [PartialOrder α] :
    LE (FilterSet (U := (inferInstance : PartialOrder α))) where
  le F G := G.elements ⊆ F.elements

instance [PartialOrder α] :
    PartialOrder (FilterSet (U := (inferInstance : PartialOrder α))) where
  le := (· ≤ ·)
  le_refl F := by
    intro x hx
    exact hx
  le_trans F G H hFG hGH := by
    intro x hxH
    exact hFG (hGH hxH)
  le_antisymm F G hFG hGF := by
    apply FilterSet.ext_elements
    exact Set.Subset.antisymm hGF hFG

-- TODO: This and below can be shortened by proving conversions with ideals first.
def freeStar_to_filterSet [P: BooleanAlgebra α] (F : FreeStar (α := α)) :
    FilterSet (U := (inferInstance : PartialOrder α)) := {
  elements := (·ᶜ) '' F.elementsᶜ
  non_empty := by
    classical
    have hex : ∃ x : α, x ∉ F.elements := by
      by_contra h
      apply F.non_univ
      ext x
      constructor
      · intro _
        trivial
      · intro _
        by_contra hx
        exact h ⟨x, hx⟩
    rcases hex with ⟨x, hx⟩
    exact ⟨xᶜ, ⟨x, by simpa [Set.mem_compl_iff] using hx, by simp⟩⟩
  cap_elements := by
    intro a b
    let G := F.elementsᶜ
    have mem_equiv (x : α) : x ∈ (·ᶜ) '' G ↔ xᶜ ∉ F.elements := by
      constructor
      · intro ⟨y, hy, hyx⟩
        have hy_eq : y = xᶜ := by
          have h := congrArg compl hyx
          simp [compl_compl] at h
          exact h
        have hy_not : y ∉ F.elements := by simpa [G] using hy
        simpa [hy_eq] using hy_not
      · intro hx
        refine ⟨xᶜ, ?_, by simp⟩
        simpa [G] using hx
    have left : (a ∈ (·ᶜ) '' G ∧ b ∈ (·ᶜ) '' G) ↔ (aᶜ ∉ F.elements ∧ bᶜ ∉ F.elements) := by
      constructor
      · intro hab
        exact ⟨(mem_equiv a).1 hab.1, (mem_equiv b).1 hab.2⟩
      · intro hab
        exact ⟨(mem_equiv a).2 hab.1, (mem_equiv b).2 hab.2⟩
    have right : (∃ z, z ∈ (·ᶜ) '' G ∧ z ≤ a ∧ z ≤ b) ↔
        ∃ y, y ∉ F.elements ∧ aᶜ ≤ y ∧ bᶜ ≤ y := by
      constructor
      · intro ⟨z, hz, hza, hzb⟩
        have hz_not : zᶜ ∉ F.elements := (mem_equiv z).1 hz
        have hya : aᶜ ≤ zᶜ := compl_le_compl hza
        have hyb : bᶜ ≤ zᶜ := compl_le_compl hzb
        exact ⟨zᶜ, hz_not, hya, hyb⟩
      · intro ⟨y, hy, hay, hby⟩
        have hy_mem : yᶜ ∈ (·ᶜ) '' G := (mem_equiv (yᶜ)).2 (by simpa using hy)
        have hza : yᶜ ≤ a := by simpa using compl_le_compl hay
        have hzb : yᶜ ≤ b := by simpa using compl_le_compl hby
        exact ⟨yᶜ, hy_mem, hza, hzb⟩
    exact (left.trans (F.cup_not_elements (a := aᶜ) (b := bᶜ))).trans right.symm
}

lemma compl_image_compl_image [BooleanAlgebra α] (s : Set α) :
    (fun x : α => xᶜ) '' ((fun x : α => xᶜ) '' s) = s := by
  calc
    (fun x : α => xᶜ) '' ((fun x : α => xᶜ) '' s)
        = ((fun x : α => xᶜ) ∘ (fun x : α => xᶜ)) '' s := by
            simpa using (Set.image_image (fun x : α => xᶜ) (fun x : α => xᶜ) s)
    _ = (fun x : α => x) '' s := by
      congr
      funext x
      simp
    _ = s := by simp

def filterSet_to_freeStar [P: BooleanAlgebra α]
    (F : FilterSet (U := (inferInstance : PartialOrder α))) : FreeStar (α := α) := {
  elements := ((·ᶜ) '' F.elements)ᶜ
  non_univ := by
    intro h_univ
    rcases F.non_empty with ⟨x, hx⟩
    have hx_mem : xᶜ ∈ (·ᶜ) '' F.elements := ⟨x, hx, rfl⟩
    have hx_not : xᶜ ∉ ((·ᶜ) '' F.elements)ᶜ := by simp [hx_mem]
    have hx_univ : xᶜ ∈ ((·ᶜ) '' F.elements)ᶜ := by simp [h_univ]
    exact hx_not hx_univ
  cup_not_elements := by
    intro a b
    let G := (·ᶜ) '' F.elements
    have mem_equiv (x : α) : x ∈ G ↔ xᶜ ∈ F.elements := by
      constructor
      · intro ⟨y, hy, hyx⟩
        have hy_eq : y = xᶜ := by
          have h := congrArg compl hyx
          simp [compl_compl] at h
          exact h
        simpa [hy_eq] using hy
      · intro hx
        use xᶜ
        constructor
        · exact hx
        · simp
    have left : (a ∉ Gᶜ ∧ b ∉ Gᶜ) ↔ (aᶜ ∈ F.elements ∧ bᶜ ∈ F.elements) := by
      simp [Set.mem_compl_iff, mem_equiv a, mem_equiv b]
    have right : (∃ z, z ∉ Gᶜ ∧ a ≤ z ∧ b ≤ z) ↔ ∃ y, y ∈ F.elements ∧ y ≤ aᶜ ∧ y ≤ bᶜ := by
      constructor
      · intro ⟨z, hz, hza, hzb⟩
        have hzG : z ∈ G := by simpa [Set.mem_compl_iff] using hz
        have hy : zᶜ ∈ F.elements := (mem_equiv z).1 hzG
        have hza_le : zᶜ ≤ aᶜ := compl_le_compl hza
        have hzb_le : zᶜ ≤ bᶜ := compl_le_compl hzb
        exact ⟨zᶜ, hy, hza_le, hzb_le⟩
      · intro ⟨y, hy, hya, hyb⟩
        have hyc : yᶜ ∈ G := (mem_equiv (yᶜ)).2 (by simpa using hy)
        have hya_le : a ≤ yᶜ := by simpa using compl_le_compl hya
        have hyb_le : b ≤ yᶜ := by simpa using compl_le_compl hyb
        exact ⟨yᶜ, by simpa [Set.mem_compl_iff] using hyc, hya_le, hyb_le⟩
    exact (left.trans (F.cap_elements (x := aᶜ) (y := bᶜ))).trans right.symm
}

theorem freeStar_to_filterSet_left_inv [P : BooleanAlgebra α]
    (F : FreeStar (α := α)) :
    filterSet_to_freeStar (freeStar_to_filterSet F) = F := by
  ext x
  simp [filterSet_to_freeStar, freeStar_to_filterSet, compl_image_compl_image]

theorem filterSet_to_freeStar_left_inv [P : BooleanAlgebra α]
    (F : FilterSet (U := (inferInstance : PartialOrder α))) :
    freeStar_to_filterSet (filterSet_to_freeStar F) = F := by
  apply FilterSet.ext_elements
  ext x
  simp [filterSet_to_freeStar, freeStar_to_filterSet, compl_image_compl_image]

theorem freeStar_to_filterSet_bijective [P : BooleanAlgebra α] :
    Function.Bijective (freeStar_to_filterSet :
      FreeStar (α := α) → FilterSet (U := (inferInstance : PartialOrder α))) := by
  constructor
  · intro F G h
    have h' : filterSet_to_freeStar (freeStar_to_filterSet F) =
        filterSet_to_freeStar (freeStar_to_filterSet G) :=
      congrArg filterSet_to_freeStar h
    calc
      F = filterSet_to_freeStar (freeStar_to_filterSet F) := (freeStar_to_filterSet_left_inv F).symm
      _ = filterSet_to_freeStar (freeStar_to_filterSet G) := h'
      _ = G := freeStar_to_filterSet_left_inv G
  · intro G
    use filterSet_to_freeStar G
    simp [filterSet_to_freeStar_left_inv]

theorem freeStar_to_filterSet_monotone [P : BooleanAlgebra α] :
    Monotone (freeStar_to_filterSet :
      FreeStar (α := α) → FilterSet (U := (inferInstance : PartialOrder α))) := by
  intro F G hFG x hx
  rcases hx with ⟨y, hy, hyx⟩
  refine ⟨y, ?_, hyx⟩
  intro hyF
  exact hy (hFG hyF)

theorem filterSet_to_freeStar_monotone [P : BooleanAlgebra α] :
    Monotone (filterSet_to_freeStar :
      FilterSet (U := (inferInstance : PartialOrder α)) → FreeStar (α := α)) := by
  intro F G hFG x hxF hxG
  apply hxF
  rcases hxG with ⟨y, hyG, hyx⟩
  refine ⟨y, hFG hyG, hyx⟩

def freeStarOrderIsoFilterSet [P : BooleanAlgebra α] :
    FreeStar (α := α) ≃o FilterSet (U := (inferInstance : PartialOrder α)) where
  toEquiv :=
    { toFun := freeStar_to_filterSet
      invFun := filterSet_to_freeStar
      left_inv := freeStar_to_filterSet_left_inv
      right_inv := filterSet_to_freeStar_left_inv }
  map_rel_iff' := by
    intro F G
    constructor
    · intro h
      have hmono := filterSet_to_freeStar_monotone (α := α)
      simpa [freeStar_to_filterSet_left_inv] using hmono h
    · intro h
      have hmono := freeStar_to_filterSet_monotone (α := α)
      simpa [filterSet_to_freeStar_left_inv] using hmono h

def filterSetOrderIsoPosetFilter [PartialOrder α] :
    FilterSet (U := (inferInstance : PartialOrder α)) ≃o
      PosetFilter (U := (inferInstance : PartialOrder α)) where
  toEquiv :=
    { toFun := PosetFilter.ThroughEquiv.toPosetFilter
      invFun := PosetFilter.toThroughEquiv
      left_inv := PosetFilter.toThroughEquiv_toPosetFilter
      right_inv := PosetFilter.ThroughEquiv.toPosetFilter_toThroughEquiv }
  map_rel_iff' := by
    intro F G
    rfl

namespace SeparatorCoreFreeStars

def separatorCoreSet [BooleanAlgebra α] (a : α) : Set α :=
  separator_core (F := Filtrator.of_subset (Set.univ : Set α)) a

lemma isLeast_iff_eq_bot [BooleanAlgebra α] (x : α) :
    is_least x ↔ x = ⊥ := by
  constructor
  · intro hx
    exact le_antisymm (hx ⊥) bot_le
  · intro hx y
    rw [hx]
    exact bot_le

lemma mem_separator_iff_inf_ne_bot [BooleanAlgebra α] (x a : α) :
    x ∈ separator a ↔ x ⊓ a ≠ ⊥ := by
  constructor
  · intro hx
    have hnot : ¬ is_least (x ⊓ a) := (meet_as_inf x a).1 hx
    intro hbot
    exact hnot ((isLeast_iff_eq_bot (x := x ⊓ a)).2 hbot)
  · intro hne
    refine (meet_as_inf x a).2 ?_
    intro hleast
    exact hne ((isLeast_iff_eq_bot (x := x ⊓ a)).1 hleast)

lemma not_mem_separator_iff_le_compl [BooleanAlgebra α] (x a : α) :
    x ∉ separator a ↔ x ≤ aᶜ := by
  rw [mem_separator_iff_inf_ne_bot]
  constructor
  · intro hx
    have hinf : x ⊓ a = ⊥ := by
      by_contra hne
      exact hx hne
    have hdisj : Disjoint x a := disjoint_iff.mpr hinf
    exact (le_compl_iff_disjoint_right).2 hdisj
  · intro hx
    have hdisj : Disjoint x a := (le_compl_iff_disjoint_right).1 hx
    have hinf : x ⊓ a = ⊥ := disjoint_iff.mp hdisj
    intro hne
    exact hne hinf

lemma not_mem_separatorCoreSet_iff_le_compl [BooleanAlgebra α] (x a : α) :
    x ∉ separatorCoreSet (α := α) a ↔ x ≤ aᶜ := by
  simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using
    (not_mem_separator_iff_le_compl (x := x) (a := a))

def separatorCoreFreeStar [BooleanAlgebra α] (a : α) : FreeStar (α := α) where
  elements := separatorCoreSet (α := α) a
  non_univ := by
    intro h_univ
    have hbot_mem : (⊥ : α) ∈ separatorCoreSet (α := α) a := by simp [h_univ]
    have hbot_not_mem : (⊥ : α) ∉ separatorCoreSet (α := α) a := by
      exact (not_mem_separatorCoreSet_iff_le_compl (x := (⊥ : α)) (a := a)).2 bot_le
    exact hbot_not_mem hbot_mem
  cup_not_elements := by
    intro x y
    constructor
    · intro hxy
      have hx_le : x ≤ aᶜ := (not_mem_separatorCoreSet_iff_le_compl (x := x) (a := a)).1 hxy.1
      have hy_le : y ≤ aᶜ := (not_mem_separatorCoreSet_iff_le_compl (x := y) (a := a)).1 hxy.2
      refine ⟨x ⊔ y, ?_, le_sup_left, le_sup_right⟩
      exact (not_mem_separatorCoreSet_iff_le_compl (x := x ⊔ y) (a := a)).2 (sup_le hx_le hy_le)
    · intro h
      rcases h with ⟨z, hz, hxz, hyz⟩
      have hz_le : z ≤ aᶜ := (not_mem_separatorCoreSet_iff_le_compl (x := z) (a := a)).1 hz
      have hx_le : x ≤ aᶜ := le_trans hxz hz_le
      have hy_le : y ≤ aᶜ := le_trans hyz hz_le
      exact ⟨(not_mem_separatorCoreSet_iff_le_compl (x := x) (a := a)).2 hx_le,
        (not_mem_separatorCoreSet_iff_le_compl (x := y) (a := a)).2 hy_le⟩

abbrev separatorCoreSetFreeStars [BooleanAlgebra α] : Type u :=
  {S : Set α // ∃ a : α, S = separatorCoreSet (α := α) a}

def separatorCoreToSetFreeStars [BooleanAlgebra α] (a : α) : separatorCoreSetFreeStars (α := α) :=
  ⟨separatorCoreSet (α := α) a, ⟨a, rfl⟩⟩

theorem separatorCoreToSetFreeStars_bijective [BooleanAlgebra α] :
    Function.Bijective (separatorCoreToSetFreeStars (α := α)) := by
  constructor
  · intro a b h
    have hset : separatorCoreSet (α := α) a = separatorCoreSet (α := α) b := congrArg Subtype.val h
    have hsep : separator a = separator b := by
      simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hset
    have hstrong : IsStronglySeparable α := StrongSeparability.boolean_imp_stronglySeparable (α := α)
    exact stronglySeparable_imp_separable hstrong a b hsep
  · intro S
    rcases S.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    exact Subtype.ext ha.symm

theorem separatorCoreToSetFreeStars_map_rel_iff [BooleanAlgebra α] (a b : α) :
    separatorCoreToSetFreeStars (α := α) a ≤ separatorCoreToSetFreeStars (α := α) b ↔ a ≤ b := by
  constructor
  · intro h
    have hsub : separator a ⊆ separator b := by
      intro x hx
      have h' :
          separatorCoreSet (α := α) a ⊆ separatorCoreSet (α := α) b :=
        Set.le_iff_subset.mp h
      have hx' : x ∈ separatorCoreSet (α := α) a := by
        simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hx
      have hy' : x ∈ separatorCoreSet (α := α) b := h' hx'
      simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hy'
    exact StrongSeparability.boolean_imp_stronglySeparable (α := α) a b hsub
  · intro hab
    change
      separatorCoreSet (α := α) a ⊆ separatorCoreSet (α := α) b
    intro x hx
    have hx_sep : x ∈ separator a := by
      simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hx
    have hx_sep' : x ∈ separator b := le_imp_separator_subset (a := a) (b := b) hab hx_sep
    simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hx_sep'

noncomputable def separatorCoreToSetFreeStars_orderIso [BooleanAlgebra α] :
    α ≃o separatorCoreSetFreeStars (α := α) where
  toEquiv :=
    { toFun := separatorCoreToSetFreeStars (α := α)
      invFun := Function.invFun (separatorCoreToSetFreeStars (α := α))
      left_inv := Function.leftInverse_invFun (separatorCoreToSetFreeStars_bijective (α := α)).1
      right_inv := Function.rightInverse_invFun (separatorCoreToSetFreeStars_bijective (α := α)).2 }
  map_rel_iff' := by
    intro a b
    exact separatorCoreToSetFreeStars_map_rel_iff (α := α) a b

abbrev separatorCoreFreeStarRange [BooleanAlgebra α] : Type u :=
  {S : FreeStar (α := α) // ∃ a : α, separatorCoreFreeStar (α := α) a = S}

def separatorCoreToFreeStarRange [BooleanAlgebra α] (a : α) :
    separatorCoreFreeStarRange (α := α) :=
  ⟨separatorCoreFreeStar (α := α) a, ⟨a, rfl⟩⟩

theorem separatorCoreToFreeStarRange_bijective [BooleanAlgebra α] :
    Function.Bijective (separatorCoreToFreeStarRange (α := α)) := by
  constructor
  · intro a b h
    have hset :
        separatorCoreSet (α := α) a = separatorCoreSet (α := α) b := by
      have h' :
          (separatorCoreFreeStar (α := α) a).elements =
            (separatorCoreFreeStar (α := α) b).elements :=
        congrArg (fun S => S.1.elements) h
      simpa [separatorCoreFreeStar] using h'
    have hsep : separator a = separator b := by
      simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hset
    have hstrong : IsStronglySeparable α := StrongSeparability.boolean_imp_stronglySeparable (α := α)
    exact stronglySeparable_imp_separable hstrong a b hsep
  · intro S
    rcases S.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    exact Subtype.ext ha

theorem separatorCoreToFreeStarRange_map_rel_iff [BooleanAlgebra α] (a b : α) :
    separatorCoreToFreeStarRange (α := α) a ≤ separatorCoreToFreeStarRange (α := α) b ↔ a ≤ b := by
  constructor
  · intro h
    have hsub :
        separatorCoreSet (α := α) a ⊆ separatorCoreSet (α := α) b := by
      intro x hx
      exact h hx
    have hsep : separator a ⊆ separator b := by
      intro x hx
      have hx' : x ∈ separatorCoreSet (α := α) a := by
        simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hx
      have hy' : x ∈ separatorCoreSet (α := α) b := hsub hx'
      simpa [separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hy'
    exact StrongSeparability.boolean_imp_stronglySeparable (α := α) a b hsep
  · intro hab
    change
      (separatorCoreFreeStar (α := α) a).elements ⊆ (separatorCoreFreeStar (α := α) b).elements
    intro x hx
    have hx_sep : x ∈ separator a := by
      simpa [separatorCoreFreeStar, separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hx
    have hx_sep' : x ∈ separator b := le_imp_separator_subset (a := a) (b := b) hab hx_sep
    simpa [separatorCoreFreeStar, separatorCoreSet, separator_core, Filtrator.of_subset, Set.univ_inter] using hx_sep'

noncomputable def separatorCoreToFreeStarRange_orderIso [BooleanAlgebra α] :
    α ≃o separatorCoreFreeStarRange (α := α) where
  toEquiv :=
    { toFun := separatorCoreToFreeStarRange (α := α)
      invFun := Function.invFun (separatorCoreToFreeStarRange (α := α))
      left_inv := Function.leftInverse_invFun (separatorCoreToFreeStarRange_bijective (α := α)).1
      right_inv := Function.rightInverse_invFun (separatorCoreToFreeStarRange_bijective (α := α)).2 }
  map_rel_iff' := by
    intro a b
    exact separatorCoreToFreeStarRange_map_rel_iff (α := α) a b

lemma orderIso_mem_separator_iff {β : Type u} [PartialOrder β]
    [BooleanAlgebra α] (e : α ≃o β) (x a : α) :
    x ∈ separator a ↔ e x ∈ separator (e a) := by
  constructor
  · intro hx
    rcases hx with ⟨c, hcx, hca, hnot⟩
    refine ⟨e c, (e.map_rel_iff).2 hcx, (e.map_rel_iff).2 hca, ?_⟩
    intro hleast
    apply hnot
    intro y
    exact (e.map_rel_iff).1 (hleast (e y))
  · intro hx
    rcases hx with ⟨c, hcx, hca, hnot⟩
    refine ⟨e.symm c, ?_, ?_, ?_⟩
    · simpa using (e.symm.map_rel_iff).2 hcx
    · simpa using (e.symm.map_rel_iff).2 hca
    intro hleast
    apply hnot
    intro y
    exact (e.symm.map_rel_iff).1 (hleast (e.symm y))

theorem separatorCoreFreeStarRange_stronglySeparable [BooleanAlgebra α] :
    IsStronglySeparable (separatorCoreFreeStarRange (α := α)) := by
  let e : α ≃o separatorCoreFreeStarRange (α := α) :=
    separatorCoreToFreeStarRange_orderIso (α := α)
  have hα : IsStronglySeparable α :=
    StrongSeparability.boolean_imp_stronglySeparable (α := α)
  intro A B hsub
  have hsub' : separator (e.symm A) ⊆ separator (e.symm B) := by
    intro x hx
    have hxA : e x ∈ separator A := by
      simpa using
        (orderIso_mem_separator_iff
          (α := α) (β := separatorCoreFreeStarRange (α := α))
          (e := e) (x := x) (a := e.symm A)).1 hx
    have hxB : e x ∈ separator B := hsub hxA
    exact
      (orderIso_mem_separator_iff
        (α := α) (β := separatorCoreFreeStarRange (α := α))
        (e := e) (x := x) (a := e.symm B)).2 (by simpa using hxB)
  have hle : e.symm A ≤ e.symm B := hα (e.symm A) (e.symm B) hsub'
  exact (e.symm.map_rel_iff).1 hle

theorem separatorCoreFreeStarRange_strongly_star_separable [BooleanAlgebra α] :
    Filtrator.strongly_star_separable
      (Filtrator.of_subset (Set.univ : Set (separatorCoreFreeStarRange (α := α)))) := by
  exact is_stronglySeparable_imp_strongly_star_sep
    (separatorCoreFreeStarRange_stronglySeparable (α := α))

end SeparatorCoreFreeStars

export SeparatorCoreFreeStars
  (separatorCoreSet separatorCoreFreeStar
    separatorCoreSetFreeStars separatorCoreToSetFreeStars
    separatorCoreToSetFreeStars_bijective separatorCoreToSetFreeStars_orderIso
    separatorCoreFreeStarRange separatorCoreToFreeStarRange
    separatorCoreToFreeStarRange_bijective separatorCoreToFreeStarRange_orderIso
    separatorCoreFreeStarRange_stronglySeparable
    separatorCoreFreeStarRange_strongly_star_separable)

lemma exists_not_mem_of_ne_univ {F : Set α} (hne : F ≠ Set.univ) : ∃ x : α, x ∉ F := by
  classical
  by_contra h
  apply hne
  ext x
  constructor
  · intro hx
    trivial
  · intro _
    by_contra hx
    exact h ⟨x, hx⟩

theorem filter_upperSet [PartialOrder α]
    (h : FilterSet (U := (inferInstance : PartialOrder α))) :
    IsUpperSet h.elements := by
  intro a b hle ha
  rcases (h.cap_elements (x := a) (y := a)).1 ⟨ha, ha⟩ with ⟨z, hz, hza, _⟩
  have hzb : z ≤ b := le_trans hza hle
  exact ((h.cap_elements (x := z) (y := b)).2 ⟨z, hz, le_rfl, hzb⟩).2

theorem ideal_lowerSet [PartialOrder α] (h : IdealSet (α := α)) : IsLowerSet h.elements := by
  intro a b hba ha
  rcases h.non_empty with ⟨x, hx⟩
  rcases (h.cup_elements (a := a) (b := x)).1 ⟨ha, hx⟩ with ⟨z, hz, haz, hxz⟩
  have hw : ∃ w : α, w ∈ h.elements ∧ b ≤ w ∧ x ≤ w := ⟨z, hz, le_trans hba haz, hxz⟩
  exact ((h.cup_elements (a := b) (b := x)).2 hw).1

theorem freeStar_upperSet [PartialOrder α] (h : FreeStar (α := α)) : IsUpperSet h.elements := by
  intro a b hle ha
  by_contra hb
  rcases exists_not_mem_of_ne_univ (hne := h.non_univ) with ⟨x, hx⟩
  rcases (h.cup_not_elements (a := x) (b := b)).1 ⟨hx, hb⟩ with ⟨z, hz, hxz, hbz⟩
  have haz : a ≤ z := le_trans hle hbz
  have hw : ∃ w : α, w ∉ h.elements ∧ a ≤ w ∧ x ≤ w := ⟨z, hz, haz, hxz⟩
  exact ((h.cup_not_elements (a := a) (b := x)).2 hw).1 ha

theorem mixer_lowerSet [PartialOrder α] (h : Mixer (α := α)) : IsLowerSet h.elements := by
  intro a b hba ha
  by_contra hb
  rcases exists_not_mem_of_ne_univ (hne := h.non_univ) with ⟨x, hx⟩
  rcases (h.cap_not_elements (a := x) (b := b)).1 ⟨hx, hb⟩ with ⟨z, hz, hzx, hzb⟩
  have hza : z ≤ a := le_trans hzb hba
  have hw : ∃ w : α, w ∉ h.elements ∧ w ≤ a ∧ w ≤ x := ⟨z, hz, hza, hzx⟩
  exact ((h.cap_not_elements (a := a) (b := x)).2 hw).1 ha

section Semilattices

theorem filter_inf_mem_iff [SemilatticeInf α]
    (h : FilterSet (U := (inferInstance : PartialOrder α))) (a b : α) :
    a ⊓ b ∈ h.elements ↔ a ∈ h.elements ∧ b ∈ h.elements := by
  have hupper : IsUpperSet h.elements := filter_upperSet h
  constructor
  · intro hab
    exact ⟨hupper inf_le_left hab, hupper inf_le_right hab⟩
  · intro hab
    rcases (h.cap_elements (x := a) (y := b)).1 hab with ⟨z, hz, hza, hzb⟩
    exact hupper (le_inf hza hzb) hz

theorem ideal_sup_mem_iff [SemilatticeSup α] (h : IdealSet (α := α)) (a b : α) :
    a ⊔ b ∈ h.elements ↔ a ∈ h.elements ∧ b ∈ h.elements := by
  have hlower : IsLowerSet h.elements := ideal_lowerSet h
  constructor
  · intro hab
    exact ⟨hlower (le_sup_left) hab, hlower (le_sup_right) hab⟩
  · intro hab
    rcases (h.cup_elements (a := a) (b := b)).1 hab with ⟨z, hz, haz, hbz⟩
    exact hlower (sup_le haz hbz) hz

theorem freeStar_sup_not_mem_iff [SemilatticeSup α] (h : FreeStar (α := α)) (a b : α) :
    a ⊔ b ∉ h.elements ↔ a ∉ h.elements ∧ b ∉ h.elements := by
  constructor
  · intro hab
    rcases (h.cup_not_elements (a := a ⊔ b) (b := a ⊔ b)).1 ⟨hab, hab⟩ with ⟨z, hz, hsz, _⟩
    have hw : ∃ w : α, w ∉ h.elements ∧ a ≤ w ∧ b ≤ w :=
      ⟨z, hz, le_trans le_sup_left hsz, le_trans le_sup_right hsz⟩
    exact (h.cup_not_elements (a := a) (b := b)).2 hw
  · intro hab
    rcases (h.cup_not_elements (a := a) (b := b)).1 hab with ⟨z, hz, haz, hbz⟩
    have hsupz : a ⊔ b ≤ z := sup_le haz hbz
    have hw : ∃ w : α, w ∉ h.elements ∧ a ⊔ b ≤ w ∧ a ⊔ b ≤ w := ⟨z, hz, hsupz, hsupz⟩
    exact ((h.cup_not_elements (a := a ⊔ b) (b := a ⊔ b)).2 hw).1

theorem freeStar_sup_mem_iff [SemilatticeSup α] (h : FreeStar (α := α)) (a b : α) :
    a ⊔ b ∈ h.elements ↔ a ∈ h.elements ∨ b ∈ h.elements := by
  constructor
  · intro hab
    by_contra h_or
    have h_not : a ∉ h.elements ∧ b ∉ h.elements := by
      simpa [not_or] using h_or
    exact (freeStar_sup_not_mem_iff h a b).2 h_not hab
  · intro hab
    by_contra hsup
    have h_not : a ∉ h.elements ∧ b ∉ h.elements := (freeStar_sup_not_mem_iff h a b).1 hsup
    cases hab with
    | inl ha => exact h_not.1 ha
    | inr hb => exact h_not.2 hb

theorem mixer_inf_not_mem_iff [SemilatticeInf α] (h : Mixer (α := α)) (a b : α) :
    a ⊓ b ∉ h.elements ↔ a ∉ h.elements ∧ b ∉ h.elements := by
  constructor
  · intro hab
    rcases (h.cap_not_elements (a := a ⊓ b) (b := a ⊓ b)).1 ⟨hab, hab⟩ with ⟨z, hz, hzs, _⟩
    have hw : ∃ w : α, w ∉ h.elements ∧ w ≤ a ∧ w ≤ b :=
      ⟨z, hz, le_trans hzs inf_le_left, le_trans hzs inf_le_right⟩
    exact (h.cap_not_elements (a := a) (b := b)).2 hw
  · intro hab
    rcases (h.cap_not_elements (a := a) (b := b)).1 hab with ⟨z, hz, hza, hzb⟩
    have hzinf : z ≤ a ⊓ b := le_inf hza hzb
    have hw : ∃ w : α, w ∉ h.elements ∧ w ≤ a ⊓ b ∧ w ≤ a ⊓ b := ⟨z, hz, hzinf, hzinf⟩
    exact ((h.cap_not_elements (a := a ⊓ b) (b := a ⊓ b)).2 hw).1

theorem mixer_inf_mem_iff [SemilatticeInf α] (h : Mixer (α := α)) (a b : α) :
    a ⊓ b ∈ h.elements ↔ a ∈ h.elements ∨ b ∈ h.elements := by
  constructor
  · intro hab
    by_contra h_or
    have h_not : a ∉ h.elements ∧ b ∉ h.elements := by
      simpa [not_or] using h_or
    exact (mixer_inf_not_mem_iff h a b).2 h_not hab
  · intro hab
    by_contra hinf
    have h_not : a ∉ h.elements ∧ b ∉ h.elements := (mixer_inf_not_mem_iff h a b).1 hinf
    cases hab with
    | inl ha => exact h_not.1 ha
    | inr hb => exact h_not.2 hb

theorem filter_upper_inf_mem_of_pair
    [SemilatticeInf α] (h : FilterSet (U := (inferInstance : PartialOrder α))) :
    IsUpperSet h.elements ∧ ∀ a b : α, a ∈ h.elements ∧ b ∈ h.elements → a ⊓ b ∈ h.elements := by
  refine ⟨filter_upperSet h, ?_⟩
  intro a b hab
  exact (filter_inf_mem_iff h a b).2 hab

theorem ideal_lower_sup_mem_of_pair
    [SemilatticeSup α] (h : IdealSet (α := α)) :
    IsLowerSet h.elements ∧ ∀ a b : α, a ∈ h.elements ∧ b ∈ h.elements → a ⊔ b ∈ h.elements := by
  refine ⟨ideal_lowerSet h, ?_⟩
  intro a b hab
  exact (ideal_sup_mem_iff h a b).2 hab

theorem freeStar_upper_sup_imp_or
    [SemilatticeSup α] (h : FreeStar (α := α)) :
    IsUpperSet h.elements ∧ h.elements ≠ Set.univ ∧
      ∀ a b : α, a ⊔ b ∈ h.elements → a ∈ h.elements ∨ b ∈ h.elements := by
  refine ⟨freeStar_upperSet h, h.non_univ, ?_⟩
  intro a b hab
  exact (freeStar_sup_mem_iff h a b).1 hab

theorem mixer_lower_inf_imp_or
    [SemilatticeInf α] (h : Mixer (α := α)) :
    IsLowerSet h.elements ∧ h.elements ≠ Set.univ ∧
      ∀ a b : α, a ⊓ b ∈ h.elements → a ∈ h.elements ∨ b ∈ h.elements := by
  refine ⟨mixer_lowerSet h, h.non_univ, ?_⟩
  intro a b hab
  exact (mixer_inf_mem_iff h a b).1 hab

end Semilattices

namespace PrincipalConstructions

variable (α : Type u) [BooleanAlgebra α]

def filterSet_principal (a : α) : FilterSet (U := (inferInstance : PartialOrder α)) :=
  PosetFilter.toThroughEquiv (PosetFilter.principal (U := (inferInstance : PartialOrder α)) a)

def freeStar_principal (a : α) : FreeStar (α := α) :=
  filterSet_to_freeStar (filterSet_principal α a)

def freeStar_principals : Set (FreeStar (α := α)) :=
  { freeStar_principal α a | a : α }

def freeStar_filtrator : Filtrator (FreeStar (α := α)) :=
  Filtrator.of_subset (freeStar_principals α)

def freeStar_filtrator_primary : Filtrator.Primary (FreeStar (α := α)) := by
  refine
    { toFiltrator := freeStar_filtrator α
      is_primary := ?_ }
  refine ⟨_, (inferInstance : PartialOrder α), ?_⟩
  let comp : PosetFilter (U := (inferInstance : PartialOrder α)) ≃o FreeStar (α := α) :=
    ((filterSetOrderIsoPosetFilter (α := α)).symm.trans
      (freeStarOrderIsoFilterSet (α := α)).symm)
  have hcomp_eval (F : PosetFilter (U := (inferInstance : PartialOrder α))) :
      comp F = filterSet_to_freeStar (PosetFilter.toThroughEquiv F) := by
    rfl
  refine ⟨{ toRelIso := comp, core_match := ?_ }⟩
  change comp.toFun '' Principals (U := (inferInstance : PartialOrder α)) =
    freeStar_principals α
  ext F
  constructor
  · intro hF
    rcases hF with ⟨G, hG, rfl⟩
    rcases hG with ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp [hcomp_eval, freeStar_principal, filterSet_principal]
  · intro hF
    rcases hF with ⟨a, rfl⟩
    refine ⟨PosetFilter.principal (U := (inferInstance : PartialOrder α)) a, ⟨a, rfl⟩, ?_⟩
    simp [hcomp_eval, freeStar_principal, filterSet_principal]

theorem freeStar_filtrator_is_primary :
    ∃ hprim : Filtrator.Primary.{u, u} (FreeStar (α := α)),
      hprim.toFiltrator = freeStar_filtrator α := by
  exact ⟨freeStar_filtrator_primary (α := α), rfl⟩

-- TODO: Don't have it as a separate lemma.
theorem freeStar_filtrator_strongly_star_separable_of_bridge
    (hbridge :
      ∀ a : α, ∀ S : FreeStar (α := α),
        freeStar_principal α a ∈ separator_core (F := freeStar_filtrator α) S ↔
          a ∈ S.elements) :
    Filtrator.strongly_star_separable (freeStar_filtrator α) := by
  intro S T hsub a haS
  have ha_coreS :
      freeStar_principal α a ∈ separator_core (F := freeStar_filtrator α) S :=
    (hbridge a S).2 haS
  have ha_coreT :
      freeStar_principal α a ∈ separator_core (F := freeStar_filtrator α) T :=
    hsub ha_coreS
  exact (hbridge a T).1 ha_coreT

lemma freeStar_to_filterSet_mem_separator_iff
    (X S : FreeStar (α := α)) :
    X ∈ separator S ↔
      freeStar_to_filterSet X ∈ separator (freeStar_to_filterSet S) := by
  constructor
  · intro h
    rcases h with ⟨C, hCX, hCS, hnotleastC⟩
    refine ⟨freeStar_to_filterSet C, ?_, ?_, ?_⟩
    · exact (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.2 hCX
    · exact (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.2 hCS
    · intro hleastFC
      apply hnotleastC
      intro D
      have hCD : freeStar_to_filterSet C ≤ freeStar_to_filterSet D := hleastFC (freeStar_to_filterSet D)
      exact (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.1 hCD
  · intro h
    rcases h with ⟨D, hDX, hDS, hnotleastD⟩
    refine ⟨filterSet_to_freeStar D, ?_, ?_, ?_⟩
    · have hDX' :
        freeStar_to_filterSet (filterSet_to_freeStar D) ≤ freeStar_to_filterSet X := by
        simpa [filterSet_to_freeStar_left_inv] using hDX
      exact (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.1 hDX'
    · have hDS' :
        freeStar_to_filterSet (filterSet_to_freeStar D) ≤ freeStar_to_filterSet S := by
        simpa [filterSet_to_freeStar_left_inv] using hDS
      exact (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.1 hDS'
    · intro hleastC
      apply hnotleastD
      intro E
      have hCE : filterSet_to_freeStar D ≤ filterSet_to_freeStar E := hleastC (filterSet_to_freeStar E)
      have hCE' :
          freeStar_to_filterSet (filterSet_to_freeStar D) ≤
            freeStar_to_filterSet (filterSet_to_freeStar E) :=
        (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.2 hCE
      simpa [filterSet_to_freeStar_left_inv] using hCE'

lemma filterSet_principal_mem_separator_iff_not_compl_mem
    (a : α) (F : FilterSet (U := (inferInstance : PartialOrder α))) :
    filterSet_principal α a ∈ separator F ↔ aᶜ ∉ F.elements := by
  constructor
  · intro hsep
    change meet (filterSet_principal α a) F at hsep
    intro hacF
    rcases hsep with ⟨C, hCP, hCF, hnotleast⟩
    have haP : a ∈ (filterSet_principal α a).elements := by
      simp [filterSet_principal, PosetFilter.toThroughEquiv, PosetFilter.principal]
    have haC : a ∈ C.elements := hCP haP
    have hacC : aᶜ ∈ C.elements := hCF hacF
    rcases (C.cap_elements (x := a) (y := aᶜ)).1 ⟨haC, hacC⟩ with ⟨z, hzC, hza, hzac⟩
    have hz_bot : z = (⊥ : α) := by
      apply le_antisymm
      · have hz_le : z ≤ a ⊓ aᶜ := le_inf hza hzac
        simpa using hz_le
      · exact bot_le
    have hupperC : IsUpperSet C.elements := filter_upperSet C
    have hbotC : (⊥ : α) ∈ C.elements := hz_bot ▸ hzC
    have hleastC : is_least C := by
      intro D
      change D.elements ⊆ C.elements
      intro x hxD
      exact hupperC bot_le hbotC
    exact hnotleast hleastC
  · intro hac_not
    change meet (filterSet_principal α a) F
    let Fp : PosetFilter (U := (inferInstance : PartialOrder α)) :=
      PosetFilter.ThroughEquiv.toPosetFilter F
    let B : PosetFilterBase (U := (inferInstance : PartialOrder α)) :=
      meet_filter_base a Fp.toPosetFilterBase
    let Cpf : PosetFilter (U := (inferInstance : PartialOrder α)) :=
      close_filter_base B
    let C : FilterSet (U := (inferInstance : PartialOrder α)) :=
      PosetFilter.toThroughEquiv Cpf
    have hC_mem_Fp (x : α) :
        x ∈ C.elements ↔ ∃ s ∈ Fp.elements, a ⊓ s ≤ x := by
      simp [C, Cpf, B, meet_filter_base, FilterBaseMeet.meet_filter_base_set,
        close_filter_base, PosetFilter.toThroughEquiv]
    have hC_mem (x : α) :
        x ∈ C.elements ↔ ∃ s ∈ F.elements, a ⊓ s ≤ x := by
      simpa [Fp] using hC_mem_Fp x
    have hC_le_P : C ≤ filterSet_principal α a := by
      intro x hxP
      rcases F.non_empty with ⟨s, hs⟩
      exact (hC_mem x).2 ⟨s, hs, le_trans inf_le_left hxP⟩
    have hC_le_F : C ≤ F := by
      intro x hxF
      exact (hC_mem x).2 ⟨x, hxF, inf_le_right⟩
    have hC_not_least : ¬ is_least C := by
      intro hleastC
      have hC_le_bot : C ≤ filterSet_principal α (⊥ : α) := hleastC _
      have hacC : aᶜ ∈ C.elements := by
        apply hC_le_bot
        simp [filterSet_principal, PosetFilter.toThroughEquiv, PosetFilter.principal]
      rcases (hC_mem (aᶜ)).1 hacC with ⟨s, hsF, hs_le⟩
      have hs_inf_bot : a ⊓ s = (⊥ : α) := by
        apply le_antisymm
        · have hs_le_inf : a ⊓ s ≤ a ⊓ aᶜ := le_inf inf_le_left hs_le
          simpa using hs_le_inf
        · exact bot_le
      have hs_disj : Disjoint s a :=
        disjoint_iff.mpr (by simpa [inf_comm] using hs_inf_bot)
      have hs_le_compl : s ≤ aᶜ := (le_compl_iff_disjoint_right).2 hs_disj
      have hupperF : IsUpperSet F.elements := filter_upperSet F
      have hacF : aᶜ ∈ F.elements := hupperF hs_le_compl hsF
      exact hac_not hacF
    exact ⟨C, hC_le_P, hC_le_F, hC_not_least⟩

lemma compl_mem_freeStar_to_filterSet_iff_not_mem
    (a : α) (S : FreeStar (α := α)) :
    aᶜ ∈ (freeStar_to_filterSet S).elements ↔ a ∉ S.elements := by
  constructor
  · intro hac
    rcases hac with ⟨y, hy, hy_eq⟩
    have hy_not : y ∉ S.elements := by
      simpa [Set.mem_compl_iff] using hy
    have hy_a : y = a := by
      have h := congrArg compl hy_eq
      simpa using h
    exact hy_a ▸ hy_not
  · intro ha
    refine ⟨a, ?_, by simp⟩
    simpa [Set.mem_compl_iff] using ha

theorem freeStar_filtrator_bridge
    (a : α) (S : FreeStar (α := α)) :
    freeStar_principal α a ∈ separator_core (F := freeStar_filtrator α) S ↔
      a ∈ S.elements := by
  have h_princ_map :
      freeStar_to_filterSet (freeStar_principal α a) = filterSet_principal α a := by
    calc
      freeStar_to_filterSet (freeStar_principal α a)
          = freeStar_to_filterSet (filterSet_to_freeStar (filterSet_principal α a)) := by
            simp [freeStar_principal]
      _ = filterSet_principal α a := filterSet_to_freeStar_left_inv (filterSet_principal α a)
  constructor
  · intro h
    have hsep : freeStar_principal α a ∈ separator S := h.2
    have hsepF' :
        freeStar_to_filterSet (freeStar_principal α a) ∈
          separator (freeStar_to_filterSet S) :=
      (freeStar_to_filterSet_mem_separator_iff (α := α)
        (X := freeStar_principal α a) (S := S)).1 hsep
    have hsepF : filterSet_principal α a ∈ separator (freeStar_to_filterSet S) := by
      simpa [h_princ_map] using hsepF'
    have hnot_compl : aᶜ ∉ (freeStar_to_filterSet S).elements :=
      (filterSet_principal_mem_separator_iff_not_compl_mem (α := α)
        a (freeStar_to_filterSet S)).1 hsepF
    by_contra ha_not
    exact hnot_compl ((compl_mem_freeStar_to_filterSet_iff_not_mem (α := α) a S).2 ha_not)
  · intro ha
    have hnot_compl : aᶜ ∉ (freeStar_to_filterSet S).elements := by
      intro hac
      exact ((compl_mem_freeStar_to_filterSet_iff_not_mem (α := α) a S).1 hac) ha
    have hsepF : filterSet_principal α a ∈ separator (freeStar_to_filterSet S) :=
      (filterSet_principal_mem_separator_iff_not_compl_mem (α := α)
        a (freeStar_to_filterSet S)).2 hnot_compl
    have hsepF' :
        freeStar_to_filterSet (freeStar_principal α a) ∈
          separator (freeStar_to_filterSet S) := by
      simpa [h_princ_map] using hsepF
    have hsep : freeStar_principal α a ∈ separator S :=
      (freeStar_to_filterSet_mem_separator_iff (α := α)
        (X := freeStar_principal α a) (S := S)).2 hsepF'
    exact ⟨⟨a, rfl⟩, hsep⟩

theorem freeStar_filtrator_strongly_star_separable
    : Filtrator.strongly_star_separable (freeStar_filtrator α) := by
  exact freeStar_filtrator_strongly_star_separable_of_bridge (α := α)
    (fun a S => freeStar_filtrator_bridge (α := α) a S)

theorem filterSet_principal_has_min (a : α) :
    ∃ z ∈ (filterSet_principal α a).elements, ∀ p ∈ (filterSet_principal α a).elements, z ≤ p := by
  refine ⟨a, ?_, ?_⟩
  · simp [filterSet_principal, PosetFilter.toThroughEquiv, PosetFilter.principal]
  · intro p hp
    simp [filterSet_principal, PosetFilter.toThroughEquiv, PosetFilter.principal] at hp
    exact hp

theorem freeStar_to_filterSet_freeStar_principal (a : α) :
    freeStar_to_filterSet (freeStar_principal α a) = filterSet_principal α a := by
  calc
    freeStar_to_filterSet (freeStar_principal α a)
        = freeStar_to_filterSet (filterSet_to_freeStar (filterSet_principal α a)) := by
          simp [freeStar_principal]
    _ = filterSet_principal α a := filterSet_to_freeStar_left_inv (filterSet_principal α a)

theorem filterSet_to_freeStar_filterSet_principal (a : α) :
    filterSet_to_freeStar (filterSet_principal α a) = freeStar_principal α a := rfl

lemma filterSet_principal_le_iff (a b : α) :
    filterSet_principal α a ≤ filterSet_principal α b ↔ a ≤ b := by
  change
    (filterSet_principal α b).elements ⊆ (filterSet_principal α a).elements ↔ a ≤ b
  constructor
  · intro h
    exact h (by
      simp [filterSet_principal, PosetFilter.toThroughEquiv, PosetFilter.principal])
  · intro hab x hx
    exact le_trans hab (by
      simpa [filterSet_principal, PosetFilter.toThroughEquiv, PosetFilter.principal] using hx)

lemma freeStar_principal_le_iff (a b : α) :
    freeStar_principal α a ≤ freeStar_principal α b ↔ a ≤ b := by
  constructor
  · intro h
    have h' :
        freeStar_to_filterSet (freeStar_principal α a) ≤
          freeStar_to_filterSet (freeStar_principal α b) :=
      (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.2 h
    simpa [freeStar_to_filterSet_freeStar_principal, filterSet_principal_le_iff]
      using h'
  · intro hab
    have h' :
        freeStar_to_filterSet (freeStar_principal α a) ≤
          freeStar_to_filterSet (freeStar_principal α b) := by
      simpa [freeStar_to_filterSet_freeStar_principal, filterSet_principal_le_iff]
        using (filterSet_principal_le_iff (α := α) a b).2 hab
    exact (freeStarOrderIsoFilterSet (α := α)).map_rel_iff.1 h'

lemma freeStar_principal_injective :
    Function.Injective (freeStar_principal α) := by
  intro a b hab
  have hfs : filterSet_principal α a = filterSet_principal α b := by
    exact (freeStar_to_filterSet_freeStar_principal (α := α) a) ▸
      (freeStar_to_filterSet_freeStar_principal (α := α) b) ▸ congrArg freeStar_to_filterSet hab
  have hpf :
      PosetFilter.principal (U := (inferInstance : PartialOrder α)) a =
        PosetFilter.principal (U := (inferInstance : PartialOrder α)) b := by
    simpa [filterSet_principal] using congrArg
      (PosetFilter.ThroughEquiv.toPosetFilter (U := (inferInstance : PartialOrder α))) hfs
  exact (principal_injective (U := (inferInstance : PartialOrder α))) hpf

noncomputable def freeStarPrincipalOrderIso :
    α ≃o {S : FreeStar (α := α) // S ∈ freeStar_principals α} where
  toEquiv :=
    { toFun := fun a => ⟨freeStar_principal α a, ⟨a, rfl⟩⟩
      invFun := fun S => Classical.choose S.2
      left_inv := by
        intro a
        exact (freeStar_principal_injective (α := α))
          (Classical.choose_spec (⟨a, rfl⟩ : ∃ x : α, freeStar_principal α x = freeStar_principal α a))
      right_inv := by
        intro S
        apply Subtype.ext
        exact Classical.choose_spec S.2 }
  map_rel_iff' := by
    intro a b
    exact freeStar_principal_le_iff (α := α) a b

lemma orderIso_mem_separator_iff {β : Type u} [PartialOrder β]
    (e : α ≃o β) (x a : α) :
    x ∈ separator a ↔ e x ∈ separator (e a) := by
  constructor
  · intro hx
    rcases hx with ⟨c, hcx, hca, hnot⟩
    refine ⟨e c, (e.map_rel_iff).2 hcx, (e.map_rel_iff).2 hca, ?_⟩
    intro hleast
    apply hnot
    intro y
    exact (e.map_rel_iff).1 (hleast (e y))
  · intro hx
    rcases hx with ⟨c, hcx, hca, hnot⟩
    refine ⟨e.symm c, ?_, ?_, ?_⟩
    · simpa using (e.symm.map_rel_iff).2 hcx
    · simpa using (e.symm.map_rel_iff).2 hca
    intro hleast
    apply hnot
    intro y
    exact (e.symm.map_rel_iff).1 (hleast (e.symm y))

end PrincipalConstructions

export PrincipalConstructions
  (freeStar_principal freeStar_principals freeStar_filtrator
    freeStarPrincipalOrderIso)

namespace StarrishPosets

def IsFreeStarLike [SemilatticeSup α] (S : Set α) : Prop :=
  IsUpperSet S ∧ ∀ x y : α, x ⊔ y ∈ S → x ∈ S ∨ y ∈ S

def IsStarrish (α : Type u) [SemilatticeSup α] : Prop :=
  ∀ a : α, IsFreeStarLike (⋆a)

def IsCompletelyStarrish (α : Type u) [CompleteLattice α] : Prop :=
  ∀ a : α, IsFreeStarLike (⋆a) ∧ ∀ T : Set α, sSup T ∈ ⋆a ↔ ∃ x ∈ T, x ∈ ⋆a

theorem distributiveLattice_isStarrish (α : Type u) [DistribLattice α] :
    IsStarrish α := by
  intro a
  refine ⟨?_, ?_⟩
  · intro x y hxy hx
    have hx_meet : meet x a := by
      simpa [separator] using hx
    exact meet_mono_left hxy hx_meet
  · intro x y hxy
    have hxy_notleast : ¬ is_least ((x ⊔ y) ⊓ a) := (meet_as_inf (x ⊔ y) a).1 hxy
    have hxy_or : ¬ is_least (x ⊓ a) ∨ ¬ is_least (y ⊓ a) := by
      by_contra h
      push_neg at h
      have hleast_sup : is_least ((x ⊓ a) ⊔ (y ⊓ a)) := by
        intro t
        exact sup_le (h.1 t) (h.2 t)
      exact hxy_notleast (by simpa [inf_sup_right] using hleast_sup)
    rcases hxy_or with hx_notleast | hy_notleast
    · exact Or.inl ((meet_as_inf x a).2 hx_notleast)
    · exact Or.inr ((meet_as_inf y a).2 hy_notleast)

theorem atoms_sup_eq_union [DistribLattice α] [OrderBot α]
    (_hstar : IsStarrish α) (a b : α) :
    atoms (a ⊔ b) = atoms a ∪ atoms b := by
  ext c
  constructor
  · intro hc
    have hsplit : c = (c ⊓ a) ⊔ (c ⊓ b) := by
      calc
        c = c ⊓ (a ⊔ b) := (inf_eq_left.2 hc.1).symm
        _ = (c ⊓ a) ⊔ (c ⊓ b) := by simp [inf_sup_left]
    have hca_cases : c ⊓ a = ⊥ ∨ c ⊓ a = c := (IsAtom.le_iff hc.2).1 inf_le_left
    rcases hca_cases with hca | hca
    · right
      have hcb_eq : c = c ⊓ b := by simpa [hca] using hsplit
      refine ⟨?_, hc.2⟩
      exact hcb_eq ▸ (inf_le_right : c ⊓ b ≤ b)
    · left
      refine ⟨?_, hc.2⟩
      exact hca ▸ (inf_le_right : c ⊓ a ≤ a)
  · intro hc
    cases hc with
    | inl ha => exact ⟨ha.1.trans le_sup_left, ha.2⟩
    | inr hb => exact ⟨hb.1.trans le_sup_right, hb.2⟩

theorem completelyStarrish_imp_starrish [CompleteLattice α]
    (h : IsCompletelyStarrish α) : IsStarrish α := by
  intro a
  exact (h a).1

theorem atoms_sSup_eq_iUnion_atoms [CompleteDistribLattice α]
    (_h : IsCompletelyStarrish α) (T : Set α) :
    atoms (sSup T) = ⋃ x ∈ T, atoms x := by
  ext c
  constructor
  · intro hc
    rcases (IsAtom.le_sSup hc.2).1 hc.1 with ⟨x, hxT, hcx⟩
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hxT, ⟨hcx, hc.2⟩⟩⟩
  · intro hc
    rcases Set.mem_iUnion.1 hc with ⟨x, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hxT, hxc⟩
    exact ⟨(IsAtom.le_sSup hxc.2).2 ⟨x, hxT, hxc.1⟩, hxc.2⟩

theorem completeDistribLattice_isCompletelyStarrish (α : Type u) [CompleteDistribLattice α] :
    IsCompletelyStarrish α := by
  intro a
  refine ⟨(distributiveLattice_isStarrish α a), ?_⟩
  intro T
  constructor
  · intro hsSup
    by_contra h
    push_neg at h
    have hleast_x : ∀ x ∈ T, is_least (x ⊓ a) := by
      intro x hx
      apply not_not.mp
      intro hx_notleast
      exact (h x hx) ((meet_as_inf x a).2 hx_notleast)
    have hleast_sup : is_least (sSup T ⊓ a) := by
      intro t
      rw [sSup_inf_eq]
      refine iSup₂_le ?_
      intro x hx
      exact hleast_x x hx t
    exact ((meet_as_inf (sSup T) a).1 hsSup) hleast_sup
  · intro hmem
    rcases hmem with ⟨x, hxT, hxmem⟩
    exact meet_mono_left (le_sSup hxT) hxmem

end StarrishPosets

export StarrishPosets
  (IsFreeStarLike IsStarrish IsCompletelyStarrish
    distributiveLattice_isStarrish atoms_sup_eq_union
    completelyStarrish_imp_starrish atoms_sSup_eq_iUnion_atoms
    completeDistribLattice_isCompletelyStarrish)

end AlternativePrimaryFiltrators
