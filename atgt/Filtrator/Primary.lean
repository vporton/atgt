import atgt.Filtrator
import atgt.PosetFilter

instance FiltratorOfFilters {u : Type*} [inst : PartialOrder u] : Filtrator (PosetFilter inst) where
  subset := Principals (U := inst)

/- TODO: Rename? -/
class Filtrator.Primary {base: Type*} (α: Set base) extends Filtrator base where
  is_primary : ∃ β: Type*, ∃ p: PartialOrder β,
    Nonempty (FiltratorIso (FiltratorOfFilters (inst := p)) toFiltrator)
  core : subset = α

theorem Filtrator.filtered_of_filters {β : Type u} (p : PartialOrder β) :
  Filtrator.Filtered (PosetFilter p) := by
  constructor
  intro F G h_sub x hxF
  have hF_le_principal : F ≤ PosetFilter.principal (U := p) x := by
    exact (le_principal_iff_subset (U := p) F x).2 hxF
  have hprincipal_in_upF : PosetFilter.principal (U := p) x ∈ Filtrator.up F := by
    exact ⟨⟨x, rfl⟩, hF_le_principal⟩
  have hprincipal_in_upG : PosetFilter.principal (U := p) x ∈ Filtrator.up G := h_sub hprincipal_in_upF
  have hG_le_principal : G ≤ PosetFilter.principal (U := p) x := hprincipal_in_upG.2
  exact (le_principal_iff_subset (U := p) G x).1 hG_le_principal

theorem Filtrator.Filtered.of_iso {α β : Type*} [i : Filtrator α] [j : Filtrator β]
    (h : Filtrator.Filtered α) (iso : FiltratorIso i j) :
    Filtrator.Filtered β := by
  constructor
  intro x y h_sub
  have h_preimage_up : Filtrator.up (iso.toRelIso.symm x) ⊆ Filtrator.up (iso.toRelIso.symm y) := by
    intro z hz
    let w := iso.toRelIso z
    have hw_in_subset : w ∈ (subset : Set β) := by
      rw [← iso.core_match]
      exact ⟨z, hz.1, rfl⟩
    have hx_le_w : x ≤ w := by
      have hx_pre : iso.toRelIso.symm x ≤ z := hz.2
      have hx_map : iso.toRelIso (iso.toRelIso.symm x) ≤ iso.toRelIso z :=
        (iso.toRelIso.map_rel_iff).2 hx_pre
      simpa [w] using hx_map
    have hy_le_w : y ≤ w := (h_sub ⟨hw_in_subset, hx_le_w⟩).2
    have hy_pre : iso.toRelIso.symm y ≤ z := by
      have hy_pre' : iso.toRelIso.symm y ≤ iso.toRelIso.symm w :=
        (iso.toRelIso.symm.map_rel_iff).2 hy_le_w
      simpa [w] using hy_pre'
    exact ⟨hz.1, hy_pre⟩
  have hyx_pre : iso.toRelIso.symm y ≤ iso.toRelIso.symm x := h.is_filtered _ _ h_preimage_up
  exact (iso.toRelIso.symm.map_rel_iff).1 hyx_pre

theorem Filtrator.primary_imp_filtered {base: Type*} (α: Set base) [Filtrator.Primary α] :
    Filtrator.Filtered base := by
  rcases (‹Filtrator.Primary α›).is_primary with ⟨β, p, ⟨iso⟩⟩
  exact Filtrator.Filtered.of_iso (h := Filtrator.filtered_of_filters p) iso

theorem Filtrator.isomorphicToPrimary_imp_filtered {base: Type*} [i : Filtrator base]
    (h : ∃ (β : Set Type*) (hprim : Filtrator.Primary β),
      Nonempty (FiltratorIso (Filtrator.Primary.toFiltrator (self := hprim)) i)) :
    Filtrator.Filtered base := by
  rcases h with ⟨β, hprim, ⟨iso⟩⟩
  letI : Filtrator.Primary β := hprim
  exact Filtrator.Filtered.of_iso (h := Filtrator.primary_imp_filtered (α := β)) iso

namespace Filtrator.Primary

open Filtrator

variable {base : Type u}
variable {α : Set base}

section primary_core
variable [Primary α]

theorem order_determined (a b : base) : a ≤ b ↔ up b ⊆ up a := by
  let h_filtered := Filtrator.primary_imp_filtered (α := α)
  constructor
  · intro hab y hy
    exact ⟨hy.1, le_trans hab hy.2⟩
  · intro h_sub
    exact h_filtered.is_filtered _ _ h_sub

theorem exists_up_in_subset (x : base) : ∃ y : subset, x ≤ y.1 := by
  have ⟨β, p, ⟨iso⟩⟩ := (‹Primary α›).is_primary
  -- iso : FiltratorIso (FiltratorOfFilters p) i
  let iso_inv := iso.symm
  let F := iso_inv x
  obtain ⟨b, hb⟩ := F.non_empty
  have h_sub : iso.toFun (PosetFilter.principal b) ∈ subset := by
    rw [← iso.core_match]
    use PosetFilter.principal b
    exact ⟨⟨b, rfl⟩, rfl⟩
  use ⟨iso.toFun (PosetFilter.principal b), h_sub⟩
  have hp : iso.symm x ≤ iso.symm (iso.toFun (PosetFilter.principal b)) := by
    change iso.invFun x ≤ iso.invFun (iso.toFun _)
    rw [iso.left_inv]
    change F ≤ PosetFilter.principal b
    -- PosetFilter order: G ≤ H ↔ H ⊆ G
    -- F ≤ principal b ↔ principal b ⊆ F ↔ b ∈ F
    intro z hz
    have hb' : b ∈ F.carrier := by simpa using hb
    have hz' : b ≤ z := by simpa using hz
    have : z ∈ F.carrier := F.upper' hz' hb'
    simpa using this
  exact iso.symm.map_rel_iff.mp hp

theorem directed_up_in_subset (x : base) (a b : subset) (ha : x ≤ a.1) (hb : x ≤ b.1) :
    ∃ c : subset, x ≤ c.1 ∧ c.1 ≤ a.1 ∧ c.1 ≤ b.1 := by
  have ⟨β, p, ⟨iso⟩⟩ := (‹Primary α›).is_primary
  let iso_inv := iso.symm
  -- Using iso.symm directly to avoid let-unfolding issues in rw
  have ha' : iso.symm x ≤ iso.symm a.1 := iso.symm.map_rel_iff.mpr ha
  have hb' : iso.symm x ≤ iso.symm b.1 := iso.symm.map_rel_iff.mpr hb

  have ⟨pa, hpa⟩ : ∃ pa, iso.symm a.1 = PosetFilter.principal pa := by
    have : a.1 ∈ iso.toFun '' Principals (U := p) := by
      erw [iso.core_match]; exact a.2
    obtain ⟨F, hF_princ, hF_eq⟩ := this
    obtain ⟨xF, hxF⟩ := hF_princ
    use xF
    rw [← hF_eq]
    change iso.invFun (iso.toFun F) = _
    rw [iso.left_inv F]
    symm; exact hxF

  have ⟨pb, hpb⟩ : ∃ pb, iso.symm b.1 = PosetFilter.principal pb := by
    have : b.1 ∈ iso.toFun '' Principals (U := p) := by
      erw [iso.core_match]; exact b.2
    obtain ⟨F, hF_princ, hF_eq⟩ := this
    obtain ⟨xF, hxF⟩ := hF_princ
    use xF
    rw [← hF_eq]
    change iso.invFun (iso.toFun F) = _
    rw [iso.left_inv F]
    symm; exact hxF

  rw [hpa] at ha'
  rw [hpb] at hb'

  -- F (iso_inv x) is a filter.
  -- iso_inv x ≤ principal pa ↔ principal pa ⊆ iso_inv x ↔ pa ∈ iso_inv x.
  have pa_in_F : pa ∈ (iso_inv x).elements := ha' (le_refl _)
  have pb_in_F : pb ∈ (iso_inv x).elements := hb' (le_refl _)

  obtain ⟨pc, hpc, hpc_le_a, hpc_le_b⟩ := (iso_inv x).cap_elements pa_in_F pb_in_F

  let c_val := iso.toFun (PosetFilter.principal pc)
  have c_in_subset : c_val ∈ subset := by
    rw [← iso.core_match]
    use PosetFilter.principal pc
    exact ⟨⟨pc, rfl⟩, rfl⟩

  use ⟨iso.toFun (PosetFilter.principal pc), c_in_subset⟩
  constructor
  . apply iso.symm.map_rel_iff.mp
    change iso.invFun x ≤ iso.invFun (iso.toFun _); rw [iso.left_inv]
    intro z hz
    have hpc' : pc ∈ (iso.symm x).carrier := by simpa using hpc
    have hz' : pc ≤ z := by simpa using hz
    have : z ∈ (iso.symm x).carrier := (iso.symm x).upper' hz' hpc'
    simpa using this
  . constructor
    . change iso.toFun (PosetFilter.principal pc) ≤ a.1; apply iso.symm.map_rel_iff.mp
      rw [hpa]
      change iso.invFun (iso.toFun _) ≤ _; rw [iso.left_inv]
      intro z hz; refine le_trans hpc_le_a hz
    . apply iso.symm.map_rel_iff.mp; rw [hpb]
      change iso.invFun (iso.toFun _) ≤ _; rw [iso.left_inv]
      intro z hz; refine le_trans hpc_le_b hz

attribute [local instance] Filtrator.suborder

def to_poset_filter (x : base) : PosetFilter (Filtrator.suborder (α := base)) :=
  { elements := Filtrator.up_suborder (x := x)
    non_empty := by
      rcases exists_up_in_subset (α := α) x with ⟨y, hy⟩
      exact ⟨y, hy⟩
    cap_elements := fun {a b} ha hb => by
      exact directed_up_in_subset x a b ha hb
    carrier := Filtrator.up_suborder (x := x)
    upper' := fun {a b} hab ha => by
      exact le_trans ha hab
    carrier_eq_elements := rfl }

def up_is_filter (x : base) :
    PosetFilter (Filtrator.suborder (α := base)) :=
  -- Obvious 461, first direction: the upper set of any core element is a filter.
  to_poset_filter x

/-- The canonical map from α to filters on its suborder. -/
noncomputable def to_filters_iso :
    FiltratorIso (Filtrator.Primary.toFiltrator (self := ‹Primary α›))
      (FiltratorOfFilters (inst := Filtrator.suborder (α := base))) := by
  let h_prim := (‹Primary α›).is_primary
  let β := Classical.choose h_prim
  let h_prim_beta := Classical.choose_spec h_prim
  let p := Classical.choose h_prim_beta
  let iso_nonempty := Classical.choose_spec h_prim_beta
  let iso := Classical.choice iso_nonempty

  -- The isomorphism between base posets p and suborder
  let sub_iso_toFun (x : β) : subset :=
    ⟨iso.toRelIso (PosetFilter.principal (U := p) x), by
      rw [← iso.core_match]
      use PosetFilter.principal (U := p) x
      exact ⟨⟨x, rfl⟩, rfl⟩⟩

  let sub_iso : β ≃o (subset : Type u) := {
    toFun := sub_iso_toFun
    invFun := fun ⟨y, hy⟩ =>
      -- y ∈ subset. iso.symm y ∈ Principals p.
      have h_ex : ∃ x : β, PosetFilter.principal (U := p) x = iso.toRelIso.symm y := by
        rw [← iso.core_match] at hy
        rcases hy with ⟨F, hF_princ, hF_eq⟩
        rw [← hF_eq]
        rcases hF_princ with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [hx]
        simp
      Classical.choose h_ex
    left_inv := fun x => by
      dsimp
      simp [sub_iso_toFun]
      apply (principal_injective (U := p))
      have witness := Classical.choose_spec
        (show ∃ x' : β,
            PosetFilter.principal (U := p) x' =
              iso.toRelIso.symm (iso.toRelIso (PosetFilter.principal (U := p) x)) from by
          refine ⟨x, ?_⟩
          simp)
      simpa using witness.trans (by simp)
    right_inv := fun ⟨y, hy⟩ => by
      simp [sub_iso_toFun]
      let h_ex : ∃ x : β, PosetFilter.principal (U := p) x = iso.toRelIso.symm y := by
        rw [← iso.core_match] at hy
        rcases hy with ⟨F, hF_princ, hF_eq⟩
        rw [← hF_eq]
        rcases hF_princ with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [hx]
        simp
      have witness := Classical.choose_spec h_ex
      have hmap := congrArg iso.toRelIso witness
      simpa using hmap
    map_rel_iff' := fun {x y} => by
      dsimp [sub_iso_toFun]
      simp only [Subtype.mk_le_mk]
      rw [iso.toRelIso.map_rel_iff]
      -- principal x ≤ principal y ↔ x ≤ y
      -- principal y ⊆ principal x ↔ x ≤ y
      -- {z | y ≤ z} ⊆ {z | x ≤ z} ↔ x ≤ y
      constructor
      . intro h
        change {z | y ≤ z} ⊆ {z | x ≤ z} at h
        exact h le_rfl
      . intro h
        change {z | y ≤ z} ⊆ {z | x ≤ z}
        intro z hz
        exact le_trans h hz
  }

  -- Redefine filters_iso correctly using map logic (Order Iso).
  let filters_iso' : PosetFilter (U := p) ≃o PosetFilter (U := Filtrator.suborder (α := base)) := {
    toFun := fun F => {
      elements := sub_iso '' F.elements
      non_empty := by obtain ⟨x, hx⟩ := F.non_empty; use sub_iso x; exact ⟨x, hx, rfl⟩
      cap_elements := by
        intro y1 y2 ⟨x1, hx1, eq1⟩ ⟨x2, hx2, eq2⟩
        obtain ⟨x3, hx3, le1, le2⟩ := F.cap_elements hx1 hx2
        use sub_iso x3
        refine ⟨⟨x3, hx3, rfl⟩, ?_, ?_⟩
        . rw [← eq1]; rw [sub_iso.map_rel_iff]; exact le1
        . rw [← eq2]; rw [sub_iso.map_rel_iff]; exact le2
      carrier := sub_iso '' F.elements
      upper' := fun {y1 y2} le ⟨x1, hx1, eq1⟩ => by
        use sub_iso.symm y2
        constructor
        . have hx1' : x1 ∈ F.carrier := by simpa using hx1
          have hrel : x1 ≤ sub_iso.symm y2 := by
            rw [← eq1] at le
            conv at le => rhs; rw [← sub_iso.apply_symm_apply y2]
            rw [sub_iso.map_rel_iff] at le
            exact le
          have hmem : sub_iso.symm y2 ∈ F.carrier := F.upper' hrel hx1'
          simpa using hmem
        . simp
      carrier_eq_elements := rfl
    }
    invFun := fun F => {
      elements := sub_iso.symm '' F.elements
      non_empty := by obtain ⟨y, hy⟩ := F.non_empty; use sub_iso.symm y; exact ⟨y, hy, rfl⟩
      cap_elements := by
        intro x1 x2 ⟨y1, hy1, eq1⟩ ⟨y2, hy2, eq2⟩
        obtain ⟨y3, hy3, le1, le2⟩ := F.cap_elements hy1 hy2
        use sub_iso.symm y3
        refine ⟨⟨y3, hy3, rfl⟩, ?_, ?_⟩
        . rw [← eq1]; rw [sub_iso.symm.map_rel_iff]; exact le1
        . rw [← eq2]; rw [sub_iso.symm.map_rel_iff]; exact le2
      carrier := sub_iso.symm '' F.elements
      upper' := fun {x1 x2} le ⟨y1, hy1, eq1⟩ => by
        use sub_iso x2
        constructor
        . have hy1' : y1 ∈ F.carrier := by simpa using hy1
          have hrel : y1 ≤ sub_iso x2 := by
            rw [← eq1] at le
            conv at le => rhs; rw [← sub_iso.symm_apply_apply x2]
            rw [sub_iso.symm.map_rel_iff] at le
            exact le
          have hmem : sub_iso x2 ∈ F.carrier := F.upper' hrel hy1'
          simpa using hmem
        . simp
      carrier_eq_elements := rfl
    }
    left_inv := fun F => by
      apply PosetFilter.ext
      apply PosetFilterBase.ext_elements
      simp only [Set.image_image]
      convert Set.image_id _
      simp
    right_inv := fun F => by
      apply PosetFilter.ext
      apply PosetFilterBase.ext_elements
      simp only [Set.image_image]
      convert Set.image_id _
      simp
    map_rel_iff' := fun {F G} => by
      change sub_iso '' G.elements ⊆ sub_iso '' F.elements ↔ G.elements ⊆ F.elements
      apply Set.image_subset_image_iff sub_iso.toEquiv.injective
  }

  -- Note: iso is FiltratorIso (PosetFilter p) i.
  -- iso.symm is i ≃o PosetFilter p.
  -- iso.symm is RelIso.
  -- filters_iso' is PosetFilter p ≃o PosetFilter suborder.
  -- Result: iso.symm.trans filters_iso'.

  let comp := iso.toRelIso.symm.trans filters_iso'

  -- We need FiltratorIso.
  refine {
      toRelIso := comp
      core_match := by
         have hcomp :
             comp.toFun '' subset = filters_iso' '' (iso.toRelIso.symm '' subset) := by
           ext F
           constructor
           . intro hF
             rcases hF with ⟨x, hx, rfl⟩
             refine ⟨iso.toRelIso.symm x, ⟨x, hx, rfl⟩, ?_⟩
             rfl
           . intro hF
             rcases hF with ⟨y, hy, rfl⟩
             rcases hy with ⟨x, hx, rfl⟩
             refine ⟨x, hx, ?_⟩
             rfl
         rw [hcomp]
         have h1 : iso.toRelIso.symm '' subset = Principals (U := p) := by
           apply Set.ext
           intro F
           constructor
           . intro hF
             rcases hF with ⟨y, hy, hEq⟩
             rw [← iso.core_match] at hy
             rcases hy with ⟨P, hP, rfl⟩
             have hPF : P = F := by simpa using hEq
             exact hPF ▸ hP
           . intro hF
             refine ⟨iso.toRelIso F, ?_, ?_⟩
             . rw [← iso.core_match]
               exact ⟨F, hF, rfl⟩
             . simp

         rw [h1]
         have hprincipal (x : β) :
             filters_iso' (PosetFilter.principal (U := p) x) =
               PosetFilter.principal (U := Filtrator.suborder (α := base)) (sub_iso x) := by
           apply PosetFilter.ext
           apply PosetFilterBase.ext_elements
           ext y
           constructor
           . intro hy
             rcases hy with ⟨z, hz, rfl⟩
             exact (sub_iso.map_rel_iff).2 hz
           . intro hy
             refine ⟨sub_iso.symm y, ?_, by simp⟩
             have hy' : sub_iso x ≤ sub_iso (sub_iso.symm y) := by simpa using hy
             exact (sub_iso.map_rel_iff).1 hy'
         apply Set.ext
         intro F
         constructor
         . intro hF_in_image
           rcases hF_in_image with ⟨P, hP_in_principals_p, hF_eq_filters_iso_P⟩
           rcases hP_in_principals_p with ⟨x, rfl⟩
           use sub_iso x
           simpa [hF_eq_filters_iso_P] using (hprincipal x).symm
         . intro hF_in_principals_suborder
           rcases hF_in_principals_suborder with ⟨s, rfl⟩
           use PosetFilter.principal (U := p) (sub_iso.symm s)
           constructor
           . exact ⟨sub_iso.symm s, rfl⟩
           . have hs := hprincipal (sub_iso.symm s)
             simpa using hs.trans (by simp)
  }

theorem exists_filter_for_up (F : PosetFilter (Filtrator.suborder (α := base))) :
    ∃ x : base, to_filters_iso.toRelIso x = F := by
  -- Conversely to Obvious 461: every suborder filter comes from some up-set.
  use (to_filters_iso.toRelIso).symm F
  exact (to_filters_iso.toRelIso).apply_symm_apply F

end primary_core

/-- For an isomorphism from filters on `β`, the induced principal map sends the
elements of `iso.symm x` exactly to `up_suborder x`. -/
lemma image_principals_eq_up_suborder
    {γ : Type*} [i : Filtrator γ] {β : Type*} (p : PartialOrder β)
    (iso : FiltratorIso (FiltratorOfFilters (inst := p)) i)
    (x : γ) :
    (let sub_iso_toFun : β → @Filtrator.subset γ i :=
      fun z => ⟨iso.toRelIso (PosetFilter.principal (U := p) z), by
        rw [← iso.core_match]
        exact ⟨PosetFilter.principal (U := p) z, ⟨z, rfl⟩, rfl⟩⟩
    sub_iso_toFun '' (iso.toRelIso.symm x).elements) =
      @Filtrator.up_suborder γ i x := by
  classical
  let sub_iso_toFun : β → @Filtrator.subset γ i :=
    fun z => ⟨iso.toRelIso (PosetFilter.principal (U := p) z), by
      rw [← iso.core_match]
      exact ⟨PosetFilter.principal (U := p) z, ⟨z, rfl⟩, rfl⟩⟩
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    change x ≤ iso.toRelIso (PosetFilter.principal (U := p) z)
    have hz_le : iso.toRelIso.symm x ≤ PosetFilter.principal (U := p) z := by
      exact (le_principal_iff_subset (U := p) _ z).2 hz
    have hz_map : iso.toRelIso (iso.toRelIso.symm x) ≤ iso.toRelIso (PosetFilter.principal (U := p) z) :=
      (iso.toRelIso.map_rel_iff).2 hz_le
    simpa using hz_map
  · intro hy
    have hcore_symm : iso.toRelIso.symm '' (@Filtrator.subset γ i) = Principals (U := p) := by
      apply Set.ext
      intro F
      constructor
      · intro hF
        rcases hF with ⟨u, hu, rfl⟩
        rw [← iso.core_match] at hu
        rcases hu with ⟨G, hG, rfl⟩
        simpa using hG
      · intro hF
        refine ⟨iso.toRelIso F, ?_, by simp⟩
        rw [← iso.core_match]
        exact ⟨F, hF, rfl⟩
    have hy_princ : iso.toRelIso.symm y.1 ∈ Principals (U := p) := by
      have : iso.toRelIso.symm y.1 ∈ iso.toRelIso.symm '' (@Filtrator.subset γ i) := by
        exact ⟨y.1, y.2, rfl⟩
      simpa [hcore_symm] using this
    rcases hy_princ with ⟨z, hz_eq⟩
    have hz_mem : z ∈ (iso.toRelIso.symm x).elements := by
      have hy_symm : iso.toRelIso.symm x ≤ iso.toRelIso.symm y.1 :=
        (iso.toRelIso.symm.map_rel_iff).2 hy
      have hz_le : iso.toRelIso.symm x ≤ PosetFilter.principal (U := p) z := by
        simpa [hz_eq] using hy_symm
      exact (le_principal_iff_subset (U := p) _ z).1 hz_le
    have hz_map : iso.toRelIso (PosetFilter.principal (U := p) z) = y.1 := by
      have := congrArg iso.toRelIso hz_eq
      simpa using this
    refine ⟨z, hz_mem, ?_⟩
    apply Subtype.ext
    simpa [sub_iso_toFun] using hz_map

section primary_other
variable {base: Type*}
variable (x : base) {α: Set base}
variable [Primary α]

/--
Bridge theorem: the canonical `to_filters_iso` map coincides with the concrete filter
`to_poset_filter`.
-/
theorem to_filters_iso_eq_to_poset_filter :
    to_filters_iso.toRelIso x = to_poset_filter (α := α) x := by
  classical
  let h_prim := (‹Primary α›).is_primary
  let β := Classical.choose h_prim
  let h_prim_beta := Classical.choose_spec h_prim
  let p := Classical.choose h_prim_beta
  let iso_nonempty := Classical.choose_spec h_prim_beta
  let iso := Classical.choice iso_nonempty
  apply PosetFilter.ext
  apply PosetFilterBase.ext_elements
  simpa [to_filters_iso, to_poset_filter, h_prim, β, h_prim_beta, p, iso_nonempty, iso] using
    (@Filtrator.Primary.image_principals_eq_up_suborder base
      (Filtrator.Primary.toFiltrator (self := ‹Primary α›))
      β p iso x)

/--
Every filter on the core suborder is the upper set filter of some element.
This is the concrete form used by Section 5.8 proofs.
-/
theorem exists_to_poset_filter_eq (F : PosetFilter (Filtrator.suborder (α := base))) :
    ∃ x : base, to_poset_filter (α := α) x = F := by
  rcases exists_filter_for_up (α := α) F with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  calc
    to_poset_filter (α := α) x = to_filters_iso.toRelIso x := by
      symm
      exact to_filters_iso_eq_to_poset_filter (α := α) x
    _ = F := hx
end primary_other

noncomputable instance BotOfPrimaryFiltrator [F: Filtrator.Primary α] [OrderBot F.subset] :
    OrderBot F.supset := by
  letI : OrderBot (PosetFilter (U := Filtrator.suborder (α := base))) := {
    -- Bottom filter `{⊥}` in the core order.
    bot := PosetFilter.principal (U := Filtrator.suborder (α := base))
      (⊥ : Filtrator.subset (α := base))
    bot_le := by
      intro G x hx
      exact (show (⊥ : Filtrator.subset (α := base)) ≤ x from bot_le)
  }
  let e := (to_filters_iso (α := α)).toRelIso
  refine {
    bot := e.symm ⊥
    bot_le := ?_
  }
  intro x
  have hbot_filter : (⊥ : PosetFilter (U := Filtrator.suborder (α := base))) ≤ e x := bot_le
  have hbot_pullback : e.symm (⊥ : PosetFilter (U := Filtrator.suborder (α := base))) ≤ e.symm (e x) :=
    (e.symm.map_rel_iff).2 hbot_filter
  simpa using hbot_pullback

noncomputable instance TopOfPrimaryFiltrator [F: Filtrator.Primary α] [OrderTop F.subset] :
    OrderTop F.supset := by
  letI : OrderTop (PosetFilter (U := Filtrator.suborder (α := base))) := {
    -- Top filter `{⊤}` in the core order.
    top := PosetFilter.principal (U := Filtrator.suborder (α := base))
      (⊤ : Filtrator.subset (α := base))
    le_top := by
      intro G x hx
      rcases G.non_empty with ⟨y, hy⟩
      have hy' : y ∈ G.carrier := by
        simpa [G.carrier_eq_elements] using hy
      have htop_mem : (⊤ : Filtrator.subset (α := base)) ∈ G.carrier :=
        G.upper' (show y ≤ (⊤ : Filtrator.subset (α := base)) from le_top) hy'
      have hx_eq_top : x = (⊤ : Filtrator.subset (α := base)) := le_antisymm le_top hx
      have hx' : x ∈ G.carrier := hx_eq_top ▸ htop_mem
      simpa [G.carrier_eq_elements] using hx'
  }
  let e := (to_filters_iso (α := α)).toRelIso
  refine {
    top := e.symm ⊤
    le_top := ?_
  }
  intro x
  have htop_filter : e x ≤ (⊤ : PosetFilter (U := Filtrator.suborder (α := base))) := le_top
  have htop_pullback : e.symm (e x) ≤ e.symm (⊤ : PosetFilter (U := Filtrator.suborder (α := base))) :=
    (e.symm.map_rel_iff).2 htop_filter
  simpa using htop_pullback

end Filtrator.Primary
