import atgt.PointfreeFuncoid.Identities

/-!
Section 20.7 (Funcoidal product of elements).
-/

universe u v w

namespace PointfreeFuncoid

@[simp] theorem not_meet_bot_left
    {α : Type u} [PartialOrder α] [OrderBot α] (x : α) :
    ¬ meet (⊥ : α) x := by
  intro h
  rcases h with ⟨c, hc_bot, _, hnotleast⟩
  have hleast : is_least c := by
    intro t
    have hc_eq_bot : c = (⊥ : α) := le_antisymm hc_bot bot_le
    simp [hc_eq_bot]
  exact hnotleast hleast

@[simp] theorem not_meet_bot_right
    {α : Type u} [PartialOrder α] [OrderBot α] (x : α) :
    ¬ meet x (⊥ : α) := by
  simpa [meet_comm] using (not_meet_bot_left (α := α) (x := x))

/-- Binary (funcoidal) product `A ×^FCD B`. -/
noncomputable def binaryProduct
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β]
    (a : α) (b : β) :
    PointfreeFuncoid X Y := by
  classical
  refine {
    fwd := fun x => if meet x a then b else ⊥
    bwd := fun y => if meet y b then a else ⊥
    rev := ?_
  }
  intro x y
  by_cases hxa : meet x a
  · by_cases hyb : meet y b
    · have hax : meet a x := (meet_comm x a).1 hxa
      have hby : meet b y := (meet_comm y b).1 hyb
      simp [hxa, hyb, hax, hby]
    · have hby : ¬ meet b y := by
        intro h
        exact hyb ((meet_comm y b).2 h)
      simp [hxa, hyb, hby]
  · by_cases hyb : meet y b
    · have hax : ¬ meet a x := by
        intro h
        exact hxa ((meet_comm x a).2 h)
      simp [hxa, hyb, hax]
    · simp [hxa, hyb]

/-- Relation form of the binary funcoidal product. -/
theorem funcoid_rel_binaryProduct
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β]
    (a x : α) (b y : β) :
    (binaryProduct (X := X) (Y := Y) a b).funcoid_rel x y ↔
      meet x a ∧ meet y b := by
  classical
  by_cases hxa : meet x a
  · by_cases hyb : meet y b
    · have hby : meet b y := (meet_comm y b).1 hyb
      simp [PointfreeFuncoid.funcoid_rel, binaryProduct, hxa, hyb, hby]
    · have hby : ¬ meet b y := by
        intro h
        exact hyb ((meet_comm y b).2 h)
      simp [PointfreeFuncoid.funcoid_rel, binaryProduct, hxa, hyb, hby]
  · by_cases hyb : meet y b
    · simp [PointfreeFuncoid.funcoid_rel, binaryProduct, hxa, hyb]
    · simp [PointfreeFuncoid.funcoid_rel, binaryProduct, hxa, hyb]

theorem binaryProduct_inv
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β]
    (a : α) (b : β) :
    (binaryProduct (X := X) (Y := Y) a b).inv =
      (binaryProduct (X := Y) (Y := X) b a) := by
  ext <;> rfl

theorem fwd_bot
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β]
    (f : PointfreeFuncoid X Y) :
    f.fwd (⊥ : α) = (⊥ : β) := by
  apply le_antisymm
  · have hleast : is_least (f.fwd (⊥ : α)) := by
      by_contra hnotleast
      have hself : meet (f.fwd (⊥ : α)) (f.fwd (⊥ : α)) :=
        ⟨f.fwd (⊥ : α), le_rfl, le_rfl, hnotleast⟩
      have hbot : meet (f.bwd (f.fwd (⊥ : α))) (⊥ : α) :=
        (f.rev (⊥ : α) (f.fwd (⊥ : α))).1 hself
      exact (not_meet_bot_right (α := α) (x := f.bwd (f.fwd (⊥ : α)))) hbot
    exact hleast (⊥ : β)
  · exact bot_le

theorem bwd_bot
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β]
    (f : PointfreeFuncoid X Y) :
    f.bwd (⊥ : β) = (⊥ : α) := by
  simpa [PointfreeFuncoid.inv] using
    (fwd_bot (f := f.inv))

theorem image_binaryProduct_of_meet_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop α]
    (a : α) (b : β)
    (h : meet (⊤ : α) a) :
    (binaryProduct (X := X) (Y := Y) a b).image = b := by
  classical
  simp [PointfreeFuncoid.image, binaryProduct, h]

theorem image_binaryProduct_of_not_meet_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop α]
    (a : α) (b : β)
    (h : ¬ meet (⊤ : α) a) :
    (binaryProduct (X := X) (Y := Y) a b).image = ⊥ := by
  classical
  simp [PointfreeFuncoid.image, binaryProduct, h]

theorem image_binaryProduct_le
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop α]
    (a : α) (b : β) :
    (binaryProduct (X := X) (Y := Y) a b).image ≤ b := by
  classical
  by_cases hta : meet (⊤ : α) a
  · simp [PointfreeFuncoid.image, binaryProduct, hta]
  · simp [PointfreeFuncoid.image, binaryProduct, hta]

theorem domain_binaryProduct_of_meet_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop β]
    (a : α) (b : β)
    (h : meet (⊤ : β) b) :
    (binaryProduct (X := X) (Y := Y) a b).domain = a := by
  simpa [PointfreeFuncoid.domain, binaryProduct_inv] using
    (image_binaryProduct_of_meet_top (X := Y) (Y := X) (a := b) (b := a) h)

theorem domain_binaryProduct_of_not_meet_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop β]
    (a : α) (b : β)
    (h : ¬ meet (⊤ : β) b) :
    (binaryProduct (X := X) (Y := Y) a b).domain = ⊥ := by
  simpa [PointfreeFuncoid.domain, binaryProduct_inv] using
    (image_binaryProduct_of_not_meet_top (X := Y) (Y := X) (a := b) (b := a) h)

theorem domain_binaryProduct_le
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop β]
    (a : α) (b : β) :
    (binaryProduct (X := X) (Y := Y) a b).domain ≤ a := by
  simpa [PointfreeFuncoid.domain, binaryProduct_inv] using
    (image_binaryProduct_le (X := Y) (Y := X) (a := b) (b := a))

/-- Proposition 1662: upper bound by a binary funcoidal product implies domain/image bounds. -/
theorem proposition1662
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop α] [OrderTop β]
    (f : PointfreeFuncoid X Y) (a : α) (b : β)
    (h : f ≤ (binaryProduct (X := X) (Y := Y) a b)) :
    f.domain ≤ a ∧ f.image ≤ b := by
  constructor
  · exact le_trans (PointfreeFuncoid.domain_mono (f := f) (g := binaryProduct (X := X) (Y := Y) a b) h)
      (domain_binaryProduct_le (X := X) (Y := Y) (a := a) (b := b))
  · exact le_trans (PointfreeFuncoid.image_mono (f := f) (g := binaryProduct (X := X) (Y := Y) a b) h)
      (image_binaryProduct_le (X := X) (Y := Y) (a := a) (b := b))

/-- Theorem 1663 (`\label{pf-im-dom}`): characterization of `f ≤ A ×^FCD B` by domain/image. -/
theorem theorem1663_pf_im_dom
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderBot α] [OrderBot β] [OrderTop α] [OrderTop β]
    (h_src_strong : IsStronglySeparable α)
    (h_dst_strong : IsStronglySeparable β)
    (f : PointfreeFuncoid X Y) (a : α) (b : β) :
    f ≤ (binaryProduct (X := X) (Y := Y) a b) ↔
      f.domain ≤ a ∧ f.image ≤ b := by
  constructor
  · intro h
    exact proposition1662 (f := f) (a := a) (b := b) h
  · intro h
    rcases h with ⟨hdom, himage⟩
    refine ⟨?_, ?_⟩
    · intro x
      by_cases hxa : meet x a
      · have hmono_fwd : Monotone f.fwd :=
          PointfreeFuncoid.fwd_monotone_of_stronglySeparable (f := f) h_dst_strong
        have hfx_le_image : f.fwd x ≤ f.image := by
          simpa [PointfreeFuncoid.image] using hmono_fwd (le_top : x ≤ (⊤ : α))
        have hfx_le_b : f.fwd x ≤ b := le_trans hfx_le_image himage
        simpa [binaryProduct, hxa] using hfx_le_b
      · have h_not_meet_dom : ¬ meet x f.domain := by
          intro hxd
          exact hxa (meet_mono_right hdom hxd)
        have h_least_fx : is_least (f.fwd x) := by
          by_contra h_notleast
          exact h_not_meet_dom
            ((meet_domain_iff_fwd_not_least (f := f) (x := x)).2 h_notleast)
        have hfx_eq_bot : f.fwd x = (⊥ : β) :=
          le_antisymm (h_least_fx ⊥) bot_le
        simp [binaryProduct, hxa, hfx_eq_bot]
    · intro y
      by_cases hyb : meet y b
      · have hmono_bwd : Monotone f.bwd :=
          PointfreeFuncoid.bwd_monotone_of_stronglySeparable (f := f) h_src_strong
        have hby_le_dom : f.bwd y ≤ f.domain := by
          simpa [PointfreeFuncoid.domain] using hmono_bwd (le_top : y ≤ (⊤ : β))
        have hby_le_a : f.bwd y ≤ a := le_trans hby_le_dom hdom
        simpa [binaryProduct, hyb] using hby_le_a
      · have h_not_meet_image : ¬ meet y f.image := by
          intro hyi
          exact hyb (meet_mono_right himage hyi)
        have h_not_meet_inv_domain : ¬ meet y f.inv.domain := by
          simpa [PointfreeFuncoid.domain, PointfreeFuncoid.image] using h_not_meet_image
        have h_least_by : is_least (f.bwd y) := by
          by_contra h_notleast
          exact h_not_meet_inv_domain
            ((meet_domain_iff_fwd_not_least (f := f.inv) (x := y)).2 h_notleast)
        have hby_eq_bot : f.bwd y = (⊥ : α) :=
          le_antisymm (h_least_by ⊥) bot_le
        simp [binaryProduct, hyb, hby_eq_bot]

theorem binaryProduct_comp
    {α : Type u} {β : Type v} {γ : Type w}
    {X : PartialOrder α} {Y : PartialOrder β} {Z : PartialOrder γ}
    [OrderBot α] [OrderBot β] [OrderBot γ]
    (a : α) (b : β)
    (f : PointfreeFuncoid Y Z) :
    (binaryProduct (X := X) (Y := Y) a b) ∘ f =
      (binaryProduct (X := X) (Y := Z) a (f.fwd b)) := by
  classical
  apply PointfreeFuncoid.ext
  · funext x
    by_cases hxa : meet x a
    · simp [comp, binaryProduct, hxa]
    · simp [comp, binaryProduct, hxa, fwd_bot]
  · funext y
    by_cases hy : meet y (f.fwd b)
    · have hb : meet (f.bwd y) b := by
        exact (f.rev b y).1 (by simpa [meet_comm] using hy)
      simp [comp, binaryProduct, hy, hb]
    · have hb : ¬ meet (f.bwd y) b := by
        intro hby
        apply hy
        exact (by simpa [meet_comm] using (f.rev b y).2 hby)
      simp [comp, binaryProduct, hy, hb]

theorem binaryProduct_comp_inv
    {α : Type u} {β : Type v} {γ : Type w}
    {X : PartialOrder α} {Y : PartialOrder β} {Z : PartialOrder γ}
    [OrderBot α] [OrderBot β] [OrderBot γ]
    (a : α) (b : β)
    (g : PointfreeFuncoid Z X) :
    g ∘ (binaryProduct (X := X) (Y := Y) a b) =
      (binaryProduct (X := Z) (Y := Y) (g.bwd a) b) := by
  let B := binaryProduct (X := Y) (Y := X) b a
  let B' := binaryProduct (X := Y) (Y := Z) b (g.inv.fwd a)
  have h :=
    binaryProduct_comp
      (X := Y) (Y := X) (Z := Z)
      (a := b) (b := a)
      (f := g.inv)
  have bin_prod_eq :=
    binaryProduct_inv
      (X := X) (Y := Y)
      (a := a) (b := b)
  have bin_prod_eq' := by
    simpa [inv_inv_funcoid] using congrArg PointfreeFuncoid.inv bin_prod_eq
  have inv_comp_eq :
    g ∘ B.inv = (B ∘ g.inv).inv := by
    have h_inv := inv_comp (f := B) (g := g.inv)
    simp [PointfreeFuncoid.inv] at h_inv
    exact h_inv.symm
  calc
    g ∘ (binaryProduct (X := X) (Y := Y) a b) =
        g ∘ B.inv := by rw [bin_prod_eq']
    _ = (B ∘ g.inv).inv := by rw [inv_comp_eq]
    _ = B'.inv := by rw [h]
    _ = binaryProduct (X := Z) (Y := Y) (g.inv.fwd a) b := by
      rw [binaryProduct_inv (X := Y) (Y := Z) (a := b) (b := g.inv.fwd a)]
    _ = binaryProduct (X := Z) (Y := Y) (g.bwd a) b := by
      rfl

/--
Theorem 1664 (GLB form): for bounded separable meet-semilattices, the
composition with restricted identities is the greatest lower bound of
`f` and `A ×^FCD B`.

This is the order-theoretic formulation of
`f ⊓ (A ×^FCD B) = id_B ∘ f ∘ id_A`.
-/
theorem theorem1664_binaryProduct_glb
    {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : SemilatticeInf β}
    [OrderBot α] [OrderBot β] [OrderTop α] [OrderTop β]
    (h_src_sep : IsSeparable α) (h_dst_sep : IsSeparable β)
    (f : PointfreeFuncoid X.toPartialOrder Y.toPartialOrder)
    (a : α) (b : β) :
    let h :=
      (PointfreeFuncoid.restrictedIdentity (X := X) a) ∘ f ∘
        (PointfreeFuncoid.restrictedIdentity (X := Y) b)
    h ≤ f ∧ h ≤ (binaryProduct (X := X.toPartialOrder) (Y := Y.toPartialOrder) a b) ∧
      ∀ g : PointfreeFuncoid X.toPartialOrder Y.toPartialOrder,
        g ≤ f →
        g ≤ (binaryProduct (X := X.toPartialOrder) (Y := Y.toPartialOrder) a b) →
        g ≤ h := by
  let h :=
    (PointfreeFuncoid.restrictedIdentity (X := X) a) ∘ f ∘
      (PointfreeFuncoid.restrictedIdentity (X := Y) b)
  have h_src_strong : IsStronglySeparable α :=
    separable_imp_stronglySeparable h_src_sep
  have h_dst_strong : IsStronglySeparable β :=
    separable_imp_stronglySeparable h_dst_sep
  have hmono_fwd : Monotone f.fwd :=
    PointfreeFuncoid.fwd_monotone_of_stronglySeparable (f := f) h_dst_strong
  have hmono_bwd : Monotone f.bwd :=
    PointfreeFuncoid.bwd_monotone_of_stronglySeparable (f := f) h_src_strong
  have hh_le_f : h ≤ f := by
    refine ⟨?_, ?_⟩
    · intro x
      calc
        h.fwd x = b ⊓ f.fwd (a ⊓ x) := by rfl
        _ ≤ f.fwd (a ⊓ x) := inf_le_right
        _ ≤ f.fwd x := hmono_fwd inf_le_right
    · intro y
      calc
        h.bwd y = a ⊓ f.bwd (b ⊓ y) := by rfl
        _ ≤ f.bwd (b ⊓ y) := inf_le_right
        _ ≤ f.bwd y := hmono_bwd inf_le_right
  have hh_le_bin : h ≤ (binaryProduct (X := X.toPartialOrder) (Y := Y.toPartialOrder) a b) := by
    have hh_domain_le : h.domain ≤ a := by
      change a ⊓ f.bwd (b ⊓ (⊤ : β)) ≤ a
      exact inf_le_left
    have hh_image_le : h.image ≤ b := by
      change b ⊓ f.fwd (a ⊓ (⊤ : α)) ≤ b
      exact inf_le_left
    exact
      (theorem1663_pf_im_dom
        (X := X.toPartialOrder) (Y := Y.toPartialOrder)
        (h_src_strong := h_src_strong) (h_dst_strong := h_dst_strong)
        (f := h) (a := a) (b := b)).2 ⟨hh_domain_le, hh_image_le⟩
  refine ⟨hh_le_f, hh_le_bin, ?_⟩
  intro g hgf hgb
  have hdom_g : g.domain ≤ a := (proposition1662 (f := g) (a := a) (b := b) hgb).1
  have himage_g : g.image ≤ b := (proposition1662 (f := g) (a := a) (b := b) hgb).2
  have hmono_gfwd : Monotone g.fwd :=
    PointfreeFuncoid.fwd_monotone_of_stronglySeparable (f := g) h_dst_strong
  have hmono_gbwd : Monotone g.bwd :=
    PointfreeFuncoid.bwd_monotone_of_stronglySeparable (f := g) h_src_strong
  refine ⟨?_, ?_⟩
  · intro x
    have hgx_le_b : g.fwd x ≤ b := by
      have hgx_le_image : g.fwd x ≤ g.image := by
        simpa [PointfreeFuncoid.image] using hmono_gfwd (le_top : x ≤ (⊤ : α))
      exact le_trans hgx_le_image himage_g
    have hgx_eq :
        g.fwd x = g.fwd (x ⊓ g.domain) := by
      exact fwd_eq_fwd_inf_domain
        (X := X) (Y := Y.toPartialOrder)
        (h_src_sep := h_src_sep) (h_dst_sep := h_dst_sep)
        (f := g) (x := x)
    have hxd_le : x ⊓ g.domain ≤ a ⊓ x := by
      calc
        x ⊓ g.domain = g.domain ⊓ x := by simp [inf_comm]
        _ ≤ a ⊓ x := inf_le_inf hdom_g le_rfl
    have hgx_le_fax : g.fwd x ≤ f.fwd (a ⊓ x) := by
      calc
        g.fwd x = g.fwd (x ⊓ g.domain) := hgx_eq
        _ ≤ g.fwd (a ⊓ x) := hmono_gfwd hxd_le
        _ ≤ f.fwd (a ⊓ x) := hgf.1 (a ⊓ x)
    change g.fwd x ≤ b ⊓ f.fwd (a ⊓ x)
    exact le_inf hgx_le_b hgx_le_fax
  · intro y
    have hgy_le_a : g.bwd y ≤ a := by
      have hgy_le_domain : g.bwd y ≤ g.domain := by
        simpa [PointfreeFuncoid.domain] using hmono_gbwd (le_top : y ≤ (⊤ : β))
      exact le_trans hgy_le_domain hdom_g
    have hgy_eq :
        g.bwd y = g.bwd (y ⊓ g.image) := by
      have h_inv :=
        fwd_eq_fwd_inf_domain
          (X := Y) (Y := X.toPartialOrder)
          (h_src_sep := h_dst_sep) (h_dst_sep := h_src_sep)
          (f := g.inv) (x := y)
      simpa [PointfreeFuncoid.domain, PointfreeFuncoid.image] using h_inv
    have hyi_le : y ⊓ g.image ≤ b ⊓ y := by
      calc
        y ⊓ g.image = g.image ⊓ y := by simp [inf_comm]
        _ ≤ b ⊓ y := inf_le_inf himage_g le_rfl
    have hgy_le_fby : g.bwd y ≤ f.bwd (b ⊓ y) := by
      calc
        g.bwd y = g.bwd (y ⊓ g.image) := hgy_eq
        _ ≤ g.bwd (b ⊓ y) := hmono_gbwd hyi_le
        _ ≤ f.bwd (b ⊓ y) := hgf.2 (b ⊓ y)
    change g.bwd y ≤ a ⊓ f.bwd (b ⊓ y)
    exact le_inf hgy_le_a hgy_le_fby

/-- Corollary 1665: specialization to `B = ⊤` recovers source restriction. -/
theorem corollary1665_restrict_glb
    {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : SemilatticeInf β}
    [OrderBot α] [OrderBot β] [OrderTop α] [OrderTop β]
    (h_src_sep : IsSeparable α) (h_dst_sep : IsSeparable β)
    (f : PointfreeFuncoid X.toPartialOrder Y.toPartialOrder)
    (a : α) :
    let h :=
      (PointfreeFuncoid.restrictedIdentity (X := X) a) ∘ f ∘
        (PointfreeFuncoid.restrictedIdentity (X := Y) (⊤ : β))
    h = f.restrict a ∧
      h ≤ f ∧
      h ≤ (binaryProduct (X := X.toPartialOrder) (Y := Y.toPartialOrder) a (⊤ : β)) := by
  let h :=
    (PointfreeFuncoid.restrictedIdentity (X := X) a) ∘ f ∘
      (PointfreeFuncoid.restrictedIdentity (X := Y) (⊤ : β))
  have h_glb :=
    theorem1664_binaryProduct_glb
      (X := X) (Y := Y)
      (h_src_sep := h_src_sep) (h_dst_sep := h_dst_sep)
      (f := f) (a := a) (b := (⊤ : β))
  have hh_eq : h = f.restrict a := by
    apply PointfreeFuncoid.ext
    · funext x
      simp [h, PointfreeFuncoid.restrict, comp, PointfreeFuncoid.restrictedIdentity]
    · funext y
      simp [h, PointfreeFuncoid.restrict, comp, PointfreeFuncoid.restrictedIdentity]
  refine ⟨hh_eq, ?_, ?_⟩
  · simpa [h] using h_glb.1
  · simpa [h] using h_glb.2.1

end PointfreeFuncoid
