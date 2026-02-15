import atgt.PointfreeFuncoid.Core

/-!
Section 20.5 (Domain and range of a pointfree funcoid), items 1635--1648.
-/

def PointfreeFuncoid.identity {α : Type u}
    (X : PartialOrder α) : PointfreeFuncoid X X where
  fwd := id
  bwd := id
  rev x y := by
    simpa using (meet_comm x y)

def PointfreeFuncoid.restrictedIdentity {α : Type u}
    {X : SemilatticeInf α} (a : α) :
    PointfreeFuncoid X.toPartialOrder X.toPartialOrder where
  fwd x := a ⊓ x
  bwd y := a ⊓ y
  rev x y := by
    constructor <;> intro h
    · have h' : ¬ is_least ((a ⊓ x) ⊓ y) := (meet_as_inf (a ⊓ x) y).1 h
      exact (meet_as_inf (a ⊓ y) x).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')
    · have h' : ¬ is_least ((a ⊓ y) ⊓ x) := (meet_as_inf (a ⊓ y) x).1 h
      exact (meet_as_inf (a ⊓ x) y).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')

theorem restrictedIdentity_rev {α : Type u}
    {X : SemilatticeInf α} (a x y : α) :
    meet ((PointfreeFuncoid.restrictedIdentity (X := X) a).fwd x) y ↔
      meet ((PointfreeFuncoid.restrictedIdentity (X := X) a).bwd y) x :=
  (PointfreeFuncoid.restrictedIdentity (X := X) a).rev x y

theorem restrictedIdentity_inv {α : Type u}
    {X : SemilatticeInf α} (a : α) :
    (PointfreeFuncoid.restrictedIdentity (X := X) a).inv =
      (PointfreeFuncoid.restrictedIdentity (X := X) a) := by
  ext <;> rfl

theorem funcoid_rel_restrictedIdentity {α : Type u}
    {X : SemilatticeInf α} (a x y : α) :
    (PointfreeFuncoid.restrictedIdentity (X := X) a).funcoid_rel x y ↔
      meet a (x ⊓ y) := by
  change meet (a ⊓ x) y ↔ meet a (x ⊓ y)
  constructor <;> intro h
  · have h' : ¬ is_least ((a ⊓ x) ⊓ y) := (meet_as_inf (a ⊓ x) y).1 h
    exact (meet_as_inf a (x ⊓ y)).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')
  · have h' : ¬ is_least (a ⊓ (x ⊓ y)) := (meet_as_inf a (x ⊓ y)).1 h
    exact (meet_as_inf (a ⊓ x) y).2 (by simpa [inf_assoc, inf_left_comm, inf_comm] using h')

def PointfreeFuncoid.restrict {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : PartialOrder β}
    (f : PointfreeFuncoid X.toPartialOrder Y) (a : α) :
    PointfreeFuncoid X.toPartialOrder Y :=
  (PointfreeFuncoid.restrictedIdentity (X := X) a) ∘ f

def PointfreeFuncoid.image {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α] (f : PointfreeFuncoid X Y) : β :=
  f.fwd ⊤

def PointfreeFuncoid.domain {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop β] (f : PointfreeFuncoid X Y) : α :=
  f.inv.image

@[simp] theorem PointfreeFuncoid.image_eq_fwd_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α] (f : PointfreeFuncoid X Y) :
    f.image = f.fwd ⊤ := rfl

@[simp] theorem PointfreeFuncoid.domain_eq_bwd_top
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop β] (f : PointfreeFuncoid X Y) :
    f.domain = f.bwd ⊤ := rfl

lemma meet_iff_not_is_least_of_le_right {α : Type u}
    [PartialOrder α] {a b : α} (h : a ≤ b) :
    meet a b ↔ ¬ is_least a := by
  constructor
  · intro hmeet hleast
    rcases hmeet with ⟨c, hca, _, hnotleast⟩
    apply hnotleast
    intro x
    exact le_trans hca (hleast x)
  · intro hnotleast
    exact ⟨a, le_rfl, h, hnotleast⟩

theorem PointfreeFuncoid.fwd_monotone_of_stronglySeparable
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    (f : PointfreeFuncoid X Y)
    (h_dst_strong : IsStronglySeparable β) :
    Monotone f.fwd := by
  intro x z hxz
  apply h_dst_strong
  intro y hy
  have hxy : meet (f.fwd x) y := (meet_comm y (f.fwd x)).1 hy
  have hbwdx : meet (f.bwd y) x := (f.rev x y).1 hxy
  have hbwdz : meet (f.bwd y) z := meet_mono_right hxz hbwdx
  have hzy : meet (f.fwd z) y := (f.rev z y).2 hbwdz
  exact (meet_comm y (f.fwd z)).2 hzy

theorem PointfreeFuncoid.bwd_monotone_of_stronglySeparable
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    (f : PointfreeFuncoid X Y)
    (h_src_strong : IsStronglySeparable α) :
    Monotone f.bwd := by
  simpa [PointfreeFuncoid.inv] using
    (PointfreeFuncoid.fwd_monotone_of_stronglySeparable (f := f.inv) h_src_strong)

theorem image_ge_fwd {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α]
    (h_dst_strong : IsStronglySeparable β)
    (f : PointfreeFuncoid X Y) (x : α) :
    f.image ≥ f.fwd x := by
  exact (PointfreeFuncoid.fwd_monotone_of_stronglySeparable (f := f) h_dst_strong) (le_top : x ≤ ⊤)

theorem fwd_domain_eq_image
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop α] [OrderTop β]
    (h_src_strong : IsStronglySeparable α)
    (h_dst_sep : IsSeparable β)
    (f : PointfreeFuncoid X Y) :
    f.fwd (f.domain) = f.image := by
  have hmono_bwd : Monotone f.bwd :=
    PointfreeFuncoid.bwd_monotone_of_stronglySeparable (f := f) h_src_strong
  apply h_dst_sep
  ext y
  constructor
  · intro hy
    have hy' : meet (f.fwd (f.domain)) y := (meet_comm y (f.fwd (f.domain))).1 hy
    have hbwd_dom : meet (f.bwd y) (f.domain) := (f.rev (f.domain) y).1 hy'
    have hy_le_dom : f.bwd y ≤ f.domain := by
      simpa [PointfreeFuncoid.domain] using hmono_bwd (le_top : y ≤ (⊤ : β))
    have h_notleast : ¬ is_least (f.bwd y) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := f.domain) hy_le_dom).1 hbwd_dom
    have hbwd_top : meet (f.bwd y) (⊤ : α) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := (⊤ : α)) le_top).2 h_notleast
    have himage' : meet (f.fwd (⊤ : α)) y := (f.rev (⊤ : α) y).2 hbwd_top
    exact (meet_comm y (f.fwd (⊤ : α))).2 (by simpa [PointfreeFuncoid.image] using himage')
  · intro hy
    have hy' : meet (f.fwd (⊤ : α)) y := by
      simpa [PointfreeFuncoid.image] using (meet_comm y (f.fwd (⊤ : α))).1 hy
    have hbwd_top : meet (f.bwd y) (⊤ : α) := (f.rev (⊤ : α) y).1 hy'
    have hy_le_dom : f.bwd y ≤ f.domain := by
      simpa [PointfreeFuncoid.domain] using hmono_bwd (le_top : y ≤ (⊤ : β))
    have h_notleast : ¬ is_least (f.bwd y) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := (⊤ : α)) le_top).1 hbwd_top
    have hbwd_dom : meet (f.bwd y) (f.domain) :=
      (meet_iff_not_is_least_of_le_right (a := f.bwd y) (b := f.domain) hy_le_dom).2 h_notleast
    have hdom' : meet (f.fwd (f.domain)) y := (f.rev (f.domain) y).2 hbwd_dom
    exact (meet_comm y (f.fwd (f.domain))).2 hdom'

theorem fwd_eq_fwd_inf_domain
    {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : PartialOrder β}
    [OrderTop β]
    (h_src_sep : IsSeparable α)
    (h_dst_sep : IsSeparable β)
    (f : PointfreeFuncoid X.toPartialOrder Y) (x : α) :
    f.fwd x = f.fwd (x ⊓ f.domain) := by
  have h_src_strong : IsStronglySeparable α :=
    separable_imp_stronglySeparable h_src_sep
  have hmono_bwd : Monotone f.bwd :=
    PointfreeFuncoid.bwd_monotone_of_stronglySeparable (f := f) h_src_strong
  apply h_dst_sep
  ext y
  constructor
  · intro hy
    have hy' : meet (f.fwd x) y := (meet_comm y (f.fwd x)).1 hy
    have hbwd_x : meet (f.bwd y) x := (f.rev x y).1 hy'
    have hy_le_dom : f.bwd y ≤ f.domain := by
      simpa [PointfreeFuncoid.domain] using hmono_bwd (le_top : y ≤ (⊤ : β))
    rcases hbwd_x with ⟨c, hcy, hcx, hnotleast⟩
    have hcd : c ≤ f.domain := le_trans hcy hy_le_dom
    have hbwd_xd : meet (f.bwd y) (x ⊓ f.domain) :=
      ⟨c, hcy, le_inf hcx hcd, hnotleast⟩
    have hxy' : meet (f.fwd (x ⊓ f.domain)) y := (f.rev (x ⊓ f.domain) y).2 hbwd_xd
    exact (meet_comm y (f.fwd (x ⊓ f.domain))).2 hxy'
  · intro hy
    have hy' : meet (f.fwd (x ⊓ f.domain)) y := (meet_comm y (f.fwd (x ⊓ f.domain))).1 hy
    have hbwd_xd : meet (f.bwd y) (x ⊓ f.domain) := (f.rev (x ⊓ f.domain) y).1 hy'
    have hbwd_x : meet (f.bwd y) x := meet_mono_right inf_le_left hbwd_xd
    have hxy' : meet (f.fwd x) y := (f.rev x y).2 hbwd_x
    exact (meet_comm y (f.fwd x)).2 hxy'

theorem meet_domain_iff_fwd_not_least
    {α : Type u} {β : Type v}
    {X : PartialOrder α} {Y : PartialOrder β}
    [OrderTop β]
    (f : PointfreeFuncoid X Y) (x : α) :
    meet x (f.domain) ↔ ¬ is_least (f.fwd x) := by
  constructor
  · intro hx
    have hdomx : meet (f.bwd (⊤ : β)) x := by
      simpa [PointfreeFuncoid.domain] using (meet_comm x (f.bwd (⊤ : β))).1 hx
    have htop : meet (f.fwd x) (⊤ : β) := (f.rev x (⊤ : β)).2 hdomx
    exact (meet_iff_not_is_least_of_le_right (a := f.fwd x) (b := (⊤ : β)) le_top).1 htop
  · intro hnotleast
    have htop : meet (f.fwd x) (⊤ : β) :=
      (meet_iff_not_is_least_of_le_right (a := f.fwd x) (b := (⊤ : β)) le_top).2 hnotleast
    have hdomx : meet (f.bwd (⊤ : β)) x := (f.rev x (⊤ : β)).1 htop
    exact (meet_comm x (f.bwd (⊤ : β))).2 (by simpa [PointfreeFuncoid.domain] using hdomx)

def IsSeparatorAtomistic (α : Type u) [CompleteLattice α] : Prop :=
  ∀ x : α, x = sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a x}

theorem domain_eq_sSup_atoms_fwd_ne_bot
    {α : Type u} {β : Type v}
    {Y : PartialOrder β}
    [CompleteLattice α] [OrderTop β] [OrderBot β]
    (h_atomistic : IsSeparatorAtomistic α)
    (f : PointfreeFuncoid (inferInstance : PartialOrder α) Y) :
    f.domain =
      sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ f.fwd a ≠ (⊥ : β)} := by
  have hdom :
      f.domain =
        sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a f.domain} :=
    h_atomistic f.domain
  have hset :
      {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a f.domain} =
      {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ f.fwd a ≠ (⊥ : β)} := by
    ext a
    constructor
    · intro ha
      refine ⟨ha.1, ?_⟩
      have h_notleast : ¬ is_least (f.fwd a) :=
        (meet_domain_iff_fwd_not_least (f := f) (x := a)).1 ha.2
      intro hbot
      apply h_notleast
      intro z
      exact hbot ▸ bot_le
    · intro ha
      refine ⟨ha.1, ?_⟩
      have h_notleast : ¬ is_least (f.fwd a) := by
        intro hleast
        exact ha.2 (le_antisymm (hleast ⊥) bot_le)
      exact (meet_domain_iff_fwd_not_least (f := f) (x := a)).2 h_notleast
  have hsSup :
      sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ meet a f.domain} =
        sSup {a : α | a ∈ AlternativePrimaryFiltrators.atoms (⊤ : α) ∧ f.fwd a ≠ (⊥ : β)} :=
    congrArg sSup hset
  exact hdom.trans hsSup

theorem domain_restrict
    {α : Type u} {β : Type v}
    {X : SemilatticeInf α} {Y : PartialOrder β}
    [OrderTop β]
    (f : PointfreeFuncoid X.toPartialOrder Y) (a : α) :
    (f.restrict a).domain = a ⊓ f.domain := by
  rfl
