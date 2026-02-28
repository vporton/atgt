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

end PointfreeFuncoid
