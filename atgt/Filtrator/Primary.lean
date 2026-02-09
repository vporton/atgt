import atgt.Filtrator
import atgt.PosetFilter

/- TODO: Move the below to `Filtrator.Primary`. -/
class Filtrator.Filtered (α : Type u) [Filtrator α] : Prop where
  is_filtered : ∀ x y : α, up x ⊆ up y → y ≤ x

/-- A filtrator is up-determined if every element is the infimum of its core upper set. -/
class Filtrator.UpDetermined (α : Type u) [Filtrator α] : Prop where
  is_up_determined : ∀ x : α, IsGLB (Filtrator.up x) x

theorem Filtrator.up_determined_iff_filtered {α : Type u} [Filtrator α] :
  Filtrator.Filtered α ↔ Filtrator.UpDetermined α := by
  constructor
  · intro h
    constructor
    intro x
    constructor
    · intro y hy
      exact hy.2
    · intro y hy
      apply h.is_filtered
      intro z hz
      exact ⟨hz.1, hy hz⟩
  · intro h
    constructor
    intro x y h_subs
    apply (h.is_up_determined x).2
    intro z hz
    exact (h.is_up_determined y).1 (h_subs hz)

instance FiltratorOfFilters {X : Type*} [inst : PartialOrder X] : Filtrator (PosetFilter inst) where
  subset := Principals (U := inst)

-- class Filtrator.Primary (α : Type u) [Filtrator α] : Prop where
--   is_primary : True -- placeholder
