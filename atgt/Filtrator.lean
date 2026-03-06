import Mathlib.Data.Ordmap.Ordset
import Mathlib.Data.Set.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Lattice
import atgt.Poset
import Mathlib.Order.Bounds.Defs

class Filtrator (α : Type*) extends PartialOrder α where
  subset : Set α

export Filtrator (subset)

def Filtrator.suporder {α : Type*} [Filtrator α] : PartialOrder α := inferInstance

def Filtrator.suborder {α : Type*} [Filtrator α] : PartialOrder (subset : Set α) :=
  Subtype.partialOrder (· ∈ (subset : Set α))

abbrev Filtrator.supset {α : Type u} [Filtrator α] : Type u := α

-- TODO: Delete?
def Filtrator.subset_to_suporder {α : Type u} [Filtrator α]
    (x : Filtrator.subset (α := α)) : α :=
  x.1

-- variable {α : Type*} [Filtrator α]

def Filtrator.up {α : Type u} [Filtrator α] (x: α) := { y ∈ subset | x ≤ y }

def Filtrator.up_suborder {α : Type u} [Filtrator α] (x : α) : Set (subset : Set α) :=
  { y | x ≤ y.1 }

/- For simplicity, I define it only for semilattices. In the book it's more general. -/
def Filtrator.binary_meet_closed {α : Type u} [Filtrator α] [SemilatticeInf α] : Prop :=
  ∀ x y : α, x ∈ subset → y ∈ subset → x ⊓ y ∈ subset

def Filtrator.up_is_filter {α : Type u} [Filtrator α] [SemilatticeInf α] (a : α) : Prop :=
  Set.Nonempty (Filtrator.up a) ∧
    (∀ x y : α, x ∈ Filtrator.up a → y ∈ Filtrator.up a → x ⊓ y ∈ Filtrator.up a) ∧
    (∀ x y : α, x ∈ Filtrator.up a → y ∈ subset → x ≤ y → y ∈ Filtrator.up a)

/-- Theorem 535: under the usual core assumptions, the core is binary-meet closed iff each
upper set is a filter. -/
theorem Filtrator.binary_meet_closed_iff_up_filters {α : Type u} [Filtrator α] [SemilatticeInf α]
    (h_nonempty : ∀ a : α, Set.Nonempty (Filtrator.up a))
    (hord : ∀ a b : α, a ≤ b ↔ @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a b) :
    Filtrator.binary_meet_closed (α := α) ↔ ∀ a : α, Filtrator.up_is_filter a := by
  constructor
  · intro h_closed a
    constructor
    · exact h_nonempty a
    · constructor
      · intro x y hx hy
        let z_val := x ⊓ y
        have z_mem : z_val ∈ subset := h_closed x y hx.1 hy.1
        have h_a_x : a ≤ x := hx.2
        have h_a_y : a ≤ y := hy.2
        have h_a_x' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a x :=
          (hord a x).1 h_a_x
        have h_a_y' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a y :=
          (hord a y).1 h_a_y
        have h_a_z' :
            @LE.le α (inferInstance : SemilatticeInf α).toPartialOrder.toLE a z_val :=
          le_inf h_a_x' h_a_y'
        have : a ≤ z_val := (hord a z_val).2 h_a_z'
        exact show z_val ∈ Filtrator.up a from ⟨z_mem, this⟩
      · intro x y hx hy hxy
        have h_ax : a ≤ x := hx.2
        exact ⟨hy, le_trans h_ax hxy⟩
  · intro h x y hx hy
    let a := x ⊓ y
    have hx' : x ∈ Filtrator.up a := by
      refine ⟨hx, ?_⟩
      exact (hord a x).2 inf_le_left
    have hy' : y ∈ Filtrator.up a := by
      refine ⟨hy, ?_⟩
      exact (hord a y).2 inf_le_right
    rcases h a with ⟨_, ⟨hcap, _⟩⟩
    exact (hcap x y hx' hy').1

structure FiltratorIso {α β : Type*} (a: Filtrator α) (b: Filtrator β) extends RelIso a.suporder.le b.suporder.le where
  core_match: toFun '' a.subset = b.subset

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

class Filtrator.PreFiltered (α : Type u) [Filtrator α] : Prop where
  is_pre_filtered : ∀ x y : α, up x = up y → y = x

theorem filtered_imp_prefiltered (α : Type*) [Filtrator α] :
    Filtrator.Filtered α → Filtrator.PreFiltered α := by
  intro h
  constructor
  intro x y h_up_eq
  have hy_le_x := h.is_filtered x y (h_up_eq ▸ subset_rfl)
  have hx_le_y := h.is_filtered y x (Eq.symm h_up_eq ▸ subset_rfl)
  exact le_antisymm hy_le_x hx_le_y
