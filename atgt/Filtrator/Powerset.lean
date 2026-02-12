import Mathlib.Data.Set.Basic
import Mathlib.Order.RelIso.Basic
import atgt.Filtrator
import atgt.Filtrator.Primary

/-!
# Powerset filtrators

Definition 460: a primary filtrator over a poset order-isomorphic to a powerset is called a
powerset filtrator.
-/

/-- Mathlib orders `Set U` by inclusion (`⊆`); this alias exposes it explicitly. -/
def setPartialOrder (U : Type*) : PartialOrder (Set U) := inferInstance

namespace Filtrator

universe u v

/-- **Definition 460.** A primary filtrator whose underlying partial order is order-isomorphic to a
powerset is called a powerset filtrator. -/
-- def PowersetFiltrator (α : Type u) [inst : Filtrator.{u} α] : Prop :=
--   @Filtrator.Primary.{u, u} α inst ∧ ∃ β : Type*, Nonempty (α ≃o Set β)

/- TODO: Rename?  -/
class Powerset (α: Type*) [inst : Filtrator α] : Prop where
  is_powerset : ∃ β: Type*,
    Nonempty (FiltratorIso (FiltratorOfFilters (inst := setPartialOrder β)) inst)

variable {α : Type u} {inst : Filtrator α}

instance Powerset.primary [h : @Powerset.{u, v} α inst] : @Filtrator.Primary.{u, v} α inst := by
  rcases h.is_powerset with ⟨β, hIso⟩
  exact { is_primary := ⟨_, setPartialOrder β, hIso⟩ }

end Filtrator
