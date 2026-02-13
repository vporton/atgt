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

/- TODO: Rename?  -/
class Powerset (α: Type*) extends Filtrator α where
  is_powerset : ∃ β: Type*,
    Nonempty (FiltratorIso (FiltratorOfFilters (inst := setPartialOrder β)) toFiltrator)

variable {α : Type u}

noncomputable instance Powerset.primary [h : Powerset.{u, v} α] : Filtrator.Primary.{u, v} α := by
  let β := Classical.choose h.is_powerset
  let hIso : Nonempty (FiltratorIso (FiltratorOfFilters (inst := setPartialOrder β)) h.toFiltrator) :=
    Classical.choose_spec h.is_powerset
  exact { toFiltrator := h.toFiltrator, is_primary := ⟨Set β, setPartialOrder β, hIso⟩ }

end Filtrator
