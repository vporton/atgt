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

/-- A powerset-filtrator assumption, represented in this development via primarity. -/
abbrev OnPowerset (α : Type u) := Filtrator.Primary.{u, v} α

variable {α : Type u}

abbrev FilterOnPowerset (α: Type*) := PosetFilter (setPartialOrder α)

abbrev FiltratorOnPowerset (α: Type*) := Filtrator (FilterOnPowerset α)

/-- Canonical filtrator structure on powerset filters. -/
instance instFiltratorOnPowerset (α : Type*) : FiltratorOnPowerset α :=
  FiltratorOfFilters (inst := setPartialOrder α)

end Filtrator
