import Mathlib.Data.Set.Basic
import Mathlib.Order.RelIso.Basic
import atgt.Filtrator
import atgt.Filtrator.Primary

/-!
# Powerset filtrators

Definition 460: a primary filtrator over a poset order-isomorphic to a powerset is called a
powerset filtrator.
-/

namespace Filtrator

variable {u : Level}

/-- **Definition 460.** A primary filtrator whose underlying partial order is order-isomorphic to a
powerset is called a powerset filtrator. -/
def PowersetFiltrator (α : Type u) [inst : Filtrator.{u} α] : Prop :=
  @Filtrator.Primary.{u, u} α inst ∧ ∃ β : Type*, Nonempty (α ≃o Set β)

end Filtrator
