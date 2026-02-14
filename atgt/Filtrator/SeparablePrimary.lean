import atgt.Filtrator.Separable
import atgt.AlternativePrimaryFiltrators

namespace StrongSeparability

universe u

variable {α : Type u}

/-- Proposition 579 core step with the correct assumption locus:
the core type is boolean, so the boolean-core order is strongly separable. -/
theorem primary_imp_booleanStronglySeparableCore [Filtrator α] [Filtrator.Primary α]
    [BooleanAlgebra (Filtrator.subset (α := α))] :
    @IsStronglySeparable (Filtrator.supset (α := α)) (Filtrator.suporder (α := α)) := by
  sorry

end StrongSeparability

export StrongSeparability
  (primary_imp_booleanStronglySeparableCore)
