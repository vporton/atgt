import atgt.PointfreeFuncoid
import atgt.Filtrator.Powerset

universe u w

class Funcoid
    {α: Type u} {β: Type w}
    [a: PartialOrder α] [b: PartialOrder β]
    [Filtrator.Powerset α] [Filtrator.Powerset β]
  extends PointfreeFuncoid a b
