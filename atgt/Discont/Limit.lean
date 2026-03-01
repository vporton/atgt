import atgt.Funcoid
import atgt.Filtrator.Powerset
import atgt.Filtrator

universe u v w

def IsFuncoidLimit {α: Type u} {β: Type v} (d: Funcoid α β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  F ≤ Funcoid.fwd_set d ({x} : Set α)

def IsBinaryRelationLimit {α: Type u} {β: Type v} (d: α → β → Prop) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  IsFuncoidLimit (principalFuncoid d) F x

def IsFunctionLimit {α: Type u} {β: Type v} (d: α → β) (F: Filtrator.FilterOnPowerset β) (x: α) :=
  IsFuncoidLimit (principalFuncoidOfFunction d) F x
