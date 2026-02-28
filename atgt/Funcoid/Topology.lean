import Mathlib.Topology.Bases
import atgt.Funcoid

universe u

def neighborhoodRel {α : Type u} (t : TopologicalSpace α) (x y : α) : Prop :=
  letI : TopologicalSpace α := t
  ∀ U : Set α, IsOpen U → x ∈ U → y ∈ U

def closureRel {α : Type u} (t : TopologicalSpace α) (x y : α) : Prop :=
  letI : TopologicalSpace α := t
  ∀ F : Set α, IsClosed F → x ∈ F → y ∈ F

def neighborhoodFuncoid {α : Type u} (t : TopologicalSpace α) :
    PointfreeFuncoid (setPartialOrder α) (setPartialOrder α) :=
  principalFuncoid (neighborhoodRel t)

def closureFuncoid {α : Type u} (t : TopologicalSpace α) :
    PointfreeFuncoid (setPartialOrder α) (setPartialOrder α) :=
  principalFuncoid (closureRel t)

def converseRel {α : Type u} (r : α → α → Prop) : α → α → Prop :=
  fun x y => r y x

lemma closureRel_iff_converseNeighborhoodRel {α : Type u} (t : TopologicalSpace α) :
    closureRel t = converseRel (neighborhoodRel t) := by
  letI : TopologicalSpace α := t
  funext x y
  apply propext
  constructor
  · intro h U hU hyU
    by_contra hxU
    have hxUc : x ∈ Uᶜ := by simpa using hxU
    have hyUc : y ∈ Uᶜ :=
      h (Uᶜ) (isClosed_compl_iff.2 hU) hxUc
    exact hyUc hyU
  · intro h F hF hxF
    by_contra hyF
    have hyFc : y ∈ Fᶜ := by simpa using hyF
    have hxFc : x ∈ Fᶜ :=
      h (Fᶜ) (isOpen_compl_iff.2 hF) hyFc
    exact hxFc hxF

lemma principalFuncoid_inv_eq_converse {α : Type u} (r : α → α → Prop) :
    (principalFuncoid r).inv = principalFuncoid (converseRel r) := by
  apply PointfreeFuncoid.ext
  · funext A
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyA, hxy⟩
      exact ⟨y, hyA, hxy⟩
    · intro hx
      rcases hx with ⟨y, hyA, hxy⟩
      exact ⟨y, hyA, hxy⟩
  · funext A
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyA, hxy⟩
      exact ⟨y, hyA, hxy⟩
    · intro hx
      rcases hx with ⟨y, hyA, hxy⟩
      exact ⟨y, hyA, hxy⟩

theorem neighborhoodFuncoid_inv {α : Type u} (t : TopologicalSpace α) :
    (neighborhoodFuncoid t).inv = closureFuncoid t := by
  calc
    (neighborhoodFuncoid t).inv
      = (principalFuncoid (converseRel (neighborhoodRel t))) := by
          simpa [neighborhoodFuncoid] using
            principalFuncoid_inv_eq_converse (r := neighborhoodRel t)
    _ = principalFuncoid (closureRel t) := by
          simp [closureRel_iff_converseNeighborhoodRel t]
    _ = closureFuncoid t := rfl

theorem closureFuncoid_inv {α : Type u} (t : TopologicalSpace α) :
    (closureFuncoid t).inv = neighborhoodFuncoid t := by
  have h := neighborhoodFuncoid_inv t
  simpa [inv_inv_funcoid, closureFuncoid] using (congrArg PointfreeFuncoid.inv h).symm

def circ {α : Type u} (f : PointfreeFuncoid (setPartialOrder α) (setPartialOrder α)) :
    PointfreeFuncoid (setPartialOrder α) (setPartialOrder α) := f

def nearnessFuncoid {α : Type u} (t : TopologicalSpace α) :
    PointfreeFuncoid (setPartialOrder α) (setPartialOrder α) :=
  circ (closureFuncoid t).inv

theorem nearnessFuncoid_fwd_singleton_eq_neighborhoodFuncoid_fwd_singleton
    {α : Type u} (t : TopologicalSpace α) (x : α)
    (_hsep : @TopologicalSpace.SeparableSpace α t) :
    (nearnessFuncoid t).fwd ({x} : Set α) =
      (neighborhoodFuncoid t).fwd ({x} : Set α) := by
  simp [nearnessFuncoid, circ, closureFuncoid_inv]
