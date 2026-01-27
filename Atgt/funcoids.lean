import Mathlib.Data.Ordmap.Ordset

universe u v u2 v2

/- TODO: Should be in `PartialOrder`, instead. -/
def is_least{u}(s: PartialOrder u)(a: u) := ∀ x, a ≤ x

/- TODO: Should be in `PartialOrder`, instead. -/
def meet{u}(s: PartialOrder u)(a b: u) := ∃ c, c ≤ a ∧ c ≤ b ∧ ¬ (is_least s c)

/- TODO: Should be in `PartialOrder`, instead. -/
theorem meet_as_inf {u}
  (s : SemilatticeInf u) (a b : u) :
  meet s.toPartialOrder a b ↔
  ¬ is_least s.toPartialOrder (a ⊓ b) :=
by
  constructor
  · intro h
    rcases h with ⟨c, hc₁, hc₂, hnot⟩
    intro hleast
    apply hnot
    intro x
    have := hleast x
    have hcab : c ≤ a ⊓ b :=
      le_inf hc₁ hc₂
    exact le_trans hcab this
  · intro h
    refine ⟨a ⊓ b, inf_le_left, inf_le_right, ?_⟩
    exact h

structure PointfreeFuncoid {u v}(a: PartialOrder u)(b: PartialOrder v) where
    fwd : u → v
    bwd : v → u
    rev (x: u) (y: v) : @meet v b (fwd x) y ↔ @meet u a (bwd y) x

instance inv {u v}
  (a : PartialOrder u)(b : PartialOrder v)
  (f : PointfreeFuncoid a b) :
  PointfreeFuncoid b a where
    fwd := f.bwd
    bwd := f.fwd
    rev (x : v) (y : u) := (f.rev y x).symm

theorem inv_inv_funcoid{u v}(a: PartialOrder u)(b: PartialOrder v)(f: PointfreeFuncoid a b) :
    inv b a (inv a b f) = f := by simp[inv]

/- FIXME: Can be converted to instance? -/
def PointfreeFuncoid.on_semilattice_inf
  (a : SemilatticeInf u) (b : SemilatticeInf v) :=
  PointfreeFuncoid a.toPartialOrder b.toPartialOrder

instance PointfreeFuncoid.instLE
  {u v} (a : PartialOrder u) (b : PartialOrder v) :
  LE (PointfreeFuncoid a b) :=
⟨fun f g =>
  (∀ x, f.fwd x ≤ g.fwd x) ∧ (∀ y, g.bwd y ≤ f.bwd y)⟩
