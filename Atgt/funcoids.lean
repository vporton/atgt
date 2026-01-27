import Mathlib.Data.Ordmap.Ordset

universe u v u2 v2
set_option trace.Meta.synthInstance true

/- TODO: Should be in `PartialOrder`, instead. -/
def is_least{u}(s: PartialOrder u)(x: u) := ∀ a, x ≤ a

/- TODO: Should be in `PartialOrder`, instead. -/
def meet{u}(s: PartialOrder u)(a b: u) := ∃ c, a ≤ c ∧ c ≤ b ∧ ¬ (is_least s c)

theorem meet_as_inf{u}{s: SemilatticeInf u}(a b: u): ¬ (is_least s.toPartialOrder (a ⊓ b)) := sorry

theorem meet_on_semilattice{s: SemilatticeInf u}(a b: u) :
    @meet _ s.toPartialOrder a b ↔ ¬ is_least s.toPartialOrder (a ⊓ b) := sorry

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

instance PointfreeFuncoid.on_semilattice_inf(a: SemilatticeInf u)(b: SemilatticeInf u)
    : PointfreeFuncoid a.toPartialOrder b.toPartialOrder where
    fwd := f.fwd
    bwd := f.bwd
    rev := ∀ x: a, y: b, is_least (fwd x) ⊓ y ↔ is_least (bwd y) ⊓ x := sorry

instance PointfreeFuncoid.poset{a b: poset} : poset (PointfreeFuncoid a b) where
    { le := ∀ x, f.fwd x ≤ g.fwd x ∧ ∀ y, g.bwd y ≤ f.bwd y } := sorry
