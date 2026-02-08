import Mathlib.Data.Ordmap.Ordset
import atgt.Poset

universe u v u2 v2

structure PointfreeFuncoid {u v}(a: PartialOrder u)(b: PartialOrder v) where
    fwd : u → v
    bwd : v → u
    rev (x: u) (y: v) : @meet _ b (fwd x) y ↔ @meet _ a (bwd y) x

@[ext]
lemma PointfreeFuncoid.ext {u v} {a : PartialOrder u} {b : PartialOrder v}
  (f g : @PointfreeFuncoid u v a b)
  (h_fwd : f.fwd = g.fwd)
  (h_bwd : f.bwd = g.bwd) : f = g := by
  cases f; cases g;
  congr

instance PointfreeFuncoid.inv {u v}
  {a : PartialOrder u}{b : PartialOrder v}
  (f : @PointfreeFuncoid u v a b) :
  @PointfreeFuncoid v u b a where
    fwd := f.bwd
    bwd := f.fwd
    rev (x : v) (y : u) := (f.rev y x).symm

theorem inv_inv_funcoid{u v}(a: PartialOrder u)(b: PartialOrder v)(f: @PointfreeFuncoid u v a b) :
    f.inv.inv = f := by simp[PointfreeFuncoid.inv]

/- FIXME: Can be converted to instance? -/
def PointfreeFuncoid.on_semilattice_inf
  {a : SemilatticeInf u} {b : SemilatticeInf v} :=
  @PointfreeFuncoid u v a.toPartialOrder b.toPartialOrder

instance PointfreeFuncoid.instLE
  {u v} (a : PartialOrder u) (b : PartialOrder v) :
  LE (@PointfreeFuncoid u v a b) :=
⟨fun f g =>
  (∀ x, f.fwd x ≤ g.fwd x) ∧ (∀ y, g.bwd y ≤ f.bwd y)⟩

/- TODO: `instLE` is a partial order. -/

/- TODO: Add `Semicategory` to MathLib and use it for `comp`. -/
-- instance PointfreeFuncoid.instSemigroup
--   {u v} (a : PartialOrder u) (b : PartialOrder v) :
--   Semicategory (PointfreeFuncoid a b) := {
--     mul: f g:
--   }

def comp {x: Type u} {y: Type v} {z: Type w}{X: PartialOrder x}{Y: PartialOrder y}{Z: PartialOrder z}
    (f: PointfreeFuncoid X Y) (g: @PointfreeFuncoid y z Y Z)
    : @PointfreeFuncoid x z X Z
    := {
        fwd := g.fwd ∘ f.fwd
        bwd := f.bwd ∘ g.bwd
        rev := by
            intro x z
            -- g.rev gives: meet Y (g.fwd (f.fwd x)) z ↔ meet Y (f.fwd x) (g.bwd z)
            -- f.rev needs:  meet Y (g.bwd z) (f.fwd x)
            -- so we commute the meet
            refine
                    (g.rev (f.fwd x) z).trans ?_
            have := f.rev x (g.bwd z)
            -- commute the meet on Y
            simpa [meet_comm] using this
    }

infixr:80 " ∘ " => comp

theorem comp_assoc {x: Type u} {y: Type v} {z: Type w} {w_type: Type u2}
    {X: PartialOrder x}{Y: PartialOrder y}{Z: PartialOrder z}{W: PartialOrder w_type}
    (f: PointfreeFuncoid X Y) (g: @PointfreeFuncoid y z Y Z) (h: @PointfreeFuncoid z w_type Z W)
    : (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
    ext <;> rfl

theorem inv_comp {x: Type u} {y: Type v} {z: Type w}
    {X: PartialOrder x}{Y: PartialOrder y}{Z: PartialOrder z}
    (f: PointfreeFuncoid X Y) (g: @PointfreeFuncoid y z Y Z)
    : (f ∘ g).inv = g.inv ∘ f.inv := by
    ext <;> rfl

def funcoid_rel {x: Type u} {y: Type v} {X: PartialOrder x}{Y: PartialOrder y}
    (f: PointfreeFuncoid X Y) (a : x) (b : y) :
    Prop
    := @meet y Y (f.fwd a) b

theorem funcoid_rel_comm {x: Type u} {y: Type v} {X: PartialOrder x}{Y: PartialOrder y}
    (f: PointfreeFuncoid X Y) (a : x) (b : y) :
    funcoid_rel f a b ↔ funcoid_rel f.inv b a :=
    f.rev a b

-- TODO:
