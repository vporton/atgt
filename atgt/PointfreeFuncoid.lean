import Mathlib.Data.Ordmap.Ordset
import atgt.Poset
import atgt.Filtrator

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

def comp {X: PartialOrder x}{Y: PartialOrder y}{Z: PartialOrder z}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z)
    : PointfreeFuncoid X Z
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

theorem comp_assoc {X: PartialOrder u}{Y: PartialOrder v}{Z: PartialOrder w}{W: PartialOrder u2}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z) (h: PointfreeFuncoid Z W)
    : (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
    ext <;> rfl

theorem inv_comp {X: PartialOrder u}{Y: PartialOrder v}{Z: PartialOrder w}
    (f: PointfreeFuncoid X Y) (g: PointfreeFuncoid Y Z)
    : (f ∘ g).inv = g.inv ∘ f.inv := by
    ext <;> rfl

def PointfreeFuncoid.funcoid_rel {X: PartialOrder u}{Y: PartialOrder v}
    (f: PointfreeFuncoid X Y) (a : u) (b : v) :
    Prop
    := @meet v Y (f.fwd a) b

theorem funcoid_rel_comm {X: PartialOrder u}{Y: PartialOrder v}
    (f: PointfreeFuncoid X Y) (a : u) (b : v) :
    f.funcoid_rel a b ↔ f.inv.funcoid_rel b a :=
    f.rev a b

theorem sep_fwd {u v : Type _} [X : PartialOrder u] [Y : PartialOrder v] (f g : PointfreeFuncoid X Y) :
    IsSeparable u → f.fwd = g.fwd → f = g := by
    intro h_sep h_fwd
    apply PointfreeFuncoid.ext
    · exact h_fwd
    · funext y
      apply h_sep
      ext x
      simp [separator]
      rw [meet_comm x, meet_comm x]
      rw [← f.rev, ← g.rev]
      rw [h_fwd]

theorem sep_rel {u v : Type _} [X : PartialOrder u] [Y : PartialOrder v] (f g : PointfreeFuncoid X Y) :
    IsSeparable u → IsSeparable v → f.funcoid_rel = g.funcoid_rel → f = g := by
    intro h_sep_u h_sep_v h_rel
    apply sep_fwd f g h_sep_u
    funext x
    apply h_sep_v
    ext y
    simp [separator]
    rw [meet_comm y, meet_comm y]
    change ¬ f.funcoid_rel x y ↔ ¬ g.funcoid_rel x y
    rw [h_rel]

lemma rel_right_flt{α: Type u}(F: Filtrator α){X: PartialOrder u}{Y: PartialOrder v}
    (f: PointfreeFuncoid X Y) (a: u) (b: v) :
    f.funcoid_rel a b ↔ ∀ X: a, f.funcoid_rel X b := by
    intro h
    apply h
    intro x hx
    exact hx

-- TODO:
