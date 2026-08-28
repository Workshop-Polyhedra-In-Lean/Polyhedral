import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Mathlib

namespace Convexity

variable {R X ι : Type*}

open ConvexSpace

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

/-- A family of points is affinely independent if its convex-combination map is injective. -/
def IsAffineIndependent (p : ι → X) : Prop :=
  Function.Injective (fun w : StdSimplex R ι ↦ w.iConvexComb p)

/-- A finite set is affinely independent if its subtype inclusion is affinely independent. -/
def IsAffineIndependentFinset (t : Finset X) : Prop :=
  IsAffineIndependent (R := R) ((↑) : t → X)

/-- A simplex is the convex hull of a finite affinely independent set. -/
def IsSimplex (s : Set X) : Prop :=
  ∃ t : Finset X, IsAffineIndependentFinset (R := R) t ∧ s = convexHull R t

/-- A nondegenerate line segment is the convex hull of two distinct points. -/
def IsLineSegment (s : Set X) : Prop :=
  ∃ a b, a ≠ b ∧ s = convexHull R {a, b}

/-- Every simplex is a polytope. -/
lemma IsSimplex.isPolytope {s : Set X} (hs : IsSimplex (R := R) s) : IsPolytope R s :=
  hs.imp fun _ ht ↦ ht.2

lemma IsLineSegment.isPolytope {s : Set X} (hs : IsLineSegment (R := R) s) : IsPolytope R s := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  exact IsPolytope.convexHull_finite R (by simp)

variable (R) in
def UnitCube (n : ℕ) := Set.pi ⊤ (fun (_ : Fin n) => convexHull R {(0 : R), (1 : R)})

lemma UnitCube_IsPolytope (n : ℕ) : IsPolytope R (UnitCube R n) := by
  let t := Set.pi ⊤ (fun (_ : Fin n) => {(0 : R), (1 : R)})
  have hfinite : t.Finite := by
    refine Set.Finite.pi fun i => ?_
    simp only [Set.finite_insert, Set.finite_singleton]
  have ht : UnitCube R n = convexHull R t := by
    ext x
    constructor
    · sorry
    · sorry
  exact ht ▸ IsPolytope.convexHull_finite R hfinite



end Semiring

end Convexity
