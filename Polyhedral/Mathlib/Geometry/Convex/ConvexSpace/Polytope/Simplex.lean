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

/-- Every simplex is a polytope. -/
lemma IsSimplex.isPolytope {s : Set X} (hs : IsSimplex (R := R) s) : IsPolytope R s :=
  hs.imp fun _ ht ↦ ht.2

end Semiring

end Convexity
