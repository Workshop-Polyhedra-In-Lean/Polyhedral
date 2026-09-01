import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Simplex
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice

namespace Convexity

variable {R X : Type*}

open ConvexSpace

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

namespace Polytope

/-- A polytope is simplicial if every facet is a simplex. -/
def IsSimplicial (P : Polytope R X) : Prop :=
  ∀ F : (P : ConvexSet R X).Face, IsCoatom F → IsSimplex (R := R) (F : Set X)

end Polytope

end Semiring

end Convexity
