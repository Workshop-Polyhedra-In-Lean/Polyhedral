import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

noncomputable section

namespace Convexity

section Semiring

variable {R X : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [AddCommMonoid X]

open scoped Pointwise

def IsLineSegment (s : Set X) := ∃ a, ∃ b≠a, s = convexHull R {a, b}

def isZonotope (s : Set X) := ∃ segs : Multiset (Set X),
  (∀ seg ∈ segs, IsLineSegment (R := R) (seg)) ∧ (segs.sum = s)

end Semiring

end Convexity
