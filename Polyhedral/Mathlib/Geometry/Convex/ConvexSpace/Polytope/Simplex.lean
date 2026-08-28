import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization


/-! This file introduces `IsAffineIndependet` in Convex Spaces and proves equivalence in affine space. -/

noncomputable section

namespace Convexity

variable {R X Y V A ι : Type*}


open ConvexSpace

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]


def IsAffineIndependent (p : ι → X) : Prop :=
  Function.Injective (fun w : StdSimplex R ι ↦ iConvexComb w p)

def IsAffineIndependentFinSet (t : Finset X) : Prop :=
  IsAffineIndependent (R := R) ((↑) : t → X)

def IsSimplex (s : Set X) := ∃ t : Finset X, IsAffineIndependentFinSet (R := R) t
                             ∧ convexHull R t = s

def IsLineSegment (s : Set X) := ∃ a, ∃ b≠a, s = convexHull R {a, b}

end Semiring

end Convexity
