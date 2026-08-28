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
