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

--TODO : generalize this to families of convex spaces
lemma convexHull_pi {ι : Type*} [Finite ι] (s : Set ι) (α : ι → Set X) :
    Set.pi s (fun i => convexHull R (α i)) = convexHull R (Set.pi s α) := by
  have hs : Fintype s := Fintype.ofFinite ↑s
  rw [← Set.coe_toFinset s]
  set t := s.toFinset
  induction t using Finset.induction
  · simp
  · sorry --this might be hard, since we only proved convexHull distributing over cartesian prodúct but this is an intersection.

lemma UnitCube_IsPolytope (n : ℕ) : IsPolytope R (UnitCube R n) := by
  let t := Set.pi ⊤ (fun (_ : Fin n) => {(0 : R), (1 : R)})
  have hfinite : t.Finite := by
    refine Set.Finite.pi fun i => ?_
    simp only [Set.finite_insert, Set.finite_singleton]
  have ht : UnitCube R n = convexHull R t := convexHull_pi _ _
  exact ht ▸ IsPolytope.convexHull_finite R hfinite

end Semiring

end Convexity
