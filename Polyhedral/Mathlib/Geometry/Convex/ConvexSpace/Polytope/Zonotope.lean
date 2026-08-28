import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

noncomputable section

namespace Convexity

section Semiring

variable {R X V : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

open scoped Pointwise

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

variable (R) in
def IsLineSegment (s : Set X) := ∃ a, ∃ b≠a, s = convexHull R {a, b}

variable (R) in
def isZonotope (s : Set X) := ∃ n : ℕ, ∃ f : (Fin n → R) → X,
   IsAffineMap R f ∧ f '' UnitCube (R := R) n = s

variable (R) in
lemma sumOfSegments_isZonotope (s : Set V) :
  (∃ segs : Multiset (Set V),
    (∀ seg ∈ segs, IsLineSegment R (seg)) ∧ (segs.sum = s)) → isZonotope R s := sorry

variable (R) in
lemma zonotope_isSumOfSegments (s : Set V) :
  isZonotope R s → (∃ segs : Multiset (Set V),
    (∀ seg ∈ segs, IsLineSegment R (seg)) ∧ (segs.sum = s)) := sorry

variable (R) in
lemma zonotope_iff_sumOfSegments (s : Set V) :
  isZonotope R s ↔ (∃ segs : Multiset (Set V),
    (∀ seg ∈ segs, IsLineSegment R (seg)) ∧ (segs.sum = s)) := by
  constructor
  · exact zonotope_isSumOfSegments R s
  · exact sumOfSegments_isZonotope R s


end Semiring

end Convexity
