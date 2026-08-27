import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization


/-! This file introduces `IsAffineIndependet` in Convex Spaces and proves equivalence in affine space. -/

noncomputable section

namespace Convexity

variable {R X Y V A : Type*}

open ConvexSpace

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable (R) in
def ConvexSpace.IsAffineIndependent (t : Set X) : Prop :=
  Function.Injective (sConvexComb ∘ StdSimplex.map (Subtype.val) : StdSimplex R t → X)

variable (R) in
def IsSimplex (s : Set X) := ∃ t : Finset X, IsAffineIndependent R (t : Set X) ∧ s = convexHull R t

variable (R) in
def IsLineSegment (s : Set X) := ∃ a, ∃ b≠a, s = convexHull R {a, b}

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [ConvexSpace R A] [IsAffineConvexSpace R V A]

variable (V) in
lemma IsAffineIndependent_pair (a b : A) :
    IsAffineIndependent R {a, b} := by
  intro w₁ w₂ h
  simp at h
  rw [IsAffineConvexSpace.sConvexComb_eq_convexComb (V:=V)] at h



lemma LineSegmentIsSimplex (s : Set A) (h : IsLineSegment R s) : IsSimplex R s := by
  obtain ⟨a, b, hab, rfl⟩ := h
  use ⟨{a, b}, by simpa using hab.symm⟩
  simp

end Ring

end Convexity
