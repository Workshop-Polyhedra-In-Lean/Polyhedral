import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

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

/-- Every simplex is a convex set. -/
lemma IsSimplex.isConvexSet {s : Set X} (hs : IsSimplex (R := R) s) : IsConvexSet R s :=
  hs.isPolytope.isConvexSet

/-- The convex hull of simplex, is the simplex itself. -/
@[simp] lemma IsSimplex.convexHull_eq {s : Set X} (hs : IsSimplex (R := R) s) :
    convexHull R s = s := hs.isConvexSet.convexHull_eq_self

lemma IsAffineIndependentFinset.isSimplex {t : Finset X}
    (ht : IsAffineIndependentFinset (R := R) t) :
    IsSimplex (R := R) (convexHull R (↑t : Set X)) :=
  ⟨t, ht, rfl⟩

@[simp] lemma IsAffineIndependentFinset.empty :
    IsAffineIndependentFinset (R := R) (∅ : Finset X) := by
  intro w₁ w₂ _
  apply StdSimplex.ext
  apply Finsupp.ext
  exact isEmptyElim

@[simp] lemma IsSimplex.empty : IsSimplex (R := R) (∅ : Set X) :=
  ⟨∅, IsAffineIndependentFinset.empty, by simp⟩

end Semiring

end Convexity
