import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

namespace Convexity

section Semiring

variable {R X Y : Type*}
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [ConvexSpace R Y]

variable (R) in
/-- A line segment is the convex hull of two points. The two points are allowed to coincide. -/
def IsLineSegment (s : Set X) : Prop := ∃ a b, s = convexHull R {a, b}

variable (R) in
/-- A nondegenerate line segment is the convex hull of two distinct points. -/
def IsNondegenerateLineSegment (s : Set X) : Prop :=
  ∃ a b, b ≠ a ∧ s = convexHull R {a, b}

lemma IsNondegenerateLineSegment.isLineSegment {s : Set X}
    (hs : IsNondegenerateLineSegment R s) : IsLineSegment R s := by
  obtain ⟨a, b, _, rfl⟩ := hs
  exact ⟨a, b, rfl⟩

/-- Every line segment is a polytope. -/
lemma IsLineSegment.isPolytope {s : Set X} (hs : IsLineSegment R s) : IsPolytope R s := by
  classical
  obtain ⟨a, b, rfl⟩ := hs
  exact ⟨{a, b}, by simp⟩

variable (R) in
/-- A zonotope is an affine image of a finite product of line segments. -/
def IsZonotope (s : Set X) : Prop :=
  ∃ n : ℕ, ∃ f : (Fin n → StdSimplex R (Fin 2)) → X, IsAffineMap R f ∧ Set.range f = s

/-- The range of an affine map from a finite product of line segments is a zonotope. -/
lemma IsAffineMap.isZonotope_range {n : ℕ}
    {f : (Fin n → StdSimplex R (Fin 2)) → X} (hf : IsAffineMap R f) :
    IsZonotope R (Set.range f) :=
  ⟨n, f, hf, rfl⟩

/-- Every zonotope is nonempty. -/
lemma IsZonotope.nonempty {s : Set X} (hs : IsZonotope R s) : s.Nonempty := by
  obtain ⟨_, f, _, rfl⟩ := hs
  exact Set.range_nonempty f

/-- Affine images of zonotopes are zonotopes. -/
protected lemma IsZonotope.image {s : Set X} {f : X → Y}
    (hf : IsAffineMap R f) (hs : IsZonotope R s) : IsZonotope R (f '' s) := by
  obtain ⟨n, g, hg, rfl⟩ := hs
  exact ⟨n, f ∘ g, hf.comp hg, Set.range_comp f g⟩


/-- The empty set is not a zonotope. -/
@[simp]
lemma not_isZonotope_empty : ¬ IsZonotope R (∅ : Set X) := by
  intro h
  simpa using h.nonempty

variable (R) in
/-- A singleton is a zonotope (the affine image of the zero-dimensional cube). -/
@[simp] protected lemma IsZonotope.singleton (x : X) : IsZonotope R {x} := by
  exact ⟨0, fun _ ↦ x, by fun_prop, by simp⟩

end Semiring

end Convexity
