import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

namespace Convexity

section Semiring

variable {R X V : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

open scoped Pointwise

variable (R) in
def IsLineSegment (s : Set X) := ∃ a, ∃ b≠a, s = convexHull R {a, b}

lemma IsLineSegment.isPolytope {s : Set X}
    (hs : IsLineSegment (R := R) s) : IsPolytope R s := by
  classical
  rcases hs with ⟨a, b, _, rfl⟩
  exact ⟨{a, b}, by simp⟩

variable (R) in
def UnitCube (n : ℕ) := Set.pi ⊤ (fun (_ : Fin n) => convexHull R {(0 : R), (1 : R)})

variable (R) in
def isZonotope (s : Set X) := ∃ n : ℕ, ∃ f : (Fin n → R) → X,
   IsAffineMap R f ∧ f '' UnitCube (R := R) n = s

--TODO : generalize this to families of convex spaces
lemma convexHull_pi {ι : Type*} [Finite ι] (s : Set ι) (α : ι → Set X) :
    Set.pi s (fun i => convexHull R (α i)) = convexHull R (Set.pi s α) := by
  classical
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

section AddCommGroup
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

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


end AddCommGroup
end Semiring

end Convexity
