/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Geometry.Convex.Hull
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
-- TODO Move these to an appropriate place

/-!
# Convexity of affine subspaces

This file proves that an affine subspace is convex, and that convexity interacts with affine spans
in the expected way: an affine subspace is its own convex hull, and passing to the convex hull of a
set leaves its affine span unchanged.

## Main results

* `AffineSubspace.isConvexSet`: an affine subspace is a convex set, since a convex combination of
  its points is in particular an affine combination of them.
* `AffineSubspace.convexHull_eq`: an affine subspace is its own convex hull.
* `affineSpan_convexHull_eq`: the affine span of a convex hull is the affine span of the set it
  was taken of.
-/

public section

namespace Convexity

variable (k : Type*) {V P : Type*} [AddCommGroup V] [AddTorsor V P]
variable (s : Set P)

section AffineConvex

variable [DivisionRing k] [Module k V]

variable [PartialOrder k] [IsStrictOrderedRing k] [ConvexSpace k P] [IsAffineConvexSpace k V P]

-- it seems like IsAffineConvexSpace is the generality we need here
-- because a convex space requires an ordering on the ring and we
-- don't have that for general affine spaces

-- Slop ↓
/-- An affine subspace is convex: it is closed under affine combinations of its points, and
convex combinations are affine combinations. -/
theorem _root_.AffineSubspace.isConvexSet (t : AffineSubspace k P) : IsConvexSet k (t : Set P) := by
  refine IsConvexSet.of_sConvexComb_mem fun w hw ↦ ?_
  have hle : affineSpan k (w.weights.support : Set P) ≤ t := by
    simpa using affineSpan_mono k hw
  refine hle ?_
  simp only [IsAffineConvexSpace.sConvexComb_eq_convexComb]
  rw [AddTorsor.convexCombination,
    ← Finset.attach_affineCombination_coe]
  have hsum : ∑ x ∈ w.weights.support.attach,
      (⇑w.weights ∘ ((↑) : w.weights.support → P)) x = 1 := by
    simp only [Function.comp_apply, Finset.sum_attach]
    simpa [Finsupp.sum] using w.total
  have hmem := affineCombination_mem_affineSpan hsum ((↑) : w.weights.support → P)
  rwa [Subtype.range_coe] at hmem

@[simp]
theorem _root_.AffineSubspace.convexHull_eq (t : AffineSubspace k P) :
    convexHull k t = (t : Set P) :=
  convexHull_eq_self.mpr (AffineSubspace.isConvexSet ..)

@[simp]
theorem _root_.affineSpan_convexHull_eq :
    affineSpan k (convexHull k s : Set P) = affineSpan k s := by
  refine le_antisymm ?_ (affineSpan_mono k subset_convexHull_self)
  have := convexHull_min (subset_affineSpan k s) (AffineSubspace.isConvexSet _ _)
  grw [affineSpan_mono k this, affineSpan_le_of_subset_coe le_rfl]

end AffineConvex

end Convexity
