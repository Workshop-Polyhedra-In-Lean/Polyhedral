/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Geometry.Convex.Hull

-- TODO Move these to an appropriate place

namespace Convexity

variable (k : Type*) {V P : Type*} [AddCommGroup V] [AddTorsor V P]
variable (s : Set P)

section Field

variable [Field k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

-- TODO: read and consider the doc comment, should this be stated for a
-- [ConvexSpace k P] type class instead?
attribute [local instance] AddTorsor.toConvexSpace

theorem _root_.AffineSubspace.isConvexSet (t : AffineSubspace k P) : IsConvexSet k (t : Set P) :=
  IsConvexSet.of_convexCombPair_mem fun a b ha hb hab x hx y hy ↦ by
    rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply]
    exact t.smul_vsub_vadd_mem a hx hy hy

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

end Field

end Convexity
