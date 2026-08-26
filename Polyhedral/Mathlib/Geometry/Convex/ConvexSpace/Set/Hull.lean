/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Order.Closure
import Mathlib.Geometry.Convex.Hull

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Pointwise

/-!
# IsConvexSet hull

This file defines the convex hull of a set in a convex space. `convexHull R s` is the smallest
convex set containing `s`. In order theory speak, this is a closure operator.
-/

public section

open Set

namespace Convexity


section Pointwise


open Pointwise

variable {R X Y V A : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [ConvexSpace R Y]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

@[simp] lemma convexHull_neg (s : Set V) : -convexHull R s = convexHull R (-s) := by
  ext x
  simp only [mem_neg, mem_convexHull_iff]
  constructor <;> intro h t hst hcvx
  · exact neg_mem_neg.mp <| h (-t) (neg_subset.mp hst) hcvx.neg
  · exact mem_neg.mp <| h (-t) (neg_subset_neg.mpr hst) hcvx.neg

variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

lemma convexHull_vadd (s₁ : Set V) (s₂ : Set A) :
    convexHull R (s₁ +ᵥ s₂) = convexHull R s₁ +ᵥ convexHull R s₂ := by
  apply le_antisymm
  · apply convexHull_min
    · exact vadd_subset_vadd subset_convexHull_self <| subset_convexHull_self
    apply IsConvexSet.vadd IsConvexSet.convexHull <| IsConvexSet.convexHull
  · sorry

lemma convexHull_prod (s₁ : Set X) (s₂ : Set Y) :
    convexHull R (s₁ ×ˢ s₂) = (convexHull R s₁) ×ˢ (convexHull R s₂) := by
  apply le_antisymm
  · apply convexHull_min
    · apply prod_mono <;> exact subset_convexHull_self
    apply IsConvexSet.prod <;> exact IsConvexSet.convexHull
  · sorry

end Pointwise

end Convexity

end
