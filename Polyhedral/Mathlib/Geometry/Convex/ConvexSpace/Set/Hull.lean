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

variable {R V A X Y : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [ConvexSpace R Y]

lemma convexHull_prod (s : Set X) (t : Set Y) :
  convexHull R (s ×ˢ t) = (convexHull R s) ×ˢ (convexHull R t) := by
  apply Set.Subset.antisymm
  · refine convexHull_min
      (prod_mono subset_convexHull_self subset_convexHull_self) ?_
    exact IsConvexSet.convexHull.prod IsConvexSet.convexHull
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    let ιX (y₀ : Y) := fun x₀ : X ↦ (x₀, y₀)
    have hX (y₀ : Y) : IsAffineMap R (ιX y₀) := by
      constructor
      intro w
      ext <;> simp [ιX]
    let ιY (x₀ : X) := fun y₀ : Y ↦ (x₀, y₀)
    have hY (x₀ : X) : IsAffineMap R (ιY x₀) := by
      constructor
      intro w
      ext <;> simp [ιY]
    have hx_prod (y₀ : Y) (hy₀ : y₀ ∈ t) :
        (x, y₀) ∈ convexHull R (s ×ˢ t) := by
      refine convexHull_mono (s := (ιX y₀) '' s) ?_ ?_
      · rintro _ ⟨x₀, hx₀, rfl⟩
        exact ⟨hx₀, hy₀⟩
      · rw [← (hX y₀).image_convexHull s]
        exact ⟨x, hx, rfl⟩
    rw [← IsConvexSet.convexHull.convexHull_eq_self]
    refine convexHull_mono (s := (ιY x) '' t) ?_ ?_
    · rintro _ ⟨y', hy', rfl⟩
      exact hx_prod y' hy'
    · rw [← (hY x).image_convexHull t]
      exact ⟨y, hy, rfl⟩

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
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
  rw [← vadd_image_prod, ← vadd_image_prod]
  rw [← IsAffineMap.image_convexHull]
  · rw [convexHull_prod]
  · fun_prop

end Ring

end Pointwise

end Convexity

end
