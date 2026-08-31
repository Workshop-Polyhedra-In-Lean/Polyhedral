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

variable {R X Y : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [ConvexSpace R Y] {C s t : Set X} {x y : X}

section Field

variable {K Z : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K Z]
  {s : Set Z} {x : Z}

/-- A point of the convex hull of `s` is exactly `sConvexComb` of some combination supported on
`s`. This gives explicit weighted-sum representatives for elements of a convex hull, which
`mem_convexHull_iff` alone (the smallest-convex-superset characterization) does not. -/
theorem mem_convexHull_iff_exists_sConvexComb :
    x ∈ convexHull K s ↔ ∃ w : StdSimplex K Z, ↑w.weights.support ⊆ s ∧ w.sConvexComb = x := by
  classical
  constructor
  · intro hx
    refine mem_convexHull_iff.mp hx
      {y | ∃ w : StdSimplex K Z, ↑w.weights.support ⊆ s ∧ w.sConvexComb = y}
      (fun a ha => ⟨.single a, by simpa using ha, by simp⟩) ?_
    apply IsConvexSet.of_convexCombPair_mem
    rintro p q hp hq hpq a ⟨wa, hwa, rfl⟩ b ⟨wb, hwb, rfl⟩
    refine ⟨convexCombPair p q hp hq hpq wa wb, ?_, by rw [sConvexComb_convexCombPair]⟩
    simp only [convexCombPair]
    intro y hy
    rw [Finset.mem_coe] at hy
    obtain ⟨d, hd, hdy⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hy)
    have hd' : d = wa ∨ d = wb := by
      have hsupp_duple : (StdSimplex.duple wa wb hp hq hpq).weights.support ⊆ {wa, wb} := by
        rw [StdSimplex.weights_duple]
        exact Finsupp.support_add.trans
          (Finset.union_subset_union Finsupp.support_single_subset Finsupp.support_single_subset)
      simpa using hsupp_duple hd
    rcases hd' with rfl | rfl
    · exact hwa (Finset.mem_coe.mpr (Finsupp.support_smul hdy))
    · exact hwb (Finset.mem_coe.mpr (Finsupp.support_smul hdy))
  · rintro ⟨w, hw, rfl⟩
    exact IsConvexSet.convexHull.sConvexComb_mem (hw.trans subset_convexHull_self)

end Field

section Pointwise

open Pointwise

variable {R V A : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

@[simp] lemma convexHull_neg (s : Set V) : -convexHull R s = convexHull R (-s) := by
  ext x
  simp only [mem_neg, mem_convexHull_iff]
  constructor <;> intro h t hst hcvx
  · exact neg_mem_neg.mp <| h (-t) (neg_subset.mp hst) hcvx.neg
  · exact mem_neg.mp <| h (-t) (neg_subset_neg.mpr hst) hcvx.neg

variable [AddTorsor V A]

noncomputable local instance : ConvexSpace R A := AddTorsor.toConvexSpace

lemma convexHull_vadd (s₁ : Set V) (s₂ : Set A) :
    convexHull R (s₁ +ᵥ s₂) = convexHull R s₁ +ᵥ convexHull R s₂ := by
  sorry

end Pointwise

end Convexity

end
