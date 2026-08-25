/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineMap

/-! This file proves basic pointwise properties of convex sets. -/

noncomputable section

variable {R X V A : Type*}

namespace Convexity

section Pointwise

open Pointwise

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommMonoid V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

/- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.add {K₁ K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ + K₂) := by
  rw [← Set.add_image_prod]
  exact (hK₁.prod hK₂).image (by fun_prop)

end Semiring

section AddCommGroup

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

variable {K : Set V}

protected lemma IsConvexSet.neg (hK : IsConvexSet R K) : IsConvexSet R (-K) := by
  rw [← Set.image_neg_eq_neg]
  exact hK.image (by fun_prop)

@[simp] lemma IsConvexSet.neg_iff : IsConvexSet R (-K) ↔ IsConvexSet R K where
  mp := by nth_rw 2 [← neg_neg K]; exact .neg
  mpr := .neg

/- Minkowski subtraction preserves convexity. -/
protected lemma IsConvexSet.sub {K₁ K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ - K₂) := by
  rw [← Set.sub_image_prod]
  exact (hK₁.prod hK₂).image (by fun_prop)

end AddCommGroup

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [AddTorsor V A]
variable [ConvexSpace R A] [IsAffineConvexSpace R V A]

@[to_fun (attr := fun_prop)]
lemma IsAffineMap.vadd [ConvexSpace R X] {f : X → V} {g : X → A}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R (f +ᵥ g) := by
  sorry

/- Minkowski vector addition preserves convexity. -/
protected lemma IsConvexSet.vadd {K₁ : Set V} {K₂ : Set A}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ +ᵥ K₂) := by
  rw [← Set.vadd_image_prod]
  exact (hK₁.prod hK₂).image (by fun_prop)

/- Translation preserves convexity. -/
lemma IsConvexSet.translate (t : V) {K : Set A} (hK : IsConvexSet R K) :
    IsConvexSet R (t +ᵥ K) := by
  rw [← Set.singleton_vadd]
  exact IsConvexSet.vadd IsConvexSet.singleton hK

end Ring

section SMul

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [SMulCommClass R R V]

@[to_fun (attr := fun_prop)]
lemma IsAffineMap.const_smul [ConvexSpace R X] {f : X → V}
    (hf : IsAffineMap R f) (r : R) : IsAffineMap R (r • f) := by
  change IsAffineMap R (fun x => r • f x)
  exact (DistribSMul.toLinearMap R V r).isAffineMap.comp hf

protected lemma IsConvexSet.smul (r : R) {K : Set V} (hK : IsConvexSet R K) :
    IsConvexSet R (r • K) := by
  rw [← Set.image_smul]
  exact hK.image (by fun_prop)

end SMul

end Pointwise

end Convexity
