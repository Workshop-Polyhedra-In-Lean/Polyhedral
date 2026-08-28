/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

/-! This file defines the pointwise operations on convex polytopes. -/

noncomputable section

namespace Convexity

namespace IsPolytope

variable {R X Y V A : Type*}

open ConvexSpace

section Pointwise

open Pointwise

section AddCommGroup

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

variable {P P₁ P₂ : Set V}

protected lemma neg (hP : IsPolytope R P) : IsPolytope R (-P) := by classical
  obtain ⟨s, rfl⟩ := hP
  use -s
  simp only [convexHull_neg, Finset.coe_neg]

@[simp] lemma neg_iff : IsPolytope R (-P) ↔ IsPolytope R P where
  mp := by nth_rw 2 [← neg_neg P]; exact .neg
  mpr := .neg

end AddCommGroup

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

/- The Minkowski sum of two polytopes is a polytope. -/
protected lemma vadd {P₁ : Set V} {P₂ : Set A} (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) :
    IsPolytope R (P₁ +ᵥ P₂) := by classical
  obtain ⟨s₁, rfl⟩ := hP₁
  obtain ⟨s₂, rfl⟩ := hP₂
  use s₁ +ᵥ s₂
  rw [Finset.coe_vadd, convexHull_vadd]

/- Minkowski translation of a polytope is a polytope. -/
lemma translate (t : V) {K : Set A} (hK : IsPolytope R K) : IsPolytope R (t +ᵥ K) := by
  rw [← Set.singleton_vadd]
  exact (IsPolytope.singleton R t).vadd hK

/- The Minkowski addition of two polytopes is a polytope. -/
protected lemma add {P₁ : Set V} {P₂ : Set V}
    (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) : IsPolytope R (P₁ + P₂) :=
  hP₁.vadd hP₂

/- The Minkowski subtraction of two polytopes is a polytope. -/
protected lemma sub {P₁ : Set V} {P₂ : Set V}
    (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) : IsPolytope R (P₁ - P₂) := by
  rw [sub_eq_add_neg]
  exact hP₁.add hP₂.neg

variable [SMulCommClass R R V]

-- TODO: golf + move inside proof below?
lemma convexHull_smul_ (r : R) (s : Set V)
    : (convexHull R) (r • s) = r • (convexHull R) s := by
  rw [← Set.image_smul]
  apply symm
  let f := DistribSMul.toLinearMap R V r
  have h : IsAffineMap R f := f.isAffineMap
  exact Convexity.IsAffineMap.image_convexHull (f:=f) h s

protected lemma smul (r : R) {K : Set V} (hK : IsPolytope R K) :
    IsPolytope R (r • K) := by
  classical
  obtain ⟨s, rfl⟩ := hK
  use s.image (r • ·)
  rw [Finset.coe_image, Set.image_smul]
  rw [← convexHull_smul_]

end Ring

end Pointwise

end IsPolytope

end Convexity
