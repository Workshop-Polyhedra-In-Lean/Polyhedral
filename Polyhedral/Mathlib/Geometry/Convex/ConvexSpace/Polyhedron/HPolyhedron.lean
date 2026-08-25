/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Pointwise
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

/-! This file defines polyhedra as the Minkowski sums polytopes and polyhedral cones. -/


open Pointwise Set

variable {R : Type*} [Ring R] [PartialOrder R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

variable (R) in
def IsHPolyhedron (P : Set A) : Prop :=
    ∃ H : Finset (A →ᵃ[R] R), P = ⋂ h ∈ H, h ⁻¹' Set.Ici (0 : R)

lemma IsHPolyhedron.inf {P Q : Set A} (hP : IsHPolyhedron R P) (hQ : IsHPolyhedron R Q) :
    IsHPolyhedron R (P ∩ Q) := by
  classical
  obtain ⟨H1, rfl⟩ := hP
  obtain ⟨H2, rfl⟩ := hQ
  exact ⟨_, (Finset.set_biInter_inter H1 H2 _).symm⟩

lemma IsHPolyhedron.univ : IsHPolyhedron R (univ : Set A) := by
  use ∅
  simp

variable [IsOrderedRing R] [Nontrivial R]

lemma IsHPolyhedron.empty : IsHPolyhedron R (∅ : Set A) := by
  use { AffineMap.const R A (-1) }
  ext
  simp only [mem_empty_iff_false, Finset.mem_singleton, iInter_iInter_eq_left, AffineMap.coe_const,
    mem_preimage, Function.const_apply, mem_Ici, Left.nonneg_neg_iff, false_iff]
  exact (zero_lt_one' R).not_ge


section CommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {p : V →ₗ[R] W →ₗ[R] R}

open PointedCone

lemma IsHPolyhedron.dual_fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedron R (dual p C : Set W) := by
  obtain ⟨ G, hG ⟩ := hC
  classical
  use Finset.image (fun x ↦ (p x).toAffineMap) G
  ext
  simp [←hG, dual_hull]

end CommRing

section Field

-- TODO: apply MW in this section, we should probably go to finite-dim space

variable {R : Type*} [Field R] [PartialOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

-- TODO: we want to prove something like this for affine spaces
lemma IsHPolyhedron.submodule (S : Submodule R V) (hS : S.FG) :
    IsHPolyhedron R (S: Set V) := by
  sorry

lemma IsHPolyhedron.fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedron R (C : Set V) := by

  sorry

end Field
