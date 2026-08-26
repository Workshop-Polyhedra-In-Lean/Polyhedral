/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Pointwise
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization

/-! This file defines polyhedra as the Minkowski sums polytopes and polyhedral cones. -/


open Pointwise Set

variable {R : Type*} [Ring R] [PartialOrder R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

variable (R) in
def IsHPolyhedron (P : Set A) : Prop :=
    ∃ H : Finset (A →ᵃ[R] R), P = ⋂ h ∈ H, h ⁻¹' Set.Ici (0 : R)

variable (R) in
def IsHCone (P : Set V) : Prop :=
    ∃ H : Finset (V →ₗ[R] R), P = ⋂ h ∈ H, h ⁻¹' Set.Ici (0 : R)


lemma IsHPolyhedron.is_h_cone {C : Set V} (hC : IsHCone R C) :
    IsHPolyhedron R C := by
  sorry


lemma IsHCone.inf {P Q : Set V}
  (hP : IsHCone R P) (hQ : IsHCone R Q) :
    IsHCone R (P ∩ Q) := by
  classical
  obtain ⟨H₁, rfl⟩ := hP
  obtain ⟨H₂, rfl⟩ := hQ
  exact ⟨_, (Finset.set_biInter_inter H₁ H₂ _).symm⟩

lemma IsHCone.univ : IsHCone R (univ : Set V) := by
  use ∅
  simp

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

lemma IsHCone.dual_fg (C : PointedCone R V) (hC : C.FG) :
    IsHCone R (dual p C : Set W) := by
  obtain ⟨G, hG⟩ := hC
  classical
  use Finset.image (p ·) G
  ext
  simp [←hG, dual_hull]

lemma IsHPolyhedron.dual_fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedron R (dual p C : Set W) := by
  obtain ⟨G, hG⟩ := hC
  classical
  use Finset.image (p · |>.toAffineMap) G
  ext
  simp [←hG, dual_hull]

end CommRing

section Field

-- TODO: apply MW in this section, we should probably go to finite-dim space

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

private def p : V →ₗ[R] V →ₗ[R] R := by
  -- have inner := (by instance : InnerProductSpace R (V × V)).innerₗ
  sorry

open PointedCone in
-- TODO: we want to prove something like this for affine spaces
lemma IsHPolyhedron.submodule_dualfg (S : Submodule R V) (hS : S.DualFG p) :
    IsHPolyhedron R (S : Set V) := by
  classical
  -- have hS_dual : S.DualFG p := FG.dualfg p hS
  obtain ⟨gen, h_gen⟩ := hS
  have h_gen_ext := Submodule.ext_iff.mp h_gen
  simp only [Submodule.mem_dual, SetLike.mem_coe] at h_gen_ext
  -- let neg_gen := -gen -- Finset.image (-·) gen
  have h_neg (i : V) : i ∈ gen ↔ -i ∈ -gen := by simp
  use Finset.image (fun v ↦ (p v).toAffineMap) (gen ∪ -gen)
  ext x
  simp only [SetLike.mem_coe, Finset.mem_image, Finset.mem_union, Finset.mem_neg', iInter_exists,
    biInter_and', iInter_iInter_eq_right, LinearMap.coe_toAffineMap, mem_iInter, mem_preimage,
    mem_Ici]
  -- have h : x ∈ S ↔ ∀ i ∈ gen, p x i = (0 : R) := by
  --   sorry
  constructor
  · intro hx i hi
    have h := (h_gen_ext x).mpr hx
    cases hi
    · have h_i := h (show i ∈ gen by assumption)
      rw [h_i]
    · have h_i := h (show -i ∈ gen by assumption)
      simp only [_root_.map_neg, LinearMap.neg_apply, zero_eq_neg] at h_i
      rw [h_i]
  · intro h
    apply (h_gen_ext x).mp
    intro i hi
    have h₁ := (h i) (.inl hi)
    have h₂ := h (-i)
    simp only [neg_neg, _root_.map_neg, LinearMap.neg_apply, Left.nonneg_neg_iff] at h₂
    have h₂' := h₂ (.inr hi)
    linarith

lemma IsHPolyhedron.fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedron R (C : Set V) := by

  sorry


end Field
