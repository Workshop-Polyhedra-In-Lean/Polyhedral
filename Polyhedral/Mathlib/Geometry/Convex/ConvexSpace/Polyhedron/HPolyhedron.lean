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

-- CommRing could be Ring for some definitions
variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {W : Type*} [AddCommGroup W] [Module R W] -- [Module R (W →ₗ[R] R)]
variable {A : Type*} [AddTorsor V A]


variable (R) in
/--
An *H-polyhedron* is a set can be defined as the restriction of an
affine subspace with a finite number of affine inequalities.
-/
def IsHPolyhedron (P : Set A) : Prop :=
    ∃ H : Finset (A →ᵃ[R] R), ∃ S : AffineSubspace R A,
      P = (⋂ h ∈ H, h ⁻¹' Set.Ici (0 : R)) ∩ S


namespace PointedCone
variable (p : W →ₗ[R] V →ₗ[R] R)

/--
A cone is *H-polyhedral* if it is the intersection of a submodule and
a cone with finitely generated dual.

One advantage of allowing non-coFG submodules is that the dual of a polyhedral
cone is polyhedral even under infinite dimension.
TODO: prove
-/
def IsHPolyhedral (p : W →ₗ[R] V →ₗ[R] R) (P : PointedCone R V) : Prop :=
    ∃C : PointedCone R V, ∃S : Submodule R V, C.DualFG p ∧ P = C ⊓ S

/-- A polyhedral cone is a polyhedron -/
lemma IsHPolyhedral.is_h_polyhedron
  {C : PointedCone R V} (p : W →ₗ[R] V →ₗ[R] R) (hC : IsHPolyhedral p C) :
    IsHPolyhedron R C.carrier := by classical
  obtain ⟨C', ⟨S, ⟨⟨H, hH⟩, hInter⟩⟩⟩ := hC
  use H.image (p · |>.toAffineMap), S
  ext x
  simp only [hInter, Submodule.carrier_eq_coe, Submodule.coe_inf, Submodule.coe_restrictScalars,
    mem_inter_iff, SetLike.mem_coe, Finset.mem_image, iInter_exists, biInter_and',
    iInter_iInter_eq_right, LinearMap.coe_toAffineMap, mem_iInter, mem_preimage, mem_Ici,
    Submodule.mem_toAffineSubspace, and_congr_left_iff, ←hH]
  intro hS
  rw [show (x ∈ dual p ↑H) = {y | ∀ ⦃x : W⦄, x ∈ ↑H → 0 ≤ (p x) y} x from rfl]
  exact Eq.to_iff rfl

variable (p : W →ₗ[R] V →ₗ[R] R)

/-- The intersection of polyhedral cones is polyhedral -/
lemma IsHPolyhedral.inf {P Q : PointedCone R V}
  (hP : IsHPolyhedral p P) (hQ : IsHPolyhedral p Q) :
    IsHPolyhedral p (P ⊓ Q) := by
  classical
  obtain ⟨H₁, ⟨S₁, ⟨⟨H_dual_gen₁, h_gen₁⟩, h_inter₁⟩⟩⟩ := hP
  obtain ⟨H₂, ⟨S₂, ⟨⟨H_dual_gen₂, h_gen₂⟩, h_inter₂⟩⟩⟩ := hQ
  use H₁ ⊓ H₂, S₁ ⊓ S₂
  constructor
  · use H_dual_gen₁ ⊔ H_dual_gen₂
    simp [dual_union, h_gen₁, h_gen₂]
  · ext x
    simp [h_inter₁, h_inter₂]
    tauto

/-- The full cone is polyhedral. -/
lemma IsHPolyhedral.top : IsHPolyhedral p (⊤ : PointedCone R V) :=
  by use ⊤, ⊤; simp

/-- The null cone is polyhedral. -/
lemma IsHPolyhedral.zero : IsHPolyhedral p (⊥ : PointedCone R V) :=
  by use ⊤, ⊥; simp

-- `∅` is not even a `PointedCone R V`, so we cannot state the following lemma:
-- lemma empty_not_is_h_cone : ¬ IsHPolyhedral p (∅ : Set V) := by
--   sorry

end PointedCone

section PartialOrder
omit [IsOrderedRing R]

/-- The intersection of H-polyhedra is an H-polyhedron. -/
lemma IsHPolyhedron.inf {P Q : Set A} (hP : IsHPolyhedron R P) (hQ : IsHPolyhedron R Q) :
    IsHPolyhedron R (P ∩ Q) := by
  classical
  obtain ⟨H₁, ⟨S₁, ⟨⟨H_dual_gen₁, h_gen₁⟩, h_inter₁⟩⟩⟩ := hP
  obtain ⟨H₂, ⟨S₂, ⟨⟨H_dual_gen₂, h_gen₂⟩, h_inter₂⟩⟩⟩ := hQ
  use H₁ ∪ H₂, S₁ ⊓ S₂
  ext x
  simp only [
    mem_inter_iff, mem_iInter, mem_preimage, mem_Ici, SetLike.mem_coe, Finset.mem_union,
    forall₂_or_left, AffineSubspace.mem_inf_iff]
  tauto

/-- Submodules are H-polyhedra. -/
lemma IsHPolyhedron.affine_subspace (S : AffineSubspace R V) :
    IsHPolyhedron R S.carrier :=
  by use ∅, S; simp

/-- The full space is an H-polyhedron. -/
lemma IsHPolyhedron.univ : IsHPolyhedron R (univ : Set A) :=
  by use ∅, ⊤; simp

lemma IsHPolyhedron.empty : IsHPolyhedron R (∅ : Set A) :=
  by use { AffineMap.const R A (-1) }, ⊥; simp

end PartialOrder

section CommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {p : V →ₗ[R] W →ₗ[R] R}

open PointedCone


/-!
TODO: The following lemmas need to be translated to use the new definition, and checked
-/
/- lemma IsHPolyhedral.dual_fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedral p (dual p C) := by classical
  obtain ⟨G, hG⟩ := hC
  classical
  use Finset.image (p ·) G
  ext
  simp [←hG, dual_hull]


-- should be easier now: simply apply
-- IsHPolyhedral.dual_fg and IsHPolyhedron.is_h_cone
lemma IsHPolyhedron.dual_fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedron R (dual p C : Set W) := by
  obtain ⟨G, hG⟩ := hC
  classical
  use Finset.image (p · |>.toAffineMap) G
  ext
  simp [←hG, dual_hull] -/

end CommRing

section Field

-- TODO: apply MW in this section, we should probably go to finite-dim space

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {p : V →ₗ[R] V →ₗ[R] R}

-- TODO get rid of this:
-- private def p : V →ₗ[R] V →ₗ[R] R := by
  -- have inner := (by instance : InnerProductSpace R (V × V)).innerₗ
--  sorry

open PointedCone in
-- TODO: we want to prove that an affine space is an HPolyhedron
/- lemma IsHPolyhedral.submodule_dualfg (S : Submodule R V) (hS : S.DualFG p) :
    IsHPolyhedral p S := by
  classical
  obtain ⟨gen, h_gen⟩ := hS
  have h_gen_ext := Submodule.ext_iff.mp h_gen
  simp only [Submodule.mem_dual, SetLike.mem_coe] at h_gen_ext
  have h_neg (i : V) : i ∈ gen ↔ -i ∈ -gen := by simp
  use Finset.image (fun v ↦ (p v)) (gen ∪ -gen)
  ext x
  simp only [SetLike.mem_coe, Finset.mem_image, Finset.mem_union, Finset.mem_neg', iInter_exists,
    biInter_and', iInter_iInter_eq_right, mem_iInter, mem_preimage,
    mem_Ici]
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
    linarith -/

lemma IsHPolyhedron.fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedron R (C : Set V) := by

  sorry


end Field
