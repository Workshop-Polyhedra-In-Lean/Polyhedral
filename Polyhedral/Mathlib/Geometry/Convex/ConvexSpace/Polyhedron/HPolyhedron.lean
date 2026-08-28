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
variable {W : Type*} [AddCommGroup W] [Module R W]
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
  rfl

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

section ConvexSet

open Convexity

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {A : Type*} [AddCommGroup A] [Module R A] [AddTorsor V A] --[space : ConvexSpace R A]

attribute [local instance] AddTorsor.toConvexSpace

lemma IsConvexSet.halfspace (f : A →ᵃ[R] R) : IsConvexSet R (f ⁻¹' Set.Ici 0) := by
  apply IsConvexSet.preimage
  exact f.isAffineMap
  sorry

#click_suggestions
/-- An *H*-polyhedron is a convex set -/
-- TODO: Prove this using convexity of intersections, preimages and affine subspaces
-- lemma IsConvexSet.h_polyhedron {P : Set A} (hP : IsHPolyhedron R P) : IsConvexSet R P := by
--   classical
--   obtain ⟨C', ⟨S, ⟨⟨H, hH⟩, hInter⟩⟩⟩ := hP

--   apply IsConvexSet.inter
--   · have Cf := C'.image (·.toFun ⁻¹' Set.Ici 0)
--     have h := IsConvexSet.sInter (show ∀ s ∈ Cf, IsConvexSet R s by

--       sorry
--     )
--     intro s

--     sorry
--   · sorry

--   apply IsConvexSet.of_convexCombPair_mem
--   intro a b ha hb hab x hx y hy
--   unfold convexCombPair sConvexComb AddTorsor.toConvexSpace AddTorsor.convexCombination Finset.affineCombination
--   simp
--   -- rw [show (Finsupp.single x a + Finsupp.single y b).support = {x, y} by
--   --   rw [Finsupp.support_add_eq, Finsupp.support_single, Finsupp.support_single]
--   --   simp
--   --   ]
--   sorry

def IsHPolyhedron.toConvexSet {P : Set A} (hP : IsHPolyhedron R P) : ConvexSet R A :=
    sorry --⟨P, IsConvexSet.h_polyhedron hP⟩

end ConvexSet

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

-- Simple Lemmas to prove IsConvexSet
lemma IsHPolyhedron.halfspace (f : A →ᵃ[R] R) : IsHPolyhedron R (f ⁻¹' Set.Ici 0) := by
  use {f}, ⊤
  simp


-- TODO: Maybe define coercion AffineSubspace -> HPolyhedron
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
open PointedCone Module in
/-- A finitely generated cone is H-polyhedral with respect to the standard dual pairing:
by Minkowski-Weyl (`FG.exists_dualfg_inf_span`) it is the intersection of a `DualFG` cone
with its linear span. -/
lemma PointedCone.IsHPolyhedral.fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedral (LinearMap.id (R := R) (M := Dual R V)) C := by
  obtain ⟨D, hD, hDC⟩ :=
    FG.exists_dualfg_inf_span (LinearMap.id (R := R) (M := Dual R V)) hC
  exact ⟨D, Submodule.span R (C : Set V), hD, hDC.symm⟩

open PointedCone Module in
/-- A finitely generated cone is an H-polyhedron. -/
lemma IsHPolyhedron.fg (C : PointedCone R V) (hC : C.FG) :
    IsHPolyhedron R (C : Set V) :=
  IsHPolyhedral.is_h_polyhedron _ (IsHPolyhedral.fg C hC)

end Field

section RecessionDirection

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

/-- In an H-polyhedron, a ray direction that stays inside from a single point stays inside
from every point: if `a • v +ᵥ x ∈ P` for all `a ≥ 0` for some `x ∈ P`, then the same holds
from every `y ∈ P`.

This is the H-polyhedral (and topology-free) version of the fact that for closed convex sets
membership in the recession cone can be tested at a single point; for general non-closed
convex sets it fails. As a consequence, the `∀`- and `∃`-versions of the recession cone of an
H-polyhedron agree, see `IsHPolyhedron.forall_smul_vadd_mem_iff_exists`. -/
theorem IsHPolyhedron.smul_vadd_mem_of_forall_smul_vadd_mem {P : Set A}
    (hP : IsHPolyhedron R P) {x : A} (hx : x ∈ P) {v : V}
    (hxv : ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P) {y : A} (hy : y ∈ P) {a : R} (ha : 0 ≤ a) :
    a • v +ᵥ y ∈ P := by
  obtain ⟨H, S, rfl⟩ := hP
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici,
    SetLike.mem_coe, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add] at hx hy hxv ⊢
  refine ⟨fun h hh => ?_, ?_⟩
  · -- every defining functional is nonnegative on `v`, else walking far along the ray
    -- from `x` would violate its inequality
    have hlin : 0 ≤ h.linear v := by
      by_contra hneg
      push Not at hneg
      have h0 : (0 : R) ≤ h x := hx.1 h hh
      have hdiv : (0 : R) ≤ (h x + 1) / (-h.linear v) :=
        div_nonneg (by linarith) (by linarith)
      have hkey := (hxv _ hdiv).1 h hh
      have hcancel : (h x + 1) / (-h.linear v) * (-h.linear v) = h x + 1 :=
        div_mul_cancel₀ _ (by linarith)
      linarith
    exact add_nonneg (mul_nonneg ha hlin) (hy.1 h hh)
  · -- `v` lies in the direction of the affine subspace
    have hv : v ∈ S.direction := by
      have h1 : (1 : R) • v +ᵥ x ∈ S := (hxv 1 zero_le_one).2
      rw [one_smul] at h1
      simpa using AffineSubspace.vsub_mem_direction h1 hx.2
    exact AffineSubspace.vadd_mem_of_mem_direction (S.direction.smul_mem a hv) hy.2

/-- For a nonempty H-polyhedron, a direction recedes from every point as soon as it recedes
from a single point. In particular the `∀`-definition of the recession cone
(see `Convex.Set.recess`) agrees with the `∃`-version. -/
theorem IsHPolyhedron.forall_smul_vadd_mem_iff_exists {P : Set A} (hP : IsHPolyhedron R P)
    (hne : P.Nonempty) {v : V} :
    (∀ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P) ↔
      ∃ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, h x hx⟩
  · rintro ⟨x, hx, hxv⟩ y hy a ha
    exact hP.smul_vadd_mem_of_forall_smul_vadd_mem hx hxv hy ha

end RecessionDirection
