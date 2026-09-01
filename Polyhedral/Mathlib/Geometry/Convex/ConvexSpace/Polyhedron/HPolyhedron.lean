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
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization

/-! This file defines polyhedra as the Minkowski sums polytopes and polyhedral cones. -/


open Pointwise Set

-- CommRing could be Ring for some definitions
variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {V' : Type*} [AddCommGroup V'] [Module R V']
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
variable (p : V' →ₗ[R] V →ₗ[R] R)

/--
A cone is *H-polyhedral* if it is the intersection of a submodule and
a cone with finitely generated dual.

One advantage of allowing non-coFG submodules is that the dual of a polyhedral
cone is polyhedral even under infinite dimension.
TODO: prove
-/
def IsHPolyhedral (p : V' →ₗ[R] V →ₗ[R] R) (P : PointedCone R V) : Prop :=
    ∃C : PointedCone R V, ∃S : Submodule R V, C.DualFG p ∧ P = C ⊓ S

/--
The dual of a *V-polyhedral cone* is an *H-polyhedral cone*.
-/
theorem IsHPolyhedral.dual_isPolyhedral (p : V →ₗ[R] V' →ₗ[R] R) {C : PointedCone R V}
    (h : IsPolyhedral C) : IsHPolyhedral p (PointedCone.dual p C.carrier) := by
  classical
  obtain ⟨C', ⟨hFG, ⟨S, rfl⟩⟩⟩ := h
  use PointedCone.dual p C', Submodule.dual p S
  -- The proof below is *basically* by-definition, so it should be easier to write
  constructor
  · exact FG.dual_dualfg p hFG
  · rw [← coe_dual]
    ext x
    constructor
    · intro hx
      simp [dual] at hx
      -- Use 0 on hx to get rid of the term we don't want on each case
      constructor
      · intro v hv
        simpa using hx v hv 0 (Submodule.zero_mem S)
      · intro v hv
        simpa using hx 0 (Submodule.zero_mem C') v hv
    · intro hx
      simp only [Submodule.carrier_eq_coe, dual_sup, Submodule.coe_restrictScalars, mem_dual,
        mem_union, SetLike.mem_coe]
      intro v hv
      obtain ⟨hx₁, hx₂⟩ := hx
      apply Or.by_cases hv
      · intro hv
        exact hx₁ hv
      · intro hv
        simp [hx₂ hv]


section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {V' : Type*} [AddCommGroup V'] [Module R V']
variable {A : Type*} [AddTorsor V A]

#click_suggestions
theorem IsPolyhedral.dual_isHPolyhedral (p : V →ₗ[R] V' →ₗ[R] R)
    [Fact p.SeparatingRight] {C : PointedCone R V}
    (h : IsHPolyhedral p.flip C) : IsPolyhedral (PointedCone.dual p C.carrier) := by
  classical
  obtain ⟨C', ⟨S, ⟨hDualFG, rfl⟩⟩⟩ := h
  use PointedCone.dual p C'
  constructor
    -- Note: DualFG.dual_fg requires a field with linear order + p.SeparatingRight,
    --       while the dual `FG.dual_dualfg` requires none of these.
  · exact DualFG.dual_fg hDualFG
  · use Submodule.dual p S
    ext x
    constructor
    · intro h
      simp [PointedCone.dual, Submodule.dual] at ⊢ h

      sorry
    · sorry

end Field

/-- A polyhedral cone is a polyhedron -/
lemma IsHPolyhedral.isHPolyhedron
  {C : PointedCone R V} (p : V' →ₗ[R] V →ₗ[R] R) (hC : IsHPolyhedral p C) :
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

variable (p : V' →ₗ[R] V →ₗ[R] R)

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
variable {A : Type*} [AddCommGroup A] [Module R A] [AddTorsor V A] --[space : ConvexSpace R A]

attribute [local instance] AddTorsor.toConvexSpace

lemma isConvexSet_Iic (b : R) : IsConvexSet R (Set.Iic b) := by
  classical
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := R)
  refine IsConvexSet.of_sConvexComb_mem fun w hw => ?_
  rw [sConvexComb_eq_sum, Finsupp.sum]
  have hle : ∀ m ∈ w.weights.support, w.weights m • m ≤ w.weights m * b := fun m hm => by
    rw [smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hw hm) (Finsupp.le_def.mp w.nonneg m)
  refine Set.mem_Iic.mpr (le_trans (Finset.sum_le_sum hle) ?_)
  rw [← Finset.sum_mul]
  have htot := w.total
  rw [Finsupp.sum] at htot
  rw [htot, one_mul]

lemma isConvexSet_Ici (b : R) : IsConvexSet R (Set.Ici b) := by
  classical
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := R)
  refine IsConvexSet.of_sConvexComb_mem fun w hw => ?_
  rw [sConvexComb_eq_sum, Finsupp.sum]
  have hle : ∀ m ∈ w.weights.support, w.weights m * b ≤ w.weights m • m := fun m hm => by
    rw [smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hw hm) (Finsupp.le_def.mp w.nonneg m)
  refine Set.mem_Ici.mpr (le_trans ?_ (Finset.sum_le_sum hle))
  rw [← Finset.sum_mul]
  have htot := w.total
  rw [Finsupp.sum] at htot
  rw [htot, one_mul]

omit [AddCommGroup A] [Module R A] in
lemma IsConvexSet.halfspace (f : A →ᵃ[R] R) : IsConvexSet R (f ⁻¹' Set.Ici 0) :=
  (isConvexSet_Ici 0).preimage f.isAffineMap

end ConvexSet

section ConvexityOfHPolyhedra

open Convexity

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

attribute [local instance] AddTorsor.toConvexSpace

/-- Affine subspaces are convex. -/
lemma AffineSubspace.isConvexSet (T : AffineSubspace R A) : IsConvexSet R (T : Set A) := by
  rcases (T : Set A).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · rw [he]
    exact IsConvexSet.empty
  · let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := V)
    have hT : (T : Set A)
        = ((AffineEquiv.vaddConst R x₀).symm.toAffineMap : A →ᵃ[R] V) ⁻¹' T.direction := by
      ext y
      simp only [Set.mem_preimage, AffineEquiv.coe_toAffineMap,
        AffineEquiv.vaddConst_symm_apply, SetLike.mem_coe]
      exact (AffineSubspace.vsub_right_mem_direction_iff_mem hx₀ y).symm
    rw [hT]
    exact T.direction.isConvexSet.preimage (AffineMap.isAffineMap _)

/-- H-polyhedra are convex. -/
lemma IsHPolyhedron.isConvexSet {P : Set A} (hP : IsHPolyhedron R P) : IsConvexSet R P := by
  obtain ⟨H, T, rfl⟩ := hP
  refine IsConvexSet.inter ?_ (AffineSubspace.isConvexSet T)
  rw [show (⋂ h ∈ H, ⇑h ⁻¹' Set.Ici (0 : R))
      = ⋂₀ ((fun h : A →ᵃ[R] R => ⇑h ⁻¹' Set.Ici (0 : R)) '' ↑H) by simp [Set.sInter_image]]
  refine IsConvexSet.sInter ?_
  rintro s ⟨h, -, rfl⟩
  exact IsConvexSet.halfspace h

/-- An H-polyhedron, bundled as a convex set. -/
def IsHPolyhedron.toConvexSet {P : Set A} (hP : IsHPolyhedron R P) : ConvexSet R A :=
  ⟨P, hP.isConvexSet⟩

end ConvexityOfHPolyhedra

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
variable {V' : Type*} [AddCommGroup V'] [Module R V']
variable {p : V →ₗ[R] V' →ₗ[R] R}

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
    IsHPolyhedron R (dual p C : Set V') := by
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
  IsHPolyhedral.isHPolyhedron _ (IsHPolyhedral.fg C hC)

variable {V' : Type*} [AddCommGroup V'] [Module R V']

open PointedCone in
/-- An H-polyhedral cone with respect to any pairing is polyhedral: its defining functionals
are in particular plain linear functionals (`DualFG.id`), so the full dual pairing machinery
applies. -/
lemma PointedCone.IsHPolyhedral.isPolyhedral {q : V' →ₗ[R] V →ₗ[R] R} {C : PointedCone R V}
    (hC : IsHPolyhedral q C) : IsPolyhedral C := by
  obtain ⟨D, S, hD, rfl⟩ := hC
  exact .of_dualfg_inf_submodule hD.id S

open PointedCone in
/-- The dual of an H-polyhedral cone is polyhedral. -/
theorem PointedCone.IsPolyhedral.isHPolyhedral (q : V →ₗ[R] V' →ₗ[R] R) {C : PointedCone R V}
    (h : IsHPolyhedral q.flip C) : IsPolyhedral (PointedCone.dual q C.carrier) :=
  h.isPolyhedral.dual q

variable {V' : Type*} [AddCommGroup V'] [Module R V']

open PointedCone in
/-- An H-polyhedral cone with respect to any pairing is polyhedral: its defining functionals
are in particular plain linear functionals (`DualFG.id`), so the full dual pairing machinery
applies. -/
lemma PointedCone.IsHPolyhedral.isPolyhedral' {q : V' →ₗ[R] V →ₗ[R] R} {C : PointedCone R V}
    (hC : IsHPolyhedral q C) : IsPolyhedral C := by
  obtain ⟨D, S, hD, rfl⟩ := hC
  exact .of_dualfg_inf_submodule hD.id S

open PointedCone in
/-- The dual of an H-polyhedral cone is polyhedral. -/
theorem PointedCone.IsPolyhedral.of_h_repr (q : V →ₗ[R] V' →ₗ[R] R) {C : PointedCone R V}
    (h : IsHPolyhedral q.flip C) : IsPolyhedral (PointedCone.dual q C.carrier) :=
  h.isPolyhedral.dual q

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
    (hxv : ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P)
    {y : A} (hy : y ∈ P) {a : R} (ha : 0 ≤ a) : a • v +ᵥ y ∈ P := by
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
