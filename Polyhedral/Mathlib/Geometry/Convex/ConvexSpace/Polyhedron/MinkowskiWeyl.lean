/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Pointwise
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.RecessionCone
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.HPolyhedron
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.Basic

/-! # Minkowski-Weyl for polyhedra

This file transfers between H- and V-descriptions of polyhedra via homogenization. -/

section Homogenization

open Convexity Pointwise Set PointedCone Submodule
open Convexity.ConvexSet

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {V' : Type*} [AddCommGroup V'] [Module 𝕜 V']
variable {W : Type*} [AddCommGroup W] [Module 𝕜 W]

variable {A : Type*} [AddTorsor V A]


attribute [local instance] AddTorsor.toConvexSpace

section Homogenize

variable [IsModuleConvexSpace 𝕜 W]
variable [hom : Affine.IsHomogenization 𝕜 A W]

/--
The dehomogenization of an H-polyhedral cone is an H-polyhedron: each functional `f`
cutting out the cone descends to the affine map `f ∘ ofPoint`, and the submodule pulls back
to an affine subspace.
-/
lemma ConvexSet.dehomogenize_isHPolyhedron (C : PointedCone 𝕜 W)
    (hC : IsHPolyhedral .id C) :
    IsHPolyhedron 𝕜 (PointedCone.dehomogenize A C : Set A) := by
  classical
  obtain ⟨D, S, ⟨G, rfl⟩, rfl⟩ := hC
  refine ⟨G.image fun f => f.toAffineMap.comp hom.ofPoint,
    S.toAffineSubspace.comap hom.ofPoint, ?_⟩
  ext x
  simp [PointedCone.dehomogenize, ConvexSet.dehomogenize, Set.mem_preimage,
    PointedCone.mem_dual, Submodule.mem_toAffineSubspace]


open Convex

variable (W) in
/-- The closure of the homogenization of a convex set includes its recession cone. -/
def Convexity.ConvexSet.homogenize_closure (S : ConvexSet 𝕜 A) : PointedCone 𝕜 W :=
    homogenize W S ⊔ ((S : Set A).recessionCone 𝕜).map hom.ofVector

/--
Dehomogenizing the sum of a cone embedded at weight zero and the homogenization of a
convex set yieds the pointwise sum.
-/
-- TODO: `C +ᵥ P` should be a convex set, and this equality should be on `ConvexSet`s.
lemma dehomogenize_map_ofVector_sup_homogenize (C : PointedCone 𝕜 V) (P : ConvexSet 𝕜 A) :
    (PointedCone.dehomogenize A (homogenize W P ⊔ C.map hom.ofVector) : Set A)
      = (C : Set V) +ᵥ (P : Set A) := by
  ext x
  simp only [PointedCone.dehomogenize, ConvexSet.dehomogenize, ConvexSet.mk_eq,
    Set.mem_preimage, sup_comm]
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc, rfl⟩ := PointedCone.mem_map.mp hy
    have hw : hom.weight z = 1 := by
      have := congrArg hom.weight hyz
      simpa [hom.weight_zero, hom.weight_one] using this
    obtain ⟨r, hr, _, ⟨y', hy', rfl⟩, rfl⟩ :=
      Set.mem_smul.mp <| smul_pos_of_mem_homogenize hz (by rintro rfl; simp at hw)
    have hr1 : r = 1 := by simpa [hom.weight_one] using hw
    refine Set.mem_vadd.mpr ⟨c, hc, y', hy', hom.ofPoint_injective ?_⟩
    rw [AffineMap.map_vadd]
    simpa [hr1, vadd_eq_add] using hyz
  · rintro ⟨c, hc, y, hy, rfl⟩
    rw [AffineMap.map_vadd, vadd_eq_add]
    exact Submodule.add_mem_sup (PointedCone.mem_map.mpr ⟨c, hc, rfl⟩)
      (mem_span_of_mem (Set.mem_image_of_mem _ hy))

/--
The dehomogenization of the homogenization closure recovers the original set.
-/
-- TODO: We need `ext` because `dehomogenize_map_ofVector_sup_homogenize` is stated for `Set` instead
--       of `ConvexSet`
lemma dehomogenize_homogenize_closure (S : ConvexSet 𝕜 A) :
    (PointedCone.dehomogenize A (homogenize_closure W S)) = S := by
  ext x
  rw [homogenize_closure, ConvexSet.mem_mk, ConvexSet.carrier_eq_coe,
    dehomogenize_map_ofVector_sup_homogenize, Convex.Set.recessionCone_vadd_self, SetLike.mem_coe]

/--
The weight-zero slice of the homogenization with closure consists exactly of the
embedded recession directions.
-/
lemma mem_map_recessionCone_of_weight_eq_zero {S : ConvexSet 𝕜 A} {z : W}
    (hz : z ∈ homogenize_closure W S)
    (hw : hom.weight z = 0) :
    z ∈ hom.ofVector '' ((S : Set A).recessionCone 𝕜) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨v, hv, rfl⟩ := PointedCone.mem_map.mp hm
  have hwh : hom.weight h = 0 := by
    simpa [hom.weight_zero] using hw
  have h0 : h = 0 := by
    by_contra h0
    obtain ⟨r, hr, _, ⟨y, -, rfl⟩, rfl⟩ :=
      Set.mem_smul.mp <| smul_pos_of_mem_homogenize hh h0
    rw [map_smul, hom.weight_one, smul_eq_mul, mul_one] at hwh
    exact (Set.mem_Ioi.mp hr).ne' hwh
  rw [h0, zero_add]
  exact PointedCone.mem_map.mpr ⟨v, hv, rfl⟩

end Homogenize

-- `H = (C + S) +ᵥ P` should become the definition of `IsVPolyhedron`


/- Minkowski-Weyl for polyhedral cones -/
variable {p : V' →ₗ[𝕜] V →ₗ[𝕜] 𝕜}

-- TODO: Redundancy with V -> H (?)
-- TODO: The `Fact (Surjective p)` should not be necessary (?)
lemma isHPolyhedral_of_isVPolyhedral [Fact (Function.Surjective p)] {C : PointedCone 𝕜 V}
    (hC : IsPolyhedral C) : IsHPolyhedral p C := by
  obtain ⟨D, hD, hDC⟩ := hC.exists_dualfg_inf_span p
  exact ⟨D, Submodule.span 𝕜 (C : Set V), hD, hDC.symm⟩

section Homogenize

variable [IsModuleConvexSpace 𝕜 W]
variable [hom : Affine.IsHomogenization 𝕜 A W]

include hom in
/--
The Minkowski sum of an H-polyhedral cone and a polytope is an H-polyhedron: lift the
cone to weight zero in the homogenization space, add the homogenization of the polytope,
and dehomogenize the resulting polyhedral cone.
-/
lemma IsHPolyhedron.isPolyhedral_vadd_isPolytope {C : PointedCone 𝕜 V}
    (hC : IsHPolyhedral .id C) {P : Set A} (hP : IsPolytope 𝕜 P) :
    IsHPolyhedron 𝕜 ((C : Set V) +ᵥ P) := by
  have hpoly : ((homogenize W (⟨P, hP.isConvexSet⟩ : ConvexSet 𝕜 A))
      ⊔ C.map hom.ofVector).IsPolyhedral :=
    (IsPolyhedral.of_fg (IsPolytope.homogenize_fg W hP)).sup
      (hC.isPolyhedral.map hom.ofVector)
  simpa [dehomogenize_map_ofVector_sup_homogenize] using
    ConvexSet.dehomogenize_isHPolyhedron (A := A) _ (isHPolyhedral_of_isVPolyhedral hpoly)

end Homogenize

/- Minkowski-Weyl for polyhedra -/
open Convex

-- def IsHPolyhedron.vertices {P : Set A}
-- (hP : IsHPolyhedron R P) : Finset { v ∈ Set A | IsFace 0 hP v}

-- TODO: This should be a more general theorem in Mathlib
/--
If an affine functional is nonnegative along the ray `a • v +ᵥ x`, `a ≥ 0`, then its
linear part is nonnegative on the direction `v`.
-/
lemma AffineMap.linear_nonneg_of_forall_nonneg (h : A →ᵃ[𝕜] 𝕜) {x : A} {v : V}
    (hray : ∀ a : 𝕜, 0 ≤ a → 0 ≤ h (a • v +ᵥ x)) : 0 ≤ h.linear v := by
  by_contra hneg
  push Not at hneg
  have h0 : (0 : 𝕜) ≤ h x := by simpa using hray 0 le_rfl
  have hdiv : (0 : 𝕜) ≤ (h x + 1) / (-h.linear v) := div_nonneg (by linarith) (by linarith)
  have hkey := hray _ hdiv
  simp only [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add] at hkey
  have hcancel : (h x + 1) / (-h.linear v) * (-h.linear v) = h x + 1 :=
    div_mul_cancel₀ _ (by linarith)
  linarith

section Homogenize

variable [IsModuleConvexSpace 𝕜 W]
variable [hom : Affine.IsHomogenization 𝕜 A W]

omit [LinearOrder 𝕜] [IsOrderedRing 𝕜] [IsModuleConvexSpace 𝕜 W] in
-- TODO: This should be added to the new Mathlib homogenization API
-- TODO: This could receive the point `x₀` as an argument, and defer the burden of
--       choice on the users
/--
Every affine functional extends to a linear functional on the homogenization space which
agrees with it on points and with its linear part on vectors.
-/
lemma Affine.IsHomogenization.exists_linear_extension (h : A →ᵃ[𝕜] 𝕜) :
    ∃ F : W →ₗ[𝕜] 𝕜, (∀ x : A, F (hom.ofPoint x) = h x) ∧
      ∀ v : V, F (hom.ofVector v) = h.linear v := by
  obtain ⟨F, hF, -⟩ := hom.extend 𝕜 h
  have hFx : ∀ x : A, F (hom.ofPoint x) = h x := fun x => congrFun hF x
  refine ⟨F, hFx, fun v => ?_⟩
  have x₀ := Classical.arbitrary A
  have hv : hom.ofVector v = hom.ofPoint (v +ᵥ x₀) - hom.ofPoint x₀ := by simp
  rw [hv, map_sub, hFx, hFx]
  simp


variable (W) in
omit [IsModuleConvexSpace 𝕜 W] in
/--
The homogenization of an H-polyhedron, together with its recession cone placed at weight
zero, is an H-polyhedral cone.
-/
theorem PointedCone.homogenize_sup_recessionCone_isHPolyhedral
    {S : ConvexSet 𝕜 A} (hS : IsHPolyhedron 𝕜 (S : Set A)) :
    IsHPolyhedral .id (homogenize_closure W S) := by
  classical
  by_cases hne : (S : Set A).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨H, T, hST⟩ := hS
    choose ext hext hextlin using hom.exists_linear_extension
    have hmem : ∀ x : A, x ∈ (S : Set A) ↔ (∀ h ∈ H, 0 ≤ h x) ∧ x ∈ T := by
      intro x
      rw [hST]
      simp
    have hx₀T : x₀ ∈ T := ((hmem x₀).mp hx₀).2
    refine ⟨dual .id ↑(insert hom.weight (H.image ext)),
      T.direction.map hom.ofVector ⊔ 𝕜 ∙ hom.ofPoint x₀,
      ⟨insert hom.weight (H.image ext), rfl⟩, ?_⟩
    apply le_antisymm
    · refine sup_le ?_ ?_
      · -- generators `ofPoint x`, `x ∈ S`
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨hxH, hxT⟩ := (hmem x).mp hx
        refine Submodule.mem_inf.mpr ⟨PointedCone.mem_dual.mpr fun g hg => ?_, ?_⟩
        · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image,
            Set.mem_image, Finset.mem_coe] at hg
          rcases hg with rfl | ⟨h, hh, rfl⟩
          · simp [hom.weight_one]
          · simpa [hext] using hxH h hh
        · have : hom.ofPoint x = hom.ofVector (x -ᵥ x₀) + hom.ofPoint x₀ := by simp
          rw [this]
          exact Submodule.add_mem_sup
            (Submodule.mem_map_of_mem (AffineSubspace.vsub_mem_direction hxT hx₀T))
            (Submodule.mem_span_singleton_self _)
      · -- recession directions at weight zero
        rintro _ ⟨v, hv, rfl⟩
        have hvlin : ∀ h ∈ H, 0 ≤ h.linear v := fun h hh =>
          AffineMap.linear_nonneg_of_forall_nonneg h (x := x₀) fun a ha =>
            ((hmem _).mp (hv x₀ hx₀ a ha)).1 h hh
        have hvdir : v ∈ T.direction := by
          have h1 := ((hmem _).mp (hv x₀ hx₀ 1 zero_le_one)).2
          rw [one_smul] at h1
          simpa using AffineSubspace.vsub_mem_direction h1 hx₀T
        refine Submodule.mem_inf.mpr ⟨PointedCone.mem_dual.mpr fun g hg => ?_,
          Submodule.mem_sup_left (Submodule.mem_map_of_mem hvdir)⟩
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image,
          Set.mem_image, Finset.mem_coe] at hg
        rcases hg with rfl | ⟨h, hh, rfl⟩
        · simp [hom.weight_zero]
        · simpa [hextlin] using hvlin h hh
    · rintro w hw
      obtain ⟨hwdual, hwT⟩ := Submodule.mem_inf.mp hw
      rw [Submodule.restrictScalars_mem] at hwT
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hwT
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hdual := PointedCone.mem_dual.mp hwdual
      have hc0 : 0 ≤ c := by
        have := hdual (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
        simpa [hom.weight_zero, hom.weight_one] using this
      have hlin : ∀ h ∈ H, 0 ≤ h.linear u + c * h x₀ := by
        intro h hh
        have := hdual (Finset.mem_coe.mpr
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ext hh)))
        simpa [hext, hextlin] using this
      rcases hc0.eq_or_lt with rfl | hcpos
      · -- weight zero: a recession direction
        rw [zero_smul, add_zero]
        refine Submodule.mem_sup_right (PointedCone.mem_map.mpr ⟨u, ?_, rfl⟩)
        change ∀ y ∈ (S : Set A), ∀ a : 𝕜, 0 ≤ a → a • u +ᵥ y ∈ (S : Set A)
        intro y hy a ha
        obtain ⟨hyH, hyT⟩ := (hmem y).mp hy
        refine (hmem _).mpr ⟨fun h hh => ?_, ?_⟩
        · have hlu : 0 ≤ h.linear u := by simpa using hlin h hh
          simp only [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
          exact add_nonneg (mul_nonneg ha hlu) (hyH h hh)
        · exact AffineSubspace.vadd_mem_of_mem_direction (T.direction.smul_mem a hu) hyT
      · -- positive weight: a point of `S`, rescaled
        have hyS : (c⁻¹ • u +ᵥ x₀) ∈ (S : Set A) := by
          refine (hmem _).mpr ⟨fun h hh => ?_, ?_⟩
          · simp only [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
            have := mul_nonneg (inv_nonneg.mpr hc0) (hlin h hh)
            rwa [mul_add, ← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul] at this
          · exact AffineSubspace.vadd_mem_of_mem_direction
              (T.direction.smul_mem c⁻¹ hu) hx₀T
        refine Submodule.mem_sup_left ?_
        have heq : hom.ofVector u + c • hom.ofPoint x₀
            = c • hom.ofPoint (c⁻¹ • u +ᵥ x₀) := by
          rw [AffineMap.map_vadd]
          simp [vadd_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hcpos.ne']
        rw [heq]
        exact PointedCone.smul_mem _ hc0
          (Submodule.mem_span_of_mem (Set.mem_image_of_mem _ hyS))
  · -- the empty polyhedron: the cone is the weight-zero hyperplane
    have hSe : (S : Set A) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have h1 : homogenize W S = ⊥ := by
      have hSbot : S = (⊥ : ConvexSet 𝕜 A) := SetLike.ext' (by simpa using hSe)
      rw [hSbot]
      exact homogenize_bot
    have h2 : (S : Set A).recessionCone 𝕜 = ⊤ := by
      rw [eq_top_iff]
      rintro v -
      change ∀ y ∈ (S : Set A), ∀ a : 𝕜, 0 ≤ a → a • v +ᵥ y ∈ (S : Set A)
      simp [hSe]
    refine ⟨⊤, LinearMap.ker hom.weight, by simp, ?_⟩
    rw [homogenize_closure, h1, h2, bot_sup_eq]
    ext w
    simp only [PointedCone.mem_map, Submodule.mem_top, true_and, Submodule.mem_inf,
      Submodule.restrictScalars_mem, LinearMap.mem_ker]
    constructor
    · rintro ⟨v, rfl⟩
      exact hom.weight_zero v
    · intro hw
      have hrange : w ∈ LinearMap.range hom.ofVector := by
        rw [hom.ofVector_range_eq_weight_ker]
        exact hw
      exact LinearMap.mem_range.mp hrange


omit [AddCommGroup W] [Module 𝕜 W] [IsModuleConvexSpace 𝕜 W] in
/--
`H → V` direction of the Minkowski-Weyl theorem for polyhedra: every H-polyhedron is the
Minkowski sum of its recession cone and a polytope. The polytope is extracted from a finite
generating set of the homogenization-with-recession-cone by normalizing the positive-weight
generators to weight one.
-/
theorem IsHPolyhedron.exists_isPolytope_recessionCone_vadd {H : Set A}
    (hH : IsHPolyhedron 𝕜 H) :
    ∃ P : Set A, IsPolytope 𝕜 P ∧ H = (H.recessionCone 𝕜 : Set V) +ᵥ P := by
  classical
  let W := CanonicalHomogenization 𝕜 A
  let hom : Affine.IsHomogenization 𝕜 A W := inferInstance
  -- TODO: We shouldn't need to specify R, V by name
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)
  --
  set S : ConvexSet 𝕜 A := hH.toConvexSet with hSdef
  set CHom : PointedCone 𝕜 W :=
    homogenize W S ⊔ ((S : Set A).recessionCone 𝕜).map hom.ofVector with hCHom
  have hdeh : PointedCone.dehomogenize A CHom = H := by
    exact (@SetLike.coe_injective (ConvexSet 𝕜 A) A).eq_iff.mpr
      (dehomogenize_homogenize_closure S)
  obtain ⟨D, hDfg, S₀, hsplit⟩ :=
    (PointedCone.homogenize_sup_recessionCone_isHPolyhedral W (S := ↑S) hH).isPolyhedral
  obtain ⟨G, hG⟩ := hDfg
  rw [homogenize_closure, ← hCHom] at hsplit
  -- all weights in `CHom` are nonnegative
  have hCw : ∀ z ∈ CHom, 0 ≤ hom.weight z := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨v, -, rfl⟩ := PointedCone.mem_map.mp hb
    have haw : 0 ≤ hom.weight a := by
      rcases eq_or_ne a 0 with rfl | ha0
      · simp
      · obtain ⟨r, hr, _, ⟨y, -, rfl⟩, rfl⟩ :=
          Set.mem_smul.mp <| smul_pos_of_mem_homogenize ha ha0
        rw [map_smul, hom.weight_one, smul_eq_mul, mul_one]
        exact (Set.mem_Ioi.mp hr).le
    simpa [hom.weight_zero] using haw
  have hDle : D ≤ CHom := hsplit ▸ le_sup_left
  have hGw : ∀ g ∈ G, 0 ≤ hom.weight g := fun g hg =>
    hCw _ (hDle (hG ▸ Submodule.subset_span hg))
  have hS₀w : ∀ s ∈ S₀, hom.weight s = 0 := by
    intro s hs
    have h₁ := hCw _ (hsplit ▸ Submodule.mem_sup_right (Submodule.neg_mem _ hs) :
      -s ∈ CHom)
    have h₂ := hCw _ (hsplit ▸ Submodule.mem_sup_right hs : s ∈ CHom)
    simp only [_root_.map_neg, Left.nonneg_neg_iff] at h₁
    exact le_antisymm h₁ h₂
  -- split the generators by weight
  set Gpos := G.filter (fun g => 0 < hom.weight g) with hGpos
  set Gzero := G.filter (fun g => ¬ 0 < hom.weight g) with hGzero
  have hGsplit : G = Gpos ∪ Gzero := by
    rw [hGpos, hGzero, Finset.filter_union_filter_not_eq]
  have hGzerow : ∀ g ∈ Gzero, hom.weight g = 0 := by
    intro g hg
    rw [hGzero, Finset.mem_filter] at hg
    exact le_antisymm (not_lt.mp hg.2) (hGw g hg.1)
  -- normalize the positive-weight generators to weight one
  have hex : ∀ g ∈ Gpos, ∃ x : A, hom.ofPoint x = (hom.weight g)⁻¹ • g := by
    intro g hg
    rw [hGpos, Finset.mem_filter] at hg
    have h1 : (hom.weight g)⁻¹ • g ∈ Set.range hom.ofPoint := by
      rw [hom.ofPoint_range_eq_preimage_weight_one]
      simp [inv_mul_cancel₀ hg.2.ne']
    exact h1
  choose pt hpt using hex
  set T : Finset A := Gpos.attach.image (fun g => pt g.1 g.2) with hT
  -- the positive part generates the homogenization of the polytope
  have hhull : PointedCone.hull 𝕜 (hom.ofPoint '' ↑T) = PointedCone.hull 𝕜 ↑Gpos := by
    apply le_antisymm <;> rw [Submodule.span_le]
    · rintro _ ⟨x, hx, rfl⟩
      rw [hT] at hx
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_attach, Set.mem_univ,
        true_and] at hx
      obtain ⟨⟨g, hg⟩, -, rfl⟩ := hx
      rw [hpt g hg]
      have hg' := Finset.mem_filter.mp (hGpos ▸ hg)
      exact PointedCone.smul_mem _ (inv_nonneg.mpr hg'.2.le)
        (Submodule.subset_span (Finset.mem_coe.mpr hg))
    · intro g hg
      rw [Finset.mem_coe] at hg
      have hg' := Finset.mem_filter.mp (hGpos ▸ hg)
      have hgeq : g = hom.weight g • ((hom.weight g)⁻¹ • g) := by
        rw [smul_smul, mul_inv_cancel₀ hg'.2.ne', one_smul]
      rw [hgeq, ← hpt g hg]
      refine PointedCone.smul_mem _ hg'.2.le (Submodule.subset_span ?_)
      exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ (Finset.mem_attach Gpos ⟨g, hg⟩)))
    -- membership of `pt g hg` in `T`
  have hDsplit : D
      = homogenize W (ConvexSet.convexHull 𝕜 (↑T : Set A)) ⊔ PointedCone.hull 𝕜 ↑Gzero := by
    rw [← hull_image_ofPoint_eq_homogenize_convexHull, hhull, ← hG]
    conv_lhs => rw [hGsplit]
    rw [Finset.coe_union, Submodule.span_union]
  -- the zero-weight part
  have hKw : ∀ z ∈ (PointedCone.hull 𝕜 ↑Gzero ⊔ (S₀ : PointedCone 𝕜 W) : PointedCone 𝕜 W),
      hom.weight z = 0 := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    have hha : hom.weight a = 0 := by
      have hle : PointedCone.hull 𝕜 ↑Gzero
          ≤ ((LinearMap.ker hom.weight : Submodule 𝕜 W) : PointedCone 𝕜 W) :=
        Submodule.span_le.mpr fun g hg => by
          simpa using hGzerow g (Finset.mem_coe.mp hg)
      simpa using hle ha
    have hhb := hS₀w b (by simpa using hb)
    simp [hha, hhb]
  -- the polytope
  refine ⟨Convexity.convexHull 𝕜 ↑T, ⟨T, rfl⟩, ?_⟩
  have hPH : Convexity.convexHull 𝕜 ↑T ⊆ H := by
    intro y hy
    have h2 : hom.ofPoint y ∈ CHom := by
      rw [hsplit, hDsplit]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_span_of_mem (Set.mem_image_of_mem _ hy)))
    rw [← hdeh]
    simpa [PointedCone.dehomogenize, ConvexSet.dehomogenize] using h2
  have hHsub : H ⊆ (H.recessionCone 𝕜 : Set V) +ᵥ Convexity.convexHull 𝕜 ↑T := by
    intro x hx
    have hx' : hom.ofPoint x ∈ CHom := by
      rw [← hdeh] at hx
      simpa [PointedCone.dehomogenize, ConvexSet.dehomogenize] using hx
    rw [hsplit, hDsplit, sup_assoc] at hx'
    obtain ⟨q, hq, k, hk, hqk⟩ := Submodule.mem_sup.mp hx'
    have hkw : hom.weight k = 0 := hKw k hk
    have hqw : hom.weight q = 1 := by
      have := congrArg hom.weight hqk
      simpa [hkw, hom.weight_one] using this
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hqw
    obtain ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩ :=
      Set.mem_smul.mp <| smul_pos_of_mem_homogenize hq hq0
    have hr1 : r = 1 := by
      simpa [hom.weight_one] using hqw
    rw [hr1, one_smul] at hqk
    have hkofv : k = hom.ofVector (x -ᵥ y) := by
      have hvsub : hom.ofVector (x -ᵥ y) = hom.ofPoint x - hom.ofPoint y := by simp
      rw [hvsub, ← hqk]
      abel
    have hkC : k ∈ CHom := by
      rw [hsplit, hDsplit, sup_assoc]
      exact Submodule.mem_sup_right hk
    obtain ⟨v, hv, hveq⟩ :=
      PointedCone.mem_map.mp (mem_map_recessionCone_of_weight_eq_zero (hCHom ▸ hkC) hkw)
    have hxy : x -ᵥ y ∈ H.recessionCone 𝕜 := by
      have hveq' : v = x -ᵥ y := hom.ofVector_injective (by rw [hveq, hkofv])
      exact hveq' ▸ hv
    exact Set.mem_vadd.mpr ⟨x -ᵥ y, hxy, y, hy, vsub_vadd x y⟩
  refine Set.Subset.antisymm hHsub ?_
  rintro _ ⟨v, hv, y, hy, rfl⟩
  rw [← Convex.Set.recessionCone_vadd_self (R := 𝕜) (P := H)]
  exact Set.mem_vadd.mpr ⟨v, hv, y, hPH hy, rfl⟩


#click_suggestions
omit [AddCommGroup W] [Module 𝕜 W] [IsModuleConvexSpace 𝕜 W] in
/-- ALTERNATIVE ATTEMPT `H → V` direction -/
theorem IsHPolyhedron.exists_isPolytope_recessionCone_vadd_VERSION2 {H : Set A}
    (hH : IsHPolyhedron 𝕜 H) :
    ∃ P : Set A, IsPolytope 𝕜 P ∧
    ∃ C : PointedCone 𝕜 V, IsPolyhedral C ∧
    H = (C : Set V) +ᵥ P := by
  classical
  let W := CanonicalHomogenization 𝕜 A
  let hom : Affine.IsHomogenization 𝕜 A W := inferInstance
  -- TODO: We shouldn't need to specify R, V by name
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)

  -- 1. obtain the affine functions `F` and subspace `S` describing the H-polyhedron `H`
  obtain ⟨F, S, hH⟩ := hH
  -- 2. homogenize the functions to get linear functions `F_hom`:
  -- let F_hom := -- hom.extend 𝕜 '' F



  -- 3. homogenize the subspace to get `S_hom`:

  let S_hom : Submodule 𝕜 W := Submodule.span 𝕜 (hom.ofPoint '' S)

  -- 4. intersect `C_hom` with the "upper" half-space to get the H-cone `C'_hom`
  -- let C'_hom := PointedCone.inter (PointedCone.halfSpace 𝕜 W hom.weight 1)
  -- (PointedCone.hull 𝕜 ↑F_hom)

  let C'_hom : PointedCone 𝕜 W := sorry --?


  -- 5. intersect `S_hom` with the "horizontal" hyperplane to get the subspace `S'_hom`
  let S'_hom : Submodule 𝕜 W :=
    -- PointedCone.inter (PointedCone.halfSpace 𝕜 W hom.weight 0) (PointedCone.hull 𝕜 ↑F_hom)
    sorry
  -- ALTERNATIVE: "translate" the subspace `S` to the hyperplane `weight = 1` by adding a point of weight one

  -- 6. Fun fact: Dehomogenizing `C'_hom` gives back the original H-polyhedron `H`.
  -- AS A POINT SET; NOT AS AN OBJECT -- OF TYPE `IsHPolyhedron` (which would require a proof of convexity)
  have dehomogenize_gives_back_H : True := by
    -- PointedCone.dehomogenize W (C'_hom) = H := by
    sorry

  -- 7. Apply the Minkowski-Weyl theorem for polyhedral cones to `C'_hom`
  -- to get a finite set of generators `G` and a subspace `S_hom` such that
  -- `C'_hom = PointedCone.hull 𝕜 G
  let G_hom : Set W := sorry

  -- 8. Split the generators `G_hom` into the generators `G_hom_pos` with positive weight
  -- and the generators `G_hom_zero` with zero weight.
  let G_hom_pos :=  { g ∈ G_hom | hom.weight g > 0 }
  let G_hom_zero := { g ∈ G_hom | hom.weight g = 0 }
  have hG_split : G_hom = G_hom_pos ∪ G_hom_zero := by
    -- everything in C'_hom has either positive weight or zero weight
    sorry

  -- 9. Normalize the positive-weight generators to weight one to get a finite set of points `P`
  let G := { x : A | ∃ g ∈ G_hom_pos, hom.ofPoint x = (hom.weight g)⁻¹ • g }
  let P := ConvexSet.convexHull 𝕜 G
  have hP : IsPolytope 𝕜 (P : Set A) := by
    sorry



  sorry

/--
The recession cone of an H-polyhedron is a polyhedral cone.
-/
lemma IsHPolyhedron.recessionCone_isPolyhedral {H : Set A} (hH : IsHPolyhedron 𝕜 H) :
    IsPolyhedral (H.recessionCone 𝕜) := by
  let W := CanonicalHomogenization 𝕜 A
  let hom : Affine.IsHomogenization 𝕜 A W := inferInstance
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)
  --
  have hmap : ((H.recessionCone 𝕜).map hom.ofVector : PointedCone 𝕜 W)
      = (homogenize W hH.toConvexSet
          ⊔ ((hH.toConvexSet : Set A).recessionCone 𝕜).map hom.ofVector)
        ⊓ ↑(LinearMap.ker hom.weight) := by
    apply le_antisymm
    · refine le_inf le_sup_right ?_
      rintro _ ⟨v, -, rfl⟩
      simpa using hom.weight_zero v
    · rintro z hz
      obtain ⟨hz₁, hz₂⟩ := Submodule.mem_inf.mp hz
      exact mem_map_recessionCone_of_weight_eq_zero hz₁ (by simpa using hz₂)
  have hpoly : ((H.recessionCone 𝕜).map hom.ofVector).IsPolyhedral := by
    rw [hmap]
    exact (PointedCone.homogenize_sup_recessionCone_isHPolyhedral W hH).isPolyhedral.inf
      (.of_submodule _)
  have hcm : ((H.recessionCone 𝕜).map hom.ofVector).comap hom.ofVector
      = H.recessionCone 𝕜 := by
    ext v
    rw [PointedCone.mem_comap, PointedCone.mem_map]
    constructor
    · rintro ⟨w, hw, heq⟩
      exact hom.ofVector_injective heq ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  exact hcm ▸ hpoly.comap hom.ofVector

end Homogenize

-- TODO: It would be nice to not need the explicit coercion Cone → Set
-- TODO: Update the verbal theorem statement.
/--
`H → V` direction of the *Minkowski-Weyl* Theorem.
Every *H-polyhedron* H can be decomposed as the Minkowski sum of
a *V-polytope* P, a *finitely generated cone*, and a *submodule*.
The finitely generated cone and the submodule together form the
recession cone in this theorem.

As in the definition of *H-polyhedron*, this *submodule* need not have finite dimension
or finite codimension (which is only relevant in infinite dimension).
-/
lemma isVPolyhedron_of_isHPolyhedron {H : Set A} (hH : IsHPolyhedron 𝕜 H) :
    ∃P : Set A, (IsPolytope 𝕜 P) ∧ H = (H.recessionCone 𝕜 : Set V) +ᵥ P := by
    exact IsHPolyhedron.exists_isPolytope_recessionCone_vadd hH
  -- let W := CanonicalHomogenization 𝕜 A
  -- let hom : Affine.IsHomogenization 𝕜 A W := inferInstance
  -- let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)
  -- --
  -- have hpoly : ((homogenize W hH.toConvexSet)
  --     ⊔ (H.recessionCone 𝕜).map hom.ofVector).IsPolyhedral :=
  --   (IsPolyhedral.of_fg (IsPolytope.homogenize_fg W hH)).sup
  --     ((H.recessionCone 𝕜).isPolyhedral.map hom.ofVector)
  -- simpa [dehomogenize_map_ofVector_sup_homogenize] using
  --   ConvexSet.dehomogenize_isHPolyhedron (A := A) _ (isHPolyhedral_of_isVPolyhedral hpoly)

/-
`V → H` direction of the *Minkowski-Weyl* theorem.
For every finite *V-polytope* + *rays* + *submodule*,
there exists a finite set of inequalities that describe it.
-/
lemma isHPolyhedron_of_isPolytope {P : Set A} (hP : IsPolytope 𝕜 P) :
    IsHPolyhedron 𝕜 P := by
  let W := CanonicalHomogenization 𝕜 A
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)
  --
  simpa [PointedCone.dehomogenize] using
    ConvexSet.dehomogenize_isHPolyhedron (A := A) _
      (IsHPolyhedral.fg _ (
        IsPolytope.homogenize_fg (R := 𝕜) W (C := ⟨P, hP.isConvexSet⟩) hP))

/--
`V → H` direction of the Minkowski-Weyl theorem for polyhedra: the Minkowski sum of an
H-polyhedral cone and a polytope is an H-polyhedron.
-/
lemma isHPolyhedron_of_isVPolyhedron {P : Set A} (hP : IsPolytope 𝕜 P)
    {C : PointedCone 𝕜 V} (hC : IsHPolyhedral .id C) :
    IsHPolyhedron 𝕜 ((C : Set V) +ᵥ P) := by
  let W := CanonicalHomogenization 𝕜 A
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)
  --
  exact IsHPolyhedron.isPolyhedral_vadd_isPolytope (W := W) hC hP

open Convex in
/--
The Minkowski sum of two H-polyhedra is an H-polyhedron: decompose both by Minkowski-Weyl,
sum the polytopes and the recession cones separately, and reassemble.
-/
lemma IsHPolyhedron.vadd
    {P : Set V} (hP : IsHPolyhedron 𝕜 P) {Q : Set A} (hQ : IsHPolyhedron 𝕜 Q) :
    IsHPolyhedron 𝕜 (P +ᵥ Q) := by
  obtain ⟨P₁, hP₁, hPeq⟩ := isVPolyhedron_of_isHPolyhedron hP
  obtain ⟨Q₁, hQ₁, hQeq⟩ := isVPolyhedron_of_isHPolyhedron hQ
  rw [show P +ᵥ Q =
      ((P.recessionCone 𝕜 ⊔ Q.recessionCone 𝕜 : PointedCone 𝕜 V) : Set V) +ᵥ (P₁ +ᵥ Q₁) by calc
    _ = ((P.recessionCone 𝕜 : Set V) +ᵥ P₁) +ᵥ (Q.recessionCone 𝕜 : Set V) +ᵥ Q₁ := by
      conv_lhs => rw [hPeq, hQeq]
    _ = (((P.recessionCone 𝕜 : Set V)) +ᵥ (Q.recessionCone 𝕜 : Set V)) +ᵥ P₁ +ᵥ Q₁ := by
      rw [vadd_assoc, vadd_comm P₁, vadd_assoc]
    -- TODO: Why does this require a double coercion?
    _ = (((P.recessionCone 𝕜 ⊔ Q.recessionCone 𝕜) : PointedCone 𝕜 V) : Set V) +ᵥ P₁ +ᵥ Q₁ := by
      rw [vadd_eq_add, ←Submodule.coe_sup]]
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := V)
  exact isHPolyhedron_of_isVPolyhedron (hP₁.vadd hQ₁) (isHPolyhedral_of_isVPolyhedral
    (hP.recessionCone_isPolyhedral.sup hQ.recessionCone_isPolyhedral))


end Field
end Homogenization
