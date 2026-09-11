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
lemma ConvexSetimagedehomogenize_isHPolyhedron (C : PointedCone 𝕜 W)
    (hC : IsHPolyhedral .id C) :
    IsHPolyhedron 𝕜 (PointedCone.dehomogenize A C : Set A) := by
  classical
  obtain ⟨D, S, ⟨G, rfl⟩, rfl⟩ := hC
  refine ⟨G.image fun f => f.toAffineMap.comp hom.ofPoint,
    S.toAffineSubspace.comap hom.ofPoint, ?_⟩
  ext x
  simp only [PointedCone.dehomogenize, ConvexSet.dehomogenize, Submodule.coe_inf,
    coe_restrictScalars, preimage_inter, mk_eq, mem_inter_iff, mem_preimage, SetLike.mem_coe,
    PointedCone.mem_dual, LinearMap.id_coe, id_eq, Finset.mem_image, iInter_exists, biInter_and',
    iInter_iInter_eq_right, AffineMap.coe_comp, LinearMap.coe_toAffineMap, AffineSubspace.coe_comap,
    mem_iInter, Function.comp_apply, mem_Ici, mem_toAffineSubspace]


open Convex

variable (W) in
/-- The closure of the homogenization of a convex set includes its recession cone. -/
def Convexity.ConvexSet.homogenize_closure (S : ConvexSet 𝕜 A) : PointedCone 𝕜 W :=
    homogenize W S ⊔ ((S : Set A).recessionCone 𝕜).map hom.ofVector

lemma dehomogenize_sup_vector_left (C : PointedCone 𝕜 V) (P : PointedCone 𝕜 W) :
    PointedCone.dehomogenize A (C.map hom.ofVector ⊔ P)
    = (C : Set V) +ᵥ (PointedCone.dehomogenize A P : Set A) := by
  ext x
  simp only [PointedCone.dehomogenize, ConvexSet.dehomogenize, sup_comm, mk_eq, mem_preimage,
    SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc, rfl⟩ := PointedCone.mem_map.mp hz
    have hw : hom.weight y = 1 := by
      have := congrArg hom.weight hyz
      simpa only [map_add, hom.weight_zero, add_zero, hom.weight_one] using this
    obtain ⟨y', hy'⟩ := (hom.weight_one_iff _).mp hw
    refine ⟨c, hc, y', by simp_all only [PointedCone.mem_map, mem_preimage, SetLike.mem_coe], ?_⟩
    rw [hy', add_comm, ← vadd_eq_add, ← AffineMap.map_vadd] at hyz
    exact hom.ofPoint_injective hyz
  · rintro ⟨c, hc, y, hy, rfl⟩
    rw [AffineMap.map_vadd, vadd_eq_add, add_comm]
    exact Submodule.add_mem_sup hy (PointedCone.mem_map.mpr ⟨c, hc, rfl⟩)

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
      simpa only [map_add, hom.weight_zero, zero_add, hom.weight_one] using this
    have := Set.mem_smul.mp <| smul_pos_of_mem_homogenize hz (by rintro rfl; simp only [map_zero,
      zero_ne_one] at hw)
    obtain ⟨r, hr, _, ⟨y', hy', rfl⟩, rfl⟩ :=
      Set.mem_smul.mp <| smul_pos_of_mem_homogenize hz (by rintro rfl; simp only [map_zero,
        zero_ne_one] at hw)
    have hr1 : r = 1 := by simpa only [map_smul, hom.weight_one, smul_eq_mul, mul_one] using hw
    refine Set.mem_vadd.mpr ⟨c, hc, y', hy', hom.ofPoint_injective ?_⟩
    rw [AffineMap.map_vadd]
    simpa only [vadd_eq_add, hr1, one_smul] using hyz
  · rintro ⟨c, hc, y, hy, rfl⟩
    rw [AffineMap.map_vadd, vadd_eq_add]
    exact Submodule.add_mem_sup (PointedCone.mem_map.mpr ⟨c, hc, rfl⟩)
      (mem_span_of_mem (Set.mem_image_of_mem _ hy))

/--
The dehomogenization of the homogenization closure recovers the original set.
-/
-- TODO: We need `ext` because `dehomogenize_map_ofVector_sup_homogenize` is
--       stated for `Set` instead of `ConvexSet`
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
    simpa only [map_add, hom.weight_zero, add_zero] using hw
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
theorem isHPolyhedral_of_isVPolyhedral [Fact (Function.Surjective p)] {C : PointedCone 𝕜 V}
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
  -- simpa [dehomogenize_map_ofVector_sup_homogenize] using
  --   ConvexSet.dehomogenize_isHPolyhedron (A := A) _ (isHPolyhedral_of_isVPolyhedral hpoly)
  sorry

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
  have h0 : (0 : 𝕜) ≤ h x := by simpa only [zero_smul, zero_vadd] using hray 0 le_rfl
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
  classical -- added
  obtain ⟨F, hF, -⟩ := hom.extend 𝕜 h
  have hFx : ∀ x : A, F (hom.ofPoint x) = h x := fun x => congrFun hF x
  refine ⟨F, hFx, fun v => ?_⟩
  have x₀ := Classical.arbitrary A
  have hv : hom.ofVector v = hom.ofPoint (v +ᵥ x₀) - hom.ofPoint x₀ := by
    simp only [AffineMap.map_vadd, vadd_eq_add, add_sub_cancel_right]
  rw [hv, map_sub, hFx, hFx]
  simp only [AffineMap.map_vadd, vadd_eq_add, add_sub_cancel_right]

/- Every affine functional extends to a unique linear functional on the homogenization space which
agrees with it on points and with its linear part on vectors.
-/
-- def Affine.IsHomogenization.linear_extension (h : A →ᵃ[𝕜] 𝕜) : W →ₗ[𝕜] 𝕜 :=

variable [DecidableEq (W →ₗ[𝕜] 𝕜)]

variable (W) in
noncomputable def AffineMap.linear_extension : (A →ᵃ[𝕜] 𝕜) ↪ W →ₗ[𝕜] 𝕜 where
  toFun := (hom.exists_linear_extension · |>.choose)
  inj' := sorry

-- We might need to pass the affine subspace to homogenize_dual
variable (W) in
noncomputable
def homogenize_dual (H : Finset (A →ᵃ[𝕜] 𝕜)) : PointedCone 𝕜 W :=
    PointedCone.dual .id (
      insert hom.weight (H.image (AffineMap.linear_extension W)) : Finset (W →ₗ[𝕜] 𝕜))

omit [IsModuleConvexSpace 𝕜 W] in
variable (W) in
lemma homogenize_dual_dualFG (H : Finset (A →ᵃ[𝕜] 𝕜)) : (homogenize_dual W H).DualFG .id := by
  rw [homogenize_dual]
  exact DualFG.dual_of_finset .id (insert hom.weight (H.image (AffineMap.linear_extension W)))

lemma homogenize_dual_weight_zero_eq_recessionCone (H : Finset (A →ᵃ[𝕜] 𝕜)) :
    (homogenize_dual W H) ⊓ hom.weight.ker =
      (⋂ h ∈ H, (h.linear_extension W) ⁻¹' Set.Ici 0).recessionCone 𝕜 := by
  sorry

variable (W) in
lemma IsHPolyhedron.exists_homogenize_dual {P : Set A} (hP : IsHPolyhedron 𝕜 P) :
    ∃ H : Finset (A →ᵃ[𝕜] 𝕜), ∃ S : AffineSubspace 𝕜 A,
      (P = (⋂ h ∈ H, h ⁻¹' Set.Ici 0) ⊓ S) ∧
      ConvexSet.dehomogenize A (
        homogenize_dual W H ⊓ (S.direction.map hom.ofVector : Submodule 𝕜 W)) = P := by
  obtain ⟨ineqs, S, rfl⟩ := hP
  use ineqs, S
  constructor
  · rfl
  sorry

-- IDEA: We could have general notation for an `∃ statement with witness`, which would
--       have computable access to the witness in definitions.
--       The Exists could have a head/tail coercion into ExistsWithWitness
--       relying on choice for use in proofs, and (witness → predicate) could have a
--       coercion into ExistsWithWitness to avoid `constructor` in proofs of ExistsWithWitness.
--       Then we could use `IsHPolyhedron 𝕜 P with H` as an argument when we demand the
--       that the actual inequalities are made explicit.
-- lemma homogenize_dual_splits {P : Set A} {H : Finset (W →ₗ[𝕜] 𝕜)} (hP : IsHPolyhedron 𝕜 P with H) :
--     (homogenize_dual A H).recessionCone

-- lemma split_zero_pos (D : PointedCone 𝕜 W) (hD : D.FG) (S : Submodule 𝕜 W) :

/--
Minkowski-Weyl theorem for polyhedra, `H → V` direction.
Proved as a chain of equalities.
-/
theorem IsHPolyhedron.exists_isPolytope_recessionCone_vadd' {H : ConvexSet 𝕜 A}
    (hH : IsHPolyhedron 𝕜 (H : Set A)) :
    ∃ P : Set A, IsPolytope 𝕜 P ∧ H = ((H : Set A).recessionCone 𝕜 : Set V) +ᵥ P := by classical
  -- Build canonical homogenization:
  let W := CanonicalHomogenization 𝕜 A
  let hom : Affine.IsHomogenization 𝕜 A W := inferInstance
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)

  -- Build polytope:
  obtain ⟨ineqs, S, h_dual_eq⟩ := IsHPolyhedron.exists_homogenize_dual W hH
  let H_hom := homogenize_dual W ineqs ⊓ (S.direction.map hom.ofVector : Submodule 𝕜 W)
  have hC_H : H_hom.IsHPolyhedral .id := by
    use homogenize_dual W ineqs, (S.direction.map hom.ofVector : Submodule 𝕜 W)
    exact ⟨homogenize_dual_dualFG W ineqs, rfl⟩
  obtain ⟨D, hD, S, h_union⟩ := hC_H.isPolyhedral
  obtain ⟨D₀, h0, Dₚ, hp, h_split⟩ := sorry D S hom.weight
  let P := dehomogenize A Dₚ
  have hP : IsPolytope 𝕜 P := by
    exact dehomogenize_fg
    sorry

  -- Proof:
  use P
  calc
    H = dehomogenize A (homogenize_dual W H ⊓ S_hom) := by -- homogenize and dehomogenize
      exact h_dual_eq.symm
      -- exact dehomogenize_homogenize_closure.symm
    _ = dehomogenize A (H_hom) := by rfl
    _ = dehomogenize A (D ⊔ S) := by rw [h_union]
    _ = dehomogenize A (D₀ ⊔ Dₚ) := by exact h_split -- split 0 and positive rays
    _ = (D₀ : Set V) +ᵥ P := by -- extract weight 0 as cone
      exact pointedCone_vadd_of_dehomogenize_pointedCone_add
    _ = (H.recessionCone 𝕜 : Set V) +ᵥ P := by -- weight 0 is precisely the recession cone
      exact homogenize_closure_weight_zero_eq_recessionCone


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
      simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_Ici, SetLike.mem_coe]
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
          · simp only [LinearMap.id_coe, id_eq, hom.weight_one, zero_le_one]
          · simpa only [LinearMap.id_coe, id_eq, hext] using hxH h hh
        · have : hom.ofPoint x = hom.ofVector (x -ᵥ x₀) + hom.ofPoint x₀ := by
            simp only [AffineMap.linearMap_vsub, vsub_eq_sub, sub_add_cancel]
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
          simpa only [vadd_vsub] using AffineSubspace.vsub_mem_direction h1 hx₀T
        refine Submodule.mem_inf.mpr ⟨PointedCone.mem_dual.mpr fun g hg => ?_,
          Submodule.mem_sup_left (Submodule.mem_map_of_mem hvdir)⟩
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image,
          Set.mem_image, Finset.mem_coe] at hg
        rcases hg with rfl | ⟨h, hh, rfl⟩
        · simp only [LinearMap.id_coe, id_eq, LinearMap.coe_restrictScalars, hom.weight_zero,
          Std.le_refl]
        · simpa only [LinearMap.id_coe, id_eq, LinearMap.coe_restrictScalars, hextlin] using
          hvlin h hh
    · rintro w hw
      obtain ⟨hwdual, hwT⟩ := Submodule.mem_inf.mp hw
      rw [Submodule.restrictScalars_mem] at hwT
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hwT
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hdual := PointedCone.mem_dual.mp hwdual
      have hc0 : 0 ≤ c := by
        have := hdual (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
        simpa only [hom.weight_zero, hom.weight_one, ge_iff_le, LinearMap.id_coe, id_eq, map_add,
          map_smul, smul_eq_mul, mul_one, zero_add] using this
      have hlin : ∀ h ∈ H, 0 ≤ h.linear u + c * h x₀ := by
        intro h hh
        have := hdual (Finset.mem_coe.mpr
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ext hh)))
        simpa only [hext, hextlin, ge_iff_le, LinearMap.id_coe, id_eq, map_add, map_smul,
          smul_eq_mul] using this
      rcases hc0.eq_or_lt with rfl | hcpos
      · -- weight zero: a recession direction
        rw [zero_smul, add_zero]
        refine Submodule.mem_sup_right (PointedCone.mem_map.mpr ⟨u, ?_, rfl⟩)
        change ∀ y ∈ (S : Set A), ∀ a : 𝕜, 0 ≤ a → a • u +ᵥ y ∈ (S : Set A)
        intro y hy a ha
        obtain ⟨hyH, hyT⟩ := (hmem y).mp hy
        refine (hmem _).mpr ⟨fun h hh => ?_, ?_⟩
        · have hlu : 0 ≤ h.linear u := by simpa only [zero_mul, add_zero] using hlin h hh
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
          simp only [map_smul, vadd_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hcpos.ne',
            one_smul]
        rw [heq]
        exact PointedCone.smul_mem _ hc0
          (Submodule.mem_span_of_mem (Set.mem_image_of_mem _ hyS))
  · -- the empty polyhedron: the cone is the weight-zero hyperplane
    have hSe : (S : Set A) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have h1 : homogenize W S = ⊥ := by
      have hSbot : S = (⊥ : ConvexSet 𝕜 A) := SetLike.ext' (by simpa only [SetLike.coe_bot,
        bot_eq_empty] using hSe)
      rw [hSbot]
      exact homogenize_bot
    have h2 : (S : Set A).recessionCone 𝕜 = ⊤ := by
      rw [eq_top_iff]
      rintro v -
      change ∀ y ∈ (S : Set A), ∀ a : 𝕜, 0 ≤ a → a • v +ᵥ y ∈ (S : Set A)
      simp only [hSe, mem_empty_iff_false, imp_false, not_le, IsEmpty.forall_iff, implies_true]
    refine ⟨⊤, LinearMap.ker hom.weight, by simp only [DualFG.top], ?_⟩
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
      · simp only [map_zero, Std.le_refl]
      · obtain ⟨r, hr, _, ⟨y, -, rfl⟩, rfl⟩ :=
          Set.mem_smul.mp <| smul_pos_of_mem_homogenize ha ha0
        rw [map_smul, hom.weight_one, smul_eq_mul, mul_one]
        exact (Set.mem_Ioi.mp hr).le
    simpa only [hom.weight_zero, map_add, add_zero, ge_iff_le] using haw
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
      simp only [inv_mul_cancel₀ hg.2.ne', mem_preimage, map_smul, smul_eq_mul, mem_singleton_iff]
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
          simpa only [coe_restrictScalars, SetLike.mem_coe, LinearMap.mem_ker] using
            hGzerow g (Finset.mem_coe.mp hg)
      simpa only [restrictScalars_mem, LinearMap.mem_ker] using hle ha
    have hhb := hS₀w b (by simpa using hb)
    simp only [hha, hhb, map_add, add_zero]
  -- the polytope
  refine ⟨Convexity.convexHull 𝕜 ↑T, ⟨T, rfl⟩, ?_⟩
  have hPH : Convexity.convexHull 𝕜 ↑T ⊆ H := by
    intro y hy
    have h2 : hom.ofPoint y ∈ CHom := by
      rw [hsplit, hDsplit]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_span_of_mem (Set.mem_image_of_mem _ hy)))
    rw [← hdeh]
    simpa only [PointedCone.dehomogenize, ConvexSet.dehomogenize, mk_eq, mem_preimage,
      SetLike.mem_coe] using h2
  have hHsub : H ⊆ (H.recessionCone 𝕜 : Set V) +ᵥ Convexity.convexHull 𝕜 ↑T := by
    intro x hx
    have hx' : hom.ofPoint x ∈ CHom := by
      rw [← hdeh] at hx
      simpa only [PointedCone.dehomogenize, ConvexSet.dehomogenize, mk_eq, mem_preimage,
        SetLike.mem_coe] using hx
    rw [hsplit, hDsplit, sup_assoc] at hx'
    obtain ⟨q, hq, k, hk, hqk⟩ := Submodule.mem_sup.mp hx'
    have hkw : hom.weight k = 0 := hKw k hk
    have hqw : hom.weight q = 1 := by
      have := congrArg hom.weight hqk
      simpa only [map_add, hom.weight_one, hkw, add_zero] using this
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp only [map_zero, zero_ne_one] at hqw
    obtain ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩ :=
      Set.mem_smul.mp <| smul_pos_of_mem_homogenize hq hq0
    have hr1 : r = 1 := by
      simpa only [hom.weight_one, map_smul, smul_eq_mul, mul_one] using hqw
    rw [hr1, one_smul] at hqk
    have hkofv : k = hom.ofVector (x -ᵥ y) := by
      have hvsub : hom.ofVector (x -ᵥ y) = hom.ofPoint x - hom.ofPoint y := by
        simp only [AffineMap.linearMap_vsub, vsub_eq_sub]
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
  rw [← Convex.Set.recessionCone_vadd_self (𝕜 := 𝕜) (P := H)]
  exact Set.mem_vadd.mpr ⟨v, hv, y, hPH hy, rfl⟩

-- alternative formulation (with =) of the following lemma.
-- variable (V) in
-- variable [IsModuleConvexSpace 𝕜 V] in
-- lemma hull_invariant_under_scaling (G : Finset V) (multiplier : V → 𝕜) :
--   (∀ g ∈ G, multiplier g > 0) ∧  multiplier.support = G →
--   PointedCone.hull 𝕜 G = PointedCone.hull 𝕜 ((G : Set V).image (fun g => multiplier g • g)) := by
--     sorry

/-- Scaling the generators of a cone by positive multipliers does not change the cone.
    This lemma proves half of this statement. -/
lemma hull_invariant_under_scaling_subset (G1 G2 : Set V)
  (h_scaling : ∀ g1 ∈ G1, ∃ g2 ∈ G2, ∃ multiplier : 𝕜, multiplier > 0 ∧ g1 = multiplier • g2) :
  PointedCone.hull 𝕜 G1 ≤ PointedCone.hull 𝕜 G2 := by
    rw [Submodule.span_le, subset_def]
    intro g1 hg1
    apply h_scaling at hg1
    obtain ⟨g2, ⟨hg2, ⟨multiplier, ⟨hmultiplier_pos, h_g1_versus_g2⟩⟩⟩⟩ := hg1
    rw [h_g1_versus_g2]
    have : g2 ∈ hull 𝕜 G2 := mem_span_of_mem hg2
    exact PointedCone.smul_mem (hull 𝕜 G2) hmultiplier_pos.le this

-- Something like this ought to be a theorem
-- in Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Basic
theorem ConvexCone_map {G : Set V} (f : V →ₗ[𝕜] W) :
    PointedCone.hull 𝕜 (f '' G) = PointedCone.map f (PointedCone.hull 𝕜 G) := by
  symm
  simpa using (PointedCone.map_hull (R := 𝕜) (f := f) (s := G))

#click_suggestions
-- omit [AddCommGroup W] [Module 𝕜 W] [IsModuleConvexSpace 𝕜 W] in
-- G.R. don't understand: W does not appear in the theorem statement!
-- TODO: Find a better name?
/-- ALTERNATIVE ATTEMPT `H → V` direction
verbose and in little steps -/
theorem IsHPolyhedron.exists_Polytope_plus_Cone_VERSION2 {H : Set A}
    (hH : IsHPolyhedron 𝕜 H) :
    ∃ P : Set A, IsPolytope 𝕜 P ∧
    ∃ C : PointedCone 𝕜 V, IsPolyhedral C ∧
    H = (C : Set V) +ᵥ P := by
  classical
  let V_hom := CanonicalHomogenization 𝕜 A
  let hom : Affine.IsHomogenization 𝕜 A V_hom := inferInstance
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := V_hom) -- affine space

  -- 1. obtain the affine functions `F` and subspace `S` describing the H-polyhedron `H`
  obtain ⟨F, S, hH⟩ := hH
  -- hH : H = { x : A | ∀ f ∈ F, f x ≥ 0 } ⊓ S

  -- 2. homogenize the functions to get linear functions `F_hom`:
  choose extend_function hext hextlin using hom.exists_linear_extension
  let F_hom := Finset.image extend_function F
  -- 3. add the linear constraint for the "upper" half-space to get `F0_hom`
  set F0_hom := insert hom.weight F_hom with hF0_hom
  -- 4. Form the H-cone `C0_hom` in `V_hom` defined by the constraints `F0_hom`
  let C0_hom : PointedCone 𝕜 V_hom := dual .id F0_hom
  --- C0_hom.carrier = { x : V_hom | ∀ f_hom ∈ F0_hom, f_hom x ≥ 0 },  -- pedestrian definition
  have hC0_nonneg : ∀ z ∈ C0_hom, 0 ≤ hom.weight z := by
    intro z hz
    exact (PointedCone.mem_dual.mp hz) (x := hom.weight)
      (by simp only [hF0_hom, Finset.coe_insert, mem_insert_iff, SetLike.mem_coe, true_or])
  have hC0_hom.dualFG : C0_hom.DualFG .id := by
    use F0_hom

  -- 5. homogenize the subspace `S` to get `S_hom`:
  let S_hom : Submodule 𝕜 V_hom := Submodule.span 𝕜 (hom.ofPoint '' S)

  -- 6. Form the H-cone `H_hom` by intersecting `C0_hom` with the subspace `S_hom`.
  set H_hom : PointedCone 𝕜 V_hom := C0_hom ⊓ S_hom with hC_hom

  -- 7. Fun fact: Dehomogenizing `H_hom` gives back the original H-polyhedron `H`.
  have dehomogenize_gives_back_H :
    PointedCone.dehomogenize A (H_hom) = H := by
    sorry

  -- 7. Apply the Minkowski-Weyl theorem for polyhedral cones to `H_hom`
  -- to get a finite set of generators `G_hom` and a linear subspace `T` such that
  -- `H_hom = PointedCone.hull 𝕜 G_hom ⊔ T`
  have : IsHPolyhedral .id H_hom := by use C0_hom, S_hom
  obtain ⟨D_hom, ⟨G_hom, hG_hom⟩, T, h_representation⟩ :=
                     PointedCone.IsHPolyhedral.isPolyhedral this
  -- h_representation : H_hom = D_hom ⊔ ↑T
  -- `D_hom` is the cone generated by `G_hom`

  -- intermediate result: all vectors in G_hom have nonnegative weights.
  have hG_hom_nonneg : ∀ g ∈ G_hom, hom.weight g >= 0 := by
    intro g hG
    apply hC0_nonneg -- it remains to show `g ∈ C0_hom`
    have : g ∈ D_hom := by simp only [←hG_hom, hG, SetLike.mem_coe, mem_span_of_mem]
    have : g ∈ D_hom ⊔ T := mem_sup_left this
    rw [←h_representation] at this
    exact (Submodule.mem_inf.mp this).1

  -- 8. Split the generators `G_hom` into the generators `G_hom_pos` with positive weight
  -- and the generators `G_hom_zero` with zero weight.
  set G_hom_pos :=  { g ∈ G_hom | g.weight > 0 } with hG_hom_pos
  set G_hom_zero := { g ∈ G_hom | g.weight = 0 } with hG_hom_zero
  have hG_hom_split : G_hom = G_hom_pos ∪ G_hom_zero := by
    -- everything in C'_hom has either positive weight or zero weight
    rw [Finset.Subset.antisymm_iff]
    constructor
    · intro g hg -- show `⊆`
      rw [Finset.mem_union]
      by_cases sign : 0 < g.weight
      · apply Or.inl
        -- show that g ∈ G_hom_pos:
        rw [hG_hom_pos, Finset.mem_filter]
        constructor
        · exact hg
        · exact sign
      · have zero : g.weight = 0 := le_antisymm (not_lt.mp sign) (hG_hom_nonneg g hg)
        apply Or.inr
        -- show that g ∈ G_hom_zero:
        rw [hG_hom_zero, Finset.mem_filter]
        constructor
        · exact hg
        · exact zero
    · apply Finset.union_subset -- converse direction `⊇` is easy
      · apply Finset.filter_subset
      · apply Finset.filter_subset

  -- 9. Normalize the positive-weight generators to weight 1 to get a finite set of points `Points`
  set G_hom_pos_normalized := G_hom_pos.image (fun g => g.weight⁻¹ • g) with h_G_hom_pos_normalized
  set Points := G_hom_pos_normalized.preimage (hom.ofPoint) (hom.ofPoint_injective.injOn)
         with hPoints
  -- have G_hom_pos_normalized = (hom.ofPoint '' ↑Points) with

  set P_convSet : ConvexSet 𝕜 A := ConvexSet.convexHull 𝕜 Points with hP_conv
  set P := (P_convSet : Set A) with hP -- == Convexity.convexHull 𝕜 Points
  -- two version of P, of different types. Do we need both?
  -- For example, `homogenize` needs `P_convSet`.
  have P_is_polytope : IsPolytope 𝕜 P := by
    use Points
    rw [hP, hP_conv, mk_eq, ConvexSet.carrier_eq_coe]
    rfl

  -- try to prove this directly?:
  have X1_to_Y : ∀ g1 ∈ G_hom_pos, ∃ g2 ∈ G_hom_pos_normalized,
       ∃ multiplier : 𝕜, multiplier > 0 ∧ g1 = multiplier • g2 := by sorry
  have Y1_to_X : ∀ g1 ∈ G_hom_pos_normalized, ∃ g2 ∈ G_hom_pos,
       ∃ multiplier : 𝕜, multiplier > 0 ∧ g1 = multiplier • g2 := by sorry

  -- 10. Generate the cone `C` from the zero-weight generators and the subspace S
  set Rays := hom.ofVector ⁻¹' G_hom_zero with hRays
  set Linear_subspace : Submodule 𝕜 V := T.map hom.ofVector.leftInverse with hLinear
  -- The lineality space of the cone is a superspace of this. (The cone generated by Rays
  -- might have an additional lineality space of its own, which has to be added.)
  set C := PointedCone.hull 𝕜 Rays ⊔ Linear_subspace with hC

  -- 11. We have now constructed the polyhedral cone `C` and the polytope `P`.
  -- It remains to show that `H = C +ᵥ P`

  -- Intermediate result: All elements of `T` have weight zero
  have T_weight_eq_zero : ∀ t ∈ T, hom.weight t = 0 := by
    intro t ht
    have ht' : ∀ t ∈ T, t ∈ C0_hom ⊓ S_hom := by
          intro t ht
          rw [←hC_hom, h_representation]
          exact Submodule.mem_sup_right ht
    -- NOTE: The following could be proved directly above
    have ht'' : ∀ t ∈ T, t ∈ C0_hom := by
          intro t ht
          exact (mem_inf.mp (ht' t ht)).1
    have ht_nonneg : 0 ≤ hom.weight t := hC0_nonneg t (ht'' t ht)
    have ht_neg_nonneg : 0 ≤ hom.weight (-t) :=
          hC0_nonneg (-t) (ht'' (-t) (by simp only [Submodule.neg_mem _ ht]))
    have ht_neg : hom.weight (-t) = - hom.weight t := by
          simp only [LinearMap.map_neg]
    rw [ht_neg] at ht_neg_nonneg
    linarith

  -- The desired representation is `H = C +ᵥ P`:
  use P_convSet -- or use P ?
  constructor
  · exact P_is_polytope
  use C
  constructor
  · use hull 𝕜 Rays
    constructor
    · apply fg_span -- show that hull 𝕜 Rays is finitely generated
      rw [hRays]
      apply Finite.preimage
      · exact hom.ofVector_injective.injOn
      · exact Finset.finite_toSet G_hom_zero
    · use Linear_subspace
  · -- The goal is now to show that `H = C +ᵥ P`:
    rw [Subset.antisymm_iff]
    constructor
    -- show H ⊆ C +ᵥ P
    · intro x hx
      set x_hom : V_hom := hom.ofPoint x with hx_hom_def
      have x_hom_weight_eq_one: x_hom.weight = 1 := by
        have : x_hom ∈ hom.weight ⁻¹' {1} := by
          rw [← hom.ofPoint_range_eq_preimage_weight_one]
          use x
        rw [mem_preimage, mem_singleton_iff] at this
        exact this

      have hx' : x_hom ∈ C0_hom := by
        sorry
          --- exact Submodule.mem_span_of_mem (Set.mem_image_of_mem _ (hH.2 hx))
      have hx22 : x_hom ∈ S_hom := by
        sorry
      have hx_hom : x_hom ∈ H_hom := by
        rw [Submodule.mem_inf]
        exact ⟨hx', hx22⟩
      have hC_hom_rep : x_hom ∈ D_hom ⊔ T := by
        rw [← h_representation]
        exact hx_hom
      -- show that x ∈ C +ᵥ P
      -- since x_hom ∈ H_hom, `x_hom = (∑ μ_j r_j + t) +ᵥ (∑ λ_i g_i)`
      -- for some r_j ∈ Rays, t ∈ Linear_subspace, g_i ∈ G_hom_pos, μ_j ≥ 0, λ_i ≥ 0.
      obtain ⟨d_hom, hd_hom, t_hom, ht_hom, d_hom_plus_t_hom_eq_x_hom⟩ := mem_sup.mp hC_hom_rep
      -- rw [← hG_hom] at hd_hom
      have split_d : D_hom = hull 𝕜 G_hom_pos ⊔ hull 𝕜 G_hom_zero := by
        sorry
      rw [split_d] at hd_hom
      obtain ⟨p_hom, hp_hom, z_hom, hz_hom, p_hom_plus_z_hom_eq_d_hom⟩ := mem_sup.mp hd_hom
      -- Now we have the decomposition `x_hom = p_hom + z_hom + t_hom`
      -- This needs to be translated to `x = p + z + t = (z +ᵥ t) +ₐ p` with `p ∈ P` and `z + t ∈ C`

      -- set p := hom.ofPoint⁻¹ p_hom with hp
      -- set z := hom.ofVector ⁻¹ z_hom with hz
      -- set t := hom.ofVector ⁻¹ t_hom with ht

      --/-
      -- Alternative attempt following Moritz's proof:

      -- Construction path of Points:
      --    (G_hom_pos ⊆ V_hom) → (G_hom_pos_normalized ⊆ V_hom) → (Points ⊆ A)

      -- intermediate result: G_hom_pos and G_hom_pos_normalized generate the some hull:
      set X := (G_hom_pos : Set V_hom) with hX-- abbreviations
      set Y := (G_hom_pos_normalized : Set V_hom) with hY
      have hhull : PointedCone.hull 𝕜 X = PointedCone.hull 𝕜 Y := by
        have Y_to_X : ∀ g1 ∈ G_hom_pos_normalized, ∃ g2 ∈ G_hom_pos,
               ∃ multiplier : 𝕜, multiplier > 0 ∧ g1 = multiplier • g2 := by
          intro g1 hg1
          rw [h_G_hom_pos_normalized, Finset.mem_image] at hg1
          obtain ⟨g, g_in_G, g_versus_g1⟩ := hg1
          use g
          simp only [g_in_G, gt_iff_lt, true_and]
          use (hom.weight g)⁻¹ -- as multiplier
          rw [hG_hom_pos, Finset.mem_filter] at g_in_G
          have multiplier_pos : (hom.weight g)⁻¹ > 0 := inv_pos_of_pos g_in_G.2
          simp only [multiplier_pos, true_and, ← g_versus_g1]
          rfl
        have X_to_Y : ∀ g1 ∈ G_hom_pos, ∃ g2 ∈ G_hom_pos_normalized,
               ∃ multiplier : 𝕜, multiplier > 0 ∧ g1 = multiplier • g2 := by
          intro g1 hg1
          have hg1_in_hom_pos : g1 ∈ G_hom_pos := hg1
          rw [hG_hom_pos, Finset.mem_filter] at hg1
          obtain ⟨g_in_G, g_weight_pos⟩ := hg1
          have multiplier_pos : hom.weight g1 > 0 := g_weight_pos
          set g2 := (hom.weight g1)⁻¹ • g1 with hg2
          use g2
          rw [h_G_hom_pos_normalized, Finset.mem_image]
          constructor
          · use g1
            simp only [hg1_in_hom_pos, hg2, true_and]
            rfl
          · use hom.weight g1
            simp only [gt_iff_lt, multiplier_pos, hg2, true_and]
            simp only [smul_smul, mul_inv_cancel₀ multiplier_pos.ne', one_smul]

        have : PointedCone.hull 𝕜 X ≤ PointedCone.hull 𝕜 Y :=
          hull_invariant_under_scaling_subset X Y X_to_Y
        have : PointedCone.hull 𝕜 Y ≤ PointedCone.hull 𝕜 X :=
          hull_invariant_under_scaling_subset Y X Y_to_X
        apply le_antisymm <;> assumption

      have weight_G_normalized_eq_one : ∀ g ∈ G_hom_pos_normalized, hom.weight g = 1 := by
        sorry

      have Points_vs_G_hom_pos_normalized : hom.ofPoint '' Points = G_hom_pos_normalized := by
        rw [hPoints]
        simp only [Finset.coe_preimage]
        apply image_preimage_eq_of_subset
        rw [hom.ofPoint_range_eq_preimage_weight_one, ←image_subset_iff, subset_singleton_iff]
        intro w hw
        rw [mem_image] at hw
        obtain ⟨x, ⟨hxG, weight_of_x_eq_w⟩ ⟩ := hw
        rw [←weight_G_normalized_eq_one x hxG]
        exact weight_of_x_eq_w.symm

      have : hull 𝕜 (hom.ofPoint '' Points) = homogenize V_hom P_convSet := by
        rw [← hull_image_ofPoint_eq_homogenize_convexHull]


      have : D_hom = hull 𝕜 G_hom := by rw [←hG_hom]

      have x_hom_decomp : x_hom = p_hom + z_hom + t_hom := by
        rw [p_hom_plus_z_hom_eq_d_hom, d_hom_plus_t_hom_eq_x_hom]
      -- We have the decomposition `x_hom = p_hom + z_hom + t_hom`
      -- This needs to be translated to `x = p + z + t = (z +ᵥ t) +ₐ p` with `p ∈ P` and `z + t ∈ C`

      -- set p := hom.ofPoint⁻¹ p_hom with hp
      -- set z := hom.ofVector ⁻¹ z_hom with hz
      -- set t := hom.ofVector ⁻¹ t_hom with ht

      have t_weight_eq_zero : t_hom.weight = 0 := T_weight_eq_zero t_hom ht_hom

      have z_weight_eq_zero : z_hom.weight = 0 := by
        have hmap_zero : (hull 𝕜 ↑(G_hom_zero : Set V_hom)).map hom.weight = ⊥ := by
          rw [PointedCone.map_hull, span_eq_bot, forall_mem_image]
          intro x hx
          rw [Finset.mem_coe, Finset.mem_filter] at hx
          exact hx.2
        have h_z_mem_bot : hom.weight z_hom ∈ (⊥ : PointedCone 𝕜 𝕜) := by
          rw [←hmap_zero, PointedCone.mem_map]
          exact ⟨z_hom, hz_hom, rfl⟩
        rw [mem_bot] at h_z_mem_bot
        exact h_z_mem_bot

      have p_weight_eq_one : p_hom.weight = 1 := by
        have : x_hom.weight = p_hom.weight + z_hom.weight + t_hom.weight := by
          rw [x_hom_decomp, map_add, map_add, add_right_inj]
        rw [t_weight_eq_zero, z_weight_eq_zero, x_hom_weight_eq_one, add_zero, add_zero] at this
        exact this.symm

      have p_exists : ∃ p : A, p_hom = hom.ofPoint p := by -- because p_hom.weight = 1
        apply (hom.weight_one_iff p_hom).mp
        exact p_weight_eq_one
      have v_exists : ∀ v_hom : V_hom, (v_hom.weight = 0) → ∃ v : V, hom.ofVector v = v_hom := by
        intro v_hom hv_hom
        have hrange : v_hom ∈ LinearMap.range hom.ofVector := by
          rw [hom.ofVector_range_eq_weight_ker]
          exact hv_hom
        exact (LinearMap.mem_range.mp hrange)

      choose (p : A) hp using p_exists
      choose (z : V) hz using v_exists z_hom z_weight_eq_zero
      choose (t : V) ht using v_exists t_hom t_weight_eq_zero

      have x_decomp : x = (z +ᵥ t) +ᵥ p := by
        have : hom.ofPoint x = hom.ofPoint ((z +ᵥ t) +ᵥ p) := calc
          hom.ofPoint x = x_hom := hx_hom_def.symm
          _ = p_hom + z_hom + t_hom := x_hom_decomp
          _ = hom.ofPoint p + (hom.ofVector z + hom.ofVector t) := by rw [←hp, ←hz, ←ht, add_assoc]
          _ = hom.ofPoint p + hom.ofVector (z + t) := by rw [← LinearMap.map_add]
          _ = hom.ofVector (z + t) + hom.ofPoint p := by rw [add_comm]
          _ = hom.ofPoint ((z +ᵥ t) +ᵥ p) := by
            simp only [map_add, vadd_eq_add, AffineMap.map_vadd]
          --_ = hom.ofPoint (z +ᵥ t +ᵥ p) := by sorry
        apply hom.ofPoint_injective
        exact this

      have : p ∈ P := by
        sorry

      have : t ∈ Linear_subspace := by
        rw [ hLinear]
        simp only [Submodule.mem_map]
        use t_hom
        constructor
        · rw [← SetLike.mem_coe]
          exact ht_hom
        · rw [←ht]
          unfold LinearMap.leftInverse
          have ofVector_inj : hom.ofVector.ker = ⊥ := LinearMap.ker_eq_bot_of_injective hom.ofVector_injective
          rw [dite_eq_left ofVector_inj]
          -- simp?

          -- How do I prove "Affine.IsHomogenization.ofVector.leftInverse (Affine.IsHomogenization.ofVector t) = t" when I know that the function "ofVector" is injective?
          sorry
      have : z ∈ hull 𝕜 Rays := by
        sorry --?simp?


      have a1 : hull 𝕜 (hom.ofPoint '' Points) = homogenize V_hom P_convSet := by
        rw [← hull_image_ofPoint_eq_homogenize_convexHull]

--  /-- Dehomogenizing the homogenization of a convex set yields the same set again. -/
-- @[simp] theorem dehomogenize_homogenize (P : ConvexSet R A) :
--     dehomogenize A (homogenize W P) = P := by

--lemma ofPoint_mem_homogenize_iff_mem (x : A) (P : ConvexSet R A) :
--    hom.ofPoint x ∈ homogenize W P ↔ x ∈ P := by

      have : p ∈ P := by -- lots of small steps
        have : p_hom ∈ hull 𝕜 ↑G_hom_pos := hp_hom
        have : p_hom ∈ hull 𝕜 ↑G_hom_pos_normalized := by
          rw [←hhull]
          exact this
        have : p_hom ∈ hull 𝕜 (hom.ofPoint '' Points) := by
          rw [Points_vs_G_hom_pos_normalized]
          exact this
        have a2 : p_hom ∈ homogenize V_hom P_convSet := by
          rw [← a1]
          exact this
        rw [hp] at a2
        apply (ofPoint_mem_homogenize_iff_mem V_hom p P_convSet).mp at a2
        rw [hP]
        simp only [SetLike.mem_coe]
        exact a2

      -- The following will be partially obsolete. -----------------------------------
      obtain ⟨μ, ⟨hμ, h_positive_combination_μ⟩ ⟩ := Submodule.mem_span_finset.mp hp_hom
      -- We can normalize the g_i to weight 1 to get points in Points.
      -- Since `x` as well as the points in `Points` have weight 1,
      -- and all other points have weight 0,  `∑ λ_i = 1`, and thus
      -- `x` is a convex combination of (normalized) points in Points plus a point in C:
      -- x_hom = c +ᵥ p for some c ∈ C and p ∈ P
      let P_pos := μ.support
      have sum_pos1: ∑ g ∈ G_hom_pos, μ g * g.weight = 1 := by
        have sum_1: ∑ g ∈ G_hom, μ g * g.weight = 1 := by
          have t_weight_zero : t_hom.weight = 0 := T_weight_eq_zero t_hom ht_hom
          --have : (d_hom + t_hom).weight = 1 := by
          --  rw [d_hom_plus_s_is_x_hom, hx_hom_def]
          --  exact hom.weight_one x
          --have : (d_hom + t_hom).weight = d_hom.weight + s.weight := by rw [LinearMap.map_add]
          have d_hom.weight_eq_one : d_hom.weight = 1 :=
          calc
            d_hom.weight = d_hom.weight + 0 := by rw [add_zero]
            _ = d_hom.weight + t_hom.weight     := by rw [t_weight_zero]
            _ = (d_hom + t_hom).weight          := by rw [LinearMap.map_add]
            _ = x_hom.weight                := by rw [d_hom_plus_t_hom_eq_x_hom]
            _ = hom.weight x_hom            := by rfl
            _ = hom.weight (hom.ofPoint x)  := by rw [hx_hom_def]
            _ = 1                           := hom.weight_one x
          have h_mul_eq_smul : ∀ g ∈ G_hom, μ g * g.weight = (μ g • g).weight := by
            intro g hg
            simp only [LinearMap.map_smul_of_tower]
            congr
          have h_lin: ∑ g ∈ G_hom, (μ g • g).weight = (∑ g ∈ G_hom, μ g • g).weight := by
            simp only [map_sum, LinearMap.map_smul_of_tower]
          rw [Finset.sum_congr rfl h_mul_eq_smul]
          sorry -- a translation step from V_hom to V is missing.
          -- rw [h_lin, h_positive_combination_μ, d_hom.weight_eq_one]
        have sum_0: ∑ g ∈ G_hom_zero, μ g * g.weight = 0 := by
          apply Finset.sum_eq_zero
          intro g hg
          rw [hG_hom_zero, Finset.mem_filter ] at hg
          rw [hg.2, mul_zero]
        rw [← Finset.sum_filter_add_sum_filter_not G_hom
            (fun g => g.weight > 0)] at sum_1

        have hG_hom_nonpos : ∑ x ∈ G_hom with ¬ x.weight > 0, ↑(μ x) * x.weight = 0 := by
          apply Finset.sum_eq_zero
          intro g hg
          obtain ⟨hg, hg'⟩ := Finset.mem_filter.mp hg
          have h_nonneg : g.weight ≥ 0 := hG_hom_nonneg g hg
          have h_zero : g.weight = 0 := by
            apply le_antisymm (le_of_not_gt hg') h_nonneg
          simp only [h_zero, mul_zero]
        rw [hG_hom_nonpos] at sum_1
        simpa only [gt_iff_lt, add_zero] using sum_1
      have d_exists : ∃ d : A, hom.ofPoint d = d_hom := by
        sorry
      -- choose (d : A) (hd : hom.ofPoint d = d_hom) using d_exists
      choose (d : A) hd using d_exists

      have : d ∈ P := by
/- for showing that d ∈ Convexhull Points = P, get inspiration from above definition of hDsplit:
   have hDsplit : D = homogenize W (ConvexSet.convexHull 𝕜 (↑T : Set A)) ⊔ ... := by
    rw [← hull_image_ofPoint_eq_homogenize_convexHull, hhull, ← hPoints]
       -/
        sorry
      sorry
    -- Converse direction: show C +ᵥ P ⊆ H
    · intro x hx
      obtain ⟨c, hc, p, hp, rfl⟩ := Set.mem_vadd.mp hx
      -- let x ∈ C +ᵥ P. Then x = c +ᵥ p for some c ∈ C and p ∈ P
      -- We start by showing that p ∈ H
      have hp_in_H : p ∈ H := by
        rw [← dehomogenize_gives_back_H]
        sorry
      -- adding c does not lead out of H
      have hp_pos : (hom.ofPoint p).weight >= 0 := by
        sorry

      -- the rest is AI-generated stuff:
      have hc' : hom.ofVector c ∈ H_hom := by
        sorry
      have hp' : hom.ofPoint p ∈ H_hom := by
        sorry
      have hcp' : hom.ofPoint (c +ᵥ p) ∈ H_hom := by
        sorry
      have hcp : c +ᵥ p ∈ H := by
        rw [← dehomogenize_gives_back_H]
        sorry -- exact PointedCone.dehomogenize_mem.mpr hcp'
      exact hcp

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
      simpa only [LinearMap.coe_restrictScalars, restrictScalars_mem, LinearMap.mem_ker] using
        hom.weight_zero v
    · rintro z hz
      obtain ⟨hz₁, hz₂⟩ := Submodule.mem_inf.mp hz
      exact mem_map_recessionCone_of_weight_eq_zero hz₁
        (by simpa only [restrictScalars_mem, LinearMap.mem_ker] using hz₂)
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
  -- How to abstract the following two lines? (without meta)
  let W := CanonicalHomogenization 𝕜 A
  let := IsModuleConvexSpace.ofAddTorsor (R := 𝕜) (V := W)
  simpa only [PointedCone.dehomogenize, dehomogenize_homogenize, mk_eq] using
    ConvexSetimagedehomogenize_isHPolyhedron (A := A) _
      (IsHPolyhedral.fg _ (IsPolytope.homogenize_fg (R := 𝕜) W (C := ⟨P, hP.isConvexSet⟩) hP))

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

-- TODO: This should be moved to the polyhedral operations file. The proof relies on MW.
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

-- Wishlist:
-- * A bounded polyhedron is a polytope (i.e. the recession cone is trivial)
-- * Definition "bounded": Every affine function is bounded:
-- * Equivalent statement for polyhedra (for all convex sets?): There are no rays.
