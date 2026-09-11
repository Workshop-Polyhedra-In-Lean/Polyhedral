/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

-- Günter Rote : separated the alternative proof in a separate file.--

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
-- import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.MinkowskiWeyl

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



-- `H = (C + S) +ᵥ P` should become the definition of `IsVPolyhedron`


/- Minkowski-Weyl for polyhedra -/
open Convex

section Homogenize

variable [IsModuleConvexSpace 𝕜 W]
variable [hom : Affine.IsHomogenization 𝕜 A W]

-- The following Lemma is copied from MinkowskiWeyl.lean:

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

variable [DecidableEq (W →ₗ[𝕜] 𝕜)]

-----------------------------------------------------------------

-- alternative formulation (with =) of the following lemma.
-- variable (V) in
-- variable [IsModuleConvexSpace 𝕜 V] in
-- lemma hull_invariant_under_scaling (G : Finset V) (multiplier : V → 𝕜) :
--   (∀ g ∈ G, multiplier g > 0) ∧  multiplier.support = G →
--   PointedCone.hull 𝕜 G = PointedCone.hull 𝕜 ((G : Set V).image (fun g => multiplier g • g)) := by

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

#click_suggestions
-- omit [AddCommGroup W] [Module 𝕜 W] [IsModuleConvexSpace 𝕜 W] in
-- G.R. don't understand: W does not appear in the theorem statement!
-- TODO: Find a better name?

-- An alternative formulation of the conclusion would be `H = C ⊔  P`

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
  choose extend_function hext_affine hext_linear using hom.exists_linear_extension
  set F_hom := Finset.image extend_function F with hF_hom
  -- 3. add the linear constraint for the "upper" half-space to get `F0_hom`
  set F0_hom := insert hom.weight F_hom with hF0_hom
  -- 4. Form the H-cone `C0_hom` in `V_hom` defined by the constraints `F0_hom`
  set C0_hom : PointedCone 𝕜 V_hom := dual .id F0_hom with hC0_hom
  --- C0_hom.carrier = { x : V_hom | ∀ f_hom ∈ F0_hom, f_hom x ≥ 0 },  -- pedestrian definition
  have hC0_nonneg : ∀ z ∈ C0_hom, 0 ≤ hom.weight z := by
    intro z hz
    exact (PointedCone.mem_dual.mp hz) (x := hom.weight)
      (by simp only [hF0_hom, Finset.coe_insert, mem_insert_iff, SetLike.mem_coe, true_or])
  have hC0_hom.dualFG : C0_hom.DualFG .id := by
    use F0_hom

  -- 5. homogenize the subspace `S` to get `S_hom`:
  set S_hom : Submodule 𝕜 V_hom := Submodule.span 𝕜 (hom.ofPoint '' S) with hS_hom

  -- 6. Form the H-cone `H_hom` by intersecting `C0_hom` with the subspace `S_hom`.
  set H_hom : PointedCone 𝕜 V_hom := C0_hom ⊓ S_hom with hC_hom

  -- 7. Fun fact: Dehomogenizing `H_hom` gives back the original H-polyhedron `H`. (not needed?)
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
      set x_hom : V_hom := hom.ofPoint x with hx_hom
      have x_hom_weight_eq_one: x_hom.weight = 1 := by
        have : x_hom ∈ hom.weight ⁻¹' {1} := by
          rw [← hom.ofPoint_range_eq_preimage_weight_one]
          use x
        rw [mem_preimage, mem_singleton_iff] at this
        exact this

      -- the following statements essentially prove the same as `dehomogenize_gives_back_H` :
      have hx' : x_hom ∈ C0_hom := by
        have x_satisfies_F : ∀ f ∈ F, 0 ≤ f x := by
          rw [hH] at hx
          apply mem_of_mem_inter_left at hx
          simp only [mem_iInter] at hx
          exact hx
        rw [hC0_hom, PointedCone.mem_dual, LinearMap.id_coe]
        simp only [SetLike.mem_coe, id_eq]
        intro f0_hom hf0_hom
        simp only [hF0_hom, Finset.mem_insert] at hf0_hom
        cases hf0_hom with
        | inl f_weight =>
            have : hom.weight x_hom = 1 := x_hom_weight_eq_one
            rw [f_weight, this]
            linarith
        | inr f_hom =>
            rw [hF_hom, Finset.mem_image] at f_hom
            obtain ⟨f, hf⟩  := f_hom
            have := hext_affine f x
            rw [hf.2, ←hx_hom] at this
            rw [this]
            exact x_satisfies_F f hf.1 -- show `f x ≥ 0`
      have hx22 : x_hom ∈ S_hom := by
        have : x ∈ S := by
          rw [hH] at hx
          simp only [mem_inter_iff] at hx
          exact hx.2
        have : x_hom ∈ hom.ofPoint '' ↑S := by
          simp only [mem_image, SetLike.mem_coe]
          use x
        rw [hS_hom]
        exact mem_span_of_mem this
      have hx_hom_in_H_hom : x_hom ∈ H_hom := by
        rw [Submodule.mem_inf]
        exact ⟨hx', hx22⟩
      have hC_hom_rep : x_hom ∈ D_hom ⊔ T := by
        rw [← h_representation]
        exact hx_hom_in_H_hom
      -- show that x ∈ C +ᵥ P
      -- since x_hom ∈ H_hom, `x_hom = (∑ μ_j r_j + t) +ᵥ (∑ λ_i g_i)`
      -- for some r_j ∈ Rays, t ∈ Linear_subspace, g_i ∈ G_hom_pos, μ_j ≥ 0, λ_i ≥ 0.
      obtain ⟨d_hom, hd_hom, t_hom, ht_hom, d_hom_plus_t_hom_eq_x_hom⟩ := mem_sup.mp hC_hom_rep
      -- rw [← hG_hom] at hd_hom
      have split_d : D_hom = hull 𝕜 G_hom_pos ⊔ hull 𝕜 G_hom_zero := by
        rw [←hull_union, ← Finset.coe_union, ←hG_hom_split, ←hG_hom]
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
        intro g hg
        rw [h_G_hom_pos_normalized, Finset.mem_image] at hg
        obtain ⟨g_hom, hg_hom ⟩ := hg
        rw [←hg_hom.2,  LinearMap.map_smul, inv_smul_eq_iff₀]
        · rw [smul_eq_mul, mul_one]
          rfl
        · -- prove `g_hom.weight ≠ 0` :
          apply ne_of_gt
          rw [hG_hom_pos, Finset.mem_filter] at hg_hom
          exact hg_hom.1.2

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
          hom.ofPoint x = x_hom := hx_hom.symm
          _ = p_hom + z_hom + t_hom := x_hom_decomp
          _ = hom.ofPoint p + (hom.ofVector z + hom.ofVector t) := by rw [←hp, ←hz, ←ht, add_assoc]
          _ = hom.ofPoint p + hom.ofVector (z + t) := by rw [←LinearMap.map_add]
          _ = hom.ofVector (z + t) + hom.ofPoint p := by rw [add_comm]
          _ = hom.ofPoint ((z +ᵥ t) +ᵥ p) := by
            simp only [map_add, vadd_eq_add, AffineMap.map_vadd]
        apply hom.ofPoint_injective
        exact this

      have t_in_Linear_subspace : t ∈ Linear_subspace := by
        rw [hLinear]
        simp only [Submodule.mem_map]
        refine ⟨t_hom, ⟨?t_hom_in_T , ?left_inverse ⟩⟩
        · rw [← SetLike.mem_coe]
          exact ht_hom
        · rw [←ht]
          have ofVector_inj : hom.ofVector.ker = ⊥ :=
            LinearMap.ker_eq_bot_of_injective hom.ofVector_injective
          exact LinearMap.leftInverse_apply_of_inj (f := hom.ofVector) ofVector_inj t
      have z_in_Rays : z ∈ hull 𝕜 Rays := by
        sorry --?simp? SCHON ZU HAUSE??

      have a1 : hull 𝕜 (hom.ofPoint '' Points) = homogenize V_hom P_convSet := by
        rw [← hull_image_ofPoint_eq_homogenize_convexHull]

--  /-- Dehomogenizing the homogenization of a convex set yields the same set again. -/
-- @[simp] theorem dehomogenize_homogenize (P : ConvexSet R A) :
--     dehomogenize A (homogenize W P) = P := by

--lemma ofPoint_mem_homogenize_iff_mem (x : A) (P : ConvexSet R A) :
--    hom.ofPoint x ∈ homogenize W P ↔ x ∈ P := by

      have p_in_P : p ∈ P := by
        rw [hP]
        have a3 : hom.ofPoint p ∈ homogenize V_hom P_convSet := by
          rw [←hp] -- p_hom ∈ ...
          rw [←a1] -- p_hom ∈ hull 𝕜 (hom.ofPoint '' Points)
          rw [Points_vs_G_hom_pos_normalized] --  p_hom ∈ hull 𝕜 ↑G_hom_pos_normalized
          rw [←hhull]
          exact hp_hom
        apply (ofPoint_mem_homogenize_iff_mem V_hom p P_convSet).mp at a3
        exact a3 -- a3 : p ∈ P_convSet

/- for showing that d ∈ Convexhull Points = P, could also get
   inspiration from above definition of hDsplit:
   have hDsplit : D = homogenize W (ConvexSet.convexHull 𝕜 (↑T : Set A)) ⊔ ... := by
    rw [← hull_image_ofPoint_eq_homogenize_convexHull, hhull, ← hPoints]
       -/

      have : z +ᵥ t ∈ C := by
        rw [hC]
        simp only [vadd_eq_add]
        rw [mem_sup]
        refine ⟨z, ⟨z_in_Rays, ?_⟩⟩ -- use z
        refine ⟨t, ⟨t_in_Linear_subspace, ?_⟩⟩ -- use t
        rfl
      rw [mem_vadd]
      refine ⟨z +ᵥ t, ⟨this, ?_⟩⟩ -- use z + t
      refine ⟨p, ⟨p_in_P, ?_⟩⟩ -- use p
      exact x_decomp.symm

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

end Homogenize
end Field
end Homogenization
