/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.KreinMilman

/-! Krein-Milman for polytopes: a polytope is the convex hull of finitely many of its own
extreme points. Proved by transporting `PointedCone.FG.krein_milman` (Krein-Milman for finitely
generated cones, already proved in `Cone.Pointed.Finite.Face.KreinMilman`) through
homogenization, using the face-lattice correspondence in `Set.Face.Homogenization`. -/

namespace Convexity

open Affine Affine.IsHomogenization Pointwise PointedCone

variable {R A W : Type*}

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddTorsor V A]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R W]
variable [hom : Affine.IsHomogenization R A W]

/-- Krein-Milman for polytopes: a polytope is the convex hull of finitely many of its own
extreme points.

AI proofs
 -/
theorem IsPolytope.eq_convexHull_extremePoints (W : Type*) [AddCommGroup W] [Module R W]
    [IsModuleConvexSpace R W] [hom : Affine.IsHomogenization R A W]
    {C : Set A} (hC : IsPolytope R C) :
    ∃ E : Finset A, (↑E ⊆ C) ∧ C = Convexity.convexHull R (E : Set A) ∧
      ∀ y ∈ E, (({y} : ConvexSet R A)).IsFaceOf ⟨C, hC.isConvexSet⟩ := by
  classical
  set Cs : ConvexSet R A := ⟨C, IsPolytope.isConvexSet hC⟩ with hCs
  have hCfg : (ConvexSet.homogenize W Cs).FG := IsPolytope.homogenize_fg hC
  have hCsal : (ConvexSet.homogenize W Cs).Salient := ConvexSet.homogenize_salient
  obtain ⟨t, ht, htface⟩ := FG.krein_milman hCfg hCsal
  set t' := t.filter (· ≠ 0) with ht'def
  have ht'sub : (t' : Set W) ⊆ (t : Set W) := Finset.filter_subset _ _
  have ht'mem : ∀ v ∈ t', v ∈ Cs.homogenize W := fun v hv => ht ▸ subset_hull (ht'sub hv)
  have hchoice : ∀ v ∈ t', ∃ y ∈ Cs, ∃ c : R, 0 < c ∧ v = c • hom.ofPoint y := by
    intro v hv
    have hv0 : v ≠ 0 := (Finset.mem_filter.mp hv).2
    obtain ⟨c, hc, _, ⟨y, hy, rfl⟩, hveq⟩ :=
      ConvexSet.smul_pos_of_mem_homogenize (ht'mem v hv) hv0
    exact ⟨y, hy, c, hc, hveq.symm⟩
  choose y hy c hc hveq using hchoice
  set E : Finset A := t'.image (fun v => if h : v ∈ t' then y v h else Classical.arbitrary A)
    with hEdef
  have hEval : ∀ v (hv : v ∈ t'),
      (if h : v ∈ t' then y v h else Classical.arbitrary A) = y v hv := by
    intro v hv; simp [hv]
  have hEmem : ∀ v (hv : v ∈ t'), y v hv ∈ E :=
    fun v hv => Finset.mem_image.mpr ⟨v, hv, hEval v hv⟩
  have hinv : ∀ (a : A) (r : R), 0 < r → ∀ u : W, u = r • hom.ofPoint a →
      hom.ofPoint a = r⁻¹ • u := by
    intro a r hr u heq
    rw [heq, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  refine ⟨E, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    rw [hEval v hv]; exact hy v hv
  · -- C = convexHull R (E : Set A)
    have hspan : PointedCone.hull R (t' : Set W) =
        PointedCone.hull R (hom.ofPoint '' (E : Set A)) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        intro v hv
        rw [hveq v hv]
        exact (PointedCone.hull R (hom.ofPoint '' (E : Set A))).smul_mem (hc v hv).le
          (subset_hull ⟨y v hv, hEmem v hv, rfl⟩)
      · apply Submodule.span_le.mpr
        rintro w ⟨a, ha, rfl⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
        rw [hEval v hv, hinv (y v hv) (c v hv) (hc v hv) v (hveq v hv)]
        exact (PointedCone.hull R (t' : Set W)).smul_mem (inv_nonneg.mpr (hc v hv).le)
          (subset_hull hv)
    have h1 : PointedCone.hull R (t' : Set W) = Cs.homogenize W := by
      rw [← ht]
      apply le_antisymm
      · exact PointedCone.hull_mono ht'sub
      · apply Submodule.span_le.mpr
        intro v hv
        by_cases hv0 : v = 0
        · simp [hv0]
        · exact subset_hull (Finset.mem_filter.mpr ⟨hv, hv0⟩)
    have h2 : PointedCone.hull R (hom.ofPoint '' (E : Set A)) =
        ConvexSet.homogenize W (ConvexSet.convexHull R (E : Set A)) :=
      ConvexSet.hull_image_ofPoint_eq_homogenize_convexHull
    have h3 : Cs.homogenize W = ConvexSet.homogenize W (ConvexSet.convexHull R (E : Set A)) := by
      rw [← h1, hspan, h2]
    have h4 : Cs = ConvexSet.convexHull R (E : Set A) :=
      ConvexSet.homogenize_injective h3
    exact congrArg (SetLike.coe) h4
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    rw [hEval v hv]
    have hface : (R ∙₊ v).IsFaceOf (Cs.homogenize W) := htface v (ht'sub hv)
    rw [hveq v hv, PointedCone.hull_singleton_smul_eq (hc v hv)] at hface
    have hd := dehomogenize_isFaceOf A hface
    have heq1 : (R ∙₊ hom.ofPoint (y v hv) : PointedCone R W) =
        ConvexSet.homogenize W ({y v hv} : ConvexSet R A) := by
      simp [ConvexSet.homogenize]
    rw [heq1, ConvexSet.dehomogenize_homogenize, ConvexSet.dehomogenize_homogenize] at hd
    exact hd

end Field

end Convexity
