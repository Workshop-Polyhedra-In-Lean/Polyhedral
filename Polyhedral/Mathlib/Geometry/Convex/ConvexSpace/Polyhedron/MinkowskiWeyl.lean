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
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.HPolyhedron
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.Basic

/-! # Minkowski-Weyl for polyhedra

This file transfers between H- and V-descriptions of polyhedra via homogenization. -/

section Homogenization

open Convexity Pointwise Set PointedCone Submodule
open Convexity.ConvexSet

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {V' : Type*} [AddCommGroup V'] [Module R V']
variable {W : Type*} [AddCommGroup W] [Module R W]

variable {A : Type*} [AddTorsor V A]


attribute [local instance] AddTorsor.toConvexSpace

section Homogenize

variable [IsModuleConvexSpace R W]
variable [hom : Affine.IsHomogenization R A W]

/-- The dehomogenization of an H-polyhedral cone is an H-polyhedron: each functional `f`
cutting out the cone descends to the affine map `f ∘ ofPoint`, and the submodule pulls back
to an affine subspace. -/
lemma ConvexSet.dehomogenize_is_h_polyhedron (C : PointedCone R W)
    (hC : IsHPolyhedral .id C) :
    IsHPolyhedron R (PointedCone.dehomogenize A C : Set A) := by
  classical
  obtain ⟨D, S, ⟨G, rfl⟩, rfl⟩ := hC
  refine ⟨G.image fun f => f.toAffineMap.comp hom.ofPoint,
    S.toAffineSubspace.comap hom.ofPoint, ?_⟩
  ext x
  simp [PointedCone.dehomogenize, ConvexSet.dehomogenize, Set.mem_preimage,
    PointedCone.mem_dual, Submodule.mem_toAffineSubspace]

/-- Dehomogenizing the sum of a cone embedded at weight zero and the homogenization of a
convex set yields the pointwise sum. -/
lemma dehomogenize_map_ofVector_sup_homogenize (C : PointedCone R V) (P : ConvexSet R A) :
    (PointedCone.dehomogenize A (C.map hom.ofVector ⊔ homogenize W P) : Set A)
      = (C : Set V) +ᵥ (P : Set A) := by
  ext x
  simp only [PointedCone.dehomogenize, ConvexSet.dehomogenize, ConvexSet.mk_eq,
    Set.mem_preimage]
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

end Homogenize

-- `H = (C + S) +ᵥ P` should become the definition of `IsVPolyhedron`


/- Minkowski-Weyl for polyhedral cones -/
variable {p : V' →ₗ[R] V →ₗ[R] R} [Fact p.SeparatingRight]

omit [Fact p.SeparatingRight] in
lemma isHPolyhedral_of_v_polyhedral [Fact (Function.Surjective p)] {C : PointedCone R V}
    (hC : IsPolyhedral C) : IsHPolyhedral p C := by
  obtain ⟨D, hD, hDC⟩ := hC.exists_dualfg_inf_span p
  exact ⟨D, Submodule.span R (C : Set V), hD, hDC.symm⟩

section Homogenize

variable [IsModuleConvexSpace R W]
variable [hom : Affine.IsHomogenization R A W]

include hom in
/-- The Minkowski sum of an H-polyhedral cone and a polytope is an H-polyhedron: lift the
cone to weight zero in the homogenization space, add the homogenization of the polytope,
and dehomogenize the resulting polyhedral cone. -/
lemma isHPolyhedron_vadd_of_isHPolyhedral_of_isPolytope {C : PointedCone R V}
    (hC : IsHPolyhedral .id C) {P : Set A} (hP : IsPolytope R P) :
    IsHPolyhedron R ((C : Set V) +ᵥ P) := by
  have hpoly : ((C.map hom.ofVector)
      ⊔ homogenize W (⟨P, hP.isConvexSet⟩ : ConvexSet R A)).IsPolyhedral :=
    (hC.isPolyhedral.map hom.ofVector).sup
      (.of_fg (IsPolytope.homogenize_fg (C := ⟨P, hP.isConvexSet⟩) hP))
  have hH := ConvexSet.dehomogenize_is_h_polyhedron (A := A) _
    (isHPolyhedral_of_v_polyhedral hpoly)
  rw [dehomogenize_map_ofVector_sup_homogenize] at hH
  simpa using hH

end Homogenize

/- Minkowski-Weyl for polyhedra -/
open Convex

-- def IsHPolyhedron.vertices {P : Set A} (hP : IsHPolyhedron R P) : Finset { v ∈ Set A | IsFace 0 hP v}

-- Could be for `ConvexSet` (to avoid polluting the `Set` namespace)
-- This definiton assigns ⊤ as the recession cone of ∅
-- The ∀ could be an ∃ (we could prove it's equivalent for polytopes)
-- For `ConvexSet`, the ∀a is not necessary
#click_suggestions
variable (R) in
def Convex.Set.recessionCone (P : Set A) : PointedCone R V where
  carrier := { v : V | ∀ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P }
  add_mem' := by
    -- TODO: golf
    intro a b ha hb
    simp only [mem_ofPred_eq, smul_add] at ha hb ⊢
    intro x hx c hc
    have hb' := hb x hx c hc
    have ha' := ha (c•b +ᵥ x) hb' c
    rw [add_vadd]
    exact ha' hc
  zero_mem' := by
    simp only [mem_ofPred_eq, smul_zero, zero_vadd]
    intro x hx a ha
    exact hx
  smul_mem' := by
    -- TODO: golf
    intro ⟨c, hc⟩ x h
    simp only [mem_ofPred_eq, Nonneg.mk_smul] at ⊢ h
    intro y hy a ha
    rw [smul_smul]
    exact h y hy (a * c) (show 0 ≤ a * c by exact Right.mul_nonneg ha hc)

lemma Convex.Set.mem_recessionCone {P : Set A} {v : V} :
    v ∈ P.recessionCone R ↔ ∀ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P := Iff.rfl

/-- For a nonempty H-polyhedron, membership in the recession cone can be tested at a single
point: a direction recedes from every point as soon as it recedes from one. -/
lemma IsHPolyhedron.mem_recessionCone_iff_exists {P : Set A} (hP : IsHPolyhedron R P)
    (hne : P.Nonempty) {v : V} :
    v ∈ P.recessionCone R ↔ ∃ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P := by
  rw [Convex.Set.mem_recessionCone]
  exact hP.forall_smul_vadd_mem_iff_exists hne

/-- Minkowski addition of a set P and its recession cone leaves P unchanged. -/
lemma Convex.Set.recessionCone_vadd_self {P : Set A} :
    (P.recessionCone R : Set V) +ᵥ P = P := by
  ext x
  constructor
  · rintro ⟨v, hv, y, hy, rfl⟩
    simpa using (Convex.Set.mem_recessionCone.mp hv) y hy 1 zero_le_one
  · intro hx
    exact ⟨0, (P.recessionCone R).zero_mem, x, hx, zero_vadd _ _⟩

/-- The recession cone of a nonempty polytope is trivial: any nonzero direction admits a
linear functional positive on it, which is bounded on the convex hull of the finitely many
generators. -/
lemma Convexity.IsPolytope.recessionCone_eq_bot {P : Set A} (hP : IsPolytope R P)
    (hne : P.Nonempty) : P.recessionCone R = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra hv0
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual R V, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff R v).mp hcon)
  obtain ⟨x₀, hx₀⟩ := hne
  set g : Module.Dual R V := (f v)⁻¹ • f with hg
  have hgv : g v = 1 := by simp [hg, inv_mul_cancel₀ hf]
  set h : A →ᵃ[R] R := g.toAffineMap.comp (AffineEquiv.vaddConst R x₀).symm.toAffineMap
    with hhdef
  have happ : ∀ y : A, h y = g (y -ᵥ x₀) := fun y => by simp [hhdef]
  obtain ⟨t, rfl⟩ := hP
  have hte : t.Nonempty := by
    rcases Finset.eq_empty_or_nonempty t with rfl | hte
    · simp at hx₀
    · exact hte
  have hbound : ∀ y ∈ Convexity.convexHull R (t : Set A), h y ≤ t.sup' hte h := by
    intro y hy
    refine convexHull_min (fun s hs => ?_)
      ((isConvexSet_Iic (t.sup' hte h)).preimage h.isAffineMap) hy
    exact Finset.le_sup' h hs
  have hray : ∀ a : R, 0 ≤ a → a ≤ t.sup' hte h := by
    intro a ha
    have hb := hbound _ ((Convex.Set.mem_recessionCone.mp hv) x₀ hx₀ a ha)
    rwa [happ, vadd_vsub, map_smul, smul_eq_mul, hgv, mul_one] at hb
  have h0 : (0 : R) ≤ t.sup' hte h := hray 0 le_rfl
  have := hray (t.sup' hte h + 1) (by linarith)
  linarith

-- this lemma does not seem to be used.
#click_suggestions
lemma IsHPolyhedron.recessionCone_isHPolyhedral {P : Set A} (hP : IsHPolyhedron R P) :
    IsHPolyhedral .id (P.recessionCone R) := by
  classical
  by_cases h : ∅ = P
  · simp only [Convex.Set.recessionCone, h.symm, mem_empty_iff_false, imp_false, not_le,
      IsEmpty.forall_iff, implies_true, ofPred_true]
    exact IsHPolyhedral.top _
  -- We need to use a point in `P` for the proof below
  obtain ⟨x, hx : x ∈ P⟩ := Set.nonempty_iff_empty_ne.mpr h

  obtain ⟨H₁, ⟨S₁, rfl⟩⟩ := hP

  unfold IsHPolyhedral Set.recessionCone
  let P := (⋂ h ∈ H₁, ⇑h ⁻¹' Ici 0) ∩ ↑S₁
  let C := H₁.image (·.linear)

  simp only [IsHPolyhedral, Set.recessionCone, mem_inter_iff, mem_iInter, mem_preimage, mem_Ici,
    SetLike.mem_coe, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, and_imp,
    exists_and_left]
  use (PointedCone.dual .id C)
  constructor
  · exact DualFG.dual_of_finset .id C
  · use S₁.direction
    ext v
    simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, mem_ofPred_eq,
      Finset.coe_preimage, mem_inf, PointedCone.mem_dual, mem_preimage,
      SetLike.mem_coe, restrictScalars_mem]

    constructor
    · intro h
      specialize h x
      specialize h (by
        intro i hi
        simp at hx
        simp [hi, hx]
      )
      sorry
      -- specialize h (by
      --   simp at hx
      --   simp [hx]
      --   sorry
      -- )
      -- constructor
      -- · intro w hw
      --   -- have hf : ∃f ∈ H₁, p w = f.linear := match (hC' (p w)).mp hw with
      --   --   | ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ => ⟨f, ⟨hf, h_eq⟩⟩
      --   -- have h_zero : ∃a ∈ A, (p w) a = 0,
      --   -- obtain ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ := (hC' (p w)).mp hw
      --   -- let ker := f ⁻¹' {0}
      --   -- let k := f.linear.zero
      --   -- have i := p w
      --   sorry
      -- · sorry
    · intro ⟨hv, hvs⟩ y hyP hyS a ha
      constructor
      · intro i hi
        have hiP := hyP i hi
        -- have hc := (hC i).mp hi
        sorry
      · have h_av : a • v ∈ S₁.direction := by exact Submodule.smul_mem S₁.direction a hvs
        exact (AffineSubspace.vadd_mem_iff_mem_of_mem_direction h_av).mpr hyS

/-- If an affine functional is nonnegative along the ray `a • v +ᵥ x`, `a ≥ 0`, then its
linear part is nonnegative on the direction `v`. -/
lemma AffineMap.linear_nonneg_of_forall_nonneg (h : A →ᵃ[R] R) {x : A} {v : V}
    (hray : ∀ a : R, 0 ≤ a → 0 ≤ h (a • v +ᵥ x)) : 0 ≤ h.linear v := by
  by_contra hneg
  push Not at hneg
  have h0 : (0 : R) ≤ h x := by simpa using hray 0 le_rfl
  have hdiv : (0 : R) ≤ (h x + 1) / (-h.linear v) := div_nonneg (by linarith) (by linarith)
  have hkey := hray _ hdiv
  simp only [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add] at hkey
  have hcancel : (h x + 1) / (-h.linear v) * (-h.linear v) = h x + 1 :=
    div_mul_cancel₀ _ (by linarith)
  linarith

section Homogenize

variable [IsModuleConvexSpace R W]
variable [hom : Affine.IsHomogenization R A W]

omit [LinearOrder R] [IsOrderedRing R] [IsModuleConvexSpace R W] in
/-- Every affine functional extends to a linear functional on the homogenization space which
agrees with it on points and with its linear part on vectors. -/
lemma Affine.IsHomogenization.exists_linear_extension (h : A →ᵃ[R] R) :
    ∃ F : W →ₗ[R] R, (∀ x : A, F (hom.ofPoint x) = h x) ∧
      ∀ v : V, F (hom.ofVector v) = h.linear v := by
  obtain ⟨F, hF, -⟩ := hom.extend R h
  have hFx : ∀ x : A, F (hom.ofPoint x) = h x := fun x => congrFun hF x
  refine ⟨F, hFx, fun v => ?_⟩
  have x₀ := Classical.arbitrary A
  have hv : hom.ofVector v = hom.ofPoint (v +ᵥ x₀) - hom.ofPoint x₀ := by simp
  rw [hv, map_sub, hFx, hFx]
  simp

omit [IsModuleConvexSpace R W] in
/-- The homogenization of an H-polyhedron, together with its recession cone placed at weight
zero, is an H-polyhedral cone. -/
theorem PointedCone.homogenize_sup_recessionCone_is_h_polyhedral (S : ConvexSet R A)
    (hS : IsHPolyhedron R (S : Set A)) :
    IsHPolyhedral .id
      (homogenize W S ⊔ ((S : Set A).recessionCone R).map hom.ofVector) := by
  classical
  by_cases hne : (S : Set A).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨H, T, hST⟩ := hS
    choose ext hext hextlin using fun h : A →ᵃ[R] R => hom.exists_linear_extension h
    have hmem : ∀ x : A, x ∈ (S : Set A) ↔ (∀ h ∈ H, 0 ≤ h x) ∧ x ∈ T := by
      intro x
      rw [hST]
      simp
    have hx₀T : x₀ ∈ T := ((hmem x₀).mp hx₀).2
    refine ⟨dual .id ↑(insert hom.weight (H.image ext)),
      T.direction.map hom.ofVector ⊔ R ∙ hom.ofPoint x₀,
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
        change ∀ y ∈ (S : Set A), ∀ a : R, 0 ≤ a → a • u +ᵥ y ∈ (S : Set A)
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
      have hSbot : S = (⊥ : ConvexSet R A) := SetLike.ext' (by simpa using hSe)
      rw [hSbot]
      exact homogenize_bot
    have h2 : (S : Set A).recessionCone R = ⊤ := by
      rw [eq_top_iff]
      rintro v -
      change ∀ y ∈ (S : Set A), ∀ a : R, 0 ≤ a → a • v +ᵥ y ∈ (S : Set A)
      simp [hSe]
    refine ⟨⊤, LinearMap.ker hom.weight, by simp, ?_⟩
    rw [h1, h2, bot_sup_eq]
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

/-- Dehomogenizing the homogenization-with-recession-cone of a convex set recovers the set. -/
lemma dehomogenize_homogenize_sup_recessionCone (S : ConvexSet R A) :
    (PointedCone.dehomogenize A
      (homogenize W S ⊔ ((S : Set A).recessionCone R).map hom.ofVector) : Set A) = S := by
  rw [sup_comm, dehomogenize_map_ofVector_sup_homogenize, Convex.Set.recessionCone_vadd_self]

/-- The weight-zero slice of the homogenization-with-recession-cone consists exactly of the
embedded recession directions. -/
lemma mem_map_recessionCone_of_weight_eq_zero {S : ConvexSet R A} {z : W}
    (hz : z ∈ homogenize W S ⊔ ((S : Set A).recessionCone R).map hom.ofVector)
    (hw : hom.weight z = 0) :
    z ∈ ((S : Set A).recessionCone R).map hom.ofVector := by
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

include hom in
/-- `H → V` direction of the Minkowski-Weyl theorem for polyhedra: every H-polyhedron is the
Minkowski sum of its recession cone and a polytope. The polytope is extracted from a finite
generating set of the homogenization-with-recession-cone by normalizing the positive-weight
generators to weight one. -/
theorem IsHPolyhedron.exists_isPolytope_recessionCone_vadd {H : Set A}
    (hH : IsHPolyhedron R H) :
    ∃ P : Set A, IsPolytope R P ∧ H = (H.recessionCone R : Set V) +ᵥ P := by
  classical
  set S : ConvexSet R A := hH.toConvexSet with hSdef
  set Chom : PointedCone R W :=
    homogenize W S ⊔ ((S : Set A).recessionCone R).map hom.ofVector with hChom
  have hdeh : (PointedCone.dehomogenize A Chom : Set A) = H :=
    dehomogenize_homogenize_sup_recessionCone S
  obtain ⟨D, hDfg, S₀, hsplit⟩ :=
    (PointedCone.homogenize_sup_recessionCone_is_h_polyhedral (W := W) S hH).isPolyhedral
  obtain ⟨G, hG⟩ := hDfg
  rw [← hChom] at hsplit
  -- all weights in `Chom` are nonnegative
  have hCw : ∀ z ∈ Chom, 0 ≤ hom.weight z := by
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
  have hDle : D ≤ Chom := hsplit ▸ le_sup_left
  have hGw : ∀ g ∈ G, 0 ≤ hom.weight g := fun g hg =>
    hCw _ (hDle (hG ▸ Submodule.subset_span hg))
  have hS₀w : ∀ s ∈ S₀, hom.weight s = 0 := by
    intro s hs
    have h₁ := hCw _ (hsplit ▸ Submodule.mem_sup_right (Submodule.neg_mem _ hs) :
      -s ∈ Chom)
    have h₂ := hCw _ (hsplit ▸ Submodule.mem_sup_right hs : s ∈ Chom)
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
  have hhull : PointedCone.hull R (hom.ofPoint '' ↑T) = PointedCone.hull R ↑Gpos := by
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
      = homogenize W (ConvexSet.convexHull R (↑T : Set A)) ⊔ PointedCone.hull R ↑Gzero := by
    rw [← hull_image_ofPoint_eq_homogenize_convexHull, hhull, ← hG]
    conv_lhs => rw [hGsplit]
    rw [Finset.coe_union, Submodule.span_union]
  -- the zero-weight part
  have hKw : ∀ z ∈ (PointedCone.hull R ↑Gzero ⊔ (S₀ : PointedCone R W) : PointedCone R W),
      hom.weight z = 0 := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    have hha : hom.weight a = 0 := by
      have hle : PointedCone.hull R ↑Gzero
          ≤ ((LinearMap.ker hom.weight : Submodule R W) : PointedCone R W) :=
        Submodule.span_le.mpr fun g hg => by
          simpa using hGzerow g (Finset.mem_coe.mp hg)
      simpa using hle ha
    have hhb := hS₀w b (by simpa using hb)
    simp [hha, hhb]
  -- the polytope
  refine ⟨Convexity.convexHull R ↑T, ⟨T, rfl⟩, ?_⟩
  have hPH : Convexity.convexHull R ↑T ⊆ H := by
    intro y hy
    have h2 : hom.ofPoint y ∈ Chom := by
      rw [hsplit, hDsplit]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_span_of_mem (Set.mem_image_of_mem _ hy)))
    rw [← hdeh]
    simpa [PointedCone.dehomogenize, ConvexSet.dehomogenize] using h2
  have hHsub : H ⊆ (H.recessionCone R : Set V) +ᵥ Convexity.convexHull R ↑T := by
    intro x hx
    have hx' : hom.ofPoint x ∈ Chom := by
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
    have hkC : k ∈ Chom := by
      rw [hsplit, hDsplit, sup_assoc]
      exact Submodule.mem_sup_right hk
    obtain ⟨v, hv, hveq⟩ :=
      PointedCone.mem_map.mp (mem_map_recessionCone_of_weight_eq_zero (hChom ▸ hkC) hkw)
    have hxy : x -ᵥ y ∈ H.recessionCone R := by
      have hveq' : v = x -ᵥ y := hom.ofVector_injective (by rw [hveq, hkofv])
      exact hveq' ▸ hv
    exact Set.mem_vadd.mpr ⟨x -ᵥ y, hxy, y, hy, vsub_vadd x y⟩
  refine Set.Subset.antisymm hHsub ?_
  rintro _ ⟨v, hv, y, hy, rfl⟩
  rw [← Convex.Set.recessionCone_vadd_self (R := R) (P := H)]
  exact Set.mem_vadd.mpr ⟨v, hv, y, hPH hy, rfl⟩

include hom in
lemma IsHPolyhedron.recessionCone_isPolyhedral_aux {H : Set A} (hH : IsHPolyhedron R H) :
    IsPolyhedral (H.recessionCone R) := by
  have hmap : ((H.recessionCone R).map hom.ofVector : PointedCone R W)
      = (homogenize W hH.toConvexSet
          ⊔ ((hH.toConvexSet : Set A).recessionCone R).map hom.ofVector)
        ⊓ ↑(LinearMap.ker hom.weight) := by
    apply le_antisymm
    · refine le_inf le_sup_right ?_
      rintro _ ⟨v, -, rfl⟩
      simpa using hom.weight_zero v
    · rintro z hz
      obtain ⟨hz₁, hz₂⟩ := Submodule.mem_inf.mp hz
      exact mem_map_recessionCone_of_weight_eq_zero hz₁ (by simpa using hz₂)
  have hpoly : ((H.recessionCone R).map hom.ofVector).IsPolyhedral := by
    rw [hmap]
    exact (PointedCone.homogenize_sup_recessionCone_is_h_polyhedral (W := W)
      hH.toConvexSet hH).isPolyhedral.inf (.of_submodule _)
  have hcm : ((H.recessionCone R).map hom.ofVector).comap hom.ofVector
      = H.recessionCone R := by
    ext v
    rw [PointedCone.mem_comap, PointedCone.mem_map]
    constructor
    · rintro ⟨w, hw, heq⟩
      exact hom.ofVector_injective heq ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  exact hcm ▸ hpoly.comap hom.ofVector

end Homogenize

/-- The recession cone of an H-polyhedron is a polyhedral cone. -/
lemma IsHPolyhedron.recessionCone_isPolyhedral {H : Set A} (hH : IsHPolyhedron R H) :
    IsPolyhedral (H.recessionCone R) := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  exact IsHPolyhedron.recessionCone_isPolyhedral_aux (W := W) hH

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
lemma isVPolyhedron_of_isHPolyhedron (H : Set A) (hH : IsHPolyhedron R H) :
    ∃P : Set A, (IsPolytope R P) ∧ H = (H.recessionCone R : Set V) +ᵥ P := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  exact IsHPolyhedron.exists_isPolytope_recessionCone_vadd (W := W) hH

/-
`V → H` direction of the *Minkowski-Weyl* theorem.
For every finite *V-polytope* + *rays* + *submodule*,
there exists a finite set of inequalities that describe it.
-/
lemma isHPolyhedron_of_isPolytope {P : Set A} (hP : IsPolytope R P) :
    IsHPolyhedron R P := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  have h := ConvexSet.dehomogenize_is_h_polyhedron (A := A) _
    (IsHPolyhedral.fg _ (IsPolytope.homogenize_fg (W := W) (C := ⟨P, hP.isConvexSet⟩) hP))
  simpa [PointedCone.dehomogenize] using h

/-- `V → H` direction of the Minkowski-Weyl theorem for polyhedra: the Minkowski sum of an
H-polyhedral cone and a polytope is an H-polyhedron. -/
lemma isHPolyhedron_of_isVPolyhedron {P : Set A} (hP : IsPolytope R P)
    {C : PointedCone R V} (hC : IsHPolyhedral .id C) :
    IsHPolyhedron R ((C : Set V) +ᵥ P) := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  exact isHPolyhedron_vadd_of_isHPolyhedral_of_isPolytope (W := W) hC hP

/-- The Minkowski sum of two H-polyhedra is an H-polyhedron: decompose both by Minkowski-Weyl,
sum the polytopes and the recession cones separately, and reassemble. -/
lemma IsHPolyhedron.vadd {P : Set V} (hP : IsHPolyhedron R P) {Q : Set A}
    (hQ : IsHPolyhedron R Q) :
    IsHPolyhedron R (P +ᵥ Q) := by
  obtain ⟨P₁, hP₁, hPeq⟩ := isVPolyhedron_of_isHPolyhedron P hP
  obtain ⟨Q₁, hQ₁, hQeq⟩ := isVPolyhedron_of_isHPolyhedron Q hQ
  have hEq : P +ᵥ Q
      = ((P.recessionCone R ⊔ Q.recessionCone R : PointedCone R V) : Set V)
        +ᵥ (P₁ +ᵥ Q₁) := by
    conv_lhs => rw [hPeq, hQeq]
    ext z
    constructor
    · rintro ⟨_, ⟨c₁, hc₁, p₁, hp₁, rfl⟩, _, ⟨c₂, hc₂, q₁, hq₁, rfl⟩, rfl⟩
      refine Set.mem_vadd.mpr ⟨c₁ + c₂, Submodule.add_mem_sup hc₁ hc₂,
        p₁ +ᵥ q₁, Set.mem_vadd.mpr ⟨p₁, hp₁, q₁, hq₁, rfl⟩, ?_⟩
      simp only [vadd_vadd, vadd_eq_add]
      congr 1
      abel
    · rintro ⟨v, hv, _, ⟨p₁, hp₁, q₁, hq₁, rfl⟩, rfl⟩
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := Submodule.mem_sup.mp hv
      refine Set.mem_vadd.mpr ⟨c₁ +ᵥ p₁, Set.mem_vadd.mpr ⟨c₁, hc₁, p₁, hp₁, rfl⟩,
        c₂ +ᵥ q₁, Set.mem_vadd.mpr ⟨c₂, hc₂, q₁, hq₁, rfl⟩, ?_⟩
      simp only [vadd_vadd, vadd_eq_add]
      congr 1
      abel
  rw [hEq]
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := V)
  exact isHPolyhedron_of_isVPolyhedron (hP₁.vadd hQ₁)
    (isHPolyhedral_of_v_polyhedral (hP.recessionCone_isPolyhedral.sup
      hQ.recessionCone_isPolyhedral))

end Field
end Homogenization
