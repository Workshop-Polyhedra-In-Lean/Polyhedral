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
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.HPolyhedron
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.Basic

section Homogenization

open Convexity Pointwise Set PointedCone Submodule
open Convexity.ConvexSet

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {A : Type*} [AddTorsor V A]
-- variable {W : Type*} [AddCommGroup W] [Module R W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R V]

variable [hom : Affine.IsHomogenization R A V]

-- TODO: `ConvexSet` should be `SetLike` to avoid manual coercion

/-- The homogenization of a polyhedron is a polyhedral cone -/
lemma PointedCone.homogenize_is_h_polyhedral
  (p : W →ₗ[R] V →ₗ[R] R) (S : ConvexSet R A) (hS : IsHPolyhedron R S.carrier) :
    PointedCone.IsHPolyhedral p (homogenize V S) := by

  sorry

/-- The dehomogenization of a polyhedral cone is a polyhedron -/
lemma ConvexSet.dehomogenize_is_h_polyhedron
  (p : W →ₗ[R] V →ₗ[R] R) (C : PointedCone R V) (hC : IsHPolyhedral p C) :
    IsHPolyhedron R (PointedCone.dehomogenize A C : Set A) := by
  sorry

-- theorem IsHPolyhedron.homogenize_polyhedral_iff {S : ConvexSet R A} (p : W →ₗ[R] V →ₗ[R] R) :
--     IsHPolyhedron R S.carrier ↔ (homogenize V S).IsHPolyhedral := by
--   exact ⟨by simp [ConvexSet.dehomogenize_is_h_polyhedron], PointedCone.homogenize_is_h_polyhedral p S⟩

-- `H = (C + S) +ᵥ P` should become the definition of `IsVPolyhedron`
-- TODO: ConvexSet should have a coercion to Set


/- Minkowski-Weyl for polyhedral cones -/
variable {p : W →ₗ[R] V →ₗ[R] R} [Fact p.SeparatingRight]

-- lemma isVPolyhedral_of_isHPolyhedral {C : PointedCone R V} (hC : IsHPolyhedral p C) :
--     IsPolyhedral C := by
--   obtain ⟨gen, ⟨S, ⟨h_DualFG, hInter⟩⟩⟩ := hC

--   have h := h_DualFG.fg
--   unfold IsPolyhedral

--   use PointedCone.dual p C.carrier
--   constructor
--   · sorry
--   · use S
--     sorry

lemma isHPolyhedral_of_v_polyhedral {C : PointedCone R V} (hC : IsPolyhedral C) :
    IsHPolyhedral p C := by
  obtain ⟨gen, h_gen⟩ := hC
  sorry

/- Minkowski-Weyl for polyhedra -/

-- def IsHPolyhedron.vertices {P : Set A} (hP : IsHPolyhedron R P) : Finset { v ∈ Set A | IsFace 0 hP v}

-- Could be for `ConvexSet` (to avoid polluting the `Set` namespace)
-- This definiton assigns ⊤ as the recession cone of ∅
def IsHPolyhedron.recess (P : Set A) : PointedCone R V where
  carrier := { v : V | ∀x ∈ P, ∀a : R, a•v +ᵥ x ∈ P }
  add_mem' := by
    -- TODO: golf
    intro a b ha hb
    simp only [mem_ofPred_eq, smul_add] at ha hb ⊢
    intro x hx c
    have hb' := hb x hx c
    have ha' := ha (c•b +ᵥ x) hb' c
    rw [add_vadd]
    exact ha'
  zero_mem' := by simp
  smul_mem' := by
    -- TODO: golf
    intro ⟨c, hc⟩ x h
    simp only [mem_ofPred_eq, Nonneg.mk_smul] at ⊢ h
    intro y hy a
    rw [smul_smul]
    exact h y hy (a * c)


#click_suggestions
lemma IsHPolyhedron.recess_isHPolyhedral {P : Set A} (hP : IsHPolyhedron R P) :
    IsHPolyhedral p (IsHPolyhedron.recess P) := by
  classical
  obtain ⟨H₁, ⟨S₁, rfl⟩⟩ := hP
  unfold IsHPolyhedral recess
  let P := (⋂ h ∈ H₁, ⇑h ⁻¹' Ici 0) ∩ ↑S₁
  let C := H₁.image (·.linear)
  -- let C' := PointedCone.hull (C.preimage p (p.injective))
  simp
  have S := S₁.direction
  use PointedCone.dual .id C
  constructor
  · unfold PointedCone.DualFG
    use C
    sorry
  · use S
    ext
    simp
    sorry

/--
Every *H-polyhedron* can be decomposed as the Minkowski sum of
a *V-polytope*, a *finitely generated cone*, and a *submodule*.
`H → V` direction of the *Minkowski-Weyl* theorem.

As in the definition of *H-polyhedron*, we allow this *submodule*
to be neither finitely nor co-finitely generated, which is only
relevant in infinite dimension.
-/
lemma isVPolyhedron_of_isHPolyhedron (H : Set A) (hH : IsHPolyhedron R H) :
    ∃P : Set A, ∃C : PointedCone R V, ∃S : Submodule R V,
      (IsPolytope R P) ∧ C.IsHPolyhedral p ∧ H = ((C : Set V) + S) +ᵥ P := by
  obtain ⟨gen, h_gen⟩ := hH
  obtain ⟨S, hS⟩ := h_gen
  sorry

/-
`V → H` direction of the *Minkowski-Weyl* theorem.
For every finite *V-polytope* + *rays* + *submodule*,
there exists a finite set of inequalities that describe it.
-/
lemma isHPolyhedron_of_isVPolyhedron
  {P : Set A} (hP : IsPolytope R P) {C : PointedCone R V} (hC : C.FG) (S : Submodule R V) :
    IsHPolyhedron R (((C : Set V) + S) +ᵥ P) := by
  obtain ⟨verts, h_hull⟩ := hP
  obtain ⟨C_gen, hC_gen⟩ := hC
  sorry

end Field
end Homogenization
