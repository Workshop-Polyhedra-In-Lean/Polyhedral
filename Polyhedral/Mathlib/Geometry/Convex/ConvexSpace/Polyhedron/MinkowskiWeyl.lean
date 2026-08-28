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
open Convex

-- def IsHPolyhedron.vertices {P : Set A} (hP : IsHPolyhedron R P) : Finset { v ∈ Set A | IsFace 0 hP v}

-- Could be for `ConvexSet` (to avoid polluting the `Set` namespace)
-- This definiton assigns ⊤ as the recession cone of ∅
-- The ∀ could be an ∃ (we could prove it's equivalent for polytopes)
-- For `ConvexSet`, the ∀a is not necessary
#click_suggestions
variable (R) in
def Convex.Set.recess (P : Set A) : PointedCone R V where
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

#click_suggestions
lemma IsHPolyhedron.recess_isHPolyhedral {P : Set A} (hP : IsHPolyhedron R P) :
    IsHPolyhedral p (P.recess R) := by
  classical
  -- by_cases h : ∅ = P
  -- · simp only [Convex.Set.recess, h.symm, mem_empty_iff_false, imp_false, not_le,
  --     IsEmpty.forall_iff, implies_true, ofPred_true]
  --   exact IsHPolyhedral.top p
  -- -- We need to use a point in `P` for the proof below
  -- obtain ⟨x, hx : x ∈ P⟩ := Set.nonempty_iff_empty_ne.mpr h

  obtain ⟨H₁, ⟨S₁, rfl⟩⟩ := hP

  -- unfold IsHPolyhedral recess
  -- let P := (⋂ h ∈ H₁, ⇑h ⁻¹' Ici 0) ∩ ↑S₁

  let C := H₁.image (·.linear)
  let C_gen := C.preimage p (injOn_of_injective hp)

  simp only [IsHPolyhedral, Convex.Set.recess, mem_inter_iff, mem_iInter, mem_preimage, mem_Ici,
    SetLike.mem_coe, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, and_imp,
    exists_and_left]
  use (PointedCone.dual p C_gen)
  constructor
  · use C_gen
  · use S₁.direction
    ext v
    simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, mem_ofPred_eq,
      Finset.coe_preimage, mem_inf, PointedCone.mem_dual, mem_preimage,
      SetLike.mem_coe, restrictScalars_mem, C_gen]

    constructor
    · intro h
      have h' := h x (by
          intro i hi

          simp [hx]
        )
      constructor
      · intro w hw
        -- have hf : ∃f ∈ H₁, p w = f.linear := match (hC' (p w)).mp hw with
        --   | ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ => ⟨f, ⟨hf, h_eq⟩⟩
        -- have h_zero : ∃a ∈ A, (p w) a = 0,
        -- obtain ⟨f, ⟨hf, ⟨_, h_eq⟩⟩⟩ := (hC' (p w)).mp hw
        -- let ker := f ⁻¹' {0}
        -- let k := f.linear.zero
        -- have i := p w


        sorry
      · sorry
    · intro ⟨hv, hvs⟩ y hyP hyS a
      constructor
      · intro i hi
        have hiP := hyP i hi
        have hc := (hC i).mp hi
        sorry
      · have h_av : a • v ∈ S₁.direction := by exact Submodule.smul_mem S₁.direction a hvs
        exact (AffineSubspace.vadd_mem_iff_mem_of_mem_direction h_av).mpr hyS

-- TODO: It would be nice to not need the explicit coercion Cone → Set
/--
Every *H-polyhedron* can be decomposed as the Minkowski sum of
a *V-polytope*, a *finitely generated cone*, and a *submodule*.
`H → V` direction of the *Minkowski-Weyl* theorem.

As in the definition of *H-polyhedron*, we allow this *submodule*
to be neither finitely nor co-finitely generated, which is only
relevant in infinite dimension.
-/
lemma isVPolyhedron_of_isHPolyhedron (H : Set A) (hH : IsHPolyhedron R H) :
    ∃P : Set A, (IsPolytope R P) ∧ H = (H.recess R : Set V) +ᵥ P := by
  obtain ⟨gen, h_gen⟩ := hH
  obtain ⟨S, hS⟩ := h_gen
  sorry

/-
`V → H` direction of the *Minkowski-Weyl* theorem.
For every finite *V-polytope* + *rays* + *submodule*,
there exists a finite set of inequalities that describe it.
-/
lemma isHPolyhedron_of_isVPolyhedron
  {P : Set A} (hP : IsPolytope R P) :
    IsHPolyhedron R ((P.recess R : Set V) +ᵥ P) := by
  obtain ⟨verts, h_hull⟩ := hP

  sorry

end Field
end Homogenization
