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
variable {V' : Type*} [AddCommGroup V'] [Module R V']
variable {W : Type*} [AddCommGroup W] [Module R W]

variable {A : Type*} [AddTorsor V A]


attribute [local instance] AddTorsor.toConvexSpace

section Homogenize

variable [IsModuleConvexSpace R W]
variable [hom : Affine.IsHomogenization R A W]

/-- The homogenization of an H-polyhedron is an H-polyhedral cone (with respect to the
standard dual pairing). -/
-- This is not true: If S is unbounded, the homogenization is not a closed set.
lemma PointedCone.homogenize_is_h_polyhedral (S : ConvexSet R A)
    (hS : IsHPolyhedron R (S : Set A)) :
    PointedCone.IsHPolyhedral .id (homogenize W S) := by
  sorry

/-- The dehomogenization of an H-polyhedral cone is an H-polyhedron. -/
lemma ConvexSet.dehomogenize_is_h_polyhedron (C : PointedCone R W)
    (hC : IsHPolyhedral .id C) :
    IsHPolyhedron R (PointedCone.dehomogenize A C : Set A) := by
  sorry

-- theorem IsHPolyhedron.homogenize_polyhedral_iff {S : ConvexSet R A} :
--     IsHPolyhedron R (S : Set A) ↔ (homogenize W S).IsHPolyhedral .id := by
--   exact ⟨PointedCone.homogenize_is_h_polyhedral S, by simp [dehomogenize_is_h_polyhedron]⟩

end Homogenize

-- `H = (C + S) +ᵥ P` should become the definition of `IsVPolyhedron`


/- Minkowski-Weyl for polyhedral cones -/
variable {p : V' →ₗ[R] V →ₗ[R] R} [Fact p.SeparatingRight]

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

#check smul_zero
variable (R) in
def Convex.Set.recessionCone (P : Set A) : PointedCone R V where
  carrier := { v : V | ∀ x ∈ P, ∀ a : R, 0 ≤ a → a • v +ᵥ x ∈ P }
  add_mem' := by
    -- TODO: golf
    intro a b ha hb
    simp only [mem_ofPred, smul_add] at ha hb ⊢
    intro x hx c hc
    have hb' := hb x hx c hc
    have ha' := ha (c•b +ᵥ x) hb' c
    rw [add_vadd]
    exact ha' hc
  zero_mem' := by
    -- rw [mem_ofPred] --, smul_zero a]
    -- rw [smul_zero]
    simp only [mem_ofPred, smul_zero, zero_vadd]
    -- tauto -- would also work
    intro x hx a ha
    exact hx
  smul_mem' := by
    -- TODO: golf
    intro ⟨c, hc⟩ x h
    simp only [mem_ofPred, Nonneg.mk_smul] at ⊢ h
    intro y hy a ha
    rw [smul_smul]
    exact h y hy (a * c) (show 0 ≤ a * c by exact Right.mul_nonneg ha hc)

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
    ∃P : Set A, (IsPolytope R P) ∧ H = (H.recessionCone R : Set V) +ᵥ P := by
  obtain ⟨gen, h_gen⟩ := hH
  obtain ⟨S, hS⟩ := h_gen
  sorry

/-
`V → H` direction of the *Minkowski-Weyl* theorem.
For every finite *V-polytope* + *rays* + *submodule*,
there exists a finite set of inequalities that describe it.
-/
lemma isHPolyhedron_of_isPolytope
  {P : Set A} (hP : IsPolytope R P) :
    IsHPolyhedron R P := by

  sorry

lemma IsHPolyhedron.vadd {P : Set V} (hP : IsHPolyhedron R P) {Q : Set A}
    (hQ : IsHPolyhedron R Q) :
    IsHPolyhedron R (P +ᵥ Q) := by
  sorry

lemma isHPolyhedron_of_isVPolyhedron {P : Set A} (hP : IsPolytope R P)
    {C : PointedCone R V} (hC : IsHPolyhedral .id C) :
    IsHPolyhedron R ((C : Set V) +ᵥ P) := by
  sorry

end Field
end Homogenization
