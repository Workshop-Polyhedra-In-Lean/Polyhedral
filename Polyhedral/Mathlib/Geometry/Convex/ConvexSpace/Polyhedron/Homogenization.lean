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

section Homogenization

open Convexity Pointwise Set PointedCone Submodule
open Convexity.ConvexSet

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
-- variable {W : Type*} [AddCommGroup W] [Module R W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R V]

variable [hom : Affine.IsHomogenization R A V]

-- lemma IsHPolyhedra.homogenize_dualfg (C : ConvexSet R A) : (IsHPolyhedron R C.carrier) ↔ (homogenize V C).DualFG p := by
--   sorry

variable (R) in
def homogenize (P : Set A) : PointedCone R V :=
    PointedCone.hull R (hom.ofPoint '' P)

variable (R) in
def ConvexSet.homogenize (P : ConvexSet R A) : ConvexCone R V :=
    ↑(PointedCone.hull R (hom.ofPoint '' P))

omit [IsModuleConvexSpace R V] in
@[simp]
lemma ConvexSet.homogenize_coe (P : ConvexSet R A) :
    _root_.homogenize R (P : Set A) = homogenize R P := by rfl

variable (R) in
def dehomogenize (P : Submodule R V) : Set A := hom.ofPoint ⁻¹' P

-- variable (R) in
-- def ConvexCone.dehomogenize (P : ConvexCone R V) : ConvexSet R A :=
--     ⟨hom.ofPoint ⁻¹' P, by
--       obtain ⟨sP, smul_mem, add_mem⟩ := P
--       simp only [coe_mk]
--       apply IsConvexSet.preimage hom.ofPoint.isAffineMap
--       apply IsConvexSet.of_convexCombPair_mem
--       intro a b ha hb hab x hx y hy
--       simp
--       apply add_mem <;> apply smul_mem; sorry
--       -- We have the 0 problem here
--     ⟩

-- TODO: Why is ConvexSet not SetLike, nor can be coerced to Set
-- @[simp]
-- lemma ConvexCone.dehomogenize_coe (P : ConvexCone R V) : _root_.dehomogenize R P.toPointedCone = (dehomogenize R P).carrier := by rfl

-- lemma IsHPolyhedralCone.homogenize_hpolyhedron (P : Set A) (hP : IsHPolyhedron R P) :
--     IsHCone R (homogenize R P).carrier := by
--   obtain ⟨H, h_gen⟩ := hP
--   have l := hom.ofPoint.linear.leftInverse
--   have Hₗ := H.map (fun (m : A →ᵃ[R] R) ↦ ((m.linear <| hom.ofVector ⁻¹ ·) : V →ₗ[R] R)) H
--   sorry

end Field
end Homogenization
