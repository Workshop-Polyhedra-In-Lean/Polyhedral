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
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {A : Type*} [AddTorsor V A]
-- variable {W : Type*} [AddCommGroup W] [Module R W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R V]

variable [hom : Affine.IsHomogenization R A V]


-- TODO: We might want to define `homogenize` on non-convex Sets
-- TODO: `ConvexSet` should be `SetLike` to avoid manual coercion

/-- The homogenization of a polyhedron is a polyhedral cone -/
lemma PointedCone.homogenize_is_h_polyhedral
  (S : ConvexSet R A) (hS : IsHPolyhedron R S.carrier) (p : W →ₗ[R] V →ₗ[R] R) :
    PointedCone.IsHPolyhedral p (homogenize V S) := by
  sorry

/-- The dehomogenization of a polyhedral cone is a polyhedron -/
lemma ConvexSet.dehomogenize_is_h_polyhedron
  (C : PointedCone R V) (p : W →ₗ[R] V →ₗ[R] R) (hC : IsHPolyhedral p C) :
    IsHPolyhedron R (PointedCone.dehomogenize A C).carrier := by
  sorry

-- `H = (C + S) +ᵥ P` should become the definition of `IsVPolyhedron`
-- TODO: ConvexSet should have a coercion to Set

/--
Every *H-polyhedron* can be decomposed as the Minkowski sum of
a *V-polytope*, a *finitely generated cone*, and a *submodule*.
`H → V` direction of the *Minkowski-Weyl* theorem.

As in the definition of *H-polyhedron*, we allow this *submodule*
to be neither finitely nor co-finitely generated, which is only
relevant in infinite dimension.
-/
lemma v_polyhedral_of_h_polyhedral (H : Set A) (hH : IsHPolyhedron R H) :
    ∃P : Set A, ∃C : PointedCone R V, ∃S : Submodule R V,
      (IsPolytope R P) ∧ C.FG ∧ H = ((C : Set V) + S) +ᵥ P := by
  obtain ⟨gen, h_gen⟩ := hH
  obtain ⟨S, hS⟩ := h_gen
  sorry

/-
`V → H` direction of the *Minkowski-Weyl* theorem.
For every finite *V-polytope* + *rays* + *submodule*,
there exists a finite set of inequalities that describe it.
-/
lemma h_polyhedral_of_v_polyhedral
  {P : Set A} (hP : IsPolytope R P) {C : PointedCone R V} (hC : C.FG) (S : Submodule R V) :
    IsHPolyhedron R (((C : Set V) + S) +ᵥ P) := by
  obtain ⟨verts, h_hull⟩ := hP
  obtain ⟨C_gen, hC_gen⟩ := hC
  sorry

end Field
end Homogenization
