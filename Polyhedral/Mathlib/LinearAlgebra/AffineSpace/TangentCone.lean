/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

-- TODO: #min_imports later
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Dimension
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice

namespace Affine

section VsubAffineMap

/-! Subtracting a fixed basepoint from every point of an affine space is an affine map onto the
underlying module of translations. This is the elementary fact underlying
`tangentCone_eq_hull_image` and the finite generation of tangent cones of polytopes. -/

variable {V P : Type*} [AddCommGroup V] [AddTorsor V P]
variable (k : Type*) [Ring k] [PartialOrder k] [IsStrictOrderedRing k] [Module k V]

attribute [local instance] AddTorsor.toConvexSpace
attribute [local instance] Convexity.ConvexSpace.ofModule
local instance : Convexity.IsModuleConvexSpace k V := .ofModule

open Convexity in
/-- Subtracting a fixed point `x` is an affine map from an affine space `P` to its module of
translations `V`. -/
theorem isAffineMap_vsub_right (x : P) :
    Convexity.IsAffineMap k (· -ᵥ x : P → V) where
  map_sConvexComb w := by
    classical
    have hsum : ∑ i ∈ w.weights.support, w.weights i = 1 := by
      simpa [Finsupp.sum] using w.total
    rw [AddTorsor.sConvexComb_eq_affineCombination,
      w.weights.support.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
        (⇑w.weights) id hsum x,
      vadd_vsub, Finset.weightedVSubOfPoint_apply, Convexity.sConvexComb_eq_sum]
    simp only [StdSimplex.map]
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
    rfl

end VsubAffineMap

section TangentCone

variable (k : Type*) {V P : Type*} [AddCommGroup V] [AddTorsor V P]
variable (s : Set P)
variable (x : s)

-- TODO: #min assumptions later
variable [Field k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

/-- The tangent cone of `s` at `x`.

LST comment: is the conic hull of the chordal directions emanating from x.
If s is nonconvex this is not a sensible definition.  If s is smooth, this
is only the relint.
-/
def tangentCone : PointedCone k V :=
  PointedCone.hull k {y -ᵥ (x : P) | y ∈ s}

/-- The normal cone of `s` at `x`, defined as the dual of the tangent cone. -/
def normalCone : PointedCone k (Module.Dual k V) :=
  PointedCone.dual (Module.Dual.eval k V) (tangentCone k s x : Set V)

lemma tangentCone_eq_hull_image :
    tangentCone k s x = PointedCone.hull k ((· -ᵥ (x : P)) '' s) := rfl

lemma vsub_mem_tangentCone {y : P} (hy : y ∈ s) : y -ᵥ (x : P) ∈ tangentCone k s x :=
  PointedCone.subset_hull ⟨y, hy, rfl⟩

end TangentCone

end Affine
