/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Geometry.Convex.Set
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Geometry.Convex.ConvexSpace.Module

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Prod

/-!
# Affine spaces are convex spaces

This file shows that every affine space is a convex space.

-/

namespace Convexity

variable {R V P I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]

-- for consistent naming
@[implicit_reducible]
alias ConvexSpace.ofAddTorsor := AddTorsor.toConvexSpace

variable (R V P) [ConvexSpace R P] in
/-- Typeclass for a convex space structure on an affine space to be given by affine
combinations. -/
class IsAffineConvexSpace : Prop where
  sConvexComb_eq_convexComb (w : StdSimplex R P) :
    w.sConvexComb = AddTorsor.convexCombination w

export IsAffineConvexSpace (sConvexComb_eq_convexComb)
attribute [simp] sConvexComb_eq_convexComb

/-- `iConvexComb` in an affine space can be expressed as an affine combination. -/
lemma iConvexComb_eq_affineCombination [ConvexSpace R P] [IsAffineConvexSpace R V P]
    (w : StdSimplex R I) (f : I → P) :
    w.iConvexComb f = w.weights.support.affineCombination R f w.weights := by
  rw [iConvexComb, sConvexComb_eq_convexComb (V := V)]
  exact AddTorsor.iConvexComb_eq_affineCombination w f

section IsAffineConvexSpace

variable [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [ConvexSpace R P] [IsAffineConvexSpace R V P]

@[simp]
lemma iConvexComb_vadd (w : StdSimplex R I) (f : I → V) (g : I → P) :
    w.iConvexComb (f +ᵥ g) = w.iConvexComb f +ᵥ w.iConvexComb g := by
  rw [eq_vadd_iff_vsub_eq, iConvexComb_eq_affineCombination w (f +ᵥ g),
    iConvexComb_eq_affineCombination w g,
    ← Finset.sum_smul_vsub_eq_affineCombination_vsub]
  simp [Finsupp.sum]

@[fun_prop]
lemma isAffineMap_vadd : IsAffineMap R fun x : V × P ↦ x.1 +ᵥ x.2 where
  map_sConvexComb w := by
    change w.iConvexComb Prod.fst +ᵥ w.iConvexComb Prod.snd =
      w.iConvexComb fun x ↦ x.1 +ᵥ x.2
    exact (iConvexComb_vadd w Prod.fst Prod.snd).symm

@[to_fun (attr := fun_prop)]
lemma IsAffineMap.vadd {X : Type*} [ConvexSpace R X] {f : X → V} {g : X → P}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (f +ᵥ g) := by
  change IsAffineMap R fun x ↦ f x +ᵥ g x
  simpa only [Function.comp_def] using isAffineMap_vadd.comp (hf.prod_mk hg)

end IsAffineConvexSpace

attribute [local instance] ConvexSpace.ofAddTorsor in
instance IsAffineConvexSpace.ofAddTorsor : IsAffineConvexSpace R V P where
  sConvexComb_eq_convexComb _ := rfl

instance [ConvexSpace R V] [IsModuleConvexSpace R V] : IsAffineConvexSpace R V V where
  sConvexComb_eq_convexComb w := by
    rw [IsModuleConvexSpace.sConvexComb_eq_sum, AddTorsor.convexCombination,
      Finset.affineCombination_eq_linear_combination _ _ _ w.total]
    rfl

end Convexity
