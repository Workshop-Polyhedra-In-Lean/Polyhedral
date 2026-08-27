/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.TangentCone
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice

/-! This file relates the tangent cone `Affine.tangentCone` (see
`Polyhedral.Mathlib.LinearAlgebra.AffineSpace.TangentCone`) to the convexity of the underlying
set, via the elementary (topology-free) notion of an extreme point: the tangent cone of `s` at
`x` is salient (pointed) iff `x` is an extreme point of `s`. Only the direction needed downstream
(extreme point implies salient) is proved. -/

namespace Affine

section TangentCone

variable (k : Type*) {V P : Type*} [AddCommGroup V] [AddTorsor V P]
variable (s : Set P)
variable (x : s)

variable [Field k] [Module k V] [LinearOrder k] [IsStrictOrderedRing k]

/-- `x` is an extreme point of `s` if it is never the interior point of a chord of `s`, i.e.
`x` is not a proper convex combination of two points of `s`, unless those points are `x` itself.
This is the elementary (topology-free) notion of a vertex. -/
def IsExtremePoint (x : P) : Prop :=
  ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → ∀ ⦃c : k⦄, 0 < c → c < 1 → AffineMap.lineMap y z c = x → y = x

attribute [local instance] AddTorsor.toConvexSpace
attribute [local instance] Convexity.ConvexSpace.ofModule
local instance : Convexity.IsModuleConvexSpace k V := .ofModule

open Convexity Pointwise in
/-- If `x` is an extreme point of `s`, the tangent cone at `x` is salient (pointed). The converse
also holds but is not needed here.

This is an algebraic, closure-free notion, and it disagrees with the topological picture one
might expect from a smooth convex body because we don't take limits of chordal directions.

AI proof

-/
theorem Salient.tangentCone_of_isExtremePoint (hsc : IsConvexSet k s)
    (hx : IsExtremePoint k s (x : P)) : (tangentCone k s x).Salient := by
  have hne : ((· -ᵥ (x : P)) '' s).Nonempty := ⟨_, Set.mem_image_of_mem _ x.2⟩
  have hconv : IsConvexSet k ((· -ᵥ (x : P)) '' s) := hsc.image (isAffineMap_vsub_right k (x : P))
  intro a ha b hb hab
  rw [tangentCone_eq_hull_image, ← SetLike.mem_coe, PointedCone.hull_eq_smul hne hconv,
    Set.mem_smul] at ha hb
  obtain ⟨c, hc, u, hu, rfl⟩ := ha
  obtain ⟨d, hd, v, hv, rfl⟩ := hb
  obtain ⟨y, hy, rfl⟩ := hu
  obtain ⟨z, hz, rfl⟩ := hv
  rw [Set.mem_Ici] at hc hd
  rcases hc.eq_or_lt with hc0 | hc0
  · simp [← hc0]
  rcases hd.eq_or_lt with hd0 | hd0
  · have hyx0 : y -ᵥ (x : P) = 0 := by
      have hzero : c • (y -ᵥ (x : P)) = 0 := by simpa [← hd0] using hab
      exact (smul_eq_zero.mp hzero).resolve_left hc0.ne'
    simp [hyx0]
  · set t : k := d / (c + d) with ht_def
    have hcd : 0 < c + d := add_pos hc0 hd0
    have ht0 : 0 < t := div_pos hd0 hcd
    have ht1 : t < 1 := (div_lt_one hcd).mpr (lt_add_of_pos_left d hc0)
    have hkey : AffineMap.lineMap y z t = (x : P) := by
      have hrw : AffineMap.lineMap y z t -ᵥ (x : P)
          = (1 - t) • (y -ᵥ (x : P)) + t • (z -ᵥ (x : P)) := by
        simp only [AffineMap.lineMap_apply, vadd_vsub_assoc]
        rw [show z -ᵥ y = (z -ᵥ (x : P)) - (y -ᵥ (x : P)) from
          (vsub_sub_vsub_cancel_right z y (x : P)).symm, smul_sub]
        module
      have hdt : (c + d) * t = d := by rw [ht_def]; field_simp
      have hct : (c + d) * (1 - t) = c := by rw [mul_sub, hdt]; ring
      have hcomb : c • (y -ᵥ (x : P)) + d • (z -ᵥ (x : P))
          = (c + d) • ((1 - t) • (y -ᵥ (x : P)) + t • (z -ᵥ (x : P))) := by
        rw [smul_add, smul_smul, smul_smul, hct, hdt]
      rw [← hrw] at hcomb
      have hz0 : (c + d) • (AffineMap.lineMap y z t -ᵥ (x : P)) = 0 := hcomb ▸ hab
      have := (smul_eq_zero.mp hz0).resolve_left hcd.ne'
      rwa [vsub_eq_zero_iff_eq] at this
    have hyx := hx hy hz ht0 ht1 hkey
    simp [hyx]

open Convexity in
/-- An extreme point (in the elementary, chord-based sense of `IsExtremePoint`) is a genuine
`ConvexSet.IsFaceOf` face of `s`, i.e. an extreme point in the classical sense.
-/
theorem ConvexSet.isFaceOf_of_isExtremePoint (hsc : IsConvexSet k s)
    (hx : IsExtremePoint k s (x : P)) :
    (({(x : P)} : ConvexSet k P)).IsFaceOf ⟨s, hsc⟩ where
  le := by rintro _ rfl; exact x.2
  left_mem_of_mem_openSegment := by
    intro a ha b hb w hw hwseg
    have hw' : w = (x : P) := hw
    subst hw'
    rw [Convexity.openSegment_symm] at hwseg
    obtain ⟨p, q, hp, hq, hpq, hcomb⟩ := hwseg
    rw [AddTorsor.convexCombPair_eq_lineMap] at hcomb
    have ha' : a = (x : P) := hx ha hb hp (by linarith) hcomb
    exact ha'

end TangentCone

end Affine
