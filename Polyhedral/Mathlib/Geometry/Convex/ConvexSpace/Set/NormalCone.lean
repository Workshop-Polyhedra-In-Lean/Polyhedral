/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.TangentCone

/-! # The normal cone of a face of a convex set

The normal cone of a face `F` of a convex set `K` is the dual of the tangent cone `K.tangentCone
F`, paired against the negated evaluation pairing so that membership matches the classical
convention "attains its *maximum* over `K` on `F`" (the plain, unnegated dual of a tangent cone
would instead pick out forms *minimized* on `F`, matching `IsExposedFaceOf`'s convention).

`mem_normalCone_iff` is the main fact: `φ ∈ normalCone K F` iff `φ (y -ᵥ x) ≤ 0` for every `x ∈ F`
and `y ∈ K` — i.e. for each `x ∈ F`, `x` maximizes the affine functional `y ↦ φ (y -ᵥ x)` over
`K`, which vanishes at `x` itself. -/

noncomputable section

namespace Convexity

namespace ConvexSet

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P : Type*} [AddTorsor M P]

local instance instConvexSpaceOfAddTorsor : ConvexSpace R P := AddTorsor.toConvexSpace

variable [ConvexSpace R M] [IsModuleConvexSpace R M]

variable {K F : ConvexSet R P}

/-- **The normal cone of a face `F` of `K`**: linear forms that attain their maximum over `K`
everywhere on `F`. Defined as the dual of the tangent cone `K.tangentCone F`, w.r.t. the negated
evaluation pairing (so that `φ` pairs nonnegatively with every tangent direction `y -ᵥ x`,
`y ∈ K`, `x ∈ F`, iff `φ` does not *increase* moving from `x` into `K`, i.e. `φ` is maximized at
`x`). -/
def normalCone (K F : ConvexSet R P) : PointedCone R (Module.Dual R M) :=
  PointedCone.dual (p := -(Module.Dual.eval R M)) (K.tangentCone F : Set M)

/-- **A linear form is maximized over `K` on `F` iff it lies in the normal cone of `F`.** Directly
from the definitions: `φ ∈ normalCone K F` unfolds (via `PointedCone.mem_dual`) to `φ` pairing
nonnegatively, against the *negated* evaluation, with every generator `y -ᵥ x` of `K.tangentCone
F` — i.e. `φ (y -ᵥ x) ≤ 0` for every `y ∈ K`, `x ∈ F`. The reverse direction extends this from
generators to the whole tangent cone using `mem_tangentCone_iff` (every element is a nonnegative
scalar multiple of a single generator, `PointedCone.hull` needing nothing more since the
generating set is already convex, `mem_tangentCone_iff`). -/
theorem mem_normalCone_iff (hFK : F ≤ K) (hFne : (F : Set P).Nonempty) {φ : Module.Dual R M} :
    φ ∈ normalCone K F ↔ ∀ x ∈ F, ∀ y ∈ K, φ (y -ᵥ x) ≤ 0 := by
  simp only [normalCone, PointedCone.mem_dual]
  constructor
  · intro h x hx y hy
    have hv : y -ᵥ x ∈ K.tangentCone F := PointedCone.subset_hull ⟨y, hy, x, hx, rfl⟩
    simpa using h hv
  · intro h v hv
    obtain ⟨r, hr, y, hy, x, hx, rfl⟩ := (mem_tangentCone_iff K F hFK hFne v).mp hv
    have hφ := h x hx y hy
    simp only [LinearMap.neg_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      Module.Dual.eval_apply, mul_neg]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hr hφ)

/-- **A linear form fails to be maximized over `K` on `F` iff some tangent-cone generator is an
ascent direction.** Immediate negation of `mem_normalCone_iff`: `φ` is *not* maximized on `F`
(`φ ∉ normalCone K F`) iff some generator `y -ᵥ x` of `K.tangentCone F` (`y ∈ K`, `x ∈ F`) has
`φ (y -ᵥ x) > 0`, i.e. moving from `x` towards `y` strictly increases `φ`. -/
theorem not_mem_normalCone_iff (hFK : F ≤ K) (hFne : (F : Set P).Nonempty) {φ : Module.Dual R M} :
    φ ∉ normalCone K F ↔ ∃ x ∈ F, ∃ y ∈ K, 0 < φ (y -ᵥ x) := by
  rw [mem_normalCone_iff hFK hFne]
  push Not
  rfl

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- **Cone-level reformulation of `mem_normalCone_iff`.** Unlike `mem_normalCone_iff`, this needs
no hypotheses on `F`: it is immediate from the definition of `normalCone` as a dual cone
(`PointedCone.mem_dual`) that `φ ∈ normalCone K F` iff `φ` pairs nonpositively with *every*
element of the tangent cone `K.tangentCone F`, not just its raw generators `y -ᵥ x`. -/
theorem mem_normalCone_iff_forall_mem_tangentCone {φ : Module.Dual R M} :
    φ ∈ normalCone K F ↔ ∀ v ∈ K.tangentCone F, φ v ≤ 0 := by
  simp only [normalCone, PointedCone.mem_dual, LinearMap.neg_apply, Left.nonneg_neg_iff,
    Module.Dual.eval_apply]
  rfl

omit [ConvexSpace R M] [IsModuleConvexSpace R M] in
/-- **Cone-level reformulation of `not_mem_normalCone_iff`.** -/
theorem not_mem_normalCone_iff_exists_mem_tangentCone {φ : Module.Dual R M} :
    φ ∉ normalCone K F ↔ ∃ v ∈ K.tangentCone F, 0 < φ v := by
  rw [mem_normalCone_iff_forall_mem_tangentCone]
  push Not
  rfl

end Field

end ConvexSet

end Convexity
