/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

/-! This file proves results about affine spans. -/

namespace Affine

section Ring

variable (R : Type*) [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

lemma spanPoints_empty : spanPoints R (∅ : Set A) = ∅ := by simp [spanPoints]

@[gcongr]
lemma spanPoints_mono (F G : Set A) (hFG : G < F) : spanPoints R G ⊆ spanPoints R F := by
    exact fun p ⟨p₁, hp₁, v, hv, hp⟩ =>
      ⟨p₁, hFG.le hp₁, v, Submodule.span_mono (Set.vsub_subset_vsub hFG.le hFG.le) hv, hp⟩

noncomputable def rank (s : Set A) := Module.rank R (affineSpan R s).direction

noncomputable def finrank (s : Set A) := Module.finrank R (affineSpan R s).direction

lemma finrank_empty [Nontrivial R] : finrank R (A := A) ∅ = 0 := by
  rw [finrank, AffineSubspace.span_empty, AffineSubspace.direction_bot, finrank_bot R V]

/-
lemma finrank_empty : finrank R (A := A) ∅ = 0 := by
  rw [finrank, AffineSubspace.span_empty, AffineSubspace.direction_bot]
  rcases subsingleton_or_nontrivial R with hTrivial | hNontrivial
  · simp -- False
    sorry
  · exact finrank_bot R V
-/

end Ring

end Affine
