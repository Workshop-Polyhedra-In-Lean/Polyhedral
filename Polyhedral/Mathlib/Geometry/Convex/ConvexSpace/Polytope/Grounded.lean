/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice

namespace Convexity

variable {R X Y V A : Type*}

open ConvexSpace

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]
variable (M : Set X)

variable (R) in
/-- A set `s` is a *grounded polytope* in `M` if there exists a finite set `t` contained in `M`
such that `s` is the convex hull of `t`. If `M` is a lattice, this is usually called a
*lattice polytope*. -/
def IsGroundedPolytope (s : Set X) : Prop :=
  ∃ t : Finset X, (t : Set X) ⊆ M ∧ s = convexHull R t

namespace IsGroundedPolytope

lemma isPolytope (s : Set X)
    (h : IsGroundedPolytope R M s) : IsPolytope R s := by
  obtain ⟨t, _, hs⟩ := h
  exact ⟨t, hs⟩

protected lemma empty : IsGroundedPolytope R M ∅ := ⟨∅, by simp, by simp⟩

protected lemma singleton (x : X) (h : x ∈ M) : IsGroundedPolytope R M {x} :=
  ⟨{x}, by simpa, by simp⟩

variable (R) in
lemma convexHull_finite {v : Set X} (hv : v.Finite) (hvM : v ⊆ M) :
    IsGroundedPolytope R M (convexHull R v) :=
  ⟨hv.toFinset, by simpa, by simp⟩

lemma convexHull_union {P Q : Set X} (hP : IsGroundedPolytope R M P)
    (hQ : IsGroundedPolytope R M Q) :
    IsGroundedPolytope R M (convexHull R (P ∪ Q)) := by classical
  obtain ⟨t₁, ht₁, rfl⟩ := hP
  obtain ⟨t₂, ht₂, rfl⟩ := hQ
  exact ⟨t₁ ∪ t₂, by simp [ht₁, ht₂],
    by simp [convexHull_union_convexHull, convexHull_convexHull_union]⟩

lemma mono_subset {P : Set X} {M N : Set X} (hP : IsGroundedPolytope R M P) (hMN : M ⊆ N) :
    IsGroundedPolytope R N P := by
  obtain ⟨t, h₁, h₂⟩ := hP
  exact ⟨t, h₁.trans hMN, h₂⟩

lemma inf_groundSet_nonempty_of_nonempty {P : Set X} (hP : IsGroundedPolytope R M P)
    (h : P.Nonempty) : (P ⊓ M).Nonempty := by
  obtain ⟨t, htM, hPt⟩ := hP
  apply Set.Nonempty.mono (by simpa using ⟨hPt ▸ subset_convexHull_self, htM⟩)
  by_contra! H
  simp only [H, convexHull_empty] at hPt
  exact Set.not_nonempty_empty (hPt ▸ h)

lemma inf_groundSet_nonempty_iff {P : Set X} (hP : IsGroundedPolytope R M P) :
    (P ⊓ M).Nonempty ↔ P.Nonempty :=
  ⟨Set.Nonempty.left, hP.inf_groundSet_nonempty_of_nonempty M⟩

end IsGroundedPolytope

open IsGroundedPolytope

end Convexity
