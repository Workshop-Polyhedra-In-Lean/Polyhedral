/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization
import Mathlib.Order.SuccPred.Basic

/-! This file proves results about faces of polytopes by transporting results from FG
cones along a homogenization. -/

variable {R V A : Type*}

open Convexity ConvexSet Affine

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

attribute [local instance] AddTorsor.toConvexSpace

variable {C F : ConvexSet R A}

/-- Faces of polytopes are polytopes. -/
theorem IsPolytope.face_isPolytope (hC : IsPolytope R (C : Set A)) (hF : IsFaceOf F C) :
    IsPolytope R (F : Set A) := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  have homC := IsPolytope.homogenize_fg (W := W) hC
  have homF := IsHomogenization.homogenize_isFaceOf (W := W) hF
  have := PointedCone.IsFaceOf.fg homC homF
  convert FG.dehomogenize_isPolytope this (fun _ a b ↦ weight_pos_of_mem_homogenize a b)
  simp [dehomogenize_homogenize]

instance {P : Polytope R A} : CoeOut (Face (P : ConvexSet R A)) (Polytope R A) where
  coe F := ⟨_, IsPolytope.face_isPolytope P.isPolytope F.isFaceOf⟩

-- TODO Where should these live? What should its form be?
@[simp]
lemma pred_zero_eq_bot : Order.pred (0 : WithBot ℕ) = ⊥ := rfl

@[simp]
lemma pred_one_eq_zero : Order.pred (1 : WithBot ℕ) = 0 := rfl

lemma _root_.WithBot.natCast_orderSucc (a : ℕ) :
    Nat.cast (Order.succ a) = Order.succ (a : WithBot ℕ) :=
  WithBot.orderSucc_coe _

@[simp]
lemma _root_.WithBot.orderPred_natCast_add_one (a : ℕ) :
    Order.pred ((a : WithBot ℕ) + 1) = a := by
  rw [← Nat.cast_succ, ← Nat.succ_eq_succ, _root_.WithBot.natCast_orderSucc]
  simp

@[simp]
lemma _root_.WithBot.orderPred_natCast_eq_pred_of_zero_le {a : ℕ} (ha : 0 < a) :
    Order.pred (a : WithBot ℕ) = a.pred := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one.mpr ha
  simp

/-- The face lattice of a polytope as a graded order with grading given by the dimensions of
homogenization cones. -/
noncomputable instance Polytope.faceHomogenizationGradeOrder (P : Polytope R A) :
    GradeOrder (WithBot ℕ) (Face (P : ConvexSet R A)) := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  have : PointedCone.FG (homogenize W (P : ConvexSet R A)) :=
    IsPolytope.homogenize_fg (W := W) P.isPolytope
  let := PointedCone.FG.gradeOrder_finrank this
  have := GradeOrder.liftRight (𝕆 := ℕ) (β := (homogenize W (P : ConvexSet R A)).Face) _
    IsHomogenization.Face.homogenizeIso.strictMono (fun x y ↦ (apply_covBy_apply_iff _).mpr)
  refine GradeOrder.liftLeft (fun (x : ℕ) ↦ Order.pred (x : WithBot ℕ)) ?_ ?_
  · exact fun x y hxy ↦ Order.pred_lt_pred_of_not_isMin (by simpa) (by simp)
  · simp only [Nat.covBy_iff_add_one_eq, forall_eq']
    exact fun a ↦ Order.succ_eq_iff_covBy.mp (by simp)

end Field
