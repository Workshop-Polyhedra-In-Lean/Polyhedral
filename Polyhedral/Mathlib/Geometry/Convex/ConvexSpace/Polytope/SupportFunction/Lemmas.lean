/-
Copyright (c) 2026 Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor
-/
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.SupportFunction.Basic
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.Module.Pointwise
import Mathlib.Order.Bounds.Image
import Mathlib.Algebra.Order.Field.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Data.Set.Image
/-! # Basic properties of support functions (of sets)
-/

section

variable {α : Type*} [DecidableEq α] [MulZeroClass α]

#synth Mul (WithTopBot α)
#check WithTop.instMulZeroClass

-- note: the multiplication we have on WithBotTop R will have -1 * ∞ = ∞
-- (but we don`t use that because r>0 in our properties)
-- this may not be what we want (but it coincides with what we want for positive scalars)
-- pehraps assume (a ≠ 0) (ha' : a ≠ -⊤) instead?
-- (h : 0 < a)
lemma WithBotTop.mul_top {a : WithBotTop α} (ha : a ≠ 0) (ha' : a ≠ ⊥) : a * ⊤ = ⊤ := by
  rw [WithBot.mul_def]
  have : ⊤ ≠ (0 : WithBot (WithTop α)) := by
    sorry -- what's the lemma to use?
  simp [ha, this]
  --rw [WithBot.map₂_bot_right (a := a)]
  sorry --rw [WithBot.map₂_coe_coe  (a := a) (b := (⊤ : WithTop α))]
  --simp [WithBot.map₂, Option.map₂, Option.bind, Option.map]

lemma WithBotTop.mul_bot {a : WithBotTop α} (ha : a ≠ 0) (ha' : a ≠ ⊤) : a * ⊥ = ⊥ := by
  rw [WithBot.mul_def]
  have : ⊤ ≠ (0 : WithBot (WithTop α)) := by
    sorry -- what's the lemma to use?
  simp [ha]

end

section convex
-- Would be nice to have it in this more general way:
-- variable {R V : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
--   [Convexity.ConvexSpace R V]
-- Semifield
variable {R V : Type*} [Semifield R] [PartialOrder R] [IsStrictOrderedRing R] [PosMulReflectLT R]
  [Convexity.ConvexSpace R V]
  {P : Set V}

/- upperBounds(r • φ '' P) ⊆ r • upperBounds(φ '' P) is not true for a ring (we found
 a counter example for ℤ ) but we need something weaker, we just need is for the least
 upper bound-/
-- we know for sure that it is true for a semifild but not for a semiring
-- is pos. homogeneous (Judith + Valentina)
open scoped Classical Pointwise in
-- XXX: right name?
lemma supportFunctionAffine_homogeneous {r : R} (hr : 0 < r) (φ : ConvexSpace.dual R V) :
    supportFunctionAffine R P (r • φ) = r * supportFunctionAffine R P φ := by
  by_cases! hP : P.Nonempty
  · by_cases hP' : ∃ x, IsLUB (φ '' P) x
    · obtain ⟨x, hx⟩ := hP'
      have hrP : IsLUB ((r • φ) '' P) (r * x) := by
        have := IsLUB.mul_left hr.le hx
        have h : ((fun b ↦ r * b) '' φ '' P) = ((r • φ) '' P) := by
          apply Set.image_image
        rw [← h]
        exact this
      rw [supportFunctionAffine_of_nonempty_of_isLUB hP hx,
        supportFunctionAffine_of_nonempty_of_isLUB (by simp [hP]) hrP]
      simp [WithBotTop.coe]
    · have hrP : ¬∃ x, IsLUB (⇑(r • φ) '' P) x := by
        simp only [Convexity.ConvexSpace.AffineMap.smul_apply, smul_eq_mul, not_exists]
        intro y hy
        have H : IsLUB (φ '' P) (r⁻¹ • y) := sorry
        exact
      sorry
      rw [supportFunctionAffine_of_nonempty_of_not_exists_isLUB hP hrP,
         supportFunctionAffine_of_nonempty_of_not_exists_isLUB hP hP']
      simp only [WithBotTop.coe, Function.comp_apply]
      rw [WithBotTop.mul_top (by simp [hr.ne']) (by simp)]
  · rw [hP]
    simp only [supportFunctionAffine_empty, Pi.bot_apply]
    rw [WithBotTop.mul_bot _ (by simp)]
    · sorry -- missing lemma? should be easy in any case

open scoped Classical Pointwise in
lemma supportFunctionAffine_homogeneous' (hP : P.Nonempty)
    {r : R} (hr : 0 ≤ r) (φ : ConvexSpace.dual R V) :
    supportFunctionAffine R P (r • φ) = r * supportFunctionAffine R P φ := by
  sorry

end convex




section linear

variable {R V : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [Convexity.ConvexSpace R V] [Convexity.IsModuleConvexSpace R V]
-- To be able to use the lemma "positive homogeneity for IsAffineMap
-- one maybe has to change "[CommRing R]" to "[Semifield R]"

/- ## Basic properties -/

-- is positively homogeneous (i.e., behaviour under scaling φ): TODO write down

-- invariance under dilation
open scoped Pointwise Classical in
lemma supportFunction_smul
    {P : Set V} {r : R} (hr : 0 ≤ r) (hP : P.Nonempty) (φ : Module.Dual R V) :
    supportFunction R (r • P) φ = r * (supportFunction R P φ) := by
  by_cases hP' : ∃ x, IsLUB (φ '' P) x
  · obtain ⟨x, hx⟩ := hP'
    have hrP : IsLUB (⇑φ '' (r • P)) (r * x) := sorry
    rw [supportFunction_of_nonempty_of_isLUB hP hx,
      supportFunction_of_nonempty_of_isLUB (by simp [hP]) hrP]
    simp [WithBotTop.coe]
  · sorry

open scoped Pointwise Classical in
/-- Version of `supportFunction_smul` allowing for `P` to be empty, but asking for positive `R`. -/
lemma supportFunction_smul'
    (P : Set V) {r : R} (hr : 0 < r) (φ : Module.Dual R V) :
    supportFunction R (r • P) φ = r * (supportFunction R P φ) := by
  sorry

-- additivity: TODO write down!

/-
supportFunction of Minkowski sum  ---> Rockefeller's book?

Note: this will require some hypotheses about boundedness of sets
Perhaps add a typeclass "every bounded set has a least upper bound" (which is satisfied for
e.g. `ℝ`), and prove a version of this lemma without this hypothesis.
Asked on Zulip about a name for this concept, and if this already exists:
https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Every.20bounded.20above.20set.20has.20a.20least.20upper.20bound
-/

/- ## Convex closure -/
-- TODO: figure out the right variables to use!

-- if V has a nice topology... we can define convexClosure, and should have the following
-- P a set in the convex space, with a topology
-- (and hope that if V is a module, we have a convex space)


section

-- before: variable {R V Q W : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
-- [AddCommMonoid V] [Module R V][CommSemiring Q] [PartialOrder Q] [IsStrictOrderedRing Q] [Convexity.ConvexSpace Q W]
-- now: We want that our R-module is a convex space. For this we need [CommRing R], [AddCommGroup V]
-- TODO: We have to check again!!!!

variable {R V Q W : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [Convexity.ConvexSpace R V]
  [CommSemiring Q] [PartialOrder Q] [IsStrictOrderedRing Q] [Convexity.ConvexSpace Q W]

lemma supportFunctionConvexHull (P : Set V) :
    supportFunction R P = supportFunction R (Convexity.convexHull R P) := by
    -- we have to cast the module R V into a ConvexSpace R V
    -- this should be doable with Mathlib.Geometry.Convex.ConvexSpace.Module
    sorry

    -- idea: prove two inequalities
    -- first follows by inclusion, the other with convex_convexHull_eq and linearity
    -- convex_convexHull_eq only exists for the Analysis definition
    -- there should be convex_convexHull_eq for convex spaces
  -- sorry

lemma supportFunctionAffineConvexHull (P : Set W) :
    supportFunctionAffine Q P = supportFunctionAffine Q (Convexity.convexHull Q P) := by
    -- what is the convex hull of ∅
    --> this is ∅ and therefore compatible with our definition (see convexHull_empty)
    -- check compatibility with our junk value definition
    -- "good" remaining case should be then the normal proof
  sorry

-----
-- Our attempt
lemma supportFunctionAffineConvexHull_2 (P : Set W) (φ : ConvexSpace.dual Q W) :
    supportFunctionAffine Q P φ = supportFunctionAffine Q (Convexity.convexHull Q P) (φ):= by
    by_cases! hP : P.Nonempty
    · by_cases hP' : ∃ x, IsLUB (φ '' P) x
      · obtain ⟨x, hx⟩ := hP'
        have hx' : IsLUB (φ '' Convexity.convexHull Q P) x := by sorry
        have hC : φ '' Convexity.convexHull Q P = Convexity.convexHull Q (φ '' P ) := sorry
/- for this we could apply Convexity.IsAffineMap.image_convexHull but we need that φ isAffineMap
and we have that it is in the convex space dual-/
        sorry
-- this is the case where there is no LUB
      · sorry
--this is the case with P = ∅
    rw [hP]
    rw [Convexity.convexHull_empty]


end

def convexClosure (P : Set V) : Set V := sorry

-- split into convex hull, and one statement about topological closure

example {P : Set V} : supportFunction R P = supportFunction R (convexClosure P) := sorry



-- example: over ℚ, take P = (0, √2) ∩ ℚ ⊆ ℚ.
-- (is not a polytope, but perhaps still an interesting set)
-- check: is a convex set over ℚ (?!)
-- our current definition returns either 0 (for a negative rational number) or "the junk value 37"
-- convex closure is (to be filled in)

/-- The interval `(0, √2) ∩ ℚ ⊆ ℚ`, whose support function is a test case for the
"special junk value" in our definition of support functions. -/
def funkySet : Set ℚ := { q | 0 < q ∧ q ^2 < 2}

instance : IsStrictOrderedRing ℚ where
  add_le_add_left a b hab c := by gcongr
  le_of_add_le_add_left a b c h := Rat.add_le_add_left.mp h
  mul_lt_mul_of_pos_left a ha b c h := (Rat.mul_lt_mul_left ha).mpr h
  mul_lt_mul_of_pos_right c hc a b h := (Rat.mul_lt_mul_right hc).mpr h

lemma isConvex_funkySet : Convexity.IsConvexSet ℚ funkySet := by
  sorry

lemma supportFunction_funkySet : supportFunction ℚ funkySet = sorry := sorry

end linear
