/-
Copyright (c) 2026 TODO AUTHORS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor
-/
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.SupportFunction.Basic

/-! # Basic properties of support functions (of sets)
-/

variable {R V : Type*} [Semiring R] [PartialOrder R] [AddCommMonoid V] [Module R V]

/- ## Basic properties -/

-- is positively homogeneous (i.e., behaviour under scaling φ): TODO write down

-- invariance under dilation: TODO write down!

-- additivity: TODO write down!

-- supportFunction of Minkowski sum  ---> Rockefeller's book?

/- ## Convex closure -/
-- TODO: figure out the right variables to use!

-- if V has a nice topology... we can define convexClosure, and should have the following
-- P a set in the convex space, with a topology
-- (and hope that if V is a module, we have a convex space)
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
