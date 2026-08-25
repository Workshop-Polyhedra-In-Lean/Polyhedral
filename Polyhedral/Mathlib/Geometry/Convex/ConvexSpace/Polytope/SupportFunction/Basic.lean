import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

/-! # General properties of support functions

We define the support function of a set in a general module over a semiring.

- mention generality we want
- special values for empty and unbounded
- special junk value for sets without a least upper bound
- example over ℚ

Basic properties to prove: in progress!

-/

variable {R V : Type*} [Semiring R] [PartialOrder R] [AddCommMonoid V] [Module R V]

-- S convex set; take supremum instead of scalar product
-- support function for a convex set (in a convex space, with a total order on the ring)
-- why do we need a total order? do we now the sup is the max??
-- maximum need not be attained: maximum need not be attained
-- but do need the supremum to exist (and be unique)
-- partial order could have two maximal elements which are incomparable
-- -> want a total order!

/-
This definition does not assume P to be convex (as we don't use it in the definition).
We don't assume R to have a total order either, but just that every set has a supremum.
(A lattice need not be totally ordered, but still has suprema.)

XXX: This does not cover polytopes in affine spaces; is there a version for them?
What would the support function even be?
-/

/-
idea
 if P is empty, -∞
 if φ '' P is unbounded, assign +∞
 otherwise, take the supremum

question: what's -∞ + ∞, is it -∞? (yes so for EReal)
  (otherwise, addition is obvious)
multiplication is similar, +∞ * -∞ = -∞

-/

/-
next steps, after the definition
- prove that ∅ has -∞
- supportFunction of singleton
- supportFunction is homogeneous
- supportFunction of Minkowski sum  ---> Rockefeller's book?

(Rockefeller uses inner products and convex sets, and assumes non-emptiness)
-/

variable (R) in
-- XXX: use WithTopBot if that exists?
noncomputable
def supportFunction /-[SupSet R]-/ (P : Set V)
    -- Initial candidate for the definition: any non-empty bounded above set has
    -- a least upper bound.
    -- Issue: not satisfied for the rational numbers; perhaps want rational support
    -- functions for rational polytopes (would be impossible)!
    -- If the subset of R we're dealing with has a least upper bound, return that;
    -- otherwise return a junk value.
    -- Motivation: rational polytopes, which occur naturally during computation.

    -- Support functions are closely related to convex bodies;
    -- can extend to unbounded convex sets.
    -- TODO: what's the right order-theoretic definition for this?
    : --(hR : ∀ s : Set R, s.Nonempty → BddAbove s → ∃ x : R, IsLUB s x) :
    Module.Dual R V → WithBot (WithTop R) :=
  fun φ ↦ by
  -- New definition: -∞ for the empty set; +∞ if unbounded above,
  -- a LUB if there exists one (and otherwise 0).
  by_cases hP : P.Nonempty
  · let S := φ '' P
    by_cases hS : BddAbove S
    · by_cases hS' : ∃ x, IsLUB S x
      · choose x hx using hS
        exact some (some x)
      · exact 37 -- TODO: is this the good junk value?
    -- Other definition
    -- by_cases hS : BddAbove S
    -- · -- Take a least upper bound of S.
    --   have : S.Nonempty := by
    --     simp only [S]
    --     exact Set.Nonempty.image (⇑φ) hP
    --   choose x hx using hR S this hS
    --   exact some (some x)
    · exact ⊤
  · exact ⊥





-- invariant under convex hull
-- invariance under convex closure
-- invariance under additivity
-- invariance under dilation


-- later task: when we replace this set by its convex hull?
-- prove that it equals its convex hull in nice cases

-- example: unit ball without a point on the boundary; its support fn over R^n
-- is the same as for the full unit ball.
-- this is what we want, fine (because it's the supp)

-- support function of a set should be (in good cases? ideally always)
-- the support function of its convex closure,
-- i.e. the topological closure of its convex hull




variable {P : Set V} -- (hP : Convex R P)


/-
## Open questions/for later

### What about unbounded polyhedra

What do you do about unbounded polyhedra, if the supremum would be infinite?
(For linear programs, that occurs naturally.)

Our approach won't work here: while NNReal is still a semiring (it's fine),
WithTop Real is not a semiring (and neither is EReal): -2 * ∞ = -∞; -∞ + ∞ = trouble

For unbounded bodies, we usually choose the value infinity on paper.
(But most theorems assume boundedness.)
Linear programming duality cares about unbounded programs.

Maybe it's not as important for support functions?

(Also, what's a good way to define linear programming?)
-/
