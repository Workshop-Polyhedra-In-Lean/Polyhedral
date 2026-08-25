/-
Copyright (c) 2026 TODO AUTHORS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor
-/
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

/-! # General properties of support functions

We define the support function of a set in a general module over a semiring.
We do not assume the set to be convex (let alone a polyhedron).
We don't assume `R` to have a total order; a partial order is sufficient.
(For example, any lattice need not be totally ordered.)
Neither do we assume that the supremum is this definition is attained as the maximum.
(For a continuous pairing over a compact set, this is true.)

- mention generality we want
- special values for empty and unbounded
- special junk value for sets without a least upper bound
- example over ℚ


(For comparison, note that Rockefeller uses inner products and convex sets in the definition,
and assumes non-emptiness. They mention the unbounded case, though.)


## Main definitions and results
Assume `V` is a module over a semiring `R` endowed with a partial order.
- `supportFunction P` is the support function of `P : Set V`,
  mapping `Module.Dual R V` to `WithBotTop R`.

Basic properties to prove: in progress!

## TODO

* generalise from the standard dual (or, any inner product) to bilinear pairings
  Assume a bilinear pairing `M →ₗ[R] N →ₗ[R] R` instead, so `P : Set M` would have support function
  of type `N →ₗ[R] R → WithBot (WithTop R)`
* use `WithBotTop R` as the codomain; this should have the properties we want
-/

variable {R V : Type*} [Semiring R] [PartialOrder R] [AddCommMonoid V] [Module R V]

-- S convex set; take supremum instead of scalar product
-- support function for a convex set (in a convex space, with a total order on the ring)
-- why do we need a total order? do we now the sup is the max??
-- maximum need not be attained: maximum need not be attained
-- but do need the supremum to exist (and be unique)
-- partial order could have two maximal elements which are incomparable
-- -> want a total order!

    -- Support functions are closely related to convex bodies;
    -- can extend to unbounded convex sets.

/-
XXX: This does not cover polytopes in affine spaces; is there a version for them?
What would the support function even be?
-/

/-
Note that the codomain still has good arithmetic properties (which we need)!
We want addition to satisfy `-∞ + ∞ = -∞`, similarly to `EReal`:
the support function of the Minkowski sum of two sets should be the sum of two polytopes,
and for the empty resp. an unbounded polytope, the sum of support functions is the LHS,
whereas their Minkowski sum is empty (so has support function mapping to `-∞`).
-/

/-
History of this definition

- Attempt 1: assumed `SupSet R` and took the `sSup (φ '' P)`... that's way too strong, excludes e.g.
  the real numbers.
- Attempt 2: assume `(hR : ∀ s : Set R, s.Nonempty → BddAbove s → ∃ x : R, IsLUB s x)`,
  i.e. assume any non-empty bounded above set has a least upper bound (and choose that).
  Issue: this not satisfied for the rational numbers; perhaps we want rational support functions
  for rational polytopes (which this definition excludes)
  Rational polytopes occur naturally during computation.
-/

/-
The support function of a set `P ⊆ V`, inside an `R`-module `V`.
This definition has several special cases:
If `P` is empty, map any functional to `-∞`. Otherwise, for each functional `φ`,
- if `φ '' P` is unbounded, we map `φ` to `+∞`;
- if `φ '' P` has no least upper bound, we map it to a junk value (currently 37).
Otherwise, we return a supremum of `φ '' P` (which is unique because `R` has a partial order).
-/
variable (R) in
noncomputable
def supportFunction (P : Set V) :
    Module.Dual R V → WithBot (WithTop R) := -- could use WithBotTop as the codomain
  fun φ ↦ by
  by_cases hP : P.Nonempty
  · letI S := φ '' P
    by_cases hS' : ∃ x, IsLUB S x
    · exact WithBot.some (WithTop.some hS'.choose)
    · by_cases hS : BddAbove S
      · -- TODO: can we simplify, by taking -∞ also as this junk value?
        exact 37 -- TODO: is this the good junk value?
      · exact ⊤
    -- Other definition
    -- by_cases hS : BddAbove S
    -- · -- Take a least upper bound of S.
    --   have : S.Nonempty := by
    --     simp only [S]
    --     exact Set.Nonempty.image (⇑φ) hP
    --   choose x hx using hR S this hS
    --   exact some (some x)
  · exact ⊥

@[simp]
lemma supportFunction_empty : supportFunction R (∅ : Set V) = ⊥ := by
  unfold supportFunction
  ext φ
  have : ¬((∅ : Set V).Nonempty) := by simp
  simp

lemma supportFunction_of_nonempty_of_isLUB
    {P : Set V} (hP : P.Nonempty) {φ : Module.Dual R V}
    {r : R} (hr : IsLUB (φ '' P) r) :
    supportFunction R P φ = r := by
  have aux : ∃ x, IsLUB (⇑φ '' P) x := by use r
  simp [supportFunction, hP, aux, aux.choose_spec.unique hr]

-- supportFunction of singleton
lemma supportFunction_singleton' {v : V} {φ : Module.Dual R V} : supportFunction R {v} φ = φ v := by
  rw [supportFunction_of_nonempty_of_isLUB (by simp)]
  simp

lemma supportFunction_singleton {v : V} : supportFunction R {v} = fun φ ↦ φ v := by
  ext φ
  rw [supportFunction_singleton']

-- XXX: do we want this lemma, or is it not worth it?
open scoped Classical in
lemma supportFunction_of_nonempty_of_bddAbove {P : Set V} (hP : P.Nonempty) {φ : Module.Dual R V}
    (hP' : BddAbove (φ '' P)) :
    supportFunction R P φ =
      if hS : ∃ x, IsLUB (⇑φ '' P) x then
      WithBot.some (WithTop.some hS.choose) else WithBot.some 37
    := by
  unfold supportFunction
  rw [dite_eq_left hP]
  simp only [hP']
  by_cases hx : ∃ x, IsLUB (φ '' P) x
  · simp [hx]
  · simp [hx]

/- TODO: we want more specialized versions of this lemma instead
open scoped Classical in
lemma supportFunction_of_nonempty {P : Set V} (hP : P.Nonempty) (φ : Module.Dual R V) :
    supportFunction R P φ = (
      if hS : BddAbove (⇑φ '' P) then
        if _hS' : ∃ x, IsLUB (⇑φ '' P) x then
        WithBot.some (WithTop.some (Classical.choose hS)) else WithBot.some (37 : R) else ⊤)
    := by
  unfold supportFunction
  dsimp
  rw [ite_eq_left hP]
  /- by_cases hS : BddAbove (φ '' P); swap
  · simp [hS]
  simp only [hS, ↓reduceDIte]
  by_cases hx : ∃ x, IsLUB (φ '' P) x; swap
  · simp [hx]; rfl
  simp [hx]
  rfl -/
  sorry -/

-- example: unit ball without a point on the boundary; its support fn over R^n
-- is the same as for the full unit ball.
-- this is what we want, fine (because it's the supp)

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


## Linear versus affine space

Does anybody care about support functions in affine space?
(for the same reason as polarity; given an affine space, want ... (unsure what))
how do we affinise? on an affine space w.r.t. a point


If we take a compact convex body, we want the polar body (formed by all the support functions)
to be compact. That's true w.r.t. a point in the relative interior of the initial body.
----> make an auxiliary choice in the definition?
---> or take your constructions all w.r.t. to a point

currently, given an affine space A and a point x, get a separate space A' which is a linear space
so need, to transport A and all the other objects into A'

not conclusive, TODO continue this discussion!
-/
