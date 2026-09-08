/-
Copyright (c) 2026 Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor
-/
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Mathlib.Order.WithBotTop
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Geometry.Convex.ConvexSpace.Module

/-! # General properties of support functions

We define the support function of a set in a general module over a semiring.
We do not assume the set to be convex (let alone a polyhedron).
We don't assume `R` to have a total order; a partial order is sufficient.
(For example, any lattice need not be totally ordered.)
Neither do we assume that the supremum is this definition is attained as the maximum.
(For a continuous pairing over a compact set, this is true.)

(For comparison, note that Rockefeller uses inner products and convex sets in the definition,
and assumes non-emptiness. They mention the unbounded case, though.)

## Main definitions and results
Assume `V` is a module over a semiring `R` endowed with a partial order.
- `supportFunction P` is the support function of `P : Set V`,
  mapping `Module.Dual R V` to `WithBotTop R`.

* generalise from the standard dual (or, any inner product) to bilinear pairings
  Assume a bilinear pairing `M →ₗ[R] N →ₗ[R] R` instead, so `P : Set M` would have support function
  of type `N →ₗ[R] R → WithBot (WithTop R)`
-/

-- Prerequisites for generalising the definition of support function to convex spaces.
section

open Convexity
variable {R V W : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R V] [ConvexSpace R W]

variable (R V) in
abbrev ConvexSpace.dual := ConvexSpace.AffineMap R V R

lemma ConvexSpace.dualMap_IsAffine (f : ConvexSpace.dual R V) : IsAffineMap R f := by
  exact ConvexSpace.AffineMap.isAffineMap f

instance : FunLike (ConvexSpace.dual R V) V R := by
  exact ConvexSpace.AffineMap.instFunLike

end

section

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [Convexity.ConvexSpace R V]

variable (R) in
noncomputable def supportFunctionAffine (P : Set V) : ConvexSpace.dual R V → WithBotTop R :=
  fun φ ↦ by classical exact
  if hP : P.Nonempty then
    -- Note that we choose `⊤` as junk value if S is not bounded above.
    if hP' : ∃ x, IsLUB (φ '' P) x then WithBotTop.coe hP'.choose else ⊤
  else ⊥

@[simp]
lemma supportFunctionAffine_empty : supportFunctionAffine R (∅ : Set V) = ⊥ := by
  unfold supportFunctionAffine
  ext φ
  have : ¬((∅ : Set V).Nonempty) := by simp
  simp

lemma supportFunctionAffine_of_nonempty_of_isLUB
    {P : Set V} (hP : P.Nonempty) {φ : ConvexSpace.dual R V}
    {r : R} (hr : IsLUB (φ '' P) r) :
    supportFunctionAffine R P φ = r := by
  have aux : ∃ x, IsLUB (⇑φ '' P) x := by use r
  simp [supportFunctionAffine, hP, aux, aux.choose_spec.unique hr]

lemma supportFunctionAffine_of_nonempty_of_not_exists_isLUB
    {P : Set V} (hP : P.Nonempty) {φ : ConvexSpace.dual R V}
    (hP' : ¬(∃ x, IsLUB (φ '' P) x)) :
    supportFunctionAffine R P φ = ⊤ := by
  simp [supportFunctionAffine, hP, hP']

@[simp]
lemma supportFunctionAffine_singleton_value {v : V} {φ : ConvexSpace.dual R V} :
    supportFunctionAffine R {v} φ = φ v := by
  rw [supportFunctionAffine_of_nonempty_of_isLUB (by simp)]
  simp

@[simp]
lemma supportFunctionAffine_singleton {v : V} : supportFunctionAffine R {v} = fun φ ↦ φ v := by
  ext φ
  simp

end

section
/-
Then, redefine the linear support function as the restriction of the affine one to the module dual.
Scalar multiplication, Minkowski sum etc. will still be true under restriction.

-/

variable {R V : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [Convexity.ConvexSpace R V] [Convexity.IsModuleConvexSpace R V]

-- linear maps are convex combination preserving
-- ask olivia about this definition
def iota (φ : Module.Dual R V) : ConvexSpace.dual R V where
  toFun := φ

/-
The support function of a set `P ⊆ V`, inside an `R`-module `V`.
This definition has several special cases:
If `P` is empty, map any functional to `-∞`. Otherwise, for each functional `φ`,
- if `φ '' P` is unbounded, we map `φ` to `+∞`;
- if `φ '' P` has no least upper bound, we map it to `+∞` as a junk value
Otherwise, we return a supremum of `φ '' P` (which is unique because `R` has a partial order).
-/
variable (R) in
noncomputable
def supportFunction (P : Set V) : Module.Dual R V → WithBotTop R :=
  fun φ ↦ supportFunctionAffine R P (iota φ)

variable {R V : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [Convexity.ConvexSpace R V] [Convexity.IsModuleConvexSpace R V]

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
  replace hr : IsLUB (⇑(iota φ) '' P) r := by
    have hphi : ⇑(iota φ) = φ := by rfl
    rw [hphi]
    exact hr
  have aux : ∃ (x : R), IsLUB ((iota φ) '' P) x := by use r
  simp [supportFunction, supportFunctionAffine, hP, aux, aux.choose_spec.unique hr]

@[simp]
lemma supportFunction_singleton_value {v : V} {φ : Module.Dual R V} :
supportFunction R {v} φ = φ v := by
  rw [supportFunction_of_nonempty_of_isLUB (by simp)]
  simp

lemma supportFunction_singleton {v : V} : supportFunction R {v} = fun φ ↦ φ v := by
  ext φ
  rw [supportFunction_singleton_value]

-- XXX: do we want this lemma, or is it not worth it?
open scoped Classical in
lemma supportFunction_of_nonempty_of_bddAbove {P : Set V} (hP : P.Nonempty) {φ : Module.Dual R V}
    (hP' : BddAbove (φ '' P)) :
    supportFunction R P φ =
      if hS : ∃ x, IsLUB (⇑φ '' P) x then WithBotTop.coe hS.choose else ⊤
    := by
  unfold supportFunction
  sorry

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
end
