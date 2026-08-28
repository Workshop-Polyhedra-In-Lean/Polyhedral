/-
Copyright (c) 2026 TODO AUTHORS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor
-/
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Mathlib.Order.WithBotTop
import Mathlib.Geometry.Convex.ConvexSpace.Defs

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
-/

-- Prerequisites for generalising the definition of support function to convex spaces.
section

open Convexity
variable {R V W : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R V] [ConvexSpace R W]

-- TODO: think about the right generality for this lemma!
lemma IsAffineMap.add {f g : V → R} (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R (f + g) := by
  refine ⟨fun s ↦ ?_⟩
  sorry -- TODO!

-- TODO: think about the right generality for this lemma!
lemma IsAffineMap.smul {f : V → R} {c : R} (hf : IsAffineMap R f) :
    IsAffineMap R (c • f) := by
  refine ⟨fun s ↦ ?_⟩
  sorry -- TODO!

@[fun_prop]
lemma IsAffineMap.zero [Zero W] : IsAffineMap R (0 : V → W) := IsAffineMap.const _

variable (R V) in
/-- The dual of a convex space `V` over `R`: the module of all affine maps `V → R` -/
def ConvexSpace.dual : Submodule R (V → R) where
  carrier := { f | IsAffineMap R f }
  add_mem' {f g} hf hg := by simp_all [IsAffineMap.add]
  zero_mem' := by simp only [Set.mem_ofPred_eq]; fun_prop
  smul_mem' c x hx := by simp_all [IsAffineMap.smul]

instance : FunLike (ConvexSpace.dual R V) V R where
  coe φ := φ.1
  coe_injective φ ψ h := by simp_all

end

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
- Attempt 2a: reorder the definition cases; just a Lean issue.
- Attempt 3: add another case distinction into the definition
  If S is bounded above (but no least upper bound), return a junk value `37`.
  If if is unbounded, we return `⊤` instead.
- Attempt 4: generalize to all convex spaces; defined on the dual of a convex space
  Issue: is the wrong definition for the scaling property to hold!
  so revert back to definition 3

  Other issue: choices of junk values
  For multiplication, if `φ '' P` is a "funky" set (i.e., bounded without a least upper bound),
  the equation `λ * (supportFunction R P φ) = supportFunction R (λ • P) φ` becomes `λ * junk = junk`.
  This is false for the current junk value, but becomes true for the junk value `37`.
  This is also useful as the definition will make one fewer case distinction.

  For Minkowski sums, note that the Minkowski sum of a set `S` with a least upper bound and a funky
  set `T` can be funky, but also could have a least upper bound. Take `S = [0, 1) x {0} ⊆ ℚ²`
  and `T = {0} × [0, 1]`. Then `S + T` is the unit square without the edge `{1}×[0,1]`.
  For some suitable functional (e.g., the function `(x, y) ↦ x)`), this will have no least upper
  bound, but for other other functionals, there will be a least upper bound.

current definition (attempt 5) below

-/

section

variable {R V : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [Convexity.ConvexSpace R V]

variable (R) in
/- Variant of supportFunction, for general convex spaces.

We don't want to define linear programs using support functions,
but a linear program should have an associated support function.
"Support fns arise from varying an objective function in a linear program."
Often, it's convenient to add a constant to a linear program (i.e., you'd want an affine support fn)
but it's not clear if this is called "support function" in the literature.

WARNING: this does not coincide with the supportFunction over modules,
as their domains are different.

Q(Martin): Is there a definition of support functions with affine maps in the literature?
A(Georg): yes, via linear programs (above).
-/
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

-- supportFunction of singleton
lemma supportFunctionAffine_singleton' {v : V} {φ : ConvexSpace.dual R V} :
    supportFunctionAffine R {v} φ = φ v := by
  rw [supportFunctionAffine_of_nonempty_of_isLUB (by simp)]
  simp

lemma supportFunctionAffine_singleton {v : V} : supportFunctionAffine R {v} = fun φ ↦ φ v := by
  ext φ
  rw [supportFunctionAffine_singleton']

/-
Then, redefine the linear support function as the restriction of the affine one to the module dual.
Scalar multiplication, Minkowski sum etc. will still be true under restriction.

-/

end

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
def supportFunction (P : Set V) :
    Module.Dual R V → WithBotTop R :=
  fun φ ↦ by
  by_cases hP : P.Nonempty
  · letI S := φ '' P
    by_cases hS' : ∃ x, IsLUB S x
    · exact WithBotTop.coe  hS'.choose
    · -- Note that we choose `⊤` as junk value if S is not bounded above.
      exact ⊤
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
    (_hP' : BddAbove (φ '' P)) :
    supportFunction R P φ =
      if hS : ∃ x, IsLUB (⇑φ '' P) x then WithBotTop.coe hS.choose else ⊤
    := by
  unfold supportFunction
  rw [dite_eq_left hP]

/- TODO: we want more specialized versions of this lemma instead
open scoped Classical in
lemma supportFunction_of_nonempty {P : Set V} (hP : P.Nonempty) (φ : Module.Dual R V) :
    supportFunction R P φ = (
      if hS : BddAbove (⇑φ '' P) then
        if _hS' : ∃ x, IsLUB (⇑φ '' P) x then
        WithBotTop.coe hs.choose else WithBotTop.coe 37 else ⊤)
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
