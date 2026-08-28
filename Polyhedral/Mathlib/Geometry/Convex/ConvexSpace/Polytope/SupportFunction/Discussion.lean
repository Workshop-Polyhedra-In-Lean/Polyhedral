/-
Copyright (c) 2026 Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor
-/

/-
More discussion notes

- IsAffineMap should be renamed! (-> mathlib PR)

- can generalise support functions also to convex spaces;
  want to have morphisms of convex spaces then
  (these exist as `IsAffineMap` in mathlib, horribly named. unbundled
   the Polyhedral repo has that Affine maps are affine, but not other examples.)
   there are such examples, by the way!

- every R-Module (over a semiring) is a convex space; mathlib knows this already
- motivating example: convex cone, is a module over NNReal (i.e., a semiring)
- are there convex spaces which are not modules over a semiring?
  yes, lattices with the sup operation as addition (did I get this right?)

- right generality of lemmas? have R-modules and convex spaces as generality for now

in R-modules
  c f_P = f_cP for λ ≥ 0
    structural reason: scaling is a poset isomorphism (precisely because we're in an ordered ring)
  f_P + f_Q = f_{minkowskiSum P Q}

in convex spaces
  f_s = f_{convexHull s}
  f_{S∪T} = max(f_S, f_T)

Georg's advice: take a look in textbook if there's another property of support functions we want.


(In general, there's a theory of abstract convexity, which defines convexity by a set of axioms it
satisfies. Perhaps mathlib should be generalised this way, but that might be just another convexity
refactor. XXX why was that useful?)

TODO/open question: should the notion of "convex function" also be generalized to
any convex space? (The current definition is far more specialized.)
Motivating example: a support function should be a convex function

----------

Question: given `φ : V → R`, does `IsAffineMap φ` imply that `φ` is affine?
(The converse is clearly true.) TODO: if so, generalise this lemma to that setting!
This would imply that the dual of a module V, as a convex space, coincides with its dual module.
Martin believes this is true; would be rather helpful.
Then, this lemma would hold for any convex map with φ 0 = 0.

/-
On a module, we have affine maps (`AddTorsor`'s `AffineMap`), and
convex space's convex maps `IsAffineMap`. We know that the former are the latter
(proven in the repo). Is the converse true?

Hm... should the "convex space dual" for affine spaces then restrict to only linear maps?

-/

-------

Note. You cannot directly generalise the definition to "any convex space".
Convex spaces have a dual space (namely, all "convex maps" `V → R`).
The definition of support functions generalises with domain of this dual,
i.e. it can be defined for any functional.

However, this is not the right definition, as dilation invariance becomes false:
an `R`-module `V` has two notion of spaces, either as a module `Module.Dual R V` or as a convex space.
These spaces are not the same: a convex map `V \to R` (of R-modules) is always affine,
but need not be linear. The scaling property of the support function only works for linear functionals.

(discussion not converged)

-/
