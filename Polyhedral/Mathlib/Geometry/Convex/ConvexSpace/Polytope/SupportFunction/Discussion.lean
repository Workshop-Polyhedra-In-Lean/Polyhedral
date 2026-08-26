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

-/
