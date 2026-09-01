import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Prod

open Convexity
namespace AddTorsor

variable {R V P I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [ConvexSpace R P] [IsAffineConvexSpace R V P]

@[simp]
lemma iConvexComb_vadd (w : StdSimplex R I) (f : I → V) (g : I → P) :
    w.iConvexComb (f +ᵥ g) = w.iConvexComb f +ᵥ w.iConvexComb g := by
  rw [eq_vadd_iff_vsub_eq, iConvexComb_eq_affineCombination w (f +ᵥ g),
    iConvexComb_eq_affineCombination w g,
    ← Finset.sum_smul_vsub_eq_affineCombination_vsub]
  simp [Finsupp.sum]

@[fun_prop]
lemma isAffineMap_vadd : IsAffineMap R fun x : V × P ↦ x.1 +ᵥ x.2 where
  map_sConvexComb w := by
    change w.iConvexComb Prod.fst +ᵥ w.iConvexComb Prod.snd =
      w.iConvexComb fun x ↦ x.1 +ᵥ x.2
    exact (iConvexComb_vadd w Prod.fst Prod.snd).symm

@[to_fun (attr := fun_prop)]
lemma _root_.Convexity.IsAffineMap.vadd {X : Type*} [ConvexSpace R X] {f : X → V} {g : X → P}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (f +ᵥ g) := by
  change IsAffineMap R fun x ↦ f x +ᵥ g x
  simpa only [Function.comp_def] using isAffineMap_vadd.comp (hf.prod_mk hg)

end AddTorsor
