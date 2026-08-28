import Mathlib.Geometry.Convex.ConvexSpace.Prod

namespace Convexity

variable {R X Y Z : Type*}
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]

@[fun_prop]
lemma IsAffineMap.prod_mk {f : X → Y} {g : X → Z}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R fun x ↦ (f x, g x) where
  map_sConvexComb w := by
    ext
    · simpa using hf.map_iConvexComb w id
    · simpa using hg.map_iConvexComb w id

end Convexity
