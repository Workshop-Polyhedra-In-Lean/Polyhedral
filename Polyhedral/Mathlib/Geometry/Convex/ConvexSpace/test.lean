import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Pointwise
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.RecessionCone
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.HPolyhedron
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.Basic

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
theorem zero_smul_v (w : V) : (0 : K) • w = (0 : V) := by
  apply add_right_cancel (b := (0:K)• w)
  rw [←add_smul]
  --rw [exx]

  sorry
