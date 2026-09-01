import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

namespace Convexity

variable {R X : Type*}
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable (R)

lemma IsConvexSet.Iic (a : R) : IsConvexSet R (Set.Iic a) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  change w.sConvexComb ≤ a
  rw [sConvexComb_eq_sum, ← iConvexComb_const w a, iConvexComb_eq_sum]
  exact Finsupp.sum_le_sum fun x hx ↦
    smul_le_smul_of_nonneg_left (hw (by simpa using hx)) (w.weights_nonneg x)

lemma IsConvexSet.Ici (a : R) : IsConvexSet R (Set.Ici a) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  change a ≤ w.sConvexComb
  rw [sConvexComb_eq_sum, ← iConvexComb_const w a, iConvexComb_eq_sum]
  exact Finsupp.sum_le_sum fun x hx ↦
    smul_le_smul_of_nonneg_left (hw (by simpa using hx)) (w.weights_nonneg x)

lemma IsConvexSet.Icc (a b : R) : IsConvexSet R (Set.Icc a b) := by
  simpa [Set.Ici_inter_Iic] using
    (IsConvexSet.Ici R a).inter (IsConvexSet.Iic R b)

lemma convexHull_pair_subset_Icc_of_le (a b : R) (hab : a ≤ b) :
  convexHull R {a, b} ⊆ Set.Icc a b := by
  apply convexHull_min
  · exact Set.pair_subset (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  · exact IsConvexSet.Icc R a b

lemma Icc_zero_one_subset_convexHull [ExistsAddOfLE R] :
    Set.Icc 0 1 ⊆ convexHull R ({0, 1} : Set R) := by
  rintro x ⟨hx0, hx1⟩
  obtain ⟨c, hc, hxc⟩ := exists_nonneg_add_of_le hx1
  have hC : IsConvexSet R (convexHull R ({0, 1} : Set R)) :=
    IsConvexSet.convexHull
  simpa using hC.convexCombPair_mem (x := 1) (y := 0)
    (subset_convexHull_self (by simp))
    (subset_convexHull_self (by simp))
    hx0 hc hxc

lemma unitInterval_eq_convexHull [ExistsAddOfLE R] :
  Set.Icc 0 1 = convexHull R ({0, 1}: Set R) := by
  apply Set.Subset.antisymm
  · exact Icc_zero_one_subset_convexHull R
  · exact convexHull_pair_subset_Icc_of_le R 0 1 zero_le_one

end Convexity
