/-
Copyright (c) 2026 Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor, Mara Gruss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Grillo, Judith Müller, Michael Rothgang, Moritz Stargalla, Valentina Taylor, Mara Gruss
-/
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.SupportFunction.Basic
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.Module.Pointwise
import Mathlib.Order.Bounds.Image
import Mathlib.Algebra.Order.Field.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Data.Set.Image
/-! # Basic properties of support functions (of sets)
-/

section

variable {α : Type*} [DecidableEq α] [MulZeroClass α]

-- note: the multiplication we have on WithBotTop R will have -1 * ∞ = ∞
-- (but we don`t use that because r>0 in our properties)
-- this may not be what we want (but it coincides with what we want for positive scalars)
-- pehraps assume (a ≠ 0) (ha' : a ≠ -⊤) instead?
-- (h : 0 < a)
lemma WithBotTop.mul_top {a : WithBotTop α} (ha : a ≠ 0) (ha' : a ≠ ⊥) : a * ⊤ = ⊤ := by
  by_cases! hha : a = ⊤
  · rw [hha]
    change ((↑(⊤ : WithTop α) : WithBot (WithTop α)) *
      ↑(⊤ : WithTop α)) =
    (↑(⊤ : WithTop α) : WithBot (WithTop α))
    rw [← WithBot.coe_mul]
    simp
  · lift a to WithTop α using ha'
    have hha' : a ≠ (⊤ : WithTop α) := by
      intro h
      apply hha
      exact congrArg (fun x : WithTop α => (x : WithBot (WithTop α))) h
    lift a to α using hha'
    change (↑((↑a : WithTop α) * ⊤) : WithBot (WithTop α)) = ↑(⊤ : WithTop α)
    congr
    apply WithTop.mul_top
    intro h
    apply ha
    exact congrArg (fun x : WithTop α => (x : WithBot (WithTop α))) h

/- infinity * -inifinity equals -infinity, so we can ommit the hypothesis that
a is different than infinity-/
lemma WithBotTop.mul_bot {a : WithBotTop α} (ha : a ≠ 0) : a * ⊥ = ⊥ := by
  by_cases! hha : a = ⊥
  · rw [hha]
    simp only [ne_eq, WithBot.bot_ne_zero, not_false_eq_true, WithBot.mul_bot]
  · apply WithBot.mul_bot
    exact ha

end

section convex
-- Would be nice to have it in this more general way:
-- variable {R V : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
--   [Convexity.ConvexSpace R V]
-- Semifield
variable {R V : Type*} [Semifield R] [PartialOrder R] [IsStrictOrderedRing R] [PosMulReflectLT R]
  [Convexity.ConvexSpace R V]
  {P : Set V}

/- upperBounds(r • φ '' P) ⊆ r • upperBounds(φ '' P) is not true for a ring (we found
 a counter example for ℤ ) but we need something weaker, we just need is for the least
 upper bound-/
-- we know for sure that it is true for a semifild but not for a semiring
-- is pos. homogeneous (Judith + Valentina)
open scoped Classical Pointwise in
-- XXX: right name?
lemma supportFunctionAffine_smul_of_pos {r : R} (hr : 0 < r) (φ : ConvexSpace.dual R V) :
    supportFunctionAffine R P (r • φ) = r * supportFunctionAffine R P φ := by
  by_cases! hP : P.Nonempty
  · by_cases hP' : ∃ x, IsLUB (φ '' P) x
    · obtain ⟨x, hx⟩ := hP'
      have hrP : IsLUB ((r • φ) '' P) (r * x) := by
        have := IsLUB.mul_left hr.le hx
        have h : ((fun b ↦ r * b) '' φ '' P) = ((r • φ) '' P) := by
          apply Set.image_image
        rw [← h]
        exact this
      rw [supportFunctionAffine_of_nonempty_of_isLUB hP hx,
        supportFunctionAffine_of_nonempty_of_isLUB (by simp [hP]) hrP]
      simp [WithBotTop.coe]
    · have hrP : ¬∃ x, IsLUB (⇑(r • φ) '' P) x := by
        simp only [Convexity.ConvexSpace.AffineMap.smul_apply, smul_eq_mul, not_exists]
        intro y hy
        have H : IsLUB (φ '' P) (r⁻¹ • y) := by
          have hr': 0 ≤ r⁻¹:= by
            refine inv_nonneg_of_nonneg ?_
            exact Std.le_of_lt hr
          have hyy: IsLUB (⇑(r⁻¹ • r • φ) '' P) (r⁻¹ • y) := by
            have := IsLUB.mul_left hr' hy
            convert this
            · simp only [Convexity.ConvexSpace.AffineMap.smul_apply, smul_eq_mul]
              rw [Set.image_image]
            · rw[smul_eq_mul]
          have hphi: ⇑(r⁻¹ • r • φ) = ⇑ φ := by
            simp only [Convexity.ConvexSpace.AffineMap.coe_smul]
            refine inv_smul_smul₀ ?_ ⇑φ
            exact Ne.symm (Std.ne_of_lt hr)
          rw [hphi] at hyy
          exact hyy
        apply hP'
        exact Exists.intro (r⁻¹ • y) H
      rw [supportFunctionAffine_of_nonempty_of_not_exists_isLUB hP hrP,
         supportFunctionAffine_of_nonempty_of_not_exists_isLUB hP hP']
      simp only [WithBotTop.coe, Function.comp_apply]
      rw [WithBotTop.mul_top (by simp [hr.ne']) (by simp)]
  · rw [hP]
    simp only [supportFunctionAffine_empty, Pi.bot_apply]
    rw [WithBotTop.mul_bot _]
    have:= WithBotTop.coe_lt_coe.mpr hr
    exact this.ne.symm

open scoped Classical Pointwise in
/-here empty set should be excluded, maybe we dont want this lemma -/
lemma supportFunctionAffine_homogeneous' (hP : P.Nonempty)
    {r : R} (hr : 0 ≤ r) (φ : ConvexSpace.dual R V) :
    supportFunctionAffine R P (r • φ) = r * supportFunctionAffine R P φ := by
  sorry

end convex

section linear

variable {R V : Type*} [Field R] [PartialOrder R] [IsStrictOrderedRing R] [PosMulReflectLT R]
  [AddCommGroup V] [Module R V] [Convexity.ConvexSpace R V] [Convexity.IsModuleConvexSpace R V]
-- To be able to use the lemma "positive homogeneity for IsAffineMap
-- one maybe has to change "[CommRing R]" to "[Semifield R]"

/- ## Basic properties -/

-- is positively homogeneous (i.e., behaviour under scaling φ): TODO write down

-- invariance under dilation
open scoped Pointwise Classical in
lemma supportFunction_smul_set_of_nonneg
    {P : Set V} {r : R} (hr : 0 ≤ r) (hP : P.Nonempty) (φ : Module.Dual R V) :
    supportFunction R (r • P) φ = r * (supportFunction R P φ) := by
  by_cases hP' : ∃ x, IsLUB (φ '' P) x
  · obtain ⟨x, hx⟩ := hP'
    have hrP : IsLUB (⇑φ '' (r • P)) (r * x) := by
      have hphi : φ '' ( r • P )= r • φ '' P := by
        refine Set.image_smul_comm (⇑φ) r P ?_
        intro b
        simp only [map_smul, smul_eq_mul]
      rw [hphi]
      have := IsLUB.mul_left hr hx
      convert this
      conv =>
        lhs
        rw [← Set.image_smul]
      rfl
    rw [supportFunction_of_nonempty_of_isLUB hP hx,
      supportFunction_of_nonempty_of_isLUB (by simp [hP]) hrP]
    simp [WithBotTop.coe]
  · rw [supportFunction_of_nonempty_of_not_exists_isLUB hP hP']
    by_cases hzero: r=0
    · rw [hzero]
      rw [mul_eq_zero_comm.mp]
      · rw [Set.zero_smul_set]
        · have : supportFunction R 0 φ = φ 0 := supportFunction_singleton_value
          rw [this]
          simp only [map_zero]
          exact (AddOpposite.op_eq_zero_iff (WithBotTop.coe 0)).mp rfl
        · exact hP
      · exact mul_eq_zero_of_right ⊤ rfl
    · have h0 : 0 < r := by exact Std.lt_of_le_of_ne hr fun a ↦ hzero (id (Eq.symm a))
      have inf: WithBotTop.coe r * ⊤ = ⊤ := by
        refine WithBotTop.mul_top ?_ ?_
        · have:= WithBotTop.coe_lt_coe.mpr h0
          exact this.ne.symm
        · simp
      rw [inf]
      have hnon : ¬∃ x, IsLUB (⇑φ '' (r • P)) x := by
        simp only [not_exists]
        intro y hy
        have hyr : IsLUB (⇑φ '' P) (r⁻¹ • y) := by
          have : ⇑φ '' (r • P) = r • ⇑φ '' P := by
            refine Set.image_smul_comm (⇑φ) r P ?_
            intro b
            simp only [map_smul, smul_eq_mul]
          rw [this] at hy
          have hr': 0 ≤ r⁻¹:= by
            refine inv_nonneg_of_nonneg ?_
            exact Std.le_of_lt h0
          have hphi: ⇑(r⁻¹ • r • φ) = ⇑ φ := by
            simp only [LinearMap.coe_smul]
            refine inv_smul_smul₀ ?_ ⇑φ
            exact Ne.symm (Std.ne_of_lt h0)
          have hyy: IsLUB (⇑(r⁻¹ • r • φ) '' P) (r⁻¹ • y) := by
            have := IsLUB.mul_left hr' hy
            convert this
            · have (r : R ) (M : Set R ) : (fun b ↦ r * b) '' (M) = r • M := by
                exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1)
              specialize this r⁻¹ (r • (φ '' P))
              rw [this]
              rw [hphi]
              exact Eq.symm (inv_smul_smul₀ hzero (⇑φ '' P))
            · rw[smul_eq_mul]
          rw [hphi] at hyy
          exact hyy
        apply hP'
        exact Exists.intro (r⁻¹ • y) hyr
      have hPr : (r • P).Nonempty := by
        exact Set.Nonempty.smul_set hP
      rw [supportFunction_of_nonempty_of_not_exists_isLUB hPr hnon]


open scoped Pointwise Classical in
/-- Version of `supportFunction_smul` allowing for `P` to be empty, but asking for positive `R`. -/
lemma supportFunction_smul_set_of_pos {P : Set V} {r : R} (hr : 0 < r) (φ : Module.Dual R V) :
supportFunction R (r • P) φ = r * (supportFunction R P φ) := by
  by_cases! hP : P.Nonempty
  · apply supportFunction_smul_set_of_nonneg hr.le hP
  · have hPr : r • P = ∅ := by
      exact Set.smul_set_eq_empty.mpr hP
    rw [hPr, hP]
    rw [supportFunction_empty]
    simp only [Pi.bot_apply]
    refine Eq.symm (WithBotTop.mul_bot ?_)
    · have hrr := WithBotTop.coe_lt_coe.mpr hr
      exact Ne.symm (Std.ne_of_lt hrr)

-- additivity: TODO write down!

/-
supportFunction of Minkowski sum  ---> Rockefeller's book?

Note: this will require some hypotheses about boundedness of sets
Perhaps add a typeclass "every bounded set has a least upper bound" (which is satisfied for
e.g. `ℝ`), and prove a version of this lemma without this hypothesis.
Asked on Zulip about a name for this concept, and if this already exists:
https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Every.20bounded.20above.20set.20has.20a.20least.20upper.20bound
-/

/- ## Convex closure -/
-- TODO: figure out the right variables to use!

-- if V has a nice topology... we can define convexClosure, and should have the following
-- P a set in the convex space, with a topology
-- (and hope that if V is a module, we have a convex space)


section

-- before: variable {R V Q W : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
-- [AddCommMonoid V] [Module R V][CommSemiring Q] [PartialOrder Q] [IsStrictOrderedRing Q]
-- [Convexity.ConvexSpace Q W]
-- now: We want that our R-module is a convex space. For this we need [CommRing R], [AddCommGroup V]
-- TODO: We have to check again!!!!

variable {R V Q W : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [Convexity.ConvexSpace R V]
  [CommSemiring Q] [PartialOrder Q] [IsStrictOrderedRing Q] [Convexity.ConvexSpace Q W]

/- lemma supportFunctionConvexHull (P : Set V) :
    supportFunction R P = supportFunction R (Convexity.convexHull R P) := by
    -- we have to cast the module R V into a ConvexSpace R V
    -- this should be doable with Mathlib.Geometry.Convex.ConvexSpace.Module
    sorry

    -- idea: prove two inequalities
    -- first follows by inclusion, the other with convex_convexHull_eq and linearity
    -- convex_convexHull_eq only exists for the Analysis definition
    -- there should be convex_convexHull_eq for convex spaces
  -- sorry -/

lemma supportFunctionAffineConvexHull (P : Set W) :
    supportFunctionAffine Q P = supportFunctionAffine Q (Convexity.convexHull Q P) := by
    by_cases! hP: P = ∅
    · rw[hP]
      simp
    ·
      sorry
    -- what is the convex hull of ∅
    --> this is ∅ and therefore compatible with our definition (see convexHull_empty)
    -- check compatibility with our junk value definition
    -- "good" remaining case should be then the normal proof

-----
-- to shorten the following proof, we need theorems about upper bounds on convex hulls
lemma supportFunctionAffineConvexHull_2 (P : Set W) (φ : ConvexSpace.dual Q W) :
    supportFunctionAffine Q P φ = supportFunctionAffine Q (Convexity.convexHull Q P) (φ):= by
    by_cases! hP : P.Nonempty
    · by_cases hP' : ∃ x, IsLUB (φ '' P) x
      · obtain ⟨x, hx⟩ := hP'
        have hx' : IsLUB (φ '' Convexity.convexHull Q P) x := by
          rw[Convexity.IsAffineMap.image_convexHull]
          · refine isLUB_iff_le_iff.mpr ?_
            intro b
            constructor
            · intro hb
              rw [isLUB_iff_le_iff] at hx
              specialize hx b
              have hx' := hx.mp hb
              rw [mem_upperBounds_iff_subset_Iic] at hx' ⊢
              apply Convexity.convexHull_min hx'
              refine Convexity.IsConvexSet.of_sConvexComb_mem ?_
              intro w hw
              change w.sConvexComb ≤ b
              rw [Convexity.sConvexComb_eq_sum]
              calc
                w.weights.sum (fun q r => r • q) ≤ w.weights.sum (fun _ r => r • b) := by
                  apply Finsupp.sum_le_sum
                  intro q hq
                  have hqb : q ≤ b := hw hq
                  exact smul_le_smul_of_nonneg_left hqb (w.weights_nonneg q)
                _ = (w.weights.sum fun _ r => r) • b := by
                  simp only [Finsupp.sum]
                  rw [Finset.sum_smul]
                _ = b := by
                  rw [w.total, one_smul]
            · intro hb
              rw [isLUB_iff_le_iff] at hx
              specialize hx b
              have hPP : ⇑φ '' P ⊆ Convexity.convexHull Q (⇑φ '' P) := by simp
              have h := upperBounds_mono_set hPP
              have hh : b ∈ upperBounds (⇑φ '' P) := by
                apply Set.mem_of_subset_of_mem h hb
              have := hx.mpr hh
              exact this
          · exact Convexity.ConvexSpace.AffineMap.isAffineMap φ
        rw [supportFunctionAffine_of_nonempty_of_isLUB hP hx]
        rw [supportFunctionAffine_of_nonempty_of_isLUB _ hx']
        simp only [Convexity.convexHull_nonempty]
        exact hP
      · rw[supportFunctionAffine_of_nonempty_of_not_exists_isLUB hP hP']
        have h : ¬ ∃ x, IsLUB (φ '' Convexity.convexHull Q P) x := by
          rw [φ.isAffineMap.image_convexHull P]
          intro hex
          apply hP'
          rcases hex with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          have hub : upperBounds (Convexity.convexHull Q (φ '' P)) = upperBounds (φ '' P) := by
            refine Set.ext ?_
            intro x
            constructor
            · have hPP : ⇑φ '' P ⊆ Convexity.convexHull Q (⇑φ '' P) := by simp
              have h := upperBounds_mono_set hPP
              intro hx
              have hh : x ∈ upperBounds (⇑φ '' P) := by
                apply Set.mem_of_subset_of_mem h hx
              exact hh
            · intro hx
              rw [mem_upperBounds_iff_subset_Iic] at hx ⊢
              apply Convexity.convexHull_min hx
              refine Convexity.IsConvexSet.of_sConvexComb_mem ?_
              intro w hw
              change w.sConvexComb ≤ x
              rw [Convexity.sConvexComb_eq_sum]
              calc
                w.weights.sum (fun q r => r • q) ≤ w.weights.sum (fun _ r => r • x) := by
                  apply Finsupp.sum_le_sum
                  intro q hq
                  have hqb : q ≤ x := hw hq
                  exact smul_le_smul_of_nonneg_left hqb (w.weights_nonneg q)
                _ = (w.weights.sum fun _ r => r) • x := by
                  simp only [Finsupp.sum]
                  rw [Finset.sum_smul]
                _ = x := by
                  rw [w.total, one_smul]
          unfold IsLUB at hx
          rw [hub] at hx
          exact hx
        rw[supportFunctionAffine_of_nonempty_of_not_exists_isLUB _ h]
        simp only [Convexity.convexHull_nonempty]
        exact hP
    · rw [hP]
      rw [Convexity.convexHull_empty]


end

def convexClosure (P : Set V) : Set V := sorry

-- split into convex hull, and one statement about topological closure

example {P : Set V} : supportFunction R P = supportFunction R (convexClosure P) := sorry



-- example: over ℚ, take P = (0, √2) ∩ ℚ ⊆ ℚ.
-- (is not a polytope, but perhaps still an interesting set)
-- check: is a convex set over ℚ (?!)
-- our current definition returns either 0 (for a negative rational number) or "the junk value 37"
-- convex closure is (to be filled in)

/-- The interval `(0, √2) ∩ ℚ ⊆ ℚ`, whose support function is a test case for the
"special junk value" in our definition of support functions. -/
def funkySet : Set ℚ := { q | 0 < q ∧ q ^2 < 2}

instance : IsStrictOrderedRing ℚ where
  add_le_add_left a b hab c := by gcongr
  le_of_add_le_add_left a b c h := Rat.add_le_add_left.mp h
  mul_lt_mul_of_pos_left a ha b c h := (Rat.mul_lt_mul_left ha).mpr h
  mul_lt_mul_of_pos_right c hc a b h := (Rat.mul_lt_mul_right hc).mpr h

lemma isConvex_funkySet : Convexity.IsConvexSet ℚ funkySet := by
  sorry

lemma supportFunction_funkySet : supportFunction ℚ funkySet = sorry := sorry

end linear
