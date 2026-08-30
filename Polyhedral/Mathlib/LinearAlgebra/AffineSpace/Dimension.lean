/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
## (Finite) Dimension of an affine subspace

This file defines the dimension of affine subspace to be `⊥` for the empty subspace,
and otherwise equal to the `Module.rank` of the direction of the subspace. The finite dimension
is similary defined using `Module.finrank`.

## Main definitions

* `AffineSubspace.dim`: Dimension expressed as `WithBot Cardinal`
* `AffineSubspace.findim`: Dimension expressed as `WithBot ℕ` with a junk value of 0 for infinite
  dimensional spaces.

## TODO

* Relate `dim`/`findim` to `AffineBasis`
* All of `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean` needs to be audited and possibly
  integrated with this file. i.e. `Collinear`/`Coplanar` should be redefined. Should other lemmas
  be re-stated?
-/

namespace AffineSubspace

universe u v v' a a'

variable {R : Type u} {V : Type v} {V' : Type v'} {A : Type a} {A' : Type a'}
variable [AddCommGroup V] [AddTorsor V A] [AddCommGroup V'] [AddTorsor V' A']

section Ring

variable [Ring R] [Module R V] [Module R V']
variable {s t : AffineSubspace R A}

-- TODO: Should live with definition of direction
@[simp]
theorem direction_eq_bot_iff : s.direction = ⊥ ↔ (s : Set A).Subsingleton := by
  simp [AffineSubspace.direction]

-- TODO: Should live with definiton of Singleton until it goes upstream
@[simp]
theorem singleton_ne_bot (x : A) : ({x} : AffineSubspace R A) ≠ ⊥ := by
  simp [← coe_eq_bot_iff]

-- TODO: Useful below but looks like it shouldn't be
@[simp]
theorem direction_singleton_eq_bot (x : A) : ({x} : AffineSubspace R A).direction = ⊥ := by
  simp

@[simp]
theorem coe_affineSpan_eq_singleton_iff {s : Set A} (x : A) : affineSpan R s = {x} ↔ s = {x} := by
  refine ⟨fun h ↦ ?_, by simp +contextual [AffineSubspace.ext_iff]⟩
  refine Set.Nonempty.subset_singleton_iff ?_ |>.mp (by simpa using affineSpan_le.mp h.le)
  exact affineSpan_nonempty R |>.mp (by simp [h])

@[simp]
theorem _root_.WithBot.unbot_natCast (n : ℕ) (hn : (n : WithBot ℕ) ≠ ⊥) :
    (n : WithBot ℕ).unbot hn = n := by
  rfl

@[simp]
theorem _root_.WithBot.map_eq_unbot_of_ne_bot
    {α β : Type*} (f : α → β) (a : WithBot α) (ha : a ≠ ⊥) :
    WithBot.map f a = f (a.unbot ha) := by
  grind [WithBot.map_eq_some_iff, WithBot.coe_unbot]

open Module in
theorem _root_.Module.rank_eq_natCast_finrank
    {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (hn : finrank R M ≠ 0) : Module.rank R M = Module.finrank R M :=
  (Cardinal.toNat_eq_iff hn).mp rfl

open Classical in
/-- The dimension of `s` is equal to `⊥` if `s = ⊥`, and otherwise it is equal to the dimension of
`s` interpreted as a linear space. -/
noncomputable def dim (s : AffineSubspace R A) : WithBot Cardinal :=
  if s = ⊥ then ⊥
  else Module.rank R s.direction

/-- The dimension of `s` is equal to `⊥` if `s = ⊥`, and otherwise it is equal to the finite
dimension of `s` interpreted as a linear space. Note that this inherits `Module.finrank`s junk
value: `AffineSubspace.findim s = 0` for infinite dimensional subspaces. -/
noncomputable def findim (s : AffineSubspace R A) : WithBot ℕ :=
  WithBot.map Cardinal.toNat (dim s)

@[simp]
theorem dim_bot : dim (⊥ : AffineSubspace R A) = ⊥ := by
  simp [dim]

@[simp]
theorem findim_bot : findim (⊥ : AffineSubspace R A) = ⊥ := by
  simp [findim]

@[simp]
theorem dim_singleton [Nontrivial R] (x : A) :
    dim ({x} : AffineSubspace R A) = 0 := by
  dsimp [dim]
  rw [direction_singleton_eq_bot]
  simp

@[simp]
theorem findim_singleton [Nontrivial R] (x : A) : findim ({x} : AffineSubspace R A) = 0 := by
  simp [findim]

@[simp]
theorem dim_eq_bot_iff : dim s = ⊥ ↔ s = ⊥ := by
  simp [dim]

@[simp]
theorem findim_eq_bot_iff : findim s = ⊥ ↔ s = ⊥ := by
  simp [findim]

theorem dim_ne_bot_iff : dim s ≠ ⊥ ↔ (s : Set A).Nonempty := by
  contrapose!
  simp

theorem findim_ne_bot_iff : findim s ≠ ⊥ ↔ (s : Set A).Nonempty := by
  contrapose!
  simp

theorem dim_eq_rank (h : s ≠ ⊥) : dim s = Module.rank R s.direction := by
  simpa [dim]

theorem findim_eq_finrank (h : s ≠ ⊥) : findim s = Module.finrank R s.direction := by
  simp [findim, dim_eq_rank h]
  norm_cast

theorem findim_eq_finrank_of_not_finite [Module.Free R s.direction] [StrongRankCondition R]
    (h : ¬Module.Finite R s.direction) : findim s = 0 := by
  by_cases hs : s = ⊥
  · rw [hs, direction_bot] at h
    exact False.elim <| h <| Module.Finite.bot ..
  rw [findim_eq_finrank hs, Nat.cast_eq_zero]
  exact Module.finrank_of_not_finite h

@[simp]
theorem dim_lt_aleph0 [StrongRankCondition R] (s : AffineSubspace R A)
    [Module.Finite R s.direction] : dim s < Cardinal.aleph0 := by
  dsimp [dim]
  split_ifs <;> simp [Module.rank_lt_aleph0]

theorem finite_iff_dim_lt_aleph0 [StrongRankCondition R] (s : AffineSubspace R A)
    [Module.Free R s.direction] :
    Module.Finite R s.direction ↔ dim s < Cardinal.aleph0 := by
  refine ⟨fun h ↦ dim_lt_aleph0 s, fun h ↦ ?_⟩
  rcases eq_or_ne s ⊥ with rfl | hs
  · rw [direction_bot]
    infer_instance
  · exact Module.rank_lt_aleph0_iff.mp (by simpa [dim_eq_rank hs] using h)

theorem finite_of_findim_ne_zero [StrongRankCondition R] (s : AffineSubspace R A)
    [Module.Free R s.direction] (h : findim s ≠ 0) : Module.Finite R s.direction := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · rw [direction_bot]
    infer_instance
  exact Module.finite_of_finrank_pos <| Nat.pos_of_ne_zero (by simpa [findim_eq_finrank hs] using h)

theorem findim_eq_map_dim_toNat : findim s = (dim s).map Cardinal.toNat := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [findim, dim_eq_rank hs]

theorem dim_eq_findim_unbot (hs : s ≠ ⊥) [StrongRankCondition R] [Module.Finite R s.direction] :
    dim s = (findim s).unbot (by simpa) := by
  simp only [dim_eq_rank hs, findim, WithBot.map_coe, WithBot.unbot_coe]
  norm_cast
  refine (Cardinal.cast_toNat_of_lt_aleph0 ?_).symm
  exact Module.rank_lt_aleph0 R ↥s.direction

@[mono]
theorem dim_mono (h : s ≤ t) : dim s ≤ dim t := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [dim_eq_rank hs, dim_eq_rank (ne_bot_of_le_ne_bot hs h),
    Submodule.rank_mono (direction_le h)]

@[mono]
theorem findim_mono [StrongRankCondition R] [Module.Finite R t.direction] (h : s ≤ t) :
    findim s ≤ findim t := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [findim_eq_finrank hs, findim_eq_finrank (ne_bot_of_le_ne_bot hs h),
    Submodule.finrank_mono (direction_le h)]

theorem map_lift_dim_map_le (f : A →ᵃ[R] A') (s : AffineSubspace R A) :
    WithBot.map Cardinal.lift.{v} (map f s).dim ≤
      WithBot.map Cardinal.lift.{v'} s.dim := by
  by_cases hs : map f s = ⊥
  · simp [hs]
  rw [dim_eq_rank hs, dim_eq_rank (by contrapose! hs; simpa), map_direction]
  simp [lift_rank_map_le]

theorem findim_map_le_findim [StrongRankCondition R] (f : A →ᵃ[R] A') (s : AffineSubspace R A)
    [Module.Finite R s.direction] : (map f s).findim ≤ s.findim := by
  by_cases hs : (map f s) = ⊥
  · simp [hs]
  rw [findim_eq_finrank hs, findim_eq_finrank (by contrapose! hs; simpa), map_direction]
  simp [Submodule.finrank_map_le]

theorem map_lift_dim_map_eq_of_injective {f : A →ᵃ[R] A'} (hf : Function.Injective f)
    (s : AffineSubspace R A) :
    WithBot.map Cardinal.lift.{v} (map f s).dim =
      WithBot.map Cardinal.lift.{v'} s.dim := by
  by_cases hs : map f s = ⊥
  · simp_all
  rw [dim_eq_rank hs, dim_eq_rank (by contrapose! hs; simpa), map_direction]
  simp only [WithBot.map_coe, WithBot.coe_inj]
  refine LinearEquiv.lift_rank_eq <| (Submodule.equivMapOfInjective _ ?_ _).symm
  exact (AffineMap.linear_injective_iff f).mpr hf

theorem findim_map_eq_findim_of_injective {f : A →ᵃ[R] A'} (hf : Function.Injective f)
    (s : AffineSubspace R A) : (map f s).findim = s.findim := by
  by_cases hs : map f s = ⊥
  · simp_all
  rw [findim_eq_finrank hs, findim_eq_finrank (by contrapose! hs; simpa), map_direction]
  norm_cast
  refine LinearEquiv.finrank_eq <| (Submodule.equivMapOfInjective _ ?_ _).symm
  exact (AffineMap.linear_injective_iff f).mpr hf

@[simp]
theorem dim_le_zero_iff_subsingleton [IsDomain R] [Module.IsTorsionFree R s.direction] :
    dim s ≤ 0 ↔ (s : Set A).Subsingleton := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [dim_eq_rank, hs, rank_zero_iff, Submodule.subsingleton_iff_eq_bot]

@[simp]
theorem findim_le_zero_iff_subsingleton [StrongRankCondition R] [IsDomain R]
    [Module.IsTorsionFree R s.direction] [Module.Finite R s.direction] :
    findim s ≤ 0 ↔ (s : Set A).Subsingleton := by
  by_cases hs : s = ⊥
  · simp [hs]
  simp [findim_eq_finrank, hs, Module.finrank_zero_iff, Submodule.subsingleton_iff_eq_bot]

end Ring

section DivisionRing

variable [DivisionRing R] [Module R V]
variable {s t : AffineSubspace R A}

@[mono]
theorem findim_strictMono [Module.Finite R t.direction] (h : s < t) : findim s < findim t := by
  by_cases hs : s = ⊥
  · rw [hs, bot_lt_iff_ne_bot] at h
    simpa [hs, bot_lt_iff_ne_bot]
  rw [findim_eq_finrank hs, findim_eq_finrank (ne_bot_of_gt h), Nat.cast_lt]
  refine Submodule.finrank_lt_finrank_of_lt (direction_lt_of_nonempty h ?_)
  exact (nonempty_iff_ne_bot _).mpr hs

@[simp]
theorem dim_eq_zero_iff : dim s = 0 ↔ ∃ x : A, s = {x} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h₁ : (s : Set A).Nonempty := dim_ne_bot_iff.mp (by simp [h])
    have h₂ := dim_le_zero_iff_subsingleton.mp (le_of_eq h)
    obtain ⟨x, hx⟩ := Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨h₁, h₂⟩
    exact ⟨x, (AffineSubspace.ext_iff _ _).mpr hx⟩
  · obtain ⟨x, rfl⟩ := h
    simp [dim]

@[simp]
theorem findim_eq_zero_iff [Module.Finite R s.direction] : findim s = 0 ↔ ∃ x : A, s = {x} := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simpa using fun x ↦ Ne.symm (singleton_ne_bot _)
  simp [findim, show s.dim ≠ ⊥ by simpa, WithBot.unbot_eq_iff]

-------------------------------------------------------------------------------------------
section MathlibPR43230

-- non-sorry'd version in PR
theorem finite_of_fin_dim_affineIndependent' {ι : Type*} {p : ι → A}
    [FiniteDimensional R (vectorSpan R (Set.range p))] (hi : AffineIndependent R p) :
    Finite ι := by
  sorry

variable (R) in
/-- An affine-independent subset of an affine space whose spanned direction is finite-dimensional
is finite. -/
theorem finite_set_of_fin_dim_affineIndependent' {ι : Type*} {s : Set ι} {f : s → A}
    [FiniteDimensional R (vectorSpan R (Set.range f))]
    (hi : AffineIndependent R f) : s.Finite :=
  @Set.toFinite _ s (finite_of_fin_dim_affineIndependent' hi)

end MathlibPR43230

-- TODO should be stated for `dim` in terms of cardinal and then re-derived for findim?
-- TODO: Weaken V being finite dimensional to (affineSpan R s).direction being finite.
theorem exists_affineIndependent_of_finiteDimensional'' (s : Set A)
    [FiniteDimensional R (vectorSpan R s)] :
    ∃ t ⊆ s, affineSpan R t = affineSpan R s ∧ AffineIndependent R ((↑) : t → A) ∧
      t.ncard = (affineSpan R s).findim.succ := by
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_affineIndependent R V s
  refine ⟨t, ht1, ht2, ht3, ?_⟩
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp_all
  rw [findim_eq_finrank (by simpa [← Set.nonempty_iff_ne_empty]), ← ht2, direction_affineSpan,
    WithBot.succ_natCast]
  have : FiniteDimensional R (vectorSpan R (Set.range ((↑) : t → A))) := by
    rwa [Subtype.range_coe, ← direction_affineSpan, ht2, direction_affineSpan]
  have := finite_set_of_fin_dim_affineIndependent' R ht3
  have := finite_of_fin_dim_affineIndependent' ht3
  have := Set.Finite.fintype this
  have : t.ncard ≠ 0 := by
    grind [Set.ncard_eq_zero, affineSpan_eq_bot, Set.not_nonempty_empty]
  have := ht3.finrank_vectorSpan (n := t.ncard - 1) (by simp [Nat.sub_one_add_one this])
  rw [Subtype.range_coe] at this
  lia
-------------------------------------------------------------------------------------------

@[simp]
theorem finrank_vectorSpan_pair {x y : A} (h : x ≠ y) :
    Module.finrank R (vectorSpan R {x, y}) = 1 :=
  Matrix.range_cons_cons_empty .. ▸ (affineIndependent_of_ne R h).finrank_vectorSpan (by simp)

@[simp]
theorem rank_vectorSpan_pair {x y : A} (h : x ≠ y) :
    Module.rank R (vectorSpan R {x, y}) = 1 :=
  Module.rank_eq_one_iff_finrank_eq_one.mpr (finrank_vectorSpan_pair h)

-- TOOD: Derive from a exists_affineIndependent analog?
theorem dim_eq_one_iff :
    dim s = 1 ↔ ∃ x y : s, x ≠ y ∧ s = affineSpan R {x.1, y.1} := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simp
  rw [dim_eq_rank hs, WithBot.coe_eq_one]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := Module.finite_of_rank_eq_one h
    rw [direction_eq_vectorSpan] at this
    obtain ⟨t, h₁, _, _, h₂⟩ := exists_affineIndependent_of_finiteDimensional'' (R := R) (s : Set A)
    obtain ⟨x, y, _, ht⟩ :=
      Set.ncard_eq_two.mp (by simpa [findim_eq_map_dim_toNat, dim_eq_rank hs, h] using h₂)
    exact ⟨⟨x, h₁ (by simp [ht])⟩, ⟨y, h₁ (by simp [ht])⟩, by simp_all⟩
  · obtain ⟨_, _, h₁, h₂⟩ := h
    rw [Module.rank_eq_one_iff_finrank_eq_one, h₂, direction_affineSpan]
    exact finrank_vectorSpan_pair (by simpa)

theorem findim_eq_one_iff :
    findim s = 1 ↔ ∃ x y : s, x ≠ y ∧ s = affineSpan R {x.1, y.1} := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simp
  rw [findim_eq_finrank hs, Nat.cast_eq_one, ← Module.rank_eq_one_iff_finrank_eq_one]
  simpa [dim_eq_rank hs] using dim_eq_one_iff (s := s)

end DivisionRing

end AffineSubspace
