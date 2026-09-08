/-
Copyright (c) 2026 Louis Theran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Theran
-/

import Mathlib.Order.KrullDimension

/-! # Atoms have height one

`Order.isAtom_iff_height_eq_one`: in a preorder with a bottom element, an element is an atom iff
its `Order.height` is exactly `1`. -/

namespace Order

variable {α : Type*} [PartialOrder α] [OrderBot α] {a : α}

theorem isAtom_iff_height_eq_one : IsAtom a ↔ height a = 1 := by
  constructor
  · intro ha
    have h0 : height a ≠ 0 := fun h => ha.1 (isMin_iff_eq_bot.mp (height_eq_zero.mp h))
    have h1 : height a ≤ 1 := by
      have h1' : height a ≤ ((1 : ℕ) : ℕ∞) := by
        rw [height_le_coe_iff]
        intro y hy
        rw [ha.2 y hy, height_bot]
        exact zero_lt_one
      simpa using h1'
    rcases h1.lt_or_eq with hlt | heq
    · exact absurd (Order.lt_one_iff.mp hlt) h0
    · exact heq
  · intro h1
    have hane : a ≠ ⊥ := by
      intro hbot
      rw [hbot, height_bot] at h1
      exact absurd h1 zero_ne_one
    refine ⟨hane, fun b hb => ?_⟩
    have h1' : height a ≤ ((1 : ℕ) : ℕ∞) := by rw [h1]; simp
    rw [height_le_coe_iff] at h1'
    have hblt : height b < ((1 : ℕ) : ℕ∞) := h1' b hb
    have hb0 : height b = 0 := Order.lt_one_iff.mp (by simpa using hblt)
    exact isMin_iff_eq_bot.mp (height_eq_zero.mp hb0)

end Order
