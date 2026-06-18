/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.RestrictExtend

open YoungDiagram SemistandardYoungTableau Kostka

namespace YoungDiagram

def hookLength (γ : YoungDiagram) (i j : ℕ) : ℕ :=
  (γ.rowLen i - (j + 1)) + (γ.colLen j - (i + 1)) + 1

@[simp] lemma hookLength_def (γ : YoungDiagram) (i j : ℕ) :
    γ.hookLength i j = (γ.rowLen i - (j + 1)) + (γ.colLen j - (i + 1)) + 1 := by rfl


-- def IsCornerCell (γ : YoungDiagram) (x : ℕ × ℕ) :=
--   x.2 + 1 = γ.rowLen x.1 ∧ x.1 + 1 = γ.colLen x.2

def corners (γ : YoungDiagram) : Finset (ℕ × ℕ) :=
    {x ∈ γ.cells | x.2 + 1 = γ.rowLen x.1 ∧ x.1 + 1 = γ.colLen x.2}

def hook (γ : YoungDiagram) (i j : ℕ) : Finset (ℕ × ℕ) :=
    {x ∈ γ.cells | ((x.1 = i ∧ x.2 ≥ j) ∨ (x.1 ≥ i ∧ x.2 = j))}

lemma self_mem_hook (γ : YoungDiagram) (i j : ℕ) (h : (i, j) ∈ γ) :
    (i, j) ∈ γ.hook i j := by simp [hook, h]

lemma hook_card_eq_hookLength (γ : YoungDiagram) (i j : ℕ) (h : (i, j) ∈ γ) :
    (γ.hook i j).card = γ.hookLength i j := by
  let f : ℕ × ℕ → ℕ :=
    fun x ↦ if (x.1 = i ∧ x.2 ≥ j) then x.2 - j else γ.rowLen i - (j + 1) + x.1 - i
  conv => rhs; rw [← Finset.card_range (γ.hookLength i j)]
  refine Set.BijOn.finsetCard_eq f ?_
  constructor
  · intro x hx
    rw [Finset.mem_coe] at hx
    simp only [hookLength_def, Finset.coe_range, ge_iff_le, Set.mem_Iio, f]
    grind [γ.mem_iff_lt_colLen, γ.mem_iff_lt_rowLen, hook, mem_cells]
  constructor
  · grind [γ.mem_iff_lt_rowLen, hook, mem_cells, Set.InjOn]
  · intro a
    simp only [hookLength_def, Finset.coe_range, Set.mem_Iio, ge_iff_le, hook, Finset.coe_filter,
      mem_cells, Set.mem_image, Set.mem_setOf_eq, Prod.exists, f]
    intro ha
    by_cases hah : a ≤ γ.rowLen i - (j + 1)
    · use i, (a + j)
      simp only [le_add_iff_nonneg_left, zero_le, and_self, le_refl, Nat.add_eq_right, true_and,
        true_or, and_true, ↓reduceIte, add_tsub_cancel_right]
      rw [γ.mem_iff_lt_rowLen] at h ⊢
      lia
    · use (a - (γ.rowLen i - (j + 1)) + i), j
      grind [γ.mem_iff_lt_colLen]

lemma corner_iff_hookLength_eq_one (γ : YoungDiagram) (x : ℕ × ℕ) (hx : x ∈ γ) :
    (x.2 + 1 = γ.rowLen x.1 ∧ x.1 + 1 = γ.colLen x.2) ↔ γ.hookLength x.1 x.2 = 1 := by
  grind [γ.mem_iff_lt_rowLen, γ.mem_iff_lt_colLen, hookLength_def]

lemma hookLength_ne_zero (γ : YoungDiagram) (i j : ℕ) (h : (i, j) ∈ γ) : γ.hookLength i j ≠ 0 := by
  rw [← Nat.pos_iff_ne_zero, ← hook_card_eq_hookLength _ _ _ h]
  refine Finset.card_pos.mpr ?_
  use (i, j)
  exact γ.self_mem_hook i j h

lemma exists_hook_of_hookLength_ne_one (γ : YoungDiagram) (i j : ℕ) (hij : (i, j) ∈ γ)
    (h : γ.hookLength i j ≠ 1) : ∃ x ∈ γ.hook i j, x ≠ (i, j) := by
  refine Finset.exists_mem_ne ?_ (i, j)
  rw [hook_card_eq_hookLength _ _ _ hij]
  have hhl := γ.hookLength_ne_zero i j hij
  lia

end YoungDiagram
