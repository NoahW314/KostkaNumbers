import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.RestrictExtend

open YoungDiagram SemistandardYoungTableau Kostka

namespace YoungDiagram

def hookLength (γ : YoungDiagram) (i j : ℕ) : ℕ :=
  (γ.rowLen i - (j + 1)) + (γ.colLen j - (i + 1)) + 1

@[simp] lemma hookLength_def (γ : YoungDiagram) (i j : ℕ) :
    γ.hookLength i j = (γ.rowLen i - (j + 1)) + (γ.colLen j - (i + 1)) + 1 := by rfl


def IsCornerCell (γ : YoungDiagram) (x : ℕ × ℕ) :=
  x.2 + 1 = γ.rowLen x.1 ∧ x.1 + 1 = γ.colLen x.2

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
    split_ifs with hij
    · obtain ⟨hxi, hxj⟩ := hij
      subst hxi
      simp only [hook, ge_iff_le, Finset.mem_filter, mem_cells, true_and, le_refl] at hx
      obtain ⟨hx, _⟩ := hx
      rw [γ.mem_iff_lt_rowLen] at hx
      omega
    · have hij' : (x.1 ≥ i ∧ x.2 = j) := by
        simp only [hook, ge_iff_le, Finset.mem_filter, mem_cells] at hx
        omega
      obtain ⟨hxi, hxj⟩ := hij'
      subst hxj
      simp only [hook, ge_iff_le, Finset.mem_filter, mem_cells, le_refl, and_true] at hx
      obtain ⟨hx, _⟩ := hx
      rw [γ.mem_iff_lt_colLen] at hx
      omega
  constructor
  · intro x hx y hy hf
    simp_all [hook, f]
    rw [Prod.ext_iff]
    obtain ⟨hxγ, hx⟩ := hx
    obtain ⟨hyγ, hy⟩ := hy
    split_ifs at hf with hx' hy' hy'
    · omega
    · obtain ⟨hxi, hxj⟩ := hx'
      subst hxi
      rw [γ.mem_iff_lt_rowLen] at hxγ
      omega
    · obtain ⟨hyi, hyj⟩ := hy'
      subst hyi
      rw [γ.mem_iff_lt_rowLen] at hyγ
      omega
    · omega
  · intro a
    simp only [hookLength_def, Finset.coe_range, Set.mem_Iio, ge_iff_le, hook, Finset.coe_filter,
      mem_cells, Set.mem_image, Set.mem_setOf_eq, Prod.exists, f]
    intro ha
    by_cases hah : a ≤ γ.rowLen i - (j + 1)
    · use i; use (a + j)
      simp only [le_add_iff_nonneg_left, zero_le, and_self, le_refl, Nat.add_eq_right, true_and,
        true_or, and_true, ↓reduceIte, add_tsub_cancel_right]
      rw [γ.mem_iff_lt_rowLen]
      rw [γ.mem_iff_lt_rowLen] at h
      omega
    · use (a - (γ.rowLen i - (j + 1)) + i); use j
      simp [γ.mem_iff_lt_colLen, show a - (γ.rowLen i - (j + 1)) ≠ 0 by omega]
      omega

lemma corner_iff_hookLength_eq_one (γ : YoungDiagram) (x : ℕ × ℕ) (hx : x ∈ γ) :
    γ.IsCornerCell x ↔ γ.hookLength x.1 x.2 = 1 := by
  simp only [IsCornerCell, hookLength_def, Nat.add_eq_right, Nat.add_eq_zero]
  have hx2 := hx
  rw [γ.mem_iff_lt_rowLen] at hx
  rw [γ.mem_iff_lt_colLen] at hx2
  omega

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
  omega

end YoungDiagram
