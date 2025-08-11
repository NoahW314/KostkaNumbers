import Mathlib
import KostkaNumbers.Dominate
import KostkaNumbers.Recursion


open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ ν : Multiset ℕ}


/-
theorem kostka_antitone_of_card_eq (h : Multiset.sort (· ≥ ·) μ ⊵ Multiset.sort (· ≥ ·) ν)
    (hl : μ.card = ν.card) (hsum : μ.sum = ν.sum) (hsum' : γ.card = μ.sum) :
    kostkaNumber γ μ ≤ kostkaNumber γ ν := by
  sorry

theorem kostka_antitone (h : Multiset.sort (· ≥ ·) μ ⊵ Multiset.sort (· ≥ ·) ν)
    (hsum : μ.sum = ν.sum) : kostkaNumber γ μ ≤ kostkaNumber γ ν := by
  by_cases hsum' : γ.card = μ.sum; swap
  · rw [kostka_ne_card γ μ hsum']
    exact Nat.zero_le (kostkaNumber γ ν)

  by_cases hl : μ.card = ν.card
  · exact kostka_antitone_of_card_eq h hl hsum hsum'

  let hl' := lengths_le_of_dominates h ?_ ?_
  swap
  · sorry
  swap
  · sorry

  simp only [ge_iff_le, Multiset.length_sort] at hl'

  sorry
-/
