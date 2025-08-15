import Mathlib
import KostkaNumbers.KostkaPos
import KostkaNumbers.HookDiagram
import KostkaNumbers.HorizontalDiagram
import KostkaNumbers.VerticalDiagram

open Kostka SemistandardYoungTableau YoungDiagram

variable {γ : YoungDiagram} {μ : Multiset ℕ}

lemma kostka_ineq_not_dominate {n : ℕ} (hd : ¬ γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ)
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  rw [← kostka_pos_iff_dominates h h0, Nat.pos_iff_ne_zero] at hd
  push_neg at hd
  rw [hd, mul_zero]
  exact Nat.zero_le ((μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1))


lemma kostka_ineq_hook {n : ℕ} (hn : n ≥ 2) (hγ : γ = hookDiagram n)
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  have hnc : γ.card = n := by rw [hγ, hookDiagram_card]
  rw [hγ]; nth_rw 2 [← hnc]
  rw [h, kostka_hook μ h0, mul_comm, kostka_hook_replicate n hn]
  rw [← h, hnc]; exact hn





lemma rowLens_dominates_card_iff {n : ℕ} (h : γ.card = n) : ([n] ⊴ γ.rowLens) ↔
    γ = horizontalDiagram n := by
  by_cases hn : n = 0
  · rw [hn, horizontalDiagram_zero, eq_bot_iff_card_eq_zero, h]
    simp [hn]

  constructor
  · intro hd
    rw [← rowLens_eq_iff, horizontalDiagram_rowLens hn, ← dominates_singleton_iff ?_ hn]
    · exact hd
    · intro i
      refine γ.pos_of_mem_rowLens _ ?_
      exact List.getElem_mem (Fin.val_lt_of_le i (le_refl γ.rowLens.length))
    · rw [← h, card_eq_sum_rowLens]
  · intro hd
    rw [hd, horizontalDiagram_rowLens hn]
    exact dominates_self

lemma kostka_ineq_singleton {n : ℕ} (hγ : γ ≠ horizontalDiagram n) (hμ : μ = {n})
    (h : γ.card = μ.sum) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  have h0 : n ≠ 0 := by
    contrapose! hγ
    rw [hγ, horizontalDiagram_zero, eq_bot_iff_card_eq_zero, h, hμ, hγ, Multiset.sum_singleton]

  by_cases hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ
  swap
  · refine kostka_ineq_not_dominate hd h ?_
    rw [hμ, Multiset.mem_singleton]
    push_neg; symm; exact h0
  · suffices γ = horizontalDiagram n by contradiction
    simp only [ge_iff_le, hμ, Multiset.sort_singleton, Multiset.sum_singleton,
      h, rowLens_dominates_card_iff] at hd h
    exact hd



lemma kostka_ineq_replicate {n : ℕ} (hμ : μ = Multiset.replicate n 1) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  rw [hμ, Multiset.card_replicate]


lemma kostka_ineq_vertical {n : ℕ} (hγ : γ = verticalDiagram n)
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  by_cases hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ
  swap
  · exact kostka_ineq_not_dominate hd h h0
  · rw [hγ, verticalDiagram_rowLens] at hd
    rw [hγ, verticalDiagram_card] at h
    symm at h
    rw [replicate_one_dominates_iff, Multiset.sort_eq_replicate_iff] at hd
    · exact kostka_ineq_replicate hd
    · rw [Multiset.sort_sum, h]
    · intro i hi
      rw [Multiset.mem_sort] at hi
      contrapose! h0
      rw [Nat.le_zero] at h0
      rw [← h0]
      exact hi
