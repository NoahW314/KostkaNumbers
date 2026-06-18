/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.InequalitySpecial
import KostkaNumbers.ComputationProof.Partition
import KostkaNumbers.ComputationProof.Computation
import KostkaNumbers.ComputationProof.HookLengthComputation

open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n : ℕ}

theorem kostka_ineq_small2 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hγ : γ.card = n) (hn : n = 2) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  subst hn
  have hp2 := partition2 μ ?_ (by grind)
  · rcases hp2 with hp2 | hp2
    · exact kostka_ineq_singleton hhd hp2 h
    · exact kostka_ineq_replicate (by simp [hp2])
  · rw [← h, hγ]

theorem kostka_ineq_small3 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hγ : γ.card = n) (hn : n = 3) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  subst hn
  have hp3 := partition3 (Multiset.ofList (γ.rowLens)) ?_ γ.pos_of_mem_rowLens
  · rcases hp3 with h3 | h3 | h3
    · simp only [Multiset.coe_eq_singleton] at h3
      rw [ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens (by norm_num)] at hhd
      contradiction
    · refine kostka_ineq_hook (by norm_num) ?_ h h0
      rw [← rowLens_eq_iff', h3, hookDiagram_rowLens]
      · rfl
      · norm_num
    · refine kostka_ineq_vertical ?_ h h0
      rw [← rowLens_eq_iff', h3, verticalDiagram_rowLens, Multiset.coe_replicate]
      rfl
  · rw [Multiset.sum_coe, ← card_eq_sum_rowLens, hγ]

theorem kostka_ineq_small4 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hsq : γ ≠ ofRowLens [2, 2] (sorted_pair (by rfl)) ∨ μ ≠ {2, 2})
    (hγ : γ.card = n) (hn : n = 4) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  subst hn
  by_cases! hd : ¬ γ.rowLens ⊵ μ.sort (· ≥ ·)
  · exact kostka_ineq_not_dominate hd h h0
  by_cases hμ1 : μ = {1, 1, 1, 1}
  · refine kostka_ineq_replicate ?_
    rw [hμ1]
    rfl
  have hp4 := partition4 (Multiset.ofList γ.rowLens) ?_ γ.pos_of_mem_rowLens
  · rcases hp4 with h4 | h4 | h4 | h4 | h4
    · rw [Multiset.coe_eq_singleton] at h4
      rw [ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens (by norm_num)] at hhd
      contradiction
    · refine kostka_ineq_hook (by norm_num) ?_ h h0
      rw [← rowLens_eq_iff', h4, hookDiagram_rowLens]
      · rfl
      · norm_num
    · have hμ4 := partition4 μ (by rw [← h, hγ]) (by grind)
      have h4 : γ.rowLens = [2, 2] := by
        refine List.Perm.eq_of_pairwise' γ.rowLens_sorted.pairwise
          (sorted_pair (by rfl)).pairwise ?_
        rwa [← Multiset.coe_eq_coe]
      · rcases hμ4 with hμ4 | hμ4 | hμ4 | hμ4 | hμ4
        · simp [hμ4, Multiset.sort_singleton, h4, pair_dominates_singleton] at hd
        · rw [hμ4, sort_pair_ge (by norm_num), h4] at hd
          simp [pair_dominates_pair] at hd
        · rw [hμ4, ne_eq, ← rowLens_eq_iff, rowLens_ofRowLens_eq_self, h4] at hsq
          · contradiction
          · simp
        · have hγ4 : γ = ofRowLens [2, 2] (sorted_pair (by rfl)) := by
            simp [← rowLens_eq_iff, rowLens_ofRowLens_eq_self, h4]
          rw [hγ4, hμ4, kostka_22, kostka_g22u211]
          norm_num
        · contradiction
    · have hμ4 := partition4 μ (by rw [← h, hγ]) (by grind)
      have h4' : γ.rowLens = [2, 1, 1] := by
        refine List.Perm.eq_of_pairwise' γ.rowLens_sorted.pairwise
          (sorted_triple (by norm_num) (by rfl)).pairwise ?_
        rwa [← Multiset.coe_eq_coe]
      · rcases hμ4 with hμ4 | hμ4 | hμ4 | hμ4 | hμ4
        · simp [hμ4, Multiset.sort_singleton, h4', triple_dominates_singleton] at hd
        · rw [hμ4, sort_pair_ge (by norm_num), h4'] at hd
          simp [triple_dominates_pair] at hd
        · rw [hμ4, sort_pair_ge (by rfl), h4'] at hd
          simp [triple_dominates_pair] at hd
        · have hγ4 : γ = ofRowLens [2, 1, 1] (sorted_triple (by norm_num) (by rfl)) := by
            simp [← rowLens_eq_iff, rowLens_ofRowLens_eq_self, h4']
          rw [hμ4, ← h4, kostka_self, h4, hγ4, kostka_211]
          norm_num
        · contradiction
    · refine kostka_ineq_vertical ?_ h h0
      rw [← rowLens_eq_iff', h4, verticalDiagram_rowLens]
      rfl
  · rw [Multiset.sum_coe, ← card_eq_sum_rowLens, hγ]

theorem kostka_ineq_small (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hsq : γ ≠ ofRowLens [2, 2] (sorted_pair (by rfl)) ∨ μ ≠ {2, 2})
    (hγ : γ.card = n) (hn4 : n ≤ 4) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  interval_cases hn : n
  · simp
  · simp
  · exact kostka_ineq_small2 hhd h h0 hγ (by rfl)
  · exact kostka_ineq_small3 hhd h h0 hγ (by rfl)
  · exact kostka_ineq_small4 hhd h h0 hsq hγ (by rfl)
