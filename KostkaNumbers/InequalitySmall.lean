import Mathlib
import KostkaNumbers.InequalitySpecial
import KostkaNumbers.ComputationProof.Partition
import KostkaNumbers.ComputationProof.Computation
import KostkaNumbers.ComputationProof.HookLengthComputation

open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n : ℕ}

lemma forall_pos_of_zero_notMem (h0 : 0 ∉ μ) : ∀ x ∈ μ, x > 0 := by
  intro x hx
  contrapose! h0
  rw [Nat.le_zero] at h0
  rw [← h0]
  exact hx

theorem kostka_ineq_small2 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hγ : γ.card = n) (hn : n = 2) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  let hp2 := partition2 μ ?_ (forall_pos_of_zero_notMem h0)
  · rcases hp2 with hp2 | hp2
    · rw [← hn] at hp2
      exact kostka_ineq_singleton hhd hp2 h
    · suffices μ = Multiset.replicate n 1 by exact kostka_ineq_replicate this
      simp [hn, hp2]
  · rw [← h, hγ, hn]

theorem kostka_ineq_small3 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hγ : γ.card = n) (hn : n = 3) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  let hp3 := partition3 (Multiset.ofList (γ.rowLens)) ?_ ?_
  · rcases hp3 with h3 | h3 | h3
    · simp only [Multiset.coe_eq_singleton] at h3
      rw [hn, ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens (by norm_num)] at hhd
      contradiction
    · suffices γ = hookDiagram 3 by
        rw [← hn] at this
        refine kostka_ineq_hook ?_ this h h0
        rw [hn]; norm_num
      rw [← rowLens_eq_iff', h3, hookDiagram_rowLens]
      · rfl
      · norm_num
    · suffices γ = verticalDiagram 3 by
        rw [← hn] at this
        exact kostka_ineq_vertical this h h0
      rw [← rowLens_eq_iff', h3, verticalDiagram_rowLens, Multiset.coe_replicate]
      simp
  · rw [Multiset.sum_coe, ← card_eq_sum_rowLens, hγ, hn]
  · simp only [Multiset.mem_coe, gt_iff_lt]
    exact γ.pos_of_mem_rowLens


theorem kostka_ineq_small4 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hsq : γ ≠ ofRowLens [2, 2] (by simp) ∨ μ ≠ {2, 2})
    (hγ : γ.card = n) (hn : n = 4) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  by_cases hd : ¬ γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)
  · exact kostka_ineq_not_dominate hd h h0
  by_cases hμ1 : μ = {1, 1, 1, 1}
  · suffices μ = Multiset.replicate 4 1 by
      rw [← hn] at this
      exact kostka_ineq_replicate this
    rw [hμ1]; rfl

  push_neg at hd
  let hp4 := partition4 (Multiset.ofList γ.rowLens) ?_ ?_
  · rcases hp4 with h4 | h4 | h4 | h4 | h4
    · rw [Multiset.coe_eq_singleton] at h4
      rw [hn, ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens (by norm_num)] at hhd
      contradiction
    · suffices γ = hookDiagram 4 by
        rw [← hn] at this
        refine kostka_ineq_hook ?_ this h h0
        rw [hn]; norm_num
      rw [← rowLens_eq_iff', h4, hookDiagram_rowLens]
      · rfl
      · norm_num
    · let hμ4 := partition4 μ ?_ (forall_pos_of_zero_notMem h0)
      swap
      · rw [← h, hγ, hn]
      have h4 : γ.rowLens = [2, 2] := by
        refine List.eq_of_perm_of_sorted ?_ γ.rowLens_sorted ?_
        · rw [← Multiset.coe_eq_coe]; exact h4
        · exact sorted_pair (by norm_num)
      · rcases hμ4 with hμ4 | hμ4 | hμ4 | hμ4 | hμ4
        · simp [hμ4, Multiset.sort_singleton, h4, pair_dominates_singleton] at hd
        · rw [← Multiset.coe_toList μ, Multiset.coe_sort, hμ4,
            sort_pair_ge (by norm_num), h4] at hd
          simp [pair_dominates_pair] at hd
        · rw [hμ4, ne_eq, ← rowLens_eq_iff, rowLens_ofRowLens_eq_self, h4] at hsq
          · contradiction
          · simp
        · have hγ4 : γ = ofRowLens [2, 2] (sorted_pair (by rfl)) := by
            simp [← rowLens_eq_iff, rowLens_ofRowLens_eq_self, h4]
          rw [hn, hγ4, hμ4, kostka_22, kostka_g22u211]
          norm_num
        · contradiction

    · let hμ4 := partition4 μ ?_ (forall_pos_of_zero_notMem h0)
      swap
      · rw [← h, hγ, hn]
      have h4' : γ.rowLens = [2, 1, 1] := by
        refine List.eq_of_perm_of_sorted ?_ γ.rowLens_sorted ?_
        · rw [← Multiset.coe_eq_coe]; exact h4
        · exact sorted_triple (by norm_num) (by rfl)
      · rcases hμ4 with hμ4 | hμ4 | hμ4 | hμ4 | hμ4
        · simp [hμ4, Multiset.sort_singleton, h4', triple_dominates_singleton] at hd
        · rw [← Multiset.coe_toList μ, Multiset.coe_sort, hμ4,
            sort_pair_ge (by norm_num), h4'] at hd
          simp [triple_dominates_pair] at hd
        · rw [← Multiset.coe_toList μ, Multiset.coe_sort, hμ4,
            sort_pair_ge (by rfl), h4'] at hd
          simp [triple_dominates_pair] at hd
        · have hγ4 : γ = ofRowLens [2, 1, 1] (sorted_triple (by norm_num) (by rfl)) := by
            simp [← rowLens_eq_iff, rowLens_ofRowLens_eq_self, h4']
          rw [hn, hμ4, ← h4, kostka_self, h4, hγ4, kostka_211]
          norm_num
        · contradiction

    · suffices γ = verticalDiagram 4 by
        rw [← hn] at this
        exact kostka_ineq_vertical this h h0
      rw [← rowLens_eq_iff', h4, verticalDiagram_rowLens]
      rfl
  · rw [Multiset.sum_coe, ← card_eq_sum_rowLens, hγ, hn]
  · simp only [Multiset.mem_coe, gt_iff_lt]
    exact γ.pos_of_mem_rowLens

theorem kostka_ineq_small (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hsq : γ ≠ ofRowLens [2, 2] (by simp) ∨ μ ≠ {2, 2})
    (hγ : γ.card = n) (hn4 : n ≤ 4) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  interval_cases hn : n
  · simp
  · simp
  · exact kostka_ineq_small2 hhd h h0 hγ (by rfl)
  · exact kostka_ineq_small3 hhd h h0 hγ (by rfl)
  · exact kostka_ineq_small4 hhd h h0 hsq hγ (by rfl)
