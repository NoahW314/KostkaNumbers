import Mathlib
import KostkaNumbers.InequalitySpecial
import KostkaNumbers.ComputationProof.HookLengthComputation
import KostkaNumbers.ComputationProof.Partition
import KostkaNumbers.ComputationProof.Computation
import KostkaNumbers.InequalityTwoRows

open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n : ℕ}



theorem kostka_ineq_221 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hn : n = 5) (hμ : μ = {2, 2, 1}) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  let h5 := partition5 (Multiset.ofList γ.rowLens) ?_ ?_
  swap
  · simp [Multiset.sum_coe, ← card_eq_sum_rowLens, h, hμ]
  swap
  · simp only [Multiset.mem_coe, gt_iff_lt]
    exact γ.pos_of_mem_rowLens
  by_cases hd : ¬ γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)
  · exact kostka_ineq_not_dominate hd h h0

  push_neg at hd
  rcases h5 with h5 | h5 | h5 | h5 | h5 | h5 | h5
  · rw [ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens, hn] at hhd
    · rw [Multiset.coe_eq_singleton] at h5
      contradiction
    · rw [hn]; norm_num
  · suffices γ = hookDiagram 5 by
      rw [← hn] at this
      refine kostka_ineq_hook ?_ this h h0
      rw [hn]; norm_num
    rw [← rowLens_eq_iff', h5, hookDiagram_rowLens]
    · rfl
    · norm_num
  · have h5' : γ = ofRowLens [3, 2] (by simp) := by
      rw [← rowLens_eq_iff', rowLens_ofRowLens_eq_self, h5]
      · rfl
      · simp
    rw [hμ, h5', hn, kostka_32]
    refine le_trans (Nat.mul_le_mul_left _ kostka_g32u221_le) ?_
    norm_num
  · have h5' : γ = ofRowLens [3,1,1] (by simp) := by
      rw [← rowLens_eq_iff', rowLens_ofRowLens_eq_self, h5]
      · rfl
      · simp
    rw [hμ, h5', hn, kostka_311, kostka_g311u221]
    norm_num
  · have h5' : γ = ofRowLens [2,2,1] (by simp) := by
      rw [← rowLens_eq_iff', rowLens_ofRowLens_eq_self, h5]
      · rfl
      · simp
    rw [hμ, ← h5, kostka_self, h5, hn, h5', kostka_221]
    norm_num
  · have h5' : γ.rowLens = [2, 1, 1, 1] := by
      refine List.eq_of_perm_of_sorted ?_ γ.rowLens_sorted ?_
      · rw [← Multiset.coe_eq_coe, h5]
        rfl
      · simp
    rw [← Multiset.coe_toList μ, Multiset.coe_sort, hμ, sort_triple_ge (by rfl) (by norm_num),
      h5', quad_dominates_triple] at hd
    simp at hd
  · suffices γ = verticalDiagram 5 by
      rw [← hn] at this
      exact kostka_ineq_vertical this h h0
    rw [← rowLens_eq_iff', h5, verticalDiagram_rowLens]
    rfl



@[simp] lemma min_el_triple {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    min_el ({a, b, c} : Multiset ℕ) (by simp) = c := by
  suffices min_el (Multiset.ofList (({a, b, c} : Multiset ℕ)).toList) (by simp) = c by
    simp only [Multiset.coe_toList] at this
    exact this
  unfold min_el
  simp only [Multiset.coe_sort, sort_triple_ge hab hbc]
  simp


theorem kostka_ineq_222 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hn : n = 6) (hμ : μ = {2, 2, 2}) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  let h6 := partition6 (Multiset.ofList γ.rowLens) ?_ ?_
  swap
  · rw [Multiset.sum_coe, ← card_eq_sum_rowLens, h, hμ]
    norm_num
  swap
  · simp only [Multiset.mem_coe, gt_iff_lt]
    exact γ.pos_of_mem_rowLens
  by_cases hd : ¬ γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)
  · exact kostka_ineq_not_dominate hd h h0

  push_neg at hd
  rcases h6 with h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6
  · rw [Multiset.coe_eq_singleton] at h6
    rw [ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens, hn] at hhd
    · contradiction
    · positivity
  · have h6' : γ = hookDiagram 6 := by
      rw [← rowLens_eq_iff', hookDiagram_rowLens, h6]
      rfl
      norm_num
    rw [← hn] at h6'
    refine kostka_ineq_hook ?_ h6' h h0
    rw [hn]; norm_num

  · have hγ : γ.rowLens = [n - 2, 2] := by
      rw [hn]; norm_num1
      refine List.eq_of_perm_of_sorted ?_ γ.rowLens_sorted (by simp)
      rw [← Multiset.coe_eq_coe, h6]
      rfl
    refine kostka_ineq_two_rows hγ ?_ (by norm_num) ?_ h ?_ ?_
    · rw [hn]; norm_num1
    · rw [card_eq_sum_rowLens, hγ, hn]
      norm_num
    · simp [hμ]
    · simp only [min_el_triple (by rfl) (by rfl), hμ]
      rfl

  · have h6' : γ = ofRowLens [4, 1, 1] (by simp) := by
      rw [← rowLens_eq_iff', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    rw [hμ, h6', hn, kostka_411, kostka_g411u222]
    norm_num
  · have h6' : γ = ofRowLens [3, 3] (by simp) := by
      rw [← rowLens_eq_iff', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    rw [hμ, h6', hn, kostka_33, kostka_g33u222]
    norm_num
  · have h6' : γ = ofRowLens [3, 2, 1] (by simp) := by
      rw [← rowLens_eq_iff', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    rw [hμ, h6', hn, kostka_321]
    refine le_trans (Nat.mul_le_mul_left _ kostka_g321u222_le) ?_
    norm_num

  · have h6' : γ.rowLens = [3, 1, 1, 1] := by
      refine List.eq_of_perm_of_sorted ?_ γ.rowLens_sorted ?_
      · rw [← Multiset.coe_eq_coe, h6]
        rfl
      · simp
    rw [← Multiset.coe_toList μ, Multiset.coe_sort, hμ, h6',
      sort_triple_ge (by rfl) (by rfl), quad_dominates_triple] at hd
    simp at hd

  · have h6' : γ = ofRowLens [2, 2, 2] (by simp) := by
      rw [← rowLens_eq_iff', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    rw [hn, hμ, ← h6, kostka_self, h6, h6', kostka_222]
    norm_num

  · have h6' : γ.rowLens = [2, 2, 1, 1] := by
      refine List.eq_of_perm_of_sorted ?_ γ.rowLens_sorted ?_
      · rw [← Multiset.coe_eq_coe, h6]
        rfl
      · simp
    rw [← Multiset.coe_toList μ, Multiset.coe_sort, hμ, h6',
      sort_triple_ge (by rfl) (by rfl), quad_dominates_triple] at hd
    simp at hd
  · have h6' : γ.rowLens = [2, 1, 1, 1, 1] := by
      refine List.eq_of_perm_of_sorted ?_ γ.rowLens_sorted ?_
      · rw [← Multiset.coe_eq_coe, h6]
        rfl
      · simp
    rw [← Multiset.coe_toList μ, Multiset.coe_sort, hμ, h6',
      sort_triple_ge (by rfl) (by rfl)] at hd
    apply sum_three_le_of_dominates at hd
    simp at hd
  · have h6' : γ = verticalDiagram 6 := by
      rw [← rowLens_eq_iff', h6, verticalDiagram_rowLens]
      rfl
    rw [← hn] at h6'
    exact kostka_ineq_vertical h6' h h0
