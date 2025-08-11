import Mathlib
import KostkaNumbers.KostkaPos
import KostkaNumbers.HookDiagram
import KostkaNumbers.HorizontalDiagram

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

lemma rowLens_eq_iff {γ γ' : YoungDiagram} : γ.rowLens = γ'.rowLens ↔ γ = γ' := by
  constructor; swap
  · intro h; rw [h]
  intro h
  ext x
  by_cases hx : x.1 < γ.rowLens.length
  · rw [mem_cells, mem_iff_lt_rowLen, ← get_rowLens]
    · simp only [h]
      rw [get_rowLens, ← mem_iff_lt_rowLen, ← mem_cells]
      exact hx
  · let hx' := hx
    rw [length_rowLens, ← mem_iff_lt_colLen] at hx
    rw [h, length_rowLens, ← mem_iff_lt_colLen] at hx'
    have hxm : x ∉ γ := by
      contrapose! hx
      exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) hx
    have hxm' : x ∉ γ':= by
      contrapose! hx'
      exact γ'.up_left_mem (by rfl) (Nat.zero_le x.2) hx'
    simp only [mem_cells, hxm, hxm']

lemma kostka_ineq_singleton {n : ℕ} (hγ : γ ≠ horizontalDiagram n) (hμ : μ = {n})
    (h : γ.card = μ.sum) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  by_cases h0 : n = 0
  · simp only [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, h0, Finset.range_zero,
      Finset.product_empty, Finset.map_empty, Finset.union_idempotent, ne_eq] at hγ
    rw [hμ, h0, Multiset.sum_singleton, Finset.card_eq_zero] at h
    contrapose! hγ
    ext x
    simp [h]
  · by_cases hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ
    · have hhd : γ = horizontalDiagram n := by
        rw [← rowLens_eq_iff, horizontalDiagram, rowLens_ofRowLens_eq_self]
        · suffices γ.rowLens.length = 1 by
            refine List.eq_of_sum_take_eq ?_ ?_
            · rw [List.length_cons, List.length_nil, zero_add]
              exact this
            · rw [this]
              intro i hi
              by_cases hi0 : i = 0
              · simp [hi0]
              · have hi1 : i = 1 := by omega
                rw [hi1]
                let this2 := this
                rw [List.length_eq_one_iff] at this
                obtain ⟨m, hm⟩ := this
                simp [hm]
                rw [hμ, card_eq_sum_rowLens, Multiset.sum_singleton] at h
                rw [← h]
                symm
                rw [Finset.sum_eq_single_of_mem (⟨0, by rw [this2]; exact zero_lt_one⟩ :
                  Fin γ.rowLens.length) ?_ ?_]
                · simp [hm]
                · simp
                · intro ⟨x, hx⟩
                  rw [this2, Nat.lt_one_iff] at hx
                  simp [hx]

          apply lengths_le_of_dominates at hd
          specialize hd ?_ ?_
          · rw [← Fin.sum_univ_getElem]
            simp only [← List.get_eq_getElem]
            rw [← card_eq_sum_rowLens, h]
            nth_rw 2 [← Multiset.coe_toList μ]
            rw [Multiset.coe_sort, ← Multiset.sum_coe]
            congr
            nth_rw 1 [← Multiset.coe_toList μ, Multiset.coe_eq_coe]
            refine List.Perm.symm ?_
            exact List.mergeSort_perm _ _
          · intro i
            refine pos_of_mem_rowLens γ (γ.rowLens.get i) ?_
            exact List.get_mem γ.rowLens i
          rw [hμ, Multiset.length_sort, Multiset.card_singleton] at hd
          refine antisymm hd ?_
          contrapose! h0
          rw [hμ, Multiset.sum_singleton, card_eq_sum_rowLens] at h
          rw [Nat.lt_one_iff] at h0
          rw [← h]
          refine Finset.sum_eq_zero ?_
          intro ⟨x, hx⟩
          rw [h0] at hx
          contradiction
        · simp [Nat.pos_iff_ne_zero, h0]
      contradiction
    · refine kostka_ineq_not_dominate hd h ?_
      rw [hμ, Multiset.mem_singleton]
      push_neg; symm; exact h0


lemma kostka_ineq_replicate {n : ℕ} (hμ : μ = Multiset.replicate n 1) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  rw [hμ, Multiset.card_replicate]



/-lemma kostka_ineq_replicate' {n : ℕ} (hγ : γ = verticalDiagram n)
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  rw [hγ]
  sorry
-/
