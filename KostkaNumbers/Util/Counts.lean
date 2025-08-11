import Mathlib


namespace Multiset

section Counts

variable {α : Type*} [DecidableEq α]

def counts (M : Multiset α) : Multiset ℕ :=
  Multiset.map (fun x : α => Multiset.count x M) M.dedup

@[simp] lemma zero_notMem_counts {M : Multiset α} : 0 ∉ M.counts := by simp [counts]

@[simp] lemma counts_pos {M : Multiset α} : ∀ n ∈ M.counts, n > 0 := by
  intro n; rw [gt_iff_lt, Nat.pos_iff_ne_zero]
  contrapose!; intro h; rw [h]; exact zero_notMem_counts

lemma bot_counts_iff {M : Multiset ℕ} : M.counts = ⊥ ↔ M = ⊥ := by
  simp [counts, dedup_eq_zero]

lemma sum_counts_eq_card (M : Multiset ℕ) : Multiset.sum M.counts = M.card := by
  simp [counts]
  rw [Finset.sum_multiset_map_count]
  simp [Multiset.count_dedup]
  have hms : ∀ a ∈ M, a ∈ M.toFinset := by simp
  rw [← Multiset.sum_count_eq_card hms]
  apply Finset.sum_congr (rfl)
  intro x hx; rw [mem_toFinset] at hx
  simp only [hx, reduceIte]

lemma counts_card (M : Multiset ℕ) : M.counts.card = M.toFinset.card := by
  simp [counts]
  exact rfl

lemma counts_replicate (n a : ℕ) (hn : n ≠ 0) : (Multiset.replicate n a).counts = {n} := by
  simp only [counts, count_replicate]
  refine map_eq_singleton.mpr ?_
  use a; constructor
  · rw [← nsmul_singleton]
    rw [dedup_nsmul hn, dedup_singleton]
  · simp


lemma replicate_dedup {α : Type*} [DecidableEq α] (a : α) (n : ℕ) (h : n ≠ 0) :
    (replicate n a).dedup = {a} := by
  ext b
  by_cases hab : a = b
  · simp [hab, mem_replicate, h]
  · push_neg at hab; symm at hab
    simp [hab, mem_replicate]

lemma replicate_add_counts_of_notMem {a : α} {M : Multiset α} (h : a ∉ M) (n : ℕ) (hn : n ≠ 0) :
    ((replicate n a) + M).counts = M.counts + {n} := by
  simp [counts, count_replicate]
  ext m
  rw [count_add, count_map, count_map]
  rw [Disjoint.dedup_add, replicate_dedup a n hn, filter_add, card_add, add_comm]
  · by_cases hmn : m = n
    · simp [hmn]
      · congr 2
        · refine filter_congr ?_
          intro x hx
          rw [mem_dedup] at hx
          have hax : a ≠ x := by contrapose! h; rw [h]; exact hx
          simp [hax]
        · rw [card_eq_one]; use a
          rw [filter_eq_self]
          simp [h]
    · rw [← count_pos, Nat.pos_iff_ne_zero] at h; push_neg at h
      simp [hmn, filter_singleton, h]
      congr 1
      refine filter_congr ?_
      intro x hx
      rw [mem_dedup] at hx
      have hax : a ≠ x := by
        rw [← count_pos, Nat.pos_iff_ne_zero] at hx
        contrapose! hx
        rw [← hx]; exact h
      simp [hax]
  · refine disjoint_left.mpr ?_
    intro b hb
    rw [mem_replicate] at hb
    simp only [ne_eq, hn, not_false_eq_true, true_and] at hb
    rw [hb]; exact h


end Counts

end Multiset
