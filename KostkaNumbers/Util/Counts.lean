/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib


namespace Multiset

section Counts

variable {α : Type*} [DecidableEq α] (M : Multiset α)

def counts : Multiset ℕ := Multiset.map (fun x : α => Multiset.count x M) M.dedup

@[simp] lemma zero_notMem_counts : 0 ∉ M.counts := by simp [counts]

@[simp] lemma counts_pos (n : ℕ) (hn : n ∈ M.counts) : n > 0 := by
  grind [zero_notMem_counts]

lemma bot_counts_iff : M.counts = ⊥ ↔ M = ⊥ := by
  simp [counts, dedup_eq_zero]

lemma sum_counts_eq_card : M.counts.sum = M.card := by
  simp only [counts, Finset.sum_multiset_map_count, toFinset_dedup, count_dedup, smul_eq_mul,
    ite_mul, one_mul, zero_mul,
    ← Multiset.sum_count_eq_card (s := M.toFinset) (m := M) (by simp)]
  exact Finset.sum_congr rfl (by grind)

lemma counts_card : M.counts.card = M.toFinset.card := by
  simp only [counts, card_map]
  rfl

lemma counts_replicate {n : ℕ} (a : α) (hn : n ≠ 0) : (replicate n a).counts = {n} := by
  simp_rw [counts, count_replicate, map_eq_singleton]
  use a
  simp [← nsmul_singleton, dedup_nsmul hn]

-- upstream (and fix List.replicate_dedup)
lemma replicate_dedup {x : α} {k : ℕ} (h : k ≠ 0) : (replicate k x).dedup = {x} := by
  simp [← coe_replicate, List.replicate_dedup h]

lemma replicate_add_counts_of_notMem {a : α} {M : Multiset α} {n : ℕ} (h : a ∉ M) (hn : n ≠ 0) :
    ((replicate n a) + M).counts = {n} + M.counts := by
  simp only [counts, count_add, count_replicate]
  ext m
  rw [count_add, count_map, count_map, Disjoint.dedup_add, replicate_dedup hn, filter_add,
    card_add]
  · by_cases hmn : m = n
    · simp only [hmn, nodup_singleton, mem_singleton, count_eq_one_of_mem]
      · congr 2
        · rw [card_eq_one]
          use a
          simp [h]
        · exact filter_congr (by grind [mem_dedup])
    · rw [← count_pos, Nat.pos_iff_ne_zero] at h
      push Not at h
      simp only [filter_singleton, ↓reduceIte, h, add_zero, hmn, empty_eq_zero, card_zero,
        mem_singleton, not_false_eq_true, count_eq_zero_of_notMem]
      congr 2
      refine filter_congr ?_
      intro x hx
      have hax : a ≠ x := by
        rw [mem_dedup, ← count_pos, Nat.pos_iff_ne_zero] at hx
        grind
      simp [hax]
  · refine disjoint_left.mpr ?_
    simp_all [mem_replicate]


end Counts

end Multiset
