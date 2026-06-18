/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Dominate


/-
Small domination results
-/

lemma singleton_dominates_singleton {a b : ℕ} : ([a] ⊴ [b]) ↔ a ≤ b := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp [h]

lemma singleton_dominates_pair {a b c : ℕ} : ([a, b] ⊴ [c]) ↔ a + b ≤ c := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h] <;> lia

lemma singleton_dominates_triple {a b c d : ℕ} : ([a, b, c] ⊴ [d]) ↔ a + b + c ≤ d := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa [← add_assoc] using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h] <;> lia



lemma pair_dominates_singleton {a b c : ℕ} : ([a] ⊴ [b, c]) ↔ a ≤ b := by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]

lemma pair_dominates_pair {a b c d : ℕ} : ([a, b] ⊴ [c, d]) ↔ a ≤ c ∧ a + b ≤ c + d := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa using h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h₁, h₂]

lemma pair_dominates_triple {a b c d e : ℕ} : ([a, b, c] ⊴ [d, e]) ↔
    a ≤ d ∧ a + b + c ≤ d + e := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa [add_assoc] using h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂] <;> lia



lemma triple_dominates_singleton {a b c d : ℕ} : ([a] ⊴ [b, c, d]) ↔ a ≤ b := by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]

lemma triple_dominates_pair {a b c d e : ℕ} : ([a, b] ⊴ [c, d, e]) ↔
    a ≤ c ∧ a + b ≤ c + d := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂]

lemma triple_dominates_triple {a b c d e f : ℕ} : ([a, b, c] ⊴ [d, e, f]) ↔
    a ≤ d ∧ a + b ≤ d + e ∧ a + b + c ≤ d + e + f := by
  constructor
  · intro h
    constructor; swap; constructor
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa [← add_assoc] using h
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂, h₃⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂, h₃]


lemma quad_dominates_triple {a b c d e f g : ℕ} : ([a, b, c] ⊴ [d, e, f, g]) ↔
    a ≤ d ∧ a + b ≤ d + e ∧ a + b + c ≤ d + e + f := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    constructor
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
    · refine sum_three_le_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂, h₃⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, Fin.sum_univ_four, h₁, h₂, h₃]
