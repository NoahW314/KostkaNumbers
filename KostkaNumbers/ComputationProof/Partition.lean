/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Util.Util


/-
Utility Theorems
-/

lemma ne_nil_of_sum_ne_zero {μ : Multiset ℕ} {n : ℕ} (h : μ.sum = n)
    (hn : n ≠ 0) : μ.toList ≠ [] := by
  rw [ne_eq, Multiset.toList_eq_nil]
  contrapose! hn
  rw [← h, hn, Multiset.sum_zero]

lemma sum_max_erase {μ : Multiset ℕ} {n : ℕ} (h : μ.sum = n) (hμ : μ.toList ≠ []) :
    (μ.erase (μ.toList.max hμ)).sum = n - (μ.toList.max hμ) := by
  have hm : (μ.toList.max hμ) ∈ μ.toList := List.max_mem hμ
  rw [Multiset.mem_toList] at hm
  rw [← h, ← Multiset.sum_erase hm, add_comm, add_tsub_cancel_right]

lemma pos_of_max_erase {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (hp : ∀ x ∈ μ, x > 0) :
    ∀ x ∈ (μ.erase (μ.toList.max hμ)), x > 0 := by
  intro x hx
  exact hp x (Multiset.mem_of_mem_erase hx)

lemma erase_ne_cons_of_lt_max {μ ν : Multiset ℕ} {a n : ℕ} (hμ : μ.toList ≠ [])
    (h : μ.toList.max hμ = n) (ha : n < a) : μ.erase n ≠ a ::ₘ ν := by
  contrapose! ha
  rw [← h]
  refine List.le_max_of_mem ?_
  rw [Multiset.mem_toList]
  exact Multiset.mem_of_mem_erase <| ha ▸ Multiset.mem_cons_self a ν

lemma singleton_lt_max {μ : Multiset ℕ} {a n : ℕ} (hμ : μ.toList ≠ [])
    (h : μ.toList.max hμ = n) (ha : n < a) : μ.erase n ≠ {a} := by
  simpa using erase_ne_cons_of_lt_max (ν := 0) hμ h ha


/-
Enumeration of the partitions for n ≤ 6
-/

lemma partition0 (μ : Multiset ℕ) (h : μ.sum = 0) (hp : ∀ x ∈ μ, x > 0) :
    μ = 0 := by
  apply Multiset.card_le_sum at hp
  rwa [h, Nat.le_zero, Multiset.card_eq_zero] at hp

theorem partition1 (μ : Multiset ℕ) (h : μ.sum = 1) (hp : ∀ x ∈ μ, x > 0) :
    μ = {1} := by
  have hμ := ne_nil_of_sum_ne_zero h one_ne_zero
  have hμ' : μ.toList.max hμ ∈ μ := by rw [← Multiset.mem_toList]; exact List.max_mem hμ
  have hml : μ.toList.max hμ > 0 := hp (μ.toList.max hμ) hμ'
  have hmu : μ.toList.max hμ ≤ 1 := h ▸ Multiset.le_sum_of_mem hμ'
  have hms := sum_max_erase h hμ
  have hmp := pos_of_max_erase hμ hp
  rw [← Multiset.cons_erase hμ']
  interval_cases hm : μ.toList.max hμ
  · ring_nf at hms
    have h0 := partition0 (μ.erase 1) hms hmp
    simp [h0]

theorem partition2 (μ : Multiset ℕ) (h : μ.sum = 2) (hp : ∀ x ∈ μ, x > 0) :
    μ = {2} ∨ μ = {1, 1} := by
  have hμ := ne_nil_of_sum_ne_zero h two_ne_zero
  have hμ' : μ.toList.max hμ ∈ μ := by rw [← Multiset.mem_toList]; exact List.max_mem hμ
  have hml : μ.toList.max hμ > 0 := hp (μ.toList.max hμ) hμ'
  have hmu : μ.toList.max hμ ≤ 2 := h ▸ Multiset.le_sum_of_mem hμ'
  have hms := sum_max_erase h hμ
  have hmp := pos_of_max_erase hμ hp
  rw [← Multiset.cons_erase hμ']
  interval_cases hm : μ.toList.max hμ
  · ring_nf at hms
    simp [partition1 (μ.erase 1) hms hmp]
  · ring_nf at hms
    simp [partition0 (μ.erase 2) hms hmp]

theorem partition3 (μ : Multiset ℕ) (h : μ.sum = 3) (hp : ∀ x ∈ μ, x > 0) :
    μ = {3} ∨ μ = {2, 1} ∨ μ = {1, 1, 1} := by
  have hμ := ne_nil_of_sum_ne_zero h three_ne_zero
  have hμ' : μ.toList.max hμ ∈ μ := by rw [← Multiset.mem_toList]; exact List.max_mem hμ
  have hml : μ.toList.max hμ > 0 := hp (μ.toList.max hμ) hμ'
  have hmu : μ.toList.max hμ ≤ 3 := h ▸ Multiset.le_sum_of_mem hμ'
  have hms := sum_max_erase h hμ
  have hmp := pos_of_max_erase hμ hp
  rw [← Multiset.cons_erase hμ']
  interval_cases hm : μ.toList.max hμ
  · ring_nf at hms
    have h2 := partition2 (μ.erase 1) hms hmp
    simp [singleton_lt_max hμ hm] at h2
    simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 2) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 3) hms hmp
    simp [h0]

theorem partition4 (μ : Multiset ℕ) (h : μ.sum = 4) (hp : ∀ x ∈ μ, x > 0) :
    μ = {4} ∨ μ = {3, 1} ∨ μ = {2, 2} ∨ μ = {2, 1, 1} ∨ μ = {1, 1, 1, 1} := by
  have hμ := ne_nil_of_sum_ne_zero h four_ne_zero
  have hμ' : μ.toList.max hμ ∈ μ := by rw [← Multiset.mem_toList]; exact List.max_mem hμ
  have hml : μ.toList.max hμ > 0 := hp (μ.toList.max hμ) hμ'
  have hmu : μ.toList.max hμ ≤ 4 := h ▸ Multiset.le_sum_of_mem hμ'
  have hms := sum_max_erase h hμ
  have hmp := pos_of_max_erase hμ hp
  rw [← Multiset.cons_erase hμ']
  interval_cases hm : μ.toList.max hμ
  · ring_nf at hms
    have h3 := partition3 (μ.erase 1) hms hmp
    simp [singleton_lt_max hμ hm, erase_ne_cons_of_lt_max hμ hm] at h3
    simp [h3]
  · ring_nf at hms
    have h2 := partition2 (μ.erase 2) hms hmp
    rcases h2 with h2 | h2 <;> simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 3) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 4) hms hmp
    simp [h0]

theorem partition5 (μ : Multiset ℕ) (h : μ.sum = 5) (hp : ∀ x ∈ μ, x > 0) :
    μ = {5} ∨ μ = {4, 1} ∨ μ = {3, 2} ∨ μ = {3, 1, 1} ∨ μ = {2, 2, 1} ∨
    μ = {2, 1, 1, 1} ∨ μ = {1, 1, 1, 1, 1} := by
  have hμ := ne_nil_of_sum_ne_zero h (by norm_num)
  have hμ' : μ.toList.max hμ ∈ μ := by rw [← Multiset.mem_toList]; exact List.max_mem hμ
  have hml : μ.toList.max hμ > 0 := hp (μ.toList.max hμ) hμ'
  have hmu : μ.toList.max hμ ≤ 5 := h ▸ Multiset.le_sum_of_mem hμ'
  have hms := sum_max_erase h hμ
  have hmp := pos_of_max_erase hμ hp
  rw [← Multiset.cons_erase hμ']
  interval_cases hm : μ.toList.max hμ
  · ring_nf at hms
    have h4 := partition4 (μ.erase 1) hms hmp
    simp [singleton_lt_max hμ hm, erase_ne_cons_of_lt_max hμ hm] at h4
    simp [h4]
  · ring_nf at hms
    have h3 := partition3 (μ.erase 2) hms hmp
    simp only [Nat.lt_add_one, singleton_lt_max hμ hm, Multiset.insert_eq_cons, false_or] at h3
    rcases h3 with h3 | h3 <;> simp [h3]
  · ring_nf at hms
    have h2 := partition2 (μ.erase 3) hms hmp
    rcases h2 with h2 | h2 <;> simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 4) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 5) hms hmp
    simp [h0]


theorem partition6 (μ : Multiset ℕ) (h : μ.sum = 6) (hp : ∀ x ∈ μ, x > 0) :
    μ = {6} ∨ μ = {5, 1} ∨ μ = {4, 2} ∨ μ = {4, 1, 1} ∨ μ = {3, 3} ∨ μ = {3, 2, 1} ∨
    μ = {3, 1, 1, 1} ∨ μ = {2, 2, 2} ∨ μ = {2, 2, 1, 1} ∨ μ = {2, 1, 1, 1, 1} ∨
    μ = {1, 1, 1, 1, 1, 1} := by
  have hμ := ne_nil_of_sum_ne_zero h (by norm_num)
  have hμ' : μ.toList.max hμ ∈ μ := by rw [← Multiset.mem_toList]; exact List.max_mem hμ
  have hml : μ.toList.max hμ > 0 := hp (μ.toList.max hμ) hμ'
  have hmu : μ.toList.max hμ ≤ 6 := h ▸ Multiset.le_sum_of_mem hμ'
  have hms := sum_max_erase h hμ
  have hmp := pos_of_max_erase hμ hp
  rw [← Multiset.cons_erase hμ']
  interval_cases hm : μ.toList.max hμ
  · ring_nf at hms
    have h5 := partition5 (μ.erase 1) hms hmp
    simp [singleton_lt_max hμ hm, erase_ne_cons_of_lt_max hμ hm] at h5
    simp [h5]
  · ring_nf at hms
    have h4 := partition4 (μ.erase 2) hms hmp
    simp only [Nat.reduceLT, singleton_lt_max hμ hm, Multiset.insert_eq_cons, Nat.lt_add_one,
      erase_ne_cons_of_lt_max hμ hm, false_or] at h4
    rcases h4 with h4 | h4 | h4 <;> simp [h4]
  · ring_nf at hms
    have h3 := partition3 (μ.erase 3) hms hmp
    rcases h3 with h3 | h3 | h3 <;> simp [h3]
  · ring_nf at hms
    have h2 := partition2 (μ.erase 4) hms hmp
    rcases h2 with h2 | h2 <;> simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 5) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 6) hms hmp
    simp [h0]
