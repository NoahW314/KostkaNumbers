/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib

namespace Multiset

section Remove

variable {α : Type*} [DecidableEq α] (S : Multiset α) (a : α)

def remove := S - (replicate (count a S) a)

@[simp] lemma remove_bot : remove (⊥ : Multiset α) a = ⊥ := by
  simp [remove]

@[simp] lemma remove_zero : remove 0 a = 0 := by
  simp [remove]

@[grind ., simp]
lemma notMem_of_remove : a ∉ S.remove a := by
  simp [remove, ← count_eq_zero]

lemma remove_of_notMem (ha : a ∉ S) : S.remove a = S := by
  rw [← count_pos, Nat.pos_iff_ne_zero] at ha
  push Not at ha
  rw [remove, ha, replicate_zero, Multiset.sub_zero]

lemma mem_remove_of_ne {a b : α} (h : a ≠ b) : b ∈ S.remove a ↔ b ∈ S := by
  simp [remove, mem_sub, count_replicate, h, count_pos]

variable {S : Multiset α} {a b : α}

lemma mem_remove_of_mem (b : α) (h : a ∈ S) : a ∈ S.remove b ↔ b ≠ a := by
  grind [mem_remove_of_ne]

lemma mem_of_mem_remove (h : b ∈ S.remove a) : b ∈ S := by
  rw [← count_pos]
  rw [remove, mem_sub] at h
  exact lt_of_le_of_lt (Nat.zero_le _) h

lemma insert_remove_toFinset (ha : a ∈ S) : insert a (S.remove a).toFinset = S.toFinset := by
  grind [mem_of_mem_remove, mem_remove_of_ne]

@[grind =]
lemma remove_toFinset (S : Multiset α) (a : α) : (S.remove a).toFinset = S.toFinset.erase a := by
  by_cases ha : a ∈ S
  · grind [insert_remove_toFinset]
  · grind [remove_of_notMem]

lemma remove_toFinset_card (S : Multiset α) (a : α) (ha : a ∈ S) :
    (S.remove a).toFinset.card = S.toFinset.card - 1 := by grind

lemma remove_zero_sum (μ : Multiset ℕ) : μ.sum = (μ.remove 0).sum := by
  by_cases! h0 : 0 ∉ μ
  · rw [remove_of_notMem μ 0 h0]
  simp only [Finset.sum_multiset_count, smul_eq_mul, remove, count_sub, count_replicate]
  rw [← insert_remove_toFinset h0, Finset.sum_insert_zero]
  · exact Finset.sum_congr rfl (by grind)
  · rw [mul_zero]

lemma cons_remove {μ : Multiset ℕ} (a : ℕ) : (a ::ₘ μ).remove a = μ.remove a := by
  simp [Multiset.remove]

lemma sub_card_le_card {s t : Multiset α} : (s - t).card ≤ s.card := by
  exact card_le_card <| Multiset.sub_le_self s t

lemma remove_card_le_card {μ : Multiset α} {a : α} : (μ.remove a).card ≤ μ.card := by
  simp [Multiset.remove, sub_card_le_card]

end Remove

end Multiset
