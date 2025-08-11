import Mathlib

namespace Multiset

section Remove

variable {α : Type*} [DecidableEq α]

def remove (S : Multiset α) (a : α) := S - (replicate (count a S) a)

@[simp] lemma remove_bot {a : α} : remove (⊥ : Multiset α) a = ⊥ := by
  simp [remove]

@[simp] lemma remove_zero {a : α} : remove 0 a = 0 := by
  simp [remove]

@[simp] lemma notMem_of_remove (S : Multiset α) (a : α) : a ∉ S.remove a := by
  rw [remove, ← count_eq_zero, count_sub, count_replicate]
  simp

lemma remove_of_notMem (S : Multiset α) (a : α) (ha : a ∉ S) : S.remove a = S := by
  rw [← count_pos, Nat.pos_iff_ne_zero] at ha; push_neg at ha
  rw [remove, ha, replicate_zero, Multiset.sub_zero]

lemma mem_remove_of_ne (S : Multiset α) {a b : α} (h : a ≠ b) : b ∈ S.remove a ↔ b ∈ S := by
  simp [remove, mem_sub, count_replicate, h, count_pos]

lemma mem_remove_of_mem_ne {S : Multiset α} {a b : α} (h : b ∈ S) (hab : a ≠ b) :
    b ∈ S.remove a := by
  exact (mem_remove_of_ne S hab).mpr h

lemma mem_remove_of_mem {S : Multiset α} (a b : α) (h : b ∈ S) : b ∈ S.remove a ↔ a ≠ b := by
  constructor
  · contrapose!; intro hab; rw [hab]; exact notMem_of_remove S b
  · intro hab
    exact mem_remove_of_mem_ne h hab

lemma mem_of_mem_remove {S : Multiset α} (a b : α) (h : b ∈ S.remove a) : b ∈ S := by
  rw [← count_pos]
  rw [remove, mem_sub] at h
  exact lt_of_le_of_lt (Nat.zero_le _) h


lemma insert_remove_toFinset (S : Multiset α) (a : α) (ha : a ∈ S) : S.toFinset =
    insert a (S.remove a).toFinset := by
  ext x
  rw [mem_toFinset, Finset.mem_insert]
  constructor
  · intro h
    by_cases hx0 : x = a
    · left; exact hx0
    right
    rw [mem_toFinset, remove, mem_sub, count_replicate]
    push_neg at hx0; symm at hx0
    simp [hx0]
    exact count_pos.mpr h
  · intro h
    by_cases hx0 : x = a
    · rw [hx0]; exact ha
    · push_neg at hx0
      simp only [hx0] at h
      rw [false_or, mem_toFinset, remove, mem_sub, count_replicate] at h
      symm at hx0
      simp [hx0] at h
      exact count_pos.mp h

lemma remove_toFinset (S : Multiset α) (a : α) :
    (S.remove a).toFinset = S.toFinset.erase a := by
  by_cases ha : a ∈ S
  · rw [insert_remove_toFinset S a ha, Finset.erase_insert]
    rw [mem_toFinset]
    exact notMem_of_remove S a
  · rw [remove_of_notMem S a ha, Finset.erase_eq_of_notMem]
    rw [mem_toFinset]
    exact ha

lemma remove_toFinset_card (S : Multiset α) (a : α) (ha : a ∈ S) :
    (S.remove a).toFinset.card = S.toFinset.card - 1 := by
  rw [remove_toFinset S a, Finset.card_erase_of_mem]
  rw [mem_toFinset]
  exact ha

lemma remove_zero_sum (μ : Multiset ℕ) : μ.sum = (μ.remove 0).sum := by
  by_cases h0 : 0 ∉ μ
  · rw [remove_of_notMem μ 0 h0]

  push_neg at h0
  simp [Finset.sum_multiset_count, remove, count_replicate]
  rw [insert_remove_toFinset μ 0 h0, Finset.sum_insert_zero]
  · refine Finset.sum_congr (rfl) ?_
    intro x hx
    rw [mem_toFinset] at hx
    have hx0 : 0 ≠ x := by
      contrapose! hx
      rw [← hx, ← remove]
      exact notMem_of_remove μ 0
    simp [hx0]
  · rw [mul_zero]

lemma cons_remove {μ : Multiset ℕ} (a : ℕ) : (a ::ₘ μ).remove a = μ.remove a := by
  simp [Multiset.remove]

lemma sub_card_le_card {s t : Multiset α} : (s - t).card ≤ s.card := by
  exact card_le_card <| Multiset.sub_le_self s t

lemma remove_card_le_card {μ : Multiset α} {a : α} : (μ.remove a).card ≤ μ.card := by
  simp [Multiset.remove, sub_card_le_card]

end Remove

end Multiset
