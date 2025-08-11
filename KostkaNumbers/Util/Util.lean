import Mathlib

-- Some results about Lists and Multisets that I need but don't appear to be in Mathlib


namespace List

lemma append_sorted (L : List ℕ) (hL : List.Sorted (· ≤ ·) L) {n : ℕ} (h : ∀ m ∈ L, m ≤ n) :
    List.Sorted (· ≤ ·) (L ++ [n]) := by
  unfold List.Sorted
  rw [List.pairwise_append]
  constructor; swap; constructor
  · exact List.pairwise_singleton (fun x1 x2 ↦ x1 ≤ x2) n
  · simp; exact h
  · exact hL

lemma append_sorted_ge (L : List ℕ) (hL : List.Sorted (· ≥ ·) L) {n : ℕ} (h : ∀ m ∈ L, m ≥ n) :
    List.Sorted (· ≥ ·) (L ++ [n]) := by
  unfold List.Sorted
  rw [List.pairwise_append]
  constructor; swap; constructor
  · exact List.pairwise_singleton (fun x1 x2 ↦ x1 ≥ x2) n
  · simp; exact h
  · exact hL


lemma cons_sort_eq_sort_append (M : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ M, m ≤ n) :
    (n ::ₘ M).toList.mergeSort (· ≤ ·) = M.toList.mergeSort (· ≤ ·) ++ [n] := by
  apply List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _)

  · apply append_sorted _ (List.sorted_mergeSort' _ _)
    simp; exact h

  apply List.Perm.trans (List.mergeSort_perm (n ::ₘ M).toList _)
  apply List.Perm.symm
  apply List.Perm.trans (List.perm_append_singleton _ _)
  apply List.Perm.symm
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.cons_inj_right]
  nth_rw 1 [← Multiset.coe_toList M]
  rw [Multiset.coe_eq_coe]
  apply List.Perm.symm
  apply List.mergeSort_perm

lemma cons_sort_eq_sort_append_ge (M : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ M, m ≥ n) :
    (n ::ₘ M).toList.mergeSort (· ≥ ·) = M.toList.mergeSort (· ≥ ·) ++ [n] := by
  apply List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _)

  · apply append_sorted_ge _ (List.sorted_mergeSort' _ _)
    simp; exact h

  apply List.Perm.trans (List.mergeSort_perm (n ::ₘ M).toList _)
  apply List.Perm.symm
  apply List.Perm.trans (List.perm_append_singleton _ _)
  apply List.Perm.symm
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.cons_inj_right]
  nth_rw 1 [← Multiset.coe_toList M]
  rw [Multiset.coe_eq_coe]
  apply List.Perm.symm
  apply List.mergeSort_perm


lemma coe_ofList_sorted {L : List ℕ} (h : L.Sorted (· ≥ ·)) :
    (Multiset.ofList L).toList.mergeSort (· ≥ ·) = L := by
  refine List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _) h
  refine List.Perm.trans (List.mergeSort_perm _ _) ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]


lemma ge_sort_eq_reverse_le_sort (L : List ℕ) : L.mergeSort (· ≥ ·) =
    (L.mergeSort (· ≤ ·)).reverse := by
  refine List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _) ?_
  · rw [← Multiset.coe_eq_coe, Multiset.coe_reverse, Multiset.coe_eq_coe]
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    refine List.Perm.symm ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← Multiset.coe_eq_coe]
  · rw [List.Sorted, List.pairwise_reverse, ← List.Sorted]
    simp only [ge_iff_le, List.sorted_mergeSort']


end List




namespace Multiset

lemma sum_eq_zero_iff_eq_zero {μ : Multiset ℕ} (h0 : 0 ∉ μ) : μ.sum = 0 ↔ μ = 0 := by
  constructor
  · intro h
    rw [Multiset.sum_eq_zero_iff] at h
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x
    contrapose! h0
    specialize h x h0
    rw [← h]; exact h0
  · intro h; rw [h, Multiset.sum_zero]

lemma card_le_sum (μ : Multiset ℕ) (hp : ∀ x ∈ μ, x > 0) : μ.card ≤ μ.sum := by
  let hc := Multiset.card_nsmul_le_sum hp
  rw [Nat.succ_eq_add_one, zero_add, smul_eq_mul, mul_one] at hc
  exact hc

lemma sum_erase' {μ : Multiset ℕ} {a : ℕ} (h : a ∈ μ) : (μ.erase a).sum = μ.sum - a := by
  rw [← sum_erase h]
  simp only [add_tsub_cancel_left]



lemma range_eq_dedup (M : Multiset ℕ) {m : ℕ} (hmem : ∀ n < m, n ∈ M) (hnmem : ∀ n ≥ m, n ∉ M) :
    range m = M.dedup := by
  ext n
  rw [count_eq_of_nodup (nodup_dedup M), count_eq_of_nodup (nodup_range m)]
  by_cases hn : n ∈ range m
  · simp only [hn, ↓reduceIte, mem_dedup, left_eq_ite_iff, one_ne_zero, imp_false,
      Decidable.not_not]
    rw [mem_range] at hn
    exact hmem n hn
  · simp only [hn, ↓reduceIte, mem_dedup, right_eq_ite_iff, zero_ne_one, imp_false]
    rw [mem_range] at hn; push_neg at hn
    exact hnmem n hn

lemma sub_sub_of_sub {s t : Multiset ℕ} (h : t ≤ s) : s - (s - t) = t := by
  ext x
  rw [count_sub, count_sub]
  apply Multiset.count_le_of_le x at h
  omega

lemma replicate_count_le {s : Multiset ℕ} {a : ℕ} :
    Multiset.replicate (Multiset.count a s) a ≤ s := by
  rw [Multiset.le_iff_count]
  intro x
  rw [Multiset.count_replicate]
  split_ifs  with hx
  · rw [hx]
  · exact Nat.zero_le (Multiset.count x s)

lemma erase_eq_zero_iff {μ : Multiset ℕ} (hμ : μ ≠ 0) (a : ℕ) :
    μ.erase a = 0 ↔ μ = {a} := by
  constructor
  · intro h
    contrapose! hμ
    ext b
    by_cases hb : b = a
    · rw [hb, Multiset.count_zero]
      contrapose! hμ
      ext b
      by_cases hb : b = a
      · simp [hb]
        apply_fun Multiset.count a at h
        simp at h
        omega
      · simp [← Multiset.count_erase_of_ne hb, h]
    · rw [← Multiset.count_erase_of_ne hb, h]
  · intro h
    rw [h]
    exact Multiset.erase_singleton a

@[simp] lemma sort_sum {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r]
    [IsAntisymm α r] [IsTotal α r] [AddCommMonoid α] (s : Multiset α) :
    (Multiset.sort r s).sum = s.sum := by
  conv => lhs; rw [← coe_toList s, coe_sort]
  conv => rhs; rw [← sum_toList]
  exact List.Perm.sum_eq (List.mergeSort_perm s.toList _)

end Multiset
