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



lemma forall_mem_eq_one_of_length_eq_sum {L : List ℕ} (h : L.length = L.sum)
    (hp : ∀ x ∈ L, x > 0) : ∀ x ∈ L, x = 1 := by
  contrapose! h
  obtain ⟨x, hxL, hx⟩ := h
  let hpx := hp x hxL
  rw [List.mem_iff_getElem] at hxL
  obtain ⟨n, ⟨hn, hnx⟩⟩ := hxL
  refine ne_of_lt ?_
  rw [← Fin.sum_univ_getElem, ← Finset.sum_erase_add _ _ (Finset.mem_univ ⟨n, hn⟩)]
  simp only [hnx]
  have hlen : L.length = L.length - 1 + 1 := by omega
  nth_rw 1 [hlen]
  suffices L.length - 1 ≤ ∑ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin (L.length)),
    L[i.1] by omega
  refine le_trans ?_ (Finset.card_nsmul_le_sum _ _ 1 ?_)
  · simp
  · intro y hy
    refine hp L[y.1] ?_
    exact List.getElem_mem _

variable {α : Type*}
lemma sorted_ge_replicate (n : ℕ) (a : α) [Preorder α] :
    List.Sorted (· ≥ ·) (List.replicate n a) := by
  simp [Sorted, pairwise_replicate]

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


lemma count_sort {M : Multiset ℕ} {n : ℕ} :
    List.count n (sort (· ≥ ·) M) = count n M := by
  rw [← Multiset.coe_count]
  congr
  simp

lemma sort_eq_replicate_iff {μ : Multiset ℕ} {n a : ℕ} :
    (Multiset.sort (· ≥ ·) μ) = List.replicate n a ↔ μ = Multiset.replicate n a := by
  constructor
  · intro h
    ext x
    apply_fun List.count x at h
    rw [Multiset.count_sort] at h
    rw [h, ← Multiset.coe_count, Multiset.coe_replicate]
  · intro h
    rw [h, ← Multiset.coe_replicate, Multiset.coe_sort]
    refine List.eq_of_perm_of_sorted (List.mergeSort_perm _ _) (List.sorted_mergeSort' _ _) ?_
    exact List.sorted_ge_replicate n a


-- Add to Mathlib

lemma erase_replicate {n a : ℕ} : (Multiset.replicate n a).erase a =
    Multiset.replicate (n - 1) a := by
  ext b
  by_cases hb : b = a
  · simp [hb, count_erase_self]
  · let hb2 := hb; push_neg at hb2; symm at hb2
    simp [count_erase_of_ne hb, count_replicate, hb2]

@[simp] lemma sort_sum {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r]
    [IsAntisymm α r] [IsTotal α r] [AddCommMonoid α] (s : Multiset α) :
    (Multiset.sort r s).sum = s.sum := by
  conv => lhs; rw [← coe_toList s, coe_sort]
  conv => rhs; rw [← sum_toList]
  exact List.Perm.sum_eq (List.mergeSort_perm s.toList _)

end Multiset
