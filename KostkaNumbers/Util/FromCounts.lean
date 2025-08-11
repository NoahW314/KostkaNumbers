import Mathlib
import KostkaNumbers.Util.Util
import KostkaNumbers.Util.Remove
import KostkaNumbers.Util.Counts
import KostkaNumbers.Util.MinMaxEl

namespace Multiset

section Counts

variable {μ : Multiset ℕ}

noncomputable
instance fintype_bounded : Fintype {n : ℕ // n < (μ.toList.mergeSort (· ≥ ·)).length} := by
  exact Fintype.ofFinite { n // n < (μ.toList.mergeSort fun x1 x2 ↦ decide (x1 ≥ x2)).length }

noncomputable
def fromCounts (μ : Multiset ℕ) : Multiset ℕ := ∑ n :
  {n : ℕ // n < (μ.toList.mergeSort (· ≥ ·)).length},
  replicate ((μ.toList.mergeSort (· ≥ ·))[n.1]'(n.2)) n.1

lemma count_fromCounts {μ : Multiset ℕ} {n : ℕ} (h : n < μ.card) :
    count n μ.fromCounts = (μ.toList.mergeSort (· ≥ ·))[n]'(by simp[h]) := by
  simp only [fromCounts, ge_iff_le, count_sum', count_replicate]
  rw [Finset.sum_eq_single_of_mem (⟨n, by simp[h]⟩ :
    {n : ℕ // n < (μ.toList.mergeSort (· ≥ ·)).length}) (Finset.mem_univ _)]
  · simp
  · simp only [Finset.mem_univ, ne_eq, ite_eq_right_iff, forall_const, Subtype.forall, ge_iff_le,
      List.length_mergeSort, length_toList, Subtype.mk.injEq]
    intro a _ ha ha'
    contradiction


lemma mem_fromCounts (μ : Multiset ℕ) (h0 : 0 ∉ μ) (n : ℕ) (hn : n < μ.card) :
    n ∈ μ.fromCounts := by
  rw [← count_pos, count_fromCounts hn]
  contrapose! h0
  rw [Nat.le_zero] at h0
  rw [← h0]
  have hn' : n < (μ.toList.mergeSort (· ≥ ·)).length := by simp [hn]
  let hm := List.getElem_mem hn'
  rw [List.mem_mergeSort, mem_toList] at hm
  exact hm

lemma notMem_fromCounts (μ : Multiset ℕ) (n : ℕ) (hn : n ≥ μ.card) :
    n ∉ μ.fromCounts := by
  rw [← count_pos, fromCounts, count_sum']
  push_neg; rw [Nat.le_zero]
  simp only [ge_iff_le, count_replicate, Finset.sum_eq_zero_iff, Finset.mem_univ, ite_eq_right_iff,
    forall_const, Subtype.forall, List.length_mergeSort, length_toList]
  intro a ha han
  omega

lemma mem_fromCounts_iff {n : ℕ} {μ : Multiset ℕ} (h0 : 0 ∉ μ) :
    n ∈ μ.fromCounts ↔ n < μ.card := by
  constructor
  · contrapose!
    exact notMem_fromCounts μ n
  · exact mem_fromCounts μ h0 n

lemma map_count_fromCounts (μ : Multiset ℕ) : List.map (fun n ↦ count n μ.fromCounts)
    (List.range μ.card) = μ.toList.mergeSort (· ≥ ·) := by
  refine List.ext_getElem ?_ ?_
  · simp
  · simp only [List.length_map, List.length_range, ge_iff_le, List.length_mergeSort, length_toList,
      List.getElem_map, List.getElem_range]
    intro i hi _
    rw [count_fromCounts hi]

lemma fromCounts_dedup (h0 : 0 ∉ μ) : μ.fromCounts.dedup = range μ.card := by
  symm
  exact range_eq_dedup μ.fromCounts (mem_fromCounts μ h0) (notMem_fromCounts μ)

lemma fromCounts_counts (h0 : 0 ∉ μ) : μ.fromCounts.counts = μ := by
  rw [counts, fromCounts_dedup h0, ← coe_range, map_coe, map_count_fromCounts]
  nth_rw 2 [← coe_toList μ]
  rw [coe_eq_coe]
  exact List.mergeSort_perm μ.toList fun x1 x2 ↦ decide (x1 ≥ x2)

lemma fromCounts_sorted (μ : Multiset ℕ) : List.Sorted (· ≥ ·) <|
    List.map (fun n => Multiset.count n μ.fromCounts) (List.range μ.card) := by
  rw [map_count_fromCounts]
  exact List.sorted_mergeSort' (fun x1 x2 ↦ x1 ≥ x2) μ.toList


@[simp] lemma fromCounts_card : μ.fromCounts.card = μ.sum := by
  simp only [fromCounts, ge_iff_le, card_sum, card_replicate]
  let e : {n : ℕ // n < (μ.toList.mergeSort (· ≥ ·)).length} →
    Fin (μ.toList.mergeSort (· ≥ ·)).length :=
    fun n ↦ ⟨n, n.2⟩
  rw [Fintype.sum_bijective e ?_ _ (fun n ↦ (μ.toList.mergeSort (· ≥ ·))[n.1]) ?_]
  · rw [Fin.sum_univ_getElem, ← sum_coe]
    congr
    nth_rw 2 [← coe_toList μ]
    rw [coe_eq_coe]
    exact List.mergeSort_perm _ _
  · constructor
    · intro n m
      simp [e]
      exact Subtype.eq
    · intro n
      use ⟨n.1, n.2⟩
  · simp [e]

@[simp] lemma fromCounts_zero : fromCounts 0 = 0 := by
  rw [← Multiset.bot_eq_zero, ← bot_counts_iff]
  refine fromCounts_counts ?_
  rw [bot_eq_zero]
  exact notMem_zero 0

@[simp] lemma fromCounts_bot : fromCounts ⊥ = ⊥ := by simp


lemma ne_zero_of_fromCounts_ne_zero (hμ : μ.fromCounts ≠ 0) : μ ≠ 0 := by
  contrapose! hμ
  rw [hμ, fromCounts_zero]

lemma zero_mem_fromCounts_of_nonempty (hμ : μ.fromCounts ≠ 0) : 0 ∈ μ.fromCounts := by
  have hex : ∃ n, n ∈ μ.fromCounts := by
    contrapose! hμ
    exact eq_zero_of_forall_notMem hμ
  obtain ⟨n, hn⟩ := hex
  rw [← count_pos, count_fromCounts] at hn
  · rw [← count_pos, count_fromCounts]
    · refine lt_of_lt_of_le hn ?_
      refine List.Sorted.rel_get_of_le (List.sorted_mergeSort' (· ≥ ·) _) ?_
      simp
    · rw [Nat.pos_iff_ne_zero, ne_eq, card_eq_zero]
      exact ne_zero_of_fromCounts_ne_zero hμ
  · rw [count_pos] at hn
    contrapose! hn
    exact notMem_fromCounts μ n hn

lemma fromCounts_eq_zero_iff (μ : Multiset ℕ) (h0 : 0 ∉ μ) :
    μ.fromCounts = 0 ↔ μ = 0 := by
  rw [← Multiset.bot_eq_zero, ← Multiset.bot_counts_iff, Multiset.fromCounts_counts h0]

lemma fromCounts_remove_card (h0 : 0 ∉ μ) :
    (μ.fromCounts.remove 0).toFinset.card = μ.card - 1 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  · rw [remove_toFinset_card]
    · nth_rw 2 [← fromCounts_counts h0]
      rw [counts_card]
    · refine zero_mem_fromCounts_of_nonempty ?_
      rw [ne_eq, fromCounts_eq_zero_iff μ h0]
      exact hμ

lemma cons_fromCounts_of_min {μ : Multiset ℕ} (n : ℕ) (h : ∀ m ∈ μ, m ≥ n) :
    (n ::ₘ μ).fromCounts = μ.fromCounts + Multiset.replicate n (μ.card) := by
  simp only [fromCounts, ge_iff_le, List.cons_sort_eq_sort_append_ge μ h]
  let n' : {m // m < ((n ::ₘ μ).toList.mergeSort (· ≥ ·)).length} :=
    ⟨((n ::ₘ μ).toList.mergeSort (· ≥ ·)).length - 1, by simp⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n')]
  conv => lhs; rhs; simp only [ge_iff_le, List.length_mergeSort, length_toList, card_cons,
    add_tsub_cancel_right, le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero,
    n']
  rw [add_left_inj]
  let e : (a : {m // m < ((n ::ₘ μ).toList.mergeSort (· ≥ ·)).length}) →
    (a ∈ (Finset.univ.erase n')) → {m // m < (μ.toList.mergeSort (· ≥ ·)).length} :=
    fun a ha ↦ ⟨a.1, by
      let ha' := a.2
      simp only [ge_iff_le, List.length_mergeSort, length_toList, card_cons, add_tsub_cancel_right,
        Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, n'] at ha ha'
      simp only [ge_iff_le, List.length_mergeSort, length_toList, gt_iff_lt]
      rw [← Subtype.coe_inj] at ha
      simp only at ha
      omega⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  all_goals simp [e]
  · intro a ha
    use (by omega)
    simp only [ge_iff_le, List.length_mergeSort, length_toList, card_cons, add_tsub_cancel_right,
      Subtype.mk.injEq, n']
    exact ne_of_lt ha
  · intro a ha ha'
    rw [List.getElem_append_left]

lemma erase_fromCounts_of_min (μ : Multiset ℕ) (hμ : μ ≠ 0) :
    (μ.erase (min_el μ hμ)).fromCounts = μ.fromCounts.remove (μ.card - 1) := by
  nth_rw 3 [←  cons_erase (min_el_mem hμ)]
  rw [cons_fromCounts_of_min (min_el μ hμ), remove, count_add, count_replicate,
    card_erase_eq_ite]
  · simp only [min_el_mem hμ, ↓reduceIte, Nat.pred_eq_sub_one]
    suffices count (μ.card - 1) (μ.erase (min_el μ hμ)).fromCounts = 0 by
      rw [this, zero_add, Multiset.add_sub_cancel_right]
    rw [count_eq_zero]
    refine notMem_fromCounts _ (μ.card - 1) ?_
    rw [card_erase_eq_ite, Nat.pred_eq_sub_one]
    · simp only [min_el_mem hμ, ↓reduceIte, ge_iff_le, le_refl]
  · intro m hm
    refine min_el_le' hμ ?_
    exact mem_of_mem_erase hm

lemma fromCounts_singleton {n : ℕ} (hn : n ≠ 0) :
    ({n} : Multiset ℕ).fromCounts = Multiset.replicate n 0 := by
  have hn0 : 0 ∉ ({n} : Multiset ℕ) := by
    rw [mem_singleton]; push_neg; symm; exact hn
  simp only [fromCounts, toList_singleton, ge_iff_le, List.mergeSort_singleton,
    List.getElem_singleton]
  rw [Finset.sum_eq_single_of_mem ⟨0, by simp⟩ (Finset.mem_univ _) (by simp)]

end Counts

end Multiset
