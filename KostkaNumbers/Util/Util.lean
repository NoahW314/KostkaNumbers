/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib

-- Some results about Lists and Multisets that I need but don't appear to be in Mathlib

-- We should upstream this whole file


namespace Multiset

variable {α : Type*}

lemma sum_eq_zero_iff_eq_zero [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    [CanonicallyOrderedAdd α] {μ : Multiset α} (h0 : 0 ∉ μ) :
    μ.sum = 0 ↔ μ = 0 := by
  constructor
  · rw [Multiset.sum_eq_zero_iff, Multiset.eq_zero_iff_forall_notMem]
    grind
  · intro h
    rw [h, Multiset.sum_zero]

lemma card_le_sum (μ : Multiset ℕ) (hp : ∀ x ∈ μ, x > 0) : μ.card ≤ μ.sum := by
  grind [Multiset.card_nsmul_le_sum hp]

lemma sum_erase' {μ : Multiset ℕ} {a : ℕ} (h : a ∈ μ) : (μ.erase a).sum = μ.sum - a := by
  rw [← sum_erase h]
  simp only [add_tsub_cancel_left]


lemma dedup_eq_range {M : Multiset ℕ} {m : ℕ} (h : ∀ n < m, n ∈ M) (h' : ∀ n ≥ m, n ∉ M) :
    M.dedup = range m := by
  ext n
  rw [count_eq_of_nodup (nodup_dedup M), count_eq_of_nodup (nodup_range m)]
  grind [mem_dedup, mem_range]


lemma erase_eq_zero_iff [DecidableEq α] (s : Multiset α) (a : α) :
    s.erase a = 0 ↔ s = 0 ∨ s = {a} := by
  rw [← coe_toList s, coe_erase, coe_eq_zero, List.erase_eq_nil_iff, coe_eq_zero, coe_eq_singleton]

lemma erase_replicate [DecidableEq α] {n : ℕ} {a : α} :
    (replicate n a).erase a = replicate (n - 1) a := by
  ext b
  by_cases! hb : b = a
  · simp [hb, count_erase_self]
  · simp [count_erase_of_ne hb, count_replicate, hb.symm]

variable {r : α → α → Prop} [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

lemma count_sort [DecidableEq α] {M : Multiset α} {x : α} :
    List.count x (M.sort r) = count x M := by
  simp [← Multiset.coe_count]

lemma sort_perm_toList (s : Multiset α) : (s.sort r).Perm s.toList := by
  nth_rw 1 [← coe_toList s]
  rw [coe_sort]
  exact List.mergeSort_perm _ _

lemma sort_getElem_zero_eq_max {α : Type*} [LinearOrder α] {μ : Multiset α}
    (hμ : μ.toList ≠ []) :
    (μ.sort (· ≥ ·))[0]'(by simp [Multiset.card_pos, ← Multiset.toList_eq_nil, hμ]) =
    μ.toList.max hμ := by
  symm
  rw [List.max_eq_iff]
  simp_rw [Multiset.mem_toList, ← Multiset.mem_sort (· ≥ ·)]
  constructor
  · exact List.getElem_mem _
  · intro a ha
    obtain ⟨i, _, hia⟩ := List.getElem_of_mem ha
    rw [← hia]
    exact List.Pairwise.rel_get_of_le (Multiset.pairwise_sort _ (· ≥ ·)) (by simp)

lemma sort_getElem_zero_eq_min {α : Type*} [LinearOrder α] {μ : Multiset α}
    (hμ : μ.toList ≠ []) :
    (μ.sort (· ≤ ·))[0]'(by simp [Multiset.card_pos, ← Multiset.toList_eq_nil, hμ]) =
    μ.toList.min hμ := by
  symm
  rw [List.min_eq_iff]
  simp_rw [Multiset.mem_toList, ← Multiset.mem_sort (· ≤ ·)]
  constructor
  · exact List.getElem_mem _
  · intro a ha
    obtain ⟨i, _, hia⟩ := List.getElem_of_mem ha
    rw [← hia]
    exact List.Pairwise.rel_get_of_le (Multiset.pairwise_sort _ (· ≤ ·)) (by simp)

-- don't upstream
lemma sort_eq_replicate_iff {μ : Multiset α} {n : ℕ} {x : α} :
    (μ.sort r) = List.replicate n x ↔ μ = Multiset.replicate n x := by
  constructor
  · intro h
    apply_fun Multiset.ofList at h
    rwa [Multiset.coe_replicate, Multiset.sort_eq] at h
  · intro h
    rw [h, ← Multiset.coe_replicate, Multiset.coe_sort]
    refine List.mergeSort_eq_self _ ?_
    simp [List.pairwise_replicate, refl]

@[simp]
lemma sort_sum (r : α → α → Prop) [DecidableRel r] [IsTrans α r]
    [Std.Antisymm r] [Std.Total r] [AddCommMonoid α] (s : Multiset α) :
    (s.sort r).sum = s.sum := by
  conv => lhs; rw [← coe_toList s, coe_sort]
  conv => rhs; rw [← sum_toList]
  exact List.Perm.sum_eq (List.mergeSort_perm s.toList _)

end Multiset



namespace List

variable {α : Type*} {x : α} {R : α → α → Prop} {r : α → α → Bool}

lemma sortedGE_replicate {α : Type*} [Preorder α] {a : α} (n : ℕ) :
    (List.replicate n a).SortedGE := pairwise_replicate_of_refl.sortedGE

lemma pairwise_append_singleton {L : List α} (hL : Pairwise R L) (h : ∀ y ∈ L, R y x) :
    Pairwise R (L ++ [x]) := by
  simpa [List.pairwise_append, hL]

lemma sort_cons' {M : Multiset α} [DecidableRel R] [Std.Total R] [IsTrans α R]
    [Std.Antisymm R] (h : ∀ y ∈ M, R y x) :
    (x ::ₘ M).sort R = M.sort R ++ [x] := by
  refine List.Perm.eq_of_pairwise' (r := R) ?_ ?_ ?_
  · exact Multiset.pairwise_sort _ _
  · simpa [pairwise_append]
  · refine List.Perm.trans (Multiset.sort_perm_toList _) <| List.Perm.symm ?_
    refine List.Perm.trans (List.perm_append_singleton _ _) <| List.Perm.symm ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.cons_inj_right,
      ← Multiset.coe_toList M, Multiset.coe_eq_coe, Multiset.coe_toList]
    exact List.Perm.symm <| Multiset.sort_perm_toList _

lemma mergeSort_toList_coe_eq_self {L : List α} [DecidableRel R] [Std.Total R] [IsTrans α R]
    [Std.Antisymm R] (h : L.Pairwise R) :
    (Multiset.ofList L).toList.mergeSort (fun a b ↦ decide (R a b)) = L := by
  refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) h ?_
  refine List.Perm.trans (List.mergeSort_perm _ _) ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]

lemma max_eq_bot_iff {α : Type*} [Max α] [PartialOrder α] [OrderBot α] [Std.LawfulOrderSup α]
    {l : List α} (hl : l ≠ []) :
    l.max hl = ⊥ ↔ ∀ x ∈ l, x = ⊥ := by
  simp_rw [eq_bot_iff, List.max_le_iff]

lemma min_eq_bot_of_bot_mem {α : Type*} [LinearOrder α] [OrderBot α]
    {l : List α} (hl : l ≠ []) (h : ⊥ ∈ l) :
    l.min hl = ⊥ := by
  rw [eq_bot_iff]
  exact List.min_le_of_mem h

-- don't upstream
lemma forall_mem_eq_one_of_length_eq_sum {L : List ℕ} (h : L.length = L.sum)
    (hp : ∀ x ∈ L, x > 0) : ∀ x ∈ L, x = 1 := by
  contrapose! h
  obtain ⟨x, hxL, hx⟩ := h
  have hxL' := hxL
  rw [List.mem_iff_getElem] at hxL
  obtain ⟨n, ⟨hn, hnx⟩⟩ := hxL
  refine ne_of_lt ?_
  rw [← Fin.sum_univ_getElem, ← Finset.sum_erase_add _ _ (Finset.mem_univ ⟨n, hn⟩)]
  suffices L.length - 1 ≤ ∑ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin (L.length)), L[i.1] by grind
  refine le_trans ?_ (Finset.card_nsmul_le_sum _ _ 1 ?_)
  · simp
  · grind [List.getElem_mem]

end List
