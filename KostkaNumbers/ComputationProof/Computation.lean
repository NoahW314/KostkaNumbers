/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.KostkaPos
import KostkaNumbers.ComputationProof.RowColEq
import KostkaNumbers.ComputationProof.Zeros
import KostkaNumbers.SmallDominate

open Kostka SemistandardYoungTableau YoungDiagram

lemma sorted_pair {a b : ℕ} (h : a ≥ b) : List.SortedGE [a, b] :=
  List.Pairwise.sortedGE (by simp [h])

lemma sorted_triple {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    List.SortedGE [a, b, c] := List.Pairwise.sortedGE (by simp [hab, hbc, le_trans hbc hab])


lemma sort_pair_ge {a b : ℕ} (hab : a ≥ b) : ({a, b} : Multiset ℕ).sort (· ≥ ·) = [a, b] := by
  refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) (sorted_pair hab).pairwise ?_
  exact List.Perm.trans (List.mergeSort_perm _ _) (by rfl)

lemma sort_triple_le {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) = [c, b, a] := by
  have habc : [a, b, c].reverse = [c, b, a] := by simp
  refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) ?_ ?_
  · rw [← habc, List.pairwise_reverse]
    exact (sorted_triple hab hbc).pairwise
  · refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← habc, List.perm_reverse]

lemma sort_triple_ge {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    (({a, b, c} : Multiset ℕ).sort (· ≥ ·)) = [a, b, c] :=
  List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) (sorted_triple hab hbc).pairwise <|
    List.Perm.trans (List.mergeSort_perm _ _) (by rfl)



@[simp] lemma max_triple {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    ({a, b, c} : Multiset ℕ).toList.max (by simp) = a := by
  rw! [← Multiset.sort_getElem_zero_eq_max, sort_triple_ge hab hbc]
  rfl

@[simp] lemma min_triple {a b c : ℕ} (hab : a ≥ b) (hbc : b ≥ c) :
    ({a, b, c} : Multiset ℕ).toList.min (by simp) = c := by
  rw! [← Multiset.sort_getElem_zero_eq_min, sort_triple_le hab hbc]
  rfl

/-
Cases for partitions of 4
-/

def Tg22u211 : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, 1 => 0
  | 1, 0 => 1
  | 1, 1 => 2
  | _, _ => 0

lemma g22u211 (T : SemistandardYoungTableau (ofRowLens [2, 2] (sorted_pair (by rfl))))
    (hT : T.content = ({2, 1, 1} : Multiset ℕ).fromCounts) :
    ∀ i ≠ 1, ∀ j, T i j = Tg22u211 i j := by
  intro i hi j
  by_cases hi' : i = 0
  · have hTj : Tg22u211 0 j = 0 := by
      have hj : j = 0 ∨ j = 1 ∨ j > 1 := by lia
      unfold Tg22u211
      grind
    rw [hi', hTj]
    have hje : j < 2 ↔ (0, j) ∈ (ofRowLens [2, 2] (sorted_pair (by rfl))) := by
      rw [mem_iff_lt_rowLen, ← get_rowLens]
      · simp [rowLens_ofRowLens_eq_self]
      · rw [rowLens_length_ofRowLens]
        all_goals simp
    by_cases hj : j < 2
    · rw [entry_eq_zero_iff_of_mem T ?_ hT (hje.mp hj)]
      · rw [max_triple one_le_two (by rfl)]
        simp only [hj, and_self]
      · simp
    · refine T.zeros ?_
      rwa [← hje]
  · simp only [Tg22u211, hi', imp_false, IsEmpty.forall_iff, hi]
    refine T.zeros ?_
    rw [mem_iff_lt_rowLen]
    suffices (ofRowLens [2, 2] (sorted_pair (by rfl))).rowLen i = 0 by
      rw [this]
      exact Nat.not_lt_zero j
    exact rowLen_ofRowLens_eq_zero (by simp) (by simp; lia)

lemma kostka_g22u211 : kostkaNumber (ofRowLens [2, 2] (sorted_pair (by rfl)))
    ({2, 1, 1} : Multiset ℕ) = 1 := by
  have hk : kostkaNumber (ofRowLens [2, 2] (sorted_pair (by rfl)))
      ({2, 1, 1} : Multiset ℕ) ≥ 1 := by
    refine Nat.le_of_pred_lt ?_
    rw [Nat.pred_eq_sub_one, tsub_self, kostka_pos_iff_dominates, rowLens_ofRowLens_eq_self]
    · rw [sort_triple_ge (one_le_two) (by rfl), pair_dominates_triple]
      simp
    all_goals simp
  refine antisymm hk ?_
  rw [kostkaNumber, Nat.card_eq_card_finite_toFinset (Set.finite_of_ncard_pos hk),
    ge_iff_le, Finset.card_le_one_iff]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro T T' hT hT'
  exact eq_of_missing_row' T T' (by rw [hT, hT']) 1 (g22u211 T hT) (g22u211 T' hT')

/-
Cases for partitions of 5
-/

def Tg311u221 : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 1
  | 1, 0 => 1
  | 2, 0 => 2
  | _, _ => 0

lemma st311 : List.SortedGE [3, 1, 1] := sorted_triple (by lia) (by rfl)

lemma g311u221 (T : SemistandardYoungTableau (ofRowLens [3, 1, 1] st311))
    (hT : T.content = ({2, 2, 1} : Multiset ℕ).fromCounts) :
    ∀ i ≠ 0, ∀ j, T i j = Tg311u221 i j := by
  intro i hi j
  have h0 : T 0 0 = 0 := by
    refine top_left_of_content_fromCounts ?_ hT
    suffices (0, 0) ∈ ofRowLens [3, 1, 1] st311 by
      contrapose! this
      rw [this]
      exact notMem_bot (0, 0)
    simp [mem_ofRowLens]
  have h2 : T 2 0 = 2 := by
    have h20 : (2, 0) ∈ ofRowLens [3, 1, 1] st311 := by simp [mem_ofRowLens]
    refine antisymm (entry_ge_col h20) ?_
    have hc : T 2 0 ∈ T.content := mem_content_of_mem h20
    refine Nat.le_of_lt_succ ?_
    simpa [hT, Multiset.mem_fromCounts_iff] using hc
  fun_cases Tg311u221
  · contradiction
  · contradiction
  · contradiction
  · suffices 0 < T 1 0 ∧ T 1 0 < 2 by lia
    constructor
    · nth_rw 1 [← h0]
      refine T.col_strict (zero_lt_one) ?_
      simp [mem_ofRowLens]
    · rw [← h2]
      refine T.col_strict (one_lt_two) ?_
      simp [mem_ofRowLens]
  · exact h2
  · refine T.zeros ?_
    simp only [mem_ofRowLens, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      not_exists, not_lt]
    intro hi'
    rw [← Nat.pos_iff_ne_zero] at hi
    interval_cases i
    all_goals simp_all; lia

lemma kostka_g311u221 : kostkaNumber (ofRowLens [3, 1, 1] st311)
    ({2, 2, 1} : Multiset ℕ) = 1 := by
  have hk : kostkaNumber (ofRowLens [3, 1, 1] st311) ({2, 2, 1} : Multiset ℕ) ≥ 1 := by
    refine Nat.le_of_pred_lt ?_
    rw [Nat.pred_eq_sub_one, tsub_self, kostka_pos_iff_dominates, rowLens_ofRowLens_eq_self]
    · rw [sort_triple_ge (by rfl) (one_le_two), triple_dominates_triple]
      simp
    all_goals simp
  refine antisymm hk ?_
  rw [kostkaNumber, Nat.card_eq_card_finite_toFinset (Set.finite_of_ncard_pos hk),
    ge_iff_le, Finset.card_le_one_iff]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro T T' hT hT'
  refine eq_of_missing_row' T T' ?_ 0 (g311u221 T hT) (g311u221 T' hT')
  rw [hT, hT']





lemma st32 : List.SortedGE [3, 2] := sorted_pair (by lia)

lemma g32u221 (T T' : SemistandardYoungTableau (ofRowLens [3, 2] st32))
    (hT : T.content = ({2, 2, 1} : Multiset ℕ).fromCounts)
    (hT' : T'.content = ({2, 2, 1} : Multiset ℕ).fromCounts) :
    T = T' ↔ T 0 2 = T' 0 2 := by
  constructor
  · intro h
    rw [h]
  · intro h
    refine eq_of_missing_row T T' ?_ 1 ?_
    · rw [hT, hT']
    · intro i hi j
      by_cases hij : (i, j) ∈ (ofRowLens [3, 2] st32)
      · simp only [mem_ofRowLens, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd] at hij
        obtain ⟨hi2, hij⟩ := hij
        have hi0 : i = 0 := by lia
        rw [hi0]
        simp [hi0] at hij
        have h01 : (0, 1) ∈ (ofRowLens [3, 2] st32) := by simp [mem_ofRowLens]
        have hμ : ({2, 2, 1} : Multiset ℕ).toList ≠ [] := by simp
        have hmax : ({2, 2, 1} : Multiset ℕ).toList.max hμ = 2 := max_triple (by rfl) (one_le_two)
        have hγ : (ofRowLens [3, 2] st32) ≠ ⊥ := by
          contrapose! h01
          rw [h01]
          exact notMem_bot (0, 1)
        interval_cases j
        · rw [top_left_of_content_fromCounts hγ hT,
            top_left_of_content_fromCounts hγ hT']
        · rw [(entry_eq_zero_iff_of_mem T hμ hT h01).mpr,
            (entry_eq_zero_iff_of_mem T' hμ hT' h01).mpr]
          all_goals rw [hmax]; simp
        · exact h
      · rw [T.zeros hij, T'.zeros hij]

lemma g32u221_02_eq_one_or_two (T : SemistandardYoungTableau (ofRowLens [3, 2] st32))
    (hT : T.content = ({2, 2, 1} : Multiset ℕ).fromCounts) :
    T 0 2 = 1 ∨ T 0 2 = 2 := by
  suffices 0 < T 0 2 ∧ T 0 2 < 3 by lia
  have hμ : ({2, 2, 1} : Multiset ℕ).toList ≠ [] := by simp
  have hmax : ({2, 2, 1} : Multiset ℕ).toList.max hμ = 2 := max_triple (by rfl) (one_le_two)
  constructor
  · rw [Nat.pos_iff_ne_zero, ne_eq, entry_eq_zero_iff_of_mem T hμ hT, hmax]
    all_goals simp [mem_ofRowLens]
  · have hT02 : T 0 2 ∈ T.content := mem_content_of_mem (by simp [mem_ofRowLens])
    simpa [hT, Multiset.mem_fromCounts_iff] using hT02

lemma kostka_g32u221_le : kostkaNumber (ofRowLens [3, 2] st32)
    ({2, 2, 1} : Multiset ℕ) ≤ 2 := by
  rw [kostkaNumber_eq_card_ssyt_content, Nat.card_eq_card_finite_toFinset (finite_ssyt_content _ _)]
  refine Nat.le_of_not_gt ?_
  rw [gt_iff_lt, Finset.two_lt_card]
  simp only [Set.Finite.mem_toFinset, ne_eq, not_exists, not_and, not_not]
  intro T hT T' hT' T'' hT'' hTT' hTT''
  rw [g32u221 T' T'' hT' hT'']
  rw [g32u221 T T' hT hT'] at hTT'
  rw [g32u221 T T'' hT hT''] at hTT''
  have h02 := g32u221_02_eq_one_or_two T hT
  have h02' := g32u221_02_eq_one_or_two T' hT'
  have h02'' := g32u221_02_eq_one_or_two T'' hT''
  lia



/-
Cases for partitions of 6
-/

def Tg411u222 : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 1
  | 0, 3 => 2
  | 1, 0 => 1
  | 2, 0 => 2
  | _, _ => 0

lemma st411 : List.SortedGE [4, 1, 1] := sorted_triple (by lia) (by rfl)

lemma g411u222 (T : SemistandardYoungTableau (ofRowLens [4, 1, 1] st411))
    (hT : T.content = ({2, 2, 2} : Multiset ℕ).fromCounts) :
    ∀ i ≠ 0, ∀ j, T i j = Tg411u222 i j := by
  intro i hi j
  have h0 : T 0 0 = 0 := by
    refine top_left_of_content_fromCounts ?_ hT
    suffices (0, 0) ∈ ofRowLens [4, 1, 1] st411 by
      contrapose! this
      rw [this]
      exact notMem_bot (0, 0)
    simp [mem_ofRowLens]
  have h2 : T 2 0 = 2 := by
    have h20 : (2, 0) ∈ ofRowLens [4, 1, 1] st411 := by
      simp [mem_ofRowLens]
    refine antisymm (entry_ge_col h20) ?_
    have hc : T 2 0 ∈ T.content := mem_content_of_mem h20
    refine Nat.le_of_lt_succ ?_
    simpa [hT, Multiset.mem_fromCounts_iff] using hc
  fun_cases Tg411u222
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · suffices 0 < T 1 0 ∧ T 1 0 < 2 by lia
    constructor
    · nth_rw 1 [← h0]
      refine T.col_strict (zero_lt_one) ?_
      simp [mem_ofRowLens]
    · rw [← h2]
      refine T.col_strict (one_lt_two) ?_
      simp [mem_ofRowLens]
  · exact h2
  · refine T.zeros ?_
    simp only [mem_ofRowLens, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      not_exists, not_lt]
    intro hi'
    rw [← Nat.pos_iff_ne_zero] at hi
    interval_cases i
    all_goals simp_all; lia

lemma kostka_g411u222 : kostkaNumber (ofRowLens [4, 1, 1] st411)
    ({2, 2, 2} : Multiset ℕ) = 1 := by
  have hk : kostkaNumber (ofRowLens [4, 1, 1] st411) ({2, 2, 2} : Multiset ℕ) ≥ 1 := by
    refine Nat.le_of_pred_lt ?_
    rw [Nat.pred_eq_sub_one, tsub_self, kostka_pos_iff_dominates, rowLens_ofRowLens_eq_self]
    · rw [sort_triple_ge (by rfl) (by rfl), triple_dominates_triple]
      simp
    all_goals simp
  refine antisymm hk ?_
  rw [kostkaNumber, Nat.card_eq_card_finite_toFinset (Set.finite_of_ncard_pos hk),
    ge_iff_le, Finset.card_le_one_iff]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro T T' hT hT'
  refine eq_of_missing_row' T T' ?_ 0 (g411u222 T hT) (g411u222 T' hT')
  rw [hT, hT']




def Tg33u222 : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 1
  | 1, 0 => 1
  | 1, 1 => 2
  | 1, 2 => 2
  | _, _ => 0

lemma st33 : List.SortedGE [3, 3] := sorted_pair (by rfl)

lemma g33u222 (T : SemistandardYoungTableau (ofRowLens [3, 3] st33))
    (hT : T.content = ({2, 2, 2} : Multiset ℕ).fromCounts) :
    ∀ i ≠ 1, ∀ j, T i j = Tg33u222 i j := by
  intro i hi j
  have hμ : ({2, 2, 2} : Multiset ℕ).toList ≠ [] := by simp
  have hmax : ({2, 2, 2} : Multiset ℕ).toList.max hμ = 2 := max_triple (by rfl) (by rfl)
  fun_cases Tg33u222
  · rw [entry_eq_zero_iff_of_mem T hμ hT ?_, hmax]
    · simp
    · simp [mem_ofRowLens]
  · rw [entry_eq_zero_iff_of_mem T hμ hT ?_, hmax]
    · simp
    · simp [mem_ofRowLens]
  · have hT0 : T 0 2 ≥ 1 := by
      suffices T 0 2 > 0 by exact this
      rw [gt_iff_lt, Nat.pos_iff_ne_zero, ne_eq, entry_eq_zero_iff_of_mem T hμ hT ?_, hmax]
      · simp
      · simp [mem_ofRowLens]
    refine antisymm hT0 ?_
    contrapose! hT
    suffices 3 ≤ T 1 2 by
      have hT12 : T 1 2 ∈ T.content := mem_content_of_mem (by simp [mem_ofRowLens])
      contrapose! hT12
      simp [hT12, Multiset.mem_fromCounts_iff, this]
    suffices 2 < T 1 2 by exact this
    refine lt_of_le_of_lt hT ?_
    refine T.col_strict zero_lt_one ?_
    simp [mem_ofRowLens]
  · contradiction
  · contradiction
  · contradiction
  · refine T.zeros ?_
    simp only [mem_ofRowLens, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Order.lt_two_iff, not_exists, not_lt]
    intro hi2
    interval_cases i
    all_goals simp_all
    · lia

lemma kostka_g33u222 : kostkaNumber (ofRowLens [3, 3] st33)
    ({2, 2, 2} : Multiset ℕ) = 1 := by
  have hk : kostkaNumber (ofRowLens [3, 3] st33) ({2, 2, 2} : Multiset ℕ) ≥ 1 := by
    refine Nat.le_of_pred_lt ?_
    rw [Nat.pred_eq_sub_one, tsub_self, kostka_pos_iff_dominates, rowLens_ofRowLens_eq_self]
    · rw [sort_triple_ge (by rfl) (by rfl), pair_dominates_triple]
      simp
    all_goals simp
  refine antisymm hk ?_
  rw [kostkaNumber, Nat.card_eq_card_finite_toFinset (Set.finite_of_ncard_pos hk),
    ge_iff_le, Finset.card_le_one_iff]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro T T' hT hT'
  refine eq_of_missing_row' T T' ?_ 1 (g33u222 T hT) (g33u222 T' hT')
  rw [hT, hT']





lemma st321 : List.SortedGE [3, 2, 1] := sorted_triple (by norm_num) (by norm_num)

lemma entry20_of_321 (T : SemistandardYoungTableau (ofRowLens [3, 2, 1] st321))
    (hT : T.content = ({2, 2, 2} : Multiset ℕ).fromCounts) : T 2 0 = 2 := by
  have h20 : (2, 0) ∈ (ofRowLens [3, 2, 1] st321) := by simp [mem_ofRowLens]
  refine antisymm (entry_ge_col h20) ?_
  have hT20 : T 2 0 ∈ T.content := mem_content_of_mem h20
  simp [hT, Multiset.mem_fromCounts_iff] at hT20
  lia

lemma g321u222 (T T' : SemistandardYoungTableau (ofRowLens [3, 2, 1] st321))
    (hT : T.content = ({2, 2, 2} : Multiset ℕ).fromCounts)
    (hT' : T'.content = ({2, 2, 2} : Multiset ℕ).fromCounts) :
    T = T' ↔ T 0 2 = T' 0 2 := by
  constructor
  · intro h
    rw [h]
  · intro h
    refine eq_of_missing_row T T' ?_ 1 ?_
    · rw [hT, hT']
    · intro i hi j
      by_cases hij : (i, j) ∈ (ofRowLens [3, 2, 1] st321)
      · simp only [mem_ofRowLens, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd] at hij
        obtain ⟨hi3, hij⟩ := hij
        have h01 : (0, 1) ∈ (ofRowLens [3, 2, 1] st321) := by simp [mem_ofRowLens]
        have hμ : ({2, 2, 2} : Multiset ℕ).toList ≠ [] := by simp
        have hmax : ({2, 2, 2} : Multiset ℕ).toList.max hμ = 2 := max_triple (by rfl) (by rfl)
        have hγ : (ofRowLens [3, 2, 1] st321) ≠ ⊥ := by
          contrapose! h01
          exact h01 ▸ notMem_bot (0, 1)
        interval_cases i
        · simp only [List.getElem_cons_zero] at hij
          interval_cases j
          · rw [top_left_of_content_fromCounts hγ hT,
              top_left_of_content_fromCounts hγ hT']
          · rw [(entry_eq_zero_iff_of_mem T hμ hT h01).mpr,
              (entry_eq_zero_iff_of_mem T' hμ hT' h01).mpr]
            all_goals rw [hmax]; simp
          · exact h
        · contradiction
        · simp only [List.getElem_cons_succ, List.getElem_cons_zero, Nat.lt_one_iff] at hij
          rw [hij, entry20_of_321 _ hT, entry20_of_321 _ hT']
      · rw [T.zeros hij, T'.zeros hij]

lemma g321u222_02_eq_one_or_two (T : SemistandardYoungTableau (ofRowLens [3, 2, 1] st321))
    (hT : T.content = ({2, 2, 2} : Multiset ℕ).fromCounts) :
    T 0 2 = 1 ∨ T 0 2 = 2 := by
  suffices 0 < T 0 2 ∧ T 0 2 < 3 by lia
  have hμ : ({2, 2, 2} : Multiset ℕ).toList ≠ [] := by simp
  have hmax : ({2, 2, 2} : Multiset ℕ).toList.max hμ = 2 := max_triple (by rfl) (by rfl)
  constructor
  · rw [Nat.pos_iff_ne_zero, ne_eq, entry_eq_zero_iff_of_mem T hμ hT, hmax]
    all_goals simp [mem_ofRowLens]
  · have hT02 : T 0 2 ∈ T.content := mem_content_of_mem (by simp [mem_ofRowLens])
    simpa [hT, Multiset.mem_fromCounts_iff] using hT02

lemma kostka_g321u222_le : kostkaNumber (ofRowLens [3, 2, 1] st321)
    ({2, 2, 2} : Multiset ℕ) ≤ 2 := by
  rw [kostkaNumber_eq_card_ssyt_content, Nat.card_eq_card_finite_toFinset (finite_ssyt_content _ _)]
  refine Nat.le_of_not_gt ?_
  rw [gt_iff_lt, Finset.two_lt_card]
  simp only [Set.Finite.mem_toFinset, ne_eq, not_exists, not_and, not_not]
  intro T hT T' hT' T'' hT'' hTT' hTT''
  rw [g321u222 T' T'' hT' hT'']
  rw [g321u222 T T' hT hT'] at hTT'
  rw [g321u222 T T'' hT hT''] at hTT''
  let h02 := g321u222_02_eq_one_or_two T hT
  let h02' := g321u222_02_eq_one_or_two T' hT'
  let h02'' := g321u222_02_eq_one_or_two T'' hT''
  lia
