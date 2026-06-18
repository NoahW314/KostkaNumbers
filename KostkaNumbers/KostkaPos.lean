/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Dominate
import KostkaNumbers.Recursion

open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ ν : Multiset ℕ}

/-
Proof that Kostka positive implies domination
-/

lemma bsum_rowLens {r : ℕ} : ∑ i with i.1 ≤ r, γ.rowLens.get i =
    Finset.card {x ∈ γ.cells | x.1 ≤ r} := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_cells, mem_row_iff]
    constructor
    · intro ⟨a, ha, hx⟩
      simp [hx, ha]
    · intro h
      use ⟨x.1, by
        simp only [length_rowLens, ← mem_iff_lt_colLen]
        exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) h.1⟩
      simp [h]
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.PairwiseDisjoint]
    intro a ha b hb hab
    simp only [Function.onFun]
    intro s has hbs x hx
    specialize has hx
    specialize hbs hx
    rw [mem_row_iff] at has hbs
    contrapose! hab
    rw [Fin.mk_eq_mk, ← has.2, ← hbs.2]


theorem dominates_of_kostka_pos (hk : 0 < kostkaNumber γ μ) :
    γ.rowLens ⊵ μ.sort (· ≥ ·) := by
  simp only [kostkaNumber, Set.coe_setOf, Nat.pos_iff_ne_zero, ne_eq, Nat.card_eq_zero, not_or,
    not_isEmpty_iff, nonempty_subtype, not_infinite_iff_finite] at hk
  obtain ⟨⟨T, hT⟩, hk⟩ := hk
  intro r
  suffices Finset.card {x ∈ γ.cells | T x.1 x.2 ≤ r} =
      ∑ i with i.1 ≤ r, (μ.sort (· ≥ ·)).get i by
    rw [bsum_rowLens, ← this]
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_filter, mem_cells] at hx ⊢
    obtain ⟨hγ, hx⟩ := hx
    constructor
    · exact hγ
    · contrapose! hx
      exact lt_of_lt_of_le hx <| entry_ge_col hγ
  rw [Finset.card_def,
    ← Multiset.card_map (fun x : ℕ × ℕ ↦ T x.1 x.2) {x ∈ γ.cells | T x.1 x.2 ≤ r}.val]
  simp only [Finset.filter_val, Multiset.card_map, List.get_eq_getElem, ge_iff_le]
  have hcfc :  ∑ x : Fin (μ.sort (· ≥ ·)).length with x.1 ≤ r,
      (μ.sort (· ≥ ·))[x.1] = ∑ x : Fin (μ.sort (· ≥ ·)).length
      with x.1 ≤ r, Multiset.count x.1 μ.fromCounts := by
    congr
    ext ⟨x, hx⟩
    rw [Multiset.count_fromCounts ?_]
    simpa using hx
  rw [hcfc, ← hT]
  have hctc : ∀ n, Multiset.count n T.content =
      (Multiset.filter (fun x ↦ T x.1 x.2 = n) γ.cells.val).card := by
    intro n
    simp [content, Multiset.count_map, Eq.comm]
  simp only [hctc]
  rw [← Multiset.card_sum]
  congr
  ext x
  simp_rw [Multiset.count_sum', Multiset.count_filter,
    Multiset.count_eq_of_nodup (Finset.nodup _)]
  split
  · rename_i hT
    split_ifs
    · symm
      rw [Finset.sum_ite]
      have hT' : T x.1 x.2 < (μ.sort (· ≥ ·)).length := by
        rename_i hTc hx
        rw [Finset.mem_val, mem_cells] at hx
        simp [entry_lt_card hTc hx]
      have hT'' : ⟨T x.1 x.2, hT'⟩ ∈ ({i : Fin (μ.sort (· ≥ ·)).length | i.1 ≤ r} : Finset _) := by
        simp [hT]
      simp [Fin.filter_eq_val_eq_singleton' (T x.1 x.2) hT' hT'']
    · simp
  · rename_i hT
    exact (Finset.sum_eq_zero (by grind)).symm

lemma zero_zero_mem_of_dominates (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    (0, 0) ∈ γ := by
  suffices ¬γ = ⊥ by
    contrapose! this
    exact eq_bot_iff_zero_zero_notMem.mpr this
  rw [eq_bot_iff_card_eq_zero, card_eq_sum_rowLens]
  apply sum_le_sum_of_dominates at hd
  contrapose! hd
  rw [hd, Nat.pos_iff_ne_zero, ← Multiset.coe_toList μ, Multiset.coe_sort,
    List.Perm.sum_nat (List.mergeSort_perm _ _), Multiset.sum_toList, ne_eq,
    Multiset.sum_eq_zero_iff_eq_zero h0]
  exact hμ


/-
Lemmas about jth
-/

private noncomputable
def jth (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ.toList ≠ []) : ℕ :=
  sSup {j : ℕ | γ.rowLen' j ≥ μ.toList.min hμ}

lemma jth_set_nonempty (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (hμ : μ.toList ≠ []) :
    {j : ℕ | γ.rowLen' j ≥ μ.toList.min hμ}.Nonempty := by
  use 0
  rw [Set.mem_setOf]
  by_cases h0 : 0 ∈ μ
  · rw [← bot_eq_zero, ← Multiset.mem_toList] at h0
    rw [List.min_eq_bot_of_bot_mem hμ h0]
    exact Nat.zero_le _
  let hd2 := hd
  apply get_zero_ge_of_dominates at hd
  have hμ2 : 0 < (μ.sort (· ≥ ·)).length := by
    simp [Nat.pos_iff_ne_zero, ← Multiset.toList_eq_nil, hμ]
  specialize hd ?_ hμ2
  · rw [length_rowLens, ← mem_iff_lt_colLen]
    rw [ne_eq, Multiset.toList_eq_nil] at hμ
    exact zero_zero_mem_of_dominates γ hd2 hμ h0
  · rw [get_rowLens, ← rowLen'_eq_rowLen] at hd
    refine le_trans ?_ hd
    refine List.min_le_of_mem ?_
    rw [Multiset.mem_toList, ← Multiset.mem_sort (· ≥ ·)]
    exact List.getElem_mem _

lemma lt_colLen_of_min_le_rowLen' (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ.toList ≠ [])
    (h0 : 0 ∉ μ) {j : ℕ} (h : μ.toList.min hμ ≤ γ.rowLen' j) : j < γ.colLen 0 := by
  contrapose h0
  rw [rowLen'_eq_zero h0, nonpos_iff_eq_zero] at h
  rw [← Multiset.mem_toList]
  exact h ▸ List.min_mem hμ

lemma jth_set_bddAbove (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    BddAbove {j : ℕ | γ.rowLen' j ≥ μ.toList.min hμ} := by
  rw [bddAbove_def]
  use γ.colLen 0
  intro j
  rw [Set.mem_setOf]
  intro hj
  rw [ge_iff_le] at hj
  apply lt_colLen_of_min_le_rowLen' γ hμ h0 at hj
  exact le_of_lt hj

lemma min_le_jth_rowLen' (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    μ.toList.min hμ ≤ γ.rowLen' (jth γ hμ) := by
  suffices jth γ hμ ∈ {j : ℕ | γ.rowLen' j ≥ μ.toList.min hμ} by
    rwa [Set.mem_setOf] at this
  exact Nat.sSup_mem (jth_set_nonempty hd hμ) (jth_set_bddAbove hμ h0)

lemma jth_lt_colLen (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    jth γ hμ < γ.colLen 0 := by
  exact lt_colLen_of_min_le_rowLen' γ hμ h0 (min_le_jth_rowLen' γ hd hμ h0)

lemma min_gt_rowLen' (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    {i : ℕ} (hi : i > jth γ hμ) : μ.toList.min hμ > γ.rowLen' i := by
  rw [gt_iff_lt] at hi
  let hmc := notMem_of_csSup_lt hi (jth_set_bddAbove hμ h0)
  simpa using hmc

lemma min_gt_rowLen'_jth_add_one (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ.toList ≠ [])
    (h0 : 0 ∉ μ) : μ.toList.min hμ > γ.rowLen' (jth γ hμ + 1) :=
  min_gt_rowLen' γ hμ h0 <| lt_add_one (jth γ hμ)

lemma jth_le_card_sub_one (hd : γ.rowLens ⊵ μ.sort (· ≥ ·))
    (h : γ.card = μ.sum) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) : jth γ hμ ≤ μ.card - 1 := by
  suffices jth γ hμ < μ.card by
    rw [ne_eq, Multiset.toList_eq_nil, ← Multiset.card_eq_zero] at hμ
    lia
  refine lt_of_lt_of_le (jth_lt_colLen γ hd hμ h0) ?_
  apply lengths_le_of_dominates at hd
  specialize hd ?_ ?_
  · simp only [ge_iff_le, Multiset.sort_sum, ← h, card_eq_sum_rowLens]
  · intro i
    exact γ.pos_of_mem_rowLens _ <| List.get_mem γ.rowLens i
  · rwa [length_rowLens, Multiset.length_sort] at hd


/-
Definition of the function that subtracts from row lens
-/

private noncomputable
def sub_max_fun (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ.toList ≠ []) : ℕ → ℕ :=
  fun n ↦ if n = (jth γ hμ) then (μ.toList.min hμ) - γ.rowLen' ((jth γ hμ) + 1)
  else if n > (jth γ hμ) then γ.rowLen' n - γ.rowLen' (n + 1) else 0

lemma sub_max_fun_support (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (n : ℕ) :
    sub_max_fun γ hμ n ≠ 0 ↔ (n = (jth γ hμ) ∧ (μ.toList.min hμ) > γ.rowLen' ((jth γ hμ) + 1))
    ∨ (n > (jth γ hμ) ∧ γ.rowLen' n > γ.rowLen' (n + 1) ∧ n < γ.colLen 0) := by
  simp only [sub_max_fun, gt_iff_lt, ne_eq]
  split_ifs with h h'
  all_goals simp [h]
  · lia
  · by_cases hn : n < γ.colLen 0
    · grind
    · simp [hn]
  · simp [h']


lemma sub_max_fun_le_rowLen' (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (μ.sort (· ≥ ·))) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) (i : ℕ) :
    sub_max_fun γ hμ i ≤ γ.rowLen' i := by
  grind [sub_max_fun, min_le_jth_rowLen' γ hd hμ h0]

lemma rowLen'_le_rowLen'_sub_max_fun (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (μ.sort (· ≥ ·))) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) (i : ℕ) :
    γ.rowLen' (i + 1) ≤ γ.rowLen' i - sub_max_fun γ hμ i := by
  grind [sub_max_fun, γ.rowLen'_anti (Nat.le_add_right i 1), min_gt_rowLen'_jth_add_one γ hμ h0,
    min_le_jth_rowLen' γ hd hμ h0]

lemma sub_max_fun_support_finite (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (μ.sort (· ≥ ·))) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    Finite {n : ℕ | (n = (jth γ hμ) ∧ (μ.toList.min hμ) > γ.rowLen' ((jth γ hμ) + 1))
    ∨ (n > (jth γ hμ) ∧ γ.rowLen' n > γ.rowLen' (n + 1) ∧ n < γ.colLen 0)} := by
  suffices {n : ℕ | (n = (jth γ hμ) ∧ (μ.toList.min hμ) > γ.rowLen' ((jth γ hμ) + 1))
      ∨ (n > (jth γ hμ) ∧ γ.rowLen' n > γ.rowLen' (n + 1) ∧ n < γ.colLen 0)} ⊆
      {n : ℕ | n < γ.colLen 0} by exact Finite.Set.subset _ this
  intro n hn
  rw [Set.mem_setOf] at hn
  rcases hn with hn | hn
  · simp [hn.1, jth_lt_colLen γ hd hμ h0]
  · simp [hn.2.2]


private noncomputable
def sub_max_finsupp (γ : YoungDiagram) {μ : Multiset ℕ}
  (hd : γ.rowLens ⊵ (μ.sort (· ≥ ·))) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) : ℕ →₀ ℕ :=
  ⟨Set.Finite.toFinset (sub_max_fun_support_finite γ hd hμ h0),
  sub_max_fun γ hμ,
  by
    intro n
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Iff.comm]
    exact sub_max_fun_support γ hμ n⟩

private noncomputable
def sub_max (γ : YoungDiagram) {μ : Multiset ℕ}
  (hd : γ.rowLens ⊵ (μ.sort (· ≥ ·))) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
  SubRowLensType γ :=
  ⟨sub_max_finsupp γ hd hμ h0,
  by
    constructor
    · simp only [sub_max_finsupp, Finsupp.coe_mk]
      exact rowLen'_le_rowLen'_sub_max_fun γ hd hμ h0
    · simp only [sub_max_finsupp, Finsupp.coe_mk]
      exact sub_max_fun_le_rowLen' γ hd hμ h0⟩

lemma sub_max_support_sum (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (μ.sort (· ≥ ·))) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    ∑ x ∈ (sub_max γ hd hμ h0).1.support, (sub_max γ hd hμ h0).1 x = μ.toList.min hμ := by
  simp only [sub_max, sub_max_finsupp, gt_iff_lt, Finsupp.coe_mk, sub_max_fun]
  rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_filter, Finset.sum_ite_eq_of_mem']
  · rw [Finset.filter_filter]
    suffices ∑ x ∈ Finset.filter (fun x => (¬x = jth γ hμ ∧ jth γ hμ < x))
        (Set.Finite.toFinset (sub_max_fun_support_finite γ hd hμ h0)),
        (γ.rowLen' x - γ.rowLen' (x + 1)) =
        ∑ x ∈ Finset.range (γ.colLen 0) \ Finset.range (jth γ hμ + 1),
        (γ.rowLen' x - γ.rowLen' (x + 1)) by
      rw [this]
      zify
      have hxa : ∀ x, ↑(γ.rowLen' x - γ.rowLen' (x + 1)) =
          (γ.rowLen' x : ℤ) - (γ.rowLen' (x + 1) : ℤ) := by
        intro x
        exact Nat.cast_sub <| γ.rowLen'_anti (Nat.le_add_right x 1)
      simp only [hxa]
      rw [Finset.sum_sdiff_eq_sub, Finset.sum_range_sub', Finset.sum_range_sub',
        Nat.cast_sub (le_of_lt (min_gt_rowLen'_jth_add_one γ hμ h0))]
      · simp
      · rw [Finset.range_subset_range]
        exact jth_lt_colLen γ hd hμ h0
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ (by intro _ _; rfl)
    · intro x
      simp
      grind
    · intro x
      simp
      lia
  · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, true_and, lt_self_iff_false,
      false_and, or_false]
    exact min_gt_rowLen'_jth_add_one γ hμ h0

/-
Convenient definition
-/

noncomputable
def sub_diagram (hd : γ.rowLens ⊵ μ.sort (· ≥ ·))
    (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) : YoungDiagram := γ.sub (sub_max γ hd hμ h0).1

lemma sub_diagram_colLen_le (hd : γ.rowLens ⊵ μ.sort (· ≥ ·))
    (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) : (sub_diagram hd hμ h0).colLen 0 ≤ γ.colLen 0 :=
  colLen_mono _ <| γ.sub_le (sub_cond (sub_max γ hd hμ h0).2.1)

lemma sub_diagram_colLen (hd : γ.rowLens ⊵ μ.sort (· ≥ ·))
    (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) : γ.colLen 0 - 1 ≤ (sub_diagram hd hμ h0).colLen 0 := by
  have hγ0 : γ.colLen 0 ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, ← mem_iff_lt_colLen]
    rw [ne_eq, Multiset.toList_eq_nil] at hμ
    exact zero_zero_mem_of_dominates γ hd hμ h0
  by_cases hγ : γ.colLen 0 = 1
  · simp [hγ]
  suffices (sub_diagram hd hμ h0).rowLen (γ.colLen 0 - 2) > 0 by
    conv => rhs; unfold colLen
    rw [Nat.le_find_iff]
    intro n hn
    push Not
    rw [mem_cells, mem_iff_lt_rowLen]
    refine lt_of_lt_of_le this (rowLen_anti _ _ _ (by lia))
  rw [← rowLen'_eq_rowLen, sub_diagram, sub_rowLen' (sub_cond (sub_max γ hd hμ h0).2.1)]
  simp only [sub_max, sub_max_finsupp, gt_iff_lt, Finsupp.coe_tsub, Finsupp.coe_mk, Pi.sub_apply,
    sub_max_fun, tsub_pos_iff_lt]
  have hc1 : γ.rowLen' (γ.colLen 0 - 1) > 0 := by
    rw [rowLen'_eq_rowLen, gt_iff_lt, ← mem_iff_lt_rowLen, mem_iff_lt_colLen]
    lia
  have hc2 : γ.rowLen' (γ.colLen 0 - 2) > 0 := lt_of_lt_of_le hc1 <| γ.rowLen'_anti <| by lia
  split_ifs with h₁ h₂
  · rw [h₁]
    have := min_le_jth_rowLen' γ hd hμ h0
    grind
  · grind
  · grind

-- proof that card = sum is preserved after the subtraction and erasure

lemma card_sub_max_eq_sum_erase_min (γ : YoungDiagram) (μ : Multiset ℕ)
    (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (h : γ.card = μ.sum) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    (sub_diagram hd hμ h0).card = (μ.erase (μ.toList.min hμ)).sum := by
  have hμ' : μ.toList.min hμ ∈ μ := by
    rw [← Multiset.mem_toList]
    exact List.min_mem hμ
  rw [sub_diagram, card_sub, sub_max_support_sum, tsub_eq_iff_eq_add_of_le, add_comm,
    Multiset.sum_erase hμ', h]
  · exact h ▸ Multiset.le_sum_of_mem hμ'
  · simp only [sub_max, sub_max_finsupp, Finsupp.coe_mk]
    exact sub_cond (sub_max γ hd hμ h0).2.1
  · exact sub_max_fun_le_rowLen' γ hd hμ h0

/-
Proof of domination after subtraction and erasure
-/

variable {r : ℕ}

lemma jth_le_sub_colLen (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (hμ : μ.toList ≠ [])
    (h0 : 0 ∉ μ) : jth γ hμ ≤ (sub_diagram hd hμ h0).colLen 0 := by
  grind [jth_lt_colLen γ hd hμ h0, sub_diagram_colLen hd hμ h0]

lemma sum_rowLens_sub_sub_max_fun_lt_jth (hd : γ.rowLens ⊵ μ.sort (· ≥ ·))
    (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) (hr : r < jth γ hμ) :
    ∑ x : Fin ((sub_diagram hd hμ h0).rowLens.length) with x.1 ≤ r,
    (sub_diagram hd hμ h0).rowLen' x =
    ∑ x : Fin (γ.rowLens.length) with x.1 ≤ r,
    γ.rowLen' x := by
  let e : (x : Fin (sub_diagram hd hμ h0).rowLens.length) →
    (hx : x ∈ Finset.filter (fun x ↦ x.1 ≤ r) Finset.univ) → Fin γ.rowLens.length :=
    fun x _ ↦ ⟨x.1, by
      let hx := x.2
      simp only [sub_diagram, length_rowLens] at hx
      nth_rw 1 [γ.length_rowLens]
      exact lt_of_lt_of_le hx (colLen_mono _ (γ.sub_le (sub_cond (sub_max γ hd hμ h0).2.1)))⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · grind
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, exists_prop, e]
    intro x hx
    use ⟨x.1, by
      nth_rw 2 [length_rowLens]
      exact lt_of_le_of_lt hx (lt_of_lt_of_le hr (jth_le_sub_colLen hd hμ h0))⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
    intro x hx
    have hx' : x.1 ≠ jth γ hμ := by lia
    have hx'' : ¬x.1 > jth γ hμ := by lia
    unfold sub_diagram
    rw [sub_rowLen' (sub_cond (sub_max γ hd hμ h0).2.1)]
    simp [sub_max, sub_max_finsupp, sub_max_fun, hx', hx'']

lemma sum_fin_with_eq_sum_nat_bdd' {n m : ℕ} {f : ℕ → ℕ} :
    ∑ x : Fin n with x.1 ≤ m, f x.1 = ∑ x ∈ {x : ℕ | x ≤ m}.toFinset with x < n, f x := by
  let e : (x : Fin n) → (hx : x ∈ Finset.filter (fun x ↦ x.1 ≤ m) Finset.univ) → ℕ :=
    fun x _ ↦ x.1
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · grind
  · simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      exists_prop, and_imp, e]
    intro b _ hn
    use ⟨b, hn⟩
  · simp [e]

lemma sum_fin_with_eq_sum_nat_bdd {n m : ℕ} {f : ℕ → ℕ} (hf : ∀ x ≥ n, f x = 0) :
    ∑ x : Fin n with x.1 ≤ m, f x.1 = ∑ x ∈ {x : ℕ | x ≤ m}.toFinset, f x := by
  rw [sum_fin_with_eq_sum_nat_bdd']
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · intro x hx
    simp_all
  · grind
  · simp

lemma sum_rowLens_sub_sub_max_fun_ge_jth (hd : γ.rowLens ⊵ μ.sort (· ≥ ·))
    (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) (hr : r ≥ jth γ hμ) :
    ∑ x : Fin ((sub_diagram hd hμ h0).rowLens.length) with x.1 ≤ r,
    (sub_diagram hd hμ h0).rowLen' x =
    ∑ x : Fin (γ.rowLens.length) with x.1 ≤ r + 1,
    γ.rowLen' x - μ.toList.min hμ := by
  rw [sum_fin_with_eq_sum_nat_bdd rowLen'_eq_zero_of_ge_length,
    sum_fin_with_eq_sum_nat_bdd rowLen'_eq_zero_of_ge_length]
  have hj : jth γ hμ ∈ {x : ℕ | x ≤ r}.toFinset := by simp [hr]
  rw [← Finset.sum_erase_add _ _ hj]
  conv => {
    lhs; rhs;
    unfold sub_diagram
    rw [sub_rowLen' (sub_cond (sub_max γ hd hμ h0).2.1)]
    simp [sub_max, sub_max_finsupp, gt_iff_lt, sub_rowLen',
    Finsupp.coe_tsub, Finsupp.coe_mk, Pi.sub_apply, sub_max_fun, ↓reduceIte]
  }
  have hj' : jth γ hμ ∈ {x : ℕ | x ≤ r + 1}.toFinset := by
    rw [Set.mem_toFinset, Set.mem_setOf_eq]
    exact Nat.le_add_right_of_le hr
  rw [← Finset.sum_erase_add _ _ hj']
  have hj1 : jth γ hμ + 1 ∈ {x : ℕ | x ≤ r + 1}.toFinset.erase (jth γ hμ) := by simp [hr]
  rw [← Finset.sum_erase_add _ _ hj1, add_assoc,
    add_tsub_assoc_of_le <| Nat.le_add_left_of_le <| min_le_jth_rowLen' γ hd hμ h0]
  have hrl : γ.rowLen' (jth γ hμ) - (μ.toList.min hμ - γ.rowLen' (jth γ hμ + 1)) =
      γ.rowLen' (jth γ hμ + 1) + γ.rowLen' (jth γ hμ) - μ.toList.min hμ := by
    have := min_gt_rowLen'_jth_add_one γ hμ h0
    lia
  rw [hrl, Nat.add_right_cancel_iff]
  let e : (x : ℕ) → (hx : x ∈ {x : ℕ | x ≤ r}.toFinset.erase (jth γ hμ)) → ℕ :=
    fun x _ ↦ if x < jth γ hμ then x else x + 1
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · grind
  · intro x₁ hx₁ x₂ hx₂
    unfold e
    simp at hx₁ hx₂
    split_ifs with hxj₁ hxj₂
    all_goals lia
  · simp only [Finset.mem_erase, ne_eq, Set.mem_toFinset, Set.mem_setOf_eq, exists_prop, and_imp, e]
    intro x hxj1 hxj hxr1
    by_cases hx : x < jth γ hμ
    · use x
      simp only [hxj, not_false_eq_true, true_and, hx, ↓reduceIte, and_true]
      exact le_trans (le_of_lt hx) hr
    · use x - 1
      grind
  · unfold sub_diagram
    rw [sub_rowLen' (sub_cond (sub_max γ hd hμ h0).2.1)]
    simp only [Finset.mem_erase, ne_eq, Set.mem_toFinset, Set.mem_setOf_eq, sub_max,
      sub_max_finsupp, gt_iff_lt, Finsupp.coe_tsub, Finsupp.coe_mk, Pi.sub_apply,
      sub_max_fun, and_imp, e]
    intro x hxj hxr
    grind [γ.rowLen'_anti (Nat.le_add_right x 1)]

lemma sum_sort_erase_lt_card_sub_one (hμ : μ.toList ≠ []) (hr : r < μ.card - 1) :
    ∑ x : Fin (((μ.erase (μ.toList.min hμ)).sort (· ≥ ·)).length) with x.1 ≤ r,
    ((μ.erase (μ.toList.min hμ)).sort (· ≥ ·))[x.1] =
    ∑ x : Fin ((μ.sort (· ≥ ·)).length) with x.1 ≤ r,
    (μ.sort (· ≥ ·))[x.1] := by
  have hμ' : μ.toList.min hμ ∈ μ := by
    rw [← Multiset.mem_toList]
    exact List.min_mem hμ
  let e : (x : Fin (((μ.erase (μ.toList.min hμ)).sort (· ≥ ·)).length)) →
    (hx : x ∈ Finset.filter (fun x ↦ x.1 ≤ r) Finset.univ) →
    Fin ((μ.sort (· ≥ ·)).length) := fun x _ ↦ ⟨x.1, by grind [Multiset.length_sort]⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · grind
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
    intro x hx
    use ⟨x.1, by
      simp_all [Multiset.card_erase_of_mem hμ']
      lia⟩
    simp [hx]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ge_iff_le, e]
    intro x hx
    have hml : (μ.sort (· ≥ ·)) =
        ((μ.toList.min hμ) ::ₘ μ.erase (μ.toList.min hμ)).sort (· ≥ ·) := by
      rw [Multiset.cons_erase hμ']
    have hm : ∀ m ∈ μ.erase (μ.toList.min hμ), m ≥ μ.toList.min hμ := by
      intro m hm
      refine List.min_le_of_mem ?_
      rw [Multiset.mem_toList]
      exact Multiset.mem_of_mem_erase hm
    simp only [hml, List.sort_cons' hm]
    rw [List.getElem_append_left]


lemma sum_with_le_sum_with_add_one_sub_min (hμ : μ.toList ≠ []) (hr : r < μ.card - 1) :
    ∑ x : Fin (μ.sort (· ≥ ·)).length with x.1 ≤ r,
    (μ.sort (· ≥ ·))[x.1] ≤
    ∑ x : Fin (μ.sort (· ≥ ·)).length with x.1 ≤ r + 1,
    (μ.sort (· ≥ ·))[x.1] - μ.toList.min hμ := by
  let r1 : Fin (μ.sort (· ≥ ·)).length := ⟨r + 1, by simp; lia⟩
  have hr1 : r1 ∈ Finset.filter (fun x ↦ x.1 ≤ r + 1) Finset.univ := by simp [r1]
  rw [← Finset.sum_erase_add _ _ hr1]
  have hs : (Finset.filter (fun x ↦ x.1 ≤ r + 1) Finset.univ).erase r1 =
      Finset.filter (fun x ↦ x.1 ≤ r) Finset.univ := by grind
  rw [hs, add_tsub_assoc_of_le, add_comm]
  · exact le_add_self
  refine List.min_le_of_mem ?_
  rw [Multiset.mem_toList, ← Multiset.mem_sort (· ≥ ·)]
  exact List.getElem_mem _

lemma rowLens_sub_dominates_sort_erase_min (γ : YoungDiagram) (μ : Multiset ℕ)
    (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (h : γ.card = μ.sum) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    (sub_diagram hd hμ h0).rowLens ⊵ (μ.erase (μ.toList.min hμ)).sort (· ≥ ·) := by
  refine dominates_of_forall_lt_min ?_ ?_
  · intro r hr
    simp only [List.get_eq_getElem, get_rowLens, ← rowLen'_eq_rowLen]
    by_cases hrj : r < jth γ hμ
    · rw [sum_sort_erase_lt_card_sub_one hμ (lt_of_lt_of_le hrj
        (jth_le_card_sub_one hd h hμ h0)), sum_rowLens_sub_sub_max_fun_lt_jth hd hμ h0 hrj]
      specialize hd r
      simpa only [List.get_eq_getElem, get_rowLens, rowLen'_eq_rowLen] using hd
    · push Not at hrj
      rw [lt_min_iff] at hr
      rw [sum_rowLens_sub_sub_max_fun_ge_jth hd hμ h0 hrj]
      specialize hd (r + 1)
      simp only [List.get_eq_getElem, get_rowLens, ← rowLen'_eq_rowLen, ge_iff_le] at hd
      refine le_trans ?_ (Nat.sub_le_sub_right hd _)
      have hrl : r < μ.card - 1 := by
        have hμ' : μ.toList.min hμ ∈ μ := by
          rw [← Multiset.mem_toList]
          exact List.min_mem hμ
        simp only [ge_iff_le, Multiset.length_sort, Multiset.card_erase_of_mem hμ',
          Nat.pred_eq_sub_one, length_rowLens] at hr
        exact hr.1
      rw [sum_sort_erase_lt_card_sub_one hμ hrl]
      exact sum_with_le_sum_with_add_one_sub_min hμ hrl
  · rw [Multiset.sort_sum, ← (card_sub_max_eq_sum_erase_min γ μ hd h hμ h0),
      card_eq_sum_rowLens]

/-
The main theorem
-/

theorem kostka_pos_of_dominates (γ : YoungDiagram) (μ : Multiset ℕ)
    (hd : γ.rowLens ⊵ μ.sort (· ≥ ·)) (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    kostkaNumber γ μ > 0 := by
  by_cases hμ : μ.toList = []
  · have hμ' : μ = 0 := by rwa [← Multiset.toList_eq_nil]
    have hγ : γ = ⊥ := by rwa [eq_bot_iff_card_eq_zero, h, Multiset.sum_eq_zero_iff_eq_zero h0]
    rw [hμ', hγ, ← Multiset.bot_eq_zero, kostka_bot_bot]
    exact zero_lt_one
  have hμm : μ.toList.min hμ ∈ μ := by
    rw [← Multiset.mem_toList]
    exact List.min_mem hμ
  rw [kostka_recursion hμ h0 h]
  suffices ∃ f : SubRowLensType γ, ((γ.sub f.1).rowLens ⊵ (μ.erase (μ.toList.min hμ)).sort (· ≥ ·))
      ∧ (γ.sub f.1).card = (μ.erase (μ.toList.min hμ)).sum by
    obtain ⟨f, hf, hγμ⟩ := this
    let hf := kostka_pos_of_dominates _ _ hf hγμ ?_
    · refine lt_of_lt_of_le hf ?_
      have hfp : ∀ f : SubRowLensType γ, f ∈ Finset.univ → 0 ≤ kostkaNumber (γ.sub f.1)
          (μ.erase (μ.toList.min hμ)) := by simp
      exact Finset.single_le_sum hfp (Finset.mem_univ _)
    · contrapose! h0
      exact Multiset.mem_of_mem_erase h0
  use sub_max γ hd hμ h0
  constructor
  · exact rowLens_sub_dominates_sort_erase_min γ μ hd h hμ h0
  · exact card_sub_max_eq_sum_erase_min γ μ hd h hμ h0
  termination_by μ.card
  decreasing_by simpa [hμm, Nat.pos_iff_ne_zero, ← Multiset.toList_eq_nil]

theorem kostka_pos_iff_dominates (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    0 < kostkaNumber γ μ ↔ γ.rowLens ⊵ μ.sort (· ≥ ·) := by
  constructor
  · exact dominates_of_kostka_pos
  · intro hd
    exact kostka_pos_of_dominates γ μ hd h h0
