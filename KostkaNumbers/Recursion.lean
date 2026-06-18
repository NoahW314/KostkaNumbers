/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.FinsuppEquiv
import KostkaNumbers.RestrictExtend


open YoungDiagram Kostka SemistandardYoungTableau

def SubRowLensType (γ : YoungDiagram) := {f : ℕ →₀ ℕ //
  (∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) ∧ (∀ i, f i ≤ γ.rowLen' i)}

lemma finite_subRowLensType (γ : YoungDiagram) : Finite (SubRowLensType γ) := by
  suffices Finite {f : ℕ →₀ ℕ | (∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) ∧
    (∀ i, f i ≤ γ.rowLen' i)} by exact this
  have : Finite {f : ℕ →₀ ℕ | f ≤ γ.rowLen'} := instFiniteSubtypeLeOfLocallyFiniteOrderBot
  refine Finite.Set.subset {f : ℕ →₀ ℕ | f ≤ γ.rowLen'} ?_
  intro f hf
  rw [Set.mem_setOf] at hf ⊢
  intro i
  exact hf.2 i

noncomputable
instance subRowLensFintype (γ : YoungDiagram) : Fintype (SubRowLensType γ) := by
  have := finite_subRowLensType γ
  exact Fintype.ofFinite (SubRowLensType γ)

lemma zero_subRowLensType {γ : YoungDiagram} :
    (∀ i, γ.rowLen' i - (0 : ℕ →₀ ℕ) i ≥ γ.rowLen' (i + 1)) ∧
    (∀ i, (0 : ℕ →₀ ℕ) i ≤ γ.rowLen' i) := by
  constructor
  · simp only [Finsupp.coe_zero, Pi.zero_apply, tsub_zero, ge_iff_le]
    intro i
    exact γ.rowLen'_anti (Nat.le_add_right i 1)
  · simp


lemma exists_max_cell_start {γ : YoungDiagram} (T : SemistandardYoungTableau γ) (i : ℕ)
    (hT : T.content.toList ≠ []) :
    ∃ j : ℕ, ∀ j' ≥ j, (i, j') ∈ γ → T i j' = T.content.toList.max hT := by
  use γ.rowLen i
  grind [mem_iff_lt_rowLen]

open Classical in
lemma find_max_cell_start_le {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    {i j : ℕ} (hT : T.content.toList ≠ []) (h : T i j = T.content.toList.max hT) :
    Nat.find (exists_max_cell_start T i hT) ≤ j := by
  refine Nat.find_min' (exists_max_cell_start T i hT) ?_
  intro j' hj hij'
  refine antisymm (entry_le_max hT) ?_
  rw [← h]
  exact T.row_weak_of_le hj hij'

open Classical in
lemma find_max_cell_start_eq_zero {γ : YoungDiagram}
    (T : SemistandardYoungTableau γ) (hTc : T.content.toList ≠ []) {i : ℕ}
    (h : ∀ x ∈ T.content, x = 0) :
    Nat.find (exists_max_cell_start T i hTc) = 0 := by
  rw [← Nat.le_zero]
  refine find_max_cell_start_le T hTc ?_
  have hT : T.content.toList.max hTc = 0 := by
    simp_rw [← Nat.bot_eq_zero, List.max_eq_bot_iff, Multiset.mem_toList] at h ⊢
    exact h
  rw [hT]
  by_cases hi : (i, 0) ∈ γ
  · exact h (T i 0) (mem_content_of_mem hi)
  · exact T.zeros hi

open Classical in
lemma entry_find_eq_max {γ : YoungDiagram} {T : SemistandardYoungTableau γ}
    (i : ℕ) (hT : T.content.toList ≠ []) (h : (i, Nat.find (exists_max_cell_start T i hT)) ∈ γ) :
    T i (Nat.find (exists_max_cell_start T i hT)) = T.content.toList.max hT := by
  let hm := Nat.find_spec (exists_max_cell_start T i hT)
  exact hm (Nat.find (exists_max_cell_start T i hT)) (by rfl) h

open Classical in
noncomputable
def max_cell_len {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
  (hTc : T.content.toList ≠ []) : ℕ →₀ ℕ :=
  ⟨ if T.content.toList.max hTc ≠ 0 then
    {i ∈ Finset.range <| γ.colLen 0 | ∃ j, T i j = T.content.toList.max hTc}
    else Finset.range <| γ.colLen 0,
  fun i ↦ γ.rowLen' i - Nat.find (exists_max_cell_start T i hTc),
    by
    split_ifs with hTc0
    · intro i
      constructor
      · intro hi
        simp only [Finset.mem_filter, Finset.mem_range, ← mem_iff_lt_colLen] at hi
        obtain ⟨hi, ⟨j, hj⟩⟩ := hi
        refine ne_of_gt ?_
        simp only [tsub_pos_iff_lt, rowLen'_eq_rowLen]
        rw [← hj] at hTc0
        refine lt_of_le_of_lt (find_max_cell_start_le T hTc hj) ?_
        rw [← mem_iff_lt_rowLen]
        contrapose! hTc0
        exact T.zeros hTc0
      · simp only [Finset.mem_filter, Finset.mem_range]
        intro hi
        constructor
        · rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero]
          rw [rowLen'_eq_rowLen] at hi
          contrapose! hi
          rw [hi, zero_tsub]
        · contrapose! hi
          suffices ¬ Nat.find (exists_max_cell_start T i hTc) < γ.rowLen i by
            push Not at this
            rw [rowLen'_eq_rowLen]
            exact Nat.sub_eq_zero_of_le this
          rw [← mem_iff_lt_rowLen]
          contrapose! hi
          use (Nat.find (exists_max_cell_start T i hTc))
          exact entry_find_eq_max i hTc hi
    · push Not at hTc0
      simp_rw [← Nat.bot_eq_zero, List.max_eq_bot_iff, Multiset.mem_toList, Nat.bot_eq_zero] at hTc0
      simp [← mem_iff_lt_colLen, rowLen'_eq_rowLen, ← Nat.pos_iff_ne_zero,
        find_max_cell_start_eq_zero T hTc hTc0, ← mem_iff_lt_rowLen]
    ⟩



lemma max_cell_len_sub {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i : ℕ) : γ.rowLen' i - (max_cell_len T hTc i) ≥
    γ.rowLen' (i + 1) := by
  simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk]
  rw [Nat.sub_sub_eq_min, Nat.le_min]
  constructor
  · exact γ.rowLen'_anti (Nat.le_add_right i 1)
  · refine Nat.le_of_not_gt ?_
    rw [rowLen'_eq_rowLen, gt_iff_lt, ← mem_iff_lt_rowLen]
    by_contra! h
    let hc := T.col_strict (Nat.lt_add_one i) h
    rw [entry_find_eq_max i hTc (γ.up_left_mem (le_of_lt (Nat.lt_add_one i)) (by rfl) h)] at hc
    contrapose! hc
    exact entry_le_max hTc

lemma max_cell_len_le_rowLen' {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i : ℕ) : (max_cell_len T hTc i) ≤ γ.rowLen' i := by
  simp [max_cell_len]

open Classical in
lemma find_max_cell_start_le_rowLen' {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (i : ℕ) (hTc : T.content.toList ≠ []) : Nat.find (exists_max_cell_start T i hTc) ≤
    γ.rowLen' i := by
  refine Nat.find_min' _ ?_
  intro j hij hij'
  rw [mem_iff_lt_rowLen, ← rowLen'_eq_rowLen] at hij'
  lia

lemma entry_eq_max {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij : (i, j) ∈ γ)
    (hij' : (i, j) ∉ γ.sub (max_cell_len T hTc)) :
    T i j = T.content.toList.max hTc := by
  rw [mem_sub _ (sub_cond (max_cell_len_sub T hTc))] at hij'
  simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk, not_lt,
    tsub_le_iff_right] at hij'
  classical
  suffices j ≥ Nat.find (exists_max_cell_start T i hTc) by
    exact Nat.find_spec (exists_max_cell_start T i hTc) j this hij
  let hc := find_max_cell_start_le_rowLen' T i
  grind

lemma entry_eq_max_iff {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (he : ∃ x ∈ T.content, x ≠ ⊥)
    (i j : ℕ) : T i j = T.content.toList.max hTc ↔
    (i, j) ∈ γ.cells \ (γ.sub (max_cell_len T hTc)).cells := by
  constructor
  · intro hij
    rw [Finset.mem_sdiff, mem_cells, mem_cells, mem_sub _ (sub_cond (max_cell_len_sub T hTc))]
    simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk, not_lt, tsub_le_iff_right]
    constructor
    · contrapose! hij
      symm
      simp_rw [T.zeros hij, ← bot_eq_zero, ne_eq, List.max_eq_bot_iff, Multiset.mem_toList]
      push Not
      exact he
    · apply find_max_cell_start_le T at hij
      let hc := find_max_cell_start_le_rowLen' T i
      lia
  · intro hij
    simp only [Finset.mem_sdiff, mem_cells] at hij
    exact entry_eq_max T hTc i j hij.1 hij.2

lemma exists_nonzero_of_mem_sub {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    ∃ x ∈ T.content, x ≠ 0 := by
  contrapose! hij'
  simp [max_cell_len, find_max_cell_start_eq_zero T hTc hij']

lemma entry_lt_max {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    T i j < T.content.toList.max hTc := by
  have hemp := exists_nonzero_of_mem_sub T hTc i j hij'
  contrapose! hij'
  have he : T i j = T.content.toList.max hTc := antisymm' hij' <| entry_le_max hTc
  rw [entry_eq_max_iff T hTc hemp, Finset.mem_sdiff, mem_cells] at he
  exact he.2

lemma entry_restrict_lt_max {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    (T.restrict (γ.sub_le (sub_cond (max_cell_len_sub T hTc))))
    i j < T.content.toList.max hTc := by
  simp only [restrict, DFunLike.coe, hij']
  exact entry_lt_max T hTc i j hij'


lemma count_max_restrict_max_cells {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) : Multiset.count (T.content.toList.max hTc)
    (T.restrict (γ.sub_le (sub_cond (max_cell_len_sub T hTc)))).content = 0 := by
  simp only [content, Multiset.count_eq_zero, Multiset.mem_map, Finset.mem_val, mem_cells,
    Prod.exists, not_exists, not_and]
  intro i j hij
  exact ne_of_lt <| entry_restrict_lt_max T hTc i j hij

lemma restrict_max_cells_content {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content.toList ≠ []) :
    (T.restrict (γ.sub_le (sub_cond (max_cell_len_sub T hTc)))).content =
    T.content.remove (T.content.toList.max hTc) := by
  nth_rw 7 [← restrict_extend T (γ.sub_le (sub_cond (max_cell_len_sub T hTc)))
      (γ.sub_valid (max_cell_len_sub T hTc)) (entry_eq_max T hTc)]
  · rw [extend_content]
    · simp only [Multiset.remove, Multiset.count_add, Multiset.count_replicate_self]
      symm
      rw [count_max_restrict_max_cells, zero_add, Multiset.add_sub_cancel_right]
    · exact sub_le (sub_cond (max_cell_len_sub T hTc))
  · exact entry_restrict_lt_max T hTc


lemma max_fromCounts_add_one_eq_card {μ : Multiset ℕ} (hμ : μ.fromCounts.toList ≠ []) (h0 : 0 ∉ μ) :
    μ.fromCounts.toList.max hμ + 1 = μ.card := by
  have hle : μ.fromCounts.toList.max hμ + 1 ≤ μ.card := by
    suffices μ.fromCounts.toList.max hμ < μ.card by exact this
    rw [← Multiset.mem_fromCounts_iff h0, ← Multiset.mem_toList]
    exact List.max_mem hμ
  refine antisymm hle ?_
  suffices μ.card - 1 ≤ μ.fromCounts.toList.max hμ by lia
  refine List.le_max_of_mem ?_
  rw [Multiset.mem_toList]
  refine Multiset.mem_fromCounts h0 (μ.card - 1) ?_
  simp only [tsub_lt_self_iff, zero_lt_one, and_true]
  rwa [Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero, ← Multiset.fromCounts_eq_zero_iff _ h0,
      ← Multiset.toList_eq_nil]

lemma max_fromCounts_eq_card_sub_one {μ : Multiset ℕ} (hμ : μ.fromCounts.toList ≠ []) (h0 : 0 ∉ μ) :
    μ.fromCounts.toList.max hμ = μ.card - 1 := by
  rw [← max_fromCounts_add_one_eq_card hμ h0, add_tsub_cancel_right]

open Classical in
def unionEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    SemistandardYoungTableauWithContent γ μ ≃
    Finset.biUnion (Finset.univ : Finset (SubRowLensType γ)) (fun ⟨_, hf⟩ ↦
    {T : SemistandardYoungTableauWithContent γ μ |
    (T.1.restrict (γ.sub_le (sub_cond hf.1))).content =
    (μ.erase (μ.toList.min hμ)).fromCounts}) where
  toFun T := ⟨T, by
    have hTc : T.1.content.toList ≠ [] := by
      rwa [T.2, ne_eq, Multiset.fromCounts_eq_nil_iff h0]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    use ⟨max_cell_len T.1 hTc, by
      constructor
      · exact max_cell_len_sub T.1 hTc
      · exact max_cell_len_le_rowLen' T.1 hTc
      ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [restrict_max_cells_content T.1 hTc]
    nth_rw 1 [T.2, Multiset.erase_fromCounts_of_min μ hμ]
    rw [← max_fromCounts_eq_card_sub_one ?_ h0]
    · congr
      exact T.2
    · rwa [T.2] at hTc
    ⟩
  invFun T := ⟨T.1, by simp⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]










lemma entry_eq_ite_max {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    {f : ℕ →₀ ℕ} (hf : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1))
    (T : SemistandardYoungTableau γ) (hT : T.content = μ.fromCounts)
    (hT' : (T.restrict <| γ.sub_le (sub_cond hf)).content =
    (μ.erase (μ.toList.min hμ)).fromCounts) (i j : ℕ) (hij : (i, j) ∈ γ)
    (hij' : (i, j) ∉ γ.sub f) :
    T i j = (if hTc : (T.restrict (γ.sub_le (sub_cond hf))).content.toList = []
    then 0 else (T.restrict (γ.sub_le (sub_cond hf))).content.toList.max hTc + 1) := by
  split_ifs with hc0
  · have hμ0 : μ ≠ 0 := by rwa [ne_eq, ← Multiset.toList_eq_nil]
    rw [hT', Multiset.fromCounts_eq_nil_iff, Multiset.toList_eq_nil,
      Multiset.erase_eq_zero_iff] at hc0
    · simp only [hμ0, false_or] at hc0
      rw [hc0, Multiset.fromCounts_singleton] at hT
      · have hTc : T i j ∈ T.content := T.mem_content_of_mem hij
        rw [hT, Multiset.mem_replicate] at hTc
        exact hTc.2
      · contrapose! h0
        rw [← h0, ← Multiset.mem_toList]
        exact List.min_mem hμ
    · contrapose! h0
      exact Multiset.mem_of_mem_erase h0
  · simp only [hT']
    have h0' : 0 ∉ μ.erase (μ.toList.min hμ) := by
      contrapose! h0
      exact Multiset.mem_of_mem_erase h0
    rw [max_fromCounts_add_one_eq_card ?_ h0',
      Multiset.card_erase_of_mem, Nat.pred_eq_sub_one]
    · have hijs : (i, j) ∈ γ.cells \ (γ.sub f).cells := by
        simp [hij, hij']
      let hijc := mem_content_sdiff_of_mem_sdiff T (γ.sub_le (sub_cond hf)) hijs
      rw [hT, hT', Multiset.erase_fromCounts_of_min μ hμ, Multiset.remove,
        tsub_tsub_cancel_of_le, Multiset.mem_replicate] at hijc
      · exact hijc.2
      · rw [← Multiset.le_count_iff_replicate_le]
    · rw [← Multiset.mem_toList]
      exact List.min_mem hμ
    · rw [ne_eq, ← hT']
      exact hc0



noncomputable
def recEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) (f : ℕ →₀ ℕ) (hf : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) :
    {T : SemistandardYoungTableauWithContent γ μ |
    (T.1.restrict (γ.sub_le (sub_cond hf))).content =
    (μ.erase (μ.toList.min hμ)).fromCounts} ≃
    SemistandardYoungTableauWithContent (γ.sub f) (μ.erase (μ.toList.min hμ)) where
  toFun := fun ⟨T, hT⟩ ↦ ⟨T.1.restrict (γ.sub_le (sub_cond hf)), by
    simp at hT
    simp [SemistandardYoungTableauWithContent, hT]⟩
  invFun := fun ⟨T, hT⟩ ↦ ⟨⟨T.extend (γ.sub_valid hf)
    (if hTc : T.content.toList = [] then 0 else ((T.content.toList.max hTc) + 1))
    (entry_lt_ite_max T), by
    rw [SemistandardYoungTableauWithContent, Set.mem_setOf] at hT ⊢
    rw [extend_content T (γ.sub_le (sub_cond hf)), hT]
    apply_fun Multiset.card at hT
    simp only [content_card_eq_card, Multiset.fromCounts_card] at hT
    rw [hT, h, ← Multiset.sum_erase, Nat.add_sub_cancel]
    · suffices (if hμ' : (μ.erase (μ.toList.min hμ)).fromCounts.toList = [] then 0 else
          (μ.erase (μ.toList.min hμ)).fromCounts.toList.max hμ' + 1) =
          (μ.erase (μ.toList.min hμ)).card by
        rw [this, ← Multiset.cons_fromCounts_of_min]
        · congr
          refine Multiset.cons_erase ?_
          rw [← Multiset.mem_toList]
          exact List.min_mem hμ
        · intro m hm
          refine List.min_le_of_mem ?_
          rw [Multiset.mem_toList]
          exact Multiset.mem_of_mem_erase hm
      have h0' : 0 ∉ (μ.erase (μ.toList.min hμ)) := by
        contrapose! h0
        exact Multiset.mem_of_mem_erase h0
      by_cases! hTc : (μ.erase (μ.toList.min hμ)).fromCounts.toList = []
      · simp only [hTc, ↓reduceDIte]
        rw [Multiset.fromCounts_eq_nil_iff h0', Multiset.toList_eq_nil] at hTc
        rw [hTc, Multiset.card_zero]
      · simp only [hTc, ↓reduceDIte]
        exact max_fromCounts_add_one_eq_card hTc h0'
    · rw [← Multiset.mem_toList]
      exact List.min_mem hμ
    ⟩, by
    rw [SemistandardYoungTableauWithContent, Set.mem_setOf] at hT
    rw [Set.mem_setOf, T.extend_restrict, hT]
    ⟩
  left_inv := by
    simp only [Function.LeftInverse, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall,
      Subtype.mk.injEq]
    intro T hT hT'
    symm
    nth_rw 1 [← T.restrict_extend (γ.sub_le (sub_cond hf))]
    exact entry_eq_ite_max hμ h0 hf T hT hT'
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Subtype.forall, Subtype.mk.injEq]
    intro T _
    exact T.extend_restrict (γ.sub_le (sub_cond hf)) (γ.sub_valid hf)
      _ (entry_lt_ite_max T)



theorem kostka_recursion {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) : kostkaNumber γ μ =
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) (μ.erase (μ.toList.min hμ)) := by
  classical
  rw [kostkaNumber_eq_card_ssyt_content, Nat.card_congr (unionEquiv γ μ hμ h0),
    Nat.card_eq_finsetCard, Finset.card_biUnion]
  · congr
    ext f
    rw [kostkaNumber_eq_card_ssyt_content, ← Nat.card_congr (recEquiv γ μ hμ h0 h f.1 f.2.1)]
    refine (Nat.subtype_card _ ?_).symm
    split
    simp
  · intro ⟨f, hf⟩ _ ⟨g, hg⟩ _ hfg s hfs hgs ⟨T, hT⟩ hTs
    contrapose! hfg
    suffices f = g by simp [this]
    specialize hfs hTs
    specialize hgs hTs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfs hgs
    rw [SemistandardYoungTableauWithContent, Set.mem_setOf] at hT
    by_contra! hfg
    apply exists_mem_sdiff_of_ne hf.1 hg.1 hf.2 hg.2 at hfg
    obtain ⟨x, hxγ, hx⟩ := hfg
    wlog hx' : (x ∈ (γ.sub f).cells \ (γ.sub g).cells) generalizing f g
    · exact this g hg (by assumption) f hf (by assumption) hgs hfs (by rwa [Or.comm]) (by
        simpa [hx'] using hx)
    simp only [Finset.mem_sdiff, mem_cells] at hx'
    let Tf := T.restrict (γ.sub_le (sub_cond hf.1))
    let Tg := T.restrict (γ.sub_le (sub_cond hg.1))
    have hxm : Tf x.1 x.2 ∈ Tf.content := mem_content_of_mem hx'.1
    rw [hfs, Multiset.erase_fromCounts_of_min μ hμ, restrict_entry _ _ _ _ hx'.1,
      Multiset.mem_remove_of_mem] at hxm
    · have hxc : T x.1 x.2 ∈ T.content - Tg.content :=
        mem_content_sdiff_of_mem_sdiff T (γ.sub_le (sub_cond hg.1)) (by simp [hxγ, hx'.2])
      rw [hT, hgs, Multiset.erase_fromCounts_of_min μ hμ, Multiset.remove, tsub_tsub_cancel_of_le,
        Multiset.mem_replicate] at hxc
      · rw [← hxc.2] at hxm
        contradiction
      · rw [← Multiset.le_count_iff_replicate_le]
    · rw [← hT]
      exact mem_content_of_mem hxγ





lemma sum_support_subRowLensType_le_card {γ : YoungDiagram} (f : SubRowLensType γ) :
    ∑ x ∈ f.1.support, f.1 x ≤ γ.card := by
  rw [card_eq_sum_rowLen, Fin.sum_univ_eq_sum_range]
  simp only [← rowLen'_eq_rowLen]
  have hfs : f.1.support ⊆ Finset.range (γ.rowLens.length + 1) := by
    intro x
    simp only [Finsupp.mem_support_iff, ne_eq, length_rowLens, Finset.mem_range,
      Order.lt_add_one_iff]
    contrapose!
    intro hx
    suffices γ.rowLen x = 0 by
      rw [← Nat.le_zero, ← this]
      exact f.2.2 x
    exact γ.rowLen_eq_zero (by lia)
  refine le_trans (Finset.sum_le_sum_of_subset hfs) <| Finset.sum_le_sum ?_
  intro i hi
  exact f.2.2 i

lemma sum_subRowLensSumType {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ [])
    (h0 : 0 ∉ μ) (k : ℕ) (h : γ.card - k = μ.sum) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) μ =
    ∑ f : SubRowLensType γ with (∑ x ∈ f.1.support, f.1 x = k), kostkaNumber (γ.sub f.1) μ := by
  classical
  refine (Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_).symm
  · intro f _
    exact Finset.mem_univ f
  · intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hf
    refine kostka_ne_card _ _ ?_
    rw [card_sub (sub_cond f.2.1) f.2.2]
    have hcf := sum_support_subRowLensType_le_card f
    have hμ0 : μ.sum ≠ 0 := by
      rwa [ne_eq, Multiset.sum_eq_zero_iff_eq_zero h0, ← Multiset.toList_eq_nil]
    lia
  · intro _ _
    rfl

lemma sum_subRowLensType_with_sum_eq {γ : YoungDiagram} {μ : Multiset ℕ} {hμ : μ.toList ≠ []}
    (h : γ.card = μ.sum) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1)
    (μ.erase (μ.toList.min hμ)) = ∑ f : SubRowLensType γ with (∑ x ∈ f.1.support,
    f.1 x = μ.toList.min hμ), kostkaNumber (γ.sub f.1)
    (μ.erase (μ.toList.min hμ)) := by
  classical
  refine (Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_).symm
  · intro f _
    exact Finset.mem_univ f
  · intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hf
    refine kostka_ne_card _ _ ?_
    rw [card_sub (sub_cond f.2.1) f.2.2]
    have hcf := sum_support_subRowLensType_le_card f
    have hme : μ.toList.min hμ + (μ.erase (μ.toList.min hμ)).sum = μ.sum :=
      Multiset.sum_erase <| by rw [← Multiset.mem_toList]; exact List.min_mem hμ
    have hmm : μ.toList.min hμ ≤ μ.sum :=
      Multiset.le_sum_of_mem <| (by rw [← Multiset.mem_toList]; exact List.min_mem hμ)
    lia
  · intro _ _
    rfl

theorem kostka_recursion' {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) :
    kostkaNumber γ μ = ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = μ.toList.min hμ,
    kostkaNumber (γ.sub f.1) (μ.erase (μ.toList.min hμ)) := by
  rw [kostka_recursion hμ h0 h, sum_subRowLensType_with_sum_eq h]
