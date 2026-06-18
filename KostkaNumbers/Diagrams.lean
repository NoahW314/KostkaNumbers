/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Util.Util

/-
Additional lemmas about young diagrams that I need
-/

namespace YoungDiagram

-- upstream
@[simp] lemma bot_card : (⊥ : YoungDiagram).card = 0 := by simp

-- upstream
@[simp] lemma bot_rowLens : (⊥ : YoungDiagram).rowLens = [] := by
  simp [rowLens, colLen]

variable {γ : YoungDiagram}


lemma eq_bot_iff_forall_notMem : γ = ⊥ ↔ ∀ i j : ℕ, (i, j) ∉ γ := by
  constructor
  · grind [notMem_bot]
  · intro h
    ext x
    grind [mem_cells, cells_bot]

-- upstream
lemma eq_bot_iff_card_eq_zero : γ = ⊥ ↔ γ.card = 0 := by
  constructor
  · grind [bot_card]
  · intro h
    ext x
    grind [cells_bot]

lemma eq_bot_iff_zero_zero_notMem : γ = ⊥ ↔ (0, 0) ∉ γ := by
  constructor
  · intro h
    rw [eq_bot_iff_forall_notMem] at h
    exact h 0 0
  · contrapose!
    intro h
    rw [ne_eq, eq_bot_iff_forall_notMem] at h
    push Not at h
    obtain ⟨i, j, hij⟩ := h
    exact γ.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hij



lemma rowLens_eq_iff {γ γ' : YoungDiagram} : γ.rowLens = γ'.rowLens ↔ γ = γ' := by
  constructor
  · intro h
    rw [← equivListRowLens_apply_coe, ← equivListRowLens_apply_coe, Subtype.coe_inj] at h
    exact equivListRowLens.injective h
  · intro h
    rw [h]

lemma rowLens_eq_iff' {γ γ' : YoungDiagram} : Multiset.ofList γ.rowLens =
    Multiset.ofList γ'.rowLens ↔ γ = γ' := by
  constructor
  · intro h
    rw [← rowLens_eq_iff]
    refine List.Perm.eq_of_sortedGE γ.rowLens_sorted γ'.rowLens_sorted ?_
    rw [← Multiset.coe_eq_coe, h]
  · intro h
    rw [h]

-- upstream
lemma colLen_mono {γ γ' : YoungDiagram} (j : ℕ) (h : γ' ≤ γ) : γ'.colLen j ≤ γ.colLen j := by
  refine Nat.le_of_not_gt ?_
  rw [gt_iff_lt, ← mem_iff_lt_colLen]
  by_contra!
  apply h at this
  simp [mem_iff_lt_colLen] at this


lemma cells_add_sub_row (i : ℕ) : (γ.cells.val - (γ.row i).val) + (γ.row i).val = γ.cells.val := by
  refine Multiset.add_sub_cancel ?_
  rw [Finset.val_le_iff]
  exact Finset.filter_subset _ _

lemma cells_add_sub_col (j : ℕ) : (γ.cells.val - (γ.col j).val) + (γ.col j).val = γ.cells.val := by
  refine Multiset.add_sub_cancel ?_
  rw [Finset.val_le_iff]
  exact Finset.filter_subset _ _

lemma card_sdiff {γ' : YoungDiagram} (h : γ' ≤ γ) :
    γ.card - γ'.card = (γ.cells \ γ'.cells).card := by
  rw [YoungDiagram.card, Finset.card_sdiff_of_subset h]


lemma rowLen_eq_filter {n : ℕ} : γ.rowLen n = (Multiset.filter
    (fun a ↦ n = if a ∈ γ then a.1 else 0) γ.cells.val).card := by
  rw [rowLen_eq_card, row,
    ← Multiset.toFinset_card_eq_card_iff_nodup.mpr <| Multiset.Nodup.filter _ γ.cells.nodup]
  congr
  ext x
  simp
  grind


lemma cells_eq_biUnion_row : γ.cells = Finset.biUnion
    (Finset.univ : Finset (Fin (γ.rowLens.length))) (fun x ↦ γ.row x) := by
  ext x
  simp only [mem_cells, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro h
    use ⟨x.1, by
      rw [length_rowLens, ← mem_iff_lt_colLen]
      exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) h⟩
    simp [mem_row_iff, h]
  · grind [mem_row_iff]

lemma disjoint_row {i j : ℕ} (h : i ≠ j) : Disjoint (γ.row i) (γ.row j) := by
  intro s has hbs x hx
  simp only [Finset.bot_eq_empty, Finset.notMem_empty]
  specialize has hx
  specialize hbs hx
  grind [mem_row_iff]

lemma card_eq_sum_rowLens_get : γ.card = ∑ i : Fin (γ.rowLens.length), γ.rowLens.get i := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion, YoungDiagram.card, cells_eq_biUnion_row]
  simp only [Set.PairwiseDisjoint, Finset.coe_univ]
  intro a _ b _ hab
  simp only [Function.onFun]
  exact disjoint_row <| Fin.val_ne_of_ne hab

lemma card_eq_sum_rowLen : γ.card = ∑ i : Fin (γ.rowLens.length + 1), γ.rowLen i := by
  let r : Fin (γ.rowLens.length + 1) := ⟨γ.rowLens.length, Nat.lt_add_one γ.rowLens.length⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
  have hrl : ¬ γ.rowLen r.1 ≠ 0 := by
    simp [← Nat.pos_iff_ne_zero, ← mem_iff_lt_rowLen, mem_iff_lt_colLen, r]
  push Not at hrl
  rw [hrl, card_eq_sum_rowLens_get, add_zero]
  let e : (i : Fin γ.rowLens.length) → (i ∈ Finset.univ) → Fin (γ.rowLens.length + 1) :=
    fun i _ ↦ ⟨i.1, lt_trans i.2 (Nat.lt_add_one γ.rowLens.length)⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · grind
  · grind
  · simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, exists_const, e, r]
    intro i hi
    rw [Fin.eq_mk_iff_val_eq] at hi
    use ⟨i, by lia⟩
  · simp only [Finset.mem_univ, List.get_eq_getElem, get_rowLens, imp_self, implies_true, e]

lemma card_eq_sum_rowLens : γ.card = γ.rowLens.sum := by
  simp only [card_eq_sum_rowLens_get, List.get_eq_getElem, Fin.sum_univ_getElem]


lemma length_rowLens_ofRowLens_le_length {w : List ℕ} {hw : w.SortedGE} :
    (ofRowLens w hw).rowLens.length ≤ w.length := by
  simp [← Nat.not_lt, ← mem_iff_lt_colLen, ofRowLens, YoungDiagram.mem_cellsOfRowLens]


@[simp]
lemma card_ofRowLens {L : List ℕ} {hL : L.SortedGE} (hp : ∀ x ∈ L, 0 < x) :
    (ofRowLens L hL).card = L.sum := by
  rw [card_eq_sum_rowLens_get, rowLens_ofRowLens_eq_self hp]
  simp only [List.get_eq_getElem, Fin.sum_univ_getElem]

lemma rowLen_ofRowLens_eq_zero {L : List ℕ} {hL : L.SortedGE} {i : ℕ}
    (hp : ∀ x ∈ L, 0 < x) (hi : ¬i < L.length) :
    (ofRowLens L hL).rowLen i = 0 := by
  rw [← Nat.le_zero]
  refine Nat.le_of_not_gt ?_
  rwa [gt_iff_lt, ← mem_iff_lt_rowLen, mem_iff_lt_colLen, ← length_rowLens,
    rowLens_length_ofRowLens hp]

@[simp]
lemma rowLen_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  exact Function.notMem_support.mp hi



@[simp] lemma rowLen_ofRowLens' {w : List ℕ} {hw : w.SortedGE} {i : ℕ}
    (hi : i < w.length) : (ofRowLens w hw).rowLen i = w[i] := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens, hi]

@[simp] lemma colLen_ofRowLens_two {a b : ℕ} {hab : [a, b].SortedGE} {i : ℕ} :
    (ofRowLens [a, b] hab).colLen i = if i < a then if i < b then 2 else 1 else 0 := by
  split_ifs with ha hb
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind

@[simp] lemma colLen_ofRowLens_three {a b c : ℕ}
    {habc : [a, b, c].SortedGE} {i : ℕ} :
    (ofRowLens [a, b, c] habc).colLen i =
    if i < a then if i < b then if i < c then 3 else 2 else 1 else 0 := by
  split_ifs with ha hb hc
  all_goals simp [colLen, Nat.find_eq_iff, mem_ofRowLens]; grind


end YoungDiagram
