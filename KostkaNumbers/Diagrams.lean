import Mathlib
import KostkaNumbers.Util.Util

/-
Additional lemmas about young diagrams that I need
-/

namespace YoungDiagram


@[simp] lemma bot_card : (⊥ : YoungDiagram).card = 0 := by simp

variable {γ : YoungDiagram}

lemma zero_notMem_rowLens : 0 ∉ Multiset.ofList γ.rowLens := by
  by_contra! h
  apply γ.pos_of_mem_rowLens at h
  contradiction

lemma eq_bot_iff_forall_notMem : γ = ⊥ ↔ ∀ i j : ℕ, (i, j) ∉ γ := by
  constructor
  · intro h
    simp [h]
  · intro h
    ext x
    simp only [mem_cells, cells_bot, Finset.notMem_empty, iff_false]
    exact h x.1 x.2

lemma eq_bot_iff_forall_notMem' : γ = ⊥ ↔ ∀ x : ℕ × ℕ , x ∉ γ := by
  simp [eq_bot_iff_forall_notMem]

lemma eq_bot_iff_card_eq_zero : γ = ⊥ ↔ γ.card = 0 := by
  constructor
  · intro h
    rw [h, bot_card]
  · intro h
    rw [Finset.card_eq_zero] at h
    ext x
    simp [h]

lemma eq_bot_iff_zero_zero_notMem : γ = ⊥ ↔ (0, 0) ∉ γ := by
  constructor
  · intro h
    rw [eq_bot_iff_forall_notMem] at h
    exact h 0 0
  · contrapose!
    intro h
    rw [ne_eq, eq_bot_iff_forall_notMem] at h
    push_neg at h
    obtain ⟨i, j, hij⟩ := h
    exact γ.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hij


lemma colLen_le_of_le {γ γ' : YoungDiagram} (h : γ' ≤ γ) : γ'.colLen 0 ≤ γ.colLen 0 := by
  refine Nat.le_of_not_gt ?_
  rw [gt_iff_lt, ← mem_iff_lt_colLen]
  by_contra!
  apply h at this
  simp [mem_iff_lt_colLen] at this


lemma cells_add_sub_row (i : ℕ) : (γ.cells.val - (γ.row i).val) + (γ.row i).val = γ.cells.val := by
  refine Multiset.add_sub_cancel ?_
  rw [Finset.val_le_iff]
  intro x
  rw [mem_row_iff, mem_cells]
  intro hx
  exact hx.1

lemma cells_add_sub_col (j : ℕ) : (γ.cells.val - (γ.col j).val) + (γ.col j).val = γ.cells.val := by
  refine Multiset.add_sub_cancel ?_
  rw [Finset.val_le_iff]
  intro x
  rw [mem_col_iff, mem_cells]
  intro hx
  exact hx.1


lemma card_sdiff {γ' : YoungDiagram} (h : γ' ≤ γ) :
    γ.card - γ'.card = (γ.cells \ γ'.cells).card := by
  rw [YoungDiagram.card, Finset.card_sdiff h]


lemma rowLen_eq_filter {n : ℕ} : γ.rowLen n = (Multiset.filter
    (fun a ↦ n = if a ∈ γ then a.1 else 0) γ.cells.val).card := by
  suffices Multiset.filter (fun a ↦ n = if a ∈ γ then a.1 else 0) γ.cells.val =
      (γ.cells.filter (fun a ↦ a.1 = n)).val by
    rw [this, ← row, ← Finset.card_def]
    exact γ.rowLen_eq_card
  rw [Finset.filter_val]
  refine Multiset.filter_congr ?_
  intro x hx
  rw [Finset.mem_val, mem_cells] at hx
  simp [hx]
  exact eq_comm


lemma range_colLen_eq_map_dedup (γ : YoungDiagram) : Multiset.range (γ.colLen 0) =
    (Multiset.map (fun a ↦ if a ∈ γ then a.1 else 0) γ.cells.val).dedup := by
  refine Multiset.range_eq_dedup _ ?_ ?_
  · intro n hn
    rw [← mem_iff_lt_colLen] at hn
    simp only [Multiset.mem_map, Finset.mem_val, mem_cells, Prod.exists]
    use n; use 0
    simp [hn]
  · intro n hn
    simp only [Multiset.mem_map, Finset.mem_val, mem_cells, Prod.exists, not_exists, not_and]
    intro i j hij
    simp only [hij, ↓reduceIte]
    contrapose! hn
    rw [← hn, ← mem_iff_lt_colLen]
    exact γ.up_left_mem (by rfl) (Nat.zero_le j) hij



lemma card_eq_sum_rowLens : γ.card = ∑ i : Fin (γ.rowLens.length), γ.rowLens.get i := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion, YoungDiagram.card]
  · congr
    ext x
    simp only [mem_cells, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro h
      use ⟨x.1, by
        rw [length_rowLens, ← mem_iff_lt_colLen]
        exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) h⟩
      rw [mem_row_iff]
      simp [h]
    · intro h
      obtain ⟨a, h⟩ := h
      rw [mem_row_iff] at h
      exact h.1
  simp only [Set.PairwiseDisjoint, Finset.coe_univ]
  intro a _ b _ hab
  simp only [Function.onFun]
  intro s has hbs x hx
  simp only [Finset.bot_eq_empty, Finset.notMem_empty]
  specialize has hx; specialize hbs hx
  rw [mem_row_iff] at has; rw [mem_row_iff] at hbs
  rw [ne_eq, ← Fin.val_eq_val] at hab
  rw [← has.2, ← hbs.2] at hab
  exact hab rfl

lemma card_eq_sum_rowLens' : γ.card = ∑ i : Fin (γ.rowLens.length+1), γ.rowLen i := by
  let r : Fin (γ.rowLens.length+1) := ⟨γ.rowLens.length, Nat.lt_add_one γ.rowLens.length⟩
  have hr : r ∈ Finset.univ := by exact Finset.mem_univ r
  suffices γ.card = ∑ i ∈ Finset.univ.erase r, γ.rowLen i + γ.rowLen r by
    rw [Finset.sum_erase_add] at this
    exact this
    exact hr
  have hrl : ¬γ.rowLen r.1 ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, ← mem_iff_lt_rowLen, mem_iff_lt_colLen]
    unfold r
    simp
  push_neg at hrl
  rw [hrl, card_eq_sum_rowLens, add_zero]
  let e : (i : Fin γ.rowLens.length) → (i ∈ Finset.univ) → Fin (γ.rowLens.length+1) :=
    fun i _ ↦ ⟨i.1, by exact lt_trans i.2 (Nat.lt_add_one γ.rowLens.length)⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · intro ⟨i, hi⟩
    simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, Fin.mk.injEq, and_true,
      forall_const, r, e]
    exact ne_of_lt hi
  · simp only [Finset.mem_univ, Fin.mk.injEq, forall_const, e]
    intro i₁ i₂ hi
    exact Fin.eq_of_val_eq hi
  · simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, exists_const, e, r]
    intro i hi
    have hi : i.1 ≠ γ.rowLens.length := by
      contrapose! hi
      exact Fin.eq_mk_iff_val_eq.mpr hi
    use ⟨i, by omega⟩
  · simp only [Finset.mem_univ, List.get_eq_getElem, get_rowLens, imp_self, implies_true, e]

lemma rowLens_ofRowLens_length_le_length {w : List ℕ} {hw : List.Sorted (· ≥ ·) w} :
    (ofRowLens w hw).rowLens.length ≤ w.length := by
  simp [← Nat.not_lt, ← mem_iff_lt_colLen, ofRowLens, YoungDiagram.mem_cellsOfRowLens]


@[simp] lemma card_ofRowLens {L : List ℕ} {hL : List.Sorted (· ≥ ·) L}
    (hp : ∀ x ∈ L, 0 < x) :
    (ofRowLens L hL).card = L.sum := by
  rw [card_eq_sum_rowLens, rowLens_ofRowLens_eq_self hp]
  simp only [List.get_eq_getElem, Fin.sum_univ_getElem]

lemma rowLen_ofRowLens_eq_zero {L : List ℕ} {hL : List.Sorted (· ≥ ·) L} {i : ℕ}
    (hp : ∀ x ∈ L, 0 < x) (hi : ¬i < L.length) :
    (ofRowLens L hL).rowLen i = 0 := by
  rw [← Nat.le_zero]
  refine Nat.le_of_not_gt ?_
  rw [gt_iff_lt, ← mem_iff_lt_rowLen, mem_iff_lt_colLen, ← length_rowLens,
    rowLens_length_ofRowLens hp]
  exact hi

@[simp] lemma rowLen_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  push_neg at hi
  exact hi


end YoungDiagram
