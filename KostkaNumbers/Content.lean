import Mathlib
import KostkaNumbers.Diagrams
import KostkaNumbers.Util

/-
Definition of the content of a SemistandardYoungTableau, i.e. the multiset of numbers
  in the entries of the tableau.
Also some lemmas about the content of various special types of diagrams
-/

open YoungDiagram

variable {γ : YoungDiagram} {T : SemistandardYoungTableau γ}

namespace SemistandardYoungTableau

def content (T : SemistandardYoungTableau γ) :=
  Multiset.map (fun (i, j) => T i j) (γ.cells).val

@[simp] lemma content_card_eq_card : T.content.card = γ.card := by
  simp [content]

lemma mem_content_of_mem_cells {i j : ℕ} (h : (i, j) ∈ γ) : T i j ∈ T.content := by
  simp only [content, Multiset.mem_map, Finset.mem_val, YoungDiagram.mem_cells, Prod.exists]
  use i; use j

lemma mem_content_of_nonzero {i j : ℕ} (h : T i j ≠ 0) : T i j ∈ T.content := by
  apply mem_content_of_mem_cells
  contrapose! h; exact T.zeros h


def bot_ssyt : SemistandardYoungTableau ⊥ := ⟨0, by simp, by simp, by simp⟩

@[simp] lemma bot_content : bot_ssyt.content = ⊥ := by simp [content]

lemma content_eq_bot_iff : T.content = ⊥ ↔ γ = ⊥ := by
  simp [content]; symm
  exact YoungDiagram.ext_iff

lemma ssyt_bot (T : SemistandardYoungTableau ⊥) : T = bot_ssyt := by
  ext i j
  rw [zeros T (notMem_bot (i, j)), zeros bot_ssyt (notMem_bot (i, j))]

lemma zero_entry_of_bot {i j : ℕ} (h : γ = ⊥) : T i j = 0 := by
  apply T.zeros; rw [h]; apply notMem_bot


lemma zero_notMem_rowLens : 0 ∉ Multiset.ofList γ.rowLens := by
  by_contra! h
  apply γ.pos_of_mem_rowLens at h
  contradiction

lemma entry_lt_rowLens_card (h : T.content = (Multiset.ofList γ.rowLens).fromCounts) {i j : ℕ}
    (hij : (i, j) ∈ γ) : T i j < (Multiset.ofList γ.rowLens).card := by
  suffices T i j ∈ (Multiset.ofList γ.rowLens).fromCounts by
    contrapose! this
    rw [← Multiset.remove_of_notMem (Multiset.ofList γ.rowLens) 0 zero_notMem_rowLens] at this
    exact Multiset.notMem_fromCounts (Multiset.ofList γ.rowLens) (T i j) this
  rw [← h]
  exact mem_content_of_mem_cells hij

lemma range_colLen_eq_map_dedup (γ : YoungDiagram) : Multiset.range (γ.colLen 0) =
    (Multiset.map (fun a ↦ if a ∈ γ then a.1 else 0) γ.cells.val).dedup := by
  have ha : ∀ a ∈ γ.cells.val, (if a ∈ γ then a.1 else 0) = a.1 := by
    intro a ha
    rw [Finset.mem_val, mem_cells] at ha
    simp [ha]
  rw [Multiset.map_congr (by rfl) ha]
  ext n
  simp [Multiset.count_eq_of_nodup, Multiset.nodup_range]
  suffices n < γ.colLen 0 ↔ n ∈ (Multiset.map Prod.fst γ.cells.val).dedup by
    by_cases hn : n < γ.colLen 0
    let hn2 := hn; rw [this] at hn2
    simp [hn, hn2]
    let hn2 := hn; rw [this] at hn2
    simp [hn, hn2]
  simp [← mem_iff_lt_colLen]
  constructor
  · intro h; use 0
  · intro h; obtain ⟨x, h⟩ := h
    exact γ.up_left_mem (by rfl) (Nat.zero_le x) h

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


lemma highestWeight_content : (highestWeight γ).content =
    (Multiset.ofList γ.rowLens).fromCounts := by
  rw [Multiset.eq_fromCounts_iff _ _ zero_notMem_rowLens]
  constructor; swap; constructor; swap; constructor

  · simp [highestWeight, content, DFunLike.coe]
    intro n hn; use n; use 0
    suffices (n, 0) ∈ γ by simp [this]
    exact mem_iff_lt_colLen.mpr hn

  · simp [highestWeight, content, DFunLike.coe]
    intro n hn i j hij
    simp [hij]
    contrapose! hn
    rw [← mem_iff_lt_colLen, ← hn]
    exact γ.up_left_mem (by rfl) (Nat.zero_le j) hij

  · simp only [ge_iff_le, content, DFunLike.coe, highestWeight, to_fun_eq_coe, Prod.mk.eta,
      Multiset.count_map, Multiset.coe_card,
      Multiset.remove_of_notMem (Multiset.ofList γ.rowLens) 0 zero_notMem_rowLens]
    suffices ∀ n ∈ List.range γ.rowLens.length, γ.rowLen n = (Multiset.filter
        (fun a ↦ n = if a ∈ γ then a.1 else 0) γ.cells.val).card by
      rw [← List.map_congr_left this]
      simp
      rw [← YoungDiagram.rowLens]
      exact rowLens_sorted γ
    intro n _
    exact rowLen_eq_filter

  · simp [highestWeight, content, DFunLike.coe, Multiset.counts, rowLens]
    rw [← Multiset.map_coe, Multiset.coe_range]
    refine Multiset.map_congr (Eq.symm (range_colLen_eq_map_dedup γ)) ?_
    intro n hn
    symm
    rw [Multiset.count_map]
    exact rowLen_eq_filter



lemma highestWeight_horizontal_content (n : ℕ) :
    (highestWeight (horizontalDiagram n)).content = Multiset.replicate n 0 := by
  simp [content, horizontalDiagram,
    ofRowLens, YoungDiagram.cellsOfRowLens]



lemma entry_zero_of_content_eq_replicate (n : ℕ)
    (h : T.content = Multiset.replicate n 0) (i j : ℕ) : T i j = 0 := by
  by_cases hb : γ = ⊥
  · exact zero_entry_of_bot hb

  suffices T i j ∈ T.content by
    rw [h] at this
    exact Multiset.eq_of_mem_replicate this
  by_cases htij : T i j = 0
  · rw [htij, h]
    refine Multiset.mem_replicate.mpr ?_
    simp only [ne_eq, and_true]
    contrapose! hb
    rw [hb, Multiset.replicate_zero, ← Multiset.bot_eq_zero, content_eq_bot_iff] at h
    exact h
  exact mem_content_of_nonzero htij




lemma content_horizontal_ofMultiset (μ : Multiset ℕ) :
    (horizontal_ofMultiset μ).content = μ := by
  apply Multiset.induction_on_with_le μ
  · simp [content, Finset.eq_empty_iff_forall_notMem]
  intro n s _ _ hn hs
  simp [content, horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
  congr
  · apply horizontal_ofMultiset_cons_largest_end s hn
  symm; nth_rw 1 [← hs]; symm
  simp [content, horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
  apply Multiset.map_congr rfl
  intro x hx; rw [Multiset.mem_range] at hx
  exact horizontal_ofMultiset_cons_largest s hn x hx

lemma eq_horizontal_ofMultiset_content {n : ℕ}
    (T : SemistandardYoungTableau γ) (h : γ = horizontalDiagram n) :
    T.entry = (horizontal_ofMultiset (T.content)).entry := by
  ext i j
  by_cases hij : ¬(j < T.content.card ∧ i = 0)
  · simp only [horizontal_ofMultiset, hij, reduceDIte]
    apply T.zeros
    rw [h]
    simp only [mem_horizontalDiagram]
    rw [content_card_eq_card, h, horizontalDiagram_card] at hij
    rw [And.comm]; exact hij
  push_neg at hij
  simp only [horizontal_ofMultiset, hij, and_true, reduceDIte]
  rw [List.getElem_map_range n (fun j => T.entry 0 j)]
  · congr
    apply List.eq_of_perm_of_sorted ?_ ?_ (List.sorted_mergeSort' _ _)
    · apply List.Perm.symm
      apply List.Perm.trans (List.mergeSort_perm _ _)
      rw [← Multiset.coe_eq_coe, Multiset.coe_toList]
      simp [content, h, horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
      rw [← Multiset.map_coe, Multiset.coe_range]
    · unfold List.Sorted
      rw [List.pairwise_map, List.pairwise_iff_getElem]
      simp
      intro i j hi hj hij
      apply T.row_weak hij
      simp [h, hj]
  · simp [content_card_eq_card, h, horizontalDiagram_card] at hij
    exact hij.1
  · simp

lemma eq_horizontal_ofMultiset_content' {n : ℕ}
    (T : SemistandardYoungTableau (horizontalDiagram n)) :
    T.entry = (horizontal_ofMultiset (T.content)).entry := by
  exact eq_horizontal_ofMultiset_content T rfl




@[simp] lemma content_hook_ofMultiset (M : Multiset ℕ) (m : ℕ) (h : ∃ x ∈ M, x < m) :
    M.card > 0 → (hook_ofMultiset M m h).content = m ::ₘ M := by
  simp [hook_ofMultiset, content, DFunLike.coe]
  apply Multiset.induction_on_with_le M
  · simp
  intro n s hnM hsM hmn ih hcard
  by_cases hsc : s.card = 0
  · simp [hsc, hookDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
    rw [Multiset.card_eq_zero] at hsc
    simp [hsc, Multiset.union_def, ← Multiset.singleton_add, add_comm]
  · push_neg at hsc
    rw [← Nat.pos_iff_ne_zero] at hsc
    specialize ih hsc
    rw [Multiset.cons_swap, ← ih]

    simp [hookDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, Multiset.union_def]
    congr
    · simp [List.cons_sort_eq_sort_append s hmn]
    · have hs0 : s ≠ 0 := by
        rw [ne_eq, ← Multiset.card_eq_zero]
        push_neg
        rw [← Nat.pos_iff_ne_zero]
        exact hsc
      simp [hs0, Multiset.union_def]
      refine Multiset.map_congr (rfl) ?_
      intro x hx
      rw [Multiset.mem_range] at hx
      have hx' : x < s.card+1 := by omega
      simp [hx, hx', List.cons_sort_eq_sort_append s hmn]


end SemistandardYoungTableau
