import Mathlib
import KostkaNumbers.Content
import KostkaNumbers.HorizontalDiagram

open YoungDiagram SemistandardYoungTableau

lemma card_of_exists {M : Multiset ℕ} {m : ℕ} (h : ∃ x ∈ M, x < m) :
    M.card+1 ≥ 2 := by
  suffices M.card ≠ 0 by omega
  rw [ne_eq, Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
  push_neg
  obtain ⟨x, h⟩ := h
  use x; exact h.1

def hookDiagram (n : ℕ) := if h0 : n = 0 then (⊥ : YoungDiagram) else
  if h1 : n = 1 then horizontalDiagram 1 else
  ofRowLens [n-1, 1] (by simp; omega)

@[simp] lemma mem_hookDiagram (n : ℕ) {x : ℕ × ℕ} (hn : n ≥ 2) : x ∈ hookDiagram n ↔
    (x.1 = 1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ x.2 < n-1) := by
  have h0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  have h1 : n ≠ 1 := by exact Ne.symm (Nat.ne_of_lt hn)
  have hx : x = (1, 0) ↔ (x.1 = 1 ∧ x.2 = 0) := by
    constructor; intro hx
    rw [hx]; simp
    intro hx
    ext; simp [hx]; simp [hx]
  have ha : (∃ a < n - 1, (0, a) = x) ↔ (x.1 = 0 ∧ x.2 < n - 1) := by
    constructor; intro ha
    obtain ⟨a, ha, hax⟩ := ha
    simp [← hax, ha]
    intro ha; use x.2
    simp [← ha.1, ha.2]
  rw [Or.comm]
  simp [h0, h1, hookDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, hx, ha]

@[simp] lemma hookDiagram_zero : hookDiagram 0 = ⊥ := by simp [hookDiagram]

lemma hookDiagram_card (n : ℕ) : (hookDiagram n).card = n := by
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · simp [hookDiagram, h1]

  simp [hookDiagram, YoungDiagram.card, h0, h1, ofRowLens, YoungDiagram.cellsOfRowLens]
  exact Nat.succ_pred_eq_of_ne_zero h0



-- m is the entry in the second row. accompied by a proof that m is greater than
--   the smallest element of M
noncomputable
def hook_ofMultiset (M : Multiset ℕ) (m : ℕ) (h : ∃ x ∈ M, x < m) :
    SemistandardYoungTableau (hookDiagram (M.card+1)) :=
  ⟨fun i j ↦ if i = 1 ∧ j = 0 then m else
  if hj : i = 0 ∧ j < M.card then (M.toList.mergeSort (· ≤ ·))[j]'(by
  simp [List.length_mergeSort, hj]) else 0,
  by
  intro i j1 j2 hj
  simp [card_of_exists h]
  intro hij
  rcases hij with hij|hij
  · omega
  · have hj1 : j1 < M.card := by omega
    simp [hij, hj1]
    exact List.Sorted.rel_get_of_lt (List.sorted_mergeSort' _ _) hj
  ,
  by
  intro i1 i2 j hi
  simp [card_of_exists h]
  intro hij
  rcases hij with hij|hij
  · have hij2 : i1 = 0 ∧ 0 < M.card := by
      let hmc := card_of_exists h
      omega
    simp [hij2, hij]
    obtain ⟨x, hM, hm⟩ := h
    refine lt_of_le_of_lt ?_ hm
    rw [List.getElem_zero_eq_head]
    refine List.Pairwise.rel_head (List.sorted_mergeSort' (· ≤ ·) _) ?_
    rw [List.mem_mergeSort, Multiset.mem_toList]
    exact hM
  · omega
  ,
  by
  intro i j
  simp only [ge_iff_le, card_of_exists h, mem_hookDiagram, add_tsub_cancel_right, not_or]
  intro ⟨hij0, hij1⟩
  simp [hij0, hij1]
  ⟩


@[simp] lemma hook_ofMultiset10 {M : Multiset ℕ} {m : ℕ} {h : ∃ x ∈ M, x < m} :
    (hook_ofMultiset M m h) 1 0 = m := by
  simp [hook_ofMultiset, DFunLike.coe]



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
