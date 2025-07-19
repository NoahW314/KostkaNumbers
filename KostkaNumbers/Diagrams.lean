import Mathlib
import KostkaNumbers.Util

/-
Special types of Young diagrams that we will use
-/

namespace YoungDiagram

@[simp] lemma bot_card : (⊥ : YoungDiagram).card = 0 := by simp



def horizontalDiagram (n : ℕ) := ofRowLens [n] <| List.sorted_singleton n

@[simp] lemma mem_horizontalDiagram (n : ℕ) (x : ℕ × ℕ) : x ∈ horizontalDiagram n ↔
    x.1 = 0 ∧ x.2 < n := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
  constructor
  · intro ⟨j, h⟩
    simp [← h.2, h.1]
  · intro h
    use x.2
    constructor
    · exact h.2
    · rw [← h.1]

lemma horizontalDiagram_succ (n : ℕ) :
    (horizontalDiagram (n+1)).cells.val = (0,n) ::ₘ (horizontalDiagram n).cells.val := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]


@[simp] lemma horizontalDiagram_card {n : ℕ} : (horizontalDiagram n).card = n := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, YoungDiagram.card]



noncomputable
def horizontal_ofMultiset (M : Multiset ℕ) :
    SemistandardYoungTableau (horizontalDiagram M.card) :=
  ⟨fun i j => if h : j < M.card ∧ i = 0 then (M.toList.mergeSort (· ≤ ·))[j]'(by
  simp [List.length_mergeSort]; exact h.1) else 0,
  by
  simp only [mem_horizontalDiagram, and_imp]
  intro i j1 j2 hj hi hj2; symm at hi
  have hj1 : j1 < M.card := by apply lt_trans hj hj2
  simp only [hj1, hi, and_self, ↓reduceDIte, hj2, ge_iff_le]
  apply List.Sorted.rel_get_of_lt
  · apply List.sorted_mergeSort' (· ≤ ·) M.toList
  · rw [Fin.mk_lt_mk]; exact hj
  ,
  by
  simp only [mem_horizontalDiagram, and_imp]
  intro i1 i2 j hi hi2
  omega
  ,
  by
  simp only [mem_horizontalDiagram]
  intro i j hij; rw [And.comm] at hij
  simp only [hij, ↓reduceDIte]
  ⟩



lemma horizontal_ofMultiset_cons_largest (M : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ M, m ≤ n) :
    ∀ j < M.card, (horizontal_ofMultiset (n ::ₘ M)) 0 j =
    (horizontal_ofMultiset M) 0 j := by
  intro j hj
  have hj2 : j < M.card + 1 := by omega
  simp only [DFunLike.coe, horizontal_ofMultiset, Multiset.card_cons,
    hj2, and_self, ↓reduceDIte, hj]
  simp [List.cons_sort_eq_sort_append M h, hj]


lemma horizontal_ofMultiset_cons_largest_end (M : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ M, m ≤ n) :
    (horizontal_ofMultiset (n ::ₘ M)) 0 M.card = n := by
  simp [DFunLike.coe, horizontal_ofMultiset, List.cons_sort_eq_sort_append M h]




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


lemma card_of_exists {M : Multiset ℕ} {m : ℕ} (h : ∃ x ∈ M, x < m) :
    M.card+1 ≥ 2 := by
  suffices M.card ≠ 0 by omega
  rw [ne_eq, Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
  push_neg
  obtain ⟨x, h⟩ := h
  use x; exact h.1

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


end YoungDiagram
