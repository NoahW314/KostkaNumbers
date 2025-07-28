import Mathlib
import KostkaNumbers.Util
import KostkaNumbers.Content

open YoungDiagram SemistandardYoungTableau

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



lemma highestWeight_horizontal_content (n : ℕ) :
    (highestWeight (horizontalDiagram n)).content = Multiset.replicate n 0 := by
  simp [content, horizontalDiagram,
    ofRowLens, YoungDiagram.cellsOfRowLens]



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

variable {γ : YoungDiagram}

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
