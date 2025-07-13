import Mathlib
import KostkaNumbers.Util

/-
Special types of Young diagrams that we will use
-/

namespace YoungDiagram

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

noncomputable
def horizontal_ofCounts (μ : Multiset ℕ) := horizontal_ofMultiset (μ.fromCounts)


lemma horizontal_ofMultiset_cons_largest (μ : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ μ, m ≤ n) :
    ∀ j < μ.card, (horizontal_ofMultiset (n ::ₘ μ)) 0 j =
    (horizontal_ofMultiset μ) 0 j := by
  intro j hj
  have hj2 : j < μ.card + 1 := by omega
  simp only [DFunLike.coe, horizontal_ofMultiset, Multiset.card_cons,
    hj2, and_self, ↓reduceDIte, hj]
  simp [List.cons_sort_eq_sort_append μ h, hj]


lemma horizontal_ofMultiset_cons_largest_end (μ : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ μ, m ≤ n) :
    (horizontal_ofMultiset (n ::ₘ μ)) 0 μ.card = n := by
  simp [DFunLike.coe, horizontal_ofMultiset, List.cons_sort_eq_sort_append μ h]

end YoungDiagram
