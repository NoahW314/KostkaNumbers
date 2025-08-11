import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.ComputationProof.RowColEq

open Kostka YoungDiagram SemistandardYoungTableau

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
  unfold content
  let γ := horizontalDiagram μ.card
  have hγ : γ.cells = (γ.row 0) := by
    ext i
    simp only [horizontalDiagram, mem_cells, mem_ofRowLens, List.getElem_singleton,
      List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff, exists_prop,
      mem_row_iff, γ]
    conv => rhs ; rw [And.comm]; simp only [and_self_left]
  rw [hγ, ← map_row, Multiset.map_coe, ← List.ofFn_eq_map]
  conv => rhs; rw [← Multiset.coe_toList μ]
  suffices (List.ofFn (fun k : Fin (γ.rowLen 0) ↦ (horizontal_ofMultiset μ) 0 k)) =
      μ.toList.mergeSort (· ≤ ·) by
    rw [this, Multiset.coe_eq_coe]
    exact List.mergeSort_perm _ _
  have hc : γ.rowLen 0 = μ.card := by
    rw [rowLen_eq_card, ← hγ]
    simp [γ]
  have hc2 : μ.card = (μ.toList.mergeSort (· ≤ ·)).length := by simp
  simp [hc, horizontal_ofMultiset, DFunLike.coe]
  conv => rhs; rw [← List.ofFn_getElem (μ.toList.mergeSort (· ≤ ·))]
  congr
  exact (Fin.heq_fun_iff hc2).mpr (congrFun rfl)

variable {γ : YoungDiagram}

lemma eq_horizontal_ofMultiset_content {n : ℕ}
    (T : SemistandardYoungTableau γ) (h : γ = horizontalDiagram n) :
    T.entry = (horizontal_ofMultiset (T.content)).entry := by
  have hn : n = T.content.card := by rw [content_card_eq_card, h, horizontalDiagram_card]
  rw [hn] at h
  refine eq_of_missing_row'' T (horizontal_ofMultiset (T.content)) h ?_ 0 ?_
  · rw [content_horizontal_ofMultiset]
  · intro i hi j
    rw [T.zeros, (horizontal_ofMultiset T.content).zeros]
    · simp [hi]
    · rw [h]
      simp [hi]

lemma eq_horizontal_ofMultiset_content' {n : ℕ}
    (T : SemistandardYoungTableau (horizontalDiagram n)) :
    T.entry = (horizontal_ofMultiset (T.content)).entry := by
  exact eq_horizontal_ofMultiset_content T rfl



theorem kostka_horizontal (μ : Multiset ℕ) :
    kostkaNumber (horizontalDiagram μ.sum) μ = 1 := by
  unfold kostkaNumber
  rw [Nat.card_eq_one_iff_exists, ← Multiset.fromCounts_card]
  use ⟨horizontal_ofMultiset μ.fromCounts, by
    rw [Set.mem_setOf, content_horizontal_ofMultiset]⟩
  intro ⟨T, hT⟩
  rw [Subtype.mk.injEq]; rw [Set.mem_setOf] at hT
  ext i j; simp only [DFunLike.coe]
  rw [eq_horizontal_ofMultiset_content' T]
  congr


theorem kostka_horizontal' (n : ℕ) (μ : Multiset ℕ) :
    kostkaNumber (horizontalDiagram n) μ = 1 ↔ μ.sum = n := by
  constructor; swap
  · intro h
    rw [← h]
    exact kostka_horizontal μ
  contrapose!
  intro h; symm at h
  rw [kostka_ne_card]
  · exact zero_ne_one
  simp [h]
