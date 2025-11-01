import Mathlib
import KostkaNumbers.Diagrams


namespace YoungDiagram


private lemma sum_Iio_plus_one (γ : YoungDiagram) (i : ℕ) :
    ∑ k ∈ Finset.Iio (i + 1), γ.rowLen k =
    γ.rowLen i + ∑ k ∈ Finset.Iio i, γ.rowLen k := by
  have hi : i ∈ Finset.Iio (i + 1) := by simp
  rw [← Finset.add_sum_erase _ _ hi]
  congr; ext x; simp; omega

lemma colLen_sum_rowLen_eq_card (γ : YoungDiagram) :
    ∑ k < (γ.colLen 0 + 1), γ.rowLen k = γ.card := by
  rw [card_eq_sum_rowLen]
  let e : (k : ℕ) → (hk : k ∈ Finset.Iio (γ.colLen 0 + 1)) → Fin (γ.rowLens.length + 1) :=
    fun k hk ↦ ⟨k, by
      rw [Finset.mem_Iio] at hk
      rw [length_rowLens]
      exact hk⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp
  · simp [e]
  · simp only [Finset.mem_univ, Finset.mem_Iio, forall_const, e]
    intro ⟨b, hb⟩
    use b
    use (by rw [length_rowLens] at hb; exact hb)
  · simp [e]



def cell_index (γ : YoungDiagram) (i j : ℕ) : ℕ :=
  j + ∑ k < i, γ.rowLen k

lemma cell_index_lt_card (γ : YoungDiagram) (i j : ℕ) (h : (i, j) ∈ γ) :
    γ.cell_index i j < γ.card := by
  rw [mem_iff_lt_rowLen] at h
  unfold cell_index
  rw [← colLen_sum_rowLen_eq_card]
  refine lt_of_lt_of_le (add_lt_add_right h _) ?_
  rw [← sum_Iio_plus_one γ i]
  refine Finset.sum_le_sum_of_subset ?_
  refine Finset.Iio_subset_Iio ?_
  rw [← mem_iff_lt_rowLen, mem_iff_lt_colLen] at h
  have hcl := γ.colLen_anti 0 j (Nat.zero_le j)
  omega

lemma cell_index_injective (γ : YoungDiagram) {i j i' j' : ℕ} (hij : (i, j) ∈ γ)
    (hij' : (i', j') ∈ γ) (h : γ.cell_index i j = γ.cell_index i' j') :
    i = i' ∧ j = j' := by
  unfold cell_index at h
  contrapose! h
  by_cases hi : i = i'
  · subst hi
    simp only [forall_const] at h
    simp [h]
  · wlog hil : i < i'
    · push_neg at hi; symm at hi
      symm
      refine this γ hij' hij ?_ hi ?_
      · simp [hi]
      · omega
    · refine ne_of_lt ?_
      calc j + ∑ k ∈ Finset.Iio i, γ.rowLen k
        _ < γ.rowLen i + ∑ k ∈ Finset.Iio i, γ.rowLen k := by simp [← mem_iff_lt_rowLen, hij]
        _ = ∑ k ∈ Finset.Iio (i + 1), γ.rowLen k := by symm; exact sum_Iio_plus_one γ i
        _ ≤ ∑ k ∈ Finset.Iio i', γ.rowLen k := by
          refine Finset.sum_le_sum_of_subset ?_
          exact Finset.Iio_subset_Iio hil
        _ ≤ j' + ∑ k ∈ Finset.Iio i', γ.rowLen k := by omega




lemma exists_lt_sum (γ : YoungDiagram) (n : ℕ) (h : n < γ.card) :
    ∃ i, n < ∑ k < i, γ.rowLen k := by
  use (γ.colLen 0 + 1)
  rw [colLen_sum_rowLen_eq_card γ]
  exact h

lemma exists_cell_index_eq (γ : YoungDiagram) (n : ℕ) (h : n < γ.card) :
    ∃ x : ℕ × ℕ, x ∈ γ ∧ γ.cell_index x.1 x.2 = n := by
  use ((Nat.find (exists_lt_sum γ n h) - 1),
    (n - ∑ k < (Nat.find (exists_lt_sum γ n h)) - 1, γ.rowLen k))
  constructor
  · by_cases hn : Nat.find (exists_lt_sum γ n h) = 0
    · have h' := Nat.find_spec (exists_lt_sum γ n h)
      simp [hn] at h'
    rw [mem_iff_lt_rowLen]
    have hn := Nat.find_spec (exists_lt_sum γ n h)
    have this := sum_Iio_plus_one γ (Nat.find (exists_lt_sum γ n h) - 1)
    rw [show Nat.find (exists_lt_sum γ n h) - 1 + 1 =
      Nat.find (exists_lt_sum γ n h) by omega] at this
    rw [this] at hn
    suffices ¬ n < ∑ k < (Nat.find (exists_lt_sum γ n h)) - 1, γ.rowLen k by omega
    exact Nat.find_min (exists_lt_sum γ n h) (by omega)
  · unfold cell_index
    by_cases hn : Nat.find (exists_lt_sum γ n h) = 0
    · simp [hn]
    simp
    suffices ¬ n < ∑ k < (Nat.find (exists_lt_sum γ n h)) - 1, γ.rowLen k by omega
    exact Nat.find_min (exists_lt_sum γ n h) (by omega)

noncomputable
def nth_cell (γ : YoungDiagram) (n : ℕ) (h : n < γ.card) :=
  Classical.choose (exists_cell_index_eq γ n h)


lemma nth_cell_mem {γ : YoungDiagram} {n : ℕ} (h : n < γ.card) :
    γ.nth_cell n h ∈ γ :=
  (Classical.choose_spec (exists_cell_index_eq γ n h)).1

lemma nth_cell_index (γ : YoungDiagram) (n : ℕ) (h : n < γ.card) :
    γ.cell_index (γ.nth_cell n h).1 (γ.nth_cell n h).2 = n :=
  (Classical.choose_spec (exists_cell_index_eq γ n h)).2

lemma cell_index_cell (γ : YoungDiagram) (i j : ℕ) (h : (i, j) ∈ γ) :
    γ.nth_cell (γ.cell_index i j) (γ.cell_index_lt_card i j h) = (i, j) := by
  unfold cell_index nth_cell
  obtain ⟨hγ, h'⟩ := Classical.choose_spec (exists_cell_index_eq γ (γ.cell_index i j)
    (γ.cell_index_lt_card i j h))
  apply γ.cell_index_injective hγ h at h'
  obtain ⟨left, right⟩ := h'
  ext : 1
  · simp_all only
    exact left
  · simp_all only
    exact right


end YoungDiagram
