import Mathlib
import KostkaNumbers.Content


open YoungDiagram SemistandardYoungTableau

/-
This file proves that the zeros in the tableau have to be located in the first
  row.  In particular, if a tableau has content μ.fromCounts, then the zeros are
  located precisely in the cells of the first row whose column is strictly less
  than the maximum element of μ.
-/

variable {γ : YoungDiagram}

lemma zero_of_left_zero (T : SemistandardYoungTableau γ) {i j1 j2 : ℕ} (hj : j1 ≤ j2)
    (hij : (i, j2) ∈ γ) (h : T i j2 = 0) : T i j1 = 0 := by
  rw [← Nat.le_zero, ← h]
  exact T.row_weak_of_le hj hij


def content_zero_equiv (i j : ℕ) : {x : ℕ × ℕ | x.1 = i ∧ x.2 ≤ j} → Fin (j+1) :=
  fun ⟨x, hx⟩ ↦
  ⟨x.2, by
    rw [Set.mem_setOf] at hx
    exact Order.lt_add_one_iff.mpr hx.2⟩
lemma content_equiv_bijective (i j : ℕ) : Function.Bijective <| content_zero_equiv i j := by
  constructor
  · intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [Set.mem_setOf] at hx hy
    rw [Subtype.mk.injEq]
    simp only [Fin.mk.injEq, content_zero_equiv] at hxy
    ext
    · rw [hx.1, hy.1]
    · exact hxy
  · intro k
    use ⟨(i, k), by simp; omega⟩
    simp [content_zero_equiv]

noncomputable
instance fintypeRowLe (i j : ℕ) : Fintype {x : ℕ × ℕ | x.1 = i ∧ x.2 ≤ j} :=
  Fintype.ofInjective (content_zero_equiv i j) (content_equiv_bijective i j).1

lemma content_zero_card (i j : ℕ) : {x : ℕ × ℕ | x.1 = i ∧ x.2 ≤ j}.toFinset.card = j + 1 := by
  rw [Set.toFinset_card, Fintype.card_of_bijective (content_equiv_bijective i j),
    Fintype.card_fin]


theorem entry_zero_of_lt_max_el (T : SemistandardYoungTableau γ) {μ : Multiset ℕ} (hμ : μ ≠ 0)
    (hc : T.content = μ.fromCounts) {j : ℕ} (hij : (0, j) ∈ γ)
    (hj : j < max_el μ hμ) : T 0 j = 0 := by
  by_cases hj0 : j = 0
  · rw [hj0]
    refine top_left_of_content_fromCounts ?_ hc
    contrapose! hij
    rw [hij]
    exact notMem_bot (0, j)

  rw [← Nat.le_zero]
  apply_fun Multiset.count 0 at hc
  contrapose! hc
  refine ne_of_lt ?_
  rw [content, Multiset.count_map, Multiset.count_fromCounts ?_,
    ← max_el_eq_get_zero_of_ge_sort μ hμ]
  swap
  · rw [Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero]
    exact hμ
  simp only
  suffices (Multiset.filter (fun x ↦ 0 = T x.1 x.2) γ.cells.val).toFinset ⊆
      {x : ℕ × ℕ | x.1 = 0 ∧ x.2 ≤ j - 1}.toFinset by
    apply Finset.card_le_card at this
    rw [← Multiset.toFinset_card_eq_card_iff_nodup.mpr]
    refine lt_of_le_of_lt this ?_
    rw [content_zero_card, Nat.sub_one_add_one hj0]
    exact hj

    exact Multiset.Nodup.filter _ γ.cells.nodup

  simp only [Multiset.toFinset_filter, Finset.val_toFinset, Set.subset_toFinset, Finset.coe_filter,
    mem_cells, Set.setOf_subset_setOf, and_imp, Prod.forall]
  intro a b hab habT
  have ha : a = 0 := by
    rw [← Nat.le_zero, habT]
    exact entry_ge_col hab
  constructor
  · exact ha
  · contrapose! hc
    nth_rw 2 [habT]
    rw [ha]; rw [ha] at hab
    have hjb : j ≤ b := Nat.le_of_pred_lt hc
    exact T.row_weak_of_le hjb hab

theorem lt_max_el_of_entry_zero (T : SemistandardYoungTableau γ) {μ : Multiset ℕ} (hμ : μ ≠ 0)
    (hc : T.content = μ.fromCounts) {i j : ℕ} (hij : (i, j) ∈ γ)
    (h : T i j = 0) : i = 0 ∧ j < max_el μ hμ := by
  constructor
  · rw [← Nat.le_zero, ← h]
    exact entry_ge_col hij
  · contrapose! hc
    suffices Multiset.count 0 T.content ≠ Multiset.count 0 μ.fromCounts by
      contrapose! this
      rw [this]
    rw [Multiset.count_fromCounts ?_, ← max_el_eq_get_zero_of_ge_sort μ hμ]
    · refine ne_of_gt ?_
      simp [content, Multiset.count_map]
      suffices {x : ℕ × ℕ | x.1 = i ∧ x.2 ≤ j}.toFinset ⊆
          (Multiset.filter (fun x ↦ 0 = T x.1 x.2) γ.cells.val).toFinset by
        rw [← Multiset.toFinset_card_eq_card_iff_nodup.mpr]
        apply Finset.card_le_card at this
        refine lt_of_lt_of_le ?_ this
        rw [content_zero_card]
        exact Order.lt_add_one_iff.mpr hc

        exact Multiset.Nodup.filter _ γ.cells.nodup
      intro x
      simp only [Set.mem_toFinset, Set.mem_setOf_eq, Multiset.toFinset_filter,
        Finset.val_toFinset, Finset.mem_filter, mem_cells, and_imp]
      intro hx1 hx2
      constructor
      · exact γ.up_left_mem (Nat.le_of_eq hx1) hx2 hij
      · symm
        rw [hx1]
        exact zero_of_left_zero T hx2 hij h
    · rw [Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero]
      exact hμ

theorem zero_iff_of_mem (T : SemistandardYoungTableau γ) {μ : Multiset ℕ} (hμ : μ ≠ 0)
    (hc : T.content = μ.fromCounts) {i j : ℕ} (hij : (i, j) ∈ γ) :
    T i j = 0 ↔ i = 0 ∧ j < max_el μ hμ := by
  constructor
  · exact lt_max_el_of_entry_zero T hμ hc hij
  · intro ⟨hi, hj⟩
    rw [hi] at hij
    rw [hi]
    exact entry_zero_of_lt_max_el T hμ hc hij hj
