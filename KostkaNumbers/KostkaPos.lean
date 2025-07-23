import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.Dominate

/-
This formalization is based on these proofs given by Matthew Fayers
https://mathoverflow.net/questions/226537/is-there-a-short-proof-that-the-kostka-number-k-lambda-mu-is-non-zero-when
https://arxiv.org/pdf/1903.12499
-/

open Kostka SemistandardYoungTableau YoungDiagram

variable {γ : YoungDiagram} {μ ν : Multiset ℕ}

/-
theorem kostka_antitone (h : Multiset.sort (· ≥ ·) μ ⊵ Multiset.sort (· ≥ ·) ν) :
    kostkaNumber γ μ ≤ kostkaNumber γ ν := by
  sorry
-/

lemma bsum_rowLens {r : ℕ} : ∑ i with i.1 ≤ r, γ.rowLens.get i =
    Finset.card {x ∈ γ.cells | x.1 ≤ r} := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_cells, mem_row_iff]
    constructor
    · intro ⟨a, ha, hx⟩
      simp [hx, ha]
    · intro h
      use ⟨x.1, by
        simp [← mem_iff_lt_colLen]
        exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) h.1
        ⟩
      simp [h]
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.PairwiseDisjoint]
    intro a ha b hb hab
    simp only [Function.onFun]
    intro s has hbs x hx
    simp only [Finset.le_eq_subset] at has; simp only [Finset.le_eq_subset] at hbs
    specialize has hx; specialize hbs hx
    rw [mem_row_iff] at has; rw [mem_row_iff] at hbs
    contrapose! hab
    rw [Fin.mk_eq_mk, ← has.2, ← hbs.2]

theorem dominates_of_kostka_pos (h0 : 0 ∉ μ) (hk : 0 < kostkaNumber γ μ) :
    γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ := by
  rw [kostkaNumber, Nat.pos_iff_ne_zero, ne_eq, Nat.card_eq_zero] at hk
  simp only [Set.coe_setOf, not_or, not_isEmpty_iff, nonempty_subtype,
    not_infinite_iff_finite] at hk
  obtain ⟨T, hT⟩ := hk.1
  intro r
  suffices Finset.card {x ∈ γ.cells | T x.1 x.2 ≤ r} =
      ∑ i with i.1 ≤ r, (Multiset.sort (· ≥ ·) μ).get i by
    rw [bsum_rowLens, ← this]
    refine Finset.card_le_card ?_
    intro x hx
    simp; simp at hx
    obtain ⟨hγ, hx⟩ := hx
    constructor
    · exact hγ
    · contrapose! hx
      refine lt_of_lt_of_le hx ?_
      exact entry_ge_col hγ
  rw [Finset.card_def,
    ← Multiset.card_map (fun x : ℕ × ℕ ↦ T x.1 x.2) {x ∈ γ.cells | T x.1 x.2 ≤ r}.val]
  rw [← Multiset.coe_toList μ, Multiset.coe_sort (· ≥ ·) μ.toList]
  simp
  have hcfc :  ∑ x : Fin (μ.toList.mergeSort (· ≥ ·)).length with x.1 ≤ r,
      (μ.toList.mergeSort (· ≥ ·))[x.1] = ∑ x : Fin (μ.toList.mergeSort (· ≥ ·)).length
      with x.1 ≤ r, Multiset.count x.1 μ.fromCounts := by
    congr
    ext x
    rw [Multiset.count_fromCounts ?_ h0]
    let hx := x.2
    simp at hx
    exact hx
  rw [hcfc, ← hT]
  have hctc : ∀ n, Multiset.count n T.content =
      (Multiset.filter (fun x ↦ T x.1 x.2 = n) γ.cells.val).card := by
    intro n
    simp [content, Multiset.count_map, Eq.comm]
  simp only [hctc]
  rw [← Multiset.card_sum]
  congr
  ext x
  rw [Multiset.count_eq_of_nodup, Multiset.count_eq_of_nodup]
  · congr 1
    simp [Finset.mem_sum]
    constructor
    · intro ⟨hx, hTr⟩
      use ⟨T x.1 x.2, by simp [entry_lt_card hT hx h0]⟩
    · intro ⟨a, har, hx, haT⟩
      simp [har, hx, haT]
  · rw [Multiset.nodup_iff_count_le_one]
    simp [Multiset.count_sum', Multiset.count_filter, Multiset.count_eq_of_nodup γ.cells.nodup]
    intro i j
    by_cases hijγ : (i, j) ∈ γ
    · simp [hijγ]
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_filter] at hb
      rw [Fin.eq_mk_iff_val_eq, ← ha.2, ← hb.2]
    · simp [hijγ]

  · refine Multiset.Nodup.filter _ ?_
    exact γ.cells.nodup

private lemma nat_lemma {a b c d : ℕ} (h1 : a ≥ b) (h2 : b ≥ c) (h3 : c ≥ d) :
  d ≤ a - (b - c) := by omega

private lemma nat_lemma2 {a b c : ℕ} (h1 : a ≥ b) (h2 : b ≥ c) :
  a - (b - c) = c + a - b := by omega



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

lemma sum_rowLen_ofRowLens {w : List ℕ} {hw : List.Sorted (· ≥ ·) w} :
    ∑ i : Fin (ofRowLens w hw).rowLens.length, (ofRowLens w hw).rowLens.get i =
    ∑ i : Fin w.length, w.get i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin (w.length) => i.1 ≥ (ofRowLens w hw).rowLens.length)]
  have hj : ∑ x with x.1 ≥ (ofRowLens w hw).rowLens.length, w.get x = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [length_rowLens, ge_iff_le, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [← Nat.not_lt, ← mem_iff_lt_colLen.not, ofRowLens, ← mem_cells] at hi
    simp only at hi
    rw [YoungDiagram.mem_cellsOfRowLens] at hi
    simp at hi
    exact hi
  rw [hj, zero_add]; simp only [not_le]
  let e : (i : Fin (ofRowLens w hw).rowLens.length) → (i ∈ Finset.univ) →
    Fin w.length := fun i _ ↦ ⟨i, by
      exact lt_of_lt_of_le i.2 rowLens_ofRowLens_length_le_length⟩

  refine Finset.sum_bij e ?_ ?_ ?_ ?_

  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
    exact i.2
  · intro i₁ _ i₂ _
    simp [e]
    exact fun a ↦ Fin.eq_of_val_eq a
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    use ⟨k, hk⟩
    use (by simp)
  · intro i hi
    simp [e]
    exact rowLen_ofRowLens (e i hi)

lemma sum_rowLen_ofRowLens' {w : List ℕ} {hw : List.Sorted (· ≥ ·) w} (r : ℕ) :
    ∑ i : Fin (ofRowLens w hw).rowLens.length with i.1 ≤ r, (ofRowLens w hw).rowLens.get i =
    ∑ i : Fin w.length with i.1 ≤ r, w.get i := by
  rw [← Finset.sum_filter_add_sum_filter_not _
    (fun i : Fin (w.length) => i.1 ≥ (ofRowLens w hw).rowLens.length)]
  have hj : ∑ x ∈ {i | i.1 ≤ r} with x.1 ≥ (ofRowLens w hw).rowLens.length, w.get x = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [length_rowLens, ge_iff_le, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply And.right at hi
    rw [← Nat.not_lt, ← mem_iff_lt_colLen.not, ofRowLens, ← mem_cells] at hi
    simp only at hi
    rw [YoungDiagram.mem_cellsOfRowLens] at hi
    simp at hi
    exact hi
  rw [hj, zero_add]; simp only [not_le]
  let e : (i : Fin (ofRowLens w hw).rowLens.length) →
    (i ∈ ({i | i.1 ≤ r} : Finset (Fin (ofRowLens w hw).rowLens.length))) →
    Fin w.length := fun i _ ↦ ⟨i, by
      exact lt_of_lt_of_le i.2 rowLens_ofRowLens_length_le_length⟩

  refine Finset.sum_bij e ?_ ?_ ?_ ?_

  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, hi]
    exact i.2
  · intro i₁ _ i₂ _
    simp [e]
    exact fun a ↦ Fin.eq_of_val_eq a
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    use ⟨k, hk.2⟩
    use (by simp [hk.1])
  · intro i hi
    simp [e]
    exact rowLen_ofRowLens (e i hi)

lemma exists_of_not_bot (hμ : μ ≠ 0) (h : γ.card = μ.sum) (h0 : 0 ∉ μ) : ∃ x : ℕ × ℕ, x ∈ γ := by
  contrapose! hμ
  rw [← Multiset.sum_eq_zero_iff_eq_zero h0, ← h, Finset.card_eq_zero]
  ext x
  rw [mem_cells]
  simp only [Finset.notMem_empty, hμ]

lemma sort_ne_nil (h : μ ≠ 0) : (Multiset.sort (· ≥ ·) μ) ≠ [] := by
  rw [ne_eq, List.eq_nil_iff_length_eq_zero, Multiset.length_sort, Multiset.card_eq_zero]
  exact h

def min_el (μ : Multiset ℕ) (h : μ ≠ 0) := List.getLast (Multiset.sort (· ≥ ·) μ) (sort_ne_nil h)

lemma min_el_mem (hμ : μ ≠ 0) : min_el μ hμ ∈ μ := by
  rw [min_el, ← Multiset.mem_sort (· ≥ ·)]
  exact List.getLast_mem (sort_ne_nil hμ)

lemma min_el_ne_zero (hμ : μ ≠ 0) (h0 : 0 ∉ μ) : min_el μ hμ ≠ 0 := by
  contrapose! h0; rw [← h0]; exact min_el_mem hμ

lemma min_el_le (hμ : μ ≠ 0) (i : Fin (Multiset.sort (· ≥ ·) μ).length) :
    min_el μ hμ ≤ (Multiset.sort (· ≥ ·) μ).get i := by
  rw [min_el, List.getLast_eq_getElem (sort_ne_nil hμ), ← ge_iff_le]
  refine List.Sorted.rel_get_of_le ?_ ?_
  · exact Multiset.sort_sorted _ _
  let hi := i.2
  rw [Fin.mk_le_mk]
  exact Nat.le_sub_one_of_lt hi

lemma min_el_le' (hμ : μ ≠ 0) {a : ℕ} (ha : a ∈ μ) : min_el μ hμ ≤ a := by
  rw [← Multiset.mem_sort (· ≥ ·)] at ha
  apply List.get_of_mem at ha
  obtain ⟨i, ha⟩ := ha
  rw [← ha]
  exact min_el_le hμ i

lemma cons_erase_min_el (hμ : μ ≠ 0) : (min_el μ hμ) ::ₘ (μ.erase (min_el μ hμ)) = μ := by
  exact Multiset.cons_erase (min_el_mem hμ)


lemma set_rowLen_ge_nonempty (hμ : μ ≠ 0) (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ))
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :  {j : ℕ | γ.rowLen j ≥ min_el μ hμ}.Nonempty := by
  use 0; rw [Set.mem_setOf]
  refine le_trans (min_el_le hμ ⟨0, by simp [Nat.pos_iff_ne_zero, hμ]⟩) ?_
  rw [← γ.get_rowLens]
  refine get_zero_ge_of_dominates hd ?_ ?_
  rw [γ.length_rowLens]
  rw [← mem_iff_lt_colLen]
  obtain ⟨x, hx⟩ := exists_of_not_bot hμ h h0
  exact γ.up_left_mem (Nat.zero_le x.1) (Nat.zero_le x.2) hx

lemma set_rowLen_ge_bddAbove (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    BddAbove {j : ℕ | γ.rowLen j ≥ min_el μ hμ} := by
  rw [bddAbove_def]
  use γ.colLen 0; intro i hi; rw [Set.mem_setOf] at hi
  have hi0 : γ.rowLen i > 0 := by
    let hme0 := min_el_ne_zero hμ h0
    rw [← Nat.pos_iff_ne_zero] at hme0
    exact lt_of_lt_of_le hme0 hi
  rw [gt_iff_lt, ← mem_iff_lt_rowLen, mem_iff_lt_colLen] at hi0
  exact le_of_lt hi0

lemma min_el_le_rowLen_sup (hμ : μ ≠ 0) (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ))
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    min_el μ hμ ≤ γ.rowLen (sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ}) := by
  let hj := Nat.sSup_mem (set_rowLen_ge_nonempty hμ hd h h0) (set_rowLen_ge_bddAbove hμ h0)
  rw [Set.mem_setOf] at hj
  exact hj

lemma rowLen_sup_add_one_le_min_el (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    γ.rowLen (sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ} + 1) ≤ min_el μ hμ := by
  refine le_of_lt ?_
  let hj := notMem_of_csSup_lt (lt_add_one <| sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ})
    (set_rowLen_ge_bddAbove hμ h0)
  rw [Set.mem_setOf] at hj; push_neg at hj
  exact hj


noncomputable
def remove_bottom_rowLen (γ : YoungDiagram) (hμ : μ ≠ 0) : Fin (γ.colLen 0) → ℕ :=
  fun i => if i < sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ} then γ.rowLen i.1
  else if i = sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ} then
    γ.rowLen i.1 - (min_el μ hμ - γ.rowLen (i.1+1))
  else γ.rowLen (i.1+1)

noncomputable
def remove_bottom (γ : YoungDiagram) (hμ : μ ≠ 0) (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ))
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    YoungDiagram :=
  ofRowLens (List.ofFn (remove_bottom_rowLen γ hμ))
  (by
    rw [List.sorted_ge_ofFn_iff]
    intro n m hnm
    unfold remove_bottom_rowLen
    let j := sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ}
    by_cases h1m : m < j
    · have h1n : n < j := by exact lt_of_le_of_lt hnm h1m
      simp only [j, h1m, ↓reduceIte, h1n, ge_iff_le]
      exact γ.rowLen_anti n m hnm
    · by_cases h2m : m = j
      · by_cases h1n : n < j
        · simp only [j, h2m, lt_self_iff_false, ↓reduceIte, h1n, tsub_le_iff_right]
          apply le_of_lt at h1n
          apply γ.rowLen_anti n j at h1n
          exact Nat.le_add_right_of_le h1n
        · have h2n : n = j := by
            push_neg at h1n
            exact antisymm (by rw [← h2m]; exact hnm) h1n
          simp only [j, h2m, lt_self_iff_false, ↓reduceIte, h2n, le_refl]
      · by_cases h1n : n < j
        · simp only [j, h1m, ↓reduceIte, h2m, h1n]
          refine γ.rowLen_anti n (m+1) ?_
          exact Nat.le_add_right_of_le hnm
        · by_cases h2n : n = j
          · simp only [j, h1m, ↓reduceIte, h2m, h2n, lt_self_iff_false]
            apply nat_lemma (min_el_le_rowLen_sup hμ hd h h0) (rowLen_sup_add_one_le_min_el hμ h0)
            refine γ.rowLen_anti (j+1) (m+1) ?_
            push_neg at h1m
            exact Nat.add_le_add_right h1m 1
          · simp only [j, h1m, ↓reduceIte, h2m, h1n, h2n]
            refine γ.rowLen_anti (n+1) (m+1) ?_
            exact Nat.add_le_add_right hnm 1
)

lemma remove_bottom_le (hμ : μ ≠ 0) (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ))
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) : remove_bottom γ hμ hd h h0 ≤ γ := by
  intro x
  simp only [remove_bottom, mem_cells, mem_ofRowLens, List.getElem_ofFn, remove_bottom_rowLen,
    ge_iff_le, List.length_ofFn, exists_prop, and_imp]
  intro hx1 hx2
  by_cases hx1l : x.1 < sSup {j | min_el μ hμ ≤ γ.rowLen j}
  · simp only [hx1l, ↓reduceIte] at hx2
    rw [mem_iff_lt_rowLen]
    exact hx2
  · by_cases hx1e : x.1 = sSup {j | min_el μ hμ ≤ γ.rowLen j}
    · simp only [hx1e, lt_self_iff_false, ↓reduceIte] at hx2
      rw [mem_iff_lt_rowLen]
      rw [← hx1e] at hx2
      refine lt_of_lt_of_le hx2 ?_
      exact Nat.sub_le (γ.rowLen x.1) (min_el μ hμ - γ.rowLen (x.1 + 1))
    · simp [hx1l, hx1e, ← mem_iff_lt_rowLen] at hx2
      exact γ.up_left_mem (Nat.le_add_right x.1 1) (by rfl) hx2

theorem remove_bottom_card_eq_erase_min_el_sum (hμ : μ ≠ 0)
    (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (remove_bottom γ hμ hd h h0).card = (μ.erase (min_el μ hμ)).sum := by
  let j := sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ}
  have hj : ∀ i ≤ j, γ.rowLen i ≥ min_el μ hμ := by
    intro i hi
    exact le_trans (min_el_le_rowLen_sup hμ hd h h0) (γ.rowLen_anti i j hi)
  let h2 := h
  rw [← Multiset.sum_erase (min_el_mem hμ), card_eq_sum_rowLens'] at h
  have hjfl : j < (List.ofFn (remove_bottom_rowLen γ hμ)).length := by
    simp only [List.length_ofFn]
    specialize hj (γ.colLen 0)
    contrapose! hj
    constructor; exact hj
    suffices γ.rowLen (γ.colLen 0) = 0 by
      rw [this, Nat.pos_iff_ne_zero]
      exact min_el_ne_zero hμ h0
    suffices (γ.colLen 0, 0) ∉ γ by
      rw [mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at this
      push_neg at this
      exact this
    rw [mem_iff_lt_colLen]
    exact Nat.lt_irrefl (γ.colLen 0)
  have hjflm : (⟨j, hjfl⟩ : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length) ∈
      Finset.univ := by
    exact Finset.mem_univ _
  have hrlfl : (List.ofFn (remove_bottom_rowLen γ hμ)).length = γ.rowLens.length := by simp
  rw [card_eq_sum_rowLens, remove_bottom, sum_rowLen_ofRowLens,
    ← Finset.sum_erase_add _ _ hjflm]
  · have hjrl : j < γ.rowLens.length + 1 := by
      rw [← hrlfl]
      exact lt_trans hjfl (lt_add_one (List.ofFn (remove_bottom_rowLen γ hμ)).length)
    have hjrlm : (⟨j, hjrl⟩ : Fin (γ.rowLens.length + 1)) ∈ Finset.univ := by
      exact Finset.mem_univ _
    have hjrl' : j + 1 < γ.rowLens.length + 1 := by
      rw [← hrlfl, Nat.add_one_lt_add_one_iff]
      exact hjfl
    have hjrlm' : (⟨j+1, hjrl'⟩ : Fin (γ.rowLens.length + 1)) ∈
        Finset.univ.erase ⟨j, hjrl⟩ := by simp
    rw [← Finset.sum_erase_add _ _ hjrlm, ← Finset.sum_erase_add _ _ hjrlm'] at h
    suffices ∑ x ∈ Finset.univ.erase ⟨j, hjfl⟩, (List.ofFn (remove_bottom_rowLen γ hμ)).get x +
        (List.ofFn (remove_bottom_rowLen γ hμ)).get ⟨j, hjfl⟩ = ∑ x ∈
        ((Finset.univ : Finset (Fin (γ.rowLens.length+1))).erase ⟨j, hjrl⟩).erase
        ⟨j + 1, hjrl'⟩, γ.rowLen x + γ.rowLen (j + 1) + γ.rowLen j -
        (min_el μ hμ) by
      simp only at h
      rw [this, h, add_tsub_cancel_left]

    rw [add_assoc, Nat.add_sub_assoc]
    · have hasdf : (List.ofFn (remove_bottom_rowLen γ hμ)).get ⟨j, hjfl⟩ = γ.rowLen (j + 1) +
          γ.rowLen j - (min_el μ hμ) := by
        simp [remove_bottom_rowLen, j]
        exact nat_lemma2 (min_el_le_rowLen_sup hμ hd h2 h0) (rowLen_sup_add_one_le_min_el hμ h0)
      rw [← hasdf, Nat.add_right_cancel_iff]
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      let e : (i : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length) →
        (i ∈ Finset.univ.erase ⟨j, hjfl⟩) → (Fin (γ.rowLens.length + 1)) :=
        fun i hi => if i < j then
        ⟨i, by rw [← hrlfl]; exact lt_trans i.2 (lt_add_one _)⟩ else
        ⟨i+1, by rw [← hrlfl, add_lt_add_iff_right]; exact i.2⟩
      refine Finset.sum_bij e ?_ ?_ ?_ ?_
      · intro i hi
        simp [e]
        simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hi
        by_cases hij : i.1 < j
        · simp [hij]; omega
        · simp [hij]; constructor
          · contrapose! hi
            exact Fin.eq_mk_iff_val_eq.mpr hi
          · omega
      · intro i₁ hi₁ i₂ hi₂ hi
        simp [e] at hi
        by_cases hi₁j : i₁.1 < j
        · simp [hi₁j] at hi
          by_cases hi₂j : i₂.1 < j
          · simp [hi₂j] at hi
            exact Fin.eq_of_val_eq hi
          · simp [hi₂j] at hi
            omega
        · simp [hi₁j] at hi
          by_cases hi₂j : i₂.1 < j
          · simp [hi₂j] at hi
            omega
          · simp [hi₂j] at hi
            exact Fin.eq_of_val_eq hi
      · intro k hk
        by_cases hkj : k < j
        · use ⟨k, by exact lt_trans hkj hjfl⟩
          use (by
            simp only [Finset.mem_erase, ne_eq, Fin.mk.injEq, Finset.mem_univ, and_true]
            exact ne_of_lt hkj)
          simp [e, hkj]
        · simp at hk
          have hkne : k.1 ≠ j := by
            apply And.right at hk
            contrapose! hk
            exact Fin.eq_mk_iff_val_eq.mpr hk
          have hk0 : k.1 > 0 := by
            by_cases hj0 : j > 0
            · push_neg at hkj
              exact lt_of_lt_of_le hj0 hkj
            · rw [gt_iff_lt, Nat.pos_iff_ne_zero] at hj0
              push_neg at hj0
              rw [gt_iff_lt, Nat.pos_iff_ne_zero, ← hj0]
              exact hkne
          use ⟨k-1, by omega⟩
          use (by
            simp only [Finset.mem_erase, ne_eq, Fin.mk.injEq, Finset.mem_univ, and_true]
            apply And.left at hk
            contrapose! hk
            rw [Fin.eq_mk_iff_val_eq, ← hk]
            exact (Nat.sub_eq_iff_eq_add hk0).mp rfl)
          have hkj2 : ¬(k-1 < j) := by omega
          simp [e, hkj2, Nat.sub_one_add_one_eq_of_pos hk0]
      · intro i hi
        simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hi
        rw [Fin.eq_mk_iff_val_eq] at hi
        simp [j, remove_bottom_rowLen, e, hi]
        by_cases hij : i.1 < j
        · simp [j, hij]
        · simp [j, hij]
    · exact Nat.le_add_left_of_le (min_el_le_rowLen_sup hμ hd h2 h0)

lemma sort_erase_min_el (hμ : μ ≠ 0) : Multiset.sort (· ≥ ·) μ =
    (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))) ++ [min_el μ hμ] := by
  refine List.eq_of_perm_of_sorted ?_ (Multiset.sort_sorted _ _) ?_
  · rw [← Multiset.coe_eq_coe]
    ext x
    simp only [ge_iff_le, Multiset.sort_eq, Multiset.coe_count, List.count_append]
    rw [← Multiset.coe_count, Multiset.sort_eq, ← Multiset.coe_count]
    nth_rw 1 [← cons_erase_min_el hμ, ← Multiset.singleton_add, add_comm]
    simp
  · rw [List.Sorted, List.pairwise_append]
    constructor; swap; constructor
    · simp
    · intro a ha
      simp only [ge_iff_le, Multiset.mem_sort] at ha
      apply Multiset.mem_of_mem_erase at ha
      simp [min_el_le' hμ ha]
    · exact Multiset.sort_sorted _ _

lemma get_sort_erase_min_el (hμ : μ ≠ 0)
    (i : Fin (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length) :
    (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).get i =
    (Multiset.sort (· ≥ ·) μ).get ⟨i, by
      let hi := i.2
      simp [Multiset.card_erase_of_mem (min_el_mem hμ)] at hi
      simp
      exact Nat.lt_of_lt_pred hi⟩ := by
  simp only [List.get_eq_getElem, ge_iff_le, sort_erase_min_el hμ]
  symm
  exact List.getElem_append_left _

lemma sum_sort_erase_min_el (hμ : μ ≠ 0) {r : ℕ}
    (hr : r < (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length) :
    ∑ i : Fin (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length with i.1 ≤ r,
    (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).get i =
    ∑ i : Fin (Multiset.sort (· ≥ ·) μ).length with i.1 ≤ r,
    (Multiset.sort (· ≥ ·) μ).get i := by
  let e : (i : Fin (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length) →
    (hi : i ∈ ({i | i.1 ≤ r} : Finset
    (Fin (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length))) →
    Fin (Multiset.sort (· ≥ ·) μ).length :=
    fun ⟨i, hi⟩ _ ↦ ⟨i, by
      simp [Multiset.card_erase_of_mem (min_el_mem hμ)] at hi
      simp
      exact Nat.lt_of_lt_pred hi⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · intro ⟨i, hi⟩ hir
    simp at hir
    simp [e, hir]
  · intro ⟨i₁, hi₁⟩ _ ⟨i₂, hi₂⟩ _
    simp [e]
  · intro ⟨i, hi⟩
    simp [e]
    intro hir
    use ⟨i, by exact lt_of_le_of_lt hir hr⟩
  · intro ⟨i, hi⟩ hir
    simp only [e]
    exact get_sort_erase_min_el hμ ⟨i, hi⟩

lemma sum_sort_erase_min_el' (hμ : μ ≠ 0) {r : ℕ}
    (hr : r ≥ (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length) :
    ∑ i : Fin (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length with i.1 ≤ r,
    (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).get i =
    ∑ i : Fin (Multiset.sort (· ≥ ·) μ).length with i.1 ≤ r,
    (Multiset.sort (· ≥ ·) μ).get i  - min_el μ hμ:= by
  nth_rw 11 [min_el]
  rw [List.getLast_eq_getElem]
  let ℓ : Fin (Multiset.sort (· ≥ ·) μ).length :=
    ⟨(Multiset.sort (· ≥ ·) μ).length - 1, by simp [Nat.pos_iff_ne_zero, hμ]⟩
  have hlr : ℓ ∈ (Finset.filter (fun i : Fin (Multiset.sort (· ≥ ·) μ).length ↦ i.1 ≤ r)
      Finset.univ) := by
    simp only [ge_iff_le, Multiset.length_sort, Multiset.card_erase_of_mem (min_el_mem hμ),
      Nat.pred_eq_sub_one, tsub_le_iff_right] at hr
    simp [ℓ, hr]
  rw [← Finset.sum_erase_add (Finset.filter
    (fun i : Fin (Multiset.sort (· ≥ ·) μ).length ↦ i.1 ≤ r) Finset.univ)
    _ hlr]
  rw [List.get_eq_getElem, add_tsub_cancel_right]
  unfold ℓ
  let e : (i : Fin (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length) →
    (hi : i ∈ ({i | i.1 ≤ r} : Finset
    (Fin (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length))) →
    Fin (Multiset.sort (· ≥ ·) μ).length := fun ⟨i, hi⟩ _ ↦ ⟨i, by
      simp [Multiset.card_erase_of_mem (min_el_mem hμ)] at hi
      simp
      exact Nat.lt_of_lt_pred hi⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · intro ⟨i, hi⟩
    simp [Multiset.card_erase_of_mem (min_el_mem hμ)] at hi
    apply ne_of_lt at hi
    simp [e, hi]
  · intro ⟨i₁, hi₁⟩ _ ⟨i₂, hi₂⟩ _
    simp [e]
  · intro ⟨i, hi⟩ hir
    simp at hir
    simp [e]
    obtain ⟨hir₁, hir₂⟩ := hir
    use ⟨i, by
      simp at hi
      simp [Multiset.card_erase_of_mem (min_el_mem hμ)]
      omega⟩
  · intro ⟨i, hi⟩ hir
    simp only [e]
    exact get_sort_erase_min_el hμ ⟨i, hi⟩

lemma sum_remove_bottom_rowLen_eq_sum_rowLen (hμ : μ ≠ 0) {r : ℕ}
    (hr : r < sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ}) :
    ∑ x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length with x.1 ≤ r,
    (List.ofFn (remove_bottom_rowLen γ hμ)).get x =
    ∑ x : Fin γ.rowLens.length with x.1 ≤ r,
    γ.rowLens.get x := by
  let e : (x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length) →
    (hx : x ∈ ({i | i.1 ≤ r} : Finset
    (Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length))) →
    Fin γ.rowLens.length := fun ⟨x, hx⟩ _ ↦ ⟨x, by
      rw [List.length_ofFn] at hx
      rw [length_rowLens]
      exact hx⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · intro ⟨x₁, hx₁⟩ _ ⟨x₂, hx₂⟩ _
    simp [e]
  · intro ⟨x, hx⟩ hxr
    rw [length_rowLens] at hx
    simp at hxr
    simp [e]
    use ⟨x, by rw [List.length_ofFn]; exact hx⟩
  · simp [remove_bottom_rowLen, e]
    intro x hxr hjx
    simp only [ge_iff_le] at hr
    omega

lemma sum_rowLen_with_eq_sup (hμ : μ ≠ 0) :
    ∑ (x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length) with x.1 =
    sSup {j | min_el μ hμ ≤ γ.rowLen j}, (γ.rowLen x.1 - (min_el μ hμ - γ.rowLen (x.1 + 1))) =
    γ.rowLen (sSup {j | min_el μ hμ ≤ γ.rowLen j}) - (min_el μ hμ -
    γ.rowLen (sSup {j | min_el μ hμ ≤ γ.rowLen j} + 1)) := by
  by_cases hj : sSup {j | min_el μ hμ ≤ γ.rowLen j} < (List.ofFn (remove_bottom_rowLen γ hμ)).length
  · rw [Finset.sum_eq_single_of_mem ⟨sSup {j | min_el μ hμ ≤ γ.rowLen j}, hj⟩]
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
      intro ⟨b, hb⟩ hbj hbj'
      rw [Fin.mk.injEq] at hbj'
      simp only at hbj
      contradiction
  · suffices ¬γ.rowLen (sSup {j | min_el μ hμ ≤ γ.rowLen j}) ≠ 0 by
      push_neg at this
      rw [this, zero_tsub, Finset.sum_eq_zero]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro ⟨x, hx⟩ hxj
      rw [hxj, this, zero_tsub]
    rw [← Nat.pos_iff_ne_zero, ← mem_iff_lt_rowLen, mem_iff_lt_colLen]
    rw [List.length_ofFn] at hj
    exact hj

lemma sum_rowLen_fin_cast (hμ : μ ≠ 0) :
    ∑ x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length with x.1 <
    sSup {j | min_el μ hμ ≤ γ.rowLen j}, γ.rowLen x.1 = ∑ x : Fin γ.rowLens.length
    with x.1 < sSup {j | min_el μ hμ ≤ γ.rowLen j}, γ.rowLen x.1 := by
  let e : (x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length) →
    (hx : x ∈ ({x | x.1 < sSup {j | min_el μ hμ ≤ γ.rowLen j}} :
    Finset (Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length))) →
    Fin γ.rowLens.length := fun ⟨x, hx⟩ _ ↦ ⟨x, by
      rw [List.length_ofFn] at hx
      rw [length_rowLens]
      exact hx⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · intro ⟨x₁, hx₁⟩ _ ⟨x₂, hx₂⟩ _
    simp [e]
  · simp [e]
    intro ⟨x, hx⟩ _
    use ⟨x, by
      rw [List.length_ofFn]
      rw [length_rowLens] at hx
      exact hx⟩
  · simp [e]

lemma sum_rowLen_fin_cast' (hμ : μ ≠ 0) {r : ℕ} :
    ∑ x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length with
    sSup {j | min_el μ hμ ≤ γ.rowLen j} < x.1 ∧ x.1 ≤ r, γ.rowLen (x.1 + 1) =
    ∑ x : Fin γ.rowLens.length with sSup {j | min_el μ hμ ≤ γ.rowLen j} < x.1 ∧
    x.1 ≤ r, γ.rowLen (x.1 + 1) := by
  let e : (x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length) →
    (hx : x ∈ ({x | sSup {j | min_el μ hμ ≤ γ.rowLen j} < x.1 ∧ x.1 ≤ r} :
    Finset (Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length))) →
    Fin γ.rowLens.length := fun ⟨x, hx⟩ _ ↦ ⟨x, by
      rw [List.length_ofFn] at hx
      rw [length_rowLens]
      exact hx⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · intro ⟨x₁, hx₁⟩ _ ⟨x₂, hx₂⟩ _
    simp [e]
  · simp [e]
    intro ⟨x, hx⟩ _ _
    use ⟨x, by
      rw [List.length_ofFn]
      rw [length_rowLens] at hx
      exact hx⟩
  · simp [e]

lemma sum_rowLen_add_sup (hμ : μ ≠ 0) {r : ℕ} (hr : sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ r) :
    ∑ x : Fin γ.rowLens.length with x.1 ≤ r + 1 ∧ sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ x.1,
    γ.rowLen x.1 = γ.rowLen (sSup {j | min_el μ hμ ≤ γ.rowLen j}) + ∑ x: Fin γ.rowLens.length
    with x.1 ≤ r + 1 ∧ sSup {j | min_el μ hμ ≤ γ.rowLen j} < x.1, γ.rowLen x.1 := by
  by_cases hj : sSup {j | min_el μ hμ ≤ γ.rowLen j} < γ.rowLens.length
  · have hjs : ⟨sSup {j | min_el μ hμ ≤ γ.rowLen j}, hj⟩ ∈ ({x | x.1 ≤ r + 1 ∧
        sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ x.1} : Finset (Fin γ.rowLens.length)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, le_refl, and_true, true_and]
      exact le_trans hr (Nat.le_add_right r 1)
    rw [← Finset.add_sum_erase _ _ hjs]
    simp only
    rw [Nat.add_left_cancel_iff]
    congr
    ext ⟨x, hx⟩
    simp only [Finset.mem_erase, ne_eq, Fin.mk.injEq, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · have hrl : γ.rowLen (sSup {j | min_el μ hμ ≤ γ.rowLen j}) = 0 := by
      rw [length_rowLens, ← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hj
      push_neg at hj
      exact hj
    rw [hrl, zero_add]
    congr
    ext ⟨x, hx⟩
    simp only [and_congr_right_iff]
    intro _
    push_neg at hj
    apply lt_of_le_of_lt' hj at hx
    apply ne_of_lt at hx
    symm at hx
    exact Ne.le_iff_lt hx


lemma sum_rowLen_add_sup_add_one (hμ : μ ≠ 0) {r : ℕ}
    (hr : sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ r) :
    ∑ x : Fin γ.rowLens.length with x.1 ≤ r ∧ sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ x.1,
    γ.rowLen (x.1 + 1) = γ.rowLen (sSup {j | min_el μ hμ ≤ γ.rowLen j} + 1) +
    ∑ x : Fin γ.rowLens.length with sSup {j | min_el μ hμ ≤ γ.rowLen j} < x.1 ∧ x.1 ≤ r,
    γ.rowLen (x.1 + 1) := by
  simp only [And.comm]
  by_cases hj : sSup {j | min_el μ hμ ≤ γ.rowLen j} < γ.rowLens.length
  · have hjs : ⟨sSup {j | min_el μ hμ ≤ γ.rowLen j}, hj⟩ ∈ ({x | x.1 ≤ r ∧
        sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ x.1} : Finset (Fin γ.rowLens.length)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, le_refl, and_true, true_and]
      exact hr
    rw [← Finset.add_sum_erase _ _ hjs]
    simp only
    rw [Nat.add_left_cancel_iff]
    congr
    ext ⟨x, hx⟩
    simp only [Finset.mem_erase, ne_eq, Fin.mk.injEq, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · have hrl : γ.rowLen (sSup {j | min_el μ hμ ≤ γ.rowLen j} + 1) = 0 := by
      push_neg at hj
      apply le_trans' (Nat.le_add_right _ 1) at hj
      rw [← Nat.not_lt, length_rowLens, ← mem_iff_lt_colLen, mem_iff_lt_rowLen,
        Nat.pos_iff_ne_zero] at hj
      push_neg at hj
      exact hj
    rw [hrl, zero_add]
    congr
    ext ⟨x, hx⟩
    simp only [and_congr_right_iff]
    intro _
    push_neg at hj
    apply lt_of_le_of_lt' hj at hx
    apply ne_of_lt at hx
    symm at hx
    exact Ne.le_iff_lt hx


lemma sum_rowLen_reindex (hμ : μ ≠ 0) {r : ℕ} :
    ∑ x : Fin γ.rowLens.length with x.1 ≤ r + 1 ∧ sSup {j | min_el μ hμ ≤ γ.rowLen j} <
    x.1, γ.rowLen x.1 = ∑ x : Fin γ.rowLens.length with x.1 ≤ r ∧
    sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ x.1, γ.rowLen (x.1 + 1) := by
  have hs01 : ∀ x ∈ ({x | x.1 ≤ r ∧ sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ x.1} :
      Finset (Fin γ.rowLens.length)), γ.rowLen (x.1 + 1) ≠ 0 →
      x.1 + 1 < γ.rowLens.length := by
    intro ⟨x, _⟩ _
    simp only
    intro hx
    rw [length_rowLens, ← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero]
    exact hx
  have hs0 : ∀ x ∈ ({x | x.1 ≤ r + 1 ∧ sSup {j | min_el μ hμ ≤ γ.rowLen j} < x.1} :
      Finset (Fin γ.rowLens.length)), γ.rowLen x.1 ≠ 0 → x.1 < γ.rowLens.length := by
    intro ⟨x, _⟩ _
    simp only
    intro hx
    rw [length_rowLens, ← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero]
    exact hx
  rw [← Finset.sum_filter_of_ne hs01, ← Finset.sum_filter_of_ne hs0]
  rw [Finset.filter_filter, Finset.filter_filter]
  symm
  let e : (x : Fin γ.rowLens.length) →
    (hx : x ∈ ({x | (x.1 ≤ r ∧ sSup {j | min_el μ hμ ≤ γ.rowLen j} ≤ x.1)
    ∧ x.1 + 1 < γ.rowLens.length} : Finset (Fin γ.rowLens.length))) →
    Fin γ.rowLens.length := fun x hx ↦ ⟨x.1+1, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.2⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e, Nat.le_iff_lt_add_one]
  · intro ⟨x₁, hx₁⟩ _ ⟨x₂, hx₂⟩
    simp [e]
  · intro ⟨x, hx⟩
    simp only [length_rowLens, Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk.injEq,
      exists_prop, and_imp, e]
    intro hx1 hx2 hx3
    use ⟨x-1, by exact lt_of_le_of_lt (Nat.sub_le x 1) hx⟩
    have hx0 : x > 0 := by
      refine lt_of_le_of_lt ?_ hx2
      exact Nat.zero_le (sSup {j | min_el μ hμ ≤ γ.rowLen j})
    use (by
      simp only [tsub_le_iff_right]
      omega
    )
    simp only
    exact Nat.sub_one_add_one_eq_of_pos hx0
  · simp [e]

open Classical in
lemma sum_remove_bottom_rowLen_eq_sum_rowLen' (hμ : μ ≠ 0)
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (h : γ.card = μ.sum) (h0 : 0 ∉ μ) {r : ℕ}
    (hr : r ≥ sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ}) :
    ∑ x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length with x.1 ≤ r,
    (List.ofFn (remove_bottom_rowLen γ hμ)).get x =
    ∑ x : Fin γ.rowLens.length with x.1 ≤ r+1,
    γ.rowLens.get x - min_el μ hμ := by
  simp only [List.get_eq_getElem, List.getElem_ofFn, remove_bottom_rowLen, ge_iff_le, get_rowLens]
  rw [Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.filter_filter, not_lt]
  let j := sSup {j | min_el μ hμ ≤ γ.rowLen j}
  have hle : ∀ x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length,
      (x.1 ≤ r ∧ x.1 < j) = (x.1 < j) := by
    intro ⟨x, hx⟩
    simp only [eq_iff_iff, and_iff_right_iff_imp]
    intro hxj
    exact le_trans (le_of_lt hxj) hr
  have heq : ∀ x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length,
      ((x.1 ≤ r ∧ j ≤ x.1) ∧ x.1 = j) = (x.1 = j) := by
    intro ⟨x, hx⟩
    simp only [eq_iff_iff, and_iff_right_iff_imp]
    intro hxj
    simp [hxj, hr, j]
  have hge : ∀ x : Fin (List.ofFn (remove_bottom_rowLen γ hμ)).length,
      ((x.1 ≤ r ∧ j ≤ x.1) ∧ ¬ x.1 = j) = (j < x.1 ∧ x.1 ≤ r) := by
    intro ⟨x, hx⟩
    simp only [eq_iff_iff]
    omega
  simp only [hle, heq, hge, j]

  have hmiddle : γ.rowLen j - (min_el μ hμ - γ.rowLen (j + 1)) =
      γ.rowLen j + γ.rowLen (j + 1) - min_el μ hμ := by
    refine Nat.sub_sub_right _ ?_
    exact rowLen_sup_add_one_le_min_el hμ h0
  rw [sum_rowLen_with_eq_sup hμ, hmiddle, tsub_add_eq_add_tsub, ← Nat.add_sub_assoc,
    Nat.sub_eq_iff_eq_add, Nat.sub_add_cancel]
  · have hsum : ∑ x : Fin γ.rowLens.length with x.1 ≤ r + 1, γ.rowLen x.1 =
        ∑ x ∈ ({x | x.1 ≤ r + 1} : Finset (Fin γ.rowLens.length)) with x.1 < j, γ.rowLen x.1 +
        ∑ x ∈ ({x | x.1 ≤ r + 1} : Finset (Fin γ.rowLens.length)) with ¬(x.1 < j), γ.rowLen x.1
        := by
      symm; apply Finset.sum_filter_add_sum_filter_not
    rw [hsum, Finset.filter_filter, Finset.filter_filter]; push_neg
    have hrjf : ∀ x : Fin γ.rowLens.length, (x.1 ≤ r + 1 ∧ x.1 < j) = (x.1 < j) := by
      intro x
      simp only [eq_iff_iff, and_iff_right_iff_imp, j]
      simp only [ge_iff_le] at hr
      intro hxj
      omega
    simp only [hrjf]
    rw [sum_rowLen_fin_cast hμ, Nat.add_left_cancel_iff, sum_rowLen_add_sup hμ hr,
      add_assoc, Nat.add_left_cancel_iff, sum_rowLen_reindex hμ,
      sum_rowLen_add_sup_add_one hμ hr, Nat.add_left_cancel_iff,
      sum_rowLen_fin_cast' hμ]

  · have hγ0 : 0 < γ.rowLens.length := by
      let hx := exists_of_not_bot hμ h h0
      obtain ⟨x, hx⟩ := hx
      rw [length_rowLens, ← mem_iff_lt_colLen]
      exact γ.up_left_mem (Nat.zero_le x.1) (Nat.zero_le x.2) hx
    refine le_trans (min_el_le_rowLen_sup hμ hd h h0) ?_
    refine le_trans (γ.rowLen_anti 0 j (Nat.zero_le j)) ?_
    have h00 : (0 : ℕ) = ↑(⟨0, hγ0⟩ : Fin γ.rowLens.length) := by simp
    have h000 : (⟨0, hγ0⟩ : Fin γ.rowLens.length) ∈ ({x | x.1 ≤ r + 1} :
        Finset (Fin γ.rowLens.length)) := by simp
    have h0f : ∀ x ∈ ({x | x.1 ≤ r + 1} : Finset (Fin γ.rowLens.length)),
        0 ≤ γ.rowLen x.1 := by
      intro x ?_
      exact Nat.zero_le (γ.rowLen ↑x)
    rw [h00]
    exact Finset.single_le_sum h0f h000

  · rw [add_comm, add_assoc, add_assoc]
    refine Nat.le_add_right_of_le ?_
    exact min_el_le_rowLen_sup hμ hd h h0
  · rw [add_assoc]
    refine Nat.le_add_right_of_le ?_
    exact min_el_le_rowLen_sup hμ hd h h0
  · refine Nat.le_add_right_of_le ?_
    exact min_el_le_rowLen_sup hμ hd h h0



lemma sSup_rowLen_le_sort_erase_length (hμ : μ ≠ 0)
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) : sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ} ≤
    (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length := by
  let hll := lengths_le_of_dominates hd ?_ ?_
  · simp [Multiset.card_erase_of_mem (min_el_mem hμ)]
    simp at hll
    suffices sSup {j | min_el μ hμ ≤ γ.rowLen j} < γ.colLen 0 by
      rw [Nat.le_sub_one_iff_lt]
      exact lt_of_lt_of_le this hll
      rw [Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero]
      exact hμ
    by_contra! hle
    let hle2 := le_trans (min_el_le_rowLen_sup hμ hd h h0)
      (γ.rowLen_anti (γ.colLen 0) _ hle)
    suffices ¬γ.rowLen (γ.colLen 0) ≠ 0 by
      push_neg at this
      simp [this] at hle2
      contrapose! h0
      rw [← hle2]
      exact min_el_mem hμ
    rw [← Nat.pos_iff_ne_zero, ← mem_iff_lt_rowLen, mem_iff_lt_colLen]
    exact Nat.lt_irrefl (γ.colLen 0)
  · rw [← Fin.sum_univ_getElem]
    simp only [← List.get_eq_getElem]
    rw [← card_eq_sum_rowLens, h, ← Multiset.sum_coe, Multiset.sort_eq]
  · intro i
    refine γ.pos_of_mem_rowLens _ ?_
    exact List.get_mem γ.rowLens i

theorem remove_bottom_dominates_erase_min_el (hμ : μ ≠ 0)
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (remove_bottom γ hμ hd h h0).rowLens ⊵ Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ)) := by
  intro r
  rw [remove_bottom, sum_rowLen_ofRowLens' r]
  by_cases hrℓ : r < (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length
  · rw [sum_sort_erase_min_el hμ hrℓ]
    by_cases hrj : r < sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ}
    · rw [sum_remove_bottom_rowLen_eq_sum_rowLen hμ hrj]
      exact hd r
    · push_neg at hrj
      rw [sum_remove_bottom_rowLen_eq_sum_rowLen' hμ hd h h0 hrj]
      refine le_trans ?_ (tsub_le_tsub_right (hd (r+1)) (min_el μ hμ))
      have hfr : r + 1 < (Multiset.sort (· ≥ ·) μ).length := by
        rw [Multiset.length_sort, ← Nat.add_one_lt_add_one_iff,
          Multiset.card_erase_add_one (min_el_mem hμ)] at hrℓ
        rw [Multiset.length_sort]
        exact hrℓ
      refine le_trans (le_add_of_nonneg_right
        (Nat.zero_le ((Multiset.sort (· ≥ ·) μ).get ⟨r+1, hfr⟩ - min_el μ hμ))) ?_
      rw [← Nat.add_sub_assoc (min_el_le hμ ⟨r + 1, hfr⟩)]
      have hfer : (Finset.filter (fun i : Fin (Multiset.sort (· ≥ ·) μ).length => i.1 ≤ r)
          Finset.univ) = (Finset.filter (fun i : Fin (Multiset.sort (· ≥ ·) μ).length =>
          i.1 ≤ r + 1) Finset.univ).erase ⟨r + 1, hfr⟩ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
        rw [Fin.eq_mk_iff_val_eq]
        push_neg
        omega
      rw [hfer, Finset.sum_erase_add]
      simp
  · push_neg at hrℓ
    rw [sum_sort_erase_min_el' hμ hrℓ, ge_iff_le]
    have hrj : r ≥ sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ} := by
      refine le_trans (sSup_rowLen_le_sort_erase_length hμ hd h h0) hrℓ
    rw [sum_remove_bottom_rowLen_eq_sum_rowLen' hμ hd h h0 hrj]
    specialize hd r
    refine le_trans (tsub_le_tsub_right hd (min_el μ hμ)) ?_
    refine tsub_le_tsub_right ?_ (min_el μ hμ)
    refine Finset.sum_le_sum_of_subset ?_
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

lemma remove_bottom_single_column (hμ : μ ≠ 0) (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ)
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) (i1 i2 j : ℕ) (hi : i1 < i2) (hij2 : (i2, j) ∈ γ) :
    (i1, j) ∈ (remove_bottom γ hμ hd h h0) := by
  rw [remove_bottom, mem_ofRowLens]
  simp only [List.getElem_ofFn, List.length_ofFn]
  use (by
    rw [← mem_iff_lt_colLen]
    exact γ.up_left_mem (le_of_lt hi) (Nat.zero_le j) hij2)
  simp only [remove_bottom_rowLen, ge_iff_le]
  by_cases hi1 : i1 < sSup {j | min_el μ hμ ≤ γ.rowLen j}
  · simp [hi1]
    rw [← mem_iff_lt_rowLen]
    exact γ.up_left_mem (le_of_lt hi) (by rfl) hij2
  · by_cases hi1' : i1 = sSup {j | min_el μ hμ ≤ γ.rowLen j}
    · simp [hi1']
      rw [← hi1', tsub_tsub_assoc]
      · suffices j < γ.rowLen (i1 + 1) by
          refine lt_of_lt_of_le this ?_
          simp only [le_add_iff_nonneg_left, zero_le]
        rw [← mem_iff_lt_rowLen]
        exact γ.up_left_mem hi (by rfl) hij2
      · rw [hi1']; exact min_el_le_rowLen_sup hμ hd h h0
      · rw [hi1']; exact rowLen_sup_add_one_le_min_el hμ h0
    · simp [hi1, hi1']
      rw [← mem_iff_lt_rowLen]
      exact γ.up_left_mem hi (by rfl) hij2

def extend_ssyt_by {γ' : YoungDiagram} (T' : SemistandardYoungTableau γ') (ℓ : ℕ)
  (hγ : γ' ≤ γ) (hℓ : ∀ i j : ℕ, (i, j) ∈ γ' → T' i j < ℓ)
  (h : ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ γ → (i1, j) ∈ γ') :
  SemistandardYoungTableau γ :=
  ⟨fun i j =>
  if (i, j) ∈ γ' then T' i j else
  if (i, j) ∈ γ then ℓ
  else 0
  , by
    intro i j1 j2 hj hij2
    have hij1 : (i, j1) ∈ γ := by exact γ.up_left_mem (by rfl) (le_of_lt hj) hij2
    by_cases hij2' : (i, j2) ∈ γ'
    · have hij1' : (i, j1) ∈ γ' := by exact γ'.up_left_mem (by rfl) (le_of_lt hj) hij2'
      simp only [hij1', ↓reduceIte, hij2', ge_iff_le]
      exact T'.row_weak hj hij2'
    · by_cases hij1' : (i, j1) ∈ γ'
      · simp only [hij1', ↓reduceIte, hij2', hij2, ge_iff_le]
        exact le_of_lt (hℓ i j1 hij1')
      · simp only [hij1', ↓reduceIte, hij1, hij2', hij2, le_refl]
  , by
    intro i1 i2 j hi hij2
    have hij1' : (i1, j) ∈ γ' := h i1 i2 j hi hij2
    by_cases hij2' : (i2, j) ∈ γ'
    · simp only [hij1', ↓reduceIte, hij2', gt_iff_lt]
      exact T'.col_strict hi hij2'
    · simp only [hij1', ↓reduceIte, hij2', hij2, gt_iff_lt]
      exact hℓ i1 j hij1'
  , by
    intro i j hij
    have hij' : (i, j) ∉ γ' := by
      contrapose! hij
      apply hγ at hij
      rw [mem_cells] at hij
      exact hij
    simp [hij, hij']
    ⟩

lemma YoungDiagram.card_sdiff {γ' : YoungDiagram} (h : γ' ≤ γ) :
    γ.card - γ'.card = (γ.cells \ γ'.cells).card := by
  rw [YoungDiagram.card, Finset.card_sdiff h]

lemma count_content_of_forall_lt {γ' : YoungDiagram} {T' : SemistandardYoungTableau γ'}
    {n ℓ : ℕ} (hℓ : ∀ i j : ℕ, (i, j) ∈ γ' → T' i j < ℓ) (hnℓ : n ≥ ℓ) :
    Multiset.count n T'.content = 0 := by
  simp only [content, Multiset.count_eq_zero, Multiset.mem_map, Finset.mem_val, mem_cells,
        Prod.exists, not_exists, not_and]
  intro i j hij
  refine ne_of_lt ?_
  exact lt_of_lt_of_le (hℓ i j hij) hnℓ

lemma forall_mem_extend_ssyt_by_lt {γ' : YoungDiagram} {T' : SemistandardYoungTableau γ'}
    {ℓ : ℕ} {hγ : γ' ≤ γ} {hℓ : ∀ i j : ℕ, (i, j) ∈ γ' → T' i j < ℓ}
    {h : ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ γ → (i1, j) ∈ γ'} :
    ∀ i j : ℕ, (i, j) ∈ γ → (extend_ssyt_by T' ℓ hγ hℓ h) i j < ℓ + 1 := by
  intro i j hij
  simp only [extend_ssyt_by, DFunLike.coe]
  by_cases hij' : (i, j) ∈ γ'
  · simp [hij']
    exact lt_trans (hℓ i j hij') (Nat.lt_add_one ℓ)
  · simp [hij, hij']

theorem content_extend_ssyt_by {γ' : YoungDiagram} {T' : SemistandardYoungTableau γ'}
    {ℓ : ℕ} {hγ : γ' ≤ γ} {hℓ : ∀ i j : ℕ, (i, j) ∈ γ' → T' i j < ℓ}
    {h : ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ γ → (i1, j) ∈ γ'} :
    (extend_ssyt_by T' ℓ hγ hℓ h).content =
    T'.content + Multiset.replicate (γ.card - γ'.card) ℓ := by
  ext n
  rw [Multiset.count_add]
  by_cases hn : n ≥ ℓ
  · rw [count_content_of_forall_lt hℓ hn, zero_add]
    by_cases hn' : n > ℓ
    · rw [count_content_of_forall_lt (forall_mem_extend_ssyt_by_lt) hn', Multiset.count_replicate]
      apply ne_of_lt at hn'
      simp [hn']
    · push_neg at hn'
      have hn : n = ℓ := by exact antisymm hn hn'
      rw [hn, Multiset.count_replicate_self]
      simp only [content, Multiset.count_map, card_sdiff hγ]
      congr
      ext x
      rw [Multiset.count_filter, Multiset.count_eq_of_nodup γ.cells.nodup,
        Multiset.count_eq_of_nodup (γ.cells \ γ'.cells).nodup]
      simp only [Finset.mem_sdiff, Finset.mem_val, extend_ssyt_by, DFunLike.coe, mem_cells]

      by_cases hx' : x ∈ γ'
      · specialize hℓ x.1 x.2 hx'
        apply ne_of_lt at hℓ; symm at hℓ
        simp [hx', hℓ]
      · by_cases hx : x ∈ γ
        · simp [hx', hx]
        · simp [hx, hx']
  · push_neg at hn
    rw [Multiset.count_replicate]
    let hn' := hn; apply ne_of_lt at hn'; symm at hn'
    simp [hn', content, Multiset.count_map]
    congr 1
    ext x
    rw [Multiset.count_filter, Multiset.count_filter,
      Multiset.count_eq_of_nodup (γ.cells.nodup), Multiset.count_eq_of_nodup (γ'.cells.nodup)]
    simp only [Finset.mem_val, mem_cells, extend_ssyt_by, DFunLike.coe]
    by_cases hx' : x ∈ γ'
    · have hx : x ∈ γ := by exact hγ hx'
      simp [hx, hx']
    · by_cases hx : x ∈ γ
      · symm at hn'
        simp [hx, hx', hn']
      · simp [hx, hx']



theorem content_extend_ssyt_by_eq_insert_fromCounts {γ' : YoungDiagram}
    {T' : SemistandardYoungTableau γ'} {ℓ : ℕ} {hγ : γ' ≤ γ}
    {hℓ : ∀ i j : ℕ, (i, j) ∈ γ' → T' i j < ℓ}
    {h : ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ γ → (i1, j) ∈ γ'}
    {μ' : Multiset ℕ} (hT' : T'.content = μ'.fromCounts) (hc : μ'.card = ℓ)
    (hmin : ∀ a ∈ μ', a ≥ γ.card-γ'.card):
    (extend_ssyt_by T' ℓ hγ hℓ h).content = (insert (γ.card-γ'.card) μ').fromCounts := by
  rw [Multiset.insert_eq_cons, content_extend_ssyt_by,
    Multiset.cons_fromCounts_of_min (γ.card - γ'.card), hT', hc]
  exact hmin


theorem exists_ssyt_of_dominates (γ : YoungDiagram) (μ : Multiset ℕ)
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    ∃ T : SemistandardYoungTableau γ, T.content = μ.fromCounts := by
  by_cases hμ : μ = 0
  · have hγ : γ = ⊥ := by
      rw [hμ, Multiset.sum_zero] at h
      simp at h
      ext x
      simp [h]
    rw [hμ, hγ]
    use bot_ssyt
    simp
  · let ℓ := (Multiset.sort (· ≥ ·) μ).length
    have hl : ℓ - 1 < ℓ := by
      rw [← Multiset.card_eq_zero] at hμ
      push_neg at hμ; rw [← Nat.pos_iff_ne_zero] at hμ
      simp [ℓ, hμ]
    let j := sSup {j : ℕ | γ.rowLen j ≥ min_el μ hμ}
    let γ' := remove_bottom γ hμ hd h h0
    let μ' := μ.erase (min_el μ hμ)
    have h0' : 0 ∉ μ' := by
      unfold μ'
      rw [Multiset.mem_erase_of_ne]
      · exact h0
      symm
      exact min_el_ne_zero hμ h0
    suffices ∃ T' : SemistandardYoungTableau γ', T'.content = μ'.fromCounts by
      obtain ⟨T', hT'⟩ := this
      have hμ'c : μ'.card = ℓ - 1 := by simp [μ', min_el_mem hμ, ℓ]

      have hℓ : ∀ i j : ℕ, (i, j) ∈ γ' → T' i j < ℓ-1 := by
        intro i j hij
        have hT'ij : T' i j ∈ T'.content := by exact mem_content_of_mem_cells hij
        rw [hT', Multiset.mem_fromCounts_iff h0', hμ'c] at hT'ij
        exact hT'ij
      use (extend_ssyt_by T' (ℓ-1) (remove_bottom_le hμ hd h h0) hℓ
        (remove_bottom_single_column hμ hd h h0))

      have hmin : μ.sum - μ'.sum = min_el μ hμ := by
        symm
        exact (Nat.eq_sub_of_add_eq (Multiset.sum_erase (min_el_mem hμ)))
      rw [content_extend_ssyt_by_eq_insert_fromCounts hT' hμ'c, h]
      conv => lhs; rhs; rhs; unfold μ'
      rw [remove_bottom_card_eq_erase_min_el_sum hμ hd h h0, Multiset.insert_eq_cons,
          hmin, Multiset.cons_erase (min_el_mem hμ)]
      rw [h, remove_bottom_card_eq_erase_min_el_sum hμ hd h h0, hmin]
      intro a ha
      refine min_el_le' hμ ?_
      exact Multiset.mem_of_mem_erase ha


    refine exists_ssyt_of_dominates γ' μ' ?_ ?_ h0'
    · exact remove_bottom_dominates_erase_min_el hμ hd h h0
    · exact remove_bottom_card_eq_erase_min_el_sum hμ hd h h0

    termination_by μ.sum
    decreasing_by
      rw [← Multiset.sum_erase (min_el_mem hμ)]
      simp
      rw [Nat.pos_iff_ne_zero]
      exact min_el_ne_zero hμ h0




theorem finite_ssyt_content : Finite {T : SemistandardYoungTableau γ |
    T.content = μ.fromCounts} := by
  let f : {T : SemistandardYoungTableau γ | T.content = μ.fromCounts} →
    (γ.cells → {n // n ∈ μ.fromCounts}) := fun ⟨T, hT⟩ ↦ (fun ⟨x, hx⟩ ↦ ⟨T x.1 x.2, by
      rw [Set.mem_setOf] at hT
      rw [← hT]
      exact mem_content_of_mem_cells hx⟩)
  refine Finite.of_injective f ?_
  intro ⟨T, hT⟩ ⟨T', hT'⟩ hf
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
  ext i j
  by_cases hij : (i, j) ∈ γ
  · have hf : (f ⟨T, hT⟩) ⟨(i, j), hij⟩ = (f ⟨T', hT'⟩) ⟨(i, j), hij⟩ := by
      exact congrFun hf ⟨(i, j), hij⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, f] at hf
    exact hf
  · rw [T.zeros hij, T'.zeros hij]

theorem kostka_pos_iff_dominates (h : γ.card = μ.sum) (h0 : 0 ∉ μ) : 0 < kostkaNumber γ μ ↔
    γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ := by
  constructor
  · intro hk
    exact dominates_of_kostka_pos h0 hk
  · intro hd
    simp [Nat.pos_iff_ne_zero, kostkaNumber, ne_eq, Nat.card_eq_zero, not_or]
    constructor
    · exact exists_ssyt_of_dominates γ μ hd h h0
    · exact finite_ssyt_content
