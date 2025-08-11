import Mathlib
import KostkaNumbers.Content

open SemistandardYoungTableau YoungDiagram

variable {γ : YoungDiagram}

theorem row_sorted (T : SemistandardYoungTableau γ) (i j : ℕ) (hj : j < γ.rowLen i) :
    T i j = ((List.ofFn (fun k : Fin (γ.rowLen i) ↦ T i k)).mergeSort (· ≤ ·))[j]'(by
      rw [List.length_mergeSort, List.length_ofFn]; exact hj) := by
  have hTij : T i j = (List.ofFn (fun k : Fin (γ.rowLen i) ↦ T i k))[j]'(by
    rw [List.length_ofFn]; exact hj) := by simp only [List.getElem_ofFn]
  rw [hTij]
  congr 1
  symm
  refine List.mergeSort_of_sorted ?_
  simp only [decide_eq_true_eq, List.pairwise_ofFn]
  intro ⟨j1, _⟩ ⟨j2, hj2⟩ hj
  simp only
  rw [Fin.mk_lt_mk] at hj
  refine T.row_weak hj ?_
  rw [mem_iff_lt_rowLen]
  exact hj2

theorem col_sorted (T : SemistandardYoungTableau γ) (i j : ℕ) (hi : i < γ.colLen j) :
    T i j = ((List.ofFn (fun k : Fin (γ.colLen j) ↦ T k j)).mergeSort (· ≤ ·))[i]'(by
      rw [List.length_mergeSort, List.length_ofFn]; exact hi) := by
  have hTij : T i j = (List.ofFn (fun k : Fin (γ.colLen j) ↦ T k j))[i]'(by
    rw [List.length_ofFn]; exact hi) := by simp only [List.getElem_ofFn]
  rw [hTij]
  congr 1
  symm
  refine List.mergeSort_of_sorted ?_
  simp only [decide_eq_true_eq, List.pairwise_ofFn]
  intro ⟨i1, _⟩ ⟨i2, hi2⟩ hi
  simp only
  rw [Fin.mk_lt_mk] at hi
  refine le_of_lt ?_
  refine T.col_strict hi ?_
  rw [mem_iff_lt_colLen]
  exact hi2




lemma map_row (T : SemistandardYoungTableau γ) {i : ℕ} :
    Multiset.map (fun j : Fin (γ.rowLen i) ↦ T i j.1)
      (Multiset.ofList (List.finRange (γ.rowLen i))) =
    Multiset.map (fun x : ℕ × ℕ ↦ T x.1 x.2) (γ.row i).val := by
  let e : (a : Fin (γ.rowLen i)) → (a ∈ (Multiset.ofList (List.finRange (γ.rowLen i)))) →
    (ℕ × ℕ) := fun a ha ↦ (i, a.1)
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ ?_ ?_ e ?_ ?_ ?_ ?_
  · rw [Multiset.coe_nodup]
    exact List.nodup_finRange (γ.rowLen i)
  · exact (γ.row i).nodup
  · intro ⟨a, ha⟩ ha'
    rw [← mem_iff_lt_rowLen] at ha
    simp [Finset.mem_val, mem_row_iff, e, ha]
  · intro a₁ _ a₂ _ he
    simp [e] at he
    exact Fin.eq_of_val_eq he
  · intro x
    simp only [Finset.mem_val, mem_row_iff, Multiset.mem_coe, List.mem_finRange, exists_const,
      and_imp, e]
    intro hx hxi
    use ⟨x.2, by
      rw [← hxi, ← mem_iff_lt_rowLen]
      exact hx⟩
    simp [← hxi]
  · intro ⟨a, ha⟩ ha'
    simp [e]

lemma map_col (T : SemistandardYoungTableau γ) {j : ℕ} :
    Multiset.map (fun i : Fin (γ.colLen j) ↦ T i j)
      (Multiset.ofList (List.finRange (γ.colLen j))) =
    Multiset.map (fun x : ℕ × ℕ ↦ T x.1 x.2) (γ.col j).val := by
  let e : (a : Fin (γ.colLen j)) → (a ∈ (Multiset.ofList (List.finRange (γ.colLen j)))) →
    (ℕ × ℕ) := fun a ha ↦ (a.1, j)
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ ?_ ?_ e ?_ ?_ ?_ ?_
  · rw [Multiset.coe_nodup]
    exact List.nodup_finRange (γ.colLen j)
  · exact (γ.col j).nodup
  · intro ⟨a, ha⟩ ha'
    rw [← mem_iff_lt_colLen] at ha
    simp [Finset.mem_val, mem_col_iff, e, ha]
  · intro a₁ _ a₂ _ he
    simp [e] at he
    exact Fin.eq_of_val_eq he
  · intro x
    simp only [Finset.mem_val, mem_col_iff, Multiset.mem_coe, List.mem_finRange, exists_const,
      and_imp, e]
    intro hx hxi
    use ⟨x.1, by
      rw [← hxi, ← mem_iff_lt_colLen]
      exact hx⟩
    simp [← hxi]
  · intro ⟨a, ha⟩ ha'
    simp [e]



theorem eq_of_missing_row'' {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    (T' : SemistandardYoungTableau γ') (hγ : γ = γ') (hc : T.content = T'.content) (i₀ : ℕ)
    (h : ∀ i ≠ i₀, ∀ j, T i j = T' i j) : T.entry = T'.entry := by
  ext i j
  by_cases hi : i ≠ i₀
  · exact h i hi j
  push_neg at hi
  simp only [content] at hc
  by_cases hij : (i, j) ∈ γ
  · rw [mem_iff_lt_rowLen] at hij
    let hij' := hij; rw [hγ] at hij'
    rw [to_fun_eq_coe, row_sorted T i j hij, to_fun_eq_coe, row_sorted T' i j hij']
    congr 1
    refine List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _) (List.sorted_mergeSort' _ _)
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    refine List.Perm.symm ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← Multiset.coe_eq_coe, List.ofFn_eq_map, List.ofFn_eq_map, ← Multiset.map_coe,
      ← Multiset.map_coe, map_row, map_row]
    nth_rw 2 [← cells_add_sub_row i] at hc
    nth_rw 1 [← cells_add_sub_row i] at hc
    simp at hc
    suffices Multiset.map (fun x ↦ T x.1 x.2) (γ.cells.val - (γ.row i).val) =
        Multiset.map (fun x ↦ T' x.1 x.2) (γ'.cells.val - (γ'.row i).val) by
      rw [this, add_right_inj] at hc
      symm; exact hc
    simp [← hγ]
    refine Multiset.map_congr rfl ?_
    intro (a, b) hab
    simp only
    by_cases habγ : (a, b) ∈ γ
    · rw [← Multiset.count_pos, Multiset.count_sub, tsub_pos_iff_lt,
        Multiset.count_eq_of_nodup (γ.row i).nodup,
        Multiset.count_eq_of_nodup γ.cells.nodup] at hab
      simp only [Finset.mem_val, mem_row_iff, habγ, true_and, mem_cells, ↓reduceIte, Nat.lt_one_iff,
        ite_eq_right_iff, one_ne_zero, imp_false] at hab
      rw [hi] at hab
      exact h a hab b
    · let habγ' := habγ; rw [hγ] at habγ'
      rw [T.zeros habγ, T'.zeros habγ']
  · let hij' := hij; rw [hγ] at hij'
    rw [to_fun_eq_coe, to_fun_eq_coe, T.zeros hij, T'.zeros hij']

theorem eq_of_missing_row (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (i₀ : ℕ) (h : ∀ i ≠ i₀, ∀ j, T i j = T' i j) : T = T' := by
  suffices T.entry = T'.entry by
    exact ext fun i ↦ congrFun (congrFun this i)
  exact eq_of_missing_row'' T T' rfl hc i₀ h

theorem eq_of_missing_row' (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (i₀ : ℕ) {f : ℕ → ℕ → ℕ} (h : ∀ i ≠ i₀, ∀ j, T i j = f i j)
    (h' : ∀ i ≠ i₀, ∀ j, T' i j = f i j) : T = T' := by
  have h2 : ∀ i ≠ i₀, ∀ j, T i j = T' i j := by
    intro i hi j
    rw [h i hi j, h' i hi j]
  exact eq_of_missing_row T T' hc i₀ h2


theorem eq_of_missing_col'' {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    (T' : SemistandardYoungTableau γ') (hγ : γ = γ') (hc : T.content = T'.content) (j₀ : ℕ)
    (h : ∀ i, ∀ j ≠ j₀, T i j = T' i j) : T.entry = T'.entry := by
  ext i j
  by_cases hj : j ≠ j₀
  · exact h i j hj
  push_neg at hj
  simp only [content] at hc
  by_cases hij : (i, j) ∈ γ
  · rw [mem_iff_lt_colLen] at hij
    let hij' := hij; rw [hγ] at hij'
    rw [to_fun_eq_coe, col_sorted T i j hij, to_fun_eq_coe, col_sorted T' i j hij']
    congr 1
    refine List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _) (List.sorted_mergeSort' _ _)
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    refine List.Perm.symm ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← Multiset.coe_eq_coe, List.ofFn_eq_map, List.ofFn_eq_map, ← Multiset.map_coe,
      ← Multiset.map_coe, map_col, map_col]
    nth_rw 2 [← cells_add_sub_col j] at hc
    nth_rw 1 [← cells_add_sub_col j] at hc
    simp at hc
    suffices Multiset.map (fun x ↦ T x.1 x.2) (γ.cells.val - (γ.col j).val) =
        Multiset.map (fun x ↦ T' x.1 x.2) (γ'.cells.val - (γ'.col j).val) by
      rw [this, add_right_inj] at hc
      symm; exact hc
    simp [← hγ]
    refine Multiset.map_congr rfl ?_
    intro (a, b) hab
    simp only
    by_cases habγ : (a, b) ∈ γ
    · rw [← Multiset.count_pos, Multiset.count_sub, tsub_pos_iff_lt,
        Multiset.count_eq_of_nodup (γ.col j).nodup,
        Multiset.count_eq_of_nodup γ.cells.nodup] at hab
      simp only [Finset.mem_val, mem_col_iff, habγ, true_and, mem_cells, ↓reduceIte, Nat.lt_one_iff,
        ite_eq_right_iff, one_ne_zero, imp_false] at hab
      rw [hj] at hab
      exact h a b hab
    · let habγ' := habγ; rw [hγ] at habγ'
      rw [T.zeros habγ, T'.zeros habγ']
  · let hij' := hij; rw [hγ] at hij'
    rw [to_fun_eq_coe, to_fun_eq_coe, T.zeros hij, T'.zeros hij']

theorem eq_of_missing_col (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (j₀ : ℕ) (h : ∀ i, ∀ j ≠ j₀, T i j = T' i j) : T = T' := by
  suffices T.entry = T'.entry by
    exact ext fun i ↦ congrFun (congrFun this i)
  exact eq_of_missing_col'' T T' rfl hc j₀ h


theorem eq_of_missing_col' (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (j₀ : ℕ) {f : ℕ → ℕ → ℕ} (h : ∀ i, ∀ j ≠ j₀, T i j = f i j)
    (h' : ∀ i, ∀ j ≠ j₀, T' i j = f i j) : T = T' := by
  have h2 : ∀ i, ∀ j ≠ j₀, T i j = T' i j := by
    intro i j hj
    rw [h i j hj, h' i j hj]
  exact eq_of_missing_col T T' hc j₀ h2
