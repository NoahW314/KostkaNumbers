/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Content

open SemistandardYoungTableau YoungDiagram

variable {γ : YoungDiagram}

theorem row_sorted (T : SemistandardYoungTableau γ) (i j : ℕ) (hj : j < γ.rowLen i) :
    T i j = ((List.ofFn (fun k : Fin (γ.rowLen i) ↦ T i k)).mergeSort (· ≤ ·))[j]'(by
      rwa [List.length_mergeSort, List.length_ofFn]) := by
  have hTij : T i j = (List.ofFn (fun k : Fin (γ.rowLen i) ↦ T i k))[j]'(by rwa [List.length_ofFn])
    := by simp
  rw [hTij]
  congr 1
  refine (List.mergeSort_of_pairwise ?_).symm
  simp only [decide_eq_true_eq, List.pairwise_ofFn]
  intro ⟨j1, _⟩ ⟨j2, hj2⟩ hj
  rw [Fin.mk_lt_mk] at hj
  refine T.row_weak hj ?_
  rw [mem_iff_lt_rowLen]
  exact hj2

theorem col_sorted (T : SemistandardYoungTableau γ) (i j : ℕ) (hi : i < γ.colLen j) :
    T i j = ((List.ofFn (fun k : Fin (γ.colLen j) ↦ T k j)).mergeSort (· ≤ ·))[i]'(by
      rwa [List.length_mergeSort, List.length_ofFn]) := by
  have hTij : T i j = (List.ofFn (fun k : Fin (γ.colLen j) ↦ T k j))[i]'(by
    rwa [List.length_ofFn]) := by simp
  rw [hTij]
  congr 1
  refine (List.mergeSort_of_pairwise ?_).symm
  simp only [decide_eq_true_eq, List.pairwise_ofFn]
  intro ⟨i1, _⟩ ⟨i2, hi2⟩ hi
  rw [Fin.mk_lt_mk] at hi
  refine le_of_lt <| T.col_strict hi ?_
  rwa [mem_iff_lt_colLen]




lemma map_row (f : ℕ → ℕ → ℕ) {i : ℕ} :
    Multiset.map (fun j : Fin (γ.rowLen i) ↦ f i j.1)
      (Multiset.ofList (List.finRange (γ.rowLen i))) =
    Multiset.map (fun x : ℕ × ℕ ↦ f x.1 x.2) (γ.row i).val := by
  let e : (a : Fin (γ.rowLen i)) → (a ∈ (Multiset.ofList (List.finRange (γ.rowLen i)))) →
    (ℕ × ℕ) := fun a ha ↦ (i, a.1)
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ ?_ (γ.row i).nodup e ?_ ?_ ?_ ?_
  · rw [Multiset.coe_nodup]
    exact List.nodup_finRange (γ.rowLen i)
  · intro ⟨a, ha⟩ ha'
    rw [← mem_iff_lt_rowLen] at ha
    simp [Finset.mem_val, mem_row_iff, e, ha]
  · grind
  · intro x
    simp only [Finset.mem_val, mem_row_iff, Multiset.mem_coe, List.mem_finRange, exists_const,
      and_imp, e]
    intro hx hxi
    use ⟨x.2, by rwa [← hxi, ← mem_iff_lt_rowLen]⟩
    simp [← hxi]
  · grind

-- upstream
lemma row_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.row i =
    Finset.image Prod.swap (γ.col i) := by
  ext x
  simp [row, col]
  grind

-- upstream
lemma col_transpose (γ : YoungDiagram) (i : ℕ) : γ.transpose.col i =
    Finset.image Prod.swap (γ.row i) := by
  nth_rw 2 [← transpose_transpose γ]
  rw [row_transpose γ.transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

lemma col_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.col i =
    Finset.image Prod.swap (γ.transpose.row i) := by
  rw [row_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

lemma row_eq_image_swap_transpose {γ : YoungDiagram} (i : ℕ) : γ.row i =
    Finset.image Prod.swap (γ.transpose.col i) := by
  rw [col_transpose, Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

lemma map_col (f : ℕ → ℕ → ℕ) {j : ℕ} :
    Multiset.map (fun i : Fin (γ.colLen j) ↦ f i j)
    (Multiset.ofList (List.finRange (γ.colLen j))) =
    Multiset.map (fun x : ℕ × ℕ ↦ f x.1 x.2) (γ.col j).val := by
  rw [← rowLen_transpose, col_eq_image_swap_transpose, Finset.image_val_of_injOn,
    Multiset.map_map]
  · exact map_row (fun i j ↦ f j i)
  · exact Set.injOn_of_injective Prod.swap_injective



theorem eq_entry_of_map_row {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (T' : SemistandardYoungTableau γ) (i j : ℕ)
    (h : Multiset.map (fun x ↦ T x.1 x.2) (γ.row i).val =
    Multiset.map (fun x ↦ T' x.1 x.2) (γ.row i).val) : T i j = T' i j := by
  by_cases hij : (i, j) ∈ γ
  · rw [mem_iff_lt_rowLen] at hij
    rw [row_sorted T i j hij, row_sorted T' i j hij]
    congr 1
    refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _)
      (List.pairwise_mergeSort' _ _) ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) <| List.Perm.symm ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← Multiset.coe_eq_coe, List.ofFn_eq_map, List.ofFn_eq_map, ← Multiset.map_coe,
      ← Multiset.map_coe, map_row, map_row]
    exact h.symm
  · rw [T.zeros hij, T'.zeros hij]

theorem eq_of_missing_row'' {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    (T' : SemistandardYoungTableau γ') (hγ : γ = γ') (hc : T.content = T'.content) (i₀ : ℕ)
    (h : ∀ i ≠ i₀, ∀ j, T i j = T' i j) : T.entry = T'.entry := by
  ext i j
  by_cases hi : i ≠ i₀
  · exact h i hi j
  push Not at hi
  simp only [content] at hc
  by_cases hij : (i, j) ∈ γ
  · rw [mem_iff_lt_rowLen] at hij
    let hij' := hij; rw [hγ] at hij'
    rw [to_fun_eq_coe, row_sorted T i j hij, to_fun_eq_coe, row_sorted T' i j hij']
    congr 1
    refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _)
      (List.pairwise_mergeSort' _ _) ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) <| List.Perm.symm ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← Multiset.coe_eq_coe, List.ofFn_eq_map, List.ofFn_eq_map, ← Multiset.map_coe,
      ← Multiset.map_coe, map_row, map_row]
    nth_rw 2 [← cells_add_sub_row i] at hc
    nth_rw 1 [← cells_add_sub_row i] at hc
    simp only [Multiset.map_add] at hc
    suffices Multiset.map (fun x ↦ T x.1 x.2) (γ.cells.val - (γ.row i).val) =
        Multiset.map (fun x ↦ T' x.1 x.2) (γ'.cells.val - (γ'.row i).val) by
      rw [this, add_right_inj] at hc
      exact hc.symm
    simp only [← hγ]
    refine Multiset.map_congr rfl ?_
    intro (a, b) hab
    simp only
    by_cases habγ : (a, b) ∈ γ
    · rw [← Multiset.count_pos, Multiset.count_sub, tsub_pos_iff_lt,
        Multiset.count_eq_of_nodup (γ.row i).nodup,
        Multiset.count_eq_of_nodup γ.cells.nodup] at hab
      simp only [Finset.mem_val, mem_row_iff, habγ, true_and, mem_cells, ↓reduceIte, Nat.lt_one_iff,
        ite_eq_right_iff, one_ne_zero, imp_false, hi] at hab
      exact h a hab b
    · rw [T.zeros habγ, T'.zeros (hγ ▸ habγ)]
  · rw [to_fun_eq_coe, to_fun_eq_coe, T.zeros hij, T'.zeros (hγ ▸ hij)]

theorem eq_of_missing_row (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (i₀ : ℕ) (h : ∀ i ≠ i₀, ∀ j, T i j = T' i j) : T = T' := by
  suffices T.entry = T'.entry by exact ext fun i ↦ congrFun (congrFun this i)
  exact eq_of_missing_row'' T T' rfl hc i₀ h

theorem eq_of_missing_row' (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (i₀ : ℕ) {f : ℕ → ℕ → ℕ} (h : ∀ i ≠ i₀, ∀ j, T i j = f i j)
    (h' : ∀ i ≠ i₀, ∀ j, T' i j = f i j) : T = T' :=
  eq_of_missing_row T T' hc i₀ (by grind)


theorem eq_of_missing_col'' {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    (T' : SemistandardYoungTableau γ') (hγ : γ = γ') (hc : T.content = T'.content) (j₀ : ℕ)
    (h : ∀ i, ∀ j ≠ j₀, T i j = T' i j) : T.entry = T'.entry := by
  ext i j
  by_cases hj : j ≠ j₀
  · exact h i j hj
  push Not at hj
  simp only [content] at hc
  by_cases hij : (i, j) ∈ γ
  · rw [mem_iff_lt_colLen] at hij
    let hij' := hij; rw [hγ] at hij'
    rw [to_fun_eq_coe, col_sorted T i j hij, to_fun_eq_coe, col_sorted T' i j hij']
    congr 1
    refine List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _)
      (List.pairwise_mergeSort' _ _) ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) <| List.Perm.symm ?_
    refine List.Perm.trans (List.mergeSort_perm _ _) ?_
    rw [← Multiset.coe_eq_coe, List.ofFn_eq_map, List.ofFn_eq_map, ← Multiset.map_coe,
      ← Multiset.map_coe, map_col, map_col]
    nth_rw 2 [← cells_add_sub_col j] at hc
    nth_rw 1 [← cells_add_sub_col j] at hc
    simp only [Multiset.map_add] at hc
    suffices Multiset.map (fun x ↦ T x.1 x.2) (γ.cells.val - (γ.col j).val) =
        Multiset.map (fun x ↦ T' x.1 x.2) (γ'.cells.val - (γ'.col j).val) by
      rw [this, add_right_inj] at hc
      exact hc.symm
    simp only [← hγ]
    refine Multiset.map_congr rfl ?_
    intro (a, b) hab
    simp only
    by_cases habγ : (a, b) ∈ γ
    · rw [← Multiset.count_pos, Multiset.count_sub, tsub_pos_iff_lt,
        Multiset.count_eq_of_nodup (γ.col j).nodup,
        Multiset.count_eq_of_nodup γ.cells.nodup] at hab
      simp only [Finset.mem_val, mem_col_iff, habγ, true_and, mem_cells, ↓reduceIte, Nat.lt_one_iff,
        ite_eq_right_iff, one_ne_zero, imp_false, hj] at hab
      exact h a b hab
    · rw [T.zeros habγ, T'.zeros (hγ ▸ habγ)]
  · rw [to_fun_eq_coe, to_fun_eq_coe, T.zeros hij, T'.zeros (hγ ▸ hij)]

theorem eq_of_missing_col (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (j₀ : ℕ) (h : ∀ i, ∀ j ≠ j₀, T i j = T' i j) : T = T' := by
  suffices T.entry = T'.entry by exact ext fun i ↦ congrFun (congrFun this i)
  exact eq_of_missing_col'' T T' rfl hc j₀ h


theorem eq_of_missing_col' (T T' : SemistandardYoungTableau γ) (hc : T.content = T'.content)
    (j₀ : ℕ) {f : ℕ → ℕ → ℕ} (h : ∀ i, ∀ j ≠ j₀, T i j = f i j)
    (h' : ∀ i, ∀ j ≠ j₀, T' i j = f i j) : T = T' :=
  eq_of_missing_col T T' hc j₀ (by grind)
