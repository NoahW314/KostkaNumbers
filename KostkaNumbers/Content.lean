/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Util.FromCounts
import KostkaNumbers.Diagrams

/-
Definition of the content of a SemistandardYoungTableau, i.e. the multiset of numbers
  in the entries of the tableau.
Also some lemmas about the content of various special types of diagrams
-/

open YoungDiagram

variable {γ : YoungDiagram} {T : SemistandardYoungTableau γ}

namespace SemistandardYoungTableau

def content (T : SemistandardYoungTableau γ) :=
  Multiset.map (fun (i, j) => T i j) (γ.cells).val

@[simp] lemma content_card_eq_card : T.content.card = γ.card := by
  simp [content]

lemma mem_content_of_mem {i j : ℕ} (h : (i, j) ∈ γ) : T i j ∈ T.content := by
  simp only [content, Multiset.mem_map, Finset.mem_val, YoungDiagram.mem_cells, Prod.exists]
  use i, j

lemma mem_content_of_nonzero {i j : ℕ} (h : T i j ≠ 0) : T i j ∈ T.content := by
  refine mem_content_of_mem ?_
  contrapose! h
  exact T.zeros h




def bot_ssyt : SemistandardYoungTableau ⊥ := ⟨0, by simp, by simp, by simp⟩

@[simp] lemma bot_content : bot_ssyt.content = ⊥ := by simp [content]

lemma content_eq_bot_iff : T.content = ⊥ ↔ γ = ⊥ := by
  simp [content, eq_bot_iff_card_eq_zero]

lemma ssyt_bot (T : SemistandardYoungTableau ⊥) : T = bot_ssyt := by
  ext i j
  rw [zeros T (notMem_bot (i, j)), zeros bot_ssyt (notMem_bot (i, j))]

lemma zero_entry_of_bot {i j : ℕ} (h : γ = ⊥) : T i j = 0 := by
  refine T.zeros ?_
  rw [h]
  exact notMem_bot _


lemma entry_le_max {γ : YoungDiagram} {T : SemistandardYoungTableau γ} {i j : ℕ}
    (hTc : T.content.toList ≠ []) :
    T i j ≤ T.content.toList.max hTc := by
  by_cases hij : T i j = 0
  · rw [hij]
    exact Nat.zero_le _
  · refine List.le_max_of_mem ?_
    simp [mem_content_of_nonzero hij]

lemma entry_lt_card {μ : Multiset ℕ} (h : T.content = μ.fromCounts) {i j : ℕ}
    (hij : (i, j) ∈ γ) : T i j < μ.card := by
  suffices T i j ∈ μ.fromCounts by
    contrapose! this
    exact Multiset.notMem_fromCounts μ (T i j) this
  rw [← h]
  exact mem_content_of_mem hij


lemma entry_ge_col {i j : ℕ} (h : (i, j) ∈ γ) : T i j ≥ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      calc T (i + 1) j
        _ > T i j := T.col_strict (lt_add_one i) h
        _ ≥ i := ih <| γ.up_left_mem (le_of_lt (lt_add_one i)) (by rfl) h


-- upstream these six (or more?) lemmas
@[simp]
lemma Set.setOf_subtype_eq_eq_singleton {α : Type*} {p : α → Prop} (a : α) (ha : p a) :
    {x : Subtype p | x.1 = a} = {⟨a, ha⟩} := by grind

@[simp]
lemma Set.setOf_subtype_eq_eq_singleton' {α : Type*} {p : α → Prop} (a : α) (ha : p a) :
    {x : Subtype p | a = x.1} = {⟨a, ha⟩} := by grind

@[simp]
lemma Finset.filter_eq_eq_singleton {α : Type*} [DecidableEq α] {s : Finset α} (a : α)
    (ha : a ∈ s) : Finset.filter (fun x ↦ x = a) s = {a} := by grind

@[simp]
lemma Finset.filter_eq_eq_singleton' {α : Type*} [DecidableEq α] {s : Finset α} (a : α)
    (ha : a ∈ s) : Finset.filter (fun x ↦ a = x) s = {a} := by grind

@[simp]
lemma Finset.filter_subtype_eq_eq_singleton {α : Type*} [DecidableEq α] {p : α → Prop}
    {s : Finset (Subtype p)} (a : α) (ha : p a) (has : ⟨a, ha⟩ ∈ s) :
    Finset.filter (fun x : Subtype p ↦ x.1 = a) s = {⟨a, ha⟩} := by grind

@[simp]
lemma Finset.filter_subtype_eq_eq_singleton' {α : Type*} [DecidableEq α] {p : α → Prop}
    {s : Finset (Subtype p)} (a : α) (ha : p a) (has : ⟨a, ha⟩ ∈ s) :
    Finset.filter (fun x : Subtype p ↦ a = x.1) s = {⟨a, ha⟩} := by grind

@[simp]
lemma Fin.filter_eq_val_eq_singleton {n : ℕ} {s : Finset (Fin n)} (a : ℕ) (ha : a < n)
    (has : ⟨a, ha⟩ ∈ s) :
    Finset.filter (fun x : Fin n ↦ x.1 = a) s = {⟨a, ha⟩} := by grind

@[simp]
lemma Fin.filter_eq_val_eq_singleton' {n : ℕ} {s : Finset (Fin n)} (a : ℕ) (ha : a < n)
    (has : ⟨a, ha⟩ ∈ s) :
    Finset.filter (fun x : Fin n ↦ a = x.1) s = {⟨a, ha⟩} := by grind



lemma highestWeight_content : (highestWeight γ).content =
    (Multiset.ofList γ.rowLens).fromCounts := by
  simp only [content, DFunLike.coe, highestWeight, to_fun_eq_coe, Prod.mk.eta, Multiset.fromCounts,
    Multiset.coe_sort, ge_iff_le]
  ext n
  simp only [Multiset.count_map, ← rowLen_eq_filter, get_rowLens, Multiset.count_sum',
    List.mergeSort_eq_self _ γ.rowLens_sorted.pairwise, Multiset.count_replicate, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  let : Fintype {n : ℕ // n < (γ.rowLens.mergeSort (· ≥ ·)).length} :=
    Fintype.ofFinite { n // n < (γ.rowLens.mergeSort (· ≥ ·)).length }
  by_cases! hn : n < ((Multiset.ofList γ.rowLens).sort (· ≥ ·)).length
  · rw [Finset.filter_subtype_eq_eq_singleton n hn (Finset.mem_univ _)]
    simp
  · simp only [ge_iff_le, Multiset.coe_sort, List.length_mergeSort, length_rowLens] at hn
    rw [rowLen_eq_zero <| Nat.not_lt.mpr hn]
    refine (Finset.sum_eq_zero ?_).symm
    simp
    grind




lemma entry_zero_of_content_eq_replicate (n : ℕ)
    (h : T.content = Multiset.replicate n 0) (i j : ℕ) : T i j = 0 := by
  by_cases hb : γ = ⊥
  · exact zero_entry_of_bot hb
  suffices T i j ∈ T.content by
    rw [h] at this
    exact Multiset.eq_of_mem_replicate this
  by_cases htij : T i j = 0
  · rw [htij, h, Multiset.mem_replicate]
    simp only [ne_eq, and_true]
    contrapose! hb
    rwa [hb, Multiset.replicate_zero, ← Multiset.bot_eq_zero, content_eq_bot_iff] at h
  · exact mem_content_of_nonzero htij



theorem top_left_of_content_fromCounts {μ : Multiset ℕ} (hγ : γ ≠ ⊥)
    (h : T.content = μ.fromCounts) : T 0 0 = 0 := by
  have h0 : 0 ∈ μ.fromCounts := by
    refine Multiset.zero_mem_fromCounts_of_nonempty ?_
    rwa [← h, ne_eq, ← bot_eq_zero, content_eq_bot_iff]
  simp only [← h, content, Multiset.mem_map, Finset.mem_val, mem_cells, Prod.exists] at h0
  obtain ⟨i, j, hij, hT⟩ := h0
  refine antisymm ?_ (Nat.zero_le (T 0 0))
  nth_rw 3 [← hT]
  refine le_trans (T.col_weak (Nat.zero_le i) <| γ.up_left_mem (by rfl) (Nat.zero_le j) hij) ?_
  exact T.row_weak_of_le (Nat.zero_le j) hij




end SemistandardYoungTableau
