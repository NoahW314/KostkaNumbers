import Mathlib
import KostkaNumbers.Util.FromCounts
import KostkaNumbers.Util.MinMaxEl
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

lemma mem_content_of_mem_cells {i j : ℕ} (h : (i, j) ∈ γ) : T i j ∈ T.content := by
  simp only [content, Multiset.mem_map, Finset.mem_val, YoungDiagram.mem_cells, Prod.exists]
  use i; use j

lemma mem_content_of_nonzero {i j : ℕ} (h : T i j ≠ 0) : T i j ∈ T.content := by
  apply mem_content_of_mem_cells
  contrapose! h; exact T.zeros h




def bot_ssyt : SemistandardYoungTableau ⊥ := ⟨0, by simp, by simp, by simp⟩

@[simp] lemma bot_content : bot_ssyt.content = ⊥ := by simp [content]

lemma content_eq_bot_iff : T.content = ⊥ ↔ γ = ⊥ := by
  simp [content]; symm
  exact YoungDiagram.ext_iff

lemma ssyt_bot (T : SemistandardYoungTableau ⊥) : T = bot_ssyt := by
  ext i j
  rw [zeros T (notMem_bot (i, j)), zeros bot_ssyt (notMem_bot (i, j))]

lemma zero_entry_of_bot {i j : ℕ} (h : γ = ⊥) : T i j = 0 := by
  apply T.zeros; rw [h]; apply notMem_bot


lemma entry_le_max_el {γ : YoungDiagram} {T : SemistandardYoungTableau γ} {i j : ℕ}
    (hTc : T.content ≠ 0) : T i j ≤ max_el T.content hTc := by
  by_cases hij : T i j = 0
  · rw [hij]
    exact Nat.zero_le (max_el T.content hTc)
  · refine le_max_el' hTc ?_
    exact mem_content_of_nonzero hij

lemma entry_lt_card {μ : Multiset ℕ} (h : T.content = μ.fromCounts) {i j : ℕ}
    (hij : (i, j) ∈ γ) : T i j < μ.card := by
  suffices T i j ∈ μ.fromCounts by
    contrapose! this
    exact Multiset.notMem_fromCounts μ (T i j) this
  rw [← h]
  exact mem_content_of_mem_cells hij

lemma entry_lt_rowLens_card (h : T.content = (Multiset.ofList γ.rowLens).fromCounts) {i j : ℕ}
    (hij : (i, j) ∈ γ) : T i j < (Multiset.ofList γ.rowLens).card := by
  exact entry_lt_card h hij


lemma entry_ge_col {i j : ℕ} (h : (i, j) ∈ γ) : T i j ≥ i := by
  induction' i with i ih
  · simp
  calc T (i + 1) j
    _ > T i j := T.col_strict (lt_add_one i) h
    _ ≥ i := by refine ih ?_; exact γ.up_left_mem (le_of_lt (lt_add_one i)) (by rfl) h


lemma highestWeight_content : (highestWeight γ).content =
    (Multiset.ofList γ.rowLens).fromCounts := by
  simp [Multiset.fromCounts, content, highestWeight, DFunLike.coe]
  ext n
  simp only [Multiset.count_map, ← ge_iff_le, List.coe_ofList_sorted (rowLens_sorted γ),
    get_rowLens, Multiset.count_sum', Multiset.count_replicate]
  by_cases hn : n < ((Multiset.ofList γ.rowLens).toList.mergeSort (· ≥ ·)).length
  · rw [Finset.sum_eq_single_of_mem (⟨n, hn⟩ : {m //
      m < ((Multiset.ofList γ.rowLens).toList.mergeSort (· ≥ ·)).length}) (Finset.mem_univ _)]
    · simp [rowLen_eq_filter]
    · simp only [Finset.mem_univ, ne_eq, ite_eq_right_iff, forall_const, Subtype.forall, ge_iff_le,
        List.length_mergeSort, Multiset.length_toList, Multiset.coe_card, length_rowLens,
        Subtype.mk.injEq]
      intro a _ han han'
      contradiction

  · rw [Finset.sum_eq_zero]
    · simp only [Multiset.card_eq_zero, Multiset.filter_eq_nil, Finset.mem_val, mem_cells,
        Prod.forall]
      intro i j hij
      simp only [hij, ↓reduceIte]
      contrapose! hn
      simp only [hn, ge_iff_le, List.length_mergeSort, Multiset.length_toList, Multiset.coe_card,
        length_rowLens, ← mem_iff_lt_colLen]
      exact γ.up_left_mem (by rfl) (Nat.zero_le j) hij
    · simp only [Finset.mem_univ, ite_eq_right_iff, forall_const, Subtype.forall, ge_iff_le,
        List.length_mergeSort, Multiset.length_toList, Multiset.coe_card, length_rowLens]
      intro a ha han
      rw [han] at ha
      simp only [ge_iff_le, List.length_mergeSort, Multiset.length_toList, Multiset.coe_card,
        length_rowLens, not_lt] at hn
      omega




lemma entry_zero_of_content_eq_replicate (n : ℕ)
    (h : T.content = Multiset.replicate n 0) (i j : ℕ) : T i j = 0 := by
  by_cases hb : γ = ⊥
  · exact zero_entry_of_bot hb

  suffices T i j ∈ T.content by
    rw [h] at this
    exact Multiset.eq_of_mem_replicate this
  by_cases htij : T i j = 0
  · rw [htij, h]
    refine Multiset.mem_replicate.mpr ?_
    simp only [ne_eq, and_true]
    contrapose! hb
    rw [hb, Multiset.replicate_zero, ← Multiset.bot_eq_zero, content_eq_bot_iff] at h
    exact h
  exact mem_content_of_nonzero htij



theorem top_left_of_content_fromCounts {μ : Multiset ℕ} (hγ : γ ≠ ⊥)
    (h : T.content = μ.fromCounts) : T 0 0 = 0 := by
  have h0 : 0 ∈ μ.fromCounts := by
    refine Multiset.zero_mem_fromCounts_of_nonempty ?_
    rw [← h, ne_eq, ← bot_eq_zero, content_eq_bot_iff]
    exact hγ
  rw [← h] at h0
  simp [content] at h0
  obtain ⟨i, j, hij, hT⟩ := h0
  refine antisymm ?_ (Nat.zero_le (T 0 0))
  nth_rw 3 [← hT]
  have hi : T 0 0 ≤ T i 0 := by
    exact T.col_weak (Nat.zero_le i) <| γ.up_left_mem (by rfl) (Nat.zero_le j) hij
  refine le_trans hi ?_
  exact T.row_weak_of_le (Nat.zero_le j) hij




end SemistandardYoungTableau
