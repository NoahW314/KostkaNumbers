import Mathlib
import KostkaNumbers.Util
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




lemma entry_lt_card {μ : Multiset ℕ} (h : T.content = μ.fromCounts) {i j : ℕ}
    (hij : (i, j) ∈ γ) (h0 : 0 ∉ μ) : T i j < μ.card := by
  suffices T i j ∈ μ.fromCounts by
    contrapose! this
    rw [← Multiset.remove_of_notMem μ 0 h0] at this
    exact Multiset.notMem_fromCounts μ (T i j) this
  rw [← h]
  exact mem_content_of_mem_cells hij

lemma entry_lt_rowLens_card (h : T.content = (Multiset.ofList γ.rowLens).fromCounts) {i j : ℕ}
    (hij : (i, j) ∈ γ) : T i j < (Multiset.ofList γ.rowLens).card := by
  exact entry_lt_card h hij zero_notMem_rowLens

lemma highestWeight_content : (highestWeight γ).content =
    (Multiset.ofList γ.rowLens).fromCounts := by
  rw [Multiset.eq_fromCounts_iff _ _ zero_notMem_rowLens]
  constructor; swap; constructor; swap; constructor

  · simp [highestWeight, content, DFunLike.coe]
    intro n hn; use n; use 0
    suffices (n, 0) ∈ γ by simp [this]
    exact mem_iff_lt_colLen.mpr hn

  · simp [highestWeight, content, DFunLike.coe]
    intro n hn i j hij
    simp [hij]
    contrapose! hn
    rw [← mem_iff_lt_colLen, ← hn]
    exact γ.up_left_mem (by rfl) (Nat.zero_le j) hij

  · simp only [ge_iff_le, content, DFunLike.coe, highestWeight, to_fun_eq_coe, Prod.mk.eta,
      Multiset.count_map, Multiset.coe_card,
      Multiset.remove_of_notMem (Multiset.ofList γ.rowLens) 0 zero_notMem_rowLens]
    suffices ∀ n ∈ List.range γ.rowLens.length, γ.rowLen n = (Multiset.filter
        (fun a ↦ n = if a ∈ γ then a.1 else 0) γ.cells.val).card by
      rw [← List.map_congr_left this]
      simp
      rw [← YoungDiagram.rowLens]
      exact rowLens_sorted γ
    intro n _
    exact rowLen_eq_filter

  · simp [highestWeight, content, DFunLike.coe, Multiset.counts, rowLens]
    rw [← Multiset.map_coe, Multiset.coe_range]
    refine Multiset.map_congr (Eq.symm (range_colLen_eq_map_dedup γ)) ?_
    intro n hn
    symm
    rw [Multiset.count_map]
    exact rowLen_eq_filter






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







end SemistandardYoungTableau
