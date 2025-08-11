import Mathlib
import KostkaNumbers.Coe
import KostkaNumbers.Diagrams
import KostkaNumbers.Content
import KostkaNumbers.ComputationProof.RowColEq

open SemistandardYoungTableau
open YoungDiagram

/-
Convention: Use capital letters for normal multisets and Greek letters for partition-like multisets
  e.g. γ : YoungDiagram, μ = M.counts
-/




namespace Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {T : SemistandardYoungTableau γ}

def SemistandardYoungTableauWithContent (γ : YoungDiagram) (μ : Multiset ℕ) :=
  {T : SemistandardYoungTableau γ | T.content = μ.fromCounts}

lemma finite_ssyt_content (γ : YoungDiagram) (μ : Multiset ℕ) :
    Finite (SemistandardYoungTableauWithContent γ μ) := by
  let f : {T : SemistandardYoungTableau γ | T.content = μ.fromCounts} →
    (γ.cells → {n // n ∈ μ.fromCounts}) := fun ⟨T, hT⟩ ↦ (fun ⟨x, hx⟩ ↦ ⟨T x.1 x.2, by
      rw [Set.mem_setOf] at hT
      rw [← hT]
      exact mem_content_of_mem_cells hx⟩)
  refine Finite.of_injective f ?_
  intro ⟨T, hT⟩ ⟨T', hT'⟩ hf
  simp only [Subtype.mk.injEq]
  ext i j
  by_cases hij : (i, j) ∈ γ
  · have hf : (f ⟨T, hT⟩) ⟨(i, j), hij⟩ = (f ⟨T', hT'⟩) ⟨(i, j), hij⟩ := by
      exact congrFun hf ⟨(i, j), hij⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, f] at hf
    exact hf
  · rw [T.zeros hij, T'.zeros hij]

noncomputable
instance fintype_ssyt_content (γ : YoungDiagram) (μ : Multiset ℕ) :
    Fintype (SemistandardYoungTableauWithContent γ μ) := by
  have := finite_ssyt_content γ μ
  exact Fintype.ofFinite (SemistandardYoungTableauWithContent γ μ)


noncomputable def kostkaNumber (γ : YoungDiagram) (μ : Multiset ℕ) :=
  Nat.card {T : SemistandardYoungTableau γ | T.content = μ.fromCounts}


lemma kostkaNumber_eq_card_ssyt_content : kostkaNumber γ μ =
    Nat.card (SemistandardYoungTableauWithContent γ μ) := by
  simp [kostkaNumber, SemistandardYoungTableauWithContent]


theorem kostka_eq_zero {γ : YoungDiagram} {μ : Multiset ℕ}
    (h : ∀ T : SemistandardYoungTableau γ, T.content ≠ μ.fromCounts) : kostkaNumber γ μ = 0 := by
  rw [kostkaNumber, Nat.card_eq_zero]
  left; exact Subtype.isEmpty_of_false h

theorem kostka_eq_zero_iff_forall_not {γ : YoungDiagram} {μ : Multiset ℕ} :
    kostkaNumber γ μ = 0 ↔ ∀ T : SemistandardYoungTableau γ, T.content ≠ μ.fromCounts := by
  constructor
  · intro h
    contrapose! h
    simp only [kostkaNumber, Set.coe_setOf, nonempty_subtype, h, ne_eq, Nat.card_eq_zero,
      not_isEmpty_of_nonempty, false_or, not_infinite_iff_finite]
    exact finite_ssyt_content γ μ
  · exact kostka_eq_zero


lemma kostka_bot_bot : kostkaNumber ⊥ ⊥ = 1 := by
  rw [kostkaNumber, Nat.card_eq_one_iff_exists]
  use ⟨bot_ssyt, by rw [Set.mem_setOf, Multiset.fromCounts_bot]; exact bot_content⟩
  intro ⟨T, hT⟩
  simp only [Subtype.mk.injEq]
  exact ssyt_bot T

theorem kostka_ne_card (γ : YoungDiagram) (μ : Multiset ℕ) (h : γ.card ≠ μ.sum) :
    kostkaNumber γ μ = 0 := by
  apply kostka_eq_zero
  intro T
  contrapose! h
  symm; rw [← Multiset.fromCounts_card, ← h]
  exact content_card_eq_card

lemma eq_highestWeight_ge_row (h : T.content = (Multiset.ofList γ.rowLens).fromCounts)
    (i₀ i j : ℕ) (hi : i ≥ i₀) : T i j = (highestWeight γ) i j := by
  by_cases hi₀ : i₀ ≥ γ.colLen 0
  · have hij : (i, j) ∉ γ := by
      contrapose! hi₀
      rw [← mem_iff_lt_colLen]
      exact γ.up_left_mem hi (Nat.zero_le j) hi₀
    rw [T.zeros hij, (highestWeight γ).zeros hij]
  · push_neg at hi₀
    have hT : ∀ i' ≥ i₀ + 1, ∀ j', T i' j' = (highestWeight γ) i' j' := by
      intro i' hi' j'
      exact eq_highestWeight_ge_row h (i₀ + 1) i' j' hi'
    suffices T i₀ j = (highestWeight γ) i₀ j by
      by_cases hi₀' : i = i₀
      · rw [hi₀', this]
      · have hi' : i ≥ i₀ + 1 := by omega
        exact hT i hi' j
    by_cases hij : (i₀, j) ∈ γ
    · conv => rhs; simp only [highestWeight, DFunLike.coe, hij, reduceIte]
      refine antisymm (entry_ge_col hij) ?_
      have hTc : T i₀ j < (Multiset.ofList γ.rowLens).card := entry_lt_card h hij
      apply_fun Multiset.count (T i₀ j) at h
      contrapose! h
      refine ne_of_gt ?_
      rw [Multiset.count_fromCounts hTc]
      simp [List.coe_ofList_sorted (rowLens_sorted γ), content, Multiset.count_map,
        rowLen_eq_card]
      refine Multiset.card_lt_card ?_
      refine lt_of_le_of_ne ?_ ?_
      · rw [Multiset.le_iff_subset (γ.row (T i₀ j)).nodup]
        intro x
        simp only [Finset.mem_val, mem_row_iff, Multiset.mem_filter, mem_cells, and_imp]
        intro hx hxT
        simp only [hx, true_and]
        specialize hT x.1 ?_ x.2
        · rw [hxT]
          exact h
        · simp only [highestWeight_apply, Prod.mk.eta, hx, ↓reduceIte] at hT
          rw [hT, hxT]
      · apply_fun Multiset.count (i₀, j)
        apply ne_of_lt at h
        simp [Multiset.count_eq_of_nodup (γ.cells.nodup), mem_row_iff, hij, h]
    · rw [T.zeros hij, (highestWeight γ).zeros hij]

lemma eq_highestWeight_iff :
    T = highestWeight γ ↔ T.content = (Multiset.ofList γ.rowLens).fromCounts := by
  constructor
  · intro h
    rw [h]
    exact highestWeight_content
  · intro h
    ext i j
    exact eq_highestWeight_ge_row h 0 i j (Nat.zero_le i)

theorem kostka_self : kostkaNumber γ (Multiset.ofList γ.rowLens) = 1 := by
  simp [kostkaNumber, ← eq_highestWeight_iff]


end Kostka
