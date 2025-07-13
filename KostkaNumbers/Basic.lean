import Mathlib
import KostkaNumbers.Util
import KostkaNumbers.Diagrams
import KostkaNumbers.Content

open SemistandardYoungTableau
open YoungDiagram

/-
Convention: Use capital letters for normal multisets and Greek letters for partition-like multisets
  e.g. γ : YoungDiagram, μ = M.counts
-/


namespace Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {T : SemistandardYoungTableau γ}

noncomputable def kostkaNumber (γ : YoungDiagram) (μ : Multiset ℕ) :=
  Nat.card {T : SemistandardYoungTableau γ | T.content = μ.fromCounts}



theorem kostka_eq_zero {γ : YoungDiagram} {μ : Multiset ℕ}
    (h : ∀ T : SemistandardYoungTableau γ, T.content ≠ μ.fromCounts) : kostkaNumber γ μ = 0 := by
  rw [kostkaNumber, Nat.card_eq_zero]
  left; exact Subtype.isEmpty_of_false h

theorem kostka_eq_zero_iff {γ : YoungDiagram} {μ : Multiset ℕ} :
    kostkaNumber γ μ = 0 ↔ ∀ T : SemistandardYoungTableau γ, T.content ≠ μ.fromCounts := by
  constructor; swap
  · exact kostka_eq_zero
  rw [kostkaNumber, Nat.card_eq_zero]
  intro h
  suffices ¬Infinite {T : SemistandardYoungTableau γ // T.content = μ.fromCounts} by
    simp [this] at h
    rw [isEmpty_iff] at h
    intro T hT
    exact h ⟨T, hT⟩
  simp
  refine Fintype.finite ?_
  sorry


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



theorem kostka_horizontal (μ : Multiset ℕ) :
    kostkaNumber (horizontalDiagram μ.sum) μ = 1 := by
  unfold kostkaNumber
  rw [Nat.card_eq_one_iff_exists, ← Multiset.fromCounts_card]
  use ⟨horizontal_ofMultiset μ.fromCounts, by
    rw [Set.mem_setOf, content_horizontal_ofMultiset]⟩
  intro ⟨T, hT⟩
  rw [Subtype.mk.injEq]; rw [Set.mem_setOf] at hT
  ext i j; simp only [DFunLike.coe]
  rw [eq_horizontal_ofMultiset_content T]
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



end Kostka
