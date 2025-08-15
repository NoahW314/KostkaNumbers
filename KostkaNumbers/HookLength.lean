import Mathlib
import KostkaNumbers.Basic

open YoungDiagram SemistandardYoungTableau Kostka

namespace YoungDiagram

def hookLength (γ : YoungDiagram) (i j : ℕ) : ℕ :=
  (γ.rowLen i - (j + 1)) + (γ.colLen j - (i + 1)) + 1

@[simp] lemma hookLength_def (γ : YoungDiagram) (i j : ℕ) :
    γ.hookLength i j = (γ.rowLen i - (j + 1)) + (γ.colLen j - (i + 1)) + 1 := by rfl

-- TODO: Prove that this is equivalent to the card definition given in the paper

end YoungDiagram


theorem hookLength_formula (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    kostkaNumber γ (Multiset.replicate n 1) =
    Nat.factorial n / ∏ x ∈ γ.cells, γ.hookLength x.1 x.2 := by
  sorry
