import Mathlib
import KostkaNumbers.HookLength
import KostkaNumbers.FactorialLemma


open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n : ℕ}

theorem kostka_ineq_two_rows {p : ℕ} (h2 : γ.rowLens = [n - p, p]) (hn : n ≥ 5)
    (hp0 : p ≠ 0) (hγ : γ.card = n) (h : γ.card = μ.sum) (hμ : μ ≠ 0)
    (hp : p ≤ min_el μ hμ) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  sorry
