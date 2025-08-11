import Mathlib
import KostkaNumbers.Basic

open Kostka YoungDiagram

def padZeros_parts {d : ℕ} (μ : Nat.Partition d) (n : ℕ) : Multiset ℕ :=
  (Multiset.replicate (n-d) 0) + μ.parts

/-
The main inequality concering Kostka numbers that I'm trying to prove.
Corollary 4.7 in the paper
-/

/-
theorem kostka_inequality {n d : ℕ} (hn : n ≥ 2) (hd : d ≥ 2) (hnd : n > d)
    (γ : YoungDiagram) (hγc : γ.card = n) (hγ : γ ≠ horizontalDiagram n) :
    (kostkaNumber γ (Multiset.replicate n 1)) *
    (∑ μ : Nat.Partition d, kostkaNumber (hookDiagram n) (padZeros_parts μ n).counts) ≥
    (kostkaNumber (hookDiagram n) (Multiset.replicate n 1)) *
    (∑ μ : Nat.Partition d, kostkaNumber γ ((padZeros_parts μ n).counts)) := by
  sorry
-/
