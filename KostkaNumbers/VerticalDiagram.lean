import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.ComputationProof.RowColEq

open Kostka SemistandardYoungTableau YoungDiagram

namespace List

variable {α : Type*}

lemma sorted_ge_replicate (n : ℕ) (a : α) [Preorder α] :
    List.Sorted (· ≥ ·) (List.replicate n a) := by
  simp [Sorted, pairwise_replicate]

end List

def verticalDiagram (n : ℕ) := ofRowLens (List.replicate n 1) <| (List.sorted_ge_replicate n 1)
