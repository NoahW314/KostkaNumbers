import Mathlib
import KostkaNumbers.Util.Util
import KostkaNumbers.Diagrams

open SemistandardYoungTableau YoungDiagram

namespace List

variable {α : Type*}

end List

def verticalDiagram (n : ℕ) := ofRowLens (List.replicate n 1) <| (List.sorted_ge_replicate n 1)


@[simp] lemma verticalDiagram_card {n : ℕ} : (verticalDiagram n).card = n := by
  simp [verticalDiagram]

@[simp] lemma verticalDiagram_rowLens {n : ℕ} :
    (verticalDiagram n).rowLens = List.replicate n 1 := by
  simp [verticalDiagram, rowLens_ofRowLens_eq_self]
