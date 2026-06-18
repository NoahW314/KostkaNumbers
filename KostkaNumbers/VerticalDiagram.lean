/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Util.Util
import KostkaNumbers.Diagrams

open SemistandardYoungTableau YoungDiagram

def verticalDiagram (n : ℕ) := ofRowLens (List.replicate n 1) (List.sortedGE_replicate n)


@[simp] lemma verticalDiagram_card {n : ℕ} : (verticalDiagram n).card = n := by
  simp [verticalDiagram]

@[simp] lemma verticalDiagram_rowLens {n : ℕ} :
    (verticalDiagram n).rowLens = List.replicate n 1 := by
  simp [verticalDiagram, rowLens_ofRowLens_eq_self]
