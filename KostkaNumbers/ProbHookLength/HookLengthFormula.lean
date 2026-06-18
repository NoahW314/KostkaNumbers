/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.HookLength.HookLength
/-!
This file formalizes the probabilistic proof of the hook length formula given by
  Greene, Nijenhus, and Wilf (1979).
-/
open Kostka MeasureTheory
open scoped ENNReal NNReal


namespace YoungDiagram

variable (γ : YoungDiagram)
end YoungDiagram

theorem hookLength_formula' (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    (∏ x ∈ γ.cells, γ.hookLength x.1 x.2) *
    kostkaNumber γ (Multiset.replicate n 1) = Nat.factorial n := by
  sorry

theorem hookLength_formula (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    kostkaNumber γ (Multiset.replicate n 1) =
    Nat.factorial n / ∏ x ∈ γ.cells, γ.hookLength x.1 x.2 := by
  simp [← hookLength_formula' γ h]
