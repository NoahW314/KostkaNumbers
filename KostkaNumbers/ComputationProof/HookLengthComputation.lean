/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.ProbHookLength.HookLengthFormula
import KostkaNumbers.ComputationProof.Computation


open YoungDiagram SemistandardYoungTableau Kostka


/-
Partitions of 4
-/

lemma kostka_22 : kostkaNumber (ofRowLens [2, 2] (sorted_pair (by rfl))) (Multiset.replicate 4 1) =
    2 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 2] (sorted_pair (by rfl))).cells = {(0,0), (0,1), (1,0), (1,1)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  grind

lemma kostka_211 : kostkaNumber (ofRowLens [2, 1, 1] (sorted_triple (by norm_num) (by rfl)))
    (Multiset.replicate 4 1) = 3 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 1, 1] (sorted_triple (by norm_num) (by rfl))).cells =
      {(0,0), (0,1), (1,0), (2,0)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind


/-
Partitiosn of 5
-/

lemma kostka_32 : kostkaNumber (ofRowLens [3, 2] (sorted_pair (by norm_num)))
    (Multiset.replicate 5 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 2] (sorted_pair (by norm_num))).cells =
      {(0,0), (0,1), (0,2), (1,0), (1,1)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind

lemma kostka_311 : kostkaNumber (ofRowLens [3, 1, 1] (sorted_triple (by norm_num) (by rfl)))
    (Multiset.replicate 5 1) = 6 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 1, 1] (sorted_triple (by norm_num) (by rfl))).cells =
      {(0,0), (0,1), (0,2), (1,0), (2,0)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind

lemma kostka_221 : kostkaNumber (ofRowLens [2, 2, 1] (sorted_triple (by rfl) (by norm_num)))
    (Multiset.replicate 5 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 2, 1] (sorted_triple (by rfl) (by norm_num))).cells =
      {(0,0), (0,1), (1,0), (1,1), (2,0)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind


/-
Partitions of 6
-/

lemma kostka_411 : kostkaNumber (ofRowLens [4, 1, 1] (sorted_triple (by norm_num) (by rfl)))
    (Multiset.replicate 6 1) = 10 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [4, 1, 1] (sorted_triple (by norm_num) (by rfl))).cells =
      {(0,0), (0,1), (0,2), (0,3), (1,0), (2,0)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind

lemma kostka_33 : kostkaNumber (ofRowLens [3, 3] (sorted_pair (by rfl)))
    (Multiset.replicate 6 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 3] (sorted_pair (by rfl))).cells =
      {(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind

lemma kostka_321 : kostkaNumber (ofRowLens [3, 2, 1] (sorted_triple (by norm_num) (by norm_num)))
    (Multiset.replicate 6 1) = 16 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 2, 1] (sorted_triple (by norm_num) (by norm_num))).cells =
      {(0,0), (0,1), (0,2), (1,0), (1,1), (2,0)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind

lemma kostka_222 : kostkaNumber (ofRowLens [2, 2, 2] (sorted_triple (by rfl) (by rfl)))
    (Multiset.replicate 6 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 2, 2] (sorted_triple (by rfl) (by rfl))).cells =
      {(0,0), (0,1), (1,0), (1,1), (2,0), (2,1)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  grind
