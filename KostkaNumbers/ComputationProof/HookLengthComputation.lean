import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.HookLength


open YoungDiagram SemistandardYoungTableau Kostka


/-
Partitions of 4
-/

lemma kostka_22 : kostkaNumber (ofRowLens [2, 2] (by simp))
    (Multiset.replicate 4 1) = 2 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 2] (by simp)).cells = {(0,0), (0,1), (1,0), (1,1)} by simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx; interval_cases hx2 : x.2
    all_goals rw [← Prod.eta x]; simp [hx1, hx2]
  · intro h
    rcases h with h|h|h|h
    all_goals simp [h]

lemma kostka_211 : kostkaNumber (ofRowLens [2, 1, 1] (by simp))
    (Multiset.replicate 4 1) = 3 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 1, 1] (by simp)).cells =
      {(0,0), (0,1), (1,0), (2,0)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx;
    · interval_cases hx2 : x.2
      all_goals rw [← Prod.eta x]; simp [hx1, hx2]
    all_goals rw [← Prod.eta x]; simp [hx1, hx]
  · intro h
    rcases h with h|h|h|h
    all_goals simp [h]


/-
Partitiosn of 5
-/

lemma kostka_32 : kostkaNumber (ofRowLens [3, 2] (by simp))
    (Multiset.replicate 5 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 2] (by simp)).cells =
      {(0,0), (0,1), (0,2), (1,0), (1,1)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx; interval_cases hx2 : x.2
    all_goals rw [← Prod.eta x]; simp [hx1, hx2]
  · intro h
    rcases h with h|h|h|h|h
    all_goals simp [h]

lemma kostka_311 : kostkaNumber (ofRowLens [3, 1, 1] (by simp))
    (Multiset.replicate 5 1) = 6 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 1, 1] (by simp)).cells =
      {(0,0), (0,1), (0,2), (1,0), (2,0)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx;
    · interval_cases hx2 : x.2
      all_goals rw [← Prod.eta x]; simp [hx1, hx2]
    all_goals rw [← Prod.eta x]; simp [hx1, hx]
  · intro h
    rcases h with h|h|h|h|h
    all_goals simp [h]

lemma kostka_221 : kostkaNumber (ofRowLens [2, 2, 1] (by simp))
    (Multiset.replicate 5 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 2, 1] (by simp)).cells =
      {(0,0), (0,1), (1,0), (1,1), (2,0)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx
    rotate_right 1
    · rw [← Prod.eta x]; simp [hx1, hx]
    all_goals interval_cases hx2 : x.2
    all_goals rw [← Prod.eta x]; simp [hx1, hx2]
  · intro h
    rcases h with h|h|h|h|h
    all_goals simp [h]


/-
Partitions of 6
-/

lemma kostka_411 : kostkaNumber (ofRowLens [4, 1, 1] (by simp))
    (Multiset.replicate 6 1) = 10 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [4, 1, 1] (by simp)).cells =
      {(0,0), (0,1), (0,2), (0,3), (1,0), (2,0)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx;
    · interval_cases hx2 : x.2
      all_goals rw [← Prod.eta x]; simp [hx1, hx2]
    all_goals rw [← Prod.eta x]; simp [hx1, hx]
  · intro h
    rcases h with h|h|h|h|h|h
    all_goals simp [h]

lemma kostka_33 : kostkaNumber (ofRowLens [3, 3] (by simp))
    (Multiset.replicate 6 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 3] (by simp)).cells =
      {(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx; interval_cases hx2 : x.2
    all_goals rw [← Prod.eta x]; simp [hx1, hx2]
  · intro h
    rcases h with h|h|h|h|h|h
    all_goals simp [h]

lemma kostka_321 : kostkaNumber (ofRowLens [3, 2, 1] (by simp))
    (Multiset.replicate 6 1) = 16 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [3, 2, 1] (by simp)).cells =
      {(0,0), (0,1), (0,2), (1,0), (1,1), (2,0)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx
    rotate_right 1
    · rw [← Prod.eta x]; simp [hx1, hx]
    all_goals interval_cases hx2 : x.2
    all_goals rw [← Prod.eta x]; simp [hx1, hx2]
  · intro h
    rcases h with h|h|h|h|h|h
    all_goals simp [h]

lemma kostka_222 : kostkaNumber (ofRowLens [2, 2, 2] (by simp))
    (Multiset.replicate 6 1) = 5 := by
  rw [hookLength_formula _ (by simp)]
  norm_num
  suffices (ofRowLens [2, 2, 2] (by simp)).cells =
      {(0,0), (0,1), (1,0), (1,1), (2,0), (2,1)} by
    simp [this]
  ext x
  simp [mem_ofRowLens]
  constructor
  · intro ⟨h, hx⟩
    interval_cases hx1 : x.1
    all_goals simp at hx; interval_cases hx2 : x.2
    all_goals rw [← Prod.eta x]; simp [hx1, hx2]
  · intro h
    rcases h with h|h|h|h|h|h
    all_goals simp [h]
