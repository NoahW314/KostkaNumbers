/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Recursion

open Kostka SemistandardYoungTableau YoungDiagram

variable {γ : YoungDiagram}

lemma exists_nonzero {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∃ m, f.1 m ≠ 0 := by
  have hf' : ∑ x ∈ f.1.support, f.1 x ≠ 0 := hf ▸ (Nat.zero_ne_add_one k).symm
  simpa using hf'

noncomputable
def extractOne {f : SubRowLensType γ} {k : ℕ} (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ℕ →₀ ℕ :=
  Finsupp.single (Classical.choose (exists_nonzero hf)) 1

lemma extractOne_SubRowLensType {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) :
    (∀ i, γ.rowLen' i - (f.1 - extractOne hf) i ≥ γ.rowLen' (i + 1)) ∧
    (∀ i, (f.1 - extractOne hf) i ≤ γ.rowLen' i) := by
  constructor
  · intro i
    let hf' := f.2.1
    specialize hf' i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le]
    lia
  · intro i
    let hf' := f.2.2
    specialize hf' i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, tsub_le_iff_right, ge_iff_le]
    lia

lemma extractOne_le {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : extractOne hf ≤ f.1 := by
  intro i
  unfold extractOne
  by_cases hi : i = Classical.choose (exists_nonzero hf)
  · rw [hi, Finsupp.single_eq_same]
    exact Nat.one_le_iff_ne_zero.mpr <| Classical.choose_spec (exists_nonzero hf)
  · rw [Finsupp.single_eq_of_ne hi]
    exact Nat.zero_le _

lemma extractOne_sub_add {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) :
    f.1 - extractOne hf + extractOne hf = f.1 := by
  have hle := extractOne_le hf
  ext i
  specialize hle i
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
  lia

lemma extractOne_le_sub {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∀ i, extractOne hf i ≤
    (γ.sub (f.1 - extractOne hf)).rowLen' i := by
  intro i
  rw [sub_rowLen']
  · simp only [Finsupp.coe_tsub, Pi.sub_apply]
    grind [extractOne_le hf i]
  · intro i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
    have := f.2.1 i
    lia

lemma extractOne_rowLen'_sub_self_ge {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∀ i,
    (γ.sub (f.1 - extractOne hf)).rowLen' i - extractOne hf i ≥
    (γ.sub (f.1 - extractOne hf)).rowLen' (i + 1) := by
  intro i
  rw [sub_rowLen' <| sub_cond (extractOne_SubRowLensType hf).1]
  simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
  grind [extractOne_le hf i]

lemma extractOne_sum_support {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) :
    ∑ x ∈ (extractOne hf).support, extractOne hf x = 1 := by
  simp [extractOne]

lemma extractOne_sub_sum_support {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) :
    ∑ x ∈ (f.1 - extractOne hf).support, (f.1 - extractOne hf) x = k := by
  have : ∑ x ∈ (f.1 - extractOne hf).support,
      (f.1 - extractOne hf) x = ∑ x ∈ f.1.support, (f.1 - extractOne hf) x :=
    Finset.sum_subset_zero_on_sdiff Finsupp.support_tsub (by simp) (by simp)
  rw [this]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  rw [Finset.sum_tsub_distrib, hf]
  · suffices ∑ x ∈ (extractOne hf).support, (extractOne hf) x =
        ∑ x ∈ f.1.support, (extractOne hf) x by
      rw [← this, extractOne_sum_support hf, add_tsub_cancel_right]
    exact Finset.sum_subset_zero_on_sdiff (Finsupp.support_mono (extractOne_le hf)) (by simp)
      (by simp)
  · intro x _
    exact extractOne_le hf x

lemma sub_extractOne_eq_sub {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : γ.sub f.1 =
    (γ.sub (f.1 - extractOne hf)).sub (extractOne hf) := by
  have hfi : ∀ i, γ.rowLen' i - (f.1 - extractOne hf) i ≥
      γ.rowLen' (i + 1) - (f.1 - extractOne hf) (i + 1) := by
    intro i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
    have := f.2.1 i
    lia
  rw [← rowLen'_eq_iff, sub_rowLen' (sub_cond f.2.1),
    sub_rowLen', sub_rowLen' hfi]
  · ext i
    simp
    grind [extractOne_le hf i]
  · intro i
    simp [sub_rowLen' hfi]
    grind [extractOne_le hf i]
