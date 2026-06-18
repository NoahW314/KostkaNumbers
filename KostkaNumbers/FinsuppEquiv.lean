/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Diagrams

/-
This shows that YoungDiagrams are equivalent to finitely supported
  antitone functions from ℕ to ℕ
-/

open YoungDiagram

namespace YoungDiagram

def rowLen' (γ : YoungDiagram) : ℕ →₀ ℕ := ⟨Finset.range (γ.colLen 0),
  γ.rowLen, by simp [← Nat.pos_iff_ne_zero, ← mem_iff_lt_colLen, mem_iff_lt_rowLen]⟩

lemma rowLen'_anti (γ : YoungDiagram) : Antitone (γ.rowLen') := by
  rw [Finsupp.coe_mk]
  exact γ.rowLen_anti

lemma rowLen'_eq_rowLen {γ : YoungDiagram} {i : ℕ} : γ.rowLen' i = γ.rowLen i := by
  simp [rowLen']

def ofRowLen' (f : ℕ →₀ ℕ) (hf : Antitone f) : YoungDiagram :=
  ⟨Finset.biUnion f.support (fun i ↦ {i} ×ˢ Finset.range (f i)),
  by
  simp only [IsLowerSet, Finset.singleton_product, Finset.coe_biUnion, Finset.mem_coe,
    Finsupp.mem_support_iff, ne_eq, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_range,
    Set.mem_iUnion, Set.mem_image, Set.mem_Iio, exists_prop, forall_exists_index, and_imp,
    Prod.forall, Prod.mk.injEq, exists_eq_right_right, Prod.mk_le_mk]
  intro a b c d hca hdb x hfx y hyfx hxa hyb
  rw [hxa] at hfx
  rw [hxa, hyb] at hyfx
  constructor
  · contrapose! hfx
    rw [← nonpos_iff_eq_zero, ← hfx]
    exact hf hca
  · specialize hf hca
    lia
  ⟩

@[simp] lemma mem_ofRowLen' (f : ℕ →₀ ℕ) (hf : Antitone f) (x : ℕ × ℕ) :
    x ∈ ofRowLen' f hf ↔ x.2 < f x.1 := by
  simp only [ofRowLen', Finset.singleton_product, mem_mk, Finset.mem_biUnion,
    Finsupp.mem_support_iff, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · intro h
    obtain ⟨a, _, ⟨b, hb, hx⟩⟩ := h
    simp [← hx, hb]
  · intro hx
    use x.1
    constructor
    · rw [← Nat.pos_iff_ne_zero]
      exact lt_of_le_of_lt (Nat.zero_le x.2) hx
    · use x.2

@[simp] lemma ofRowLen'_rowLen'_eq_self (γ : YoungDiagram) :
    ofRowLen' γ.rowLen' γ.rowLen'_anti = γ := by
  ext x
  simp [rowLen', ← mem_iff_lt_rowLen]

@[simp] lemma rowLen'_ofRowLen'_eq_self (f : ℕ →₀ ℕ) (hf : Antitone f) :
    (ofRowLen' f hf).rowLen' = f := by
  ext n
  simp only [rowLen', ofRowLen', Finsupp.coe_mk, rowLen_eq_card, row]
  suffices Finset.filter (fun c ↦ c.1 = n)
      (f.support.biUnion (fun i ↦ {i} ×ˢ Finset.range (f i))) =
      {n} ×ˢ Finset.range (f n) by
    rw [this]
    simp
  aesop

def equivRowLen' : YoungDiagram ≃ {f : ℕ →₀ ℕ // Antitone f} where
  toFun γ := ⟨γ.rowLen', γ.rowLen'_anti⟩
  invFun f := ofRowLen' f.1 f.2
  left_inv := ofRowLen'_rowLen'_eq_self
  right_inv := by
    intro ⟨f, hf⟩
    simp


@[simp] lemma rowLen'_eq_zero {γ : YoungDiagram} {i : ℕ} (hi : ¬ i < γ.colLen 0) :
    γ.rowLen' i = 0 := by
  rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hi
  push Not at hi
  exact hi

lemma rowLen'_eq_zero_of_ge_length {γ : YoungDiagram} (i : ℕ) (hi : i ≥ γ.rowLens.length) :
    γ.rowLen' i = 0 := by
  rw [length_rowLens] at hi
  exact rowLen'_eq_zero (by lia)

-- upstream
lemma rowLen_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) : γ'.rowLen ≤ γ.rowLen := by
  intro i
  refine le_of_not_gt ?_
  rw [← mem_iff_lt_rowLen]
  suffices (i, γ.rowLen i) ∉ γ by
    contrapose this
    exact h this
  rw [mem_iff_lt_rowLen]
  exact Nat.lt_irrefl (γ.rowLen i)

lemma rowLen'_mono {γ γ' : YoungDiagram} (h : γ' ≤ γ) : γ'.rowLen' ≤ γ.rowLen' := by
  simp_rw [rowLen', Finsupp.le_def, Finsupp.coe_mk]
  exact rowLen_mono h

lemma rowLen'_eq_iff {γ γ' : YoungDiagram} : γ.rowLen' = γ'.rowLen' ↔ γ = γ' := by
  constructor
  · intro h
    rw! [← γ.ofRowLen'_rowLen'_eq_self, h, γ'.ofRowLen'_rowLen'_eq_self]
    rfl
  · intro h
    rw [h]

end YoungDiagram
