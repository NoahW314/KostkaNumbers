/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.FinsuppEquiv
import KostkaNumbers.Content

open YoungDiagram SemistandardYoungTableau


namespace YoungDiagram

lemma antitone_sub_of_antitone {f g : ℕ →₀ ℕ}
    (h : ∀ i, f i - g i ≥ f (i + 1) - g (i + 1)) : Antitone (f - g) := by
  intro i j
  induction j with
  | zero => grind
  | succ j ih =>
    intro hij
    by_cases hij' : i = j + 1
    · rw [hij']
    specialize ih (by lia)
    refine le_trans ?_ ih
    rw [Finsupp.coe_tsub, Pi.sub_apply, Pi.sub_apply]
    exact h j


open Classical in
noncomputable
def sub (γ : YoungDiagram) (f : ℕ →₀ ℕ) : YoungDiagram :=
  if h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))
  then ofRowLen' (γ.rowLen' - f) (antitone_sub_of_antitone h) else ⊥

variable {γ : YoungDiagram} {f : ℕ →₀ ℕ}

@[simp] lemma mem_sub (x : ℕ × ℕ)
    (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))) :
    x ∈ γ.sub f ↔ x.2 < γ.rowLen' x.1 - f x.1 := by
  simp [sub, h]

@[simp] lemma sub_rowLen' (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))) :
    (γ.sub f).rowLen' = γ.rowLen' - f := by
  simp [sub, h]

@[simp]
lemma sub_zero (γ : YoungDiagram) : γ.sub (0 : ℕ →₀ ℕ) = γ := by
  rw [← rowLen'_eq_iff, sub_rowLen', tsub_zero]
  intro i
  simp [γ.rowLen'_anti (Nat.le_add_right i 1)]

lemma sub_le (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1))) :
    γ.sub f ≤ γ := by
  intro x hx
  rw [mem_sub _ h] at hx
  rw [mem_iff_lt_rowLen]
  exact lt_of_lt_of_le hx <| Nat.sub_le (γ.rowLen x.1) (f x.1)


theorem sub_cond (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) :
    ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1)) := by
  grind

lemma exists_mem_sdiff_of_ne {g : ℕ →₀ ℕ}
    (hf : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1))
    (hg : ∀ i, γ.rowLen' i - g i ≥ γ.rowLen' (i + 1))
    (hf' : ∀ i, f i ≤ γ.rowLen' i) (hg' : ∀ i, g i ≤ γ.rowLen' i)
    (hfg : f ≠ g) :
    ∃ x ∈ γ, (x ∈ (γ.sub f).cells \ (γ.sub g).cells) ∨
    (x ∈ (γ.sub g).cells \ (γ.sub f).cells) := by
  rw [Finsupp.ne_iff] at hfg
  obtain ⟨i, hfg⟩ := hfg
  wlog hfg' : f i > g i generalizing f g
  · specialize this hg hf hg' hf' hfg.symm ?_
    · push Not at hfg'
      exact Nat.lt_of_le_of_ne hfg' hfg
    · obtain ⟨x, this⟩ := this
      rw [Or.comm] at this
      use x
  · use (i, γ.rowLen' i - (g i + 1))
    constructor
    · rw [mem_iff_lt_rowLen, ← rowLen'_eq_rowLen]
      grind
    · right
      simp only [Finset.mem_sdiff, mem_cells, mem_sub _ (sub_cond hf),
        mem_sub _ (sub_cond hg), not_lt, tsub_le_iff_right]
      grind

abbrev valid_extend (γ γ' : YoungDiagram) := ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ γ → (i1, j) ∈ γ'

lemma sub_valid (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1)) :
    valid_extend γ (γ.sub f) := by
  intro i1 i2 j hi hij2
  rw [mem_iff_lt_rowLen] at hij2
  simp only [mem_sub _ (sub_cond h)]
  refine lt_of_lt_of_le ?_ (h i1)
  rw [rowLen'_eq_rowLen]
  refine lt_of_lt_of_le hij2 ?_
  exact γ.rowLen_anti (i1 + 1) i2 hi


lemma card_sub (h : ∀ i, γ.rowLen' i - f i ≥ γ.rowLen' (i + 1) - (f (i + 1)))
    (h' : ∀ i, f i ≤ γ.rowLen' i) :
    (γ.sub f).card = γ.card - ∑ x ∈ f.support, f x := by
  simp only [card_eq_sum_rowLens_get, List.get_eq_getElem, get_rowLens, ← rowLen'_eq_rowLen,
    sub_rowLen' h, Finsupp.coe_tsub, Pi.sub_apply]
  have hf : ∑ x ∈ f.support, f x = ∑ x : Fin (γ.rowLens.length), f x.1 := by
    rw [Fin.sum_univ_eq_sum_range]
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · intro x
      simp only [Finsupp.mem_support_iff, ne_eq, length_rowLens, Finset.mem_range]
      contrapose
      intro hx
      suffices γ.rowLen' x = 0 by grind
      rw [rowLen'_eq_rowLen]
      exact rowLen_eq_zero hx
    · simp
    · simp
  rw [hf, ← Finset.sum_tsub_distrib _ (by simp [h'])]
  have hrs : ∑ x : Fin (γ.sub f).rowLens.length, (γ.rowLen' x.1 - f x.1) =
      ∑ x ∈ Finset.range (γ.sub f).rowLens.length, (γ.rowLen' x - f x) := by
    rw [← Fin.sum_univ_eq_sum_range]
  have hrs' : ∑ x : Fin γ.rowLens.length, (γ.rowLen' x.1 - f x.1) =
      ∑ x ∈ Finset.range γ.rowLens.length, (γ.rowLen' x - f x) := by
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hrs, hrs']
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · simp [colLen_mono 0 (γ.sub_le h)]
  · simp only [length_rowLens, Finset.mem_sdiff, Finset.mem_range, not_lt, and_imp]
    intro x hx hxs
    rw [← Pi.sub_apply, ← Finsupp.coe_tsub, ← sub_rowLen' h, rowLen'_eq_rowLen]
    have : ¬ x < (γ.sub f).colLen 0 := by lia
    rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen] at this
    push Not at this
    rwa [Nat.le_zero] at this
  · simp

end YoungDiagram


namespace SemistandardYoungTableau

lemma entry_lt_ite_max {γ : YoungDiagram} {f : ℕ →₀ ℕ} (T : SemistandardYoungTableau (γ.sub f))
    (i j : ℕ) (hij : (i, j) ∈ γ.sub f) :
     T i j < (if hTc : T.content.toList = [] then 0 else ((T.content.toList.max hTc) + 1)) := by
  split_ifs with hTc
  · apply_fun List.length at hTc
    simp only [Multiset.length_toList, content_card_eq_card, List.length_nil,
      Finset.card_eq_zero] at hTc
    rw [← mem_cells, hTc] at hij
    contradiction
  · suffices T i j ≤ T.content.toList.max hTc by exact Order.lt_add_one_iff.mpr this
    refine List.le_max_of_mem ?_
    simp [mem_content_of_mem hij]






def restrict {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ' ≤ γ) :
  SemistandardYoungTableau γ' := ⟨
    fun i j ↦ if (i, j) ∈ γ' then T i j else 0,
    by
      intro i j1 j2 hj hij2
      have hij1 : (i, j1) ∈ γ' := γ'.up_left_mem (by rfl) (le_of_lt hj) hij2
      simp only [hij2, ↓reduceIte, hij1, T.row_weak hj (h hij2)]
    ,
      by
      intro i1 i2 j hi hij2
      have hij1 : (i1, j) ∈ γ' := γ'.up_left_mem (le_of_lt hi) (by rfl) hij2
      simp only [hij1, ↓reduceIte, hij2]
      exact T.col_strict hi (h hij2)
    ,
      by grind
  ⟩

def extend {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ')
  (hγ : valid_extend γ γ') (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
  SemistandardYoungTableau γ := ⟨
    fun i j ↦ if (i, j) ∈ γ then if (i, j) ∈ γ' then T i j else a else 0, by
      intro i j1 j2 hj hij2
      have hij1 : (i, j1) ∈ γ := γ.up_left_mem (by rfl) (le_of_lt hj) hij2
      by_cases hij2' : (i, j2) ∈ γ'
      · have hij1' : (i, j1) ∈ γ' := γ'.up_left_mem (by rfl) (le_of_lt hj) hij2'
        simp [hij1, hij2, hij1', hij2', T.row_weak hj hij2']
      · grind
    ,
      by
      intro i1 i2 j hi hij2
      have hij1 : (i1, j) ∈ γ := γ.up_left_mem (le_of_lt hi) (by rfl) hij2
      by_cases hij2' : (i2, j) ∈ γ'
      · have hij1' : (i1, j) ∈ γ' := γ'.up_left_mem (le_of_lt hi) (by rfl) hij2'
        simp [hij1', hij2', hij1, hij2, T.col_strict hi hij2']
      · have hij1' : (i1, j) ∈ γ' := hγ i1 i2 j hi hij2
        simp [hij1, hij2, hij1', hij2', ha i1 j hij1']
    ,
      by grind
  ⟩

@[simp] lemma restrict_entry {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ' ≤ γ)
    (i j : ℕ) (hij : (i, j) ∈ γ') : (T.restrict h) i j = T i j := by
  simp only [restrict, DFunLike.coe, hij, reduceIte]

theorem extend_restrict {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ') (h : γ' ≤ γ)
    (hγ : valid_extend γ γ') (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
    (T.extend hγ a ha).restrict h = T := by
  ext i j
  simp only [extend, restrict, DFunLike.coe]
  by_cases hij' : (i, j) ∈ γ'
  · have hij : (i, j) ∈ γ := h hij'
    simp [hij', hij]
  · simp only [hij', ↓reduceIte]
    exact (T.zeros hij').symm

theorem restrict_extend {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    {a : ℕ} (h : γ' ≤ γ) (hγ : valid_extend γ γ')
    (hγ' : ∀ i j : ℕ, (i, j) ∈ γ → (i, j) ∉ γ' → T i j = a)
    (ha : ∀ i j : ℕ, (i, j) ∈ γ' → (T.restrict h) i j < a) :
    (T.restrict h).extend hγ a ha = T := by
  ext i j
  simp only [restrict, extend, DFunLike.coe]
  by_cases hij' : (i, j) ∈ γ'
  · have hij : (i, j) ∈ γ := h hij'
    simp [hij, hij']
  · by_cases hij : (i, j) ∈ γ
    · simp only [hij, ↓reduceIte, hij']
      exact (hγ' i j hij hij').symm
    · simp only [hij, ↓reduceIte]
      exact (T.zeros hij).symm


lemma extend_content {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ') (h : γ' ≤ γ)
    (hγ : valid_extend γ γ') (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
    (T.extend hγ a ha).content = T.content + Multiset.replicate (γ.card - γ'.card) a := by
  simp only [content, extend, DFunLike.coe, Prod.mk.eta]
  ext b
  by_cases hb : b = a
  · simp only [hb, Multiset.count_map, Multiset.count_add, Multiset.count_replicate_self]
    rw [card_sdiff h, Finset.card_def, ← Multiset.card_add]
    congr
    ext x
    simp [Multiset.count_filter, Multiset.count_eq_of_nodup γ'.cells.nodup,
      Multiset.count_eq_of_nodup γ.cells.nodup]
    grind
  · push Not at hb
    simp only [Multiset.count_map, Multiset.count_add, Multiset.count_replicate, hb.symm,
      ↓reduceIte, add_zero]
    congr 1
    ext x
    simp [Multiset.count_filter, Multiset.count_eq_of_nodup γ'.cells.nodup,
      Multiset.count_eq_of_nodup γ.cells.nodup]
    by_cases hx' : x ∈ γ'
    · simp [h hx', hx']
    · grind

lemma mem_content_sdiff_of_mem_sdiff {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hγ : γ' ≤ γ) {i j : ℕ} (h : (i, j) ∈ γ.cells \ γ'.cells) :
    T i j ∈ T.content - (T.restrict hγ).content := by
  simp at h
  have hmap : Multiset.map (fun x ↦ (T.restrict hγ) x.1 x.2) γ'.cells.val =
      Multiset.map (fun x ↦ T x.1 x.2) γ'.cells.val := by
    refine Multiset.map_congr rfl ?_
    intro x hx
    simp only [Finset.mem_val, mem_cells] at hx
    simp [restrict, hx, ← to_fun_eq_coe]
  simp only [content, hmap, Multiset.mem_sub, Multiset.count_map, gt_iff_lt]
  refine Multiset.card_lt_card ?_
  rw [Multiset.lt_iff_cons_le]
  use (i, j)
  rw [Multiset.le_iff_subset]
  · intro x
    simp only [Multiset.mem_cons, Multiset.mem_filter, Finset.mem_val, mem_cells]
    intro hx
    rcases hx with hx | hx
    · simp [hx, h.1]
    · constructor
      · exact hγ hx.1
      · exact hx.2
  · refine Multiset.nodup_cons.mpr ?_
    constructor
    · simp [h.2]
    · exact Multiset.Nodup.filter _ γ'.cells.nodup

end SemistandardYoungTableau
