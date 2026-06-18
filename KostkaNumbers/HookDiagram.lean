/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.HorizontalDiagram

open YoungDiagram SemistandardYoungTableau Kostka

lemma card_of_exists {M : Multiset ℕ} {m : ℕ} (h : ∃ x ∈ M, x < m) :
    M.card + 1 ≥ 2 := by
  suffices M.card ≠ 0 by lia
  rw [ne_eq, Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
  push Not
  obtain ⟨x, h⟩ := h
  use x
  exact h.1

def hookDiagram (n : ℕ) := if h0 : n = 0 then (⊥ : YoungDiagram)
  else if h1 : n = 1 then horizontalDiagram 1
  else ofRowLens [n - 1, 1] (List.Pairwise.sortedGE (by grind))

@[simp] lemma mem_hookDiagram (n : ℕ) {x : ℕ × ℕ} (hn : n ≥ 2) : x ∈ hookDiagram n ↔
    (x.1 = 1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ x.2 < n-1) := by
  have h0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have h1 : n ≠ 1 := Ne.symm (Nat.ne_of_lt hn)
  have hx : x = (1, 0) ↔ (x.1 = 1 ∧ x.2 = 0) := by grind
  have ha : (∃ a < n - 1, (0, a) = x) ↔ (x.1 = 0 ∧ x.2 < n - 1) := by grind
  simp [h0, h1, hookDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, hx, ha]


@[simp] lemma hookDiagram_zero : hookDiagram 0 = ⊥ := by simp [hookDiagram]

@[simp] lemma hookDiagram_card (n : ℕ) : (hookDiagram n).card = n := by
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · simp [hookDiagram, h1]
  simp [hookDiagram, YoungDiagram.card, h0, h1, ofRowLens, YoungDiagram.cellsOfRowLens]
  lia

@[simp] lemma hookDiagram_cells {n : ℕ} (h : n > 0) : (hookDiagram (n + 1)).cells =
    (horizontalDiagram n).cells ∪ {(1, 0)} := by
  ext x
  obtain ⟨fst, snd⟩ := x
  simp [mem_cells, mem_hookDiagram (n + 1) (by lia), add_tsub_cancel_right, Or.comm,
    mem_horizontalDiagram, Prod.mk.injEq]

@[simp] lemma hookDiagram_rowLens {n : ℕ} (hn : n ≥ 2) :
    (hookDiagram n).rowLens = [n - 1, 1] := by
  grind [rowLens_ofRowLens_eq_self, hookDiagram]


-- m is the entry in the second row. accompied by a proof that m is greater than
--   the smallest element of M
noncomputable
def hook_ofMultiset (M : Multiset ℕ) (m : ℕ) (h : ∃ x ∈ M, x < m) :
    SemistandardYoungTableau (hookDiagram (M.card+1)) :=
  ⟨fun i j ↦ if i = 1 ∧ j = 0 then m else
  if hj : i = 0 ∧ j < M.card then (M.sort (· ≤ ·))[j]'(by
  simp [hj]) else 0,
  by
    intro i j1 j2 hj
    simp only [ge_iff_le, card_of_exists h, mem_hookDiagram, add_tsub_cancel_right]
    intro hij
    rcases hij with hij|hij
    · lia
    · have hj1 : j1 < M.card := by lia
      simp only [hij, zero_ne_one, false_and, ↓reduceIte, hj1, and_self, ↓reduceDIte, ge_iff_le]
      exact List.Pairwise.rel_get_of_lt (Multiset.pairwise_sort _ _) hj
  ,
  by
    intro i1 i2 j hi
    simp only [ge_iff_le, card_of_exists h, mem_hookDiagram, add_tsub_cancel_right]
    intro hij
    rcases hij with hij | hij
    · have hij2 : i1 = 0 ∧ 0 < M.card := by grind [card_of_exists h]
      simp only [hij2, zero_ne_one, hij, and_true, ↓reduceIte, and_self, ↓reduceDIte, gt_iff_lt]
      obtain ⟨x, hM, hm⟩ := h
      refine lt_of_le_of_lt ?_ hm
      rw [List.getElem_zero_eq_head]
      refine List.Pairwise.rel_head (Multiset.pairwise_sort _ _) ?_
      rwa [Multiset.mem_sort]
    · lia
  ,
  by grind [mem_hookDiagram, card_of_exists h]
  ⟩


@[simp] lemma hook_ofMultiset10 {M : Multiset ℕ} {m : ℕ} {h : ∃ x ∈ M, x < m} :
    (hook_ofMultiset M m h) 1 0 = m := by
  simp [hook_ofMultiset, DFunLike.coe]



@[simp] lemma content_hook_ofMultiset (M : Multiset ℕ) (m : ℕ) (h : ∃ x ∈ M, x < m)
    (hM : M.card > 0) : (hook_ofMultiset M m h).content = m ::ₘ M := by
  simp only [content, gt_iff_lt, hM, hookDiagram_cells, Finset.union_val, Finset.singleton_val,
    DFunLike.coe, hook_ofMultiset, to_fun_eq_coe]
  rw [← Multiset.add_eq_union_iff_disjoint.mpr, Multiset.map_add]
  · simp only [Multiset.map_singleton, and_self, ↓reduceIte, Multiset.add_comm,
      Multiset.singleton_add, Multiset.cons_inj_right]
    conv => rhs; rw [← content_horizontal_ofMultiset M]
    unfold content
    rw [Multiset.map_congr rfl]
    intro x hx
    simp only [Finset.mem_val, mem_cells, mem_horizontalDiagram] at hx
    simp [hx, horizontal_ofMultiset, DFunLike.coe]
  · simp


lemma T10_mem_fromCounts_remove {μ : Multiset ℕ} {T : SemistandardYoungTableau (hookDiagram μ.sum)}
    (h : T.content = μ.fromCounts) (hμ : μ.sum ≥ 2) :
    T 1 0 ∈ μ.fromCounts.remove 0 := by
  refine (Multiset.mem_remove_of_mem _ ?_).mpr ?_
  · rw [← h]
    refine mem_content_of_mem ?_
    simp [mem_hookDiagram μ.sum hμ]
  · nth_rw 1 [← top_left_of_content_fromCounts ?_ h]
    · refine ne_of_lt ?_
      refine T.3 zero_lt_one ?_
      simp [mem_hookDiagram μ.sum hμ]
    · apply_fun YoungDiagram.card
      rw [hookDiagram_card, bot_card]
      lia

theorem kostka_hook (μ : Multiset ℕ) (h0 : 0 ∉ μ) (hμ : μ.sum ≥ 2) :
    kostkaNumber (hookDiagram μ.sum) μ = μ.card - 1 := by
  unfold kostkaNumber
  rw [← Multiset.fromCounts_remove_card h0, ← Nat.card_eq_finsetCard]
  simp only [Multiset.mem_toFinset, Set.coe_setOf]
  let f : {T : SemistandardYoungTableau (hookDiagram μ.sum) | T.content = μ.fromCounts} →
    {x // x ∈ (μ.fromCounts.remove 0)}
     :=
    fun ⟨T, hT⟩ ↦ ⟨T 1 0, by
    rw [Set.mem_setOf] at hT
    exact T10_mem_fromCounts_remove hT hμ
    ⟩
  refine Nat.card_eq_of_bijective f ?_
  constructor
  · intro ⟨T, hT⟩ ⟨T', hT'⟩ hf
    simp only [Set.coe_setOf, Subtype.mk.injEq, f] at hf
    rw [Subtype.mk.injEq]
    refine eq_of_missing_row T T' (by rw [hT, hT']) 0 ?_
    intro i hi j
    by_cases hij : (i, j) ∈ hookDiagram μ.sum
    · simp only [mem_hookDiagram μ.sum hμ, hi, false_and, or_false] at hij
      rw [hij.1, hij.2, hf]
    · rw [T.zeros hij, T'.zeros hij]
  · intro ⟨m, hm⟩
    have hhd : hookDiagram ((μ.fromCounts.erase m).card + 1) = hookDiagram μ.sum := by
      congr
      rw [Multiset.card_erase_of_mem (Multiset.mem_of_mem_remove hm), Multiset.fromCounts_card,
        Nat.pred_eq_sub_one]
      lia
    have hm0 : m ≠ 0 := by
      contrapose! hm
      rw [hm]
      exact Multiset.notMem_of_remove μ.fromCounts 0
    have hx0 : ∃ x ∈ μ.fromCounts.erase m, x < m := by
      use 0
      constructor
      · rw [Multiset.mem_erase_of_ne hm0.symm]
        refine Multiset.zero_mem_fromCounts_of_nonempty ?_
        contrapose! hm
        simp [hm]
      · rwa [Nat.pos_iff_ne_zero]
    use ⟨coe (hook_ofMultiset (μ.fromCounts.erase m) m ?_) hhd, by
      rw [coe_content, content_hook_ofMultiset, Multiset.cons_erase]
      · exact Multiset.mem_of_mem_remove hm
      · rw [Multiset.card_erase_of_mem]
        · simp [Nat.lt_of_succ_le hμ]
        · exact Multiset.mem_of_mem_remove hm
      ⟩
    · simp only [Set.coe_setOf, coe_eval, Subtype.mk.injEq, f]
      exact hook_ofMultiset10
    · exact hx0

theorem kostka_hook_replicate (n : ℕ) (hn : n ≥ 2) :
    kostkaNumber (hookDiagram n) (Multiset.replicate n 1) = n - 1 := by
  have h := kostka_hook (Multiset.replicate n 1) (by simp [Multiset.mem_replicate])
  rw [Multiset.sum_replicate, smul_eq_mul, mul_one, Multiset.card_replicate] at h
  exact h hn
