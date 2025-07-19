import Mathlib
import KostkaNumbers.Util
import KostkaNumbers.Diagrams
import KostkaNumbers.Content
import KostkaNumbers.EraseAtEdge

open SemistandardYoungTableau
open YoungDiagram

/-
Convention: Use capital letters for normal multisets and Greek letters for partition-like multisets
  e.g. γ : YoungDiagram, μ = M.counts
-/

namespace SemistandardYoungTableau

def coe {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ = γ') :
  SemistandardYoungTableau γ' := ⟨T.entry, by
  rw [to_fun_eq_coe, ← h]; exact T.row_weak
  , by
  rw [to_fun_eq_coe, ← h]; exact T.col_strict
  , by
  rw [to_fun_eq_coe, ← h]; exact T.zeros
  ⟩

@[simp] lemma coe_eval {γ γ' : YoungDiagram} {T : SemistandardYoungTableau γ} {h : γ = γ'}
    {i j : ℕ} : (T.coe h) i j = T i j := by
  simp only [coe, DFunLike.coe]

@[simp] lemma coe_content {γ γ' : YoungDiagram} {T : SemistandardYoungTableau γ} {h : γ = γ'} :
    (T.coe h).content = T.content := by
  simp [content, h]

end SemistandardYoungTableau


namespace Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {T : SemistandardYoungTableau γ}

noncomputable def kostkaNumber (γ : YoungDiagram) (μ : Multiset ℕ) :=
  Nat.card {T : SemistandardYoungTableau γ | T.content = μ.fromCounts}



theorem kostka_eq_zero {γ : YoungDiagram} {μ : Multiset ℕ}
    (h : ∀ T : SemistandardYoungTableau γ, T.content ≠ μ.fromCounts) : kostkaNumber γ μ = 0 := by
  rw [kostkaNumber, Nat.card_eq_zero]
  left; exact Subtype.isEmpty_of_false h




lemma kostka_bot_bot : kostkaNumber ⊥ ⊥ = 1 := by
  rw [kostkaNumber, Nat.card_eq_one_iff_exists]
  use ⟨bot_ssyt, by rw [Set.mem_setOf, Multiset.fromCounts_bot]; exact bot_content⟩
  intro ⟨T, hT⟩
  simp only [Subtype.mk.injEq]
  exact ssyt_bot T

theorem kostka_ne_card (γ : YoungDiagram) (μ : Multiset ℕ) (h : γ.card ≠ μ.sum) :
    kostkaNumber γ μ = 0 := by
  apply kostka_eq_zero
  intro T
  contrapose! h
  symm; rw [← Multiset.fromCounts_card, ← h]
  exact content_card_eq_card



theorem kostka_horizontal (μ : Multiset ℕ) :
    kostkaNumber (horizontalDiagram μ.sum) μ = 1 := by
  unfold kostkaNumber
  rw [Nat.card_eq_one_iff_exists, ← Multiset.fromCounts_card]
  use ⟨horizontal_ofMultiset μ.fromCounts, by
    rw [Set.mem_setOf, content_horizontal_ofMultiset]⟩
  intro ⟨T, hT⟩
  rw [Subtype.mk.injEq]; rw [Set.mem_setOf] at hT
  ext i j; simp only [DFunLike.coe]
  rw [eq_horizontal_ofMultiset_content' T]
  congr



theorem kostka_horizontal' (n : ℕ) (μ : Multiset ℕ) :
    kostkaNumber (horizontalDiagram n) μ = 1 ↔ μ.sum = n := by
  constructor; swap
  · intro h
    rw [← h]
    exact kostka_horizontal μ
  contrapose!
  intro h; symm at h
  rw [kostka_ne_card]
  · exact zero_ne_one
  simp [h]

theorem top_left_of_content_fromCounts (hγ : γ ≠ ⊥)
    (h : T.content = μ.fromCounts) : T 0 0 = 0 := by
  have h0 : 0 ∈ μ.fromCounts := by
    refine Multiset.mem_fromCounts μ 0 ?_
    rw [Nat.pos_iff_ne_zero]
    contrapose! hγ
    rw [Multiset.card_eq_zero] at hγ
    rw [Multiset.fromCounts_eq_remove_zero_fromCounts, hγ, Multiset.fromCounts_zero] at h
    unfold content at h
    rw [Multiset.map_eq_zero, Finset.val_eq_zero] at h
    ext x; rw [h, cells_bot]
  rw [← h] at h0
  simp [content] at h0
  obtain ⟨i, j, hij, hT⟩ := h0
  refine antisymm ?_ (Nat.zero_le (T 0 0))
  nth_rw 3 [← hT]
  have hi : T 0 0 ≤ T i 0 := by
    exact T.col_weak (Nat.zero_le i) <| γ.up_left_mem (by rfl) (Nat.zero_le j) hij
  refine le_trans hi ?_
  exact T.row_weak_of_le (Nat.zero_le j) hij

theorem kostka_hook (μ : Multiset ℕ) (hμ : μ.sum ≥ 2) :
    kostkaNumber (hookDiagram μ.sum) μ = (μ.remove 0).card - 1 := by
  unfold kostkaNumber
  rw [← Multiset.remove_fromCounts_remove_counts_card, ← Nat.card_eq_finsetCard]
  simp only [Multiset.mem_toFinset, Set.coe_setOf]
  let f : {T : SemistandardYoungTableau (hookDiagram μ.sum) | T.content = μ.fromCounts} →
    {x // x ∈ ((μ.remove 0).fromCounts.remove 0)}
     :=
    fun ⟨T, hT⟩ ↦ ⟨T 1 0, by
    rw [Set.mem_setOf] at hT
    refine Multiset.mem_remove_of_mem_ne ?_ ?_
    · rw [← Multiset.fromCounts_eq_remove_zero_fromCounts, ← hT]
      refine mem_content_of_mem_cells ?_
      rw [mem_hookDiagram]
      simp
      exact hμ
    · nth_rw 1 [← top_left_of_content_fromCounts ?_ hT]
      refine ne_of_lt ?_
      refine T.3 zero_lt_one ?_
      rw [mem_hookDiagram μ.sum hμ]
      simp

      apply_fun YoungDiagram.card
      rw [hookDiagram_card, bot_card]
      omega
    ⟩
  refine Nat.card_eq_of_bijective f ?_

  constructor
  · intro ⟨T, hT⟩ ⟨T', hT'⟩ hf
    simp [f] at hf
    ext i j; simp only
    by_cases h10 : i = 1 ∧ j = 0
    · rw [h10.1, h10.2]
      exact hf
    · let R := horizontal_ofMultiset (μ.fromCounts.erase (T 1 0))
      have h2 : (1 + 1, 0) ∉ hookDiagram μ.sum := by simp [mem_hookDiagram, hμ]
      have h11 : (1, 0 + 1) ∉ hookDiagram μ.sum := by simp [mem_hookDiagram, hμ]
      have h10m : (1, 0) ∈ hookDiagram μ.sum := by simp [mem_hookDiagram, hμ]
      let S := T.eraseAtEdge 1 0 h2 h11
      let S' := T'.eraseAtEdge 1 0 h2 h11

      rw [← erase_eval h2 h11 h10, ← erase_eval h2 h11 h10]
      simp only [DFunLike.coe]
      rw [eq_horizontal_ofMultiset_content S (hook_erase h2 h11 hμ),
          eq_horizontal_ofMultiset_content S' (hook_erase h2 h11 hμ),
          erase_content h2 h11 h10m, erase_content h2 h11 h10m,
          hT, hT', hf]
  · intro ⟨x, hx⟩
    have hx' : x ∈ μ.fromCounts := by
      rw [Multiset.fromCounts_eq_remove_zero_fromCounts]
      exact Multiset.mem_of_mem_remove 0 x hx
    have hx0 : 0 ≠ x := by
      contrapose! hx; rw [hx]
      exact Multiset.notMem_of_remove _ x
    have h1 : 0 ∈ (μ.remove 0).fromCounts.erase x ∧ 0 < x := by
      constructor
      · rw [Multiset.mem_erase_of_ne hx0, ← Multiset.fromCounts_eq_remove_zero_fromCounts]
        refine Multiset.mem_fromCounts μ 0 ?_
        rw [Multiset.remove_zero_sum μ] at hμ
        rw [Nat.pos_iff_ne_zero]
        contrapose! hμ
        rw [Multiset.card_eq_zero] at hμ
        rw [hμ, Multiset.sum_zero]
        exact zero_lt_two
      · symm at hx0; exact Nat.pos_of_ne_zero hx0
    have hhd : hookDiagram (((μ.remove 0).fromCounts.erase x).card + 1) = hookDiagram μ.sum := by
      congr
      rw [← Multiset.fromCounts_eq_remove_zero_fromCounts, Multiset.card_erase_of_mem hx']
      simp; omega
    use ⟨coe (hook_ofMultiset ((μ.remove 0).fromCounts.erase x) x (by use 0)) hhd, by
      rw [coe_content, content_hook_ofMultiset, ← Multiset.fromCounts_eq_remove_zero_fromCounts]
      · exact Multiset.cons_erase hx'
      rw [gt_iff_lt, Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero,
        Multiset.eq_zero_iff_forall_notMem]
      push_neg
      use 0; exact h1.1
      ⟩
    simp [f]

theorem kostka_hook_replicate (n : ℕ) (hn : n ≥ 2) :
    kostkaNumber (hookDiagram n) (Multiset.replicate n 1) = n - 1 := by
  let h := kostka_hook (Multiset.replicate n 1) ?_
  swap
  · rw [Multiset.sum_replicate, smul_eq_mul, mul_one]; exact hn

  rw [Multiset.sum_replicate, smul_eq_mul, mul_one,
    Multiset.remove_of_notMem, Multiset.card_replicate] at h
  · exact h
  simp [Multiset.mem_replicate]



lemma entry_ge_col {i j : ℕ} (h : (i, j) ∈ γ) : T i j ≥ i := by
  induction' i with i ih
  · simp
  calc T (i + 1) j
    _ > T i j := T.col_strict (lt_add_one i) h
    _ ≥ i := by refine ih ?_; exact γ.up_left_mem (le_of_lt (lt_add_one i)) (by rfl) h


lemma eq_highestWeight_iff :
    T = highestWeight γ ↔ T.content = (Multiset.ofList γ.rowLens).fromCounts := by
  constructor
  · intro h
    rw [h]
    exact highestWeight_content

  intro h
  ext i j
  rw [highestWeight_apply]
  by_cases hi : i < γ.colLen 0
  · apply downwardStrongInduction (fun x ↦ T x.1 x.2 = if (x.1, x.2) ∈ γ then x.1 else 0)
        (i, j) (γ.colLen 0) ?_ ?_
    · simp only
      exact hi
    · intro z hz ih
      by_cases hzγ : (z.1, z.2) ∈ γ
      · simp only [gt_iff_lt, Prod.forall] at ih
        simp [hzγ]
        refine antisymm (entry_ge_col hzγ) ?_
        by_contra! hT
        have h2 : T.content = (Multiset.ofList γ.rowLens).fromCounts := h
        apply_fun Multiset.count (T z.1 z.2) at h
        simp [content, Multiset.count_map] at h
        rw [Multiset.count_fromCounts] at h
        · simp [List.coe_ofList_sorted γ.rowLens_sorted] at h
          suffices (Multiset.filter (fun a ↦ T z.1 z.2 = T a.1 a.2)
              γ.cells.val).card ≥ (γ.row (T z.1 z.2) ∪ {(z.1, z.2)}).card by
            rw [h, Finset.card_union_eq_card_add_card.mpr ?_] at this
            · rw [Prod.mk.eta, Finset.card_singleton, ← γ.rowLen_eq_card] at this
              omega
            · rw [Prod.mk.eta, Finset.disjoint_singleton_right, mem_row_iff, not_and_or]
              right; exact ne_of_lt hT
          refine le_trans ?_ (Multiset.toFinset_card_le _)
          · refine Finset.card_le_card ?_
            intro w hw
            simp
            simp at hw
            rcases hw with hrow | hwz
            · rw [mem_row_iff] at hrow;
              constructor
              · exact hrow.1
              · symm
                rw [hrow.2]
                specialize ih (T z.1 z.2) w.2 hT ?_
                · rw [← hrow.2, ← mem_iff_lt_colLen]
                  exact γ.up_left_mem (by rfl) (Nat.zero_le w.2) hrow.1
                simp [hrow.1, ← hrow.2] at ih
                simp [← hrow.2, ih]
            · rw [hwz]; constructor
              · contrapose! hT
                rw [T.zeros hT]
                exact Nat.zero_le z.1
              · rfl
        · exact entry_lt_rowLens_card h2 hzγ
        · let h0rl := γ.pos_of_mem_rowLens 0
          simp at h0rl
          simp [h0rl]
      · simp [hzγ, zeros]
  · rw [← mem_iff_lt_colLen] at hi
    have hij : (i, j) ∉ γ := by
      contrapose! hi
      exact γ.up_left_mem (by rfl) (Nat.zero_le j) hi
    simp [hij, zeros]

theorem kostka_self : kostkaNumber γ (Multiset.ofList γ.rowLens) = 1 := by
  simp [kostkaNumber, ← eq_highestWeight_iff]


end Kostka
