import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.HorizontalDiagram

open YoungDiagram SemistandardYoungTableau Kostka

lemma card_of_exists {M : Multiset ℕ} {m : ℕ} (h : ∃ x ∈ M, x < m) :
    M.card+1 ≥ 2 := by
  suffices M.card ≠ 0 by omega
  rw [ne_eq, Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
  push_neg
  obtain ⟨x, h⟩ := h
  use x; exact h.1

def hookDiagram (n : ℕ) := if h0 : n = 0 then (⊥ : YoungDiagram) else
  if h1 : n = 1 then horizontalDiagram 1 else
  ofRowLens [n-1, 1] (by simp; omega)

@[simp] lemma mem_hookDiagram (n : ℕ) {x : ℕ × ℕ} (hn : n ≥ 2) : x ∈ hookDiagram n ↔
    (x.1 = 1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ x.2 < n-1) := by
  have h0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  have h1 : n ≠ 1 := by exact Ne.symm (Nat.ne_of_lt hn)
  have hx : x = (1, 0) ↔ (x.1 = 1 ∧ x.2 = 0) := by
    constructor; intro hx
    rw [hx]; simp
    intro hx
    ext; simp [hx]; simp [hx]
  have ha : (∃ a < n - 1, (0, a) = x) ↔ (x.1 = 0 ∧ x.2 < n - 1) := by
    constructor; intro ha
    obtain ⟨a, ha, hax⟩ := ha
    simp [← hax, ha]
    intro ha; use x.2
    simp [← ha.1, ha.2]
  rw [Or.comm]
  simp [h0, h1, hookDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, hx, ha]

@[simp] lemma hookDiagram_zero : hookDiagram 0 = ⊥ := by simp [hookDiagram]

@[simp] lemma hookDiagram_card (n : ℕ) : (hookDiagram n).card = n := by
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · simp [hookDiagram, h1]

  simp [hookDiagram, YoungDiagram.card, h0, h1, ofRowLens, YoungDiagram.cellsOfRowLens]
  exact Nat.succ_pred_eq_of_ne_zero h0

@[simp] lemma hookDiagram_cells (n : ℕ) (h : n > 0) : (hookDiagram (n+1)).cells =
    (horizontalDiagram n).cells ∪ {(1, 0)} := by
  ext x
  obtain ⟨fst, snd⟩ := x
  simp only [mem_cells, mem_hookDiagram (n + 1) (by omega), add_tsub_cancel_right, Or.comm,
    Finset.mem_union, mem_horizontalDiagram, Finset.mem_singleton, Prod.mk.injEq]

@[simp] lemma hookDiagram_rowLens {n : ℕ} (hn : n ≥ 2) :
    (hookDiagram n).rowLens = [n-1, 1] := by
  have h0 : n ≠ 0 := by positivity
  have h1 : n ≠ 1 := by omega
  simp only [hookDiagram, h0, ↓reduceDIte, h1]
  rw [rowLens_ofRowLens_eq_self]
  simp; omega


-- m is the entry in the second row. accompied by a proof that m is greater than
--   the smallest element of M
noncomputable
def hook_ofMultiset (M : Multiset ℕ) (m : ℕ) (h : ∃ x ∈ M, x < m) :
    SemistandardYoungTableau (hookDiagram (M.card+1)) :=
  ⟨fun i j ↦ if i = 1 ∧ j = 0 then m else
  if hj : i = 0 ∧ j < M.card then (M.toList.mergeSort (· ≤ ·))[j]'(by
  simp [List.length_mergeSort, hj]) else 0,
  by
  intro i j1 j2 hj
  simp [card_of_exists h]
  intro hij
  rcases hij with hij|hij
  · omega
  · have hj1 : j1 < M.card := by omega
    simp [hij, hj1]
    exact List.Sorted.rel_get_of_lt (List.sorted_mergeSort' _ _) hj
  ,
  by
  intro i1 i2 j hi
  simp [card_of_exists h]
  intro hij
  rcases hij with hij|hij
  · have hij2 : i1 = 0 ∧ 0 < M.card := by
      let hmc := card_of_exists h
      omega
    simp [hij2, hij]
    obtain ⟨x, hM, hm⟩ := h
    refine lt_of_le_of_lt ?_ hm
    rw [List.getElem_zero_eq_head]
    refine List.Pairwise.rel_head (List.sorted_mergeSort' (· ≤ ·) _) ?_
    rw [List.mem_mergeSort, Multiset.mem_toList]
    exact hM
  · omega
  ,
  by
  intro i j
  simp only [ge_iff_le, card_of_exists h, mem_hookDiagram, add_tsub_cancel_right, not_or]
  intro ⟨hij0, hij1⟩
  simp [hij0, hij1]
  ⟩


@[simp] lemma hook_ofMultiset10 {M : Multiset ℕ} {m : ℕ} {h : ∃ x ∈ M, x < m} :
    (hook_ofMultiset M m h) 1 0 = m := by
  simp [hook_ofMultiset, DFunLike.coe]



@[simp] lemma content_hook_ofMultiset (M : Multiset ℕ) (m : ℕ) (h : ∃ x ∈ M, x < m) :
    M.card > 0 → (hook_ofMultiset M m h).content = m ::ₘ M := by
  intro hM
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
    refine Multiset.mem_remove_of_mem_ne ?_ ?_
    · rw [← hT]
      refine mem_content_of_mem_cells ?_
      simp [mem_hookDiagram μ.sum hμ]
    · nth_rw 1 [← top_left_of_content_fromCounts ?_ hT]
      refine ne_of_lt ?_
      refine T.3 zero_lt_one ?_
      simp [mem_hookDiagram μ.sum hμ]

      apply_fun YoungDiagram.card
      rw [hookDiagram_card, bot_card]
      omega
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
      rw [Multiset.card_erase_of_mem, Multiset.fromCounts_card, Nat.pred_eq_sub_one]
      omega
      exact Multiset.mem_of_mem_remove _ _ hm
    have hm0 : m ≠ 0 := by
        contrapose! hm
        rw [hm]
        exact Multiset.notMem_of_remove μ.fromCounts 0
    have hx0 : ∃ x ∈ μ.fromCounts.erase m, x < m := by
      use 0
      constructor
      · symm at hm0
        rw [Multiset.mem_erase_of_ne hm0]
        refine Multiset.zero_mem_fromCounts_of_nonempty ?_
        contrapose! hm
        simp [hm]
      · rw [Nat.pos_iff_ne_zero]
        exact hm0
    use ⟨coe (hook_ofMultiset (μ.fromCounts.erase m) m ?_) hhd, by
      rw [coe_content, content_hook_ofMultiset, Multiset.cons_erase]
      · exact Multiset.mem_of_mem_remove _ _ hm
      · rw [Multiset.card_erase_of_mem]
        · simp; omega
        · exact Multiset.mem_of_mem_remove _ _ hm
      · exact hx0
      ⟩
    · simp only [Set.coe_setOf, coe_eval, Subtype.mk.injEq, f]
      exact hook_ofMultiset10

theorem kostka_hook_replicate (n : ℕ) (hn : n ≥ 2) :
    kostkaNumber (hookDiagram n) (Multiset.replicate n 1) = n - 1 := by
  let h := kostka_hook (Multiset.replicate n 1) ?_
  swap
  · simp [Multiset.mem_replicate]

  rw [Multiset.sum_replicate, smul_eq_mul, mul_one, Multiset.card_replicate] at h
  exact h hn
