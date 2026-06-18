/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.ProbHookLength.HookLengthFormula
import KostkaNumbers.FactorialLemma
import KostkaNumbers.InequalitySpecial


open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n p : ℕ}

theorem kostka_replicate_two_rows (h2 : γ.rowLens = [n - p, p])
    (hn : n ≥ 5) (hp0 : p ≠ 0) (hγ : γ.card = n) :
    ((Nat.factorial p) * (Nat.factorial (n - p + 1))) *
    kostkaNumber γ (Multiset.replicate n 1) = (Nat.factorial n) * (n - 2 * p + 1) := by
  have hpn : p ≤ n - p := by
    have hrls := γ.rowLens_sorted
    rwa [h2, List.sortedGE_iff_pairwise, List.pairwise_pair] at hrls
  have hk0 : kostkaNumber γ (Multiset.replicate n 1) ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, kostka_pos_iff_dominates]
    · rw [h2, Multiset.sort_eq_replicate_iff.mpr (by rfl)]
      refine dominates_replicate_one ?_ ?_
      all_goals simp; lia
    · simp [hγ, Multiset.sum_replicate]
    · simp [Multiset.mem_replicate]
  suffices ∏ x ∈ γ.cells, γ.hookLength x.1 x.2 =
      p.factorial * (n - 2 * p).factorial * (n - p + 1).descFactorial p by
    rw [← hookLength_formula' γ hγ, this]
    nth_rw 2 [mul_assoc]
    nth_rw 7 [mul_comm]
    rw [← mul_assoc]
    simp only [mul_eq_mul_right_iff, hk0, or_false]
    simp only [mul_assoc, mul_eq_mul_left_iff, Nat.factorial_ne_zero, or_false]
    nth_rw 3 [mul_comm]
    rw [← mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← Nat.factorial_succ, show n - 2 * p + 1 = (n - p + 1) - p by lia,
      Nat.factorial_mul_descFactorial (by lia)]
  rw [← Finset.prod_filter_mul_prod_filter_not _ (fun x : ℕ × ℕ ↦ x.1 = 1)]
  nth_rw 2 [← Finset.prod_filter_not_mul_prod_filter _ (fun x : ℕ × ℕ ↦ x.2 < p)]
  simp_rw [Finset.filter_filter]
  have hr0 : γ.rowLen 0 = n - p := by
    rw [← get_rowLens]
    · simp [h2]
    · simp [h2]
  have hr1 : γ.rowLen 1 = p := by
    rw [← get_rowLens]
    · simp [h2]
    · simp [h2]
  have hr2 : γ.rowLen 2 = 0 := by
    refine rowLen_eq_zero ?_
    simp [← length_rowLens, h2]
  have hi0 : ∀ i j : ℕ, (i, j) ∈ γ → i ≠ 1 → i = 0 := by
    intro i j hij hi
    rw [mem_iff_lt_colLen] at hij
    apply lt_of_le_of_lt' (γ.colLen_anti 0 j (Nat.zero_le j)) at hij
    simp only [← length_rowLens, h2, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd] at hij
    lia
  have hhl1 : ∏ x ∈ γ.cells with x.1 = 1, γ.hookLength x.1 x.2 = p.factorial := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    let e : (i : ℕ) → (hi : i ∈ Finset.range p) → ℕ × ℕ := fun i hi ↦ (1, (p-1)-i)
    rw [Finset.prod_bij e]
    · simp only [Finset.mem_range, Finset.mem_filter, mem_cells, and_true, e]
      intro i _
      rw [mem_iff_lt_rowLen, hr1]
      lia
    · simp [e]
      lia
    · simp only [Finset.mem_filter, mem_cells, Finset.mem_range, exists_prop, and_imp, Prod.forall,
        Prod.mk.injEq, e]
      intro i j hij hi
      use p - 1 - j
      rw [hi, mem_iff_lt_rowLen, hr1] at hij
      lia
    · simp only [Finset.mem_range, hookLength_def, hr1, Nat.reduceAdd, Nat.add_right_cancel_iff, e]
      intro i hi
      suffices γ.colLen (p - 1 - i) = 2 by lia
      have hcle : γ.colLen (p - 1 - i) ≤ 2 := by
        refine le_trans (γ.colLen_anti 0 _ (Nat.zero_le _)) ?_
        simp [← length_rowLens, h2]
      suffices 1 < γ.colLen (p - 1 - i) by lia
      rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr1]
      lia
  have hhl2 : ∏ x ∈ γ.cells with ¬x.1 = 1 ∧ ¬x.2 < p,
      γ.hookLength x.1 x.2 = (n - 2 * p).factorial := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    let e : (i : ℕ) → (hi : i ∈ Finset.range (n - 2 * p)) → ℕ × ℕ :=
      fun i _ ↦ (0, n - p - 1 - i)
    rw [Finset.prod_bij e]
    · simp only [Finset.mem_range, not_lt, Finset.mem_filter, mem_cells, zero_ne_one,
        not_false_eq_true, true_and, e]
      intro i hi
      constructor
      · rw [mem_iff_lt_rowLen, hr0]
        lia
      · lia
    · simp [e]
      lia
    · simp only [not_lt, Finset.mem_filter, mem_cells, Finset.mem_range, exists_prop, and_imp,
        Prod.forall, Prod.mk.injEq, e]
      intro i j hij hi hj
      use n - p - 1 - j
      specialize hi0 i j hij hi
      rw [hi0, mem_iff_lt_rowLen, hr0] at hij
      lia
    · simp only [Finset.mem_range, hookLength_def, hr0, zero_add, Nat.add_right_cancel_iff, e]
      intro i hi
      suffices γ.colLen (n - p - 1 - i) = 1 by lia
      suffices ¬ 1 < γ.colLen (n - p - 1 - i) ∧ 0 < γ.colLen (n - p - 1 - i) by lia
      constructor
      · rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr1]
        lia
      · rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr0]
        lia
  have hhl3 : ∏ x ∈ γ.cells with ¬x.1 = 1 ∧ x.2 < p,
      γ.hookLength x.1 x.2 = (n - p + 1).descFactorial p := by
    rw [Nat.descFactorial_eq_prod_range]
    let e : (i : ℕ) → (hi : i ∈ Finset.range p) → ℕ × ℕ := fun i _ ↦ (0, i)
    rw [Finset.prod_bij e]
    · simp [mem_iff_lt_rowLen, hr0, e]
      lia
    · simp [e]
    · simp only [Finset.mem_filter, mem_cells, Finset.mem_range, exists_prop, and_imp, Prod.forall,
        Prod.mk.injEq, exists_eq_right_right, e]
      intro i j hij hi
      specialize hi0 i j hij hi
      simp [hi0]
    · simp only [Finset.mem_range, hookLength_def, hr0, zero_add, e]
      intro i hi
      suffices γ.colLen i = 2 by lia
      suffices ¬ 2 < γ.colLen i ∧ 1 < γ.colLen i by lia
      simp_rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr1, hr2]
      lia
  rw [hhl1, hhl2, hhl3]
  ring

lemma mem_list_sym {α : Type*} [DecidableEq α] {n : ℕ} {L : List α} {xs : Sym α n}
    (h : xs.val.dedup ≤ Multiset.ofList L) : xs ∈ L.sym n := by
  unfold List.sym
  by_cases hn : n = 0
  · subst hn
    simp [Sym.eq_nil_of_card_zero xs]
  by_cases hL : L = []
  · subst hL
    simp only [Sym.val_eq_coe, Multiset.coe_nil, nonpos_iff_eq_zero, Multiset.dedup_eq_zero] at h
    rw [← Multiset.card_eq_zero, Sym.card_coe] at h
    contradiction
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨x, L', hL⟩ := List.exists_cons_of_ne_nil hL
  subst hm hL
  simp only [Nat.succ_eq_add_one, List.mem_append, List.mem_map]
  by_cases hx : x ∈ xs
  · left
    obtain ⟨ys, hys⟩ := Sym.exists_cons_of_mem hx
    use ys
    constructor
    · refine mem_list_sym ?_
      rw [Multiset.le_iff_count]
      intro a
      simp only [Sym.val_eq_coe, Multiset.count_dedup, Sym.mem_coe, Multiset.coe_count]
      split_ifs with ha
      · rw [List.one_le_count_iff]
        have ha' : a ∈ xs := by
          rw [hys]
          simp [ha]
        rw [Multiset.le_iff_count] at h
        specialize h a
        simpa [ha'] using h
      · exact Nat.zero_le _
    · exact hys.symm
  · right
    refine mem_list_sym ?_
    rw [Multiset.le_iff_count]
    intro a
    simp only [Nat.succ_eq_add_one, Sym.val_eq_coe, Multiset.count_dedup,
      Sym.mem_coe, Multiset.coe_count]
    split_ifs with ha
    · have hax : a ≠ x := by
        contrapose! hx
        exact hx ▸ ha
      rw [List.one_le_count_iff]
      rw [Multiset.le_iff_count] at h
      specialize h a
      simpa [ha, hax] using h
    · exact Nat.zero_le _
  termination_by n + L.length

private lemma lt_sub_sort_length {content row2 : Multiset ℕ} {i : ℕ} (hrc : row2 ≤ content)
    (hr0 : γ.rowLen 0 = content.card - row2.card) (hr1 : γ.rowLen 1 = row2.card)
    (hi : i < row2.card) : i < ((content - row2).sort (· ≤ ·)).length := by
  simp [Multiset.card_sub hrc, ← hr0]
  grind [γ.rowLen_anti 0 1 zero_le_one]

noncomputable
def twoRowTableau {γ : YoungDiagram} {content row2 : Multiset ℕ}
  (hr0 : γ.rowLen 0 = content.card - row2.card)
  (hr1 : γ.rowLen 1 = row2.card) (hc0 : γ.colLen 0 = 2)
  (hrc : row2 ≤ content)
  (h : ∀ i : ℕ, (hi : i < row2.card) → (∀ r ∈ row2, r >
    ((content - row2).sort (· ≤ ·))[i]'(lt_sub_sort_length hrc hr0 hr1 hi)))
  : SemistandardYoungTableau γ :=
  ⟨fun i j ↦ if h0 : i = 0 ∧ j < ((content - row2).sort (· ≤ ·)).length then
  ((content - row2).sort (· ≤ ·))[j]'(h0.2) else
  if h1 : i = 1 ∧ j < (row2.sort (· ≤ ·)).length then
  (row2.sort (· ≤ ·))[j]'(h1.2) else 0,
  by
  intro i j1 j2 hj hij
  have hij' := γ.up_left_mem (by rfl) (le_of_lt hj) hij
  by_cases h0 : i = 0
  · have hj' : ∀ j : ℕ, (i, j) ∈ γ → j < content.card - row2.card := by
      intro j hij
      rwa [h0, mem_iff_lt_rowLen, hr0] at hij
    simp only [h0, Multiset.length_sort, Multiset.card_sub hrc, hj' j1 hij', and_self, ↓reduceDIte,
      hj' j2 hij, ge_iff_le]
    exact List.pairwise_iff_getElem.mp (Multiset.pairwise_sort _ _) j1 j2 _ _ hj
  · have hi0 : i = 1 := by
      rw [mem_iff_lt_colLen] at hij
      apply lt_of_le_of_lt' (γ.colLen_anti 0 j2 (Nat.zero_le j2)) at hij
      rw [hc0] at hij
      lia
    have hj' : ∀ j : ℕ, (i, j) ∈ γ → j < row2.card := by
      intro j hij
      rwa [hi0, mem_iff_lt_rowLen, hr1] at hij
    simp only [hi0, one_ne_zero, Multiset.length_sort, false_and, ↓reduceDIte, hj' j1 hij',
      and_self, hj' j2 hij, ge_iff_le]
    exact List.pairwise_iff_getElem.mp (Multiset.pairwise_sort _ _) _ _ _ _ hj
  ,
  by
  intro i1 i2 j hi hij
  have hij' := γ.up_left_mem (le_of_lt hi) (by rfl) hij
  have hi2 : i2 = 1 := by
    rw [mem_iff_lt_colLen] at hij
    apply lt_of_le_of_lt' (γ.colLen_anti 0 j (Nat.zero_le j)) at hij
    rw [hc0] at hij
    lia
  have hi1 : i1 = 0 := by lia
  have hjn : j < content.card - row2.card := by rwa [hi1, mem_iff_lt_rowLen, hr0] at hij'
  have hjp : j < row2.card := by rwa [hi2, mem_iff_lt_rowLen, hr1] at hij
  simp only [hi1, Multiset.length_sort, Multiset.card_sub hrc, hjn, and_self, ↓reduceDIte, hi2,
    one_ne_zero, and_true, hjp, gt_iff_lt]
  refine h j hjp _ ?_
  have hrll : (row2.sort (· ≤ ·))[j]'(by simp [hjp]) ∈ row2.sort (· ≤ ·) := List.getElem_mem _
  rwa [Multiset.mem_sort] at hrll
  ,
  by
  intro i j hij
  simp [Multiset.length_sort, Multiset.card_sub hrc]
  grind [mem_iff_lt_rowLen]
  ⟩

@[simp]
theorem twoRow_content {γ : YoungDiagram} {content row2 : Multiset ℕ}
    (hr0 : γ.rowLen 0 = content.card - row2.card)
    (hr1 : γ.rowLen 1 = row2.card) (hc0 : γ.colLen 0 = 2)
    (hrc : row2 ≤ content)
    (h : ∀ i : ℕ, (hi : i < row2.card) → (∀ r ∈ row2, r >
      ((content - row2).sort (· ≤ ·))[i]'(lt_sub_sort_length hrc hr0 hr1 hi))) :
    (twoRowTableau hr0 hr1 hc0 hrc h).content = content := by
  have hγ : γ.cells = γ.row 0 ∪ γ.row 1 := by
    rw [cells_eq_biUnion_row, γ.length_rowLens, hc0]
    ext x
    simp
  simp only [SemistandardYoungTableau.content, hγ, Finset.union_val]
  rw [← Multiset.add_eq_union_iff_disjoint.mpr, Multiset.map_add, ← map_row, ← map_row]
  · simp only [DFunLike.coe, twoRowTableau, Multiset.length_sort, Multiset.card_sub hrc,
    to_fun_eq_coe, true_and, zero_ne_one, false_and, ↓reduceDIte, Multiset.map_coe, one_ne_zero,
    Multiset.coe_add]
    rw [hr0, hr1]
    simp only [Fin.is_lt, ↓reduceDIte]
    have hms : List.map (fun x ↦ ((content - row2).sort (· ≤ ·))[x.1]'
        (by simp [x.2, Multiset.card_sub hrc])) (List.finRange (content.card - row2.card)) =
        ((content - row2).sort (· ≤ ·)) := by
      refine List.ext_getElem ?_ ?_
      all_goals simp [Multiset.card_sub hrc]
    rw [hms]
    have hpsub : row2.card = (row2.sort (· ≤ ·)).length := by simp
    rw! [hpsub]
    simp_rw [List.map_getElem_finRange, ← Multiset.coe_add, Multiset.sort_eq,
      tsub_add_cancel_of_le hrc]
  · rw [Finset.disjoint_val]
    exact disjoint_row zero_ne_one

theorem map_twoRow_eq_row2_sub_one {γ : YoungDiagram} {content row2 : Multiset ℕ}
    {hr0 : γ.rowLen 0 = content.card - row2.card}
    {hr1 : γ.rowLen 1 = row2.card} {hc0 : γ.colLen 0 = 2}
    {hrc : row2 ≤ content}
    {h : ∀ i : ℕ, (hi : i < row2.card) → (∀ r ∈ row2, r >
      ((content - row2).sort (· ≤ ·))[i]'(lt_sub_sort_length hrc hr0 hr1 hi))} :
    Multiset.map (fun x ↦ (twoRowTableau hr0 hr1 hc0 hrc h) x.1 x.2 - 1)
    (Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val) =
    Multiset.map (· - 1) row2 := by
  rw [show Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val = (γ.row 1).val by rfl,
    ← map_row (fun i j ↦ (twoRowTableau hr0 hr1 hc0 hrc h) i j - 1), Multiset.map_coe]
  conv => rhs; rw [← Multiset.sort_eq row2 (· ≤ ·), Multiset.map_coe]
  congr 1
  refine List.ext_get ?_ ?_
  · simp [hr1]
  · simp only [DFunLike.coe, twoRowTableau, Multiset.length_sort, to_fun_eq_coe, one_ne_zero,
      false_and, ↓reduceDIte, true_and, List.length_map, List.length_finRange, ↓dreduceDIte,
      List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    intro i h₁ h₂
    simp [h₂]

lemma sorted_le_of_exists_multiset (L : List ℕ) (hL : L.Pairwise (· ≤ ·))
    (i : ℕ) (hi : i < L.length) (n : ℕ)
    (h : ∃ S : Multiset ℕ, S ≤ Multiset.ofList L ∧ S.card ≥ i + 1 ∧ ∀ s ∈ S, s ≤ n) :
    L[i]'hi ≤ n := by
  by_cases hi0 : i = 0
  · subst hi0
    obtain ⟨S, hS, hcard, hn⟩ := h
    apply Multiset.card_pos_iff_exists_mem.mp at hcard
    obtain ⟨a, ha⟩ := hcard
    specialize hn a ha
    refine le_trans ?_ hn
    apply Multiset.mem_of_le hS at ha
    rw [Multiset.mem_coe] at ha
    obtain ⟨i, ⟨hi, hia⟩⟩ := List.getElem_of_mem ha
    rw [← hia]
    by_cases! hi0' : i = 0
    · subst hi0'
      rfl
    exact List.pairwise_iff_getElem.mp hL _ _ _ _ (Nat.pos_of_ne_zero hi0')
  · obtain ⟨S, hS, hcard, hn⟩ := h
    have hlt : (L.tail)[i-1]'(by rw [List.length_tail]; lia) = L[i] := by
      simp_rw [List.getElem_tail, show i - 1 + 1 = i by lia]
    rw [← hlt]
    refine sorted_le_of_exists_multiset L.tail (List.Pairwise.tail hL) (i - 1) _ n ?_
    use (S.erase L[0])
    constructor
    · rw [Multiset.le_iff_count]
      intro a
      apply Multiset.count_le_of_le a at hS
      by_cases ha : a = L[0]
      · rw [← ha, Multiset.count_erase_self, Multiset.coe_count]
        rw [Multiset.coe_count] at hS
        have hct : List.count a L - 1 ≤ List.count a L.tail := List.le_count_tail
        lia
      · rw [Multiset.count_erase_of_ne ha, Multiset.coe_count, List.count_tail]
        rw [Multiset.coe_count] at hS
        suffices ¬ L.head? == some a by simpa [this]
        simp only [List.head?, beq_iff_eq]
        suffices L = L[0] :: L.tail by
          rw [this]
          simp only [Option.some.injEq, ne_eq]
          push Not at ha
          exact ha.symm
        have hL0 : L ≠ [] := by
          rw [ne_eq, List.eq_nil_iff_length_eq_zero]
          lia
        exact (List.head_eq_getElem_zero hL0) ▸ (List.cons_head_tail hL0).symm
    constructor
    · rw [Multiset.card_erase_eq_ite, Nat.pred_eq_sub_one]
      grind
    · intro s hs
      exact hn s <| Multiset.mem_of_mem_erase hs

private lemma eq_of_map_sub_one_filter_eq {γ : YoungDiagram} {μ : Multiset ℕ}
    (hc : γ.colLen 0 = 2)
    (T₁ : SemistandardYoungTableau γ) (hT₁ : T₁ ∈ SemistandardYoungTableauWithContent γ μ)
    (T₂ : SemistandardYoungTableau γ) (hT₂ : T₂ ∈ SemistandardYoungTableauWithContent γ μ)
    (h : Multiset.map (fun x ↦ T₁ x.1 x.2 - 1) (Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val) =
    Multiset.map (fun x ↦ T₂ x.1 x.2 - 1) (Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val)) :
    T₁ = T₂ := by
  refine eq_of_missing_row T₁ T₂ ?_ 0 ?_
  · rw [hT₁, hT₂]
  · intro i hi j
    by_cases hij : (i, j) ∈ γ
    · refine eq_entry_of_map_row T₁ T₂ i j ?_
      have hi0 : ∀ i j : ℕ, (i, j) ∈ γ → i ≠ 0 → i = 1 := by
        intro i j hij hi
        rw [mem_iff_lt_colLen] at hij
        apply lt_of_le_of_lt' (γ.colLen_anti 0 j (Nat.zero_le j)) at hij
        lia
      specialize hi0 i j hij hi
      rw [hi0, row]
      ext a
      by_cases ha : a = 0
      · suffices ∀ T : SemistandardYoungTableau γ, Multiset.count a (Multiset.map
          (fun x : ℕ × ℕ ↦ T x.1 x.2) {c ∈ γ.cells | c.1 = 1}.val) = 0 by rw [this T₁, this T₂]
        intro T
        simp only [ha, Finset.filter_val, Multiset.count_eq_zero, Multiset.mem_map,
          Multiset.mem_filter, Finset.mem_val, mem_cells, Prod.exists, not_exists, not_and,
          and_imp]
        intro i j hij hi
        suffices T i j ≥ i by lia
        exact entry_ge_col hij
      simp only [Finset.filter_val, Multiset.count_map, Multiset.filter_filter]
      simp only [Multiset.ext, Multiset.count_map, Multiset.filter_filter] at h
      specialize h (a - 1)
      suffices ∀ T : SemistandardYoungTableau γ,
          (Multiset.filter (fun x ↦ a = T x.1 x.2 ∧ x.1 = 1) γ.cells.val).card =
          (Multiset.filter (fun x ↦ a - 1 = T x.1 x.2 - 1 ∧ x.1 = 1) γ.cells.val).card by
        rw [this T₁, this T₂, h]
      clear h hT₁ T₁ hT₂ T₂
      intro T
      rw [
        ← Multiset.toFinset_card_eq_card_iff_nodup.mpr <| Multiset.Nodup.filter _ γ.cells.nodup,
        ← Multiset.toFinset_card_eq_card_iff_nodup.mpr <| Multiset.Nodup.filter _ γ.cells.nodup]
      refine Finset.card_bijective id Function.bijective_id ?_
      intro x
      simp only [Multiset.toFinset_filter, Finset.val_toFinset, Finset.mem_filter, mem_cells,
        id_eq, and_congr_right_iff, and_congr_left_iff]
      intro hx hx1
      suffices T x.1 x.2 ≥ 1 by lia
      exact hx1 ▸ entry_ge_col hx
    · rw [T₁.zeros hij, T₂.zeros hij]

private lemma exists_ssytwc_map_sub_one_filter {γ : YoungDiagram} {n p : ℕ} {μ : Multiset ℕ}
    (hγ : γ.rowLens = [n - p, p]) (hcs : γ.card = μ.sum) (hμ : μ.toList ≠ [])
    (hp : p ≤ μ.toList.min hμ)
    (L : Sym ℕ p) (hL : L ∈ List.sym p (List.range (μ.card - 1))) :
    ∃ T ∈ SemistandardYoungTableauWithContent γ μ,
    Multiset.map (fun x ↦ T x.1 x.2 - 1) (Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val) =
    L.toMultiset := by
  have hμc : μ.card ≠ 0 := by rwa [ne_eq, Multiset.card_eq_zero, ← Multiset.toList_eq_nil]
  have hr0 : γ.rowLen 0 = n - p := by simp [← get_rowLens, hγ]
  have hr1 : γ.rowLen 1 = p := by simp [← get_rowLens, hγ]
  have hc0 : γ.colLen 0 = 2 := by simp [← length_rowLens, hγ]
  let M := Multiset.map (· + 1) L.val
  have hM : M ≤ μ.fromCounts := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a < μ.card
    · simp only [Sym.val_eq_coe, Multiset.count_map, Multiset.count_fromCounts ha, ge_iff_le, M]
      have hmf : (Multiset.filter (fun b ↦ a = b + 1) L.val).card ≤ p := by
        have hLp : p = L.val.card := by simp
        conv => rhs; rw [hLp]
        exact Multiset.card_le_card (by simp)
      refine le_trans hmf <| le_trans hp <| List.min_le_of_mem ?_
      rw [Multiset.mem_toList, ← Multiset.mem_sort (· ≥ ·)]
      exact List.getElem_mem _
    · suffices Multiset.count a M = 0 by simp [this]
      simp only [Sym.val_eq_coe, Multiset.count_eq_zero, Multiset.mem_map, Sym.mem_coe,
        not_exists, not_and, M]
      intro x hx
      suffices x < μ.card - 1 by lia
      apply List.mem_of_mem_of_mem_sym hx at hL
      rwa [List.mem_range] at hL
  have hnp : p ≤ n - p := by
    rw [← hr0, ← hr1]
    exact γ.rowLen_anti 0 1 zero_le_one
  have hμn : μ.fromCounts.card = n := by
    simp [← hcs, card_eq_sum_rowLens, hγ]
    lia
  have hMp : M.card = p := by simp [M]
  have hr0' : γ.rowLen 0 = μ.fromCounts.card - M.card := by rw [hμn, hMp, hr0]
  use (twoRowTableau hr0' (hMp ▸ hr1) hc0 hM ?_)
  swap
  · intro i hi r hr
    simp [M] at hr
    suffices ((μ.fromCounts - M).sort (· ≤ ·))[i]'(by
        simp [Multiset.card_sub hM, hMp, hμn]; lia) = 0 by lia
    rw [← Nat.le_zero]
    refine sorted_le_of_exists_multiset _ (Multiset.pairwise_sort _ _) i _ 0 ?_
    use Multiset.filter (fun x ↦ 0 = x) (μ.fromCounts - M)
    constructor
    · rw [Multiset.le_iff_count]
      intro a
      rw [Multiset.coe_count, Multiset.count_sort]
      exact Multiset.count_le_of_le a (Multiset.filter_le _ _)
    constructor
    · rw [← Multiset.count_eq_card_filter_eq, Multiset.count_sub,
        Multiset.count_fromCounts (Nat.pos_iff_ne_zero.mpr hμc),
        show Multiset.count 0 M = 0 by simp [M]]
      rw [Multiset.sort_getElem_zero_eq_max hμ]
      have hmm := List.min_le_of_mem (List.max_mem hμ)
      lia
    · intro s
      rw [Multiset.mem_filter]
      lia
  constructor
  · simp [SemistandardYoungTableauWithContent]
  · simp [map_twoRow_eq_row2_sub_one, M]

private lemma map_sub_one_filter_mem_sym {γ : YoungDiagram} {μ : Multiset ℕ} {p : ℕ}
    (hr1 : γ.rowLen 1 = p) (h0 : 0 ∉ μ)
    (T : SemistandardYoungTableau γ) (hT : T ∈ SemistandardYoungTableauWithContent γ μ) :
    ⟨Multiset.map (fun x ↦ T x.1 x.2 - 1) (Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val),
      by
      simp only [Multiset.card_map]
      rw [show Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val = (γ.row 1).val by rfl,
        Finset.card_val, ← γ.rowLen_eq_card, hr1]⟩ ∈
    List.sym p (List.range (μ.card - 1)) := by
  refine mem_list_sym ?_
  simp only
  rw [Multiset.le_iff_count]
  intro a
  simp only [Multiset.count_dedup, Multiset.mem_map, Multiset.mem_filter,
    Finset.mem_val, mem_cells, Prod.exists, ↓existsAndEq, and_true, Multiset.coe_count,
    List.count_range]
  split_ifs <;> norm_num
  rename_i ham ha
  simp only [Multiset.mem_map, Multiset.mem_filter, Finset.mem_val, mem_cells, Prod.exists,
    ↓existsAndEq, and_true] at ham
  obtain ⟨i, hi, hia⟩ := ham
  subst hia
  have := entry_ge_col (T := T) hi
  apply T.mem_content_of_mem at hi
  rw [hT, Multiset.mem_fromCounts_iff h0] at hi
  lia

theorem kostka_two_rows (h2 : γ.rowLens = [n - p, p]) (h : γ.card = μ.sum) (hμ : μ.toList ≠ [])
    (h0 : 0 ∉ μ) (hp : p ≤ μ.toList.min hμ) :
    kostkaNumber γ μ = (p + μ.card - 2).choose p := by
  have hμc : μ.card ≠ 0 := by rwa [ne_eq, Multiset.card_eq_zero, ← Multiset.toList_eq_nil]
  have hr1 : γ.rowLen 1 = p := by simp [← get_rowLens, h2]
  have hc0 : γ.colLen 0 = 2 := by simp [← length_rowLens, h2]
  rw [show p + μ.card - 2 = (μ.card - 1) + p - 1 by lia, ← Nat.multichoose_eq,
    kostkaNumber_eq_card_ssyt_content,
    ← show (List.range (μ.card - 1)).length = μ.card - 1 by exact List.length_range,
    ← List.length_sym, ← Multiset.coe_card,
    ← Multiset.toFinset_card_of_nodup <| Multiset.coe_nodup.mpr <|
      List.Nodup.sym _ List.nodup_range,
    Nat.card_eq_card_finite_toFinset (finite_ssyt_content γ μ)]
  let e : (T : SemistandardYoungTableau γ) →
    (hT : T ∈ Set.Finite.toFinset (finite_ssyt_content γ μ)) → Sym ℕ p :=
    fun T hT ↦ ⟨Multiset.map (fun (i, j) => (T i j) - 1) (Finset.filter (fun x ↦ x.1 = 1)
      (γ.cells)).val, by
      simp only [Finset.filter_val, Multiset.card_map]
      rw [show Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val = (γ.row 1).val by rfl,
        Finset.card_val, ← γ.rowLen_eq_card, hr1]
      ⟩
  refine Finset.card_bij e ?_ ?_ ?_
  · simp only [Set.toFinite_toFinset, Set.mem_toFinset, List.toFinset_coe, Finset.filter_val,
      List.mem_toFinset, e]
    exact map_sub_one_filter_mem_sym hr1 h0
  · simp only [Set.toFinite_toFinset, Set.mem_toFinset, Finset.filter_val, ← Sym.coe_inj,
      Sym.coe_mk, e]
    exact eq_of_map_sub_one_filter_eq hc0
  · simp only [List.toFinset_coe, List.mem_toFinset, Finset.filter_val, Set.toFinite_toFinset,
      Set.mem_toFinset, exists_prop, e, ← Sym.coe_inj, Sym.coe_mk]
    exact exists_ssytwc_map_sub_one_filter h2 h hμ hp

theorem kostka_ineq_two_rows (h2 : γ.rowLens = [n - p, p]) (hn : n ≥ 5)
    (hp0 : p ≠ 0) (hγ : γ.card = n) (h : γ.card = μ.sum) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (hp : p ≤ μ.toList.min hμ) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  by_cases hp1 : p = 1
  · refine kostka_ineq_hook (by lia) ?_ h h0
    rw [← rowLens_eq_iff, h2, hookDiagram_rowLens (by lia), hp1]
  have hp2 : p ≥ 2 := by lia
  by_cases hm1 : μ.card = 1
  · rw [Multiset.card_eq_one] at hm1
    obtain ⟨m, hm⟩ := hm1
    have h' := h
    rw [hm, Multiset.sum_singleton, hγ] at h'
    rw [← h'] at hm
    refine kostka_ineq_singleton ?_ hm h
    rw [ne_eq, ← rowLens_eq_iff, h2, horizontalDiagram_rowLens]
    · simp only [List.cons.injEq, List.cons_ne_self, and_false, not_false_eq_true]
    · lia
  have hm2 : μ.card ≥ 2 := by
    suffices μ.card ≠ 0 by lia
    rwa [ne_eq, Multiset.card_eq_zero, ← Multiset.toList_eq_nil]
  have hlpn : n ≥ μ.card * p := by
    rw [← hγ, h]
    refine le_trans (Multiset.card_nsmul_le_sum ?_) (by rfl)
    intro x hx
    rw [← Multiset.mem_toList] at hx
    exact le_trans hp (List.min_le_of_mem hx)
  have hfl := factorial_lemma n μ.card p hn hp2 hm2 hlpn
  rw [kostka_two_rows h2 h hμ h0 hp, Nat.choose_eq_factorial_div_factorial (by lia),
    show p + μ.card - 2 - p = μ.card - 2 by lia]
  refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) ?_
  refine Nat.div_le_of_le_mul ?_
  have hf := kostka_replicate_two_rows h2 hn hp0 hγ
  conv at hfl => rhs; lhs; lhs; rw [mul_assoc, ← hf]
  have hpnf : (Nat.factorial p) * Nat.factorial (n - p + 1) > 0 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpnf
  rw [← mul_assoc]
  refine le_trans hfl ?_
  ring_nf
  rfl
