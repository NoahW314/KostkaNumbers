import Mathlib
import KostkaNumbers.Dominate
import KostkaNumbers.Recursion

open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ ν : Multiset ℕ}

/-
Proof that Kostka positive implies domination
-/

lemma bsum_rowLens {r : ℕ} : ∑ i with i.1 ≤ r, γ.rowLens.get i =
    Finset.card {x ∈ γ.cells | x.1 ≤ r} := by
  simp only [List.get_eq_getElem, get_rowLens, rowLen_eq_card]
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_cells, mem_row_iff]
    constructor
    · intro ⟨a, ha, hx⟩
      simp [hx, ha]
    · intro h
      use ⟨x.1, by
        simp [← mem_iff_lt_colLen]
        exact γ.up_left_mem (by rfl) (Nat.zero_le x.2) h.1
        ⟩
      simp [h]
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.PairwiseDisjoint]
    intro a ha b hb hab
    simp only [Function.onFun]
    intro s has hbs x hx
    simp only [Finset.le_eq_subset] at has; simp only [Finset.le_eq_subset] at hbs
    specialize has hx; specialize hbs hx
    rw [mem_row_iff] at has; rw [mem_row_iff] at hbs
    contrapose! hab
    rw [Fin.mk_eq_mk, ← has.2, ← hbs.2]

theorem dominates_of_kostka_pos (hk : 0 < kostkaNumber γ μ) :
    γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ := by
  rw [kostkaNumber, Nat.pos_iff_ne_zero, ne_eq, Nat.card_eq_zero] at hk
  simp only [Set.coe_setOf, not_or, not_isEmpty_iff, nonempty_subtype,
    not_infinite_iff_finite] at hk
  obtain ⟨T, hT⟩ := hk.1
  intro r
  suffices Finset.card {x ∈ γ.cells | T x.1 x.2 ≤ r} =
      ∑ i with i.1 ≤ r, (Multiset.sort (· ≥ ·) μ).get i by
    rw [bsum_rowLens, ← this]
    refine Finset.card_le_card ?_
    intro x hx
    simp; simp at hx
    obtain ⟨hγ, hx⟩ := hx
    constructor
    · exact hγ
    · contrapose! hx
      refine lt_of_lt_of_le hx ?_
      exact entry_ge_col hγ
  rw [Finset.card_def,
    ← Multiset.card_map (fun x : ℕ × ℕ ↦ T x.1 x.2) {x ∈ γ.cells | T x.1 x.2 ≤ r}.val]
  rw [← Multiset.coe_toList μ, Multiset.coe_sort (· ≥ ·) μ.toList]
  simp
  have hcfc :  ∑ x : Fin (μ.toList.mergeSort (· ≥ ·)).length with x.1 ≤ r,
      (μ.toList.mergeSort (· ≥ ·))[x.1] = ∑ x : Fin (μ.toList.mergeSort (· ≥ ·)).length
      with x.1 ≤ r, Multiset.count x.1 μ.fromCounts := by
    congr
    ext x
    rw [Multiset.count_fromCounts ?_]
    let hx := x.2
    simp at hx
    exact hx
  rw [hcfc, ← hT]
  have hctc : ∀ n, Multiset.count n T.content =
      (Multiset.filter (fun x ↦ T x.1 x.2 = n) γ.cells.val).card := by
    intro n
    simp [content, Multiset.count_map, Eq.comm]
  simp only [hctc]
  rw [← Multiset.card_sum]
  congr
  ext x
  rw [Multiset.count_eq_of_nodup, Multiset.count_eq_of_nodup]
  · congr 1
    simp [Finset.mem_sum]
    constructor
    · intro ⟨hx, hTr⟩
      use ⟨T x.1 x.2, by simp [entry_lt_card hT hx]⟩
    · intro ⟨a, har, hx, haT⟩
      simp [har, hx, haT]
  · rw [Multiset.nodup_iff_count_le_one]
    simp [Multiset.count_sum', Multiset.count_filter, Multiset.count_eq_of_nodup γ.cells.nodup]
    intro i j
    by_cases hijγ : (i, j) ∈ γ
    · simp [hijγ]
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_filter] at hb
      rw [Fin.eq_mk_iff_val_eq, ← ha.2, ← hb.2]
    · simp [hijγ]

  · refine Multiset.Nodup.filter _ ?_
    exact γ.cells.nodup

/-
This is a lemma
-/

lemma zero_zero_mem_of_dominates (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    (0, 0) ∈ γ := by
  suffices ¬γ = ⊥ by
    contrapose! this
    exact eq_bot_iff_zero_zero_notMem.mpr this
  rw [eq_bot_iff_card_eq_zero, card_eq_sum_rowLens]
  apply sum_le_sum_of_dominates at hd
  contrapose! hd
  rw [hd, Nat.pos_iff_ne_zero, ← Multiset.coe_toList μ, Multiset.coe_sort,
    List.Perm.sum_nat (List.mergeSort_perm _ _), Multiset.sum_toList, ne_eq,
    Multiset.sum_eq_zero_iff_eq_zero h0]
  exact hμ

/-
Lemmas about jth
-/

private noncomputable
def jth (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ ≠ 0) : ℕ :=
  sSup {j : ℕ | γ.rowLens' j ≥ min_el μ hμ}

lemma jth_set_nonempty (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (hμ : μ ≠ 0) :
    {j : ℕ | γ.rowLens' j ≥ min_el μ hμ}.Nonempty := by
  use 0
  rw [Set.mem_setOf]
  by_cases h0 : 0 ∈ μ
  · rw [min_el_of_zero_mem h0]
    exact Nat.zero_le _

  let hd2 := hd
  apply get_zero_ge_of_dominates at hd
  have hμ2 : 0 < (Multiset.sort (· ≥ ·) μ).length := by simp [Nat.pos_iff_ne_zero, hμ]
  specialize hd ?_ hμ2
  · rw [length_rowLens, ← mem_iff_lt_colLen]
    exact zero_zero_mem_of_dominates γ hd2 hμ h0
  · refine le_trans (min_el_le hμ ⟨0, hμ2⟩) ?_
    rw [get_rowLens] at hd
    simp [rowLens'_eq_rowLen, hd]

lemma lt_colLen_of_min_el_le_rowLens' (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    {j : ℕ} (h : min_el μ hμ ≤ γ.rowLens' j) : j < γ.colLen 0 := by
  contrapose h0
  push_neg
  simp only [h0, not_false_eq_true, rowLens'_eq_zero, nonpos_iff_eq_zero] at h
  rw [← h]
  exact min_el_mem hμ

lemma jth_set_bddAbove (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    BddAbove {j : ℕ | γ.rowLens' j ≥ min_el μ hμ} := by
  rw [bddAbove_def]
  use γ.colLen 0
  intro j
  rw [Set.mem_setOf]
  intro hj
  rw [ge_iff_le] at hj
  apply lt_colLen_of_min_el_le_rowLens' γ hμ h0 at hj
  exact le_of_lt hj

lemma min_el_le_jth_rowLens' (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    min_el μ hμ ≤ γ.rowLens' (jth γ hμ) := by
  suffices jth γ hμ ∈ {j : ℕ | γ.rowLens' j ≥ min_el μ hμ} by
    rw [Set.mem_setOf] at this
    exact this
  exact Nat.sSup_mem (jth_set_nonempty hd hμ) (jth_set_bddAbove hμ h0)

lemma jth_lt_colLen (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    jth γ hμ < γ.colLen 0 := by
  exact lt_colLen_of_min_el_le_rowLens' γ hμ h0 (min_el_le_jth_rowLens' γ hd hμ h0)

lemma min_el_gt_rowLens' (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    {i : ℕ} (hi : i > jth γ hμ) : min_el μ hμ > γ.rowLens' i := by
  rw [gt_iff_lt] at hi
  let hmc := notMem_of_csSup_lt hi (jth_set_bddAbove hμ h0)
  rw [Set.mem_setOf] at hmc
  push_neg at hmc
  exact hmc

lemma min_el_gt_rowLens'_jth_add_one (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ ≠ 0)
    (h0 : 0 ∉ μ) : min_el μ hμ > γ.rowLens' (jth γ hμ + 1) := by
  refine min_el_gt_rowLens' γ hμ h0 ?_
  exact lt_add_one (jth γ hμ)

lemma jth_le_card_sub_one (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ))
    (h : γ.card = μ.sum) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) : jth γ hμ ≤ μ.card - 1 := by
  suffices jth γ hμ < μ.card by
    rw [ne_eq, ← Multiset.card_eq_zero] at hμ
    omega
  refine lt_of_lt_of_le (jth_lt_colLen γ hd hμ h0) ?_
  apply lengths_le_of_dominates at hd
  specialize hd ?_ ?_
  · simp only [ge_iff_le, Multiset.sort_sum, ← h, card_eq_sum_rowLens]
  · intro i
    refine γ.pos_of_mem_rowLens _ <| List.get_mem γ.rowLens i
  · rw [length_rowLens, Multiset.length_sort] at hd
    exact hd


/-
Definition of the function that subtracts from row lens
-/

private noncomputable
def sub_max_fun (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ ≠ 0) : ℕ → ℕ :=
  fun n ↦ if n = (jth γ hμ) then (min_el μ hμ) - γ.rowLens' ((jth γ hμ) + 1)
  else if n > (jth γ hμ) then γ.rowLens' n - γ.rowLens' (n + 1) else 0

lemma sub_max_fun_support (γ : YoungDiagram) {μ : Multiset ℕ} (hμ : μ ≠ 0) (n : ℕ) :
    sub_max_fun γ hμ n ≠ 0 ↔ (n = (jth γ hμ) ∧ (min_el μ hμ) > γ.rowLens' ((jth γ hμ) + 1))
    ∨ (n > (jth γ hμ) ∧ γ.rowLens' n > γ.rowLens' (n + 1) ∧ n < γ.colLen 0) := by
  simp only [sub_max_fun, gt_iff_lt, ne_eq]
  split_ifs with h h'
  all_goals simp [h]
  · omega
  · by_cases hn : n < γ.colLen 0
    · simp only [h', hn, and_true, true_and]; omega
    · simp [hn]
  · simp [h']


lemma sub_max_fun_le_rowLens' (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) (i : ℕ) :
    sub_max_fun γ hμ i ≤ γ.rowLens' i := by
  unfold sub_max_fun
  split_ifs with h h'
  all_goals simp [h]
  have := min_el_le_jth_rowLens' γ hd hμ h0
  omega

lemma rowLens'_le_rowLens'_sub_max_fun (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) (i : ℕ) :
    γ.rowLens' (i + 1) ≤ γ.rowLens' i - sub_max_fun γ hμ i := by
  unfold sub_max_fun
  split_ifs with h h'
  · rw [h]
    let hi := min_el_gt_rowLens'_jth_add_one γ hμ h0
    let hi' := min_el_le_jth_rowLens' γ hd hμ h0
    omega
  · let hi := γ.rowLens'_anti (Nat.le_add_right i 1)
    omega
  · rw [tsub_zero]
    exact γ.rowLens'_anti (Nat.le_add_right i 1)

lemma sub_max_fun_support_finite (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    Finite {n : ℕ | (n = (jth γ hμ) ∧ (min_el μ hμ) > γ.rowLens' ((jth γ hμ) + 1))
    ∨ (n > (jth γ hμ) ∧ γ.rowLens' n > γ.rowLens' (n + 1) ∧ n < γ.colLen 0)} := by
  suffices {n : ℕ | (n = (jth γ hμ) ∧ (min_el μ hμ) > γ.rowLens' ((jth γ hμ) + 1))
      ∨ (n > (jth γ hμ) ∧ γ.rowLens' n > γ.rowLens' (n + 1) ∧ n < γ.colLen 0)} ⊆
      {n : ℕ | n < γ.colLen 0} by exact Finite.Set.subset _ this
  intro n hn
  rw [Set.mem_setOf] at hn
  rcases hn with hn|hn
  · simp [hn.1, jth_lt_colLen γ hd hμ h0]
  · simp [hn.2.2]


private noncomputable
def sub_max_finsupp (γ : YoungDiagram) {μ : Multiset ℕ}
  (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) : ℕ →₀ ℕ :=
  ⟨Set.Finite.toFinset (sub_max_fun_support_finite γ hd hμ h0),
  sub_max_fun γ hμ, by
  intro n
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Iff.comm]
  exact sub_max_fun_support γ hμ n⟩

private noncomputable
def sub_max (γ : YoungDiagram) {μ : Multiset ℕ}
  (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
  SubRowLensType γ :=
  ⟨sub_max_finsupp γ hd hμ h0, by
    constructor
    · simp only [sub_max_finsupp, Finsupp.coe_mk]
      exact rowLens'_le_rowLens'_sub_max_fun γ hd hμ h0
    · simp only [sub_max_finsupp, Finsupp.coe_mk]
      exact sub_max_fun_le_rowLens' γ hd hμ h0⟩

lemma sub_max_support_sum (γ : YoungDiagram) {μ : Multiset ℕ}
    (hd : γ.rowLens ⊵ (Multiset.sort (· ≥ ·) μ)) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    ∑ x ∈ (sub_max γ hd hμ h0).1.support, (sub_max γ hd hμ h0).1 x = min_el μ hμ := by
  simp only [sub_max, sub_max_finsupp, gt_iff_lt, Finsupp.coe_mk, sub_max_fun]
  rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_filter, Finset.sum_ite_eq_of_mem']
  · rw [Finset.filter_filter]
    suffices ∑ x ∈ Finset.filter (fun x => (¬x = jth γ hμ ∧ jth γ hμ < x))
        (Set.Finite.toFinset (sub_max_fun_support_finite γ hd hμ h0)),
        (γ.rowLens' x - γ.rowLens' (x + 1)) =
        ∑ x ∈ Finset.range (γ.colLen 0) \ Finset.range (jth γ hμ + 1),
        (γ.rowLens' x - γ.rowLens' (x + 1)) by
      rw [this]
      zify
      have hxa : ∀ x, ↑(γ.rowLens' x - γ.rowLens' (x + 1)) =
          (γ.rowLens' x : ℤ) - (γ.rowLens' (x + 1) : ℤ) := by
        intro x
        exact Nat.cast_sub <| γ.rowLens'_anti (Nat.le_add_right x 1)
      simp only [hxa]
      rw [Finset.sum_sdiff_eq_sub, Finset.sum_range_sub', Finset.sum_range_sub',
        Nat.cast_sub (le_of_lt (min_el_gt_rowLens'_jth_add_one γ hμ h0))]
      · simp
      · rw [Finset.range_subset]
        exact jth_lt_colLen γ hd hμ h0
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ (by intro _ _; rfl)
    · intro x
      simp only [gt_iff_lt, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
        Finset.mem_sdiff, Finset.mem_range, not_lt, and_imp]
      intro hx hx' hx''
      simp only [hx', false_and, hx'', true_and, false_or] at hx
      constructor
      · exact hx.2
      · exact hx''
    · intro x
      simp only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_range, not_lt, Finset.mem_filter,
        Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_and, and_imp]
      omega
  · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, true_and, lt_self_iff_false,
      false_and, or_false]
    exact min_el_gt_rowLens'_jth_add_one γ hμ h0

/-
Convenient definition
-/

noncomputable
def sub_diagram (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ)
    (hμ : μ ≠ 0) (h0 : 0 ∉ μ) : YoungDiagram := γ.sub (sub_max γ hd hμ h0).1

lemma sub_diagram_colLen_le (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ)
    (hμ : μ ≠ 0) (h0 : 0 ∉ μ) : (sub_diagram hd hμ h0).colLen 0 ≤ γ.colLen 0 := by
  refine colLen_le_of_le ?_
  unfold sub_diagram
  exact γ.sub_le _ (sub_cond (sub_max γ hd hμ h0).2.1)

lemma sub_diagram_colLen (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ)
    (hμ : μ ≠ 0) (h0 : 0 ∉ μ) : γ.colLen 0 - 1 ≤ (sub_diagram hd hμ h0).colLen 0 := by
  have hγ0 : γ.colLen 0 ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, ← mem_iff_lt_colLen]
    exact zero_zero_mem_of_dominates γ hd hμ h0
  by_cases hγ : γ.colLen 0 = 1
  · simp [hγ]

  suffices (sub_diagram hd hμ h0).rowLen (γ.colLen 0 - 2) > 0 by
    conv => rhs; unfold colLen
    rw [Nat.le_find_iff]
    intro n hn
    push_neg
    rw [mem_cells, mem_iff_lt_rowLen]
    refine lt_of_lt_of_le this (rowLen_anti _ _ _ (by omega))
  rw [← rowLens'_eq_rowLen, sub_diagram, sub_rowLens _ _ (sub_cond (sub_max γ hd hμ h0).2.1)]
  simp only [sub_max, sub_max_finsupp, gt_iff_lt, Finsupp.coe_tsub, Finsupp.coe_mk, Pi.sub_apply,
    sub_max_fun, tsub_pos_iff_lt]
  have hc1 : γ.rowLens' (γ.colLen 0 - 1) > 0 := by
    rw [rowLens'_eq_rowLen, gt_iff_lt, ← mem_iff_lt_rowLen, mem_iff_lt_colLen]
    omega
  have hc2 : γ.rowLens' (γ.colLen 0 - 2) > 0 := lt_of_lt_of_le hc1 <| γ.rowLens'_anti <| by omega
  have hc : γ.colLen 0 - 2 + 1 = γ.colLen 0 - 1 := by omega
  split_ifs with h₁ h₂
  · rw [h₁]
    have hm := min_el_le_jth_rowLens' γ hd hμ h0
    have hm' := min_el_gt_rowLens'_jth_add_one γ hμ h0
    suffices γ.rowLens' (jth γ hμ + 1) ≠ 0 by omega
    rw [← h₁, hc, ← Nat.pos_iff_ne_zero]
    exact hc1
  · simp [hc, hc1, hc2]
  · exact hc2

-- proof that card = sum is preserved after the subtraction and erasure

lemma card_sub_max_eq_sum_erase_min_el (γ : YoungDiagram) (μ : Multiset ℕ)
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (h : γ.card = μ.sum) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    (sub_diagram hd hμ h0).card = (μ.erase (min_el μ hμ)).sum := by
  rw [sub_diagram, card_sub, sub_max_support_sum, Multiset.sum_erase' (min_el_mem hμ), h]
  all_goals simp only [sub_max, sub_max_finsupp, Finsupp.coe_mk]
  · exact sub_cond (sub_max γ hd hμ h0).2.1
  · intro i
    exact sub_max_fun_le_rowLens' γ hd hμ h0 i

/-
Proof of domination after subtraction and erasure
-/

variable {r : ℕ}

lemma jth_le_sub_colLen (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (hμ : μ ≠ 0)
    (h0 : 0 ∉ μ) : jth γ hμ ≤ (sub_diagram hd hμ h0).colLen 0 := by
  let hj := jth_lt_colLen γ hd hμ h0
  let hc := sub_diagram_colLen hd hμ h0
  omega

lemma sum_rowLens_sub_sub_max_fun_lt_jth (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ)
    (hμ : μ ≠ 0) (h0 : 0 ∉ μ) (hr : r < jth γ hμ) :
    ∑ x : Fin ((sub_diagram hd hμ h0).rowLens.length) with x.1 ≤ r,
    (sub_diagram hd hμ h0).rowLens' x =
    ∑ x : Fin (γ.rowLens.length) with x.1 ≤ r,
    γ.rowLens' x := by
  let e : (x : Fin (sub_diagram hd hμ h0).rowLens.length) →
    (hx : x ∈ Finset.filter (fun x ↦ x.1 ≤ r) Finset.univ) → Fin γ.rowLens.length :=
    fun x _ ↦ ⟨x.1, by
      let hx := x.2
      simp only [sub_diagram, length_rowLens] at hx
      nth_rw 1 [γ.length_rowLens]
      exact lt_of_lt_of_le hx (colLen_le_of_le (γ.sub_le _ (sub_cond (sub_max γ hd hμ h0).2.1)))⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · intro x₁ _ x₂ _
    simp only [Fin.mk.injEq, e]
    exact Fin.eq_of_val_eq
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, exists_prop, e]
    intro x hx
    use ⟨x.1, by
      nth_rw 2 [length_rowLens]
      exact lt_of_le_of_lt hx (lt_of_lt_of_le hr (jth_le_sub_colLen hd hμ h0))⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
    intro x hx
    have hx' : x.1 ≠ jth γ hμ := by omega
    have hx'' : ¬x.1 > jth γ hμ := by omega
    unfold sub_diagram
    rw [sub_rowLens _ _ (sub_cond (sub_max γ hd hμ h0).2.1)]
    simp [sub_max, sub_max_finsupp, sub_max_fun, hx', hx'']

lemma sum_fin_with_eq_sum_nat_bdd' {n m : ℕ} {f : ℕ → ℕ} :
    ∑ x : Fin n with x.1 ≤ m, f x.1 = ∑ x ∈ {x : ℕ | x ≤ m}.toFinset with x < n, f x := by
  let e : (x : Fin n) → (hx : x ∈ Finset.filter (fun x ↦ x.1 ≤ m) Finset.univ) → ℕ :=
    fun x _ ↦ x.1
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · intro x₁ _ x₂ _
    unfold e
    exact Fin.eq_of_val_eq
  · simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      exists_prop, and_imp, e]
    intro b _ hn
    use ⟨b, hn⟩
  · simp [e]

lemma sum_fin_with_eq_sum_nat_bdd {n m : ℕ} {f : ℕ → ℕ} (hf : ∀ x ≥ n, f x = 0) :
    ∑ x : Fin n with x.1 ≤ m, f x.1 = ∑ x ∈ {x : ℕ | x ≤ m}.toFinset, f x := by
  rw [sum_fin_with_eq_sum_nat_bdd']
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · intro x
    simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq, and_imp]
    intro hx
    simp only [hx, implies_true]
  · intro x
    simp only [Finset.mem_sdiff, Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, not_and,
      not_lt, and_imp]
    intro hxm hx
    specialize hx hxm
    exact hf x hx
  · simp

lemma sum_rowLens_sub_sub_max_fun_ge_jth (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ)
    (hμ : μ ≠ 0) (h0 : 0 ∉ μ) (hr : r ≥ jth γ hμ) :
    ∑ x : Fin ((sub_diagram hd hμ h0).rowLens.length) with x.1 ≤ r,
    (sub_diagram hd hμ h0).rowLens' x =
    ∑ x : Fin (γ.rowLens.length) with x.1 ≤ r + 1,
    γ.rowLens' x - min_el μ hμ := by
  rw [sum_fin_with_eq_sum_nat_bdd, sum_fin_with_eq_sum_nat_bdd]
  swap;
  · intro x hx
    rw [length_rowLens] at hx
    refine rowLens'_eq_zero ?_
    exact Nat.not_lt.mpr hx
  swap
  · intro x hx
    rw [length_rowLens] at hx
    refine rowLens'_eq_zero ?_
    exact Nat.not_lt.mpr hx

  have hj : jth γ hμ ∈ {x : ℕ | x ≤ r}.toFinset := by simp [hr]
  rw [← Finset.sum_erase_add _ _ hj]
  conv => {
    lhs; rhs;
    unfold sub_diagram
    rw [sub_rowLens _ _ (sub_cond (sub_max γ hd hμ h0).2.1)]
    simp only [sub_max, sub_max_finsupp, gt_iff_lt, sub_rowLens,
    Finsupp.coe_tsub, Finsupp.coe_mk, Pi.sub_apply, sub_max_fun, ↓reduceIte]
  }
  have hj' : jth γ hμ ∈ {x : ℕ | x ≤ r + 1}.toFinset := by
    rw [Set.mem_toFinset, Set.mem_setOf_eq]
    exact Nat.le_add_right_of_le hr
  rw [← Finset.sum_erase_add _ _ hj']
  have hj1 : jth γ hμ + 1 ∈ {x : ℕ | x ≤ r + 1}.toFinset.erase (jth γ hμ) := by simp [hr]
  rw [← Finset.sum_erase_add _ _ hj1, add_assoc, add_tsub_assoc_of_le]
  swap
  · exact Nat.le_add_left_of_le <| min_el_le_jth_rowLens' γ hd hμ h0

  have hrl : γ.rowLens' (jth γ hμ) - (min_el μ hμ - γ.rowLens' (jth γ hμ + 1)) =
      γ.rowLens' (jth γ hμ + 1) + γ.rowLens' (jth γ hμ) - min_el μ hμ := by
    have := min_el_gt_rowLens'_jth_add_one γ hμ h0
    omega
  rw [hrl, Nat.add_right_cancel_iff]
  let e : (x : ℕ) → (hx : x ∈ {x : ℕ | x ≤ r}.toFinset.erase (jth γ hμ)) → ℕ :=
    fun x _ ↦ if x < jth γ hμ then x else x + 1
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp only [Finset.mem_erase, ne_eq, Set.mem_toFinset, Set.mem_setOf_eq,
      and_imp, e]
    intro x hxj hxr
    by_cases hx : x < jth γ hμ
    · simp only [hx, ↓reduceIte, hxj, not_false_eq_true, true_and]
      omega
    · simp only [hx, ↓reduceIte, Nat.add_right_cancel_iff, add_le_add_iff_right]
      omega

  · intro x₁ hx₁ x₂ hx₂
    unfold e
    simp at hx₁ hx₂
    split_ifs with hxj₁ hxj₂
    all_goals omega
  · simp only [Finset.mem_erase, ne_eq, Set.mem_toFinset, Set.mem_setOf_eq, exists_prop, and_imp,
      e]
    intro x hxj1 hxj hxr1
    by_cases hx : x < jth γ hμ
    · use x
      simp only [hxj, not_false_eq_true, true_and, hx, ↓reduceIte, and_true]
      exact le_trans (le_of_lt hx) hr
    · use (x - 1)
      have hxj' : ¬ x - 1 < jth γ hμ := by omega
      simp [hxj']
      omega
  · unfold sub_diagram
    rw [sub_rowLens _ _ (sub_cond (sub_max γ hd hμ h0).2.1)]
    simp only [Finset.mem_erase, ne_eq, Set.mem_toFinset, Set.mem_setOf_eq, sub_max,
      sub_max_finsupp, gt_iff_lt, Finsupp.coe_tsub, Finsupp.coe_mk, Pi.sub_apply,
      sub_max_fun, and_imp, e]
    intro x hxj hxr
    simp only [hxj, ↓reduceIte]
    by_cases hx : x < jth γ hμ
    · have hx' : ¬ jth γ hμ < x := by omega
      simp [hx, hx']
    · have hx' : jth γ hμ < x := by omega
      let hrl := γ.rowLens'_anti (Nat.le_add_right x 1)
      simp [hx, hx']
      omega

lemma sum_sort_erase_lt_card_sub_one (hμ : μ ≠ 0) (hr : r < μ.card - 1) :
    ∑ x : Fin ((Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length) with x.1 ≤ r,
    (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ)))[x.1] =
    ∑ x : Fin ((Multiset.sort (· ≥ ·) μ).length) with x.1 ≤ r,
    (Multiset.sort (· ≥ ·) μ)[x.1] := by
  let e : (x : Fin ((Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))).length)) →
    (hx : x ∈ Finset.filter (fun x ↦ x.1 ≤ r) Finset.univ) →
    Fin ((Multiset.sort (· ≥ ·) μ).length) := fun x _ ↦ ⟨x.1, by
      let hx := x.2; simp_all; omega⟩
  refine Finset.sum_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · intro x₁ _ x₂ _
    simp only [Fin.mk.injEq, e]
    exact Fin.eq_of_val_eq
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
    intro x hx
    use ⟨x.1, by
      let hx := x.2; simp_all [Multiset.card_erase_of_mem (min_el_mem hμ)]; omega⟩
    simp [hx]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ge_iff_le, e]
    intro x hx
    have hml : (Multiset.sort (· ≥ ·) μ) =
        ((min_el μ hμ) ::ₘ μ.erase (min_el μ hμ)).toList.mergeSort (· ≥ ·) := by
      rw [cons_erase_min_el hμ, ← Multiset.coe_sort, Multiset.coe_toList]
    have hm : ∀ m ∈ μ.erase (min_el μ hμ), m ≥ min_el μ hμ := by
      intro m hm
      exact min_el_le' hμ (Multiset.mem_of_mem_erase hm)
    simp only [hml, List.cons_sort_eq_sort_append_ge (μ.erase (min_el μ hμ)) hm]
    rw [List.getElem_append_left]
    · simp [← Multiset.coe_sort]
    · simp [Multiset.card_erase_of_mem (min_el_mem hμ)]
      omega


lemma sum_with_le_sum_with_add_one_sub_min_el (hμ : μ ≠ 0) (hr : r < μ.card - 1) :
    ∑ x : Fin (Multiset.sort (· ≥ ·) μ).length with x.1 ≤ r,
    (Multiset.sort (· ≥ ·) μ)[x.1] ≤
    ∑ x : Fin (Multiset.sort (· ≥ ·) μ).length with x.1 ≤ r + 1,
    (Multiset.sort (· ≥ ·) μ)[x.1] - min_el μ hμ := by
  let r1 : Fin (Multiset.sort (· ≥ ·) μ).length := ⟨r + 1, by simp; omega⟩
  have hr1 : r1 ∈ Finset.filter (fun x ↦ x.1 ≤ r + 1) Finset.univ := by simp [r1]
  rw [← Finset.sum_erase_add _ _ hr1]
  suffices (Finset.filter (fun x ↦ x.1 ≤ r + 1) Finset.univ).erase r1 =
      Finset.filter (fun x ↦ x.1 ≤ r) Finset.univ by
    rw [this]
    let hm := min_el_le hμ r1
    rw [List.get_eq_getElem] at hm
    omega
  ext x
  simp only [Finset.mem_erase, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, r1]
  have hx : x = ⟨x.1, x.2⟩ := rfl
  conv => lhs; lhs; rw [hx, Fin.mk.inj_iff]
  omega

lemma rowLens_sub_dominates_sort_erase_min_el (γ : YoungDiagram) (μ : Multiset ℕ)
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (h : γ.card = μ.sum) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    (sub_diagram hd hμ h0).rowLens ⊵ Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ)) := by
  refine dominates_of_forall_lt_min ?_ ?_
  swap
  · rw [Multiset.sort_sum, ← (card_sub_max_eq_sum_erase_min_el γ μ hd h hμ h0),
      card_eq_sum_rowLens]

  intro r hr
  simp only [List.get_eq_getElem, get_rowLens, ← rowLens'_eq_rowLen]
  by_cases hrj : r < jth γ hμ
  · rw [sum_sort_erase_lt_card_sub_one hμ (lt_of_lt_of_le hrj
      (jth_le_card_sub_one hd h hμ h0)), sum_rowLens_sub_sub_max_fun_lt_jth hd hμ h0 hrj]
    specialize hd r
    simp only [List.get_eq_getElem, get_rowLens] at hd
    exact hd
  · push_neg at hrj
    rw [lt_min_iff] at hr
    rw [sum_rowLens_sub_sub_max_fun_ge_jth hd hμ h0 hrj]
    specialize hd (r + 1)
    simp only [List.get_eq_getElem, get_rowLens, ← rowLens'_eq_rowLen, ge_iff_le] at hd
    refine le_trans ?_ (Nat.sub_le_sub_right hd _)
    have hrl : r < μ.card - 1 := by
      simp only [ge_iff_le, Multiset.length_sort, Multiset.card_erase_of_mem (min_el_mem hμ),
        Nat.pred_eq_sub_one, length_rowLens] at hr
      exact hr.1
    rw [sum_sort_erase_lt_card_sub_one hμ hrl]
    exact sum_with_le_sum_with_add_one_sub_min_el hμ hrl

/-
The main theorem
-/

theorem kostka_pos_of_dominates (γ : YoungDiagram) (μ : Multiset ℕ)
    (hd : γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ) (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    kostkaNumber γ μ > 0 := by
  by_cases hμ : μ = 0
  · have hγ : γ = ⊥ := by rw [eq_bot_iff_card_eq_zero, h, hμ, Multiset.sum_zero]
    rw [hμ, hγ, ← Multiset.bot_eq_zero, kostka_bot_bot]
    exact zero_lt_one

  rw [kostka_recursion γ μ hμ h0 h]
  suffices ∃ f : SubRowLensType γ, ((γ.sub f.1).rowLens
      ⊵ Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))) ∧
      (γ.sub f.1).card = (μ.erase (min_el μ hμ)).sum by
    obtain ⟨f, hf, hγμ⟩ := this
    let hf := kostka_pos_of_dominates _ _ hf hγμ ?_
    · refine lt_of_lt_of_le hf ?_
      have hfp : ∀ f : SubRowLensType γ, f ∈ Finset.univ →
          0 ≤ kostkaNumber (γ.sub f.1)
          (μ.erase (min_el μ hμ)) := by simp
      exact Finset.single_le_sum hfp (Finset.mem_univ _)
    · contrapose! h0
      exact Multiset.mem_of_mem_erase h0
  use sub_max γ hd hμ h0
  constructor
  · exact rowLens_sub_dominates_sort_erase_min_el γ μ hd h hμ h0
  · exact card_sub_max_eq_sum_erase_min_el γ μ hd h hμ h0
  termination_by μ.card
  decreasing_by simp [min_el_mem hμ, Nat.pos_iff_ne_zero, hμ]

theorem kostka_pos_iff_dominates (h : γ.card = μ.sum) (h0 : 0 ∉ μ) : 0 < kostkaNumber γ μ ↔
    γ.rowLens ⊵ Multiset.sort (· ≥ ·) μ := by
  constructor
  · intro hk
    exact dominates_of_kostka_pos hk
  · intro hd
    exact kostka_pos_of_dominates γ μ hd h h0
