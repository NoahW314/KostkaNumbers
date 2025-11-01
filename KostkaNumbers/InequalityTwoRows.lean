import Mathlib
import KostkaNumbers.HookLength.HookLengthFormula
import KostkaNumbers.FactorialLemma
import KostkaNumbers.InequalitySpecial


open YoungDiagram SemistandardYoungTableau Kostka

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n p : ℕ}

theorem kostka_replicate_two_rows (h2 : γ.rowLens = [n - p, p])
    (hn : n ≥ 5) (hp0 : p ≠ 0) (hγ : γ.card = n) :
    ((Nat.factorial p)*(Nat.factorial (n - p + 1))) *
    kostkaNumber γ (Multiset.replicate n 1) = (Nat.factorial n)*(n-2*p+1) := by
  have hpn : p ≤ n - p := by
    have hrls := γ.rowLens_sorted
    rw [h2] at hrls
    simp at hrls
    exact hrls
  have hk0 : kostkaNumber γ (Multiset.replicate n 1) ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, kostka_pos_iff_dominates]
    · rw [h2, Multiset.sort_eq_replicate_iff.mpr (by rfl)]
      refine dominates_replicate_one ?_ ?_
      all_goals simp; omega
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
    rw [← Nat.factorial_succ,
      show n - 2 * p + 1 = (n - p + 1) - p by omega,
      Nat.factorial_mul_descFactorial (by omega)]
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
    omega
  have hhl1 : ∏ x ∈ γ.cells with x.1 = 1, γ.hookLength x.1 x.2 = p.factorial := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    let e : (i : ℕ) → (hi : i ∈ Finset.range p) → ℕ × ℕ := fun i hi ↦ (1, (p-1)-i)
    rw [Finset.prod_bij e]
    · simp only [Finset.mem_range, Finset.mem_filter, mem_cells, and_true, e]
      intro i _
      rw [mem_iff_lt_rowLen, hr1]
      omega
    · simp [e]
      omega
    · simp only [Finset.mem_filter, mem_cells, Finset.mem_range, exists_prop, and_imp, Prod.forall,
        Prod.mk.injEq, e]
      intro i j hij hi
      use p - 1 - j
      rw [hi, mem_iff_lt_rowLen, hr1] at hij
      omega
    · simp only [Finset.mem_range, hookLength_def, hr1, Nat.reduceAdd, Nat.add_right_cancel_iff, e]
      intro i hi
      suffices γ.colLen (p - 1 - i) = 2 by omega
      have hcle : γ.colLen (p - 1 - i) ≤ 2 := by
        refine le_trans (γ.colLen_anti 0 _ (Nat.zero_le _)) ?_
        simp [← length_rowLens, h2]
      suffices 1 < γ.colLen (p - 1 - i) by omega
      rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr1]
      omega
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
        omega
      · omega
    · simp [e]
      omega
    · simp only [not_lt, Finset.mem_filter, mem_cells, Finset.mem_range, exists_prop, and_imp,
        Prod.forall, Prod.mk.injEq, e]
      intro i j hij hi hj
      use n - p - 1 - j
      specialize hi0 i j hij hi
      rw [hi0, mem_iff_lt_rowLen, hr0] at hij
      omega
    · simp only [Finset.mem_range, hookLength_def, hr0, zero_add, Nat.add_right_cancel_iff, e]
      intro i hi
      suffices γ.colLen (n - p - 1 - i) = 1 by omega
      suffices ¬ 1 < γ.colLen (n - p - 1 - i) ∧ 0 < γ.colLen (n - p - 1 - i) by omega
      constructor
      · rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr1]
        omega
      · rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr0]
        omega
  have hhl3 : ∏ x ∈ γ.cells with ¬x.1 = 1 ∧ x.2 < p,
      γ.hookLength x.1 x.2 = (n - p + 1).descFactorial p := by
    rw [Nat.descFactorial_eq_prod_range]
    let e : (i : ℕ) → (hi : i ∈ Finset.range p) → ℕ × ℕ := fun i _ ↦ (0, i)
    rw [Finset.prod_bij e]
    · simp [mem_iff_lt_rowLen, hr0, e]
      omega
    · simp [e]
    · simp only [Finset.mem_filter, mem_cells, Finset.mem_range, exists_prop, and_imp, Prod.forall,
        Prod.mk.injEq, exists_eq_right_right, e]
      intro i j hij hi
      specialize hi0 i j hij hi
      simp [hi0]
    · simp only [Finset.mem_range, hookLength_def, hr0, zero_add, e]
      intro i hi
      suffices γ.colLen i = 2 by omega
      suffices ¬ 2 < γ.colLen i ∧ 1 < γ.colLen i by omega
      simp_rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, hr1, hr2]
      omega
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
    simp only [Sym.val_eq_coe, Multiset.coe_nil, nonpos_iff_eq_zero] at h
    rw [Multiset.dedup_eq_zero, ← Multiset.card_eq_zero, Sym.card_coe] at h
    contradiction
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  subst hm

  obtain ⟨x, L', hL⟩ := List.exists_cons_of_ne_nil hL
  subst hL
  simp only [Nat.succ_eq_add_one, List.mem_append, List.mem_map]
  by_cases hx : x ∈ xs
  · left
    obtain ⟨ys, hys⟩ := Sym.exists_cons_of_mem hx
    use ys
    constructor
    · have h' : ys.val.dedup ≤ Multiset.ofList (x :: L') := by
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
          simp only [Nat.succ_eq_add_one, Sym.val_eq_coe, Multiset.nodup_dedup, Multiset.mem_dedup,
            Sym.mem_coe, ha', Multiset.count_eq_one_of_mem, Multiset.coe_count,
            List.one_le_count_iff] at h
          exact h
        · exact Nat.zero_le _
      exact mem_list_sym h'
    · symm
      exact hys
  · right
    have h' : xs.val.dedup ≤ Multiset.ofList L' := by
      rw [Multiset.le_iff_count]
      intro a
      simp only [Nat.succ_eq_add_one, Sym.val_eq_coe, Multiset.count_dedup,
        Sym.mem_coe, Multiset.coe_count]
      split_ifs with ha
      · rw [List.one_le_count_iff]
        rw [Multiset.le_iff_count] at h
        specialize h a
        simp [ha] at h
        have hax : a ≠ x := by
           contrapose! hx
           rw [← hx]
           exact ha
        simp only [hax, false_or] at h
        exact h
      · exact Nat.zero_le _
    exact mem_list_sym h'
  termination_by n+L.length

noncomputable
def twoRowTableau {γ : YoungDiagram} {n p : ℕ} (hr0 : γ.rowLen 0 = n - p)
  (hr1 : γ.rowLen 1 = p) (hc0 : γ.colLen 0 = 2)
  (content : Multiset ℕ) (row2 : Multiset ℕ) (hrc : row2 ≤ content)
  (hc : content.card = n) (hr : row2.card = p)
  (h : ∀ i : ℕ, (hi : i < p) → (∀ r ∈ row2, r >
    ((content - row2).toList.mergeSort (· ≤ ·))[i]'(by
    simp [Multiset.card_sub hrc, hc, hr]
    refine lt_of_lt_of_le hi ?_
    rw [← hr0, ← hr1]
    exact γ.rowLen_anti 0 1 (by simp))))
  : SemistandardYoungTableau γ :=
  ⟨fun i j ↦ if h0 : i = 0 ∧ j < ((content - row2).toList.mergeSort (· ≤ ·)).length then
  ((content - row2).toList.mergeSort (· ≤ ·))[j]'(h0.2) else
  if h1 : i = 1 ∧ j < (row2.toList.mergeSort (· ≤ ·)).length then
  (row2.toList.mergeSort (· ≤ ·))[j]'(h1.2) else 0,

  by
  intro i j1 j2 hj hij
  have hcr : (content - row2).card = n - p := by rw [Multiset.card_sub hrc, hc, hr]
  have hi0 : ∀ i j : ℕ, (i, j) ∈ γ → i ≠ 0 → i = 1 := by
    intro i j hij hi
    rw [mem_iff_lt_colLen] at hij
    apply lt_of_le_of_lt' (γ.colLen_anti 0 j (Nat.zero_le j)) at hij
    rw [hc0] at hij
    omega
  have hij' := γ.up_left_mem (by rfl) (le_of_lt hj) hij
  by_cases h0 : i = 0
  · have hj' : ∀ j : ℕ, (i, j) ∈ γ → j < n - p := by
      intro j hij
      rw [h0, mem_iff_lt_rowLen, hr0] at hij
      exact hij
    simp [h0, hcr, hj' j1 hij', hj' j2 hij]
    exact List.Sorted.rel_get_of_lt (List.sorted_mergeSort' _ _) hj
  · specialize hi0 i j2 hij h0
    have hj' : ∀ j : ℕ, (i, j) ∈ γ → j < p := by
      intro j hij
      rw [hi0, mem_iff_lt_rowLen, hr1] at hij
      exact hij
    simp [hi0, hr, hj' j1 hij', hj' j2 hij]
    exact List.Sorted.rel_get_of_lt (List.sorted_mergeSort' _ _) hj
  ,
  by
  intro i1 i2 j hi hij
  have hij' := γ.up_left_mem (le_of_lt hi) (by rfl) hij
  have hi2 : i2 = 1 := by
    rw [mem_iff_lt_colLen] at hij
    apply lt_of_le_of_lt' (γ.colLen_anti 0 j (Nat.zero_le j)) at hij
    rw [hc0] at hij
    omega
  have hi1 : i1 = 0 := by omega
  have hjn : j < n - p := by
    rw [hi1, mem_iff_lt_rowLen, hr0] at hij'
    exact hij'
  have hjp : j < p := by
    rw [hi2, mem_iff_lt_rowLen, hr1] at hij
    exact hij
  simp [hi1, hi2, Multiset.card_sub hrc, hc, hr, hjp, hjn]
  refine h j hjp _ ?_
  have hrll : (row2.toList.mergeSort (· ≤ ·))[j]'(by simp [hr, hjp]) ∈
    row2.toList.mergeSort (· ≤ ·) := List.getElem_mem _
  rw [List.mem_mergeSort, Multiset.mem_toList] at hrll
  exact hrll
  ,
  by
  intro i j hij
  have hcr : (content - row2).card = n - p := by rw [Multiset.card_sub hrc, hc, hr]
  simp only [List.length_mergeSort, Multiset.length_toList, hcr, hr]
  split_ifs with hi0 hi1
  · rw [hi0.1, mem_iff_lt_rowLen, hr0] at hij
    omega
  · rw [hi1.1, mem_iff_lt_rowLen, hr1] at hij
    omega
  · rfl
  ⟩

@[simp]
theorem twoRow_content {γ : YoungDiagram} {n p : ℕ} (hr0 : γ.rowLen 0 = n - p)
    (hr1 : γ.rowLen 1 = p) (hc0 : γ.colLen 0 = 2)
    (content : Multiset ℕ) (row2 : Multiset ℕ) (hrc : row2 ≤ content)
    (hc : content.card = n) (hr : row2.card = p)
    (h : ∀ i : ℕ, (hi : i < p) → (∀ r ∈ row2, r >
      ((content - row2).toList.mergeSort (· ≤ ·))[i]'(by
      simp [Multiset.card_sub hrc, hc, hr]
      refine lt_of_lt_of_le hi ?_
      rw [← hr0, ← hr1]
      exact γ.rowLen_anti 0 1 (by simp)))) :
    (twoRowTableau hr0 hr1 hc0 content row2 hrc hc hr h).content = content := by
  have hcr : (content - row2).card = n - p := by rw [Multiset.card_sub hrc, hc, hr]
  have hγ : γ.cells = γ.row 0 ∪ γ.row 1 := by
    ext x
    constructor
    · simp_rw [mem_cells, Finset.mem_union, mem_row_iff]
      intro hx
      simp only [hx, true_and]
      rw [mem_iff_lt_colLen] at hx
      apply lt_of_le_of_lt' (γ.colLen_anti 0 x.2 (Nat.zero_le x.2)) at hx
      omega
    · simp_rw [Finset.mem_union, mem_row_iff, mem_cells]
      intro hx
      rcases hx with hx|hx
      all_goals exact hx.1
  simp [SemistandardYoungTableau.content, hγ]
  rw [← Multiset.add_eq_union_iff_disjoint.mpr, Multiset.map_add, ← map_row, ← map_row]

  · simp [twoRowTableau, DFunLike.coe, hcr, hr]
    rw [hr0, hr1]
    simp
    have hasd : List.map (fun x ↦ ((content - row2).toList.mergeSort (· ≤ ·))[x.1]'
        (by simp [x.2, hcr])) (List.finRange (n - p)) =
        ((content - row2).toList.mergeSort (· ≤ ·)) := by
      refine List.ext_getElem ?_ ?_
      all_goals simp [hcr]
    rw [hasd]
    have hpsub : p = (row2.toList.mergeSort (· ≤ ·)).length := by simp [← hr]
    subst hpsub
    simp_rw [List.finRange_map_getElem, ← Multiset.coe_add, ← Multiset.coe_sort,
      Multiset.sort_eq, Multiset.coe_toList]
    rw [Multiset.sub_add_cancel hrc]
  · rw [Multiset.disjoint_left]
    simp [mem_row_iff]
    omega

theorem map_twoRow_eq_row2_sub_one {γ : YoungDiagram} {n p : ℕ} {hr0 : γ.rowLen 0 = n - p}
    {hr1 : γ.rowLen 1 = p} {hc0 : γ.colLen 0 = 2}
    {content : Multiset ℕ} {row2 : Multiset ℕ} {hrc : row2 ≤ content}
    {hc : content.card = n} {hr : row2.card = p}
    {h : ∀ i : ℕ, (hi : i < p) → (∀ r ∈ row2, r >
      ((content - row2).toList.mergeSort (· ≤ ·))[i]'(by
      simp [Multiset.card_sub hrc, hc, hr]
      refine lt_of_lt_of_le hi ?_
      rw [← hr0, ← hr1]
      exact γ.rowLen_anti 0 1 (by simp)))} :
    Multiset.map (fun x ↦ (twoRowTableau hr0 hr1 hc0 content row2 hrc hc hr h) x.1 x.2 - 1)
    (Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val) =
    Multiset.map (· - 1) row2 := by
  rw [show Multiset.filter (fun x ↦ x.1 = 1) γ.cells.val = (γ.row 1).val by rfl,
    ← map_row (fun i j ↦ (twoRowTableau hr0 hr1 hc0 content row2 hrc hc hr h) i j - 1)]
  rw [Multiset.map_coe]
  conv => rhs; rw [show row2 = Multiset.ofList (row2.toList.mergeSort (· ≤ ·)) by
    simp [← Multiset.coe_sort], Multiset.map_coe]
  congr 1
  refine List.ext_get ?_ ?_
  · simp [hr, hr1]
  · simp [twoRowTableau, DFunLike.coe]
    intro i h₁ h₂
    simp [h₂]

lemma sorted_le_of_exists_set (L : List ℕ) (hL : L.Sorted (· ≤ ·))
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
    refine List.Sorted.rel_get_of_le hL ?_
    simp
  · obtain ⟨S, hS, hcard, hn⟩ := h
    have hlt : (L.tail)[i-1]'(by rw [List.length_tail]; omega) = L[i] := by
      simp_rw [List.getElem_tail, show i - 1 + 1 = i by omega]
    rw [← hlt]
    refine sorted_le_of_exists_set L.tail (List.Sorted.tail hL) (i - 1) _ n ?_
    use (S.erase L[0])
    constructor; swap; constructor
    · rw [Multiset.card_erase_eq_ite, Nat.pred_eq_sub_one]
      split_ifs
      all_goals omega
    · intro s hs
      refine hn s <| Multiset.mem_of_mem_erase hs
    · rw [Multiset.le_iff_count]
      intro a
      apply Multiset.count_le_of_le a at hS
      have hct : List.count a L - 1 ≤ List.count a L.tail := List.le_count_tail
      by_cases ha : a = L[0]
      · rw [← ha, Multiset.count_erase_self, Multiset.coe_count]
        rw [Multiset.coe_count] at hS
        omega
      · rw [Multiset.count_erase_of_ne ha, Multiset.coe_count, List.count_tail]
        rw [Multiset.coe_count] at hS
        suffices ¬ L.head? == some a by simp [this]; exact hS
        simp
        unfold List.head?
        suffices L = L[0] :: L.tail by
          rw [this]
          simp only [Option.some.injEq, ne_eq]
          push_neg; symm
          exact ha
        have hL0 : L ≠ [] := by
          rw [ne_eq, List.eq_nil_iff_length_eq_zero]
          omega
        rw [← List.head_eq_getElem_zero hL0]
        symm
        exact List.cons_head_tail hL0


theorem kostka_two_rows (h2 : γ.rowLens = [n - p, p]) (hn : n ≥ 5)
    (h : γ.card = μ.sum) (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    (hp : p ≤ min_el μ hμ) :
    kostkaNumber γ μ = (p + μ.card - 2).choose p := by
  have hμc : μ.card ≠ 0 := by
    rw [ne_eq, Multiset.card_eq_zero]
    exact hμ
  have hr0 : γ.rowLen 0 = n - p := by
    rw [← get_rowLens]
    all_goals simp [h2]
  have hr1 : γ.rowLen 1 = p := by
    rw [← get_rowLens]
    all_goals simp [h2]
  have hc0 : γ.colLen 0 = 2 := by simp [← length_rowLens, h2]
  have hi0 : ∀ i j : ℕ, (i, j) ∈ γ → i ≠ 0 → i = 1 := by
    intro i j hij hi
    rw [mem_iff_lt_colLen] at hij
    apply lt_of_le_of_lt' (γ.colLen_anti 0 j (Nat.zero_le j)) at hij
    simp only [← length_rowLens, h2, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd] at hij
    omega

  rw [show p + μ.card - 2 = (μ.card - 1) + p - 1 by omega, ← Nat.multichoose_eq,
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
    intro T hT
    refine mem_list_sym ?_
    simp only
    rw [Multiset.le_iff_count]
    intro a
    simp [Multiset.count_dedup]
    by_cases ha : a < μ.card - 1
    · simp [ha]
      split_ifs
      all_goals simp
    · simp [ha]
      intro i j hij hi
      simp only [SemistandardYoungTableauWithContent, Set.mem_setOf_eq] at hT
      have hij' := hij
      apply T.mem_content_of_mem_cells at hij
      rw [hT, Multiset.mem_fromCounts_iff h0] at hij
      suffices T i j ≥ 1 by omega
      refine le_trans ?_ (entry_ge_col hij')
      rw [hi]
  · simp [e]
    intro T₁ hT₁ T₂ hT₂ hT
    rw [Subtype.mk_eq_mk] at hT
    refine eq_of_missing_row T₁ T₂ ?_ 0 ?_
    · rw [SemistandardYoungTableauWithContent, Set.mem_setOf] at hT₁ hT₂
      rw [hT₁, hT₂]
    · intro i hi j
      by_cases hij : (i, j) ∈ γ
      · refine eq_entry_of_map_row T₁ T₂ i j ?_
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
          suffices T i j ≥ i by omega
          exact entry_ge_col hij

        simp [Multiset.count_map]
        simp [Multiset.ext, Multiset.count_map] at hT
        specialize hT (a-1)
        suffices ∀ T : SemistandardYoungTableau γ,
            (Multiset.filter (fun x ↦ a = T x.1 x.2 ∧ x.1 = 1) γ.cells.val).card =
            (Multiset.filter (fun x ↦ a - 1 = T x.1 x.2 - 1 ∧ x.1 = 1) γ.cells.val).card by
          rw [this T₁, this T₂, hT]
        clear hT hT₁ T₁ hT₂ T₂
        intro T
        rw [
          ← Multiset.toFinset_card_eq_card_iff_nodup.mpr <| Multiset.Nodup.filter _ γ.cells.nodup,
          ← Multiset.toFinset_card_eq_card_iff_nodup.mpr <| Multiset.Nodup.filter _ γ.cells.nodup]
        refine Finset.card_bijective id Function.bijective_id ?_
        intro x
        simp only [Multiset.toFinset_filter, Finset.val_toFinset, Finset.mem_filter, mem_cells,
          id_eq, and_congr_right_iff, and_congr_left_iff]
        intro hx hx1
        suffices T x.1 x.2 ≥ 1 by omega
        rw [← hx1]
        exact entry_ge_col hx
      · rw [T₁.zeros hij, T₂.zeros hij]
  · simp [e]
    intro L hL
    let M := Multiset.map (· + 1) L.val
    have hM : M ≤ μ.fromCounts := by
      rw [Multiset.le_iff_count]
      intro a
      by_cases ha : a < μ.card
      · simp only [Sym.val_eq_coe, Multiset.count_map, Multiset.count_fromCounts ha, ge_iff_le, M]
        have hmf : (Multiset.filter (fun b ↦ a = b + 1) L.val).card ≤ p := by
          have hLp : p = L.val.card := by simp
          conv => rhs; rw [hLp]
          refine Multiset.card_le_card ?_
          simp
        refine le_trans hmf ?_
        refine le_trans hp ?_
        refine min_el_le' hμ ?_
        have hmm : (μ.toList.mergeSort (· ≥ ·))[a]'(by simp [ha]) ∈
            μ.toList.mergeSort (· ≥ ·) := List.getElem_mem _
        rw [List.mem_mergeSort, Multiset.mem_toList] at hmm
        exact hmm
      · suffices Multiset.count a M = 0 by simp [this]
        simp only [Sym.val_eq_coe, Multiset.count_eq_zero, Multiset.mem_map, Sym.mem_coe,
          not_exists, not_and, M]
        intro x hx
        suffices x < μ.card - 1 by omega
        apply List.mem_of_mem_of_mem_sym hx at hL
        rw [List.mem_range] at hL
        exact hL
    have hnp : p ≤ n - p := by
        rw [← hr0, ← hr1]
        exact γ.rowLen_anti 0 1 zero_le_one
    have hμn : μ.fromCounts.card = n := by
      simp only [Multiset.fromCounts_card, ← h, card_eq_sum_rowLens, h2, List.sum_cons,
        List.sum_nil, add_zero]
      omega
    have hMp : M.card = p := by simp [M]
    use (twoRowTableau hr0 hr1 hc0 μ.fromCounts M hM hμn hMp ?_)
    swap
    · intro i hi r hr
      simp [M] at hr
      suffices ((μ.fromCounts - M).toList.mergeSort (· ≤ ·))[i]'(by
          simp [Multiset.card_sub hM, hMp, hμn]; omega) = 0 by
        rw [this]
        omega
      rw [← Nat.le_zero]
      refine sorted_le_of_exists_set _ (List.sorted_mergeSort' _ _) i _ 0 ?_
      use Multiset.filter (fun x ↦ 0 = x) (μ.fromCounts - M)
      constructor; swap; constructor
      · rw [← Multiset.count_eq_card_filter_eq, Multiset.count_sub,
          Multiset.count_fromCounts (Nat.pos_iff_ne_zero.mpr hμc),
          show Multiset.count 0 M = 0 by simp [M]]
        have hmm : (μ.toList.mergeSort (· ≥ ·))[0]'
            (by simp; exact Nat.pos_iff_ne_zero.mpr hμc) ∈
            μ.toList.mergeSort (· ≥ ·) := List.getElem_mem _
        rw [List.mem_mergeSort, Multiset.mem_toList] at hmm
        apply min_el_le' hμ at hmm
        omega
      · intro s
        rw [Multiset.mem_filter]
        omega
      · rw [Multiset.le_iff_count]
        intro a
        rw [Multiset.coe_count, List.Perm.count_eq (List.mergeSort_perm _ _),
          ← Multiset.coe_count, Multiset.coe_toList]
        exact Multiset.count_le_of_le a (Multiset.filter_le _ _)

    constructor
    · simp [SemistandardYoungTableauWithContent]
    · simp [map_twoRow_eq_row2_sub_one]
      suffices Multiset.map (· - 1) M = L.val by simp [this]; rfl
      simp [M]

theorem kostka_ineq_two_rows (h2 : γ.rowLens = [n - p, p]) (hn : n ≥ 5)
    (hp0 : p ≠ 0) (hγ : γ.card = n) (h : γ.card = μ.sum) (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    (hp : p ≤ min_el μ hμ) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  by_cases hp1 : p = 1
  · suffices γ = hookDiagram n by exact kostka_ineq_hook (by omega) this h h0
    rw [← rowLens_eq_iff, h2, hookDiagram_rowLens (by omega), hp1]
  have hp2 : p ≥ 2 := by omega
  by_cases hm1 : μ.card = 1
  · rw [Multiset.card_eq_one] at hm1
    obtain ⟨m, hm⟩ := hm1
    have h' := h
    rw [hm, Multiset.sum_singleton, hγ] at h'
    rw [← h'] at hm
    refine kostka_ineq_singleton ?_ hm h
    rw [ne_eq, ← rowLens_eq_iff, h2, horizontalDiagram_rowLens]
    · simp only [List.cons.injEq, List.cons_ne_self, and_false, not_false_eq_true]
    · omega
  have hm2 : μ.card ≥ 2 := by
    suffices μ.card ≠ 0 by omega
    rw [ne_eq, Multiset.card_eq_zero]
    exact hμ

  have hlpn : n ≥ μ.card * p := by
    rw [← hγ, h]
    refine le_trans (Multiset.card_nsmul_le_sum ?_) (by rfl)
    intro x hx
    exact le_trans hp (min_el_le' hμ hx)

  have hfl := factorial_lemma n μ.card p hn hp2 hm2 hlpn
  rw [kostka_two_rows h2 hn h hμ h0 hp,
    Nat.choose_eq_factorial_div_factorial (by omega),
    show p + μ.card - 2 - p = μ.card - 2 by omega]
  refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) ?_
  refine Nat.div_le_of_le_mul ?_
  have hf := kostka_replicate_two_rows h2 hn hp0 hγ
  conv at hfl => rhs; lhs; lhs; rw [mul_assoc, ← hf]
  have hpnf : (Nat.factorial p) * Nat.factorial (n-p+1) > 0 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpnf
  rw [← mul_assoc]
  refine le_trans hfl ?_
  ring_nf
  rfl
