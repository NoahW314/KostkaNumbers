import Mathlib

-- Some results about Lists and Multisets that I need but don't appear to be in Mathlib


lemma downwardStrongInduction (p : ℕ × ℕ → Prop) (x : ℕ × ℕ) (n : ℕ) (hxm : x.1 < n)
    (ind : ∀ z : ℕ × ℕ, z.1 < n → (∀ w : ℕ × ℕ, w.1 > z.1 → w.1 < n → p w) → p z) : p x := by
  contrapose! ind
  let S := { i : ℕ | i < n ∧ ∃ j : ℕ, ¬ p (i, j)}
  have hsbdd : BddAbove S := by
    rw [bddAbove_def]; use n; intro i hi
    unfold S at hi; rw [Set.mem_setOf] at hi
    exact le_of_lt hi.1
  have hS : sSup S ∈ S := by
    refine Nat.sSup_mem ?_ hsbdd

    use x.1; unfold S; rw [Set.mem_setOf]
    constructor
    exact hxm
    use x.2
  conv  at hS => lhs; unfold S
  rw [Set.mem_setOf] at hS
  obtain ⟨hS, ⟨j, hj⟩⟩ := hS
  use (sSup S, j)
  simp only [hS, gt_iff_lt, Prod.forall, hj, not_false_eq_true, and_true, true_and]

  intro a b ha han
  suffices a ∉ S by
    simp [S, han] at this
    exact this b
  exact notMem_of_csSup_lt ha hsbdd

namespace List

-- we can prove a result about a list by building it up
-- the key difference between this and normal induction on a list
--   is that we only need the inductive step for this particular list
--   this is needed, because we will want to assume that the list is sorted later
lemma induction_build {α : Type*} {p : List α → Prop} (L : List α)
    (empty : p []) (build : ∀ i : ℕ, (h : i < L.length) → p (List.take i L) →
    p (List.take (i + 1) L)) : p L := by
  suffices ∀ i ≤ L.length, p (List.take i L) by
    specialize this L.length (by rfl)
    rw [List.take_length] at this
    exact this

  intro i hi
  induction' i with i ih
  · rw [List.take_zero]; exact empty
  · apply build i
    · omega
    · apply ih
      omega


lemma take_coe {le : ℕ → ℕ → Bool} (l : List ℕ)
    (trans : ∀ a b c : ℕ, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b : ℕ, le a b || le b a) [IsAntisymm ℕ (fun a b => le a b)]
    (h : List.Sorted (fun a b => le a b) l) {i : ℕ} (hi : i < l.length) :
    List.take (i + 1) l =
    (Multiset.ofList (l[i] :: (List.take i l))).toList.mergeSort le := by
  suffices (List.take (i + 1) l).Perm (Multiset.ofList (l[i] :: (List.take i l))).toList by
    apply List.eq_of_perm_of_sorted ?_ ?_ (List.sorted_mergeSort trans total _)
    apply List.Perm.trans this
    apply List.Perm.symm
    apply List.mergeSort_perm
    unfold List.Sorted
    apply List.Pairwise.take h
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, Multiset.coe_eq_coe]
  rw [← List.take_append_getElem hi]
  exact List.perm_append_singleton l[i] (List.take i l)


lemma append_sorted (L : List ℕ) (hL : List.Sorted (· ≤ ·) L) {n : ℕ} (h : ∀ m ∈ L, m ≤ n) :
    List.Sorted (· ≤ ·) (L ++ [n]) := by
  unfold List.Sorted
  rw [List.pairwise_append]
  constructor; swap; constructor
  · exact List.pairwise_singleton (fun x1 x2 ↦ x1 ≤ x2) n
  · simp; exact h
  · exact hL


lemma cons_sort_eq_sort_append (M : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ M, m ≤ n) :
    (n ::ₘ M).toList.mergeSort (· ≤ ·) = M.toList.mergeSort (· ≤ ·) ++ [n] := by
  apply List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _)

  · apply append_sorted _ (List.sorted_mergeSort' _ _)
    simp; exact h

  apply List.Perm.trans (List.mergeSort_perm (n ::ₘ M).toList _)
  apply List.Perm.symm
  apply List.Perm.trans (List.perm_append_singleton _ _)
  apply List.Perm.symm
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.cons_inj_right]
  nth_rw 1 [← Multiset.coe_toList M]
  rw [Multiset.coe_eq_coe]
  apply List.Perm.symm
  apply List.mergeSort_perm


lemma getElem_map_range {j : ℕ} (n : ℕ) (f : ℕ → ℕ)
    (hj : j < n) (hn : n = (List.map f (List.range n)).length)
    : f j = (List.map f (List.range n))[j]'(by omega) := by
  simp only [List.getElem_map, List.getElem_range]


lemma coe_ofList_sorted {L : List ℕ} (h : L.Sorted (· ≥ ·)) :
    (Multiset.ofList L).toList.mergeSort (· ≥ ·) = L := by
  refine List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _) h
  refine List.Perm.trans (List.mergeSort_perm _ _) ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]


end List




namespace Multiset

-- version of induction on multisets.  The difference between this and the normal induction
--   on multisets is that here we can assume that the element we are working with is
--   as least as large as all the other elements
theorem induction_on_with_rel {p : Multiset ℕ → Prop} (S : Multiset ℕ)
    (le : ℕ → ℕ → Bool) (trans : ∀ a b c : ℕ, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b : ℕ, le a b || le b a) [IsAntisymm ℕ (fun a b => le a b)] (empty : p 0)
    (cons : ∀ {n : ℕ} {s : Multiset ℕ}, n ∈ S → s ⊆ S → (∀ m ∈ s, le m n) → p s → p (n ::ₘ s)) :
    p S := by
  let p' : List ℕ → Prop := fun L => p (Multiset.ofList L)
  have hp : ∀ T : Multiset ℕ, p T ↔ p' ((T.toList).mergeSort le) := by
    intro T
    suffices Multiset.ofList T.toList = Multiset.ofList (T.toList.mergeSort le) by
      simp [p', ← this]
    symm; rw [coe_eq_coe]
    apply List.mergeSort_perm
  rw [hp]
  apply List.induction_build
  · simp [p', empty]
  · intro i hi hs
    have hsi : (S.toList.mergeSort le).get ⟨i, hi⟩ ∈ S.toList.mergeSort le := by
      exact List.get_mem (S.toList.mergeSort le) ⟨i, hi⟩
    have hss : Multiset.ofList (List.take i (S.toList.mergeSort le)) ⊆ S := by
      intro a ha;
      rw [mem_coe, List.mem_take_iff_getElem] at ha
      obtain ⟨j, ⟨hj, ha⟩⟩ := ha
      rw [← ha, ← mem_toList]
      apply List.mem_mergeSort.mp (List.get_mem _ _)
    rw [List.mem_mergeSort, mem_toList] at hsi
    specialize cons hsi hss ?_ ?_
    · intro m hm
      rw [mem_coe, List.mem_take_iff_getElem] at hm
      obtain ⟨j, ⟨hj, hm⟩⟩ := hm
      rw [← hm, List.get_eq_getElem]
      apply List.Sorted.rel_get_of_lt (List.sorted_mergeSort trans total S.toList)
      simp; omega
    · simp [p'] at hs; exact hs
    simp only [List.get_eq_getElem, cons_coe, hp] at cons
    suffices List.take (i + 1) (S.toList.mergeSort le) =
        (Multiset.ofList ((S.toList.mergeSort le)[i] ::
        (List.take i (S.toList.mergeSort le)))).toList.mergeSort le by
      rw [this]; exact cons
    apply List.take_coe _ trans total
    apply List.sorted_mergeSort trans total

theorem induction_on_with_le {p : Multiset ℕ → Prop} (S : Multiset ℕ) (empty : p 0)
    (cons : ∀ {n : ℕ} {s : Multiset ℕ}, n ∈ S → s ⊆ S → (∀ m ∈ s, m ≤ n) → p s → p (n ::ₘ s)) :
    p S := by
  apply induction_on_with_rel S (· ≤ ·) ?_ ?_ empty ?_
  · simp; intro a b c
    exact Nat.le_trans
  · simp
    intro a b
    exact Nat.le_total a b
  · simp; exact cons

theorem induction_on_with_ge {p : Multiset ℕ → Prop} (S : Multiset ℕ) (empty : p 0)
    (cons : ∀ {n : ℕ} {s : Multiset ℕ}, n ∈ S → s ⊆ S → (∀ m ∈ s, m ≥ n) → p s → p (n ::ₘ s)) :
    p S := by
  apply induction_on_with_rel S (· ≥ ·) ?_ ?_ empty ?_
  · simp; intro a b c
    exact fun a_1 a_2 ↦ Nat.le_trans a_2 a_1
  · simp
    intro a b
    exact Nat.le_total b a
  · simp; exact cons



lemma replicate_dedup {α : Type*} [DecidableEq α] (a : α) (n : ℕ) (h : n ≠ 0) :
    (replicate n a).dedup = {a} := by
  ext b
  by_cases hab : a = b
  · simp [hab, mem_replicate, h]
  · push_neg at hab; symm at hab
    simp [hab, mem_replicate]

section Remove

variable {α : Type*} [DecidableEq α]

def remove (S : Multiset α) (a : α) := S - (replicate (count a S) a)

@[simp] lemma remove_bot {a : α} : remove (⊥ : Multiset α) a = ⊥ := by
  simp [remove]

@[simp] lemma notMem_of_remove (S : Multiset α) (a : α) : a ∉ S.remove a := by
  rw [remove, ← count_eq_zero, count_sub, count_replicate]
  simp

lemma remove_of_notMem (S : Multiset α) (a : α) (ha : a ∉ S) : S.remove a = S := by
  rw [← count_pos, Nat.pos_iff_ne_zero] at ha; push_neg at ha
  rw [remove, ha, replicate_zero, Multiset.sub_zero]

lemma mem_remove_of_ne (S : Multiset α) {a b : α} (h : a ≠ b) : b ∈ S.remove a ↔ b ∈ S := by
  simp [remove, mem_sub, count_replicate, h, count_pos]

lemma mem_remove_of_mem_ne {S : Multiset α} {a b : α} (h : b ∈ S) (hab : a ≠ b) :
    b ∈ S.remove a := by
  exact (mem_remove_of_ne S hab).mpr h

lemma mem_remove_of_mem {S : Multiset α} (a b : α) (h : b ∈ S) : b ∈ S.remove a ↔ a ≠ b := by
  constructor
  · contrapose!; intro hab; rw [hab]; exact notMem_of_remove S b
  · intro hab
    exact mem_remove_of_mem_ne h hab

lemma mem_of_mem_remove {S : Multiset α} (a b : α) (h : b ∈ S.remove a) : b ∈ S := by
  rw [← count_pos]
  rw [remove, mem_sub] at h
  exact lt_of_le_of_lt (Nat.zero_le _) h


lemma insert_remove_toFinset (S : Multiset α) (a : α) (ha : a ∈ S) : S.toFinset =
    insert a (S.remove a).toFinset := by
  ext x
  rw [mem_toFinset, Finset.mem_insert]
  constructor
  · intro h
    by_cases hx0 : x = a
    · left; exact hx0
    right
    rw [mem_toFinset, remove, mem_sub, count_replicate]
    push_neg at hx0; symm at hx0
    simp [hx0]
    exact count_pos.mpr h
  · intro h
    by_cases hx0 : x = a
    · rw [hx0]; exact ha
    · push_neg at hx0
      simp only [hx0] at h
      rw [false_or, mem_toFinset, remove, mem_sub, count_replicate] at h
      symm at hx0
      simp [hx0] at h
      exact count_pos.mp h

lemma remove_toFinset (S : Multiset α) (a : α) :
    (S.remove a).toFinset = S.toFinset.erase a := by
  by_cases ha : a ∈ S
  · rw [insert_remove_toFinset S a ha, Finset.erase_insert]
    rw [mem_toFinset]
    exact notMem_of_remove S a
  · rw [remove_of_notMem S a ha, Finset.erase_eq_of_notMem]
    rw [mem_toFinset]
    exact ha

lemma remove_toFinset_card (S : Multiset α) (a : α) (ha : a ∈ S) :
    (S.remove a).toFinset.card = S.toFinset.card - 1 := by
  rw [remove_toFinset S a, Finset.card_erase_of_mem]
  rw [mem_toFinset]
  exact ha

lemma remove_zero_sum (μ : Multiset ℕ) : μ.sum = (μ.remove 0).sum := by
  by_cases h0 : 0 ∉ μ
  · rw [remove_of_notMem μ 0 h0]

  push_neg at h0
  simp [Finset.sum_multiset_count, remove, count_replicate]
  rw [insert_remove_toFinset μ 0 h0, Finset.sum_insert_zero]
  · refine Finset.sum_congr (rfl) ?_
    intro x hx
    rw [mem_toFinset] at hx
    have hx0 : 0 ≠ x := by
      contrapose! hx
      rw [← hx, ← remove]
      exact notMem_of_remove μ 0
    simp [hx0]
  · rw [mul_zero]



end Remove


section Counts

variable {α : Type*} [DecidableEq α]

def counts (M : Multiset α) : Multiset ℕ :=
  Multiset.map (fun x : α => Multiset.count x M) M.dedup

@[simp] lemma zero_notMem_counts {M : Multiset α} : 0 ∉ M.counts := by simp [counts]

@[simp] lemma counts_pos {M : Multiset α} : ∀ n ∈ M.counts, n > 0 := by
  intro n; rw [gt_iff_lt, Nat.pos_iff_ne_zero]
  contrapose!; intro h; rw [h]; exact zero_notMem_counts

lemma bot_counts_iff {M : Multiset ℕ} : M.counts = ⊥ ↔ M = ⊥ := by
  simp [counts, dedup_eq_zero]

lemma sum_counts_eq_card (M : Multiset ℕ) : Multiset.sum M.counts = M.card := by
  simp [counts]
  rw [Finset.sum_multiset_map_count]
  simp [Multiset.count_dedup]
  have hms : ∀ a ∈ M, a ∈ M.toFinset := by simp
  rw [← Multiset.sum_count_eq_card hms]
  apply Finset.sum_congr (rfl)
  intro x hx; rw [mem_toFinset] at hx
  simp only [hx, reduceIte]

lemma counts_card (M : Multiset ℕ) : M.counts.card = M.toFinset.card := by
  simp [counts]
  exact rfl

lemma counts_replicate (n a : ℕ) (hn : n ≠ 0) : (Multiset.replicate n a).counts = {n} := by
  simp only [counts, count_replicate]
  refine map_eq_singleton.mpr ?_
  use a; constructor
  · rw [← nsmul_singleton]
    rw [dedup_nsmul hn, dedup_singleton]
  · simp

lemma replicate_add_counts_of_notMem {a : α} {M : Multiset α} (h : a ∉ M) (n : ℕ) (hn : n ≠ 0) :
    ((replicate n a) + M).counts = M.counts + {n} := by
  simp [counts, count_replicate]
  ext m
  rw [count_add, count_map, count_map]
  rw [Disjoint.dedup_add, replicate_dedup a n hn, filter_add, card_add, add_comm]
  · by_cases hmn : m = n
    · simp [hmn]
      · congr 2
        · refine filter_congr ?_
          intro x hx
          rw [mem_dedup] at hx
          have hax : a ≠ x := by contrapose! h; rw [h]; exact hx
          simp [hax]
        · rw [card_eq_one]; use a
          rw [filter_eq_self]
          simp [h]
    · rw [← count_pos, Nat.pos_iff_ne_zero] at h; push_neg at h
      simp [hmn, filter_singleton, h]
      congr 1
      refine filter_congr ?_
      intro x hx
      rw [mem_dedup] at hx
      have hax : a ≠ x := by
        rw [← count_pos, Nat.pos_iff_ne_zero] at hx
        contrapose! hx
        rw [← hx]; exact h
      simp [hax]
  · refine disjoint_left.mpr ?_
    intro b hb
    rw [mem_replicate] at hb
    simp only [ne_eq, hn, not_false_eq_true, true_and] at hb
    rw [hb]; exact h



variable {μ : Multiset ℕ}


theorem exists_fromCounts (μ : Multiset ℕ) : 0 ∉ μ → ∃ M : Multiset ℕ,
    M.counts = μ ∧ (List.Sorted (· ≥ ·) <|
    List.map (fun n => Multiset.count n M) (List.range μ.card)) ∧
    (∀ n < μ.card, n ∈ M) ∧ (∀ n ≥ μ.card, n ∉ M) := by
  apply induction_on_with_ge μ
  · intro h0
    use 0; constructor
    · rw [← bot_eq_zero, bot_counts_iff]
    · simp
  · intro a s _ _ ha ih h0
    have h0s : 0 ∉ s := by
      contrapose! h0
      exact mem_cons_of_mem h0
    obtain ⟨M, hs, hsort, hM, hM'⟩ := ih h0s
    let b := s.card
    have hb : b ∉ M := by refine hM' b ?_; rfl
    use ((replicate a b) + M)
    constructor
    · rw [replicate_add_counts_of_notMem hb a, hs, add_comm, singleton_add]
      rw [mem_cons, not_or] at h0
      symm; exact h0.1
    constructor
    · suffices List.map (fun n ↦ count n (replicate a b + M)) (List.range (a ::ₘ s).card) =
          (List.map (fun n ↦ count n M) (List.range s.card)) ++ [a] by
        rw [this, List.Sorted, List.pairwise_append]
        constructor; swap; constructor
        · exact List.pairwise_singleton (fun x1 x2 ↦ x1 ≥ x2) a
        · intro m hm a' ha'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
          rw [ha']
          refine ha m ?_
          rw [← hs, counts, mem_map]
          rw [List.mem_map] at hm
          obtain ⟨n, hns, hnm⟩ := hm
          use n; constructor
          · rw [List.mem_range] at hns
            rw [mem_dedup]
            exact hM n hns
          · exact hnm
        · exact hsort
      rw [List.map_eq_append_iff]
      use List.range (s.card); use [s.card]
      constructor
      · rw [card_cons, List.range_succ]
      constructor
      · refine List.map_congr_left ?_
        intro n hn
        rw [List.mem_range] at hn
        rw [count_add, count_replicate]
        apply ne_of_lt at hn
        symm at hn
        simp [b, hn]
      · simp [count_replicate, b, hb]
    constructor
    · rw [card_cons]
      intro n hn
      by_cases hn' : n = s.card
      · rw [mem_add, mem_replicate, hn']; left
        constructor;
        · rw [mem_cons, not_or] at h0
          symm; exact h0.1
        · rfl
      rw [mem_add]; right
      refine hM n ?_
      omega
    · rw [card_cons]
      intro n hn
      rw [mem_add, not_or, mem_replicate, not_and_or]
      constructor
      · right; omega
      · refine hM' n ?_
        omega


noncomputable
def fromCounts (μ : Multiset ℕ) := Classical.choose
  (exists_fromCounts (μ.remove 0) (notMem_of_remove μ 0))



lemma fromCounts_sorted (μ : Multiset ℕ) : List.Sorted (· ≥ ·) <|
    List.map (fun n => Multiset.count n μ.fromCounts) (List.range (μ.remove 0).card) := by
  let h := Classical.choose_spec (exists_fromCounts (μ.remove 0) (notMem_of_remove μ 0))
  exact h.2.1



lemma fromCounts_counts (hμ : 0 ∉ μ) : μ.fromCounts.counts = μ := by
  let h := Classical.choose_spec (exists_fromCounts (μ.remove 0) (notMem_of_remove μ 0))
  rw [fromCounts, h.1]
  exact remove_of_notMem μ 0 hμ


lemma mem_fromCounts (μ : Multiset ℕ) (n : ℕ) (hn : n < (μ.remove 0).card) : n ∈ μ.fromCounts := by
  let h := Classical.choose_spec (exists_fromCounts (μ.remove 0) (notMem_of_remove μ 0))
  exact h.2.2.1 n hn

lemma notMem_fromCounts (μ : Multiset ℕ) (n : ℕ) (hn : n ≥ (μ.remove 0).card) :
    n ∉ μ.fromCounts := by
  let h := Classical.choose_spec (exists_fromCounts (μ.remove 0) (notMem_of_remove μ 0))
  exact h.2.2.2 n hn


lemma fromCounts_eq_remove_zero_fromCounts : μ.fromCounts = (μ.remove 0).fromCounts := by
  simp [fromCounts, remove]


@[simp] lemma fromCounts_card : μ.fromCounts.card = μ.sum := by
  rw [← sum_counts_eq_card μ.fromCounts]
  rw [fromCounts_eq_remove_zero_fromCounts]
  rw [fromCounts_counts (notMem_of_remove μ 0), ← remove_zero_sum]

@[simp] lemma fromCounts_zero : fromCounts 0 = 0 := by
  rw [← Multiset.bot_eq_zero, ← bot_counts_iff]
  refine fromCounts_counts ?_
  rw [bot_eq_zero]
  exact notMem_zero 0

@[simp] lemma fromCounts_bot : fromCounts ⊥ = ⊥ := by simp



lemma range_eq_dedup (M : Multiset ℕ) {m : ℕ} (hmem : ∀ n < m, n ∈ M) (hnmem : ∀ n ≥ m, n ∉ M) :
    range m = M.dedup := by
  ext n
  rw [count_eq_of_nodup (nodup_dedup M), count_eq_of_nodup (nodup_range m)]
  by_cases hn : n ∈ range m
  · simp only [hn, ↓reduceIte, mem_dedup, left_eq_ite_iff, one_ne_zero, imp_false,
      Decidable.not_not]
    rw [mem_range] at hn
    exact hmem n hn
  · simp only [hn, ↓reduceIte, mem_dedup, right_eq_ite_iff, zero_ne_one, imp_false]
    rw [mem_range] at hn; push_neg at hn
    exact hnmem n hn

lemma count_fromCounts {μ : Multiset ℕ} {n : ℕ} (h : n < μ.card) (h0 : 0 ∉ μ) :
    Multiset.count n μ.fromCounts = (μ.toList.mergeSort (· ≥ ·))[n]'(by simp[h]) := by
  suffices (List.map (fun n => Multiset.count n μ.fromCounts) (List.range (μ.remove 0).card)) =
      (μ.toList.mergeSort (· ≥ ·)) by
    simp [← this]
  refine List.eq_of_perm_of_sorted ?_ (Multiset.fromCounts_sorted μ) (List.sorted_mergeSort' _ _)
  refine List.Perm.symm ?_
  refine List.Perm.trans (List.mergeSort_perm μ.toList (· ≥ ·)) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_range]
  nth_rw 1 [← Multiset.fromCounts_counts h0, Multiset.counts]
  refine Multiset.map_congr ?_ (by exact fun x a ↦ rfl)
  rw [Multiset.range_eq_dedup μ.fromCounts (Multiset.mem_fromCounts μ)
    (Multiset.notMem_fromCounts μ)]


theorem eq_fromCounts_iff (M μ : Multiset ℕ) (h0 : 0 ∉ μ) : M = μ.fromCounts ↔
    M.counts = μ ∧ (List.Sorted (· ≥ ·) <|
    List.map (fun n => Multiset.count n M) (List.range (μ.remove 0).card)) ∧
    (∀ n < μ.card, n ∈ M) ∧ (∀ n ≥ μ.card, n ∉ M) := by
  constructor
  · intro h
    rw [← remove_of_notMem μ 0 h0, h, fromCounts]
    nth_rw 10 [remove_of_notMem μ 0 h0]
    exact Classical.choose_spec (exists_fromCounts (μ.remove 0) (notMem_of_remove μ 0))


  intro ⟨h1, h2, h3, h4⟩

  rw [← remove_of_notMem μ 0 h0] at h3
  rw [← remove_of_notMem μ 0 h0] at h4
  suffices (List.map (fun n ↦ count n M) (List.range (μ.remove 0).card)) =
      (List.map (fun n ↦ count n μ.fromCounts) (List.range (μ.remove 0).card)) by
    ext n
    by_cases hn : n ≥ (μ.remove 0).card
    · specialize h4 n hn
      rw [← count_pos, Nat.pos_iff_ne_zero] at h4; push_neg at h4
      symm; rw [h4, count_eq_zero]
      exact notMem_fromCounts μ n hn
    · push_neg at hn
      have count_get : count n M = (List.map (fun n ↦ count n M)
          (List.range (μ.remove 0).card))[n]'(by simp [hn]) := by
        simp
      simp [count_get, this]
  refine List.eq_of_perm_of_sorted ?_ h2 (fromCounts_sorted μ)
  rw [← coe_eq_coe, ← map_coe, ← map_coe, coe_range]
  nth_rw 1 [range_eq_dedup M h3 h4]
  rw [range_eq_dedup μ.fromCounts (mem_fromCounts μ) (notMem_fromCounts μ)]
  rw [← counts, ← counts, fromCounts_counts h0]
  exact h1


lemma remove_fromCounts_remove_counts_card :
    ((μ.remove 0).fromCounts.remove 0).toFinset.card =
    (μ.remove 0).card - 1 := by
  by_cases h0 : (μ.remove 0).card = 0
  · rw [card_eq_zero] at h0
    simp [h0]; simp [← bot_eq_zero]

  · rw [remove_toFinset_card]
    · nth_rw 2 [← fromCounts_counts (notMem_of_remove μ 0)]
      rw [counts_card]
    · rw [← fromCounts_eq_remove_zero_fromCounts]
      push_neg at h0; rw [← Nat.pos_iff_ne_zero] at h0
      exact mem_fromCounts μ 0 h0

end Counts


end Multiset
