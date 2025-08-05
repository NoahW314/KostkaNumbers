import Mathlib
import KostkaNumbers.Util


def Dominates (L L' : List ℕ) := ∀ r : ℕ, ∑ i : Fin L.length with i.1 ≤ r,
  L.get i ≥ ∑ i : Fin L'.length with i.1 ≤ r, L'.get i

notation L " ⊵ " L' => Dominates L L'
notation L " ⊴ " L' => Dominates L' L


lemma get_zero_ge_of_dominates {L L' : List ℕ} (h : L ⊵ L') (hL : 0 < L.length)
    (hL' : 0 < L'.length) : L[0] ≥ L'[0] := by
  specialize h 0
  have hL0 : Finset.filter (fun i : Fin L.length => i.1 ≤ 0) Finset.univ = {⟨0, hL⟩} := by
    ext x; simp [Fin.eq_mk_iff_val_eq]
  have hL'0 : Finset.filter (fun i : Fin L'.length => i.1 ≤ 0) Finset.univ = {⟨0, hL'⟩} := by
    ext x; simp [Fin.eq_mk_iff_val_eq]
  rw [hL0, hL'0, Finset.sum_singleton, Finset.sum_singleton,
    List.get_eq_getElem, List.get_eq_getElem] at h
  exact h

lemma lengths_le_of_dominates {L L' : List ℕ} (hd : L ⊵ L') (h : L.sum = L'.sum)
    (hp : ∀ i, L.get i > 0) :
    L.length ≤ L'.length := by
  by_cases h0 : L'.length = 0
  · rw [h0]
    suffices Multiset.ofList L = 0 by
      simp at this
      simp [this]
    rw [← Multiset.sum_eq_zero_iff_eq_zero, Multiset.sum_coe, h]
    · simp only [List.length_eq_zero_iff] at h0
      rw [h0, List.sum_nil]
    · contrapose! hp
      rw [Multiset.mem_coe] at hp
      apply List.get_of_mem at hp
      obtain ⟨i, hi⟩ := hp
      use i; rw [hi]

  contrapose! h
  specialize hd (L'.length-1)
  symm
  refine ne_of_lt ?_
  simp only [List.get_eq_getElem, ge_iff_le] at hd
  have hLs : L'.sum = ∑ x : Fin L'.length with x.1 ≤ L'.length - 1, L'[x.1] := by
    rw [← Fin.sum_univ_getElem]
    congr
    ext x
    simp only [Finset.mem_univ, Finset.mem_filter, true_and, true_iff]
    exact Nat.le_sub_one_of_lt x.2
  rw [hLs]
  refine lt_of_le_of_lt hd ?_
  rw[← Fin.sum_univ_getElem]
  let i := (⟨L.length-1, by exact Nat.sub_one_lt_of_lt h⟩ : Fin L.length)
  refine Finset.sum_lt_sum_of_subset ?_ (Finset.mem_univ i) ?_ ?_ ?_
  · simp
  · simp [i]
    refine lt_of_le_of_lt ?_ h
    refine le_of_eq ?_
    exact Nat.succ_pred_eq_of_ne_zero h0
  · rw [← List.get_eq_getElem]
    exact hp i
  · simp

lemma sum_two_le_of_dominates {L L' : List ℕ} (hd : L ⊴ L')
  (hL : 1 < L.length) (hL' : 1 < L'.length) : L[0] + L[1] ≤ L'[0] + L'[1] := by
  specialize hd 1
  simp at hd
  have hL1 : Finset.filter (fun i : Fin L.length => i.1 ≤ 1) Finset.univ =
      {⟨0, by omega⟩, ⟨1, hL⟩} := by
    ext x
    simp [Fin.eq_mk_iff_val_eq]
    exact Nat.le_one_iff_eq_zero_or_eq_one
  have hL'1 : Finset.filter (fun i : Fin L'.length => i.1 ≤ 1) Finset.univ =
      {⟨0, by omega⟩, ⟨1, hL'⟩} := by
    ext x
    simp [Fin.eq_mk_iff_val_eq]
    exact Nat.le_one_iff_eq_zero_or_eq_one
  rw [hL1, hL'1] at hd
  simp at hd
  exact hd

lemma dominates_self {L : List ℕ} : L ⊴ L := by intro r; rfl

lemma dominates_of_max_length_eq_zero {L L' : List ℕ} (h : max L.length L'.length = 0) :
    L ⊴ L' := by
  suffices L = L' by rw [this]; exact dominates_self
  rw [← Nat.le_zero, Nat.max_le, Nat.le_zero, Nat.le_zero, List.length_eq_zero_iff,
    List.length_eq_zero_iff] at h
  rw [h.1, h.2]

lemma sum_with_eq_sum_with_length {L : List ℕ} {r : ℕ} (hr : r ≥ L.length - 1) :
    ∑ i : Fin L.length with i.1 ≤ r, L.get i =
    ∑ i : Fin L.length with i.1 ≤ L.length - 1, L.get i := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hi
    exact Nat.le_trans hi hr
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, List.get_eq_getElem]
    intro x hx hxl
    omega

lemma sum_with_eq_sum_with {L : List ℕ} {r s : ℕ} (hr : r ≥ L.length - 1) (hs : s ≥ L.length - 1) :
    ∑ i : Fin L.length with i.1 ≤ r, L.get i =
    ∑ i : Fin L.length with i.1 ≤ s, L.get i := by
  rw [sum_with_eq_sum_with_length hr, sum_with_eq_sum_with_length hs]

lemma dominates_of_forall_le_max {L L' : List ℕ} (h : ∀ r < max L.length L'.length,
    ∑ i : Fin L.length with i.1 ≤ r, L.get i ≤
    ∑ i : Fin L'.length with i.1 ≤ r, L'.get i) : L ⊴ L' := by
  by_cases hle : max L.length L'.length = 0
  · exact dominates_of_max_length_eq_zero hle

  intro r
  by_cases hr : r < max L.length L'.length
  · exact h r hr
  · specialize h ((max L.length L'.length) - 1) (Nat.sub_one_lt hle)
    push_neg at hr
    rw [Nat.max_le] at hr
    obtain ⟨hrL, hrL'⟩ := hr
    apply le_trans (Nat.sub_le L.length 1) at hrL
    apply le_trans (Nat.sub_le L'.length 1) at hrL'
    have hmL : max L.length L'.length - 1 ≥ L.length - 1 := by omega
    have hmL' : max L.length L'.length - 1 ≥ L'.length - 1 := by omega
    rw [sum_with_eq_sum_with hrL hmL, sum_with_eq_sum_with hrL' hmL']
    exact h

lemma sum_with_eq_sum_univ {L : List ℕ} (r : ℕ) (h : r ≥ L.length - 1) :
    ∑ i, L.get i = ∑ i with i.1 ≤ r, L.get i := by
  symm
  refine Finset.sum_subset ?_ ?_
  · simp
  · simp only [Finset.mem_univ, Finset.mem_filter, true_and, not_le, List.get_eq_getElem,
      forall_const]
    intro x hx
    omega

lemma sum_le_sum_of_dominates {L L' : List ℕ} (hd : L ⊴ L') : L.sum ≤ L'.sum := by
  rw [← Fin.sum_univ_getElem, ← Fin.sum_univ_getElem]
  simp [← List.get_eq_getElem]
  rw [sum_with_eq_sum_univ (max L.length L'.length - 1) (by omega),
    sum_with_eq_sum_univ (max L.length L'.length - 1) (by omega)]
  exact hd (max L.length L'.length - 1)

/-
Small domination results
-/

lemma singleton_dominates_singleton {a b : ℕ} : ([a] ⊴ [b]) ↔ a ≤ b := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simp at h
    exact h
  · intro h
    refine dominates_of_forall_le_max ?_
    simp [h]

lemma singleton_dominates_pair {a b c : ℕ} : ([a, b] ⊴ [c]) ↔ a + b ≤ c := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simp at h
    exact h
  · intro h
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]
    · exact Nat.le_of_add_right_le h

lemma singleton_dominates_triple {a b c d : ℕ} : ([a, b, c] ⊴ [d]) ↔ a + b + c ≤ d := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simp [← add_assoc] at h
    exact h
  · intro h
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h]
    · rw [add_assoc] at h
      exact Nat.le_of_add_right_le h
    · exact Nat.le_of_add_right_le h



lemma pair_dominates_singleton {a b c : ℕ} : ([a] ⊴ [b, c]) ↔ a ≤ b := by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]
    · exact Nat.le_add_right_of_le h

lemma pair_dominates_pair {a b c d : ℕ} : ([a, b] ⊴ [c, d]) ↔ a ≤ c ∧ a + b ≤ c + d := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simp at h
      exact h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h₁, h₂]

lemma pair_dominates_triple {a b c d e : ℕ} : ([a, b, c] ⊴ [d, e]) ↔
    a ≤ d ∧ a + b + c ≤ d + e := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simp at h
      rw [add_assoc]
      exact h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂]
    · exact Nat.le_of_add_right_le h₂


lemma triple_dominates_singleton {a b c d : ℕ} : ([a] ⊴ [b, c, d]) ↔ a ≤ b := by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h, Fin.sum_univ_three]
    · exact Nat.le_add_right_of_le h
    · rw [add_assoc]
      exact Nat.le_add_right_of_le h

lemma triple_dominates_pair {a b c d e : ℕ} : ([a, b] ⊴ [c, d, e]) ↔
    a ≤ c ∧ a + b ≤ c + d := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂]
    · exact Nat.le_add_right_of_le h₂

lemma triple_dominates_triple {a b c d e f : ℕ} : ([a, b, c] ⊴ [d, e, f]) ↔
    a ≤ d ∧ a + b ≤ d + e ∧ a + b + c ≤ d + e + f := by
  constructor
  · intro h
    constructor; swap; constructor
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simp [← add_assoc] at h
      exact h
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂, h₃⟩
    refine dominates_of_forall_le_max ?_
    simp
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂, h₃]
