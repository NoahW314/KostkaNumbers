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
