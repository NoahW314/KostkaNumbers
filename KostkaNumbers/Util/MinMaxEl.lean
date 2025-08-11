import Mathlib
import KostkaNumbers.Util.Util


variable {μ : Multiset ℕ}

lemma sort_ne_nil_ge (h : μ ≠ 0) : (Multiset.sort (· ≥ ·) μ) ≠ [] := by
  rw [ne_eq, List.eq_nil_iff_length_eq_zero, Multiset.length_sort, Multiset.card_eq_zero]
  exact h

def min_el (μ : Multiset ℕ) (h : μ ≠ 0) := List.getLast (Multiset.sort (· ≥ ·) μ) (sort_ne_nil_ge h)

lemma min_el_mem (hμ : μ ≠ 0) : min_el μ hμ ∈ μ := by
  rw [min_el, ← Multiset.mem_sort (· ≥ ·)]
  exact List.getLast_mem (sort_ne_nil_ge hμ)

lemma min_el_ne_zero (hμ : μ ≠ 0) (h0 : 0 ∉ μ) : min_el μ hμ ≠ 0 := by
  contrapose! h0; rw [← h0]; exact min_el_mem hμ

lemma min_el_le (hμ : μ ≠ 0) (i : Fin (Multiset.sort (· ≥ ·) μ).length) :
    min_el μ hμ ≤ (Multiset.sort (· ≥ ·) μ).get i := by
  rw [min_el, List.getLast_eq_getElem (sort_ne_nil_ge hμ), ← ge_iff_le]
  refine List.Sorted.rel_get_of_le ?_ ?_
  · exact Multiset.sort_sorted _ _
  let hi := i.2
  rw [Fin.mk_le_mk]
  exact Nat.le_sub_one_of_lt hi

lemma min_el_le' (hμ : μ ≠ 0) {a : ℕ} (ha : a ∈ μ) : min_el μ hμ ≤ a := by
  rw [← Multiset.mem_sort (· ≥ ·)] at ha
  apply List.get_of_mem at ha
  obtain ⟨i, ha⟩ := ha
  rw [← ha]
  exact min_el_le hμ i

lemma cons_erase_min_el (hμ : μ ≠ 0) : (min_el μ hμ) ::ₘ (μ.erase (min_el μ hμ)) = μ := by
  exact Multiset.cons_erase (min_el_mem hμ)

lemma min_el_of_zero_mem (h0 : 0 ∈ μ) : min_el μ (by
    rw [ne_eq, Multiset.eq_zero_iff_forall_notMem]
    push_neg; use 0) = 0 := by
  refine antisymm ?_ (Nat.zero_le _)
  exact min_el_le' _ h0


lemma sort_ne_nil_le {μ : Multiset ℕ} (h : μ ≠ 0) : (Multiset.sort (· ≤ ·) μ) ≠ [] := by
  rw [ne_eq, List.eq_nil_iff_length_eq_zero, Multiset.length_sort, Multiset.card_eq_zero]
  exact h

def max_el (μ : Multiset ℕ) (h : μ ≠ 0) := List.getLast (Multiset.sort (· ≤ ·) μ) (sort_ne_nil_le h)

lemma le_max_el {μ : Multiset ℕ} (hμ : μ ≠ 0) (i : Fin (Multiset.sort (· ≤ ·) μ).length) :
    (Multiset.sort (· ≤ ·) μ).get i ≤ max_el μ hμ := by
  rw [max_el, List.getLast_eq_getElem (sort_ne_nil_le hμ)]
  refine List.Sorted.rel_get_of_le ?_ ?_
  · exact Multiset.sort_sorted _ _
  let hi := i.2
  rw [Fin.mk_le_mk]
  exact Nat.le_sub_one_of_lt hi

lemma le_max_el' {μ : Multiset ℕ} (hμ : μ ≠ 0) {a : ℕ} (ha : a ∈ μ) :
    a ≤ max_el μ hμ := by
  rw [← Multiset.mem_sort (· ≤ ·)] at ha
  apply List.get_of_mem at ha
  obtain ⟨i, ha⟩ := ha
  rw [← ha]
  exact le_max_el hμ i

lemma max_el_mem {μ : Multiset ℕ} (hμ : μ ≠ 0) : max_el μ hμ ∈ μ := by
  rw [max_el, ← Multiset.mem_sort (· ≤ ·)]
  exact List.getLast_mem (sort_ne_nil_le hμ)

lemma cons_erase_max_el {μ : Multiset ℕ} (hμ : μ ≠ 0) : μ =
    (max_el μ hμ) ::ₘ (μ.erase (max_el μ hμ)) := by
  symm
  exact Multiset.cons_erase (max_el_mem hμ)


lemma max_el_ne_zero_iff_exists_nonzero {μ : Multiset ℕ} (hμ : μ ≠ 0) :
    max_el μ hμ ≠ 0 ↔ ∃ x ∈ μ, x ≠ 0 := by
  constructor
  · intro h
    use max_el μ hμ
    constructor
    · exact max_el_mem hμ
    · exact h
  · contrapose!
    intro h x hx
    rw [← Nat.le_zero, ← h]
    exact le_max_el' hμ hx

lemma max_el_replicate {n a : ℕ} (h : n ≠ 0) : max_el (Multiset.replicate n a)
    (by rw [ne_eq, ← Multiset.card_eq_zero, Multiset.card_replicate]; exact h) = a := by
  have hr0 : Multiset.replicate n a ≠ 0 := by
    rw [ne_eq, ← Multiset.card_eq_zero, Multiset.card_replicate]
    exact h
  let ha := max_el_mem hr0
  rw [Multiset.mem_replicate] at ha
  exact ha.2

lemma max_el_eq_get_zero_of_ge_sort (μ : Multiset ℕ) (hμ : μ ≠ 0) :
    max_el μ hμ = (μ.toList.mergeSort (· ≥ ·))[0]'(by simp [Nat.pos_iff_ne_zero, hμ]) := by
  unfold max_el
  rw [List.getLast_eq_head_reverse, List.head_eq_getElem]
  congr
  nth_rw 1 [← Multiset.coe_toList μ, List.ge_sort_eq_reverse_le_sort]
  congr
