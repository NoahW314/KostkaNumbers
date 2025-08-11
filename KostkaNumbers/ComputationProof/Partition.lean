import Mathlib
import KostkaNumbers.Util.MinMaxEl


/-
Utility Theorems
-/

lemma ne_zero_of_sum_ne_zero {μ : Multiset ℕ} {n : ℕ} (h : μ.sum = n)
    (hn : n ≠ 0) : μ ≠ 0 := by
  contrapose! hn
  rw [← h, hn, Multiset.sum_zero]

lemma sum_max_el_erase {μ : Multiset ℕ} {n : ℕ} (h : μ.sum = n) (hμ : μ ≠ 0) :
    (μ.erase (max_el μ hμ)).sum = n - max_el μ hμ := by
  rw [← h, ← Multiset.sum_erase (max_el_mem hμ)]
  rw [add_comm, add_tsub_cancel_right]

lemma pos_of_max_el_erase {μ : Multiset ℕ} (hμ : μ ≠ 0) (hp : ∀ x ∈ μ, x > 0) :
    ∀ x ∈ (μ.erase (max_el μ hμ)), x > 0 := by
  intro x hx
  exact hp x (Multiset.mem_of_mem_erase hx)

lemma cons_lt_max_el {μ ν : Multiset ℕ} {a n : ℕ} {hμ : μ ≠ 0}
    (h : max_el μ hμ = n) (ha : n < a) : μ.erase n ≠ a ::ₘ ν := by
  contrapose! ha
  rw [← h]
  refine le_max_el' hμ ?_
  suffices a ∈ μ.erase n by exact Multiset.mem_of_mem_erase this
  rw [ha]
  exact Multiset.mem_cons_self a ν

lemma singleton_lt_max_el {μ : Multiset ℕ} {a n : ℕ} {hμ : μ ≠ 0}
    (h : max_el μ hμ = n) (ha : n < a) : μ.erase n ≠ {a} := by
  contrapose! ha
  rw [← h]
  refine le_max_el' hμ ?_
  suffices a ∈ μ.erase n by exact Multiset.mem_of_mem_erase this
  rw [ha]
  exact Multiset.mem_singleton.mpr rfl


/-
Enumeration of the partitions for n ≤ 6
-/

lemma partition0 (μ : Multiset ℕ) (h : μ.sum = 0) (hp : ∀ x ∈ μ, x > 0) :
    μ = 0 := by
  apply Multiset.card_le_sum at hp
  rw [h, Nat.le_zero, Multiset.card_eq_zero] at hp
  exact hp

theorem partition1 (μ : Multiset ℕ) (h : μ.sum = 1) (hp : ∀ x ∈ μ, x > 0) :
    μ = {1} := by
  have hμ : μ ≠ 0 := by exact ne_zero_of_sum_ne_zero h one_ne_zero
  have hml : max_el μ hμ > 0 := hp (max_el μ hμ) (max_el_mem hμ)
  have hmu : max_el μ hμ ≤ 1 := by rw[← h]; exact Multiset.le_sum_of_mem (max_el_mem hμ)
  have hms := sum_max_el_erase h hμ
  have hmp := pos_of_max_el_erase hμ hp
  rw [cons_erase_max_el hμ]
  interval_cases hm : max_el μ hμ
  · ring_nf at hms
    have h0 := partition0 (μ.erase 1) hms hmp
    simp [h0]

theorem partition2 (μ : Multiset ℕ) (h : μ.sum = 2) (hp : ∀ x ∈ μ, x > 0) :
    μ = {2} ∨ μ = {1, 1} := by
  have hμ : μ ≠ 0 := by exact ne_zero_of_sum_ne_zero h two_ne_zero
  have hml : max_el μ hμ > 0 := hp (max_el μ hμ) (max_el_mem hμ)
  have hmu : max_el μ hμ ≤ 2 := by rw [← h]; exact Multiset.le_sum_of_mem (max_el_mem hμ)
  have hms := sum_max_el_erase h hμ
  have hmp := pos_of_max_el_erase hμ hp
  rw [cons_erase_max_el hμ]
  interval_cases hm : max_el μ hμ
  · ring_nf at hms
    have h1 := partition1 (μ.erase 1) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 2) hms hmp
    simp [h0]

theorem partition3 (μ : Multiset ℕ) (h : μ.sum = 3) (hp : ∀ x ∈ μ, x > 0) :
    μ = {3} ∨ μ = {2, 1} ∨ μ = {1, 1, 1} := by
  have hμ : μ ≠ 0 := by exact ne_zero_of_sum_ne_zero h three_ne_zero
  have hml : max_el μ hμ > 0 := hp (max_el μ hμ) (max_el_mem hμ)
  have hmu : max_el μ hμ ≤ 3 := by rw [← h]; exact Multiset.le_sum_of_mem (max_el_mem hμ)
  have hms := sum_max_el_erase h hμ
  have hmp := pos_of_max_el_erase hμ hp
  rw [cons_erase_max_el hμ]
  interval_cases hm : max_el μ hμ
  · ring_nf at hms
    have h2 := partition2 (μ.erase 1) hms hmp
    simp [singleton_lt_max_el hm] at h2
    simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 2) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 3) hms hmp
    simp [h0]

theorem partition4 (μ : Multiset ℕ) (h : μ.sum = 4) (hp : ∀ x ∈ μ, x > 0) :
    μ = {4} ∨ μ = {3, 1} ∨ μ = {2, 2} ∨ μ = {2, 1, 1} ∨ μ = {1, 1, 1, 1} := by
  have hμ : μ ≠ 0 := by exact ne_zero_of_sum_ne_zero h four_ne_zero
  have hml : max_el μ hμ > 0 := hp (max_el μ hμ) (max_el_mem hμ)
  have hmu : max_el μ hμ ≤ 4 := by rw [← h]; exact Multiset.le_sum_of_mem (max_el_mem hμ)
  have hms := sum_max_el_erase h hμ
  have hmp := pos_of_max_el_erase hμ hp
  rw [cons_erase_max_el hμ]
  interval_cases hm : max_el μ hμ
  · ring_nf at hms
    have h3 := partition3 (μ.erase 1) hms hmp
    simp [singleton_lt_max_el hm, cons_lt_max_el hm] at h3
    simp [h3]
  · ring_nf at hms
    have h2 := partition2 (μ.erase 2) hms hmp
    rcases h2 with h2|h2
    · simp [h2]
    · simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 3) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 4) hms hmp
    simp [h0]

theorem partition5 (μ : Multiset ℕ) (h : μ.sum = 5) (hp : ∀ x ∈ μ, x > 0) :
    μ = {5} ∨ μ = {4, 1} ∨ μ = {3, 2} ∨ μ = {3, 1, 1} ∨ μ = {2, 2, 1} ∨
    μ = {2, 1, 1, 1} ∨ μ = {1, 1, 1, 1, 1} := by
  have hμ : μ ≠ 0 := by exact ne_zero_of_sum_ne_zero h (by omega)
  have hml : max_el μ hμ > 0 := hp (max_el μ hμ) (max_el_mem hμ)
  have hmu : max_el μ hμ ≤ 5 := by rw [← h]; exact Multiset.le_sum_of_mem (max_el_mem hμ)
  have hms := sum_max_el_erase h hμ
  have hmp := pos_of_max_el_erase hμ hp
  rw [cons_erase_max_el hμ]
  interval_cases hm : max_el μ hμ
  · ring_nf at hms
    have h4 := partition4 (μ.erase 1) hms hmp
    simp [singleton_lt_max_el hm, cons_lt_max_el hm] at h4
    simp [h4]
  · ring_nf at hms
    have h3 := partition3 (μ.erase 2) hms hmp
    simp [singleton_lt_max_el hm] at h3
    rcases h3 with h3|h3
    · simp [h3]
    · simp [h3]
  · ring_nf at hms
    have h2 := partition2 (μ.erase 3) hms hmp
    rcases h2 with h2|h2
    · simp [h2]
    · simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 4) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 5) hms hmp
    simp [h0]


theorem partition6 (μ : Multiset ℕ) (h : μ.sum = 6) (hp : ∀ x ∈ μ, x > 0) :
    μ = {6} ∨ μ = {5, 1} ∨ μ = {4, 2} ∨ μ = {4, 1, 1} ∨ μ = {3, 3} ∨ μ = {3, 2, 1} ∨
    μ = {3, 1, 1, 1} ∨ μ = {2, 2, 2} ∨ μ = {2, 2, 1, 1} ∨ μ = {2, 1, 1, 1, 1} ∨
    μ = {1, 1, 1, 1, 1, 1} := by
  have hμ : μ ≠ 0 := by exact ne_zero_of_sum_ne_zero h (by omega)
  have hml : max_el μ hμ > 0 := hp (max_el μ hμ) (max_el_mem hμ)
  have hmu : max_el μ hμ ≤ 6 := by rw [← h]; exact Multiset.le_sum_of_mem (max_el_mem hμ)
  have hms := sum_max_el_erase h hμ
  have hmp := pos_of_max_el_erase hμ hp
  rw [cons_erase_max_el hμ]
  interval_cases hm : max_el μ hμ
  · ring_nf at hms
    have h5 := partition5 (μ.erase 1) hms hmp
    simp [singleton_lt_max_el hm, cons_lt_max_el hm] at h5
    simp [h5]
  · ring_nf at hms
    have h4 := partition4 (μ.erase 2) hms hmp
    simp [singleton_lt_max_el hm, cons_lt_max_el hm] at h4
    rcases h4 with h4|h4|h4
    · simp [h4]
    · simp [h4]
    · simp [h4]
  · ring_nf at hms
    have h3 := partition3 (μ.erase 3) hms hmp
    rcases h3 with h3|h3|h3
    · simp [h3]
    · simp [h3]
    · simp [h3]
  · ring_nf at hms
    have h2 := partition2 (μ.erase 4) hms hmp
    rcases h2 with h2|h2
    · simp [h2]
    · simp [h2]
  · ring_nf at hms
    have h1 := partition1 (μ.erase 5) hms hmp
    simp [h1]
  · ring_nf at hms
    have h0 := partition0 (μ.erase 6) hms hmp
    simp [h0]
