import Mathlib
import KostkaNumbers.Util

/-
Additional lemms about young diagrams that I need
-/

namespace YoungDiagram


@[simp] lemma bot_card : (⊥ : YoungDiagram).card = 0 := by simp

variable {γ : YoungDiagram}

lemma zero_notMem_rowLens : 0 ∉ Multiset.ofList γ.rowLens := by
  by_contra! h
  apply γ.pos_of_mem_rowLens at h
  contradiction



lemma rowLen_eq_filter {n : ℕ} : γ.rowLen n = (Multiset.filter
    (fun a ↦ n = if a ∈ γ then a.1 else 0) γ.cells.val).card := by
  suffices Multiset.filter (fun a ↦ n = if a ∈ γ then a.1 else 0) γ.cells.val =
      (γ.cells.filter (fun a ↦ a.1 = n)).val by
    rw [this, ← row, ← Finset.card_def]
    exact γ.rowLen_eq_card
  rw [Finset.filter_val]
  refine Multiset.filter_congr ?_
  intro x hx
  rw [Finset.mem_val, mem_cells] at hx
  simp [hx]
  exact eq_comm


lemma range_colLen_eq_map_dedup (γ : YoungDiagram) : Multiset.range (γ.colLen 0) =
    (Multiset.map (fun a ↦ if a ∈ γ then a.1 else 0) γ.cells.val).dedup := by
  have ha : ∀ a ∈ γ.cells.val, (if a ∈ γ then a.1 else 0) = a.1 := by
    intro a ha
    rw [Finset.mem_val, mem_cells] at ha
    simp [ha]
  rw [Multiset.map_congr (by rfl) ha]
  ext n
  simp [Multiset.count_eq_of_nodup, Multiset.nodup_range]
  suffices n < γ.colLen 0 ↔ n ∈ (Multiset.map Prod.fst γ.cells.val).dedup by
    by_cases hn : n < γ.colLen 0
    let hn2 := hn; rw [this] at hn2
    simp [hn, hn2]
    let hn2 := hn; rw [this] at hn2
    simp [hn, hn2]
  simp [← mem_iff_lt_colLen]
  constructor
  · intro h; use 0
  · intro h; obtain ⟨x, h⟩ := h
    exact γ.up_left_mem (by rfl) (Nat.zero_le x) h

end YoungDiagram
