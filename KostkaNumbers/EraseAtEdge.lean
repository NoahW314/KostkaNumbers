import Mathlib
import KostkaNumbers.Content

open YoungDiagram SemistandardYoungTableau

namespace YoungDiagram

def eraseAtEdge (γ : YoungDiagram) (i j : ℕ) (hi1j : (i + 1, j) ∉ γ)
    (hij1 : (i, j + 1) ∉ γ) : YoungDiagram :=
  ⟨γ.cells.erase (i,j), by
  rw [Finset.coe_erase]
  refine IsLowerSet.sdiff γ.2 ?_
  simp only [Finset.mem_coe, mem_cells, Set.mem_singleton_iff, forall_eq, Prod.forall,
    Prod.mk_le_mk, Prod.mk.injEq, and_imp]
  intro a b hab hia hjb
  contrapose hab
  rw [not_and_or] at hab
  rcases hab with ha|hb
  · have ha := lt_of_le_of_ne' hia ha
    contrapose! hi1j
    exact γ.up_left_mem ha hjb hi1j
  · have hb := lt_of_le_of_ne' hjb hb
    contrapose! hij1
    exact γ.up_left_mem hia hb hij1
  ⟩

/-
lemma erase_of_notMem {γ : YoungDiagram} {i j : ℕ} (hi : (i + 1, j) ∉ γ) (hj : (i, j + 1) ∉ γ)
    (h : (i, j) ∉ γ) : (γ.eraseAtEdge i j hi hj) = γ := by
  sorry
-/

end YoungDiagram

namespace SemistandardYoungTableau

variable {γ : YoungDiagram} {μ : Multiset ℕ} {T : SemistandardYoungTableau γ}

def eraseAtEdge (T : SemistandardYoungTableau γ) (i j : ℕ)
    (hi1j : (i + 1, j) ∉ γ) (hij1 : (i, j + 1) ∉ γ) :
    SemistandardYoungTableau (γ.eraseAtEdge i j hi1j hij1) :=
  ⟨fun a b => if a = i ∧ b = j then 0 else T a b, by
  intro i' j1 j2 hj hij
  simp only [YoungDiagram.eraseAtEdge, mem_mk, Finset.mem_erase, ne_eq, Prod.mk.injEq,
    mem_cells] at hij
  simp [hij.1]
  by_cases hij' : i' = i ∧ j1 = j
  · simp [hij']
  · simp [hij']
    exact T.row_weak hj hij.2
  , by
  intro i1 i2 j' hi hij
  simp only [YoungDiagram.eraseAtEdge, mem_mk, Finset.mem_erase, ne_eq, Prod.mk.injEq,
    mem_cells] at hij
  simp [hij.1]
  by_cases hij' : i1 = i ∧ j' = j
  · simp [hij']
    rw [hij'.2] at hij
    exact lt_of_le_of_lt (Nat.zero_le (T i1 j)) <| T.col_strict hi hij.2
  · simp [hij']
    exact T.col_strict hi hij.2
  , by
  intro i' j' hij'
  simp [YoungDiagram.eraseAtEdge] at hij'
  simp
  intro himp; specialize hij' himp
  exact zeros T hij'
  ⟩



lemma hook_erase (h2 : (1 + 1, 0) ∉ hookDiagram (μ.sum)) (h11 : (1, 0 + 1) ∉ hookDiagram (μ.sum))
    (h : μ.sum ≥ 2) :
    (hookDiagram (μ.sum)).eraseAtEdge 1 0 h2 h11 = horizontalDiagram (μ.sum - 1) := by
  have h0 : μ.sum ≠ 0 := by omega
  have h1 : μ.sum ≠ 1 := by omega
  simp [hookDiagram, h0, h1, horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens,
    YoungDiagram.eraseAtEdge, Finset.erase_union_distrib, Finset.erase_singleton,
    Finset.union_empty]

/-lemma erase_of_notMem {i j : ℕ} (hi : (i + 1, j) ∉ γ) (hj : (i, j + 1) ∉ γ)
    (h : (i, j) ∉ γ) : (T.eraseAtEdge i j hi hj).entry = T.entry := by
  sorry
-/

lemma erase_eval {i j i' j' : ℕ} (hi : (i + 1, j) ∉ γ) (hj : (i, j + 1) ∉ γ)
    (h : ¬(i' = i ∧ j' = j)) :
    (T.eraseAtEdge i j hi hj) i' j' = T i' j' := by
  simp only [eraseAtEdge, DFunLike.coe, h, reduceIte]

lemma erase_content {i j : ℕ} (hi : (i + 1, j) ∉ γ) (hj : (i, j + 1) ∉ γ)
    (h : (i, j) ∈ γ) :
    (T.eraseAtEdge i j hi hj).content = T.content.erase (T i j) := by
  unfold content
  simp only
  have htij : T i j = (fun x : ℕ×ℕ ↦ T x.1 x.2) (i, j) := by simp only
  rw [htij, ← Multiset.map_erase_of_mem]
  swap
  · rw [Finset.mem_val, mem_cells]
    exact h
  simp only [YoungDiagram.eraseAtEdge, Finset.erase_val]
  refine Multiset.map_congr (rfl) ?_
  intro x hx
  refine erase_eval hi hj ?_
  apply Finset.ne_of_mem_erase at hx
  contrapose! hx
  rw [← hx.1, ← hx.2]



lemma erase_content_cons {i j : ℕ} (hi : (i + 1, j) ∉ γ) (hj : (i, j + 1) ∉ γ) (h : (i, j) ∈ γ) :
    (T i j) ::ₘ (T.eraseAtEdge i j hi hj).content = T.content := by
  rw [erase_content hi hj h, Multiset.cons_erase]
  exact mem_content_of_mem_cells h


end SemistandardYoungTableau
