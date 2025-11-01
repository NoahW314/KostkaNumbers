import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.RestrictExtend
import KostkaNumbers.HookLength.PointerTableau
import KostkaNumbers.HookLength.PermWord
import KostkaNumbers.HookLength.ReduceList
import KostkaNumbers.HookLength.CellIndex

open YoungDiagram SemistandardYoungTableau Kostka


def Subdiagram (γ : YoungDiagram) : Set (YoungDiagram) := {μ : YoungDiagram | μ ≤ γ}

lemma subdiagram_self (γ : YoungDiagram) : γ ∈ Subdiagram γ := by simp [Subdiagram]

lemma finite_subdiagrams (γ : YoungDiagram) : Finite (Subdiagram γ) := by
  let S := {f : ℕ →₀ ℕ | f ≤ γ.rowLens'}
  have hS : Finite (S) := instFiniteSubtypeLeOfLocallyFiniteOrderBot
  let g : Subdiagram γ → S := fun μ ↦ ⟨μ.1.rowLens', by
    have hμ := μ.2
    unfold Subdiagram at hμ
    rw [Set.mem_setOf] at hμ
    rw [Set.mem_setOf]
    exact rowLens'_le hμ
    ⟩
  refine Finite.of_injective g ?_
  intro μ μ' hg
  simp only [Subtype.mk.injEq, rowLens'_eq_iff, g] at hg
  exact SetCoe.ext hg

noncomputable
instance fintype_subdiagrams {γ : YoungDiagram} : Fintype (Subdiagram γ) := by
  have := finite_subdiagrams γ
  exact Fintype.ofFinite (Subdiagram γ)




lemma sub_cond_of_remove_corner (γ : YoungDiagram) (x : ℕ × ℕ) (hx : IsCornerCell γ x) :
    ∀ i, γ.rowLens' i - (Finsupp.single x.1 1) i ≥
    γ.rowLens' (i + 1) := by
  intro i
  simp only [Finsupp.single_apply, ge_iff_le]
  have hrli : γ.rowLens' (i + 1) ≤ γ.rowLens' i := by exact γ.rowLens'_anti (by omega)
  split_ifs with hi
  · unfold IsCornerCell at hx
    subst hi
    rw [γ.rowLens'_eq_rowLen, γ.rowLens'_eq_rowLen, ← hx.1]
    simp only [add_tsub_cancel_right, ge_iff_le]
    suffices ¬ x.2 < γ.rowLen (x.1 + 1) by omega
    rw [← γ.mem_iff_lt_rowLen, γ.mem_iff_lt_colLen, hx.2]
    omega
  · omega

def pi (γ : YoungDiagram) (n : ℕ) (h : γ.card = n) :
  PermWord n × ((μ : Subdiagram γ) → {P : PointerTableau μ | IsStrict P}) →
  SemistandardYoungTableauWithContent γ (Multiset.replicate n 1) ×
  (PointerTableau γ) × ((μ : Subdiagram γ) → {P : PointerTableau μ | IsStrict P}) :=
  fun (σ, P) ↦ by
  by_cases hn : n = 0
  · subst hn
    have hγ := eq_bot_iff_card_eq_zero.mpr h
    subst hγ
    simp only [Multiset.replicate_zero, Set.coe_setOf]
    have hb : bot_ssyt ∈ SemistandardYoungTableauWithContent ⊥ 0 := by
      simp [SemistandardYoungTableauWithContent]
    use ⟨bot_ssyt, hb⟩
    use bot_pointer
    use P

  have hsc : (σ.1)[0]'(by rw [σ.2.2]; omega) < γ.card := by
    rw [h]
    exact permWord_getElem_lt σ 0 (by omega)
  let x : ℕ × ℕ := γ.nth_cell (σ.1[0]'(by rw [σ.2.2]; omega)) hsc
  let σ' : PermWord (n - 1) := ⟨reduceList σ.1.tail, by
    have hst : σ.1.tail.Nodup := List.Sublist.nodup (List.tail_sublist _) (permWord_nodup σ)
    simp [PermWord, reduceList_length, σ.2.2, reduceList_multiset _ hst]⟩
  let x' : ℕ × ℕ := followPath (P ⟨γ, subdiagram_self γ⟩) x (nth_cell_mem hsc)
  have hccx' : IsCornerCell γ x' := followPath_isCornerCell
    (P ⟨γ, subdiagram_self γ⟩).2 x (nth_cell_mem hsc)

  let γ' : YoungDiagram := γ.sub (Finsupp.single x'.1 1)
  have hγ' := sub_le γ (Finsupp.single x'.1 1) <| sub_cond <| sub_cond_of_remove_corner γ x' hccx'
  let P' : (μ : Subdiagram γ') → {P : PointerTableau μ | IsStrict P} :=
    fun μ ↦ P ⟨μ.1, by
      simp only [Subdiagram, Set.mem_setOf_eq]
      exact le_trans μ.2 hγ'⟩
  have hγ'n : γ'.card = n - 1 := by
    unfold γ'
    rw [γ.card_sub _ (sub_cond (sub_cond_of_remove_corner γ x' hccx')), h,
      Finsupp.support_single_ne_zero _ Nat.one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same]
    intro i
    rw [Finsupp.single_apply]
    split_ifs with hix
    · rw [← hix, γ.rowLens'_eq_rowLen]
      suffices 0 < γ.rowLen x'.1 by omega
      rw [← γ.mem_iff_lt_rowLen]
      exact γ.up_left_mem (by rfl) (Nat.zero_le _)
        (followPath_mem_diagram (P ⟨γ, subdiagram_self γ⟩) x (nth_cell_mem hsc))
    · exact Nat.zero_le _

  obtain ⟨T', K', Q'⟩ := pi γ' (n-1) hγ'n (σ', P')

  have han : ∀ i j : ℕ, (i, j) ∈ γ' → T'.1 i j < n - 1 := by
    have hT := T'.2
    unfold SemistandardYoungTableauWithContent at hT
    rw [Set.mem_setOf] at hT
    intro i j hij
    have hTc : T'.1 i j ∈ T'.1.content := mem_content_of_mem_cells hij
    rw [hT, Multiset.mem_fromCounts_iff, Multiset.card_replicate] at hTc
    omega
    rw [Multiset.mem_replicate]
    omega
  let T : SemistandardYoungTableau γ := extend T'.1
    (sub_valid γ (Finsupp.single x'.1 1) (sub_cond_of_remove_corner γ x' hccx')) (n - 1) han


  sorry

theorem hookLength_formula_card (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    Nat.card (PermWord n × ((μ : Subdiagram γ) → {P : PointerTableau μ | IsStrict P})) =
    Nat.card (SemistandardYoungTableauWithContent γ (Multiset.replicate n 1) ×
    (PointerTableau γ) × ((μ : Subdiagram γ) → {P : PointerTableau μ | IsStrict P}))
     := by
  refine Nat.card_eq_of_bijective (pi γ n h) ?_
  sorry

theorem hookLength_formula' (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    (∏ x ∈ γ.cells, γ.hookLength x.1 x.2) *
    kostkaNumber γ (Multiset.replicate n 1) = Nat.factorial n := by
  have hlf := hookLength_formula_card γ h
  simp_rw [Nat.card_prod, Nat.card_pi, permWord_card, γ.pointerTableau_card,
    ← kostkaNumber_eq_card_ssyt_content, ← mul_assoc] at hlf
  symm
  rw [mul_comm]
  refine Nat.mul_right_cancel ?_ hlf
  rw [Nat.pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro ⟨μ, hμ⟩ _
  rw [Nat.card_ne_zero]
  constructor
  · exact strictPointerTableau_nonempty μ
  · exact strictPointerTableau_finite μ

theorem hookLength_formula (γ : YoungDiagram) {n : ℕ} (h : γ.card = n) :
    kostkaNumber γ (Multiset.replicate n 1) =
    Nat.factorial n / ∏ x ∈ γ.cells, γ.hookLength x.1 x.2 := by
  rw [← hookLength_formula' γ h]
  simp
