import Mathlib
import KostkaNumbers.Recursion

open YoungDiagram

namespace Fin

def tpred {n : ℕ} (i : Fin n) : Fin n := ⟨i.1 - 1,
  lt_of_le_of_lt (Nat.sub_le (↑i) 1) i.2⟩

lemma le_tpred_of_lt {n : ℕ} (i j : Fin n) (h : i < j) : i ≤ j.tpred := by
  unfold tpred
  suffices i.1 ≤ j.1 - 1 by exact this
  exact Nat.le_sub_one_of_lt h

lemma tpred_lt_of_lt {n : ℕ} (i j : Fin n) (h : i < j) : j.tpred < j := by
  unfold tpred
  suffices j.1 - 1 < j.1 by exact this
  exact Nat.sub_one_lt_of_lt h

end Fin

namespace YoungDiagram

def ofRowLens_c {n : ℕ} (f : Fin n → ℕ) (hf : Antitone f) :
  YoungDiagram :=
  ⟨Finset.biUnion Finset.univ (fun i ↦ {i.1} ×ˢ Finset.range (f i)),
  by
  simp [IsLowerSet]

  intro a b c d hca hdb x y hyfx hxa hyb
  rw [hyb] at hyfx
  let i : Fin n := ⟨c, by
    refine lt_of_le_of_lt hca ?_
    rw [← hxa]
    exact x.2⟩
  use i
  constructor
  · refine lt_of_le_of_lt hdb ?_
    refine lt_of_lt_of_le hyfx ?_
    refine hf ?_
    suffices i.1 ≤ x.1 by exact this
    simp [i, hxa, hca]
  · simp only [i]
  ⟩

def rowLens_c (γ : YoungDiagram) : Fin (γ.colLen 0) → ℕ := fun i ↦ γ.rowLen i.1

lemma antitone_sub_fin {n : ℕ} (f g : Fin n → ℕ)
    (h : ∀ i : Fin n, f i.tpred - g i.tpred ≥ f i - g i) (i j : Fin n)
    (hij : i ≤ j) : (f - g) j ≤ (f - g) i := by
  by_cases he : i = j
  · rw [he]
  · have hij' : i < j := by exact lt_of_le_of_ne hij he
    refine le_trans (h j) ?_
    rw [← Pi.sub_apply]
    exact antitone_sub_fin f g h i j.tpred (Fin.le_tpred_of_lt i j hij')
  termination_by j.1 - i.1
  decreasing_by
    let hjp := Fin.tpred_lt_of_lt i j hij'
    omega



def sub_c (γ : YoungDiagram) (f : Fin (γ.colLen 0) → ℕ)
  (h : ∀ i : Fin (γ.colLen 0), γ.rowLens_c i.tpred - f i.tpred ≥
  γ.rowLens' i - f i) : YoungDiagram :=
  ofRowLens_c (γ.rowLens_c - f) (antitone_sub_fin γ.rowLens_c f h)


lemma sub_lift {γ : YoungDiagram} {f : Fin (γ.colLen 0) → ℕ}
    (h : ∀ i, γ.rowLens_c i.tpred - f i.tpred ≥ γ.rowLens_c i) :
    ∀ i, γ.rowLens_c i.tpred - f i.tpred ≥ γ.rowLens_c i - f i := by
  intro i
  specialize h i
  omega

end YoungDiagram

def recUnionType_c (γ : YoungDiagram) := {f : Fin (γ.colLen 0) → ℕ //
  (∀ i, γ.rowLens_c i.tpred - f i.tpred ≥ γ.rowLens_c i) ∧
  (∀ i, f i ≤ γ.rowLens_c i) }

def fin_fun_coe (γ : YoungDiagram) : (Fin (γ.colLen 0) → Fin (γ.rowLen 0 + 1)) →
  (Fin (γ.colLen 0) → ℕ) := fun f ↦ (fun i ↦ (f i).1)

def recUnionSet (γ : YoungDiagram) : Finset (Fin (γ.colLen 0) → ℕ) :=
  Finset.filter (fun f ↦ (∀ i, γ.rowLens_c i.tpred - f i.tpred ≥ γ.rowLens_c i) ∧
  (∀ i, f i ≤ γ.rowLens_c i)) (Finset.image (fin_fun_coe γ) Finset.univ)

def recUnion_coe (γ : YoungDiagram) : recUnionSet γ → recUnionType_c γ := fun ⟨f, hf⟩ ↦
  ⟨f, by
    rw [recUnionSet, Finset.mem_filter] at hf
    exact hf.2⟩

instance decidablEqRecUnionType_c (γ : YoungDiagram) : DecidableEq (recUnionType_c γ) := by
  unfold recUnionType_c
  exact instDecidableEqOfLawfulBEq

instance recUnionFintype_c (γ : YoungDiagram) : Fintype (recUnionType_c γ) :=
  ⟨Finset.image (recUnion_coe γ) Finset.univ, by
  intro ⟨f, hf⟩
  simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, recUnion_coe, true_and,
    Subtype.exists]
  use f; use (by
    simp only [recUnionSet, ge_iff_le, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · use (fun i ↦ ⟨(f i), by
        suffices f i ≤ γ.rowLen 0 by exact Order.lt_add_one_iff.mpr this
        refine le_trans (hf.2 i) ?_
        unfold rowLens_c
        exact γ.rowLen_anti 0 i.1 (Nat.zero_le ↑i)
        ⟩)
      unfold fin_fun_coe
      simp
    · exact hf
    )
  ⟩

def computeKostka (γ : YoungDiagram) (μ : Multiset ℕ) :=
  if hμ : μ = 0 then (if γ.card = 0 then 1 else 0) else
  ∑ f : recUnionType_c γ, computeKostka (γ.sub_c f.1 (sub_lift f.2.1))
  (μ.erase (min_el μ hμ))
  termination_by μ.card
  decreasing_by exact Multiset.card_erase_lt_of_mem (min_el_mem hμ)

/-
lemma computeKostka11 : computeKostka (horizontalDiagram 1) ({1} : Multiset ℕ) = 0 := by
  unfold computeKostka
  simp [recUnionType_c]
  intro f h
  have hmin : min_el {1} (by sorry) = 1 := by simp [min_el]
  rw [hmin]
  have hasd : ({1} : Multiset ℕ).erase 1 = 0 := by simp
  rw [hasd]
  have hasdγ : (horizontalDiagram 1).sub_c f (sub_lift h.1) = ⊥ := by
    ext x
    simp [sub_c, ofRowLens_c, rowLens_c]
    intro i j hj
    have hc1 : (horizontalDiagram 1).colLen 0 = 1 := by sorry
    have hi : i.1 = 0 := by

      sorry
    rw [hi] at hj
    have hr1 : (horizontalDiagram 1).rowLen 0 = 1 := by sorry
    rw [hr1] at hj
    contradiction
  rw [hasdγ]
  unfold computeKostka
  simp only [↓reduceDIte, bot_card, ↓reduceIte]
  sorry
-/

--#eval computeKostka (horizontalDiagram 1) ({1} : Multiset ℕ)
