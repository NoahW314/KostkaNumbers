/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import KostkaNumbers.InequalitySmall
import KostkaNumbers.InequalitySpecial
import KostkaNumbers.InequalityTwoRows
import KostkaNumbers.ComputationProof.InequalityComputation
import KostkaNumbers.ExtractOne
/-!
This file completes the proof of the inequality involving kostka numbers.
-/

open Kostka SemistandardYoungTableau YoungDiagram

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n : ℕ}


lemma erase_min_eq_22_iff {hμ : μ.toList ≠ []} (h0 : 0 ∉ μ) :
    μ.erase (μ.toList.min hμ) = {2, 2} ↔ μ = {2, 2, 1} ∨ μ = {2, 2, 2} := by
  constructor
  · intro h
    have hμ' : μ.toList.min hμ ∈ μ := by
      rw [← Multiset.mem_toList]
      exact List.min_mem hμ
    have hm : μ.toList.min hμ = 1 ∨ μ.toList.min hμ = 2 := by
      suffices 0 < μ.toList.min hμ ∧ μ.toList.min hμ ≤ 2 by lia
      constructor
      · rw [Nat.pos_iff_ne_zero]
        contrapose! h0
        rwa [← h0]
      · have h2 : 2 ∈ μ.erase (μ.toList.min hμ) := by simp [h]
        apply Multiset.mem_of_mem_erase at h2
        rw [← Multiset.mem_toList] at h2
        exact List.min_le_of_mem h2
    rw [← Multiset.cons_erase hμ', h]
    rcases hm with hm | hm
    · left
      simp only [hm, Multiset.insert_eq_cons, ← Multiset.singleton_add]
      abel
    · right
      rw [hm]
      rfl
  · intro h
    rcases h with h | h
    · simp only [h, min_triple (by rfl) one_le_two]
      rfl
    · simp only [h, min_triple (by rfl) (by rfl)]
      rfl

lemma sum_kostka_sub_eq_kostka (hγ : γ.card = n) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) (Multiset.replicate n 1) =
    kostkaNumber γ (Multiset.replicate n 1) := by
  conv => rhs; rw [← sub_zero γ]
  rw [Finset.sum_eq_single_of_mem ⟨0, zero_subRowLensType⟩ (Finset.mem_univ _) ?_]
  intro f _ hf
  refine kostka_ne_card _ _ ?_
  rw [Multiset.sum_replicate, smul_eq_mul, mul_one, ← hγ,
    card_sub (sub_cond f.2.1) f.2.2]
  suffices ∑ x ∈ f.1.support, f.1 x ≠ 0 by
    let hasd := sum_support_subRowLensType_le_card f
    lia
  simp only [ne_eq, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, _root_.not_imp_self,
    not_forall]
  contrapose! hf
  suffices f.1 = (0 : ℕ →₀ ℕ) by
    rw [Subtype.coe_eq_iff] at this
    obtain ⟨_, this⟩ := this
    exact this
  ext x
  exact hf x

private lemma kostka_double_sum {k : ℕ} (h : γ.card - k = μ.sum) (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ) :
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k, kostkaNumber (γ.sub f.1) μ =
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k,
    ∑ g : SubRowLensType (γ.sub f.1) with ∑ x ∈ g.1.support, g.1 x = μ.toList.min hμ,
    kostkaNumber ((γ.sub f.1).sub g.1) (μ.erase (μ.toList.min hμ)) := by
  refine Finset.sum_congr (by rfl) ?_
  intro f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  refine kostka_recursion' hμ h0 ?_
  rw [card_sub (sub_cond f.2.1) f.2.2, hf, h]

lemma subSubSetFinite (γ : YoungDiagram) (f : ℕ →₀ ℕ) :
    Finite {g : ℕ →₀ ℕ | ((∀ i, (γ.sub f).rowLen' i - g i ≥
    (γ.sub f).rowLen' (i + 1)) ∧ (∀ i, g i ≤ (γ.sub f).rowLen' i) ∧
    ∑ x ∈ g.support, g x = 1)} := by
  have : Finite {g : ℕ →₀ ℕ | g ≤ (γ.sub f).rowLen'} := instFiniteSubtypeLeOfLocallyFiniteOrderBot
  refine Finite.Set.subset {g : ℕ →₀ ℕ | g ≤ (γ.sub f).rowLen'} ?_
  intro g
  simp only [ge_iff_le, Set.mem_setOf_eq, and_imp]
  intro _ h _ i
  exact h i

noncomputable
def subSubFinset (γ : YoungDiagram) (f : ℕ →₀ ℕ) : Finset (ℕ →₀ ℕ) :=
  Set.Finite.toFinset (subSubSetFinite γ f)

-- upstream
lemma Finset.sum_le_sum_of_injective {ι α : Type*} [DecidableEq α] {M : Type*}
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] {f : ι → M}
    {g : α → M} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : Finset.image e s ⊆ t) (h : ∀ x ∈ s, f x ≤ g (e x)) (h0 : ∀ y ∈ t, 0 ≤ g y) :
    ∑ x ∈ s, f x ≤ ∑ y ∈ t, g y := by
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg ht ?_)
  · rw [Finset.sum_image he]
    exact Finset.sum_le_sum h
  · intro y hy _
    exact h0 y hy

lemma kostka_sum_le_kostka_double_sum {k : ℕ} :
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k + 1, kostkaNumber (γ.sub f.1) μ ≤
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k,
    ∑ g ∈ subSubFinset γ f.1, kostkaNumber ((γ.sub f.1).sub g) μ := by
  have hfinS : Finite {(f, g) : (SubRowLensType γ × (ℕ →₀ ℕ)) |
      ∑ x ∈ f.1.support, f.1 x = k ∧ g ∈ subSubFinset γ f.1} := by
    have : {(f, g) : (SubRowLensType γ × (ℕ →₀ ℕ)) |
        ∑ x ∈ f.1.support, f.1 x = k ∧ g ∈ subSubFinset γ f.1} =
        ⋃ f ∈ { f : SubRowLensType γ | ∑ x ∈ f.1.support, f.1 x = k },
        (({f} : Set (SubRowLensType γ)) ×ˢ SetLike.coe (subSubFinset γ f.1)) := by
      ext x
      simp
    rw [this]
    refine Set.finite_iUnion ?_
    intro f
    refine Set.finite_iUnion ?_
    intro hf
    simp [Set.finite_prod]
  let s : Finset (SubRowLensType γ × (ℕ →₀ ℕ)) := Set.Finite.toFinset hfinS
  rw [← Finset.sum_finset_product' s]
  · let e : (f : SubRowLensType γ) → (SubRowLensType γ × (ℕ →₀ ℕ)) :=
      fun f ↦ if hf : ∑ x ∈ f.1.support, f.1 x = k + 1 then
        (⟨f.1 - extractOne hf, extractOne_SubRowLensType hf⟩, extractOne hf) else
        (⟨0, zero_subRowLensType⟩, 0)
    classical refine Finset.sum_le_sum_of_injective e ?_ ?_ ?_ ?_
    · intro f₁ hf₁ f₂ hf₂ he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf₁ hf₂
      simp only [hf₁, ↓reduceDIte, hf₂, Prod.mk.injEq, e] at he
      unfold SubRowLensType at he ⊢
      rw [Subtype.mk_eq_mk] at he
      rw [← Subtype.coe_inj, ← extractOne_sub_add hf₁, ← extractOne_sub_add hf₂,
        he.1, he.2]
    · intro f hf
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨f', hf', heff⟩ := hf
      simp only [← heff, hf', ↓reduceDIte, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
        Finsupp.coe_tsub, Pi.sub_apply, s, e, subSubFinset]
      constructor
      · exact extractOne_sub_sum_support hf'
      constructor
      · exact extractOne_rowLen'_sub_self_ge hf'
      constructor
      · exact extractOne_le_sub hf'
      · exact extractOne_sum_support hf'
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro f hf
      simp only [hf, ↓reduceDIte, e]
      rw [sub_extractOne_eq_sub hf]
    · simp
  · simp [subSubFinset, s]

@[simp]
lemma Multiset.replicate_eq_zero_iff {α : Type*} (n : ℕ) (a : α) :
    Multiset.replicate n a = 0 ↔ n = 0 := by
  simp [replicate]

instance instAntisymmEq {α : Type*} : Std.Antisymm (Eq (α := α)) where
  antisymm _ _ h _ := h

@[simp]
lemma Multiset.replicate_toList {α : Type*} (n : ℕ) (a : α) :
    (Multiset.replicate n a).toList = List.replicate n a := by
  rw [← List.perm_replicate, ← Multiset.coe_eq_coe, Multiset.coe_toList, Multiset.coe_replicate]

lemma kostka_sum_sub_replicate_le {k : ℕ} (hk : n > k) (hγ : γ.card = n) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) (Multiset.replicate (n - k) 1) ≤
    kostkaNumber γ (Multiset.replicate n 1) := by
  induction k with
  | zero => rw [tsub_zero, sum_kostka_sub_eq_kostka hγ]
  | succ k ih =>
    refine le_trans ?_ (ih (by lia))
    rw [sum_subRowLensSumType ?_ ?_ (k + 1), sum_subRowLensSumType ?_ ?_ k,
      kostka_double_sum (k := k)]
    · have hnk : n - (k + 1) = n - k - 1 := by lia
      rw! [Multiset.replicate_toList, List.min_replicate, Multiset.erase_replicate, ← hnk]
      refine le_trans kostka_sum_le_kostka_double_sum ?_
      refine le_of_eq ?_
      refine Finset.sum_congr (by rfl) ?_
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      let e : (g : ℕ →₀ ℕ) → (hg : g ∈ subSubFinset γ f.1) → SubRowLensType (γ.sub f.1) :=
        fun g hg ↦ ⟨g, by
          simp only [subSubFinset, ge_iff_le, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
          constructor
          · exact hg.1
          · exact hg.2.1⟩
      refine Finset.sum_bij e ?_ ?_ ?_ ?_
      · simp [Finset.mem_filter, Finset.mem_univ, true_and, e, subSubFinset]
      · intro g₁ _ g₂ _ hg
        unfold e SubRowLensType at hg
        rwa [Subtype.mk_eq_mk] at hg
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
        intro g hg
        use g.1
        simp [subSubFinset, hg, g.2.2, g.2.1]
      · simp [e]
    all_goals simp [hγ, Multiset.mem_replicate]
    all_goals lia

private lemma sum_subRowLensType_min_mul_kostka_sub_erase (hμ : μ.toList ≠ []) (h0 : 0 ∉ μ)
    (hγ : γ.card = n) (hmc1 : μ.card > 1) (hnmin : n > μ.toList.min hμ) (hmp : μ.toList.min hμ > 0)
    (h : γ.card = μ.sum) (hμ' : μ.toList.min hμ ∈ μ)
    (hf : ∀ f : SubRowLensType γ, f ∈ Finset.univ →
      (n - μ.toList.min hμ - 1) * kostkaNumber (γ.sub f.1) (μ.erase (μ.toList.min hμ)) ≤
      (μ.card - 2) * kostkaNumber (γ.sub f.1) (Multiset.replicate (n - (μ.toList.min hμ)) 1))
    (hrl' : ∀ f : SubRowLensType γ, (γ.sub f.1).card = (μ.erase (μ.toList.min hμ)).sum →
      (γ.sub f.1).rowLens.length ≠ 1) :
    ∑ f : SubRowLensType γ, (μ.toList.min hμ) * kostkaNumber (γ.sub f.1)
    (μ.erase (μ.toList.min hμ)) ≤
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1)
    (Multiset.replicate (n - μ.toList.min hμ) 1) := by
  refine Finset.sum_le_sum ?_
  intro f _
  qify
  specialize hf f (Finset.mem_univ f)
  qify at hf
  by_cases hl : μ.card ≠ 2
  · rw [← div_le_iff₀' (by simp; lia)] at hf
    refine le_trans ?_ hf
    rw [mul_div_right_comm]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · rw [le_div_iff₀ (by simp; lia), Nat.cast_sub (by lia), mul_sub,
        Nat.cast_sub (by lia), Nat.cast_sub (by lia)]
      suffices μ.toList.min hμ * μ.card ≤ n by
        qify at this
        simp only [Nat.cast_ofNat, Nat.cast_one, tsub_le_iff_right, ge_iff_le]
        refine le_trans this ?_
        suffices n ≤ n - (μ.toList.min hμ) - 1 + μ.toList.min hμ * 2 by
          qify at this
          rw [Nat.cast_sub (by lia), Nat.cast_sub (by lia)] at this
          exact this
        lia
      rw [← hγ, h]
      have hxm : ∀ x ∈ μ, μ.toList.min hμ ≤ x := by
        intro x hx
        rw [← Multiset.mem_toList] at hx
        exact List.min_le_of_mem hx
      refine le_trans ?_ (Multiset.card_nsmul_le_sum hxm)
      rw [nsmul_eq_mul, mul_comm]
      rfl
    · exact Nat.cast_nonneg' _
  · by_cases h' : (γ.sub f.1).card = (μ.erase (μ.toList.min hμ)).sum
    swap
    · simp [kostka_ne_card _ _ h']
    suffices ¬ (γ.sub f.1).rowLens ⊵ (μ.erase (μ.toList.min hμ)).sort (· ≥ ·) by
      rw [← kostka_pos_iff_dominates h', Nat.pos_iff_ne_zero] at this
      · push Not at this
        simp [this]
      · contrapose! h0
        exact Multiset.mem_of_mem_erase h0
    push Not at hl
    specialize hrl' f h'
    contrapose! hrl'
    apply lengths_le_of_dominates at hrl'
    specialize hrl' ?_ ?_
    · rw [← card_eq_sum_rowLens, Multiset.sort_sum, h']
    · intro i
      refine (γ.sub f.1).pos_of_mem_rowLens _ ?_
      exact List.get_mem _ _
    · simp only [ge_iff_le, Multiset.length_sort,
        Multiset.card_erase_of_mem hμ', hl, Nat.pred_eq_sub_one,
        Nat.add_one_sub_one] at hrl'
      suffices (γ.sub f.1).card ≠ 0 by
        rw [ne_eq, ← eq_bot_iff_card_eq_zero, ← rowLens_eq_iff, bot_rowLens,
          ← List.length_eq_zero_iff] at this
        lia
      rw [h', ne_eq, Multiset.sum_eq_zero_iff_eq_zero, ← Multiset.card_eq_zero,
        Multiset.card_erase_of_mem hμ', hl]
      · norm_num
      · contrapose! h0
        exact Multiset.mem_of_mem_erase h0

theorem kostka_ineq (γ : YoungDiagram) (μ : Multiset ℕ) (n : ℕ)
    (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hγ : γ.card = n)
    (hsq : γ ≠ ofRowLens [2, 2] (sorted_pair (by rfl)) ∨ μ ≠ {2, 2}) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  by_cases hn4 : n ≤ 4
  · exact kostka_ineq_small hhd h h0 hsq hγ hn4
  by_cases h221 : μ = {2, 2, 1}
  · refine kostka_ineq_221 hhd h h0 ?_ h221
    rw [← hγ, h, h221]
    norm_num
  by_cases h222 : μ = {2, 2, 2}
  · refine kostka_ineq_222 hhd h h0 ?_ h222
    rw [← hγ, h, h222]
    norm_num
  have hμ : μ.toList ≠ [] := by
    contrapose! hn4
    rw [← hγ, h, ← Multiset.sum_toList, hn4, List.sum_nil]
    norm_num
  have hμ' : μ.toList.min hμ ∈ μ := by
    rw [← Multiset.mem_toList]
    exact List.min_mem hμ
  by_cases hμn : μ = {n}
  · exact kostka_ineq_singleton hhd hμn h
  by_cases hcrl : γ.rowLens.length = 2 ∧ γ.rowLen 1 ≤ μ.toList.min hμ
  · rw [List.length_eq_two] at hcrl
    obtain ⟨⟨a, b, hab⟩, hmin⟩ := hcrl
    have ha : a = n - b := by
      rw [← hγ, card_eq_sum_rowLens, hab]
      simp
    rw [ha] at hab
    refine kostka_ineq_two_rows hab (by lia) ?_ hγ h hμ h0 ?_
    · by_contra! hb0
      simp only [hb0, tsub_zero] at hab
      have h0 : 0 ∈ γ.rowLens := by simp [hab]
      apply γ.pos_of_mem_rowLens at h0
      contradiction
    · suffices b = γ.rowLen 1 by rwa [this]
      simp [← γ.get_rowLens, hab]
  have hrl : γ.rowLens.length ≠ 1 := by
    contrapose! hhd
    rw [← rowLens_eq_iff, horizontalDiagram_rowLens (by lia)]
    rw [List.length_eq_one_iff] at hhd
    obtain ⟨m, hm⟩ := hhd
    rw [card_eq_sum_rowLens, hm, List.sum_singleton] at hγ
    rw [← hγ, hm]
  have hcrl : (γ.rowLens.length = 2 ∧ γ.rowLen 1 > μ.toList.min hμ) ∨ γ.rowLens.length > 2 := by
    push Not at hcrl
    by_cases hl : γ.rowLens.length = 2
    · simp [hl, hcrl]
    · simp only [hl, false_and, false_or]
      suffices γ.rowLens.length ≠ 0 by lia
      rw [ne_eq, List.length_eq_zero_iff]
      contrapose! hn4
      rw [← hγ, card_eq_sum_rowLens, hn4, List.sum_nil]
      norm_num
  have hrl' : ∀ f : SubRowLensType γ, (γ.sub f.1).card = (μ.erase (μ.toList.min hμ)).sum →
      (γ.sub f.1).rowLens.length ≠ 1 := by
    intro f h'
    suffices (γ.sub f.1).rowLen 1 > 0 by
      contrapose! this
      rw [Nat.le_zero]
      refine rowLen_eq_zero ?_
      rw [← length_rowLens, this]
      exact Nat.lt_irrefl 1
    rw [← rowLen'_eq_rowLen, sub_rowLen' (sub_cond f.2.1)]
    simp only [Finsupp.coe_tsub, Pi.sub_apply, gt_iff_lt]
    rcases hcrl with hcrl | hcrl
    · rw [tsub_pos_iff_lt, rowLen'_eq_rowLen]
      refine lt_of_le_of_lt ?_ hcrl.2
      suffices ∑ x ∈ f.1.support, f.1 x = μ.toList.min hμ by
        by_cases hfs : 1 ∈ f.1.support
        · rw [← this]
          refine Finset.single_le_sum ?_ hfs
          intro _ _
          exact Nat.zero_le _
        · rw [Finsupp.mem_support_iff] at hfs
          push Not at hfs
          rw [hfs]
          exact Nat.zero_le _
      rwa [card_sub (sub_cond f.2.1) f.2.2, Multiset.sum_erase' hμ', h, tsub_right_inj] at h'
      · exact h ▸ sum_support_subRowLensType_le_card f
      · exact Multiset.single_le_sum (by simp) _ hμ'
    · refine lt_of_lt_of_le ?_ (f.2.1 1)
      rw [rowLen'_eq_rowLen, ← mem_iff_lt_rowLen, mem_iff_lt_colLen,
        ← length_rowLens]
      exact hcrl
  rw [kostka_recursion hμ h0 h]
  have hmc1 : μ.card > 1 := by
    contrapose! hμn
    rw [ne_eq, Multiset.toList_eq_nil, ← Multiset.card_eq_zero] at hμ
    have hμn : μ.card = 1 := by lia
    rw [Multiset.card_eq_one] at hμn
    obtain ⟨m, hm⟩ := hμn
    rw [h, hm, Multiset.sum_singleton] at hγ
    rw [hm, hγ]
  have hnmin : n > μ.toList.min hμ := by
    contrapose! hmc1
    have hn0 : n > 0 := by lia
    refine Nat.le_of_mul_le_mul_right ?_ hn0
    rw [← smul_eq_mul, one_mul]
    conv => rhs; rw [← hγ, h]
    refine Multiset.card_nsmul_le_sum ?_
    intro x hx
    rw [← Multiset.mem_toList] at hx
    exact le_trans hmc1 <| List.min_le_of_mem hx
  have hmp : μ.toList.min hμ > 0 := by
    contrapose! h0
    rw [Nat.le_zero] at h0
    rwa [← h0]
  have hnm : n - 1 = (n - μ.toList.min hμ - 1) + μ.toList.min hμ := by lia
  rw [hnm, add_mul, Finset.mul_sum, Finset.mul_sum]
  have hf : ∀ f : SubRowLensType γ, f ∈ Finset.univ →
      (n - μ.toList.min hμ - 1) * kostkaNumber (γ.sub f.1) (μ.erase (μ.toList.min hμ)) ≤
      (μ.card - 2) * kostkaNumber (γ.sub f.1) (Multiset.replicate (n - (μ.toList.min hμ)) 1) := by
    intro f _
    by_cases h' : (γ.sub f.1).card = (μ.erase (μ.toList.min hμ)).sum
    · have : μ.card - 2 = (μ.erase (μ.toList.min hμ)).card - 1 := by
        rw [Multiset.card_erase_of_mem hμ', Nat.pred_eq_sub_one]
        lia
      rw [this]
      refine kostka_ineq _ _ _ ?_ h' ?_ ?_ ?_
      · rw [ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens (by lia)]
        apply_fun List.length
        rw [List.length_singleton]
        exact hrl' f h'
      · contrapose! h0
        exact Multiset.mem_of_mem_erase h0
      · rw [h', Multiset.sum_erase' hμ', ← h, hγ]
      · right
        rw [ne_eq, erase_min_eq_22_iff h0, not_or]
        constructor
        · exact h221
        · exact h222
    · simp [kostka_ne_card _ _ h']
  refine le_trans (Nat.add_le_add_right (Finset.sum_le_sum hf) _) ?_
  have hsum2 := sum_subRowLensType_min_mul_kostka_sub_erase hμ h0 hγ hmc1 hnmin hmp h hμ' hf hrl'
  refine le_trans (Nat.add_le_add_left hsum2 _) ?_
  rw [← Finset.mul_sum, ← Nat.add_one_mul]
  have hmc1 : μ.card - 1 ≠ 0 := by lia
  have hmc : μ.card - 2 + 1 = μ.card - 1 := by lia
  rw [hmc]
  refine Nat.mul_le_mul_left _ ?_
  exact kostka_sum_sub_replicate_le hnmin hγ


def padZeros_parts {d : ℕ} (μ : Nat.Partition d) (n : ℕ) : Multiset ℕ :=
  (Multiset.replicate (n - μ.parts.card) 0) + μ.parts

lemma padZeros_parts_counts_sum {d : ℕ} (μ : Nat.Partition d) {n : ℕ} (h : n ≥ d) :
    (padZeros_parts μ n).counts.sum = n := by
  have hnμ : n ≥ μ.parts.card := by
    refine le_trans ?_ h
    refine le_trans ?_ (le_of_eq μ.parts_sum)
    refine μ.parts.card_le_sum ?_
    intro _ hx
    exact μ.parts_pos hx
  simp [padZeros_parts, Multiset.sum_counts_eq_card]
  lia

lemma nat_partition2 : (Finset.univ : Finset (Nat.Partition 2)) =
    ({⟨{2}, by simp, by simp⟩, ⟨{1, 1}, by simp, by simp⟩} :
    Finset (Nat.Partition 2)) := by
  ext μ
  have hp := partition2 μ.parts μ.parts_sum (by intro x hx; exact μ.parts_pos hx)
  simp only [Finset.mem_univ, Finset.mem_insert, Nat.Partition.ext_iff,
    Finset.mem_singleton, hp]

/-
The main inequality concering Kostka numbers that I'm trying to prove.
Lemma 4.5 in the paper
-/

theorem kostka_inequality {n d : ℕ} (hn : n ≥ 2) (hd : d ≥ 2) (hnd : n > d)
    (γ : YoungDiagram) (hγc : γ.card = n) (hhd : γ ≠ horizontalDiagram n) :
    (kostkaNumber γ (Multiset.replicate n 1)) *
    (∑ μ : Nat.Partition d, kostkaNumber (hookDiagram n) (padZeros_parts μ n).counts) ≥
    (kostkaNumber (hookDiagram n) (Multiset.replicate n 1)) *
    (∑ μ : Nat.Partition d, kostkaNumber γ ((padZeros_parts μ n).counts)) := by
  rw [kostka_hook_replicate _ (by lia)]
  have hsn : ∑ μ : Nat.Partition d, kostkaNumber (hookDiagram n)
      (padZeros_parts μ n).counts = ∑ μ : Nat.Partition d,
      ((padZeros_parts μ n).counts.card - 1) := by
    refine Finset.sum_congr (by rfl) ?_
    intro μ _
    nth_rw 1 [← padZeros_parts_counts_sum μ (le_of_lt hnd)]
    rw [kostka_hook]
    · exact Multiset.zero_notMem_counts _
    · rw [padZeros_parts_counts_sum μ (le_of_lt hnd)]
      exact hn
  rw [hsn, Finset.mul_sum, Finset.mul_sum]
  by_cases! hγ : γ ≠ ofRowLens [2, 2] (sorted_pair (by rfl)) ∨ d = 3
  · refine Finset.sum_le_sum ?_
    intro μ _
    conv => rhs; rw [mul_comm]
    refine kostka_ineq γ (padZeros_parts μ n).counts n hhd ?_ (by simp) hγc ?_
    · rw [hγc, padZeros_parts_counts_sum μ (le_of_lt hnd)]
    · rcases hγ with hγ | hd3
      · left
        exact hγ
      · right
        subst hd3
        have hp := partition3 μ.parts μ.parts_sum ?_
        · rcases hp with hp | hp | hp
          · apply_fun Multiset.count 1
            simp [padZeros_parts, hp, Multiset.counts, Multiset.mem_replicate]
          · apply_fun Multiset.count 1
            simp [padZeros_parts, hp, Multiset.counts, Multiset.mem_replicate]
          · apply_fun Multiset.count 3
            simp [padZeros_parts, hp, Multiset.counts, Multiset.mem_replicate]
        · intro x hx
          exact μ.parts_pos hx
  obtain ⟨hγ, hd3⟩ := hγ
  have hn4 : n = 4 := by
    apply_fun YoungDiagram.card at hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, forall_eq, Nat.ofNat_pos,
      card_ofRowLens, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd] at hγ
    rw [← hγc, hγ]
  have hd2 : d = 2 := by lia
  subst hd2
  have h02 : (0 ::ₘ 0 ::ₘ 0 ::ₘ {2}).counts = {3, 1} := by rfl
  have h10 : (1 ::ₘ 0 ::ₘ 0 ::ₘ {1}).counts = {2, 2} := by rfl
  have h1r : Multiset.replicate 4 1 = 1 ::ₘ 1 ::ₘ 1 ::ₘ {1} := by rfl
  simp only [nat_partition2, Multiset.insert_eq_cons, hγ, hn4, Multiset.replicate_succ,
    Multiset.replicate_zero, Multiset.cons_zero, padZeros_parts, Multiset.counts_card,
    Multiset.toFinset_add, Multiset.toFinset_replicate, Finset.mem_singleton,
    Nat.Partition.mk.injEq, Multiset.singleton_eq_cons_iff, OfNat.ofNat_ne_one,
    Multiset.singleton_ne_zero, and_self, not_false_eq_true, Finset.sum_insert,
    Multiset.card_singleton, Nat.add_one_sub_one, OfNat.ofNat_ne_zero, ↓reduceIte,
    Multiset.toFinset_singleton, Finset.singleton_union, OfNat.zero_ne_ofNat,
    Finset.card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd, mul_one,
    Finset.sum_singleton, Multiset.card_cons, Nat.reduceSub, Multiset.toFinset_cons,
    Finset.insert_eq_of_mem, zero_ne_one, Multiset.cons_add, Multiset.singleton_add,
    Multiset.add_cons, ge_iff_le]
  have h22 : Multiset.ofList (ofRowLens [2, 2] (sorted_pair (by rfl))).rowLens = {2, 2} := by
    rw [rowLens_ofRowLens_eq_self (by simp)]
    rfl
  rw [← h1r, kostka_22, h02, h10, ← h22, kostka_self]
  suffices ¬ 0 < kostkaNumber (ofRowLens [2, 2] (sorted_pair (by rfl))) {3, 1} by
    rw [Nat.pos_iff_ne_zero] at this
    push Not at this
    rw [this]
    norm_num
  rw [kostka_pos_iff_dominates, sort_pair_ge (by norm_num), rowLens_ofRowLens_eq_self,
    pair_dominates_pair]
  all_goals simp
