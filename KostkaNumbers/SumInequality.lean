import Mathlib
import KostkaNumbers.InequalitySmall
import KostkaNumbers.InequalitySpecial
import KostkaNumbers.InequalityTwoRows
import KostkaNumbers.ComputationProof.InequalityComputation

open Kostka SemistandardYoungTableau YoungDiagram

variable {γ : YoungDiagram} {μ : Multiset ℕ} {n : ℕ}


lemma erase_min_el_eq_22_iff {hμ : μ ≠ 0} (h0 : 0 ∉ μ) : μ.erase (min_el μ hμ) = {2, 2} ↔
    μ = {2, 2, 1} ∨ μ = {2, 2, 2} := by
  constructor
  · intro h
    have hm : min_el μ hμ = 1 ∨ min_el μ hμ = 2 := by
      suffices 0 < min_el μ hμ ∧ min_el μ hμ ≤ 2 by omega
      constructor
      · rw [Nat.pos_iff_ne_zero]
        contrapose! h0
        rw [← h0]
        exact min_el_mem hμ
      · have h2 : 2 ∈ μ.erase (min_el μ hμ) := by simp [h]
        apply Multiset.mem_of_mem_erase at h2
        exact min_el_le' hμ h2
    rw [← cons_erase_min_el hμ, h]
    rcases hm with hm | hm
    · left
      simp only [hm, Multiset.insert_eq_cons, ← Multiset.singleton_add]
      abel
    · right; rw [hm]; rfl
  · intro h
    rcases h with h | h
    · simp only [h, min_el_triple (by rfl) one_le_two]
      simp
    · simp only [h, min_el_triple (by rfl) (by rfl)]
      simp

lemma zero_subRowLensType : (∀ i, γ.rowLens' i - (0 : ℕ →₀ ℕ) i ≥
    γ.rowLens' (i + 1)) ∧ (∀ i, (0 : ℕ →₀ ℕ) i ≤ γ.rowLens' i) := by
  constructor
  · simp only [Finsupp.coe_zero, Pi.zero_apply, tsub_zero, ge_iff_le]
    intro i
    exact γ.rowLens'_anti (Nat.le_add_right i 1)
  · simp

lemma diagram_sub_zero (γ : YoungDiagram) : γ.sub (0 : ℕ →₀ ℕ) = γ := by
  rw [← rowLens'_eq_iff, sub_rowLens _ _, tsub_zero]
  intro i
  simp [γ.rowLens'_anti (Nat.le_add_right i 1)]

lemma sum_kostka_sub_eq_kostka (hγ : γ.card = n) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) (Multiset.replicate n 1) =
    kostkaNumber γ (Multiset.replicate n 1) := by
  conv => rhs; rw [← diagram_sub_zero γ]
  rw [Finset.sum_eq_single_of_mem ⟨0, zero_subRowLensType⟩ (Finset.mem_univ _) ?_]
  intro f _ hf
  refine kostka_ne_card _ _ ?_
  rw [Multiset.sum_replicate, smul_eq_mul, mul_one, ← hγ,
    card_sub _ _ (sub_cond f.2.1) f.2.2]
  suffices ∑ x ∈ f.1.support, f.1 x ≠ 0 by
    let hasd := sum_support_subRowLensType_le_card f
    omega
  simp only [ne_eq, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, _root_.not_imp_self,
    not_forall]
  contrapose! hf
  suffices f.1 = (0 : ℕ →₀ ℕ) by
    rw [Subtype.coe_eq_iff] at this
    obtain ⟨_, this⟩ := this
    exact this
  ext x
  exact hf x

open Classical in
lemma sum_subRowLensSumType {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ ≠ 0)
    (h0 : 0 ∉ μ) (k : ℕ) (h : γ.card - k = μ.sum) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1)
    μ = ∑ f : SubRowLensType γ with (∑ x ∈ f.1.support, f.1 x = k),
    kostkaNumber (γ.sub f.1) μ := by
  symm
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · intro f _; exact Finset.mem_univ f
  · intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hf
    refine kostka_ne_card _ _ ?_
    rw [card_sub _ _ (sub_cond f.2.1) f.2.2]
    have hcf := sum_support_subRowLensType_le_card f
    have hμ0 : μ.sum ≠ 0 := by
      rw [ne_eq, Multiset.sum_eq_zero_iff_eq_zero h0]
      exact hμ
    omega
  · intro _ _; rfl

private lemma kostka_double_sum {k : ℕ} (h : γ.card - k = μ.sum) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k,
    kostkaNumber (γ.sub f.1) μ =
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k,
    ∑ g : SubRowLensType (γ.sub f.1) with ∑ x ∈ g.1.support, g.1 x = min_el μ hμ,
    kostkaNumber ((γ.sub f.1).sub g.1)
    (μ.erase (min_el μ hμ)) := by
  refine Finset.sum_congr (by rfl) ?_
  intro f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  refine kostka_recursion' _ _ hμ h0 ?_
  rw [card_sub _ _ (sub_cond f.2.1) f.2.2, hf, h]



lemma subSubSetFinite (γ : YoungDiagram) (f : ℕ →₀ ℕ) :
    Finite {g : ℕ →₀ ℕ | ((∀ i, (γ.sub f).rowLens' i - g i ≥
    (γ.sub f).rowLens' (i + 1)) ∧ (∀ i, g i ≤ (γ.sub f).rowLens' i) ∧
    ∑ x ∈ g.support, g x = 1)} := by
  have : Finite {g : ℕ →₀ ℕ | g ≤ (γ.sub f).rowLens'} := by
    exact instFiniteSubtypeLeOfLocallyFiniteOrderBot
  refine Finite.Set.subset {g : ℕ →₀ ℕ | g ≤ (γ.sub f).rowLens'} ?_
  intro g
  simp only [ge_iff_le, Set.mem_setOf_eq, and_imp]
  intro _ h _ i
  exact h i

noncomputable
def subSubFinset (γ : YoungDiagram) (f : ℕ →₀ ℕ) : Finset (ℕ →₀ ℕ) :=
  Set.Finite.toFinset (subSubSetFinite γ f)


lemma exists_nonzero {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∃ m, f.1 m ≠ 0 := by
  have hf' : ∑ x ∈ f.1.support, f.1 x ≠ 0 := by
    rw [hf]; exact Ne.symm (Nat.zero_ne_add_one k)
  simp only [ne_eq, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, _root_.not_imp_self,
    not_forall] at hf'
  exact hf'

noncomputable
def extractOne {f : SubRowLensType γ} {k : ℕ} (hf : ∑ x ∈ f.1.support,
  f.1 x = k + 1) : (ℕ →₀ ℕ) :=
  Finsupp.single (Classical.choose (exists_nonzero hf)) 1


lemma extractOne_SubRowLensType {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) :
    (∀ i, γ.rowLens' i - (f.1 - extractOne hf) i ≥ γ.rowLens' (i + 1)) ∧
    (∀ i, (f.1 - extractOne hf) i ≤ γ.rowLens' i) := by
  constructor
  · intro i
    let hf' := f.2.1
    specialize hf' i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le]
    omega
  · intro i
    let hf' := f.2.2
    specialize hf' i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, tsub_le_iff_right, ge_iff_le]
    omega

lemma extractOne_le {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : extractOne hf ≤ f.1 := by
  intro i
  simp [extractOne]
  by_cases hi : i = Classical.choose (exists_nonzero hf)
  · rw [hi, Finsupp.single_eq_same]
    exact Nat.one_le_iff_ne_zero.mpr <| Classical.choose_spec (exists_nonzero hf)
  · push_neg at hi; symm at hi
    rw [Finsupp.single_eq_of_ne hi]
    exact Nat.zero_le _

lemma extractOne_sub_add {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) :
    f.1 - extractOne hf + extractOne hf = f.1 := by
  let hle := extractOne_le hf
  ext i
  specialize hle i
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
  omega

lemma extractOne_le_sub {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∀ i, extractOne hf i ≤
    (γ.sub (f.1 - extractOne hf)).rowLens' i := by
  intro i
  rw [sub_rowLens _ _]
  · simp only [Finsupp.coe_tsub, Pi.sub_apply]
    let hf3 := f.2.2 i
    let hf4 := extractOne_le hf i
    omega
  · intro i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
    let hf2 := f.2.1 i
    omega

lemma extractOne_rowLens'_sub_self_ge {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∀ i,
    (γ.sub (f.1 - extractOne hf)).rowLens' i - extractOne hf i ≥
    (γ.sub (f.1 - extractOne hf)).rowLens' (i + 1) := by
  intro i
  rw [sub_rowLens _ _ <| sub_cond (extractOne_SubRowLensType hf).1]
  simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
  let hf2 := extractOne_le hf i
  let hf3 := f.2.1 i
  omega

lemma extractOne_sum_support {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∑ x ∈ (extractOne hf).support,
    extractOne hf x = 1 := by
  simp [extractOne, Finsupp.support_single_ne_zero]


lemma extractOne_sub_sum_support {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : ∑ x ∈ (f.1 - extractOne hf).support,
    (f.1 - extractOne hf) x = k := by
  have : ∑ x ∈ (f.1 - extractOne hf).support,
      (f.1 - extractOne hf) x = ∑ x ∈ f.1.support, (f.1 - extractOne hf) x := by
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · exact Finsupp.support_tsub
    · simp
    · simp
  rw [this]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  rw [Finset.sum_tsub_distrib, hf]
  · suffices ∑ x ∈ (extractOne hf).support, (extractOne hf) x =
        ∑ x ∈ f.1.support, (extractOne hf) x by
      rw [← this, extractOne_sum_support hf, add_tsub_cancel_right]
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · exact Finsupp.support_mono (extractOne_le hf)
    · simp
    · simp
  · intro x _
    exact extractOne_le hf x

lemma sub_extractOne_eq_sub {f : SubRowLensType γ} {k : ℕ}
    (hf : ∑ x ∈ f.1.support, f.1 x = k + 1) : γ.sub f.1 =
    (γ.sub (f.1 - extractOne hf)).sub (extractOne hf) := by
  have hfi : ∀ i, γ.rowLens' i - (f.1 - extractOne hf) i ≥
      γ.rowLens' (i + 1) - (f.1 - extractOne hf) (i + 1) := by
    intro i
    let hf2 := f.2.1 i
    simp only [Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
    omega
  rw [← rowLens'_eq_iff, sub_rowLens _ _ (sub_cond f.2.1),
    sub_rowLens, sub_rowLens _ _ hfi]
  · ext i
    let hf2 := f.2.2 i
    let hf3 := extractOne_le hf i
    simp only [Finsupp.coe_tsub, Pi.sub_apply]
    omega
  · intro i
    simp only [sub_rowLens _ _ hfi, Finsupp.coe_tsub, Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
    let hf2 := f.2.1 i
    let hf3 := extractOne_le hf i
    omega

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

open Classical in
lemma kostka_sum_le_kostka_double_sum {k : ℕ} :
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k + 1,
    kostkaNumber (γ.sub f.1) μ ≤
    ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = k,
    ∑ g ∈ subSubFinset γ f.1, kostkaNumber ((γ.sub f.1).sub g) μ := by
  have hfinS : Finite {(f, g) : (SubRowLensType γ × (ℕ →₀ ℕ)) |
      ∑ x ∈ f.1.support, f.1 x = k ∧ g ∈ subSubFinset γ f.1} := by
    have : {(f, g) : (SubRowLensType γ × (ℕ →₀ ℕ)) |
        ∑ x ∈ f.1.support, f.1 x = k ∧ g ∈ subSubFinset γ f.1} =
        ⋃ f ∈ { f : SubRowLensType γ | ∑ x ∈ f.1.support, f.1 x = k },
        (({f} : Set (SubRowLensType γ)) ×ˢ (subSubFinset γ f.1).toSet) := by
      ext x; simp
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
    refine Finset.sum_le_sum_of_injective e ?_ ?_ ?_ ?_
    · intro f₁ hf₁ f₂ hf₂ he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf₁ hf₂
      simp only [hf₁, ↓reduceDIte, hf₂, Prod.mk.injEq, e] at he
      rw [Subtype.mk_eq_mk] at he
      rw [← Subtype.coe_inj, ← extractOne_sub_add hf₁, ← extractOne_sub_add hf₂,
        he.1, he.2]
    · intro f hf
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨f', hf', heff⟩ := hf
      simp only [← heff, hf', ↓reduceDIte,
        Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finsupp.coe_tsub, Pi.sub_apply, s, e,
        subSubFinset]
      constructor; swap; constructor; swap; constructor
      · exact extractOne_le_sub hf'
      · exact extractOne_sum_support hf'
      · exact extractOne_rowLens'_sub_self_ge hf'
      · exact extractOne_sub_sum_support hf'
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro f hf
      simp only [hf, ↓reduceDIte, e]
      rw [sub_extractOne_eq_sub hf]
    · simp
  · simp [subSubFinset, s]




lemma kostka_sum_sub_replicate_le {k : ℕ} (hk : n > k) (hγ : γ.card = n) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1) (Multiset.replicate (n - k) 1) ≤
    kostkaNumber γ (Multiset.replicate n 1) := by
  induction' k with k ih
  · rw [tsub_zero, sum_kostka_sub_eq_kostka hγ]
  · refine le_trans ?_ (ih (by omega))
    rw [sum_subRowLensSumType ?_ ?_ (k + 1), sum_subRowLensSumType ?_ ?_ k]
    rotate_left 1
    · simp [hγ]
    · suffices 1 ∈ Multiset.replicate (n - k) 1 by
        contrapose! this
        rw [this]
        exact Multiset.notMem_zero 1
      rw [Multiset.mem_replicate]
      omega
    · rw [Multiset.mem_replicate]
      omega
    · simp [hγ]
    · suffices 1 ∈ Multiset.replicate (n - (k + 1)) 1 by
        contrapose! this
        rw [this]
        exact Multiset.notMem_zero 1
      rw [Multiset.mem_replicate]
      omega
    · rw [Multiset.mem_replicate]
      omega

    nth_rw 2 [kostka_double_sum]
    · rw [min_el_replicate _ _ (by omega), Multiset.erase_replicate]
      have hnk : n - (k + 1) = n - k - 1 := by omega
      rw [← hnk]
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
        unfold e at hg
        rw [Subtype.mk_eq_mk] at hg
        exact hg
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
        intro g hg
        use g.1
        simp [subSubFinset, hg, g.2.2, g.2.1]
      · simp [e]
    · simp [hγ]
    · rw [Multiset.mem_replicate]
      omega

theorem kostka_ineq (γ : YoungDiagram) (μ : Multiset ℕ) (n : ℕ)
    (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum)
    (h0 : 0 ∉ μ) (hγ : γ.card = n)
    (hsq : γ ≠ ofRowLens [2, 2] (by simp) ∨ μ ≠ {2, 2}) :
    (n - 1) * kostkaNumber γ μ ≤
    (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
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

  have hμ : μ ≠ 0 := by
    contrapose! hn4
    rw [← hγ, h, hn4, Multiset.sum_zero]
    norm_num

  by_cases hμn : μ = {n}
  · exact kostka_ineq_singleton hhd hμn h

  by_cases hcrl : γ.rowLens.length = 2 ∧ γ.rowLen 1 ≤ min_el μ hμ
  · rw [List.length_eq_two] at hcrl
    obtain ⟨⟨a, b, hab⟩, hmin⟩ := hcrl
    have ha : a = n - b := by
      suffices a + b = n by omega
      rw [← hγ, card_eq_sum_rowLens, hab]
      simp
    rw [ha] at hab
    refine kostka_ineq_two_rows hab (by omega) ?_ hγ h hμ ?_
    · by_contra! hb0
      simp only [hb0, tsub_zero] at hab
      have h0 : 0 ∈ γ.rowLens := by simp [hab]
      apply γ.pos_of_mem_rowLens at h0
      contradiction
    · suffices b = γ.rowLen 1 by
        rw [this]
        exact hmin
      simp [← γ.get_rowLens, hab]

  have hrl : γ.rowLens.length ≠ 1 := by
    contrapose! hhd
    rw [← rowLens_eq_iff, horizontalDiagram_rowLens (by omega)]
    rw [List.length_eq_one_iff] at hhd
    obtain ⟨m, hm⟩ := hhd
    rw [card_eq_sum_rowLens, hm, List.sum_singleton] at hγ
    rw [← hγ, hm]
  have hcrl : (γ.rowLens.length = 2 ∧ γ.rowLen 1 > min_el μ hμ) ∨ γ.rowLens.length > 2 := by
    push_neg at hcrl
    by_cases hl : γ.rowLens.length = 2
    · simp [hl, hcrl]
    · simp only [hl, false_and, false_or]
      suffices γ.rowLens.length ≠ 0 by omega
      rw [ne_eq, List.length_eq_zero_iff]
      contrapose! hn4
      rw [← hγ, card_eq_sum_rowLens, hn4, List.sum_nil]
      norm_num
  have hrl' : ∀ f : SubRowLensType γ, (γ.sub f.1).card = (μ.erase (min_el μ hμ)).sum →
      (γ.sub f.1).rowLens.length ≠ 1 := by
    intro f h'
    suffices (γ.sub f.1).rowLen 1 > 0 by
      contrapose! this
      rw [Nat.le_zero]
      refine rowLen_eq_zero ?_
      rw [← length_rowLens, this]
      exact Nat.lt_irrefl 1
    rw [← rowLens'_eq_rowLen, sub_rowLens _ _ (sub_cond f.2.1)]
    simp only [Finsupp.coe_tsub, Pi.sub_apply, gt_iff_lt]
    rcases hcrl with hcrl | hcrl
    · rw [tsub_pos_iff_lt, rowLens'_eq_rowLen]
      refine lt_of_le_of_lt ?_ hcrl.2
      suffices ∑ x ∈ f.1.support, f.1 x = min_el μ hμ by
        by_cases hfs : 1 ∈ f.1.support
        · rw [← this]
          refine Finset.single_le_sum ?_ hfs
          intro _ _
          exact Nat.zero_le _
        · rw [Finsupp.mem_support_iff] at hfs
          push_neg at hfs
          rw [hfs]
          exact Nat.zero_le (min_el μ hμ)
      rw [card_sub _ _ (sub_cond f.2.1) f.2.2, Multiset.sum_erase' (min_el_mem hμ), h,
        tsub_right_inj ?_ ?_] at h'
      · exact h'
      · rw [← h]
        exact sum_support_subRowLensType_le_card f
      · refine Multiset.single_le_sum ?_ _ (min_el_mem hμ)
        simp
    · refine lt_of_lt_of_le ?_ (f.2.1 1)
      rw [rowLens'_eq_rowLen, ← mem_iff_lt_rowLen, mem_iff_lt_colLen,
        ← length_rowLens]
      exact hcrl


  rw [kostka_recursion γ μ hμ h0 h]

  have hmc1 : μ.card > 1 := by
    contrapose! hμn
    rw [ne_eq, ← Multiset.card_eq_zero] at hμ
    have hμn : μ.card = 1 := by omega
    rw [Multiset.card_eq_one] at hμn
    obtain ⟨m, hm⟩ := hμn
    rw [h, hm, Multiset.sum_singleton] at hγ
    rw [hm, hγ]
  have hnmin : n > min_el μ hμ := by
    contrapose! hmc1
    have hn0 : n > 0 := by omega
    refine Nat.le_of_mul_le_mul_right ?_ hn0
    rw [← smul_eq_mul, one_mul]
    conv => rhs; rw [← hγ, h]
    refine Multiset.card_nsmul_le_sum ?_
    intro x hx
    exact le_trans hmc1 <| min_el_le' hμ hx
  have hmp : min_el μ hμ > 0 := by
    contrapose! h0
    rw [Nat.le_zero] at h0
    rw [← h0]
    exact min_el_mem hμ

  have hnm : n - 1 = (n - (min_el μ hμ) - 1) + min_el μ hμ := by omega
  rw [hnm, add_mul, Finset.mul_sum, Finset.mul_sum]

  have hf : ∀ f : SubRowLensType γ, f ∈ Finset.univ →
      (n - min_el μ hμ - 1) * kostkaNumber (γ.sub f.1) (μ.erase (min_el μ hμ)) ≤
      (μ.card - 2) * kostkaNumber (γ.sub f.1) (Multiset.replicate (n - (min_el μ hμ)) 1) := by
    intro f _
    by_cases h' : (γ.sub f.1).card = (μ.erase (min_el μ hμ)).sum
    swap
    · simp [kostka_ne_card _ _ h']
    · have : μ.card - 2 = (μ.erase (min_el μ hμ)).card - 1 := by
        rw [Multiset.card_erase_of_mem (min_el_mem hμ), Nat.pred_eq_sub_one]
        omega
      rw [this]
      refine kostka_ineq _ _ _ ?_ h' ?_ ?_ ?_
      · rw [ne_eq, ← rowLens_eq_iff, horizontalDiagram_rowLens (by omega)]
        apply_fun List.length
        rw [List.length_singleton]
        exact hrl' f h'
      · contrapose! h0
        exact Multiset.mem_of_mem_erase h0
      · rw [h', Multiset.sum_erase' (min_el_mem hμ), ← h, hγ]
      · right
        rw [ne_eq, erase_min_el_eq_22_iff h0, not_or]
        constructor
        · exact h221
        · exact h222

  refine le_trans (Nat.add_le_add_right (Finset.sum_le_sum hf) _) ?_

  have hsum2 : ∑ f : SubRowLensType γ, (min_el μ hμ) * kostkaNumber
      (γ.sub f.1) (μ.erase (min_el μ hμ)) ≤
      ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1)
      (Multiset.replicate (n - (min_el μ hμ)) 1) := by
    refine Finset.sum_le_sum ?_
    intro f _
    qify
    specialize hf f (Finset.mem_univ f)
    qify at hf
    by_cases hl : μ.card ≠ 2
    · rw [← div_le_iff₀' (by simp; omega)] at hf
      refine le_trans ?_ hf
      rw [mul_div_right_comm]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · rw [le_div_iff₀ (by simp; omega), Nat.cast_sub (by omega), mul_sub,
          Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        suffices min_el μ hμ * μ.card ≤ n by
          qify at this
          simp only [Nat.cast_ofNat, Nat.cast_one, tsub_le_iff_right, ge_iff_le]
          refine le_trans this ?_
          suffices n ≤ n - (min_el μ hμ) - 1 + min_el μ hμ * 2 by
            qify at this
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at this
            exact this
          omega
        rw [← hγ, h]
        have hxm : ∀ x ∈ μ, min_el μ hμ ≤ x := by
          intro x hx
          exact min_el_le' hμ hx
        refine le_trans ?_ (Multiset.card_nsmul_le_sum hxm)
        rw [nsmul_eq_mul, mul_comm]
        rfl
      · exact Nat.cast_nonneg' _
    · by_cases h' : (γ.sub f.1).card = (μ.erase (min_el μ hμ)).sum
      swap
      · simp [kostka_ne_card _ _ h']

      suffices ¬ (γ.sub f.1).rowLens ⊵ (Multiset.sort (· ≥ ·) (μ.erase (min_el μ hμ))) by
        rw [← kostka_pos_iff_dominates h', Nat.pos_iff_ne_zero] at this
        · push_neg at this
          simp [this]
        · contrapose! h0
          exact Multiset.mem_of_mem_erase h0
      push_neg at hl
      specialize hrl' f h'
      contrapose! hrl'
      apply lengths_le_of_dominates at hrl'
      specialize hrl' ?_ ?_
      · rw [← card_eq_sum_rowLens, Multiset.sort_sum, h']
      · intro i
        refine (γ.sub f.1).pos_of_mem_rowLens _ ?_
        exact List.get_mem _ _
      · simp only [ge_iff_le, Multiset.length_sort,
          Multiset.card_erase_of_mem (min_el_mem hμ), hl, Nat.pred_eq_sub_one,
          Nat.add_one_sub_one] at hrl'
        suffices (γ.sub f.1).card ≠ 0 by
          rw [ne_eq, ← eq_bot_iff_card_eq_zero, ← rowLens_eq_iff, bot_rowLens,
            ← List.length_eq_zero_iff] at this
          omega
        rw [h', ne_eq, Multiset.sum_eq_zero_iff_eq_zero, ← Multiset.card_eq_zero,
          Multiset.card_erase_of_mem (min_el_mem hμ), hl]
        · norm_num
        · contrapose! h0
          exact Multiset.mem_of_mem_erase h0



  refine le_trans (Nat.add_le_add_left hsum2 _) ?_
  rw [← Finset.mul_sum, ← Nat.add_one_mul]
  have hmc1 : μ.card - 1 ≠ 0 := by omega
  have hmc : μ.card - 2 + 1 = μ.card - 1 := by omega

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
  simp only [padZeros_parts, Multiset.sum_counts_eq_card, Multiset.card_add,
    Multiset.card_replicate]
  omega

lemma nat_partition2 : (Finset.univ : Finset (Nat.Partition 2)) =
    ({⟨{2}, by simp, by simp⟩, ⟨{1, 1}, by simp, by simp⟩} :
    Finset (Nat.Partition 2)) := by
  ext μ
  have hp := partition2 μ.parts μ.parts_sum (by intro x hx; exact μ.parts_pos hx)
  simp only [Finset.mem_univ, Finset.mem_insert, Nat.Partition.ext_iff,
    Finset.mem_singleton, hp]

/-
The main inequality concering Kostka numbers that I'm trying to prove.
Corollary 4.7 in the paper
-/

theorem kostka_inequality {n d : ℕ} (hn : n ≥ 2) (hd : d ≥ 2) (hnd : n > d)
    (γ : YoungDiagram) (hγc : γ.card = n) (hhd : γ ≠ horizontalDiagram n) :
    (kostkaNumber γ (Multiset.replicate n 1)) *
    (∑ μ : Nat.Partition d, kostkaNumber (hookDiagram n) (padZeros_parts μ n).counts) ≥
    (kostkaNumber (hookDiagram n) (Multiset.replicate n 1)) *
    (∑ μ : Nat.Partition d, kostkaNumber γ ((padZeros_parts μ n).counts)) := by
  rw [kostka_hook_replicate _ (by omega)]
  have hsn : ∑ μ : Nat.Partition d, kostkaNumber (hookDiagram n)
      (padZeros_parts μ n).counts = ∑ μ : Nat.Partition d,
      ((padZeros_parts μ n).counts.card - 1) := by
    refine Finset.sum_congr (by rfl) ?_
    intro μ _
    nth_rw 1 [← padZeros_parts_counts_sum μ (le_of_lt hnd)]
    rw [kostka_hook]
    · exact Multiset.zero_notMem_counts
    · rw [padZeros_parts_counts_sum μ (le_of_lt hnd)]
      exact hn
  rw [hsn, Finset.mul_sum, Finset.mul_sum]
  by_cases hγ : γ ≠ ofRowLens [2, 2] (by simp) ∨ d = 3
  · refine Finset.sum_le_sum ?_
    intro μ _
    conv => rhs; rw [mul_comm]
    refine kostka_ineq γ (padZeros_parts μ n).counts n hhd ?_ ?_ hγc ?_
    · rw [hγc, padZeros_parts_counts_sum μ (le_of_lt hnd)]
    · simp
    · rcases hγ with hγ|hd3
      · left; exact hγ
      · right
        subst hd3
        have hp := partition3 μ.parts μ.parts_sum ?_
        swap
        · intro x hx
          exact μ.parts_pos hx
        rcases hp with hp|hp|hp
        · apply_fun Multiset.count 1
          simp [padZeros_parts, hp, Multiset.counts]
          use 3
          simp [Multiset.mem_replicate]
        · apply_fun Multiset.count 1
          simp [padZeros_parts, hp, Multiset.counts, Multiset.mem_replicate]
        · apply_fun Multiset.count 3
          simp [padZeros_parts, hp, Multiset.counts]
          use 1
          simp [Multiset.mem_replicate]

  push_neg at hγ
  obtain ⟨hγ, hd3⟩ := hγ
  have hn4 : n = 4 := by
    apply_fun YoungDiagram.card at hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, forall_eq, Nat.ofNat_pos,
      card_ofRowLens, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd] at hγ
    rw [← hγc, hγ]
  have hd2 : d = 2 := by omega
  subst hd2
  have h02 : (0 ::ₘ 0 ::ₘ 0 ::ₘ {2}).counts = {3, 1} := by rfl
  have h10 : (1 ::ₘ 0 ::ₘ 0 ::ₘ {1}).counts = {2, 2} := by rfl
  have h1r : Multiset.replicate 4 1 = 1 ::ₘ 1 ::ₘ 1 ::ₘ {1} := by rfl
  simp [nat_partition2, padZeros_parts, hγ, hn4, Multiset.counts_card]
  rw [← h1r, kostka_22, h02, h10]
  have h22 : Multiset.ofList (ofRowLens [2, 2] (by simp)).rowLens = {2, 2} := by
    rw [rowLens_ofRowLens_eq_self]
    rfl
    simp
  rw [← h22, kostka_self]
  suffices ¬ 0 < kostkaNumber (ofRowLens [2, 2] (by simp)) {3, 1} by
    rw [Nat.pos_iff_ne_zero] at this; push_neg at this
    rw [this]; norm_num
  rw [kostka_pos_iff_dominates, ← Multiset.coe_toList {3, 1}, Multiset.coe_sort,
    sort_pair_ge (by norm_num), rowLens_ofRowLens_eq_self, pair_dominates_pair]
  all_goals simp
