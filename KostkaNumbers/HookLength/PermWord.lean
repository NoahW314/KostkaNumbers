import Mathlib


def PermWord (n : ℕ) : Set (List ℕ) :=
  {L : List ℕ | Multiset.ofList L = Multiset.range n ∧ L.length = n}

@[ext]
lemma permWord_ext {n : ℕ} (σ τ : PermWord n) (h : σ.1 = τ.1) : σ = τ := by
  obtain ⟨L, s⟩ := σ
  obtain ⟨L', t⟩ := τ
  subst h
  simp_all only

lemma permWord_getElem_lt {n : ℕ} (σ : PermWord n) (i : ℕ) (h : i < n) :
    (σ.1)[i]'(by rw [σ.2.2]; exact h) < n := by
  let hi : i < σ.1.length := by rw [σ.2.2]; exact h
  let hs := σ.2.1
  rw [← Multiset.mem_range]
  conv => lhs; rw [← hs]
  simp

lemma permWord_nodup {n : ℕ} (L : PermWord n) : L.1.Nodup := by
  simp_rw [List.nodup_iff_count, ← Multiset.coe_count,
    ← Multiset.nodup_iff_count_le_one, L.2.1]
  exact Multiset.nodup_range _

noncomputable
def equivEquivPermWord (n : ℕ) : Equiv.Perm (Fin n) ≃ PermWord n where
  toFun := fun σ : Equiv.Perm (Fin n) ↦ ⟨List.ofFn ((fun i ↦ i.1) ∘ ⇑σ), by
    simp only [PermWord, Set.mem_setOf_eq, List.length_ofFn, and_true]
    ext x
    rw [Multiset.coe_count, Multiset.count_eq_of_nodup (Multiset.nodup_range _)]
    split_ifs with h
    · refine List.count_eq_one_of_mem ?_ ?_
      · rw [List.nodup_ofFn]
        refine Function.Injective.comp ?_ (Equiv.injective σ)
        intro i j
        simp only
        exact fun a ↦ Fin.eq_of_val_eq a
      · simp only [List.mem_ofFn, Function.comp_apply]
        rw [Multiset.mem_range] at h
        use (σ⁻¹ ⟨x, h⟩)
        simp
    · rw [List.count_eq_zero]
      simp only [List.mem_ofFn, Function.comp_apply, not_exists]
      rw [Multiset.mem_range] at h
      omega
    ⟩
  invFun := fun L : PermWord n ↦ Equiv.ofBijective (fun i ↦ ⟨L.1[i.1]'(by
    rw [L.2.2]; exact i.2), permWord_getElem_lt L i.1 i.2⟩)
    (by
    constructor
    · intro i j hij
      simp only [Fin.mk.injEq] at hij
      rw [List.Nodup.getElem_inj_iff] at hij
      · exact Fin.eq_of_val_eq hij
      · exact permWord_nodup L
    · intro j
      have hj : j.1 ∈ L.1 := by
        rw [← Multiset.mem_coe, L.2.1, Multiset.mem_range]
        exact j.2
      obtain ⟨i, ⟨hi, hij⟩⟩ := List.getElem_of_mem hj
      rw [L.2.2] at hi
      use ⟨i, hi⟩
      simp [hij]
    )
  left_inv := by
    intro σ
    ext x
    simp
  right_inv := by
    intro L
    refine permWord_ext _ _ ?_
    simp only
    refine List.ext_getElem ?_ ?_
    all_goals simp [L.2.2]

lemma permWord_card (n : ℕ) : Nat.card (PermWord n) = n.factorial := by
  rw [← Nat.card_eq_of_bijective ⇑(equivEquivPermWord n) (Equiv.bijective (equivEquivPermWord n)),
    Nat.card_perm, Nat.card_fin]
