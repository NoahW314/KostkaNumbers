import Mathlib


/-
This shows that YoungDiagrams are equivalent to finitely supported
  antitone functions from ℕ to ℕ
-/

open YoungDiagram

namespace YoungDiagram

def rowLens' (γ : YoungDiagram) : ℕ →₀ ℕ := ⟨Finset.range (γ.colLen 0),
  γ.rowLen, by simp [← Nat.pos_iff_ne_zero, ← mem_iff_lt_colLen, mem_iff_lt_rowLen]⟩

lemma rowLens'_anti (γ : YoungDiagram) : Antitone (γ.rowLens') := by
  rw [Finsupp.coe_mk]
  exact γ.rowLen_anti

lemma rowLens'_eq_rowLen {γ : YoungDiagram} {i : ℕ} : γ.rowLens' i = γ.rowLen i := by
  simp [rowLens']

def ofRowLens' (f : ℕ →₀ ℕ) (hf : Antitone f) : YoungDiagram :=
  ⟨Finset.biUnion f.support (fun i ↦ {i} ×ˢ Finset.range (f i)),
  by
  simp only [IsLowerSet, Finset.singleton_product, Finset.coe_biUnion, Finset.mem_coe,
    Finsupp.mem_support_iff, ne_eq, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_range,
    Set.mem_iUnion, Set.mem_image, Set.mem_Iio, exists_prop, forall_exists_index, and_imp,
    Prod.forall, Prod.mk.injEq, exists_eq_right_right, Prod.mk_le_mk]
  intro a b c d hca hdb x hfx y hyfx hxa hyb
  rw [hxa] at hfx; rw [hxa] at hyfx
  rw [hyb] at hyfx
  constructor
  · contrapose! hfx
    rw [← nonpos_iff_eq_zero, ← hfx]
    exact hf hca
  · refine lt_of_le_of_lt hdb ?_
    refine lt_of_lt_of_le hyfx ?_
    exact hf hca
  ⟩

@[simp] lemma mem_ofRowLens' (f : ℕ →₀ ℕ) (hf : Antitone f) (x : ℕ × ℕ) :
    x ∈ ofRowLens' f hf ↔ x.2 < f x.1 := by
  simp only [ofRowLens', Finset.singleton_product, mem_mk, Finset.mem_biUnion,
    Finsupp.mem_support_iff, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · intro h
    obtain ⟨a, _, ⟨b, hb, hx⟩⟩ := h
    simp [← hx, hb]
  · intro hx
    use x.1
    constructor
    · rw [← Nat.pos_iff_ne_zero]
      exact lt_of_le_of_lt (Nat.zero_le x.2) hx
    · use x.2

@[simp] lemma ofRowLens'_rowLens'_eq_self (γ : YoungDiagram) :
    ofRowLens' γ.rowLens' γ.rowLens'_anti = γ := by
  ext x; simp [rowLens', ← mem_iff_lt_rowLen]

@[simp] lemma rowLens'_ofRowLens'_eq_self (f : ℕ →₀ ℕ) (hf : Antitone f) :
    (ofRowLens' f hf).rowLens' = f := by
  ext n
  simp only [rowLens', ofRowLens', Finsupp.coe_mk, rowLen_eq_card, row]
  suffices Finset.filter (fun c ↦ c.1 = n)
      (f.support.biUnion (fun i ↦ {i} ×ˢ Finset.range (f i))) =
      {n} ×ˢ Finset.range (f n) by
    rw [this]; simp
  aesop

def equivRowLens : YoungDiagram ≃ {f : ℕ →₀ ℕ | Antitone f} where
  toFun γ := ⟨γ.rowLens', γ.rowLens'_anti⟩
  invFun f := ofRowLens' f.1 f.2
  left_inv := ofRowLens'_rowLens'_eq_self
  right_inv := by
    intro ⟨f, hf⟩;
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
    exact rowLens'_ofRowLens'_eq_self f hf

end YoungDiagram
