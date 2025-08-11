import Mathlib
import KostkaNumbers.FinsuppEquiv
import KostkaNumbers.Content

open YoungDiagram SemistandardYoungTableau


namespace YoungDiagram

lemma antitone_sub_of_antitone (f g : ℕ →₀ ℕ)
    (h : ∀ i, f i - g i ≥ f (i + 1) - g (i + 1)) : Antitone (f - g) := by
  intro i j
  induction' j with j ih
  · intro hi
    rw [nonpos_iff_eq_zero] at hi
    rw [hi]
  · intro hij
    by_cases hij' : i = j + 1
    · rw [hij']
    specialize ih (by omega)
    refine le_trans ?_ ih
    rw [Finsupp.coe_tsub, Pi.sub_apply, Pi.sub_apply]
    exact h j


noncomputable
def sub (γ : YoungDiagram) (f : ℕ →₀ ℕ)
  (h : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1) - (f (i + 1))) : YoungDiagram
  := ofRowLens' (γ.rowLens' - f) (antitone_sub_of_antitone γ.rowLens' f h)

@[simp] lemma mem_sub (γ : YoungDiagram) (x : ℕ × ℕ) {f : ℕ →₀ ℕ}
    {h : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1) - (f (i + 1))} :
    x ∈ γ.sub f h ↔ x.2 < γ.rowLens' x.1 - f x.1 := by
  simp [sub]

@[simp] lemma sub_rowLens (γ : YoungDiagram) (f : ℕ →₀ ℕ) (h : ∀ i, γ.rowLens' i - f i ≥
    γ.rowLens' (i + 1) - (f (i + 1))) : (γ.sub f h).rowLens' = γ.rowLens' - f := by
  simp [sub]

lemma sub_le (γ : YoungDiagram) (f : ℕ →₀ ℕ)
    (h : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1) - (f (i + 1))) :
    γ.sub f h ≤ γ := by
  intro x hx
  simp only [mem_cells, mem_sub, rowLens', Finsupp.coe_mk] at hx
  rw [mem_cells, mem_iff_lt_rowLen]
  refine lt_of_lt_of_le hx ?_
  exact Nat.sub_le (γ.rowLen x.1) (f x.1)


theorem sub_le_sub_of_sub_le_next {γ : YoungDiagram} {f : ℕ →₀ ℕ}
    (h : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) :
    ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1) - (f (i + 1)) := by
  intro i
  specialize h i
  omega

lemma exists_mem_sdiff_of_ne {γ : YoungDiagram} {f g : ℕ →₀ ℕ}
    (hf : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1))
    (hg : ∀ i, γ.rowLens' i - g i ≥ γ.rowLens' (i + 1))
    (hf' : ∀ i, f i ≤ γ.rowLens' i) (hg' : ∀ i, g i ≤ γ.rowLens' i)
    (hfg : f ≠ g) :
    ∃ x ∈ γ, (x ∈ (γ.sub f (sub_le_sub_of_sub_le_next hf)).cells \
    (γ.sub g (sub_le_sub_of_sub_le_next hg)).cells) ∨
    (x ∈ (γ.sub g (sub_le_sub_of_sub_le_next hg)).cells \
    (γ.sub f (sub_le_sub_of_sub_le_next hf)).cells) := by
  rw [Finsupp.ne_iff] at hfg
  obtain ⟨i, hfg⟩ := hfg
  wlog hfg' : f i > g i generalizing f g
  · symm at hfg
    specialize this hg hf hg' hf' hfg ?_
    · push_neg at hfg'
      exact Nat.lt_of_le_of_ne hfg' (id (Ne.symm hfg))
    · obtain ⟨x, this⟩ := this
      rw [Or.comm] at this
      use x
  · use (i, γ.rowLens' i - (g i + 1)); constructor
    · rw [mem_iff_lt_rowLen, ← rowLens'_eq_rowLen]
      specialize hf' i; specialize hg' i
      omega
    · right
      simp only [Finset.mem_sdiff, mem_cells, mem_sub, not_lt, tsub_le_iff_right]
      constructor
      · specialize hf' i
        omega
      · omega

def valid_extend (γ γ' : YoungDiagram) := ∀ i1 i2 j : ℕ, i1 < i2 →
  (i2, j) ∈ γ → (i1, j) ∈ γ'

lemma sub_valid (γ : YoungDiagram) (f : ℕ →₀ ℕ)
    (h : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) :
    valid_extend γ (γ.sub f (sub_le_sub_of_sub_le_next h)) := by
  intro i1 i2 j hi hij2
  rw [mem_iff_lt_rowLen] at hij2
  simp only [mem_sub]
  refine lt_of_lt_of_le ?_ (h i1)
  rw [ rowLens'_eq_rowLen]
  refine lt_of_lt_of_le hij2 ?_
  exact γ.rowLen_anti (i1+1) i2 hi


lemma card_sub (γ : YoungDiagram) (f : ℕ →₀ ℕ) (h : ∀ i, γ.rowLens' i - f i ≥
    γ.rowLens' (i + 1) - (f (i + 1))) (h' : ∀ i, f i ≤ γ.rowLens' i) :
    (γ.sub f h).card = γ.card - ∑ x ∈ f.support, f x := by
  simp only [card_eq_sum_rowLens, List.get_eq_getElem, get_rowLens, ← rowLens'_eq_rowLen,
    sub_rowLens, Finsupp.coe_tsub, Pi.sub_apply]
  have hf : ∑ x ∈ f.support, f x = ∑ x : Fin (γ.rowLens.length), f x.1 := by
    rw [Fin.sum_univ_eq_sum_range]
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · intro x
      simp only [Finsupp.mem_support_iff, ne_eq, length_rowLens, Finset.mem_range]
      contrapose
      intro hx
      suffices γ.rowLens' x = 0 by
        push_neg
        specialize h' x
        rw [this] at h'
        rw [← Nat.le_zero]
        exact h'
      rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero] at hx
      push_neg at hx
      rw [rowLens'_eq_rowLen, hx]
    · simp
    · simp
  rw [hf, ← Finset.sum_tsub_distrib]
  · have hrs : ∑ x : Fin (γ.sub f h).rowLens.length, (γ.rowLens' x.1 - f x.1) =
        ∑ x ∈ Finset.range (γ.sub f h).rowLens.length, (γ.rowLens' x - f x) := by
      rw [← Fin.sum_univ_eq_sum_range]
    have hrs' : ∑ x : Fin γ.rowLens.length, (γ.rowLens' x.1 - f x.1) =
        ∑ x ∈ Finset.range γ.rowLens.length, (γ.rowLens' x - f x) := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [hrs, hrs']
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · simp [colLen_le_of_le (γ.sub_le f h)]
    · simp only [length_rowLens, Finset.mem_sdiff, Finset.mem_range, not_lt, and_imp]
      intro x hx hxs
      rw [← Pi.sub_apply, ← Finsupp.coe_tsub, ← sub_rowLens γ f h, rowLens'_eq_rowLen]
      have : ¬ x < (γ.sub f h).colLen 0 := by omega
      rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen] at this
      push_neg at this
      rw [Nat.le_zero] at this
      exact this
    · simp
  · simp [h']

end YoungDiagram


namespace SemistandardYoungTableau

lemma entry_lt_ite_max_el {γ : YoungDiagram} {f : ℕ →₀ ℕ}
    (hf : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1))
    (T : SemistandardYoungTableau (γ.sub f (sub_le_sub_of_sub_le_next hf)))
    (i j : ℕ) (hij : (i, j) ∈ γ.sub f (sub_le_sub_of_sub_le_next hf)) : T i j <
    (if hTc : T.content = 0 then 0 else ((max_el T.content hTc) + 1)) := by
  split_ifs with hTc
  · apply_fun Multiset.card at hTc
    simp at hTc
    rw [← mem_cells, hTc] at hij
    contradiction
  · suffices T i j ≤ max_el T.content hTc by exact Order.lt_add_one_iff.mpr this
    exact le_max_el' hTc (mem_content_of_mem_cells hij)






def restrict {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ' ≤ γ) :
  SemistandardYoungTableau γ' := ⟨
    fun i j ↦ if (i, j) ∈ γ' then T i j else 0, by
      intro i j1 j2 hj hij2
      simp only [hij2, ↓reduceIte]
      have hij1 : (i, j1) ∈ γ' := γ'.up_left_mem (by rfl) (le_of_lt hj) hij2
      simp only [hij1, reduceIte]
      exact T.row_weak hj (h hij2)
    ,
      by
      intro i1 i2 j hi hij2
      have hij1 : (i1, j) ∈ γ' := γ'.up_left_mem (le_of_lt hi) (by rfl) hij2
      simp only [hij1, ↓reduceIte, hij2]
      exact T.col_strict hi (h hij2)
    ,
      by
      intro i j hij
      simp [hij]
  ⟩

def extend {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ')
  (hγ : valid_extend γ γ') (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
  SemistandardYoungTableau γ := ⟨
    fun i j ↦ if (i, j) ∈ γ then if (i, j) ∈ γ' then T i j else a else 0, by
      intro i j1 j2 hj hij2
      have hij1 : (i, j1) ∈ γ := γ.up_left_mem (by rfl) (le_of_lt hj) hij2
      by_cases hij2' : (i, j2) ∈ γ'
      · have hij1' : (i, j1) ∈ γ' := γ'.up_left_mem (by rfl) (le_of_lt hj) hij2'
        simp [hij1, hij2, hij1', hij2']
        exact T.row_weak hj hij2'
      · by_cases hij1' : (i, j1) ∈ γ'
        · simp [hij1, hij2, hij1', hij2', le_of_lt <| ha i j1 hij1']
        · simp [hij1, hij2, hij1', hij2']
    ,
      by
      intro i1 i2 j hi hij2
      have hij1 : (i1, j) ∈ γ := γ.up_left_mem (le_of_lt hi) (by rfl) hij2
      by_cases hij2' : (i2, j) ∈ γ'
      · have hij1' : (i1, j) ∈ γ' := γ'.up_left_mem (le_of_lt hi) (by rfl) hij2'
        simp [hij1', hij2', hij1, hij2]
        exact T.col_strict hi hij2'
      · have hij1' : (i1, j) ∈ γ' := hγ i1 i2 j hi hij2
        simp [hij1, hij2, hij1', hij2', ha i1 j hij1']
    ,
      by
      intro i j hij
      simp [hij]
  ⟩

@[simp] lemma restrict_entry {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ' ≤ γ)
    (i j : ℕ) (hij : (i, j) ∈ γ') : (T.restrict h) i j = T i j := by
  simp only [restrict, DFunLike.coe, hij, reduceIte]

theorem extend_restrict {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ') (h : γ' ≤ γ)
    (hγ : valid_extend γ γ') (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
    (T.extend hγ a ha).restrict h = T := by
  ext i j
  simp only [extend, restrict, DFunLike.coe]
  simp only [to_fun_eq_coe]
  by_cases hij' : (i, j) ∈ γ'
  · have hij : (i, j) ∈ γ := h hij'
    simp [hij', hij]
  · simp only [hij', ↓reduceIte];
    symm
    exact T.zeros hij'

theorem restrict_extend {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    {a : ℕ} (h : γ' ≤ γ) (hγ : valid_extend γ γ')
    (hγ' : ∀ i j : ℕ, (i, j) ∈ γ → (i, j) ∉ γ' → T i j = a)
    (ha : ∀ i j : ℕ, (i, j) ∈ γ' → (T.restrict h) i j < a) :
    (T.restrict h).extend hγ a ha = T := by
  ext i j
  simp only [restrict, extend, DFunLike.coe]
  simp only [to_fun_eq_coe]
  by_cases hij' : (i, j) ∈ γ'
  · have hij : (i, j) ∈ γ := h hij'
    simp [hij, hij']
  · by_cases hij : (i, j) ∈ γ
    · simp only [hij, ↓reduceIte, hij']
      symm
      exact hγ' i j hij hij'
    · simp only [hij, ↓reduceIte]
      symm
      exact T.zeros hij


lemma extend_content {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ') (h : γ' ≤ γ)
    (hγ : valid_extend γ γ') (a : ℕ) (ha : ∀ i j : ℕ, (i, j) ∈ γ' → T i j < a) :
    (T.extend hγ a ha).content =
    T.content + Multiset.replicate (γ.card - γ'.card) a := by
  simp only [content, extend, DFunLike.coe]
  simp only [Prod.mk.eta, to_fun_eq_coe]
  ext b
  by_cases hb : b = a
  · simp [hb, Multiset.count_map]
    rw [card_sdiff h, Finset.card_def, ← Multiset.card_add]
    congr
    ext x
    simp [Multiset.count_filter, Multiset.count_eq_of_nodup γ'.cells.nodup,
      Multiset.count_eq_of_nodup γ.cells.nodup]
    by_cases hx' : x ∈ γ'
    · have hx : x ∈ γ := h hx'
      simp [hx, hx']
    · by_cases hx : x ∈ γ
      · simp [hx, hx']
      · simp [hx, hx']
  · push_neg at hb; symm at hb
    simp [Multiset.count_replicate, hb, Multiset.count_map]
    congr 1
    ext x
    simp [Multiset.count_filter, Multiset.count_eq_of_nodup γ'.cells.nodup,
      Multiset.count_eq_of_nodup γ.cells.nodup]
    by_cases hx' : x ∈ γ'
    · have hx : x ∈ γ := h hx'
      simp [hx, hx']
    · by_cases hx : x ∈ γ
      · symm at hb
        simp [hx, hx', hb]
      · simp [hx, hx']

lemma mem_content_sdiff_of_mem_sdiff {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hγ : γ' ≤ γ) {i j : ℕ} (h : (i, j) ∈ γ.cells \ γ'.cells) :
    T i j ∈ T.content - (T.restrict hγ).content := by
  simp at h
  have hmap : Multiset.map (fun x ↦ (T.restrict hγ) x.1 x.2) γ'.cells.val =
      Multiset.map (fun x ↦ T x.1 x.2) γ'.cells.val := by
    refine Multiset.map_congr rfl ?_
    intro x hx
    simp only [Finset.mem_val, mem_cells] at hx
    simp only [restrict, DFunLike.coe]
    simp [hx]
  simp [content, hmap, Multiset.mem_sub, Multiset.count_map]
  refine Multiset.card_lt_card ?_
  rw [Multiset.lt_iff_cons_le]
  use (i, j)
  rw [Multiset.le_iff_subset]
  · intro x
    simp only [Multiset.mem_cons, Multiset.mem_filter, Finset.mem_val, mem_cells]
    intro hx
    rcases hx with hx|hx
    · simp [hx, h.1]
    · constructor
      · exact hγ hx.1
      · exact hx.2
  · refine Multiset.nodup_cons.mpr ?_
    constructor
    · simp [h.2]
    · refine Multiset.Nodup.filter _ ?_
      exact γ'.cells.nodup

end SemistandardYoungTableau
