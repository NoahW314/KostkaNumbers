import Mathlib
import KostkaNumbers.Util.MinMaxEl
import KostkaNumbers.Basic
import KostkaNumbers.FinsuppEquiv
import KostkaNumbers.RestrictExtend


open YoungDiagram Kostka SemistandardYoungTableau

def SubRowLensType (γ : YoungDiagram) := {f : ℕ →₀ ℕ //
  (∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) ∧ (∀ i, f i ≤ γ.rowLens' i)}

lemma finite_subRowLensType (γ : YoungDiagram) : Finite (SubRowLensType γ) := by
  suffices Finite {f : ℕ →₀ ℕ | (∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) ∧
    (∀ i, f i ≤ γ.rowLens' i)} by exact this
  have hasd : Finite {f : ℕ →₀ ℕ | f ≤ γ.rowLens'} := by
    exact instFiniteSubtypeLeOfLocallyFiniteOrderBot
  refine Finite.Set.subset {f : ℕ →₀ ℕ | f ≤ γ.rowLens'} ?_
  intro f hf
  rw [Set.mem_setOf] at hf
  rw [Set.mem_setOf]
  intro i
  exact hf.2 i

noncomputable
instance subRowLensFintype (γ : YoungDiagram) : Fintype (SubRowLensType γ) := by
  have := finite_subRowLensType γ
  exact Fintype.ofFinite (SubRowLensType γ)




lemma exists_max_cell_start {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i : ℕ) :
    ∃ j : ℕ, ∀ j' ≥ j, (i, j') ∈ γ → T i j' = max_el T.content hTc := by
  use γ.rowLen i
  intro j
  rw [mem_iff_lt_rowLen]
  intro hij hij'
  omega

open Classical in
lemma find_max_cell_start_le {γ : YoungDiagram}
    (T : SemistandardYoungTableau γ) (hTc : T.content ≠ 0) {i j : ℕ}
    (h : T i j = max_el T.content hTc) :
    Nat.find (exists_max_cell_start T hTc i) ≤ j := by
  refine Nat.find_min' (exists_max_cell_start T hTc i) ?_
  intro j' hj hij'
  refine antisymm (entry_le_max_el hTc) ?_
  rw [← h]
  exact T.row_weak_of_le hj hij'


open Classical in
lemma find_max_cell_start_eq_zero {γ : YoungDiagram}
    (T : SemistandardYoungTableau γ) (hTc : T.content ≠ 0) {i : ℕ}
    (h : ∀ x ∈ T.content, x = 0) :
    Nat.find (exists_max_cell_start T hTc i) = 0 := by
  rw [← Nat.le_zero]
  refine find_max_cell_start_le T hTc ?_
  have hT : ¬max_el T.content hTc ≠ 0 := by
    rw [max_el_ne_zero_iff_exists_nonzero hTc]
    push_neg
    exact h
  push_neg at hT
  rw [hT]
  by_cases hi : (i, 0) ∈ γ
  · exact h (T i 0) (mem_content_of_mem_cells hi)
  · exact T.zeros hi

open Classical in
lemma entry_find_eq_max_el {γ : YoungDiagram} {T : SemistandardYoungTableau γ}
    (hTc : T.content ≠ 0) (i : ℕ) (h : (i, Nat.find (exists_max_cell_start T hTc i)) ∈ γ) :
    T i (Nat.find (exists_max_cell_start T hTc i)) = max_el T.content hTc := by
  let hm := Nat.find_spec (exists_max_cell_start T hTc i)
  exact hm (Nat.find (exists_max_cell_start T hTc i)) (by rfl) h

open Classical in
noncomputable
def max_cell_len {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
  (hTc : T.content ≠ 0) : ℕ →₀ ℕ :=
  ⟨ if max_el T.content hTc ≠ 0 then
    {i ∈ Finset.range <| γ.colLen 0 | ∃ j, T i j = max_el T.content hTc}
    else Finset.range <| γ.colLen 0,
  fun i ↦ γ.rowLens' i - Nat.find (exists_max_cell_start T hTc i),
    by
    split_ifs with hTc0
    swap
    · rw [max_el_ne_zero_iff_exists_nonzero] at hTc0
      push_neg at hTc0
      simp only [Finset.mem_range, ← mem_iff_lt_colLen, rowLens'_eq_rowLen, ge_iff_le,
        find_max_cell_start_eq_zero T hTc hTc0, tsub_zero, ne_eq, ← Nat.pos_iff_ne_zero,
        ← mem_iff_lt_rowLen, implies_true]

    intro i
    constructor
    · intro hi
      simp [← mem_iff_lt_colLen] at hi
      obtain ⟨hi, ⟨j, hj⟩⟩ := hi
      simp only
      refine ne_of_gt ?_
      simp only [tsub_pos_iff_lt, rowLens'_eq_rowLen]
      rw [← hj] at hTc0
      refine lt_of_le_of_lt (find_max_cell_start_le T hTc hj) ?_
      rw [← mem_iff_lt_rowLen]
      contrapose! hTc0
      exact T.zeros hTc0
    · simp only [Finset.mem_filter, Finset.mem_range]
      intro hi
      constructor
      · rw [← mem_iff_lt_colLen, mem_iff_lt_rowLen, Nat.pos_iff_ne_zero]
        rw [rowLens'_eq_rowLen] at hi
        contrapose! hi
        rw [hi, zero_tsub]
      · contrapose! hi
        suffices ¬ Nat.find (exists_max_cell_start T hTc i) < γ.rowLen i by
          push_neg at this
          rw [rowLens'_eq_rowLen]
          exact Nat.sub_eq_zero_of_le this
        rw [← mem_iff_lt_rowLen]
        contrapose! hi
        use (Nat.find (exists_max_cell_start T hTc i))
        exact entry_find_eq_max_el hTc i hi
    ⟩



open Classical in
lemma max_cell_len_sub {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i : ℕ) : γ.rowLens' i - (max_cell_len T hTc i) ≥
    γ.rowLens' (i + 1) := by
  simp [max_cell_len, Finsupp.coe_mk]
  rw [Nat.sub_sub_eq_min, Nat.le_min]
  constructor
  · exact γ.rowLens'_anti (Nat.le_add_right i 1)
  · refine Nat.le_of_not_gt ?_
    rw [rowLens'_eq_rowLen, gt_iff_lt, ← mem_iff_lt_rowLen]
    by_contra! h
    let hc := T.col_strict (Nat.lt_add_one i) h
    rw [entry_find_eq_max_el hTc i
      (γ.up_left_mem (le_of_lt (Nat.lt_add_one i)) (by rfl) h)] at hc
    contrapose! hc
    exact entry_le_max_el hTc

open Classical in
lemma max_cell_len_le_rowLens' {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i : ℕ) : (max_cell_len T hTc i) ≤ γ.rowLens' i := by
  simp [max_cell_len]

open Classical in
lemma find_max_cell_start_le_rowLens' {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i : ℕ) : Nat.find (exists_max_cell_start T hTc i) ≤
    γ.rowLens' i := by
  refine Nat.find_min' _ ?_
  intro j hij hij'
  rw [mem_iff_lt_rowLen, ← rowLens'_eq_rowLen] at hij'
  omega

open Classical in
lemma entry_eq_max_el {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i j : ℕ) (hij : (i, j) ∈ γ)
    (hij' : (i, j) ∉ γ.sub (max_cell_len T hTc)) :
    T i j = max_el T.content hTc := by
  rw [mem_sub _ _ (sub_cond (max_cell_len_sub T hTc))] at hij'
  simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk, not_lt,
    tsub_le_iff_right] at hij'
  suffices j ≥ Nat.find (exists_max_cell_start T hTc i) by
    exact Nat.find_spec (exists_max_cell_start T hTc i) j this hij
  let hc := find_max_cell_start_le_rowLens' T hTc i
  omega

lemma entry_eq_max_el_iff {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (he : ∃ x ∈ T.content, x ≠ 0)
    (i j : ℕ) : T i j = max_el T.content hTc ↔
    (i, j) ∈ γ.cells \ (γ.sub (max_cell_len T hTc)).cells := by
  constructor
  · intro hij
    rw [Finset.mem_sdiff, mem_cells, mem_cells,
      mem_sub _ _ (sub_cond (max_cell_len_sub T hTc))]
    simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk, not_lt, tsub_le_iff_right]
    constructor
    · contrapose! hij
      symm
      rw [T.zeros hij, max_el_ne_zero_iff_exists_nonzero]
      exact he
    · apply find_max_cell_start_le T hTc at hij
      let hc := find_max_cell_start_le_rowLens' T hTc i
      omega
  · intro hij
    simp only [Finset.mem_sdiff, mem_cells] at hij
    exact entry_eq_max_el T hTc i j hij.1 hij.2

lemma exists_nonzero_of_mem_sub {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    ∃ x ∈ T.content, x ≠ 0 := by
  contrapose! hij'
  rw [mem_sub _ _ (sub_cond (max_cell_len_sub T hTc))]
  simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, Finsupp.coe_mk, not_lt,
    tsub_le_iff_right]
  rw [find_max_cell_start_eq_zero T hTc hij']
  simp

lemma entry_lt_max_el {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    T i j < max_el T.content hTc := by
  have hemp := exists_nonzero_of_mem_sub T hTc i j hij'
  contrapose! hij'
  have he : T i j = max_el T.content hTc := antisymm' hij' <| entry_le_max_el hTc
  rw [entry_eq_max_el_iff T hTc hemp, Finset.mem_sdiff, mem_cells] at he
  exact he.2

lemma entry_restrict_lt_max_el {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)) :
    (T.restrict (γ.sub_le (max_cell_len T hTc) (sub_cond (max_cell_len_sub T hTc))))
    i j < max_el T.content hTc := by
  simp only [restrict, DFunLike.coe]
  simp only [hij', ↓reduceIte, to_fun_eq_coe]
  exact entry_lt_max_el T hTc i j hij'


lemma count_max_el_restrict_max_cells {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) : Multiset.count (max_el T.content hTc)
    (T.restrict (γ.sub_le (max_cell_len T hTc) (sub_cond
    (max_cell_len_sub T hTc)))).content = 0 := by
  simp only [content, Multiset.count_eq_zero, Multiset.mem_map, Finset.mem_val, mem_cells,
    Prod.exists, not_exists, not_and]
  intro i j hij
  refine ne_of_lt ?_
  exact entry_restrict_lt_max_el T hTc i j hij

lemma restrict_max_cells_content {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) :
    (T.restrict (γ.sub_le (max_cell_len T hTc) (sub_cond
    (max_cell_len_sub T hTc)))).content = T.content.remove (max_el T.content hTc) := by
  nth_rw 7 [← restrict_extend T (γ.sub_le (max_cell_len T hTc)
    (sub_cond (max_cell_len_sub T hTc))) (γ.sub_valid (max_cell_len T hTc)
    (max_cell_len_sub T hTc)) (entry_eq_max_el T hTc)]
  rw [extend_content]
  · simp only [Multiset.remove, Multiset.count_add, Multiset.count_replicate_self]
    symm
    rw [count_max_el_restrict_max_cells, zero_add, Multiset.add_sub_cancel_right]
  · exact sub_le γ (max_cell_len T hTc) (sub_cond (max_cell_len_sub T hTc))
  · exact entry_restrict_lt_max_el T hTc


lemma max_el_fromCounts_add_one_eq_card {μ : Multiset ℕ} (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    max_el μ.fromCounts (by rw [ne_eq, Multiset.fromCounts_eq_zero_iff μ h0]; exact hμ) + 1 =
    μ.card := by
  have hμ' : μ.fromCounts ≠ 0 := by rw [ne_eq, Multiset.fromCounts_eq_zero_iff μ h0]; exact hμ
  have hle : max_el μ.fromCounts hμ' + 1 ≤ μ.card := by
    suffices max_el μ.fromCounts hμ' < μ.card by exact this
    rw [← Multiset.mem_fromCounts_iff h0]
    exact max_el_mem hμ'
  refine antisymm hle ?_
  suffices μ.card - 1 ≤ max_el μ.fromCounts hμ' by omega
  refine le_max_el' hμ' ?_
  refine Multiset.mem_fromCounts μ h0 (μ.card - 1) ?_
  simp only [tsub_lt_self_iff, zero_lt_one, and_true]
  rw [Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero]
  exact hμ

lemma max_el_fromCounts_eq_card_sub_one {μ : Multiset ℕ} (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    max_el μ.fromCounts (by rw [ne_eq, Multiset.fromCounts_eq_zero_iff μ h0]; exact hμ) =
    μ.card - 1 := by
  rw [← max_el_fromCounts_add_one_eq_card hμ h0, add_tsub_cancel_right]

open Classical in
def unionEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    SemistandardYoungTableauWithContent γ μ ≃
    Finset.biUnion (Finset.univ : Finset (SubRowLensType γ)) (fun ⟨f, hf⟩ ↦
    {T : SemistandardYoungTableauWithContent γ μ |
    (T.1.restrict (γ.sub_le f (sub_cond hf.1))).content =
    (μ.erase (min_el μ hμ)).fromCounts}) where
  toFun T := ⟨T, by
    have hTc : T.1.content ≠ 0 := by
      rw [T.2, ne_eq, Multiset.fromCounts_eq_zero_iff μ h0]
      exact hμ
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    use ⟨max_cell_len T.1 hTc, by
      constructor
      · exact max_cell_len_sub T.1 hTc
      · exact max_cell_len_le_rowLens' T.1 hTc
      ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [restrict_max_cells_content T.1 hTc]
    nth_rw 1 [T.2, Multiset.erase_fromCounts_of_min μ hμ]
    rw [← max_el_fromCounts_eq_card_sub_one hμ h0]
    congr
    exact T.2
    ⟩
  invFun T := ⟨T.1, by simp⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]










lemma entry_eq_ite_max_el {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    {f : ℕ →₀ ℕ} (hf : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1))
    (T : SemistandardYoungTableau γ) (hT : T.content = μ.fromCounts)
    (hT' : (T.restrict <| γ.sub_le f (sub_cond hf)).content =
    (μ.erase (min_el μ hμ)).fromCounts) (i j : ℕ) (hij : (i, j) ∈ γ)
    (hij' : (i, j) ∉ γ.sub f) :
    T i j = (if hTc : (T.restrict (γ.sub_le f (sub_cond hf))).content = 0
    then 0 else max_el (T.restrict (γ.sub_le f (sub_cond hf))).content hTc
    + 1) := by
  split_ifs with hc0
  · rw [hT', Multiset.fromCounts_eq_zero_iff, Multiset.erase_eq_zero_iff hμ] at hc0
    · rw [hc0, Multiset.fromCounts_singleton] at hT
      · have hTc : T i j ∈ T.content := T.mem_content_of_mem_cells hij
        rw [hT, Multiset.mem_replicate] at hTc
        exact hTc.2
      · contrapose! h0
        rw [← h0]
        exact min_el_mem hμ
    · contrapose! h0
      exact Multiset.mem_of_mem_erase h0
  · simp only [hT']
    have h0' : 0 ∉ μ.erase (min_el μ hμ) := by
      contrapose! h0
      exact Multiset.mem_of_mem_erase h0
    rw [max_el_fromCounts_add_one_eq_card ?_ h0',
      Multiset.card_erase_of_mem (min_el_mem hμ), Nat.pred_eq_sub_one]
    · have hijs : (i, j) ∈ γ.cells \ (γ.sub f).cells := by
        simp [hij, hij']
      let hijc := mem_content_sdiff_of_mem_sdiff T
        (γ.sub_le f (sub_cond hf)) hijs
      rw [hT, hT', Multiset.erase_fromCounts_of_min μ hμ, Multiset.remove,
        tsub_tsub_cancel_of_le, Multiset.mem_replicate] at hijc
      · exact hijc.2
      exact Multiset.replicate_count_le
    · rw [ne_eq, ← Multiset.fromCounts_eq_zero_iff _ h0', ← hT']
      exact hc0



noncomputable
def recEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) (f : ℕ →₀ ℕ) (hf : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) :
    {T : SemistandardYoungTableauWithContent γ μ |
    (T.1.restrict (γ.sub_le f (sub_cond hf))).content =
    (μ.erase (min_el μ hμ)).fromCounts} ≃
    SemistandardYoungTableauWithContent (γ.sub f)
    (μ.erase (min_el μ hμ)) where
  toFun := fun ⟨T, hT⟩ ↦ ⟨T.1.restrict (γ.sub_le f (sub_cond hf)), by
    simp at hT
    simp [SemistandardYoungTableauWithContent, hT]⟩
  invFun := fun ⟨T, hT⟩ ↦ ⟨⟨T.extend (γ.sub_valid f hf)
    (if hTc : T.content = 0 then 0 else ((max_el T.content hTc) + 1))
    (entry_lt_ite_max_el T), by
    rw [SemistandardYoungTableauWithContent, Set.mem_setOf] at hT
    rw [SemistandardYoungTableauWithContent, Set.mem_setOf,
      extend_content T (γ.sub_le f (sub_cond hf)), hT]
    apply_fun Multiset.card at hT
    simp only [content_card_eq_card, Multiset.fromCounts_card] at hT
    rw [hT, h, ← Multiset.sum_erase (min_el_mem hμ), Nat.add_sub_cancel]
    suffices (if hTc : (μ.erase (min_el μ hμ)).fromCounts = 0 then 0 else
        max_el (μ.erase (min_el μ hμ)).fromCounts hTc + 1) =
        (μ.erase (min_el μ hμ)).card by
      rw [this, ← Multiset.cons_fromCounts_of_min]
      congr
      exact cons_erase_min_el hμ
      intro m hm
      refine min_el_le' hμ ?_
      exact Multiset.mem_of_mem_erase hm
    have h0' : 0 ∉ (μ.erase (min_el μ hμ)) := by
      contrapose! h0
      exact Multiset.mem_of_mem_erase h0
    by_cases hTc : (μ.erase (min_el μ hμ)).fromCounts = 0
    · simp only [hTc, ↓reduceDIte]
      rw [Multiset.fromCounts_eq_zero_iff _ h0'] at hTc
      rw [hTc, Multiset.card_zero]
    · simp only [hTc, ↓reduceDIte]
      refine max_el_fromCounts_add_one_eq_card ?_ h0'
      rw [ne_eq, ← Multiset.fromCounts_eq_zero_iff _ h0']
      exact hTc
    ⟩, by
    rw [SemistandardYoungTableauWithContent, Set.mem_setOf] at hT
    rw [Set.mem_setOf, T.extend_restrict, hT]
    ⟩
  left_inv := by
    simp only [Function.LeftInverse, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall,
      Subtype.mk.injEq]
    intro T hT hT'
    symm
    nth_rw 1 [← T.restrict_extend (γ.sub_le f (sub_cond hf))]
    exact entry_eq_ite_max_el hμ h0 hf T hT hT'
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Subtype.forall, Subtype.mk.injEq]
    intro T _
    exact T.extend_restrict (γ.sub_le f (sub_cond hf)) (γ.sub_valid f hf)
      _ (entry_lt_ite_max_el T)



open Classical in
theorem kostka_recursion (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) :
    kostkaNumber γ μ = ∑ f : SubRowLensType γ,
    kostkaNumber (γ.sub f.1) (μ.erase (min_el μ hμ)) := by

  let hcc := Nat.card_congr (unionEquiv γ μ hμ h0)
  rw [kostkaNumber_eq_card_ssyt_content, hcc, Nat.card_eq_finsetCard, Finset.card_biUnion]
  · congr; ext f
    let hcc2 := Nat.card_congr (recEquiv γ μ hμ h0 h f.1 f.2.1)
    rw [kostkaNumber_eq_card_ssyt_content, ← hcc2]
    symm
    refine Nat.subtype_card _ ?_
    split
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      implies_true]
  · intro ⟨f, hf⟩ _ ⟨g, hg⟩ _ hfg s hfs hgs ⟨T, hT⟩ hTs
    contrapose! hfg
    rw [Subtype.mk.injEq]
    specialize hfs hTs; specialize hgs hTs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hgs
    rw [SemistandardYoungTableauWithContent, Set.mem_setOf] at hT
    by_contra! hfg
    apply exists_mem_sdiff_of_ne hf.1 hg.1 hf.2 hg.2 at hfg
    obtain ⟨x, hxγ, hx⟩ := hfg

    wlog hx' : (x ∈ (γ.sub f).cells \ (γ.sub g).cells) generalizing f g
    · specialize this g hg ?_ f hf ?_ hgs hfs ?_
      · (expose_names; exact h_2)
      · (expose_names; exact h_1)
      · rw [Or.comm]
        exact hx
      · refine this ?_
        simp only [hx', false_or] at hx
        exact hx

    simp only [Finset.mem_sdiff, mem_cells] at hx'
    let Tf := T.restrict (γ.sub_le f (sub_cond hf.1))
    let Tg := T.restrict (γ.sub_le g (sub_cond hg.1))
    have hxm : Tf x.1 x.2 ∈ Tf.content := by exact mem_content_of_mem_cells hx'.1
    rw [hfs, Multiset.erase_fromCounts_of_min μ hμ, restrict_entry _ _ _ _ hx'.1,
      Multiset.mem_remove_of_mem] at hxm
    swap
    · rw [← hT]
      exact mem_content_of_mem_cells hxγ

    have hxc : T x.1 x.2 ∈ T.content - Tg.content := by
      refine mem_content_sdiff_of_mem_sdiff T (γ.sub_le g (sub_cond hg.1)) ?_
      simp [hxγ, hx'.2]
    rw [hT, hgs, Multiset.erase_fromCounts_of_min μ hμ, Multiset.remove, tsub_tsub_cancel_of_le,
      Multiset.mem_replicate] at hxc
    · rw [← hxc.2] at hxm
      contradiction
    · exact Multiset.replicate_count_le





lemma sum_support_subRowLensType_le_card {γ : YoungDiagram} (f : SubRowLensType γ) :
    ∑ x ∈ f.1.support, f.1 x ≤ γ.card := by
  rw [card_eq_sum_rowLen, Fin.sum_univ_eq_sum_range]
  simp only [← rowLens'_eq_rowLen]
  have hfs : f.1.support ⊆ Finset.range (γ.rowLens.length + 1) := by
    intro x
    simp
    contrapose!
    intro hx
    suffices γ.rowLen x = 0 by rw [← Nat.le_zero, ← this]; exact f.2.2 x
    exact γ.rowLen_eq_zero (by omega)
  refine le_trans (Finset.sum_le_sum_of_subset hfs) ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  exact f.2.2 i

open Classical in
lemma sum_subRowLensType_with_sum_eq {γ : YoungDiagram} {μ : Multiset ℕ} {hμ : μ ≠ 0}
    (h : γ.card = μ.sum) :
    ∑ f : SubRowLensType γ, kostkaNumber (γ.sub f.1)
    (μ.erase (min_el μ hμ)) = ∑ f : SubRowLensType γ with (∑ x ∈ f.1.support,
    f.1 x = min_el μ hμ), kostkaNumber (γ.sub f.1)
    (μ.erase (min_el μ hμ)) := by
  symm
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · intro f _; exact Finset.mem_univ f
  · intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hf
    refine kostka_ne_card _ _ ?_
    rw [Multiset.sum_erase' (min_el_mem hμ), card_sub _ _ (sub_cond f.2.1) f.2.2]
    have hcf := sum_support_subRowLensType_le_card f
    have hmm := Multiset.le_sum_of_mem (min_el_mem hμ)
    omega
  · intro _ _; rfl

theorem kostka_recursion' (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) :
    kostkaNumber γ μ = ∑ f : SubRowLensType γ with ∑ x ∈ f.1.support, f.1 x = min_el μ hμ,
    kostkaNumber (γ.sub f.1) (μ.erase (min_el μ hμ)) := by
  rw [kostka_recursion _ _ hμ h0 h, sum_subRowLensType_with_sum_eq h]
