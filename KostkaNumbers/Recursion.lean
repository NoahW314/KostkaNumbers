import Mathlib
import KostkaNumbers.Basic
import KostkaNumbers.FinsuppEquiv
import KostkaNumbers.KostkaPos

open YoungDiagram Kostka SemistandardYoungTableau

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

lemma sub_le (γ : YoungDiagram) (f : ℕ →₀ ℕ)
    (h : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1) - (f (i + 1))) :
    γ.sub f h ≤ γ := by
  intro x hx
  simp only [mem_cells, mem_sub, rowLens', Finsupp.coe_mk] at hx
  rw [mem_cells, mem_iff_lt_rowLen]
  refine lt_of_lt_of_le hx ?_
  exact Nat.sub_le (γ.rowLen x.1) (f x.1)

def valid_extend (γ γ' : YoungDiagram) := ∀ i1 i2 j : ℕ, i1 < i2 →
  (i2, j) ∈ γ → (i1, j) ∈ γ'

theorem sub_le_sub_of_sub_le_next {γ : YoungDiagram} {f : ℕ →₀ ℕ}
    (h : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) :
    ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1) - (f (i + 1)) := by
  intro i
  specialize h i
  omega

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

end YoungDiagram

lemma sort_ne_nil' {μ : Multiset ℕ} (h : μ ≠ 0) : (Multiset.sort (· ≤ ·) μ) ≠ [] := by
  rw [ne_eq, List.eq_nil_iff_length_eq_zero, Multiset.length_sort, Multiset.card_eq_zero]
  exact h

def max_el (μ : Multiset ℕ) (hμ : μ ≠ 0) := List.getLast (Multiset.sort (· ≤ ·) μ) (sort_ne_nil' hμ)

lemma le_max_el {μ : Multiset ℕ} (hμ : μ ≠ 0) (i : Fin (Multiset.sort (· ≤ ·) μ).length) :
    (Multiset.sort (· ≤ ·) μ).get i ≤ max_el μ hμ := by
  rw [max_el, List.getLast_eq_getElem (sort_ne_nil' hμ)]
  refine List.Sorted.rel_get_of_le ?_ ?_
  · exact Multiset.sort_sorted _ _
  let hi := i.2
  rw [Fin.mk_le_mk]
  exact Nat.le_sub_one_of_lt hi

lemma le_max_el' {μ : Multiset ℕ} (hμ : μ ≠ 0) {a : ℕ} (ha : a ∈ μ) :
    a ≤ max_el μ hμ := by
  rw [← Multiset.mem_sort (· ≤ ·)] at ha
  apply List.get_of_mem at ha
  obtain ⟨i, ha⟩ := ha
  rw [← ha]
  exact le_max_el hμ i

lemma entry_le_max_el {γ : YoungDiagram} {T : SemistandardYoungTableau γ} {i j : ℕ}
    (hTc : T.content ≠ 0) : T i j ≤ max_el T.content hTc := by
  by_cases hij : T i j = 0
  · rw [hij]
    exact Nat.zero_le (max_el T.content hTc)
  · refine le_max_el' hTc ?_
    exact mem_content_of_nonzero hij

lemma max_el_mem {μ : Multiset ℕ} (hμ : μ ≠ 0) : max_el μ hμ ∈ μ := by
  rw [max_el, ← Multiset.mem_sort (· ≤ ·)]
  exact List.getLast_mem (sort_ne_nil' hμ)

namespace SemistandardYoungTableau

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

end SemistandardYoungTableau

def recUnionType (γ : YoungDiagram) := {f : ℕ →₀ ℕ //
  (∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) ∧ (∀ i, f i ≤ γ.rowLens' i)}

lemma recUnionFinite (γ : YoungDiagram) : Finite (recUnionType γ) := by
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
instance recUnionFintype (γ : YoungDiagram) : Fintype (recUnionType γ) := by
  have := recUnionFinite γ
  exact Fintype.ofFinite (recUnionType γ)

def recUnionTableauType (γ : YoungDiagram) (μ : Multiset ℕ) :=
  {T : SemistandardYoungTableau γ | T.content = μ.fromCounts}

lemma recUnionTableauFinite (γ : YoungDiagram) (μ : Multiset ℕ) :
    Finite (recUnionTableauType γ μ) := by
  exact finite_ssyt_content

noncomputable
instance recUnionTableauFintype (γ : YoungDiagram) (μ : Multiset ℕ) :
    Fintype (recUnionTableauType γ μ) := by
  have := recUnionTableauFinite γ μ
  exact Fintype.ofFinite (recUnionTableauType γ μ)



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

lemma max_el_ne_zero_iff_exists_nonzero {μ : Multiset ℕ} (hμ : μ ≠ 0) :
    max_el μ hμ ≠ 0 ↔ ∃ x ∈ μ, x ≠ 0 := by
  constructor
  · intro h
    use max_el μ hμ
    constructor
    · exact max_el_mem hμ
    · exact h
  · contrapose!
    intro h x hx
    rw [← Nat.le_zero, ← h]
    exact le_max_el' hμ hx

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
    (hTc : T.content ≠ 0) (i j : ℕ) (hij : (i, j) ∈ γ) (hij' : (i, j) ∉
    γ.sub (max_cell_len T hTc) (sub_le_sub_of_sub_le_next (max_cell_len_sub T hTc))) :
    T i j = max_el T.content hTc := by
  simp [max_cell_len] at hij'
  suffices j ≥ Nat.find (exists_max_cell_start T hTc i) by
    exact Nat.find_spec (exists_max_cell_start T hTc i) j this hij
  let hc := find_max_cell_start_le_rowLens' T hTc i
  omega

lemma entry_eq_max_el_iff {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (he : ∃ x ∈ T.content, x ≠ 0)
    (i j : ℕ) : T i j = max_el T.content hTc ↔
    (i, j) ∈ γ.cells \ (γ.sub (max_cell_len T hTc) (sub_le_sub_of_sub_le_next
    (max_cell_len_sub T hTc))).cells := by
  constructor
  · intro hij
    simp [max_cell_len]
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
    (hTc : T.content ≠ 0) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)
    (sub_le_sub_of_sub_le_next (max_cell_len_sub T hTc))) :
    ∃ x ∈ T.content, x ≠ 0 := by
  contrapose! hij'
  simp only [max_cell_len, ne_eq, ite_not, ge_iff_le, mem_sub, Finsupp.coe_mk, not_lt,
    tsub_le_iff_right]
  rw [find_max_cell_start_eq_zero T hTc hij']
  simp

lemma entry_lt_max_el {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)
    (sub_le_sub_of_sub_le_next (max_cell_len_sub T hTc))) :
    T i j < max_el T.content hTc := by
  have hemp := exists_nonzero_of_mem_sub T hTc i j hij'
  contrapose! hij'
  have he : T i j = max_el T.content hTc := antisymm' hij' <| entry_le_max_el hTc
  rw [entry_eq_max_el_iff T hTc hemp, Finset.mem_sdiff, mem_cells] at he
  exact he.2

lemma entry_restrict_lt_max_el {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) (i j : ℕ) (hij' : (i, j) ∈ γ.sub (max_cell_len T hTc)
    (sub_le_sub_of_sub_le_next (max_cell_len_sub T hTc))) :
    (T.restrict (γ.sub_le (max_cell_len T hTc) (sub_le_sub_of_sub_le_next
    (max_cell_len_sub T hTc)))) i j < max_el T.content hTc := by
  simp only [restrict, DFunLike.coe]
  simp only [hij', ↓reduceIte, to_fun_eq_coe]
  exact entry_lt_max_el T hTc i j hij'


lemma count_max_el_restrict_max_cells {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) : Multiset.count (max_el T.content hTc)
    (T.restrict (γ.sub_le (max_cell_len T hTc) (sub_le_sub_of_sub_le_next
    (max_cell_len_sub T hTc)))).content = 0 := by
  simp only [content, Multiset.count_eq_zero, Multiset.mem_map, Finset.mem_val, mem_cells,
    Prod.exists, not_exists, not_and]
  intro i j hij
  refine ne_of_lt ?_
  exact entry_restrict_lt_max_el T hTc i j hij

lemma restrict_max_cells_content {γ : YoungDiagram} (T : SemistandardYoungTableau γ)
    (hTc : T.content ≠ 0) :
    (T.restrict (γ.sub_le (max_cell_len T hTc) (sub_le_sub_of_sub_le_next
    (max_cell_len_sub T hTc)))).content = T.content.remove (max_el T.content hTc) := by
  nth_rw 11 [← restrict_extend T (γ.sub_le (max_cell_len T hTc) (sub_le_sub_of_sub_le_next
    (max_cell_len_sub T hTc))) (γ.sub_valid (max_cell_len T hTc) (max_cell_len_sub T hTc))
    (entry_eq_max_el T hTc)]
  · rw [extend_content]
    · simp only [Multiset.remove, Multiset.count_add, Multiset.count_replicate_self]
      symm
      rw [count_max_el_restrict_max_cells, zero_add, Multiset.add_sub_cancel_right]
    · exact sub_le γ (max_cell_len T hTc) (sub_le_sub_of_sub_le_next (max_cell_len_sub T hTc))
    · exact entry_restrict_lt_max_el T hTc

lemma Multiset.erase_fromCounts_of_min (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    (μ.erase (min_el μ hμ)).fromCounts = μ.fromCounts.remove (μ.card - 1) := by
  nth_rw 3 [←  cons_erase (min_el_mem hμ)]
  rw [cons_fromCounts_of_min (min_el μ hμ), remove, count_add, count_replicate,
    card_erase_eq_ite]
  · simp only [min_el_mem hμ, ↓reduceIte, Nat.pred_eq_sub_one]
    suffices count (μ.card - 1) (μ.erase (min_el μ hμ)).fromCounts = 0 by
      rw [this, zero_add, Multiset.add_sub_cancel_right]
    rw [count_eq_zero]
    refine notMem_fromCounts _ (μ.card - 1) ?_
    rw [remove_of_notMem, card_erase_eq_ite, Nat.pred_eq_sub_one]
    · simp only [min_el_mem hμ, ↓reduceIte, ge_iff_le, le_refl]
    contrapose! h0
    exact mem_of_mem_erase h0
  · intro m hm
    refine min_el_le' hμ ?_
    exact mem_of_mem_erase hm

lemma Multiset.fromCounts_eq_zero_iff (μ : Multiset ℕ) (h0 : 0 ∉ μ) :
    μ.fromCounts = 0 ↔ μ = 0 := by
  rw [← Multiset.bot_eq_zero, ← Multiset.bot_counts_iff, Multiset.fromCounts_counts h0]

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
  refine Multiset.mem_fromCounts μ (μ.card - 1) ?_
  rw [Multiset.remove_of_notMem μ 0 h0]
  simp only [tsub_lt_self_iff, zero_lt_one, and_true]
  rw [Nat.pos_iff_ne_zero, ne_eq, Multiset.card_eq_zero]
  exact hμ

lemma max_el_fromCounts_eq_card_sub_one {μ : Multiset ℕ} (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    max_el μ.fromCounts (by rw [ne_eq, Multiset.fromCounts_eq_zero_iff μ h0]; exact hμ) =
    μ.card - 1 := by
  rw [← max_el_fromCounts_add_one_eq_card hμ h0, add_tsub_cancel_right]

open Classical in
def unionEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ) :
    {T : SemistandardYoungTableau γ | T.content = μ.fromCounts} ≃
    Finset.biUnion (Finset.univ : Finset (recUnionType γ)) (fun ⟨f, hf⟩ ↦
    {T : recUnionTableauType γ μ |
    (T.1.restrict (γ.sub_le f (sub_le_sub_of_sub_le_next hf.1))).content =
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
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [restrict_max_cells_content T.1 hTc]
    nth_rw 1 [T.2, Multiset.erase_fromCounts_of_min μ hμ h0]
    rw [← max_el_fromCounts_eq_card_sub_one hμ h0]
    congr
    exact T.2
    ⟩
  invFun T := ⟨T.1, by simp⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]



lemma Multiset.erase_eq_zero_iff {μ : Multiset ℕ} (hμ : μ ≠ 0) (a : ℕ) :
    μ.erase a = 0 ↔ μ = {a} := by
  constructor
  · intro h
    contrapose! hμ
    ext b
    by_cases hb : b = a
    · rw [hb, Multiset.count_zero]
      contrapose! hμ
      ext b
      by_cases hb : b = a
      · simp [hb]
        apply_fun Multiset.count a at h
        simp at h
        omega
      · simp [← Multiset.count_erase_of_ne hb, h]
    · rw [← Multiset.count_erase_of_ne hb, h]
  · intro h
    rw [h]
    exact Multiset.erase_singleton a

lemma Multiset.fromCounts_singleton {n : ℕ} (hn : n ≠ 0) :
    ({n} : Multiset ℕ).fromCounts = Multiset.replicate n 0 := by
  have hn0 : 0 ∉ ({n} : Multiset ℕ) := by
    rw [mem_singleton]; push_neg; symm; exact hn
  symm
  rw [eq_fromCounts_iff _ _ hn0]

  constructor; swap; constructor; swap; constructor
  · simp [mem_replicate, hn]
  · simp [mem_replicate, ← Nat.pos_iff_ne_zero]
    intro m hm _
    exact hm
  · simp [remove_of_notMem {n} 0 hn0]
  · exact counts_replicate n 0 hn

lemma max_el_replicate {n a : ℕ} (h : n ≠ 0) : max_el (Multiset.replicate n a)
    (by rw [ne_eq, ← Multiset.card_eq_zero, Multiset.card_replicate]; exact h) = a := by
  have hr0 : Multiset.replicate n a ≠ 0 := by
    rw [ne_eq, ← Multiset.card_eq_zero, Multiset.card_replicate]
    exact h
  let ha := max_el_mem hr0
  rw [Multiset.mem_replicate] at ha
  exact ha.2


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

lemma Multiset.sub_sub_of_sub {s t : Multiset ℕ} (h : t ≤ s) : s - (s - t) = t := by
  ext x
  rw [count_sub, count_sub]
  apply Multiset.count_le_of_le x at h
  omega

lemma Multiset.replicate_count_le {s : Multiset ℕ} {a : ℕ} :
    Multiset.replicate (Multiset.count a s) a ≤ s := by
  rw [Multiset.le_iff_count]
  intro x
  rw [Multiset.count_replicate]
  split_ifs  with hx
  · rw [hx]
  · exact Nat.zero_le (Multiset.count x s)

lemma entry_eq_ite_max_el {γ : YoungDiagram} {μ : Multiset ℕ} (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    {f : ℕ →₀ ℕ} (hf : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1))
    (T : SemistandardYoungTableau γ) (hT : T.content = μ.fromCounts)
    (hT' : (T.restrict <| γ.sub_le f (sub_le_sub_of_sub_le_next hf)).content =
    (μ.erase (min_el μ hμ)).fromCounts) (i j : ℕ) (hij : (i, j) ∈ γ)
    (hij' : (i, j) ∉ γ.sub f (sub_le_sub_of_sub_le_next hf)) :
    T i j = (if hTc : (T.restrict (γ.sub_le f (sub_le_sub_of_sub_le_next hf))).content = 0
    then 0 else max_el (T.restrict (γ.sub_le f (sub_le_sub_of_sub_le_next hf))).content hTc
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
    · have hijs : (i, j) ∈ γ.cells \ (γ.sub f (sub_le_sub_of_sub_le_next hf)).cells := by
        simp [hij, hij']
      let hijc := mem_content_sdiff_of_mem_sdiff T
        (γ.sub_le f (sub_le_sub_of_sub_le_next hf)) hijs
      rw [hT, hT', Multiset.erase_fromCounts_of_min μ hμ h0, Multiset.remove,
        Multiset.sub_sub_of_sub, Multiset.mem_replicate] at hijc
      · exact hijc.2
      exact Multiset.replicate_count_le
    · rw [ne_eq, ← Multiset.fromCounts_eq_zero_iff _ h0', ← hT']
      exact hc0

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

noncomputable
def recEquiv (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) (f : ℕ →₀ ℕ) (hf : ∀ i, γ.rowLens' i - f i ≥ γ.rowLens' (i + 1)) :
    {T : recUnionTableauType γ μ |
    (T.1.restrict (γ.sub_le f (sub_le_sub_of_sub_le_next hf))).content =
    (μ.erase (min_el μ hμ)).fromCounts} ≃
    {T : SemistandardYoungTableau (γ.sub f (sub_le_sub_of_sub_le_next hf)) |
    T.content = (μ.erase (min_el μ hμ)).fromCounts} where
  toFun := fun ⟨T, hT⟩ ↦ ⟨T.1.restrict (γ.sub_le f (sub_le_sub_of_sub_le_next hf)), by
    simp at hT
    simp [hT]⟩
  invFun := fun ⟨T, hT⟩ ↦ ⟨⟨T.extend (γ.sub_valid f hf)
    (if hTc : T.content = 0 then 0 else ((max_el T.content hTc) + 1))
    (entry_lt_ite_max_el hf T), by
    unfold recUnionTableauType
    rw [Set.mem_setOf] at hT
    rw [Set.mem_setOf, extend_content T (γ.sub_le f (sub_le_sub_of_sub_le_next hf)), hT]
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
    rw [Set.mem_setOf] at hT
    rw [Set.mem_setOf, T.extend_restrict, hT]
    ⟩
  left_inv := by
    simp only [Function.LeftInverse, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall,
      Subtype.mk.injEq]
    intro T hT hT'
    symm
    nth_rw 1 [← T.restrict_extend (γ.sub_le f (sub_le_sub_of_sub_le_next hf))]
    exact entry_eq_ite_max_el hμ h0 hf T hT hT'
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Set.coe_setOf, Set.mem_setOf_eq,
      Subtype.forall, Subtype.mk.injEq]
    intro T _
    exact T.extend_restrict (γ.sub_le f (sub_le_sub_of_sub_le_next hf)) (γ.sub_valid f hf)
      _ (entry_lt_ite_max_el hf T)


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

open Classical in
theorem kostka_recursion (γ : YoungDiagram) (μ : Multiset ℕ) (hμ : μ ≠ 0) (h0 : 0 ∉ μ)
    (h : γ.card = μ.sum) :
    kostkaNumber γ μ = ∑ f : recUnionType γ,
    kostkaNumber (γ.sub f.1 (sub_le_sub_of_sub_le_next f.2.1)) (μ.erase (min_el μ hμ)) := by
  unfold kostkaNumber

  let hcc := Nat.card_congr (unionEquiv γ μ hμ h0)
  rw [hcc, Nat.card_eq_finsetCard, Finset.card_biUnion]
  · congr; ext f
    let hcc2 := Nat.card_congr (recEquiv γ μ hμ h0 h f.1 f.2.1)
    rw [← hcc2]
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
    rw [recUnionTableauType, Set.mem_setOf] at hT
    by_contra! hfg
    apply exists_mem_sdiff_of_ne hf.1 hg.1 hf.2 hg.2 at hfg
    obtain ⟨x, hxγ, hx⟩ := hfg

    wlog hx' : (x ∈ (γ.sub f (sub_le_sub_of_sub_le_next hf.1)).cells \
      (γ.sub g (sub_le_sub_of_sub_le_next hg.1)).cells) generalizing f g
    · specialize this g hg ?_ f hf ?_ hgs hfs ?_
      · (expose_names; exact h_2)
      · (expose_names; exact h_1)
      · rw [Or.comm]
        exact hx
      · refine this ?_
        simp only [hx', false_or] at hx
        exact hx

    simp only [Finset.mem_sdiff, mem_cells] at hx'
    let Tf := T.restrict (γ.sub_le f (sub_le_sub_of_sub_le_next hf.1))
    let Tg := T.restrict (γ.sub_le g (sub_le_sub_of_sub_le_next hg.1))
    have hxm : Tf x.1 x.2 ∈ Tf.content := by exact mem_content_of_mem_cells hx'.1
    rw [hfs, Multiset.erase_fromCounts_of_min μ hμ h0, restrict_entry _ _ _ _ hx'.1,
      Multiset.mem_remove_of_mem] at hxm
    swap
    · rw [← hT]
      exact mem_content_of_mem_cells hxγ

    have hxc : T x.1 x.2 ∈ T.content - Tg.content := by
      refine mem_content_sdiff_of_mem_sdiff T (γ.sub_le g (sub_le_sub_of_sub_le_next hg.1)) ?_
      simp [hxγ, hx'.2]
    rw [hT, hgs, Multiset.erase_fromCounts_of_min μ hμ h0, Multiset.remove, Multiset.sub_sub_of_sub,
      Multiset.mem_replicate] at hxc
    · rw [← hxc.2] at hxm
      contradiction
    · exact Multiset.replicate_count_le
