import Mathlib



variable {γ : YoungDiagram} {T : SemistandardYoungTableau γ}

namespace YoungDiagram

def horizontalDiagram (n : ℕ) := ofRowLens [n] <| List.sorted_singleton n

@[simp] lemma mem_horizontalDiagram (n : ℕ) (x : ℕ × ℕ) : x ∈ horizontalDiagram n ↔
    x.1 = 0 ∧ x.2 < n := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
  constructor
  · intro ⟨j, h⟩
    simp [← h.2, h.1]
  · intro h
    use x.2
    constructor
    · exact h.2
    · rw [← h.1]


noncomputable
def horizontal_ofMultiset (μ : Multiset ℕ) :
    SemistandardYoungTableau (horizontalDiagram μ.toList.length) :=
  ⟨fun i j => if h : j < μ.toList.length ∧ i = 0 then (μ.toList.mergeSort (· ≤ ·))[j]'(by
  rw [List.length_mergeSort]; exact h.1) else 0,
  by
  simp only [mem_horizontalDiagram, and_imp]
  intro i j1 j2 hj hi hj2; symm at hi
  have hj1 : j1 < μ.toList.length := by apply lt_trans hj hj2
  simp only [hj1, hi, and_self, ↓reduceDIte, hj2, ge_iff_le]
  apply List.Sorted.rel_get_of_lt
  · apply List.sorted_mergeSort' (· ≤ ·) μ.toList
  · rw [Fin.mk_lt_mk]; exact hj
  ,
  by
  simp only [mem_horizontalDiagram, and_imp]
  intro i1 i2 j hi hi2
  omega
  ,
  by
  simp only [mem_horizontalDiagram]
  intro i j hij; rw [And.comm] at hij
  simp only [hij, ↓reduceDIte]
  ⟩


end YoungDiagram




namespace SemistandardYoungTableau

def content (T : SemistandardYoungTableau γ) :=
  Multiset.map (fun (i, j) => T i j) (γ.cells).val

def bot_ssyt : SemistandardYoungTableau ⊥ := ⟨0, by simp, by simp, by simp⟩

@[simp] lemma bot_content : bot_ssyt.content = ⊥ := by simp [content]

lemma content_eq_bot_iff : T.content = ⊥ ↔ γ = ⊥ := by
  simp [content]; symm
  exact YoungDiagram.ext_iff

lemma mem_content_of_mem_cells {i j : ℕ} (h : (i, j) ∈ γ) : T i j ∈ T.content := by
  simp only [content, Multiset.mem_map, Finset.mem_val, YoungDiagram.mem_cells, Prod.exists]
  use i; use j

lemma mem_content_of_nonzero {i j : ℕ} (h : T i j ≠ 0) : T i j ∈ T.content := by
  apply mem_content_of_mem_cells
  contrapose! h; exact T.zeros h

def coe_diagrams {γ ζ : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ = ζ) :
    SemistandardYoungTableau ζ := ⟨T.entry, by rw [← h]; exact T.row_weak,
    by rw [← h]; exact T.col_strict, by rw [← h]; exact T.zeros⟩


end SemistandardYoungTableau

lemma list_induction_build {α : Type*} {p : List α → Prop} (L : List α)
    (empty : p []) (build : ∀ i : ℕ, (h : i < L.length) → p (List.take i L) →
    p (List.take (i + 1) L)) : p L := by
  suffices ∀ i ≤ L.length, p (List.take i L) by
    specialize this L.length (by rfl)
    rw [List.take_length] at this
    exact this

  intro i hi
  induction' i with i ih
  · rw [List.take_zero]; exact empty
  · apply build i
    · omega
    · apply ih
      omega

namespace Multiset

lemma list_take_coe (l : List ℕ) (h : List.Sorted (· ≤ ·) l) {i : ℕ} (hi : i < l.length) :
    List.take (i + 1) l =
    (Multiset.ofList (l[i] :: (List.take i l))).toList.mergeSort (· ≤ ·) := by
  suffices (List.take (i + 1) l).Perm (Multiset.ofList (l[i] :: (List.take i l))).toList by
    apply List.eq_of_perm_of_sorted ?_ ?_ (List.sorted_mergeSort' (· ≤ ·) _)
    apply List.Perm.trans this
    apply List.Perm.symm
    apply List.mergeSort_perm
    unfold List.Sorted
    apply List.Pairwise.take h
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, Multiset.coe_eq_coe]
  rw [← List.take_append_getElem hi]
  exact List.perm_append_singleton l[i] (List.take i l)

theorem induction_on_with_le {p : Multiset ℕ → Prop} (S : Multiset ℕ) (empty : p 0)
    (cons : ∀ {n : ℕ} {s : Multiset ℕ}, n ∈ S → s ⊆ S → (∀ m ∈ s, m ≤ n) → p s → p (n ::ₘ s)) :
    p S := by
  let p' : List ℕ → Prop := fun L => p (Multiset.ofList L)
  have hp : ∀ T : Multiset ℕ, p T ↔ p' ((T.toList).mergeSort (· ≤ ·)) := by
    intro T
    suffices Multiset.ofList T.toList = Multiset.ofList (T.toList.mergeSort (· ≤ ·)) by
      simp [p', ← this]
    symm; rw [coe_eq_coe]
    apply List.mergeSort_perm
  rw [hp]
  apply list_induction_build
  · simp [p', empty]
  · intro i hi hs
    have hsi : (S.toList.mergeSort (· ≤ ·)).get ⟨i, hi⟩ ∈ S.toList.mergeSort (· ≤ ·) := by
      exact List.get_mem (S.toList.mergeSort fun x1 x2 ↦ decide (x1 ≤ x2)) ⟨i, hi⟩
    have hss : Multiset.ofList (List.take i (S.toList.mergeSort (· ≤ ·))) ⊆ S := by
      intro a ha;
      rw [mem_coe, List.mem_take_iff_getElem] at ha
      obtain ⟨j, ⟨hj, ha⟩⟩ := ha
      rw [← ha, ← mem_toList]
      apply List.mem_mergeSort.mp (List.get_mem _ _)
    rw [List.mem_mergeSort, mem_toList] at hsi
    specialize cons hsi hss ?_ ?_
    · intro m hm
      rw [mem_coe, List.mem_take_iff_getElem] at hm
      obtain ⟨j, ⟨hj, hm⟩⟩ := hm
      rw [← hm]
      apply List.Sorted.rel_get_of_lt (List.sorted_mergeSort' LE.le S.toList)
      simp; omega
    · simp [p'] at hs; exact hs
    simp only [List.get_eq_getElem, cons_coe, hp] at cons
    suffices List.take (i + 1) (S.toList.mergeSort (· ≤ ·)) =
        (Multiset.ofList ((S.toList.mergeSort (· ≤ ·))[i] ::
        (List.take i (S.toList.mergeSort (· ≤ ·))))).toList.mergeSort (· ≤ ·) by
      rw [this]; exact cons
    apply list_take_coe
    apply List.sorted_mergeSort'

end Multiset


namespace KostkaNumber

open SemistandardYoungTableau
open YoungDiagram



noncomputable def kostkaNumber (γ : YoungDiagram) (μ : Multiset ℕ) :=
  Nat.card {T : SemistandardYoungTableau γ | T.content = μ}

lemma ssyt_bot (T : SemistandardYoungTableau ⊥) : T = bot_ssyt := by
  ext i j
  rw [zeros T (notMem_bot (i, j)), zeros bot_ssyt (notMem_bot (i, j))]

lemma zero_entry_of_bot {i j : ℕ} (h : γ = ⊥) : T i j = 0 := by
  apply T.zeros; rw [h]; apply notMem_bot

lemma kostka_bot_bot : kostkaNumber ⊥ ⊥ = 1 := by
  rw [kostkaNumber, Nat.card_eq_one_iff_exists]
  use ⟨bot_ssyt, by rw [Set.mem_setOf]; exact bot_content⟩
  intro ⟨T, hT⟩
  simp only [Subtype.mk.injEq]
  exact ssyt_bot T

lemma highestWeight_horizontal_content (n : ℕ) :
    (highestWeight (horizontalDiagram n)).content = Multiset.replicate n 0 := by
  simp [content, horizontalDiagram,
    ofRowLens, YoungDiagram.cellsOfRowLens]

lemma entry_zero_of_content_eq_replicate (n : ℕ)
    (h : T.content = Multiset.replicate n 0) (i j : ℕ) : T i j = 0 := by
  by_cases hb : γ = ⊥
  · exact zero_entry_of_bot hb

  suffices T i j ∈ T.content by
    rw [h] at this
    exact Multiset.eq_of_mem_replicate this
  by_cases htij : T i j = 0
  · rw [htij, h]
    refine Multiset.mem_replicate.mpr ?_
    simp only [ne_eq, and_true]
    contrapose! hb
    rw [hb, Multiset.replicate_zero, ← Multiset.bot_eq_zero, content_eq_bot_iff] at h
    exact h
  exact mem_content_of_nonzero htij

theorem kostka_n1 (n : ℕ) : kostkaNumber (horizontalDiagram n) (Multiset.replicate n 0) = 1 := by
  unfold kostkaNumber
  rw [Nat.card_eq_one_iff_exists]
  use ⟨(highestWeight (horizontalDiagram n)), highestWeight_horizontal_content n⟩
  intro ⟨T, hT⟩; rw [Set.mem_setOf] at hT
  rw [Subtype.mk.injEq]
  ext i j
  by_cases hij : j < n ∧ i = 0
  · simp [hij]
    rw [entry_zero_of_content_eq_replicate n hT]

  · rw [And.comm] at hij; simp [hij]
    apply T.zeros; simp only [mem_horizontalDiagram]
    exact hij

lemma horizontalDiagram_succ (n : ℕ) :
    (horizontalDiagram (n+1)).cells.val = (0,n) ::ₘ (horizontalDiagram n).cells.val := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]

lemma append_sorted (L : List ℕ) (hL : List.Sorted (· ≤ ·) L) {n : ℕ} (h : ∀ m ∈ L, m ≤ n) :
    List.Sorted (· ≤ ·) (L ++ [n]) := by
  unfold List.Sorted
  rw [List.pairwise_append]
  constructor; swap; constructor
  · exact List.pairwise_singleton (fun x1 x2 ↦ x1 ≤ x2) n
  · simp; exact h
  · exact hL

lemma cons_sort_eq_sort_append (μ : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ μ, m ≤ n) :
    (n ::ₘ μ).toList.mergeSort (· ≤ ·) = μ.toList.mergeSort (· ≤ ·) ++ [n] := by
  apply List.eq_of_perm_of_sorted ?_ (List.sorted_mergeSort' _ _)

  · apply append_sorted _ (List.sorted_mergeSort' _ _)
    simp; exact h

  apply List.Perm.trans (List.mergeSort_perm (n ::ₘ μ).toList _)
  apply List.Perm.symm
  apply List.Perm.trans (List.perm_append_singleton _ _)
  apply List.Perm.symm
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.cons_inj_right]
  nth_rw 1 [← Multiset.coe_toList μ]
  rw [Multiset.coe_eq_coe]
  apply List.Perm.symm
  apply List.mergeSort_perm

lemma horizontal_ofMultiset_cons_largest (μ : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ μ, m ≤ n) :
    ∀ j < μ.card, (horizontal_ofMultiset (n ::ₘ μ)) 0 j =
    (horizontal_ofMultiset μ) 0 j := by
  intro j hj
  have hj2 : j < μ.card + 1 := by omega
  simp only [DFunLike.coe, horizontal_ofMultiset, Multiset.length_toList, Multiset.card_cons,
    to_fun_eq_coe, hj2, and_self, ↓reduceDIte, hj]
  simp [cons_sort_eq_sort_append μ h, hj]


lemma horizontal_ofMultiset_cons_largest_end (μ : Multiset ℕ) {n : ℕ} (h : ∀ m ∈ μ, m ≤ n) :
    (horizontal_ofMultiset (n ::ₘ μ)) 0 μ.card = n := by
  simp [DFunLike.coe, horizontal_ofMultiset, cons_sort_eq_sort_append μ h]

lemma content_horizontal_ofMultiset (μ : Multiset ℕ) :
    (horizontal_ofMultiset μ).content = μ := by
  apply Multiset.induction_on_with_le μ
  · simp [content, Finset.eq_empty_iff_forall_notMem]
  intro n s _ _ hn hs
  simp [content, horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
  congr
  · apply horizontal_ofMultiset_cons_largest_end s hn
  symm; nth_rw 1 [← hs]; symm
  simp [content, horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
  apply Multiset.map_congr rfl
  intro x hx; rw [Multiset.mem_range] at hx
  exact horizontal_ofMultiset_cons_largest s hn x hx

@[simp] lemma horizontalDiagram_card {n : ℕ} : (horizontalDiagram n).card = n := by
  simp [horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens, YoungDiagram.card]

@[simp] lemma content_card_eq_card : T.content.card = γ.card := by
  simp [content]


lemma list_getElem_map_range {j : ℕ} (n : ℕ) (f : ℕ → ℕ)
    (hj : j < n) (hn : n = (List.map f (List.range n)).length)
    : f j = (List.map f (List.range n))[j]'(by omega) := by
  simp only [List.getElem_map, List.getElem_range]

lemma eq_horizontal_ofMultiset_content {n : ℕ}
    (T : SemistandardYoungTableau (horizontalDiagram n)) :
    T.entry = (horizontal_ofMultiset (T.content)).entry := by
  ext i j
  by_cases hij : ¬(j < T.content.toList.length ∧ i = 0)
  · simp only [horizontal_ofMultiset, hij, reduceDIte]
    apply T.zeros
    simp only [mem_horizontalDiagram]
    rw [Multiset.length_toList, content_card_eq_card, horizontalDiagram_card] at hij
    rw [And.comm]; exact hij
  push_neg at hij
  simp only [horizontal_ofMultiset, hij, and_true, reduceDIte]
  rw [list_getElem_map_range n (fun j => T.entry 0 j)]
  · congr
    apply List.eq_of_perm_of_sorted ?_ ?_ (List.sorted_mergeSort' _ _)
    · apply List.Perm.symm
      apply List.Perm.trans (List.mergeSort_perm _ _)
      rw [← Multiset.coe_eq_coe, Multiset.coe_toList]
      simp [content, horizontalDiagram, ofRowLens, YoungDiagram.cellsOfRowLens]
      rw [← Multiset.map_coe, Multiset.coe_range]
    · unfold List.Sorted
      rw [List.pairwise_map, List.pairwise_iff_getElem]
      simp
      intro i j hi hj hij
      apply T.row_weak hij
      simp [hj]
  · simp [content_card_eq_card, horizontalDiagram_card] at hij
    exact hij.1
  · simp


theorem kostka_horizontal (μ : Multiset ℕ) :
    kostkaNumber (horizontalDiagram μ.toList.length) μ = 1 := by
  unfold kostkaNumber
  rw [Nat.card_eq_one_iff_exists]
  use ⟨horizontal_ofMultiset μ, by
    rw [Set.mem_setOf, content_horizontal_ofMultiset]⟩
  intro ⟨T, hT⟩
  rw [Subtype.mk.injEq]; rw [Set.mem_setOf] at hT
  ext i j; simp only [DFunLike.coe]
  rw [eq_horizontal_ofMultiset_content T]
  congr

theorem kostka_eq_zero {γ : YoungDiagram} {μ : Multiset ℕ}
    (h : ∀ T : SemistandardYoungTableau γ, T.content ≠ μ) : kostkaNumber γ μ = 0 := by
  rw [kostkaNumber, Nat.card_eq_zero]
  left; exact Subtype.isEmpty_of_false h

theorem kostka_ne_card (γ : YoungDiagram) (μ : Multiset ℕ) (h : γ.card ≠ μ.card) :
    kostkaNumber γ μ = 0 := by
  apply kostka_eq_zero
  intro T
  contrapose! h
  symm; rw [← h]
  exact content_card_eq_card

theorem kostka_horizontal' (n : ℕ) (μ : Multiset ℕ) :
    kostkaNumber (horizontalDiagram n) μ = 1 ↔ μ.card = n := by
  constructor; swap
  · intro h
    rw [← h, ← Multiset.length_toList]
    exact kostka_horizontal μ
  contrapose!
  intro h; symm at h
  rw [kostka_ne_card]
  · exact zero_ne_one
  simp [h]





end KostkaNumber
