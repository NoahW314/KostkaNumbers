import Mathlib
import KostkaNumbers.HookLength.HookLength

open YoungDiagram

namespace YoungDiagram

structure PointerTableau (γ : YoungDiagram) where
  pointer : (ℕ × ℕ) → (ℕ × ℕ)
  points_hook : ∀ x ∈ γ, pointer x ∈ γ.hook x.1 x.2
  zeros : ∀ x ∉ γ, pointer x = (0, 0)

@[ext]
lemma pointerTableau_ext {γ : YoungDiagram} (P Q : PointerTableau γ)
    (h : P.pointer = Q.pointer) : P = Q := by
  cases P; cases Q; simp_all

def bot_pointer : PointerTableau ⊥ := ⟨fun x ↦ (0, 0), by simp, by simp⟩


def IsStrict {γ : YoungDiagram} (P : PointerTableau γ) :=
  ∀ x ∈ γ, x ∉ γ.corners → P.pointer x ≠ x

lemma pointerTableau_card (γ : YoungDiagram) :
    Nat.card (PointerTableau γ) = ∏ x ∈ γ.cells, γ.hookLength x.1 x.2 := by
  have hprod : ∏ x ∈ γ.cells, γ.hookLength x.1 x.2 =
      ∏ x ∈ γ.cells, (γ.hook x.1 x.2).card := by
    refine Finset.prod_congr (by rfl) ?_
    intro x hx
    rw [γ.mem_cells] at hx
    symm
    exact γ.hook_card_eq_hookLength x.1 x.2 hx
  rw [hprod, ← Finset.card_pi, ← Nat.card_eq_finsetCard]
  let φ : PointerTableau γ → {f // f ∈ γ.cells.pi fun x ↦ γ.hook x.1 x.2} :=
    fun P ↦ ⟨fun a _ ↦ P.pointer a,
      by
      simp only [Finset.mem_pi, mem_cells, Prod.forall]
      intro i j
      exact P.points_hook (i, j)⟩
  refine Nat.card_eq_of_bijective φ ?_
  constructor
  · intro P₁ P₂ hP
    refine pointerTableau_ext _ _ ?_
    rw [← Set.eqOn_univ]
    intro x hx; clear hx
    simp only [Subtype.mk.injEq, φ] at hP
    by_cases hx : x ∈ γ.cells
    · have hf : (fun a x ↦ P₁.pointer a) x hx = (fun a x ↦ P₂.pointer a) x hx := by rw [hP]
      simp only at hf
      exact hf
    · rw [P₁.zeros x hx, P₂.zeros x hx]
  · intro ⟨f, hf⟩
    use ⟨fun x ↦ if h : x ∈ γ.cells then f x h else (0, 0),
      by
      intro x hx
      simp only [Finset.mem_pi, mem_cells] at hf
      simp [hx, hf x hx],
      by
      intro x hx
      simp [hx]⟩
    simp only [Subtype.mk.injEq, φ]
    ext x hx
    all_goals simp [hx]

lemma strictPointerTableau_nonempty (γ : YoungDiagram) :
    Nonempty {P : PointerTableau γ | IsStrict P} := by
  let P : PointerTableau γ := ⟨fun (i, j) ↦ if hij : (i, j) ∈ γ
    then if h : γ.hookLength i j = 1 then (i, j)
    else Classical.choose (γ.exists_hook_of_hookLength_ne_one i j hij h)
    else (0, 0),
    by
    simp only [Prod.mk.eta, ne_eq, Prod.forall]
    intro i j hij
    simp only [hij, ↓reduceDIte]
    split_ifs with h
    · exact γ.self_mem_hook i j hij
    · have hc := Classical.choose_spec (γ.exists_hook_of_hookLength_ne_one i j hij h)
      exact hc.1
    ,
    by
    simp only [Prod.mk.eta, hookLength_def, Nat.add_eq_right, Nat.add_eq_zero, ne_eq,
      dite_eq_right_iff, Prod.forall]
    intro i j hij hij'
    contradiction⟩
  use P
  rw [Set.mem_setOf_eq]
  intro x hx hcc
  unfold P
  simp only [corners, Finset.mem_filter, mem_cells, hx, corner_iff_hookLength_eq_one _ _ hx,
    true_and] at hcc
  simp only [hx, hcc, ↓reduceDIte, Prod.mk.eta, ne_eq]
  let hxc := Classical.choose_spec (γ.exists_hook_of_hookLength_ne_one x.1 x.2 hx hcc)
  exact hxc.2

lemma strictPointerTableau_finite (γ : YoungDiagram) :
    Finite {P : PointerTableau γ | IsStrict P} := by
  suffices Finite (PointerTableau γ) by exact Subtype.finite
  refine Nat.finite_of_card_ne_zero ?_
  rw [pointerTableau_card, Finset.prod_ne_zero_iff]
  intro x hx
  simp


lemma pointer_mem_diagram {γ : YoungDiagram} {P : PointerTableau γ} (x : ℕ × ℕ)
    (hx : x ∈ γ) : P.pointer x ∈ γ := by
  apply P.points_hook x at hx
  simp [hook] at hx
  exact hx.1

lemma pointer_row_le {γ : YoungDiagram} (P : PointerTableau γ) {x : ℕ × ℕ}
    (hx : x ∈ γ) :
    x.1 ≤ (P.pointer x).1 := by
  have hxp := P.points_hook x hx
  rw [hook, Finset.mem_filter] at hxp
  apply And.right at hxp
  omega

lemma pointer_col_le {γ : YoungDiagram} (P : PointerTableau γ) {x : ℕ × ℕ}
    (hx : x ∈ γ) :
    x.2 ≤ (P.pointer x).2 := by
  have hxp := P.points_hook x hx
  rw [hook, Finset.mem_filter] at hxp
  apply And.right at hxp
  omega

lemma pointer_sum_lt {γ : YoungDiagram} (P : PointerTableau γ) {x : ℕ × ℕ}
    (hx : x ∈ γ) (h : P.pointer x ≠ x) :
    x.1 + x.2 < (P.pointer x).1 + (P.pointer x).2 := by
  have hxp := P.points_hook x hx
  rw [hook, Finset.mem_filter] at hxp
  apply And.right at hxp
  contrapose! h
  ext
  all_goals omega

lemma pointer_rowLen_le {γ : YoungDiagram} (P : PointerTableau γ) {x : ℕ × ℕ}
    (hx : x ∈ γ) :
    γ.rowLen (P.pointer x).1 ≤ γ.rowLen x.1 := γ.rowLen_anti _ _ (pointer_row_le P hx)

lemma pointer_colLen_le {γ : YoungDiagram} (P : PointerTableau γ) {x : ℕ × ℕ}
    (hx : x ∈ γ) :
    γ.colLen (P.pointer x).2 ≤ γ.colLen x.2 := γ.colLen_anti _ _ (pointer_col_le P hx)

lemma rowLen_ge_col_add_one (γ : YoungDiagram) (x : ℕ × ℕ) (hx : x ∈ γ) :
    γ.rowLen x.1 ≥ (x.2 + 1) := by
  suffices γ.rowLen x.1 > x.2 by omega
  rw [mem_iff_lt_rowLen] at hx
  exact hx

lemma colLen_ge_row_add_one (γ : YoungDiagram) (x : ℕ × ℕ) (hx : x ∈ γ) :
    γ.colLen x.2 ≥ (x.1 + 1) := by
  suffices γ.colLen x.2 > x.1 by omega
  rw [mem_iff_lt_colLen] at hx
  exact hx

lemma pointer_hookLength_lt {γ : YoungDiagram} {P : PointerTableau γ} {x : ℕ × ℕ}
    (hx : x ∈ γ) (h : P.pointer x ≠ x) :
    γ.hookLength (P.pointer x).1 (P.pointer x).2 < γ.hookLength x.1 x.2 := by
  simp only [hookLength_def, add_lt_add_iff_right]
  have := pointer_rowLen_le P hx
  have := pointer_colLen_le P hx
  have := pointer_sum_lt P hx h
  have := γ.rowLen_ge_col_add_one x hx
  have := γ.colLen_ge_row_add_one x hx
  have := γ.rowLen_ge_col_add_one (P.pointer x) (pointer_mem_diagram x hx)
  have := γ.colLen_ge_row_add_one (P.pointer x) (pointer_mem_diagram x hx)
  omega

def followPath {γ : YoungDiagram} (P : PointerTableau γ) (x : ℕ × ℕ) (h : x ∈ γ) :=
  if P.pointer x = x then x else
    followPath P (P.pointer x) (pointer_mem_diagram x h)
  termination_by γ.hookLength x.1 x.2
  decreasing_by expose_names; exact pointer_hookLength_lt h h_1

lemma followPath_mem_diagram {γ : YoungDiagram} (P : PointerTableau γ) (x : ℕ × ℕ) (hx : x ∈ γ) :
    followPath P x hx ∈ γ := by
  by_cases hP : P.pointer x = x
  · unfold followPath
    simp [hP, hx]
  · unfold followPath
    simp [hP]
    exact followPath_mem_diagram P (P.pointer x) (pointer_mem_diagram x hx)
  termination_by γ.hookLength x.1 x.2
  decreasing_by exact pointer_hookLength_lt hx hP

lemma followPath_pointer {γ : YoungDiagram} (P : PointerTableau γ) (x : ℕ × ℕ) (hx : x ∈ γ) :
    P.pointer (followPath P x hx) = (followPath P x hx) := by
  by_cases hP : P.pointer x = x
  · unfold followPath
    simp [hP]
  · unfold followPath
    simp [hP]
    exact followPath_pointer P (P.pointer x) (pointer_mem_diagram x hx)
  termination_by γ.hookLength x.1 x.2
  decreasing_by exact pointer_hookLength_lt hx hP

lemma followPath_mem_corners {γ : YoungDiagram} {P : PointerTableau γ} (hP : IsStrict P)
    (x : ℕ × ℕ) (hx : x ∈ γ) : (followPath P x hx) ∈ γ.corners := by
  unfold IsStrict at hP
  specialize hP (followPath P x hx) (followPath_mem_diagram P x hx)
  contrapose! hP
  constructor
  · exact hP
  · exact followPath_pointer P x hx

end YoungDiagram
