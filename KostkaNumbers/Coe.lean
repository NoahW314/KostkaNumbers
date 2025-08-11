import Mathlib
import KostkaNumbers.Content

namespace SemistandardYoungTableau

def coe {γ γ' : YoungDiagram} (T : SemistandardYoungTableau γ) (h : γ = γ') :
  SemistandardYoungTableau γ' := ⟨T.entry, by
  rw [to_fun_eq_coe, ← h]; exact T.row_weak
  , by
  rw [to_fun_eq_coe, ← h]; exact T.col_strict
  , by
  rw [to_fun_eq_coe, ← h]; exact T.zeros
  ⟩

@[simp] lemma coe_eval {γ γ' : YoungDiagram} {T : SemistandardYoungTableau γ} {h : γ = γ'}
    {i j : ℕ} : (T.coe h) i j = T i j := by
  simp only [coe, DFunLike.coe]

@[simp] lemma coe_content {γ γ' : YoungDiagram} {T : SemistandardYoungTableau γ} {h : γ = γ'} :
    (T.coe h).content = T.content := by
  simp [content, h]

end SemistandardYoungTableau
