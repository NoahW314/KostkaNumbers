import Mathlib

notation n "!" => Nat.factorial n




lemma reworked_bin_lemma (n p : ℕ) (pb : 0 ≤ p) (half : p + 3 ≤ n / 2) :
    (p + 3)! * (n - (p + 3))! ≤ 3! * (n - 3)! := by
  induction p with
  | zero => simp
  | succ p ih =>
    specialize ih (by norm_num) (by omega)
    refine le_trans ?_ ih
    rw [Nat.factorial_succ, show n - (p + 1 + 3) = n - (p + 3) - 1 by omega,
      mul_assoc]
    have hasd : (p+1+3)*((p+3)!*(n-(p+3)-1)!) ≤
        (n-(p+3))*((p+3)!*(n-(p+3)-1)!) := by
      apply Nat.mul_le_mul_right; omega
    refine le_trans hasd ?_
    nth_rw 4 [← Nat.mul_factorial_pred]
    · ring_nf
      rfl
    · omega



lemma iter2_fact {n : ℕ} (h : 0 < n - 2) : n * (n - 1) * (n - 2)! = (n)! := by
  nth_rw 2 [← Nat.mul_factorial_pred, ← Nat.mul_factorial_pred]
  · ring_nf
    congr 1
  all_goals omega

lemma ascFactorial_le_ascFactorial {n m k : ℕ} (h : n ≤ m) :
    n.ascFactorial k ≤ m.ascFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [Nat.ascFactorial_succ]
    exact Nat.mul_le_mul (by omega) ih


theorem factorial_lemma (n ell p : ℕ) (nb : 5 ≤ n) (pb : 2 ≤ p) (ellb : 2 ≤ ell)
    (sqb : ell * p ≤ n) :
    (n-1) * (p+ell-2)! * (p)! * (n-p+1)! ≤
    (ell-1) * (n)! * (n-2*p+1) * (p)! * (ell-2)! := by
  by_cases hell : ell = 2
  · subst hell
    by_cases hp : p = 2
    · subst hp
      simp +arith [show n - 2 + 1 = n - 1 by omega, show n - 4 + 1 = n - 3 by omega]
      calc
        (n - 1) * 2 * 2 * (n - 1)!
        _ = (4 * (n - 1)!) * (n - 1) := by ring
        _ ≤ 4 * (n - 1)! * n := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (n * (n - 1)!) := by ring
        _ = 2 * (2 * (n)!) := by rw [Nat.mul_factorial_pred]; all_goals omega
        _ ≤ (n-3) * (2 * (n)!) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * ((n)! * (n - 3)) := by ring


    · simp +arith
      calc
        (n - 1) * (p)! * (p)! * (n - p + 1)!
        _ = (n - 1) * (p)! * (p)! * ((n - p + 1) * (n - p)!) := by rw [← Nat.factorial_succ]
        _ = (n - 1) * (p)! * (n - p + 1) * ((p)! * (n - p)!) := by ring
        _ ≤ (n - 1) * (p)! * (n - p + 1) * (3! * (n - 3)!) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [show p = p - 3 + 3 by omega]
          refine reworked_bin_lemma n (p - 3) ?_ ?_
          all_goals omega
        _ = (n-1) * (p)! * (n - p + 1) * (n - 3)! * 6 := by
          rw [Nat.factorial_succ, Nat.factorial_two]
          simp +arith; ring
        _ ≤ (n - 1) * (p)! * (n - p + 1) * (n - 3)! * n :=  Nat.mul_le_mul_left _ (by omega)
        _ = (n - 1) * (p)! * n * (n - 3)! * (n - p + 1) := by ring
        _ ≤ (n - 1) * (p)! * n * (n - 3)! * (n - 2) := Nat.mul_le_mul_left _ (by omega)
        _ = (n - 1) * (p)! * n * ((n - 2) * (n - 3)!) := by ring
        _ = (n - 1) * (p)! * n * ((n - 2) * (n - 2 - 1)!) := by rw [show n - 3 = n - 2 - 1 by omega]
        _ = (n - 1) * (p)! * n * (n - 2)! := by rw [Nat.mul_factorial_pred]; omega
        _ = (p)! * (n * (n - 1) * (n - 2)!) := by ring
        _ = (p)! * (n)! := by rw [iter2_fact]; omega
        _ ≤ (p)! * (n)! * (n - 2 * p + 1) := Nat.le_mul_of_pos_right _ (by omega)
        _ = (n)! * (n - 2 * p + 1) * (p)! := by ring

  · by_cases hp : p = 2
    · subst hp
      simp +arith
      rw [show n - 2 + 1 = n - 1 by omega, show n - 4 + 1 = n - 3 by omega]

      calc
        (n - 1) * (ell)! * 2 * (n - 1)!
        _ = (n - 1) * (ell * (ell - 1) * (ell - 2)! * 2 * (n - 1)!) := by
          rw[← iter2_fact (by omega)]; ring
        _ ≤ n * (ell * (ell - 1) * (ell - 2)! * 2 * (n - 1)!) := Nat.mul_le_mul_right _ (by omega)
        _ = n * (ell - 1) * (ell - 2)! * 2 * (n - 1)! * ell := by ring
        _ ≤ n * (ell - 1) * (ell - 2)! * 2 * (n - 1)! * (n - 3) := Nat.mul_le_mul_left _ (by omega)
        _ = (ell - 1)*(n)!*(n-3)*2*(ell-2)! := by
          nth_rw 3 [← Nat.mul_factorial_pred (by omega)]
          ring

    have h2 : ell-2+1 = ell-1 := by omega
    have h3 : ell-1 = (p+ell-2)-(p-1) := by omega
    have h4 : p = p-1+1 := by omega
    have h5 : ell-1+1 = ell := by omega
    have h6 : p-1 = p-2+1 := by omega
    have h7 : ell = (p+ell-2)-(p-2) := by omega
    have h8 : p-2 = (p-3).succ := by omega
    have h9 : ell+1+(p-3) = p+ell-2 := by omega

    have m1 : ell ≤ n-2*p+1 := by
      suffices (ell - 2) * (p - 1) + 2 * p + (ell - 2) ≤ n by
        have : 1 ≤ (ell-2)*(p-1) := Right.one_le_mul (by omega) (by omega)
        omega
      calc
        (ell-2)*(p-1)+2*p+(ell-2)
        _ = (ell-2)*(p-1)+2*(p-1)+(ell-2+2) := by omega
        _ = (ell-2+2)*(p-1)+(ell-2+2)*1 := by simp +arith; rw [← Nat.add_mul]
        _ = (ell-2+2)*(p-1+1) := by rw [← Nat.mul_add]
        _ = ell*p := by congr 1; all_goals omega
        _ ≤ n := by exact sqb

    have h10 : n-p+1+(p-3) = n-2 := by omega


    calc
      (n-1)*(p+ell-2)!*(p)!*(n-p+1)!
      _ = (n-1)*((ell-2)+p)!*(p)!*(n-p+1)! := by congr; omega
      _ = (n-1)*(ell-2)!*((ell-1).ascFactorial p)*(p)!*(n-p+1)! := by
          rw[← Nat.factorial_mul_ascFactorial, h2]
          ring
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(ell.ascFactorial (p-1)) := by
          nth_rw 1 [h4, h3]
          rw [← Nat.ascFactorial_of_sub, ← h3, h5]; ring
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(((p+ell-2)-(p-2)).ascFactorial (p-2+1)) := by
          rw [h6, ← h7]
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*((ell+1).ascFactorial (p-2))*ell := by
          rw [← Nat.ascFactorial_of_sub, ← h7]; ring
      _ ≤ (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*((ell+1).ascFactorial (p-2))*(n-2*p+1) :=
          Nat.mul_le_mul_left _ m1
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(p+ell-2)*
        (n-2*p+1)*((ell+1).ascFactorial (p-3)) := by rw[h8, Nat.ascFactorial_succ, h9]; ring
      _ ≤ (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(p+ell-2)*
        (n-2*p+1)*((n-p+2).ascFactorial (p-3)) := by
          apply Nat.mul_le_mul_left; apply ascFactorial_le_ascFactorial; omega
      _ = (n-1)*(ell-2)!*(ell-1)*(n-2*p+1)*(p+ell-2)*(p)!*
        ((n-p+1)!*((n-p+1+1).ascFactorial (p-3))) := by ring
      _ = (n-1)*(ell-2)!*(ell-1)*(n-2*p+1)*(p)!*(n-2)!*(p+ell-2) := by
          rw[Nat.factorial_mul_ascFactorial, h10]; ring
      _ ≤ (n-1)*(ell-2)!*(ell-1)*(n-2*p+1)*(p)!*(n-2)!*n := by apply Nat.mul_le_mul_left; omega
      _ = (ell-1)*(ell-2)!*(n-2*p+1)*(p)!*(n*(n-1)*(n-2)!) := by ring
      _ = (ell-1)*(n)!*(n-2*p+1)*(p)!*(ell-2)! := by
        rw[iter2_fact]
        · ring
        omega
