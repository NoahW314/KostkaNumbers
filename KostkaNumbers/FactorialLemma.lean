import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic

notation n "!" => Nat.factorial n




lemma reworked_bin_lemma (n p : ℕ) (pb : 0 ≤ p) (half : p + 3 ≤ n / 2)
  : (p+3)!*(n-(p+3))! ≤ 3!*(n-3)! := by induction p with
  | zero => simp
  | succ p ih =>
    have pb : 0 ≤ p := by omega
    specialize ih pb
    have half : p+3 ≤ n/2 := by omega
    specialize ih half
    have tot : 0 < (n-(p+3)) := by omega

    have h5 : n-(p+1+3) = n-(p+3)-1 := by omega
    have h6 : p+1+3 ≤ n-(p+3) := by omega
    have h7 : (p+3)!*(n-(p+3)-1)! ≤ ((p+3)!*(n-(p+3)-1)!) := by rfl

    have prevlt : (p+1+3)!*(n-(p+1+3))! ≤ (p+3)!*(n-(p+3))!
    calc
      (p+1+3)!*(n-(p+1+3))!
      _ = (p+1+3)*(p+3)!*(n-(p+1+3))! := by rw[Nat.factorial_succ]
      _ = (p+1+3)*(p+3)!*(n-(p+3)-1)! := by rw[h5]
      _ = (p+1+3)*((p+3)!*(n-(p+3)-1)!) := by ring
      _ ≤ (n-(p+3))*((p+3)!*(n-(p+3)-1)!) := by apply Nat.mul_le_mul_right; omega
      _ = (p+3)!*((n-(p+3))*(n-(p+3)-1)!) := by ring
      _ = (p+3)!*(n-(p+3))! := by rw[Nat.mul_factorial_pred]; rw [Nat.ne_zero_iff_zero_lt]; exact tot

    exact Nat.le_trans prevlt ih

lemma iter2_fact {n : ℕ} (h : 0 < n - 2) : n*(n-1)*(n-2)! = (n)! :=
  have h2 : n-2 = n-1-1 := by omega
  calc
    n*(n-1)*(n-2)!
    _ = n*((n-1)*(n-2)!) := by ring
    _ = n*((n-1)*(n-1-1)!) := by rw[h2]
    _ = n*(n-1)! := by rw[Nat.mul_factorial_pred]; omega
    _ = (n)! := by rw[Nat.mul_factorial_pred]; omega

lemma ascFactorial_le_ascFactorial {n m k : ℕ} (h : n ≤ m) : n.ascFactorial k ≤ m.ascFactorial k :=
  by induction k with
  | zero => simp
  | succ k ih =>
    rw[Nat.ascFactorial_succ]
    rw[Nat.ascFactorial_succ]
    have h2 : n+k ≤ m+k := by omega
    apply Nat.mul_le_mul h2 ih


theorem factorial_lemma (n ell p : ℕ) (nb : 5 ≤ n) (pb : 2 ≤ p) (ellb : 2 ≤ ell)
(sqb : ell * p ≤ n) : (n-1)*(p+ell-2)!*(p)!*(n-p+1)! ≤ (ell-1)*(n)!*(n-2*p+1)*(p)!*(ell-2)! := by
  by_cases hell : ell = 2
  · by_cases hp : p = 2
    · rw[hp,hell]
      simp +arith
      have h1 : n-2+1 = n-1 := by omega
      have h2 : n-4+1 = n-3 := by omega
      rw[h1, h2]
      calc
        (n-1)*2*2* (n-1)!
        _ = (4*(n-1)!)*(n-1) := by ring
        _ ≤ 4*(n-1)!*n := by apply Nat.mul_le_mul_left; omega
        _ = 4* (n*(n-1)!) := by ring
        _ = 4*(n)! := by rw[Nat.mul_factorial_pred]; omega
        _ = 2*(2*(n)!) := by ring
        _ ≤ (n-3)*(2*(n)!) := by apply Nat.mul_le_mul_right; omega
        _ = 2*((n)! * (n-3)) := by ring

    · rw[hell]
      rw[hell] at sqb
      simp +arith
      have hp: 0 ≤ p-3 := by omega
      have h1 : p-3+3 = p := by omega
      have h2 : p-3+3 ≤ n/2

      rw[h1]

      have h24 : 0 < 2 := by linarith
      have h25 : p ≤ n/2 ↔ p*2 ≤ n := by apply Nat.le_div_iff_mul_le h24
      rw[mul_comm] at sqb
      rw[← h25] at sqb
      exact sqb

      have h3 : (p-3+3)!*(n-(p-3+3))! ≤ 3!*(n-3)! := by apply reworked_bin_lemma n (p-3) hp h2
      have h4 : (n-1)*(p)!*(n-p+1) ≤ (n-1)*(p)!*(n-p+1) := by rfl
      rw [h1] at h3

      have h7 : n-3 = n-2-1 := by omega

      calc
        (n-1)*(p)!*(p)!*(n-p+1)!
        _ = (n-1)*(p)!*(p)!*((n-p+1)*(n-p)!) := by rw[← Nat.factorial_succ]
        _ = (n-1)*(p)!*(n-p+1)*((p)!*(n-p)!) := by ring
        _ ≤ (n-1)*(p)!*(n-p+1)*(3!*(n-3)!) := by apply Nat.mul_le_mul_left; exact h3
        _ = (n-1)*(p)!*(n-p+1)*(n-3)!*6 := by rw[Nat.factorial_succ, Nat.factorial_two]; simp +arith; ring
        _ ≤ (n-1)*(p)!*(n-p+1)*(n-3)!*n := by apply Nat.mul_le_mul_left; omega
        _ = (n-1)*(p)!*n*(n-3)!*(n-p+1) := by ring
        _ ≤ (n-1)*(p)!*n*(n-3)!*(n-2) := by apply Nat.mul_le_mul_left; omega
        _ = (n-1)*(p)!*n*((n-2)*(n-3)!) := by ring
        _ = (n-1)*(p)!*n*((n-2)*(n-2-1)!) := by rw[h7]
        _ = (n-1)*(p)!*n*(n-2)! := by rw[Nat.mul_factorial_pred]; omega
        _ = (p)!*(n*(n-1)*(n-2)!) := by ring
        _ = (p)!*(n)! := by rw[iter2_fact]; omega
        _ = (p)!*(n)!*1 := by simp +arith
        _ ≤ (p)!*(n)!*(n-2*p+1) := by apply Nat.mul_le_mul_left; omega
        _ = (n)!*(n-2*p+1)*(p)! := by ring

  · by_cases hp : p = 2
    rw[hp]
    simp +arith
    rw[hp] at sqb
    have hell : 3 ≤ ell := by omega

    have m1 : ell ≤ n-3 := by omega

    have h1 : n-2+1 = n-1 := by omega
    have h2 : n-1 ≤ n := by omega
    have h3 : n-3 = n-4+1 := by omega

    calc
      (n-1)*(ell)!*2*(n-2+1)!
      _ = (n-1)*(ell)!*2*(n-1)! := by rw[h1]
      _ = (n-1)*(ell*(ell-1)*(ell-2)!*2*(n-1)!) := by rw[← iter2_fact]; ring; omega
      _ ≤ n*(ell*(ell-1)*(ell-2)!*2*(n-1)!) := by apply Nat.mul_le_mul_right; omega
      _ = n*(ell-1)*(ell-2)!*2*(n-1)!*ell := by ring
      _ ≤ n*(ell-1)*(ell-2)!*2*(n-1)!*(n-3) := by apply Nat.mul_le_mul_left; exact m1
      _ = (n-3)*(ell-1)*(ell-2)!*2*(n*(n-1)!) := by ring
      _ = (n-3)*(ell-1)*(ell-2)!*2*(n)! := by rw[Nat.mul_factorial_pred]; omega
      _ = (n-4+1)*(ell-1)*(ell-2)!*2*(n)! := by rw[h3]
      _ = (ell-1)*(n)!*(n-4+1)*2*(ell-2)! := by ring





    have h1 : p+ell-2 = (ell-2)+p := by omega
    have h2 : ell-2+1 = ell-1 := by omega
    have h3 : ell-1 = (p+ell-2)-(p-1) := by omega
    have h4 : p = p-1+1 := by omega
    have h5 : ell-1+1 = ell := by omega
    have h6 : p-1 = p-2+1 := by omega
    have h7 : ell = (p+ell-2)-(p-2) := by omega
    have h8 : p-2 = (p-3).succ := by omega
    have h9 : ell+1+(p-3) = p+ell-2 := by omega


    have m1 : ell ≤ n-2*p+1
    have b1 : ell=ell-2+2 := by omega
    have b2 : (ell-2)*(p-1)+2*p+(ell-2) ≤ n
    have b25 : 2*p+(ell-2) = (2*p-2)+(ell-2+2) := by omega
    calc
      (ell-2)*(p-1)+2*p+(ell-2)
      _ = (ell-2)*(p-1)+(2*p+(ell-2)) := by ring
      _ = (ell-2)*(p-1)+(2*p-2*1)+(ell-2+2) := by rw[b25]; ring
      _ = (ell-2)*(p-1)+2*(p-1)+(ell-2+2) := by rw[← Nat.mul_sub]
      _ = (ell-2+2)*(p-1)+(ell-2+2)*1 := by simp +arith; rw[← Nat.add_mul]
      _ = (ell-2+2)*(p-1+1) := by rw[← Nat.mul_add]
      _ = ell*p := by rw[← h4,← b1]
      _ ≤ n := by exact sqb

    have b3 : 1 ≤ p-1 := by omega
    have b4 : 1 ≤ ell-2 := by omega
    have b5 : 1 ≤ (ell-2)*(p-1) := by apply Nat.mul_le_mul b4 b3
    omega



    have h10 : ell+1 ≤ n-p+2 := by omega

    have m2 : (ell+1).ascFactorial (p-3) ≤ (n-p+2).ascFactorial (p-3) := by apply ascFactorial_le_ascFactorial h10

    have h11 : n-p+1+(p-3) = n-2 := by omega


    calc
      (n-1)*(p+ell-2)!*(p)!*(n-p+1)!
      _ = (n-1)*((ell-2)+p)!*(p)!*(n-p+1)! := by rw[h1]
      _ = (n-1)*((ell-2)!*(ell-1).ascFactorial p)*(p)!*(n-p+1)! := by rw[← Nat.factorial_mul_ascFactorial]; rw[h2]
      _ = (n-1)*(ell-2)!*((ell-1).ascFactorial p)*(p)!*(n-p+1)! := by ring
      _ = (n-1)*(ell-2)!*(((p+ell-2)-(p-1)).ascFactorial (p-1+1))*(p)!*(n-p+1)! := by nth_rw 1 [h4]; nth_rw 1 [h3]
      _ = (n-1)*(ell-2)!*(((p+ell-2)-(p-1))*(((p+ell-2)-(p-1)+1).ascFactorial (p-1)))*(p)!*(n-p+1)! := by rw[← Nat.ascFactorial_of_sub]
      _ = (n-1)*(ell-2)!*((ell-1)*(ell.ascFactorial (p-1)))*(p)!*(n-p+1)! := by rw[← h3, h5]
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(ell.ascFactorial (p-1)) := by ring
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(((p+ell-2)-(p-2)).ascFactorial (p-2+1)) := by rw[h6, ← h7]
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*((p+ell-2-(p-2))*(((p+ell-2)-(p-2)+1).ascFactorial (p-2))) := by rw[← Nat.ascFactorial_of_sub]
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(ell*((ell+1).ascFactorial (p-2))) := by rw[← h7]
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*((ell+1).ascFactorial (p-2))*ell := by ring
      _ ≤ (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*((ell+1).ascFactorial (p-2))*(n-2*p+1) := by apply Nat.mul_le_mul_left; exact m1
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*((ell+1).ascFactorial (p-3).succ)*(n-2*p+1) := by rw[h8]
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(p+ell-2)*((ell+1).ascFactorial (p-3))*(n-2*p+1) := by rw[Nat.ascFactorial_succ,h9]; ring
      _ = (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(p+ell-2)*(n-2*p+1)*((ell+1).ascFactorial (p-3)) := by ring
      _ ≤ (n-1)*(ell-2)!*(ell-1)*(p)!*(n-p+1)!*(p+ell-2)*(n-2*p+1)*((n-p+2).ascFactorial (p-3)) := by apply Nat.mul_le_mul_left; exact m2
      _ = (n-1)*(ell-2)!*(ell-1)*(n-2*p+1)*(p+ell-2)*(p)!*((n-p+1)!*((n-p+1+1).ascFactorial (p-3))) := by ring
      _ = (n-1)*(ell-2)!*(ell-1)*(n-2*p+1)*(p)!*(n-2)!*(p+ell-2) := by rw[Nat.factorial_mul_ascFactorial,h11]; ring
      _ ≤ (n-1)*(ell-2)!*(ell-1)*(n-2*p+1)*(p)!*(n-2)!*n := by apply Nat.mul_le_mul_left; omega
      _ = (ell-1)*(ell-2)!*(n-2*p+1)*(p)!*(n*(n-1)*(n-2)!) := by ring
      _ = (ell-1)*(ell-2)!*(n-2*p+1)*(p)!*(n)! := by rw[iter2_fact]; omega
      _ = (ell-1)*(n)!*(n-2*p+1)*(p)!*(ell-2)! := by ring
