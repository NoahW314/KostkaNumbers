/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib

notation n "!" => Nat.factorial n




lemma bin_lemma (n p : ℕ) (pb : 0 ≤ p) (half : p + 3 ≤ n / 2) :
    (p + 3)! * (n - (p + 3))! ≤ 3! * (n - 3)! := by
  induction p with
  | zero => simp
  | succ p ih =>
    specialize ih (by norm_num) (by lia)
    refine le_trans ?_ ih
    rw [Nat.factorial_succ, show n - (p + 1 + 3) = n - (p + 3) - 1 by lia, mul_assoc]
    have hp : (p + 1 + 3) * ((p + 3)! * (n - (p + 3) - 1)!) ≤
        (n - (p + 3)) * ((p + 3)! * (n - (p + 3) - 1)!) := by
      apply Nat.mul_le_mul_right
      lia
    refine le_trans hp ?_
    nth_rw 4 [← Nat.mul_factorial_pred]
    · ring_nf
      rfl
    · lia

lemma iter2_fact {n : ℕ} (h : 0 < n - 2) : n * (n - 1) * (n - 2)! = (n)! := by
  nth_rw 2 [← Nat.mul_factorial_pred, ← Nat.mul_factorial_pred]
  · ring_nf
    congr 1
  all_goals lia

-- upstream
lemma ascFactorial_mono {n m : ℕ} (k : ℕ) (h : n ≤ m) :
    n.ascFactorial k ≤ m.ascFactorial k := by
  induction k with
  | zero => simp
  | succ k ih => exact Nat.mul_le_mul (by lia) ih


theorem factorial_lemma (n ell p : ℕ) (nb : 5 ≤ n) (pb : 2 ≤ p) (ellb : 2 ≤ ell)
    (sqb : ell * p ≤ n) :
    (n - 1) * (p + ell - 2)! * (p)! * (n - p + 1)! ≤
    (ell - 1) * (n)! * (n - 2 * p + 1) * (p)! * (ell - 2)! := by
  by_cases hell : ell = 2
  · subst hell
    by_cases hp : p = 2
    · subst hp
      simp +arith only [Nat.reduceAdd, Nat.reduceSub, Nat.factorial_two,
        show n - 2 + 1 = n - 1 by lia, Nat.add_one_sub_one, one_mul, Nat.reduceMul,
        show n - 4 + 1 = n - 3 by lia, tsub_self, Nat.factorial_zero, mul_one]
      calc
        (n - 1) * 2 * 2 * (n - 1)!
        _ = (4 * (n - 1)!) * (n - 1) := by ring
        _ ≤ 4 * (n - 1)! * n := Nat.mul_le_mul_left _ (by lia)
        _ = 4 * (n * (n - 1)!) := by ring
        _ = 2 * (2 * (n)!) := by
          rw [Nat.mul_factorial_pred]
          · ring
          · positivity
        _ ≤ (n-3) * (2 * (n)!) := Nat.mul_le_mul_right _ (by lia)
        _ = 2 * ((n)! * (n - 3)) := by ring
    · simp +arith only [add_tsub_cancel_right, Nat.add_one_sub_one, one_mul, tsub_self,
        Nat.factorial_zero, mul_one]
      calc
        (n - 1) * (p)! * (p)! * (n - p + 1)!
        _ = (n - 1) * (p)! * (p)! * ((n - p + 1) * (n - p)!) := by rw [← Nat.factorial_succ]
        _ = (n - 1) * (p)! * (n - p + 1) * ((p)! * (n - p)!) := by ring
        _ ≤ (n - 1) * (p)! * (n - p + 1) * (3! * (n - 3)!) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [show p = p - 3 + 3 by lia]
          refine bin_lemma n (p - 3) ?_ ?_
          all_goals lia
        _ = (n-1) * (p)! * (n - p + 1) * (n - 3)! * 6 := by
          simp +arith [Nat.factorial_succ]
          ring
        _ ≤ (n - 1) * (p)! * (n - p + 1) * (n - 3)! * n :=  Nat.mul_le_mul_left _ (by lia)
        _ = (n - 1) * (p)! * n * (n - 3)! * (n - p + 1) := by ring
        _ ≤ (n - 1) * (p)! * n * (n - 3)! * (n - 2) := Nat.mul_le_mul_left _ (by lia)
        _ = (n - 1) * (p)! * n * ((n - 2) * (n - 3)!) := by ring
        _ = (n - 1) * (p)! * n * ((n - 2) * (n - 2 - 1)!) := by rw [show n - 3 = n - 2 - 1 by lia]
        _ = (n - 1) * (p)! * n * (n - 2)! := by rw [Nat.mul_factorial_pred (by lia)]
        _ = (p)! * (n * (n - 1) * (n - 2)!) := by ring
        _ = (p)! * (n)! := by rw [iter2_fact (by lia)]
        _ ≤ (p)! * (n)! * (n - 2 * p + 1) := Nat.le_mul_of_pos_right _ (by lia)
        _ = (n)! * (n - 2 * p + 1) * (p)! := by ring
  · by_cases hp : p = 2
    · subst hp
      simp +arith only [add_tsub_cancel_right, Nat.factorial_two, Nat.reduceMul,
        show n - 2 + 1 = n - 1 by lia, show n - 4 + 1 = n - 3 by lia]
      calc
        (n - 1) * (ell)! * 2 * (n - 1)!
        _ = (n - 1) * (ell * (ell - 1) * (ell - 2)! * 2 * (n - 1)!) := by
          rw [← iter2_fact (by lia)]
          ring
        _ ≤ n * (ell * (ell - 1) * (ell - 2)! * 2 * (n - 1)!) := Nat.mul_le_mul_right _ (by lia)
        _ = n * (ell - 1) * (ell - 2)! * 2 * (n - 1)! * ell := by ring
        _ ≤ n * (ell - 1) * (ell - 2)! * 2 * (n - 1)! * (n - 3) := Nat.mul_le_mul_left _ (by lia)
        _ = (ell - 1) * (n)! * (n - 3) * 2 * (ell - 2)! := by
          nth_rw 3 [← Nat.mul_factorial_pred (by lia)]
          ring
    have h1 : ell - 1 = (p + ell - 2) - (p - 1) := by lia
    have h2 : ell = (p + ell - 2) - (p-2) := by lia
    have h3 : ell ≤ n - 2 * p + 1 := by
      suffices (ell - 2) * (p - 1) + 2 * p + (ell - 2) ≤ n by
        have : 1 ≤ (ell-2)*(p-1) := Right.one_le_mul (by lia) (by lia)
        lia
      calc
        (ell - 2) * (p - 1) + 2 * p + (ell - 2)
        _ = (ell - 2) * (p - 1) + 2 * (p - 1) + (ell - 2 + 2) := by lia
        _ = (ell - 2 + 2) * (p - 1) + (ell - 2 + 2) * 1 := by simp +arith [← Nat.add_mul]
        _ = (ell - 2 + 2) * (p - 1 + 1) := by rw [← Nat.mul_add]
        _ = ell * p := by grind
        _ ≤ n := sqb
    calc
      (n - 1) * (p + ell - 2)! * (p)! * (n - p + 1)!
      _ = (n - 1) * ((ell - 2) + p)! * (p)! * (n - p + 1)! := by grind
      _ = (n - 1) * (ell - 2)! * ((ell - 1).ascFactorial p) * (p)! * (n - p + 1)! := by
          rw[← Nat.factorial_mul_ascFactorial, show ell - 2 + 1 = ell - 1 by lia]
          ring
      _ = (n - 1) * (ell - 2)! * (ell - 1) * (p)! * (n - p + 1)! * (ell.ascFactorial (p - 1)) := by
          nth_rw 1 [show p = p - 1 + 1 by lia, h1]
          rw [← Nat.ascFactorial_of_sub, ← h1, show ell - 1 + 1 = ell by lia]
          ring
      _ = (n - 1) * (ell - 2)! * (ell - 1) * (p)! * (n - p + 1)! *
        ((( p + ell - 2) - (p - 2)).ascFactorial (p - 2 + 1)) := by
          rw [show p - 1 = p - 2 + 1 by lia, ← h2]
      _ = (n - 1) * (ell - 2)! * (ell - 1) * (p)! * (n - p + 1)! * ((ell + 1).ascFactorial (p - 2))
        * ell := by
          rw [← Nat.ascFactorial_of_sub, ← h2]
          ring
      _ ≤ (n - 1) * (ell - 2)! * (ell - 1) * (p)! * (n - p + 1)! * ((ell + 1).ascFactorial (p - 2))
        * (n - 2 * p + 1) := Nat.mul_le_mul_left _ h3
      _ = (n - 1) * (ell - 2)! * (ell - 1) * (p)! * (n - p + 1)! * (p + ell- 2) * (n - 2 * p + 1) *
        ((ell + 1).ascFactorial (p - 3)) := by
          rw [show p - 2 = (p - 3).succ by lia, Nat.ascFactorial_succ,
            show ell + 1 + (p - 3) = p + ell - 2 by lia]
          ring
      _ ≤ (n - 1) * (ell - 2)! * (ell - 1) * (p)! * (n - p + 1)! * (p + ell - 2) * (n - 2 * p + 1) *
        ((n - p + 2).ascFactorial (p - 3)) := Nat.mul_le_mul_left _ <| ascFactorial_mono _ (by lia)
      _ = (n - 1) * (ell - 2)! * (ell - 1) * (n - 2 * p + 1) * (p + ell - 2) * (p)! *
        ((n - p + 1)! * ((n - p + 1 + 1).ascFactorial (p - 3))) := by ring
      _ = (n - 1) * (ell - 2)! * (ell - 1) * (n - 2 * p + 1) * (p)! * (n - 2)! * (p + ell - 2) := by
          rw [Nat.factorial_mul_ascFactorial, show n - p + 1 + (p - 3) = n - 2  by lia]
          ring
      _ ≤ (n - 1) * (ell - 2)! * (ell - 1) * (n - 2 * p + 1) * (p)! * (n - 2)! * n :=
          Nat.mul_le_mul_left _ (by lia)
      _ = (ell - 1) * (ell - 2)! * (n - 2 * p + 1) * (p)! * (n * (n - 1) * (n - 2)!) := by ring
      _ = (ell - 1) * (n)! * (n - 2 * p + 1) * (p)! * (ell - 2)! := by
          rw [iter2_fact (by lia)]
          ring
