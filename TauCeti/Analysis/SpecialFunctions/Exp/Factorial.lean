/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Tactic.FieldSimp

/-!
# Elementary exponential lower bound for factorials

For every positive integer `n`, `exp 1 * (n / exp 1) ^ n ≤ n!`. Unlike
`Stirling.le_factorial_stirling`, whose prefactor `√(2 π n)` is smaller than `exp 1` at `n = 1`,
this elementary bound is sharp at `n = 1` and follows directly from `(1 + n⁻¹) ^ n ≤ exp 1`
without analytic Stirling asymptotics.

## Main results

* `Real.exp_one_mul_div_exp_one_pow_le_factorial`: `exp 1 * (n / exp 1) ^ n ≤ n!` for `1 ≤ n`.
-/

public section

namespace Real

/-- For `1 ≤ n`, `exp 1 * (n / exp 1) ^ n ≤ n!`, sharp at `n = 1`. -/
theorem exp_one_mul_div_exp_one_pow_le_factorial {n : ℕ} (hn : 1 ≤ n) :
    exp 1 * ((n : ℝ) / exp 1) ^ n ≤ n.factorial := by
  induction n, hn using Nat.le_induction with
  | base =>
      have he : exp 1 ≠ 0 := (exp_pos 1).ne'
      simp [he]
  | succ k hk ih =>
      have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      have he : exp 1 ≠ 0 := (exp_pos 1).ne'
      have hsplit : ((k + 1 : ℕ) : ℝ) / exp 1 = (1 + (k : ℝ)⁻¹) * ((k : ℝ) / exp 1) := by
        push_cast
        field_simp [hk0.ne', he]
      have hpow : (((k + 1 : ℕ) : ℝ) / exp 1) ^ k ≤ k.factorial := calc
        (((k + 1 : ℕ) : ℝ) / exp 1) ^ k
          = (1 + (k : ℝ)⁻¹) ^ k * ((k : ℝ) / exp 1) ^ k := by rw [hsplit, mul_pow]
        _ ≤ exp 1 * ((k : ℝ) / exp 1) ^ k :=
            mul_le_mul_of_nonneg_right one_add_inv_pow_le_exp (by positivity)
        _ ≤ k.factorial := ih
      have lhs_eq : exp 1 * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1) =
          ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / exp 1) ^ k := by
        rw [pow_succ']
        field_simp [he]
      rw [lhs_eq, Nat.factorial_succ, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

end Real
