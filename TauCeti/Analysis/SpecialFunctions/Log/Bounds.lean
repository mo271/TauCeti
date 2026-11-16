/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Log.PosLog

/-!
# Elementary numerical bounds on the real logarithm

From `log x ≤ x - 1` for `x > 0` (`Real.log_le_sub_one_of_pos`) applied at `x = 2` and `x / 2`,
one obtains `log 4 = 2 log 2 ≤ 2` and `log x / x ≤ 1 / 2` for every real `x ≥ 0` (holding at
`x = 0` via `0 / 0 = 0`). The first compares explicit prime-counting constants involving `log 4`
with rational constants, and the second bounds the contribution `log p / p` of a single prime at a
real cutoff `x` when passing between inclusive and strict prime sums.

Refining the secant bound `log x ≤ x ^ ε / ε` (`Real.log_le_rpow_div`) via the tangent line
`log u ≤ exp (-1) * u` at `u = e` yields `log x ≤ exp (-1) * x ^ ε / ε` for `x ≥ 0` and `ε > 0`,
with equality at `x = exp (1 / ε)`. At `ε = 1 / 4` and `x ≥ 1` this squares to the sharp bound
`log x ^ 2 ≤ 16 * exp (-2) * √x` (attained at `x = exp 4`), which controls `√x * log x` against
`x / log x` in explicit prime-power estimates.

## Main results

* `Real.log_four_le_two`: `log 4 ≤ 2`.
* `Real.log_div_self_le_half`: `log x / x ≤ 1 / 2` for every nonnegative real `x`.
* `Real.log_le_exp_neg_one_mul`: `log x ≤ exp (-1) * x` for `0 ≤ x`.
* `Real.log_le_exp_neg_one_mul_rpow_div`: `log x ≤ exp (-1) * x ^ ε / ε` for `0 ≤ x` and `0 < ε`.
* `Real.sq_log_le_mul_sqrt`: `log x ^ 2 ≤ 16 * exp (-2) * √x` for `1 ≤ x`.
-/

public section

namespace Real

/-- The natural logarithm of `4` is at most `2`. -/
theorem log_four_le_two : log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, log_pow]
  norm_num
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- For every nonnegative real `x`, `log x / x ≤ 1 / 2` (holding at `x = 0` via `0 / 0 = 0`). -/
theorem log_div_self_le_half {x : ℝ} (hx : 0 ≤ x) : log x / x ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h := log_le_sub_one_of_pos (half_pos hx)
  rw [log_div hx.ne' two_ne_zero] at h
  rw [div_le_iff₀ hx]
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- On `[0, ∞)`, the logarithm lies below its tangent line `x ↦ exp (-1) * x` through the origin,
with equality at `x = exp 1`. -/
theorem log_le_exp_neg_one_mul {x : ℝ} (hx : 0 ≤ x) : log x ≤ exp (-1) * x :=
  (le_max_right 0 (log x)).trans (posLog_apply ▸ posLog_le_exp_neg_one_mul hx)

/-- Sharp power-law upper bound on `log`: for `0 ≤ x` and `0 < ε`,
`log x ≤ exp (-1) * x ^ ε / ε`, improving `Real.log_le_rpow_div` by the optimal factor `exp (-1)`
(attained at `x = exp (1 / ε)`). -/
theorem log_le_exp_neg_one_mul_rpow_div {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    log x ≤ exp (-1) * x ^ ε / ε := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [zero_rpow hε.ne']
  rw [le_div_iff₀' hε, ← log_rpow hx]
  exact log_le_exp_neg_one_mul (rpow_nonneg hx.le ε)

/-- Sharp square-root upper bound on `log x ^ 2`: for `1 ≤ x`,
`log x ^ 2 ≤ 16 * exp (-2) * √x`, with equality at `x = exp 4`. -/
theorem sq_log_le_mul_sqrt {x : ℝ} (hx : 1 ≤ x) : log x ^ 2 ≤ 16 * exp (-2) * √x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hquarter : log x ≤ 4 * exp (-1) * x ^ ((1 : ℝ) / 4) := by
    linarith [log_le_exp_neg_one_mul_rpow_div hx0 (show (0 : ℝ) < 1 / 4 by norm_num)]
  calc log x ^ 2 ≤ (4 * exp (-1) * x ^ ((1 : ℝ) / 4)) ^ 2 :=
        pow_le_pow_left₀ (log_nonneg hx) hquarter 2
    _ = 16 * (exp (-1) * exp (-1)) * (x ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) := by ring
    _ = 16 * exp (-2) * √x := by
        rw [← exp_add, ← rpow_mul_natCast hx0, sqrt_eq_rpow]
        norm_num

end Real
