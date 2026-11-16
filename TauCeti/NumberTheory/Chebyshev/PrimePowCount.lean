/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Bounds

/-!
# Explicit and asymptotic bounds on the number of prime powers

Counting prime powers `m ≤ x` (`IsPrimePow m`, exponent `k ≥ 1`) by grouping according to the
exponent `k` (`Chebyshev.sum_PrimePow_eq_sum_sum`) expresses the prime-power count exactly as
`∑_{1 ≤ k ≤ ⌊log x / log 2⌋₊} π ⌊x ^ (1 / k)⌋₊`. Isolating `k = 1` separates `π ⌊x⌋₊` from the
count of proper prime powers (`IsPrimePow m ∧ ¬m.Prime`), which equals
`∑_{2 ≤ k ≤ ⌊log x / log 2⌋₊} π ⌊x ^ (1 / k)⌋₊`.

Each summand with `k ≥ 2` is at most `⌊x ^ (1 / k)⌋₊ ≤ √x`, so the proper prime powers up to `x`
number at most `max (log x / log 2 - 1) 0 * √x` for `x ≥ 0` (and `(log x / log 2 - 1) * √x` for
`x ≥ 2`), making the difference from `π ⌊x⌋₊` of order `O(√x * log x)` and `o(x / log x)`.

Combining this with `Chebyshev.pi_le_log4_mul_div` (`π ⌊x⌋₊ ≤ 2 * log 4 * x / log x + √x`, where
the `+ √x` cancels the `- √x` of the proper prime-power bound) and `Real.sq_log_le_mul_sqrt`
(`log x ^ 2 ≤ 16 * exp (-2) * √x`) yields the explicit bound
`#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} ≤ 6 * x / log x` for every `x ≥ 1` (since
`2 * log 4 + 16 * exp (-2) / log 2 < 5.90 < 6`), and hence `≤ 6 * N / log N` for every natural
number `N` on `Ioc 0 N`, `Icc 1 N`, and `range N`.

## Main results

* `Chebyshev.card_Ioc_filter_isPrimePow_eq_sum_primeCounting`,
  `Chebyshev.card_Ioc_filter_isPrimePow_eq_primeCounting_add_sum`: exact prime-power count
  decompositions for `0 ≤ x`.
* `Chebyshev.card_Ioc_filter_isPrimePow_and_not_prime_eq_sum`,
  `Chebyshev.card_Ioc_filter_isPrimePow_and_not_prime_le`: exact count and `(log x / log 2 - 1) √x`
  upper bound for proper prime powers.
* `Chebyshev.card_Ioc_filter_isPrimePow_le_primeCounting_add`,
  `Chebyshev.card_Ioc_filter_isPrimePow_le_mul_div_log`: explicit upper bounds
  `π ⌊x⌋₊ + (log x / log 2 - 1) * √x` (`2 ≤ x`) and `6 * x / log x` (`1 ≤ x`).
* `Nat.primeCounting_le`, `Nat.card_Ioc_filter_isPrimePow_le_mul_div_log`,
  `Nat.card_Icc_one_filter_isPrimePow_le_mul_div_log`,
  `Nat.card_range_filter_isPrimePow_le_mul_div_log`,
  `Nat.isBigO_card_range_filter_isPrimePow`: natural-number specializations and `O(N / log N)`
  bound.
* `Chebyshev.isBigO_card_Ioc_filter_isPrimePow_sub_primeCounting`,
  `Chebyshev.isLittleO_card_Ioc_filter_isPrimePow_sub_primeCounting`,
  `Chebyshev.isBigO_card_Ioc_filter_isPrimePow`: asymptotic comparisons as `x → ∞`.

## References

* J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. **6** (1962), 64–94.
-/

public section

open Asymptotics Filter Finset
open scoped Nat.Prime

namespace Nat

/-- The prime-counting function `π n` never exceeds `n`. -/
theorem primeCounting_le (n : ℕ) : π n ≤ n := by
  rw [← primesLE_card_eq_primeCounting, primesLE_eq_filter_Ioc_zero]
  exact (card_filter_le _ _).trans_eq (Nat.card_Ioc 0 n)

end Nat

namespace Chebyshev

/-! ### Exact decompositions by exponent -/

/-- For `0 ≤ x` and any upper cutoff `N ≥ ⌊log x / log 2⌋₊`, the number of prime powers `m ≤ x`
equals `∑_{1 ≤ k ≤ N} π ⌊x ^ (1 / k)⌋₊`. -/
theorem card_Ioc_filter_isPrimePow_eq_sum_primeCounting' {x : ℝ} (hx : 0 ≤ x) {N : ℕ}
    (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    #{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} =
      ∑ k ∈ Icc 1 N, π ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
  rw [card_eq_sum_ones, sum_PrimePow_eq_sum_sum' (fun _ ↦ 1) hx hN]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← card_eq_sum_ones, ← Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_card_eq_primeCounting]

/-- For `0 ≤ x`, the number of prime powers `m ≤ x` equals
`∑_{1 ≤ k ≤ ⌊log x / log 2⌋₊} π ⌊x ^ (1 / k)⌋₊`. -/
theorem card_Ioc_filter_isPrimePow_eq_sum_primeCounting {x : ℝ} (hx : 0 ≤ x) :
    #{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} =
      ∑ k ∈ Icc 1 ⌊Real.log x / Real.log 2⌋₊, π ⌊x ^ ((1 : ℝ) / k)⌋₊ :=
  card_Ioc_filter_isPrimePow_eq_sum_primeCounting' hx le_rfl

/-- Splitting off `k = 1` separates `π ⌊x⌋₊` from the higher prime-power counts for every `x ≥ 0`
(for `0 ≤ x < 2`, all terms vanish). -/
theorem card_Ioc_filter_isPrimePow_eq_primeCounting_add_sum {x : ℝ} (hx : 0 ≤ x) :
    #{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} =
      π ⌊x⌋₊ + ∑ k ∈ Icc 2 ⌊Real.log x / Real.log 2⌋₊, π ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
  rw [card_Ioc_filter_isPrimePow_eq_sum_primeCounting hx]
  rcases lt_or_ge x 2 with hx2 | hx2
  · have hfl : ⌊x⌋₊ ≤ 1 := Nat.lt_succ_iff.mp ((Nat.floor_lt hx).mpr hx2)
    have hlog : ⌊Real.log x / Real.log 2⌋₊ = 0 := by
      rw [Nat.floor_eq_zero]
      rcases hx.eq_or_lt with rfl | hxpos
      · norm_num
      · exact (div_lt_one (Real.log_pos one_lt_two)).mpr (Real.log_lt_log hxpos hx2)
    simp [hlog, Nat.primeCounting_eq_zero_iff.mpr hfl]
  · have h1 : 1 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
      rw [Nat.one_le_floor_iff, one_le_div (Real.log_pos one_lt_two)]
      exact Real.log_le_log zero_lt_two hx2
    rw [← add_sum_Ioc_eq_sum_Icc h1, ← Icc_add_one_left_eq_Ioc]
    simp

/-- The number of proper prime powers `m ≤ x` (`IsPrimePow m ∧ ¬m.Prime`) equals
`∑_{2 ≤ k ≤ ⌊log x / log 2⌋₊} π ⌊x ^ (1 / k)⌋₊` for every `x ≥ 0`. -/
theorem card_Ioc_filter_isPrimePow_and_not_prime_eq_sum {x : ℝ} (hx : 0 ≤ x) :
    #{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m ∧ ¬m.Prime} =
      ∑ k ∈ Icc 2 ⌊Real.log x / Real.log 2⌋₊, π ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
  have hpart := card_filter_add_card_filter_not Nat.Prime
    (s := {m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m})
  have hprimes : #{m ∈ {m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} | m.Prime} = π ⌊x⌋₊ := by
    rw [filter_filter, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Ioc_zero]
    exact congrArg card (filter_congr fun m _ ↦ ⟨And.right, fun hp ↦ ⟨hp.isPrimePow, hp⟩⟩)
  rw [hprimes, filter_filter] at hpart
  have htot := card_Ioc_filter_isPrimePow_eq_primeCounting_add_sum hx
  omega

/-! ### Explicit upper bounds -/

/-- For every `x ≥ 2`, the number of proper prime powers `m ≤ x` is at most
`(log x / log 2 - 1) * √x`. -/
theorem card_Ioc_filter_isPrimePow_and_not_prime_le {x : ℝ} (hx : 2 ≤ x) :
    (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m ∧ ¬m.Prime} : ℝ) ≤
      (Real.log x / Real.log 2 - 1) * √x := by
  have hx0 : 0 ≤ x := by positivity
  have hx1 : 1 ≤ x := by linarith
  rw [card_Ioc_filter_isPrimePow_and_not_prime_eq_sum hx0, Nat.cast_sum]
  calc ∑ k ∈ Icc 2 ⌊Real.log x / Real.log 2⌋₊, (π ⌊x ^ ((1 : ℝ) / k)⌋₊ : ℝ)
      ≤ ∑ _k ∈ Icc 2 ⌊Real.log x / Real.log 2⌋₊, √x := by
        refine sum_le_sum fun k hk ↦ ?_
        have hk2 : (2 : ℝ) ≤ k := mod_cast (mem_Icc.mp hk).1
        calc (π ⌊x ^ ((1 : ℝ) / k)⌋₊ : ℝ)
            ≤ (⌊x ^ ((1 : ℝ) / k)⌋₊ : ℝ) := mod_cast Nat.primeCounting_le _
          _ ≤ x ^ ((1 : ℝ) / k) := Nat.floor_le (Real.rpow_nonneg hx0 _)
          _ ≤ x ^ ((1 : ℝ) / 2) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (one_div_le_one_div_of_le zero_lt_two hk2)
          _ = √x := (Real.sqrt_eq_rpow x).symm
    _ = (#(Icc 2 ⌊Real.log x / Real.log 2⌋₊) : ℝ) * √x := by simp
    _ ≤ (Real.log x / Real.log 2 - 1) * √x := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg x)
        have hfl : 1 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
          rw [Nat.one_le_floor_iff, one_le_div (Real.log_pos one_lt_two)]
          exact Real.log_le_log zero_lt_two hx
        rw [Nat.card_Icc, show ⌊Real.log x / Real.log 2⌋₊ + 1 - 2 =
          ⌊Real.log x / Real.log 2⌋₊ - 1 by omega, Nat.cast_sub hfl, Nat.cast_one]
        linarith [Nat.floor_le (div_nonneg (Real.log_nonneg hx1) (Real.log_nonneg one_le_two))]

/-- Uniform version valid for all `x ≥ 0`: the number of proper prime powers `m ≤ x` is at most
`max (log x / log 2 - 1) 0 * √x`. -/
theorem card_Ioc_filter_isPrimePow_and_not_prime_le_max {x : ℝ} (hx : 0 ≤ x) :
    (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m ∧ ¬m.Prime} : ℝ) ≤
      max (Real.log x / Real.log 2 - 1) 0 * √x := by
  rcases lt_or_ge x 2 with hx2 | hx2
  · have h0 : #{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m ∧ ¬m.Prime} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro m hm hmp
      have hmle : (m : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (mem_Ioc.mp hm).2
      have hm2 : (2 : ℝ) ≤ m := mod_cast hmp.1.two_le
      linarith
    rw [h0, Nat.cast_zero]
    positivity
  · exact (card_Ioc_filter_isPrimePow_and_not_prime_le hx2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x))

/-- For `x ≥ 2`, the prime powers `m ≤ x` number at most `π ⌊x⌋₊ + (log x / log 2 - 1) * √x`. -/
theorem card_Ioc_filter_isPrimePow_le_primeCounting_add {x : ℝ} (hx : 2 ≤ x) :
    (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ) ≤
      π ⌊x⌋₊ + (Real.log x / Real.log 2 - 1) * √x := by
  have hx0 : 0 ≤ x := by positivity
  rw [card_Ioc_filter_isPrimePow_eq_primeCounting_add_sum hx0, Nat.cast_add,
    ← card_Ioc_filter_isPrimePow_and_not_prime_eq_sum hx0]
  gcongr
  exact card_Ioc_filter_isPrimePow_and_not_prime_le hx

/-- Uniform version for all `x ≥ 0`: the prime powers `m ≤ x` number at most
`π ⌊x⌋₊ + max (log x / log 2 - 1) 0 * √x`. -/
theorem card_Ioc_filter_isPrimePow_le_primeCounting_add_max {x : ℝ} (hx : 0 ≤ x) :
    (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ) ≤
      π ⌊x⌋₊ + max (Real.log x / Real.log 2 - 1) 0 * √x := by
  rw [card_Ioc_filter_isPrimePow_eq_primeCounting_add_sum hx, Nat.cast_add,
    ← card_Ioc_filter_isPrimePow_and_not_prime_eq_sum hx]
  gcongr
  exact card_Ioc_filter_isPrimePow_and_not_prime_le_max hx

private lemma two_mul_log_four_add_sixteen_mul_exp_neg_two_div_log_two_le_six :
    2 * Real.log 4 + 16 * Real.exp (-2) / Real.log 2 ≤ 6 := by
  have hexp2 : Real.exp (-2) < 0.3678794412 ^ 2 := by
    rw [show (-2 : ℝ) = -1 + -1 by norm_num, Real.exp_add, sq]
    exact mul_lt_mul'' Real.exp_neg_one_lt_d9 Real.exp_neg_one_lt_d9
      (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hdiv : 16 * Real.exp (-2) / Real.log 2 < 16 * 0.3678794412 ^ 2 / 0.6931471803 := by
    rw [div_lt_div_iff₀ (Real.log_pos one_lt_two) (by norm_num)]
    nlinarith [Real.log_two_gt_d9, Real.exp_pos (-2)]
  rw [Real.log_four_eq]
  linarith [Real.log_two_lt_d9]

/-- Explicit unconditional upper bound on the prime-power count: for every real `x ≥ 1`,
`#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} ≤ 6 * x / log x` (at `x = 1`, both sides are `0`). -/
theorem card_Ioc_filter_isPrimePow_le_mul_div_log {x : ℝ} (hx : 1 ≤ x) :
    (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ) ≤ 6 * x / Real.log x := by
  rcases lt_or_ge x 2 with hx2 | hx2
  · have h0 : #{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro m hm hmp
      have hmle : (m : ℝ) ≤ x := (Nat.le_floor_iff (zero_le_one.trans hx)).mp (mem_Ioc.mp hm).2
      have hm2 : (2 : ℝ) ≤ m := mod_cast hmp.two_le
      linarith
    rw [h0, Nat.cast_zero]
    exact div_nonneg (by positivity) (Real.log_nonneg hx)
  · have hx0 : 0 ≤ x := by positivity
    have hlog_pos : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx2)
    have hpi : (π ⌊x⌋₊ : ℝ) ≤ 2 * Real.log 4 * x / Real.log x + √x := by
      have h := pi_le_log4_mul_div (one_lt_two.trans_le hx2)
      rwa [Real.log_sqrt hx0, div_div_eq_mul_div, mul_comm (Real.log 4 * x) 2, ← mul_assoc] at h
    rw [le_div_iff₀ hlog_pos]
    calc (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ) * Real.log x
        ≤ (2 * Real.log 4 * x / Real.log x + Real.log x / Real.log 2 * √x) * Real.log x := by
          refine mul_le_mul_of_nonneg_right ?_ hlog_pos.le
          linarith [card_Ioc_filter_isPrimePow_le_primeCounting_add hx2]
      _ = 2 * Real.log 4 * x + Real.log x ^ 2 / Real.log 2 * √x := by
          field_simp [hlog_pos.ne']
      _ ≤ 2 * Real.log 4 * x + 16 * Real.exp (-2) * √x / Real.log 2 * √x := by
          gcongr
          exact Real.sq_log_le_mul_sqrt hx
      _ = (2 * Real.log 4 + 16 * Real.exp (-2) / Real.log 2) * x := by
          have hsq : √x * √x = x := Real.mul_self_sqrt hx0
          calc 2 * Real.log 4 * x + 16 * Real.exp (-2) * √x / Real.log 2 * √x
              = 2 * Real.log 4 * x + 16 * Real.exp (-2) / Real.log 2 * (√x * √x) := by ring
            _ = (2 * Real.log 4 + 16 * Real.exp (-2) / Real.log 2) * x := by rw [hsq]; ring
      _ ≤ 6 * x :=
          mul_le_mul_of_nonneg_right
            two_mul_log_four_add_sixteen_mul_exp_neg_two_div_log_two_le_six hx0

/-! ### Asymptotics as `x → ∞` -/

/-- The contribution of proper prime powers to the prime-power count is `O(√x * log x)`. -/
theorem isBigO_card_Ioc_filter_isPrimePow_sub_primeCounting :
    (fun x : ℝ ↦ (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ) - π ⌊x⌋₊) =O[atTop]
      (fun x : ℝ ↦ √x * Real.log x) := by
  refine IsBigO.of_bound (Real.log 2)⁻¹ ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hx0 : 0 ≤ x := by positivity
  have hdiff : (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ) - π ⌊x⌋₊ =
      (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m ∧ ¬m.Prime} : ℝ) := by
    rw [card_Ioc_filter_isPrimePow_eq_primeCounting_add_sum hx0, Nat.cast_add, add_sub_cancel_left,
      card_Ioc_filter_isPrimePow_and_not_prime_eq_sum hx0]
  rw [hdiff, Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg (by linarith)))]
  calc (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m ∧ ¬m.Prime} : ℝ)
      ≤ (Real.log x / Real.log 2 - 1) * √x := card_Ioc_filter_isPrimePow_and_not_prime_le hx
    _ ≤ Real.log x / Real.log 2 * √x := by
        gcongr
        linarith
    _ = (Real.log 2)⁻¹ * (√x * Real.log x) := by ring

/-- Proper prime powers contribute `o(x / log x)` to the prime-power count. -/
theorem isLittleO_card_Ioc_filter_isPrimePow_sub_primeCounting :
    (fun x : ℝ ↦ (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ) - π ⌊x⌋₊) =o[atTop]
      (fun x : ℝ ↦ x / Real.log x) := by
  refine isBigO_card_Ioc_filter_isPrimePow_sub_primeCounting.trans_isLittleO ?_
  refine ((isBigO_refl (fun x : ℝ ↦ √x / Real.log x) atTop).mul_isLittleO
    (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2))).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx
    rw [Real.rpow_two]
    field_simp [(Real.log_pos hx).ne']
  · filter_upwards [eventually_gt_atTop 1] with x hx
    rw [← Real.sqrt_eq_rpow, div_mul_eq_mul_div, Real.mul_self_sqrt (zero_le_one.trans hx.le)]

/-- The total number of prime powers `m ≤ x` is `O(x / log x)` as `x → ∞`. -/
theorem isBigO_card_Ioc_filter_isPrimePow :
    (fun x : ℝ ↦ (#{m ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow m} : ℝ)) =O[atTop]
      (fun x : ℝ ↦ x / Real.log x) := by
  refine IsBigO.of_bound 6 ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (div_nonneg (by positivity) (Real.log_nonneg hx.le)), ← mul_div_assoc]
  exact card_Ioc_filter_isPrimePow_le_mul_div_log hx.le

end Chebyshev

namespace Nat

/-- For every natural number `N`, the prime powers in `(0, N]` number at most `6 * N / log N`
(at `N = 0, 1`, both sides are `0`). -/
theorem card_Ioc_filter_isPrimePow_le_mul_div_log (N : ℕ) :
    (#{m ∈ Ioc 0 N | IsPrimePow m} : ℝ) ≤ 6 * N / Real.log N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · simpa using Chebyshev.card_Ioc_filter_isPrimePow_le_mul_div_log
      (x := (N : ℝ)) (mod_cast Nat.one_le_iff_ne_zero.mpr hN)

/-- For every natural number `N`, the prime powers in `[1, N]` number at most `6 * N / log N`. -/
theorem card_Icc_one_filter_isPrimePow_le_mul_div_log (N : ℕ) :
    (#{m ∈ Icc 1 N | IsPrimePow m} : ℝ) ≤ 6 * N / Real.log N := by
  simpa only [← Icc_add_one_left_eq_Ioc, zero_add] using card_Ioc_filter_isPrimePow_le_mul_div_log N

/-- For every natural number `N`, the prime powers strictly below `N` number at most
`6 * N / log N`. -/
theorem card_range_filter_isPrimePow_le_mul_div_log (N : ℕ) :
    (#{m ∈ range N | IsPrimePow m} : ℝ) ≤ 6 * N / Real.log N := by
  refine (Nat.cast_le.mpr (card_le_card fun m hm ↦ ?_)).trans
    (card_Ioc_filter_isPrimePow_le_mul_div_log N)
  rw [mem_filter] at hm ⊢
  exact ⟨mem_Ioc.mpr ⟨hm.2.pos, (mem_range.mp hm.1).le⟩, hm.2⟩

/-- The number of prime powers below `N` is `O(N / log N)` as `N → ∞`. -/
theorem isBigO_card_range_filter_isPrimePow :
    (fun N : ℕ ↦ (#{m ∈ range N | IsPrimePow m} : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log N) := by
  refine IsBigO.of_bound 6 ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < N := mod_cast hN
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg N) (Real.log_nonneg hN1.le)), ← mul_div_assoc]
  exact card_range_filter_isPrimePow_le_mul_div_log N

end Nat
