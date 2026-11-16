/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Log.Base

/-!
# Explicit bounds and transfers for the difference `ψ - θ`

For `x ≥ 2`, Chebyshev's functions satisfy
`ψ x - θ x = ∑_{2 ≤ k ≤ ⌊log x / log 2⌋₊} θ (x ^ (1 / k))`
(`Chebyshev.psi_eq_theta_add_sum_theta`). Isolating `k = 2` separates the square-root main term
`θ √x` from the cube-root and higher-root sum `∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} θ (x ^ (1 / k))` for
every `x ≥ 0`. This file develops both the logarithmic-factor bounds of Rosser–Schoenfeld and the
sharper dyadic-envelope bounds of Broadbent, Kadiri, Lumley, Ng, and Wilk, together with the
bidirectional error transfers between `ψ` and `θ`.

1. **Crude cube-root tail and unconditional bound.** Since `θ` is monotone and nonnegative, the
   `k ≥ 3` terms are bounded by `(⌊log x / log 2⌋₊ - 2) * θ (x ^ (1 / 3))` and, under any linear
   bound `θ y ≤ c * y` on `(0, x ^ (1 / 3)]`, by `c * max (log x / log 2 - 2) 0 * x ^ (1 / 3)`.
   Applying `Chebyshev.theta_le_log4_mul_x` gives
   `ψ x - θ x ≤ log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ (1 / 3))` for `x ≥ 0`, and transfers
   any pointwise bound on `|ψ x - x|` to `|θ x - x|` (and conversely) with the same correction.

2. **Dyadic higher-root weight and envelope.** Following Broadbent–Kadiri–Lumley–Ng–Wilk, define
   `Chebyshev.cubeRootTailWeight x = ∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} x ^ (1 / k - 1 / 3)` for `x ≥ 8`
   (and `0` for `x < 8`), so that
   `∑_{k ≥ 3} θ (x ^ (1 / k)) ≤ c * cubeRootTailWeight x * x ^ (1 / 3)`.
   On each dyadic interval `[2 ^ n, 2 ^ (n + 1))` with `n ≥ 4`, the index set is fixed and every
   exponent `1 / k - 1 / 3` with `k ≥ 4` is negative, so `cubeRootTailWeight` is strictly
   decreasing there. At the dyadic endpoints `2 ^ n`, `cubeRootTailWeight (2 ^ n)` increases up to
   `n = 9` (`cubeRootTailWeight (2 ^ 8) < cubeRootTailWeight (2 ^ 9)`) and is strictly decreasing
   for `n ≥ 9`. Consequently, for every `X ≥ 2 ^ 9` and `x ≥ X`,
   `cubeRootTailWeight x ≤ cubeRootTailBound X :=
     max (cubeRootTailWeight X) (cubeRootTailWeight (2 ^ (⌊log X / log 2⌋₊ + 1)))`,
   and `cubeRootTailBound` is itself antitone on `[2 ^ 9, ∞)`.

3. **General-input `ψ`-to-`θ` transfers.** Combining `cubeRootTailBound` with an upper `ψ`-bound on
   `[exp b, ∞)` (`b ≥ 7`, since `2 ^ 9 < exp 7`) and `θ y ≤ y` on `(0, x₁]` (`x₁ ≥ exp 7`) gives
   `θ x ≤ (1 + ε (log x₁)) * x` for all `x ≥ 0` and Theorem 5 of Broadbent–Kadiri–Lumley–Ng–Wilk.
   In the opposite direction, Costa Pereira's upper bound
   `Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi` transfers lower `ψ`-bounds to lower `θ`-bounds
   (their Lemmas 9 and 11).

## Main definitions

* `Chebyshev.cubeRootTailWeight`: the normalized higher-root sum
  `∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} x ^ (1 / k - 1 / 3)` for `x ≥ 8` (`0` for `x < 8`).
* `Chebyshev.cubeRootTailBound`: the dyadic upper envelope
  `max (cubeRootTailWeight X) (cubeRootTailWeight (2 ^ (⌊log X / log 2⌋₊ + 1)))`.

## Main results

* `Chebyshev.psi_sub_theta_eq_theta_sqrt_add_sum`:
  `ψ x - θ x = θ √x + ∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} θ (x ^ (1 / k))` for `0 ≤ x`.
* `Chebyshev.psi_sub_theta_le_log_four_mul`:
  `ψ x - θ x ≤ log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ (1 / 3))` for `0 ≤ x`.
* `Chebyshev.one_sub_mul_sqrt_le_psi_sub_theta_of_abs_theta_sub_self_le`,
  `Chebyshev.psi_sub_theta_le_one_add_mul_sqrt_add`: transfers from `|θ y - y| ≤ ε * y`.
* `Chebyshev.abs_theta_sub_self_le_of_abs_psi_sub_self_le`,
  `Chebyshev.abs_psi_sub_self_le_of_abs_theta_sub_self_le`: bidirectional pointwise error transfers.
* `Chebyshev.strictAntiOn_cubeRootTailWeight_Ico_two_pow`,
  `Chebyshev.cubeRootTailWeight_two_pow_eight_lt_nine`,
  `Chebyshev.strictAntiOn_cubeRootTailWeight_two_pow`,
  `Chebyshev.cubeRootTailWeight_le_cubeRootTailBound`,
  `Chebyshev.antitoneOn_cubeRootTailBound_Ici`: dyadic monotonicity and upper-envelope bound.
* `Chebyshev.psi_sub_theta_le_mul_sqrt_add_mul_cubeRootTailBound`,
  `Chebyshev.theta_le_one_add_mul_of_psi_le`,
  `Chebyshev.psi_sub_theta_le_of_abs_psi_sub_self_le`,
  `Chebyshev.le_theta_of_psi_le_mul`,
  `Chebyshev.le_theta_of_sub_psi_le_mul_sqrt`: general-input transfers of
  Broadbent–Kadiri–Lumley–Ng–Wilk (Proposition 4, Corollary 3.1, Theorem 5, Lemmas 9 and 11).

## References

* L. Schoenfeld, *Sharper bounds for the Chebyshev functions `θ(x)` and `ψ(x)`. II*,
  Math. Comp. **30** (1976), 337–360.
* N. Costa Pereira, *Estimates for the Chebyshev function `ψ(x) - θ(x)`*,
  Math. Comp. **44** (1985), 211–221.
* S. Broadbent, H. Kadiri, A. Lumley, N. Ng, and K. Wilk, *Sharper bounds for the Chebyshev
  function `θ(x)`*, Math. Comp. **90** (2021), 2281–2315 (arXiv:2002.11068v2).
-/

public section

open Finset
open scoped Chebyshev

namespace Chebyshev

/-! ### Dyadic floor-logarithm helpers -/

private lemma le_natFloor_log_div_log_two {x : ℝ} {n : ℕ} (h : (2 : ℝ) ^ n ≤ x) :
    n ≤ ⌊Real.log x / Real.log 2⌋₊ := by
  have h1x : 1 ≤ x := (one_le_pow₀ one_le_two).trans h
  rw [Nat.le_floor_iff (div_nonneg (Real.log_nonneg h1x) (Real.log_nonneg one_le_two)),
    le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
  exact Real.log_le_log (by positivity) h

private lemma natFloor_log_div_log_two_lt {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hn : 0 < n)
    (h : x < (2 : ℝ) ^ n) : ⌊Real.log x / Real.log 2⌋₊ < n := by
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [Nat.floor_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hx hx1) (Real.log_nonneg one_le_two))]
    exact hn
  · rw [Nat.floor_lt (div_nonneg (Real.log_nonneg hx1.le) (Real.log_nonneg one_le_two)),
      div_lt_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_lt_log (zero_lt_one.trans hx1) h

private lemma natFloor_log_div_log_two_eq {x : ℝ} {n : ℕ} (hlo : (2 : ℝ) ^ n ≤ x)
    (hhi : x < (2 : ℝ) ^ (n + 1)) : ⌊Real.log x / Real.log 2⌋₊ = n :=
  le_antisymm
    (Nat.lt_succ_iff.mp (natFloor_log_div_log_two_lt ((by positivity : (0 : ℝ) ≤ 2 ^ n).trans hlo)
      (Nat.succ_pos n) hhi))
    (le_natFloor_log_div_log_two hlo)

/-! ### Higher-root decomposition and unconditional `log 4` bound -/

/-- For `4 ≤ x` and any upper index `N ≥ ⌊log x / log 2⌋₊`, isolating `k = 2` in
`Chebyshev.psi_eq_theta_add_sum_theta'` writes `ψ x - θ x` as `θ √x` plus the `k ≥ 3` root sum. -/
theorem psi_sub_theta_eq_theta_sqrt_add_sum' {x : ℝ} (hx : 4 ≤ x) {N : ℕ}
    (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    ψ x - θ x = θ √x + ∑ k ∈ Icc 3 N, θ (x ^ ((1 : ℝ) / k)) := by
  have h2N : 2 ≤ N :=
    (le_natFloor_log_div_log_two (show (2 : ℝ) ^ 2 ≤ x by norm_num; exact hx)).trans hN
  rw [psi_eq_theta_add_sum_theta' (by linarith) hN, add_sub_cancel_left,
    ← add_sum_Ioc_eq_sum_Icc h2N, ← Icc_add_one_left_eq_Ioc, Real.sqrt_eq_rpow]
  norm_num

/-- For every `x ≥ 0`, `ψ x - θ x = θ √x + ∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} θ (x ^ (1 / k))`
(for `0 ≤ x < 4`, all three terms vanish). -/
theorem psi_sub_theta_eq_theta_sqrt_add_sum {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x = θ √x + ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) := by
  rcases lt_or_ge x 4 with hx4 | hx4
  · have hsqrt : √x < 2 := by
      rw [← Real.sqrt_sq zero_le_two]
      exact Real.sqrt_lt_sqrt hx (by linarith)
    have hfl : ⌊Real.log x / Real.log 2⌋₊ ≤ 1 :=
      Nat.lt_succ_iff.mp (natFloor_log_div_log_two_lt hx two_pos (by norm_num; exact hx4))
    rw [theta_eq_zero_of_lt_two hsqrt, Icc_eq_empty (by omega), sum_empty, add_zero]
    rcases lt_or_ge x 2 with hx2 | hx2
    · simp [psi_eq_zero_of_lt_two hx2, theta_eq_zero_of_lt_two hx2]
    · rw [psi_eq_theta_add_sum_theta hx2, add_sub_cancel_left, Icc_eq_empty (by omega), sum_empty]
  · exact psi_sub_theta_eq_theta_sqrt_add_sum' hx4 le_rfl

/-- For every real `x`, `θ √x ≤ ψ x - θ x`. -/
theorem theta_sqrt_le_psi_sub_theta (x : ℝ) : θ √x ≤ ψ x - θ x := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [Real.sqrt_eq_zero_of_nonpos hx.le, theta_zero,
      psi_eq_zero_of_lt_two (by linarith), theta_eq_zero_of_lt_two (by linarith), sub_self]
  · rw [psi_sub_theta_eq_theta_sqrt_add_sum hx, le_add_iff_nonneg_right]
    exact sum_nonneg fun _ _ ↦ theta_nonneg _

/-- For every `x ≥ 0`, `θ √x + θ (x ^ (1 / 3)) ≤ ψ x - θ x`. -/
theorem theta_sqrt_add_theta_cbrt_le_psi_sub_theta {x : ℝ} (hx : 0 ≤ x) :
    θ √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x := by
  rcases lt_or_ge x 8 with hx8 | hx8
  · have hcbrt : x ^ ((1 : ℝ) / 3) < 2 := by
      calc x ^ ((1 : ℝ) / 3) < (8 : ℝ) ^ ((1 : ℝ) / 3) :=
            Real.rpow_lt_rpow hx hx8 (by norm_num)
        _ = 2 := by norm_num [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast_mul]
    rw [theta_eq_zero_of_lt_two hcbrt, add_zero]
    exact theta_sqrt_le_psi_sub_theta x
  · rw [psi_sub_theta_eq_theta_sqrt_add_sum hx, add_le_add_iff_left]
    have h3 : 3 ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊ :=
      mem_Icc.mpr ⟨le_rfl, le_natFloor_log_div_log_two (by norm_num; exact hx8)⟩
    simpa using single_le_sum (f := fun k : ℕ ↦ θ (x ^ ((1 : ℝ) / k)))
      (fun _ _ ↦ theta_nonneg _) h3

/-- Monotonicity bound on the `k ≥ 3` root sum: for `x ≥ 0`,
`∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} θ (x ^ (1 / k)) ≤ (⌊log x / log 2⌋₊ - 2 : ℕ) * θ (x ^ (1 / 3))`. -/
theorem sum_Icc_three_theta_rpow_le_sub_two_mul_theta_cbrt {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) ≤
      ((⌊Real.log x / Real.log 2⌋₊ - 2 : ℕ) : ℝ) * θ (x ^ ((1 : ℝ) / 3)) := by
  rcases lt_or_ge x 8 with hx8 | hx8
  · have hfl : ⌊Real.log x / Real.log 2⌋₊ ≤ 2 :=
      Nat.lt_succ_iff.mp (natFloor_log_div_log_two_lt hx (by norm_num) (by norm_num; exact hx8))
    rw [Icc_eq_empty (by omega), sum_empty]
    positivity
  · have h3 : 3 ≤ ⌊Real.log x / Real.log 2⌋₊ :=
      le_natFloor_log_div_log_two (by norm_num; exact hx8)
    have hcard : #(Icc 3 ⌊Real.log x / Real.log 2⌋₊) = ⌊Real.log x / Real.log 2⌋₊ - 2 := by
      rw [Nat.card_Icc]; omega
    calc ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k))
        ≤ ∑ _k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / 3)) := by
          refine sum_le_sum fun k hk ↦ theta_mono ?_
          exact Real.rpow_le_rpow_of_exponent_le (by linarith)
            (one_div_le_one_div_of_le (by norm_num) (mod_cast (mem_Icc.mp hk).1))
      _ = (#(Icc 3 ⌊Real.log x / Real.log 2⌋₊) : ℝ) * θ (x ^ ((1 : ℝ) / 3)) := by simp
      _ = ((⌊Real.log x / Real.log 2⌋₊ - 2 : ℕ) : ℝ) * θ (x ^ ((1 : ℝ) / 3)) := by rw [hcard]

/-- Continuous-factor form of `sum_Icc_three_theta_rpow_le_sub_two_mul_theta_cbrt`: for `x ≥ 0`,
`∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} θ (x ^ (1 / k)) ≤ max (log x / log 2 - 2) 0 * θ (x ^ (1 / 3))`. -/
theorem sum_Icc_three_theta_rpow_le_mul_theta_cbrt {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) ≤
      max (Real.log x / Real.log 2 - 2) 0 * θ (x ^ ((1 : ℝ) / 3)) := by
  refine (sum_Icc_three_theta_rpow_le_sub_two_mul_theta_cbrt hx).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (theta_nonneg _)
  rcases lt_or_ge ⌊Real.log x / Real.log 2⌋₊ 2 with h2 | h2
  · rw [Nat.sub_eq_zero_of_le h2.le, Nat.cast_zero]
    exact le_max_right _ _
  · rw [Nat.cast_sub h2, Nat.cast_ofNat]
    refine (sub_le_sub_right (Nat.floor_le ?_) _).trans (le_max_left _ _)
    by_contra! hneg
    have : ⌊Real.log x / Real.log 2⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
    omega

/-- Under a linear upper bound `θ y ≤ c * y` on `(0, x ^ (1 / 3)]`, the `k ≥ 3` root sum is at
most `c * max (log x / log 2 - 2) 0 * x ^ (1 / 3)` for every `x ≥ 0` (when `x ≥ 4`, `1` lies in
`(0, x ^ (1 / 3)]`, forcing `0 ≤ c` automatically). -/
theorem sum_Icc_three_theta_rpow_le {x c : ℝ} (hx : 0 ≤ x)
    (hc : ∀ y, 0 < y → y ≤ x ^ ((1 : ℝ) / 3) → θ y ≤ c * y) :
    ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) ≤
      c * max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) := by
  rcases lt_or_ge x 4 with hx4 | hx4
  · have hfl : ⌊Real.log x / Real.log 2⌋₊ ≤ 1 :=
      Nat.lt_succ_iff.mp (natFloor_log_div_log_two_lt hx two_pos (by norm_num; exact hx4))
    have hmax : max (Real.log x / Real.log 2 - 2) 0 = 0 := by
      rw [max_eq_right_iff, sub_nonpos]
      rcases hx.eq_or_lt with rfl | hxpos
      · norm_num
      · rw [div_le_iff₀ (Real.log_pos one_lt_two), ← Real.log_four_eq]
        exact (Real.log_lt_log hxpos hx4).le
    rw [Icc_eq_empty (by omega), sum_empty, hmax, mul_zero, zero_mul]
  · have hcbrt_pos : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by positivity) _
    calc ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k))
        ≤ max (Real.log x / Real.log 2 - 2) 0 * θ (x ^ ((1 : ℝ) / 3)) :=
          sum_Icc_three_theta_rpow_le_mul_theta_cbrt hx
      _ ≤ max (Real.log x / Real.log 2 - 2) 0 * (c * x ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left (hc _ hcbrt_pos le_rfl) (le_max_right _ _)
      _ = c * max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) := by ring

/-- Unconditional upper bound on `ψ - θ`: for every `x ≥ 0`,
`ψ x - θ x ≤ log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ (1 / 3))`. -/
theorem psi_sub_theta_le_log_four_mul {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x ≤ Real.log 4 * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) := by
  rw [psi_sub_theta_eq_theta_sqrt_add_sum hx, mul_add, ← mul_assoc]
  exact add_le_add (theta_le_log4_mul_x (Real.sqrt_nonneg x))
    (sum_Icc_three_theta_rpow_le hx fun y hy _ ↦ theta_le_log4_mul_x hy.le)

/-! ### Bidirectional transfers between `θ` and `ψ` -/

/-- A lower bound `d * √x ≤ θ √x` transfers directly to `d * √x ≤ ψ x - θ x`. -/
theorem mul_sqrt_le_psi_sub_theta {x d : ℝ} (hd : d * √x ≤ θ √x) : d * √x ≤ ψ x - θ x :=
  hd.trans (theta_sqrt_le_psi_sub_theta x)

/-- Retaining the cube-root term gives `d * √x + θ (x ^ (1 / 3)) ≤ ψ x - θ x` for `x ≥ 0`. -/
theorem mul_sqrt_add_theta_cbrt_le_psi_sub_theta {x d : ℝ} (hx : 0 ≤ x) (hd : d * √x ≤ θ √x) :
    d * √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x := by
  linarith [theta_sqrt_add_theta_cbrt_le_psi_sub_theta hx]

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Proposition 4 (lower half).** If `θ y ≥ (1 - η) * y` for
all `y ≥ √X` and `x ≥ X ≥ 0`, then `(1 - η) * √x + θ (x ^ (1 / 3)) ≤ ψ x - θ x`. -/
theorem one_sub_mul_sqrt_add_theta_cbrt_le_psi_sub_theta {X x η : ℝ} (hX : 0 ≤ X) (hx : X ≤ x)
    (hθ : ∀ y, √X ≤ y → (1 - η) * y ≤ θ y) :
    (1 - η) * √x + θ (x ^ ((1 : ℝ) / 3)) ≤ ψ x - θ x :=
  mul_sqrt_add_theta_cbrt_le_psi_sub_theta (hX.trans hx) (hθ √x (Real.sqrt_le_sqrt hx))

/-- Upper bound on `ψ x - θ x` from `θ √x ≤ d * √x` and `θ y ≤ c * y` on `(0, x ^ (1 / 3)]`. -/
theorem psi_sub_theta_le_of_theta_le {x d c : ℝ} (hx : 0 ≤ x) (hsqrt : θ √x ≤ d * √x)
    (hc : ∀ y, 0 < y → y ≤ x ^ ((1 : ℝ) / 3) → θ y ≤ c * y) :
    ψ x - θ x ≤ d * √x + c * max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) := by
  rw [psi_sub_theta_eq_theta_sqrt_add_sum hx]
  exact add_le_add hsqrt (sum_Icc_three_theta_rpow_le hx hc)

/-- Lower `ψ - θ` transfer from `|θ y - y| ≤ ε * y` on `[y₀, ∞)`: for `y₀ ≥ 0` and `x ≥ y₀ ^ 2`,
`(1 - ε) * √x ≤ ψ x - θ x`. -/
theorem one_sub_mul_sqrt_le_psi_sub_theta_of_abs_theta_sub_self_le {x y₀ ε : ℝ} (hy₀ : 0 ≤ y₀)
    (hx : y₀ ^ 2 ≤ x) (hθ : ∀ y, y₀ ≤ y → |θ y - y| ≤ ε * y) :
    (1 - ε) * √x ≤ ψ x - θ x := by
  have hy₀_sqrt : y₀ ≤ √x := by
    rw [← Real.sqrt_sq hy₀]
    exact Real.sqrt_le_sqrt hx
  refine mul_sqrt_le_psi_sub_theta ?_
  linarith [(abs_sub_le_iff.mp (hθ √x hy₀_sqrt)).2]

/-- Upper `ψ - θ` transfer from `|θ y - y| ≤ ε * y` on `[y₀, ∞)` and `θ y ≤ c * y` on `(0, ∞)`:
for `y₀ ≥ 0` and `x ≥ max 4 (y₀ ^ 2)`,
`ψ x - θ x ≤ (1 + ε) * √x + c * (log x / log 2 - 2) * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_one_add_mul_sqrt_add {x y₀ ε c : ℝ} (hy₀ : 0 ≤ y₀)
    (hx : max 4 (y₀ ^ 2) ≤ x) (hc : ∀ y, 0 < y → θ y ≤ c * y)
    (hθ : ∀ y, y₀ ≤ y → |θ y - y| ≤ ε * y) :
    ψ x - θ x ≤ (1 + ε) * √x + c * (Real.log x / Real.log 2 - 2) * x ^ ((1 : ℝ) / 3) := by
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hy₀_sqrt : y₀ ≤ √x := by
    rw [← Real.sqrt_sq hy₀]
    exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hx)
  have hsqrt : θ √x ≤ (1 + ε) * √x := by linarith [(abs_sub_le_iff.mp (hθ √x hy₀_sqrt)).1]
  have hmax : max (Real.log x / Real.log 2 - 2) 0 = Real.log x / Real.log 2 - 2 := by
    rw [max_eq_left_iff, sub_nonneg, le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_four_eq]
    exact Real.log_le_log (by norm_num) hx4
  simpa only [hmax] using psi_sub_theta_le_of_theta_le (by linarith) hsqrt fun y hy _ ↦ hc y hy

/-- Pointwise transfer from `|ψ x - x| ≤ e` and `ψ x - θ x ≤ δ` to `|θ x - x| ≤ e + δ`. -/
theorem abs_theta_sub_self_le_of_psi_sub_theta_le {x e δ : ℝ} (hψ : |ψ x - x| ≤ e)
    (hδ : ψ x - θ x ≤ δ) : |θ x - x| ≤ e + δ := by
  have h0 : 0 ≤ ψ x - θ x := sub_nonneg.mpr (theta_le_psi x)
  rw [abs_le] at hψ ⊢
  exact ⟨by linarith, by linarith⟩

/-- Pointwise transfer from `|θ x - x| ≤ e` and `ψ x - θ x ≤ δ` to `|ψ x - x| ≤ e + δ`. -/
theorem abs_psi_sub_self_le_of_psi_sub_theta_le {x e δ : ℝ} (hθ : |θ x - x| ≤ e)
    (hδ : ψ x - θ x ≤ δ) : |ψ x - x| ≤ e + δ := by
  have h0 : 0 ≤ ψ x - θ x := sub_nonneg.mpr (theta_le_psi x)
  rw [abs_le] at hθ ⊢
  exact ⟨by linarith, by linarith⟩

/-- Pointwise transfer from a `ψ`-error bound `|ψ x - x| ≤ e` (`0 ≤ x`) to `θ`:
`|θ x - x| ≤ e + log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ (1 / 3))`. -/
theorem abs_theta_sub_self_le_of_abs_psi_sub_self_le {x e : ℝ} (hx : 0 ≤ x) (hψ : |ψ x - x| ≤ e) :
    |θ x - x| ≤ e + Real.log 4 * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  abs_theta_sub_self_le_of_psi_sub_theta_le hψ (psi_sub_theta_le_log_four_mul hx)

/-- Pointwise transfer from a `θ`-error bound `|θ x - x| ≤ e` (`0 ≤ x`) to `ψ`:
`|ψ x - x| ≤ e + log 4 * (√x + max (log x / log 2 - 2) 0 * x ^ (1 / 3))`. -/
theorem abs_psi_sub_self_le_of_abs_theta_sub_self_le {x e : ℝ} (hx : 0 ≤ x) (hθ : |θ x - x| ≤ e) :
    |ψ x - x| ≤ e + Real.log 4 * (√x + max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3)) :=
  abs_psi_sub_self_le_of_psi_sub_theta_le hθ (psi_sub_theta_le_log_four_mul hx)

/-! ### Dyadic higher-root weight and upper envelope -/

/-- Normalized cube-root and higher-root weight (`f(x)` of Broadbent–Kadiri–Lumley–Ng–Wilk (2.4)):
`∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} x ^ (1 / k - 1 / 3)` for `x ≥ 8`, and `0` for `x < 8`. -/
noncomputable def cubeRootTailWeight (x : ℝ) : ℝ :=
  if x < 8 then 0 else ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)

/-- Dyadic upper envelope (`F(X)` of Broadbent–Kadiri–Lumley–Ng–Wilk, Proposition 3):
`max (cubeRootTailWeight X) (cubeRootTailWeight (2 ^ (⌊log X / log 2⌋₊ + 1)))`. -/
noncomputable def cubeRootTailBound (X : ℝ) : ℝ :=
  max (cubeRootTailWeight X) (cubeRootTailWeight ((2 : ℝ) ^ (⌊Real.log X / Real.log 2⌋₊ + 1)))

/-- Defining unfolding of `Chebyshev.cubeRootTailWeight`. -/
theorem cubeRootTailWeight_def (x : ℝ) :
    cubeRootTailWeight x =
      if x < 8 then 0 else ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3) := by
  rfl

/-- `Chebyshev.cubeRootTailWeight` vanishes below `8`. -/
@[simp]
theorem cubeRootTailWeight_of_lt_eight {x : ℝ} (hx : x < 8) : cubeRootTailWeight x = 0 := by
  rw [cubeRootTailWeight_def]
  simp [hx]

/-- Sum formula for `Chebyshev.cubeRootTailWeight` when `8 ≤ x`. -/
theorem cubeRootTailWeight_of_ge_eight {x : ℝ} (hx : 8 ≤ x) :
    cubeRootTailWeight x = ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3) := by
  rw [cubeRootTailWeight_def]
  simp [not_lt.mpr hx]

/-- For every `x ≥ 0`, `cubeRootTailWeight x` equals the finite sum
`∑_{3 ≤ k ≤ ⌊log x / log 2⌋₊} x ^ (1 / k - 1 / 3)` without a cutoff case split (for `0 ≤ x < 8`,
`⌊log x / log 2⌋₊ ≤ 2`, so the index set is empty). -/
theorem cubeRootTailWeight_eq_sum {x : ℝ} (hx : 0 ≤ x) :
    cubeRootTailWeight x = ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3) := by
  rcases lt_or_ge x 8 with hx8 | hx8
  · rw [cubeRootTailWeight_of_lt_eight hx8]
    have hfl : ⌊Real.log x / Real.log 2⌋₊ ≤ 2 :=
      Nat.lt_succ_iff.mp (natFloor_log_div_log_two_lt hx (by norm_num) (by norm_num; exact hx8))
    rw [Icc_eq_empty (by omega), sum_empty]
  · exact cubeRootTailWeight_of_ge_eight hx8

/-- Separating `k = 3` writes `cubeRootTailWeight x` for `x ≥ 8` as `1` plus the `k ≥ 4` sum. -/
theorem cubeRootTailWeight_eq_one_add_sum {x : ℝ} (hx : 8 ≤ x) :
    cubeRootTailWeight x =
      1 + ∑ k ∈ Icc 4 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3) := by
  have h3 : 3 ≤ ⌊Real.log x / Real.log 2⌋₊ :=
    le_natFloor_log_div_log_two (show (2 : ℝ) ^ 3 ≤ x by norm_num; exact hx)
  rw [cubeRootTailWeight_of_ge_eight hx, ← add_sum_Ioc_eq_sum_Icc h3, ← Icc_add_one_left_eq_Ioc]
  norm_num

/-- `Chebyshev.cubeRootTailWeight` is nonnegative everywhere. -/
theorem cubeRootTailWeight_nonneg (x : ℝ) : 0 ≤ cubeRootTailWeight x := by
  rw [cubeRootTailWeight_def]
  split_ifs with hx
  · exact le_rfl
  · exact sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by linarith) _

/-- For `8 ≤ x`, `1 ≤ cubeRootTailWeight x`. -/
theorem one_le_cubeRootTailWeight {x : ℝ} (hx : 8 ≤ x) : 1 ≤ cubeRootTailWeight x := by
  rw [cubeRootTailWeight_eq_one_add_sum hx, le_add_iff_nonneg_right]
  exact sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by linarith) _

/-- Crude logarithmic upper bound: `cubeRootTailWeight x ≤ max (log x / log 2 - 2) 0` for every
`x ≥ 0` (in fact for all `x : ℝ`). -/
theorem cubeRootTailWeight_le_max_sub_two (x : ℝ) :
    cubeRootTailWeight x ≤ max (Real.log x / Real.log 2 - 2) 0 := by
  rcases lt_or_ge x 8 with hx8 | hx8
  · rw [cubeRootTailWeight_of_lt_eight hx8]
    exact le_max_right _ _
  · have h3 : 3 ≤ ⌊Real.log x / Real.log 2⌋₊ :=
      le_natFloor_log_div_log_two (show (2 : ℝ) ^ 3 ≤ x by norm_num; exact hx8)
    have hcard : #(Icc 3 ⌊Real.log x / Real.log 2⌋₊) = ⌊Real.log x / Real.log 2⌋₊ - 2 := by
      rw [Nat.card_Icc]; omega
    calc cubeRootTailWeight x
        ≤ ∑ _k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, (1 : ℝ) := by
          rw [cubeRootTailWeight_of_ge_eight hx8]
          refine sum_le_sum fun k hk ↦ Real.rpow_le_one_of_one_le_of_nonpos (by linarith) ?_
          linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
            (mod_cast (mem_Icc.mp hk).1 : (3 : ℝ) ≤ k)]
      _ = ((⌊Real.log x / Real.log 2⌋₊ - 2 : ℕ) : ℝ) := by
          rw [sum_const, hcard, nsmul_eq_mul, mul_one]
      _ ≤ max (Real.log x / Real.log 2 - 2) 0 := by
          rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
          refine (sub_le_sub_right (Nat.floor_le ?_) _).trans (le_max_left _ _)
          exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg one_le_two)

/-- Defining unfolding of `Chebyshev.cubeRootTailBound`. -/
theorem cubeRootTailBound_def (X : ℝ) :
    cubeRootTailBound X =
      max (cubeRootTailWeight X)
        (cubeRootTailWeight ((2 : ℝ) ^ (⌊Real.log X / Real.log 2⌋₊ + 1))) := by
  rfl

/-- `cubeRootTailWeight X ≤ cubeRootTailBound X` by definition. -/
theorem le_cubeRootTailBound (X : ℝ) : cubeRootTailWeight X ≤ cubeRootTailBound X := by
  rw [cubeRootTailBound_def]
  exact le_max_left _ _

/-- `Chebyshev.cubeRootTailBound` is nonnegative everywhere. -/
theorem cubeRootTailBound_nonneg (X : ℝ) : 0 ≤ cubeRootTailBound X :=
  (cubeRootTailWeight_nonneg X).trans (le_cubeRootTailBound X)

/-! ### Dyadic monotonicity and Proposition 3 of Broadbent–Kadiri–Lumley–Ng–Wilk -/

/-- Closed form of `cubeRootTailWeight` at dyadic powers `2 ^ n` for `n ≥ 3`:
`cubeRootTailWeight (2 ^ n) = 1 + ∑_{4 ≤ k ≤ n} 2 ^ (n / k - n / 3)`. -/
theorem cubeRootTailWeight_two_pow {n : ℕ} (hn : 3 ≤ n) :
    cubeRootTailWeight ((2 : ℝ) ^ n) =
      1 + ∑ k ∈ Icc 4 n, (2 : ℝ) ^ ((n : ℝ) / k - (n : ℝ) / 3) := by
  have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ one_le_two hn
  have hfl : ⌊Real.log ((2 : ℝ) ^ n) / Real.log 2⌋₊ = n :=
    natFloor_log_div_log_two_eq le_rfl (pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self n))
  rw [cubeRootTailWeight_eq_one_add_sum h8, hfl]
  refine congrArg (1 + ·) (sum_congr rfl fun k _ ↦ ?_)
  rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
  congr 1
  ring

/-- On each dyadic interval `[2 ^ n, 2 ^ (n + 1))` with `n ≥ 4`, `cubeRootTailWeight` is strictly
decreasing. -/
theorem strictAntiOn_cubeRootTailWeight_Ico_two_pow {n : ℕ} (hn : 4 ≤ n) :
    StrictAntiOn cubeRootTailWeight (Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))) := by
  intro x hx y hy hxy
  have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ one_le_two (by omega)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) (h8.trans hx.1)
  rw [cubeRootTailWeight_eq_one_add_sum (h8.trans hx.1),
    cubeRootTailWeight_eq_one_add_sum (h8.trans hy.1),
    natFloor_log_div_log_two_eq hx.1 hx.2, natFloor_log_div_log_two_eq hy.1 hy.2,
    add_lt_add_iff_left]
  refine sum_lt_sum (fun k hk ↦ ?_) ⟨4, mem_Icc.mpr ⟨le_rfl, hn⟩, ?_⟩
  · have hk4 : (4 : ℝ) ≤ k := mod_cast (mem_Icc.mp hk).1
    have hexp : (1 : ℝ) / k - 1 / 3 ≤ 0 := by
      linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hk4]
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy.le hexp
  · exact Real.strictAntiOn_rpow_Ioi_of_exponent_neg (by norm_num) hx0 (hx0.trans hxy) hxy

/-- On every dyadic interval `[2 ^ n, 2 ^ (n + 1))` (for any `n : ℕ`), `cubeRootTailWeight` is
antitone (constant `0` for `n ≤ 2`, constant `1` for `n = 3`, strictly decreasing for `n ≥ 4`). -/
theorem antitoneOn_cubeRootTailWeight_Ico_two_pow (n : ℕ) :
    AntitoneOn cubeRootTailWeight (Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))) := by
  rcases lt_or_ge n 4 with hn | hn
  · intro x hx y hy _
    interval_cases n
    · simp [cubeRootTailWeight_of_lt_eight (hx.2.trans_le (by norm_num)),
        cubeRootTailWeight_of_lt_eight (hy.2.trans_le (by norm_num))]
    · simp [cubeRootTailWeight_of_lt_eight (hx.2.trans_le (by norm_num)),
        cubeRootTailWeight_of_lt_eight (hy.2.trans_le (by norm_num))]
    · simp [cubeRootTailWeight_of_lt_eight (hx.2.trans_le (by norm_num)),
        cubeRootTailWeight_of_lt_eight (hy.2.trans_le (by norm_num))]
    · have h8x : 8 ≤ x := (by norm_num : (8 : ℝ) ≤ (2 : ℝ) ^ 3).trans hx.1
      have h8y : 8 ≤ y := (by norm_num : (8 : ℝ) ≤ (2 : ℝ) ^ 3).trans hy.1
      rw [cubeRootTailWeight_eq_one_add_sum h8x, cubeRootTailWeight_eq_one_add_sum h8y,
        natFloor_log_div_log_two_eq hx.1 hx.2, natFloor_log_div_log_two_eq hy.1 hy.2]
      simp
  · exact (strictAntiOn_cubeRootTailWeight_Ico_two_pow hn).antitoneOn

private lemma lt_two_rpow_div {q : ℝ} {a b : ℕ} (hq : 0 ≤ q) (hb : 0 < b)
    (h : q ^ b < (2 : ℝ) ^ a) : q < (2 : ℝ) ^ ((a : ℝ) / b) := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  rw [← Real.rpow_lt_rpow_iff hq (by positivity) hb', Real.rpow_natCast,
    ← Real.rpow_mul zero_le_two, div_mul_cancel₀ _ hb'.ne', Real.rpow_natCast]
  exact h

private lemma two_rpow_div_le {q : ℝ} {a b : ℕ} (hq : 0 ≤ q) (hb : 0 < b)
    (h : (2 : ℝ) ^ a ≤ q ^ b) : (2 : ℝ) ^ ((a : ℝ) / b) ≤ q := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  rw [← Real.rpow_le_rpow_iff (by positivity) hq hb', ← Real.rpow_mul zero_le_two,
    div_mul_cancel₀ _ hb'.ne', Real.rpow_natCast, Real.rpow_natCast]
  exact h

private lemma two_rpow_div_lt {q : ℝ} {a b : ℕ} (hq : 0 ≤ q) (hb : 0 < b)
    (h : (2 : ℝ) ^ a < q ^ b) : (2 : ℝ) ^ ((a : ℝ) / b) < q := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  rw [← Real.rpow_lt_rpow_iff (by positivity) hq hb', ← Real.rpow_mul zero_le_two,
    div_mul_cancel₀ _ hb'.ne', Real.rpow_natCast, Real.rpow_natCast]
  exact h

private lemma le_two_rpow_div {q : ℝ} {a b : ℕ} (hq : 0 ≤ q) (hb : 0 < b)
    (h : q ^ b ≤ (2 : ℝ) ^ a) : q ≤ (2 : ℝ) ^ ((a : ℝ) / b) := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  rw [← Real.rpow_le_rpow_iff hq (by positivity) hb', Real.rpow_natCast,
    ← Real.rpow_mul zero_le_two, div_mul_cancel₀ _ hb'.ne', Real.rpow_natCast]
  exact h

private lemma two_rpow_sub_lt {e₁ e₂ q₁ q₂ : ℝ} {a₁ b₁ a₂ b₂ : ℕ}
    (hq₁ : 0 ≤ q₁) (hb₁ : 0 < b₁) (he₁ : e₁ = (a₁ : ℝ) / b₁) (h₁ : (2 : ℝ) ^ a₁ < q₁ ^ b₁)
    (hq₂ : 0 ≤ q₂) (hb₂ : 0 < b₂) (he₂ : e₂ = (a₂ : ℝ) / b₂) (h₂ : q₂ ^ b₂ ≤ (2 : ℝ) ^ a₂) :
    (2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂ < q₁ - q₂ := by
  subst he₁ he₂
  linarith [two_rpow_div_lt hq₁ hb₁ h₁, le_two_rpow_div hq₂ hb₂ h₂]

private lemma lt_two_rpow_sub {e₁ e₂ q₁ q₂ : ℝ} {a₁ b₁ a₂ b₂ : ℕ}
    (hq₁ : 0 ≤ q₁) (hb₁ : 0 < b₁) (he₁ : e₁ = (a₁ : ℝ) / b₁) (h₁ : q₁ ^ b₁ < (2 : ℝ) ^ a₁)
    (hq₂ : 0 ≤ q₂) (hb₂ : 0 < b₂) (he₂ : e₂ = (a₂ : ℝ) / b₂) (h₂ : (2 : ℝ) ^ a₂ ≤ q₂ ^ b₂) :
    q₁ - q₂ < (2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂ := by
  subst he₁ he₂
  linarith [lt_two_rpow_div hq₁ hb₁ h₁, two_rpow_div_le hq₂ hb₂ h₂]

private lemma cubeRootTailWeight_two_pow_sub_succ_mul {n : ℕ} (hn : 3 ≤ n) :
    (cubeRootTailWeight ((2 : ℝ) ^ n) - cubeRootTailWeight ((2 : ℝ) ^ (n + 1))) *
        (2 : ℝ) ^ (((n : ℝ) + 1) / 3) =
      (∑ k ∈ Icc 4 n, ((2 : ℝ) ^ ((n : ℝ) / k + 1 / 3) - (2 : ℝ) ^ (((n : ℝ) + 1) / k))) - 2 := by
  rw [cubeRootTailWeight_two_pow hn, cubeRootTailWeight_two_pow (by omega),
    sum_Icc_succ_top (by omega : 4 ≤ n + 1)]
  have hlast : (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / (n + 1 : ℕ) - ((n + 1 : ℕ) : ℝ) / 3) *
      (2 : ℝ) ^ (((n : ℝ) + 1) / 3) = 2 := by
    rw [← Real.rpow_add two_pos, Nat.cast_add, Nat.cast_one,
      div_self (by positivity : (n : ℝ) + 1 ≠ 0), sub_add_cancel, Real.rpow_one]
  calc (1 + ∑ k ∈ Icc 4 n, (2 : ℝ) ^ ((n : ℝ) / k - (n : ℝ) / 3) -
        (1 + ((∑ k ∈ Icc 4 n, (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / k - ((n + 1 : ℕ) : ℝ) / 3)) +
          (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / (n + 1 : ℕ) - ((n + 1 : ℕ) : ℝ) / 3)))) *
          (2 : ℝ) ^ (((n : ℝ) + 1) / 3)
      = (∑ k ∈ Icc 4 n, ((2 : ℝ) ^ ((n : ℝ) / k - (n : ℝ) / 3) -
          (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / k - ((n + 1 : ℕ) : ℝ) / 3))) *
            (2 : ℝ) ^ (((n : ℝ) + 1) / 3) -
        (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) / (n + 1 : ℕ) - ((n + 1 : ℕ) : ℝ) / 3) *
          (2 : ℝ) ^ (((n : ℝ) + 1) / 3) := by
          rw [sum_sub_distrib]
          ring
    _ = (∑ k ∈ Icc 4 n, ((2 : ℝ) ^ ((n : ℝ) / k + 1 / 3) - (2 : ℝ) ^ (((n : ℝ) + 1) / k))) - 2 := by
          rw [hlast, sum_mul]
          refine congrArg (· - 2) (sum_congr rfl fun k _ ↦ ?_)
          rw [sub_mul, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos, Nat.cast_add, Nat.cast_one]
          congr 1 <;> congr 1 <;> ring

/-- Sharpness of the threshold `n = 9`: `cubeRootTailWeight (2 ^ 8) < cubeRootTailWeight (2 ^ 9)`
(`3.1669… < 3.2108…`), so the sequence `n ↦ cubeRootTailWeight (2 ^ n)` is not antitone from
`n = 8`. -/
theorem cubeRootTailWeight_two_pow_eight_lt_nine :
    cubeRootTailWeight ((2 : ℝ) ^ 8) < cubeRootTailWeight ((2 : ℝ) ^ 9) := by
  have hmul := cubeRootTailWeight_two_pow_sub_succ_mul (n := 8) (by norm_num)
  have hsum : (∑ k ∈ Icc (4 : ℕ) 8, ((2 : ℝ) ^ ((8 : ℝ) / (k : ℝ) + 1 / 3) -
      (2 : ℝ) ^ (((8 : ℝ) + 1) / (k : ℝ)))) < 2 := by
    have h4 : (2 : ℝ) ^ ((8 : ℝ) / 4 + 1 / 3) - (2 : ℝ) ^ (((8 : ℝ) + 1) / 4) < 101 / 20 - 19 / 4 :=
      two_rpow_sub_lt (a₁ := 7) (b₁ := 3) (a₂ := 9) (b₂ := 4) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h5 : (2 : ℝ) ^ ((8 : ℝ) / 5 + 1 / 3) - (2 : ℝ) ^ (((8 : ℝ) + 1) / 5) < 77 / 20 - 69 / 20 :=
      two_rpow_sub_lt (a₁ := 29) (b₁ := 15) (a₂ := 9) (b₂ := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h6 : (2 : ℝ) ^ ((8 : ℝ) / 6 + 1 / 3) - (2 : ℝ) ^ (((8 : ℝ) + 1) / 6) < 16 / 5 - 14 / 5 :=
      two_rpow_sub_lt (a₁ := 5) (b₁ := 3) (a₂ := 3) (b₂ := 2) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h7 : (2 : ℝ) ^ ((8 : ℝ) / 7 + 1 / 3) - (2 : ℝ) ^ (((8 : ℝ) + 1) / 7) < 14 / 5 - 12 / 5 :=
      two_rpow_sub_lt (a₁ := 31) (b₁ := 21) (a₂ := 9) (b₂ := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h8 : (2 : ℝ) ^ ((8 : ℝ) / 8 + 1 / 3) - (2 : ℝ) ^ (((8 : ℝ) + 1) / 8) < 51 / 20 - 43 / 20 :=
      two_rpow_sub_lt (a₁ := 4) (b₁ := 3) (a₂ := 9) (b₂ := 8) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hexpand : Icc (4 : ℕ) 8 = {4, 5, 6, 7, 8} := by decide
    rw [hexpand]
    simp only [mem_insert, mem_singleton, Nat.reduceEqDiff, or_self, not_false_eq_true,
      sum_insert, sum_singleton, Nat.cast_ofNat]
    linarith
  have hneg : (cubeRootTailWeight ((2 : ℝ) ^ 8) - cubeRootTailWeight ((2 : ℝ) ^ 9)) *
      (2 : ℝ) ^ (((8 : ℝ) + 1) / 3) < 0 := by linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (((8 : ℝ) + 1) / 3) := by positivity
  by_contra! h
  exact hneg.not_ge (mul_nonneg (sub_nonneg.mpr h) hpos.le)

private lemma two_lt_sum_Icc_four_nine_two_rpow :
    2 < ∑ k ∈ Icc (4 : ℕ) 9,
      ((2 : ℝ) ^ ((9 : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / (k : ℝ))) := by
  have h4 : (299 : ℝ) / 50 - 283 / 50 <
      (2 : ℝ) ^ ((9 : ℝ) / 4 + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / 4) :=
    lt_two_rpow_sub (a₁ := 31) (b₁ := 12) (a₂ := 5) (b₂ := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 : (219 : ℝ) / 50 - 4 < (2 : ℝ) ^ ((9 : ℝ) / 5 + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / 5) :=
    lt_two_rpow_sub (a₁ := 32) (b₁ := 15) (a₂ := 2) (b₂ := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 : (89 : ℝ) / 25 - 159 / 50 < (2 : ℝ) ^ ((9 : ℝ) / 6 + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / 6) :=
    lt_two_rpow_sub (a₁ := 11) (b₁ := 6) (a₂ := 5) (b₂ := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 : (153 : ℝ) / 50 - 27 / 10 < (2 : ℝ) ^ ((9 : ℝ) / 7 + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / 7) :=
    lt_two_rpow_sub (a₁ := 34) (b₁ := 21) (a₂ := 10) (b₂ := 7) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : (137 : ℝ) / 50 - 119 / 50 <
      (2 : ℝ) ^ ((9 : ℝ) / 8 + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / 8) :=
    lt_two_rpow_sub (a₁ := 35) (b₁ := 24) (a₂ := 5) (b₂ := 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 : (5 : ℝ) / 2 - 109 / 50 < (2 : ℝ) ^ ((9 : ℝ) / 9 + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / 9) :=
    lt_two_rpow_sub (a₁ := 4) (b₁ := 3) (a₂ := 10) (b₂ := 9) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hexpand : Icc (4 : ℕ) 9 = {4, 5, 6, 7, 8, 9} := by decide
  rw [hexpand]
  simp only [mem_insert, mem_singleton, Nat.reduceEqDiff, or_self, not_false_eq_true,
    sum_insert, sum_singleton, Nat.cast_ofNat]
  linarith

private lemma cubeRootTailWeight_two_pow_succ_lt {n : ℕ} (hn : 9 ≤ n) :
    cubeRootTailWeight ((2 : ℝ) ^ (n + 1)) < cubeRootTailWeight ((2 : ℝ) ^ n) := by
  have hmul := cubeRootTailWeight_two_pow_sub_succ_mul (n := n) (by omega)
  have hterm_nonneg (m k : ℕ) (hk : 4 ≤ k) :
      0 ≤ (2 : ℝ) ^ ((m : ℝ) / k + 1 / 3) - (2 : ℝ) ^ (((m : ℝ) + 1) / k) := by
    refine sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    have hk4 : (4 : ℝ) ≤ k := mod_cast hk
    have hinv : (1 : ℝ) / k ≤ 1 / 3 := by
      linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hk4]
    linarith [show ((m : ℝ) + 1) / k = (m : ℝ) / k + 1 / k by ring]
  have hsub :
      ∑ k ∈ Icc (4 : ℕ) 9,
          ((2 : ℝ) ^ ((9 : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / (k : ℝ))) ≤
        ∑ k ∈ Icc (4 : ℕ) n,
          ((2 : ℝ) ^ ((n : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ (((n : ℝ) + 1) / (k : ℝ))) := by
    calc ∑ k ∈ Icc (4 : ℕ) 9,
          ((2 : ℝ) ^ ((9 : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / (k : ℝ)))
        ≤ ∑ k ∈ Icc (4 : ℕ) 9,
            ((2 : ℝ) ^ ((n : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ (((n : ℝ) + 1) / (k : ℝ))) := by
          refine sum_le_sum fun k hk ↦ ?_
          have hk4 : 4 ≤ k := (mem_Icc.mp hk).1
          have hkpos : (0 : ℝ) < k := by positivity
          have hscale :
              (2 : ℝ) ^ ((n : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ (((n : ℝ) + 1) / (k : ℝ)) =
                (2 : ℝ) ^ (((n : ℝ) - 9) / (k : ℝ)) *
                  ((2 : ℝ) ^ ((9 : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ ((10 : ℝ) / (k : ℝ))) := by
            rw [mul_sub, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
            congr 1 <;> congr 1 <;> ring
          rw [hscale]
          refine le_mul_of_one_le_left ?_ ?_
          · simpa only [Nat.cast_ofNat, show (9 : ℝ) + 1 = 10 by norm_num] using
              hterm_nonneg 9 k hk4
          · refine Real.one_le_rpow one_le_two (div_nonneg ?_ hkpos.le)
            exact sub_nonneg.mpr (mod_cast hn)
      _ ≤ ∑ k ∈ Icc (4 : ℕ) n,
            ((2 : ℝ) ^ ((n : ℝ) / (k : ℝ) + 1 / 3) - (2 : ℝ) ^ (((n : ℝ) + 1) / (k : ℝ))) :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hn) fun k hk _ ↦
            hterm_nonneg n k (mem_Icc.mp hk).1
  have hpos_prod : 0 < (cubeRootTailWeight ((2 : ℝ) ^ n) -
      cubeRootTailWeight ((2 : ℝ) ^ (n + 1))) * (2 : ℝ) ^ (((n : ℝ) + 1) / 3) := by
    linarith [two_lt_sum_Icc_four_nine_two_rpow]
  have hpos_pow : (0 : ℝ) < (2 : ℝ) ^ (((n : ℝ) + 1) / 3) := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hpos_pow).mp hpos_prod)

/-- For `n ≥ 9`, the dyadic sequence `n ↦ cubeRootTailWeight (2 ^ n)` is strictly decreasing. -/
theorem strictAntiOn_cubeRootTailWeight_two_pow :
    StrictAntiOn (fun n : ℕ ↦ cubeRootTailWeight ((2 : ℝ) ^ n)) (Set.Ici 9) := by
  intro m hm n _ hmn
  have hanti : StrictAnti fun d : ℕ ↦ cubeRootTailWeight ((2 : ℝ) ^ (9 + d)) :=
    strictAnti_nat_of_succ_lt fun d ↦ cubeRootTailWeight_two_pow_succ_lt (Nat.le_add_right 9 d)
  have hd : m - 9 < n - 9 := by simp only [Set.mem_Ici] at hm; omega
  have hm9 : 9 + (m - 9) = m := by simp only [Set.mem_Ici] at hm; omega
  have hn9 : 9 + (n - 9) = n := by simp only [Set.mem_Ici] at hm; omega
  simpa only [hm9, hn9] using hanti hd

/-- Non-strict form of `strictAntiOn_cubeRootTailWeight_two_pow` on `Set.Ici 9`. -/
theorem antitoneOn_cubeRootTailWeight_two_pow :
    AntitoneOn (fun n : ℕ ↦ cubeRootTailWeight ((2 : ℝ) ^ n)) (Set.Ici 9) :=
  strictAntiOn_cubeRootTailWeight_two_pow.antitoneOn

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Proposition 3.** For every `X ≥ 2 ^ 9` and every `x ≥ X`,
`cubeRootTailWeight x ≤ cubeRootTailBound X`. -/
theorem cubeRootTailWeight_le_cubeRootTailBound {X x : ℝ} (hX : (2 : ℝ) ^ 9 ≤ X) (hx : X ≤ x) :
    cubeRootTailWeight x ≤ cubeRootTailBound X := by
  rw [cubeRootTailBound_def X]
  set N := ⌊Real.log X / Real.log 2⌋₊
  set n := ⌊Real.log x / Real.log 2⌋₊
  have h1X : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ 9).trans hX
  have h1x : 1 ≤ x := h1X.trans hx
  have hXN : X ∈ Set.Ico ((2 : ℝ) ^ N) ((2 : ℝ) ^ (N + 1)) := by
    have hlogb : N = ⌊Real.logb 2 X⌋₊ := by rw [Real.logb]
    rw [hlogb]
    exact ⟨Real.pow_natFloor_logb_le_self one_lt_two h1X,
      Real.lt_pow_natFloor_logb_add_one one_lt_two (zero_lt_one.trans_le h1X)⟩
  have hxn : x ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)) := by
    have hlogb : n = ⌊Real.logb 2 x⌋₊ := by rw [Real.logb]
    rw [hlogb]
    exact ⟨Real.pow_natFloor_logb_le_self one_lt_two h1x,
      Real.lt_pow_natFloor_logb_add_one one_lt_two (zero_lt_one.trans_le h1x)⟩
  have h9N : 9 ≤ N := le_natFloor_log_div_log_two hX
  have hNn : N ≤ n := le_natFloor_log_div_log_two (hXN.1.trans hx)
  rcases hNn.eq_or_lt with hEq | hLt
  · have hxN : x ∈ Set.Ico ((2 : ℝ) ^ N) ((2 : ℝ) ^ (N + 1)) := hEq ▸ hxn
    exact (antitoneOn_cubeRootTailWeight_Ico_two_pow N hXN hxN hx).trans (le_max_left _ _)
  · have hstep1 : cubeRootTailWeight x ≤ cubeRootTailWeight ((2 : ℝ) ^ n) :=
      antitoneOn_cubeRootTailWeight_Ico_two_pow n
        ⟨le_rfl, pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self n)⟩ hxn hxn.1
    have hstep2 : cubeRootTailWeight ((2 : ℝ) ^ n) ≤ cubeRootTailWeight ((2 : ℝ) ^ (N + 1)) :=
      antitoneOn_cubeRootTailWeight_two_pow (Set.mem_Ici.mpr (by omega))
        (Set.mem_Ici.mpr (by omega)) hLt
    exact (hstep1.trans hstep2).trans (le_max_right _ _)

/-- The upper envelope `Chebyshev.cubeRootTailBound` is antitone on `[2 ^ 9, ∞)`. -/
theorem antitoneOn_cubeRootTailBound_Ici :
    AntitoneOn cubeRootTailBound (Set.Ici ((2 : ℝ) ^ 9)) := by
  intro X hX Y hY hXY
  rw [cubeRootTailBound_def Y]
  refine max_le (cubeRootTailWeight_le_cubeRootTailBound hX hXY) ?_
  have h1Y : 1 ≤ Y := (by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ 9).trans hY
  have hYlt : Y < (2 : ℝ) ^ (⌊Real.log Y / Real.log 2⌋₊ + 1) := by
    simpa only [Real.logb] using
      Real.lt_pow_natFloor_logb_add_one one_lt_two (zero_lt_one.trans_le h1Y)
  exact cubeRootTailWeight_le_cubeRootTailBound hX (hXY.trans hYlt.le)

/-! ### General-input bounds of Broadbent–Kadiri–Lumley–Ng–Wilk -/

/-- Under a linear upper bound `θ y ≤ c * y` on `(0, x ^ (1 / 3)]`, the `k ≥ 3` root sum is at
most `c * cubeRootTailWeight x * x ^ (1 / 3)` for every `x ≥ 0`. -/
theorem sum_Icc_three_theta_rpow_le_cubeRootTailWeight {x c : ℝ} (hx : 0 ≤ x)
    (hc : ∀ y, 0 < y → y ≤ x ^ ((1 : ℝ) / 3) → θ y ≤ c * y) :
    ∑ k ∈ Icc 3 ⌊Real.log x / Real.log 2⌋₊, θ (x ^ ((1 : ℝ) / k)) ≤
      c * cubeRootTailWeight x * x ^ ((1 : ℝ) / 3) := by
  rcases lt_or_ge x 8 with hx8 | hx8
  · have hfl : ⌊Real.log x / Real.log 2⌋₊ ≤ 2 :=
      Nat.lt_succ_iff.mp (natFloor_log_div_log_two_lt hx (by norm_num) (by norm_num; exact hx8))
    rw [Icc_eq_empty (by omega), sum_empty, cubeRootTailWeight_of_lt_eight hx8, mul_zero, zero_mul]
  · have hxpos : 0 < x := by positivity
    rw [cubeRootTailWeight_of_ge_eight hx8, mul_assoc, sum_mul, mul_sum]
    refine sum_le_sum fun k hk ↦ ?_
    have hk_le : x ^ ((1 : ℝ) / k) ≤ x ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith)
        (one_div_le_one_div_of_le (by norm_num) (mod_cast (mem_Icc.mp hk).1))
    calc θ (x ^ ((1 : ℝ) / k))
        ≤ c * x ^ ((1 : ℝ) / k) := hc _ (Real.rpow_pos_of_pos hxpos _) hk_le
      _ = c * (x ^ ((1 : ℝ) / k - 1 / 3) * x ^ ((1 : ℝ) / 3)) := by
          rw [← Real.rpow_add hxpos, sub_add_cancel]

/-- For every `x ≥ 0` and linear bound `θ y ≤ c * y` on `(0, x ^ (1 / 3)]`,
`ψ x - θ x - θ √x ≤ c * cubeRootTailWeight x * x ^ (1 / 3)`. -/
theorem psi_sub_theta_sub_theta_sqrt_le {x c : ℝ} (hx : 0 ≤ x)
    (hc : ∀ y, 0 < y → y ≤ x ^ ((1 : ℝ) / 3) → θ y ≤ c * y) :
    ψ x - θ x - θ √x ≤ c * cubeRootTailWeight x * x ^ ((1 : ℝ) / 3) := by
  rw [psi_sub_theta_eq_theta_sqrt_add_sum hx, add_sub_cancel_left]
  exact sum_Icc_three_theta_rpow_le_cubeRootTailWeight hx hc

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Proposition 4 (upper half).** If `2 ^ 9 ≤ X ≤ x`,
`θ y ≤ c' * y` for `y ≥ √X`, and `θ y ≤ c * y` on `(0, x ^ (1 / 3)]`, then
`ψ x - θ x ≤ c' * √x + c * cubeRootTailBound X * x ^ (1 / 3)`. -/
theorem psi_sub_theta_le_mul_sqrt_add_mul_cubeRootTailBound {X x c' c : ℝ}
    (hX : (2 : ℝ) ^ 9 ≤ X) (hx : X ≤ x) (hc' : ∀ y, √X ≤ y → θ y ≤ c' * y)
    (hc : ∀ y, 0 < y → y ≤ x ^ ((1 : ℝ) / 3) → θ y ≤ c * y) :
    ψ x - θ x ≤ c' * √x + c * cubeRootTailBound X * x ^ ((1 : ℝ) / 3) := by
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 9).trans (hX.trans hx)
  have hc_nonneg : 0 ≤ c := by
    have h1le : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 3) :=
      Real.one_le_rpow ((by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ 9).trans (hX.trans hx)) (by norm_num)
    simpa using hc 1 zero_lt_one h1le
  have htail : ψ x - θ x - θ √x ≤ c * cubeRootTailBound X * x ^ ((1 : ℝ) / 3) :=
    (psi_sub_theta_sub_theta_sqrt_le hx0 hc).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cubeRootTailWeight_le_cubeRootTailBound hX hx) hc_nonneg)
        (Real.rpow_nonneg hx0 _))
  linarith [hc' √x (Real.sqrt_le_sqrt hx)]

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Corollary 3.1 (and 2.1).** If `θ y ≤ y` on `(0, x₁]`
(`0 < x₁`) and `|ψ y - y| ≤ δ * y` for `y ≥ x₁`, then `θ x ≤ (1 + δ) * x` for every `x ≥ 0`. -/
theorem theta_le_one_add_mul_of_psi_le {x₁ δ x : ℝ} (hx₁ : 0 < x₁)
    (hlow : ∀ y, 0 < y → y ≤ x₁ → θ y ≤ y)
    (hψ : ∀ y, x₁ ≤ y → |ψ y - y| ≤ δ * y) (hx : 0 ≤ x) :
    θ x ≤ (1 + δ) * x := by
  have hδ : 0 ≤ δ := by
    have h := (abs_nonneg (ψ x₁ - x₁)).trans (hψ x₁ le_rfl)
    exact nonneg_of_mul_nonneg_left h hx₁
  rcases hx.eq_or_lt with rfl | hxpos
  · simp
  · rcases le_or_gt x x₁ with hle | hgt
    · calc θ x ≤ x := hlow x hxpos hle
        _ ≤ (1 + δ) * x := by nlinarith
    · calc θ x ≤ ψ x := theta_le_psi x
        _ ≤ (1 + δ) * x := by linarith [(abs_sub_le_iff.mp (hψ x hgt.le)).1]

private lemma two_pow_nine_lt_exp_seven : (2 : ℝ) ^ 9 < Real.exp 7 := by
  have h27 : (2 : ℝ) ^ 9 < 2.7182818283 ^ 7 := by norm_num
  have hexp : 2.7182818283 ^ 7 < Real.exp 7 := by
    rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  exact h27.trans hexp

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Theorem 5.** Suppose `ε : ℝ → ℝ` satisfies
`|ψ y - y| ≤ ε b * y` for every `b ≥ 7` and `y ≥ exp b`, and `θ y ≤ y` on `(0, x₁]` with
`x₁ ≥ exp 7`. Then for every `b ≥ 7` and `x ≥ exp b`,
`ψ x - θ x ≤ a₁ * √x + (1 + ε (log x₁)) * cubeRootTailBound (exp b) * x ^ (1 / 3)`,
where `a₁ = 1 + ε (log x₁)` if `b ≤ 2 * log x₁` and `a₁ = 1 + ε (b / 2)` otherwise. -/
theorem psi_sub_theta_le_of_abs_psi_sub_self_le {ε : ℝ → ℝ} {x₁ b x : ℝ}
    (hx₁ : Real.exp 7 ≤ x₁) (hb : 7 ≤ b) (hx : Real.exp b ≤ x)
    (hlow : ∀ y, 0 < y → y ≤ x₁ → θ y ≤ y)
    (hψ : ∀ u, 7 ≤ u → ∀ y, Real.exp u ≤ y → |ψ y - y| ≤ ε u * y) :
    ψ x - θ x ≤
      (if b ≤ 2 * Real.log x₁ then 1 + ε (Real.log x₁) else 1 + ε (b / 2)) * √x +
        (1 + ε (Real.log x₁)) * cubeRootTailBound (Real.exp b) * x ^ ((1 : ℝ) / 3) := by
  have hx₁_pos : 0 < x₁ := (Real.exp_pos 7).trans_le hx₁
  have hlog_x₁ : 7 ≤ Real.log x₁ := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 7) hx₁
  have hglobal (y : ℝ) (hy : 0 ≤ y) : θ y ≤ (1 + ε (Real.log x₁)) * y :=
    theta_le_one_add_mul_of_psi_le hx₁_pos hlow
      (fun z hz ↦ hψ (Real.log x₁) hlog_x₁ z ((Real.exp_log hx₁_pos).trans_le hz)) hy
  have hX9 : (2 : ℝ) ^ 9 ≤ Real.exp b :=
    two_pow_nine_lt_exp_seven.le.trans (Real.exp_le_exp.mpr hb)
  refine psi_sub_theta_le_mul_sqrt_add_mul_cubeRootTailBound hX9 hx (fun y hy ↦ ?_)
    fun y hy _ ↦ hglobal y hy.le
  split_ifs with hb_le
  · exact hglobal y ((Real.sqrt_nonneg _).trans hy)
  · have hb2 : 7 ≤ b / 2 := by linarith
    have hexp_sqrt : Real.exp (b / 2) ≤ y := by
      refine le_trans ?_ hy
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      exact Real.exp_le_exp.mpr (by ring_nf; rfl)
    calc θ y ≤ ψ y := theta_le_psi y
      _ ≤ (1 + ε (b / 2)) * y := by linarith [(abs_sub_le_iff.mp (hψ (b / 2) hb2 y hexp_sqrt)).1]

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Lemma 11.** From Costa Pereira's upper bound
`Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi`, if `(1 - δ) * x ≤ ψ x`, `ψ y ≤ c₀ * y` for all
`y > 0`, and `x ≥ exp b` (for any real `b`), then
`(1 - δ - c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5))) * x ≤ θ x`. -/
theorem le_theta_of_psi_le_mul {b x δ c₀ : ℝ} (hx : Real.exp b ≤ x)
    (hψ_lo : (1 - δ) * x ≤ ψ x) (hc₀ : ∀ y, 0 < y → ψ y ≤ c₀ * y) :
    (1 - δ - c₀ * (Real.exp (-b / 2) + Real.exp (-2 * b / 3) + Real.exp (-4 * b / 5))) * x ≤
      θ x := by
  have hxpos : 0 < x := (Real.exp_pos b).trans_le hx
  have hc₀_nonneg : 0 ≤ c₀ := by simpa using hc₀ 1 zero_lt_one
  have hpow (a : ℝ) (ha : a < 1) : x ^ a ≤ Real.exp ((a - 1) * b) * x := by
    calc x ^ a = x ^ (a - 1) * x ^ (1 : ℝ) := by
          rw [← Real.rpow_add hxpos, sub_add_cancel]
      _ ≤ (Real.exp b) ^ (a - 1) * x := by
          rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos (Real.exp_pos b) hx (by linarith)) hxpos.le
      _ = Real.exp ((a - 1) * b) * x := by rw [← Real.exp_mul, mul_comm b (a - 1)]
  have h2 : ψ (x ^ (2 : ℝ)⁻¹) ≤ c₀ * (Real.exp (-b / 2) * x) :=
    (hc₀ _ (Real.rpow_pos_of_pos hxpos _)).trans <| mul_le_mul_of_nonneg_left
      (by simpa [show ((2 : ℝ)⁻¹ - 1) * b = -b / 2 by ring] using hpow (2 : ℝ)⁻¹ (by norm_num))
      hc₀_nonneg
  have h3 : ψ (x ^ (3 : ℝ)⁻¹) ≤ c₀ * (Real.exp (-2 * b / 3) * x) :=
    (hc₀ _ (Real.rpow_pos_of_pos hxpos _)).trans <| mul_le_mul_of_nonneg_left
      (by simpa [show ((3 : ℝ)⁻¹ - 1) * b = -2 * b / 3 by ring] using hpow (3 : ℝ)⁻¹ (by norm_num))
      hc₀_nonneg
  have h5 : ψ (x ^ (5 : ℝ)⁻¹) ≤ c₀ * (Real.exp (-4 * b / 5) * x) :=
    (hc₀ _ (Real.rpow_pos_of_pos hxpos _)).trans <| mul_le_mul_of_nonneg_left
      (by simpa [show ((5 : ℝ)⁻¹ - 1) * b = -4 * b / 5 by ring] using hpow (5 : ℝ)⁻¹ (by norm_num))
      hc₀_nonneg
  linarith [psi_sub_theta_le_psi_add_psi_add_psi x]

/-- **Broadbent–Kadiri–Lumley–Ng–Wilk, Lemma 9.** From Costa Pereira's upper bound
`Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi`, if `x ≥ 0`, `x - C * √x ≤ ψ x`,
`ψ √x ≤ √x + c * x ^ (1 / 4)`, and `ψ y ≤ c₀ * y` for all `y > 0`, then
`x - (C + 1) * √x - c₀ * x ^ (1 / 3) - c * x ^ (1 / 4) - c₀ * x ^ (1 / 5) ≤ θ x`. -/
theorem le_theta_of_sub_psi_le_mul_sqrt {x C c c₀ : ℝ} (hx : 0 ≤ x)
    (hψ_lo : x - C * √x ≤ ψ x) (hψ_sqrt : ψ √x ≤ √x + c * x ^ ((1 : ℝ) / 4))
    (hc₀ : ∀ y, 0 < y → ψ y ≤ c₀ * y) :
    x - (C + 1) * √x - c₀ * x ^ ((1 : ℝ) / 3) - c * x ^ ((1 : ℝ) / 4) -
        c₀ * x ^ ((1 : ℝ) / 5) ≤ θ x := by
  rcases hx.eq_or_lt with rfl | hxpos
  · norm_num at hψ_lo hψ_sqrt ⊢
  · have h2 : ψ (x ^ (2 : ℝ)⁻¹) ≤ √x + c * x ^ ((1 : ℝ) / 4) := by
      simpa only [Real.sqrt_eq_rpow, one_div] using hψ_sqrt
    have h3 : ψ (x ^ (3 : ℝ)⁻¹) ≤ c₀ * x ^ ((1 : ℝ) / 3) := by
      simpa only [one_div] using hc₀ (x ^ (3 : ℝ)⁻¹) (Real.rpow_pos_of_pos hxpos _)
    have h5 : ψ (x ^ (5 : ℝ)⁻¹) ≤ c₀ * x ^ ((1 : ℝ) / 5) := by
      simpa only [one_div] using hc₀ (x ^ (5 : ℝ)⁻¹) (Real.rpow_pos_of_pos hxpos _)
    linarith [psi_sub_theta_le_psi_add_psi_add_psi x]

end Chebyshev
