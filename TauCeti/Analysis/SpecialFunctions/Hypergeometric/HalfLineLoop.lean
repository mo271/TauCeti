/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Topology.Compactness.Normed

/-!
# The half-line loop integral for the Gauss hypergeometric function

Euler's integral `Complex.eulerIntegral a b c z` represents the regularized Gauss hypergeometric
function only when `0 < re b < re c`. Substituting `t = u / (1 - u)` carries the unit interval
`(0, 1)` onto the positive half-line `(0, ∞)` and concentrates the `b`-dependent endpoint
singularity at `0`, while the behavior at `∞` depends only on `re (c - b) > 0`. Replacing the
integration ray `[0, ∞)` by a Hankel-type keyhole contour from `+∞` counterclockwise around `0`
and back to `+∞` removes the lower barrier `0 < re b` and continues the representation across the
half-space `re b < re c` away from the positive integer poles of `Γ(1 - b)` (DLMF 15.6.3).

We define `Complex.hypergeometricHalfLineLoop a b c z ρ` explicitly as the sum of three pieces at
loop radius `ρ`: the incoming ray `(ρ, ∞)` with zero phase of `t`, the counterclockwise circle
`t = ρ exp(i θ)` (`θ ∈ [0, 2π]`, which crosses the negative real axis at `-ρ ∈ (-1, 0)` with
`ph t = π` and `ph(1 + t) = 0`), and the outgoing ray `(ρ, ∞)` carrying the monodromy factor
`exp(2πi(b - 1))`. Whenever `re b < re c`, `1 - z ∈ Complex.slitPlane`, `0 < ρ < 1`, and
`‖1 - z‖ * ρ < 1` (so both branch points `-1` and `1 / (z - 1)` lie outside the loop), this
contour integral is independent of `ρ` and jointly holomorphic in all four complex variables
`(a, b, c, z)`. On the classical overlap `0 < re b < re c` the circle contribution vanishes as
`ρ → 0⁺`, collapsing the loop to `Complex.eulerIntegral` across `0 ≤ ρ < 1` and yielding
DLMF 15.6.3 together with closed-form evaluations at `z = 0`, `a = 0`, and `z = 1` across the full
continued parameter half-spaces.

## Main definitions and results

* `Complex.hypergeometricHalfLineLoop`: the `(0+)` keyhole loop integral from `+∞` around `0` at
  radius `ρ` and back to `+∞`.
* `Complex.hypergeometricHalfLineLoop_eq`: contour-radius independence for `0 < ρ < 1` and
  `‖1 - z‖ * ρ < 1` when `b.re < c.re` and `1 - z ∈ Complex.slitPlane`.
* `Complex.analyticOnNhd_hypergeometricHalfLineLoop`: joint holomorphy in `(a, b, c, z)` on
  `{p | p.2.1.re < p.2.2.1.re ∧ 1 - p.2.2.2 ∈ slitPlane ∧ ‖1 - p.2.2.2‖ * ρ < 1}`.
* `Complex.hypergeometricHalfLineLoop_eq_eulerIntegral` and
  `Complex.eulerIntegral_eq_hypergeometricHalfLineLoop`: loop collapse and DLMF 15.6.3 across
  `0 ≤ ρ < 1` in the overlap `0 < b.re < c.re`.
* `Complex.hypergeometricHalfLineLoop_zero`, `Complex.hypergeometricHalfLineLoop_zero_left`, and
  `Complex.hypergeometricHalfLineLoop_one`: closed-form evaluations across `b.re < c.re` and
  Gauss's half-space `b.re < c.re - a.re`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equations 15.6.1 and 15.6.3.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 5, §9.3.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., Cambridge University
  Press, 1927, §§12.43 and 14.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Interval Real Topology

namespace Complex

/-- The integrand along the positive half-line `(ρ, ∞)` in the `(0+)` hypergeometric loop. -/
private abbrev halfLineRayIntegrand (a b c z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (b - 1) * ((t : ℂ) + 1) ^ (a - c) * ((1 - z) * t + 1) ^ (-a)

/-- The parameterized integrand along the counterclockwise circle `t = ρ exp(i θ)` (`θ ∈ [0, 2π]`)
of the `(0+)` hypergeometric loop. -/
private abbrev halfLineCircleIntegrand (a b c z : ℂ) (ρ θ : ℝ) : ℂ :=
  ((ρ : ℂ) ^ (b - 1) * cexp (θ * I * (b - 1))) *
    ((ρ : ℂ) * cexp (θ * I) + 1) ^ (a - c) *
    ((1 - z) * ((ρ : ℂ) * cexp (θ * I)) + 1) ^ (-a) *
    (I * (ρ : ℂ) * cexp (θ * I))

/-- The `(0+)` keyhole loop integral for the Gauss hypergeometric function (DLMF 15.6.3):
starting at `+∞` with `ph t = 0`, encircling `0` counterclockwise along `|t| = ρ` so that
`ph t = π` and `ph(1 + t) = 0` at `t = -ρ ∈ (-1, 0)`, and returning to `+∞` with `ph t = 2π`.
When `b.re < c.re`, `1 - z ∈ Complex.slitPlane`, `0 < ρ < 1`, and `‖1 - z‖ * ρ < 1`, this value
is independent of `ρ` and continues Euler's integral across `b.re ≤ 0`; outside that regime it is
only the totalized Bochner sum. -/
def hypergeometricHalfLineLoop (a b c z : ℂ) (ρ : ℝ) : ℂ :=
  (-∫ t : ℝ in Ioi ρ,
      (t : ℂ) ^ (b - 1) * ((t : ℂ) + 1) ^ (a - c) * ((1 - z) * t + 1) ^ (-a)) +
    (∫ θ : ℝ in (0 : ℝ)..(2 * π),
      ((ρ : ℂ) ^ (b - 1) * cexp (θ * I * (b - 1))) *
        ((ρ : ℂ) * cexp (θ * I) + 1) ^ (a - c) *
        ((1 - z) * ((ρ : ℂ) * cexp (θ * I)) + 1) ^ (-a) *
        (I * (ρ : ℂ) * cexp (θ * I))) +
    (∫ t : ℝ in Ioi ρ,
      (t : ℂ) ^ (b - 1) * cexp (2 * π * I * (b - 1)) *
        ((t : ℂ) + 1) ^ (a - c) * ((1 - z) * t + 1) ^ (-a))

/-- The explicit three-piece contour formula for `hypergeometricHalfLineLoop`. -/
theorem hypergeometricHalfLineLoop_def (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricHalfLineLoop a b c z ρ =
      (-∫ t : ℝ in Ioi ρ,
          (t : ℂ) ^ (b - 1) * ((t : ℂ) + 1) ^ (a - c) * ((1 - z) * t + 1) ^ (-a)) +
        (∫ θ : ℝ in (0 : ℝ)..(2 * π),
          ((ρ : ℂ) ^ (b - 1) * cexp (θ * I * (b - 1))) *
            ((ρ : ℂ) * cexp (θ * I) + 1) ^ (a - c) *
            ((1 - z) * ((ρ : ℂ) * cexp (θ * I)) + 1) ^ (-a) *
            (I * (ρ : ℂ) * cexp (θ * I))) +
        (∫ t : ℝ in Ioi ρ,
          (t : ℂ) ^ (b - 1) * cexp (2 * π * I * (b - 1)) *
            ((t : ℂ) + 1) ^ (a - c) * ((1 - z) * t + 1) ^ (-a)) := (rfl)

/-- The incoming and outgoing rays of `hypergeometricHalfLineLoop` combine unconditionally into
`(cexp (2 * π * I * b) - 1)` times a single half-line integral over `Ioi ρ`. -/
theorem hypergeometricHalfLineLoop_eq_ray_add_circle (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricHalfLineLoop a b c z ρ =
      (cexp (2 * π * I * b) - 1) *
          (∫ t : ℝ in Ioi ρ,
            (t : ℂ) ^ (b - 1) * ((t : ℂ) + 1) ^ (a - c) * ((1 - z) * t + 1) ^ (-a)) +
        ∫ θ : ℝ in (0 : ℝ)..(2 * π),
          ((ρ : ℂ) ^ (b - 1) * cexp (θ * I * (b - 1))) *
            ((ρ : ℂ) * cexp (θ * I) + 1) ^ (a - c) *
            ((1 - z) * ((ρ : ℂ) * cexp (θ * I)) + 1) ^ (-a) *
            (I * (ρ : ℂ) * cexp (θ * I)) := by
  have hexp : cexp (2 * π * I * (b - 1)) = cexp (2 * π * I * b) := by
    rw [mul_sub, mul_one, Complex.exp_sub, exp_two_pi_mul_I, div_one]
  have hpull :
      (∫ t : ℝ in Ioi ρ,
          (t : ℂ) ^ (b - 1) * cexp (2 * π * I * (b - 1)) *
            ((t : ℂ) + 1) ^ (a - c) * ((1 - z) * t + 1) ^ (-a)) =
        cexp (2 * π * I * b) * ∫ t : ℝ in Ioi ρ, halfLineRayIntegrand a b c z t := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      dsimp only [halfLineRayIntegrand]
      rw [hexp]
      ring
  rw [hypergeometricHalfLineLoop_def, hpull]
  dsimp only [halfLineRayIntegrand]
  ring

/-! ### The Cayley chart `t = u / (1 - u)` on `(ρ, ∞)` -/

/-- Under `t = u / (1 - u)` for `u < 1`, the half-line integrand multiplied by the Jacobian
`|((1 - u) ^ 2)⁻¹|` equals Euler's integrand on `(0, 1)`. -/
private lemma abs_deriv_smul_halfLineRayIntegrand (a b c z : ℂ) {u : ℝ} (hu : u < 1) :
    |((1 - u) ^ 2)⁻¹| • halfLineRayIntegrand a b c z (u / (1 - u)) =
      (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a) := by
  have h1u : 0 < 1 - u := sub_pos.2 hu
  have h1u_inv : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  have hexp {x : ℝ} (hx : 0 < x) (w : ℂ) : (x : ℂ) ^ w = cexp (Real.log x * w) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hu_div : ((u / (1 - u) : ℝ) : ℂ) = (((1 - u)⁻¹ : ℝ) : ℂ) * (u : ℂ) := by
    push_cast; ring
  have hadd : ((u / (1 - u) : ℝ) : ℂ) + 1 = (((1 - u)⁻¹ : ℝ) : ℂ) := by
    have hr : u / (1 - u) + 1 = (1 - u)⁻¹ := by field_simp [h1u.ne']; ring
    exact mod_cast hr
  have hz_lin : (1 - z) * ((u / (1 - u) : ℝ) : ℂ) + 1 =
      (((1 - u)⁻¹ : ℝ) : ℂ) * (1 - z * u) := by
    have hne : (1 - (u : ℂ)) ≠ 0 := sub_ne_zero.2 (ofReal_ne_one.mpr hu.ne).symm
    push_cast; field_simp [hne]; ring
  have hsub : 1 - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  have hjac : ((|((1 - u) ^ 2)⁻¹| : ℝ) : ℂ) = cexp (-(2 * Real.log (1 - u))) := by
    have hr : |((1 - u) ^ 2)⁻¹| = Real.exp (-(2 * Real.log (1 - u))) := by
      rw [abs_of_nonneg (by positivity), Real.exp_neg,
        show 2 * Real.log (1 - u) = Real.log ((1 - u) ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [hr, ofReal_exp]; push_cast; ring_nf
  rw [halfLineRayIntegrand, real_smul, hadd, hz_lin, hu_div,
    TauCeti.ofReal_mul_cpow h1u_inv (u : ℂ) (b - 1),
    TauCeti.ofReal_mul_cpow h1u_inv (1 - z * u) (-a), hsub, hjac,
    hexp (inv_pos.2 h1u), hexp (inv_pos.2 h1u), hexp (inv_pos.2 h1u), hexp h1u, Real.log_inv,
    ofReal_neg]
  have hcombine :
      cexp (-(2 * Real.log (1 - u))) *
          (cexp ((-Real.log (1 - u)) * (b - 1)) * (u : ℂ) ^ (b - 1) *
            cexp ((-Real.log (1 - u)) * (a - c)) *
            (cexp ((-Real.log (1 - u)) * -a) * (1 - z * u) ^ (-a))) =
        (cexp (-(2 * Real.log (1 - u))) * cexp ((-Real.log (1 - u)) * (b - 1)) *
            cexp ((-Real.log (1 - u)) * (a - c)) * cexp ((-Real.log (1 - u)) * -a)) *
          ((u : ℂ) ^ (b - 1) * (1 - z * u) ^ (-a)) := by ring
  rw [hcombine, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  have hexp_eq :
      cexp (-(2 * Real.log (1 - u)) + (-Real.log (1 - u)) * (b - 1) +
          (-Real.log (1 - u)) * (a - c) + (-Real.log (1 - u)) * -a) =
        cexp (Real.log (1 - u) * (c - b - 1)) := by
    congr 1; ring
  rw [hexp_eq]
  ring

/-- For `-1 < ρ`, the Cayley substitution `t = u / (1 - u)` identifies the half-line integral over
`Ioi ρ` with Euler's interval integral over `(ρ / (ρ + 1))..1`, with no integrability hypothesis. -/
private lemma integral_halfLineRayIntegrand_Ioi_eq (a b c z : ℂ) {ρ : ℝ} (hρ : -1 < ρ) :
    (∫ t : ℝ in Ioi ρ, halfLineRayIntegrand a b c z t) =
      ∫ u : ℝ in (ρ / (ρ + 1))..1,
        (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a) := by
  set r₀ : ℝ := ρ / (ρ + 1)
  have hρ1 : 0 < ρ + 1 := by linarith
  have hr₀1 : r₀ < 1 := (div_lt_one hρ1).2 (by linarith)
  have hchart : (fun u : ℝ => u / (1 - u)) '' Ioo r₀ 1 = Ioi ρ := by
    rw [TauCeti.image_div_one_sub_Ioo hr₀1]
    congr 1
    dsimp [r₀]
    field_simp [hρ1.ne']
    ring
  have hderiv : ∀ u ∈ Ioo r₀ 1,
      HasDerivWithinAt (fun u : ℝ => u / (1 - u)) ((1 - u) ^ 2)⁻¹ (Ioo r₀ 1) u :=
    fun u hu => (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => u / (1 - u)) (Ioo r₀ 1) :=
    TauCeti.strictMonoOn_div_one_sub.injOn.mono Ioo_subset_Iio_self
  rw [← hchart, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
    setIntegral_congr_fun measurableSet_Ioo fun u hu =>
      abs_deriv_smul_halfLineRayIntegrand a b c z hu.2,
    setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hr₀1.le]

/-- For `0 < r₀ ≤ 1`, `b.re < c.re`, and `1 - z ∈ slitPlane`, Euler's integrand is interval
integrable on `r₀..1` (without requiring `0 < b.re`). -/
private lemma intervalIntegrable_eulerTail (a : ℂ) {b c z : ℂ} {r₀ : ℝ}
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane) :
    IntervalIntegrable
      (fun u : ℝ => (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a))
      volume r₀ 1 := by
  have hcont : ContinuousOn
      (fun u : ℝ => (u : ℂ) ^ (b - 1) * (1 - z * u) ^ (-a)) (uIcc r₀ 1) := by
    rw [uIcc_of_le hr₀1]
    refine ContinuousOn.mul (fun u hu => ?_)
      ((continuousOn_eulerKernel a hz).mono (Icc_subset_Icc hr₀0.le le_rfl))
    exact (continuous_ofReal.continuousAt.cpow continuousAt_const
      (ofReal_mem_slitPlane.2 (hr₀0.trans_le hu.1))).continuousWithinAt
  have hbeta : IntervalIntegrable (fun u : ℝ => (1 - (u : ℂ)) ^ (c - b - 1)) volume r₀ 1 := by
    have h01 := betaIntegral_convergent (u := 1) (v := c - b) one_pos
      (by simpa using sub_pos.2 hbc)
    simpa only [sub_self, cpow_zero, one_mul] using
      h01.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le zero_le_one]; exact ⟨hr₀0.le, hr₀1⟩)
        right_mem_uIcc)
  exact (hbeta.mul_continuousOn hcont).congr fun u _ => by ring

/-- For `0 < ρ`, `b.re < c.re`, and `1 - z ∈ slitPlane`, the half-line integrand is integrable on
`Ioi ρ`. -/
private lemma integrableOn_halfLineRayIntegrand_Ioi (a : ℂ) {b c z : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane) :
    IntegrableOn (halfLineRayIntegrand a b c z) (Ioi ρ) := by
  set r₀ : ℝ := ρ / (ρ + 1)
  have hρ1 : 0 < ρ + 1 := by linarith
  have hr₀0 : 0 < r₀ := div_pos hρ hρ1
  have hr₀1 : r₀ < 1 := (div_lt_one hρ1).2 (by linarith)
  have hchart : (fun u : ℝ => u / (1 - u)) '' Ioo r₀ 1 = Ioi ρ := by
    rw [TauCeti.image_div_one_sub_Ioo hr₀1]
    congr 1; dsimp [r₀]; field_simp [hρ1.ne']; ring
  have hderiv : ∀ u ∈ Ioo r₀ 1,
      HasDerivWithinAt (fun u : ℝ => u / (1 - u)) ((1 - u) ^ 2)⁻¹ (Ioo r₀ 1) u :=
    fun u hu => (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => u / (1 - u)) (Ioo r₀ 1) :=
    TauCeti.strictMonoOn_div_one_sub.injOn.mono Ioo_subset_Iio_self
  rw [← hchart, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le hr₀1.le).1
    (intervalIntegrable_eulerTail a hr₀0 hr₀1.le hbc hz)
  refine (hint.mono_set Ioo_subset_Ioc_self).congr_fun (fun u hu => ?_) measurableSet_Ioo
  exact (abs_deriv_smul_halfLineRayIntegrand a b c z hu.2).symm

/-! ### Contour-radius independence -/

/-- Pullback of the `(0+)` loop integrand to the logarithmic `w`-plane via `t = exp w`. -/
private abbrev halfLineLogIntegrand (a b c z w : ℂ) : ℂ :=
  cexp ((b - 1) * w) * (cexp w + 1) ^ (a - c) * ((1 - z) * cexp w + 1) ^ (-a) * cexp w

/-- Cauchy–Goursat vanishing of `halfLineLogIntegrand` around the rectangle
`[log ρ₁, log ρ₂] × [0, 2π]` when `0 < ρ₁ ≤ ρ₂ < 1` and `‖1 - z‖ * ρ₂ < 1`. -/
private lemma integral_boundary_rect_halfLineLogIntegrand (a b c : ℂ) {z : ℂ} {ρ₁ ρ₂ : ℝ}
    (hρ₁₀ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂₁ : ρ₂ < 1) (hzρ₂ : ‖1 - z‖ * ρ₂ < 1) :
    ((∫ x : ℝ in Real.log ρ₁..Real.log ρ₂,
          halfLineLogIntegrand a b c z ((x : ℂ) + (0 : ℝ) * I)) -
        ∫ x : ℝ in Real.log ρ₁..Real.log ρ₂,
          halfLineLogIntegrand a b c z ((x : ℂ) + ((2 * π : ℝ) : ℂ) * I)) +
      (I • (∫ θ : ℝ in (0 : ℝ)..(2 * π),
          halfLineLogIntegrand a b c z ((Real.log ρ₂ : ℂ) + (θ : ℂ) * I)) -
        I • ∫ θ : ℝ in (0 : ℝ)..(2 * π),
          halfLineLogIntegrand a b c z ((Real.log ρ₁ : ℂ) + (θ : ℂ) * I)) = 0 := by
  have hρ₂₀ : 0 < ρ₂ := hρ₁₀.trans_le hρ₁₂
  have hlog : Real.log ρ₁ ≤ Real.log ρ₂ := Real.log_le_log hρ₁₀ hρ₁₂
  have hdiff : DifferentiableOn ℂ (halfLineLogIntegrand a b c z)
      ([[Real.log ρ₁, Real.log ρ₂]] ×ℂ [[0, 2 * π]]) := by
    intro w hw
    have hw_re : w.re ≤ Real.log ρ₂ := by
      have h1 := hw.1
      rw [uIcc_of_le hlog] at h1
      exact h1.2
    have hnorm_exp : ‖cexp w‖ ≤ ρ₂ := by
      rw [Complex.norm_exp, ← Real.exp_log hρ₂₀]
      exact Real.exp_le_exp.2 hw_re
    have hslit1 : cexp w + 1 ∈ slitPlane := by
      rw [add_comm]
      exact mem_slitPlane_of_norm_lt_one (hnorm_exp.trans_lt hρ₂₁)
    have hslit2 : (1 - z) * cexp w + 1 ∈ slitPlane := by
      rw [add_comm]
      refine mem_slitPlane_of_norm_lt_one ?_
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hnorm_exp (norm_nonneg _)).trans_lt hzρ₂
    exact ((((differentiableAt_id.const_mul (b - 1)).cexp.mul
      ((differentiableAt_id.cexp.add_const 1).cpow_const hslit1)).mul
      (((differentiableAt_id.cexp.const_mul (1 - z)).add_const 1).cpow_const hslit2)).mul
      differentiableAt_id.cexp).differentiableWithinAt
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn (halfLineLogIntegrand a b c z)
    (Real.log ρ₁) ((Real.log ρ₂ : ℂ) + (2 * π : ℝ) * I) (by simpa using hdiff)
  rw [← add_sub_assoc]
  simpa only [ofReal_re, ofReal_im, add_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] using hrect

/-- Exponential change of variables `t = exp x` along the horizontal sides of the logarithmic
rectangle `[log ρ₁, log ρ₂] × [0, 2π]`. -/
private lemma integral_halfLineLogIntegrand_horizontal (a b c z : ℂ) {ρ₁ ρ₂ : ℝ}
    (hρ₁₀ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) :
    (∫ x : ℝ in Real.log ρ₁..Real.log ρ₂,
        halfLineLogIntegrand a b c z ((x : ℂ) + (0 : ℝ) * I)) =
        (∫ t : ℝ in Ioc ρ₁ ρ₂, halfLineRayIntegrand a b c z t) ∧
      (∫ x : ℝ in Real.log ρ₁..Real.log ρ₂,
          halfLineLogIntegrand a b c z ((x : ℂ) + ((2 * π : ℝ) : ℂ) * I)) =
        cexp (2 * π * I * b) * ∫ t : ℝ in Ioc ρ₁ ρ₂, halfLineRayIntegrand a b c z t := by
  have hρ₂₀ : 0 < ρ₂ := hρ₁₀.trans_le hρ₁₂
  have hlog : Real.log ρ₁ ≤ Real.log ρ₂ := Real.log_le_log hρ₁₀ hρ₁₂
  have himg : Real.exp '' Ioc (Real.log ρ₁) (Real.log ρ₂) = Ioc ρ₁ ρ₂ := by
    ext t
    simp only [mem_image, mem_Ioc]
    refine ⟨?_, fun ht => ⟨Real.log t, ⟨Real.log_lt_log hρ₁₀ ht.1,
      Real.log_le_log (hρ₁₀.trans ht.1) ht.2⟩, Real.exp_log (hρ₁₀.trans ht.1)⟩⟩
    rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨by rwa [← Real.exp_log hρ₁₀, Real.exp_lt_exp],
      by rwa [← Real.exp_log hρ₂₀, Real.exp_le_exp]⟩
  have hbot : (∫ x : ℝ in Real.log ρ₁..Real.log ρ₂,
      halfLineLogIntegrand a b c z ((x : ℂ) + (0 : ℝ) * I)) =
      ∫ t : ℝ in Ioc ρ₁ ρ₂, halfLineRayIntegrand a b c z t := by
    rw [intervalIntegral.integral_of_le hlog, ← himg,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    have hexp_b : cexp ((b - 1) * (x : ℂ)) = ((Real.exp x : ℝ) : ℂ) ^ (b - 1) := by
      rw [mul_comm, ← TauCeti.ofReal_exp_cpow]
    rw [ofReal_zero, zero_mul, add_zero, abs_of_pos (Real.exp_pos x), real_smul]
    simp only [halfLineLogIntegrand, halfLineRayIntegrand, hexp_b, ofReal_exp]
    ring
  refine ⟨hbot, ?_⟩
  have hshift (x : ℝ) : halfLineLogIntegrand a b c z ((x : ℂ) + ((2 * π : ℝ) : ℂ) * I) =
      cexp (2 * π * I * b) * halfLineLogIntegrand a b c z ((x : ℂ) + (0 : ℝ) * I) := by
    have hper : cexp ((x : ℂ) + ((2 * π : ℝ) : ℂ) * I) = cexp x := by
      rw [Complex.exp_add, show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring,
        exp_two_pi_mul_I, mul_one]
    have hb_per : cexp ((b - 1) * ((x : ℂ) + ((2 * π : ℝ) : ℂ) * I)) =
        cexp (2 * π * I * b) * cexp ((b - 1) * (x : ℂ)) := by
      rw [mul_add, Complex.exp_add,
        show (b - 1) * (((2 * π : ℝ) : ℂ) * I) = 2 * π * I * b - 2 * π * I by push_cast; ring,
        Complex.exp_sub, exp_two_pi_mul_I, div_one, mul_comm]
    simp only [halfLineLogIntegrand, hper, hb_per, ofReal_zero, zero_mul, add_zero]
    ring
  simp_rw [hshift, intervalIntegral.integral_const_mul, hbot]

/-- Monotone-radius case of `hypergeometricHalfLineLoop_eq`, combining the logarithmic-rectangle
Cauchy–Goursat identity with additivity of the ray integral on `Ioc ρ₁ ρ₂ ∪ Ioi ρ₂ = Ioi ρ₁`. -/
private theorem hypergeometricHalfLineLoop_eq_of_le (a : ℂ) {b c z : ℂ} {ρ₁ ρ₂ : ℝ}
    (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane)
    (hρ₁₀ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂₁ : ρ₂ < 1) (hzρ₂ : ‖1 - z‖ * ρ₂ < 1) :
    hypergeometricHalfLineLoop a b c z ρ₁ = hypergeometricHalfLineLoop a b c z ρ₂ := by
  have hρ₂₀ : 0 < ρ₂ := hρ₁₀.trans_le hρ₁₂
  have hrect := integral_boundary_rect_halfLineLogIntegrand a b c hρ₁₀ hρ₁₂ hρ₂₁ hzρ₂
  obtain ⟨hbot, htop⟩ := integral_halfLineLogIntegrand_horizontal a b c z hρ₁₀ hρ₁₂
  have hvert (ρ : ℝ) (hρ : 0 < ρ) :
      I • (∫ θ : ℝ in (0 : ℝ)..(2 * π),
          halfLineLogIntegrand a b c z ((Real.log ρ : ℂ) + (θ : ℂ) * I)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * π), halfLineCircleIntegrand a b c z ρ θ := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hexp_ρ : cexp ((Real.log ρ : ℂ) + (θ : ℂ) * I) = (ρ : ℂ) * cexp (θ * I) := by
      rw [Complex.exp_add, ← ofReal_exp, Real.exp_log hρ]
    have hexp_b : cexp ((b - 1) * ((Real.log ρ : ℂ) + (θ : ℂ) * I)) =
        (ρ : ℂ) ^ (b - 1) * cexp (θ * I * (b - 1)) := by
      rw [mul_add, Complex.exp_add, mul_comm (b - 1) (Real.log ρ : ℂ),
        ← TauCeti.ofReal_exp_cpow, Real.exp_log hρ, mul_comm (b - 1)]
    simp only [halfLineLogIntegrand, halfLineCircleIntegrand, hexp_ρ, hexp_b, smul_eq_mul]
    ring
  have hint := integrableOn_halfLineRayIntegrand_Ioi a hρ₁₀ hbc hz
  have hsplit : (∫ t : ℝ in Ioi ρ₁, halfLineRayIntegrand a b c z t) =
      (∫ t : ℝ in Ioc ρ₁ ρ₂, halfLineRayIntegrand a b c z t) +
        ∫ t : ℝ in Ioi ρ₂, halfLineRayIntegrand a b c z t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hρ₁₂)),
      Ioc_union_Ioi_eq_Ioi hρ₁₂]
  rw [hbot, htop, hvert ρ₁ hρ₁₀, hvert ρ₂ hρ₂₀] at hrect
  rw [hypergeometricHalfLineLoop_eq_ray_add_circle, hypergeometricHalfLineLoop_eq_ray_add_circle]
  dsimp only [halfLineRayIntegrand, halfLineCircleIntegrand] at hsplit hrect ⊢
  rw [hsplit]
  linear_combination -hrect

/-- **Radius independence of the `(0+)` hypergeometric loop.** Whenever `b.re < c.re`,
`1 - z ∈ Complex.slitPlane`, and both radii lie in `(0, 1)` with `‖1 - z‖ * ρ < 1` (so the
singularities `-1` and `1 / (z - 1)` remain outside the circles), the loop integral does not
depend on the radius. -/
theorem hypergeometricHalfLineLoop_eq (a : ℂ) {b c z : ℂ} {ρ₁ ρ₂ : ℝ}
    (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane)
    (hρ₁₀ : 0 < ρ₁) (hρ₁₁ : ρ₁ < 1) (hzρ₁ : ‖1 - z‖ * ρ₁ < 1)
    (hρ₂₀ : 0 < ρ₂) (hρ₂₁ : ρ₂ < 1) (hzρ₂ : ‖1 - z‖ * ρ₂ < 1) :
    hypergeometricHalfLineLoop a b c z ρ₁ = hypergeometricHalfLineLoop a b c z ρ₂ := by
  rcases le_total ρ₁ ρ₂ with hle | hle
  · exact hypergeometricHalfLineLoop_eq_of_le a hbc hz hρ₁₀ hle hρ₂₁ hzρ₂
  · exact (hypergeometricHalfLineLoop_eq_of_le a hbc hz hρ₂₀ hle hρ₁₁ hzρ₁).symm

/-! ### Joint holomorphy in `(a, b, c, z)` -/

/-- Pointwise power and logarithmic-derivative domination on `(0, 1]` for exponents with
`2 * δ ≤ w.re`. -/
private lemma norm_cpow_and_log_mul_le {y δ : ℝ} {w : ℂ}
    (hy0 : 0 < y) (hy1 : y ≤ 1) (hδ : 0 < δ) (hw : 2 * δ ≤ w.re) :
    ‖(y : ℂ) ^ (w - 1)‖ ≤ y ^ (δ - 1) ∧
      ‖Complex.log (y : ℂ) * (y : ℂ) ^ (w - 1)‖ ≤ δ⁻¹ * y ^ (δ - 1) := by
  have hpow2 : ‖(y : ℂ) ^ (w - 1)‖ ≤ y ^ (2 * δ - 1) := by
    rw [norm_cpow_eq_rpow_re_of_pos hy0, sub_re, one_re]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith)
  have hpow1 : y ^ (2 * δ - 1) ≤ y ^ (δ - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith)
  have hlog : |Real.log y| ≤ δ⁻¹ * y ^ (-δ) := by
    have hlog_le : Real.log (y ^ (-δ)) ≤ y ^ (-δ) :=
      (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 (-δ))).trans (by linarith)
    rw [Real.log_rpow hy0] at hlog_le
    rw [abs_of_nonpos (Real.log_nonpos hy0.le hy1), le_inv_mul_iff₀ hδ]
    linarith
  refine ⟨hpow2.trans hpow1, ?_⟩
  rw [norm_mul, ← ofReal_log hy0.le, norm_real, Real.norm_eq_abs]
  calc |Real.log y| * ‖(y : ℂ) ^ (w - 1)‖
      ≤ (δ⁻¹ * y ^ (-δ)) * y ^ (2 * δ - 1) :=
        mul_le_mul hlog hpow2 (norm_nonneg _) (by positivity)
    _ = δ⁻¹ * (y ^ (-δ) * y ^ (2 * δ - 1)) := by ring
    _ = δ⁻¹ * y ^ (δ - 1) := by
        rw [← Real.rpow_add hy0]
        congr 2; ring

/-- The circle piece of `hypergeometricHalfLineLoop` is jointly holomorphic in `(a, b, c, z)`
whenever `0 < ρ < 1` and `‖1 - z‖ * ρ < 1`. -/
private theorem analyticOnNhd_integral_halfLineCircle {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      ∫ θ : ℝ in (0 : ℝ)..(2 * π), halfLineCircleIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2 ρ θ)
      {p | ‖1 - p.2.2.2‖ * ρ < 1} := by
  intro p hp
  let φ : ℝ → ℂ := fun θ => ((projIcc 0 (2 * π) Real.two_pi_pos.le θ : ℝ) : ℂ)
  let K : Set ℂ := ofReal '' Icc (0 : ℝ) (2 * π)
  have hφ : Continuous φ :=
    continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc)
  have hφK (θ : ℝ) : φ θ ∈ K := ⟨_, (projIcc 0 (2 * π) Real.two_pi_pos.le θ).property, rfl⟩
  have hkernel : ∀ y ∈ K, AnalyticAt ℂ
      (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        ((ρ : ℂ) ^ (q.1.2.1 - 1) * cexp (q.2 * I * (q.1.2.1 - 1))) *
          ((ρ : ℂ) * cexp (q.2 * I) + 1) ^ (q.1.1 - q.1.2.2.1) *
          ((1 - q.1.2.2.2) * ((ρ : ℂ) * cexp (q.2 * I)) + 1) ^ (-q.1.1) *
          (I * (ρ : ℂ) * cexp (q.2 * I))) (p, y) := by
    rintro y ⟨θ, -, rfl⟩
    have hnorm_c : ‖(ρ : ℂ) * cexp ((θ : ℂ) * I)‖ = ρ := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hρ₀.le, norm_exp_ofReal_mul_I, mul_one]
    have hslit1 : (ρ : ℂ) * cexp ((θ : ℂ) * I) + 1 ∈ slitPlane := by
      rw [add_comm]; exact mem_slitPlane_of_norm_lt_one (hnorm_c.trans_lt hρ₁)
    have hslit2 : (1 - p.2.2.2) * ((ρ : ℂ) * cexp ((θ : ℂ) * I)) + 1 ∈ slitPlane := by
      rw [add_comm]; refine mem_slitPlane_of_norm_lt_one ?_
      rwa [norm_mul, hnorm_c]
    have ha : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => q.1.1) (p, θ) :=
      analyticAt_fst.comp analyticAt_fst
    have hb : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => q.1.2.1) (p, θ) :=
      analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
    have hc : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => q.1.2.2.1) (p, θ) :=
      analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))
    have hz : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => q.1.2.2.2) (p, θ) :=
      analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))
    have hcexp : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => cexp (q.2 * I)) (p, θ) :=
      (analyticAt_snd.mul analyticAt_const).cexp
    exact (((((analyticAt_const.cpow (hb.sub analyticAt_const)
        (ofReal_mem_slitPlane.2 hρ₀)).mul
        ((analyticAt_snd.mul analyticAt_const).mul (hb.sub analyticAt_const)).cexp).mul
        (((analyticAt_const.mul hcexp).add analyticAt_const).cpow (ha.sub hc) hslit1)).mul
        ((((analyticAt_const.sub hz).mul (analyticAt_const.mul hcexp)).add
          analyticAt_const).cpow ha.neg hslit2)).mul
        (analyticAt_const.mul hcexp))
  have hweight : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    (continuous_const : Continuous fun _ : ℝ => (1 : ℂ)).integrableOn_Ioc
  have h := TauCeti.analyticAt_integral_smul (isCompact_Icc.image continuous_ofReal)
    hφ hφK hkernel hweight
  convert h using 1
  ext q
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  simp only [one_smul, φ, halfLineCircleIntegrand,
    projIcc_of_mem Real.two_pi_pos.le (Ioc_subset_Icc_self hθ)]

/-- The continuous linear form `(a, b, c, z) ↦ c - b` governing the `u = 1` exponent of Euler's
integrand. -/
private abbrev eulerTailExpCLM : (ℂ × ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).comp
    ((ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ × ℂ))) -
    (ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ × ℂ))

/-- Smooth factor `w ^ (b - 1) * (1 - z * w) ^ (-a)` of the truncated Euler integrand on
`[r₀, 1]` (`0 < r₀`). -/
private abbrev eulerTailSmoothKernel (q : (ℂ × ℂ × ℂ × ℂ) × ℂ) : ℂ :=
  q.2 ^ (q.1.2.1 - 1) * (1 - q.1.2.2.2 * q.2) ^ (-q.1.1)

/-- Partial Fréchet derivative of `eulerTailSmoothKernel` with respect to `(a, b, c, z)`. -/
private abbrev eulerTailSmoothFDeriv (q : (ℂ × ℂ × ℂ × ℂ) × ℂ) : (ℂ × ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
  (fderiv ℂ eulerTailSmoothKernel q).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ × ℂ × ℂ) ℂ)

/-- Euler's integrand viewed as a function of `(a, b, c, z)` and `u`. -/
private abbrev eulerTailIntegrand (q : ℂ × ℂ × ℂ × ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (q.2.1 - 1) * (1 - (u : ℂ)) ^ (q.2.2.1 - q.2.1 - 1) * (1 - q.2.2.2 * u) ^ (-q.1)

/-- Parametric Fréchet derivative of `eulerTailIntegrand` with respect to `(a, b, c, z)`. -/
private abbrev eulerTailFDeriv (q : ℂ × ℂ × ℂ × ℂ) (u : ℝ) : (ℂ × ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
  eulerTailSmoothKernel (q, u) •
      ((Complex.log (1 - (u : ℂ)) * (1 - (u : ℂ)) ^ (eulerTailExpCLM q - 1)) • eulerTailExpCLM) +
    ((1 - (u : ℂ)) ^ (eulerTailExpCLM q - 1)) • eulerTailSmoothFDeriv (q, u)

/-- For `0 < r₀`, `eulerTailSmoothKernel` is jointly holomorphic at `(p₀, y)` for every
`y ∈ ofReal '' Icc r₀ 1` whenever `1 - p₀.2.2.2 ∈ slitPlane`. -/
private lemma analyticAt_eulerTailSmoothKernel {r₀ : ℝ} (hr₀0 : 0 < r₀)
    {p₀ : ℂ × ℂ × ℂ × ℂ} (hz : 1 - p₀.2.2.2 ∈ slitPlane)
    {y : ℂ} (hy : y ∈ ofReal '' Icc r₀ 1) :
    AnalyticAt ℂ eulerTailSmoothKernel (p₀, y) := by
  rcases hy with ⟨u, hu, rfl⟩
  refine ((analyticAt_snd.cpow
    ((analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)).sub analyticAt_const)
    (ofReal_mem_slitPlane.2 (hr₀0.trans_le hu.1))).mul ?_)
  exact (analyticAt_const.sub
    ((analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))).mul
      analyticAt_snd)).cpow (analyticAt_fst.comp analyticAt_fst).neg
    (one_sub_mul_ofReal_mem_slitPlane hz ⟨hr₀0.le.trans hu.1, hu.2⟩)

/-- Pointwise parametric Fréchet derivative and integrable power domination of
`eulerTailIntegrand` at `u ∈ [0, 1)`. -/
private lemma hasFDerivAt_and_norm_eulerTailIntegrand {q : ℂ × ℂ × ℂ × ℂ} {u δ M : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hδ : 0 < δ)
    (hana : AnalyticAt ℂ eulerTailSmoothKernel (q, u))
    (hB_le : ‖eulerTailSmoothKernel (q, u)‖ ≤ M)
    (hG_le : ‖eulerTailSmoothFDeriv (q, u)‖ ≤ M)
    (hL : 2 * δ ≤ (eulerTailExpCLM q).re) :
    HasFDerivAt (fun x => eulerTailIntegrand x u) (eulerTailFDeriv q u) q ∧
      ‖eulerTailFDeriv q u‖ ≤
        (M + M * (δ⁻¹ * ‖eulerTailExpCLM‖)) * (1 - u) ^ (δ - 1) := by
  have hne : 1 - (u : ℂ) ≠ 0 := sub_ne_zero.2 (ofReal_ne_one.mpr hu1.ne).symm
  have hdB : HasFDerivAt (eulerTailSmoothKernel ∘ fun x => (x, (u : ℂ)))
      (eulerTailSmoothFDeriv (q, u)) q :=
    hana.differentiableAt.hasFDerivAt.comp q (hasFDerivAt_prodMk_left (𝕜 := ℂ) q (u : ℂ))
  have hdA : HasFDerivAt (fun x => (1 - (u : ℂ)) ^ (eulerTailExpCLM x - 1))
      ((Complex.log (1 - (u : ℂ)) * (1 - (u : ℂ)) ^ (eulerTailExpCLM q - 1)) • eulerTailExpCLM) q :=
    (((eulerTailExpCLM.hasFDerivAt (x := q)).sub_const (1 : ℂ)).const_cpow (c := 1 - (u : ℂ))
      (Or.inl hne)).congr_fderiv (by rw [mul_comm])
  have hdF : HasFDerivAt (fun x => eulerTailIntegrand x u) (eulerTailFDeriv q u) q :=
    (hdB.mul hdA).congr_of_eventuallyEq
      (Eventually.of_forall fun x => by simp [eulerTailIntegrand, eulerTailSmoothKernel]; ring)
  refine ⟨hdF, ?_⟩
  have h1u : 1 - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  obtain ⟨hpow_le, hlog_le⟩ := norm_cpow_and_log_mul_le (sub_pos.2 hu1) (by linarith) hδ hL
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans hB_le
  calc ‖eulerTailFDeriv q u‖
      ≤ ‖eulerTailSmoothKernel (q, u) • ((Complex.log (1 - (u : ℂ)) *
            (1 - (u : ℂ)) ^ (eulerTailExpCLM q - 1)) • eulerTailExpCLM)‖ +
          ‖((1 - (u : ℂ)) ^ (eulerTailExpCLM q - 1)) • eulerTailSmoothFDeriv (q, u)‖ :=
        norm_add_le _ _
    _ = ‖eulerTailSmoothKernel (q, u)‖ * (‖Complex.log ((1 - u : ℝ) : ℂ) *
            ((1 - u : ℝ) : ℂ) ^ (eulerTailExpCLM q - 1)‖ * ‖eulerTailExpCLM‖) +
          ‖((1 - u : ℝ) : ℂ) ^ (eulerTailExpCLM q - 1)‖ * ‖eulerTailSmoothFDeriv (q, u)‖ := by
        simp only [h1u, norm_smul]
    _ ≤ M * ((δ⁻¹ * (1 - u) ^ (δ - 1)) * ‖eulerTailExpCLM‖) + (1 - u) ^ (δ - 1) * M :=
        add_le_add
          (mul_le_mul hB_le (mul_le_mul_of_nonneg_right hlog_le (norm_nonneg _))
            (by positivity) hM_nn)
          (mul_le_mul hpow_le hG_le (norm_nonneg _) (by positivity))
    _ = (M + M * (δ⁻¹ * ‖eulerTailExpCLM‖)) * (1 - u) ^ (δ - 1) := by ring

/-- Basepoint strong measurability of `eulerTailFDeriv` on `Ι r₀ 1` for `0 < r₀ ≤ 1`. -/
private lemma aestronglyMeasurable_eulerTailFDeriv {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    {p₀ : ℂ × ℂ × ℂ × ℂ} (hz : 1 - p₀.2.2.2 ∈ slitPlane) :
    AEStronglyMeasurable (eulerTailFDeriv p₀) (volume.restrict (Ι r₀ 1)) := by
  have hcont_F' : ContinuousOn (eulerTailFDeriv p₀) (Ioo r₀ 1) := fun u hu => by
    have hana := analyticAt_eulerTailSmoothKernel hr₀0 hz ⟨u, Ioo_subset_Icc_self hu, rfl⟩
    have hslit : 1 - (u : ℂ) ∈ slitPlane := by
      rw [show 1 - (u : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.2 (sub_pos.2 hu.2)
    have hG : ContinuousAt (fun x : ℝ => eulerTailSmoothFDeriv (p₀, x)) u :=
      (hana.fderiv.continuousAt.clm_comp continuousAt_const).comp_of_eq
        (f := fun x : ℝ => (p₀, (x : ℂ)))
        (continuous_const.prodMk continuous_ofReal).continuousAt rfl
    have hB : ContinuousAt (fun x : ℝ => eulerTailSmoothKernel (p₀, x)) u :=
      hana.continuousAt.comp_of_eq (f := fun x : ℝ => (p₀, (x : ℂ)))
        (continuous_const.prodMk continuous_ofReal).continuousAt rfl
    have hpow : ContinuousAt (fun x : ℝ => (1 - (x : ℂ)) ^ (eulerTailExpCLM p₀ - 1)) u :=
      (continuous_const.sub continuous_ofReal).continuousAt.cpow continuousAt_const hslit
    have hlog : ContinuousAt (fun x : ℝ => Complex.log (1 - (x : ℂ))) u :=
      (continuous_const.sub continuous_ofReal).continuousAt.clog hslit
    exact ((hB.smul ((hlog.mul hpow).smul continuousAt_const)).add (hpow.smul hG))
      |>.continuousWithinAt
  rw [uIoc_of_le hr₀1, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact hcont_F'.aestronglyMeasurable measurableSet_Ioo

/-- The truncated Euler integral over `[r₀, 1]` (`0 < r₀ ≤ 1`) is jointly complex differentiable,
hence holomorphic, in `(a, b, c, z)` on `{p | b.re < c.re ∧ 1 - z ∈ slitPlane}`. -/
private theorem analyticOnNhd_integral_eulerTail {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ => ∫ u : ℝ in r₀..1, eulerTailIntegrand p u)
      {p | p.2.1.re < p.2.2.1.re ∧ 1 - p.2.2.2 ∈ slitPlane} := by
  set Ω : Set (ℂ × ℂ × ℂ × ℂ) := {p | p.2.1.re < p.2.2.1.re ∧ 1 - p.2.2.2 ∈ slitPlane}
  have hΩ : IsOpen Ω := (isOpen_lt (continuous_re.comp (continuous_fst.comp continuous_snd))
    (continuous_re.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))).inter
    (isOpen_slitPlane.preimage
      (continuous_const.sub (continuous_snd.comp (continuous_snd.comp continuous_snd))))
  refine DifferentiableOn.analyticOnNhd_of_finiteDimensional (fun p₀ hp₀ => ?_) hΩ
  let K : Set ℂ := ofReal '' Icc r₀ 1
  have hBK (y : ℂ) (hy : y ∈ K) : AnalyticAt ℂ eulerTailSmoothKernel (p₀, y) :=
    analyticAt_eulerTailSmoothKernel hr₀0 hp₀.2 hy
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.image continuous_ofReal).exists_eventually_norm_le
    (F := eulerTailSmoothKernel) (x₀ := p₀) (isOpen_analyticAt ℂ eulerTailSmoothKernel)
    (fun y hy => (hBK y hy).continuousAt) hBK
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc.image continuous_ofReal).exists_eventually_norm_le
    (F := eulerTailSmoothFDeriv) (x₀ := p₀) (isOpen_analyticAt ℂ eulerTailSmoothKernel)
    (fun y hy => (hBK y hy).fderiv.continuousAt.clm_comp continuousAt_const) hBK
  set δ : ℝ := (p₀.2.2.1.re - p₀.2.1.re) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith [hp₀.1]
  set s : Set (ℂ × ℂ × ℂ × ℂ) :=
    {q | (∀ y ∈ K, AnalyticAt ℂ eulerTailSmoothKernel (q, y) ∧
        ‖eulerTailSmoothKernel (q, y)‖ ≤ M₀) ∧
      (∀ y ∈ K, AnalyticAt ℂ eulerTailSmoothKernel (q, y) ∧
        ‖eulerTailSmoothFDeriv (q, y)‖ ≤ M₁) ∧ 2 * δ < (eulerTailExpCLM q).re ∧ q ∈ Ω}
  have hs : s ∈ 𝓝 p₀ := Filter.inter_mem hM₀ (Filter.inter_mem hM₁
    (Filter.inter_mem ((isOpen_lt continuous_const
      (continuous_re.comp eulerTailExpCLM.continuous)).mem_nhds
      (by simp [eulerTailExpCLM, δ]; linarith [hp₀.1])) (hΩ.mem_nhds hp₀)))
  have hmeas_F (q : ℂ × ℂ × ℂ × ℂ) (hq : q ∈ s) :
      AEStronglyMeasurable (eulerTailIntegrand q) (volume.restrict (Ι r₀ 1)) := by
    rw [uIoc_of_le hr₀1]
    exact (intervalIntegrable_eulerTail q.1 hr₀0 hr₀1 hq.2.2.2.1 hq.2.2.2.2).1.aestronglyMeasurable
  set C : ℝ := max M₀ M₁ + max M₀ M₁ * (δ⁻¹ * ‖eulerTailExpCLM‖)
  have hbound_int : IntervalIntegrable (fun u : ℝ => C * (1 - u) ^ (δ - 1)) volume r₀ 1 :=
    IntervalIntegrable.const_mul (by simpa only [sub_sub_cancel, sub_zero] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 1 - r₀) (b := 0)
        (by linarith : -1 < δ - 1)).comp_sub_left 1) C
  have hae : ∀ᵐ u : ℝ ∂volume, u ∈ Ι r₀ 1 → ∀ q ∈ s,
      HasFDerivAt (fun x => eulerTailIntegrand x u) (eulerTailFDeriv q u) q ∧
        ‖eulerTailFDeriv q u‖ ≤ C * (1 - u) ^ (δ - 1) := by
    filter_upwards [(by simp [ae_iff] : ∀ᵐ u : ℝ ∂volume, u ≠ 1)] with u hu1 hu q hq
    rw [uIoc_of_le hr₀1] at hu
    exact hasFDerivAt_and_norm_eulerTailIntegrand (hr₀0.le.trans hu.1.le)
      (lt_of_le_of_ne hu.2 hu1) hδ (hq.1 _ ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩).1
      ((hq.1 _ ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩).2.trans (le_max_left _ _))
      ((hq.2.1 _ ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩).2.trans (le_max_right _ _)) hq.2.2.1.le
  exact (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (eventually_of_mem hs hmeas_F) (intervalIntegrable_eulerTail p₀.1 hr₀0 hr₀1 hp₀.1 hp₀.2)
    (aestronglyMeasurable_eulerTailFDeriv hr₀0 hr₀1 hp₀.2)
    (hae.mono fun u hu hmem q hq => (hu hmem q hq).2) hbound_int
    (hae.mono fun u hu hmem q hq => (hu hmem q hq).1)).differentiableAt.differentiableWithinAt

/-- **Joint holomorphy of the `(0+)` hypergeometric loop.** For `0 < ρ < 1`, the function
`(a, b, c, z) ↦ hypergeometricHalfLineLoop a b c z ρ` is jointly holomorphic on
`{p | b.re < c.re ∧ 1 - z ∈ slitPlane ∧ ‖1 - z‖ * ρ < 1}`. -/
theorem analyticOnNhd_hypergeometricHalfLineLoop {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ =>
      hypergeometricHalfLineLoop p.1 p.2.1 p.2.2.1 p.2.2.2 ρ)
      {p | p.2.1.re < p.2.2.1.re ∧ 1 - p.2.2.2 ∈ slitPlane ∧ ‖1 - p.2.2.2‖ * ρ < 1} := by
  intro p hp
  have hr₀0 : 0 < ρ / (ρ + 1) := div_pos hρ₀ (by linarith)
  have hr₀1 : ρ / (ρ + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hfactor : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => cexp (2 * π * I * q.2.1) - 1) p :=
    (analyticAt_const.mul (analyticAt_fst.comp analyticAt_snd)).cexp.sub analyticAt_const
  have hray := analyticOnNhd_integral_eulerTail hr₀0 hr₀1 p ⟨hp.1, hp.2.1⟩
  have hcirc := analyticOnNhd_integral_halfLineCircle hρ₀ hρ₁ p hp.2.2
  refine ((hfactor.mul hray).add hcirc).congr (Eventually.of_forall fun q => ?_)
  symm
  dsimp only [Pi.add_apply, Pi.mul_apply]
  rw [hypergeometricHalfLineLoop_eq_ray_add_circle,
    ← integral_halfLineRayIntegrand_Ioi_eq q.1 q.2.1 q.2.2.1 q.2.2.2 (by linarith : -1 < ρ)]

/-! ### Loop collapse and DLMF 15.6.3 -/

/-- Compactness of `closedBall 1 (1 / 2) ⊆ slitPlane` yields a constant `K` bounding the circle
integral by `K * r ^ b.re` for all sufficiently small `r > 0`. -/
private lemma exists_norm_integral_halfLineCircle_le (a b c z : ℂ) :
    ∃ K : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖∫ θ : ℝ in (0 : ℝ)..(2 * π), halfLineCircleIntegrand a b c z r θ‖ ≤ K * r ^ b.re := by
  have hpow_bdd (s : ℂ) : ∃ C : ℝ, ∀ w ∈ closedBall (1 : ℂ) (1 / 2), ‖w ^ s‖ ≤ C :=
    (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn fun w hw =>
      (continuousAt_id.cpow continuousAt_const
        ((closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1)).trans
          ball_one_subset_slitPlane hw)).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hpow_bdd (a - c)
  obtain ⟨C₂, hC₂⟩ := hpow_bdd (-a)
  set M : ℝ := Real.exp (2 * π * ‖b - 1‖) * max 0 C₁ * max 0 C₂
  refine ⟨M * (2 * π), ?_⟩
  have hr₁ : 0 < min (1 / 2 : ℝ) ((2 * (‖1 - z‖ + 1))⁻¹) :=
    lt_min (by norm_num) (inv_pos.2 (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
  have hr0 : 0 < r := hr.1
  have hr_half : r ≤ 1 / 2 := hr.2.le.trans (min_le_left _ _)
  have hzr_half : ‖1 - z‖ * r ≤ 1 / 2 := by
    have hpos : 0 < 2 * (‖1 - z‖ + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hr.2.le.trans (min_le_right _ _)) hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at hmul
    nlinarith [norm_nonneg (1 - z)]
  have hpoint (θ : ℝ) (hθ : θ ∈ uIoc (0 : ℝ) (2 * π)) :
      ‖halfLineCircleIntegrand a b c z r θ‖ ≤ M * r ^ b.re := by
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    have hnorm_rc : ‖(r : ℂ) * cexp (θ * I)‖ = r := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hr0.le, norm_exp_ofReal_mul_I, mul_one]
    have hw1 : (r : ℂ) * cexp (θ * I) + 1 ∈ closedBall (1 : ℂ) (1 / 2) := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, hnorm_rc]; exact hr_half
    have hw2 : (1 - z) * ((r : ℂ) * cexp (θ * I)) + 1 ∈ closedBall (1 : ℂ) (1 / 2) := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_mul, hnorm_rc]; exact hzr_half
    have hexp_le : ‖cexp (θ * I * (b - 1))‖ ≤ Real.exp (2 * π * ‖b - 1‖) := by
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
      rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hθ.1.le, norm_I, mul_one]
      exact mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
    have hr_pow : ‖(r : ℂ) ^ (b - 1)‖ * ‖I * (r : ℂ) * cexp (θ * I)‖ = r ^ b.re := by
      rw [norm_cpow_eq_rpow_re_of_pos hr0, sub_re, one_re, mul_assoc I, norm_mul, norm_I,
        one_mul, hnorm_rc, ← Real.rpow_add_one hr0.ne', sub_add_cancel]
    have hnorm_eq : ‖halfLineCircleIntegrand a b c z r θ‖ =
        (‖cexp (θ * I * (b - 1))‖ * ‖((r : ℂ) * cexp (θ * I) + 1) ^ (a - c)‖ *
          ‖((1 - z) * ((r : ℂ) * cexp (θ * I)) + 1) ^ (-a)‖) * r ^ b.re := by
      rw [halfLineCircleIntegrand, norm_mul, norm_mul, norm_mul, norm_mul, ← hr_pow]; ring
    rw [hnorm_eq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul hexp_le ((hC₁ _ hw1).trans (le_max_right 0 C₁))
        (norm_nonneg _) (by positivity))
        ((hC₂ _ hw2).trans (le_max_right 0 C₂)) (norm_nonneg _) (by positivity))
      (Real.rpow_nonneg hr0.le _)
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans_eq
    (by rw [sub_zero, abs_of_pos Real.two_pi_pos]; ring)

/-- When `0 < b.re`, the circle contribution around `0` tends to `0` as `r → 0⁺`. -/
private lemma tendsto_integral_halfLineCircle_zero (a : ℂ) {b : ℂ} (c z : ℂ) (hb : 0 < b.re) :
    Tendsto (fun r : ℝ => ∫ θ : ℝ in (0 : ℝ)..(2 * π), halfLineCircleIntegrand a b c z r θ)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_norm_integral_halfLineCircle_le a b c z
  have h0 : Tendsto (fun r : ℝ => r ^ b.re) (𝓝[>] 0) (𝓝 (0 ^ b.re)) :=
    (Real.continuousAt_rpow_const 0 b.re (Or.inr hb.le)).tendsto.mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow hb.ne'] at h0
  exact squeeze_zero_norm' hK (by simpa only [mul_zero] using h0.const_mul K)

/-- At radius `ρ = 0`, the circle piece vanishes identically and the positive half-line `Ioi 0`
maps via `t = u / (1 - u)` onto `(0, 1)`. -/
private lemma hypergeometricHalfLineLoop_zero_radius (a b c z : ℂ) :
    hypergeometricHalfLineLoop a b c z 0 =
      (cexp (2 * π * I * b) - 1) *
        ∫ t : ℝ in (0 : ℝ)..1,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
  rw [hypergeometricHalfLineLoop_eq_ray_add_circle]
  have hcirc : (∫ θ : ℝ in (0 : ℝ)..(2 * π), halfLineCircleIntegrand a b c z 0 θ) = 0 := by
    simp [halfLineCircleIntegrand]
  have hray := integral_halfLineRayIntegrand_Ioi_eq a b c z (by norm_num : (-1 : ℝ) < 0)
  rw [zero_div] at hray
  dsimp only [halfLineRayIntegrand, halfLineCircleIntegrand] at hray hcirc
  rw [hray, hcirc, add_zero]

/-- Euler's reflection identity in monodromy form: away from the nonpositive integer poles of `Γ`,
`(exp (2πib) - 1) Γ(b) = 2πi exp(bπi) / Γ(1 - b)`, including at positive integers `b = n + 1`
where both sides vanish. -/
private lemma exp_two_pi_I_sub_one_mul_Gamma {b : ℂ} (hb : ∀ n : ℕ, b ≠ -n) :
    (cexp (2 * π * I * b) - 1) * Gamma b = 2 * π * I * cexp (b * π * I) / Gamma (1 - b) := by
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hsin : cexp (2 * π * I * b) - 1 = cexp (b * π * I) * (2 * I * Complex.sin (π * b)) := by
    rw [Complex.sin]
    have h1 : cexp (-(π * b) * I) = (cexp (b * π * I))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; ring
    have h2 : cexp (π * b * I) = cexp (b * π * I) := by congr 1; ring
    have h3 : cexp (2 * π * I * b) = cexp (b * π * I) * cexp (b * π * I) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [h1, h2, h3]
    have hne : cexp (b * π * I) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hne]
    rw [I_sq]
    ring
  have hrefl := Gamma_mul_Gamma_one_sub b
  rw [hsin]
  by_cases hs : Complex.sin (π * b) = 0
  · rw [hs, div_zero] at hrefl
    have hΓ1b : Gamma (1 - b) = 0 := (mul_eq_zero.1 hrefl).resolve_left hΓb
    simp [hs, hΓ1b]
  · have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hΓ1b : Gamma (1 - b) ≠ 0 := fun h => by
      rw [h, mul_zero] at hrefl; exact div_ne_zero hπ hs hrefl.symm
    have hkey : Complex.sin (π * b) * Gamma b = π / Gamma (1 - b) := by
      rw [eq_div_iff hΓ1b, mul_assoc, hrefl, mul_div_cancel₀ _ hs]
    calc cexp (b * π * I) * (2 * I * Complex.sin (π * b)) * Gamma b
        = 2 * I * cexp (b * π * I) * (Complex.sin (π * b) * Gamma b) := by ring
      _ = 2 * I * cexp (b * π * I) * (π / Gamma (1 - b)) := by rw [hkey]
      _ = 2 * π * I * cexp (b * π * I) / Gamma (1 - b) := by ring

/-- In Euler's convergence region `0 < b.re < c.re`, shrinking the circle around `0` collapses
`hypergeometricHalfLineLoop` across `0 ≤ ρ < 1` to `(cexp (2 * π * I * b) - 1)` times the
unnormalized Euler integral on `[0, 1]`. -/
theorem hypergeometricHalfLineLoop_eq_integral_eulerIntegrand (a : ℂ) {b c z : ℂ} {ρ : ℝ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hzρ : ‖1 - z‖ * ρ < 1) :
    hypergeometricHalfLineLoop a b c z ρ =
      (cexp (2 * π * I * b) - 1) *
        ∫ t : ℝ in (0 : ℝ)..1,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
  rcases hρ₀.eq_or_lt with rfl | hρ₀
  · exact hypergeometricHalfLineLoop_zero_radius a b c z
  let eulerInt : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)
  have hint := intervalIntegrable_eulerIntegrand a hb hbc hz
  have hprim : ContinuousOn (fun x : ℝ => ∫ u : ℝ in x..1, eulerInt u) (Icc 0 1) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval' hint.symm left_mem_uIcc).neg
    rw [uIcc_of_ge zero_le_one] at hc
    exact hc.congr fun x _ => intervalIntegral.integral_symm 1 x
  have hchart_tendsto : Tendsto (fun r : ℝ => r / (r + 1)) (𝓝[>] 0) (𝓝[Icc 0 1] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : ContinuousAt (fun r : ℝ => r / (r + 1)) 0 :=
        continuousAt_id.div (continuousAt_id.add continuousAt_const) (by norm_num)
      simpa using h0.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact ⟨div_nonneg hr.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  have hray_lim : Tendsto (fun r : ℝ => ∫ u : ℝ in (r / (r + 1))..1, eulerInt u)
      (𝓝[>] 0) (𝓝 (∫ u : ℝ in (0 : ℝ)..1, eulerInt u)) :=
    (hprim 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp hchart_tendsto
  have hrhs : Tendsto (fun r : ℝ =>
      (cexp (2 * π * I * b) - 1) * (∫ u : ℝ in (r / (r + 1))..1, eulerInt u) +
        ∫ θ : ℝ in (0 : ℝ)..(2 * π), halfLineCircleIntegrand a b c z r θ)
      (𝓝[>] 0) (𝓝 ((cexp (2 * π * I * b) - 1) * ∫ u : ℝ in (0 : ℝ)..1, eulerInt u)) := by
    simpa only [add_zero] using (hray_lim.const_mul _).add
      (tendsto_integral_halfLineCircle_zero a c z hb)
  have hlhs : Tendsto (fun r : ℝ =>
      (cexp (2 * π * I * b) - 1) * (∫ u : ℝ in (r / (r + 1))..1, eulerInt u) +
        ∫ θ : ℝ in (0 : ℝ)..(2 * π), halfLineCircleIntegrand a b c z r θ)
      (𝓝[>] 0) (𝓝 (hypergeometricHalfLineLoop a b c z ρ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hρ₀] with r hr
    have hzr : ‖1 - z‖ * r < 1 :=
      (mul_le_mul_of_nonneg_left hr.2.le (norm_nonneg _)).trans_lt hzρ
    rw [hypergeometricHalfLineLoop_eq a hbc hz hρ₀ hρ₁ hzρ hr.1 (hr.2.trans hρ₁) hzr,
      hypergeometricHalfLineLoop_eq_ray_add_circle,
      ← integral_halfLineRayIntegrand_Ioi_eq a b c z (by linarith [hr.1] : -1 < r)]
  exact tendsto_nhds_unique hlhs hrhs

/-- In Euler's convergence region `0 < b.re < c.re`, the `(0+)` loop integral across `0 ≤ ρ < 1`
equals `2πi exp(bπi) Γ(c - b) / Γ(1 - b)` times `eulerIntegral a b c z`, including at positive
integers `b = n + 1` where both sides vanish. -/
theorem hypergeometricHalfLineLoop_eq_eulerIntegral (a : ℂ) {b c z : ℂ} {ρ : ℝ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hzρ : ‖1 - z‖ * ρ < 1) :
    hypergeometricHalfLineLoop a b c z ρ =
      2 * π * I * cexp (b * π * I) * Gamma (c - b) / Gamma (1 - b) * eulerIntegral a b c z := by
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.2 hbc)
  have heuler : (∫ t : ℝ in (0 : ℝ)..1,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
        Gamma b * Gamma (c - b) * eulerIntegral a b c z := by
    symm
    rw [eulerIntegral_def, mul_inv_cancel_left₀ (mul_ne_zero hΓb hΓcb)]
  rw [hypergeometricHalfLineLoop_eq_integral_eulerIntegrand a hb hbc hz hρ₀ hρ₁ hzρ, heuler,
    ← mul_assoc, ← mul_assoc, exp_two_pi_I_sub_one_mul_Gamma (ne_neg_natCast_of_re_pos hb)]
  ring

/-- **DLMF 15.6.3** in Euler's convergence region: for `0 < b.re < c.re` with `b ∉ {1, 2, 3, …}`,
`1 - z ∈ Complex.slitPlane`, `0 ≤ ρ < 1`, and `‖1 - z‖ * ρ < 1`, the normalized Euler integral is
recovered from `hypergeometricHalfLineLoop` by the prefactor
`exp(-bπi) Γ(1 - b) / (2πi Γ(c - b))`. -/
theorem eulerIntegral_eq_hypergeometricHalfLineLoop (a : ℂ) {b c z : ℂ} {ρ : ℝ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hb_ne : ∀ n : ℕ, b ≠ n + 1) (hz : 1 - z ∈ slitPlane)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hzρ : ‖1 - z‖ * ρ < 1) :
    eulerIntegral a b c z =
      cexp (-(b * π * I)) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricHalfLineLoop a b c z ρ := by
  have hΓ1b : Gamma (1 - b) ≠ 0 :=
    Gamma_ne_zero fun n hn => hb_ne n (by linear_combination -hn)
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.2 hbc)
  have h2πI : (2 : ℂ) * π * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero
  rw [hypergeometricHalfLineLoop_eq_eulerIntegral a hb hbc hz hρ₀ hρ₁ hzρ, Complex.exp_neg]
  field_simp [hΓ1b, hΓcb, h2πI, Complex.exp_ne_zero (b * π * I)]

/-! ### Closed-form special values across the continued parameter half-spaces -/

/-- With `a = 0`, the argument `z` drops out of `hypergeometricHalfLineLoop` at all parameters and
radii. -/
theorem hypergeometricHalfLineLoop_zero_left_eq (b c z : ℂ) (ρ : ℝ) :
    hypergeometricHalfLineLoop 0 b c z ρ = hypergeometricHalfLineLoop 0 b c 0 ρ := by
  simp only [hypergeometricHalfLineLoop_def, neg_zero, cpow_zero]

/-- At `z = 1`, the `(1 - z) t + 1` factor equals `1`, reducing `hypergeometricHalfLineLoop` to the
`a = 0`, `z = 0` loop with shifted lower parameter `c - a`. -/
theorem hypergeometricHalfLineLoop_one_eq (a b c : ℂ) (ρ : ℝ) :
    hypergeometricHalfLineLoop a b c 1 ρ = hypergeometricHalfLineLoop 0 b (c - a) 0 ρ := by
  simp only [hypergeometricHalfLineLoop_def, sub_self, zero_mul, zero_add, one_cpow,
    zero_sub, neg_sub, neg_zero, cpow_zero]

/-- At `z = 0`, `hypergeometricHalfLineLoop a b c 0 ρ` evaluates in closed form across the entire
continued half-space `b.re < c.re` (including `b.re ≤ 0` and `c.re ≤ 0`). -/
@[simp]
theorem hypergeometricHalfLineLoop_zero (a : ℂ) {b c : ℂ} {ρ : ℝ}
    (hbc : b.re < c.re) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    hypergeometricHalfLineLoop a b c 0 ρ =
      2 * π * I * cexp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  let U : Set (ℂ × ℂ) := {q | q.1.re < q.2.re}
  have hU_open : IsOpen U :=
    isOpen_lt (continuous_re.comp continuous_fst) (continuous_re.comp continuous_snd)
  have hU_preconn : IsPreconnected U := by
    refine (?_ : Convex ℝ U).isPreconnected
    intro x (hx : x.1.re < x.2.re) y (hy : y.1.re < y.2.re) u v hu hv huv
    rw [mem_ofPred]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      add_re, real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le hu with rfl | hu'
    · obtain rfl : v = 1 := by linarith
      linarith
    · nlinarith [mul_lt_mul_of_pos_left hx hu', mul_le_mul_of_nonneg_left hy.le hv]
  let f : ℂ × ℂ → ℂ := fun q => hypergeometricHalfLineLoop a q.1 q.2 0 ρ
  let g : ℂ × ℂ → ℂ := fun q =>
    2 * π * I * cexp (q.1 * π * I) * Gamma (q.2 - q.1) * (Gamma (1 - q.1))⁻¹ * (Gamma q.2)⁻¹
  have hf : AnalyticOnNhd ℂ f U := fun q hq => by
    have hemb : AnalyticAt ℂ (fun x : ℂ × ℂ => (a, (x.1, (x.2, (0 : ℂ))))) q :=
      (analyticAt_const (v := a)).prod
        (analyticAt_fst.prod (analyticAt_snd.prod (analyticAt_const (v := (0 : ℂ)))))
    exact (AnalyticAt.comp_of_eq (analyticOnNhd_hypergeometricHalfLineLoop hρ₀ hρ₁ (a, q.1, q.2, 0)
      ⟨hq, by simp [one_mem_slitPlane], by simpa using hρ₁⟩) hemb rfl).congr
      (Eventually.of_forall fun _ => rfl)
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd_of_finiteDimensional (fun q hq => ?_) hU_open
    have hΓcb := DifferentiableAt.fun_comp' q (differentiableAt_Gamma (q.2 - q.1)
      (ne_neg_natCast_of_re_pos (by simpa using sub_pos.2 hq)))
      (differentiableAt_snd.sub differentiableAt_fst)
    have hΓ1b := DifferentiableAt.fun_comp' (g := fun s : ℂ => (Gamma s)⁻¹) q
      (differentiable_one_div_Gamma (1 - q.1)) (differentiableAt_fst.const_sub (1 : ℂ))
    have hΓc := DifferentiableAt.fun_comp' (g := fun s : ℂ => (Gamma s)⁻¹) q
      (differentiable_one_div_Gamma q.2) differentiableAt_snd
    exact (((((differentiableAt_fst.mul_const (π * I)).cexp.const_mul (2 * π * I)).mul
      hΓcb).mul hΓ1b).mul hΓc).differentiableWithinAt.congr
      (fun x _ => by dsimp [g]; rw [mul_assoc x.1 π I])
      (by dsimp [g]; rw [mul_assoc q.1 π I])
  have hev : f =ᶠ[𝓝 ((1 / 2 : ℂ), (1 : ℂ))] g := by
    filter_upwards [((isOpen_lt (continuous_const (y := (0 : ℝ)))
      (continuous_re.comp continuous_fst)).inter hU_open).mem_nhds (by simp [U]; norm_num)]
      with q hq
    dsimp only [f, g]
    rw [hypergeometricHalfLineLoop_eq_eulerIntegral a hq.1 hq.2 (by simp [one_mem_slitPlane])
      hρ₀.le hρ₁ (by simpa using hρ₁), eulerIntegral_zero a hq.1 hq.2, div_eq_mul_inv]
  have heq : f (b, c) = g (b, c) := hf.eqOn_of_preconnected_of_eventuallyEq hg hU_preconn
    (by simp [U]; norm_num) hev hbc
  dsimp only [f, g] at heq
  rw [heq, div_eq_mul_inv, mul_inv]
  ring

/-- At `a = 0`, `hypergeometricHalfLineLoop 0 b c z ρ` evaluates in closed form across the entire
continued half-space `b.re < c.re`, for every complex argument `z` (including on `[1, ∞)`). -/
@[simp]
theorem hypergeometricHalfLineLoop_zero_left {b c : ℂ} (z : ℂ) {ρ : ℝ}
    (hbc : b.re < c.re) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    hypergeometricHalfLineLoop 0 b c z ρ =
      2 * π * I * cexp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  rw [hypergeometricHalfLineLoop_zero_left_eq, hypergeometricHalfLineLoop_zero 0 hbc hρ₀ hρ₁]

/-- At unit argument `z = 1`, `hypergeometricHalfLineLoop a b c 1 ρ` evaluates in closed form
across Gauss's convergence half-space `b.re < c.re - a.re`. -/
@[simp]
theorem hypergeometricHalfLineLoop_one {a b c : ℂ} {ρ : ℝ}
    (hc : b.re < c.re - a.re) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    hypergeometricHalfLineLoop a b c 1 ρ =
      2 * π * I * cexp (b * π * I) * Gamma (c - a - b) / (Gamma (1 - b) * Gamma (c - a)) := by
  rw [hypergeometricHalfLineLoop_one_eq,
    hypergeometricHalfLineLoop_zero 0 (by simpa only [sub_re] using hc) hρ₀ hρ₁]

end Complex
