/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Closed forms for the real Gaussian density

Mathlib's `ProbabilityTheory.gaussianPDFReal μ v` is stated for a general mean `μ` and variance `v`.
This file records the specialization at the standard parameters `μ = 0`, `v = 1`, where the shift
and the variance both disappear and the density collapses to `(√(2π))⁻¹ · e^{-x²/2}`.

That closed form is what any calculation against the standard Gaussian weight rewrites by, and it
is a statement about the Gaussian distribution alone: it mentions no orthogonal family, so it
belongs here rather than in any of the families that consume it (the Hermite orthogonality
relation and the Gaussian Hermite basis both do).

The file also extends the density to extended real points, by its limit `0` at `±∞`, and
differentiates it in the mean, for formulas over intervals whose bounds may be infinite. It also
differentiates the density in its real argument and turns integrability against `gaussianReal μ v`
into Lebesgue integrability of the density-weighted function, the inputs to Gaussian integration
by parts.

## Main statements

* `TauCeti.Probability.gaussianPDFReal_zero_one` — `gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`.
* `TauCeti.Probability.gaussianPDFReal_eq_gaussianPDFReal_zero_one` — standardization:
  `gaussianPDFReal m v x = φ ((x - m) / √v) / √v` with `φ = gaussianPDFReal 0 1`.
* `TauCeti.Probability.gaussianPDFReal_neg` and `TauCeti.Probability.gaussianPDFReal_zero_neg` —
  reflection `gaussianPDFReal m v (-x) = gaussianPDFReal (-m) v x` and evenness at zero mean.
* `TauCeti.Probability.antitoneOn_gaussianPDFReal` — the density decreases to the right of the
  mean.
* `TauCeti.Probability.gaussianPDFReal_self`, `TauCeti.Probability.gaussianPDFReal_le_self`,
  `TauCeti.Probability.gaussianPDFReal_le`, and `TauCeti.Probability.gaussianPDF_le` — the density
  attains its global maximum `(√(2 * π * v))⁻¹` at the mean (with both sides vanishing when
  `v = 0`).
* `TauCeti.Probability.tendsto_mul_gaussianPDFReal_zero_one_cocompact` — `x φ(x) → 0` as
  `|x| → ∞`, for the standard Gaussian density `φ`.
* `TauCeti.Probability.hasDerivAt_gaussianPDFReal` — the derivative of the Gaussian density in
  its real argument is `-(x - μ) / v` times the density, for every variance.
* `TauCeti.Probability.integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul` — at positive
  variance, integrability against `gaussianReal μ v` is equivalent to Lebesgue integrability of
  the function weighted by the density.
* `TauCeti.Probability.hasDerivAt_gaussianPDFRealEReal` — as a function of the mean `μ`, the
  density at an extended point `e` has derivative `(e - μ) / v` times the density.
* `TauCeti.Probability.gaussianPDFReal_mul_gaussianPDFReal` — pointwise product of two Gaussian
  densities as a scaled Gaussian density (completion of the square), for all variances `v₁, v₂`.
* `TauCeti.Probability.sqrt_gaussianPDFReal` — square root of a Gaussian density as a scaled
  Gaussian density with doubled variance, for all variances `v`.
* `TauCeti.Probability.sqrt_gaussianPDFReal_mul_gaussianPDFReal` — geometric mean of two Gaussian
  densities as a scaled Gaussian density, for all variances `v₁, v₂`.

## Main definitions

* `TauCeti.Probability.gaussianPDFRealEReal` — the Gaussian density at an extended real point,
  set to `0`, its limit, at `±∞`. Formulas for intervals with extended bounds, such as the
  moments of a truncated normal law, evaluate the density at the bounds through it.
-/

public section

namespace TauCeti.Probability

open Filter ProbabilityTheory Real
open scoped Topology NNReal

/-- The probability-density form of the standard Gaussian weight:
`gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) from by ring]

/-- Standardization of the Gaussian density: the density of `N(m, v)` at `x` is
`φ ((x - m) / √v) / √v`, where `φ = gaussianPDFReal 0 1` is the standard Gaussian density. At zero
variance both sides vanish. -/
theorem gaussianPDFReal_eq_gaussianPDFReal_zero_one (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x = gaussianPDFReal 0 1 ((x - m) / √(v : ℝ)) / √(v : ℝ) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, div_pow, Real.sq_sqrt hv'.le,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
  field_simp

/-- Negating the argument of `gaussianPDFReal` negates the mean parameter. -/
theorem gaussianPDFReal_neg (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v (-x) = gaussianPDFReal (-m) v x := by
  simp only [gaussianPDFReal, show -(-x - m) ^ 2 = -(x - -m) ^ 2 by ring]

/-- Any centered Gaussian density is an even function. -/
theorem gaussianPDFReal_zero_neg (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v (-x) = gaussianPDFReal 0 v x := by
  rw [gaussianPDFReal_neg, neg_zero]

/-- The Gaussian density of `N(m, v)` decreases to the right of its mean. -/
theorem antitoneOn_gaussianPDFReal (m : ℝ) (v : ℝ≥0) :
    AntitoneOn (gaussianPDFReal m v) (Set.Ici m) := fun x hx y _ hxy => by
  have hx : 0 ≤ x - m := sub_nonneg.2 hx
  simp only [gaussianPDFReal]
  gcongr

/-- At its mean `μ`, the Gaussian density equals `(√(2 * π * v))⁻¹` (and `0` when `v = 0`). -/
@[simp]
theorem gaussianPDFReal_self (μ : ℝ) (v : ℝ≥0) :
    gaussianPDFReal μ v μ = (√(2 * π * (v : ℝ)))⁻¹ := by
  simp [gaussianPDFReal]

/-- The Gaussian density of `N(μ, v)` attains its global maximum at the mean `μ`. -/
theorem gaussianPDFReal_le_self (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ gaussianPDFReal μ v μ := by
  rw [gaussianPDFReal_self, gaussianPDFReal]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- Uniform upper bound on the Gaussian density: `gaussianPDFReal μ v x ≤ (√(2 * π * v))⁻¹` for
every variance `v`, including `v = 0` where both sides vanish. -/
theorem gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (√(2 * π * (v : ℝ)))⁻¹ :=
  gaussianPDFReal_self μ v ▸ gaussianPDFReal_le_self μ v x

/-- Uniform upper bound on the `ℝ≥0∞`-valued Gaussian density `gaussianPDF`, valid at every
variance `v` (including `v = 0`, where both sides vanish). -/
theorem gaussianPDF_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDF μ v x ≤ ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ :=
  ENNReal.ofReal_le_ofReal (gaussianPDFReal_le μ v x)

/-- The standard Gaussian density decays faster than `1 / |x|`: `x φ(x) → 0` as `|x| → ∞`. -/
theorem tendsto_mul_gaussianPDFReal_zero_one_cocompact :
    Tendsto (fun x => x * gaussianPDFReal 0 1 x) (cocompact ℝ) (𝓝 0) := by
  have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1 / 2) one_half_pos 1).const_mul
    (√(2 * π))⁻¹
  rw [mul_zero] at h
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h.congr fun x => ?_)
  simp only [gaussianPDFReal_zero_one, rpow_one, norm_mul, norm_eq_abs, abs_exp,
    abs_of_pos (inv_pos.2 (sqrt_pos.2 (by positivity : (0 : ℝ) < 2 * π)))]
  ring_nf

/-- The derivative of the Gaussian density in its real argument is `-(x - μ) / v` times the
density. At zero variance both sides vanish. -/
theorem hasDerivAt_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-(x - μ) / (v : ℝ) * gaussianPDFReal μ v x) x := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  rw [gaussianPDFReal_def]
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hq :
      HasDerivAt (fun x : ℝ => -(x - μ) ^ 2 / (2 * (v : ℝ)))
        (-(x - μ) / (v : ℝ)) x := by
    convert ((((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))) using 1
    · ext y
      simp only [id_eq, Pi.neg_apply, Pi.pow_apply]
    · simp only [id_eq]
      field_simp [hv']
      ring_nf
  convert hq.exp.const_mul (Real.sqrt (2 * π * (v : ℝ)))⁻¹ using 1
  · ring_nf

/-- At positive variance, a function is integrable against `gaussianReal μ v` if and only if its
product with the Gaussian density is Lebesgue integrable. -/
theorem integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → E} :
    MeasureTheory.Integrable g (gaussianReal μ v) ↔
      MeasureTheory.Integrable (fun x => gaussianPDFReal μ v x • g x) := by
  rw [gaussianReal_of_var_ne_zero μ hv,
    MeasureTheory.integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (MeasureTheory.ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]

/-! ### The Gaussian density at an extended point -/

/-- The Gaussian density of `N(m, v)` at an extended real point: `gaussianPDFReal m v x` at a
real point `x`, and `0`, the limit of the density, at `⊥` and `⊤`. -/
noncomputable def gaussianPDFRealEReal (m : ℝ) (v : ℝ≥0) : EReal → ℝ :=
  EReal.rec 0 (gaussianPDFReal m v) 0

/-- At a real point, `gaussianPDFRealEReal` is the Gaussian density. -/
@[simp]
theorem gaussianPDFRealEReal_coe (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFRealEReal m v x = gaussianPDFReal m v x := (rfl)

/-- At `⊥`, `gaussianPDFRealEReal` vanishes. -/
@[simp]
theorem gaussianPDFRealEReal_bot (m : ℝ) (v : ℝ≥0) : gaussianPDFRealEReal m v ⊥ = 0 := (rfl)

/-- At `⊤`, `gaussianPDFRealEReal` vanishes. -/
@[simp]
theorem gaussianPDFRealEReal_top (m : ℝ) (v : ℝ≥0) : gaussianPDFRealEReal m v ⊤ = 0 := (rfl)

/-- The Gaussian density at an extended real point is nonnegative. -/
theorem gaussianPDFRealEReal_nonneg (m : ℝ) (v : ℝ≥0) (e : EReal) :
    0 ≤ gaussianPDFRealEReal m v e := by
  induction e <;> simp [gaussianPDFReal_nonneg]

/-- The Gaussian density at an extended point `e`, as a function of the mean `μ`, has derivative
`(e - μ) / v` times the density; both vanish at an infinite point and at zero variance. -/
theorem hasDerivAt_gaussianPDFRealEReal (v : ℝ≥0) (e : EReal) (μ : ℝ) :
    HasDerivAt (fun μ => gaussianPDFRealEReal μ v e)
      ((e.toReal - μ) * gaussianPDFRealEReal μ v e / v) μ := by
  rcases eq_or_ne v 0 with rfl | hv
  · induction e <;> simpa [gaussianPDFReal_zero_var] using hasDerivAt_const μ (0 : ℝ)
  induction e with
  | bot => simpa using hasDerivAt_const μ (0 : ℝ)
  | top => simpa using hasDerivAt_const μ (0 : ℝ)
  | coe x =>
    simp only [gaussianPDFRealEReal_coe, EReal.toReal_coe]
    have hshift (m : ℝ) : gaussianPDFReal m v x = gaussianPDFReal 0 v (x - m) := by
      simpa only [zero_add] using (gaussianPDFReal_sub (μ := 0) (v := v) x m).symm
    rw [hshift μ, funext hshift]
    convert (hasDerivAt_gaussianPDFReal 0 v (x - μ)).comp μ
      ((hasDerivAt_id μ).const_sub x) using 1
    · simp only [Function.comp_def]
    · field_simp
      ring

/-! ### Products and square roots of Gaussian densities -/

/-- Pointwise completion of the square for the product of two univariate Gaussian densities:
`gaussianPDFReal a v₁ x * gaussianPDFReal b v₂ x` equals `gaussianPDFReal b (v₁ + v₂) a` times the
Gaussian density with precision-weighted mean `(v₂ * a + v₁ * b) / (v₁ + v₂)` and variance
`v₁ * v₂ / (v₁ + v₂)`. Holds unconditionally for all `v₁, v₂ : ℝ≥0`. -/
theorem gaussianPDFReal_mul_gaussianPDFReal (a b : ℝ) (v₁ v₂ : ℝ≥0) (x : ℝ) :
    gaussianPDFReal a v₁ x * gaussianPDFReal b v₂ x =
      gaussianPDFReal b (v₁ + v₂) a *
        gaussianPDFReal (((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂))
          (v₁ * v₂ / (v₁ + v₂)) x := by
  by_cases hv₁ : v₁ = 0
  · simp [hv₁]
  by_cases hv₂ : v₂ = 0
  · simp [hv₂]
  have : (0 : ℝ) < v₁ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₁)
  have : (0 : ℝ) < v₂ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₂)
  set w : ℝ≥0 := v₁ * v₂ / (v₁ + v₂)
  set m : ℝ := ((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂)
  have hw_coe : (w : ℝ) = (v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂) := by simp [w]
  have hpref : (√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹ =
      (√(2 * π * ((v₁ : ℝ) + v₂)))⁻¹ * (√(2 * π * w))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 2; rw [hw_coe]; field_simp
  have hexp : exp (-(x - a) ^ 2 / (2 * v₁)) * exp (-(x - b) ^ 2 / (2 * v₂)) =
      exp (-(a - b) ^ 2 / (2 * ((v₁ : ℝ) + v₂))) * exp (-(x - m) ^ 2 / (2 * w)) := by
    rw [← exp_add, ← exp_add]
    congr 1; rw [hw_coe]; simp only [m]; field_simp; ring
  simp only [gaussianPDFReal, NNReal.coe_add]
  calc ((√(2 * π * v₁))⁻¹ * exp (-(x - a) ^ 2 / (2 * v₁))) *
        ((√(2 * π * v₂))⁻¹ * exp (-(x - b) ^ 2 / (2 * v₂)))
      = ((√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹) *
          (exp (-(x - a) ^ 2 / (2 * v₁)) * exp (-(x - b) ^ 2 / (2 * v₂))) := by ring
    _ = ((√(2 * π * ((v₁ : ℝ) + v₂)))⁻¹ * (√(2 * π * w))⁻¹) *
          (exp (-(a - b) ^ 2 / (2 * ((v₁ : ℝ) + v₂))) * exp (-(x - m) ^ 2 / (2 * w))) := by
        rw [hpref, hexp]
    _ = ((√(2 * π * ((v₁ : ℝ) + v₂)))⁻¹ * exp (-(a - b) ^ 2 / (2 * ((v₁ : ℝ) + v₂)))) *
          ((√(2 * π * w))⁻¹ * exp (-(x - m) ^ 2 / (2 * w))) := by ring

/-- The square root of a univariate Gaussian density is a constant multiple of the Gaussian density
with doubled variance. Holds unconditionally for all `v : ℝ≥0`. -/
theorem sqrt_gaussianPDFReal (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    √(gaussianPDFReal m v x) =
      √(2 * √(2 * π * (v : ℝ))) * gaussianPDFReal m (2 * v) x := by
  by_cases hv : v = 0
  · simp [hv]
  have : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  simp only [gaussianPDFReal, NNReal.coe_mul, NNReal.coe_ofNat]
  rw [Real.sqrt_mul (by positivity)]
  have hpref : √((√(2 * π * (v : ℝ)))⁻¹) =
      √(2 * √(2 * π * (v : ℝ))) * (√(2 * π * (2 * (v : ℝ))))⁻¹ := by
    refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), inv_pow,
      Real.sq_sqrt (by positivity)]
    have hsq : √(2 * π * (v : ℝ)) ^ 2 = 2 * π * (v : ℝ) := Real.sq_sqrt (by positivity)
    field_simp
    nlinarith [hsq]
  have hexp : √(exp (-(x - m) ^ 2 / (2 * (v : ℝ)))) =
      exp (-(x - m) ^ 2 / (2 * (2 * (v : ℝ)))) :=
    (Real.sqrt_eq_iff_mul_self_eq (exp_nonneg _) (exp_nonneg _)).2 (by
      rw [← exp_add]; congr 1; field_simp; ring)
  rw [hpref, hexp, mul_assoc]

/-- Pointwise completion of the square for the geometric mean of two univariate Gaussian densities:
`√(gaussianPDFReal a v₁ x * gaussianPDFReal b v₂ x)` is a constant multiple of the Gaussian density
with mean `(v₂ * a + v₁ * b) / (v₁ + v₂)` and variance `2 * v₁ * v₂ / (v₁ + v₂)`. Holds
unconditionally for all `v₁, v₂ : ℝ≥0`. -/
theorem sqrt_gaussianPDFReal_mul_gaussianPDFReal (a b : ℝ) (v₁ v₂ : ℝ≥0) (x : ℝ) :
    √(gaussianPDFReal a v₁ x * gaussianPDFReal b v₂ x) =
      √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) *
        exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) *
          gaussianPDFReal (((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂))
            (2 * v₁ * v₂ / (v₁ + v₂)) x := by
  by_cases hv₁ : v₁ = 0
  · simp [hv₁]
  by_cases hv₂ : v₂ = 0
  · simp [hv₂]
  have : (0 : ℝ) < v₁ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₁)
  have : (0 : ℝ) < v₂ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₂)
  set w : ℝ≥0 := v₁ * v₂ / (v₁ + v₂)
  rw [gaussianPDFReal_mul_gaussianPDFReal, Real.sqrt_mul (gaussianPDFReal_nonneg _ _ _),
    sqrt_gaussianPDFReal _ w x]
  have hvar : 2 * w = 2 * v₁ * v₂ / (v₁ + v₂) := by
    simp only [w, ← mul_div_assoc, mul_assoc]
  rw [hvar, ← mul_assoc]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_add]
  rw [Real.sqrt_mul (by positivity)]
  have hexp : √(exp (-(a - b) ^ 2 / (2 * ((v₁ : ℝ) + v₂)))) =
      exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) :=
    (Real.sqrt_eq_iff_mul_self_eq (exp_nonneg _) (exp_nonneg _)).2 (by
      rw [← exp_add]; congr 1; field_simp; ring)
  have hconst : √((√(2 * π * ((v₁ : ℝ) + v₂)))⁻¹) * √(2 * √(2 * π * (w : ℝ))) =
      √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) := by
    refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    have hw_coe : (w : ℝ) = (v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂) := by simp [w]
    rw [hw_coe]
    have hsqrt_w : √(2 * π * ((v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂))) =
        √(2 * π * ((v₁ : ℝ) + v₂)) * (√((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) := by
      refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
      rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), div_pow,
        Real.sq_sqrt (by positivity)]
      field_simp
    rw [hsqrt_w]
    field_simp
  rw [hexp, ← hconst]
  ring

end TauCeti.Probability
