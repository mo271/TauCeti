/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.InformationTheory.Hellinger.Product

import TauCeti.Probability.Distributions.Gaussian.Basic

/-!
# Hellinger affinity and distance for Gaussian distributions

Exact closed forms for the Hellinger affinity and squared Hellinger distance between univariate
Gaussian distributions, finite products of Gaussian distributions, and infinite Gaussian product
measures differing in finitely many coordinates.

For arbitrary variances `v₁, v₂ : ℝ≥0` with `v₁ + v₂ ≠ 0`,
`hellingerAffinity (gaussianReal a v₁) (gaussianReal b v₂) =`
`√(2 * √(v₁ * v₂) / (v₁ + v₂)) * Real.exp (-(a - b) ^ 2 / (4 * (v₁ + v₂)))`.
In the equal-variance case `v ≠ 0`, this simplifies to
`Real.exp (-(a - b) ^ 2 / (8 * v))`, and for infinite Gaussian product measures with equal
variance `v ≠ 0` whose means agree outside a finite set `s`,
`hellingerAffinity (Measure.infinitePi fun i ↦ gaussianReal (θ i) v)`
`  (Measure.infinitePi fun i ↦ gaussianReal (θ' i) v) =`
`Real.exp (-(∑ i ∈ s, (θ i - θ' i) ^ 2) / (8 * v))`.

## Main results

* `TauCeti.hellingerAffinity_gaussianReal_of_add_ne_zero`: Hellinger affinity of two univariate
  Gaussians with arbitrary variances `v₁ + v₂ ≠ 0`.
* `TauCeti.hellingerAffinity_gaussianReal`: equal-variance specialization
  `Real.exp (-(a - b) ^ 2 / (8 * v))`.
* `TauCeti.sqHellinger_gaussianReal`: squared Hellinger distance of equal-variance Gaussians.
* `TauCeti.hellingerAffinity_pi_gaussianReal`: Hellinger affinity of finite products of
  equal-variance Gaussians.
* `TauCeti.hellingerAffinity_infinitePi_gaussianReal`: Hellinger affinity of infinite products of
  equal-variance Gaussians whose means agree outside a finite coordinate set.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Section 2.4, p. 83.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace TauCeti

/-- **Hellinger affinity of two univariate Gaussian distributions** with arbitrary variances
`v₁, v₂ : ℝ≥0` not both zero. -/
theorem hellingerAffinity_gaussianReal_of_add_ne_zero (a b : ℝ) {v₁ v₂ : ℝ≥0}
    (hv : v₁ + v₂ ≠ 0) :
    hellingerAffinity (gaussianReal a v₁) (gaussianReal b v₂) =
      √(2 * √((v₁ : ℝ) * v₂) / (v₁ + v₂)) *
        exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) := by
  by_cases hv₁ : v₁ = 0
  · have hv₂ : v₂ ≠ 0 := by simpa [hv₁] using hv
    have : NullSingletonClass (gaussianReal b v₂) := nullSingletonClass_gaussianReal hv₂
    simp [hv₁, gaussianReal_zero_var, Measure.real_def]
  by_cases hv₂ : v₂ = 0
  · have : NullSingletonClass (gaussianReal a v₁) := nullSingletonClass_gaussianReal hv₁
    simp [hv₂, gaussianReal_zero_var, Measure.real_def]
  have : SigmaFinite (volume.withDensity (gaussianPDF a v₁)) := by
    rw [← gaussianReal_of_var_ne_zero a hv₁]; infer_instance
  have : SigmaFinite (volume.withDensity (gaussianPDF b v₂)) := by
    rw [← gaussianReal_of_var_ne_zero b hv₂]; infer_instance
  set v : ℝ≥0 := 2 * v₁ * v₂ / (v₁ + v₂)
  set m : ℝ := ((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂)
  have hv_ne : v ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hv₁) hv₂) hv
  rw [gaussianReal_of_var_ne_zero a hv₁, gaussianReal_of_var_ne_zero b hv₂,
    hellingerAffinity_withDensity volume (measurable_gaussianPDF a v₁).aemeasurable
      (measurable_gaussianPDF b v₂).aemeasurable]
  simp_rw [toReal_gaussianPDF,
    TauCeti.Probability.sqrt_gaussianPDFReal_mul_gaussianPDFReal a b v₁ v₂, integral_const_mul]
  rw [integral_gaussianPDFReal_eq_one m hv_ne, mul_one]

/-- **Hellinger affinity of two equal-variance univariate Gaussian distributions.** -/
theorem hellingerAffinity_gaussianReal (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    hellingerAffinity (gaussianReal a v) (gaussianReal b v) =
      exp (-(a - b) ^ 2 / (8 * (v : ℝ))) := by
  have hsum : v + v ≠ 0 := by simp [hv]
  rw [hellingerAffinity_gaussianReal_of_add_ne_zero a b hsum]
  have hv_pos : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  rw [Real.sqrt_mul_self hv_pos.le]
  have h1 : 2 * (v : ℝ) / ((v : ℝ) + v) = 1 := by
    field_simp; ring
  rw [h1, Real.sqrt_one, one_mul]
  congr 1; ring

/-- **Squared Hellinger distance of two equal-variance univariate Gaussian distributions.** -/
theorem sqHellinger_gaussianReal (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    sqHellinger (gaussianReal a v) (gaussianReal b v) =
      2 * (1 - exp (-(a - b) ^ 2 / (8 * (v : ℝ)))) := by
  rw [sqHellinger_def, hellingerAffinity_gaussianReal a b hv]

/-- **Hellinger affinity of finite products of equal-variance Gaussian distributions.** -/
theorem hellingerAffinity_pi_gaussianReal {ι : Type*} [Fintype ι] (θ θ' : ι → ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) :
    hellingerAffinity (Measure.pi fun i ↦ gaussianReal (θ i) v)
      (Measure.pi fun i ↦ gaussianReal (θ' i) v) =
      exp (-(∑ i, (θ i - θ' i) ^ 2) / (8 * (v : ℝ))) := by
  rw [hellingerAffinity_pi]
  simp_rw [hellingerAffinity_gaussianReal _ _ hv, ← exp_sum]
  congr 1
  simp only [neg_div, ← Finset.sum_div, Finset.sum_neg_distrib]

/-- **Hellinger affinity of infinite Gaussian product measures** whose mean vectors agree outside
a finite set `s` of coordinates. -/
theorem hellingerAffinity_infinitePi_gaussianReal {ι : Type*} (θ θ' : ι → ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) {s : Finset ι} (hθ : ∀ i ∉ s, θ i = θ' i) :
    hellingerAffinity (Measure.infinitePi fun i ↦ gaussianReal (θ i) v)
      (Measure.infinitePi fun i ↦ gaussianReal (θ' i) v) =
      exp (-(∑ i ∈ s, (θ i - θ' i) ^ 2) / (8 * (v : ℝ))) := by
  rw [hellingerAffinity_infinitePi (s := s) _ _ (fun i hi ↦ by rw [hθ i hi])]
  simp_rw [hellingerAffinity_gaussianReal _ _ hv, ← exp_sum]
  congr 1
  simp only [neg_div, ← Finset.sum_div, Finset.sum_neg_distrib]

end TauCeti
