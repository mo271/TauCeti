/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import TauCeti.Analysis.Convex.FiniteMean
public import TauCeti.Probability.Moments.Covariance
import TauCeti.Probability.Kernel.CondDistrib
import TauCeti.Probability.Moments.Mixture
import TauCeti.Probability.Moments.SampleMean

/-!
# Rubin's combining rules for multiple imputation

Given observed data `Y_obs` and missing data `Y_mis`, Bayesian inference about an estimand `θ`
targets the observed-data posterior `P(θ | Y_obs)`. Disintegrating through `(Y_obs, Y_mis)`
identifies `P(θ | Y_obs)` with the mixture `κ ∘ₘ ν` of the complete-data posterior kernel
`κ(z) = P(θ | Y_obs, Y_mis = z)` over the posterior predictive law `ν = P(Y_mis | Y_obs)`
(`ProbabilityTheory.condDistrib_ae_eq_comp`). By the law of total variance, the observed-data
posterior variance splits into `V_∞ + B_∞`, where `V_∞ = ∫ Var(κ z) dν(z)` is the expected
complete-data posterior variance and `B_∞ = Var_ν(z ↦ ∫ x dκ(z))` is the posterior predictive
variance of the complete-data posterior mean (`ProbabilityTheory.Kernel.variance_comp` and
`ProbabilityTheory.condVar_ae_eq_condExp_condVar_add_condVar_condExp`).

Multiple imputation approximates these quantities from `D` independent imputations
`z₁, …, z_D ∼ ν`:

* `TauCeti.miMean κ z = D⁻¹ ∑ d, ∫ x d(κ (z d))`, the pooled point estimate;
* `TauCeti.miWithin κ z = D⁻¹ ∑ d, Var(κ (z d))`, the average within-imputation variance `W`;
* `TauCeti.miBetween κ z = (D - 1)⁻¹ ∑ d, (∫ x d(κ (z d)) - miMean κ z)²`, the Bessel-corrected
  between-imputation sample variance `B`;
* `TauCeti.rubinTotalVariance κ z = W + (1 + D⁻¹) B`, Rubin's total variance estimator `T`.

With Bessel's divisor `D - 1` (requiring `2 ≤ D`), `W` and `B` are unbiased estimators of `V_∞`
and `B_∞`, while the finite-imputation inflation factor `1 + D⁻¹` accounts for the Monte Carlo
variance `D⁻¹ B_∞` of `miMean` around `E(θ | Y_obs)`: both `E[T]` and the mean-square posterior
discrepancy `E[(θ - miMean)²]` equal `Var(θ | Y_obs) + D⁻¹ B_∞`. For a vector estimand in
`EuclideanSpace ℝ ι`, the same three exact moment identities hold entrywise with outer products
and `TauCeti.covMatrix` covariance matrices.

## Main definitions and statements

* `TauCeti.miMean`, `TauCeti.miWithin`, `TauCeti.miBetween`, `TauCeti.rubinTotalVariance`:
  Rubin's scalar multiple-imputation statistics over `D` imputations.
* `TauCeti.miBetween_eq_zero_iff`: `miBetween κ z = 0` iff all `D` completed-data means agree.
* `TauCeti.integral_miMean`, `TauCeti.integral_miWithin`, `TauCeti.integral_miBetween`:
  component expectations under `Measure.pi (fun _ : Fin D ↦ ν)`.
* `TauCeti.integral_rubinTotalVariance`: exact conditional moment identities for `miMean`,
  `rubinTotalVariance`, and `(θ - miMean)²`.
* `TauCeti.ae_integral_rubinTotalVariance_condDistrib`: almost-everywhere observed-data
  posterior form of `integral_rubinTotalVariance` on a joint Bayesian model `(J, θ, Yo, Ym)`.
* `TauCeti.integral_rubinTotalVariance_vector`: exact conditional moment identities for a
  Euclidean-space vector estimand.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley,
  2020, §10.2, (10.8)–(10.14), pp. 233–234.
* D. B. Rubin, *Multiple Imputation for Nonresponse in Surveys*, Wiley, 1987, §3.1.
-/

public section

open MeasureTheory ProbabilityTheory Finset

namespace TauCeti

variable {M : Type*} [MeasurableSpace M]

section Basic

/-- The multiple-imputation point estimate, defined as the average of the completed-data
posterior means across `D` imputations. -/
noncomputable def miMean {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  (D : ℝ)⁻¹ * ∑ d, ∫ x, x ∂κ (z d)

/-- The within-imputation variance `W`, defined as the average of the completed-data posterior
variances across `D` imputations. -/
noncomputable def miWithin {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  (D : ℝ)⁻¹ * ∑ d, variance id (κ (z d))

/-- The between-imputation sample variance `B` of the completed-data posterior means, normalized
with Bessel's divisor `D - 1`. -/
noncomputable def miBetween {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  ((D : ℝ) - 1)⁻¹ * ∑ d, (∫ x, x ∂κ (z d) - miMean κ z) ^ 2

/-- Rubin's total variance estimator `T = W + (1 + D⁻¹) B`, combining within-imputation and
inflated between-imputation variance. -/
noncomputable def rubinTotalVariance {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  miWithin κ z + (1 + (D : ℝ)⁻¹) * miBetween κ z

theorem miMean_def {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    miMean κ z = (D : ℝ)⁻¹ * ∑ d, ∫ x, x ∂κ (z d) := (rfl)

theorem miWithin_def {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    miWithin κ z = (D : ℝ)⁻¹ * ∑ d, variance id (κ (z d)) := (rfl)

theorem miBetween_def {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    miBetween κ z = ((D : ℝ) - 1)⁻¹ * ∑ d, (∫ x, x ∂κ (z d) - miMean κ z) ^ 2 := (rfl)

theorem rubinTotalVariance_def {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    rubinTotalVariance κ z = miWithin κ z + (1 + (D : ℝ)⁻¹) * miBetween κ z := (rfl)

/-- `miMean` is `TauCeti.finiteMean` applied to the completed-data posterior means. -/
theorem miMean_eq_finiteMean {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    miMean κ z = finiteMean ℝ fun d ↦ ∫ x, x ∂κ (z d) := by
  simp [miMean_def, finiteMean_eq_inv_smul_sum]

/-- `miWithin` is `TauCeti.finiteMean` applied to the completed-data posterior variances. -/
theorem miWithin_eq_finiteMean {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    miWithin κ z = finiteMean ℝ fun d ↦ variance id (κ (z d)) := by
  simp [miWithin_def, finiteMean_eq_inv_smul_sum]

@[simp]
theorem miMean_zero (κ : Kernel M ℝ) (z : Fin 0 → M) : miMean κ z = 0 := by
  simp [miMean_def]

@[simp]
theorem miWithin_zero (κ : Kernel M ℝ) (z : Fin 0 → M) : miWithin κ z = 0 := by
  simp [miWithin_def]

@[simp]
theorem miBetween_zero (κ : Kernel M ℝ) (z : Fin 0 → M) : miBetween κ z = 0 := by
  simp [miBetween_def]

@[simp]
theorem rubinTotalVariance_zero (κ : Kernel M ℝ) (z : Fin 0 → M) :
    rubinTotalVariance κ z = 0 := by
  simp [rubinTotalVariance_def]

@[simp]
theorem miMean_one (κ : Kernel M ℝ) (z : Fin 1 → M) :
    miMean κ z = ∫ x, x ∂κ (z 0) := by
  simp [miMean_def]

@[simp]
theorem miWithin_one (κ : Kernel M ℝ) (z : Fin 1 → M) :
    miWithin κ z = variance id (κ (z 0)) := by
  simp [miWithin_def]

@[simp]
theorem miBetween_one (κ : Kernel M ℝ) (z : Fin 1 → M) :
    miBetween κ z = 0 := by
  simp [miBetween_def]

@[simp]
theorem rubinTotalVariance_one (κ : Kernel M ℝ) (z : Fin 1 → M) :
    rubinTotalVariance κ z = variance id (κ (z 0)) := by
  simp [rubinTotalVariance_def]

/-- The between-imputation variance vanishes if and only if all `D` completed-data posterior means
coincide (which holds vacuously for `D ≤ 1`). -/
theorem miBetween_eq_zero_iff {D : ℕ} {κ : Kernel M ℝ} {z : Fin D → M} :
    miBetween κ z = 0 ↔ ∀ d₁ d₂, (∫ x, x ∂κ (z d₁)) = ∫ x, x ∂κ (z d₂) := by
  rcases D with _ | _ | D
  · simp
  · simp [Fin.forall_fin_one]
  · have hpos : (0 : ℝ) < ((D + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
    rw [miBetween_def, mul_eq_zero, inv_eq_zero, or_iff_right hpos.ne',
      sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _]
    constructor
    · intro h d₁ d₂
      have h₁ := sub_eq_zero.1 (sq_eq_zero_iff.1 (h d₁ (mem_univ _)))
      have h₂ := sub_eq_zero.1 (sq_eq_zero_iff.1 (h d₂ (mem_univ _)))
      linarith
    · intro h d _
      rw [sq_eq_zero_iff, sub_eq_zero, miMean_eq_finiteMean]
      have hm : (fun i ↦ ∫ x, x ∂κ (z i)) = fun _ ↦ ∫ x, x ∂κ (z d) := funext fun i ↦ h i d
      have hd0 : ((D + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hm, finiteMean_eq_inv_smul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        smul_eq_mul, inv_mul_cancel_left₀ hd0]

/-- When the complete-data posterior does not depend on the imputed value, the between-imputation
variance vanishes identically. -/
@[simp]
theorem miBetween_const {D : ℕ} (μ : Measure ℝ) (z : Fin D → M) :
    miBetween (Kernel.const M μ) z = 0 :=
  miBetween_eq_zero_iff.2 fun _ _ ↦ rfl

theorem miMean_const {D : ℕ} (hD : D ≠ 0) (μ : Measure ℝ) (z : Fin D → M) :
    miMean (Kernel.const M μ) z = ∫ x, x ∂μ := by
  have hd0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD
  simp [miMean_def, inv_mul_cancel_left₀ hd0]

theorem miWithin_const {D : ℕ} (hD : D ≠ 0) (μ : Measure ℝ) (z : Fin D → M) :
    miWithin (Kernel.const M μ) z = variance id μ := by
  have hd0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD
  simp [miWithin_def, inv_mul_cancel_left₀ hd0]

/-- When every imputation produces the same posterior `μ` and `D ≠ 0`, Rubin's total variance
reduces to `variance id μ` with no between-imputation inflation. -/
theorem rubinTotalVariance_const {D : ℕ} (hD : D ≠ 0) (μ : Measure ℝ) (z : Fin D → M) :
    rubinTotalVariance (Kernel.const M μ) z = variance id μ := by
  simp [rubinTotalVariance_def, miWithin_const hD]

theorem miWithin_nonneg {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    0 ≤ miWithin κ z := by
  rw [miWithin_def]
  exact mul_nonneg (by positivity) (sum_nonneg fun _ _ ↦ variance_nonneg _ _)

theorem miBetween_nonneg {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    0 ≤ miBetween κ z := by
  rcases D with _ | _ | D
  · simp
  · simp
  · rw [miBetween_def]
    exact mul_nonneg (inv_nonneg.2 (by push_cast; linarith)) (sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem rubinTotalVariance_nonneg {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    0 ≤ rubinTotalVariance κ z := by
  rw [rubinTotalVariance_def]
  exact add_nonneg (miWithin_nonneg κ z) (mul_nonneg (by positivity) (miBetween_nonneg κ z))

theorem miWithin_le_rubinTotalVariance {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) :
    miWithin κ z ≤ rubinTotalVariance κ z := by
  rw [rubinTotalVariance_def]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (miBetween_nonneg κ z))

@[fun_prop]
theorem measurable_miMean {D : ℕ} (κ : Kernel M ℝ) :
    Measurable (miMean κ (D := D)) := by
  unfold miMean
  have hm : Measurable fun m : M ↦ ∫ x, x ∂κ m :=
    measurable_id.stronglyMeasurable.integral_kernel.measurable
  exact measurable_const.mul (Finset.measurable_sum _ fun d _ ↦ hm.comp (measurable_pi_apply d))

@[fun_prop]
theorem measurable_miWithin {D : ℕ} (κ : Kernel M ℝ) :
    Measurable (miWithin κ (D := D)) := by
  unfold miWithin
  have hv : Measurable fun m : M ↦ variance id (κ m) := measurable_id.variance_kernel
  exact measurable_const.mul (Finset.measurable_sum _ fun d _ ↦ hv.comp (measurable_pi_apply d))

@[fun_prop]
theorem measurable_miBetween {D : ℕ} (κ : Kernel M ℝ) :
    Measurable (miBetween κ (D := D)) := by
  unfold miBetween
  have hm : Measurable fun m : M ↦ ∫ x, x ∂κ m :=
    measurable_id.stronglyMeasurable.integral_kernel.measurable
  refine measurable_const.mul (Finset.measurable_sum _ fun d _ ↦ ?_)
  exact ((hm.comp (measurable_pi_apply d)).sub (measurable_miMean κ)).pow_const 2

@[fun_prop]
theorem measurable_rubinTotalVariance {D : ℕ} (κ : Kernel M ℝ) :
    Measurable (rubinTotalVariance κ (D := D)) := by
  unfold rubinTotalVariance
  exact (measurable_miWithin κ).add (measurable_const.mul (measurable_miBetween κ))

end Basic

section Helpers

private theorem integral_pi_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : Measure M} [IsProbabilityMeasure ν] {D : ℕ} (d : Fin D) {g : M → E}
    (hg : AEStronglyMeasurable g ν) :
    ∫ z, g (z d) ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ m, g m ∂ν := by
  have hmp := (measurePreserving_eval (fun _ : Fin D ↦ ν) d).map_eq
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : Fin D ↦ ν).map (Function.eval d)) :=
    hmp.symm ▸ hg
  exact (integral_map (measurable_pi_apply d).aemeasurable hg').symm.trans (by rw [hmp])

private theorem covariance_pi_eval {ν : Measure M} [IsProbabilityMeasure ν] {D : ℕ} (d : Fin D)
    {f g : M → ℝ} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) :
    cov[fun z ↦ f (z d), fun z ↦ g (z d); Measure.pi fun _ : Fin D ↦ ν] = cov[f, g; ν] := by
  have hmp := (measurePreserving_eval (fun _ : Fin D ↦ ν) d).map_eq
  have hf' : AEStronglyMeasurable f ((Measure.pi fun _ : Fin D ↦ ν).map (Function.eval d)) :=
    hmp.symm ▸ hf
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : Fin D ↦ ν).map (Function.eval d)) :=
    hmp.symm ▸ hg
  exact (covariance_map hf' hg' (measurable_pi_apply d).aemeasurable).symm.trans (by rw [hmp])

private theorem integral_prod_sub_mul_sub {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {π : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    {u₁ u₂ : α → ℝ} {v₁ v₂ : β → ℝ}
    (hu₁ : MemLp u₁ 2 μ) (hu₂ : MemLp u₂ 2 μ) (hv₁ : MemLp v₁ 2 π) (hv₂ : MemLp v₂ 2 π)
    (hm₁ : ∫ x, u₁ x ∂μ = 0) (hm₂ : ∫ x, u₂ x ∂μ = 0) :
    ∫ p, (u₁ p.1 - v₁ p.2) * (u₂ p.1 - v₂ p.2) ∂(μ.prod π) =
      (∫ x, u₁ x * u₂ x ∂μ) + ∫ y, v₁ y * v₂ y ∂π := by
  have h1 : Integrable (fun p : α × β ↦ u₁ p.1 * u₂ p.1) (μ.prod π) :=
    (hu₁.comp_fst π).integrable_mul (hu₂.comp_fst π)
  have h2 : Integrable (fun p : α × β ↦ u₁ p.1 * v₂ p.2) (μ.prod π) :=
    (hu₁.comp_fst π).integrable_mul (hv₂.comp_snd μ)
  have h3 : Integrable (fun p : α × β ↦ v₁ p.2 * u₂ p.1) (μ.prod π) :=
    (hv₁.comp_snd μ).integrable_mul (hu₂.comp_fst π)
  have h4 : Integrable (fun p : α × β ↦ v₁ p.2 * v₂ p.2) (μ.prod π) :=
    (hv₁.comp_snd μ).integrable_mul (hv₂.comp_snd μ)
  have hexp : (fun p : α × β ↦ (u₁ p.1 - v₁ p.2) * (u₂ p.1 - v₂ p.2)) =
      fun p ↦ u₁ p.1 * u₂ p.1 - u₁ p.1 * v₂ p.2 - v₁ p.2 * u₂ p.1 + v₁ p.2 * v₂ p.2 := by
    ext p; ring
  rw [hexp,
    integral_add (f := fun p ↦ u₁ p.1 * u₂ p.1 - u₁ p.1 * v₂ p.2 - v₁ p.2 * u₂ p.1)
      ((h1.sub h2).sub h3) h4,
    integral_sub (f := fun p ↦ u₁ p.1 * u₂ p.1 - u₁ p.1 * v₂ p.2) (h1.sub h2) h3,
    integral_sub h1 h2]
  have hp1 := integral_prod_mul (μ := μ) (ν := π) (f := fun x ↦ u₁ x * u₂ x) (g := fun _ ↦ (1 : ℝ))
  have hp2 := integral_prod_mul (μ := μ) (ν := π) (f := u₁) (g := v₂)
  have hp3 := integral_prod_mul (μ := μ) (ν := π) (f := u₂) (g := v₁)
  have hp4 := integral_prod_mul (μ := μ) (ν := π) (f := fun _ ↦ (1 : ℝ)) (g := fun y ↦ v₁ y * v₂ y)
  simp only [mul_one, one_mul, integral_const, probReal_univ, one_smul, hm₁, hm₂, zero_mul]
    at hp1 hp2 hp3 hp4
  have hp3' : ∫ p : α × β, v₁ p.2 * u₂ p.1 ∂(μ.prod π) = 0 := by
    simpa only [mul_comm (v₁ _)] using hp3
  rw [hp1, hp2, hp3', hp4]
  ring

end Helpers

section Moments

/-- For `D ≠ 0` i.i.d. imputations from `ν` and any kernel `κ`, the expected multiple-imputation
point estimate `miMean κ` equals the mixture mean `∫ x, x ∂(κ ∘ₘ ν)`. -/
theorem integral_miMean (ν : Measure M) [IsProbabilityMeasure ν] (κ : Kernel M ℝ)
    (h1 : Integrable id (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) :
    ∫ z, miMean κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ x, x ∂(κ ∘ₘ ν) := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  have hm_int : Integrable (fun m ↦ ∫ x, x ∂κ m) ν :=
    Measure.integrable_integral_bind κ.measurable h1
  have hd_int : ∀ d : Fin D, Integrable (fun z : Fin D → M ↦ ∫ x, x ∂κ (z d)) π := fun d ↦
    memLp_one_iff_integrable.1 <|
      (memLp_one_iff_integrable.2 hm_int).comp_measurePreserving (measurePreserving_eval _ d)
  have hd_eq : ∀ d : Fin D, ∫ z, (∫ x, x ∂κ (z d)) ∂π = ∫ m, (∫ x, x ∂κ m) ∂ν := fun d ↦
    integral_pi_eval d hm_int.aestronglyMeasurable
  have hd0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD
  simp_rw [miMean_def]
  rw [integral_const_mul, integral_finsetSum _ fun d _ ↦ hd_int d]
  simp_rw [hd_eq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, inv_mul_cancel_left₀ hd0]
  exact (Measure.integral_bind κ.aemeasurable h1).symm

/-- For `D ≠ 0` i.i.d. imputations from `ν` and any kernel `κ`, the expected within-imputation
variance `miWithin κ` equals `∫ m, variance id (κ m) ∂ν`. -/
theorem integral_miWithin (ν : Measure M) [IsProbabilityMeasure ν] (κ : Kernel M ℝ)
    {D : ℕ} (hD : D ≠ 0) :
    ∫ z, miWithin κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ m, variance id (κ m) ∂ν := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set g : M → ℝ := fun m ↦ variance id (κ m)
  have hg : Measurable g := measurable_id.variance_kernel
  have hd0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD
  by_cases hgi : Integrable g ν
  · have hd_int : ∀ d : Fin D, Integrable (fun z : Fin D → M ↦ g (z d)) π := fun d ↦
      memLp_one_iff_integrable.1 <|
        (memLp_one_iff_integrable.2 hgi).comp_measurePreserving (measurePreserving_eval _ d)
    have hd_eq : ∀ d : Fin D, ∫ z, g (z d) ∂π = ∫ m, g m ∂ν := fun d ↦
      integral_pi_eval d hgi.aestronglyMeasurable
    simp_rw [miWithin_def]
    rw [integral_const_mul, integral_finsetSum _ fun d _ ↦ hd_int d]
    simp_rw [hd_eq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, inv_mul_cancel_left₀ hd0]
  · rw [integral_undef hgi]
    refine integral_undef fun hwi ↦ hgi ?_
    let d₀ : Fin D := ⟨0, Nat.pos_of_ne_zero hD⟩
    have hmono : Integrable (fun z : Fin D → M ↦ (D : ℝ)⁻¹ * g (z d₀)) π := by
      refine hwi.mono' (((hg.comp (measurable_pi_apply d₀)).const_mul _).aestronglyMeasurable)
        (.of_forall fun z ↦ ?_)
      have hnn : 0 ≤ (D : ℝ)⁻¹ * g (z d₀) := mul_nonneg (by positivity) (variance_nonneg _ _)
      rw [Real.norm_of_nonneg hnn, miWithin_def]
      exact mul_le_mul_of_nonneg_left
        (single_le_sum (f := fun d ↦ variance id (κ (z d)))
          (fun d _ ↦ variance_nonneg _ _) (mem_univ d₀)) (by positivity)
    have hcomp : Integrable (g ∘ Function.eval d₀) π := by
      convert hmono.const_mul (D : ℝ) using 1
      ext z
      exact (mul_inv_cancel_left₀ hd0 (g (z d₀))).symm
    have hmp := (measurePreserving_eval (fun _ : Fin D ↦ ν) d₀).map_eq
    have hg' : AEStronglyMeasurable g (π.map (Function.eval d₀)) :=
      hmp.symm ▸ hg.aestronglyMeasurable
    exact hmp ▸ (integrable_map_measure hg' (measurable_pi_apply d₀).aemeasurable).2 hcomp

/-- If `miBetween κ` is integrable under `Measure.pi (fun _ : Fin D ↦ ν)` for `2 ≤ D`, then the
completed-data mean function `m ↦ ∫ x, x ∂κ m` belongs to `L²(ν)`. -/
private theorem memLp_integral_of_integrable_miBetween {ν : Measure M} [IsProbabilityMeasure ν]
    {κ : Kernel M ℝ} {D : ℕ} (hD : 2 ≤ D)
    (hbi : Integrable (miBetween κ) (Measure.pi fun _ : Fin D ↦ ν)) :
    MemLp (fun m ↦ ∫ x, x ∂κ m) 2 ν := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set f : M → ℝ := fun m ↦ ∫ x, x ∂κ m
  have hf : Measurable f := measurable_id.stronglyMeasurable.integral_kernel.measurable
  let d₀ : Fin D := ⟨0, by omega⟩
  let d₁ : Fin D := ⟨1, by omega⟩
  have hd01 : d₀ ≠ d₁ := by simp [d₀, d₁]
  have hsum_int : Integrable (fun z : Fin D → M ↦ ∑ d, (f (z d) - miMean κ z) ^ 2) π := by
    have hD1 : ((D : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ D := Nat.ofNat_le_cast.2 hD
      linarith
    convert hbi.const_mul ((D : ℝ) - 1) using 1
    ext z
    exact (mul_inv_cancel_left₀ hD1 _).symm
  have hdiff_int : Integrable (fun z : Fin D → M ↦ (f (z d₀) - f (z d₁)) ^ 2) π := by
    have hhalf : Integrable (fun z : Fin D → M ↦ (f (z d₀) - f (z d₁)) ^ 2 / 2) π := by
      refine hsum_int.mono'
        ((((hf.comp (measurable_pi_apply d₀)).sub (hf.comp (measurable_pi_apply d₁))).pow_const
          2).div_const 2).aestronglyMeasurable (.of_forall fun z ↦ ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      have hpair : (f (z d₀) - f (z d₁)) ^ 2 / 2 ≤
          (f (z d₀) - miMean κ z) ^ 2 + (f (z d₁) - miMean κ z) ^ 2 := by
        nlinarith [sq_nonneg (f (z d₀) + f (z d₁) - 2 * miMean κ z)]
      exact hpair.trans (add_le_sum (f := fun d ↦ (f (z d) - miMean κ z) ^ 2)
        (fun _ _ ↦ sq_nonneg _) (mem_univ _) (mem_univ _) hd01)
    simpa using hhalf.mul_const 2
  have hindep : IndepFun (Function.eval d₀) (Function.eval d₁) π :=
    (iIndepFun_pi (μ := fun _ : Fin D ↦ ν) fun _ ↦ aemeasurable_id).indepFun hd01
  have hmap : π.map (fun z : Fin D → M ↦ (z d₀, z d₁)) = ν.prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply d₀).aemeasurable
      (measurable_pi_apply d₁).aemeasurable).1 hindep,
      (measurePreserving_eval _ d₀).map_eq, (measurePreserving_eval _ d₁).map_eq]
  have hprod_meas : Measurable fun p : M × M ↦ (f p.1 - f p.2) ^ 2 :=
    ((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2
  have hprod_int : Integrable (fun p : M × M ↦ (f p.1 - f p.2) ^ 2) (ν.prod ν) := by
    rw [← hmap]
    exact (integrable_map_measure hprod_meas.aestronglyMeasurable (by fun_prop)).2 hdiff_int
  obtain ⟨v₀, hv₀⟩ := ((integrable_prod_iff hprod_meas.aestronglyMeasurable).1 hprod_int).1.exists
  have hv₀' : Integrable (fun y ↦ (f y - f v₀) ^ 2) ν :=
    hv₀.congr (.of_forall fun y ↦ by dsimp; ring)
  have hsub_meas : Measurable fun y ↦ f y - f v₀ := by fun_prop
  have hsub : MemLp (fun y ↦ f y - f v₀) 2 ν :=
    (memLp_two_iff_integrable_sq hsub_meas.aestronglyMeasurable).2 hv₀'
  simpa [Pi.add_def] using hsub.add (memLp_const (f v₀))

/-- For `2 ≤ D` i.i.d. imputations from `ν` and any kernel `κ`, the expected between-imputation
variance `miBetween κ` equals `variance (fun m ↦ ∫ x, x ∂κ m) ν`. -/
theorem integral_miBetween (ν : Measure M) [IsProbabilityMeasure ν] (κ : Kernel M ℝ)
    {D : ℕ} (hD : 2 ≤ D) :
    ∫ z, miBetween κ z ∂(Measure.pi fun _ : Fin D ↦ ν) =
      variance (fun m ↦ ∫ x, x ∂κ m) ν := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set f : M → ℝ := fun m ↦ ∫ x, x ∂κ m
  have hf : Measurable f := measurable_id.stronglyMeasurable.integral_kernel.measurable
  by_cases hf2 : MemLp f 2 ν
  · have hX : ∀ d : Fin D, MemLp (fun z : Fin D → M ↦ f (z d)) 2 π := fun d ↦
      hf2.comp_measurePreserving (measurePreserving_eval _ d)
    have hmean_d : ∀ d : Fin D, ∫ z, f (z d) ∂π = ∫ m, f m ∂ν := fun d ↦
      integral_pi_eval d hf.aestronglyMeasurable
    have hind : iIndepFun (fun (d : Fin D) (z : Fin D → M) ↦ f (z d)) π :=
      iIndepFun_pi fun _ ↦ hf.aemeasurable
    have hcov : Pairwise fun d₁ d₂ : Fin D ↦
        cov[fun z ↦ f (z d₁), fun z ↦ f (z d₂); π] = 0 :=
      fun _ _ hne ↦ (hind.indepFun hne).covariance_eq_zero (hX _) (hX _)
    have hdiag : ∀ d : Fin D, cov[fun z ↦ f (z d), fun z ↦ f (z d); π] = variance f ν := fun d ↦ by
      rw [covariance_pi_eval d hf.aestronglyMeasurable hf.aestronglyMeasurable,
        covariance_self hf.aemeasurable]
    have hcongr : miBetween κ = fun z : Fin D → M ↦
        ((Fintype.card (Fin D) : ℝ) - 1)⁻¹ *
          ∑ d, (f (z d) - finiteMean ℝ (fun i ↦ f (z i))) *
            (f (z d) - finiteMean ℝ (fun i ↦ f (z i))) := by
      ext z
      simp [miBetween_def, miMean_eq_finiteMean, f, sq]
    rw [hcongr]
    exact integral_inv_card_sub_one_mul_sum_sub_finiteMean_mul
      (by simpa using hD) hX hX (fun d₁ d₂ ↦ by rw [hmean_d, hmean_d]) hcov hdiag
  · rw [variance_of_not_memLp hf.aestronglyMeasurable hf2]
    exact integral_undef fun hbi ↦ hf2 (memLp_integral_of_integrable_miBetween hD hbi)

/-- Monte Carlo variance `D⁻¹ * Var_ν(m ↦ ∫ x, x ∂κ m)` of `miMean κ` around `∫ x, x ∂(κ ∘ₘ ν)`. -/
private theorem integral_miMean_sub_sq (ν : Measure M) [IsProbabilityMeasure ν] (κ : Kernel M ℝ)
    [IsMarkovKernel κ] (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) :
    ∫ z, (miMean κ z - ∫ x, x ∂(κ ∘ₘ ν)) ^ 2 ∂(Measure.pi fun _ : Fin D ↦ ν) =
      (D : ℝ)⁻¹ * variance (fun m ↦ ∫ x, x ∂κ m) ν := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set f : M → ℝ := fun m ↦ ∫ x, x ∂κ m
  set m₀ : ℝ := ∫ x, x ∂(κ ∘ₘ ν)
  have hf : Measurable f := measurable_id.stronglyMeasurable.integral_kernel.measurable
  have hf2 : MemLp f 2 ν :=
    TauCeti.Probability.memLp_integral_bind κ.measurable (.of_forall fun _ ↦ inferInstance) hLp
  have hm₀ : ∫ m, f m ∂ν = m₀ :=
    (Measure.integral_bind κ.aemeasurable (hLp.integrable one_le_two)).symm
  have hX : ∀ d : Fin D, MemLp (fun z : Fin D → M ↦ f (z d)) 2 π := fun d ↦
    hf2.comp_measurePreserving (measurePreserving_eval _ d)
  have hind : iIndepFun (fun (d : Fin D) (z : Fin D → M) ↦ f (z d)) π :=
    iIndepFun_pi fun _ ↦ hf.aemeasurable
  have hmean_d : ∀ d : Fin D, ∫ z, f (z d) ∂π = m₀ := fun d ↦
    (integral_pi_eval d hf.aestronglyMeasurable).trans hm₀
  have hvar_d : ∀ d : Fin D, ∫ z, ‖f (z d) - m₀‖ ^ 2 ∂π = variance f ν := fun d ↦ by
    simp_rw [Real.norm_eq_abs, sq_abs]
    rw [integral_pi_eval (g := fun m ↦ (f m - m₀) ^ 2) d
      (((hf.sub measurable_const).pow_const 2).aestronglyMeasurable), ← hm₀,
      variance_eq_integral hf.aemeasurable]
  have : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
  simpa [miMean_eq_finiteMean, Real.norm_eq_abs, sq_abs, div_eq_inv_mul] using
    integral_norm_finiteMean_sub_sq_of_forall_eq hX hmean_d
      (fun _ _ hne ↦ hind.indepFun hne) hvar_d

/-- Mean-square discrepancy `∫ (θ - miMean κ z) ^ 2` under `(κ ∘ₘ ν).prod (Measure.pi ...)`. -/
private theorem integral_sub_miMean_sq (ν : Measure M) [IsProbabilityMeasure ν] (κ : Kernel M ℝ)
    [IsMarkovKernel κ] (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) :
    ∫ p, (p.1 - miMean κ p.2) ^ 2 ∂((κ ∘ₘ ν).prod (Measure.pi fun _ : Fin D ↦ ν)) =
      variance id (κ ∘ₘ ν) + (D : ℝ)⁻¹ * variance (fun z ↦ ∫ x, x ∂κ z) ν := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set f : M → ℝ := fun m ↦ ∫ x, x ∂κ m
  set m₀ : ℝ := ∫ x, x ∂(κ ∘ₘ ν)
  have hf2 : MemLp f 2 ν :=
    TauCeti.Probability.memLp_integral_bind κ.measurable (.of_forall fun _ ↦ inferInstance) hLp
  have hX : ∀ d : Fin D, MemLp (fun z : Fin D → M ↦ f (z d)) 2 π := fun d ↦
    hf2.comp_measurePreserving (measurePreserving_eval _ d)
  have hbar_Lp : MemLp (fun z : Fin D → M ↦ miMean κ z - m₀) 2 π :=
    ((memLp_finsetSum univ fun d _ ↦ hX d).const_mul _).sub (memLp_const m₀)
  have hθ_Lp : MemLp (fun x : ℝ ↦ x - m₀) 2 (κ ∘ₘ ν) := hLp.sub (memLp_const m₀)
  have hm0 : ∫ x : ℝ, x - m₀ ∂(κ ∘ₘ ν) = 0 := by
    have hint : Integrable (fun x : ℝ ↦ x) (κ ∘ₘ ν) := hLp.integrable one_le_two
    rw [integral_sub hint (integrable_const m₀)]
    simp [m₀]
  have hshift : (fun p : ℝ × (Fin D → M) ↦ (p.1 - miMean κ p.2) ^ 2) =
      fun p ↦ ((p.1 - m₀) - (miMean κ p.2 - m₀)) * ((p.1 - m₀) - (miMean κ p.2 - m₀)) := by
    ext p; ring
  rw [hshift, integral_prod_sub_mul_sub hθ_Lp hθ_Lp hbar_Lp hbar_Lp hm0 hm0]
  simp_rw [← sq]
  rw [integral_miMean_sub_sq ν κ hLp hD, variance_eq_integral aemeasurable_id]
  simp [m₀, f]

/-- **Rubin's combining rules, exact form.** Given a posterior predictive probability law `ν` on `M`
and a complete-data posterior Markov kernel `κ : Kernel M ℝ` whose mixture `κ ∘ₘ ν` has a finite
second moment, for `2 ≤ D` i.i.d. imputations `z ∼ Measure.pi (fun _ : Fin D ↦ ν)` independent of
`θ ∼ κ ∘ₘ ν`:
1. `miMean κ` has expectation `∫ x, x ∂(κ ∘ₘ ν)`;
2. `rubinTotalVariance κ` has expectation `variance id (κ ∘ₘ ν) + D⁻¹ * variance (m ↦ ∫ x ∂κ m) ν`;
3. the squared posterior discrepancy `(θ - miMean κ z) ^ 2` has the same expectation. -/
theorem integral_rubinTotalVariance (ν : Measure M) [IsProbabilityMeasure ν] (κ : Kernel M ℝ)
    [IsMarkovKernel κ] (h2 : Integrable (fun x : ℝ ↦ x ^ 2) (κ ∘ₘ ν)) {D : ℕ} (hD : 2 ≤ D) :
    ∫ z, miMean κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ x, x ∂(κ ∘ₘ ν) ∧
    ∫ z, rubinTotalVariance κ z ∂(Measure.pi fun _ : Fin D ↦ ν) =
      variance id (κ ∘ₘ ν) + (D : ℝ)⁻¹ * variance (fun z ↦ ∫ x, x ∂κ z) ν ∧
    ∫ p, (p.1 - miMean κ p.2) ^ 2 ∂((κ ∘ₘ ν).prod (Measure.pi fun _ : Fin D ↦ ν)) =
      variance id (κ ∘ₘ ν) + (D : ℝ)⁻¹ * variance (fun z ↦ ∫ x, x ∂κ z) ν := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set f : M → ℝ := fun m ↦ ∫ x, x ∂κ m
  have hLp : MemLp id 2 (κ ∘ₘ ν) := (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h2
  have hf2 : MemLp f 2 ν :=
    TauCeti.Probability.memLp_integral_bind κ.measurable (.of_forall fun _ ↦ inferInstance) hLp
  have hvar_int : Integrable (fun m ↦ variance id (κ m)) ν :=
    (TauCeti.Probability.integrable_covariance_bind κ.measurable
      (.of_forall fun _ ↦ inferInstance) hLp hLp).congr
      (.of_forall fun _ ↦ covariance_self aemeasurable_id')
  have hw_int : Integrable (miWithin κ) π :=
    (integrable_finsetSum _ fun d _ ↦ memLp_one_iff_integrable.1 <|
      (memLp_one_iff_integrable.2 hvar_int).comp_measurePreserving
        (measurePreserving_eval _ d)).const_mul _
  have hb_int : Integrable (miBetween κ) π := by
    refine (integrable_finsetSum _ fun d _ ↦ ?_).const_mul _
    have hd : MemLp (fun z : Fin D → M ↦ f (z d)) 2 π :=
      hf2.comp_measurePreserving (measurePreserving_eval _ d)
    have hbar : MemLp (miMean κ) 2 π :=
      (memLp_finsetSum univ fun i _ ↦
        hf2.comp_measurePreserving (measurePreserving_eval _ i)).const_mul _
    exact (hd.sub hbar).integrable_sq
  refine ⟨integral_miMean ν κ (hLp.integrable one_le_two) (by omega), ?_,
    integral_sub_miMean_sq ν κ hLp (by omega)⟩
  simp_rw [rubinTotalVariance_def]
  rw [integral_add hw_int (hb_int.const_mul _), integral_const_mul,
    integral_miWithin ν κ (by omega), integral_miBetween ν κ hD, Kernel.variance_comp κ hLp]
  dsimp only [f, id_eq]
  ring

/-- **Conditional Rubin combining rules on a joint Bayesian missing-data model.** On a finite
measure space `(Ω, J)` carrying an `L²` real estimand `θ`, observed data `Yo`, and missing data
`Ym` in a nonempty standard Borel space `M`, for `J.map Yo`-almost every `y`, the posterior
predictive law `ν = condDistrib Ym Yo J y` and complete-data posterior kernel
`κ = (condDistrib θ (Yo, Ym) J).comap (Prod.mk y) measurable_prodMk_left` satisfy `κ ∘ₘ ν =
condDistrib θ Yo J y` together with all three exact moment identities of
`integral_rubinTotalVariance`. -/
theorem ae_integral_rubinTotalVariance_condDistrib {Ω O : Type*} [MeasurableSpace Ω]
    [MeasurableSpace O] [StandardBorelSpace M] [Nonempty M]
    {J : Measure Ω} [IsFiniteMeasure J] {θ : Ω → ℝ} {Yo : Ω → O} {Ym : Ω → M}
    (hθ : MemLp θ 2 J) (hYo : AEMeasurable Yo J) (hYm : AEMeasurable Ym J)
    {D : ℕ} (hD : 2 ≤ D) :
    ∀ᵐ y ∂J.map Yo,
      let ν := condDistrib Ym Yo J y
      let κ := (condDistrib θ (fun ω ↦ (Yo ω, Ym ω)) J).comap (Prod.mk y) measurable_prodMk_left
      κ ∘ₘ ν = condDistrib θ Yo J y ∧
        ∫ z, miMean κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ x, x ∂condDistrib θ Yo J y ∧
        ∫ z, rubinTotalVariance κ z ∂(Measure.pi fun _ : Fin D ↦ ν) =
          variance id (condDistrib θ Yo J y) + (D : ℝ)⁻¹ * variance (fun m ↦ ∫ x, x ∂κ m) ν ∧
        ∫ p, (p.1 - miMean κ p.2) ^ 2
            ∂((condDistrib θ Yo J y).prod (Measure.pi fun _ : Fin D ↦ ν)) =
          variance id (condDistrib θ Yo J y) + (D : ℝ)⁻¹ * variance (fun m ↦ ∫ x, x ∂κ m) ν := by
  have hmix := condDistrib_ae_eq_comp hθ.aemeasurable hYo hYm
  have hsq_joint : Integrable (fun p : O × ℝ ↦ p.2 ^ 2) (J.map Yo ⊗ₘ condDistrib θ Yo J) := by
    rw [compProd_map_condDistrib hYo hθ.aemeasurable]
    exact (integrable_map_measure (by fun_prop) (hYo.prodMk hθ.aemeasurable)).2 hθ.integrable_sq
  have hae_sq : ∀ᵐ y ∂J.map Yo, Integrable (fun x : ℝ ↦ x ^ 2) (condDistrib θ Yo J y) :=
    ((Measure.integrable_compProd_iff (by fun_prop)).1 hsq_joint).1
  filter_upwards [hmix, hae_sq] with y hy hsq
  have hcomp_eq : ((condDistrib θ (fun ω ↦ (Yo ω, Ym ω)) J).comap (Prod.mk y)
      measurable_prodMk_left) ∘ₘ condDistrib Ym Yo J y = condDistrib θ Yo J y := by
    ext s hs
    rw [hy, Kernel.comp_apply' _ _ _ hs,
      Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
      Kernel.lintegral_id_prod (Kernel.measurable_coe _ hs)]
    rfl
  refine ⟨hcomp_eq, ?_⟩
  simpa only [hcomp_eq] using integral_rubinTotalVariance (condDistrib Ym Yo J y)
    ((condDistrib θ (fun ω ↦ (Yo ω, Ym ω)) J).comap (Prod.mk y) measurable_prodMk_left)
    (hcomp_eq.symm ▸ hsq) hD

end Moments

section Vector

private theorem memLp_vector_coord {ι : Type*} [Fintype ι]
    {μ : Measure (EuclideanSpace ℝ ι)} (hLp : MemLp id 2 μ) (a : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ x a) 2 μ := by
  simpa only [id_eq, EuclideanSpace.coe_proj] using
    hLp.continuousLinearMap_comp (𝕜 := ℝ) (EuclideanSpace.proj a)

/-- Coordinatewise `L²` properties of the Euclidean kernel-mean map `z ↦ ∫ x, x ∂κ z`. -/
private theorem memLp_vector_mean {ι : Type*} [Fintype ι] (ν : Measure M)
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (hLp : MemLp id 2 (κ ∘ₘ ν)) :
    (∀ a : ι, (fun m ↦ (∫ x, x ∂κ m) a) =ᵐ[ν] fun m ↦ ∫ x, x a ∂κ m) ∧
      (∀ a : ι, MemLp (fun m ↦ (∫ x, x ∂κ m) a) 2 ν) ∧
      MemLp (fun m ↦ ∫ x, x ∂κ m) 2 ν := by
  have hae : ∀ᵐ m ∂ν, MemLp id 2 (κ m) :=
    ((Measure.memLp_two_bind_iff κ.measurable aestronglyMeasurable_id).1 hLp).1
  have hmean_ae : ∀ a : ι, (fun m ↦ (∫ x, x ∂κ m) a) =ᵐ[ν] fun m ↦ ∫ x, x a ∂κ m := fun a ↦ by
    filter_upwards [hae] with m hm
    simpa using ((EuclideanSpace.proj a).integral_comp_comm (hm.integrable one_le_two)).symm
  have hmean_Lp : ∀ a : ι, MemLp (fun m ↦ (∫ x, x ∂κ m) a) 2 ν := fun a ↦
    (TauCeti.Probability.memLp_integral_bind κ.measurable
      (.of_forall fun _ ↦ inferInstance) (memLp_vector_coord hLp a)).ae_eq (hmean_ae a).symm
  refine ⟨hmean_ae, hmean_Lp, ?_⟩
  simpa using MemLp.of_eval_piLp hmean_Lp

/-- Unbiasedness and integrability of the Euclidean within-imputation covariance entry `(i, j)`. -/
private theorem integral_vector_within_entry {ι : Type*} [Fintype ι]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) (i j : ι) :
    Integrable (fun z : Fin D → M ↦ (D : ℝ)⁻¹ * ∑ d, covMatrix (κ (z d)) i j)
      (Measure.pi fun _ : Fin D ↦ ν) ∧
      ∫ z : Fin D → M, (D : ℝ)⁻¹ * ∑ d, covMatrix (κ (z d)) i j
          ∂(Measure.pi fun _ : Fin D ↦ ν) =
        ∫ m, cov[fun x ↦ x i, fun x ↦ x j; κ m] ∂ν := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  have hwithin_int : Integrable (fun m ↦ covMatrix (κ m) i j) ν := by
    simp_rw [covMatrix_apply]
    exact TauCeti.Probability.integrable_covariance_bind κ.measurable
      (.of_forall fun _ ↦ inferInstance) (memLp_vector_coord hLp i) (memLp_vector_coord hLp j)
  have hd_w : ∀ d : Fin D, Integrable (fun z : Fin D → M ↦ covMatrix (κ (z d)) i j) π :=
    fun d ↦ memLp_one_iff_integrable.1 <|
      (memLp_one_iff_integrable.2 hwithin_int).comp_measurePreserving (measurePreserving_eval _ d)
  refine ⟨(integrable_finsetSum _ fun d _ ↦ hd_w d).const_mul _, ?_⟩
  have hd0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD
  rw [integral_const_mul, integral_finsetSum _ fun d _ ↦ hd_w d]
  have hd_eq : ∀ d : Fin D, ∫ z, covMatrix (κ (z d)) i j ∂π =
      ∫ m, cov[fun x ↦ x i, fun x ↦ x j; κ m] ∂ν := fun d ↦
    (integral_pi_eval d hwithin_int.aestronglyMeasurable).trans (by simp_rw [covMatrix_apply])
  simp_rw [hd_eq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, inv_mul_cancel_left₀ hd0]

/-- Unbiasedness of the Euclidean between-imputation sample cross-covariance entry `(i, j)`. -/
private theorem integral_vector_between_entry {ι : Type*} [Fintype ι]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (hD : 2 ≤ D) (i j : ι) :
    ∫ z : Fin D → M, ((D : ℝ) - 1)⁻¹ *
        ∑ d, ((∫ x, x ∂κ (z d)) i - finiteMean ℝ fun l ↦ (∫ x, x ∂κ (z l)) i) *
          ((∫ x, x ∂κ (z d)) j - finiteMean ℝ fun l ↦ (∫ x, x ∂κ (z l)) j)
        ∂(Measure.pi fun _ : Fin D ↦ ν) =
      cov[fun m ↦ ∫ x, x i ∂κ m, fun m ↦ ∫ x, x j ∂κ m; ν] := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  obtain ⟨hmean_ae, hmean_Lp, _⟩ := memLp_vector_mean ν κ hLp
  have hproj : ∀ a : ι, Measurable fun x : EuclideanSpace ℝ ι ↦ x a :=
    fun a ↦ (EuclideanSpace.proj (𝕜 := ℝ) a).measurable
  have hm_meas : Measurable fun m : M ↦ ∫ x, x ∂κ m :=
    (measurable_id.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hX : ∀ a : ι, ∀ d : Fin D, MemLp (fun z : Fin D → M ↦ (∫ x, x ∂κ (z d)) a) 2 π :=
    fun a d ↦ (hmean_Lp a).comp_measurePreserving (measurePreserving_eval _ d)
  have hind : Pairwise fun d₁ d₂ : Fin D ↦
      cov[fun z ↦ (∫ x, x ∂κ (z d₁)) i, fun z ↦ (∫ x, x ∂κ (z d₂)) j; π] = 0 := by
    intro d₁ d₂ hne
    have hi : IndepFun (Function.eval d₁) (Function.eval d₂) π :=
      (iIndepFun_pi (μ := fun _ : Fin D ↦ ν) fun _ ↦ aemeasurable_id).indepFun hne
    exact (hi.comp ((hproj i).comp hm_meas) ((hproj j).comp hm_meas)).covariance_eq_zero
      (hX i d₁) (hX j d₂)
  have hmean_d : ∀ d₁ d₂ : Fin D,
      (∫ z, (∫ x, x ∂κ (z d₁)) i ∂π) = ∫ z, (∫ x, x ∂κ (z d₂)) i ∂π := fun d₁ d₂ ↦ by
    rw [integral_pi_eval (g := fun m ↦ (∫ x, x ∂κ m) i) d₁ (hmean_Lp i).aestronglyMeasurable,
      integral_pi_eval (g := fun m ↦ (∫ x, x ∂κ m) i) d₂ (hmean_Lp i).aestronglyMeasurable]
  have hdiag : ∀ d : Fin D,
      cov[fun z ↦ (∫ x, x ∂κ (z d)) i, fun z ↦ (∫ x, x ∂κ (z d)) j; π] =
        cov[fun m ↦ ∫ x, x i ∂κ m, fun m ↦ ∫ x, x j ∂κ m; ν] := fun d ↦ by
    rw [covariance_pi_eval (f := fun m ↦ (∫ x, x ∂κ m) i) (g := fun m ↦ (∫ x, x ∂κ m) j) d
      (hmean_Lp i).aestronglyMeasurable (hmean_Lp j).aestronglyMeasurable]
    exact covariance_congr_ae (hmean_ae i) (hmean_ae j)
  simpa only [Fintype.card_fin] using
    integral_inv_card_sub_one_mul_sum_sub_finiteMean_mul
      (by simpa using hD) (hX i) (hX j) hmean_d hind hdiag

/-- Coordinatewise expectation of the Euclidean total-covariance estimator `T z i j`. -/
private theorem integral_rubinTotalCovariance_entry {ι : Type*} [Fintype ι]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (hD : 2 ≤ D) (i j : ι) :
    ∫ z : Fin D → M,
        (((D : ℝ)⁻¹ • ∑ d, covMatrix (κ (z d)) +
          (1 + (D : ℝ)⁻¹) • (((D : ℝ) - 1)⁻¹ •
            ∑ d, Matrix.of fun a b ↦
              ((∫ x, x ∂κ (z d)) - (D : ℝ)⁻¹ • ∑ l, ∫ x, x ∂κ (z l)) a *
                ((∫ x, x ∂κ (z d)) - (D : ℝ)⁻¹ • ∑ l, ∫ x, x ∂κ (z l)) b)) i j)
        ∂(Measure.pi fun _ : Fin D ↦ ν) =
      covMatrix (κ ∘ₘ ν) i j + (D : ℝ)⁻¹ * covMatrix (ν.map fun z ↦ ∫ x, x ∂κ z) i j := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set mean : M → EuclideanSpace ℝ ι := fun z ↦ ∫ x, x ∂κ z
  obtain ⟨hmean_ae, hmean_Lp, hmean_vec⟩ := memLp_vector_mean ν κ hLp
  obtain ⟨hw_pi, hwithin_eq⟩ := integral_vector_within_entry (D := D) ν κ hLp (by omega) i j
  have hproj : ∀ a : ι, Measurable fun x : EuclideanSpace ℝ ι ↦ x a :=
    fun a ↦ (EuclideanSpace.proj (𝕜 := ℝ) a).measurable
  have hX : ∀ a : ι, ∀ d : Fin D, MemLp (fun z : Fin D → M ↦ mean (z d) a) 2 π := fun a d ↦
    (hmean_Lp a).comp_measurePreserving (measurePreserving_eval _ d)
  have hbar_Lp : ∀ a : ι, MemLp (fun z : Fin D → M ↦ finiteMean ℝ fun l ↦ mean (z l) a) 2 π :=
    fun a ↦ by
      simp_rw [finiteMean_eq_inv_smul_sum, smul_eq_mul]
      exact (memLp_finsetSum univ fun l _ ↦ hX a l).const_mul _
  have hb_pi : Integrable (fun z : Fin D → M ↦ ((D : ℝ) - 1)⁻¹ *
      ∑ d, (mean (z d) i - finiteMean ℝ fun l ↦ mean (z l) i) *
        (mean (z d) j - finiteMean ℝ fun l ↦ mean (z l) j)) π :=
    (integrable_finsetSum _ fun d _ ↦
      ((hX i d).sub (hbar_Lp i)).integrable_mul ((hX j d).sub (hbar_Lp j))).const_mul _
  have hcov_map : covMatrix (ν.map mean) i j =
      cov[fun m ↦ ∫ x, x i ∂κ m, fun m ↦ ∫ x, x j ∂κ m; ν] := by
    rw [covMatrix_apply, covariance_map (hproj i).aestronglyMeasurable
      (hproj j).aestronglyMeasurable hmean_vec.aemeasurable]
    exact covariance_congr_ae (hmean_ae i) (hmean_ae j)
  have hbar_coord : ∀ z : Fin D → M, ∀ a : ι,
      ((D : ℝ)⁻¹ • ∑ l, mean (z l)) a = finiteMean ℝ fun l ↦ mean (z l) a := fun z a ↦ by
    simp [finiteMean_eq_inv_smul_sum]
  have hT_entry : (fun z : Fin D → M ↦
      (((D : ℝ)⁻¹ • ∑ d, covMatrix (κ (z d)) +
        (1 + (D : ℝ)⁻¹) • (((D : ℝ) - 1)⁻¹ •
          ∑ d, Matrix.of fun a b ↦
            (mean (z d) - (D : ℝ)⁻¹ • ∑ l, mean (z l)) a *
              (mean (z d) - (D : ℝ)⁻¹ • ∑ l, mean (z l)) b)) i j)) =
      fun z ↦ (D : ℝ)⁻¹ * ∑ d, covMatrix (κ (z d)) i j +
        (1 + (D : ℝ)⁻¹) * (((D : ℝ) - 1)⁻¹ *
          ∑ d, (mean (z d) i - finiteMean ℝ fun l ↦ mean (z l) i) *
            (mean (z d) j - finiteMean ℝ fun l ↦ mean (z l) j)) := by
    ext z
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply,
      PiLp.sub_apply, smul_eq_mul, hbar_coord]
  rw [hT_entry, integral_add hw_pi (hb_pi.const_mul _), hwithin_eq, integral_const_mul,
    integral_vector_between_entry ν κ hLp hD i j, covMatrix_apply, hcov_map,
    Kernel.covariance_comp κ (memLp_vector_coord hLp i) (memLp_vector_coord hLp j)]
  ring

/-- Pairwise expectation of centered coordinate products across imputations `(d₁, d₂)`. -/
private theorem integral_vector_pair_mul_entry {ι : Type*} [Fintype ι]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (i j : ι) (d₁ d₂ : Fin D) :
    ∫ z : Fin D → M,
        ((∫ x, x ∂κ (z d₁)) i - (∫ x, x ∂(κ ∘ₘ ν)) i) *
          ((∫ x, x ∂κ (z d₂)) j - (∫ x, x ∂(κ ∘ₘ ν)) j)
        ∂(Measure.pi fun _ : Fin D ↦ ν) =
      if d₂ = d₁ then covMatrix (ν.map fun z ↦ ∫ x, x ∂κ z) i j else 0 := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set mean : M → EuclideanSpace ℝ ι := fun z ↦ ∫ x, x ∂κ z
  set m₀ : EuclideanSpace ℝ ι := ∫ x, x ∂(κ ∘ₘ ν)
  obtain ⟨hmean_ae, hmean_Lp, _⟩ := memLp_vector_mean ν κ hLp
  have hproj : ∀ a : ι, Measurable fun x : EuclideanSpace ℝ ι ↦ x a :=
    fun a ↦ (EuclideanSpace.proj (𝕜 := ℝ) a).measurable
  have hm_meas : Measurable mean :=
    (measurable_id.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hm₀_mean : ∀ a : ι, (∫ m, mean m a ∂ν) = m₀ a := fun a ↦ by
    rw [integral_congr_ae (hmean_ae a),
      ← Measure.integral_bind κ.aemeasurable ((memLp_vector_coord hLp a).integrable one_le_two)]
    exact (EuclideanSpace.proj a).integral_comp_comm (hLp.integrable one_le_two)
  have hX : ∀ a : ι, ∀ d : Fin D, MemLp (fun z : Fin D → M ↦ mean (z d) a - m₀ a) 2 π :=
    fun a d ↦ ((hmean_Lp a).sub (memLp_const _)).comp_measurePreserving
      (measurePreserving_eval _ d)
  split_ifs with heq
  · rw [heq, covMatrix_apply, covariance_map (hproj i).aestronglyMeasurable
      (hproj j).aestronglyMeasurable hm_meas.aemeasurable,
      integral_pi_eval (g := fun m ↦ (mean m i - m₀ i) * (mean m j - m₀ j)) d₁
        ((((hproj i).comp hm_meas).sub measurable_const).mul
          (((hproj j).comp hm_meas).sub measurable_const)).aestronglyMeasurable]
    simp [covariance, hm₀_mean]
  · have hi : IndepFun (Function.eval d₁) (Function.eval d₂) π :=
      (iIndepFun_pi (μ := fun _ : Fin D ↦ ν) fun _ ↦ aemeasurable_id).indepFun (Ne.symm heq)
    have hci : IndepFun (fun z : Fin D → M ↦ mean (z d₁) i - m₀ i)
        (fun z : Fin D → M ↦ mean (z d₂) j - m₀ j) π :=
      hi.comp (((hproj i).comp hm_meas).sub measurable_const)
        (((hproj j).comp hm_meas).sub measurable_const)
    have hmean0 : (∫ z : Fin D → M, mean (z d₁) i - m₀ i ∂π) = 0 := by
      rw [integral_pi_eval (g := fun m ↦ mean m i - m₀ i) d₁
        (((hproj i).comp hm_meas).sub measurable_const).aestronglyMeasurable,
        integral_sub ((hmean_Lp i).integrable one_le_two) (integrable_const _)]
      simp [mean, hm₀_mean]
    exact (hci.integral_mul_eq_mul_integral ((hX i d₁).aestronglyMeasurable)
      ((hX j d₂).aestronglyMeasurable)).trans (by rw [hmean0, zero_mul])

/-- Cross-covariance of the pooled vector mean `bar` about `m₀ = ∫ x, x ∂(κ ∘ₘ ν)`. -/
private theorem integral_vector_bar_cov_entry {ι : Type*} [Fintype ι]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) (i j : ι) :
    ∫ z : Fin D → M,
        (((D : ℝ)⁻¹ • ∑ d, ∫ x, x ∂κ (z d)) i - (∫ x, x ∂(κ ∘ₘ ν)) i) *
          (((D : ℝ)⁻¹ • ∑ d, ∫ x, x ∂κ (z d)) j - (∫ x, x ∂(κ ∘ₘ ν)) j)
        ∂(Measure.pi fun _ : Fin D ↦ ν) =
      (D : ℝ)⁻¹ * covMatrix (ν.map fun z ↦ ∫ x, x ∂κ z) i j := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set mean : M → EuclideanSpace ℝ ι := fun z ↦ ∫ x, x ∂κ z
  set m₀ : EuclideanSpace ℝ ι := ∫ x, x ∂(κ ∘ₘ ν)
  obtain ⟨_, hmean_Lp, _⟩ := memLp_vector_mean ν κ hLp
  have hd0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD
  have hX : ∀ a : ι, ∀ d : Fin D, MemLp (fun z : Fin D → M ↦ mean (z d) a - m₀ a) 2 π :=
    fun a d ↦ ((hmean_Lp a).sub (memLp_const _)).comp_measurePreserving
      (measurePreserving_eval _ d)
  have hbi : ∀ z : Fin D → M, ∀ a : ι,
      ((D : ℝ)⁻¹ • ∑ d, mean (z d)) a - m₀ a = (D : ℝ)⁻¹ * ∑ d, (mean (z d) a - m₀ a) := by
    intro z a
    have hc : ((D : ℝ)⁻¹ • ∑ d, mean (z d)) a = (D : ℝ)⁻¹ * ∑ d, mean (z d) a := by simp
    rw [hc, sum_sub_distrib, mul_sub, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      inv_mul_cancel_left₀ hd0]
  have hrewrite : (fun z : Fin D → M ↦
      (((D : ℝ)⁻¹ • ∑ d, mean (z d)) i - m₀ i) * (((D : ℝ)⁻¹ • ∑ d, mean (z d)) j - m₀ j)) =
      fun z ↦ (D : ℝ)⁻¹ ^ 2 * ∑ d₁, ∑ d₂, (mean (z d₁) i - m₀ i) * (mean (z d₂) j - m₀ j) := by
    ext z; rw [hbi z i, hbi z j, ← sum_mul_sum]; ring
  rw [hrewrite, integral_const_mul,
    integral_finsetSum (f := fun d₁ (z : Fin D → M) ↦
      ∑ d₂, (mean (z d₁) i - m₀ i) * (mean (z d₂) j - m₀ j)) univ
      fun d₁ _ ↦ integrable_finsetSum _ fun d₂ _ ↦ (hX i d₁).integrable_mul (hX j d₂)]
  have hrow : ∀ d₁ : Fin D, ∫ z, ∑ d₂, (mean (z d₁) i - m₀ i) * (mean (z d₂) j - m₀ j) ∂π =
      covMatrix (ν.map mean) i j := by
    intro d₁
    rw [integral_finsetSum (f := fun d₂ (z : Fin D → M) ↦
      (mean (z d₁) i - m₀ i) * (mean (z d₂) j - m₀ j)) univ
      fun d₂ _ ↦ (hX i d₁).integrable_mul (hX j d₂)]
    dsimp only [π, mean, m₀]
    simp_rw [integral_vector_pair_mul_entry ν κ hLp i j d₁]
    simp
  simp_rw [hrow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Coordinatewise expectation of `(p.1 - bar p.2) i * (p.1 - bar p.2) j`. -/
private theorem integral_sub_miMean_mul_vector_entry {ι : Type*} [Fintype ι]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (hLp : MemLp id 2 (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) (i j : ι) :
    ∫ p : EuclideanSpace ℝ ι × (Fin D → M),
        (p.1 - (D : ℝ)⁻¹ • ∑ d, ∫ x, x ∂κ (p.2 d)) i *
          (p.1 - (D : ℝ)⁻¹ • ∑ d, ∫ x, x ∂κ (p.2 d)) j
        ∂((κ ∘ₘ ν).prod (Measure.pi fun _ : Fin D ↦ ν)) =
      covMatrix (κ ∘ₘ ν) i j + (D : ℝ)⁻¹ * covMatrix (ν.map fun z ↦ ∫ x, x ∂κ z) i j := by
  set π := Measure.pi fun _ : Fin D ↦ ν
  set mean : M → EuclideanSpace ℝ ι := fun z ↦ ∫ x, x ∂κ z
  set bar : (Fin D → M) → EuclideanSpace ℝ ι := fun z ↦ (D : ℝ)⁻¹ • ∑ d, mean (z d)
  set m₀ : EuclideanSpace ℝ ι := ∫ x, x ∂(κ ∘ₘ ν)
  obtain ⟨_, hmean_Lp, _⟩ := memLp_vector_mean ν κ hLp
  have hm₀_coord : ∀ a : ι, m₀ a = ∫ x, x a ∂(κ ∘ₘ ν) := fun a ↦ by
    simpa [m₀] using ((EuclideanSpace.proj a).integral_comp_comm (hLp.integrable one_le_two)).symm
  have hbar_Lp : ∀ a : ι, MemLp (fun z : Fin D → M ↦ bar z a - m₀ a) 2 π := fun a ↦ by
    have hc : ∀ z : Fin D → M, (D : ℝ)⁻¹ * (∑ d, mean (z d) a) = bar z a := fun z ↦ by simp [bar]
    exact (((memLp_finsetSum univ fun d _ ↦
      (hmean_Lp a).comp_measurePreserving (measurePreserving_eval _ d)).const_mul _).ae_eq
      (.of_forall hc)).sub (memLp_const _)
  have hθ_Lp : ∀ a : ι, MemLp (fun x : EuclideanSpace ℝ ι ↦ x a - m₀ a) 2 (κ ∘ₘ ν) :=
    fun a ↦ (memLp_vector_coord hLp a).sub (memLp_const _)
  have hm0 : ∀ a : ι, ∫ x : EuclideanSpace ℝ ι, x a - m₀ a ∂(κ ∘ₘ ν) = 0 := fun a ↦ by
    rw [integral_sub ((memLp_vector_coord hLp a).integrable one_le_two) (integrable_const _)]
    simp [hm₀_coord]
  have hshift : (fun p : EuclideanSpace ℝ ι × (Fin D → M) ↦
      (p.1 - bar p.2) i * (p.1 - bar p.2) j) =
      fun p ↦ ((p.1 i - m₀ i) - (bar p.2 i - m₀ i)) * ((p.1 j - m₀ j) - (bar p.2 j - m₀ j)) := by
    ext p; simp only [PiLp.sub_apply]; ring
  rw [hshift, integral_prod_sub_mul_sub (hθ_Lp i) (hθ_Lp j) (hbar_Lp i) (hbar_Lp j)
    (hm0 i) (hm0 j), covMatrix_apply, covariance, ← hm₀_coord i, ← hm₀_coord j]
  exact congrArg (_ + ·) (integral_vector_bar_cov_entry ν κ hLp hD i j)

/-- **Rubin's combining rules for a vector estimand.** For a complete-data posterior Markov kernel
`κ : Kernel M (EuclideanSpace ℝ ι)` whose mixture `κ ∘ₘ ν` has a finite second moment and `2 ≤ D`
i.i.d. imputations from `ν` independent of `θ ∼ κ ∘ₘ ν`, the pooled mean `bar` has expectation
`∫ x, x ∂(κ ∘ₘ ν)`, and both Rubin's total covariance matrix `T` and the outer-product discrepancy
`(θ - bar) ⊗ (θ - bar)` have entrywise expectation
`covMatrix (κ ∘ₘ ν) + D⁻¹ • covMatrix (ν.map mean)`. -/
theorem integral_rubinTotalVariance_vector {ι : Type*} [Fintype ι]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (κ : Kernel M (EuclideanSpace ℝ ι)) [IsMarkovKernel κ]
    (h2 : Integrable (fun x ↦ ‖x‖ ^ 2) (κ ∘ₘ ν)) {D : ℕ} (hD : 2 ≤ D) :
    let mean : M → EuclideanSpace ℝ ι := fun z ↦ ∫ x, x ∂κ z
    let bar : (Fin D → M) → EuclideanSpace ℝ ι := fun z ↦ (D : ℝ)⁻¹ • ∑ d, mean (z d)
    let T : (Fin D → M) → Matrix ι ι ℝ := fun z ↦
      (D : ℝ)⁻¹ • ∑ d, covMatrix (κ (z d)) + (1 + (D : ℝ)⁻¹) • (((D : ℝ) - 1)⁻¹ •
        ∑ d, Matrix.of fun i j ↦ (mean (z d) - bar z) i * (mean (z d) - bar z) j)
    ∫ z, bar z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ x, x ∂(κ ∘ₘ ν) ∧
      (∀ i j, ∫ z, T z i j ∂(Measure.pi fun _ : Fin D ↦ ν) =
        covMatrix (κ ∘ₘ ν) i j + (D : ℝ)⁻¹ * covMatrix (ν.map mean) i j) ∧
      ∀ i j, ∫ p, (p.1 - bar p.2) i * (p.1 - bar p.2) j
          ∂((κ ∘ₘ ν).prod (Measure.pi fun _ : Fin D ↦ ν)) =
        covMatrix (κ ∘ₘ ν) i j + (D : ℝ)⁻¹ * covMatrix (ν.map mean) i j := by
  intro mean bar T
  set π := Measure.pi fun _ : Fin D ↦ ν
  have hLp : MemLp id 2 (κ ∘ₘ ν) := (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2 h2
  have hm_int : Integrable mean ν :=
    Measure.integrable_integral_bind κ.measurable (hLp.integrable one_le_two)
  have hd_int : ∀ d : Fin D, Integrable (fun z : Fin D → M ↦ mean (z d)) π := fun d ↦
    memLp_one_iff_integrable.1 <|
      (memLp_one_iff_integrable.2 hm_int).comp_measurePreserving (measurePreserving_eval _ d)
  refine ⟨?_, fun i j ↦ integral_rubinTotalCovariance_entry ν κ hLp hD i j,
    fun i j ↦ integral_sub_miMean_mul_vector_entry ν κ hLp (by omega) i j⟩
  have hd0 : (D : ℝ) ≠ 0 := by positivity
  have hd_eq : ∀ d : Fin D, ∫ z, mean (z d) ∂π = ∫ m, mean m ∂ν := fun d ↦
    integral_pi_eval d hm_int.aestronglyMeasurable
  simp only [bar]
  rw [integral_smul, integral_finsetSum _ fun d _ ↦ hd_int d]
  simp_rw [hd_eq, sum_const, card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hd0, one_smul]
  exact (Measure.integral_bind κ.aemeasurable (hLp.integrable one_le_two)).symm

end Vector

end TauCeti
