/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.Predictable.Basic

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Predictable versions of filtered Brownian motion

A Brownian motion adapted to a raw filtration need not itself be literally predictable:
its paths are only almost surely continuous. This file selects predictable modifications retaining
the native Brownian law and increment independence from the past in the original filtration,
without requiring completion or right continuity of that filtration.

With almost-surely continuous paths, `exists_isStronglyPredictable_isBrownianReal_indist`
produces a predictable Brownian version agreeing outside one common null set. Without any path
regularity hypothesis, `exists_isStronglyPredictable_ae_eq` produces a predictable modification of
any filtered pre-Brownian motion agreeing almost surely at each fixed time, via Borel-Cantelli
along dyadically thinned lagged step approximations.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Chapters 1–2.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- Every filtered pre-Brownian motion admits a strongly predictable modification on the same
raw filtration, agreeing almost surely at each fixed time, with no path-continuity, completeness,
or right-continuity assumptions. -/
theorem exists_isStronglyPredictable_ae_eq (hB : IsFilteredPreBrownianReal ℱ B P) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ W ∧
      IsFilteredPreBrownianReal ℱ W P ∧ ∀ t, W t =ᵐ[P] B t := by
  obtain ⟨τ, hτ_le, hτ_sub, hτ_pred⟩ := hB.adapted.stronglyAdapted.exists_predictable_seq_le
  let W : ℝ≥0 → Ω → ℝ := fun t ω ↦ limUnder atTop (fun k : ℕ ↦ B (τ (2 ^ k) t) ω)
  have hWpred : IsStronglyPredictable ℱ W := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact StronglyMeasurable.limUnder fun k ↦ hτ_pred (2 ^ k)
  have hae (t : ℝ≥0) : B t =ᵐ[P] W t := by
    let g (k : ℕ) (ω : Ω) : ℝ≥0∞ := ENNReal.ofReal ((B t ω - B (τ (2 ^ k) t) ω) ^ 2)
    have hg_meas (k : ℕ) : Measurable (g k) :=
      (((hB.adapted t).mono (ℱ.le t) le_rfl).sub
        ((hB.adapted _).mono (ℱ.le _) le_rfl)).pow_const 2 |>.ennreal_ofReal
    have hg_int (k : ℕ) : ∫⁻ ω, g k ω ∂P ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hB.integrable_pow_sub (τ (2 ^ k) t) t 2)
        (ae_of_all _ fun _ ↦ sq_nonneg _), hB.integral_sq_sub_of_le (hτ_le (2 ^ k) t)]
      calc ENNReal.ofReal ((t : ℝ) - τ (2 ^ k) t)
        _ ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) := ENNReal.ofReal_le_ofReal <|
          (hτ_sub (2 ^ k) t).trans <| by
            rw [inv_pow, one_div]
            exact inv_anti₀ (by positivity) (by norm_cast; omega)
        _ = (2⁻¹ : ℝ≥0∞) ^ k := by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos zero_lt_two,
            ENNReal.ofReal_ofNat]
    have htsum : ∫⁻ ω, ∑' k, g k ω ∂P ≠ ∞ := by
      rw [lintegral_tsum fun k ↦ (hg_meas k).aemeasurable]
      exact ((tsum_le_tsum hg_int).trans_eq ENNReal.tsum_geometric_two).trans_lt
        ENNReal.ofNat_lt_top |>.ne
    filter_upwards [ae_lt_top (by fun_prop) htsum] with ω hω
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne)
    have hsq : Tendsto (fun k ↦ (B t ω - B (τ (2 ^ k) t) ω) ^ 2) atTop (𝓝 0) := by
      simpa only [Function.comp_def, g, ENNReal.toReal_ofReal (sq_nonneg _),
        ENNReal.toReal_zero] using h0
    have hdist : Tendsto (fun k ↦ dist (B (τ (2 ^ k) t) ω) (B t ω)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.dist_eq, abs_sub_comm,
        Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    exact (tendsto_iff_dist_tendsto_zero.mpr hdist).limUnder_eq.symm
  exact ⟨W, hWpred, hB.congr hWpred.isStronglyProgressive.stronglyAdapted.adapted hae,
    fun t ↦ (hae t).symm⟩

/-- A filtered pre-Brownian motion with almost-surely continuous paths has a predictable
indistinguishable Brownian version on the same raw filtration. The selected version is still
adapted and has increments independent of the past, not merely the same marginal laws. -/
theorem exists_isStronglyPredictable_isBrownianReal_indist
    (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω)) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ W ∧ IsBrownianReal W P ∧
      IsFilteredPreBrownianReal ℱ W P ∧ W ≡ᵐ[P] B := by
  obtain ⟨W, hW, hcont, heq⟩ :=
    hB.adapted.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_continuous hc
  have hFW := hB.congr hW.isStronglyProgressive.stronglyAdapted.adapted heq.symm.ae_eq_eval
  exact ⟨W, hW, ⟨hFW.toIsPreBrownianReal, hcont⟩, hFW, heq⟩

end TauCeti.Probability.IsFilteredPreBrownianReal
