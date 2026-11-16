/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# Holomorphy and differentiation of dominated parametric integrals

Let `(α, μ)` be an arbitrary measure space, `V` a finite-dimensional complex normed space, and `E`
a complex normed space. Suppose `F : V → α → E` is a.e.-strongly measurable for parameters `q` in a
neighbourhood `s` of `p`, complex differentiable on `s` for a.e. `a`, and dominated on `s` by an
integrable function `bound : α → ℝ`: `‖F q a‖ ≤ bound a`.

Unlike real parametric differentiation (`hasFDerivAt_integral_of_dominated_of_fderiv_le`), no
separate bound or measurability hypothesis on the parameter derivative `fderiv ℂ (F · a)` is
required:
* Cauchy's estimate on balls (`TauCeti.norm_fderiv_le_of_forall_mem_ball_norm_le`) bounds
  `‖fderiv ℂ (F · a) q‖` uniformly on a smaller ball around `p` by a constant multiple of
  `bound a`;
* the directional derivatives `fderiv ℂ (F · a) p v` are a.e. limits of measurable difference
  quotients, and reconstructing the linear map in a finite basis makes `a ↦ fderiv ℂ (F · a) p`
  a.e.-strongly measurable without any topological assumption on `α`.

Applying this on every ball inside `interior s` shows that `q ↦ ∫ a, F q a ∂μ` is complex
differentiable near `p`, hence analytic at `p` by
`DifferentiableOn.analyticAt_of_finiteDimensional`.

## Main results

* `TauCeti.hasFDerivAt_integral_of_dominated_of_differentiableOn`: differentiation under the
  integral sign from an `L¹` bound on `F` alone.
* `TauCeti.hasDerivAt_integral_of_dominated_of_differentiableOn`: the one-variable `deriv` form.
* `TauCeti.analyticAt_integral_of_dominated`: analyticity at `p` of `q ↦ ∫ a, F q a ∂μ`.
* `TauCeti.analyticOnNhd_integral_of_dominated`: analyticity on an open set `U`.

## References

* S. Lang, *Complex Analysis*, 4th ed., Graduate Texts in Mathematics **103**, Springer, 1999,
  Chapter IV, §2.
-/

public section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti

section FiniteDimensional

variable {α V E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : V → α → E} {bound : α → ℝ} {s : Set V} {p : V}

/-- At a point `p` where `F q` is a.e.-strongly measurable for `q` near `p` and `F · a` is a.e.
complex differentiable, `a ↦ fderiv ℂ (F · a) p` is a.e.-strongly measurable. -/
private theorem aestronglyMeasurable_fderiv_of_eventually
    (hF_meas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (F q) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableAt ℂ (F · a) p) :
    AEStronglyMeasurable (fun a ↦ fderiv ℂ (F · a) p) μ := by
  have happly (v : V) : AEStronglyMeasurable (fun a ↦ fderiv ℂ (F · a) p v) μ := by
    have hshift : Tendsto (fun t : ℂ ↦ p + t • v) (𝓝[≠] 0) (𝓝 p) :=
      (((continuous_id.smul continuous_const).const_add p).tendsto' 0 p
        (by simp)).mono_left nhdsWithin_le_nhds
    refine aestronglyMeasurable_of_tendsto_ae_of_eventually (𝓝[≠] (0 : ℂ))
      (f := fun t a ↦ t⁻¹ • (F (p + t • v) a - F p a)) ?_ ?_
    · filter_upwards [hshift.eventually hF_meas] with t ht
      exact (ht.sub hF_meas.self_of_nhds).const_smul t⁻¹
    · filter_upwards [hdiff] with a ha
      simpa [Function.comp_def] using
        (ha.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ)
          (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p) (by simp)).tendsto_slope_zero
  let b := Module.finBasis ℂ V
  let coord (i : Fin (Module.finrank ℂ V)) : V →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap
  have hsum : (fun a ↦ fderiv ℂ (F · a) p) = fun a ↦
      ∑ i, ContinuousLinearMap.smulRightL ℂ V E (coord i) (fderiv ℂ (F · a) p (b i)) := by
    ext a w
    simp only [ContinuousLinearMap.smulRightL_apply_apply, sum_apply,
      ContinuousLinearMap.smulRight_apply, coord, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.proj_apply, Module.Basis.equivFunL_apply]
    rw [← Finset.sum_congr rfl fun i _ ↦ map_smul (fderiv ℂ (F · a) p) (b.repr w i) (b i),
      ← map_sum, b.sum_repr]
  rw [hsum]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
    (ContinuousLinearMap.smulRightL ℂ V E (coord i)).continuous.comp_aestronglyMeasurable
      (happly (b i))

/-- **Differentiation under the integral sign for a dominated holomorphic family.** If `F q` is
a.e.-strongly measurable for `q ∈ s` (with `s ∈ 𝓝 p`), `F · a` is complex differentiable on `s` for
a.e. `a`, and `‖F q a‖ ≤ bound a` on `s` for an integrable `bound`, then `q ↦ ∫ a, F q a ∂μ` has
Fréchet derivative `∫ a, fderiv ℂ (F · a) p ∂μ` at `p`, and that derivative integrand is integrable.
-/
theorem integrable_fderiv_and_hasFDerivAt_integral_of_dominated_of_differentiableOn (hs : s ∈ 𝓝 p)
    (hF_meas : ∀ q ∈ s, AEStronglyMeasurable (F q) μ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ a ∂μ, ∀ q ∈ s, ‖F q a‖ ≤ bound a)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) s) :
    Integrable (fun a ↦ fderiv ℂ (F · a) p) μ ∧
      HasFDerivAt (fun q ↦ ∫ a, F q a ∂μ) (∫ a, fderiv ℂ (F · a) p ∂μ) p := by
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.1 hs
  have hr : 0 < R / 2 := half_pos hR
  have hsub : ∀ q ∈ ball p (R / 2), ball q (R / 2) ⊆ s := fun q hq ↦
    (ball_subset_ball' (by linarith [mem_ball.1 hq])).trans hRs
  have hp_mem : p ∈ s := mem_of_mem_nhds hs
  have hFp_int : Integrable (F p) μ :=
    hbound_int.mono' (hF_meas p hp_mem) (hbound.mono fun a ha ↦ ha p hp_mem)
  have hmeas_nhds : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (F q) μ :=
    eventually_of_mem hs hF_meas
  have hdiff_ball : ∀ᵐ a ∂μ, ∀ q ∈ ball p R, DifferentiableAt ℂ (F · a) q :=
    hdiff.mono fun a ha q hq ↦ (ha.mono hRs).differentiableAt (isOpen_ball.mem_nhds hq)
  have hF'_meas : AEStronglyMeasurable (fun a ↦ fderiv ℂ (F · a) p) μ :=
    aestronglyMeasurable_fderiv_of_eventually hmeas_nhds
      (hdiff_ball.mono fun a ha ↦ ha p (mem_ball_self hR))
  have hcauchy : ∀ᵐ a ∂μ, ∀ q ∈ ball p (R / 2), ‖fderiv ℂ (F · a) q‖ ≤ 2 * bound a / (R / 2) := by
    filter_upwards [hdiff, hbound] with a ha_diff ha_bound q hq
    exact norm_fderiv_le_of_forall_mem_ball_norm_le (ha_diff.mono (hsub q hq)) hr
      fun y hy ↦ ha_bound y (hsub q hq hy)
  have hderiv_int : Integrable (fun a ↦ fderiv ℂ (F · a) p) μ :=
    ((hbound_int.const_mul 2).div_const (R / 2)).mono' hF'_meas
      (hcauchy.mono fun a ha ↦ ha p (mem_ball_self hr))
  refine ⟨hderiv_int, hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun q a ↦ fderiv ℂ (F · a) q) (bound := fun a ↦ 2 * bound a / (R / 2))
    (ball_mem_nhds p hr) hmeas_nhds hFp_int hF'_meas hcauchy
    ((hbound_int.const_mul 2).div_const (R / 2)) ?_⟩
  filter_upwards [hdiff_ball] with a ha q hq
  exact (ha q (ball_subset_ball (by linarith) hq)).hasFDerivAt

/-- **Differentiation under the integral sign for a dominated holomorphic family.** -/
theorem hasFDerivAt_integral_of_dominated_of_differentiableOn (hs : s ∈ 𝓝 p)
    (hF_meas : ∀ q ∈ s, AEStronglyMeasurable (F q) μ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ a ∂μ, ∀ q ∈ s, ‖F q a‖ ≤ bound a)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) s) :
    HasFDerivAt (fun q ↦ ∫ a, F q a ∂μ) (∫ a, fderiv ℂ (F · a) p ∂μ) p :=
  (integrable_fderiv_and_hasFDerivAt_integral_of_dominated_of_differentiableOn hs hF_meas
    hbound_int hbound hdiff).2

/-- **Analytic dependence of a dominated integral on a parameter.** If `F q` is a.e.-strongly
measurable on a neighbourhood `s` of `p` in a finite-dimensional complex normed space, `F · a` is
complex differentiable on `s` for a.e. `a`, and `‖F q a‖ ≤ bound a` on `s` for an integrable
`bound`, then `q ↦ ∫ a, F q a ∂μ` is analytic at `p`. -/
theorem analyticAt_integral_of_dominated (hs : s ∈ 𝓝 p)
    (hF_meas : ∀ q ∈ s, AEStronglyMeasurable (F q) μ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ a ∂μ, ∀ q ∈ s, ‖F q a‖ ≤ bound a)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) s) :
    AnalyticAt ℂ (fun q ↦ ∫ a, F q a ∂μ) p := by
  by_cases hE : CompleteSpace E; swap
  · simp only [integral_of_not_completeSpace hE]
    exact analyticAt_const
  refine DifferentiableOn.analyticAt_of_finiteDimensional (s := interior s) (fun q hq ↦ ?_)
    (interior_mem_nhds.2 hs)
  exact (hasFDerivAt_integral_of_dominated_of_differentiableOn (isOpen_interior.mem_nhds hq)
    (fun y hy ↦ hF_meas y (interior_subset hy)) hbound_int
    (hbound.mono fun a ha y hy ↦ ha y (interior_subset hy))
    (hdiff.mono fun a ha ↦ ha.mono interior_subset)).differentiableAt.differentiableWithinAt

/-- **Analytic dependence of a globally dominated integral on an open set.** -/
theorem analyticOnNhd_integral_of_dominated {U : Set V} (hU : IsOpen U)
    (hF_meas : ∀ q ∈ U, AEStronglyMeasurable (F q) μ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ a ∂μ, ∀ q ∈ U, ‖F q a‖ ≤ bound a)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) U) :
    AnalyticOnNhd ℂ (fun q ↦ ∫ a, F q a ∂μ) U :=
  fun _p hp ↦ analyticAt_integral_of_dominated (hU.mem_nhds hp) hF_meas hbound_int hbound hdiff

end FiniteDimensional

section OneVariable

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : ℂ → α → E} {bound : α → ℝ} {s : Set ℂ} {z₀ : ℂ}

/-- One-variable scalar `deriv` form of
`TauCeti.hasFDerivAt_integral_of_dominated_of_differentiableOn`. -/
theorem hasDerivAt_integral_of_dominated_of_differentiableOn (hs : s ∈ 𝓝 z₀)
    (hF_meas : ∀ z ∈ s, AEStronglyMeasurable (F z) μ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ a ∂μ, ∀ z ∈ s, ‖F z a‖ ≤ bound a)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) s) :
    HasDerivAt (fun z ↦ ∫ a, F z a ∂μ) (∫ a, deriv (F · a) z₀ ∂μ) z₀ := by
  obtain ⟨hint, hfderiv⟩ :=
    integrable_fderiv_and_hasFDerivAt_integral_of_dominated_of_differentiableOn hs hF_meas
      hbound_int hbound hdiff
  simpa [ContinuousLinearMap.integral_apply hint] using hfderiv.hasDerivAt

end OneVariable

end TauCeti
