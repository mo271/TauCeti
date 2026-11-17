/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Probability.Moments.Basic

/-!
# Moment determinacy of finite measures with finite exponential moments

A finite measure on `ℝ` whose exponential moments are finite in a neighbourhood of the origin is
determined, among finite measures that also have finite exponential moments near the origin, by
its sequence of polynomial moments `∫ xⁿ dμ`.  This is the analytic engine behind
completeness of polynomials in weighted `L²` spaces: the `ae_eq_zero_of_forall_moment_eq_zero`
lemmas of `TauCeti.Probability.Moments.VanishingMoments` rest on the fact that "vanishing moments"
pins a distribution down, which for finite measures is exactly the determinacy result proved here.

The mechanism: the (complex) moment-generating function is analytic on a strip around the
imaginary axis, and its Taylor coefficients at `0` are the moments, so matching moments force the
two functions to agree, hence the characteristic functions agree and the measures coincide.  The
proof stays inside Mathlib's `ProbabilityTheory.complexMGF` /
`MeasureTheory.charFun` API:

* `ProbabilityTheory.analyticAt_complexMGF` and `analyticOnNhd_complexMGF` supply the analyticity
  on the strip `{z | z.re ∈ interior (integrableExpSet id μ)}`;
* `ProbabilityTheory.iteratedDeriv_complexMGF` identifies the `n`-th derivative at `0` with the
  `n`-th complex moment;
* the identity principle (`analyticOrderAt_eq_top`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) propagates equality from `0` to the whole
  strip, in particular to the imaginary axis;
* `ProbabilityTheory.complexMGF_id_mul_I` turns the imaginary-axis values into `charFun`, and
  `MeasureTheory.Measure.ext_of_charFun` concludes.

Both routes share one strip-propagation core, adapted from Mathlib's
`ProbabilityTheory.eqOn_complexMGF_of_mgf'` (`Mathlib/Probability/Moments/ComplexMGF.lean`): it
reuses the same analyticity strip and the same
`convex_integrableExpSet.interior.…linear_preimage Complex.reLm |>.isPreconnected`
identity-principle idiom.  That file's `## TODO` note ("once we know that equal `mgf` implies equal
distributions …")
records the determinacy fact as an open gap in Mathlib; the results here complete it for finite
measures, both via the polynomial-moment route and directly from the moment-generating function.

This file also records determinacy directly from the moment-generating function: a measure on `ℝ`
with finite exponential moments near `0` is determined among finite measures by the values its
moment-generating function takes on an arbitrarily small neighbourhood of the origin.

## Main declarations

* `TauCeti.charFun_eq_of_forall_integral_pow_eq`: matching moments (and finite exponential moments
  near `0`) give equal characteristic functions.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq`: matching moments determine a finite measure on
  `ℝ` with exponential moments near `0`, among such measures.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp`: the same conclusion from
  the exponential-moment hypothesis `∃ a > 0, Integrable (fun x => exp (a * |x|)) μ`,
  which already puts `0` in the interior of the integrability strip.  This is the form the
  completeness argument consumes: the hypothesis holds for Gaussian decay and automatically for
  compactly supported measures.
* `TauCeti.charFun_eq_of_mgf_eq` and `TauCeti.Measure.ext_of_mgf`: the same two conclusions from an
  equality of moment-generating functions near `0` instead of an equality of moments.
* `TauCeti.charFun_eq_of_integral_exp_inner_eq` and `TauCeti.measure_eq_of_integral_exp_inner_eq`:
  multivariate Laplace determinacy on inner product spaces, obtained by applying the real
  determinacy theorem to one-dimensional projections `t ↦ ⟪t, v⟫`.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology

variable {μ ν : Measure ℝ}

/-! ### The shared strip-propagation core -/

/-- **The identity principle on the strip shared by two measures with exponential moments near
`0`.** Complex moment-generating functions that agree frequently near `0` agree on the whole
shared strip, in particular on the imaginary axis, where they are the characteristic functions. -/
private theorem charFun_eq_of_frequently_complexMGF_eq
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (heq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF id μ z = complexMGF id ν z) :
    charFun μ = charFun ν := by
  set U : Set ℂ :=
    Complex.reLm ⁻¹' (interior (integrableExpSet id μ) ∩ interior (integrableExpSet id ν))
    with hUdef
  have hUconn : IsPreconnected U :=
    ((convex_integrableExpSet.interior.inter
      convex_integrableExpSet.interior).linear_preimage Complex.reLm).isPreconnected
  have hAμU : AnalyticOnNhd ℂ (complexMGF id μ) U :=
    analyticOnNhd_complexMGF.mono fun _ hz => hz.1
  have hAνU : AnalyticOnNhd ℂ (complexMGF id ν) U :=
    analyticOnNhd_complexMGF.mono fun _ hz => hz.2
  -- The imaginary axis lies in the strip, and there the values are the characteristic functions.
  have hmemU : ∀ z : ℂ, z.re = 0 → z ∈ U := by
    intro z hz
    have hz' : reLm z = 0 := by rw [Complex.reLm_coe]; exact hz
    simp only [hUdef, Set.mem_preimage, Set.mem_inter_iff, hz']
    exact ⟨hμ, hν⟩
  have hEqU : Set.EqOn (complexMGF id μ) (complexMGF id ν) U :=
    hAμU.eqOn_of_preconnected_of_frequently_eq hAνU hUconn (hmemU 0 (by simp)) heq
  ext t
  have h := hEqU (hmemU ((t : ℂ) * I) (by simp))
  rwa [complexMGF_id_mul_I, complexMGF_id_mul_I] at h

/-! ### Determinacy from the moment-generating function -/

/-- **Determinacy at the level of characteristic functions, from the moment-generating function.**
Two measures on `ℝ`, one with finite exponential moments near `0` and the other finite, whose
moment-generating functions agree on a neighbourhood of `0`, have the same characteristic
function. -/
theorem charFun_eq_of_mgf_eq [IsFiniteMeasure ν]
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ)) (hmgf : mgf id μ =ᶠ[𝓝 0] mgf id ν) :
    charFun μ = charFun ν := by
  have _ := isFiniteMeasure_of_zero_mem_integrableExpSet (interior_subset hμ)
  have hzero : μ = 0 ↔ ν = 0 := by
    have h0 : μ.real Set.univ = ν.real Set.univ := by
      simpa only [mgf_zero'] using hmgf.self_of_nhds
    rw [← Measure.measure_univ_eq_zero, ← Measure.measure_univ_eq_zero,
      ← measureReal_eq_zero_iff, ← measureReal_eq_zero_iff, h0]
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [hzero.mp rfl]
  have : NeZero μ := ⟨hμ0⟩
  have : NeZero ν := ⟨fun h => hμ0 (hzero.mpr h)⟩
  -- Where the two agree, `ν` inherits the exponential moments of `μ`, both being positive there.
  have hν : (0 : ℝ) ∈ interior (integrableExpSet id ν) := by
    refine mem_interior_iff_mem_nhds.mpr ?_
    filter_upwards [isOpen_interior.mem_nhds hμ, hmgf] with t ht hteq
    exact mgf_pos_iff.mp
      (hteq ▸ mgf_pos_iff.mpr (integrable_of_mem_integrableExpSet (interior_subset ht)))
  -- The two complex moment-generating functions agree at the real points near `0`.
  have hofReal : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  refine charFun_eq_of_frequently_complexMGF_eq hμ hν (hofReal.frequently ?_)
  refine Filter.Eventually.frequently ?_
  filter_upwards [hmgf.filter_mono nhdsWithin_le_nhds] with x hx
  rw [complexMGF_ofReal, complexMGF_ofReal, hx]

/-- **A finite measure on `ℝ` with finite exponential moments near `0` is determined by its
moment-generating function near `0`.** This is the determinacy statement recorded as a `TODO` in
Mathlib's `Mathlib/Probability/Moments/ComplexMGF.lean`.

The strip hypothesis is asked of one measure only: matching the moment-generating functions near
`0` matches the two total masses, and forces the second measure to have the exponential moments of
the first at every rate near `0`. -/
theorem Measure.ext_of_mgf [IsFiniteMeasure ν]
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ)) (hmgf : mgf id μ =ᶠ[𝓝 0] mgf id ν) :
    μ = ν := by
  have _ := isFiniteMeasure_of_zero_mem_integrableExpSet (interior_subset hμ)
  exact Measure.ext_of_charFun (charFun_eq_of_mgf_eq hμ hmgf)

/-! ### Determinacy from the moments -/

/-- The `n`-th derivative at `0` of the complex moment-generating function of `μ` is the `n`-th
complex moment `↑(∫ xⁿ dμ)`.  Immediate from `iteratedDeriv_complexMGF` at `z = 0`, where the
exponential factor is `1`. -/
private lemma iteratedDeriv_complexMGF_id_zero
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ)) (n : ℕ) :
    iteratedDeriv n (complexMGF id μ) 0 = ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
  have hz : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by simpa using hμ
  rw [iteratedDeriv_complexMGF (z := 0) hz n]
  have hpow : ∀ x : ℝ, ((x : ℂ)) ^ n * Complex.exp (0 * (x : ℂ)) = (((x ^ n : ℝ)) : ℂ) := by
    intro x
    rw [zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring
  simp only [id_eq, hpow]
  exact integral_ofReal

/-- **Equal polynomial moments make the moment-generating functions agree near `0`.** If both
measures have `0` in the interior of their exponential-moment set and all moments `∫ xⁿ` agree,
then their complex moment-generating functions coincide on a neighbourhood of `0`. -/
private theorem complexMGF_eventuallyEq_of_forall_integral_pow_eq
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    complexMGF id μ =ᶠ[𝓝 0] complexMGF id ν := by
  have hAμ : AnalyticAt ℂ (complexMGF id μ) 0 := analyticAt_complexMGF (by simpa using hμ)
  have hAν : AnalyticAt ℂ (complexMGF id ν) 0 := analyticAt_complexMGF (by simpa using hν)
  -- the difference has every iterated derivative zero at `0`, so it vanishes near `0`
  have hiter : ∀ i, iteratedDeriv i (fun z => complexMGF id μ z - complexMGF id ν z) 0 = 0 := by
    intro i
    rw [iteratedDeriv_fun_sub hAμ.contDiffAt hAν.contDiffAt,
      iteratedDeriv_complexMGF_id_zero hμ i, iteratedDeriv_complexMGF_id_zero hν i, hmom i,
      sub_self]
  have hsub : AnalyticAt ℂ (fun z => complexMGF id μ z - complexMGF id ν z) 0 := hAμ.sub hAν
  have hord : analyticOrderAt (fun z => complexMGF id μ z - complexMGF id ν z) 0 = ⊤ :=
    ENat.eq_top_iff_forall_ge.mpr fun m =>
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub).mpr fun i _ => hiter i
  filter_upwards [analyticOrderAt_eq_top.mp hord] with z hz using sub_eq_zero.mp hz

/-- **Moment determinacy at the level of characteristic functions.** If two measures on `ℝ` have
finite exponential moments near `0` (so their complex moment-generating functions are analytic on a
strip about the imaginary axis) and agree on every polynomial moment `∫ xⁿ`, then their
characteristic functions coincide. -/
theorem charFun_eq_of_forall_integral_pow_eq (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν)) (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    charFun μ = charFun ν := by
  have hEqNear : complexMGF id μ =ᶠ[𝓝 0] complexMGF id ν :=
    complexMGF_eventuallyEq_of_forall_integral_pow_eq hμ hν hmom
  exact charFun_eq_of_frequently_complexMGF_eq hμ hν
    (hEqNear.filter_mono nhdsWithin_le_nhds).frequently

/-- **Moment determinacy for finite measures on `ℝ`.** A finite measure on `ℝ` with finite
exponential moments near `0` is determined by its polynomial moments `∫ xⁿ`, among finite measures
that also have exponential moments near `0` (the hypothesis `hν`).  Combines
`charFun_eq_of_forall_integral_pow_eq` with `MeasureTheory.Measure.ext_of_charFun`.
Finiteness follows from the exponential-moment hypothesis at zero. -/
theorem Measure.ext_of_forall_integral_pow_eq
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν)) (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    μ = ν := by
  have := isFiniteMeasure_of_zero_mem_integrableExpSet (interior_subset hμ)
  have := isFiniteMeasure_of_zero_mem_integrableExpSet (interior_subset hν)
  exact Measure.ext_of_charFun (charFun_eq_of_forall_integral_pow_eq hμ hν hmom)

/-- If `∫ e^{a|x|} dμ` is finite for a single `a > 0`, then `0` lies in the interior of the
integrability set `integrableExpSet id μ`: for `|t| ≤ a` the exponential `e^{tx}` is dominated by
`e^{a|x|}`, so the open interval `(-a, a)` is contained in `integrableExpSet id μ`. -/
private lemma zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp
    (h : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) μ) :
    (0 : ℝ) ∈ interior (integrableExpSet id μ) := by
  obtain ⟨a, ha, hint⟩ := h
  refine mem_interior.mpr ⟨Set.Ioo (-a) a, ?_, isOpen_Ioo, Set.mem_Ioo.mpr ⟨neg_lt_zero.mpr ha, ha⟩⟩
  intro t ht
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq]
  refine hint.mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc t * x ≤ |t * x| := le_abs_self _
    _ = |t| * |x| := abs_mul t x
    _ ≤ a * |x| := mul_le_mul_of_nonneg_right (abs_lt.mpr ht).le (abs_nonneg x)

/-- **Moment determinacy, exponential-moment form.** A finite measure on `ℝ` for which some
exponential moment `∫ e^{a|x|} dμ` with `a > 0` is finite is determined by its polynomial moments,
among finite measures for which such an exponential moment is also finite (the hypothesis `hν`).
This is the form the completeness argument consumes: the hypothesis holds for Gaussian decay and
automatically for compactly supported measures. -/
theorem Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp
    (hμ : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) μ)
    (hν : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) ν)
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    μ = ν :=
  Measure.ext_of_forall_integral_pow_eq
    (zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp hμ)
    (zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp hν) hmom

/-! ### Multivariate Laplace determinacy -/

section Multivariate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- Pointwise characteristic-function equality for a nonzero measure `μ₁` and a finite measure `μ₂`
whose Laplace transforms agree on a ball around `0`, by one-dimensional projection along `v`. -/
private lemma charFun_apply_eq_of_integral_exp_inner_eq {μ₁ μ₂ : Measure E} [IsFiniteMeasure μ₂]
    (hμ₁ : μ₁ ≠ 0) {r : ℝ} (hr : 0 < r)
    (hint : ∀ u : E, ‖u‖ < r → Integrable (fun t ↦ Real.exp (inner ℝ u t)) μ₁)
    (heq : ∀ u : E, ‖u‖ < r →
      ∫ t, Real.exp (inner ℝ u t) ∂μ₁ = ∫ t, Real.exp (inner ℝ u t) ∂μ₂) (v : E) :
    charFun μ₁ v = charFun μ₂ v := by
  let L : E → ℝ := fun t ↦ inner ℝ t v
  set δ : ℝ := r / (‖v‖ + 1)
  have hδ : 0 < δ := div_pos hr (by positivity)
  have hnorm : ∀ s ∈ Set.Ioo (-δ) δ, ‖s • v‖ < r := fun s hs ↦ by
    rw [norm_smul, Real.norm_eq_abs]
    calc |s| * ‖v‖ ≤ |s| * (‖v‖ + 1) := by gcongr; linarith
      _ < δ * (‖v‖ + 1) := by gcongr; exact abs_lt.mpr hs
      _ = r := div_mul_cancel₀ r (by positivity)
  have hinner : ∀ s t, s * L t = inner ℝ (s • v) t := fun s t ↦ by
    simp [L, inner_smul_left, real_inner_comm]
  have hs₀ : δ / 2 ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
  have hint₁ := hint ((δ / 2) • v) (hnorm _ hs₀)
  have hL₁ : AEMeasurable L μ₁ :=
    Real.aemeasurable_of_aemeasurable_exp_mul (t := δ / 2) (by positivity)
      (by simpa only [hinner] using hint₁.aemeasurable)
  have hL₂ : AEMeasurable L μ₂ := by
    have : NeZero μ₁ := ⟨hμ₁⟩
    have hpos : 0 < ∫ t, Real.exp (inner ℝ ((δ / 2) • v) t) ∂μ₂ :=
      heq _ (hnorm _ hs₀) ▸ integral_exp_pos hint₁
    have hint₂ : Integrable (fun t ↦ Real.exp (inner ℝ ((δ / 2) • v) t)) μ₂ :=
      by_contra fun hnot ↦ hpos.ne' (integral_undef hnot)
    exact Real.aemeasurable_of_aemeasurable_exp_mul (t := δ / 2) (by positivity)
      (by simpa only [hinner] using hint₂.aemeasurable)
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (μ₁.map L)) := by
    refine mem_interior.mpr ⟨Set.Ioo (-δ) δ, fun s hs ↦ ?_, isOpen_Ioo,
      Set.mem_Ioo.mpr ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
    simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq]
    rw [integrable_map_measure (by fun_prop) hL₁]
    simpa only [Function.comp_def, hinner] using hint (s • v) (hnorm s hs)
  have hmgf : mgf id (μ₁.map L) =ᶠ[𝓝 0] mgf id (μ₂.map L) := by
    filter_upwards [isOpen_Ioo.mem_nhds (Set.mem_Ioo.mpr ⟨neg_lt_zero.mpr hδ, hδ⟩)] with s hs
    have hcont : Continuous fun y : ℝ ↦ Real.exp (s * y) := by fun_prop
    simp only [mgf, id_eq, integral_map hL₁ hcont.aestronglyMeasurable,
      integral_map hL₂ hcont.aestronglyMeasurable, hinner]
    exact heq (s • v) (hnorm s hs)
  have hcf := congrFun (charFun_eq_of_mgf_eq h0 hmgf) 1
  have hcf_map : ∀ {μ : Measure E}, AEMeasurable L μ → charFun (μ.map L) 1 = charFun μ v :=
    fun hL ↦ by
      have hcont : Continuous fun y : ℝ ↦ cexp (↑y * I) := by fun_prop
      rw [charFun_apply_real, charFun_apply]
      simp only [Complex.ofReal_one, one_mul,
        integral_map hL hcont.aestronglyMeasurable, L]
  rwa [hcf_map hL₁, hcf_map hL₂] at hcf

/-- **Multivariate Laplace determinacy at the level of characteristic functions.** Two measures on
a real inner product space, the first with finite Laplace transform on a ball around `0`, whose
Laplace transforms agree on that ball, have the same characteristic function. -/
theorem charFun_eq_of_integral_exp_inner_eq {μ₁ μ₂ : Measure E} {r : ℝ} (hr : 0 < r)
    (hint : ∀ u : E, ‖u‖ < r → Integrable (fun t ↦ Real.exp (inner ℝ u t)) μ₁)
    (heq : ∀ u : E, ‖u‖ < r →
      ∫ t, Real.exp (inner ℝ u t) ∂μ₁ = ∫ t, Real.exp (inner ℝ u t) ∂μ₂) :
    charFun μ₁ = charFun μ₂ := by
  have hfin₁ : IsFiniteMeasure μ₁ := by
    have h0 : Integrable (fun _ : E ↦ (1 : ℝ)) μ₁ := by simpa using hint 0 (by simpa using hr)
    exact (integrable_const_iff.mp h0).resolve_left one_ne_zero
  by_cases hfin₂ : IsFiniteMeasure μ₂
  swap
  · have htop : μ₂ Set.univ = ⊤ := by
      by_contra h
      exact hfin₂ ⟨lt_top_iff_ne_top.mpr h⟩
    have hμ₂ : μ₂.real Set.univ = 0 := by simp [Measure.real, htop]
    have hμ₁ : μ₁ = 0 := by
      have h0 : μ₁.real Set.univ = 0 := by simpa [hμ₂] using heq 0 (by simpa using hr)
      rw [← Measure.measure_univ_eq_zero, ← measureReal_eq_zero_iff, h0]
    ext v
    rw [hμ₁, charFun_apply, integral_zero_measure]
    exact (norm_le_zero_iff.mp ((norm_charFun_le v).trans_eq hμ₂)).symm
  rcases eq_or_ne μ₁ 0 with rfl | hμ₁
  · have hμ₂ : μ₂ = 0 := by
      have h0 : (0 : ℝ) = μ₂.real Set.univ := by simpa using heq 0 (by simpa using hr)
      rw [← Measure.measure_univ_eq_zero, ← measureReal_eq_zero_iff, ← h0]
    rw [hμ₂]
  ext v
  exact charFun_apply_eq_of_integral_exp_inner_eq hμ₁ hr hint heq v

/-- **Multivariate Laplace determinacy.** Two measures on a complete second-countable real inner
product space, one with finite Laplace transform `u ↦ ∫ exp ⟪u, t⟫ dμ₁` on a ball around `0` and
the other finite, whose Laplace transforms agree on that ball, are equal.

Finiteness of `μ₁` follows automatically from integrability at `u = 0`. -/
theorem measure_eq_of_integral_exp_inner_eq [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E] {μ₁ μ₂ : Measure E} [IsFiniteMeasure μ₂] {r : ℝ} (hr : 0 < r)
    (hint : ∀ u : E, ‖u‖ < r → Integrable (fun t ↦ Real.exp (inner ℝ u t)) μ₁)
    (heq : ∀ u : E, ‖u‖ < r →
      ∫ t, Real.exp (inner ℝ u t) ∂μ₁ = ∫ t, Real.exp (inner ℝ u t) ∂μ₂) :
    μ₁ = μ₂ := by
  have hfin : IsFiniteMeasure μ₁ := by
    have h0 : Integrable (fun _ : E ↦ (1 : ℝ)) μ₁ := by
      simpa using hint 0 (by simpa using hr)
    exact (integrable_const_iff.mp h0).resolve_left one_ne_zero
  exact Measure.ext_of_charFun (charFun_eq_of_integral_exp_inner_eq hr hint heq)

end Multivariate

end TauCeti
