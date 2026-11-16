/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.DensityEstimates
import TauCeti.Analysis.BoundedVariation.Dilation
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.Poincare
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentCone
import TauCeti.MeasureTheory.Covering.DensityTheorem
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.InnerHalfSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# De Giorgi's structure theorem for sets of locally finite perimeter

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` of dimension `n`,
and let `s ⊆ E` be a set of locally finite perimeter in `Ω` with reduced boundary
`∂*s = TauCeti.reducedBoundary μ Ω s` and measure-theoretic outer normal
`ν_s = TauCeti.outerNormal μ Ω s`. **De Giorgi's structure theorem** identifies the geometric and
measure-theoretic structure of `∂*s` and of the perimeter measure `|Dχ_s|`:

1. **Countable `(n - 1)`-rectifiability** (`TauCeti.countablyRectifiable_reducedBoundary`): `∂*s`
   is countably `(n - 1)`-rectifiable (`TauCeti.CountablyRectifiable (finrank ℝ E - 1)`).
2. **Identification of the perimeter measure**
   (`TauCeti.map_variationMeasure_volume_indicator_eq_restrict_reducedBoundary`,
   `TauCeti.map_variationMeasure_indicator_eq_smul_restrict_reducedBoundary`,
   `TauCeti.perimeter_volume_eq_euclideanHausdorffMeasure_reducedBoundary`): for Lebesgue measure,
   `|Dχ_s| = μHE[n - 1].restrict ∂*s`, and for any additive Haar measure `μ` it is scaled by
   `Measure.addHaarScalarFactor μ volume`. In particular `P(s; Ω) = Hⁿ⁻¹(∂*s)` whenever `s` has
   finite perimeter in `Ω`.
3. **Pointwise Hausdorff density one and approximate tangent hyperplanes**
   (`TauCeti.finrank_orthogonal_span_outerNormal`,
   `TauCeti.tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_div`,
   `TauCeti.tendsto_euclideanHausdorffMeasure_reducedBoundary_outside_cone_div`): at *every* point
   `x ∈ ∂*s`, `∂*s` has `(n - 1)`-dimensional Hausdorff density `1` and zero `(n - 1)`-dimensional
   density outside every cone around the orthogonal hyperplane `(ℝ ∙ ν_s x)ᗮ`, so `(ℝ ∙ ν_s x)ᗮ`
   is the approximate tangent `(n - 1)`-plane to `∂*s` at every point of `∂*s`.
4. **De Giorgi's Gauss–Green theorem**
   (`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal`,
   `TauCeti.setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal`): for every `C¹` vector
   field `φ` compactly supported in `Ω`,
   `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`.

All statements hold without dimension restrictions (`n = 0`, `n = 1`, and `n ≥ 2`). Because both
`|Dχ_s|` and `∂*s` vanish by convention when `s` does not have locally finite perimeter in `Ω`,
the rectifiability, measure-representation, density, and approximate-tangent identities hold
unconditionally for arbitrary `s : Set E`.

## Proof overview

* **Dimensions `n = 0` and `n = 1`.** In dimension zero no unit vector exists, so `∂*s = ∅`. In
  dimension one, pulling back along `t ↦ t • ν_s x` and testing Lebesgue points of `s` and `sᶜ`
  with `TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn` shows every point of `∂*s` carries
  perimeter mass at least `1`. Local finiteness of `|Dχ_s|` makes `∂*s` countable and locally
  isolated; the Poincaré inequality
  (`TauCeti.setLIntegral_enorm_sub_setAverage_le_div_mul_totalVariationOn`) on the two open
  half-balls around `x` and the Gauss–Green pairing against a bump identify `s` locally up to null
  sets with the half-line `{y | ⟪y, ν_s x⟫ < ⟪x, ν_s x⟫}` and show `|Dχ_s| {x} = 1`.
* **Countable rectifiability for `n ≥ 2`.** Stratifying `∂*s` by uniform lower volume density
  bounds (`TauCeti.eventually_ofReal_pow_le_mul_measure_inter_ball` and
  `TauCeti.eventually_ofReal_pow_le_mul_measure_ball_sdiff`), blow-up convergence to the half-space
  `{w | ⟪w, ν_s x⟫ < 0}` (`TauCeti.tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter`)
  forces every stratum to lie locally inside an arbitrarily narrow cone around `(ℝ ∙ ν_s x)ᗮ` at
  `x`. Federer's geometric cone criterion
  (`TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_le`) then makes each stratum,
  and hence `∂*s`, countably `(n - 1)`-rectifiable.
* **Measure identification.** On each member `V` of a relatively compact open exhaustion of `Ω`,
  `|Dχ_s|` has `(n - 1)`-dimensional density `1` at every point of `∂*s ∩ V`, so
  `Measure.mul_euclideanHausdorffMeasure_le_measure_of_isOpen` gives `μHE[n - 1](∂*s ∩ V) < ∞`.
  Combining the rectifiable density theorem
  (`TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`),
  Besicovitch differentiation (`Besicovitch.ae_tendsto_rnDeriv`), and absolute continuity of
  `|Dχ_s|` with respect to `μHE[n - 1]`
  (`TauCeti.map_variationMeasure_absolutelyContinuous_euclideanHausdorffMeasure`) identifies the
  Radon–Nikodym derivative as `1` almost everywhere, proving `|Dχ_s| = Hⁿ⁻¹⌊∂*s`.
* **Pointwise approximate tangent hyperplanes.** Once `|Dχ_s| = Hⁿ⁻¹⌊∂*s` is known, lower
  semicontinuity of perimeter on thin slabs `{z ∈ ball x r | |⟪z - x, ν_s x⟫| < η r}` shows all of
  the `(n - 1)`-dimensional density `1` of `∂*s` in `closedBall x r` concentrates in the slab,
  forcing the complement of every cone around `(ℝ ∙ ν_s x)ᗮ` to have `(n - 1)`-dimensional density
  zero at *every* `x ∈ ∂*s`.

## References

* E. De Giorgi, *Nuovi teoremi relativi alle misure `(r - 1)`-dimensionali in uno spazio ad `r`
  dimensioni*, Ricerche Mat. **4** (1955), 95–113.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15 (Theorem
  15.5, Corollary 15.8, and Theorem 15.9).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.3 (Theorem 5.16) and §5.8 (Theorem 5.17).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.5 (Theorem 3.59).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E} {x : E}

/-! ### Orthogonal hyperplanes and dimensions zero and one -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The distance from `w` to the orthogonal hyperplane `(ℝ ∙ ν)ᗮ` of a unit vector `ν` is
`|⟪w, ν⟫|`. -/
private theorem infDist_orthogonal_span_singleton {ν : E} (hν : ‖ν‖ = 1) (w : E) :
    infDist w ((ℝ ∙ ν)ᗮ : Set E) = |⟪w, ν⟫| := by
  have : (ℝ ∙ ν).HasOrthogonalProjection := inferInstance
  rw [← (ℝ ∙ ν).norm_starProjection_eq_infDist w, Submodule.starProjection_unit_singleton ℝ hν w,
    norm_smul, hν, mul_one, real_inner_comm, Real.norm_eq_abs]

/-- At every point `x` of the reduced boundary, the orthogonal hyperplane `(ℝ ∙ ν_s x)ᗮ` to the
measure-theoretic outer normal has dimension `finrank ℝ E - 1`. -/
theorem finrank_orthogonal_span_outerNormal (hx : x ∈ reducedBoundary μ Ω s) :
    finrank ℝ (ℝ ∙ outerNormal μ Ω s x)ᗮ = finrank ℝ E - 1 := by
  have hν0 : outerNormal μ Ω s x ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_outerNormal hx]; exact one_ne_zero)
  have : Nontrivial E := ⟨⟨outerNormal μ Ω s x, 0, hν0⟩⟩
  have : Fact (finrank ℝ E = finrank ℝ E - 1 + 1) := ⟨(Nat.sub_add_cancel finrank_pos).symm⟩
  exact Submodule.finrank_orthogonal_span_singleton hν0

/-- In a zero-dimensional space no unit vector exists, so the reduced boundary is empty. -/
theorem reducedBoundary_eq_empty_of_finrank_eq_zero (hn : finrank ℝ E = 0) :
    reducedBoundary μ Ω s = ∅ := by
  have : Subsingleton E := finrank_zero_iff.mp hn
  refine eq_empty_of_forall_notMem fun y hy => ?_
  have h1 := norm_outerNormal hy
  rw [Subsingleton.elim (outerNormal μ Ω s y) 0, norm_zero] at h1
  exact zero_ne_one h1

omit [MeasurableSpace E] [BorelSpace E] in
/-- In a one-dimensional real inner product space, scaling a unit vector `ν` gives a linear
isometry equivalence `ℝ ≃ₗᵢ[ℝ] E` with inverse `⟪·, ν⟫`. -/
private def linearIsometryEquivOfFinrankEqOne (hn : finrank ℝ E = 1) {ν : E} (hν : ‖ν‖ = 1) :
    ℝ ≃ₗᵢ[ℝ] E where
  toFun t := t • ν
  map_add' a b := add_smul a b ν
  map_smul' a b := by simp [mul_smul]
  invFun y := ⟪y, ν⟫
  left_inv t := by
    dsimp only
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hν, one_pow, mul_one]
  right_inv y := by
    have hν0 : ν ≠ 0 := norm_ne_zero_iff.mp (hν ▸ one_ne_zero)
    have : Fact (finrank ℝ E = 0 + 1) := ⟨hn⟩
    have horth : (ℝ ∙ ν)ᗮ = ⊥ :=
      Submodule.finrank_eq_zero.mp (Submodule.finrank_orthogonal_span_singleton hν0)
    have hmem : y - ⟪y, ν⟫ • ν ∈ (ℝ ∙ ν)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq, hν]
      ring
    rw [horth, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem.symm
  norm_map' t := by change ‖t • ν‖ = ‖t‖; rw [norm_smul, hν, mul_one]

/-- On an open interval `I`, two Lebesgue points of `T.indicator 1` give a lower bound on the
one-dimensional total variation regardless of their order. -/
private theorem ofReal_abs_indicator_sub_le_totalVariationOn {T : Set ℝ} (hTm : MeasurableSet T)
    {I : Opens ℝ} (hconv : Convex ℝ (I : Set ℝ)) {t₁ t₂ : ℝ} (ht₁I : t₁ ∈ (I : Set ℝ))
    (ht₂I : t₂ ∈ (I : Set ℝ))
    (ht₁L : Tendsto (fun r => ⨍ y in closedBall t₁ r,
      ‖T.indicator (1 : ℝ → ℝ) y - T.indicator 1 t₁‖) (𝓝[>] 0) (𝓝 0))
    (ht₂L : Tendsto (fun r => ⨍ y in closedBall t₂ r,
      ‖T.indicator (1 : ℝ → ℝ) y - T.indicator 1 t₂‖) (𝓝[>] 0) (𝓝 0)) :
    ENNReal.ofReal |T.indicator (1 : ℝ → ℝ) t₂ - T.indicator 1 t₁| ≤
      totalVariationOn volume I (T.indicator 1) := by
  have huI : LocallyIntegrableOn (T.indicator (1 : ℝ → ℝ)) I volume :=
    ((locallyIntegrable_const 1).indicator hTm).locallyIntegrableOn _
  rcases le_total t₁ t₂ with hle | hle
  · simpa [Fin.sum_univ_succ] using Real.ofReal_sum_abs_sub_le_totalVariationOn huI
      (x := ![t₁, t₂]) (v := fun i => T.indicator 1 (![t₁, t₂] i))
      (Fin.monotone_iff_le_succ.mpr fun i => by fin_cases i; exact hle)
      (by simpa using hconv.ordConnected.out ht₁I ht₂I) (fun i => by fin_cases i <;> assumption)
  · simpa [Fin.sum_univ_succ, abs_sub_comm] using Real.ofReal_sum_abs_sub_le_totalVariationOn huI
      (x := ![t₂, t₁]) (v := fun i => T.indicator 1 (![t₂, t₁] i))
      (Fin.monotone_iff_le_succ.mpr fun i => by fin_cases i; exact hle)
      (by simpa using hconv.ordConnected.out ht₂I ht₁I) (fun i => by fin_cases i <;> assumption)

/-- In dimension one, at a point `x` of the reduced boundary of `s` in `Ω`, every ball
`ball x r ⊆ Ω` has perimeter at least `1`. -/
private theorem one_le_perimeter_ball_of_finrank_eq_one (hn : finrank ℝ E = 1)
    (hx : x ∈ reducedBoundary volume Ω s) {r : ℝ} (hr : 0 < r) (hBΩ : ball x r ⊆ Ω) :
    1 ≤ perimeter volume ⟨ball x r, isOpen_ball⟩ s := by
  let e := linearIsometryEquivOfFinrankEqOne hn (norm_outerNormal hx)
  set s₀ := toMeasurable volume (s ∩ ball x r)
  have hs_null : NullMeasurableSet (s ∩ ball x r) volume := by
    rw [show s ∩ ball x r = (s ∩ Ω) ∩ ball x r by rw [inter_assoc, inter_eq_right.mpr hBΩ]]
    exact (nullMeasurableSet_inter_of_mem_reducedBoundary hx).inter
      measurableSet_ball.nullMeasurableSet
  have hs₀_ae : s =ᵐ[volume.restrict (ball x r)] s₀ := by
    refine (ae_restrict_iff' measurableSet_ball).mpr ?_
    filter_upwards [hs_null.toMeasurable_ae_eq] with y hy hyB
    exact ⟨fun hys => hy.mpr ⟨hys, hyB⟩, fun hys₀ => (hy.mp hys₀).1⟩
  set T : Set ℝ := e ⁻¹' s₀
  have hTm : MeasurableSet T := (measurableSet_toMeasurable _ _).preimage e.continuous.measurable
  set I : Opens ℝ := Opens.comap (e : C(ℝ, E)) ⟨ball x r, isOpen_ball⟩
  have hIeq : (I : Set ℝ) = ball (e.symm x) r := by
    ext t; simp [I, Metric.mem_ball]
  have hpos₁ : volume (T ∩ I) ≠ 0 := by
    have hae_inter : s₀ ∩ ball x r =ᵐ[volume] s ∩ ball x r := by
      filter_upwards [hs_null.toMeasurable_ae_eq] with y hy
      change (y ∈ toMeasurable volume (s ∩ ball x r) ∧ y ∈ ball x r) ↔ y ∈ s ∧ y ∈ ball x r
      by_cases hyB : y ∈ ball x r <;> simp [hyB, hy]
    rw [show T ∩ I = e ⁻¹' (s₀ ∩ ball x r) from rfl, e.measurePreserving.measure_preimage
      ((measurableSet_toMeasurable _ _).inter measurableSet_ball).nullMeasurableSet,
      measure_congr hae_inter]
    exact (measure_inter_ball_pos hx hr).ne'
  have hpos₂ : volume ((I : Set ℝ) \ T) ≠ 0 := by
    have hxc : x ∈ reducedBoundary volume Ω sᶜ := by rwa [reducedBoundary_compl]
    have hae_compl : ball x r \ s₀ =ᵐ[volume] sᶜ ∩ ball x r := by
      filter_upwards [hs_null.toMeasurable_ae_eq] with y hy
      change (y ∈ ball x r ∧ y ∉ toMeasurable volume (s ∩ ball x r)) ↔ y ∉ s ∧ y ∈ ball x r
      by_cases hyB : y ∈ ball x r <;> simp [hyB, hy, and_comm]
    rw [show (I : Set ℝ) \ T = e ⁻¹' (ball x r \ s₀) from rfl,
      e.measurePreserving.measure_preimage
        (measurableSet_ball.diff (measurableSet_toMeasurable _ _)).nullMeasurableSet,
      measure_congr hae_compl]
    exact (measure_inter_ball_pos hxc hr).ne'
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := T.indicator (1 : ℝ → ℝ)) ((locallyIntegrable_const 1).indicator hTm)
  obtain ⟨t₁, ⟨ht₁T, ht₁I⟩, ht₁L⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos₁ (ae_restrict_of_ae hae)
  obtain ⟨t₂, ⟨ht₂I, ht₂T⟩, ht₂L⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos₂ (ae_restrict_of_ae hae)
  rw [perimeter_congr_ae hs₀_ae, ← e.perimeter_comap e.measurePreserving, perimeter_def]
  simpa [ht₁T, ht₂T] using ofReal_abs_indicator_sub_le_totalVariationOn hTm
    (hIeq ▸ convex_ball (e.symm x) r) ht₁I ht₂I ht₁L ht₂L

/-- In dimension one, every point of the reduced boundary of `s` in `Ω` is an atom of the
perimeter measure of mass at least `1`. -/
private theorem one_le_variationMeasure_singleton_of_finrank_eq_one (hn : finrank ℝ E = 1)
    (hx : x ∈ reducedBoundary volume Ω s) :
    1 ≤ variationMeasure volume Ω (s.indicator 1) {⟨x, reducedBoundary_subset hx⟩} := by
  set lam := variationMeasure volume Ω (s.indicator 1)
  obtain ⟨r₀, hr₀, hr₀Ω⟩ :=
    nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  obtain ⟨r₁, hr₁, hle⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((eventually_perimeter_ball_le_variationMeasure_closedBall_of_mem_reducedBoundary hx).and
      (Ioo_mem_nhdsGT hr₀))
  set ρ := min (r₁ / 2) r₀
  have hρ : 0 < ρ := lt_min (half_pos hr₁) hr₀
  let S (n : ℕ) : Set Ω := ((↑) : Ω → E) ⁻¹' closedBall x (ρ / (n + 1 : ℝ))
  have hanti : Antitone S := fun i j hij => preimage_mono <| closedBall_subset_closedBall <| by
    gcongr
  have hSm (n : ℕ) : NullMeasurableSet (S n) lam :=
    (isClosed_closedBall.preimage continuous_subtype_val).measurableSet.nullMeasurableSet
  have hS0 : lam (S 0) ≠ ∞ := by
    have hsub : S 0 ⊆ ((↑) : Ω → E) ⁻¹' closedBall x r₀ :=
      preimage_mono (closedBall_subset_closedBall (by simp [ρ]))
    have hK : IsCompact (((↑) : Ω → E) ⁻¹' closedBall x r₀) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x r₀)
        (by rwa [Subtype.range_coe])
    exact ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have hInter : (⋂ n : ℕ, S n) = {⟨x, reducedBoundary_subset hx⟩} := by
    ext y
    simp only [S, mem_iInter, mem_preimage, mem_closedBall, mem_singleton_iff, Subtype.ext_iff]
    refine ⟨fun hy => dist_le_zero.mp (ge_of_tendsto' (x := atTop) ?_ hy),
      fun hy n => by rw [hy, dist_self]; positivity⟩
    simpa using (tendsto_const_nhds (x := ρ)).div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hlim := hInter ▸ tendsto_measure_iInter_atTop hSm hanti ⟨0, hS0⟩
  refine ge_of_tendsto' hlim fun n => ?_
  have hrn : 0 < ρ / (n + 1 : ℝ) := by positivity
  have hrn_le : ρ / (n + 1 : ℝ) ≤ ρ := div_le_self hρ.le (by linarith)
  have hrn₁ : ρ / (n + 1 : ℝ) ∈ Ioo 0 r₁ :=
    ⟨hrn, hrn_le.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr₁))⟩
  exact (one_le_perimeter_ball_of_finrank_eq_one hn hx hrn
    (ball_subset_closedBall.trans ((closedBall_subset_closedBall
      (hrn_le.trans (min_le_right _ _))).trans hr₀Ω))).trans (hle hrn₁).1

/-- In dimension one, every compact subset of `Ω` meets the reduced boundary in finitely many
points. -/
private theorem finite_inter_reducedBoundary_of_finrank_eq_one (hn : finrank ℝ E = 1)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (K ∩ reducedBoundary volume Ω s).Finite := by
  set lam := variationMeasure volume Ω (s.indicator 1)
  set A : Set Ω := ((↑) : Ω → E) ⁻¹' (K ∩ reducedBoundary volume Ω s)
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
  have hfin_lam : lam (((↑) : Ω → E) ⁻¹' K) < ∞ := hK'.measure_lt_top
  have hAfin : A.Finite := by
    by_contra hinf
    obtain ⟨F, hFA, hFcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf (Nat.floor (lam.real (((↑) : Ω → E) ⁻¹' K)) + 1)
    have hle : (F.card : ℝ≥0∞) ≤ lam (((↑) : Ω → E) ⁻¹' K) := by
      calc (F.card : ℝ≥0∞) = ∑ _ ∈ F, (1 : ℝ≥0∞) := by simp
        _ ≤ ∑ y ∈ F, lam {y} :=
            Finset.sum_le_sum fun y hy =>
              one_le_variationMeasure_singleton_of_finrank_eq_one hn (hFA hy).2
        _ = lam (⋃ y ∈ F, ({y} : Set Ω)) := (measure_biUnion_finset
            (fun y _ z _ hyz => disjoint_singleton.mpr hyz)
            fun _ _ => measurableSet_singleton _).symm
        _ ≤ lam (((↑) : Ω → E) ⁻¹' K) :=
            measure_mono (iUnion₂_subset fun _ hy =>
              singleton_subset_iff.mpr (preimage_mono inter_subset_left (hFA hy)))
    have hlt : lam.real (((↑) : Ω → E) ⁻¹' K) < F.card := by
      rw [hFcard, Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one _
    exact hlt.not_ge (by
      rw [Measure.real, ← ENNReal.toReal_natCast]
      exact ENNReal.toReal_mono hfin_lam.ne hle)
  have himg : ((↑) : Ω → E) '' A = K ∩ reducedBoundary volume Ω s := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.mpr (inter_subset_left.trans hKΩ)]
  exact himg ▸ hAfin.image Subtype.val

/-- **In dimension one, the reduced boundary is countable.** -/
theorem countable_reducedBoundary_of_finrank_eq_one [μ.IsAddHaarMeasure] (hn : finrank ℝ E = 1) :
    (reducedBoundary μ Ω s).Countable := by
  rw [reducedBoundary_eq_volume]
  obtain ⟨V, hVc, hVΩ, -, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hcover : reducedBoundary volume Ω s ⊆
      ⋃ n, closure (V n : Set E) ∩ reducedBoundary volume Ω s := fun y hy => by
    obtain ⟨n, hnV⟩ := mem_iUnion.mp (hVU.symm.subset (reducedBoundary_subset hy))
    exact mem_iUnion.mpr ⟨n, subset_closure hnV, hy⟩
  exact (countable_iUnion fun n =>
    (finite_inter_reducedBoundary_of_finrank_eq_one hn (hVc n) (hVΩ n)).countable).mono hcover

/-- In dimension one, every point `x` of `∂*s` admits a closed ball in `Ω` whose interior meets
`∂*s` only at `x`. -/
private theorem exists_closedBall_subset_and_inter_reducedBoundary_eq_singleton
    (hn : finrank ℝ E = 1) (hx : x ∈ reducedBoundary volume Ω s) :
    ∃ r > 0, closedBall x r ⊆ Ω ∧ ball x r ∩ reducedBoundary volume Ω s = {x} := by
  obtain ⟨r₁, hr₁, hr₁Ω⟩ :=
    nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  have hfin₁ := finite_inter_reducedBoundary_of_finrank_eq_one (s := s) hn
    (isCompact_closedBall x r₁) hr₁Ω
  have hopen_compl : IsOpen (((closedBall x r₁ ∩ reducedBoundary volume Ω s) \ {x})ᶜ) :=
    hfin₁.sdiff.isClosed.isOpen_compl
  obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.mp hopen_compl x (fun h => h.2 rfl)
  set r := min (r₁ / 2) (r₂ / 2)
  have hr : 0 < r := lt_min (half_pos hr₁) (half_pos hr₂)
  refine ⟨r, hr,
    (closedBall_subset_closedBall ((min_le_left _ _).trans (half_le_self hr₁.le))).trans hr₁Ω, ?_⟩
  ext y
  refine ⟨fun ⟨hyb, hyB⟩ => by_contra fun hyx => ?_,
    by rintro rfl; exact ⟨mem_ball_self hr, hx⟩⟩
  have hyr₁ : y ∈ closedBall x r₁ :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall
      ((min_le_left _ _).trans (half_le_self hr₁.le)))) hyb
  have hyr₂ : y ∈ ball x r₂ :=
    ball_subset_ball ((min_le_right _ _).trans (half_le_self hr₂.le)) hyb
  exact hr₂sub hyr₂ ⟨⟨hyr₁, hyB⟩, hyx⟩

/-- On a nonempty bounded convex open set where `s` is null-measurable and has perimeter zero, `s`
is almost everywhere empty or almost everywhere the whole open set. -/
private theorem ae_eq_empty_or_univ_of_perimeter_eq_zero {U : Opens E}
    (hUconv : Convex ℝ (U : Set E)) (hUbdd : Bornology.IsBounded (U : Set E))
    (hUne : (U : Set E).Nonempty) (hsU : NullMeasurableSet s (volume.restrict U))
    (hP : perimeter volume U s = 0) :
    s =ᵐ[volume.restrict U] (∅ : Set E) ∨ s =ᵐ[volume.restrict U] univ := by
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp U.isOpen z₀ hz₀
  have hU0 : volume (U : Set E) ≠ 0 :=
    ((measure_ball_pos volume z₀ hρ).trans_le (measure_mono hρU)).ne'
  have hUtop : volume (U : Set E) ≠ ∞ := hUbdd.measure_lt_top.ne
  have hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) U volume :=
    locallyIntegrableOn_indicator_const hsU 1
  have hpoinc := setLIntegral_enorm_sub_setAverage_le_div_mul_totalVariationOn hUconv hu
    subset_rfl hU0 hUtop
  rw [← perimeter_def, hP, mul_zero, nonpos_iff_eq_zero] at hpoinc
  have hzero := (lintegral_eq_zero_iff'
    (hu.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm).mp hpoinc
  set c := ⨍ y in (U : Set E), s.indicator (1 : E → ℝ) y
  have hae : ∀ᵐ y ∂volume.restrict U, s.indicator (1 : E → ℝ) y = c := by
    filter_upwards [hzero] with y hy
    exact sub_eq_zero.mp (eNorm_eq_zero.mp hy)
  obtain ⟨y₀, -, hy₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hU0 hae
  by_cases hy₀s : y₀ ∈ s
  · right
    rw [indicator_of_mem hy₀s, Pi.one_apply] at hy₀
    filter_upwards [hae] with y hy
    rw [← hy₀] at hy
    simp only [mem_univ, iff_true]
    exact by_contra fun hys => zero_ne_one ((indicator_of_notMem hys (1 : E → ℝ)).symm.trans hy)
  · left
    rw [indicator_of_notMem hy₀s] at hy₀
    filter_upwards [hae] with y hy
    rw [← hy₀] at hy
    simp only [mem_empty_iff_false, iff_false]
    exact fun hys => one_ne_zero ((indicator_of_mem hys (1 : E → ℝ)).symm.trans hy)

/-- A set containing `x ∈ ∂*s` cannot vanish almost everywhere on both open half-balls around `x`
when the dividing hyperplane is null. -/
private theorem not_ae_eq_empty_of_halfBalls (hx : x ∈ reducedBoundary volume Ω s) {r : ℝ}
    (hr : 0 < r) {ν : E} (hmid : volume {y ∈ ball x r | ⟪y, ν⟫ = ⟪x, ν⟫} = 0)
    (h₁ : s =ᵐ[volume.restrict {y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫}] (∅ : Set E))
    (h₂ : s =ᵐ[volume.restrict {y ∈ ball x r | ⟪x, ν⟫ < ⟪y, ν⟫}] (∅ : Set E)) : False := by
  have hm₁ : MeasurableSet {y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫} :=
    measurableSet_ball.inter
      (measurableSet_lt (by fun_prop : Measurable fun y : E => ⟪y, ν⟫) measurable_const)
  have hm₂ : MeasurableSet {y ∈ ball x r | ⟪x, ν⟫ < ⟪y, ν⟫} :=
    measurableSet_ball.inter
      (measurableSet_lt measurable_const (by fun_prop : Measurable fun y : E => ⟪y, ν⟫))
  have hv₁ : volume (s ∩ {y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫}) = 0 := by
    rwa [← Measure.restrict_apply' hm₁, ← ae_eq_empty]
  have hv₂ : volume (s ∩ {y ∈ ball x r | ⟪x, ν⟫ < ⟪y, ν⟫}) = 0 := by
    rwa [← Measure.restrict_apply' hm₂, ← ae_eq_empty]
  refine (measure_inter_ball_pos hx hr).ne' (measure_mono_null (fun y ⟨hys, hyb⟩ => ?_)
    (measure_union_null (measure_union_null hv₁ hv₂) hmid))
  rcases lt_trichotomy ⟪y, ν⟫ ⟪x, ν⟫ with hlt | heq | hgt
  · exact .inl (.inl ⟨hys, hyb, hlt⟩)
  · exact .inr ⟨hyb, heq⟩
  · exact .inl (.inr ⟨hys, hyb, hgt⟩)

/-- In dimension one, at an isolated point `x ∈ ∂*s`, `s` cannot agree almost everywhere on
`ball x r` with the opposite half-line `{y | ⟪y, -ν_s x⟫ < ⟪x, -ν_s x⟫}`. -/
private theorem not_ae_eq_setOf_inner_neg_lt_of_finrank_eq_one (hn : finrank ℝ E = 1)
    (hx : x ∈ reducedBoundary volume Ω s) {r : ℝ} (hr : 0 < r) (hrΩ : closedBall x r ⊆ Ω)
    (hiso : ball x r ∩ reducedBoundary volume Ω s = {x})
    (hs_opp : s =ᵐ[volume.restrict (ball x r)]
      {y | ⟪y, -outerNormal volume Ω s x⟫ < ⟪x, -outerNormal volume Ω s x⟫}) : False := by
  set ν := outerNormal volume Ω s x
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  let θ : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set φ : E → E := fun y => θ y • ν
  have hφ_cd : ContDiff ℝ 1 φ := θ.contDiff.smul contDiff_const
  have hφ_cs : HasCompactSupport φ := θ.hasCompactSupport.smul_right
  have hφ_ball : tsupport φ ⊆ ball x r :=
    (tsupport_smul_subset_left _ _).trans
      (θ.tsupport_eq.trans_subset (closedBall_subset_ball (half_lt_self hr)))
  have hgg := integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal hu hfin hφ_cd
    hφ_cs (hφ_ball.trans (ball_subset_closedBall.trans hrΩ))
  have hlhs : ∫ y, LinearMap.trace ℝ E (fderiv ℝ φ y : E →ₗ[ℝ] E) * s.indicator 1 y =
      ∫ y in {y | ⟪y, -ν⟫ = ⟪x, -ν⟫}, ⟪φ y, -ν⟫ ∂μHE[finrank ℝ E - 1] := by
    have hcongr :
        (fun y => LinearMap.trace ℝ E (fderiv ℝ φ y : E →ₗ[ℝ] E) * s.indicator 1 y) =ᵐ[volume]
        fun y => LinearMap.trace ℝ E (fderiv ℝ φ y : E →ₗ[ℝ] E) *
          {y | ⟪y, -ν⟫ < ⟪x, -ν⟫}.indicator 1 y := by
      filter_upwards [ae_restrict_iff' measurableSet_ball |>.mp hs_opp] with y hy
      by_cases hyb : y ∈ ball x r
      · by_cases hys : y ∈ s
        · rw [indicator_of_mem hys, indicator_of_mem ((hy hyb).mp hys)]
        · rw [indicator_of_notMem hys, indicator_of_notMem (mt (hy hyb).mpr hys)]
      · simp [((notMem_tsupport_iff_eventuallyEq.mp fun h => hyb (hφ_ball h)).fderiv_eq).trans
          (fderiv_const_apply 0)]
    rw [integral_congr_ae hcongr, ← setIntegral_setOf_inner_lt_trace_fderiv
      (by rw [norm_neg, hν]) ⟪x, -ν⟫ hφ_cd hφ_cs,
      ← integral_indicator (measurableSet_lt (by fun_prop) measurable_const)]
    congr 1 with y
    by_cases hy : y ∈ {y : E | ⟪y, -ν⟫ < ⟪x, -ν⟫}
    · rw [indicator_of_mem hy, indicator_of_mem hy, Pi.one_apply, mul_one]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  have hlhs_nonpos : ∫ y in {y | ⟪y, -ν⟫ = ⟪x, -ν⟫}, ⟪φ y, -ν⟫ ∂μHE[finrank ℝ E - 1] ≤ 0 :=
    setIntegral_nonpos (measurableSet_eq_fun (by fun_prop) measurable_const) fun y _ => by
      simp [φ, real_inner_smul_left, inner_neg_right, hν, θ.nonneg]
  set lam := variationMeasure volume Ω (s.indicator 1)
  set x₀ : Ω := ⟨x, reducedBoundary_subset hx⟩
  have hae_x₀ : (fun z : Ω => ⟪φ z, outerNormal volume Ω s z⟫) =ᵐ[lam]
      ({x₀} : Set Ω).indicator (1 : Ω → ℝ) := by
    filter_upwards [ae_mem_reducedBoundary] with z hz
    by_cases hzx : z = x₀
    · subst hzx
      simp [φ, x₀, θ.one_of_mem_closedBall (mem_closedBall_self (by positivity)), ν, hν]
    · rw [indicator_of_notMem hzx]
      exact (em ((z : E) ∈ ball x r)).elim
        (fun hzb => False.elim (hzx (Subtype.ext (hiso.subset ⟨hzb, hz⟩))))
        (fun hzb => by simp [image_eq_zero_of_notMem_tsupport fun h => hzb (hφ_ball h)])
  have hx₀_fin : lam {x₀} ≠ ∞ := by
    have hK : IsCompact (((↑) : Ω → E) ⁻¹' closedBall x r) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x r)
        (by rwa [Subtype.range_coe])
    exact ((measure_mono (singleton_subset_iff.mpr (mem_closedBall_self hr.le))).trans_lt
      hK.measure_lt_top).ne
  have hrhs_pos : 0 < ∫ z : Ω, ⟪φ z, outerNormal volume Ω s z⟫ ∂lam := by
    rw [integral_congr_ae hae_x₀, integral_indicator_one (measurableSet_singleton _)]
    exact ENNReal.toReal_pos
      (zero_lt_one.trans_le (one_le_variationMeasure_singleton_of_finrank_eq_one hn hx)).ne' hx₀_fin
  linarith

/-- Around an isolated point `x` of `∂*s`, `s` is almost everywhere empty or almost everywhere the
whole open half-ball `{y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫}` for any unit vector `ν`. -/
private theorem ae_eq_empty_or_univ_halfBall_of_isolated (hx : x ∈ reducedBoundary volume Ω s)
    {r : ℝ} (hr : 0 < r) (hrΩ : closedBall x r ⊆ Ω)
    (hiso : ball x r ∩ reducedBoundary volume Ω s = {x}) {ν : E} (hν : ‖ν‖ = 1) :
    s =ᵐ[volume.restrict {y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫}] (∅ : Set E) ∨
      s =ᵐ[volume.restrict {y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫}] univ := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  have hs_meas := nullMeasurableSet_restrict_of_mem_reducedBoundary hx
  let U : Opens E := ⟨{y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫},
    isOpen_ball.inter (isOpen_lt (by fun_prop : Continuous fun y : E => ⟪y, ν⟫) continuous_const)⟩
  have hlin : IsLinearMap ℝ fun y : E => ⟪y, ν⟫ :=
    ⟨fun a b => inner_add_left a b ν, fun c a => real_inner_smul_left a ν c⟩
  have hzero : perimeter volume U s = 0 := by
    rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin
      ((sep_subset _ _).trans (ball_subset_closedBall.trans hrΩ))]
    refine measure_mono_null ?_ (ae_iff.mp ae_mem_reducedBoundary)
    exact fun z hz hzB => hz.2.ne (congrArg (⟪·, ν⟫) (hiso.subset ⟨hz.1, hzB⟩))
  exact ae_eq_empty_or_univ_of_perimeter_eq_zero (U := U)
    ((convex_ball x r).inter (convex_halfSpace_lt hlin _))
    (isBounded_ball.subset (sep_subset _ _))
    ⟨x - (r / 2) • ν, by
      simp [U, dist_eq_norm, norm_smul, hν, abs_of_pos hr, half_lt_self hr,
        inner_sub_left, real_inner_smul_left, hr]⟩
    (hs_meas.mono (Measure.restrict_mono
      ((sep_subset _ _).trans (ball_subset_closedBall.trans hrΩ)) le_rfl))
    hzero

/-- **Local structure of the reduced boundary in dimension one.** At every point `x` of the reduced
boundary of `s` in `Ω`, `x` is isolated in `∂*s` and on a small ball `ball x r ⊆ Ω` the set `s`
agrees almost everywhere with the half-line `{y | ⟪y, ν_s x⟫ < ⟪x, ν_s x⟫}`. -/
theorem exists_ball_ae_eq_setOf_inner_lt_of_finrank_eq_one [μ.IsAddHaarMeasure]
    (hn : finrank ℝ E = 1) (hx : x ∈ reducedBoundary μ Ω s) :
    ∃ r > 0, closedBall x r ⊆ Ω ∧ ball x r ∩ reducedBoundary μ Ω s = {x} ∧
      s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, outerNormal μ Ω s x⟫ < ⟪x, outerNormal μ Ω s x⟫} := by
  rw [reducedBoundary_eq_volume] at hx ⊢
  rw [outerNormal_eq_volume]
  obtain ⟨r, hr, hrΩ, hiso⟩ := exists_closedBall_subset_and_inter_reducedBoundary_eq_singleton hn hx
  set ν := outerNormal volume Ω s x
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  have hU₁_eq : {y ∈ ball x r | ⟪x, ν⟫ < ⟪y, ν⟫} = {y ∈ ball x r | ⟪y, -ν⟫ < ⟪x, -ν⟫} := by
    ext y; simp [inner_neg_right]
  have hm₁ : MeasurableSet {y ∈ ball x r | ⟪y, ν⟫ < ⟪x, ν⟫} :=
    measurableSet_ball.inter
      (measurableSet_lt (by fun_prop : Measurable fun y : E => ⟪y, ν⟫) measurable_const)
  have hm₂ : MeasurableSet {y ∈ ball x r | ⟪x, ν⟫ < ⟪y, ν⟫} :=
    measurableSet_ball.inter
      (measurableSet_lt measurable_const (by fun_prop : Measurable fun y : E => ⟪y, ν⟫))
  have hU₁_cases := ae_eq_empty_or_univ_halfBall_of_isolated hx hr hrΩ hiso hν
  have hU₂_cases : s =ᵐ[volume.restrict {y ∈ ball x r | ⟪x, ν⟫ < ⟪y, ν⟫}] (∅ : Set E) ∨
      s =ᵐ[volume.restrict {y ∈ ball x r | ⟪x, ν⟫ < ⟪y, ν⟫}] univ := by
    rw [hU₁_eq]
    exact ae_eq_empty_or_univ_halfBall_of_isolated hx hr hrΩ hiso (by rw [norm_neg, hν])
  have hmid_null : volume {y ∈ ball x r | ⟪y, ν⟫ = ⟪x, ν⟫} = 0 := by
    let e := linearIsometryEquivOfFinrankEqOne hn hν
    have : Nontrivial E := ⟨⟨ν, 0, norm_ne_zero_iff.mp (hν ▸ one_ne_zero)⟩⟩
    exact measure_mono_null (fun _ hy => e.symm.injective hy.2) (measure_singleton x)
  refine ⟨r, hr, hrΩ, hiso, ?_⟩
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular μ (volume : Measure E),
    ← Measure.coe_nnreal_smul, Measure.restrict_smul]
  refine Measure.ae_smul_measure ?_ _
  rcases hU₁_cases with h₁ | h₁ <;> rcases hU₂_cases with h₂ | h₂
  · exact False.elim (not_ae_eq_empty_of_halfBalls hx hr hmid_null h₁ h₂)
  · refine False.elim (not_ae_eq_setOf_inner_neg_lt_of_finrank_eq_one hn hx hr hrΩ hiso ?_)
    refine (ae_restrict_iff' measurableSet_ball).mpr ?_
    filter_upwards [ae_restrict_iff' hm₁ |>.mp h₁, ae_restrict_iff' hm₂ |>.mp h₂,
      compl_mem_ae_iff.mpr hmid_null] with y hy₁ hy₂ hymid hyb
    rcases lt_trichotomy ⟪y, ν⟫ ⟪x, ν⟫ with hlt | heq | hgt
    · simp only [inner_neg_right, neg_lt_neg_iff,
        show y ∉ s by simpa using hy₁ ⟨hyb, hlt⟩, false_iff, not_lt]
      exact hlt.le
    · exact False.elim (hymid ⟨hyb, heq⟩)
    · simp only [inner_neg_right, neg_lt_neg_iff,
        show y ∈ s by simpa using hy₂ ⟨hyb, hgt⟩, true_iff]
      exact hgt
  · refine (ae_restrict_iff' measurableSet_ball).mpr ?_
    filter_upwards [ae_restrict_iff' hm₁ |>.mp h₁, ae_restrict_iff' hm₂ |>.mp h₂,
      compl_mem_ae_iff.mpr hmid_null] with y hy₁ hy₂ hymid hyb
    rcases lt_trichotomy ⟪y, ν⟫ ⟪x, ν⟫ with hlt | heq | hgt
    · simp [show y ∈ s by simpa using hy₁ ⟨hyb, hlt⟩, hlt]
    · exact False.elim (hymid ⟨hyb, heq⟩)
    · simp [show y ∉ s by simpa using hy₂ ⟨hyb, hgt⟩, not_lt_of_gt hgt]
  · have hxc : x ∈ reducedBoundary volume Ω sᶜ := by rwa [reducedBoundary_compl]
    exact False.elim (not_ae_eq_empty_of_halfBalls hxc hr hmid_null
      (h₁.compl.trans (by simp)) (h₂.compl.trans (by simp)))

/-- In `0`-dimensional Euclidean space `EuclideanSpace ℝ (Fin 0)`, every positive-radius ball has
Lebesgue measure `1`. -/
private theorem volume_ball_fin_zero {k : ℕ} (hk : k = 0) {r : ℝ} (hr : 0 < r) :
    volume (ball (0 : EuclideanSpace ℝ (Fin k)) r) = 1 := by
  subst hk
  rw [show ball (0 : EuclideanSpace ℝ (Fin 0)) r = {0} from
      eq_singleton_iff_unique_mem.mpr ⟨mem_ball_self hr, fun z _ => Subsingleton.elim z 0⟩,
    ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_zero,
    hausdorffMeasure_zero_eq_count, Measure.count_singleton]

/-- In dimension one, at a point `x` of the reduced boundary of `s` in `Ω`, all sufficiently small
closed balls around `x` have perimeter measure equal to `1`. -/
private theorem eventually_variationMeasure_closedBall_eq_one_of_finrank_eq_one
    (hn : finrank ℝ E = 1) (hx : x ∈ reducedBoundary volume Ω s) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) = 1 := by
  obtain ⟨r₀, hr₀, hr₀Ω, -, hs_eq⟩ :=
    exists_ball_ae_eq_setOf_inner_lt_of_finrank_eq_one (μ := volume) hn hx
  set B₀ : Opens E := ⟨ball x r₀, isOpen_ball⟩
  have hB₀Ω : B₀ ≤ Ω := ball_subset_closedBall.trans hr₀Ω
  set H := {y : E | ⟪y, outerNormal volume Ω s x⟫ < ⟪x, outerNormal volume Ω s x⟫}
  have hH_loc : LocallyIntegrableOn (H.indicator (1 : E → ℝ)) B₀ volume :=
    locallyIntegrableOn_indicator_const
      (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet 1
  have hH_fin : ∀ K, IsCompact K → K ⊆ (B₀ : Set E) →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (H.indicator 1) ≠ ∞ := by
    refine fun K _ hKB => ⟨B₀, hKB, ?_⟩
    rw [← perimeter_def, perimeter_ball_setOf_inner_lt (norm_outerNormal hx) x hr₀, hn]
    simp
  have hvar_eq : variationMeasure volume B₀ (s.indicator 1) =
      variationMeasure volume B₀ (H.indicator 1) :=
    variationMeasure_congr_ae (indicator_ae_eq_of_ae_eq_set hs_eq)
  filter_upwards [Ioo_mem_nhdsGT (half_pos hr₀)] with r ⟨hr, hrr₀⟩
  have hr_lt : r < r₀ := hrr₀.trans (half_lt_self hr₀)
  have hP1 : ∀ ρ, 0 < ρ → ρ ≤ r₀ →
      variationMeasure volume B₀ (H.indicator 1) (((↑) : B₀ → E) ⁻¹' ball x ρ) = 1 := by
    intro ρ hρ hρr₀
    let Uρ : Opens E := ⟨ball x ρ, isOpen_ball⟩
    change variationMeasure volume B₀ (H.indicator 1) (((↑) : B₀ → E) ⁻¹' (Uρ : Set E)) = 1
    rw [variationMeasure_preimage_coe hH_loc hH_fin (ball_subset_ball hρr₀), ← perimeter_def,
      perimeter_ball_setOf_inner_lt (norm_outerNormal hx) x hρ,
      volume_ball_fin_zero (by omega) one_pos]
    simp [hn]
  have hle₁ : 1 ≤ variationMeasure volume B₀ (H.indicator 1)
      (((↑) : B₀ → E) ⁻¹' closedBall x r) := by
    rw [← hP1 r hr hr_lt.le]
    exact measure_mono (preimage_mono ball_subset_closedBall)
  have hle₂ : variationMeasure volume B₀ (H.indicator 1)
      (((↑) : B₀ → E) ⁻¹' closedBall x r) ≤ 1 := by
    rw [← hP1 (r₀ / 2) (half_pos hr₀) (half_le_self hr₀.le)]
    exact measure_mono (preimage_mono (closedBall_subset_ball hrr₀))
  obtain ⟨hu_s, hfin_s⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  have heq : variationMeasure volume B₀ (s.indicator 1) (((↑) : B₀ → E) ⁻¹' closedBall x r) =
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
    rw [variationMeasure_eq_comap_inclusion hu_s hfin_s hB₀Ω,
      (Opens.isOpenEmbedding_of_le hB₀Ω).measurableEmbedding.comap_apply]
    congr 1; ext z
    exact ⟨by rintro ⟨w, hw, rfl⟩; exact hw,
      fun hz => ⟨⟨z, closedBall_subset_ball hr_lt hz⟩, hz, rfl⟩⟩
  rw [← heq, hvar_eq]
  exact le_antisymm hle₂ hle₁

/-- **Unrestricted-dimension density one of the perimeter measure at the reduced boundary.** For
Lebesgue measure in any dimension `n`, at every point `x` of the reduced boundary of `s` in `Ω`,
`|Dχ_s|(closedBall x r) / ω_{n-1} r^(n-1) → 1` as `r → 0⁺`. -/
private theorem tendsto_variationMeasure_volume_closedBall_div
    (hx : x ∈ reducedBoundary volume Ω s) :
    Tendsto (fun r =>
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r))
      (𝓝[>] 0) (𝓝 1) := by
  rcases lt_trichotomy (finrank ℝ E) 1 with hn0 | hn1 | hn2
  · exact False.elim
      ((reducedBoundary_eq_empty_of_finrank_eq_zero (Nat.lt_one_iff.mp hn0)).subset hx)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_variationMeasure_closedBall_eq_one_of_finrank_eq_one hn1 hx,
      self_mem_nhdsWithin] with r hr1 (hr : 0 < r)
    rw [hr1, Measure.addHaar_closedBall volume _ hr.le, finrank_euclideanSpace_fin,
      volume_ball_fin_zero (by omega) one_pos]
    simp [hn1]
  · exact tendsto_variationMeasure_closedBall_div_volume_closedBall hn2 hx

/-! ### Countable `(n - 1)`-rectifiability of the reduced boundary -/

/-- If a blow-up `(fun z => x + r • z) ⁻¹' s` is close in measure on `closedBall 0 2` to the
half-space `{z | ⟪z, ν⟫ < 0}`, any point `y = x + r • u` (`‖u‖ = 1`) carrying lower volume bounds
for both `s` and `sᶜ` at scale `r * (ε / 2)` satisfies `|⟪u, ν⟫| ≤ ε`. -/
private theorem abs_inner_le_of_blowUp_symmDiff_lt {ν u y : E} {r ε : ℝ} {C₀ : ℝ≥0∞}
    (hν : ‖ν‖ = 1) (hu_norm : ‖u‖ = 1) (hr_pos : 0 < r) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : C₀ ≠ ∞) (hxu : x + r • u = y)
    (hs1 : ENNReal.ofReal ((r * (ε / 2)) ^ finrank ℝ E) ≤ C₀ * volume (s ∩ ball y (r * (ε / 2))))
    (hs2 : ENNReal.ofReal ((r * (ε / 2)) ^ finrank ℝ E) ≤ C₀ * volume (ball y (r * (ε / 2)) \ s))
    (hbd : volume ((((fun z => x + r • z) ⁻¹' s) ∆ {z | ⟪z, ν⟫ < 0}) ∩ closedBall 0 2) <
      ENNReal.ofReal ((ε / 2) ^ finrank ℝ E) / (C₀ + 1)) :
    |⟪u, ν⟫| ≤ ε := by
  by_contra! hu_inner
  set n := finrank ℝ E
  set M := C₀ + 1
  have hM_top : M ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC₀, ENNReal.one_ne_top⟩
  have hball_sub : ball u (ε / 2) ⊆ closedBall (0 : E) 2 := fun z hz => by
    rw [mem_closedBall_zero_iff]
    have htri : ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
      simpa [sub_add_cancel] using norm_add_le (z - u) u
    have hzb : ‖z - u‖ < ε / 2 := by simpa [dist_eq_norm] using mem_ball.mp hz
    linarith only [htri, hzb, hu_norm, hε1]
  have hpre_ball : (fun z => x + r • z) ⁻¹' ball y (r * (ε / 2)) = ball u (ε / 2) := by
    ext z
    simp only [mem_preimage, mem_ball, dist_eq_norm, ← hxu, add_sub_add_left_eq_sub,
      ← smul_sub, norm_smul, Real.norm_of_nonneg hr_pos.le, mul_lt_mul_iff_right₀ hr_pos]
  have hscale (A : Set E) (hA : ENNReal.ofReal ((r * (ε / 2)) ^ n) ≤ C₀ * volume A) :
      ENNReal.ofReal ((ε / 2) ^ n) ≤ M * volume ((fun z => x + r • z) ⁻¹' A) := by
    have h1 : ENNReal.ofReal ((ε / 2) ^ n) =
        ENNReal.ofReal |(r ^ n)⁻¹| * ENNReal.ofReal ((r * (ε / 2)) ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity), mul_pow,
        inv_mul_cancel_left₀ (by positivity)]
    have hpre : (fun z => x + r • z) ⁻¹' A = (r • ·) ⁻¹' ((x + ·) ⁻¹' A) := rfl
    rw [h1, hpre, Measure.addHaar_preimage_smul volume hr_pos.ne', measure_preimage_add,
      mul_left_comm M]
    gcongr
    exact hA.trans (by gcongr; exact le_self_add)
  have hstrict : M * volume ((((fun z => x + r • z) ⁻¹' s) ∆ {z | ⟪z, ν⟫ < 0}) ∩ closedBall 0 2) <
      ENNReal.ofReal ((ε / 2) ^ n) :=
    (ENNReal.mul_lt_mul_right (by simp [M]) hM_top hbd).trans_eq
      (ENNReal.mul_div_cancel (by simp [M]) hM_top)
  rcases lt_trichotomy ⟪u, ν⟫ 0 with huneg | hu0 | hupos
  · have hsub : (fun z => x + r • z) ⁻¹' (ball y (r * (ε / 2)) \ s) ⊆
        (((fun z => x + r • z) ⁻¹' s) ∆ {z | ⟪z, ν⟫ < 0}) ∩ closedBall 0 2 := by
      intro z ⟨hzb, hzs⟩
      change z ∈ (fun z => x + r • z) ⁻¹' ball y (r * (ε / 2)) at hzb
      rw [hpre_ball] at hzb
      have hdiff : |⟪z - u, ν⟫| ≤ ε / 2 := (abs_real_inner_le_norm (z - u) ν).trans
        (by rw [hν, mul_one, ← dist_eq_norm]; exact (mem_ball.mp hzb).le)
      refine ⟨Or.inr ⟨show ⟪z, ν⟫ < 0 from ?_, hzs⟩, hball_sub hzb⟩
      have h1 : ε < -⟪u, ν⟫ := by rwa [abs_of_neg huneg] at hu_inner
      have h2 : ⟪z - u, ν⟫ ≤ ε / 2 := (abs_le.mp hdiff).2
      have h3 : ⟪z, ν⟫ = ⟪u, ν⟫ + ⟪z - u, ν⟫ := by rw [← inner_add_left, add_sub_cancel]
      linarith only [hε0, h1, h2, h3]
    exact ((hscale _ hs2).trans (mul_le_mul_right (measure_mono hsub) _)).not_gt hstrict
  · rw [hu0, abs_zero] at hu_inner
    linarith only [hε0, hu_inner]
  · have hsub : (fun z => x + r • z) ⁻¹' (s ∩ ball y (r * (ε / 2))) ⊆
        (((fun z => x + r • z) ⁻¹' s) ∆ {z | ⟪z, ν⟫ < 0}) ∩ closedBall 0 2 := by
      intro z ⟨hzs, hzb⟩
      change z ∈ (fun z => x + r • z) ⁻¹' ball y (r * (ε / 2)) at hzb
      rw [hpre_ball] at hzb
      have hdiff : |⟪z - u, ν⟫| ≤ ε / 2 := (abs_real_inner_le_norm (z - u) ν).trans
        (by rw [hν, mul_one, ← dist_eq_norm]; exact (mem_ball.mp hzb).le)
      refine ⟨Or.inl ⟨hzs, show ¬ ⟪z, ν⟫ < 0 from not_lt.mpr ?_⟩, hball_sub hzb⟩
      have h1 : ε < ⟪u, ν⟫ := by rwa [abs_of_pos hupos] at hu_inner
      have h2 : -(ε / 2) ≤ ⟪z - u, ν⟫ := (abs_le.mp hdiff).1
      have h3 : ⟪z, ν⟫ = ⟪u, ν⟫ + ⟪z - u, ν⟫ := by rw [← inner_add_left, add_sub_cancel]
      linarith only [hε0, h1, h2, h3]
    exact ((hscale _ hs1).trans (mul_le_mul_right (measure_mono hsub) _)).not_gt hstrict

/-- Uniform cone approximation on each lower-volume-density stratum of `∂*s` in dimension `n ≥ 2`:
for `k : ℕ`, `x ∈ ∂*s`, and `0 < ε ≤ 1`, points of the `k`-th stratum sufficiently close to `x`
lie inside the `ε`-cone around `(ℝ ∙ ν_s x)ᗮ`. -/
private theorem exists_infDist_orthogonal_span_outerNormal_le (hn : 2 ≤ finrank ℝ E) (k : ℕ)
    (hx : x ∈ reducedBoundary volume Ω s) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let q := NNReal.conjExponent (finrank ℝ E)
    let C₀ : ℝ≥0∞ :=
      ((1 + 2) * finrank ℝ E * eLpNormLESNormFDerivOneConst (volume : Measure E) q : ℝ≥0) ^
        finrank ℝ E
    ∃ r₀ > 0, ∀ y, y ∈ reducedBoundary volume Ω s →
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ (k + 1 : ℝ)⁻¹ →
        ENNReal.ofReal (ρ ^ finrank ℝ E) ≤ C₀ * volume (s ∩ ball y ρ) ∧
        ENNReal.ofReal (ρ ^ finrank ℝ E) ≤ C₀ * volume (ball y ρ \ s)) →
      dist y x < r₀ →
      infDist (y - x) ((ℝ ∙ outerNormal volume Ω s x)ᗮ : Set E) ≤ ε * dist y x := by
  intro q C₀
  have hC₀ : C₀ ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hM_top : C₀ + 1 ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC₀, ENNReal.one_ne_top⟩
  have hδ_pos : 0 < ENNReal.ofReal ((ε / 2) ^ finrank ℝ E) / (C₀ + 1) :=
    ENNReal.div_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hM_top
  obtain ⟨r₁, hr₁, hlt⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx
      (isCompact_closedBall (0 : E) 2)).eventually (gt_mem_nhds hδ_pos))
  refine ⟨min r₁ (k + 1 : ℝ)⁻¹, lt_min hr₁ (by positivity), fun y _ hyB hyr => ?_⟩
  rw [infDist_orthogonal_span_singleton (norm_outerNormal hx)]
  rcases eq_or_ne y x with rfl | hyx
  · simp
  set r := dist y x
  have hr_pos : 0 < r := dist_pos.mpr hyx
  have hρ_le : r * (ε / 2) ≤ (k + 1 : ℝ)⁻¹ :=
    (mul_le_of_le_one_right hr_pos.le (by linarith only [hε1])).trans
      (hyr.le.trans (min_le_right _ _))
  have hub := hyB (r * (ε / 2)) (by positivity) hρ_le
  have hle := abs_inner_le_of_blowUp_symmDiff_lt (norm_outerNormal hx)
    (u := r⁻¹ • (y - x))
    (by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr_pos.le), ← dist_eq_norm,
      inv_mul_cancel₀ hr_pos.ne'])
    hr_pos hε0 hε1 hC₀ (by simp [smul_inv_smul₀ hr_pos.ne']) hub.1 hub.2
    (hlt ⟨hr_pos, hyr.trans_le (min_le_left _ _)⟩)
  rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hr_pos)] at hle
  exact (inv_mul_le_iff₀ hr_pos).mp hle |>.trans_eq (mul_comm _ _)

/-- **De Giorgi's structure theorem, rectifiability part.** Against any additive Haar measure on a
finite-dimensional real inner product space `E`, the reduced boundary `∂*s` of any set `s` in any
open set `Ω` is countably `(finrank ℝ E - 1)`-rectifiable. -/
theorem countablyRectifiable_reducedBoundary [μ.IsAddHaarMeasure] :
    CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  rw [reducedBoundary_eq_volume]
  rcases lt_trichotomy (finrank ℝ E) 1 with hn0 | hn1 | hn2
  · rw [reducedBoundary_eq_empty_of_finrank_eq_zero (Nat.lt_one_iff.mp hn0)]
    exact CountablyRectifiable.empty
  · rw [hn1]
    exact (countable_reducedBoundary_of_finrank_eq_one (μ := volume) hn1).countablyRectifiable 0
  · set n := finrank ℝ E
    set q := NNReal.conjExponent n
    have hp : NNReal.HolderConjugate n q := .conjExponent (by exact_mod_cast hn2)
    set C₀ : ℝ≥0∞ :=
      ((1 + 2) * n * eLpNormLESNormFDerivOneConst (volume : Measure E) q : ℝ≥0) ^ n
    let B (k : ℕ) : Set E := {z ∈ reducedBoundary volume Ω s |
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ (k + 1 : ℝ)⁻¹ →
        ENNReal.ofReal (ρ ^ n) ≤ C₀ * volume (s ∩ ball z ρ) ∧
        ENNReal.ofReal (ρ ^ n) ≤ C₀ * volume (ball z ρ \ s)}
    have hcover : reducedBoundary volume Ω s = ⋃ k : ℕ, B k := by
      ext z
      refine ⟨fun hz => ?_, fun hz => let ⟨k, hk⟩ := mem_iUnion.mp hz; hk.1⟩
      obtain ⟨δ, hδ, hδB⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
        ((eventually_ofReal_pow_le_mul_measure_inter_ball hp hz one_lt_two).and
          (eventually_ofReal_pow_le_mul_measure_ball_sdiff hp hz one_lt_two))
      obtain ⟨k, hk⟩ := exists_nat_gt δ⁻¹
      refine mem_iUnion.mpr ⟨k, hz, fun ρ hρ hρk => hδB ⟨hρ, hρk.trans_lt ?_⟩⟩
      exact inv_lt_of_inv_lt₀ hδ (hk.trans_le (by exact_mod_cast Nat.le_add_right k 1))
    rw [hcover]
    refine CountablyRectifiable.iUnion fun k =>
      CountablyRectifiable.of_forall_exists_submodule_infDist_le fun x hx =>
        ⟨(ℝ ∙ outerNormal volume Ω s x)ᗮ, finrank_orthogonal_span_outerNormal hx.1,
          1 / 2, by norm_num, ?_⟩
    obtain ⟨r₀, hr₀, hcone⟩ := exists_infDist_orthogonal_span_outerNormal_le hn2 k hx.1
      (ε := 1 / 2) (by positivity) (by norm_num)
    exact ⟨r₀, hr₀, fun y hy hyr => hcone y hy.1 hy.2 hyr⟩

/-! ### Identification of the perimeter measure with `Hⁿ⁻¹⌊∂*s` -/

/-- If `lam` has `(n - 1)`-dimensional density `1` at every point of `B = ∂*s ∩ V` and both `lam`
and `νB = μHE[n - 1].restrict B` are finite measures, then `lam.rnDeriv νB =ᵐ[νB] 1`. -/
private theorem rnDeriv_eq_one_of_tendsto_closedBall_div {V : Opens E} {lam : Measure E}
    [IsFiniteMeasure lam] (hB_fin : μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ V) < ∞)
    (hdens_lam : ∀ x ∈ reducedBoundary volume Ω s ∩ V,
      Tendsto (fun r => lam (closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r)) (𝓝[>] 0) (𝓝 1)) :
    lam.rnDeriv (μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s ∩ V)) =ᵐ[
      μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s ∩ V)] 1 := by
  set n := finrank ℝ E
  set B : Set E := reducedBoundary volume Ω s ∩ V
  have hBm : MeasurableSet B := measurableSet_reducedBoundary.inter V.isOpen.measurableSet
  set νB : Measure E := μHE[n - 1].restrict B
  have : IsFiniteMeasure νB := ⟨by rw [Measure.restrict_apply_univ]; exact hB_fin⟩
  have hrect_dens : ∀ᵐ x ∂νB, Tendsto (fun r => νB (closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_restrict_iff' hBm]
    filter_upwards [((countablyRectifiable_reducedBoundary (μ := volume) (Ω := Ω) (s := s)).mono
      inter_subset_left).ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
      hBm.nullMeasurableSet] with x hx hxB
    refine (hx hxB).congr' (.of_forall fun r => ?_)
    dsimp only [νB, B]
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv lam νB, hrect_dens,
    ae_restrict_mem hBm] with x hbes hνx hxB
  rw [Pi.one_apply]
  refine tendsto_nhds_unique hbes ?_
  have hdiv := ENNReal.Tendsto.div (hdens_lam x hxB) (.inl one_ne_zero) hνx
    (.inl ENNReal.one_ne_top)
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hνx.eventually (isOpen_ne.mem_nhds one_ne_zero),
    hνx.eventually (isOpen_ne.mem_nhds ENNReal.one_ne_top)] with r (hr : 0 < r) _ htop
  have hv0 : volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r) ≠ 0 :=
    (measure_closedBall_pos volume _ hr).ne'
  have hvtop : volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r) ≠ ∞ :=
    measure_closedBall_lt_top.ne
  have hνtop : νB (closedBall x r) ≠ ∞ :=
    fun h => htop (by rw [h, ENNReal.top_div_of_ne_top hvtop])
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (.inr (ENNReal.inv_ne_top.mpr hv0)) (.inl hνtop), inv_inv,
    mul_comm (νB _)⁻¹, ← mul_assoc, mul_assoc (lam _), ENNReal.inv_mul_cancel hv0 hvtop, mul_one]

/-- On a relatively compact open subset `V` with `closure V ⊆ Ω`, the perimeter measure `|Dχ_s|`
restricted to `V` and pushed forward to `E` equals `μHE[finrank ℝ E - 1]` restricted to
`∂*s ∩ V`. -/
private theorem map_restrict_variationMeasure_eq_restrict_reducedBoundary_of_isCompact_closure
    {V : Opens E} (hVc : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Ω) :
    ((variationMeasure volume Ω (s.indicator 1)).restrict
        (((↑) : Ω → E) ⁻¹' V)).map ((↑) : Ω → E) =
      μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s ∩ V) := by
  set n := finrank ℝ E
  set lam : Measure E :=
    ((variationMeasure volume Ω (s.indicator 1)).restrict (((↑) : Ω → E) ⁻¹' V)).map ((↑) : Ω → E)
  set B : Set E := reducedBoundary volume Ω s ∩ V
  have hBm : MeasurableSet B := measurableSet_reducedBoundary.inter V.isOpen.measurableSet
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' closure (V : Set E)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hVc (by rwa [Subtype.range_coe])
  have : IsFiniteMeasure lam := ⟨by
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    exact (measure_mono (preimage_mono subset_closure)).trans_lt hK'.measure_lt_top⟩
  have hdens_lam (x : E) (hx : x ∈ B) :
      Tendsto (fun r => lam (closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r)) (𝓝[>] 0) (𝓝 1) := by
    refine (tendsto_variationMeasure_volume_closedBall_div hx.1).congr' ?_
    obtain ⟨δ, hδ, hδV⟩ := nhds_basis_closedBall.mem_iff.mp (V.isOpen.mem_nhds hx.2)
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hrδ⟩
    rw [Measure.map_apply measurable_subtype_coe measurableSet_closedBall,
      Measure.restrict_apply (measurableSet_closedBall.preimage measurable_subtype_coe),
      inter_eq_left.mpr (preimage_mono ((closedBall_subset_closedBall hrδ.le).trans hδV))]
  have hB_fin : μHE[n - 1] B < ∞ := by
    have hle := Measure.mul_euclideanHausdorffMeasure_le_measure_of_isOpen lam (n - 1) (c := 1 / 2)
      isOpen_univ (subset_univ B) fun x hx => ((((hdens_lam x hx).eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ≥0∞) < 1))).and self_mem_nhdsWithin).mono
        fun r ⟨hgt, (hr : 0 < r)⟩ => ((ENNReal.lt_div_iff_mul_lt
          (.inl (measure_closedBall_pos volume _ hr).ne')
          (.inl measure_closedBall_lt_top.ne)).mp hgt).le).frequently
    by_contra! htop
    rw [top_le_iff] at htop
    exact (hle.trans_lt (measure_lt_top lam univ)).ne (by rw [htop, ENNReal.mul_top (by norm_num)])
  set νB : Measure E := μHE[n - 1].restrict B
  have : IsFiniteMeasure νB := ⟨by rw [Measure.restrict_apply_univ]; exact hB_fin⟩
  have hac : lam ≪ νB := Measure.AbsolutelyContinuous.mk fun N hNm hN0 => by
    rw [Measure.restrict_apply hNm] at hN0
    rw [Measure.map_apply measurable_subtype_coe hNm,
      Measure.restrict_apply (hNm.preimage measurable_subtype_coe)]
    have hsub : ((↑) : Ω → E) ⁻¹' N ∩ ((↑) : Ω → E) ⁻¹' (V : Set E) ⊆
        ((↑) : Ω → E) ⁻¹' (N ∩ B) ∪ {z : Ω | (z : E) ∉ reducedBoundary volume Ω s} :=
      fun z ⟨hzN, hzV⟩ =>
        (em ((z : E) ∈ reducedBoundary volume Ω s)).imp (fun hzR => ⟨hzN, hzR, hzV⟩) id
    refine measure_mono_null hsub (measure_union_null ?_ (ae_iff.mp ae_mem_reducedBoundary))
    have h0 := map_variationMeasure_absolutelyContinuous_euclideanHausdorffMeasure
      (μ := volume) (Ω := Ω) (s := s) hN0
    rwa [Measure.map_apply measurable_subtype_coe (hNm.inter hBm)] at h0
  calc lam = νB.withDensity (lam.rnDeriv νB) := (Measure.withDensity_rnDeriv_eq lam νB hac).symm
    _ = νB.withDensity 1 :=
        withDensity_congr_ae (rnDeriv_eq_one_of_tendsto_closedBall_div hB_fin hdens_lam)
    _ = νB := withDensity_one

/-- **De Giorgi's structure theorem, measure-representation part (Lebesgue measure).** The
perimeter measure `|Dχ_s|` of `s` in `Ω`, pushed forward to `E`, is the `(n - 1)`-dimensional
Euclidean Hausdorff measure restricted to the reduced boundary `∂*s`. -/
@[simp]
theorem map_variationMeasure_volume_indicator_eq_restrict_reducedBoundary :
    (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) =
      μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s) := by
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, hVuniv⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  ext A hAm
  have h1 : ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)) A =
      ⨆ k, (((variationMeasure volume Ω (s.indicator 1)).restrict
        (((↑) : Ω → E) ⁻¹' V k)).map ((↑) : Ω → E)) A := by
    rw [Measure.map_apply measurable_subtype_coe hAm]
    have hcov : ((↑) : Ω → E) ⁻¹' A = ⋃ k, ((↑) : Ω → E) ⁻¹' A ∩ ((↑) : Ω → E) ⁻¹' V k := by
      rw [← inter_iUnion, hVuniv, inter_univ]
    have hmono₁ : Monotone fun k => ((↑) : Ω → E) ⁻¹' A ∩ ((↑) : Ω → E) ⁻¹' V k :=
      fun _ _ hij => inter_subset_inter_right _ (preimage_mono (hVmono hij))
    rw [hcov, hmono₁.measure_iUnion]
    refine iSup_congr fun k => ?_
    rw [Measure.map_apply measurable_subtype_coe hAm,
      Measure.restrict_apply (hAm.preimage measurable_subtype_coe)]
  have h2 : (μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s)) A =
      ⨆ k, (μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s ∩ V k)) A := by
    rw [Measure.restrict_apply hAm]
    have hcov : A ∩ reducedBoundary volume Ω s =
        ⋃ k, A ∩ (reducedBoundary volume Ω s ∩ V k) := by
      ext y
      simp only [mem_inter_iff, mem_iUnion]
      refine ⟨fun ⟨hyA, hyB⟩ => ?_, fun ⟨_, hyA, hyB, _⟩ => ⟨hyA, hyB⟩⟩
      obtain ⟨k, hyk⟩ := mem_iUnion.mp (hVU.symm.subset (reducedBoundary_subset hyB))
      exact ⟨k, hyA, hyB, hyk⟩
    have hmono₂ : Monotone fun k => A ∩ (reducedBoundary volume Ω s ∩ V k) :=
      fun _ _ hij => inter_subset_inter_right _ (inter_subset_inter_right _ (hVmono hij))
    rw [hcov, hmono₂.measure_iUnion]
    exact iSup_congr fun k => (Measure.restrict_apply hAm).symm
  rw [h1, h2]
  exact iSup_congr fun k => by
    rw [map_restrict_variationMeasure_eq_restrict_reducedBoundary_of_isCompact_closure
      (hVc k) (hVΩ k)]

/-- **De Giorgi's structure theorem, measure-representation part.** Against any additive Haar
measure `μ`, the perimeter measure `|Dχ_s|` of `s` in `Ω`, pushed forward to `E`, is
`Measure.addHaarScalarFactor μ volume` times `μHE[finrank ℝ E - 1]` restricted to `∂*s`. -/
theorem map_variationMeasure_indicator_eq_smul_restrict_reducedBoundary [μ.IsAddHaarMeasure] :
    (variationMeasure μ Ω (s.indicator 1)).map ((↑) : Ω → E) =
      Measure.addHaarScalarFactor μ volume •
        μHE[finrank ℝ E - 1].restrict (reducedBoundary μ Ω s) := by
  have hμ := Measure.isAddLeftInvariant_eq_smul_of_regular μ (volume : Measure E)
  conv_lhs => rw [hμ]
  rw [variationMeasure_smul_measure, Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    map_variationMeasure_volume_indicator_eq_restrict_reducedBoundary,
    reducedBoundary_eq_volume (μ := μ)]

/-- On `Ω`, the perimeter measure `|Dχ_s|` is the pullback along `((↑) : Ω → E)` of
`Measure.addHaarScalarFactor μ volume • μHE[finrank ℝ E - 1].restrict ∂*s`. -/
theorem variationMeasure_indicator_eq_comap_restrict_reducedBoundary [μ.IsAddHaarMeasure] :
    variationMeasure μ Ω (s.indicator 1) =
      (Measure.addHaarScalarFactor μ volume •
        μHE[finrank ℝ E - 1].restrict (reducedBoundary μ Ω s)).comap ((↑) : Ω → E) :=
  (Ω.isOpenEmbedding'.measurableEmbedding.comap_map _).symm.trans
    (congrArg (Measure.comap ((↑) : Ω → E))
      map_variationMeasure_indicator_eq_smul_restrict_reducedBoundary)

/-- On `Ω`, the Lebesgue perimeter measure `|Dχ_s|` is the pullback along `((↑) : Ω → E)` of
`μHE[finrank ℝ E - 1].restrict ∂*s`. -/
theorem variationMeasure_volume_indicator_eq_comap_restrict_reducedBoundary :
    variationMeasure volume Ω (s.indicator 1) =
      (μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s)).comap ((↑) : Ω → E) := by
  simpa using variationMeasure_indicator_eq_comap_restrict_reducedBoundary
    (μ := volume) (Ω := Ω) (s := s)

/-- Evaluation of the perimeter measure on an arbitrary subset `S : Set Ω` (measurable or not). -/
theorem variationMeasure_indicator_apply [μ.IsAddHaarMeasure] (S : Set Ω) :
    variationMeasure μ Ω (s.indicator 1) S =
      Measure.addHaarScalarFactor μ volume •
        μHE[finrank ℝ E - 1] (((↑) '' S) ∩ reducedBoundary μ Ω s) := by
  rw [variationMeasure_indicator_eq_comap_restrict_reducedBoundary,
    Ω.isOpenEmbedding'.measurableEmbedding.comap_apply, smul_apply,
    Measure.restrict_apply' measurableSet_reducedBoundary]

/-- Evaluation of the Lebesgue perimeter measure on an arbitrary subset `S : Set Ω` (measurable or
not). -/
theorem variationMeasure_volume_indicator_apply (S : Set Ω) :
    variationMeasure volume Ω (s.indicator 1) S =
      μHE[finrank ℝ E - 1] (((↑) '' S) ∩ reducedBoundary volume Ω s) := by
  simpa using variationMeasure_indicator_apply (μ := volume) (Ω := Ω) (s := s) S

/-- Evaluation of the perimeter measure on the preimage in `Ω` of an arbitrary set `t : Set E`
(measurable or not). -/
theorem variationMeasure_indicator_preimage [μ.IsAddHaarMeasure] (t : Set E) :
    variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' t) =
      Measure.addHaarScalarFactor μ volume •
        μHE[finrank ℝ E - 1] (t ∩ reducedBoundary μ Ω s) := by
  rw [variationMeasure_indicator_apply, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_assoc, inter_eq_right.mpr reducedBoundary_subset]

/-- Evaluation of the Lebesgue perimeter measure on the preimage in `Ω` of an arbitrary set
`t : Set E` (measurable or not). -/
theorem variationMeasure_volume_indicator_preimage (t : Set E) :
    variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' t) =
      μHE[finrank ℝ E - 1] (t ∩ reducedBoundary volume Ω s) := by
  simpa using variationMeasure_indicator_preimage (μ := volume) (Ω := Ω) (s := s) t

/-- Every compact subset `K ⊆ Ω` meets the reduced boundary `∂*s` in a set of finite
`(n - 1)`-dimensional Hausdorff measure. -/
theorem euclideanHausdorffMeasure_inter_reducedBoundary_lt_top [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    μHE[finrank ℝ E - 1] (K ∩ reducedBoundary μ Ω s) < ∞ := by
  rw [reducedBoundary_eq_volume, ← variationMeasure_volume_indicator_preimage]
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
  exact hK'.measure_lt_top

/-- For `Ω = ⊤`, the `(n - 1)`-dimensional Hausdorff measure restricted to the reduced boundary
`∂*s` is locally finite on `E`. -/
instance isLocallyFiniteMeasure_euclideanHausdorffMeasure_restrict_reducedBoundary_top
    [μ.IsAddHaarMeasure] :
    IsLocallyFiniteMeasure (μHE[finrank ℝ E - 1].restrict (reducedBoundary μ ⊤ s)) := by
  refine ⟨fun x => ⟨closedBall x 1, closedBall_mem_nhds x one_pos, ?_⟩⟩
  rw [Measure.restrict_apply' measurableSet_reducedBoundary]
  exact euclideanHausdorffMeasure_inter_reducedBoundary_lt_top (isCompact_closedBall x 1)
    (subset_univ _)

/-- For a set `s` of locally finite perimeter in `Ω` and any open `U ≤ Ω`, the perimeter of `s` in
`U` is `Measure.addHaarScalarFactor μ volume • μHE[finrank ℝ E - 1] (U ∩ ∂*s)`. -/
theorem perimeter_eq_smul_euclideanHausdorffMeasure_inter_reducedBoundary [μ.IsAddHaarMeasure]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ W : Opens E, K ⊆ (W : Set E) ∧ totalVariationOn μ W (s.indicator 1) ≠ ∞)
    {U : Opens E} (hU : U ≤ Ω) :
    perimeter μ U s = Measure.addHaarScalarFactor μ volume •
      μHE[finrank ℝ E - 1] ((U : Set E) ∩ reducedBoundary μ Ω s) := by
  rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin hU,
    variationMeasure_indicator_preimage]

/-- For a set `s` of locally finite perimeter in `Ω` with respect to Lebesgue measure and any open
`U ≤ Ω`, `P(s; U) = μHE[finrank ℝ E - 1] (U ∩ ∂*s)`. -/
theorem perimeter_volume_eq_euclideanHausdorffMeasure_inter_reducedBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ W : Opens E, K ⊆ (W : Set E) ∧ totalVariationOn volume W (s.indicator 1) ≠ ∞)
    {U : Opens E} (hU : U ≤ Ω) :
    perimeter volume U s = μHE[finrank ℝ E - 1] ((U : Set E) ∩ reducedBoundary volume Ω s) := by
  simpa using perimeter_eq_smul_euclideanHausdorffMeasure_inter_reducedBoundary hu hfin hU

/-- **Perimeter equals `Hⁿ⁻¹(∂*s)` for sets of finite perimeter.** If `s` is null-measurable on `Ω`
and has finite perimeter in `Ω`, then
`perimeter μ Ω s = Measure.addHaarScalarFactor μ volume • μHE[finrank ℝ E - 1] (∂*s)`. -/
theorem perimeter_eq_smul_euclideanHausdorffMeasure_reducedBoundary [μ.IsAddHaarMeasure]
    (hs : NullMeasurableSet s (μ.restrict Ω)) (hP : perimeter μ Ω s ≠ ∞) :
    perimeter μ Ω s = Measure.addHaarScalarFactor μ volume •
      μHE[finrank ℝ E - 1] (reducedBoundary μ Ω s) := by
  have hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const hs 1
  have hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ W : Opens E, K ⊆ (W : Set E) ∧ totalVariationOn μ W (s.indicator 1) ≠ ∞ :=
    fun _ _ hKΩ => ⟨Ω, hKΩ, by rwa [← perimeter_def]⟩
  rw [perimeter_eq_smul_euclideanHausdorffMeasure_inter_reducedBoundary hu hfin le_rfl,
    inter_eq_right.mpr reducedBoundary_subset]

/-- **Perimeter equals `Hⁿ⁻¹(∂*s)` for sets of finite perimeter (Lebesgue measure).** If `s` is
null-measurable on `Ω` and `P(s; Ω) < ∞`, then `P(s; Ω) = μHE[finrank ℝ E - 1] (∂*s)`. -/
theorem perimeter_volume_eq_euclideanHausdorffMeasure_reducedBoundary
    (hs : NullMeasurableSet s (volume.restrict Ω)) (hP : perimeter volume Ω s ≠ ∞) :
    perimeter volume Ω s = μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s) := by
  simpa using perimeter_eq_smul_euclideanHausdorffMeasure_reducedBoundary hs hP

/-! ### Pointwise Hausdorff density one and approximate tangent hyperplanes on `∂*s` -/

/-- **Pointwise `(n - 1)`-dimensional Hausdorff density one on the reduced boundary.** At *every*
point `x` of `∂*s` (not merely `Hⁿ⁻¹`-almost everywhere),
`μHE[finrank ℝ E - 1] (∂*s ∩ closedBall x r) / ω_{n-1} r^(n-1) → 1` as `r → 0⁺`. -/
theorem tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_div
    [μ.IsAddHaarMeasure] (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r =>
      μHE[finrank ℝ E - 1] (reducedBoundary μ Ω s ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r))
      (𝓝[>] 0) (𝓝 1) := by
  rw [reducedBoundary_eq_volume] at hx ⊢
  simpa only [variationMeasure_volume_indicator_preimage, inter_comm] using
    tendsto_variationMeasure_volume_closedBall_div hx

/-- For small `r > 0`, the normalized perimeter of the blow-up `(fun w => x + r • w) ⁻¹' (s ∩ Ω)`
on the unit slab `{w ∈ ball 0 1 | |⟪w, ν_s x⟫| < η}` equals the `(n - 1)`-dimensional density
ratio of `∂*s` inside the scaled slab `{z ∈ ball x r | |⟪z - x, ν_s x⟫| < η * r}`. -/
private theorem eventually_perimeter_slab_preimage_add_smul_div
    (hx : x ∈ reducedBoundary volume Ω s) (η : ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      perimeter volume ⟨{w ∈ ball 0 1 | |⟪w, outerNormal volume Ω s x⟫| < η},
        isOpen_ball.inter (isOpen_lt
          (by fun_prop : Continuous fun w : E => |⟪w, outerNormal volume Ω s x⟫|)
          continuous_const)⟩ ((fun w => x + r • w) ⁻¹' (s ∩ Ω)) /
        volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) 1) =
      μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩
        {z ∈ ball x r | |⟪z - x, outerNormal volume Ω s x⟫| < η * r}) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r) := by
  set n := finrank ℝ E
  set ν := outerNormal volume Ω s x
  have : Nontrivial E :=
    ⟨⟨ν, 0, norm_ne_zero_iff.mp ((norm_outerNormal hx) ▸ one_ne_zero)⟩⟩
  have hωtop : volume (ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1) ≠ ∞ := measure_ball_lt_top.ne
  set W₀ : Opens E := ⟨{w ∈ ball 0 1 | |⟪w, ν⟫| < η},
    isOpen_ball.inter (isOpen_lt (by fun_prop : Continuous fun w : E => |⟪w, ν⟫|) continuous_const)⟩
  let W (r : ℝ) : Opens E := ⟨{z ∈ ball x r | |⟪z - x, ν⟫| < η * r},
    isOpen_ball.inter (isOpen_lt (by fun_prop : Continuous fun z : E => |⟪z - x, ν⟫|)
      continuous_const)⟩
  have hae_s' : (s ∩ Ω : Set E) =ᵐ[volume.restrict Ω] s := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy; simp [hy]
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r ⟨hr, hrr₀⟩
  have hWrΩ : W r ≤ Ω := fun _ hz => hr₀Ω (ball_subset_ball hrr₀.le hz.1)
  let W_tr : Opens E := ⟨{z ∈ ball 0 r | |⟪z, ν⟫| < η * r},
    isOpen_ball.inter (isOpen_lt (by fun_prop : Continuous fun z : E => |⟪z, ν⟫|) continuous_const)⟩
  have hsmul₁ : ∀ w ∈ W₀, r • w ∈ W_tr := fun w hw =>
    ⟨by simpa [norm_smul, abs_of_pos hr] using
        mul_lt_of_lt_one_right hr (mem_ball_zero_iff.mp hw.1),
      by rw [real_inner_smul_left, abs_mul, abs_of_pos hr, mul_comm]
         exact mul_lt_mul_of_pos_right hw.2 hr⟩
  have hsmul₂ : ∀ z ∈ W_tr, r⁻¹ • z ∈ W₀ := fun z hz =>
    ⟨by rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact (inv_mul_lt_iff₀ hr).mpr (by simpa using mem_ball_zero_iff.mp hz.1),
      by rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hr)]
         exact (inv_mul_lt_iff₀ hr).mpr (by linarith only [hz.2])⟩
  have htr₁ : ∀ z ∈ W_tr, z + x ∈ W r := fun z hz =>
    ⟨by simpa [dist_eq_norm] using hz.1, by simpa using hz.2⟩
  have htr₂ : ∀ z ∈ W r, z - x ∈ W_tr := fun z hz =>
    ⟨by simpa [dist_eq_norm] using hz.1, by simpa using hz.2⟩
  have hP_smul : perimeter volume W₀ ((fun w => x + r • w) ⁻¹' (s ∩ Ω)) =
      ENNReal.ofReal (r / r ^ n) * perimeter volume (W r) (s ∩ Ω) := by
    rw [show (fun w => x + r • w) ⁻¹' (s ∩ Ω) = (r • ·) ⁻¹' ((· + x) ⁻¹' (s ∩ Ω)) by
        ext w; simp [add_comm],
      perimeter_preimage_smul (Ω := W_tr) hr hsmul₁ hsmul₂,
      perimeter_preimage_add_right (Ω := W r) htr₁ htr₂]
  have hP_s : perimeter volume (W r) (s ∩ Ω) = μHE[n - 1] (reducedBoundary volume Ω s ∩ W r) := by
    rw [perimeter_congr_ae (hae_s'.filter_mono (ae_mono (Measure.restrict_mono hWrΩ le_rfl))),
      perimeter_volume_eq_euclideanHausdorffMeasure_inter_reducedBoundary hu hfin hWrΩ, inter_comm]
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨_, (Nat.sub_add_cancel finrank_pos).symm⟩
  have hfac : ENNReal.ofReal (r / r ^ n) = (ENNReal.ofReal (r ^ (n - 1)))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity)]; congr 1
    rw [hm, Nat.add_sub_cancel, pow_succ]; field_simp
  rw [hP_smul, hP_s, hfac, Measure.addHaar_closedBall volume _ hr.le, finrank_euclideanSpace_fin,
    div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (.inr hωtop) (.inl ENNReal.ofReal_ne_top),
    mul_comm (ENNReal.ofReal (r ^ (n - 1)))⁻¹, mul_assoc]
  rfl

/-- At a point `x` of the reduced boundary in dimension `n ≥ 2`, the `(n - 1)`-dimensional
Hausdorff measure of `∂*s` inside the thin open slab
`{z ∈ ball x r | |⟪z - x, ν_s x⟫| < η * r}` has asymptotic density `1`. -/
private theorem tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_slab_div
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary volume Ω s) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun r =>
      μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩
        {z ∈ ball x r | |⟪z - x, outerNormal volume Ω s x⟫| < η * r}) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r))
      (𝓝[>] 0) (𝓝 1) := by
  set n := finrank ℝ E
  set ν := outerNormal volume Ω s x
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1)
  have hω0 : ω ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set W₀ : Opens E := ⟨{w ∈ ball 0 1 | |⟪w, ν⟫| < η},
    isOpen_ball.inter (isOpen_lt (by fun_prop : Continuous fun w : E => |⟪w, ν⟫|) continuous_const)⟩
  set s' := s ∩ Ω
  have hae_s' : s' =ᵐ[volume.restrict Ω] s := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy; simp [s', hy]
  have hx' : x ∈ reducedBoundary volume Ω s' := by rwa [reducedBoundary_inter_opens]
  have hPW₀ : perimeter volume W₀ {w | ⟪w, ν⟫ < 0} = ω := by
    have heq : (W₀ : Set E) ∩ {w | ⟪w, ν⟫ = 0} = ball (0 : E) 1 ∩ {w | ⟪w, ν⟫ = 0} := by
      ext w; simp only [W₀, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨⟨hw1, _⟩, hw0⟩ => ⟨hw1, hw0⟩,
        fun ⟨hw1, hw0⟩ => ⟨⟨hw1, by rw [hw0, abs_zero]; exact hη⟩, hw0⟩⟩
    have hball := perimeter_ball_setOf_inner_lt hν (0 : E) one_pos
    rw [inner_zero_left, ENNReal.ofReal_one, one_pow, one_mul,
      perimeter_setOf_inner_lt hν 0 ⟨ball 0 1, isOpen_ball⟩] at hball
    rw [perimeter_setOf_inner_lt hν 0 W₀, heq]
    exact hball
  have hν_eq : outerNormal volume Ω s' x = ν := by rw [outerNormal_congr_ae hae_s']
  have hliminf_W₀ : ω ≤ liminf (fun r : ℝ =>
      perimeter volume W₀ ((fun w => x + r • w) ⁻¹' s')) (𝓝[>] 0) := by
    rw [← hPW₀, ← hν_eq]
    refine perimeter_le_liminf ?_
      (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet
      fun K hK _ => tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx' hK
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact (nullMeasurableSet_inter_of_mem_reducedBoundary hx).preimage
      (Measure.quasiMeasurePreserving_add_smul volume x hr.ne')
  have h1_le : 1 ≤ liminf (fun r => μHE[n - 1] (reducedBoundary volume Ω s ∩
      {z ∈ ball x r | |⟪z - x, ν⟫| < η * r}) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r)) (𝓝[>] 0) := by
    rw [← liminf_congr (eventually_perimeter_slab_preimage_add_smul_div hx η), le_liminf_iff]
    intro b hb
    have hbω : b * ω < ω := by simpa [mul_comm ω] using ENNReal.mul_lt_mul_right hω0 hωtop hb
    filter_upwards [eventually_lt_of_lt_liminf (hbω.trans_le hliminf_W₀)] with r hr
    exact (ENNReal.lt_div_iff_mul_lt (.inl hω0) (.inl hωtop)).mpr hr
  have hsub_cb : ∀ r : ℝ, reducedBoundary volume Ω s ∩ {z ∈ ball x r | |⟪z - x, ν⟫| < η * r} ⊆
      reducedBoundary volume Ω s ∩ closedBall x r :=
    fun _ _ ⟨hzB, hzb, _⟩ => ⟨hzB, ball_subset_closedBall hzb⟩
  exact tendsto_of_le_liminf_of_limsup_le h1_le
    ((limsup_le_limsup (.of_forall fun r => ENNReal.div_le_div_right
      (measure_mono (hsub_cb r)) _)).trans_eq
      (tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_div hx).limsup_eq)

/-- Rescaling `closedBall x (δ * r)` gives asymptotic `(n - 1)`-dimensional ratio `δ ^ (n - 1)`. -/
private theorem tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_mul_div
    (hx : x ∈ reducedBoundary volume Ω s) {δ : ℝ} (hδ_pos : 0 < δ) :
    Tendsto (fun r =>
      μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ closedBall x (δ * r)) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (δ ^ (finrank ℝ E - 1)))) := by
  set n := finrank ℝ E
  have hcomp : Tendsto (fun r : ℝ => δ * r) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using (continuous_const_mul δ).tendsto 0 |>.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => mul_pos hδ_pos hr)
  have hmul := ENNReal.Tendsto.const_mul
    ((tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_div hx).comp hcomp)
    (a := ENNReal.ofReal (δ ^ (n - 1))) (.inr ENNReal.ofReal_ne_top)
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  dsimp only [Function.comp_def]
  set A := μHE[n - 1] (reducedBoundary volume Ω s ∩ closedBall x (δ * r))
  set B := ENNReal.ofReal (r ^ (n - 1)) * volume (ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1)
  set D := ENNReal.ofReal (δ ^ (n - 1))
  have hd0 : D ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hdtop : D ≠ ∞ := ENNReal.ofReal_ne_top
  rw [Measure.addHaar_closedBall volume _ (mul_nonneg hδ_pos.le hr.le),
    Measure.addHaar_closedBall volume _ hr.le, finrank_euclideanSpace_fin, mul_pow,
    ENNReal.ofReal_mul (by positivity), mul_assoc]
  change D * (A / (D * B)) = A / B
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (.inl hd0) (.inl hdtop),
    mul_comm A, ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, one_mul, mul_comm]

/-- In dimension `n ≥ 2`, the part of `∂*s ∩ closedBall x r` outside the thin slab
`{z ∈ ball x r | |⟪z - x, ν_s x⟫| < η * r}` has `(n - 1)`-dimensional density zero. -/
private theorem tendsto_euclideanHausdorffMeasure_reducedBoundary_closedBall_sdiff_slab_div
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary volume Ω s) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun r =>
      μHE[finrank ℝ E - 1] ((reducedBoundary volume Ω s ∩ closedBall x r) \
        {z ∈ ball x r | |⟪z - x, outerNormal volume Ω s x⟫| < η * r}) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r))
      (𝓝[>] 0) (𝓝 0) := by
  set W := fun r : ℝ => {z ∈ ball x r | |⟪z - x, outerNormal volume Ω s x⟫| < η * r}
  have hdiff := ENNReal.Tendsto.sub
    (tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_div hx)
    (tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_slab_div hn hx hη)
    (.inl ENNReal.one_ne_top)
  rw [tsub_self] at hdiff
  obtain ⟨r₁, hr₁, hr₁Ω⟩ :=
    nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  refine hdiff.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r ⟨hr, hrr₁⟩
  have hfin_cb : μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ closedBall x r) < ∞ := by
    rw [inter_comm]
    exact euclideanHausdorffMeasure_inter_reducedBoundary_lt_top (isCompact_closedBall x r)
      ((closedBall_subset_closedBall hrr₁.le).trans hr₁Ω)
  have hsub : reducedBoundary volume Ω s ∩ W r ⊆ reducedBoundary volume Ω s ∩ closedBall x r :=
    fun _ ⟨hzB, hzb, _⟩ => ⟨hzB, ball_subset_closedBall hzb⟩
  have hWm : MeasurableSet (W r) :=
    measurableSet_ball.inter (measurableSet_lt
      (by fun_prop : Measurable fun z : E => |⟪z - x, outerNormal volume Ω s x⟫|) measurable_const)
  rw [show (reducedBoundary volume Ω s ∩ closedBall x r) \ W r =
      (reducedBoundary volume Ω s ∩ closedBall x r) \ (reducedBoundary volume Ω s ∩ W r) by
      ext z; simp only [Set.mem_sdiff, mem_inter_iff]; tauto,
    measure_sdiff hsub (measurableSet_reducedBoundary.inter hWm).nullMeasurableSet
      ((measure_mono hsub).trans_lt hfin_cb).ne,
    ENNReal.sub_div fun _ _ => (measure_closedBall_pos volume _ hr).ne']

/-- **Pointwise approximate tangent hyperplanes on the reduced boundary.** At *every* point `x` of
`∂*s` and for every `ε > 0`, the part of `∂*s` outside the `ε`-cone around the orthogonal
hyperplane `(ℝ ∙ ν_s x)ᗮ` has `(n - 1)`-dimensional density zero at `x`. -/
theorem tendsto_euclideanHausdorffMeasure_reducedBoundary_outside_cone_div
    [μ.IsAddHaarMeasure] (hx : x ∈ reducedBoundary μ Ω s) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[finrank ℝ E - 1]
        {z ∈ reducedBoundary μ Ω s ∩ closedBall x r |
          ε * dist z x < infDist (z - x) ((ℝ ∙ outerNormal μ Ω s x)ᗮ : Set E)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r))
      (𝓝[>] 0) (𝓝 0) := by
  rw [reducedBoundary_eq_volume] at hx ⊢
  rw [outerNormal_eq_volume]
  rcases lt_trichotomy (finrank ℝ E) 1 with hn0 | hn1 | hn2
  · exact False.elim
      ((reducedBoundary_eq_empty_of_finrank_eq_zero (Nat.lt_one_iff.mp hn0)).subset hx)
  · obtain ⟨r₀, hr₀, -, hiso, -⟩ :=
      exists_ball_ae_eq_setOf_inner_lt_of_finrank_eq_one (μ := volume) hn1 hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r ⟨_, hrr₀⟩
    have hempty : {z ∈ reducedBoundary volume Ω s ∩ closedBall x r |
        ε * dist z x < infDist (z - x) ((ℝ ∙ outerNormal volume Ω s x)ᗮ : Set E)} = ∅ :=
      eq_empty_of_forall_notMem fun z ⟨⟨hzB, hzcb⟩, hzcone⟩ => by
        rw [infDist_orthogonal_span_singleton (norm_outerNormal hx),
          hiso.subset ⟨closedBall_subset_ball hrr₀ hzcb, hzB⟩] at hzcone
        simp at hzcone
    rw [hempty]
    simp
  · set n := finrank ℝ E
    set ν := outerNormal volume Ω s x
    set Vvol : ℝ → ℝ≥0∞ := fun r => volume (closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) r)
    refine tendsto_of_le_liminf_of_limsup_le (by simp) (le_of_forall_gt fun b hb => ?_)
    have hn1_pos : 0 < n - 1 := by omega
    have hcont_pow : Continuous fun t : ℝ => ENNReal.ofReal (t ^ (n - 1)) :=
      ENNReal.continuous_ofReal.comp (continuous_pow (n - 1))
    have hlim_pow : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ (n - 1))) (𝓝[>] 0) (𝓝 0) := by
      simpa [zero_pow hn1_pos.ne'] using hcont_pow.tendsto 0 |>.mono_left nhdsWithin_le_nhds
    obtain ⟨δ₁, hδ₁, hδ₁b⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
      (hlim_pow.eventually (gt_mem_nhds hb))
    set δ := min (δ₁ / 2) (1 / 2)
    have hδ_pos : 0 < δ := lt_min (half_pos hδ₁) (by norm_num)
    have hδb : ENNReal.ofReal (δ ^ (n - 1)) < b :=
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hδ_pos.le (min_le_left _ _) _)).trans_lt
        (hδ₁b ⟨half_pos hδ₁, half_lt_self hδ₁⟩)
    let W (r : ℝ) : Set E := {z ∈ ball x r | |⟪z - x, ν⟫| < (ε * δ) * r}
    have hbound : ∀ r > 0,
        μHE[n - 1] {z ∈ reducedBoundary volume Ω s ∩ closedBall x r |
          ε * dist z x < infDist (z - x) ((ℝ ∙ ν)ᗮ : Set E)} / Vvol r ≤
        μHE[n - 1] (reducedBoundary volume Ω s ∩ closedBall x (δ * r)) / Vvol r +
          μHE[n - 1] ((reducedBoundary volume Ω s ∩ closedBall x r) \ W r) / Vvol r := by
      intro r _
      have hsub_cone : {z ∈ reducedBoundary volume Ω s ∩ closedBall x r |
          ε * dist z x < infDist (z - x) ((ℝ ∙ ν)ᗮ : Set E)} ⊆
          (reducedBoundary volume Ω s ∩ closedBall x (δ * r)) ∪
            ((reducedBoundary volume Ω s ∩ closedBall x r) \ W r) := by
        intro z ⟨⟨hzB, hzcb⟩, hzcone⟩
        rw [infDist_orthogonal_span_singleton (norm_outerNormal hx)] at hzcone
        refine (le_or_gt (dist z x) (δ * r)).imp (fun hzd => ⟨hzB, hzd⟩) fun hzd =>
          ⟨⟨hzB, hzcb⟩, fun ⟨_, hzW⟩ => ?_⟩
        have hmul_lt : (ε * δ) * r < ε * dist z x := by
          rw [mul_assoc]; exact mul_lt_mul_of_pos_left hzd hε
        linarith only [hzcone, hzW, hmul_lt]
      rw [← ENNReal.add_div]
      exact ENNReal.div_le_div_right ((measure_mono hsub_cone).trans (measure_union_le _ _)) _
    refine (limsup_le_limsup (eventually_nhdsWithin_of_forall hbound)).trans_lt ?_
    rw [((tendsto_euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_mul_div hx hδ_pos).add
      (tendsto_euclideanHausdorffMeasure_reducedBoundary_closedBall_sdiff_slab_div hn2 hx
        (mul_pos hε hδ_pos))).limsup_eq, add_zero]
    exact hδb

/-- **`Hⁿ⁻¹`-almost everywhere approximate tangent hyperplanes on `∂*s`**, in the form of
`TauCeti.CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div`: at
`μHE[finrank ℝ E - 1]`-almost every `x ∈ ∂*s`, the hyperplane `(ℝ ∙ ν_s x)ᗮ` has dimension
`finrank ℝ E - 1` and `∂*s` has `(n - 1)`-dimensional density zero outside every cone around it. -/
theorem ae_tendsto_euclideanHausdorffMeasure_reducedBoundary_outside_cone_div
    [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ reducedBoundary μ Ω s →
      finrank ℝ (ℝ ∙ outerNormal μ Ω s x)ᗮ = finrank ℝ E - 1 ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[finrank ℝ E - 1]
          {z ∈ reducedBoundary μ Ω s ∩ closedBall x r |
            ε * dist z x < infDist (z - x) ((ℝ ∙ outerNormal μ Ω s x)ᗮ : Set E)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r))
        (𝓝[>] 0) (𝓝 0) :=
  Eventually.of_forall fun _ hx =>
    ⟨finrank_orthogonal_span_outerNormal hx,
      fun _ hε => tendsto_euclideanHausdorffMeasure_reducedBoundary_outside_cone_div hx hε⟩

/-! ### De Giorgi's Gauss–Green theorem -/

/-- Every continuous vector field `φ : E → E` compactly supported in `Ω` pairs integrably with the
outer normal `ν_s` on `∂*s` against `μHE[finrank ℝ E - 1]`. -/
theorem integrableOn_inner_outerNormal_reducedBoundary [μ.IsAddHaarMeasure] {φ : E → E}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ω) :
    IntegrableOn (fun x => ⟪φ x, outerNormal μ Ω s x⟫)
      (reducedBoundary μ Ω s) μHE[finrank ℝ E - 1] := by
  rw [reducedBoundary_eq_volume, outerNormal_eq_volume, IntegrableOn,
    ← map_variationMeasure_volume_indicator_eq_restrict_reducedBoundary,
    Ω.isOpenEmbedding'.measurableEmbedding.integrable_map_iff]
  refine (integrable_inner_polarDensity (μ := volume) (Ω := Ω) (u := s.indicator 1)
    hφ hc hsupp).neg.congr ?_
  filter_upwards [ae_outerNormal_eq] with y hy
  rw [Function.comp_apply, hy, inner_neg_right, Pi.neg_apply]

/-- **De Giorgi's Gauss–Green theorem (indicator form, general additive Haar measure).** For a set
`s` of locally finite perimeter in `Ω` and any `C¹` vector field `φ` compactly supported in `Ω`,
`∫ div φ · χ_s dμ = c • ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`, where `c = Measure.addHaarScalarFactor μ volume`
and `div φ = tr (Dφ)`. -/
theorem integral_trace_fderiv_mul_indicator_eq_smul_setIntegral_inner_outerNormal
    [μ.IsAddHaarMeasure] (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x ∂μ =
      Measure.addHaarScalarFactor μ volume •
        ∫ x in reducedBoundary μ Ω s, ⟪φ x, outerNormal μ Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  rw [integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal hu hfin hφ hc hsupp,
    ← Ω.isOpenEmbedding'.measurableEmbedding.integral_map
      (g := fun x => ⟪φ x, outerNormal μ Ω s x⟫),
    map_variationMeasure_indicator_eq_smul_restrict_reducedBoundary,
    integral_smul_nnreal_measure]

/-- **De Giorgi's Gauss–Green theorem (indicator form, Lebesgue measure).** For a set `s` of
locally finite perimeter in `Ω` and any `C¹` vector field `φ` compactly supported in `Ω`,
`∫ div φ · χ_s = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`. -/
theorem integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s,
        ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  simpa using integral_trace_fderiv_mul_indicator_eq_smul_setIntegral_inner_outerNormal
    hu hfin hφ hc hsupp

/-- **De Giorgi's Gauss–Green theorem (set-integral form, general additive Haar measure).** For a
null-measurable set `s` of locally finite perimeter in `Ω` and any `C¹` vector field `φ` compactly
supported in `Ω`, `∫_s div φ dμ = c • ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`. -/
theorem setIntegral_trace_fderiv_eq_smul_setIntegral_inner_outerNormal [μ.IsAddHaarMeasure]
    (hs : NullMeasurableSet s μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ω) :
    ∫ x in s, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) ∂μ =
      Measure.addHaarScalarFactor μ volume •
        ∫ x in reducedBoundary μ Ω s, ⟪φ x, outerNormal μ Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  have hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const (hs.mono Measure.restrict_le_self) 1
  rw [← integral_indicator₀ hs,
    ← integral_trace_fderiv_mul_indicator_eq_smul_setIntegral_inner_outerNormal
      hu hfin hφ hc hsupp]
  congr 1 with x
  by_cases hx : x ∈ s <;> simp [hx]

/-- **De Giorgi's Gauss–Green theorem (set-integral form, Lebesgue measure).** For a
null-measurable set `s` of locally finite perimeter in `Ω` and any `C¹` vector field `φ` compactly
supported in `Ω`, `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`. -/
theorem setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal
    (hs : NullMeasurableSet s volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ω) :
    ∫ x in s, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) =
      ∫ x in reducedBoundary volume Ω s,
        ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  simpa using setIntegral_trace_fderiv_eq_smul_setIntegral_inner_outerNormal
    hs hfin hφ hc hsupp

/-- **De Giorgi's Gauss–Green theorem for sets of finite perimeter (general additive Haar
measure).** If `s` is null-measurable and `perimeter μ Ω s ≠ ∞`, then
`∫_s div φ dμ = c • ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹` for every `C¹` vector field `φ` compactly supported in
`Ω`. -/
theorem setIntegral_trace_fderiv_eq_smul_setIntegral_inner_outerNormal_of_perimeter_ne_top
    [μ.IsAddHaarMeasure] (hs : NullMeasurableSet s μ) (hP : perimeter μ Ω s ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ω) :
    ∫ x in s, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) ∂μ =
      Measure.addHaarScalarFactor μ volume •
        ∫ x in reducedBoundary μ Ω s, ⟪φ x, outerNormal μ Ω s x⟫ ∂μHE[finrank ℝ E - 1] :=
  setIntegral_trace_fderiv_eq_smul_setIntegral_inner_outerNormal hs
    (fun _ _ hKΩ => ⟨Ω, hKΩ, by rwa [← perimeter_def]⟩) hφ hc hsupp

/-- **De Giorgi's Gauss–Green theorem for sets of finite perimeter (Lebesgue measure).** If `s` is
null-measurable and `perimeter volume Ω s ≠ ∞`, then `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹` for every
`C¹` vector field `φ` compactly supported in `Ω`. -/
theorem setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal_of_perimeter_ne_top
    (hs : NullMeasurableSet s volume) (hP : perimeter volume Ω s ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ω) :
    ∫ x in s, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) =
      ∫ x in reducedBoundary volume Ω s,
        ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ E - 1] :=
  setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal hs
    (fun _ _ hKΩ => ⟨Ω, hKΩ, by rwa [← perimeter_def]⟩) hφ hc hsupp

end TauCeti
