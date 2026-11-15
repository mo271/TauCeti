/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Sarason
import TauCeti.Analysis.Convolution.Basic

/-!
# Localization of functions of bounded and vanishing mean oscillation on balls

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, the VMO modulus
`η_f(r)` (`TauCeti.vmoModulus`) measures the mean oscillation of `f : E → F` at scales up to `r`.
While truncating `f` directly outside a ball can create a jump discontinuity with uncontrolled mean
oscillation across the boundary, decomposing `f` into its high-frequency remainder `f - ψ ⋆ f` at
scale `t = r / 2` plus a radially clamped copy of the smooth part `ψ ⋆ f - (ψ ⋆ f)(x₀)` produces a
global extension `g : E → F` that agrees with `f` on `closedBall x₀ r` and satisfies

`‖g‖_{BMO} ≤ C(dim E) η_f(r)`

(`TauCeti.exists_eqOn_closedBall_bmoSeminorm_le`). In particular, if `f` has vanishing mean
oscillation (`TauCeti.MemVMO`), then for every `ε > 0` there is a uniform radius `r > 0` such that
on every closed ball of radius `r`, `f` agrees with a global function of bounded mean oscillation
whose BMO seminorm is strictly below `ε`
(`TauCeti.MemVMO.exists_memBMO_eqOn_closedBall_bmoSeminorm_lt`). Together with global `Lᵖ` bounds
for commutators `[b, T]` controlled by `‖b‖_{BMO}`, this localization principle transfers global
commutator bounds directly to small-radius local commutator estimates controlled by `η_b(r)`.

## Main declarations

* `TauCeti.bmoLocalizationConst`: the explicit dimensional constant `3 + 8 · 8ⁿ + 12 · 4ⁿ`.
* `TauCeti.exists_eqOn_closedBall_bmoSeminorm_le`: every locally integrable function agrees on
  `closedBall x₀ r` (`r > 0`) with a locally integrable function whose global BMO seminorm is at
  most `bmoLocalizationConst (finrank ℝ E) * vmoModulus f μ r`.
* `TauCeti.MemVMO.exists_memBMO_eqOn_closedBall_bmoSeminorm_lt`: for `f` of vanishing mean
  oscillation and `ε > 0`, there exists `r > 0` such that on every `closedBall x₀ r`, `f` agrees
  with some `g` satisfying `MemBMO g μ` and `bmoSeminorm g μ < ε`.

## References

* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405.
* F. Chiarenza, M. Frasca, and P. Longo, *Interior `W^{2,p}` estimates for nondivergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. **40** (1991), 149–168.
* F. Chiarenza, M. Frasca, and P. Longo, *`W^{2,p}`-solvability of the Dirichlet problem for
  nondivergence elliptic equations with VMO coefficients*, Trans. Amer. Math. Soc. **336** (1993),
  841–853.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set Module ContinuousLinearMap
open scoped ENNReal NNReal Topology Convolution

/-- Explicit dimensional constant in the BMO ball-localization theorem
`TauCeti.exists_eqOn_closedBall_bmoSeminorm_le`. -/
def bmoLocalizationConst (n : ℕ) : ℝ≥0 :=
  3 + 8 * 8 ^ n + 12 * 4 ^ n

theorem bmoLocalizationConst_pos (n : ℕ) : 0 < bmoLocalizationConst n := by
  rw [bmoLocalizationConst]
  positivity

section ClampNorm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Radial retraction onto `closedBall 0 K`: leaves vectors of norm at most `K` fixed and rescales
larger vectors to norm `K`. -/
private noncomputable def clampNorm (K : ℝ) (y : F) : F :=
  if K ≤ 0 then 0 else (K / max K ‖y‖) • y

private theorem continuous_clampNorm (K : ℝ) : Continuous (clampNorm (F := F) K) := by
  unfold clampNorm
  split_ifs with hK
  · exact continuous_const
  · have hK0 : 0 < K := not_le.1 hK
    refine (continuous_const.div (continuous_const.max continuous_norm) fun y => ?_).smul
      continuous_id
    exact (lt_of_lt_of_le hK0 (le_max_left _ _)).ne'

private theorem clampNorm_eq_self {K : ℝ} {y : F} (hy : ‖y‖ ≤ K) : clampNorm K y = y := by
  unfold clampNorm
  split_ifs with hK
  · exact (norm_eq_zero.1 (le_antisymm (hy.trans hK) (norm_nonneg y))).symm
  · have hK0 : 0 < K := not_le.1 hK
    rw [max_eq_left hy, div_self hK0.ne', one_smul]

private theorem norm_clampNorm_le {K : ℝ} (hK : 0 ≤ K) (y : F) : ‖clampNorm K y‖ ≤ K := by
  unfold clampNorm
  split_ifs with hK0
  · simp [hK]
  · have hKp : 0 < K := not_le.1 hK0
    have hmax : 0 < max K ‖y‖ := lt_of_lt_of_le hKp (le_max_left _ _)
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hK hmax.le)]
    calc K / max K ‖y‖ * ‖y‖ ≤ K / max K ‖y‖ * max K ‖y‖ := by
          gcongr
          exact le_max_right K ‖y‖
      _ = K := div_mul_cancel₀ K hmax.ne'

end ClampNorm

section TentKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Tent mollifier `z ↦ max (1 - ‖z‖ / t) 0` supported in `closedBall 0 t`. -/
private noncomputable def tentKernel (t : ℝ) (z : E) : ℝ :=
  max (1 - ‖z‖ / t) 0

omit [NormedSpace ℝ E] in
private theorem continuous_tentKernel (t : ℝ) : Continuous (tentKernel (E := E) t) :=
  (continuous_const.sub (continuous_norm.div_const t)).max continuous_const

omit [NormedSpace ℝ E] in
private theorem tentKernel_nonneg (t : ℝ) (z : E) : 0 ≤ tentKernel t z :=
  le_max_right _ _

omit [NormedSpace ℝ E] in
private theorem tentKernel_le_one {t : ℝ} (ht : 0 < t) (z : E) : tentKernel t z ≤ 1 :=
  max_le (sub_le_self _ (div_nonneg (norm_nonneg z) ht.le)) zero_le_one

omit [NormedSpace ℝ E] in
private theorem tentKernel_eq_zero_of_lt {t : ℝ} (ht : 0 < t) {z : E} (hz : t < ‖z‖) :
    tentKernel t z = 0 :=
  max_eq_right (sub_nonpos.2 ((one_le_div ht).2 hz.le))

omit [NormedSpace ℝ E] in
private theorem support_tentKernel_subset {t : ℝ} (ht : 0 < t) :
    Function.support (tentKernel (E := E) t) ⊆ closedBall 0 t := by
  intro z hz
  rw [mem_closedBall_zero_iff]
  by_contra h
  exact hz (tentKernel_eq_zero_of_lt ht (not_le.1 h))

omit [NormedSpace ℝ E] in
private theorem abs_tentKernel_sub_le {t : ℝ} (ht : 0 < t) (u v : E) :
    |tentKernel t u - tentKernel t v| ≤ t⁻¹ * ‖u - v‖ := by
  calc |tentKernel t u - tentKernel t v|
      ≤ |(1 - ‖u‖ / t) - (1 - ‖v‖ / t)| := abs_max_sub_max_le_abs _ _ 0
    _ = |‖v‖ - ‖u‖| / t := by
        rw [show (1 - ‖u‖ / t) - (1 - ‖v‖ / t) = (‖v‖ - ‖u‖) / t by ring,
          abs_div, abs_of_pos ht]
    _ ≤ ‖u - v‖ / t := by
        gcongr
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le u v
    _ = t⁻¹ * ‖u - v‖ := by ring

variable [FiniteDimensional ℝ E]

private theorem hasCompactSupport_tentKernel {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (tentKernel (E := E) t) :=
  HasCompactSupport.intro (isCompact_closedBall 0 t) fun _ hz =>
    Function.notMem_support.1 fun h => hz (support_tentKernel_subset ht h)

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The integral of `tentKernel t` is at least half the Haar measure of `ball 0 (t / 2)`. -/
private theorem half_measureReal_ball_le_integral_tentKernel {t : ℝ} (ht : 0 < t) :
    2⁻¹ * μ.real (ball (0 : E) (t / 2)) ≤ ∫ z, tentKernel t z ∂μ := by
  have hint : Integrable (tentKernel (E := E) t) μ :=
    (continuous_tentKernel t).integrable_of_hasCompactSupport (hasCompactSupport_tentKernel ht)
  calc 2⁻¹ * μ.real (ball (0 : E) (t / 2))
      = ∫ _ in ball (0 : E) (t / 2), (2⁻¹ : ℝ) ∂μ := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ z in ball (0 : E) (t / 2), tentKernel t z ∂μ := by
        refine setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne) hint.integrableOn
          measurableSet_ball fun z hz => ?_
        rw [mem_ball_zero_iff] at hz
        refine le_trans ?_ (le_max_left _ 0)
        have hzt : ‖z‖ / t ≤ 2⁻¹ := by
          rw [div_le_iff₀ ht]
          linarith
        linarith
    _ ≤ ∫ z, tentKernel t z ∂μ :=
        setIntegral_le_integral hint (Eventually.of_forall (tentKernel_nonneg t))

end TentKernel

section Localization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Local version of `Sarason.edist_convolution_le` controlled by `vmoModulus f μ (2 * t)`: for
`dist x y < t` and `ψ` supported in `closedBall 0 t`, subtracting the average of `f` on
`ball x (2 * t)` bounds `edist ((ψ ⋆ f) x) ((ψ ⋆ f) y)` by the oscillation on `ball x (2 * t)`. -/
private theorem edist_convolution_le_vmoModulus {f : E → F} (hf : LocallyIntegrable f μ)
    {ψ : E → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {t : ℝ}
    (hψ0 : ∀ z, t < ‖z‖ → ψ z = 0) {x y : E} (hxy : dist x y < t) {η : ℝ≥0∞}
    (hη : ∀ w, ‖ψ (x - w) - ψ (y - w)‖ₑ ≤ η) :
    edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) x) ((ψ ⋆[lsmul ℝ ℝ, μ] f) y) ≤
      η * μ (ball (0 : E) (2 * t)) * vmoModulus f μ (2 * t) := by
  have ht : 0 < t := dist_nonneg.trans_lt hxy
  set m := ⨍ w in ball x (2 * t), f w ∂μ
  have hψi : Integrable ψ μ := hψ.integrable_of_hasCompactSupport hψc
  have hix : Integrable (fun w => ψ (x - w) • f w) μ :=
    (hψc.convolutionExists_left (lsmul ℝ ℝ) hψ hf x).integrable_swap
  have hiy : Integrable (fun w => ψ (y - w) • f w) μ :=
    (hψc.convolutionExists_left (lsmul ℝ ℝ) hψ hf y).integrable_swap
  have hd : Integrable (fun w => ψ (x - w) - ψ (y - w)) μ :=
    (hψi.comp_sub_left x).sub (hψi.comp_sub_left y)
  have heq : (ψ ⋆[lsmul ℝ ℝ, μ] f) x - (ψ ⋆[lsmul ℝ ℝ, μ] f) y =
      ∫ w, (ψ (x - w) - ψ (y - w)) • (f w - m) ∂μ := by
    have hm : ∫ w, (ψ (x - w) - ψ (y - w)) • m ∂μ = 0 := by
      rw [integral_smul_const, integral_sub (hψi.comp_sub_left x) (hψi.comp_sub_left y),
        integral_sub_left_eq_self ψ μ x, integral_sub_left_eq_self ψ μ y, sub_self, zero_smul]
    simp only [convolution_eq_swap, lsmul_apply, smul_sub]
    rw [integral_sub ((hix.sub hiy).congr (ae_of_all _ fun w => (sub_smul _ _ _).symm))
      (hd.smul_const m), hm, sub_zero, ← integral_sub hix hiy]
    simp only [sub_smul]
  rw [eDist_eq_eNorm_sub, heq]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  calc ∫⁻ w, ‖(ψ (x - w) - ψ (y - w)) • (f w - m)‖ₑ ∂μ
      ≤ ∫⁻ w, (ball x (2 * t)).indicator (fun w => η * ‖f w - m‖ₑ) w ∂μ := by
        refine lintegral_mono fun w => ?_
        rw [eNorm_smul]
        by_cases hw : w ∈ ball x (2 * t)
        · rw [indicator_of_mem hw]
          gcongr
          exact hη w
        · rw [indicator_of_notMem hw]
          have hxw : 2 * t ≤ ‖x - w‖ := by
            simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hw
          have hyw : t < ‖y - w‖ := by
            have h1 : ‖x - w‖ ≤ ‖x - y‖ + ‖y - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
            rw [← dist_eq_norm x y] at h1
            linarith
          simp [hψ0 _ (by linarith : t < ‖x - w‖), hψ0 _ hyw]
    _ = η * (μ (ball x (2 * t)) * ⨍⁻ w in ball x (2 * t), ‖f w - m‖ₑ ∂μ) := by
        have hm : AEMeasurable (fun w => ‖f w - m‖ₑ) (μ.restrict (ball x (2 * t))) :=
          (hf.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm.restrict
        rw [lintegral_indicator measurableSet_ball, lintegral_const_mul'' _ hm,
          measure_mul_setLAverage _ measure_ball_lt_top.ne]
    _ ≤ η * (μ (ball (0 : E) (2 * t)) * vmoModulus f μ (2 * t)) := by
        rw [Measure.addHaar_ball_center μ x]
        gcongr
        exact setLAverage_enorm_sub_setAverage_le_vmoModulus f μ x le_rfl
    _ = η * μ (ball (0 : E) (2 * t)) * vmoModulus f μ (2 * t) := by ring

/-- Bound on `(∫ tentKernel t)⁻¹ * μ (ball 0 (k * (t / 2)))` for positive scaling factor `k`. -/
private theorem ofReal_inv_integral_tentKernel_mul_measure_ball_le {t k : ℝ} (ht : 0 < t)
    (hk : 0 < k) :
    ENNReal.ofReal (∫ z, tentKernel (E := E) t z ∂μ)⁻¹ * μ (ball (0 : E) (k * (t / 2))) ≤
      2 * ENNReal.ofReal k ^ finrank ℝ E := by
  set ρ := μ (ball (0 : E) (t / 2))
  have hρ0 : ρ ≠ 0 := (measure_ball_pos μ 0 (half_pos ht)).ne'
  have hρtop : ρ ≠ ∞ := measure_ball_lt_top.ne
  have hρpos : 0 < ρ.toReal := ENNReal.toReal_pos hρ0 hρtop
  have hI_lb : 2⁻¹ * ρ.toReal ≤ ∫ z, tentKernel (E := E) t z ∂μ :=
    half_measureReal_ball_le_integral_tentKernel ht
  have hinv : (∫ z, tentKernel (E := E) t z ∂μ)⁻¹ ≤ 2 * (ρ.toReal)⁻¹ := by
    have h := inv_anti₀ (by positivity) hI_lb
    rwa [mul_inv, inv_inv] at h
  have hball : μ (ball (0 : E) (k * (t / 2))) = ENNReal.ofReal k ^ finrank ℝ E * ρ := by
    rw [Measure.addHaar_ball_mul_of_pos μ 0 hk (t / 2), ENNReal.ofReal_pow hk.le]
  calc ENNReal.ofReal (∫ z, tentKernel (E := E) t z ∂μ)⁻¹ * μ (ball (0 : E) (k * (t / 2)))
      ≤ ENNReal.ofReal (2 * (ρ.toReal)⁻¹) * (ENNReal.ofReal k ^ finrank ℝ E * ρ) := by
        rw [hball]
        gcongr
    _ = 2 * ρ⁻¹ * (ENNReal.ofReal k ^ finrank ℝ E * ρ) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_inv_of_pos hρpos, ENNReal.ofReal_toReal hρtop]
    _ = 2 * ENNReal.ofReal k ^ finrank ℝ E := by
        rw [mul_comm (ENNReal.ofReal k ^ finrank ℝ E) ρ, ← mul_assoc, mul_assoc 2,
          ENNReal.inv_mul_cancel hρ0 hρtop, mul_one]

/-- Normalized tent mollifier `(∫ tentKernel t)⁻¹ * tentKernel t`. -/
private noncomputable def normedTentKernel (μ : Measure E) (t : ℝ) (z : E) : ℝ :=
  (∫ w, tentKernel (E := E) t w ∂μ)⁻¹ * tentKernel t z

/-- Increment bound on `closedBall x₀ r` for the tent-kernel mollification at scale `r / 2`:
splitting `[x₀, x]` into three equal steps of length at most `r / 3 < r / 2` gives
`edist ((ψ ⋆ f) x) ((ψ ⋆ f) x₀) ≤ 6 * 4 ^ finrank ℝ E * vmoModulus f μ r`. -/
private theorem edist_normedTentKernel_convolution_closedBall_le {f : E → F}
    (hf : LocallyIntegrable f μ) (x₀ : E) {r : ℝ} (hr : 0 < r) {x : E}
    (hx : x ∈ closedBall x₀ r) :
    edist ((normedTentKernel μ (r / 2) ⋆[lsmul ℝ ℝ, μ] f) x)
        ((normedTentKernel μ (r / 2) ⋆[lsmul ℝ ℝ, μ] f) x₀) ≤
      6 * 4 ^ finrank ℝ E * vmoModulus f μ r := by
  set t := r / 2
  have ht : 0 < t := half_pos hr
  have h2t : 2 * t = r := mul_div_cancel₀ r two_ne_zero
  set ψ := normedTentKernel μ t
  set I := ∫ w, tentKernel (E := E) t w ∂μ
  have hI0 : 0 ≤ I := integral_nonneg (tentKernel_nonneg t)
  have hψ : Continuous ψ := continuous_const.mul (continuous_tentKernel t)
  have hψc : HasCompactSupport ψ := (hasCompactSupport_tentKernel ht).mul_left
  have hψ0 (z : E) (hz : t < ‖z‖) : ψ z = 0 := by
    simp [ψ, normedTentKernel, tentKernel_eq_zero_of_lt ht hz]
  -- One step of length `< t` changes `ψ ⋆ f` by at most `2 * 4ⁿ * vmoModulus f μ r`.
  have hstep {u v : E} (huv : dist u v < t) :
      edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) u) ((ψ ⋆[lsmul ℝ ℝ, μ] f) v) ≤
        2 * 4 ^ finrank ℝ E * vmoModulus f μ r := by
    have hlip (w : E) : ‖ψ (u - w) - ψ (v - w)‖ₑ ≤ ENNReal.ofReal I⁻¹ := by
      rw [Real.eNorm_eq_ofReal_abs, show ψ (u - w) - ψ (v - w) =
          I⁻¹ * (tentKernel t (u - w) - tentKernel t (v - w)) by
            simp only [ψ, normedTentKernel]; ring,
        abs_mul, abs_of_nonneg (inv_nonneg.2 hI0)]
      refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (inv_nonneg.2 hI0) ?_)
      calc |tentKernel t (u - w) - tentKernel t (v - w)|
          ≤ t⁻¹ * ‖(u - w) - (v - w)‖ := abs_tentKernel_sub_le ht _ _
        _ = dist u v / t := by rw [sub_sub_sub_cancel_right, ← dist_eq_norm, inv_mul_eq_div]
        _ ≤ 1 := (div_le_one ht).2 huv.le
    have hB : μ (ball (0 : E) (2 * t)) = μ (ball (0 : E) (4 * (t / 2))) := by ring_nf
    calc edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) u) ((ψ ⋆[lsmul ℝ ℝ, μ] f) v)
        ≤ ENNReal.ofReal I⁻¹ * μ (ball (0 : E) (2 * t)) * vmoModulus f μ (2 * t) :=
          edist_convolution_le_vmoModulus hf hψ hψc hψ0 huv hlip
      _ ≤ 2 * 4 ^ finrank ℝ E * vmoModulus f μ r := by
          rw [hB, h2t]
          refine mul_le_mul_left ?_ _
          simpa using ofReal_inv_integral_tentKernel_mul_measure_ball_le (μ := μ) ht
            (by positivity : (0 : ℝ) < 4)
  -- Split `[x₀, x]` into three equal steps of length `dist x x₀ / 3 ≤ r / 3 < r / 2 = t`.
  set v := (3⁻¹ : ℝ) • (x - x₀)
  have hv : ‖v‖ < t := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm]
    have hxr : dist x x₀ ≤ r := mem_closedBall.1 hx
    linarith
  have hd1 : dist (x₀ + v) x₀ < t := by simpa [dist_eq_norm] using hv
  have hd2 : dist (x₀ + (2 : ℝ) • v) (x₀ + v) < t := by
    simpa [dist_eq_norm, two_smul, add_sub_add_left_eq_sub] using hv
  have hd3 : dist x (x₀ + (2 : ℝ) • v) < t := by
    have hxv : x - (x₀ + (2 : ℝ) • v) = v := by
      simp only [v]
      module
    simpa [dist_eq_norm, hxv] using hv
  calc edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) x) ((ψ ⋆[lsmul ℝ ℝ, μ] f) x₀)
      ≤ edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) x) ((ψ ⋆[lsmul ℝ ℝ, μ] f) (x₀ + (2 : ℝ) • v)) +
          edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) (x₀ + (2 : ℝ) • v)) ((ψ ⋆[lsmul ℝ ℝ, μ] f) x₀) :=
        edist_triangle _ _ _
    _ ≤ edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) x) ((ψ ⋆[lsmul ℝ ℝ, μ] f) (x₀ + (2 : ℝ) • v)) +
          (edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) (x₀ + (2 : ℝ) • v)) ((ψ ⋆[lsmul ℝ ℝ, μ] f) (x₀ + v)) +
            edist ((ψ ⋆[lsmul ℝ ℝ, μ] f) (x₀ + v)) ((ψ ⋆[lsmul ℝ ℝ, μ] f) x₀)) :=
        add_le_add_right (edist_triangle _ _ _) _
    _ ≤ 2 * 4 ^ finrank ℝ E * vmoModulus f μ r +
          (2 * 4 ^ finrank ℝ E * vmoModulus f μ r +
            2 * 4 ^ finrank ℝ E * vmoModulus f μ r) :=
        add_le_add (hstep hd3) (add_le_add (hstep hd2) (hstep hd1))
    _ = 6 * 4 ^ finrank ℝ E * vmoModulus f μ r := by ring

/-- BMO bound for `f - ψ ⋆ f` when `ψ` is the normalized tent kernel at scale `r / 2`. -/
private theorem bmoSeminorm_sub_normedTentKernel_convolution_le {f : E → F}
    (hf : LocallyIntegrable f μ) {r : ℝ} (hr : 0 < r) :
    bmoSeminorm (f - normedTentKernel μ (r / 2) ⋆[lsmul ℝ ℝ, μ] f) μ ≤
      (3 + 8 * 8 ^ finrank ℝ E) * vmoModulus f μ r := by
  set t := r / 2
  have ht : 0 < t := half_pos hr
  set ψ := normedTentKernel μ t
  set I := ∫ w, tentKernel (E := E) t w ∂μ
  have hball_pos : 0 < μ.real (ball (0 : E) (t / 2)) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ 0 (half_pos ht)).ne' measure_ball_lt_top.ne
  have hI_pos : 0 < I :=
    lt_of_lt_of_le (by positivity) (half_measureReal_ball_le_integral_tentKernel ht)
  have hψ : Continuous ψ := continuous_const.mul (continuous_tentKernel t)
  have hψ0 (z : E) : 0 ≤ ψ z := mul_nonneg (inv_nonneg.2 hI_pos.le) (tentKernel_nonneg t z)
  have hψ1 : ∫ z, ψ z ∂μ = 1 := by
    -- Unfold `ψ` to expose the constant scalar factor `I⁻¹` in front of `tentKernel t`.
    change ∫ z, I⁻¹ * tentKernel t z ∂μ = 1
    rw [integral_const_mul, inv_mul_cancel₀ hI_pos.ne']
  have hψt : Function.support ψ ⊆ closedBall 0 t :=
    (Function.support_mul_subset_right _ _).trans (support_tentKernel_subset ht)
  have hψM (z : E) : ψ z ≤ I⁻¹ :=
    mul_le_of_le_one_right (inv_nonneg.2 hI_pos.le) (tentKernel_le_one ht z)
  have hBt : μ (ball (0 : E) t) = μ (ball (0 : E) (2 * (t / 2))) := by ring_nf
  have hprod : ENNReal.ofReal I⁻¹ * μ (ball (0 : E) t) ≤ 2 * 2 ^ finrank ℝ E := by
    rw [hBt]
    simpa using ofReal_inv_integral_tentKernel_mul_measure_ball_le (μ := μ) ht two_pos
  calc bmoSeminorm (f - ψ ⋆[lsmul ℝ ℝ, μ] f) μ
      ≤ (3 + 4 ^ (finrank ℝ E + 1) * ENNReal.ofReal I⁻¹ * μ (ball (0 : E) t)) *
          vmoModulus f μ t :=
        bmoSeminorm_sub_convolution_le hψ hψ0 hψ1 ht hψt hψM hf
    _ ≤ (3 + 4 ^ (finrank ℝ E + 1) * (2 * 2 ^ finrank ℝ E)) * vmoModulus f μ r := by
        rw [mul_assoc (4 ^ (finrank ℝ E + 1))]
        gcongr
        exact monotone_vmoModulus f μ (half_le_self hr.le)
    _ = (3 + 8 * 8 ^ finrank ℝ E) * vmoModulus f μ r := by
        congr 1
        rw [pow_succ, ← mul_assoc, show (4 : ℝ≥0∞) ^ finrank ℝ E * 4 * 2 * 2 ^ finrank ℝ E =
          8 * (4 ^ finrank ℝ E * 2 ^ finrank ℝ E) by ring, ← mul_pow]
        norm_num

/-- **BMO localization on a closed ball.** Let `f : E → F` be locally integrable on a
finite-dimensional real normed space `E` with an additive Haar measure `μ`, and let `r > 0`. Then
there exists a locally integrable function `g : E → F` that agrees with `f` everywhere on
`closedBall x₀ r` and satisfies

`bmoSeminorm g μ ≤ bmoLocalizationConst (finrank ℝ E) * vmoModulus f μ r`. -/
theorem exists_eqOn_closedBall_bmoSeminorm_le {f : E → F}
    (hf : LocallyIntegrable f μ) (x₀ : E) {r : ℝ} (hr : 0 < r) :
    ∃ g : E → F, LocallyIntegrable g μ ∧ EqOn g f (closedBall x₀ r) ∧
      bmoSeminorm g μ ≤ bmoLocalizationConst (finrank ℝ E) * vmoModulus f μ r := by
  rcases eq_or_ne (vmoModulus f μ r) ∞ with htop | hfin
  · refine ⟨f, hf, eqOn_refl f _, ?_⟩
    rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.2 (bmoLocalizationConst_pos _).ne')]
    exact le_top
  set t := r / 2
  have ht : 0 < t := half_pos hr
  set ψ := normedTentKernel μ t
  set u : E → F := ψ ⋆[lsmul ℝ ℝ, μ] f
  have hu : Continuous u := (hasCompactSupport_tentKernel ht).mul_left.continuous_convolution_left
    (lsmul ℝ ℝ) (continuous_const.mul (continuous_tentKernel t)) hf
  set B : ℝ≥0∞ := 6 * 4 ^ finrank ℝ E * vmoModulus f μ r
  have hBfin : B ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)) hfin
  set K : ℝ := B.toReal
  set w : E → F := fun x => clampNorm K (u x - u x₀)
  have hw_cont : Continuous w := (continuous_clampNorm K).comp (hu.sub continuous_const)
  set g : E → F := fun x => (f x - u x) + (w x + u x₀)
  refine ⟨g, (hf.sub hu.locallyIntegrable).add (hw_cont.add continuous_const).locallyIntegrable,
    fun x hx => ?_, ?_⟩
  · have hed : ‖u x - u x₀‖ₑ ≤ B := by
      simpa only [eDist_eq_eNorm_sub] using
        edist_normedTentKernel_convolution_closedBall_le hf x₀ hr hx
    have hnorm : ‖u x - u x₀‖ ≤ K := by
      rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ofReal_norm,
        ENNReal.ofReal_toReal hBfin]
      exact hed
    simp only [g, w, clampNorm_eq_self hnorm, sub_add_cancel, sub_add_cancel]
  · have hw_bmo : bmoSeminorm (fun x => w x + u x₀) μ ≤ 2 * B := by
      rw [bmoSeminorm_add_const hw_cont.aestronglyMeasurable]
      refine (bmoSeminorm_le_two_mul_eLpNorm_top w μ).trans ?_
      gcongr
      have heLp := eLpNorm_le_of_ae_bound (p := ∞) (μ := μ) hw_cont.aestronglyMeasurable
        (Eventually.of_forall fun x => norm_clampNorm_le ENNReal.toReal_nonneg (u x - u x₀))
      simpa [K, ENNReal.ofReal_toReal hBfin] using heLp
    calc bmoSeminorm g μ
        ≤ bmoSeminorm (f - u) μ + bmoSeminorm (fun x => w x + u x₀) μ :=
          bmoSeminorm_add_le (hf.aestronglyMeasurable.sub hu.aestronglyMeasurable)
            (hw_cont.add continuous_const).aestronglyMeasurable
      _ ≤ (3 + 8 * 8 ^ finrank ℝ E) * vmoModulus f μ r + 2 * B :=
          add_le_add (bmoSeminorm_sub_normedTentKernel_convolution_le hf hr) hw_bmo
      _ = bmoLocalizationConst (finrank ℝ E) * vmoModulus f μ r := by
          simp only [B, bmoLocalizationConst]
          push_cast
          ring

/-- **Small-BMO localization of VMO functions on closed balls.** If `f : E → F` has vanishing mean
oscillation and `ε > 0`, then there exists a uniform radius `r > 0` such that on every closed ball
`closedBall x₀ r`, `f` agrees with a global function `g` of bounded mean oscillation satisfying
`bmoSeminorm g μ < ε`. -/
theorem MemVMO.exists_memBMO_eqOn_closedBall_bmoSeminorm_lt {f : E → F} (hf : MemVMO f μ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r > 0, ∀ x₀ : E, ∃ g : E → F, MemBMO g μ ∧ EqOn g f (closedBall x₀ r) ∧
      bmoSeminorm g μ < ε := by
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · refine ⟨1, one_pos, fun x₀ => ⟨f, hf.memBMO, eqOn_refl f _, hf.memBMO.bmoSeminorm_lt_top⟩⟩
  set C : ℝ≥0 := bmoLocalizationConst (finrank ℝ E)
  have hC0 : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 (bmoLocalizationConst_pos _).ne'
  have hdiv : 0 < ε / 2 / C :=
    ENNReal.div_pos (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne' ENNReal.coe_ne_top
  obtain ⟨r, hr, hmod⟩ := (memVMO_iff.1 hf).2 (ε / 2 / C) hdiv
  refine ⟨r, hr, fun x₀ => ?_⟩
  obtain ⟨g, hgi, hgeq, hgbmo⟩ :=
    exists_eqOn_closedBall_bmoSeminorm_le hf.memBMO.locallyIntegrable x₀ hr
  have hlt : bmoSeminorm g μ < ε := by
    calc bmoSeminorm g μ
        ≤ C * (ε / 2 / C) := hgbmo.trans (by gcongr)
      _ = ε / 2 := ENNReal.mul_div_cancel hC0 ENNReal.coe_ne_top
      _ < ε := ENNReal.half_lt_self hε.ne' hεtop
  exact ⟨g, memBMO_iff.2 ⟨hgi, hlt.trans_le le_top⟩, hgeq, hlt⟩

end Localization

end TauCeti
