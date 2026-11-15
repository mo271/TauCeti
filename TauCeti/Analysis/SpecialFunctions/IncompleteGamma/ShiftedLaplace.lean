/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Shifted-Laplace integrals and saddle-point asymptotics on the slit plane

For `c : ℕ`, `d : ℂ`, and `z : ℂ`, the shifted-Laplace integral

`shiftedLaplaceIntegral c d z = z ^ (-c - d - 1) * ∫ u in Ioi 0, u ^ c * (u + z) ^ d * cexp (-u)`

holomorphically continues the Laplace transform
`∫ t in Ioi 0, cexp (-z * t) * t ^ c * (1 + t) ^ d` from the open right half-plane `{z | 0 < z.re}`
to `Complex.slitPlane`. At `c = 0` and `d = a - 1`, this integral is `z ^ (-a) * cexp z * Γ(a, z)`
(DLMF 8.6.4).

Along `Complex.slitPlane`, `shiftedLaplaceIntegral` satisfies the algebraic difference relation
`K(c, d) - K(c, d - 1) = K(c + 1, d - 1)` together with the integration-by-parts recurrences
`z * K(0, d) = 1 + d * K(0, d - 1)` and
`z * K(c + 1, d) = (c + 1) * K(c, d) + d * K(c + 1, d - 1)`.
Rotating the integration ray by half the argument of `z` (`ζ = z ^ (1 / 2)`, `0 < ζ.re`) exposes the
saddle point of `w ^ k * (w + ζ) ^ (-k) * cexp (-ζ * w)` near `w = √k` and yields the uniform
slit-plane asymptotic of `K(k, a - 1 - k, z)` as `k → ∞`, which drives Pincherle convergence of
Legendre's continued fraction for the upper incomplete Gamma function (DLMF 8.9.2).

## Main definitions and results

* `TauCeti.shiftedLaplaceIntegral`: the slit-plane continuation `K(c, d, z)`.
* `TauCeti.analyticOnNhd_shiftedLaplaceIntegral`: holomorphy in `z` on `Complex.slitPlane`.
* `TauCeti.shiftedLaplaceIntegral_eq_integral_of_re_pos`: unrotated Laplace integral representation
  for `0 < z.re`.
* `TauCeti.shiftedLaplaceIntegral_eq_half_angle_integral`: half-angle ray representation on
  `Complex.slitPlane`.
* `TauCeti.shiftedLaplaceIntegral_sub`, `TauCeti.mul_shiftedLaplaceIntegral_zero`,
  `TauCeti.mul_shiftedLaplaceIntegral_succ`: contiguous and integration-by-parts recurrences.
* `TauCeti.shiftedLaplaceIntegral_zero_natCast`, `TauCeti.shiftedLaplaceIntegral_zero_zero`:
  exact rational evaluation at nonnegative integer `d = m`.
* `TauCeti.isEquivalent_shiftedLaplaceIntegral_sub`: uniform slit-plane saddle-point asymptotic of
  `shiftedLaplaceIntegral k (a - 1 - k) z` as `k → ∞`.

## References

* NIST Digital Library of Mathematical Functions, §§8.6, 8.9, <https://dlmf.nist.gov/8.6>.
* W. B. Jones and W. J. Thron, *Continued Fractions: Analytic Theory and Applications*,
  Encyclopedia of Mathematics and its Applications, vol. 11, Addison--Wesley, 1980.
-/

public section

open Complex Filter Finset MeasureTheory Set
open scoped Asymptotics Nat Topology

namespace TauCeti

/-- The shifted-Laplace integral
`K(c, d, z) = z ^ (-c - d - 1) * ∫ u in Ioi 0, u ^ c * (u + z) ^ d * cexp (-u)`,
which analytically continues `∫ t in Ioi 0, cexp (-z * t) * t ^ c * (1 + t) ^ d` from
`{z | 0 < z.re}` to `Complex.slitPlane`. -/
noncomputable def shiftedLaplaceIntegral (c : ℕ) (d z : ℂ) : ℂ :=
  z ^ (-(c : ℂ) - d - 1) *
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ c * ((u : ℂ) + z) ^ d * cexp (-(u : ℂ))

/-- Unfolding lemma for `TauCeti.shiftedLaplaceIntegral`. -/
theorem shiftedLaplaceIntegral_def (c : ℕ) (d z : ℂ) :
    shiftedLaplaceIntegral c d z =
      z ^ (-(c : ℂ) - d - 1) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ c * ((u : ℂ) + z) ^ d * cexp (-(u : ℂ)) :=
  (rfl)

/-- At `c = 0` and `d = a - 1`, `shiftedLaplaceIntegral 0 (a - 1) z` is the rotated-ray Laplace
representation of `z ^ (-a) * cexp z * Γ(a, z)` (DLMF 8.6.4). -/
theorem shiftedLaplaceIntegral_zero_sub_one (a z : ℂ) :
    shiftedLaplaceIntegral 0 (a - 1) z =
      z ^ (-a) * ∫ u in Ioi (0 : ℝ), ((u : ℂ) + z) ^ (a - 1) * cexp (-(u : ℂ)) := by
  rw [shiftedLaplaceIntegral_def, show -(0 : ℕ) - (a - 1) - 1 = -a by push_cast; ring]
  simp

/-- Real domination bound `u ^ c * (1 + u) ^ r * exp (-b * u)` on `(0, ∞)` for `b > 0`. -/
private theorem integrableOn_pow_mul_one_add_rpow_mul_exp_neg (c : ℕ) (r : ℝ) {b : ℝ}
    (hb : 0 < b) :
    IntegrableOn (fun u : ℝ ↦ u ^ c * (1 + u) ^ r * Real.exp (-b * u)) (Ioi 0) := by
  set M : ℝ := max r 0
  set δ : ℝ := b / (2 * (M + 1))
  have hM0 : 0 ≤ M := le_max_right r 0
  have hδ : 0 < δ := div_pos hb (by positivity)
  have hdom : IntegrableOn
      (fun u : ℝ ↦ (1 + δ⁻¹) ^ M * (u ^ (c : ℝ) * Real.exp (-(b / 2) * u ^ (1 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [Nat.cast_nonneg (α := ℝ) c])
      one_pos (half_pos hb)).const_mul _
  have hcont : ContinuousOn (fun u : ℝ ↦ u ^ c * (1 + u) ^ r * Real.exp (-b * u)) (Ioi 0) := by
    refine ((continuousOn_id.pow c).mul ?_).mul (by fun_prop)
    exact (by fun_prop : Continuous fun u : ℝ ↦ 1 + u).continuousOn.rpow_const
      fun u (hu : 0 < u) ↦ Or.inl (by linarith)
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  have h1u : 1 ≤ 1 + u := by linarith
  have hlin : 1 + u ≤ (1 + δ⁻¹) * Real.exp (δ * u) := by
    have h1 : 1 + u ≤ (1 + δ⁻¹) * (1 + δ * u) := by
      have hmul : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
      nlinarith [inv_pos.mpr hδ, mul_pos hδ hu]
    have h2 : 1 + δ * u ≤ Real.exp (δ * u) := by linarith [Real.add_one_le_exp (δ * u)]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hMδ : δ * u * M ≤ b / 2 * u := by
    have hle : M * δ ≤ b / 2 := by
      dsimp [δ]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    nlinarith
  have hrpow : (1 + u) ^ r ≤ (1 + δ⁻¹) ^ M * Real.exp (b / 2 * u) :=
    calc (1 + u) ^ r
        ≤ (1 + u) ^ M := Real.rpow_le_rpow_of_exponent_le h1u (le_max_left r 0)
      _ ≤ ((1 + δ⁻¹) * Real.exp (δ * u)) ^ M :=
          Real.rpow_le_rpow (by positivity) hlin hM0
      _ = (1 + δ⁻¹) ^ M * Real.exp (δ * u * M) := by
          rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
      _ ≤ (1 + δ⁻¹) ^ M * Real.exp (b / 2 * u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hMδ) (by positivity)
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_natCast, Real.rpow_one]
  calc u ^ c * (1 + u) ^ r * Real.exp (-b * u)
      ≤ u ^ c * ((1 + δ⁻¹) ^ M * Real.exp (b / 2 * u)) * Real.exp (-b * u) := by gcongr
    _ = (1 + δ⁻¹) ^ M * (u ^ c * (Real.exp (b / 2 * u) * Real.exp (-b * u))) := by ring
    _ = (1 + δ⁻¹) ^ M * (u ^ c * Real.exp (-(b / 2) * u)) := by
        rw [← Real.exp_add]
        ring_nf

/-- For `z ∈ Complex.slitPlane`, the integrand of `TauCeti.shiftedLaplaceIntegral` is Bochner
integrable on `(0, ∞)`. -/
theorem integrableOn_shiftedLaplaceIntegrand (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ c * ((u : ℂ) + z) ^ d * cexp (-(u : ℂ))) (Ioi 0) := by
  have hiff := integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow
    (μ := volume) (g := fun u : ℝ ↦ (u : ℂ) ^ c * cexp (-(u : ℂ))) hz d
  have hg_meas : AEStronglyMeasurable (fun u : ℝ ↦ (u : ℂ) ^ c * cexp (-(u : ℂ)))
      (volume.restrict (Ioi 0)) :=
    Continuous.aestronglyMeasurable (by fun_prop)
  have hg_int : IntegrableOn
      (fun u : ℝ ↦ ‖(u : ℂ) ^ c * cexp (-(u : ℂ))‖ * (1 + u) ^ d.re) (Ioi 0) := by
    refine (integrableOn_pow_mul_one_add_rpow_mul_exp_neg c d.re one_pos).congr_fun ?_
      measurableSet_Ioi
    intro u (hu : 0 < u)
    dsimp only
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le, Complex.norm_exp,
      neg_re, ofReal_re, neg_one_mul]
    ring
  exact (hiff.mpr ⟨hg_meas, hg_int⟩).congr_fun (fun u _ ↦ by ring) measurableSet_Ioi

/-- `z ↦ shiftedLaplaceIntegral c d z` is complex differentiable on `Complex.slitPlane`. -/
theorem differentiableOn_shiftedLaplaceIntegral (c : ℕ) (d : ℂ) :
    DifferentiableOn ℂ (shiftedLaplaceIntegral c d) slitPlane := by
  have hint := integrableOn_shiftedLaplaceIntegrand c d one_mem_slitPlane
  have hint' : IntegrableOn
      (fun u : ℝ ↦ ((u : ℂ) ^ c * cexp (-(u : ℂ))) * ((u : ℂ) + 1) ^ d) (Ioi 0) :=
    hint.congr_fun (fun u _ ↦ by ring) measurableSet_Ioi
  have hI := differentiableOn_integral_mul_ofReal_add_cpow one_mem_slitPlane hint'
  have hpow : DifferentiableOn ℂ (fun z : ℂ ↦ z ^ (-(c : ℂ) - d - 1)) slitPlane :=
    fun z hz ↦ (differentiableAt_id.cpow_const hz).differentiableWithinAt
  refine (hpow.mul hI).congr fun z _ ↦ ?_
  rw [shiftedLaplaceIntegral_def]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ by ring

/-- `z ↦ shiftedLaplaceIntegral c d z` is holomorphic on `Complex.slitPlane`. -/
theorem analyticOnNhd_shiftedLaplaceIntegral (c : ℕ) (d : ℂ) :
    AnalyticOnNhd ℂ (shiftedLaplaceIntegral c d) slitPlane :=
  (differentiableOn_shiftedLaplaceIntegral c d).analyticOnNhd isOpen_slitPlane

/-- Identity principle on the open right half-plane from agreement on `(0, ∞)`. -/
private theorem eqOn_re_pos_of_ofReal_pos_eq {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re})
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ x : ℝ, 0 < x → f (x : ℂ) = g (x : ℂ)) :
    EqOn f g {z : ℂ | 0 < z.re} := by
  have hpre := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hreal : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    simpa using Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (x := 1)
      fun _ _ ↦ by simp_all
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hpre h1 ?_
  exact hreal.frequently (p := fun w ↦ f w = g w)
    (eventually_nhdsWithin_of_eventually_nhds ((lt_mem_nhds one_pos).mono h)).frequently

/-- Holomorphy of the unrotated Laplace integral on `{z : ℂ | 0 < z.re}`. -/
private theorem analyticOnNhd_unrotatedLaplace (c : ℕ) (d : ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦ ∫ t in Ioi (0 : ℝ), cexp (-(z * (t : ℂ))) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d)
      {z : ℂ | 0 < z.re} := by
  have hop : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  refine DifferentiableOn.analyticOnNhd (fun z₀ (hz₀ : 0 < z₀.re) ↦ ?_) hop
  have hU : {w : ℂ | z₀.re / 2 < w.re} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (half_lt_self hz₀)
  have h1t_cont : ContinuousOn (fun t : ℝ ↦ (1 + (t : ℂ)) ^ d) (Ioi 0) := by
    simpa only [add_comm] using continuousOn_ofReal_add_cpow (Or.inl one_mem_slitPlane) d
  have hmeas_base : ∀ w : ℂ, AEStronglyMeasurable
      (fun t : ℝ ↦ cexp (-(w * (t : ℂ))) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d)
      (volume.restrict (Ioi 0)) := fun w ↦
    (((by fun_prop : Continuous fun t : ℝ ↦
      cexp (-(w * (t : ℂ))) * (t : ℂ) ^ c).continuousOn.mul h1t_cont).aestronglyMeasurable
      measurableSet_Ioi)
  have hcpow_eq : ∀ t : ℝ, 0 < t → ‖(1 + (t : ℂ)) ^ d‖ = (1 + t) ^ d.re := fun t ht ↦ by
    rw [show (1 : ℂ) + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by linarith) d
  have hint₀ : IntegrableOn
      (fun t : ℝ ↦ cexp (-(z₀ * (t : ℂ))) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d) (Ioi 0) := by
    refine (integrableOn_pow_mul_one_add_rpow_mul_exp_neg c d.re hz₀).mono' (hmeas_base z₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [norm_mul, norm_mul, Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero,
      sub_zero, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, hcpow_eq t ht, ← neg_mul]
    exact le_of_eq (by ring)
  have hbound_int : IntegrableOn
      (fun t : ℝ ↦ t ^ (c + 1) * (1 + t) ^ d.re * Real.exp (-(z₀.re / 2) * t)) (Ioi 0) :=
    integrableOn_pow_mul_one_add_rpow_mul_exp_neg (c + 1) d.re (half_pos hz₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (w : ℂ) (t : ℝ) ↦ cexp (-(w * (t : ℂ))) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d)
    (F' := fun (w : ℂ) (t : ℝ) ↦ -(t : ℂ) * cexp (-(w * (t : ℂ))) * (t : ℂ) ^ c *
      (1 + (t : ℂ)) ^ d)
    (bound := fun t : ℝ ↦ t ^ (c + 1) * (1 + t) ^ d.re * Real.exp (-(z₀.re / 2) * t))
    hU (Eventually.of_forall hmeas_base) hint₀
    ((((continuous_ofReal.neg.continuousOn).aestronglyMeasurable measurableSet_Ioi).mul
      (hmeas_base z₀)).congr (Eventually.of_forall fun t ↦ by dsimp; ring)) ?_ hbound_int ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht.le,
      Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg ht.le, hcpow_eq t ht]
    have hexp : Real.exp (-(w.re * t)) ≤ Real.exp (-(z₀.re / 2) * t) :=
      Real.exp_le_exp.mpr (by nlinarith [show z₀.re / 2 < w.re from hw])
    calc t * Real.exp (-(w.re * t)) * t ^ c * (1 + t) ^ d.re
        ≤ t * Real.exp (-(z₀.re / 2) * t) * t ^ c * (1 + t) ^ d.re := by gcongr
      _ = t ^ (c + 1) * (1 + t) ^ d.re * Real.exp (-(z₀.re / 2) * t) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ w _
    have hexp_d : HasDerivAt (fun y : ℂ ↦ cexp (-(y * (t : ℂ))))
        (-(t : ℂ) * cexp (-(w * (t : ℂ)))) w := by
      simpa [id, mul_comm] using ((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp
    exact ((hexp_d.mul_const ((t : ℂ) ^ c)).mul_const ((1 + (t : ℂ)) ^ d)).congr_deriv (by ring)

/-- For `0 < z.re`, `shiftedLaplaceIntegral c d z` agrees with the unrotated Laplace transform
`∫ t in Ioi 0, cexp (-z * t) * t ^ c * (1 + t) ^ d`. -/
theorem shiftedLaplaceIntegral_eq_integral_of_re_pos (c : ℕ) (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    shiftedLaplaceIntegral c d z =
      ∫ t in Ioi (0 : ℝ), cexp (-(z * (t : ℂ))) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d := by
  have hL : AnalyticOnNhd ℂ (shiftedLaplaceIntegral c d) {w : ℂ | 0 < w.re} :=
    (analyticOnNhd_shiftedLaplaceIntegral c d).mono fun w (hw : 0 < w.re) ↦ Or.inl hw
  refine eqOn_re_pos_of_ofReal_pos_eq hL (analyticOnNhd_unrotatedLaplace c d) (fun x hx ↦ ?_) hz
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hscale : ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ c * ((u : ℂ) + (x : ℂ)) ^ d * cexp (-(u : ℂ)) =
      (x : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((x * t : ℝ) : ℂ) ^ c * (((x * t : ℝ) : ℂ) + (x : ℂ)) ^ d * cexp (-((x * t : ℝ) : ℂ)) := by
    simpa [mul_zero, Complex.real_smul] using
      (integral_comp_mul_left_Ioi'
        (fun u : ℝ ↦ (u : ℂ) ^ c * ((u : ℂ) + (x : ℂ)) ^ d * cexp (-(u : ℂ))) 0 hx).symm
  rw [shiftedLaplaceIntegral_def, hscale, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  have hsplit : (((x * t : ℝ) : ℂ) + (x : ℂ)) ^ d = (x : ℂ) ^ d * (1 + (t : ℂ)) ^ d := by
    rw [show ((x * t : ℝ) : ℂ) + (x : ℂ) = (x : ℂ) * (1 + (t : ℂ)) by push_cast; ring,
      ofReal_mul_cpow hx.le]
  have hpow : (x : ℂ) ^ (-(c : ℂ) - d - 1) * (x : ℂ) * (x : ℂ) ^ c * (x : ℂ) ^ d = 1 := by
    rw [← cpow_natCast (x : ℂ) c]
    nth_rw 2 [← cpow_one (x : ℂ)]
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
    have hexp : -(c : ℂ) - d - 1 + 1 + (c : ℂ) + d = 0 := by ring
    rw [hexp, cpow_zero]
  rw [hsplit]
  push_cast
  rw [mul_pow]
  linear_combination
    ((t : ℂ) ^ c * (1 + (t : ℂ)) ^ d * cexp (-((x : ℂ) * (t : ℂ)))) * hpow

/-- Integrability of the half-angle integrand on `(0, ∞)` when `0 < ζ.re`. -/
private theorem integrableOn_halfAngleIntegrand (c : ℕ) (d : ℂ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    IntegrableOn
      (fun w : ℝ ↦ cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d) (Ioi 0) := by
  obtain ⟨_, hU, _, C₀, _, hC₀⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow (Or.inl hζ) d
  have hζU := mem_of_mem_nhds hU
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ ↦ cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d)
      (volume.restrict (Ioi 0)) :=
    (((by fun_prop : Continuous fun w : ℝ ↦ cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c).continuousOn.mul
      (continuousOn_ofReal_add_cpow (Or.inl (Or.inl hζ)) d)).aestronglyMeasurable measurableSet_Ioi)
  refine ((integrableOn_pow_mul_one_add_rpow_mul_exp_neg c d.re hζ).const_mul C₀).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
  rw [norm_mul, norm_mul, Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero,
    sub_zero, norm_pow, Complex.norm_real, Real.norm_of_nonneg hw.le]
  calc Real.exp (-(ζ.re * w)) * w ^ c * ‖((w : ℂ) + ζ) ^ d‖
      ≤ Real.exp (-(ζ.re * w)) * w ^ c * (C₀ * (1 + w) ^ d.re) :=
        mul_le_mul_of_nonneg_left (hC₀ ζ hζU w hw.le) (by positivity)
    _ = C₀ * (w ^ c * (1 + w) ^ d.re * Real.exp (-ζ.re * w)) := by rw [← neg_mul]; ring

/-- Pointwise `ζ`-derivative of the half-angle integrand on `(0, ∞)` when `ζ ∈ slitPlane`. -/
private theorem hasDerivAt_halfAngleIntegrand (c : ℕ) (d : ℂ) {w : ℝ} (hw : 0 < w) {ζ : ℂ}
    (hζ : ζ ∈ slitPlane) :
    HasDerivAt (fun y : ℂ ↦ cexp (-(y * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + y) ^ d)
      ((-(w : ℂ) * cexp (-(ζ * (w : ℂ)))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d +
        cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * (d * ((w : ℂ) + ζ) ^ (d - 1))) ζ := by
  have hwζ : (w : ℂ) + ζ ∈ slitPlane := ofReal_add_mem_slitPlane hζ hw.le
  have hexp_d : HasDerivAt (fun y : ℂ ↦ cexp (-(y * (w : ℂ))))
      (-(w : ℂ) * cexp (-(ζ * (w : ℂ)))) ζ := by
    simpa [id, mul_comm] using ((hasDerivAt_id ζ).mul_const (w : ℂ)).neg.cexp
  exact ((hexp_d.mul_const ((w : ℂ) ^ c)).mul
    (((hasDerivAt_id ζ).const_add (w : ℂ)).cpow_const (c := d) hwζ)).congr_deriv
    (by simp only [id_eq]; ring)

/-- Measurability of the `ζ`-derivative of the half-angle integrand on `(0, ∞)`. -/
private theorem aestronglyMeasurable_halfAngleDeriv (c : ℕ) (d : ℂ) {ζ₀ : ℂ} (hζ₀ : 0 < ζ₀.re) :
    AEStronglyMeasurable
      (fun w : ℝ ↦ (-(w : ℂ) * cexp (-(ζ₀ * (w : ℂ)))) * (w : ℂ) ^ c * ((w : ℂ) + ζ₀) ^ d +
        cexp (-(ζ₀ * (w : ℂ))) * (w : ℂ) ^ c * (d * ((w : ℂ) + ζ₀) ^ (d - 1)))
      (volume.restrict (Ioi 0)) :=
  ((((by fun_prop : Continuous fun w : ℝ ↦
      (-(w : ℂ) * cexp (-(ζ₀ * (w : ℂ)))) * (w : ℂ) ^ c).continuousOn.mul
      (continuousOn_ofReal_add_cpow (Or.inl (Or.inl hζ₀)) d)).add
    ((by fun_prop : Continuous fun w : ℝ ↦ cexp (-(ζ₀ * (w : ℂ))) * (w : ℂ) ^ c).continuousOn.mul
      ((continuousOn_ofReal_add_cpow (Or.inl (Or.inl hζ₀)) (d - 1)).const_smul
        d))).aestronglyMeasurable measurableSet_Ioi)

/-- Holomorphy of the half-angle integral on `{ζ : ℂ | 0 < ζ.re}`. -/
private theorem analyticOnNhd_halfAngleIntegral (c : ℕ) (d : ℂ) :
    AnalyticOnNhd ℂ
      (fun ζ : ℂ ↦ ∫ w in Ioi (0 : ℝ), cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d)
      {ζ : ℂ | 0 < ζ.re} := by
  refine DifferentiableOn.analyticOnNhd (fun ζ₀ (hζ₀ : 0 < ζ₀.re) ↦ ?_)
    (isOpen_lt continuous_const continuous_re)
  obtain ⟨U₀, hU₀, hU₀_slit, C₀, _, hC₀⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow (Or.inl hζ₀) d
  obtain ⟨U₁, hU₁, _, C₁, _, hC₁⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow (Or.inl hζ₀) (d - 1)
  set V : Set ℂ := U₀ ∩ U₁ ∩ {ζ : ℂ | ζ₀.re / 2 < ζ.re}
  have hV : V ∈ 𝓝 ζ₀ := Filter.inter_mem (Filter.inter_mem hU₀ hU₁)
    ((isOpen_lt continuous_const continuous_re).mem_nhds (half_lt_self hζ₀))
  have hmeas : ∀ ζ ∈ V, AEStronglyMeasurable
      (fun w : ℝ ↦ cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d)
      (volume.restrict (Ioi 0)) := fun ζ hζ ↦
    (((by fun_prop : Continuous fun w : ℝ ↦ cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c).continuousOn.mul
      (continuousOn_ofReal_add_cpow (Or.inl (hU₀_slit hζ.1.1)) d)).aestronglyMeasurable
      measurableSet_Ioi)
  set B : ℝ → ℝ := fun w ↦
    C₀ * (w ^ (c + 1) * (1 + w) ^ d.re * Real.exp (-(ζ₀.re / 2) * w)) +
      ‖d‖ * C₁ * (w ^ c * (1 + w) ^ (d - 1).re * Real.exp (-(ζ₀.re / 2) * w))
  have hB_int : IntegrableOn B (Ioi 0) :=
    ((integrableOn_pow_mul_one_add_rpow_mul_exp_neg (c + 1) d.re (half_pos hζ₀)).const_mul C₀).add
      ((integrableOn_pow_mul_one_add_rpow_mul_exp_neg c (d - 1).re (half_pos hζ₀)).const_mul
        (‖d‖ * C₁))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (ζ : ℂ) (w : ℝ) ↦ cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d)
    (F' := fun ζ w ↦ (-(w : ℂ) * cexp (-(ζ * (w : ℂ)))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d +
      cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * (d * ((w : ℂ) + ζ) ^ (d - 1)))
    (bound := B) hV (Filter.eventually_iff_exists_mem.mpr ⟨V, hV, hmeas⟩)
    (integrableOn_halfAngleIntegrand c d hζ₀) (aestronglyMeasurable_halfAngleDeriv c d hζ₀) ?_
    hB_int ?_).2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w) ζ hζ
    have hexp : Real.exp (-(ζ.re * w)) ≤ Real.exp (-(ζ₀.re / 2) * w) :=
      Real.exp_le_exp.mpr (by nlinarith [show ζ₀.re / 2 < ζ.re from hζ.2])
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hw.le, Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero]
      exact (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hw.le)
        (by positivity)) (hC₀ ζ hζ.1.1 w hw.le) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, norm_pow, Complex.norm_real, Real.norm_of_nonneg hw.le]
      exact (mul_le_mul (mul_le_mul_of_nonneg_right hexp (by positivity))
        (mul_le_mul_of_nonneg_left (hC₁ ζ hζ.1.2 w hw.le) (norm_nonneg d)) (by positivity)
        (by positivity)).trans_eq (by ring)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w) ζ hζ
    exact hasDerivAt_halfAngleIntegrand c d hw (hU₀_slit hζ.1.1)

/-- Positive real scaling `u = r * w` equates `shiftedLaplaceIntegral c d (r ^ 2)` with the
half-angle integral at `ζ = r > 0`. -/
private theorem shiftedLaplaceIntegral_sq_of_pos (c : ℕ) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    shiftedLaplaceIntegral c d ((r : ℂ) ^ 2) =
      (r : ℂ) ^ (-(c : ℂ) - d - 1) *
        ∫ w in Ioi (0 : ℝ),
          cexp (-((r : ℂ) * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + (r : ℂ)) ^ d := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hscale :
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ c * ((u : ℂ) + (r : ℂ) ^ 2) ^ d * cexp (-(u : ℂ)) =
        (r : ℂ) * ∫ w in Ioi (0 : ℝ),
          ((r * w : ℝ) : ℂ) ^ c * (((r * w : ℝ) : ℂ) + (r : ℂ) ^ 2) ^ d *
            cexp (-((r * w : ℝ) : ℂ)) := by
    simpa [mul_zero, Complex.real_smul] using
      (integral_comp_mul_left_Ioi'
        (fun u : ℝ ↦ (u : ℂ) ^ c * ((u : ℂ) + (r : ℂ) ^ 2) ^ d * cexp (-(u : ℂ))) 0 hr).symm
  rw [shiftedLaplaceIntegral_def, hscale, ← integral_const_mul, ← integral_const_mul,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ ↦ ?_
  have hsplit : (((r * w : ℝ) : ℂ) + (r : ℂ) ^ 2) ^ d =
      (r : ℂ) ^ d * ((w : ℂ) + (r : ℂ)) ^ d := by
    rw [show ((r * w : ℝ) : ℂ) + (r : ℂ) ^ 2 = (r : ℂ) * ((w : ℂ) + (r : ℂ)) by push_cast; ring,
      ofReal_mul_cpow hr.le]
  have hpow : ((r : ℂ) ^ 2) ^ (-(c : ℂ) - d - 1) * (r : ℂ) * (r : ℂ) ^ c * (r : ℂ) ^ d =
      (r : ℂ) ^ (-(c : ℂ) - d - 1) := by
    rw [ofReal_pow_cpow hr.le 2 _, ← cpow_natCast (r : ℂ) c]
    nth_rw 2 [← cpow_one (r : ℂ)]
    rw [← cpow_add _ _ hr0, ← cpow_add _ _ hr0, ← cpow_add _ _ hr0]
    congr 1; push_cast; ring
  rw [hsplit]; push_cast; rw [mul_pow]
  linear_combination ((w : ℂ) ^ c * ((w : ℂ) + (r : ℂ)) ^ d * cexp (-((r : ℂ) * (w : ℂ)))) * hpow

/-- **Half-angle ray representation.** For `z ∈ Complex.slitPlane` and `ζ = z ^ (1 / 2)`,
`shiftedLaplaceIntegral c d z` equals
`ζ ^ (-c - d - 1) * ∫ w in Ioi 0, cexp (-ζ * w) * w ^ c * (w + ζ) ^ d`. -/
theorem shiftedLaplaceIntegral_eq_half_angle_integral (c : ℕ) (d : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    shiftedLaplaceIntegral c d z =
      (z ^ (1 / 2 : ℂ)) ^ (-(c : ℂ) - d - 1) *
        ∫ w in Ioi (0 : ℝ),
          cexp (-(z ^ (1 / 2 : ℂ) * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + z ^ (1 / 2 : ℂ)) ^ d := by
  have hL : AnalyticOnNhd ℂ (fun ζ : ℂ ↦ shiftedLaplaceIntegral c d (ζ ^ 2))
      {ζ : ℂ | 0 < ζ.re} :=
    (analyticOnNhd_shiftedLaplaceIntegral c d).comp (analyticOnNhd_id.pow 2)
      fun ζ (hζ : 0 < ζ.re) ↦ by simpa [sq] using mul_mem_slitPlane_of_re_pos hζ hζ
  have hpow_diff : DifferentiableOn ℂ (fun ζ : ℂ ↦ ζ ^ (-(c : ℂ) - d - 1)) {ζ : ℂ | 0 < ζ.re} :=
    fun ζ (hζ : 0 < ζ.re) ↦ (differentiableAt_id.cpow_const (Or.inl hζ)).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ
      (fun ζ : ℂ ↦ ζ ^ (-(c : ℂ) - d - 1) *
        ∫ w in Ioi (0 : ℝ), cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ c * ((w : ℂ) + ζ) ^ d)
      {ζ : ℂ | 0 < ζ.re} :=
    (hpow_diff.analyticOnNhd (isOpen_lt continuous_const continuous_re)).mul
      (analyticOnNhd_halfAngleIntegral c d)
  have h1 := eqOn_re_pos_of_ofReal_pos_eq hL hR
    (fun _ hr ↦ shiftedLaplaceIntegral_sq_of_pos c d hr) (cpow_half_re_pos hz)
  dsimp only at h1
  rwa [show (z ^ (1 / 2 : ℂ)) ^ 2 = z by simp [one_div]] at h1

/-- **Contiguous difference relation**:
`K(c, d, z) - K(c, d - 1, z) = K(c + 1, d - 1, z)` for `z ∈ Complex.slitPlane`. -/
theorem shiftedLaplaceIntegral_sub (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    shiftedLaplaceIntegral c d z - shiftedLaplaceIntegral c (d - 1) z =
      shiftedLaplaceIntegral (c + 1) (d - 1) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hint1 := integrableOn_shiftedLaplaceIntegrand c d hz
  have hint2 := integrableOn_shiftedLaplaceIntegrand c (d - 1) hz
  rw [shiftedLaplaceIntegral_def, shiftedLaplaceIntegral_def, shiftedLaplaceIntegral_def]
  have hexp1 : z ^ (-(c : ℂ) - (d - 1) - 1) = z ^ (-(c : ℂ) - d - 1) * z := by
    calc z ^ (-(c : ℂ) - (d - 1) - 1)
        = z ^ ((-(c : ℂ) - d - 1) + 1) := by congr 1; ring
      _ = z ^ (-(c : ℂ) - d - 1) * z := by rw [cpow_add _ _ hz0, cpow_one]
  have hexp2 : -((c + 1 : ℕ) : ℂ) - (d - 1) - 1 = -(c : ℂ) - d - 1 := by push_cast; ring
  have hmul_int : z * ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ c * ((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ)) =
      ∫ u in Ioi (0 : ℝ), z * ((u : ℂ) ^ c * ((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ))) :=
    (integral_const_mul z _).symm
  rw [hexp1, hexp2, mul_assoc, hmul_int, ← mul_sub, ← integral_sub hint1 (hint2.const_mul z)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) ↦ ?_
  have huz0 : (u : ℂ) + z ≠ 0 := slitPlane_ne_zero (ofReal_add_mem_slitPlane hz hu.le)
  have hd_eq : ((u : ℂ) + z) ^ d = ((u : ℂ) + z) ^ (d - 1) * ((u : ℂ) + z) := by
    calc ((u : ℂ) + z) ^ d
        = ((u : ℂ) + z) ^ ((d - 1) + 1) := by rw [sub_add_cancel]
      _ = ((u : ℂ) + z) ^ (d - 1) * ((u : ℂ) + z) := by rw [cpow_add _ _ huz0, cpow_one]
  rw [hd_eq, pow_succ]
  ring

/-- Decay at `∞` of `(u : ℂ) ^ c * ((u : ℂ) + z) ^ d * cexp (-u)` for `z ∈ Complex.slitPlane`. -/
private theorem tendsto_shiftedLaplaceBoundary_atTop (c : ℕ) (d : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    Tendsto (fun u : ℝ ↦ (u : ℂ) ^ c * ((u : ℂ) + z) ^ d * cexp (-(u : ℂ))) atTop (𝓝 0) := by
  obtain ⟨_, hU, _, C, _, hC⟩ := exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hz d
  have hzU := mem_of_mem_nhds hU
  set M : ℝ := max d.re 0
  set δ : ℝ := 1 / (2 * (M + 1))
  have hM0 : 0 ≤ M := le_max_right _ _
  have hδ : 0 < δ := div_pos one_pos (by linarith)
  have h0 : Tendsto (fun u : ℝ ↦ C * (1 + δ⁻¹) ^ M *
      (u ^ (c : ℝ) * Real.exp (-(1 / 2 : ℝ) * u))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c : ℝ) (1 / 2) (by norm_num)).const_mul
        (C * (1 + δ⁻¹) ^ M)
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hlin : 1 + u ≤ (1 + δ⁻¹) * Real.exp (δ * u) := by
    have h1 : 1 + u ≤ (1 + δ⁻¹) * (1 + δ * u) := by
      have hmul : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
      nlinarith [inv_pos.mpr hδ, mul_pos hδ hu]
    exact h1.trans (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (δ * u)])
      (by positivity))
  have hMδ : δ * u * M ≤ 1 / 2 * u := by
    have hle : M * δ ≤ 1 / 2 := by
      dsimp [δ]
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
      nlinarith
    nlinarith
  have hrpow : (1 + u) ^ d.re ≤ (1 + δ⁻¹) ^ M * Real.exp (1 / 2 * u) :=
    calc (1 + u) ^ d.re
        ≤ (1 + u) ^ M := Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
      _ ≤ ((1 + δ⁻¹) * Real.exp (δ * u)) ^ M := Real.rpow_le_rpow (by positivity) hlin hM0
      _ = (1 + δ⁻¹) ^ M * Real.exp (δ * u * M) := by
          rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
      _ ≤ (1 + δ⁻¹) ^ M * Real.exp (1 / 2 * u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hMδ) (by positivity)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le, Complex.norm_exp,
    neg_re, ofReal_re, Real.rpow_natCast]
  calc u ^ c * ‖((u : ℂ) + z) ^ d‖ * Real.exp (-u)
      ≤ u ^ c * (C * ((1 + δ⁻¹) ^ M * Real.exp (1 / 2 * u))) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          ((hC z hzU u hu.le).trans (mul_le_mul_of_nonneg_left hrpow (by positivity)))
          (by positivity)) (by positivity)
    _ = C * (1 + δ⁻¹) ^ M * (u ^ c * (Real.exp (1 / 2 * u) * Real.exp (-u))) := by ring
    _ = C * (1 + δ⁻¹) ^ M * (u ^ c * Real.exp (-(1 / 2 : ℝ) * u)) := by
        rw [← Real.exp_add]
        ring_nf

/-- **Integration-by-parts recurrence at `c = 0`**:
`z * K(0, d, z) = 1 + d * K(0, d - 1, z)` for `z ∈ Complex.slitPlane`. -/
theorem mul_shiftedLaplaceIntegral_zero (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z * shiftedLaplaceIntegral 0 d z = 1 + d * shiftedLaplaceIntegral 0 (d - 1) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hderiv : ∀ u ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ ((u : ℂ) + z) ^ d * cexp (-(u : ℂ)))
        (d * (((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ))) -
          ((u : ℂ) + z) ^ d * cexp (-(u : ℂ))) u := by
    intro u (hu : 0 ≤ u)
    have huz : (u : ℂ) + z ∈ slitPlane := ofReal_add_mem_slitPlane hz hu
    have hd1 : HasDerivAt (fun t : ℝ ↦ ((t : ℂ) + z) ^ d) (d * ((u : ℂ) + z) ^ (d - 1)) u := by
      simpa using (((hasDerivAt_id (u : ℂ)).add_const z).cpow_const (c := d) huz).comp_ofReal
    have hd2 : HasDerivAt (fun t : ℝ ↦ cexp (-(t : ℂ))) (-cexp (-(u : ℂ))) u := by
      simpa using ((hasDerivAt_id (u : ℂ)).neg.cexp).comp_ofReal
    exact (hd1.mul hd2).congr_deriv (by ring)
  have hint0_sub : IntegrableOn (fun u : ℝ ↦ ((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ))) (Ioi 0) :=
    (integrableOn_shiftedLaplaceIntegrand 0 (d - 1) hz).congr_fun (fun u _ ↦ by simp)
      measurableSet_Ioi
  have hint1 : IntegrableOn
      (fun u : ℝ ↦ d * (((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ)))) (Ioi 0) :=
    hint0_sub.const_mul d
  have hint0 : IntegrableOn (fun u : ℝ ↦ ((u : ℂ) + z) ^ d * cexp (-(u : ℂ))) (Ioi 0) :=
    (integrableOn_shiftedLaplaceIntegrand 0 d hz).congr_fun (fun u _ ↦ by simp) measurableSet_Ioi
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hint1.sub hint0)
    (by simpa using tendsto_shiftedLaplaceBoundary_atTop 0 d hz)
  rw [integral_sub hint1 hint0, integral_const_mul, ofReal_zero, zero_add, neg_zero, exp_zero,
    mul_one, zero_sub] at hftc
  have hint_eq : ∫ u in Ioi (0 : ℝ), ((u : ℂ) + z) ^ d * cexp (-(u : ℂ)) =
      z ^ d + d * ∫ u in Ioi (0 : ℝ), ((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ)) := by
    linear_combination -hftc
  rw [shiftedLaplaceIntegral_def, shiftedLaplaceIntegral_def]
  simp only [Nat.cast_zero, pow_zero, one_mul]
  rw [hint_eq]
  have hp1 : z * z ^ (-0 - d - 1) * z ^ d = 1 := by
    calc z * z ^ (-0 - d - 1) * z ^ d
        = z ^ ((1 : ℂ) + (-0 - d - 1) + d) := by
          nth_rw 1 [← cpow_one z]
          rw [← cpow_add _ _ hz0, ← cpow_add _ _ hz0]
      _ = 1 := by
          have hexp : (1 : ℂ) + (-0 - d - 1) + d = 0 := by ring
          rw [hexp, cpow_zero]
  have hp2 : z * z ^ (-0 - d - 1) = z ^ (-0 - (d - 1) - 1) := by
    calc z * z ^ (-0 - d - 1)
        = z ^ ((1 : ℂ) + (-0 - d - 1)) := by
          nth_rw 1 [← cpow_one z]
          rw [← cpow_add _ _ hz0]
      _ = z ^ (-0 - (d - 1) - 1) := by congr 1; ring
  linear_combination hp1 + d * (∫ u in Ioi (0 : ℝ), ((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ))) * hp2

/-- **Integration-by-parts recurrence for `c + 1`**:
`z * K(c + 1, d, z) = (c + 1) * K(c, d, z) + d * K(c + 1, d - 1, z)` for `z ∈ Complex.slitPlane`. -/
theorem mul_shiftedLaplaceIntegral_succ (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z * shiftedLaplaceIntegral (c + 1) d z =
      ((c + 1 : ℕ) : ℂ) * shiftedLaplaceIntegral c d z +
        d * shiftedLaplaceIntegral (c + 1) (d - 1) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set f1 : ℝ → ℂ := fun u ↦ ((c + 1 : ℕ) : ℂ) * ((u : ℂ) ^ c * ((u : ℂ) + z) ^ d * cexp (-(u : ℂ)))
  set f2 : ℝ → ℂ := fun u ↦ d * ((u : ℂ) ^ (c + 1) * ((u : ℂ) + z) ^ (d - 1) * cexp (-(u : ℂ)))
  set f3 : ℝ → ℂ := fun u ↦ (u : ℂ) ^ (c + 1) * ((u : ℂ) + z) ^ d * cexp (-(u : ℂ))
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt f3 ((f1 + f2) u - f3 u) u := fun u hu ↦ by
    have huz : (u : ℂ) + z ∈ slitPlane := ofReal_add_mem_slitPlane hz hu
    have hd1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ (c + 1)) (((c + 1 : ℕ) : ℂ) * (u : ℂ) ^ c) u := by
      simpa using (hasDerivAt_pow (c + 1) (u : ℂ)).comp_ofReal
    have hd2 : HasDerivAt (fun t : ℝ ↦ ((t : ℂ) + z) ^ d) (d * ((u : ℂ) + z) ^ (d - 1)) u := by
      simpa using (((hasDerivAt_id (u : ℂ)).add_const z).cpow_const (c := d) huz).comp_ofReal
    have hd3 : HasDerivAt (fun t : ℝ ↦ cexp (-(t : ℂ))) (-cexp (-(u : ℂ))) u := by
      simpa using ((hasDerivAt_id (u : ℂ)).neg.cexp).comp_ofReal
    exact ((hd1.mul hd2).mul hd3).congr_deriv (by dsimp [f1, f2, f3]; ring)
  have hi1 : IntegrableOn f1 (Ioi 0) := (integrableOn_shiftedLaplaceIntegrand c d hz).const_mul _
  have hi2 : IntegrableOn f2 (Ioi 0) :=
    (integrableOn_shiftedLaplaceIntegrand (c + 1) (d - 1) hz).const_mul _
  have hi3 : IntegrableOn f3 (Ioi 0) := integrableOn_shiftedLaplaceIntegrand (c + 1) d hz
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv ((hi1.add hi2).sub hi3)
    (tendsto_shiftedLaplaceBoundary_atTop (c + 1) d hz)
  rw [show f3 0 = 0 by simp [f3], sub_zero, integral_sub (hi1.add hi2) hi3,
    show (fun x ↦ (f1 + f2) x) = fun x ↦ f1 x + f2 x from rfl, integral_add hi1 hi2] at hftc
  dsimp only [f1, f2] at hftc
  rw [integral_const_mul, integral_const_mul, sub_eq_zero] at hftc
  rw [shiftedLaplaceIntegral_def, shiftedLaplaceIntegral_def, shiftedLaplaceIntegral_def]
  change z * (z ^ (-((c + 1 : ℕ) : ℂ) - d - 1) * ∫ u in Ioi (0 : ℝ), f3 u) = _
  have hp1 : z * z ^ (-((c + 1 : ℕ) : ℂ) - d - 1) = z ^ (-(c : ℂ) - d - 1) := by
    nth_rw 1 [← cpow_one z]
    rw [← cpow_add _ _ hz0]
    congr 1; push_cast; ring
  have hp2 : z ^ (-(c : ℂ) - d - 1) = z ^ (-((c + 1 : ℕ) : ℂ) - (d - 1) - 1) := by
    congr 1; push_cast; ring
  rw [← hftc, ← mul_assoc z, hp1, mul_add]
  nth_rw 2 [hp2]
  ring

/-- Helper Gamma evaluation `∫ u in Ioi 0, u ^ j * cexp (-u) = j!` for `j : ℕ`. -/
private theorem integral_pow_mul_cexp_neg (j : ℕ) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ j * cexp (-(u : ℂ)) = (j ! : ℂ) := by
  have hre : 0 < ((j : ℂ) + 1).re := by
    simp only [add_re, natCast_re, one_re]
    positivity
  have hG := (Complex.Gamma_eq_integral hre).symm
  rw [Complex.Gamma_nat_eq_factorial] at hG
  rw [← hG, Complex.GammaIntegral]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  rw [add_sub_cancel_right, cpow_natCast, ofReal_exp, ofReal_neg, mul_comm]

/-- **Exact rational evaluation at nonnegative integer `d = m`.** For every `m : ℕ` and `z : ℂ`,
`shiftedLaplaceIntegral 0 m z = ∑ j ∈ range (m + 1), (m.descFactorial j : ℂ) * (z⁻¹) ^ (j + 1)`. -/
theorem shiftedLaplaceIntegral_zero_natCast (m : ℕ) (z : ℂ) :
    shiftedLaplaceIntegral 0 (m : ℂ) z =
      ∑ j ∈ range (m + 1), (m.descFactorial j : ℂ) * (z⁻¹) ^ (j + 1) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [shiftedLaplaceIntegral_def, zero_cpow (by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]), zero_mul, inv_zero]
    simp [zero_pow (Nat.succ_ne_zero _)]
  have hexp : z ^ (-(0 : ℕ) - (m : ℂ) - 1) = (z⁻¹) ^ (m + 1) := by
    rw [show -(0 : ℕ) - (m : ℂ) - 1 = -((m + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_neg, cpow_natCast, inv_pow]
  rw [shiftedLaplaceIntegral_def, hexp]
  simp only [pow_zero, one_mul, cpow_natCast]
  have hsum_int : ∫ u in Ioi (0 : ℝ), ((u : ℂ) + z) ^ m * cexp (-(u : ℂ)) =
      ∑ j ∈ range (m + 1), (m.choose j : ℂ) * z ^ (m - j) * (j ! : ℂ) := by
    have hadd : ∀ u : ℝ, ((u : ℂ) + z) ^ m * cexp (-(u : ℂ)) =
        ∑ j ∈ range (m + 1),
          ((m.choose j : ℂ) * z ^ (m - j)) * ((u : ℂ) ^ j * cexp (-(u : ℂ))) := by
      intro u
      rw [add_pow, sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    simp_rw [hadd]
    rw [integral_finsetSum _ fun j _ ↦
      ((integrableOn_shiftedLaplaceIntegrand j 0 one_mem_slitPlane).congr_fun
        (fun _ _ ↦ by simp) measurableSet_Ioi).const_mul _]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [integral_const_mul, integral_pow_mul_cexp_neg j]
  rw [hsum_int, mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have h1 : m + 1 = (j + 1) + (m - j) := by
    have := Nat.lt_succ_iff.mp (mem_range.mp hj)
    omega
  have hzpow : (z⁻¹) ^ (m + 1) * z ^ (m - j) = (z⁻¹) ^ (j + 1) := by
    rw [h1, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, mul_one]
  have hdesc : (m.choose j : ℂ) * (j ! : ℂ) = (m.descFactorial j : ℂ) := by
    exact_mod_cast (mul_comm (m.choose j) (j !)).trans
      (Nat.descFactorial_eq_factorial_mul_choose m j).symm
  calc (z⁻¹) ^ (m + 1) * ((m.choose j : ℂ) * z ^ (m - j) * (j ! : ℂ))
      = ((m.choose j : ℂ) * (j ! : ℂ)) * ((z⁻¹) ^ (m + 1) * z ^ (m - j)) := by ring
    _ = (m.descFactorial j : ℂ) * (z⁻¹) ^ (j + 1) := by rw [hdesc, hzpow]

/-- `K(0, 0, z) = z⁻¹` for every `z : ℂ`. -/
@[simp]
theorem shiftedLaplaceIntegral_zero_zero (z : ℂ) :
    shiftedLaplaceIntegral 0 0 z = z⁻¹ := by
  simpa using shiftedLaplaceIntegral_zero_natCast 0 z

/-! ### Saddle-point asymptotics of `shiftedLaplaceIntegral k (a - 1 - k) z` -/

/-- Rescaled saddle coordinate `w = k ^ (1 / 2) - σ / 2 + k ^ (1 / 4) * s`. -/
private noncomputable def saddleCoord (σ : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  (k : ℝ) ^ (1 / 2 : ℝ) - σ / 2 + (k : ℝ) ^ (1 / 4 : ℝ) * s

/-- Normalized saddle integrand on `ℝ` obtained from the half-angle integral at `c = k` and
`d = a - 1 - k` after substituting `w = saddleCoord ζ.re k s`. -/
private noncomputable def saddleIntegrand (a ζ : ℂ) (k : ℕ) (s : ℝ) : ℂ :=
  {s' : ℝ | 0 < saddleCoord ζ.re k s'}.indicator
    (fun s' ↦
      let w : ℝ := saddleCoord ζ.re k s'
      let S : ℝ := (k : ℝ) ^ (1 / 2 : ℝ)
      cexp (2 * ζ * (S : ℂ) - ζ * (w : ℂ)) *
        (((w : ℂ) + ζ) / (S : ℂ)) ^ (a - 1) *
        ((1 + ζ / (w : ℂ)) ^ k)⁻¹) s

/-- Affine substitution `w = c + b * s` (`b > 0`) turning `∫ w in Ioi 0, g w` into an integral
over `ℝ`. -/
private theorem integral_Ioi_zero_eq_mul_integral_indicator (g : ℝ → ℂ) (c : ℝ) {b : ℝ}
    (hb : 0 < b) :
    ∫ w in Set.Ioi (0 : ℝ), g w =
      (b : ℂ) * ∫ s : ℝ, (Set.Ioi (0 : ℝ)).indicator g (c + b * s) := by
  have hmul := Measure.integral_comp_mul_left (fun w ↦ (Set.Ioi (0 : ℝ)).indicator g (c + w)) b
  rw [abs_of_pos (inv_pos.mpr hb)] at hmul
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self (fun w ↦ (Set.Ioi (0 : ℝ)).indicator g w) c, ← Complex.real_smul,
    ← one_smul ℝ (∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator g (c + x)), ← mul_inv_cancel₀ hb.ne',
    mul_smul, ← hmul]

/-- Measurability of `saddleIntegrand` when `0 < ζ.re` and `1 ≤ k`. -/
private theorem aestronglyMeasurable_saddleIntegrand (a : ℂ) {ζ : ℂ} (hζ : 0 < ζ.re) {k : ℕ}
    (hk : 1 ≤ k) :
    AEStronglyMeasurable (saddleIntegrand a ζ k) volume := by
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hS_pos : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk_pos _
  set U : Set ℝ := {s' : ℝ | 0 < saddleCoord ζ.re k s'}
  have hop : IsOpen U := isOpen_lt continuous_const (by unfold saddleCoord; fun_prop)
  have hcont_w : Continuous fun s' : ℝ ↦ (saddleCoord ζ.re k s' : ℂ) := by
    unfold saddleCoord; fun_prop
  have hcont : ContinuousOn
      (fun s' : ℝ ↦
        let w : ℝ := saddleCoord ζ.re k s'
        let S : ℝ := (k : ℝ) ^ (1 / 2 : ℝ)
        cexp (2 * ζ * (S : ℂ) - ζ * (w : ℂ)) * (((w : ℂ) + ζ) / (S : ℂ)) ^ (a - 1) *
          ((1 + ζ / (w : ℂ)) ^ k)⁻¹) U := by
    intro s' (hs' : 0 < saddleCoord ζ.re k s')
    have hw0 : (saddleCoord ζ.re k s' : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs'.ne'
    have hslit : ((saddleCoord ζ.re k s' : ℂ) + ζ) / (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ∈
        slitPlane := by
      refine Or.inl ?_
      rw [show ((saddleCoord ζ.re k s' : ℂ) + ζ) / (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
          ((saddleCoord ζ.re k s' : ℂ) + ζ) * ((((k : ℝ) ^ (1 / 2 : ℝ))⁻¹ : ℝ) : ℂ) by
        push_cast; rfl, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_re, ofReal_re]
      exact mul_pos (by linarith) (inv_pos.mpr hS_pos)
    have h1w0 : (1 + ζ / (saddleCoord ζ.re k s' : ℂ)) ^ k ≠ 0 := by
      refine pow_ne_zero k (slitPlane_ne_zero (Or.inl ?_))
      rw [add_re, one_re, show ζ / (saddleCoord ζ.re k s' : ℂ) =
          ζ * (((saddleCoord ζ.re k s')⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      linarith [mul_pos hζ (inv_pos.mpr hs')]
    have hc1 : ContinuousAt
        (fun t : ℝ ↦ cexp (2 * ζ * (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) -
          ζ * (saddleCoord ζ.re k t : ℂ))) s' :=
      Complex.continuous_exp.continuousAt.comp
        (continuousAt_const.sub (continuousAt_const.mul hcont_w.continuousAt))
    have hc2 : ContinuousAt
        (fun t : ℝ ↦ (((saddleCoord ζ.re k t : ℂ) + ζ) /
          (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) ^ (a - 1)) s' :=
      ContinuousAt.comp (g := fun z : ℂ ↦ z ^ (a - 1))
        (f := fun t : ℝ ↦
          ((saddleCoord ζ.re k t : ℂ) + ζ) / (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ))
        ((differentiableAt_id.cpow_const hslit).continuousAt)
        (((hcont_w.continuousAt.add continuousAt_const).div_const _))
    have hc3 : ContinuousAt
        (fun t : ℝ ↦ ((1 + ζ / (saddleCoord ζ.re k t : ℂ)) ^ k)⁻¹) s' :=
      (((continuousAt_const.add (continuousAt_const.div hcont_w.continuousAt hw0)).pow k).inv₀ h1w0)
    exact ((hc1.mul hc2).mul hc3).continuousWithinAt
  exact (aestronglyMeasurable_indicator_iff hop.measurableSet).mpr
    (hcont.aestronglyMeasurable hop.measurableSet)

/-- Pointwise factorization of the rescaled half-angle indicator into `saddleIntegrand`. -/
private theorem indicator_halfAngle_eq_mul_saddleIntegrand (a : ℂ) {ζ : ℂ} (hζ : 0 < ζ.re)
    {k : ℕ} (hk : 1 ≤ k) (s : ℝ) :
    (Set.Ioi (0 : ℝ)).indicator
        (fun w : ℝ ↦ cexp (-(ζ * (w : ℂ))) * (w : ℂ) ^ k * ((w : ℂ) + ζ) ^ (a - 1 - (k : ℂ)))
        ((k : ℝ) ^ (1 / 2 : ℝ) - ζ.re / 2 + (k : ℝ) ^ (1 / 4 : ℝ) * s) =
      ((((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ^ (a - 1) *
          cexp (-2 * ζ * (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ))) *
        saddleIntegrand a ζ k s := by
  set S : ℝ := (k : ℝ) ^ (1 / 2 : ℝ)
  have hS_pos : 0 < S := Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  have hS0 : (S : ℂ) ≠ 0 := ofReal_ne_zero.mpr hS_pos.ne'
  set w : ℝ := saddleCoord ζ.re k s
  change (Set.Ioi (0 : ℝ)).indicator
    (fun u : ℝ ↦ cexp (-(ζ * (u : ℂ))) * (u : ℂ) ^ k * ((u : ℂ) + ζ) ^ (a - 1 - (k : ℂ))) w = _
  by_cases hw : 0 < w
  · have hw0 : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
    have hwζ0 : (w : ℂ) + ζ ≠ 0 := slitPlane_ne_zero (ofReal_add_mem_slitPlane (Or.inl hζ) hw.le)
    have hw_Ioi : w ∈ Set.Ioi (0 : ℝ) := hw
    have hw_mem : s ∈ {s' : ℝ | 0 < saddleCoord ζ.re k s'} := hw
    rw [Set.indicator_of_mem hw_Ioi, saddleIntegrand, Set.indicator_of_mem hw_mem]
    dsimp only
    have hp1 : ((w : ℂ) + ζ) ^ (a - 1 - (k : ℂ)) =
        ((w : ℂ) + ζ) ^ (a - 1) * (((w : ℂ) + ζ) ^ k)⁻¹ := by
      rw [sub_eq_add_neg (a - 1), cpow_add _ _ hwζ0, cpow_neg, cpow_natCast]
    have hp2 : ((w : ℂ) + ζ) ^ (a - 1) =
        (S : ℂ) ^ (a - 1) * (((w : ℂ) + ζ) / (S : ℂ)) ^ (a - 1) := by
      conv_lhs => rw [show (w : ℂ) + ζ = (S : ℂ) * (((w : ℂ) + ζ) / (S : ℂ)) from
        (mul_div_cancel₀ _ hS0).symm]
      exact ofReal_mul_cpow hS_pos.le _ _
    have hp3 : (w : ℂ) ^ k * (((w : ℂ) + ζ) ^ k)⁻¹ = ((1 + ζ / (w : ℂ)) ^ k)⁻¹ := by
      rw [show (w : ℂ) + ζ = (w : ℂ) * (1 + ζ / (w : ℂ)) by field_simp [hw0],
        mul_pow, mul_inv_rev, mul_comm (((1 + ζ / (w : ℂ)) ^ k)⁻¹), ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero k hw0), one_mul]
    have hexp : cexp (-(ζ * (w : ℂ))) =
        cexp (-2 * ζ * (S : ℂ)) * cexp (2 * ζ * (S : ℂ) - ζ * (w : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hp1, hp2, hexp]
    linear_combination (S : ℂ) ^ (a - 1) * cexp (-2 * ζ * (S : ℂ)) *
      cexp (2 * ζ * (S : ℂ) - ζ * (w : ℂ)) * (((w : ℂ) + ζ) / (S : ℂ)) ^ (a - 1) * hp3
  · have hw_nIoi : w ∉ Set.Ioi (0 : ℝ) := hw
    have hw_nmem : s ∉ {s' : ℝ | 0 < saddleCoord ζ.re k s'} := hw
    rw [Set.indicator_of_notMem hw_nIoi, saddleIntegrand, Set.indicator_of_notMem hw_nmem, mul_zero]

/-- Exact factorization of `shiftedLaplaceIntegral k (a - 1 - k) z` into the saddle prefactor times
`∫ s : ℝ, saddleIntegrand a (z ^ (1 / 2)) k s` for `1 ≤ k`. -/
private theorem shiftedLaplaceIntegral_sub_eq_mul_integral_saddleIntegrand (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) {k : ℕ} (hk : 1 ≤ k) :
    shiftedLaplaceIntegral k (a - 1 - (k : ℂ)) z =
      (z ^ (1 / 2 : ℂ)) ^ (-a) * (k : ℂ) ^ (a / 2 - 1 / 4) *
        cexp (-2 * z ^ (1 / 2 : ℂ) * (k : ℂ) ^ (1 / 2 : ℂ)) *
        ∫ s : ℝ, saddleIntegrand a (z ^ (1 / 2 : ℂ)) k s := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  have hζ_re : 0 < ζ.re := cpow_half_re_pos hz
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk_ne : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk_pos.ne'
  set q : ℝ := (k : ℝ) ^ (1 / 4 : ℝ)
  set S : ℝ := (k : ℝ) ^ (1 / 2 : ℝ)
  have hSc : (S : ℂ) = (k : ℂ) ^ (1 / 2 : ℂ) := by rw [ofReal_cpow hk_pos.le]; push_cast; rfl
  have hqc : (q : ℂ) * (S : ℂ) ^ (a - 1) = (k : ℂ) ^ (a / 2 - 1 / 4) := by
    have hq_eq : (q : ℂ) = (k : ℂ) ^ (1 / 4 : ℂ) := by rw [ofReal_cpow hk_pos.le]; push_cast; rfl
    have hS_pow : (S : ℂ) ^ (a - 1) = (k : ℂ) ^ ((1 / 2 : ℂ) * (a - 1)) := by
      rw [hSc, ← Complex.cpow_mul (a - 1)]
      · rw [← ofReal_natCast, ← ofReal_log hk_pos.le,
          show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_mul, ofReal_im]
        linarith [Real.pi_pos]
      · rw [← ofReal_natCast, ← ofReal_log hk_pos.le,
          show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_mul, ofReal_im]
        exact Real.pi_pos.le
    rw [hq_eq, hS_pow, ← cpow_add _ _ hk_ne]; congr 1; ring
  rw [shiftedLaplaceIntegral_eq_half_angle_integral k (a - 1 - (k : ℂ)) hz,
    show -(k : ℂ) - (a - 1 - (k : ℂ)) - 1 = -a by ring,
    integral_Ioi_zero_eq_mul_integral_indicator _ (S - ζ.re / 2) (Real.rpow_pos_of_pos hk_pos _),
    funext (indicator_halfAngle_eq_mul_saddleIntegrand a hζ_re hk), integral_const_mul]
  dsimp only [ζ, q, S] at hSc hqc ⊢
  rw [hSc] at hqc ⊢
  calc _ = (z ^ (1 / 2 : ℂ)) ^ (-a) * ((((k : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
        ((k : ℂ) ^ (1 / 2 : ℂ)) ^ (a - 1)) *
        cexp (-2 * z ^ (1 / 2 : ℂ) * (k : ℂ) ^ (1 / 2 : ℂ)) *
        ∫ s : ℝ, saddleIntegrand a (z ^ (1 / 2 : ℂ)) k s := by ring
    _ = _ := by rw [hqc]

/-- Pointwise bound on the exponential-times-rational factor of `saddleIntegrand` for `1 ≤ k` and
`0 < saddleCoord ζ.re k s`. -/
private theorem norm_exp_mul_inv_pow_saddleCoord_le {ζ : ℂ} (hζ : 0 < ζ.re) {k : ℕ} (hk : 1 ≤ k)
    {s : ℝ} (hw : 0 < saddleCoord ζ.re k s) :
    ‖cexp (2 * ζ * (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) - ζ * (saddleCoord ζ.re k s : ℂ))‖ *
        ‖((1 + ζ / (saddleCoord ζ.re k s : ℂ)) ^ k)⁻¹‖ ≤
      Real.exp (ζ.re ^ 2 / 2 - if s ≤ 1 then (ζ.re / 2) * s ^ 2 else (ζ.re / 2) * s) := by
  set σ : ℝ := ζ.re
  set q : ℝ := (k : ℝ) ^ (1 / 4 : ℝ)
  set S : ℝ := (k : ℝ) ^ (1 / 2 : ℝ)
  set w : ℝ := saddleCoord σ k s
  have hq1 : 1 ≤ q := Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hSq : S = q ^ 2 := by
    dsimp [S, q]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hkS : (k : ℝ) = S ^ 2 := by
    dsimp [S]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hw_def : w = q ^ 2 - σ / 2 + q * s := by change S - σ / 2 + q * s = _; rw [hSq]
  have h2w : 2 * w + σ = 2 * q * (q + s) := by rw [hw_def]; ring
  have hqs_pos : 0 < q + s := by nlinarith [show 0 < 2 * w + σ by linarith]
  have hre1 : 1 + σ / w ≤ ‖1 + ζ / (w : ℂ)‖ :=
    (le_of_eq (by rw [add_re, one_re, show ζ / (w : ℂ) = ζ * ((w⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, ← div_eq_mul_inv])).trans
      (Complex.re_le_norm _)
  have hinv_le : ‖((1 + ζ / (w : ℂ)) ^ k)⁻¹‖ ≤ Real.exp (-2 * σ * S ^ 2 / (2 * w + σ)) := by
    have hlog : 2 * σ / (2 * w + σ) ≤ Real.log (1 + σ / w) := by
      have h0 := Real.le_log_one_add_of_nonneg (by positivity : 0 ≤ σ / w)
      rwa [show 2 * (σ / w) / (σ / w + 2) = 2 * σ / (2 * w + σ) by field_simp; ring] at h0
    rw [norm_inv, norm_pow]
    refine (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hre1 k)).trans ?_
    rw [← Real.exp_log (by positivity : 0 < 1 + σ / w), ← Real.exp_nat_mul, ← Real.exp_neg, hkS]
    have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg S)
    exact Real.exp_le_exp.mpr
      (by rw [show -2 * σ * S ^ 2 / (2 * w + σ) = -(S ^ 2 * (2 * σ / (2 * w + σ))) by ring]
          linarith)
  have hexp_norm : ‖cexp (2 * ζ * (S : ℂ) - ζ * (w : ℂ))‖ = Real.exp (2 * σ * S - σ * w) := by
    rw [Complex.norm_exp]; congr 1; simp [σ]
  rw [hexp_norm]
  refine (mul_le_mul_of_nonneg_left hinv_le (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  rw [show 2 * σ * S - σ * w + -2 * σ * S ^ 2 / (2 * w + σ) =
      σ ^ 2 / 2 - σ * q * s ^ 2 / (q + s) by rw [h2w, hw_def, hSq]; field_simp; ring]
  split_ifs with hs
  · have hsub : (σ / 2) * s ^ 2 ≤ σ * q * s ^ 2 / (q + s) :=
      (le_div_iff₀ hqs_pos).mpr ((mul_le_mul_of_nonneg_left (by linarith : q + s ≤ 2 * q)
        (by positivity : 0 ≤ (σ / 2) * s ^ 2)).trans_eq (by ring))
    linarith
  · have hs0 : 0 ≤ s := by linarith
    have hsub : (σ / 2) * s ≤ σ * q * s ^ 2 / (q + s) :=
      (le_div_iff₀ hqs_pos).mpr ((mul_le_mul_of_nonneg_left (by nlinarith : q + s ≤ 2 * q * s)
        (by positivity : 0 ≤ (σ / 2) * s)).trans_eq (by ring))
    linarith

/-- Elementary bound `(2 + |s|) ^ M ≤ (2 + δ⁻¹) ^ M * exp ((σ / 4) * |s|)` for `0 ≤ M`. -/
private theorem two_add_abs_rpow_le_mul_exp {σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (s : ℝ) :
    (2 + |s|) ^ M ≤ (2 + (σ / (4 * (M + 1)))⁻¹) ^ M * Real.exp ((σ / 4) * |s|) := by
  set δ : ℝ := σ / (4 * (M + 1))
  have hδ : 0 < δ := div_pos hσ (by positivity)
  have hlin : 2 + |s| ≤ (2 + δ⁻¹) * Real.exp (δ * |s|) := by
    have h1 : 2 + |s| ≤ (2 + δ⁻¹) * (1 + δ * |s|) := by
      nlinarith [inv_mul_cancel₀ hδ.ne', inv_pos.mpr hδ, mul_nonneg hδ.le (abs_nonneg s)]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (δ * |s|)]) (by positivity))
  have hMδ : δ * |s| * M ≤ (σ / 4) * |s| := by
    have hle : M * δ ≤ σ / 4 := by
      dsimp [δ]; rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith [abs_nonneg s]
  calc (2 + |s|) ^ M ≤ ((2 + δ⁻¹) * Real.exp (δ * |s|)) ^ M :=
        Real.rpow_le_rpow (by positivity) hlin hM
    _ = (2 + δ⁻¹) ^ M * Real.exp (δ * |s| * M) := by
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
    _ ≤ (2 + δ⁻¹) ^ M * Real.exp ((σ / 4) * |s|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hMδ) (by positivity)

/-- Upper bound `‖((saddleCoord ζ.re k s : ℂ) + ζ) / S‖ ≤ 2 + |s|` for `1 ≤ k`, `2 * ‖ζ‖ ≤ S`, and
`0 < saddleCoord ζ.re k s`. -/
private theorem norm_saddleRatio_le_two_add_abs {ζ : ℂ} (hζ : 0 < ζ.re) {k : ℕ} (hk : 1 ≤ k)
    (hSζ : 2 * ‖ζ‖ ≤ (k : ℝ) ^ (1 / 2 : ℝ)) {s : ℝ} (hw : 0 < saddleCoord ζ.re k s) :
    ‖((saddleCoord ζ.re k s : ℂ) + ζ) / (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ 2 + |s| := by
  set q : ℝ := (k : ℝ) ^ (1 / 4 : ℝ)
  set S : ℝ := (k : ℝ) ^ (1 / 2 : ℝ)
  have hq1 : 1 ≤ q := Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hSq : S = q ^ 2 := by
    dsimp [S, q]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hS_pos : 0 < S := by nlinarith
  rw [norm_div, Complex.norm_of_nonneg hS_pos.le, div_le_iff₀ hS_pos]
  have hw_le : saddleCoord ζ.re k s ≤ S + q * |s| := by
    change S - ζ.re / 2 + q * s ≤ S + q * |s|; nlinarith [le_abs_self s, hζ]
  have hqs : q * |s| ≤ S * |s| := mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg s)
  have hadd : ‖(saddleCoord ζ.re k s : ℂ) + ζ‖ ≤ saddleCoord ζ.re k s + ‖ζ‖ :=
    (norm_add_le _ _).trans (by rw [Complex.norm_of_nonneg hw.le])
  linarith

/-- Polynomial-factor norm bound on `(((w : ℂ) + ζ) / S) ^ (a - 1)` in the saddle coordinate. -/
private theorem norm_cpow_saddleRatio_le (a : ℂ) {ζ : ℂ} (hζ : 0 < ζ.re) {k : ℕ} (hk : 1 ≤ k)
    (hSζ : 2 * ‖ζ‖ ≤ (k : ℝ) ^ (1 / 2 : ℝ)) {s : ℝ} (hw : 0 < saddleCoord ζ.re k s) :
    ‖(((saddleCoord ζ.re k s : ℂ) + ζ) / (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) ^ (a - 1)‖ ≤
      Real.exp (Real.pi * |(a - 1).im|) * max ((1 / 2 : ℝ) ^ (a - 1).re) 1 *
          (2 + (ζ.re / (4 * (max (a - 1).re 0 + 1)))⁻¹) ^ max (a - 1).re 0 *
          Real.exp ((ζ.re / 4) * |s|) +
        if s < -(k : ℝ) ^ (1 / 4 : ℝ) / 2 then
          Real.exp (Real.pi * |(a - 1).im|) * ζ.re ^ (a - 1).re *
            ((k : ℝ) ^ (1 / 2 : ℝ)) ^ (-(a - 1).re)
        else 0 := by
  set σ : ℝ := ζ.re; set r : ℝ := (a - 1).re; set M : ℝ := max r 0
  set δ : ℝ := σ / (4 * (M + 1)); set q : ℝ := (k : ℝ) ^ (1 / 4 : ℝ)
  set S : ℝ := (k : ℝ) ^ (1 / 2 : ℝ); set w : ℝ := saddleCoord σ k s
  have hq_pos : 0 < q := Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  have hSq : S = q ^ 2 := by
    dsimp [S, q]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hS_pos : 0 < S := Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  set z_w : ℂ := ((w : ℂ) + ζ) / (S : ℂ); set C_arg : ℝ := Real.exp (Real.pi * |(a - 1).im|)
  have harg_le : ‖z_w ^ (a - 1)‖ ≤ C_arg * ‖z_w‖ ^ r := by
    refine (Complex.norm_cpow_le z_w (a - 1)).trans ?_
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((neg_le_abs _).trans
      ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_right (abs_arg_le_pi _) (abs_nonneg _)))))
      (by positivity)
  have hz_re : (w + σ) / S ≤ ‖z_w‖ := (le_of_eq (by
    rw [show z_w = ((w : ℂ) + ζ) * ((S⁻¹ : ℝ) : ℂ) by dsimp [z_w]; push_cast; rfl,
      mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_re, ofReal_re,
      ← div_eq_mul_inv])).trans (Complex.re_le_norm _)
  have hnn : 0 ≤ r → C_arg * ‖z_w‖ ^ r ≤
      C_arg * max ((1 / 2 : ℝ) ^ r) 1 * (2 + δ⁻¹) ^ M * Real.exp ((σ / 4) * |s|) := fun hr ↦ by
    have h1 : ‖z_w‖ ^ r ≤ (2 + δ⁻¹) ^ M * Real.exp ((σ / 4) * |s|) := by
      rw [(max_eq_left hr).symm]
      exact (Real.rpow_le_rpow (by positivity) (norm_saddleRatio_le_two_add_abs hζ hk hSζ hw)
        (le_max_right _ _)).trans (two_add_abs_rpow_le_mul_exp hζ (le_max_right _ _) s)
    exact (mul_le_mul_of_nonneg_left ((one_mul _).symm.le.trans
      (mul_le_mul (le_max_right ((1 / 2 : ℝ) ^ r) 1) h1
        (by positivity) (by positivity))) (by positivity)).trans_eq (by ring)
  split_ifs with hs
  · rcases le_or_gt 0 r with hr | hr
    · exact harg_le.trans ((hnn hr).trans (le_add_of_nonneg_right (by positivity)))
    · have hrpow_lo : ‖z_w‖ ^ r ≤ σ ^ r * S ^ (-r) :=
        (Real.rpow_le_rpow_of_nonpos (div_pos hζ hS_pos)
          ((div_le_div_of_nonneg_right (by linarith) hS_pos.le).trans hz_re) hr.le).trans_eq
          (by rw [Real.div_rpow hζ.le hS_pos.le, div_eq_mul_inv, Real.rpow_neg hS_pos.le])
      exact (harg_le.trans (mul_le_mul_of_nonneg_left hrpow_lo (by positivity))).trans
        (by rw [← mul_assoc]; exact le_add_of_nonneg_left (by positivity))
  · rw [add_zero]; rcases le_or_gt 0 r with hr | hr
    · exact harg_le.trans (hnn hr)
    · have hz_lo : 1 / 2 ≤ ‖z_w‖ := (le_div_iff₀ hS_pos |>.mpr (by
        change 1 / 2 * S ≤ S - σ / 2 + q * s + σ; nlinarith [hSq, hq_pos])).trans hz_re
      rw [show M = 0 from max_eq_right hr.le, Real.rpow_zero, mul_one]
      exact (harg_le.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by norm_num) hz_lo hr.le) (by positivity))).trans
        ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans
          (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))))

/-- Gaussian domination on `s ≤ 1` for the product of the quadratic exponential factor and the
polynomial bound from `norm_cpow_saddleRatio_le`. -/
private theorem exp_quad_mul_saddlePoly_le_of_le_one {σ r C₁ C_arg : ℝ} (hσ : 0 < σ)
    (hC₁ : 0 ≤ C₁) (hCarg : 0 ≤ C_arg) {k : ℕ} (hk : 1 ≤ k)
    (htail_k : σ ^ r * (((k : ℝ) ^ (1 / 2 : ℝ)) ^ (-r) *
      Real.exp (-(σ / 16) * (k : ℝ) ^ (1 / 2 : ℝ))) < 1) (s : ℝ) :
    Real.exp (σ ^ 2 / 2 - (σ / 2) * s ^ 2) * (C₁ * Real.exp ((σ / 4) * |s|) +
      if s < -(k : ℝ) ^ (1 / 4 : ℝ) / 2 then
        C_arg * σ ^ r * ((k : ℝ) ^ (1 / 2 : ℝ)) ^ (-r) else 0) ≤
      (C₁ + C_arg) * Real.exp (σ ^ 2 / 2 + σ / 16) * Real.exp (-(σ / 4) * s ^ 2) := by
  rw [mul_add]
  have hterm1 : Real.exp (σ ^ 2 / 2 - (σ / 2) * s ^ 2) * (C₁ * Real.exp ((σ / 4) * |s|)) ≤
      C₁ * Real.exp (σ ^ 2 / 2 + σ / 16) * Real.exp (-(σ / 4) * s ^ 2) := by
    have hexp_le : Real.exp (σ ^ 2 / 2 - (σ / 2) * s ^ 2) * Real.exp ((σ / 4) * |s|) ≤
        Real.exp (σ ^ 2 / 2 + σ / 16) * Real.exp (-(σ / 4) * s ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      have hsq : |s| - s ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (|s| - 1 / 2), sq_abs s]
      exact Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hsq hσ.le])
    exact (by ring : _ = C₁ *
      (Real.exp (σ ^ 2 / 2 - (σ / 2) * s ^ 2) * Real.exp ((σ / 4) * |s|))).le.trans
      ((mul_le_mul_of_nonneg_left hexp_le hC₁).trans_eq (by ring))
  have hterm2 : Real.exp (σ ^ 2 / 2 - (σ / 2) * s ^ 2) *
      (if s < -(k : ℝ) ^ (1 / 4 : ℝ) / 2 then
        C_arg * σ ^ r * ((k : ℝ) ^ (1 / 2 : ℝ)) ^ (-r) else 0) ≤
      C_arg * Real.exp (σ ^ 2 / 2 + σ / 16) * Real.exp (-(σ / 4) * s ^ 2) := by
    split_ifs with hsq_lo
    · have hS_eq : ((k : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (k : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hq_pos : 0 < (k : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hk) _
      have hs2 : (k : ℝ) ^ (1 / 2 : ℝ) / 4 ≤ s ^ 2 := by nlinarith [hS_eq]
      have hexp_split : Real.exp (σ ^ 2 / 2 - (σ / 2) * s ^ 2) ≤
          Real.exp (-(σ / 16) * (k : ℝ) ^ (1 / 2 : ℝ)) *
            (Real.exp (σ ^ 2 / 2 + σ / 16) * Real.exp (-(σ / 4) * s ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hs2 hσ.le])
      exact (mul_le_mul_of_nonneg_right hexp_split (by positivity)).trans
        ((by ring : _ = (σ ^ r * (((k : ℝ) ^ (1 / 2 : ℝ)) ^ (-r) *
            Real.exp (-(σ / 16) * (k : ℝ) ^ (1 / 2 : ℝ)))) *
            (C_arg * Real.exp (σ ^ 2 / 2 + σ / 16) * Real.exp (-(σ / 4) * s ^ 2))).le.trans
          ((mul_le_mul_of_nonneg_right htail_k.le (by positivity)).trans_eq (one_mul _)))
    · rw [mul_zero]; positivity
  exact (add_le_add hterm1 hterm2).trans_eq (by ring)

/-- Pointwise integrable-envelope domination of `‖saddleIntegrand a ζ k s‖` once the left-tail
polynomial factor is bounded by `1`. -/
private theorem norm_saddleIntegrand_le_of_tail (a : ℂ) {ζ : ℂ} (hζ : 0 < ζ.re) {k : ℕ}
    (hk : 1 ≤ k) (hSζ : 2 * ‖ζ‖ ≤ (k : ℝ) ^ (1 / 2 : ℝ))
    (htail_k : ζ.re ^ (a - 1).re * (((k : ℝ) ^ (1 / 2 : ℝ)) ^ (-(a - 1).re) *
      Real.exp (-(ζ.re / 16) * (k : ℝ) ^ (1 / 2 : ℝ))) < 1) (s : ℝ) :
    ‖saddleIntegrand a ζ k s‖ ≤
      (Real.exp (Real.pi * |(a - 1).im|) * max ((1 / 2 : ℝ) ^ (a - 1).re) 1 *
          (2 + (ζ.re / (4 * (max (a - 1).re 0 + 1)))⁻¹) ^ max (a - 1).re 0 +
          Real.exp (Real.pi * |(a - 1).im|)) * Real.exp (ζ.re ^ 2 / 2 + ζ.re / 16) *
        (Real.exp (-(ζ.re / 4) * s ^ 2) +
          (Set.Ioi (0 : ℝ)).indicator (fun t ↦ Real.exp (-(ζ.re / 4) * t)) s) := by
  set σ : ℝ := ζ.re; set r : ℝ := (a - 1).re
  set C_arg : ℝ := Real.exp (Real.pi * |(a - 1).im|)
  set C₁ : ℝ := C_arg * max ((1 / 2 : ℝ) ^ r) 1 *
    (2 + (σ / (4 * (max r 0 + 1)))⁻¹) ^ max r 0
  set C₀ : ℝ := (C₁ + C_arg) * Real.exp (σ ^ 2 / 2 + σ / 16)
  by_cases hw : 0 < saddleCoord ζ.re k s
  · have hw_mem : s ∈ {s' : ℝ | 0 < saddleCoord ζ.re k s'} := hw
    rw [saddleIntegrand, Set.indicator_of_mem hw_mem, norm_mul, norm_mul, mul_right_comm]
    refine (mul_le_mul (norm_exp_mul_inv_pow_saddleCoord_le hζ hk hw)
      (norm_cpow_saddleRatio_le a hζ hk hSζ hw) (by positivity) (by positivity)).trans ?_
    by_cases hs1 : s ≤ 1
    · simp only [hs1, ↓reduceIte]
      exact (exp_quad_mul_saddlePoly_le_of_le_one hζ (by positivity) (by positivity)
        hk htail_k s).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
          (Set.indicator_nonneg (s := Set.Ioi (0 : ℝ))
            (fun t _ ↦ (Real.exp_pos (-(σ / 4) * t)).le) s)) (by positivity))
    · have hs_pos : s ∈ Set.Ioi (0 : ℝ) := by change 0 < s; linarith
      have hnot_lo : ¬ s < -(k : ℝ) ^ (1 / 4 : ℝ) / 2 := by
        linarith [show 0 < s from hs_pos,
          Real.rpow_pos_of_pos (by exact_mod_cast hk : (0 : ℝ) < k) (1 / 4 : ℝ)]
      simp only [hs1, hnot_lo, ↓reduceIte, add_zero]
      rw [abs_of_pos hs_pos, Set.indicator_of_mem hs_pos]
      calc Real.exp (σ ^ 2 / 2 - (σ / 2) * s) * (C₁ * Real.exp ((σ / 4) * s))
          = C₁ * (Real.exp (σ ^ 2 / 2 - (σ / 2) * s) * Real.exp ((σ / 4) * s)) := by ring
        _ = C₁ * Real.exp (σ ^ 2 / 2 - (σ / 4) * s) := by rw [← Real.exp_add]; congr 2; ring
        _ ≤ (C₁ + C_arg) * Real.exp ((σ ^ 2 / 2 + σ / 16) + -(σ / 4) * s) :=
            mul_le_mul (by linarith [show 0 ≤ C_arg by positivity])
              (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
        _ = C₀ * Real.exp (-(σ / 4) * s) := by rw [Real.exp_add]; dsimp [C₀]; ring
        _ ≤ C₀ * (Real.exp (-(σ / 4) * s ^ 2) + Real.exp (-(σ / 4) * s)) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_pos _).le) (by positivity)
  · have hw_nmem : s ∉ {s' : ℝ | 0 < saddleCoord ζ.re k s'} := hw
    rw [saddleIntegrand, Set.indicator_of_notMem hw_nmem, norm_zero]
    exact mul_nonneg (by positivity) (add_nonneg (Real.exp_pos _).le
      (Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) s))

/-- Integrable uniform dominating bound on `‖saddleIntegrand a ζ k s‖` eventually in `k`. -/
private theorem eventually_norm_saddleIntegrand_le (a : ℂ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ᶠ k : ℕ in atTop, ∀ s : ℝ, ‖saddleIntegrand a ζ k s‖ ≤ B s := by
  set σ : ℝ := ζ.re
  set r : ℝ := (a - 1).re
  set C_arg : ℝ := Real.exp (Real.pi * |(a - 1).im|)
  set C₁ : ℝ := C_arg * max ((1 / 2 : ℝ) ^ r) 1 *
    (2 + (σ / (4 * (max r 0 + 1)))⁻¹) ^ max r 0
  set C₀ : ℝ := (C₁ + C_arg) * Real.exp (σ ^ 2 / 2 + σ / 16)
  refine ⟨fun s ↦ C₀ * (Real.exp (-(σ / 4) * s ^ 2) +
      (Set.Ioi (0 : ℝ)).indicator (fun t ↦ Real.exp (-(σ / 4) * t)) s), ?_, ?_⟩
  · refine ((integrable_exp_neg_mul_sq (by positivity : 0 < σ / 4)).add ?_).const_mul C₀
    rw [integrable_indicator_iff measurableSet_Ioi]
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1 : ℝ) < 0) one_pos (by positivity : 0 < σ / 4)
  have hS_atTop : Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have htail : Tendsto
      (fun k : ℕ ↦ σ ^ r * (((k : ℝ) ^ (1 / 2 : ℝ)) ^ (-r) *
        Real.exp (-(σ / 16) * (k : ℝ) ^ (1 / 2 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-r) (σ / 16)
        (by positivity)).comp hS_atTop).const_mul (σ ^ r)
  filter_upwards [eventually_ge_atTop 1, hS_atTop.eventually_ge_atTop (2 * ‖ζ‖),
    htail.eventually (gt_mem_nhds zero_lt_one)] with k hk hSζ htail_k s
  exact norm_saddleIntegrand_le_of_tail a hζ hk hSζ htail_k s

/-- Vanishing at infinity of the three rescaled saddle parameters `t = k ^ (-1 / 4)`,
`δ = s * t - (ζ.re / 2) * t ^ 2`, and `u = ζ * t ^ 2 / (1 + δ)`. -/
private theorem tendsto_saddleSmallParams (ζ : ℂ) (s : ℝ) :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (-1 / 4 : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ ↦ s * (k : ℝ) ^ (-1 / 4 : ℝ) -
        (ζ.re / 2) * ((k : ℝ) ^ (-1 / 4 : ℝ)) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ ↦ ζ * ((((k : ℝ) ^ (-1 / 4 : ℝ) : ℝ) : ℂ) ^ 2) /
        (1 + ((s * (k : ℝ) ^ (-1 / 4 : ℝ) -
          (ζ.re / 2) * ((k : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 : ℝ) : ℂ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (-1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have hδ : Tendsto (fun k : ℕ ↦ s * (k : ℝ) ^ (-1 / 4 : ℝ) -
      (ζ.re / 2) * ((k : ℝ) ^ (-1 / 4 : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using (ht.const_mul s).sub ((ht.pow 2).const_mul (ζ.re / 2))
  refine ⟨ht, hδ, ?_⟩
  have ht_c : Tendsto (fun k : ℕ ↦ (((k : ℝ) ^ (-1 / 4 : ℝ) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  have hδ_c : Tendsto (fun k : ℕ ↦ ((s * (k : ℝ) ^ (-1 / 4 : ℝ) -
      (ζ.re / 2) * ((k : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hδ
  simpa [div_eq_mul_inv] using
    ((ht_c.pow 2).const_mul ζ).mul ((hδ_c.const_add 1).inv₀ (by norm_num))

/-- Cubic Taylor remainder `(k : ℂ) * (log (1 + u k) - (u k - u k ^ 2 / 2))` tends to `0`. -/
private theorem tendsto_mul_saddleLogRemainder (ζ : ℂ) (s : ℝ) :
    Tendsto (fun k : ℕ ↦
      let t : ℝ := (k : ℝ) ^ (-1 / 4 : ℝ)
      let δ : ℝ := s * t - (ζ.re / 2) * t ^ 2
      let u : ℂ := ζ * ((t : ℂ) ^ 2) / (1 + (δ : ℂ))
      (k : ℂ) * (Complex.log (1 + u) - (u - u ^ 2 / 2))) atTop (𝓝 0) := by
  obtain ⟨ht_zero, hδ_zero, hu_zero⟩ := tendsto_saddleSmallParams ζ s
  set t : ℕ → ℝ := fun k ↦ (k : ℝ) ^ (-1 / 4 : ℝ)
  set δ : ℕ → ℝ := fun k ↦ s * t k - (ζ.re / 2) * (t k) ^ 2
  set u : ℕ → ℂ := fun k ↦ ζ * ((t k : ℂ) ^ 2) / (1 + (δ k : ℂ))
  have hbound : Tendsto
      (fun k : ℕ ↦ (‖ζ‖ / (1 + δ k)) ^ 3 * (1 - ‖u k‖)⁻¹ / 3 * (t k) ^ 2) atTop (𝓝 0) := by
    have hc1 : Tendsto (fun k : ℕ ↦ (‖ζ‖ / (1 + δ k)) ^ 3) atTop (𝓝 (‖ζ‖ ^ 3)) := by
      simpa [div_eq_mul_inv] using (((hδ_zero.const_add 1).inv₀ (by norm_num)).const_mul ‖ζ‖).pow 3
    have hc2 : Tendsto (fun k : ℕ ↦ (1 - ‖u k‖)⁻¹) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hu_zero.norm).inv₀ (by norm_num)
    simpa using (((hc1.mul hc2).div_const 3).mul (ht_zero.pow 2))
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop 1,
    hδ_zero.eventually (lt_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)),
    hu_zero.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1 / 2))] with k hk hδk huk
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have h1δ_pos : 0 < 1 + δ k := by linarith
  have ht_pos : 0 < t k := Real.rpow_pos_of_pos hk_pos _
  have hkt : (k : ℝ) * ((t k) ^ 2) ^ 3 = (t k) ^ 2 := by
    dsimp [t]; rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hk_pos.le,
      ← Real.rpow_mul hk_pos.le]
    nth_rw 1 [← Real.rpow_one (k : ℝ)]; rw [← Real.rpow_add hk_pos]; norm_num
  have hlog := Complex.norm_log_sub_logTaylor_le 2 (lt_trans huk (by norm_num : (1 / 2 : ℝ) < 1))
  rw [show Complex.logTaylor 3 (u k) = u k - (u k) ^ 2 / 2 by
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero]; ring] at hlog
  norm_num at hlog
  have hu_norm : ‖u k‖ = ‖ζ‖ * (t k) ^ 2 / (1 + δ k) := by
    dsimp [u]; rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht_pos.le,
      show (1 : ℂ) + (δ k : ℂ) = ((1 + δ k : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg h1δ_pos.le]
  rw [norm_mul, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans_eq
    (by nth_rw 1 [hu_norm]; rw [show (k : ℝ) * ((‖ζ‖ * (t k) ^ 2 / (1 + δ k)) ^ 3 *
      (1 - ‖u k‖)⁻¹ / 3) = (‖ζ‖ / (1 + δ k)) ^ 3 * (1 - ‖u k‖)⁻¹ / 3 *
      ((k : ℝ) * ((t k) ^ 2) ^ 3) by ring, hkt])

/-- Eventual algebraic expansion of `saddleIntegrand a ζ k s` around the Gaussian quadratic form. -/
private theorem eventually_saddleIntegrand_eq_cexp_mul (a ζ : ℂ) (s : ℝ) :
    (fun k : ℕ ↦
      let t : ℝ := (k : ℝ) ^ (-1 / 4 : ℝ)
      let δ : ℝ := s * t - (ζ.re / 2) * t ^ 2
      let u : ℂ := ζ * ((t : ℂ) ^ 2) / (1 + (δ : ℂ))
      let R : ℂ := Complex.log (1 + u) - (u - u ^ 2 / 2)
      cexp (ζ ^ 2 / (2 * (1 + (δ : ℂ)) ^ 2) -
          ζ * ((s : ℂ) - (ζ.re : ℂ) / 2 * (t : ℂ)) ^ 2 / (1 + (δ : ℂ)) - (k : ℂ) * R) *
        (1 + (δ : ℂ) + ζ * ((t : ℂ) ^ 2)) ^ (a - 1)) =ᶠ[atTop]
    fun k : ℕ ↦ saddleIntegrand a ζ k s := by
  obtain ⟨_, hδ_zero, hu_zero⟩ := tendsto_saddleSmallParams ζ s
  set t : ℕ → ℝ := fun k ↦ (k : ℝ) ^ (-1 / 4 : ℝ)
  set δ : ℕ → ℝ := fun k ↦ s * t k - (ζ.re / 2) * (t k) ^ 2
  set u : ℕ → ℂ := fun k ↦ ζ * ((t k : ℂ) ^ 2) / (1 + (δ k : ℂ))
  filter_upwards [eventually_ge_atTop 1,
    hδ_zero.eventually (lt_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)),
    hu_zero.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1 / 2))] with k hk hδk huk
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have h1δ_pos : 0 < 1 + δ k := by linarith
  have ht_ne : t k ≠ 0 := (Real.rpow_pos_of_pos hk_pos _).ne'
  have ht0 : (t k : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_ne
  have h1δ0 : 1 + (δ k : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) + (δ k : ℂ) = ((1 + δ k : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr h1δ_pos.ne'
  have hS_inv : (k : ℝ) ^ (1 / 2 : ℝ) = ((t k) ^ 2)⁻¹ := by
    dsimp [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hk_pos.le, ← Real.rpow_neg hk_pos.le]
    norm_num
  have hq_inv : (k : ℝ) ^ (1 / 4 : ℝ) = (t k)⁻¹ := by
    dsimp [t]; rw [← Real.rpow_neg hk_pos.le]; norm_num
  have hk_inv : (k : ℝ) = ((t k) ^ 4)⁻¹ := by
    dsimp [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hk_pos.le, ← Real.rpow_neg hk_pos.le]
    norm_num
  have hw_eq : saddleCoord ζ.re k s = (k : ℝ) ^ (1 / 2 : ℝ) * (1 + δ k) := by
    dsimp [saddleCoord, δ]; rw [hS_inv, hq_inv]; field_simp [ht_ne]; ring
  have hw_mem : s ∈ {s' : ℝ | 0 < saddleCoord ζ.re k s'} := by
    dsimp; rw [hw_eq]; exact mul_pos (Real.rpow_pos_of_pos hk_pos _) h1δ_pos
  have hu_eq : ζ / (saddleCoord ζ.re k s : ℂ) = u k := by
    dsimp [u]; rw [hw_eq, hS_inv]; push_cast; field_simp
  have hratio_eq : ((saddleCoord ζ.re k s : ℂ) + ζ) / (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
      1 + (δ k : ℂ) + ζ * ((t k : ℂ) ^ 2) := by rw [hw_eq, hS_inv]; push_cast; field_simp
  have hpow_u : ((1 + u k) ^ k)⁻¹ = cexp (-((k : ℂ) * Complex.log (1 + u k))) := by
    conv_lhs => rw [← Complex.exp_log (slitPlane_ne_zero
      (Complex.mem_slitPlane_of_norm_lt_one (lt_trans huk (by norm_num))))]
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  have halg_exp : 2 * ζ * (((k : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) - ζ * (saddleCoord ζ.re k s : ℂ) +
      -((k : ℂ) * Complex.log (1 + u k)) =
      ζ ^ 2 / (2 * (1 + (δ k : ℂ)) ^ 2) -
        ζ * ((s : ℂ) - (ζ.re : ℂ) / 2 * (t k : ℂ)) ^ 2 / (1 + (δ k : ℂ)) -
        (k : ℂ) * (Complex.log (1 + u k) - (u k - (u k) ^ 2 / 2)) := by
    have hkc : (k : ℂ) = ((t k : ℂ) ^ 4)⁻¹ := by exact_mod_cast hk_inv
    have hδc : (δ k : ℂ) = (s : ℂ) * (t k : ℂ) - (ζ.re : ℂ) / 2 * (t k : ℂ) ^ 2 := by
      dsimp [δ]; push_cast; ring
    set Rk : ℂ := Complex.log (1 + u k) - (u k - (u k) ^ 2 / 2)
    rw [show Complex.log (1 + u k) = u k - (u k) ^ 2 / 2 + Rk by dsimp [Rk]; ring,
      hw_eq, hS_inv, hkc]
    dsimp [u]; push_cast; field_simp [h1δ0, ht0]; rw [hδc]; ring
  symm; rw [saddleIntegrand, Set.indicator_of_mem hw_mem]; dsimp only
  rw [hu_eq, hratio_eq, hpow_u, mul_right_comm, ← Complex.exp_add, halg_exp]

/-- Pointwise Gaussian limit of `saddleIntegrand a ζ k s` as `k → ∞` for each `s : ℝ`. -/
private theorem tendsto_saddleIntegrand (a ζ : ℂ) (s : ℝ) :
    Tendsto (fun k : ℕ ↦ saddleIntegrand a ζ k s) atTop
      (𝓝 (cexp (ζ ^ 2 / 2 - ζ * (s : ℂ) ^ 2))) := by
  set t : ℕ → ℝ := fun k ↦ (k : ℝ) ^ (-1 / 4 : ℝ)
  have ht_zero : Tendsto t atTop (𝓝 0) := by
    simpa [t, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have ht_c : Tendsto (fun k ↦ (t k : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp ht_zero
  set δ : ℕ → ℝ := fun k ↦ s * t k - (ζ.re / 2) * (t k) ^ 2
  have hδ_c : Tendsto (fun k ↦ (δ k : ℂ)) atTop (𝓝 0) := by
    have hδ_zero : Tendsto δ atTop (𝓝 0) := by
      simpa [δ] using (ht_zero.const_mul s).sub ((ht_zero.pow 2).const_mul (ζ.re / 2))
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hδ_zero
  have hmid : Tendsto
      (fun k : ℕ ↦ (1 + (δ k : ℂ) + ζ * ((t k : ℂ) ^ 2)) ^ (a - 1)) atTop (𝓝 1) := by
    have hbase : Tendsto (fun k : ℕ ↦ 1 + (δ k : ℂ) + ζ * ((t k : ℂ) ^ 2)) atTop (𝓝 1) := by
      simpa using (hδ_c.const_add 1).add ((ht_c.pow 2).const_mul ζ)
    simpa [Function.comp_def] using
      (differentiableAt_id.cpow_const one_mem_slitPlane).continuousAt.tendsto.comp hbase
  have hd1 : Tendsto (fun k : ℕ ↦ ζ ^ 2 / (2 * (1 + (δ k : ℂ)) ^ 2)) atTop (𝓝 (ζ ^ 2 / 2)) := by
    simpa [div_eq_mul_inv] using
      ((((hδ_c.const_add 1).pow 2).const_mul (2 : ℂ)).inv₀ (by norm_num)).const_mul (ζ ^ 2)
  have hd2 : Tendsto
      (fun k : ℕ ↦ ζ * ((s : ℂ) - (ζ.re : ℂ) / 2 * (t k : ℂ)) ^ 2 / (1 + (δ k : ℂ))) atTop
      (𝓝 (ζ * (s : ℂ) ^ 2)) := by
    have hnum := (((tendsto_const_nhds (x := (s : ℂ))).sub
      (ht_c.const_mul ((ζ.re : ℂ) / 2))).pow 2).const_mul ζ
    simpa [div_eq_mul_inv] using hnum.mul ((hδ_c.const_add 1).inv₀ (by norm_num))
  have hexp_lim : Tendsto
      (fun k : ℕ ↦ cexp (ζ ^ 2 / (2 * (1 + (δ k : ℂ)) ^ 2) -
        ζ * ((s : ℂ) - (ζ.re : ℂ) / 2 * (t k : ℂ)) ^ 2 / (1 + (δ k : ℂ)) -
        (k : ℂ) * (let u : ℂ := ζ * ((t k : ℂ) ^ 2) / (1 + (δ k : ℂ))
          Complex.log (1 + u) - (u - u ^ 2 / 2))))
      atTop (𝓝 (cexp (ζ ^ 2 / 2 - ζ * (s : ℂ) ^ 2))) := by
    have hsub := (hd1.sub hd2).sub (tendsto_mul_saddleLogRemainder ζ s)
    rw [sub_zero] at hsub
    exact Complex.continuous_exp.continuousAt.tendsto.comp hsub
  exact (Tendsto.congr' (eventually_saddleIntegrand_eq_cexp_mul a ζ s) (hexp_lim.mul hmid)).trans
    (by simp)

/-- Evaluation of the Gaussian limit integral `∫ s : ℝ, cexp (ζ ^ 2 / 2 - ζ * s ^ 2)` for
`0 < ζ.re`. -/
private theorem integral_cexp_sub_mul_sq {ζ : ℂ} (hζ : 0 < ζ.re) :
    (∫ s : ℝ, cexp (ζ ^ 2 / 2 - ζ * (s : ℂ) ^ 2)) =
      (Real.sqrt Real.pi : ℂ) * cexp (ζ ^ 2 / 2) * ζ ^ (-1 / 2 : ℂ) := by
  have hζ0 : ζ ≠ 0 := slitPlane_ne_zero (Or.inl hζ)
  have hsplit : (fun s : ℝ ↦ cexp (ζ ^ 2 / 2 - ζ * (s : ℂ) ^ 2)) =
      fun s : ℝ ↦ cexp (ζ ^ 2 / 2) * cexp (-ζ * (s : ℂ) ^ 2) := by
    ext s; rw [sub_eq_add_neg, Complex.exp_add, neg_mul]
  have hpi_ζ : ((Real.pi : ℂ) / ζ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) * ζ ^ (-1 / 2 : ℂ) := by
    rw [div_eq_mul_inv, ofReal_mul_cpow Real.pi_pos.le, Real.sqrt_eq_rpow,
      ofReal_cpow Real.pi_pos.le, show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring]
    congr 1
    rw [cpow_def_of_ne_zero (inv_ne_zero hζ0), cpow_def_of_ne_zero hζ0,
      log_inv _ (slitPlane_arg_ne_pi (Or.inl hζ))]
    congr 1; ring
  rw [hsplit, integral_const_mul, integral_gaussian_complex hζ, hpi_ζ]; ring

/-- **Saddle-point asymptotic of `shiftedLaplaceIntegral k (a - 1 - k) z` on `Complex.slitPlane`.**
For any `a : ℂ` and `z ∈ Complex.slitPlane`, as `k → ∞`,
`shiftedLaplaceIntegral k (a - 1 - k) z ~ √π * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) *
  k ^ (a / 2 - 1 / 4) * cexp (-2 * z ^ (1 / 2) * k ^ (1 / 2))`. -/
theorem isEquivalent_shiftedLaplaceIntegral_sub (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (fun k : ℕ ↦ shiftedLaplaceIntegral k (a - 1 - (k : ℂ)) z) ~[atTop]
      fun k : ℕ ↦ (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) *
        (k : ℂ) ^ (a / 2 - 1 / 4) * cexp (-2 * z ^ (1 / 2 : ℂ) * (k : ℂ) ^ (1 / 2 : ℂ)) := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  have hζ_re : 0 < ζ.re := cpow_half_re_pos hz
  have hζ0 : ζ ≠ 0 := slitPlane_ne_zero (Or.inl hζ_re)
  obtain ⟨B, hB_int, hB_le⟩ := eventually_norm_saddleIntegrand_le a hζ_re
  have hmeas : ∀ᶠ k : ℕ in atTop, AEStronglyMeasurable (saddleIntegrand a ζ k) volume :=
    (eventually_ge_atTop 1).mono fun k hk ↦ aestronglyMeasurable_saddleIntegrand a hζ_re hk
  have hint_lim : Tendsto (fun k : ℕ ↦ ∫ s : ℝ, saddleIntegrand a ζ k s) atTop
      (𝓝 ((Real.sqrt Real.pi : ℂ) * cexp (z / 2) * ζ ^ (-1 / 2 : ℂ))) := by
    have hdct := tendsto_integral_filter_of_dominated_convergence B hmeas
      (hB_le.mono fun k hk ↦ Eventually.of_forall hk) hB_int
      (Eventually.of_forall (tendsto_saddleIntegrand a ζ))
    rwa [integral_cexp_sub_mul_sq hζ_re, show ζ ^ 2 = z by simp [ζ, one_div]] at hdct
  have hL0 : (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * ζ ^ (-1 / 2 : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))
      (Complex.exp_ne_zero _)) (cpow_ne_zero_iff.mpr (Or.inl hζ0))
  have hzeta_pow : ζ ^ (-a) * ζ ^ (-1 / 2 : ℂ) = z ^ (-a / 2 - 1 / 4) := by
    rw [← cpow_add _ _ hζ0]
    have him : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by
      rw [mul_im, log_im, show (1 / 2 : ℂ).re = 1 / 2 by norm_num,
        show (1 / 2 : ℂ).im = 0 by norm_num]; ring
    dsimp [ζ]
    rw [← Complex.cpow_mul (-a + (-1 / 2 : ℂ))
      (by rw [him]; linarith [neg_pi_lt_arg z, Real.pi_pos])
      (by rw [him]; linarith [arg_le_pi z, Real.pi_pos])]
    congr 1; ring
  set P : ℕ → ℂ := fun k ↦ ζ ^ (-a) * (k : ℂ) ^ (a / 2 - 1 / 4) *
    cexp (-2 * ζ * (k : ℂ) ^ (1 / 2 : ℂ))
  refine (((Asymptotics.IsEquivalent.refl (l := atTop) (u := P)).mul
    ((Asymptotics.isEquivalent_const_iff_tendsto hL0).mpr hint_lim)).congr_left ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    exact (shiftedLaplaceIntegral_sub_eq_mul_integral_saddleIntegrand a hz hk).symm
  · refine Eventually.of_forall fun k ↦ ?_
    dsimp [P, Function.const]
    linear_combination (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * (k : ℂ) ^ (a / 2 - 1 / 4) *
      cexp (-2 * ζ * (k : ℂ) ^ (1 / 2 : ℂ)) * hzeta_pow

end TauCeti

end
