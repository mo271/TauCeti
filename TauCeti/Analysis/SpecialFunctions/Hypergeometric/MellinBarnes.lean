/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.ParametricIntegral
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Mellin–Barnes integrals for the Gauss hypergeometric function

This file establishes the convergence, holomorphy, and evaluation of the two classical
Mellin–Barnes vertical-line integrals for the regularized Gauss hypergeometric function
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6) and [DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)).

1. **DLMF 15.6.6** (argument `-z ∈ slitPlane`, parameter `c` arbitrary):
   Along any vertical line `Re t = σ` avoiding the poles of `Γ(a + t)`, `Γ(b + t)`, and `Γ(-t)`,
   Stirling's upper bound for `Γ` and vertical-strip upper bound for `1 / Γ` make the integrand
   `Γ(a + t) Γ(b + t) Γ(-t) (Γ(c + t))⁻¹ (-z)^t` decay exponentially as
   `O((1 + |y|)^P e^{-(π - |arg(-z)|)|y|})`, uniformly on compact subsets of `(c, z)`. By
   `TauCeti.analyticAt_integral_of_dominated`, the integral is jointly holomorphic in `(c, z)` on
   `ℂ × {z | -z ∈ slitPlane}` (hence entire in `c` for each fixed `z` off `[0, ∞)`). When
   `-min(Re a, Re b) < σ < 0` and `0 < Re b < Re c`, inserting the Mellin–Barnes integral of
   `(1 + x u)^{-a}` into Euler's integral and exchanging integrations by Fubini evaluates the
   integral as `Complex.eulerIntegral a b c z` first for `z = -x` (`x > 0`), and then throughout
   `-z ∈ slitPlane` by `AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq`.

2. **DLMF 15.6.7** (argument `1 - z ∈ slitPlane`):
   Along any vertical line `Re t = σ` avoiding the poles of `Γ(a + t)`, `Γ(b + t)`,
   `Γ(c - a - b - t)`, and `Γ(-t)`, the four Gamma factors decay as `O((1 + |y|)^P e^{-2π|y|})`, so
   the integrand `Γ(a + t) Γ(b + t) Γ(c - a - b - t) Γ(-t) (1 - z)^t` is integrable for every
   `z : ℂ` and holomorphic in `z` on `{z | 1 - z ∈ slitPlane}`. When `σ` separates the two families
   of poles (`max(-Re a, -Re b) < σ < min(0, Re(c - a - b))`) and `‖z‖ < 1`, expanding `(1 - z)^t`
   by the binomial series, exchanging sum and integral by dominated convergence, and evaluating
   each term by Barnes's first lemma (`Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_line`)
   recovers `Complex.regularizedGaussHGFun a b c z`.

## Main results

* `Complex.integrable_mellinBarnesIntegrand`: integrability of the DLMF 15.6.6 integrand for
  `-z ∈ slitPlane` and arbitrary `c : ℂ`.
* `Complex.analyticOnNhd_integral_mellinBarnesIntegrand`: joint holomorphy of the DLMF 15.6.6
  integral in `(c, z)` on `{p : ℂ × ℂ | -p.2 ∈ slitPlane}`.
* `Complex.eulerIntegral_eq_mellinBarnes`: DLMF 15.6.6 against `Complex.eulerIntegral` on
  `{z | -z ∈ slitPlane}`.
* `Complex.integrable_mellinBarnesOneSubIntegrand`: integrability of the DLMF 15.6.7 integrand.
* `Complex.analyticOnNhd_integral_mellinBarnesOneSubIntegrand`: holomorphy of the DLMF 15.6.7
  integral on `{z | 1 - z ∈ slitPlane}`.
* `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub`: DLMF 15.6.7 against
  `Complex.regularizedGaussHGFun` on the open unit disk `‖z‖ < 1`.

## References

* NIST Digital Library of Mathematical Functions,
  [§15.6(ii)](https://dlmf.nist.gov/15.6.ii), equations 15.6.6 and 15.6.7.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., §14.5–14.52.
* G. E. Andrews, R. Askey, and R. Roy, *Special Functions*, Encyclopedia of Mathematics and its
  Applications **71**, Cambridge University Press, 1999, §§2.4 and 4.2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace Complex

/-! ### Auxiliary exponential decay and power bounds -/

/-- Any real power of `1 + |y|` multiplied by `exp (-ε |y|)` (`0 < ε`) is integrable on `ℝ`. -/
private theorem integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (P : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable fun y : ℝ ↦ (1 + |y|) ^ P * Real.exp (-(ε * |y|)) := by
  have hcont : Continuous fun y : ℝ ↦ (1 + |y|) ^ P * Real.exp (-(ε * |y|)) :=
    ((continuous_const.add continuous_abs).rpow continuous_const
      fun y ↦ Or.inl (by positivity : 1 + |y| ≠ 0)).mul (by fun_prop)
  rcases le_or_gt P 0 with hP | hP
  · refine (TauCeti.integrable_exp_neg_mul_abs hε).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg y]) hP)
  · set δ : ℝ := ε / (2 * P) with hδ_def
    have hδ : 0 < δ := by positivity
    set C : ℝ := max 1 δ⁻¹
    have hC : 0 < C := by positivity
    refine ((TauCeti.integrable_exp_neg_mul_abs (half_pos hε)).const_mul (C ^ P)).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    have hbase : 1 + |y| ≤ C * Real.exp (δ * |y|) := by
      have h1 : 1 ≤ C := le_max_left _ _
      have h2 : 1 ≤ C * δ := by
        calc (1 : ℝ) = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
          _ ≤ C * δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      calc 1 + |y| ≤ C + C * δ * |y| := by nlinarith [abs_nonneg y]
        _ = C * (1 + δ * |y|) := by ring
        _ ≤ C * Real.exp (δ * |y|) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (δ * |y|)]) hC.le
    have hrpow : (1 + |y|) ^ P ≤ C ^ P * Real.exp (ε / 2 * |y|) := by
      calc (1 + |y|) ^ P ≤ (C * Real.exp (δ * |y|)) ^ P :=
            Real.rpow_le_rpow (by positivity) hbase hP.le
        _ = C ^ P * (Real.exp (δ * |y|)) ^ P := Real.mul_rpow hC.le (Real.exp_pos _).le
        _ = C ^ P * Real.exp (ε / 2 * |y|) := by
          rw [← Real.exp_mul, hδ_def]
          congr 2
          field_simp
    rw [Real.norm_of_nonneg (by positivity)]
    calc (1 + |y|) ^ P * Real.exp (-(ε * |y|))
        ≤ (C ^ P * Real.exp (ε / 2 * |y|)) * Real.exp (-(ε * |y|)) :=
          mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le
      _ = C ^ P * Real.exp (-((ε / 2) * |y|)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- Around any `w₀ ∈ slitPlane`, there is an open neighbourhood `U ⊆ slitPlane` on which
`‖w ^ (σ + i y)‖ ≤ M * exp (θ |y|)` for a fixed `θ < π` and `M > 0`. -/
private theorem exists_open_nhds_norm_cpow_add_mul_I_le {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane)
    (σ : ℝ) :
    ∃ U : Set ℂ, IsOpen U ∧ w₀ ∈ U ∧ U ⊆ slitPlane ∧
      ∃ θ < π, ∃ M > 0, ∀ w ∈ U, ∀ y : ℝ,
        ‖w ^ ((σ : ℂ) + y * I)‖ ≤ M * Real.exp (θ * |y|) := by
  have harg₀ : |w₀.arg| < π := abs_arg_lt_pi_of_mem_slitPlane hw₀
  set θ : ℝ := (|w₀.arg| + π) / 2 with hθ_def
  have hθ_lt : θ < π := by linarith
  have hw₀_θ : |w₀.arg| < θ := by linarith
  set M : ℝ := ‖w₀‖ ^ σ + 1
  have hM : 0 < M := by positivity
  have hnhds : ∀ᶠ w : ℂ in 𝓝 w₀, w ∈ slitPlane ∧ |w.arg| < θ ∧ ‖w‖ ^ σ < M := by
    refine Eventually.and (isOpen_slitPlane.mem_nhds hw₀) (Eventually.and ?_ ?_)
    · exact (continuousAt_arg hw₀).abs.eventually (gt_mem_nhds hw₀_θ)
    · exact (continuous_norm.continuousAt.rpow continuousAt_const
        (Or.inl (norm_ne_zero_iff.2 (slitPlane_ne_zero hw₀)))).eventually
          (gt_mem_nhds (lt_add_one _))
  refine ⟨interior {w : ℂ | w ∈ slitPlane ∧ |w.arg| < θ ∧ ‖w‖ ^ σ < M}, isOpen_interior,
    mem_interior_iff_mem_nhds.2 hnhds, fun w hw ↦ (interior_subset hw).1,
    θ, hθ_lt, M, hM, fun w hw y ↦ ?_⟩
  obtain ⟨-, hw_arg, hw_rpow⟩ := interior_subset hw
  have hexp : (Real.exp (w.arg * y))⁻¹ ≤ Real.exp (θ * |y|) := by
    rw [← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    calc -(w.arg * y) ≤ |w.arg * y| := neg_le_abs _
      _ = |w.arg| * |y| := abs_mul _ _
      _ ≤ θ * |y| := mul_le_mul_of_nonneg_right hw_arg.le (abs_nonneg _)
  calc ‖w ^ ((σ : ℂ) + y * I)‖
      ≤ ‖w‖ ^ ((σ : ℂ) + y * I).re / Real.exp (w.arg * ((σ : ℂ) + y * I).im) := norm_cpow_le _ _
    _ = ‖w‖ ^ σ * (Real.exp (w.arg * y))⁻¹ := by simp [div_eq_mul_inv]
    _ ≤ M * Real.exp (θ * |y|) := mul_le_mul hw_rpow.le hexp (by positivity) hM.le

/-- Stirling upper bound for the three-Gamma product
`y ↦ Γ(a + σ + i y) Γ(b + σ + i y) Γ(-σ - i y)` along a pole-free vertical line. -/
private theorem exists_norm_three_Gamma_le {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    ∃ C > 0, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * Real.exp (-(3 * π / 2 * |y|)) := by
  obtain ⟨Ca, hCa, hba⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := a + σ)
    (by simpa using ha)
  obtain ⟨Cb, hCb, hbb⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := b + σ)
    (by simpa using hb)
  obtain ⟨Cσ, hCσ, hbσ⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := -(σ : ℂ))
    (fun n h ↦ hσ n (by simp at h; linarith))
  refine ⟨Ca * Cb * Cσ, by positivity, fun y ↦ ?_⟩
  have h1 : ‖Gamma (a + (σ + y * I))‖ ≤
      Ca * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [add_assoc] using hba y
  have h2 : ‖Gamma (b + (σ + y * I))‖ ≤
      Cb * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [add_assoc] using hbb y
  have h3 : ‖Gamma (-(σ + y * I))‖ ≤
      Cσ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    have heq : -(σ : ℂ) + (-y : ℝ) * I = -((σ : ℂ) + y * I) := by push_cast; ring
    rw [← heq]
    simpa [abs_neg] using hbσ (-y)
  have h1y : 0 < 1 + |y| := by positivity
  have hr : (a.re + σ - 1 / 2) + (b.re + σ - 1 / 2) + (-σ - 1 / 2) =
      a.re + b.re + σ - 3 / 2 := by ring
  have he : (-π * |y| / 2) + (-π * |y| / 2) + (-π * |y| / 2) = -(3 * π / 2 * |y|) := by ring
  rw [norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖
      ≤ (Ca * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (Cb * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (Cσ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
          (norm_nonneg _) (by positivity)
    _ = (Ca * Cb * Cσ) *
          ((1 + |y|) ^ (a.re + σ - 1 / 2) * (1 + |y|) ^ (b.re + σ - 1 / 2) *
            (1 + |y|) ^ (-σ - 1 / 2)) *
          (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
    _ = (Ca * Cb * Cσ) * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) *
          Real.exp (-(3 * π / 2 * |y|)) := by
        rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.exp_add, ← Real.exp_add, hr, he]

/-- Locally uniform upper bound in `c ∈ ball c₀ 1` for `‖(Γ(c + σ + i y))⁻¹‖` along `y : ℝ`. -/
private theorem exists_norm_inv_Gamma_ball_le (c₀ : ℂ) (σ : ℝ) :
    ∃ C > 0, ∃ B : ℝ, ∀ c ∈ ball c₀ 1, ∀ y : ℝ,
      ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤ C * (1 + |y|) ^ B * Real.exp (π / 2 * |y|) := by
  obtain ⟨C₀, hC₀, hstrip⟩ :=
    TauCeti.exists_norm_inv_Gamma_vertical_strip_le (c₀.re + σ - 1) (c₀.re + σ + 1)
  set B : ℝ := max (1 / 2 - (c₀.re + σ - 1)) 0
  have hB0 : 0 ≤ B := le_max_right _ _
  set K : ℝ := 1 + (|c₀.im| + 1) with hK_def
  refine ⟨C₀ * K ^ B * Real.exp (π * (|c₀.im| + 1) / 2), by positivity, B, fun c hc y ↦ ?_⟩
  have hc_norm : ‖c - c₀‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hc
  have hc_re : |c.re - c₀.re| < 1 := by simpa using (abs_re_le_norm (c - c₀)).trans_lt hc_norm
  have hc_im : |c.im| ≤ |c₀.im| + 1 := by
    have him : |c.im - c₀.im| < 1 := by simpa using (abs_im_le_norm (c - c₀)).trans_lt hc_norm
    have htri := abs_add_le c₀.im (c.im - c₀.im)
    rw [add_sub_cancel] at htri
    linarith
  have hs_re : (c + (σ + y * I)).re ∈ Icc (c₀.re + σ - 1) (c₀.re + σ + 1) := by
    obtain ⟨hl, hu⟩ := abs_lt.1 hc_re
    exact ⟨by simp; linarith, by simp; linarith⟩
  have hs_im : (c + (σ + y * I)).im = c.im + y := by simp
  have h1 : ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤
      C₀ * (1 + |c.im + y|) ^ (1 / 2 - (c.re + σ)) * Real.exp (π * |c.im + y| / 2) := by
    simpa [hs_im, add_assoc] using hstrip (c + (σ + y * I)) hs_re
  have hrpow : (1 + |c.im + y|) ^ (1 / 2 - (c.re + σ)) ≤ K ^ B * (1 + |y|) ^ B := by
    have hexp_le : 1 / 2 - (c.re + σ) ≤ B := by
      have : c₀.re + σ - 1 ≤ c.re + σ := by simpa using hs_re.1
      linarith [le_max_left (1 / 2 - (c₀.re + σ - 1)) 0]
    have hsub : 1 + |c.im + y| ≤ K * (1 + |y|) := by
      have htri := abs_add_le c.im y
      rw [hK_def]
      linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ |c₀.im| + 1) (abs_nonneg y)]
    calc (1 + |c.im + y|) ^ (1 / 2 - (c.re + σ))
        ≤ (1 + |c.im + y|) ^ B :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (c.im + y)]) hexp_le
      _ ≤ (K * (1 + |y|)) ^ B := Real.rpow_le_rpow (by positivity) hsub hB0
      _ = K ^ B * (1 + |y|) ^ B := Real.mul_rpow (by positivity) (by positivity)
  have hexp : Real.exp (π * |c.im + y| / 2) ≤
      Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π / 2 * |y|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have htri : |c.im + y| ≤ (|c₀.im| + 1) + |y| := (abs_add_le c.im y).trans (by linarith)
    nlinarith [Real.pi_pos]
  calc ‖(Gamma (c + (σ + y * I)))⁻¹‖
      ≤ C₀ * (K ^ B * (1 + |y|) ^ B) *
          (Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π / 2 * |y|)) :=
        h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left hrpow hC₀.le) hexp
          (by positivity) (by positivity))
    _ = (C₀ * K ^ B * Real.exp (π * (|c₀.im| + 1) / 2)) * (1 + |y|) ^ B *
          Real.exp (π / 2 * |y|) := by ring

/-! ### DLMF 15.6.6: Mellin–Barnes integral in `-z` -/

/-- Continuity in `y : ℝ` of the three-Gamma factor `Γ(a + σ + i y) Γ(b + σ + i y) Γ(-σ - i y)`
along a pole-free vertical line. -/
private theorem continuous_three_Gamma {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) := by
  refine ((continuous_iff_continuousAt.2 fun y ↦ ?_).mul
    (continuous_iff_continuousAt.2 fun y ↦ ?_)).mul (continuous_iff_continuousAt.2 fun y ↦ ?_)
  · exact (differentiableAt_Gamma _ fun m h ↦
      ha m (by simpa [add_assoc] using congrArg re h)).continuousAt.comp (by fun_prop)
  · exact (differentiableAt_Gamma _ fun m h ↦
      hb m (by simpa [add_assoc] using congrArg re h)).continuousAt.comp (by fun_prop)
  · exact (differentiableAt_Gamma _ fun m h ↦
      hσ m (by have := congrArg re h; simp at this; linarith)).continuousAt.comp (by fun_prop)

/-- Locally uniform integrable domination for the DLMF 15.6.6 integrand near `(c₀, z₀)` with
`-z₀ ∈ slitPlane`. -/
private theorem exists_nhds_mellinBarnes_bound {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n)
    (c₀ : ℂ) {z₀ : ℂ} (hz₀ : -z₀ ∈ slitPlane) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (c₀, z₀) ∈ W ∧ (∀ p ∈ W, -p.2 ∈ slitPlane) ∧
      ∃ bound : ℝ → ℝ, Integrable bound volume ∧ ∀ p ∈ W, ∀ y : ℝ,
        ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
            (Gamma (p.1 + (σ + y * I)))⁻¹ * (-p.2) ^ ((σ : ℂ) + y * I)‖ ≤ bound y := by
  obtain ⟨C₃, hC₃, hb₃⟩ := exists_norm_three_Gamma_le ha hb hσ
  obtain ⟨Ci, hCi, B, hbi⟩ := exists_norm_inv_Gamma_ball_le c₀ σ
  obtain ⟨U, hU_open, hw₀U, hU_slit, θ, hθ, M, _, hcpow⟩ :=
    exists_open_nhds_norm_cpow_add_mul_I_le hz₀ σ
  set P : ℝ := a.re + b.re + σ - 3 / 2 + B with hP_def
  refine ⟨ball c₀ 1 ×ˢ {z : ℂ | -z ∈ U}, isOpen_ball.prod (hU_open.preimage continuous_neg),
    ⟨mem_ball_self one_pos, hw₀U⟩, fun p hp ↦ hU_slit hp.2,
    fun y ↦ (C₃ * Ci * M) * ((1 + |y|) ^ P * Real.exp (-((π - θ) * |y|))),
    (integrable_one_add_abs_rpow_mul_exp_neg_mul_abs P (by linarith)).const_mul _,
    fun p hp y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by positivity
  have he : -(3 * π / 2 * |y|) + π / 2 * |y| + θ * |y| = -((π - θ) * |y|) := by ring
  rw [norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        ‖(Gamma (p.1 + (σ + y * I)))⁻¹‖ * ‖(-p.2) ^ ((σ : ℂ) + y * I)‖
      ≤ (C₃ * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * Real.exp (-(3 * π / 2 * |y|))) *
          (Ci * (1 + |y|) ^ B * Real.exp (π / 2 * |y|)) * (M * Real.exp (θ * |y|)) :=
        mul_le_mul (mul_le_mul (hb₃ y) (hbi p.1 hp.1 y) (norm_nonneg _) (by positivity))
          (hcpow (-p.2) hp.2 y) (norm_nonneg _) (by positivity)
    _ = (C₃ * Ci * M) * (((1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * (1 + |y|) ^ B) *
          (Real.exp (-(3 * π / 2 * |y|)) * Real.exp (π / 2 * |y|) * Real.exp (θ * |y|))) := by ring
    _ = (C₃ * Ci * M) * ((1 + |y|) ^ P * Real.exp (-((π - θ) * |y|))) := by
        rw [← Real.rpow_add h1y, ← Real.exp_add, ← Real.exp_add, ← hP_def, he]

/-- For `-z ∈ slitPlane`, arbitrary `c : ℂ`, and any vertical line `Re t = σ` avoiding the poles of
`Γ(a + t)`, `Γ(b + t)`, and `Γ(-t)`, the DLMF 15.6.6 integrand is integrable on `ℝ`. -/
theorem integrable_mellinBarnesIntegrand {a b : ℂ} (c : ℂ) {z : ℂ} (hz : -z ∈ slitPlane) {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  obtain ⟨W, -, hpW, -, bound, hbound_int, hbound⟩ :=
    exists_nhds_mellinBarnes_bound ha hb hσ c hz
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I) :=
    ((continuous_three_Gamma ha hb hσ).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero hz)))
  exact hbound_int.mono' hcont.aestronglyMeasurable (Eventually.of_forall (hbound (c, z) hpW))

/-- Along any pole-free vertical line `Re t = σ`, the DLMF 15.6.6 Mellin–Barnes integral is jointly
holomorphic in `(c, z)` on `{p : ℂ × ℂ | -p.2 ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_mellinBarnesIntegrand {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (p.1 + (σ + y * I)))⁻¹ * (-p.2) ^ (σ + y * I))
      {p : ℂ × ℂ | -p.2 ∈ slitPlane} := fun p₀ hp₀ ↦ by
  obtain ⟨W, hW_open, hp₀W, hW_slit, bound, hbound_int, hbound⟩ :=
    exists_nhds_mellinBarnes_bound ha hb hσ p₀.1 hp₀
  refine TauCeti.analyticAt_integral_of_dominated (hW_open.mem_nhds hp₀W) (fun p hp ↦ ?_)
    hbound_int (Eventually.of_forall fun y p hp ↦ hbound p hp y)
    (Eventually.of_forall fun y p hp ↦ ?_)
  · exact (((continuous_three_Gamma ha hb hσ).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero (hW_slit p hp))))
        ).aestronglyMeasurable
  · have hd1 : DifferentiableAt ℂ (fun q : ℂ × ℂ ↦ (Gamma (q.1 + (σ + y * I)))⁻¹) p :=
      (differentiable_one_div_Gamma.differentiableAt).comp p (differentiableAt_fst.add_const _)
    have hd2 : DifferentiableAt ℂ (fun q : ℂ × ℂ ↦ (-q.2) ^ ((σ : ℂ) + y * I)) p :=
      differentiableAt_snd.neg.cpow_const (hW_slit p hp)
    exact (((differentiableAt_const _).mul hd1).mul hd2).differentiableWithinAt

/-- Product integrability of the two-variable kernel in the Fubini step for DLMF 15.6.6 at
`z = -x` (`x > 0`). -/
private theorem integrable_eulerMellinKernel {a b c : ℂ} {σ x : ℝ}
    (hbc : b.re < c.re) (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) (hx : 0 < x) :
    Integrable
      (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ (b + σ - 1) * (1 - (p.1 : ℂ)) ^ (c - b - 1)) *
        (((x * p.1 : ℝ) : ℂ) ^ (p.2 * I) *
          (Gamma (a + σ + p.2 * I) * Gamma (-(σ : ℂ) - p.2 * I))))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hg₁ : Integrable (fun t : ℝ ↦ ‖(t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (betaIntegral_convergent (u := b + σ) (v := c - b) (by simp; linarith) (by simp; linarith))
    exact (hint.congr_set_ae Ioo_ae_eq_Ioc).norm
  have hg₂ : Integrable (fun y : ℝ ↦ ‖Gamma (a + σ + y * I) * Gamma (-(σ : ℂ) - y * I)‖) volume :=
    (integrable_Gamma_add_mul_Gamma_sub
      (fun n h ↦ by simp at h; linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by simp at h; linarith [n.cast_nonneg' (α := ℝ)])).norm
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ (b + σ - 1) * (1 - (p.1 : ℂ)) ^ (c - b - 1)) *
        (((x * p.1 : ℝ) : ℂ) ^ (p.2 * I) *
          (Gamma (a + σ + p.2 * I) * Gamma (-(σ : ℂ) - p.2 * I))))
      (Ioo (0 : ℝ) 1 ×ˢ univ) := fun p hp ↦ by
    have h1t : 1 - (p.1 : ℂ) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.2 (sub_pos.2 hp.1.2)
    have hc1 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (b + σ - 1)) p :=
      (continuous_ofReal.comp continuous_fst).continuousAt.cpow continuousAt_const
        (ofReal_mem_slitPlane.2 hp.1.1)
    have hc2 : ContinuousAt (fun q : ℝ × ℝ ↦ (1 - (q.1 : ℂ)) ^ (c - b - 1)) p :=
      (continuous_const.sub (continuous_ofReal.comp continuous_fst)).continuousAt.cpow
        continuousAt_const h1t
    have hc3 : ContinuousAt (fun q : ℝ × ℝ ↦ ((x * q.1 : ℝ) : ℂ) ^ (q.2 * I)) p :=
      (continuous_ofReal.comp (continuous_const.mul continuous_fst)).continuousAt.cpow
        (by fun_prop) (ofReal_mem_slitPlane.2 (mul_pos hx hp.1.1))
    have hc4 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (a + σ + q.2 * I)) p :=
      (differentiableAt_Gamma _ fun m h ↦ by
        have := congrArg re h; simp at this; linarith [m.cast_nonneg' (α := ℝ)]).continuousAt.comp
        (by fun_prop)
    have hc5 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (-(σ : ℂ) - q.2 * I)) p :=
      (differentiableAt_Gamma _ fun m h ↦ by
        have := congrArg re h; simp at this; linarith [m.cast_nonneg' (α := ℝ)]).continuousAt.comp
        (by fun_prop)
    exact ((hc1.mul hc2).mul (hc3.mul (hc4.mul hc5))).continuousWithinAt
  have hprod_eq : (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  refine (hg₁.smul_prod hg₂).mono'
    (hprod_eq ▸ hcont.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)) ?_
  filter_upwards [hprod_eq ▸ ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
  have hnorm_I : ‖((x * p.1 : ℝ) : ℂ) ^ ((p.2 : ℂ) * I)‖ = 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos (mul_pos hx hp.1.1)]
    simp
  rw [norm_mul, norm_mul (((x * p.1 : ℝ) : ℂ) ^ _) _, hnorm_I, one_mul, smul_eq_mul]

/-- The `y`-first iterated integral in the Fubini step for DLMF 15.6.6 evaluates to Euler's
integral. -/
private theorem integral_eulerMellinKernel_right (a : ℂ) {b c : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ)
    {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (σ : ℂ) * ∫ t in Ioo (0 : ℝ) 1, ∫ y : ℝ,
      ((t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        (((x * t : ℝ) : ℂ) ^ (y * I) * (Gamma (a + σ + y * I) * Gamma (-(σ : ℂ) - y * I))) =
      2 * π * Gamma a * (Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ))) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hinner : ∀ t ∈ Ioo (0 : ℝ) 1,
      (x : ℂ) ^ (σ : ℂ) * ∫ y : ℝ,
        ((t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          (((x * t : ℝ) : ℂ) ^ (y * I) * (Gamma (a + σ + y * I) * Gamma (-(σ : ℂ) - y * I))) =
        (2 * π * Gamma a) *
          ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
            (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) := fun t ht ↦ by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.1.ne'
    rw [integral_const_mul, integral_cpow_mul_I_mul_Gamma_add_mul_Gamma_sub
      (by simp; linarith) (by simp; linarith) (mul_pos hx ht.1)]
    have hsum : a + σ + -(σ : ℂ) = a := by ring
    have hxt : ((x * t : ℝ) : ℂ) ^ (-(σ : ℂ)) =
        (x : ℂ) ^ (-(σ : ℂ)) * (t : ℂ) ^ (-(σ : ℂ)) := by
      rw [ofReal_mul, TauCeti.ofReal_mul_cpow hx.le]
    have hxcancel : (x : ℂ) ^ (σ : ℂ) * (x : ℂ) ^ (-(σ : ℂ)) = 1 := by
      rw [← cpow_add _ _ hx0, add_neg_cancel, cpow_zero]
    have htpow : (t : ℂ) ^ (b + σ - 1) * (t : ℂ) ^ (-(σ : ℂ)) = (t : ℂ) ^ (b - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have h1xt : 1 + ((x * t : ℝ) : ℂ) = 1 - (-(x : ℂ)) * (t : ℂ) := by push_cast; ring
    rw [hsum, hxt, h1xt]
    linear_combination
      (2 * π * Gamma a * (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) * hxcancel +
      (2 * π * Gamma a * (1 - (t : ℂ)) ^ (c - b - 1) * (x : ℂ) ^ (σ : ℂ) *
        (x : ℂ) ^ (-(σ : ℂ)) * (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) * htpow
  rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioo hinner, integral_const_mul,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hΓb : Gamma b * Gamma (c - b) ≠ 0 :=
    mul_ne_zero (Gamma_ne_zero_of_re_pos hb) (Gamma_ne_zero_of_re_pos (by simp; linarith))
  rw [eulerIntegral_def, mul_inv_cancel_left₀ hΓb]

/-- The `t`-first iterated integral in the Fubini step for DLMF 15.6.6 evaluates to the
Mellin–Barnes integral via the complex Beta integral. -/
private theorem integral_eulerMellinKernel_left (a : ℂ) {b c : ℂ}
    (hbc : b.re < c.re) {σ : ℝ} (hbσ : -b.re < σ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (σ : ℂ) * ∫ y : ℝ, ∫ t in Ioo (0 : ℝ) 1,
      ((t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        (((x * t : ℝ) : ℂ) ^ (y * I) * (Gamma (a + σ + y * I) * Gamma (-(σ : ℂ) - y * I))) =
      Gamma (c - b) * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hinner : ∀ y : ℝ, (x : ℂ) ^ (σ : ℂ) * ∫ t in Ioo (0 : ℝ) 1,
      ((t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        (((x * t : ℝ) : ℂ) ^ (y * I) * (Gamma (a + σ + y * I) * Gamma (-(σ : ℂ) - y * I))) =
      Gamma (c - b) * (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I)) := fun y ↦ by
    have hcongr : ∀ t ∈ Ioo (0 : ℝ) 1,
        ((t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          (((x * t : ℝ) : ℂ) ^ (y * I) * (Gamma (a + σ + y * I) * Gamma (-(σ : ℂ) - y * I))) =
        ((t : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          ((x : ℂ) ^ (y * I) * (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)))) := fun t ht ↦ by
      have htpow : (t : ℂ) ^ (b + σ - 1) * (t : ℂ) ^ (y * I) =
          (t : ℂ) ^ (b + (σ + y * I) - 1) := by
        rw [← cpow_add _ _ (ofReal_ne_zero.2 ht.1.ne')]; ring_nf
      have hxt : ((x * t : ℝ) : ℂ) ^ (y * I) = (x : ℂ) ^ (y * I) * (t : ℂ) ^ (y * I) := by
        rw [ofReal_mul, TauCeti.ofReal_mul_cpow hx.le]
      have ha_eq : a + σ + y * I = a + (σ + y * I) := by ring
      have hσ_eq : -(σ : ℂ) - y * I = -((σ : ℂ) + y * I) := by ring
      rw [hxt, ha_eq, hσ_eq]
      linear_combination
        ((1 - (t : ℂ)) ^ (c - b - 1) * (x : ℂ) ^ (y * I) *
          (Gamma (a + (σ + y * I)) * Gamma (-((σ : ℂ) + y * I)))) * htpow
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_mul_const]
    have hbeta : (∫ t in Ioo (0 : ℝ) 1,
        (t : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) =
        Gamma (b + (σ + y * I)) * Gamma (c - b) / Gamma (c + (σ + y * I)) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one, ← betaIntegral,
        betaIntegral_eq_Gamma_mul_div _ _ (by simp; linarith) (by simp; linarith)]
      congr 2
      ring
    have hxpow : (x : ℂ) ^ (σ : ℂ) * (x : ℂ) ^ (y * I) = (x : ℂ) ^ ((σ : ℂ) + y * I) :=
      (cpow_add _ _ hx0).symm
    rw [hbeta, div_eq_mul_inv]
    linear_combination
      (Gamma (c - b) * Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-((σ : ℂ) + y * I)) * (Gamma (c + (σ + y * I)))⁻¹) * hxpow
  rw [← integral_const_mul]
  simp_rw [hinner, integral_const_mul]

/-- Evaluation of DLMF 15.6.6 at a negative real argument `z = -x` (`x > 0`). -/
private theorem eulerIntegral_neg_ofReal_eq_mellinBarnes (a : ℂ) {b c : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ)
    {x : ℝ} (hx : 0 < x) :
    eulerIntegral a b c (-(x : ℂ)) =
      (2 * π * Gamma a * Gamma b)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
  have hswap := integral_integral_swap (μ := volume.restrict (Ioo (0 : ℝ) 1)) (ν := volume)
    (f := fun (t : ℝ) (y : ℝ) ↦ ((t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
      (((x * t : ℝ) : ℂ) ^ (y * I) * (Gamma (a + σ + y * I) * Gamma (-(σ : ℂ) - y * I))))
    (integrable_eulerMellinKernel hbc hσ haσ hbσ hx)
  set J : ℂ := ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
    Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I)
  have heq : 2 * π * Gamma a * (Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ))) =
      Gamma (c - b) * J := by
    rw [← integral_eulerMellinKernel_right a hb hbc hσ haσ hx,
      ← integral_eulerMellinKernel_left a hbc hbσ hx, hswap]
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  calc eulerIntegral a b c (-(x : ℂ))
      = (2 * π * Gamma a * Gamma b * Gamma (c - b))⁻¹ *
          (2 * π * Gamma a * (Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ)))) := by
        field_simp [h2pi, hΓa, hΓb, hΓcb]
    _ = (2 * π * Gamma a * Gamma b * Gamma (c - b))⁻¹ * (Gamma (c - b) * J) := by rw [heq]
    _ = (2 * π * Gamma a * Gamma b)⁻¹ * J := by field_simp [h2pi, hΓa, hΓb, hΓcb]

/-- **Mellin–Barnes integral representation of Euler's hypergeometric integral**
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6)). For `0 < Re b < Re c`, `-z ∈ slitPlane`, and any
real `σ` with `-min(Re a, Re b) < σ < 0`,
`eulerIntegral a b c z = (2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + σ + i y) Γ(b + σ + i y) Γ(-σ - i y)
  (Γ(c + σ + i y))⁻¹ (-z)^{σ + i y} dy`. -/
theorem eulerIntegral_eq_mellinBarnes (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : -z ∈ slitPlane)
    {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z =
      (2 * π * Gamma a * Gamma b)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  have hneg : ∀ w : ℂ, AnalyticAt ℂ (fun x : ℂ ↦ -x) w := fun _ ↦ analyticAt_id.neg
  have hf : AnalyticOnNhd ℂ (fun w : ℂ ↦ eulerIntegral a b c (-w)) slitPlane := by
    intro w hw
    have hmem : 1 - -w ∈ slitPlane := by
      have h1 : (1 : ℂ) - -w = ((1 : ℝ) : ℂ) + w := by simp
      rw [h1]
      exact TauCeti.ofReal_add_mem_slitPlane hw zero_le_one
    exact AnalyticAt.comp₂ (f := fun _ : ℂ ↦ a) (g := fun x : ℂ ↦ -x)
      ((analyticOnNhd_eulerIntegral hb hbc) (a, -w) hmem) analyticAt_const (hneg w)
  have hg : AnalyticOnNhd ℂ (fun w : ℂ ↦ (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * w ^ (σ + y * I)) slitPlane := by
    refine analyticOnNhd_const.mul fun w hw ↦ ?_
    have hcomp := AnalyticAt.comp₂ (f := fun _ : ℂ ↦ c) (g := fun x : ℂ ↦ -x)
      (analyticOnNhd_integral_mellinBarnesIntegrand (a := a) (b := b) (σ := σ)
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
        (c, -w) (by simpa using hw))
      analyticAt_const (hneg w)
    simpa using hcomp
  have heq := hf.eqOn_slitPlane_of_ofReal_pos_eq hg fun x hx ↦
    eulerIntegral_neg_ofReal_eq_mellinBarnes a hb hbc hσ haσ hbσ hx
  simpa using heq hz

/-! ### DLMF 15.6.7: four-Gamma Mellin–Barnes integral in `1 - z` -/

/-- Stirling upper bound for the four-Gamma product
`y ↦ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - a - b - σ - i y) Γ(-σ - i y)` along a pole-free vertical
line. -/
private theorem exists_norm_four_Gamma_le {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    ∃ C > 0, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * (1 + |y|) ^ (c.re - 2) * Real.exp (-(2 * π * |y|)) := by
  obtain ⟨C₃, hC₃, hb₃⟩ := exists_norm_three_Gamma_le ha hb hσ
  obtain ⟨Cc, hCc, hbc⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := c - a - b - σ)
    (fun n h ↦ hc n (by simpa [sub_re] using h))
  refine ⟨C₃ * Cc, by positivity, fun y ↦ ?_⟩
  have h4 : ‖Gamma (c - a - b - (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ ((c - a - b).re - σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    have heq : c - a - b - (σ : ℂ) + (-y : ℝ) * I = c - a - b - ((σ : ℂ) + y * I) := by
      push_cast; ring
    rw [← heq]
    simpa [abs_neg, sub_re] using hbc (-y)
  have h1y : 0 < 1 + |y| := by positivity
  have hr : (a.re + b.re + σ - 3 / 2) + ((c - a - b).re - σ - 1 / 2) = c.re - 2 := by
    simp only [sub_re]; ring
  have he : -(3 * π / 2 * |y|) + (-π * |y| / 2) = -(2 * π * |y|) := by ring
  have hcomm : Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) =
      (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))) *
        Gamma (c - a - b - (σ + y * I)) := by ring
  rw [hcomm, norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        ‖Gamma (c - a - b - (σ + y * I))‖
      ≤ (C₃ * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * Real.exp (-(3 * π / 2 * |y|))) *
          (Cc * (1 + |y|) ^ ((c - a - b).re - σ - 1 / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (hb₃ y) h4 (norm_nonneg _) (by positivity)
    _ = (C₃ * Cc) *
          ((1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * (1 + |y|) ^ ((c - a - b).re - σ - 1 / 2)) *
          (Real.exp (-(3 * π / 2 * |y|)) * Real.exp (-π * |y| / 2)) := by ring
    _ = (C₃ * Cc) * (1 + |y|) ^ (c.re - 2) * Real.exp (-(2 * π * |y|)) := by
        rw [← Real.rpow_add h1y, ← Real.exp_add, hr, he]

/-- Along any vertical line `Re t = σ` avoiding the poles of the four Gamma factors, the
DLMF 15.6.7 integrand is integrable on `ℝ` for every `z : ℂ`. -/
theorem integrable_mellinBarnesOneSubIntegrand {a b c : ℂ} (z : ℂ) {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  by_cases hz1 : z = 1
  · have hzero : (fun y : ℝ ↦ Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) = 0 := by
      ext y
      have hne : (σ : ℂ) + y * I ≠ 0 := fun h ↦ hσ 0 (by simpa using congrArg re h)
      simp [hz1, zero_cpow hne]
    rw [hzero]
    exact integrable_zero _ _ _
  obtain ⟨C₄, hC₄, hb₄⟩ := exists_norm_four_Gamma_le ha hb hc hσ
  have h1z : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hcont4 : Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ ((σ : ℂ) + y * I) := by
    have hc_gamma : Continuous fun y : ℝ ↦ Gamma (c - a - b - (σ + y * I)) :=
      continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m h ↦
          hc m (by simpa [sub_re] using congrArg re h)).continuousAt.comp (by fun_prop)
    have h3 := continuous_three_Gamma ha hb hσ
    have hcomm : (fun y : ℝ ↦ Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ ((σ : ℂ) + y * I)) =
        fun y : ℝ ↦ (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))) *
          Gamma (c - a - b - (σ + y * I)) * (1 - z) ^ ((σ : ℂ) + y * I) := by ext y; ring
    rw [hcomm]
    exact (h3.mul hc_gamma).mul (Continuous.const_cpow (by fun_prop) (Or.inl h1z))
  refine ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (c.re - 2) Real.pi_pos).const_mul
    (C₄ * ‖1 - z‖ ^ σ)).mono' hcont4.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have hpow : ‖(1 - z) ^ ((σ : ℂ) + y * I)‖ ≤ ‖1 - z‖ ^ σ * Real.exp (π * |y|) := by
    calc ‖(1 - z) ^ ((σ : ℂ) + y * I)‖
        ≤ ‖1 - z‖ ^ ((σ : ℂ) + y * I).re / Real.exp ((1 - z).arg * ((σ : ℂ) + y * I).im) :=
          norm_cpow_le _ _
      _ = ‖1 - z‖ ^ σ * (Real.exp ((1 - z).arg * y))⁻¹ := by simp [div_eq_mul_inv]
      _ ≤ ‖1 - z‖ ^ σ * Real.exp (π * |y|) :=
          mul_le_mul_of_nonneg_left (inv_exp_arg_mul_le_exp_pi_mul_abs (1 - z) y) (by positivity)
  rw [norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ * ‖(1 - z) ^ ((σ : ℂ) + y * I)‖
      ≤ (C₄ * (1 + |y|) ^ (c.re - 2) * Real.exp (-(2 * π * |y|))) *
          (‖1 - z‖ ^ σ * Real.exp (π * |y|)) :=
        mul_le_mul (hb₄ y) hpow (norm_nonneg _) (by positivity)
    _ = (C₄ * ‖1 - z‖ ^ σ) * ((1 + |y|) ^ (c.re - 2) *
          (Real.exp (-(2 * π * |y|)) * Real.exp (π * |y|))) := by ring
    _ = (C₄ * ‖1 - z‖ ^ σ) * ((1 + |y|) ^ (c.re - 2) * Real.exp (-(π * |y|))) := by
        rw [← Real.exp_add]
        congr 3
        ring

/-- Along any pole-free vertical line `Re t = σ`, the DLMF 15.6.7 Mellin–Barnes integral is
holomorphic in `z` on the cut plane `{z | 1 - z ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_mellinBarnesOneSubIntegrand {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} := fun z₀ hz₀ ↦ by
  obtain ⟨C₄, hC₄, hb₄⟩ := exists_norm_four_Gamma_le ha hb hc hσ
  obtain ⟨U, hU_open, hw₀U, hU_slit, θ, hθ, M, _, hcpow⟩ :=
    exists_open_nhds_norm_cpow_add_mul_I_le hz₀ σ
  set V : Set ℂ := {z : ℂ | 1 - z ∈ U}
  have hV_open : IsOpen V := hU_open.preimage (continuous_const.sub continuous_id)
  refine TauCeti.analyticAt_integral_of_dominated (hV_open.mem_nhds hw₀U)
    (fun z _ ↦ (integrable_mellinBarnesOneSubIntegrand z ha hb hc hσ).aestronglyMeasurable)
    ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (c.re - 2)
      (by linarith [Real.pi_pos] : 0 < 2 * π - θ)).const_mul (C₄ * M))
    (Eventually.of_forall fun y z hz ↦ ?_) (Eventually.of_forall fun y z hz ↦ ?_)
  · rw [norm_mul]
    calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ * ‖(1 - z) ^ ((σ : ℂ) + y * I)‖
        ≤ (C₄ * (1 + |y|) ^ (c.re - 2) * Real.exp (-(2 * π * |y|))) * (M * Real.exp (θ * |y|)) :=
          mul_le_mul (hb₄ y) (hcpow (1 - z) hz y) (norm_nonneg _) (by positivity)
      _ = (C₄ * M) * ((1 + |y|) ^ (c.re - 2) *
            (Real.exp (-(2 * π * |y|)) * Real.exp (θ * |y|))) := by ring
      _ = (C₄ * M) * ((1 + |y|) ^ (c.re - 2) * Real.exp (-((2 * π - θ) * |y|))) := by
          rw [← Real.exp_add]
          congr 3
          ring
  · exact ((differentiableAt_const _).mul
      (((differentiableAt_const 1).sub differentiableAt_id).cpow_const
        (hU_slit hz))).differentiableWithinAt

/-- For `0 < Re w`, `multichoose w n * Γ(w) = Γ(w + n) / n!`. -/
private theorem multichoose_mul_Gamma_eq {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    Ring.multichoose w n * Gamma w = Gamma (w + n) / (n ! : ℂ) := by
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer w n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h1
  have h2 := Gamma_add_nat_div_Gamma_eq w (ne_neg_natCast_of_re_pos hw) (n := n)
  rw [div_eq_iff (Gamma_ne_zero_of_re_pos hw)] at h2
  rw [eq_div_iff (Nat.cast_ne_zero.2 n.factorial_ne_zero)]
  linear_combination Gamma w * h1 - h2

/-- For `0 < x`, `multichoose x n * Real.Gamma x = Real.Gamma (x + n) / n!`. -/
private theorem real_multichoose_mul_Gamma_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Ring.multichoose x n * Real.Gamma x = Real.Gamma (x + n) / (n ! : ℝ) := by
  have h2 : Real.Gamma (x + n) = (ascPochhammer ℝ n).eval x * Real.Gamma x := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Real.Gamma_add_one (by positivity), ih,
        ascPochhammer_succ_eval]
      ring
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer x n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h1
  rw [h2, ← h1, mul_assoc, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 n.factorial_ne_zero)]

/-- Continuity of `y ↦ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - a - b - σ - i y)` along a separating
vertical line. -/
private theorem continuous_three_Gamma_sub {a b c : ℂ} {σ : ℝ}
    (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) := by
  have hσc' : σ < c.re - a.re - b.re := by simpa [sub_re] using hσc
  refine ((continuous_iff_continuousAt.2 fun y ↦ ?_).mul
    (continuous_iff_continuousAt.2 fun y ↦ ?_)).mul (continuous_iff_continuousAt.2 fun y ↦ ?_)
  · exact (differentiableAt_Gamma _ fun m h ↦ by
      have := congrArg re h; simp at this; linarith [m.cast_nonneg' (α := ℝ)]
      ).continuousAt.comp (by fun_prop)
  · exact (differentiableAt_Gamma _ fun m h ↦ by
      have := congrArg re h; simp at this; linarith [m.cast_nonneg' (α := ℝ)]
      ).continuousAt.comp (by fun_prop)
  · exact (differentiableAt_Gamma _ fun m h ↦ by
      have := congrArg re h; simp at this; linarith [m.cast_nonneg' (α := ℝ)]
      ).continuousAt.comp (by fun_prop)

/-- Integrability of the norm of the `n`-independent three-Gamma factor
`Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - a - b - σ - i y)` in the series-domination step for
DLMF 15.6.7. -/
private theorem integrable_norm_three_Gamma_sub {a b c : ℂ} {σ : ℝ}
    (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    Integrable (fun y : ℝ ↦ ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I))‖) volume := by
  have hσc' : σ < c.re - a.re - b.re := by simpa [sub_re] using hσc
  obtain ⟨Ca, hCa, hba⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := a + σ)
    (fun n h ↦ by simp at h; linarith [n.cast_nonneg' (α := ℝ)])
  obtain ⟨Cb, hCb, hbb⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := b + σ)
    (fun n h ↦ by simp at h; linarith [n.cast_nonneg' (α := ℝ)])
  obtain ⟨Cc, _, hbc⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := c - a - b - σ)
    (fun n h ↦ by simp at h; linarith [n.cast_nonneg' (α := ℝ)])
  refine ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (c.re + σ - 3 / 2)
    (by positivity : 0 < 3 * π / 2)).const_mul (Ca * Cb * Cc)).mono'
    (continuous_three_Gamma_sub hσc haσ hbσ).norm.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  have h1 : ‖Gamma (a + (σ + y * I))‖ ≤
      Ca * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [add_assoc] using hba y
  have h2 : ‖Gamma (b + (σ + y * I))‖ ≤
      Cb * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [add_assoc] using hbb y
  have h3 : ‖Gamma (c - a - b - (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ ((c - a - b).re - σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    have heq : c - a - b - (σ : ℂ) + (-y : ℝ) * I = c - a - b - ((σ : ℂ) + y * I) := by
      push_cast; ring
    rw [← heq]
    simpa [abs_neg, sub_re] using hbc (-y)
  have h1y : 0 < 1 + |y| := by positivity
  have hr : (a.re + σ - 1 / 2) + (b.re + σ - 1 / 2) + ((c - a - b).re - σ - 1 / 2) =
      c.re + σ - 3 / 2 := by simp only [sub_re]; ring
  have he : (-π * |y| / 2) + (-π * |y| / 2) + (-π * |y| / 2) = -(3 * π / 2 * |y|) := by ring
  rw [norm_norm, norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ *
        ‖Gamma (c - a - b - (σ + y * I))‖
      ≤ (Ca * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (Cb * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (Cc * (1 + |y|) ^ ((c - a - b).re - σ - 1 / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
          (norm_nonneg _) (by positivity)
    _ = (Ca * Cb * Cc) *
          (((1 + |y|) ^ (a.re + σ - 1 / 2) * (1 + |y|) ^ (b.re + σ - 1 / 2) *
              (1 + |y|) ^ ((c - a - b).re - σ - 1 / 2)) *
            (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2))) := by
        ring
    _ = (Ca * Cb * Cc) * ((1 + |y|) ^ (c.re + σ - 3 / 2) * Real.exp (-(3 * π / 2 * |y|))) := by
        rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.exp_add, ← Real.exp_add, hr, he]

/-- Evaluation of the `n`-th termwise integral in the binomial expansion of DLMF 15.6.7 via
Barnes's first lemma. -/
private theorem integral_mellinBarnesOneSub_term (a b c z : ℂ) {σ : ℝ}
    (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) (n : ℕ) :
    (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) *
        (Gamma (-((σ : ℂ) + y * I) + n) / (n ! : ℂ) * z ^ n) =
      z ^ n * (((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) /
        (n ! * Gamma (c + n))) := by
  have hcongr : (fun y : ℝ ↦ Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) *
        (Gamma (-((σ : ℂ) + y * I) + n) / (n ! : ℂ) * z ^ n)) =
      fun y : ℝ ↦ (z ^ n / (n ! : ℂ)) * (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma ((n : ℂ) - (σ + y * I))) := by
    ext y
    have harg : -((σ : ℂ) + y * I) + n = (n : ℂ) - (σ + y * I) := by ring
    rw [harg]
    ring
  rw [hcongr, integral_const_mul]
  have hbarnes := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_line (a := a) (b := b)
    (c := c - a - b) (d := n) haσ hbσ hσc (by simp; linarith [n.cast_nonneg' (α := ℝ)])
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  rw [inv_mul_eq_iff_eq_mul₀ h2pi] at hbarnes
  have hca : a + (c - a - b) = c - b := by ring
  have hcb : b + (c - a - b) = c - a := by ring
  have hsum : a + b + (c - a - b) + (n : ℂ) = c + n := by ring
  rw [hbarnes, hca, hcb, hsum]
  have ha_pos : 0 < a.re := by linarith
  have hb_pos : 0 < b.re := by linarith
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha_pos
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb_pos
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp at hσc ⊢; linarith)
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp at hσc ⊢; linarith)
  have hpa := (Gamma_add_nat_div_Gamma_eq a (ne_neg_natCast_of_re_pos ha_pos) (n := n)).symm
  have hpb := (Gamma_add_nat_div_Gamma_eq b (ne_neg_natCast_of_re_pos hb_pos) (n := n)).symm
  rw [hpa, hpb]
  field_simp [h2pi, hΓa, hΓb, hΓca, hΓcb]

/-- **Mellin–Barnes integral representation of the regularized Gauss hypergeometric series**
([DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)) on the open unit disk `‖z‖ < 1`: for any real `σ`
separating the poles of `Γ(a + t) Γ(b + t)` from those of `Γ(c - a - b - t) Γ(-t)`, i.e.
`max(-Re a, -Re b) < σ < min(0, Re(c - a - b))`,
`regularizedGaussHGFun a b c z = (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + σ + i y)
  Γ(b + σ + i y) Γ(c - a - b - σ - i y) Γ(-σ - i y) (1 - z)^{σ + i y} dy`. -/
theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    {σ : ℝ} (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  have hG_int := integrable_norm_three_Gamma_sub hσc haσ hbσ
  set c_n : ℕ → ℝ := fun n ↦ Real.Gamma (-σ) * (Ring.multichoose (-σ) n * ‖z‖ ^ n)
  have hterm_bound (n : ℕ) (y : ℝ) :
      ‖(Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (c - a - b - (σ + y * I))) *
          (Gamma (-((σ : ℂ) + y * I) + n) / (n ! : ℂ) * z ^ n)‖ ≤
        c_n n * ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I))‖ := by
    have hre : 0 < (-((σ : ℂ) + y * I) + n).re := by simp; linarith [n.cast_nonneg' (α := ℝ)]
    have hΓle : ‖Gamma (-((σ : ℂ) + y * I) + n)‖ ≤ Real.Gamma (-σ + n) := by
      simpa using norm_Gamma_le_Gamma_re hre
    rw [norm_mul _ (_ / _ * _), norm_mul (_ / _) _, norm_div, norm_natCast, norm_pow]
    calc _ ≤ ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I))‖ * (Real.Gamma (-σ + n) / n ! * ‖z‖ ^ n) := by gcongr
      _ = c_n n * ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I))‖ := by
        rw [← real_multichoose_mul_Gamma_eq (neg_pos.2 hσ) n]
        simp only [c_n]
        ring
  have hF_meas (n : ℕ) : AEStronglyMeasurable
      (fun y : ℝ ↦ (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I))) *
        (Gamma (-((σ : ℂ) + y * I) + n) / (n ! : ℂ) * z ^ n)) volume := by
    refine ((continuous_three_Gamma_sub hσc haσ hbσ).mul
      (((continuous_iff_continuousAt.2 fun y ↦ ?_).div_const _).mul
        continuous_const)).aestronglyMeasurable
    exact (differentiableAt_Gamma _ fun m h ↦ by
      have := congrArg re h; simp at this
      linarith [m.cast_nonneg' (α := ℝ), n.cast_nonneg' (α := ℝ)]).continuousAt.comp (by fun_prop)
  have hc_sum : Summable c_n :=
    (TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := -σ)
      (by simpa using hz)).summable.mul_left _
  have hptwise (y : ℝ) :
      HasSum (fun n : ℕ ↦ (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I))) *
          (Gamma (-((σ : ℂ) + y * I) + n) / (n ! : ℂ) * z ^ n))
        (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) := by
    have hbinom := TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one
      (r := -((σ : ℂ) + y * I)) hz
    rw [cpow_neg, one_div, inv_inv] at hbinom
    refine (hbinom.mul_left (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-((σ : ℂ) + y * I)))).congr_fun fun n ↦ ?_
    rw [← multichoose_mul_Gamma_eq (w := -((σ : ℂ) + y * I)) (by simp; linarith) n]
    ring
  have hhasSum_scaled := (hasSum_integral_of_dominated_convergence
    (fun n (y : ℝ) ↦ c_n n * ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I))‖)
    hF_meas (fun n ↦ Eventually.of_forall (hterm_bound n))
    (Eventually.of_forall fun y ↦ hc_sum.mul_right _)
    (by simp_rw [tsum_mul_right]; exact hG_int.const_mul _)
    (Eventually.of_forall hptwise)).mul_left
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹
  simp_rw [integral_mellinBarnesOneSub_term a b c z hσ hσc haσ hbσ] at hhasSum_scaled
  have hmem : z ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
    lt_of_lt_of_le (by rwa [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one])
      (radius_regularizedGaussHGFunSeries_ge_one a b c)
  refine (((regularizedGaussHGFunSeries a b c).hasSum hmem).congr_fun fun n ↦ ?_).unique
    hhasSum_scaled
  have := (regularizedGaussHGFunSeries a b c).apply_eq_pow_smul_coeff (n := n) (z := z)
  simp [coeff_regularizedGaussHGFunSeries, this]

/-! ### Concrete checks -/

/-- Specialization of `Complex.eulerIntegral_eq_mellinBarnes` at
`(a, b, c, z) = (3/5, 4/5, 17/10, -2)` along the vertical line `Re t = -3/10`. -/
example :
    eulerIntegral (3 / 5) (4 / 5) (17 / 10) (-2) =
      (2 * π * Gamma (3 / 5) * Gamma (4 / 5))⁻¹ *
        ∫ y : ℝ, Gamma (3 / 5 + ((-3 / 10 : ℝ) + y * I)) *
          Gamma (4 / 5 + ((-3 / 10 : ℝ) + y * I)) * Gamma (-((-3 / 10 : ℝ) + y * I)) *
          (Gamma (17 / 10 + ((-3 / 10 : ℝ) + y * I)))⁻¹ *
          (2 : ℂ) ^ ((-3 / 10 : ℝ) + y * I) := by
  simpa using eulerIntegral_eq_mellinBarnes (3 / 5) (b := 4 / 5) (c := 17 / 10) (z := -2)
    (σ := -3 / 10) (by norm_num) (by norm_num) (by simp)
    (by norm_num) (by norm_num) (by norm_num)

/-- Specialization of `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub` at
`(a, b, c, z) = (1/2, 1/2, 2, 1/2)` along the vertical line `Re t = -1/4`. -/
example :
    regularizedGaussHGFun (1 / 2) (1 / 2) 2 (1 / 2) =
      (2 * π * Gamma (1 / 2) * Gamma (1 / 2) * Gamma (2 - 1 / 2) * Gamma (2 - 1 / 2))⁻¹ *
        ∫ y : ℝ, Gamma (1 / 2 + ((-1 / 4 : ℝ) + y * I)) *
          Gamma (1 / 2 + ((-1 / 4 : ℝ) + y * I)) *
          Gamma (2 - 1 / 2 - 1 / 2 - ((-1 / 4 : ℝ) + y * I)) *
          Gamma (-((-1 / 4 : ℝ) + y * I)) * (1 - (1 / 2 : ℂ)) ^ ((-1 / 4 : ℝ) + y * I) :=
  regularizedGaussHGFun_eq_mellinBarnes_one_sub (1 / 2) (1 / 2) 2 (z := 1 / 2) (σ := -1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Complex

end
