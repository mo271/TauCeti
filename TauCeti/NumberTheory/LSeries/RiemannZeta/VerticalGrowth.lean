/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Complex.VerticalStripGrowth
import Mathlib.Analysis.Complex.PhragmenLindelof
import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
import TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Growth
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.NumberTheory.LSeries.HurwitzZetaGrowth
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# Order one and polynomial vertical-strip growth of the Riemann zeta function

Mathlib's `riemannZeta₁` is the entire function agreeing with `(s - 1) ζ(s)` away from `s = 1` and
taking the value `1` at `s = 1`. Globally on `ℂ`, the completed identity
`s * riemannZeta₁ s = (s * (s - 1) * completedRiemannZeta₀ s + 1) * (Gammaℝ s)⁻¹`
combines the Hurwitz Mellin growth bound for `completedRiemannZeta₀` with Euler's product bound for
`(Gammaℝ s)⁻¹` to give `‖riemannZeta₁ s‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))`, hence
`OrderLE riemannZeta₁ 1`.

On vertical strips `a ≤ Re s ≤ b`, `riemannZeta₁` grows only polynomially in `|Im s|`:
* On `Re s ≥ σ > 1`, comparing the Dirichlet series of `ζ` and `μ` against the real `p`-series at
  `σ` gives `(Re ζ(σ))⁻¹ ≤ ‖ζ(s)‖ ≤ Re ζ(σ)`.
* On a left line `Re s = a₀ ≤ -2`, the functional equation `riemannZeta_one_sub` expresses `ζ(s)`
  in terms of `Γ(1 - s) cos (π (1 - s) / 2) ζ(1 - s)`. Vertical Stirling's formula shows that the
  exponential decay of `Γ(1 - s)` cancels the exponential growth of `cos (π (1 - s) / 2)`, leaving
  polynomial growth `O(|Im s| ^ (1 / 2 - a₀))`.
* Applying the Phragmén–Lindelöf theorem on `a₀ ≤ Re s ≤ b₀` (`b₀ = max b 2`) to
  `riemannZeta₁ s / (s - (a₀ - 1)) ^ m` with `OrderLE riemannZeta₁ 1` as the interior a priori
  bound yields `‖riemannZeta₁ s‖ ≤ C (1 + |Im s|) ^ B` across the whole strip, hence
  `HasVerticalStripGrowth riemannZeta₁` and `HasVerticalStripGrowth riemannZeta`.

## Main results

* `TauCeti.mul_riemannZeta₁_eq`: the global identity
  `s * riemannZeta₁ s = (s * (s - 1) * completedRiemannZeta₀ s + 1) * (Gammaℝ s)⁻¹`.
* `TauCeti.exists_norm_riemannZeta₁_le_exp_mul_log` and `TauCeti.orderLE_riemannZeta₁`: global
  logarithmic-exponential bound and order at most one for `riemannZeta₁`.
* `TauCeti.norm_LSeries_le_mul_riemannZeta_re`, `TauCeti.norm_riemannZeta_le_of_re_ge`, and
  `TauCeti.inv_riemannZeta_re_le_norm_riemannZeta`: half-plane bounds on `Re s ≥ σ > 1`.
* `TauCeti.exists_norm_riemannZeta₁_le_rpow` and
  `TauCeti.exists_norm_riemannZeta₁_closedBall_le_rpow`: polynomial vertical-strip and shifted-disc
  bounds for `riemannZeta₁`.
* `TauCeti.hasVerticalStripGrowth_riemannZeta₁` and `TauCeti.hasVerticalStripGrowth_riemannZeta`.

## References

* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §§2.12, 3.5, 5.1.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
-/

public section

open Complex Real Set Metric Filter Asymptotics Topology
open scoped ComplexConjugate ArithmeticFunction.Moebius LSeries.notation

namespace TauCeti

/-! ### Algebraic identities and global order one of `riemannZeta₁` -/

/-- Away from `s = 1`, `riemannZeta₁ s` equals `(s - 1) * riemannZeta s`. -/
theorem riemannZeta₁_eq_sub_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.mpr hs)]

/-- At `s = 0`, `riemannZeta₁ 0 = 1 / 2`. -/
@[simp]
theorem riemannZeta₁_zero : riemannZeta₁ 0 = 1 / 2 := by
  rw [riemannZeta₁_eq_sub_mul zero_ne_one, riemannZeta_zero]
  norm_num

/-- `riemannZeta₁` commutes with complex conjugation everywhere on `ℂ`. -/
@[simp]
theorem riemannZeta₁_conj (s : ℂ) : riemannZeta₁ (conj s) = conj (riemannZeta₁ s) := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp
  · have hcs : conj s ≠ 1 := fun h ↦ hs (by simpa using congrArg conj h)
    rw [riemannZeta₁_eq_sub_mul hcs, riemannZeta₁_eq_sub_mul hs, map_mul, map_sub, map_one,
      riemannZeta_conj]

/-- Globally on `ℂ`, `s * riemannZeta₁ s` factors as the entire completed zeta function times
`(Gammaℝ s)⁻¹`. -/
theorem mul_riemannZeta₁_eq (s : ℂ) :
    s * riemannZeta₁ s = (s * (s - 1) * completedRiemannZeta₀ s + 1) * (Gammaℝ s)⁻¹ := by
  have hL : AnalyticOnNhd ℂ (fun z ↦ z * riemannZeta₁ z) univ :=
    (differentiable_id.mul differentiable_riemannZeta₁).differentiableOn.analyticOnNhd isOpen_univ
  have hR : AnalyticOnNhd ℂ
      (fun z ↦ (z * (z - 1) * completedRiemannZeta₀ z + 1) * (Gammaℝ z)⁻¹) univ :=
    ((((differentiable_id.mul (differentiable_id.sub_const 1)).mul
      differentiable_completedZeta₀).add_const 1).mul
      Complex.differentiable_Gammaℝ_inv).differentiableOn.analyticOnNhd isOpen_univ
  have heq : (fun z : ℂ ↦ z * riemannZeta₁ z) =ᶠ[𝓝 2]
      fun z ↦ (z * (z - 1) * completedRiemannZeta₀ z + 1) * (Gammaℝ z)⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z (hz : 1 < z.re)
    have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
    have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
    have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
    rw [riemannZeta₁_eq_sub_mul hz1, riemannZeta_def_of_ne_zero hz0, completedRiemannZeta_eq,
      div_eq_mul_inv, ← mul_assoc, ← mul_assoc]
    congr 1
    field_simp
    ring
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_univ (mem_univ 2) heq (mem_univ s)

/-- **Global logarithmic-exponential bound for `riemannZeta₁`.** There exists `C > 0` such that
`‖riemannZeta₁ s‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` for all `s : ℂ`. -/
theorem exists_norm_riemannZeta₁_le_exp_mul_log :
    ∃ C > 0, ∀ s : ℂ, ‖riemannZeta₁ s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C₀, hC₀, hΛ₀⟩ := HurwitzZeta.exists_norm_completedHurwitzZetaEven₀_le_exp_mul_log 0
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  set K := max M₀ 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hLK : 0 ≤ Real.log K := Real.log_nonneg hK1
  refine ⟨C₀ + 23 + 2 * Real.log K, by positivity, fun s ↦ ?_⟩
  set W := (1 + ‖s‖) * Real.log (2 + ‖s‖)
  rw [mul_assoc]
  have hlog : 1 / 2 ≤ Real.log (2 + ‖s‖) := one_half_le_log_two_add (norm_nonneg s)
  have hW_ge : 1 / 2 ≤ W := by nlinarith [norm_nonneg s]
  rcases le_or_gt ‖s‖ 1 with hs1 | hs1
  · calc ‖riemannZeta₁ s‖ ≤ K := (hM₀ s (by simpa using hs1)).trans (le_max_left _ _)
      _ = Real.exp (Real.log K) := (Real.exp_log (zero_lt_one.trans_le hK1)).symm
      _ ≤ Real.exp ((C₀ + 23 + 2 * Real.log K) * W) := Real.exp_le_exp.mpr (by nlinarith)
  · have hpoly : ‖s‖ * ‖s - 1‖ ≤ Real.exp (4 * W) := by
      have hsub : ‖s - 1‖ ≤ 1 + ‖s‖ := (norm_sub_le s 1).trans (by norm_num; linarith)
      have h1 : ‖s‖ * ‖s - 1‖ ≤ (1 + ‖s‖) ^ 2 := by nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
      have h2 : 1 + ‖s‖ ≤ Real.exp (1 + ‖s‖) := by linarith [Real.add_one_le_exp (1 + ‖s‖)]
      calc ‖s‖ * ‖s - 1‖ ≤ Real.exp (1 + ‖s‖) ^ 2 :=
            h1.trans (pow_le_pow_left₀ (by positivity) h2 2)
        _ = Real.exp (2 * (1 + ‖s‖)) := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ Real.exp (4 * W) := Real.exp_le_exp.mpr (by nlinarith [norm_nonneg s])
    have h0 : ‖completedRiemannZeta₀ s‖ ≤ Real.exp (C₀ * W) := by
      simpa only [HurwitzZeta.completedHurwitzZetaEven₀_zero, mul_assoc] using hΛ₀ s
    have hnum : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ ≤ Real.exp ((C₀ + 8) * W) := by
      have hmul : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ Real.exp ((C₀ + 4) * W) := by
        rw [norm_mul, norm_mul]
        exact (mul_le_mul hpoly h0 (norm_nonneg _) (Real.exp_pos _).le).trans_eq
          (by rw [← Real.exp_add]; congr 1; ring)
      have h2e : (2 : ℝ) ≤ Real.exp (4 * W) := by linarith [Real.add_one_le_exp (4 * W)]
      calc ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
          ≤ Real.exp ((C₀ + 4) * W) + 1 :=
            (norm_add_le _ _).trans (by simpa using add_le_add_right hmul 1)
        _ ≤ 2 * Real.exp ((C₀ + 4) * W) := by
            linarith [Real.one_le_exp (by nlinarith : 0 ≤ (C₀ + 4) * W)]
        _ ≤ Real.exp (4 * W) * Real.exp ((C₀ + 4) * W) :=
            mul_le_mul_of_nonneg_right h2e (Real.exp_pos _).le
        _ = Real.exp ((C₀ + 8) * W) := by rw [← Real.exp_add]; congr 1; ring
    calc ‖riemannZeta₁ s‖ ≤ ‖s‖ * ‖riemannZeta₁ s‖ := le_mul_of_one_le_left (norm_nonneg _) hs1.le
      _ = ‖(s * (s - 1) * completedRiemannZeta₀ s + 1) * (Gammaℝ s)⁻¹‖ := by
          rw [← norm_mul, mul_riemannZeta₁_eq]
      _ ≤ Real.exp ((C₀ + 8) * W) * Real.exp (15 * W) := by
          rw [norm_mul]
          exact mul_le_mul hnum (by simpa [W, mul_assoc] using norm_inv_Gammaℝ_le_exp_mul_log s)
            (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp ((C₀ + 23 + 2 * Real.log K) * W) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)

/-- The regularized zeta function `riemannZeta₁` is entire of order at most one. -/
theorem orderLE_riemannZeta₁ : OrderLE riemannZeta₁ 1 := by
  obtain ⟨C, -, hC⟩ := exists_norm_riemannZeta₁_le_exp_mul_log
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-! ### Half-plane Dirichlet-series bounds on `Re s ≥ σ > 1` -/

/-- On `Re s ≥ σ > 1`, any Dirichlet series whose nonzero coefficients have norm at most `m` has
norm at most `m * (riemannZeta σ).re`. -/
theorem norm_LSeries_le_mul_riemannZeta_re {f : ℕ → ℂ} {m σ : ℝ} {s : ℂ}
    (hf : ∀ n ≠ 0, ‖f n‖ ≤ m) (hσ : 1 < σ) (hσs : σ ≤ s.re) :
    ‖LSeries f s‖ ≤ m * (riemannZeta σ).re := by
  have hm : 0 ≤ m := (norm_nonneg _).trans (hf 1 one_ne_zero)
  have hsum := hasSum_nat_rpow_neg_riemannZeta_re hσ
  have hterm (n : ℕ) : ‖_root_.LSeries.term f s n‖ ≤ m * (n : ℝ) ^ (-σ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
    · simp only [_root_.LSeries.norm_term_eq, hn, ↓reduceIte,
        div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
      exact mul_le_mul (hf n hn)
        (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn))
          (neg_le_neg hσs)) (by positivity) hm
  calc ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖_root_.LSeries.term f s n‖ :=
        norm_tsum_le_tsum_norm (LSeriesSummable_of_bounded_of_one_lt_re hf (hσ.trans_le hσs)).norm
    _ ≤ ∑' n : ℕ, m * (n : ℝ) ^ (-σ) :=
        Summable.tsum_le_tsum hterm
          (LSeriesSummable_of_bounded_of_one_lt_re hf (hσ.trans_le hσs)).norm
          (hsum.summable.mul_left m)
    _ = m * (riemannZeta σ).re := by rw [tsum_mul_left, hsum.tsum_eq]

/-- On the half-plane `Re s ≥ σ > 1`, `‖riemannZeta s‖ ≤ (riemannZeta σ).re`. -/
theorem norm_riemannZeta_le_of_re_ge {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hσs : σ ≤ s.re) :
    ‖riemannZeta s‖ ≤ (riemannZeta σ).re := by
  rw [← LSeries_one_eq_riemannZeta (hσ.trans_le hσs)]
  simpa using norm_LSeries_le_mul_riemannZeta_re (m := 1) (fun n _ ↦ by simp) hσ hσs

/-- On the half-plane `Re s ≥ σ > 1`, `‖riemannZeta s‖` is bounded below by the positive constant
`((riemannZeta σ).re)⁻¹`. -/
theorem inv_riemannZeta_re_le_norm_riemannZeta {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hσs : σ ≤ s.re) :
    ((riemannZeta σ).re)⁻¹ ≤ ‖riemannZeta s‖ := by
  have hs : 1 < s.re := hσ.trans_le hσs
  have hpos : 0 < (riemannZeta σ).re := riemannZeta_re_pos_of_one_lt hσ
  have hμ_coeff (n : ℕ) (_ : n ≠ 0) : ‖(↗μ : ℕ → ℂ) n‖ ≤ 1 := by
    dsimp; norm_cast; exact ArithmeticFunction.abs_moebius_le_one
  have hμ : ‖LSeries ↗μ s‖ ≤ (riemannZeta σ).re := by
    simpa using norm_LSeries_le_mul_riemannZeta_re hμ_coeff hσ hσs
  have hmul : riemannZeta s * LSeries ↗μ s = 1 := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have h1 : 1 = ‖riemannZeta s‖ * ‖LSeries ↗μ s‖ := by
    simpa [norm_mul] using (congrArg norm hmul).symm
  rw [inv_le_iff_one_le_mul₀ hpos, h1]
  exact mul_le_mul_of_nonneg_left hμ (norm_nonneg _)

/-! ### Left-line reflection bound and Phragmén–Lindelöf on vertical strips -/

/-- On a vertical line `Re s = a₀ ≤ -2`, `‖riemannZeta s‖` grows at most like
`|Im s| ^ (1 / 2 - a₀)` at large height. -/
theorem exists_norm_riemannZeta_le_mul_rpow_of_re_eq {a₀ : ℝ} (ha₀ : a₀ ≤ -2) :
    ∃ C > 0, ∃ T ≥ (1 : ℝ), ∀ s : ℂ, s.re = a₀ → T ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (1 / 2 - a₀) := by
  obtain ⟨CG, TG, hG⟩ := exists_abs_log_norm_Gamma_vertical_sub_le (1 - a₀) (1 - a₀)
  refine ⟨2 * (2 * π) ^ (a₀ - 1) * Real.exp (Real.log (2 * π) / 2 + |CG|) * (riemannZeta 2).re,
    mul_pos (mul_pos (by positivity) (by positivity)) (riemannZeta_re_pos_of_one_lt one_lt_two),
    max TG 1, le_max_right _ _, fun s hs ht ↦ ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_right TG 1).trans ht
  -- Reflect `s` to `w = 1 - s` (`Re w = 1 - a₀ ≥ 3`) via `riemannZeta_one_sub`.
  set w : ℂ := 1 - s
  have hw_re : w.re = 1 - a₀ := by simp [w, hs]
  have hw_im : |w.im| = |s.im| := by simp [w]
  have hfe : riemannZeta s = 2 * (2 * π) ^ (-w) * Gamma w * Complex.cos (π * w / 2) *
      riemannZeta w := by
    have hs_eq : s = 1 - w := by simp [w]
    rw [hs_eq]
    refine riemannZeta_one_sub (fun n h ↦ ?_) (fun h ↦ ?_)
    · have := congrArg re h; simp [hw_re] at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · have := congrArg re h; simp [hw_re] at this; linarith
  -- Bound each factor `(2π) ^ (-w)`, `cos (π w / 2)`, `Γ(w)`, and `ζ(w)` separately.
  have h2pi_pow : ‖(2 * π : ℂ) ^ (-w)‖ = (2 * π) ^ (a₀ - 1) := by
    have h2pi : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [h2pi, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1; simp [hw_re]
  have hcos : ‖Complex.cos (π * w / 2)‖ ≤ Real.exp (π * |s.im| / 2) := by
    have him_z : |(π * w / 2).im| = π * |s.im| / 2 := by
      have h1 : (π * w / 2).im = -(π * s.im / 2) := by simp [w, div_eq_mul_inv]
      simp [h1, abs_div, abs_mul, abs_of_pos Real.pi_pos]
    have hneg : -(π * w / 2) * I = -(π * w / 2 * I) := by ring
    rw [Complex.cos, norm_div, Complex.norm_two, hneg]
    have h1 : ‖Complex.exp (π * w / 2 * I)‖ ≤ Real.exp (π * |s.im| / 2) := by
      rw [Complex.norm_exp, mul_I_re, ← him_z]; exact Real.exp_le_exp.mpr (neg_le_abs _)
    have h2 : ‖Complex.exp (-(π * w / 2 * I))‖ ≤ Real.exp (π * |s.im| / 2) := by
      rw [Complex.norm_exp, neg_re, mul_I_re, neg_neg, ← him_z]
      exact Real.exp_le_exp.mpr (le_abs_self _)
    linarith [(norm_add_le _ _).trans (add_le_add h1 h2)]
  have hGamma : ‖Gamma w‖ ≤ Real.exp (Real.log (2 * π) / 2 + |CG|) *
      |s.im| ^ (1 / 2 - a₀) * Real.exp (-π * |s.im| / 2) := by
    have hSt := hG w (by simp [hw_re]) (hw_im ▸ (le_max_left TG 1).trans ht)
    have hexp_eq : 1 - a₀ - 1 / 2 = 1 / 2 - a₀ := by ring
    rw [hw_re, hw_im, hexp_eq] at hSt
    have hCG_div : CG / |s.im| ≤ |CG| := (le_abs_self _).trans
      (by rw [abs_div, abs_abs]; exact div_le_self (abs_nonneg CG) ht1)
    have hlog_le : Real.log ‖Gamma w‖ ≤ (Real.log (2 * π) / 2 + |CG|) +
        Real.log |s.im| * (1 / 2 - a₀) + (-π * |s.im| / 2) := by linarith [(abs_le.mp hSt).2]
    rw [← Real.exp_log (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by linarith)))]
    exact (Real.exp_le_exp.mpr hlog_le).trans_eq
      (by rw [Real.exp_add, Real.exp_add, ← Real.rpow_def_of_pos (zero_lt_one.trans_le ht1)])
  rw [hfe, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_two, h2pi_pow]
  have hζw : ‖riemannZeta w‖ ≤ (riemannZeta 2).re := by
    simpa using norm_riemannZeta_le_of_re_ge one_lt_two (s := w) (by linarith)
  have hexp1 : Real.exp (-π * |s.im| / 2) * Real.exp (π * |s.im| / 2) = 1 := by
    have h0 : -π * |s.im| / 2 + π * |s.im| / 2 = 0 := by ring
    rw [← Real.exp_add, h0, Real.exp_zero]
  calc 2 * (2 * π) ^ (a₀ - 1) * ‖Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖
      ≤ 2 * (2 * π) ^ (a₀ - 1) *
          (Real.exp (Real.log (2 * π) / 2 + |CG|) * |s.im| ^ (1 / 2 - a₀) *
            Real.exp (-π * |s.im| / 2)) *
          Real.exp (π * |s.im| / 2) * (riemannZeta 2).re := by gcongr
    _ = 2 * (2 * π) ^ (a₀ - 1) * Real.exp (Real.log (2 * π) / 2 + |CG|) *
          (riemannZeta 2).re * |s.im| ^ (1 / 2 - a₀) := by
        linear_combination 2 * (2 * π) ^ (a₀ - 1) * Real.exp (Real.log (2 * π) / 2 + |CG|) *
          (riemannZeta 2).re * |s.im| ^ (1 / 2 - a₀) * hexp1

/-- Uniform bound on `riemannZeta₁ s / (s - (a₀ - 1)) ^ (k + 1)` along the whole line `Re s = a₀`,
combining `exists_norm_riemannZeta_le_mul_rpow_of_re_eq` above `T` with compactness on `[-T, T]`. -/
private theorem exists_norm_riemannZeta₁_div_pow_le_on_left_line {a₀ : ℝ} (ha₀ : a₀ ≤ -2)
    {k : ℕ} (hk : 1 / 2 - a₀ ≤ k) :
    ∃ M : ℝ, ∀ s : ℂ, s.re = a₀ → ‖riemannZeta₁ s / (s - (a₀ - 1 : ℝ)) ^ (k + 1)‖ ≤ M := by
  obtain ⟨C, hC, T, hT1, hhigh⟩ := exists_norm_riemannZeta_le_mul_rpow_of_re_eq ha₀
  set g : ℂ → ℂ := fun z ↦ riemannZeta₁ z / (z - (a₀ - 1 : ℝ)) ^ (k + 1)
  have hcont : ContinuousOn g ((fun t : ℝ ↦ (a₀ : ℂ) + t * I) '' Icc (-T) T) := by
    refine ContinuousOn.div differentiable_riemannZeta₁.continuous.continuousOn
      ((continuousOn_id.sub continuousOn_const).pow _) ?_
    rintro _ ⟨t, -, rfl⟩
    exact pow_ne_zero _ fun h0 ↦ by have := congrArg re h0; simp at this
  obtain ⟨M₀, hM₀⟩ := ((isCompact_Icc (a := -T) (b := T)).image
    (continuous_const.add (continuous_ofReal.mul continuous_const))).exists_bound_of_continuousOn
      hcont
  refine ⟨max M₀ ((1 + |a₀ - 2|) * C), fun s hs ↦ ?_⟩
  rcases le_or_gt |s.im| T with ht | ht
  · refine (hM₀ s ⟨s.im, abs_le.mp ht, ?_⟩).trans (le_max_left _ _)
    apply Complex.ext <;> simp [hs]
  · refine le_trans ?_ (le_max_right _ _)
    have ht1 : 1 ≤ |s.im| := hT1.trans ht.le
    have him_le : |s.im| ≤ ‖s - (a₀ - 1 : ℝ)‖ := by simpa using abs_im_le_norm (s - (a₀ - 1 : ℝ))
    have hbase1 : 1 ≤ ‖s - (a₀ - 1 : ℝ)‖ := ht1.trans him_le
    have hs1_le : ‖s - 1‖ ≤ (1 + |a₀ - 2|) * ‖s - (a₀ - 1 : ℝ)‖ := by
      have hsplit : s - 1 = (s - (a₀ - 1 : ℝ)) + ((a₀ - 2 : ℝ) : ℂ) := by push_cast; ring
      calc ‖s - 1‖ ≤ ‖s - (a₀ - 1 : ℝ)‖ + |a₀ - 2| := by
            rw [hsplit]
            exact (norm_add_le _ _).trans_eq (by rw [Complex.norm_real, Real.norm_eq_abs])
        _ ≤ (1 + |a₀ - 2|) * ‖s - (a₀ - 1 : ℝ)‖ := by nlinarith [abs_nonneg (a₀ - 2)]
    have hrpow_k : |s.im| ^ (1 / 2 - a₀) ≤ ‖s - (a₀ - 1 : ℝ)‖ ^ k :=
      (Real.rpow_le_rpow_of_exponent_le ht1 hk).trans
        ((Real.rpow_natCast _ k).le.trans (pow_le_pow_left₀ (abs_nonneg _) him_le k))
    have hs_ne1 : s ≠ 1 := fun h ↦ by have := congrArg re h; simp [hs] at this; linarith
    rw [riemannZeta₁_eq_sub_mul hs_ne1, norm_div, norm_mul, norm_pow,
      div_le_iff₀ (by positivity : 0 < ‖s - (a₀ - 1 : ℝ)‖ ^ (k + 1)), pow_succ']
    calc ‖s - 1‖ * ‖riemannZeta s‖
        ≤ ((1 + |a₀ - 2|) * ‖s - (a₀ - 1 : ℝ)‖) * (C * ‖s - (a₀ - 1 : ℝ)‖ ^ k) :=
          mul_le_mul hs1_le ((hhigh s hs ht.le).trans
            (mul_le_mul_of_nonneg_left hrpow_k hC.le)) (norm_nonneg _) (by positivity)
      _ = (1 + |a₀ - 2|) * C * (‖s - (a₀ - 1 : ℝ)‖ * ‖s - (a₀ - 1 : ℝ)‖ ^ k) := by ring

/-- Uniform bound on `riemannZeta₁ z / (z - (a₀ - 1)) ^ (k + 1)` along a right line `Re z = b₀ ≥ 2`
when `a₀ ≤ -2`. -/
private theorem norm_riemannZeta₁_div_pow_le_on_right_line {a₀ b₀ : ℝ} (ha₀ : a₀ ≤ -2)
    (hb₀ : 2 ≤ b₀) (k : ℕ) {z : ℂ} (hz : z.re = b₀) :
    ‖riemannZeta₁ z / (z - (a₀ - 1 : ℝ)) ^ (k + 1)‖ ≤ (riemannZeta 2).re := by
  have hz1 : z ≠ 1 := fun h ↦ by have := congrArg re h; simp [hz] at this; linarith
  have hb1 : 1 ≤ ‖z - (a₀ - 1 : ℝ)‖ := by
    have hre : 1 ≤ (z - (a₀ - 1 : ℝ)).re := by simp [hz]; linarith
    exact hre.trans ((le_abs_self _).trans (abs_re_le_norm _))
  have hz1_le : ‖z - 1‖ ≤ ‖z - (a₀ - 1 : ℝ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    refine Real.sqrt_le_sqrt ?_
    simp only [normSq_apply, sub_re, one_re, ofReal_re, sub_im, one_im, ofReal_im, sub_zero, hz]
    nlinarith
  have hpos2 : 0 ≤ (riemannZeta 2).re := (riemannZeta_re_pos_of_one_lt one_lt_two).le
  rw [riemannZeta₁_eq_sub_mul hz1, norm_div, norm_mul, norm_pow,
    div_le_iff₀ (by positivity : 0 < ‖z - (a₀ - 1 : ℝ)‖ ^ (k + 1)), pow_succ']
  calc ‖z - 1‖ * ‖riemannZeta z‖
      ≤ ‖z - (a₀ - 1 : ℝ)‖ * (riemannZeta 2).re :=
        mul_le_mul hz1_le (norm_riemannZeta_le_of_re_ge one_lt_two (by linarith))
          (norm_nonneg _) (by positivity)
    _ = (riemannZeta 2).re * ‖z - (a₀ - 1 : ℝ)‖ * 1 := by ring
    _ ≤ (riemannZeta 2).re * ‖z - (a₀ - 1 : ℝ)‖ * ‖z - (a₀ - 1 : ℝ)‖ ^ k :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hb1) (mul_nonneg hpos2 (norm_nonneg _))
    _ = (riemannZeta 2).re * (‖z - (a₀ - 1 : ℝ)‖ * ‖z - (a₀ - 1 : ℝ)‖ ^ k) := by ring

/-- Interior double-exponential growth condition for `PhragmenLindelof.vertical_strip` from
`exists_norm_riemannZeta₁_le_exp_mul_log`. -/
private theorem exists_isBigO_riemannZeta₁_div_pow_exp_exp {a₀ b₀ : ℝ} (hab : a₀ < b₀) (m : ℕ) :
    ∃ c < π / (b₀ - a₀), ∃ B,
      (fun z : ℂ ↦ riemannZeta₁ z / (z - (a₀ - 1 : ℝ)) ^ m)
        =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a₀ b₀)]
          fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨C₁, hC₁, hZ₁⟩ := exists_norm_riemannZeta₁_le_exp_mul_log
  set c := min 1 (π / (2 * (b₀ - a₀)))
  have hc_pos : 0 < c := lt_min one_pos (div_pos Real.pi_pos (by linarith))
  have hc_lt : c < π / (b₀ - a₀) := (min_le_right _ _).trans_lt
    (div_lt_div_of_pos_left Real.pi_pos (by linarith) (by linarith))
  set R₀ := max |a₀| |b₀|
  set B := C₁ * (2 * (2 + R₀) ^ 2 + 8 / c ^ 2)
  refine ⟨c, hc_lt, B, IsBigO.of_bound 1 ?_⟩
  rw [eventually_inf_principal]
  refine Eventually.of_forall fun z (hz : a₀ < z.re ∧ z.re < b₀) ↦ ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  have hbase : 1 ≤ ‖z - (a₀ - 1 : ℝ)‖ := by
    have : 1 ≤ (z - (a₀ - 1 : ℝ)).re := by simp; linarith [hz.1]
    exact this.trans ((le_abs_self _).trans (abs_re_le_norm _))
  have hg_le : ‖riemannZeta₁ z / (z - (a₀ - 1 : ℝ)) ^ m‖ ≤ ‖riemannZeta₁ z‖ := by
    rw [norm_div, norm_pow]; exact div_le_self (norm_nonneg _) (one_le_pow₀ hbase)
  refine (hg_le.trans (hZ₁ z)).trans (Real.exp_le_exp.mpr ?_)
  have hz_norm : ‖z‖ ≤ R₀ + |z.im| := by
    refine (norm_le_abs_re_add_abs_im z).trans ?_
    gcongr; exact abs_le_max_abs_abs hz.1.le hz.2.le
  have hW_sq : (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤ (2 + R₀ + |z.im|) ^ 2 := by
    have hlog_le : Real.log (2 + ‖z‖) ≤ 2 + ‖z‖ :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    nlinarith [norm_nonneg z, Real.log_nonneg (by linarith [norm_nonneg z] : 1 ≤ 2 + ‖z‖)]
  have hu : c * |z.im| / 2 ≤ Real.exp (c * |z.im| / 2) := by
    linarith [Real.add_one_le_exp (c * |z.im| / 2)]
  have hquad : (c * |z.im| / 2) ^ 2 ≤ Real.exp (c * |z.im|) :=
    (pow_le_pow_left₀ (by positivity) hu 2).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have him_sq : |z.im| ^ 2 ≤ 4 / c ^ 2 * Real.exp (c * |z.im|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hc_pos)]
    linarith
  have hexp1 : 1 ≤ Real.exp (c * |z.im|) :=
    Real.one_le_exp (mul_nonneg hc_pos.le (abs_nonneg _))
  have hsq_bound : (2 + R₀ + |z.im|) ^ 2 ≤
      (2 * (2 + R₀) ^ 2 + 8 / c ^ 2) * Real.exp (c * |z.im|) := by
    have hdiff_sq : 0 ≤ (2 + R₀ - |z.im|) ^ 2 := sq_nonneg _
    have h1 : (2 + R₀) ^ 2 ≤ (2 + R₀) ^ 2 * Real.exp (c * |z.im|) :=
      le_mul_of_one_le_right (sq_nonneg _) hexp1
    have hexpand : (2 * (2 + R₀) ^ 2 + 8 / c ^ 2) * Real.exp (c * |z.im|) =
        2 * ((2 + R₀) ^ 2 * Real.exp (c * |z.im|)) +
          2 * (4 / c ^ 2 * Real.exp (c * |z.im|)) := by ring
    linarith
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hW_sq hC₁.le).trans
    (by simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left hsq_bound hC₁.le)

/-- **Polynomial vertical-strip bound for `riemannZeta₁`.** On every vertical strip
`a ≤ Re s ≤ b`, `riemannZeta₁ s` is bounded by `C * (1 + |Im s|) ^ B`. -/
theorem exists_norm_riemannZeta₁_le_rpow (a b : ℝ) :
    ∃ C > 0, ∃ B ≥ (0 : ℝ), ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖riemannZeta₁ s‖ ≤ C * (1 + |s.im|) ^ B := by
  set a₀ := min a (-2)
  set b₀ := max b 2
  have ha₀ : a₀ ≤ -2 := min_le_right _ _
  have hb₀ : 2 ≤ b₀ := le_max_right _ _
  set k : ℕ := ⌈1 / 2 - a₀⌉₊
  set g : ℂ → ℂ := fun z ↦ riemannZeta₁ z / (z - (a₀ - 1 : ℝ)) ^ (k + 1)
  obtain ⟨M_left, hleft⟩ := exists_norm_riemannZeta₁_div_pow_le_on_left_line ha₀ (Nat.le_ceil _)
  have hbase_ge {z : ℂ} (hz : a₀ ≤ z.re) : 1 ≤ ‖z - (a₀ - 1 : ℝ)‖ := by
    have hre : 1 ≤ (z - (a₀ - 1 : ℝ)).re := by simp; linarith
    exact hre.trans ((le_abs_self _).trans (abs_re_le_norm _))
  have hdiff : DiffContOnCl ℂ g (re ⁻¹' Ioo a₀ b₀) := by
    have hd : DifferentiableOn ℂ g {z : ℂ | a₀ - 1 / 2 < z.re} :=
      DifferentiableOn.div differentiable_riemannZeta₁.differentiableOn
        ((differentiableOn_id.sub_const _).pow _) fun z (hz : a₀ - 1 / 2 < z.re) ↦
          pow_ne_zero _ fun h0 ↦ by
            have hre := congrArg re h0; simp only [sub_re, ofReal_re, zero_re] at hre; linarith
    refine ⟨hd.mono fun z (hz : a₀ < z.re ∧ z.re < b₀) ↦ by simp only [mem_ofPred_eq]; linarith,
      hd.continuousOn.mono ((closure_minimal (preimage_mono Ioo_subset_Icc_self)
        (isClosed_Icc.preimage continuous_re)).trans
        fun z (hz : a₀ ≤ z.re ∧ z.re ≤ b₀) ↦ by simp only [mem_ofPred_eq]; linarith)⟩
  set M := max (max M_left (riemannZeta 2).re) 1
  have hM_pos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hwidth_pos : 0 < b₀ - a₀ + 1 := by linarith
  refine ⟨M * (b₀ - a₀ + 1) ^ (k + 1), by positivity, ((k + 1 : ℕ) : ℝ), Nat.cast_nonneg _,
    fun s ha_s hs_b ↦ ?_⟩
  have hs_a₀ : a₀ ≤ s.re := (min_le_left _ _).trans ha_s
  have hg_bound : ‖g s‖ ≤ M := PhragmenLindelof.vertical_strip hdiff
    (exists_isBigO_riemannZeta₁_div_pow_exp_exp (by linarith) (k + 1))
    (fun z hz ↦ (hleft z hz).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun z hz ↦ (norm_riemannZeta₁_div_pow_le_on_right_line ha₀ hb₀ k hz).trans
      ((le_max_right _ _).trans (le_max_left _ _)))
    hs_a₀ (hs_b.trans (le_max_left _ _))
  have hpow_ne : (s - (a₀ - 1 : ℝ)) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ (norm_pos_iff.mp (zero_lt_one.trans_le (hbase_ge hs_a₀)))
  have hnorm_sub : ‖s - (a₀ - 1 : ℝ)‖ ≤ (b₀ - a₀ + 1) * (1 + |s.im|) := by
    have hre_sub : |(s - (a₀ - 1 : ℝ)).re| ≤ b₀ - a₀ + 1 := by
      rw [sub_re, ofReal_re, abs_of_nonneg (by linarith)]
      linarith [hs_b.trans (le_max_left b 2)]
    calc ‖s - (a₀ - 1 : ℝ)‖ ≤ |(s - (a₀ - 1 : ℝ)).re| + |(s - (a₀ - 1 : ℝ)).im| :=
          norm_le_abs_re_add_abs_im _
      _ ≤ (b₀ - a₀ + 1) + |s.im| := by simpa using add_le_add_left hre_sub |s.im|
      _ ≤ (b₀ - a₀ + 1) * (1 + |s.im|) := by nlinarith [abs_nonneg s.im]
  rw [(div_mul_cancel₀ (riemannZeta₁ s) hpow_ne).symm, norm_mul, norm_pow, Real.rpow_natCast]
  calc ‖g s‖ * ‖s - (a₀ - 1 : ℝ)‖ ^ (k + 1)
      ≤ M * ((b₀ - a₀ + 1) * (1 + |s.im|)) ^ (k + 1) :=
        mul_le_mul hg_bound (pow_le_pow_left₀ (norm_nonneg _) hnorm_sub _) (by positivity)
          hM_pos.le
    _ = M * (b₀ - a₀ + 1) ^ (k + 1) * (1 + |s.im|) ^ (k + 1) := by rw [mul_pow]; ring

/-- Uniform polynomial bound for `riemannZeta₁` on discs `closedBall s₀ R` whose centres lie on a
vertical line `Re s₀ = σ₀`. -/
theorem exists_norm_riemannZeta₁_closedBall_le_rpow (σ₀ R : ℝ) :
    ∃ C > 0, ∃ B ≥ (0 : ℝ), ∀ s₀ w : ℂ, s₀.re = σ₀ → w ∈ closedBall s₀ R →
      ‖riemannZeta₁ w‖ ≤ C * (|s₀.im| + 2) ^ B := by
  rcases lt_or_ge R 0 with hR | hR
  · refine ⟨1, one_pos, 0, le_rfl, fun s₀ w _ hw ↦ ?_⟩
    exact absurd ((mem_closedBall.mp hw).trans_lt hR) (not_lt.mpr dist_nonneg)
  · obtain ⟨C, hC, B, hB, hstrip⟩ := exists_norm_riemannZeta₁_le_rpow (σ₀ - R) (σ₀ + R)
    refine ⟨C * (1 + R) ^ B, by positivity, B, hB, fun s₀ w hs₀ hw ↦ ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hw
    have hre_diff : |w.re - σ₀| ≤ R := by
      simpa [hs₀] using (abs_re_le_norm (w - s₀)).trans hw
    have him_diff : |w.im - s₀.im| ≤ R := by
      simpa using (abs_im_le_norm (w - s₀)).trans hw
    have hw_re : σ₀ - R ≤ w.re ∧ w.re ≤ σ₀ + R :=
      ⟨by linarith [(abs_le.mp hre_diff).1], by linarith [(abs_le.mp hre_diff).2]⟩
    have him_bound : 1 + |w.im| ≤ (1 + R) * (|s₀.im| + 2) := by
      have : |w.im| ≤ |s₀.im| + R := by
        have := abs_add_le (w.im - s₀.im) s₀.im
        rw [sub_add_cancel] at this
        linarith
      nlinarith [abs_nonneg s₀.im]
    calc ‖riemannZeta₁ w‖ ≤ C * (1 + |w.im|) ^ B := hstrip w hw_re.1 hw_re.2
      _ ≤ C * ((1 + R) * (|s₀.im| + 2)) ^ B := by gcongr
      _ = C * (1 + R) ^ B * (|s₀.im| + 2) ^ B := by
          rw [Real.mul_rpow (by positivity) (by positivity), mul_assoc]

/-- The entire regularized zeta function `riemannZeta₁` has polynomial vertical-strip growth. -/
theorem hasVerticalStripGrowth_riemannZeta₁ : HasVerticalStripGrowth riemannZeta₁ := by
  rw [hasVerticalStripGrowth_iff]
  intro a b _
  obtain ⟨C, hC, B, hB, hbound⟩ := exists_norm_riemannZeta₁_le_rpow a b
  exact ⟨C, hC, B, hB, 0, le_rfl, fun s hs _ ↦ hbound s hs.1 hs.2⟩

/-- The Riemann zeta function has polynomial vertical-strip growth. -/
theorem hasVerticalStripGrowth_riemannZeta : HasVerticalStripGrowth riemannZeta := by
  rw [hasVerticalStripGrowth_iff]
  intro a b _
  obtain ⟨C, hC, B, hB, hbound⟩ := exists_norm_riemannZeta₁_le_rpow a b
  refine ⟨C, hC, B, hB, 1, zero_le_one, fun s hs ht ↦ ?_⟩
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at ht
  have hnorm1 : 1 ≤ ‖s - 1‖ := ht.trans (by simpa using abs_im_le_norm (s - 1))
  rw [riemannZeta_eq_inv_sub_mul hs1, norm_mul, norm_inv, inv_mul_eq_div]
  exact (div_le_self (norm_nonneg _) hnorm1).trans (hbound s hs.1 hs.2)

end TauCeti

/-! ### Example

On `2 ≤ Re s`, `riemannZeta s` is pinched between `((riemannZeta 2).re)⁻¹` and `(riemannZeta 2).re`,
while `riemannZeta₁ 1 = 1` clears the simple pole at `1` without creating an artificial zero
(unlike the raw product `(1 - 1) * riemannZeta 1 = 0`). -/

example {s : ℂ} (hs : 2 ≤ s.re) :
    ((riemannZeta 2).re)⁻¹ ≤ ‖riemannZeta s‖ ∧
      ‖riemannZeta s‖ ≤ (riemannZeta 2).re ∧
      riemannZeta₁ 1 = 1 :=
  ⟨by simpa using TauCeti.inv_riemannZeta_re_le_norm_riemannZeta one_lt_two hs,
   by simpa using TauCeti.norm_riemannZeta_le_of_re_ge one_lt_two hs,
   riemannZeta₁_one⟩
