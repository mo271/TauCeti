/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Star
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Higher-order Sobolev–Morrey supremum inequality on star-shaped domains

Let `Ω` be a bounded open subset of a finite-dimensional real normed space `E` of dimension `n`
that is star-convex with respect to every point of an open ball `ball x₀ ρ` of positive radius `ρ`,
with `diam Ω ≤ γ * ρ`. Let `μ` be an additive Haar measure on `E`, `1 ≤ p < ∞`, and `k : ℕ`
satisfy the supercritical condition `n < k * p` or `p = 1 ∧ n ≤ k`. This file proves the classical
diameter-weighted supremum estimate for any `Cᵏ` function `f : E → F` into a Banach space `F`:

`‖f x‖ₑ ≤ C(n, k, p, γ, μ(B(0, 1))) * ∑_{j ≤ k} (diam Ω) ^ (j - n / p) * ‖Dʲ f‖_{Lᵖ(Ω)}`

at every `x ∈ Ω`, with no integrability assumptions on `f` or its derivatives.

## Method

For `x ∈ Ω` and `y ∈ ball x₀ ρ`, the segment `[y, x]` lies in `Ω`, so Taylor's formula with
integral remainder (`map_add_eq_sum_add_integral_iteratedFDeriv`) expresses `f x` in terms of
`Dʲ f y` (`j < k`) and a weighted integral of `Dᵏ f` along the segment. Averaging over
`y ∈ ball x₀ ρ` controls the lower-order terms by Hölder's inequality and turns the remainder into
an order-`k` Riesz potential via `TauCeti.setLIntegral_closedBall_lintegral_segment_rpow_le`, which
is bounded pointwise by `TauCeti.setLIntegral_mul_enorm_sub_rpow_sub_finrank_le` (`p > 1`) and
`TauCeti.setLIntegral_mul_enorm_sub_rpow_sub_finrank_le_of_le` (`p = 1`).

## Main declarations

* `TauCeti.starConvexSupConst`: the explicit constant `C(n, k, p, γ, vB)` for the diameter-weighted
  supremum estimate, valid for all `1 ≤ p ≤ ∞`.
* `TauCeti.starConvexSupConst_nonneg`: nonnegativity of `TauCeti.starConvexSupConst`.
* `TauCeti.enorm_le_sum_eLpNorm_of_contDiffOn_of_forall_starConvex`: the classical `Cᵏ` pointwise
  estimate on a bounded star-shaped domain, for arbitrary finite-dimensional normed spaces `E` and
  Banach codomains `F`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Chapter 4, Lemmas 4.3.1 and 4.3.4.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12.
-/

public section

noncomputable section

open Bornology MeasureTheory Metric Module Set
open scoped ContDiff ENNReal NNReal

namespace TauCeti

/-! ### Explicit constant for the star-convex supremum estimate -/

/-- The finite-exponent constant in the diameter-weighted supremum estimate on a bounded domain
of dimension `n` star-convex with respect to a ball of radius `≥ diam Ω / γ`, for unit-ball
measure `vB`. -/
private def starConvexSupConstFin (n k : ℕ) (p : ℝ≥0∞) (γ vB : ℝ) : ℝ :=
  if n = 0 then vB ^ (-1 / p.toReal)
  else
    let γ' := max γ 1
    let c₁ := vB ^ (-1 / p.toReal) * γ' ^ ((n : ℝ) / p.toReal)
    let rieszFactor :=
      if p = 1 then 1
      else ((n : ℝ) * vB * (p.toReal - 1) / ((k : ℝ) * p.toReal - n)) ^ (1 - 1 / p.toReal)
    let c₂ := (((k - 1).factorial : ℝ) * n * vB)⁻¹ * γ' ^ n * rieszFactor
    max c₁ c₂

/-- Explicit constant `C(n, k, p, γ, vB)` in the diameter-weighted supremum estimate on a bounded
domain of dimension `n` star-convex with respect to a ball of radius `≥ diam Ω / γ`, where
`vB = μ(B(0, 1))`. -/
def starConvexSupConst (n k : ℕ) (p : ℝ≥0∞) (γ vB : ℝ) : ℝ :=
  if p = ⊤ then
    if n = 0 then 1
    else starConvexSupConstFin n k (n + 1 : ℕ) γ vB * vB ^ (1 / ((n + 1 : ℕ) : ℝ))
  else starConvexSupConstFin n k p γ vB

private theorem starConvexSupConstFin_nonneg (n k : ℕ) (p : ℝ≥0∞) (γ : ℝ) {vB : ℝ}
    (hvB : 0 ≤ vB) : 0 ≤ starConvexSupConstFin n k p γ vB := by
  unfold starConvexSupConstFin
  split_ifs
  · exact Real.rpow_nonneg hvB _
  · exact le_max_of_le_left (mul_nonneg (Real.rpow_nonneg hvB _)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right γ 1)) _))
  · exact le_max_of_le_left (mul_nonneg (Real.rpow_nonneg hvB _)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right γ 1)) _))

/-- The explicit supremum constant `TauCeti.starConvexSupConst` is nonnegative whenever
`0 ≤ vB`. -/
theorem starConvexSupConst_nonneg (n k : ℕ) (p : ℝ≥0∞) (γ : ℝ) {vB : ℝ} (hvB : 0 ≤ vB) :
    0 ≤ starConvexSupConst n k p γ vB := by
  unfold starConvexSupConst
  split_ifs
  · exact zero_le_one
  · exact mul_nonneg (starConvexSupConstFin_nonneg n k (n + 1 : ℕ) γ hvB) (Real.rpow_nonneg hvB _)
  · exact starConvexSupConstFin_nonneg n k p γ hvB

/-- In dimension zero at `p = ∞`, `TauCeti.starConvexSupConst` equals `1`. -/
@[simp]
theorem starConvexSupConst_zero_top (k : ℕ) (γ vB : ℝ) :
    starConvexSupConst 0 k ⊤ γ vB = 1 := by
  simp [starConvexSupConst]

/-- In positive dimension `n ≠ 0`, `TauCeti.starConvexSupConst` at `p = ∞` is obtained by lowering
the exponent to `n + 1`. -/
theorem starConvexSupConst_top_of_ne_zero {n : ℕ} (hn : n ≠ 0) (k : ℕ) (γ vB : ℝ) :
    starConvexSupConst n k ⊤ γ vB =
      starConvexSupConst n k (n + 1 : ℕ) γ vB * vB ^ (1 / ((n + 1 : ℕ) : ℝ)) := by
  simp [starConvexSupConst, hn, ENNReal.natCast_ne_top]

/-! ### Classical `Cᵏ` pointwise estimate on bounded star-shaped domains -/

section ClassicalPointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise Taylor bound in `ℝ≥0∞` for a `C^{m+1}` function on a bounded open set `Ω`
star-convex with respect to `ball x₀ ρ`: at `x ∈ Ω` and `y ∈ ball x₀ ρ`, `‖f x‖ₑ` is controlled by
the lower-order derivatives at `y` and a weighted segment integral of `D^{m+1} f`. -/
private theorem enorm_le_sum_add_segment_of_contDiffOn [CompleteSpace F] {Ω : Set E} (hΩ : IsOpen Ω)
    (hb : IsBounded Ω) {x₀ : E} {ρ : ℝ} (hstar : ∀ z ∈ ball x₀ ρ, StarConvex ℝ z Ω)
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ (m + 1) f Ω) {x y : E} (hx : x ∈ Ω)
    (hy : y ∈ ball x₀ ρ) :
    ‖f x‖ₑ ≤
      ∑ j ∈ Finset.range (m + 1),
        ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * diam Ω ^ j) * ‖iteratedFDeriv ℝ j f y‖ₑ +
      ENNReal.ofReal (m.factorial : ℝ)⁻¹ *
        ((∫⁻ s in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (s ^ (((m + 1 : ℕ) : ℝ) - 1)) *
            Ω.indicator (fun z => ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ) (x + s • (y - x))) *
          ‖x - y‖ₑ ^ ((m + 1 : ℕ) : ℝ)) := by
  have hyΩ : y ∈ Ω := (hstar y hy).mem ⟨x, hx⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ Ω := fun t ht =>
    (hstar y hy).add_smul_sub_mem hx ht.1 ht.2
  -- Expand `f x` about `y` by Taylor's theorem and reparametrize the remainder via `s = 1 - t`.
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := y) (y := x - y) (n := m)
    fun t ht => hf.contDiffAt (hΩ.mem_nhds (hseg t ht))
  rw [add_sub_cancel] at htaylor
  have hsub : ∫ t in (0 : ℝ)..1,
      (1 - t) ^ m • iteratedFDeriv ℝ (m + 1) f (y + t • (x - y)) (fun _ => x - y) =
      ∫ s in (0 : ℝ)..1,
        s ^ m • iteratedFDeriv ℝ (m + 1) f (x + s • (y - x)) (fun _ => x - y) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) (d := 1)
      (fun s => s ^ m • iteratedFDeriv ℝ (m + 1) f (x + s • (y - x)) (fun _ => x - y))
    simp only [sub_zero, sub_self] at h
    refine (intervalIntegral.integral_congr fun t _ => ?_).trans h
    have hpt : y + t • (x - y) = x + (1 - t) • (y - x) := by module
    rw [hpt]
  rw [htaylor, hsub]
  refine (eNorm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- Bound the Taylor polynomial terms using `‖x - y‖ ≤ diam Ω`.
    refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have hxy : ‖x - y‖ ≤ diam Ω := dist_eq_norm x y ▸ dist_le_diam_of_mem hb hx hyΩ
    rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (by positivity),
      ← ofReal_norm (iteratedFDeriv ℝ j f y), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (j.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ j f y (fun _ => x - y)‖
        ≤ (j.factorial : ℝ)⁻¹ * (‖iteratedFDeriv ℝ j f y‖ * ‖x - y‖ ^ j) := by
          gcongr
          simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            (iteratedFDeriv ℝ j f y).le_opNorm (fun _ => x - y)
      _ = (j.factorial : ℝ)⁻¹ * ‖x - y‖ ^ j * ‖iteratedFDeriv ℝ j f y‖ := by ring
      _ ≤ (j.factorial : ℝ)⁻¹ * diam Ω ^ j * ‖iteratedFDeriv ℝ j f y‖ := by gcongr
  · -- Bound the integral remainder term by pulling `‖x - y‖ ^ (m + 1)` outside the integral.
    rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (by positivity),
      ENNReal.ofReal_mul (by positivity), ofReal_norm, intervalIntegral.integral_of_le zero_le_one]
    gcongr
    refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
    rw [← lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (Nat.cast_nonneg _) eNorm_ne_top)]
    refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
    have hmem : x + s • (y - x) ∈ Ω := by
      have : x + s • (y - x) = y + (1 - s) • (x - y) := by module
      rw [this]
      exact hseg (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [indicator_of_mem hmem, ← ofReal_norm, norm_smul,
      Real.norm_of_nonneg (pow_nonneg hs.1.le m), ENNReal.ofReal_mul (pow_nonneg hs.1.le m)]
    have hspow : s ^ m = s ^ (((m + 1 : ℕ) : ℝ) - 1) := by
      rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast]
    have hnorm : ENNReal.ofReal ‖iteratedFDeriv ℝ (m + 1) f (x + s • (y - x)) (fun _ => x - y)‖ ≤
        ‖iteratedFDeriv ℝ (m + 1) f (x + s • (y - x))‖ₑ * ‖x - y‖ₑ ^ ((m + 1 : ℕ) : ℝ) := by
      rw [ENNReal.rpow_natCast, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ (m + 1) f (x + s • (y - x))).le_opNorm (fun _ => x - y)
    rw [hspow, mul_assoc]
    gcongr

end ClassicalPointwise

section Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Algebraic scaling bound for the lower-order Taylor prefactor under `D ≤ γ * ρ`. -/
private theorem inv_factorial_mul_rpow_le (j n : ℕ) {D ρ γ vB q : ℝ} (hD : 0 < D) (hρ : 0 < ρ)
    (hvB : 0 < vB) (hq : 0 < q) (hγ : D ≤ γ * ρ) :
    (j.factorial : ℝ)⁻¹ * D ^ j * (ρ ^ n * vB) ^ (-1 / q) ≤
      vB ^ (-1 / q) * (max γ 1) ^ ((n : ℝ) / q) * D ^ ((j : ℝ) - n / q) := by
  have hfac : (j.factorial : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos j)
  have hDγ : D / ρ ≤ max γ 1 :=
    (div_le_iff₀ hρ).2 (hγ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le))
  have hexp : (n : ℝ) * (-1 / q) = -((n : ℝ) / q) := by ring
  have hscale : D ^ j * (ρ ^ n * vB) ^ (-1 / q) =
      vB ^ (-1 / q) * (D / ρ) ^ ((n : ℝ) / q) * D ^ ((j : ℝ) - n / q) := by
    rw [Real.mul_rpow (pow_nonneg hρ.le _) hvB.le, ← Real.rpow_natCast ρ n, ← Real.rpow_mul hρ.le,
      Real.div_rpow hD.le hρ.le, ← Real.rpow_natCast D j, div_eq_mul_inv (D ^ ((n : ℝ) / q)),
      ← Real.rpow_neg hρ.le, hexp]
    calc D ^ (j : ℝ) * (ρ ^ (-((n : ℝ) / q)) * vB ^ (-1 / q))
        = vB ^ (-1 / q) * ρ ^ (-((n : ℝ) / q)) * D ^ (j : ℝ) := by ring
      _ = vB ^ (-1 / q) * ρ ^ (-((n : ℝ) / q)) *
            (D ^ ((n : ℝ) / q) * D ^ ((j : ℝ) - n / q)) := by
          rw [← Real.rpow_add hD]
          congr 2
          ring
      _ = _ := by ring
  calc (j.factorial : ℝ)⁻¹ * D ^ j * (ρ ^ n * vB) ^ (-1 / q)
      ≤ 1 * (D ^ j * (ρ ^ n * vB) ^ (-1 / q)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = vB ^ (-1 / q) * (D / ρ) ^ ((n : ℝ) / q) * D ^ ((j : ℝ) - n / q) := by rw [one_mul, hscale]
    _ ≤ _ := by gcongr

/-- Lower-order derivative term bound after averaging over `ball x₀ ρ`. -/
private theorem inv_ball_mul_setLIntegral_iteratedFDeriv_le [Nontrivial E] {Ω : Set E}
    (hΩ : IsOpen Ω) (hb : IsBounded Ω) {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ)
    (hBΩ : ball x₀ ρ ⊆ Ω) (hγ : diam Ω ≤ γ * ρ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {k j : ℕ} (hjk : j ≤ k) {f : E → F} (hf : ContDiffOn ℝ k f Ω) :
    (μ (ball x₀ ρ))⁻¹ *
        (ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * diam Ω ^ j) *
          ∫⁻ y in ball x₀ ρ, ‖iteratedFDeriv ℝ j f y‖ₑ ∂μ) ≤
      ENNReal.ofReal (μ.real (ball (0 : E) 1) ^ (-1 / p.toReal) *
          (max γ 1) ^ ((finrank ℝ E : ℝ) / p.toReal)) *
        (ENNReal.ofReal (diam Ω ^ ((j : ℝ) - finrank ℝ E / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω)) := by
  set n := finrank ℝ E
  set vB := μ.real (ball (0 : E) 1) with hvB_def
  set D := diam Ω
  have hD : 0 < D :=
    lt_of_lt_of_le (by linarith : 0 < 2 * ρ) (Metric.diam_ball_eq x₀ hρ.le ▸ diam_mono hBΩ hb)
  have hvB : 0 < vB := Metric.measureReal_ball_pos μ 0 one_pos
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  have hcont : ContinuousOn (iteratedFDeriv ℝ j f) (ball x₀ ρ) :=
    (ContinuousOn.continuousOn_iteratedFDeriv hf hΩ (by exact_mod_cast hjk)).mono hBΩ
  have hBmeas : μ (ball x₀ ρ) = ENNReal.ofReal (ρ ^ n * vB) := by
    rw [Measure.addHaar_ball_of_pos μ x₀ hρ, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← hvB_def, ← ENNReal.ofReal_mul (pow_nonneg hρ.le _)]
  have hL1 : ∫⁻ y in ball x₀ ρ, ‖iteratedFDeriv ℝ j f y‖ₑ ∂μ ≤
      eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω) *
        (μ (ball x₀ ρ)) ^ (1 - 1 / p.toReal) := by
    rw [← eLpNorm_one_eq_lintegral_eNorm (hcont.aestronglyMeasurable measurableSet_ball)]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : (1 : ℝ≥0∞) ≤ p)
      (hcont.aestronglyMeasurable measurableSet_ball)).trans ?_
    simp only [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one]
    gcongr
  have hpowB : (μ (ball x₀ ρ))⁻¹ * (μ (ball x₀ ρ)) ^ (1 - 1 / p.toReal) =
      ENNReal.ofReal ((ρ ^ n * vB) ^ (-1 / p.toReal)) := by
    rw [← ENNReal.rpow_neg_one,
      ← ENNReal.rpow_add _ _ (measure_ball_pos μ x₀ hρ).ne' measure_ball_lt_top.ne, hBmeas,
      ENNReal.ofReal_rpow_of_pos (mul_pos (pow_pos hρ _) hvB)]
    congr 2
    ring
  have hconst := inv_factorial_mul_rpow_le j n hD hρ hvB hp_pos hγ
  calc (μ (ball x₀ ρ))⁻¹ *
        (ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * D ^ j) *
          ∫⁻ y in ball x₀ ρ, ‖iteratedFDeriv ℝ j f y‖ₑ ∂μ)
      ≤ (μ (ball x₀ ρ))⁻¹ *
        (ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * D ^ j) *
          (eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω) *
            (μ (ball x₀ ρ)) ^ (1 - 1 / p.toReal))) := by gcongr
    _ = ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * D ^ j) *
        ((μ (ball x₀ ρ))⁻¹ * (μ (ball x₀ ρ)) ^ (1 - 1 / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω) := by ring
    _ = ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * D ^ j * (ρ ^ n * vB) ^ (-1 / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω) := by
        rw [hpowB, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (vB ^ (-1 / p.toReal) * (max γ 1) ^ ((n : ℝ) / p.toReal) *
          D ^ ((j : ℝ) - n / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω) := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hvB.le _)
          (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)), mul_assoc]

/-- Pointwise order-`m + 1` Riesz potential bound for the top derivative `D^{m+1} f` on
`Ω ⊆ closedBall x D`. -/
private theorem setLIntegral_iteratedFDeriv_riesz_le [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    {x : E} {D : ℝ} (hΩD : Ω ⊆ closedBall x D) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {m : ℕ}
    (hkp : (finrank ℝ E : ℝ≥0∞) < ((m + 1 : ℕ) : ℝ≥0∞) * p ∨ (p = 1 ∧ finrank ℝ E ≤ m + 1))
    {f : E → F} (hf : ContDiffOn ℝ (m + 1) f Ω) :
    ∫⁻ z in Ω, ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ *
        ‖x - z‖ₑ ^ (((m + 1 : ℕ) : ℝ) - finrank ℝ E) ∂μ ≤
      ENNReal.ofReal (if p = 1 then 1 else ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
          (p.toReal - 1) / (((m + 1 : ℕ) : ℝ) * p.toReal - finrank ℝ E)) ^ (1 - 1 / p.toReal)) *
        (ENNReal.ofReal (D ^ (((m + 1 : ℕ) : ℝ) - finrank ℝ E / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ (m + 1) f) p (μ.restrict Ω)) := by
  set n := finrank ℝ E
  set vB := μ.real (ball (0 : E) 1)
  have hn : 0 < n := finrank_pos
  have hvB : 0 < vB := Metric.measureReal_ball_pos μ 0 one_pos
  have hcont := ContinuousOn.continuousOn_iteratedFDeriv hf hΩ le_rfl
  by_cases hp1 : p = 1
  · subst hp1
    have hnk : (n : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      rcases hkp with h | ⟨_, h⟩
      · exact_mod_cast (by simpa only [mul_one, Nat.cast_lt] using h : n < m + 1).le
      · exact_mod_cast h
    simp only [ite_true, ENNReal.ofReal_one, one_mul, ENNReal.toReal_one, div_one]
    rw [eLpNorm_one_eq_lintegral_eNorm (hcont.aestronglyMeasurable hΩ.measurableSet)]
    exact setLIntegral_mul_enorm_sub_rpow_sub_finrank_le_of_le hΩD _ hnk
  · simp only [hp1, ite_false]
    have hp_toReal : (p.toNNReal : ℝ) = p.toReal := by
      rw [← ENNReal.coe_toReal, ENNReal.coe_toNNReal hp]
    have hp_gt1 : (1 : ℝ≥0) < p.toNNReal := by
      have h1lt : (1 : ℝ≥0∞) < p := lt_of_le_of_ne Fact.out (Ne.symm hp1)
      exact_mod_cast (ENNReal.coe_lt_coe.1 (by rwa [ENNReal.coe_toNNReal hp, ENNReal.coe_one]))
    have hkp_lt : (n : ℝ≥0∞) < ((m + 1 : ℕ) : ℝ≥0∞) * p := hkp.resolve_right (fun h => hp1 h.1)
    have hkp_real : (n : ℝ) < ((m + 1 : ℕ) : ℝ) * (p.toNNReal : ℝ) := by
      have h := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top n)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hp)).2 hkp_lt
      rw [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hp_toReal] at h
      exact h
    have hbd := setLIntegral_mul_enorm_sub_rpow_sub_finrank_le (μ := μ) hΩD
      (hcont.eNorm.aemeasurable hΩ.measurableSet) hp_gt1 hkp_real
    have heLp : (∫⁻ z in Ω, ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ ^ (p.toNNReal : ℝ) ∂μ) ^
          (1 / (p.toNNReal : ℝ)) =
        eLpNorm (iteratedFDeriv ℝ (m + 1) f) p (μ.restrict Ω) := by
      have hp_eq : p = (p.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hp).symm
      conv_rhs => rw [hp_eq]
      exact (eLpNorm_nnreal_eq_lintegral (zero_lt_one.trans hp_gt1).ne'
        (hcont.aestronglyMeasurable hΩ.measurableSet)).symm
    have hKnn : 0 ≤ (n : ℝ) * vB * (p.toReal - 1) / (((m + 1 : ℕ) : ℝ) * p.toReal - n) := by
      have hp1' : 1 < p.toReal := hp_toReal ▸ (by exact_mod_cast hp_gt1 : (1 : ℝ) < p.toNNReal)
      have hkp' : (n : ℝ) < ((m + 1 : ℕ) : ℝ) * p.toReal := hp_toReal ▸ hkp_real
      exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    rw [heLp] at hbd
    refine hbd.trans_eq ?_
    rw [hp_toReal, ENNReal.ofReal_mul (Real.rpow_nonneg hKnn _), mul_assoc]

/-- Top-order Taylor remainder bound after averaging over `ball x₀ ρ`, converting the segment
integral to an order-`m + 1` Riesz potential and bounding it in `Lᵖ(Ω)`. -/
private theorem inv_ball_mul_remainder_le [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hb : IsBounded Ω) {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ) (hBΩ : ball x₀ ρ ⊆ Ω)
    (hγ : diam Ω ≤ γ * ρ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {m : ℕ}
    (hkp : (finrank ℝ E : ℝ≥0∞) < ((m + 1 : ℕ) : ℝ≥0∞) * p ∨ (p = 1 ∧ finrank ℝ E ≤ m + 1))
    {f : E → F} (hf : ContDiffOn ℝ (m + 1) f Ω) {x : E} (hx : x ∈ Ω) :
    (μ (ball x₀ ρ))⁻¹ *
        (ENNReal.ofReal (m.factorial : ℝ)⁻¹ *
          ∫⁻ y in ball x₀ ρ,
            (∫⁻ s in Ioc (0 : ℝ) 1,
              ENNReal.ofReal (s ^ (((m + 1 : ℕ) : ℝ) - 1)) *
                Ω.indicator (fun z => ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ) (x + s • (y - x))) *
              ‖x - y‖ₑ ^ ((m + 1 : ℕ) : ℝ) ∂μ) ≤
      ENNReal.ofReal ((((m.factorial : ℝ) * finrank ℝ E * μ.real (ball (0 : E) 1))⁻¹ *
          (max γ 1) ^ finrank ℝ E *
          (if p = 1 then 1 else ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * (p.toReal - 1) /
            (((m + 1 : ℕ) : ℝ) * p.toReal - finrank ℝ E)) ^ (1 - 1 / p.toReal)))) *
        (ENNReal.ofReal (diam Ω ^ (((m + 1 : ℕ) : ℝ) - finrank ℝ E / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ (m + 1) f) p (μ.restrict Ω)) := by
  set n := finrank ℝ E
  set vB := μ.real (ball (0 : E) 1) with hvB_def
  set D := diam Ω
  set g : E → ℝ≥0∞ := Ω.indicator fun z => ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ
  have hn : 0 < n := finrank_pos
  have hvB : 0 < vB := Metric.measureReal_ball_pos μ 0 one_pos
  have hg : Measurable g := by
    classical
    dsimp only [g]
    rw [← piecewise_eq_indicator]
    exact (ContinuousOn.continuousOn_iteratedFDeriv hf hΩ le_rfl).eNorm.measurable_piecewise
      continuousOn_const hΩ.measurableSet
  have hΩD : Ω ⊆ closedBall x D := fun z hz => mem_closedBall.2 (dist_le_diam_of_mem hb hz hx)
  -- Convert the weighted segment integral over `ball x₀ ρ ⊆ closedBall x D` to a Riesz potential.
  have hseg : ∫⁻ y in ball x₀ ρ,
        (∫⁻ s in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (s ^ (((m + 1 : ℕ) : ℝ) - 1)) * g (x + s • (y - x))) *
          ‖x - y‖ₑ ^ ((m + 1 : ℕ) : ℝ) ∂μ ≤
      ENNReal.ofReal (D ^ n / n) *
        ∫⁻ z in Ω, ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ *
          ‖x - z‖ₑ ^ (((m + 1 : ℕ) : ℝ) - n) ∂μ := by
    refine (lintegral_mono_set (hBΩ.trans hΩD)).trans
      ((setLIntegral_closedBall_lintegral_segment_rpow_le hg x D (by positivity)).trans_eq ?_)
    rw [← lintegral_indicator hΩ.measurableSet]
    simp only [g, indicator_mul_left]
    rfl
  -- Combine `μ(ball x₀ ρ)⁻¹`, `(m!)⁻¹`, and `D ^ n / n` using `D / ρ ≤ max γ 1`.
  have hpre : (μ (ball x₀ ρ))⁻¹ *
        (ENNReal.ofReal (m.factorial : ℝ)⁻¹ * ENNReal.ofReal (D ^ n / n)) ≤
      ENNReal.ofReal ((((m.factorial : ℝ) * n * vB)⁻¹ * (max γ 1) ^ n)) := by
    have hBmeas : μ (ball x₀ ρ) = ENNReal.ofReal (ρ ^ n * vB) := by
      rw [Measure.addHaar_ball_of_pos μ x₀ hρ, ← ofReal_measureReal measure_ball_lt_top.ne,
        ← hvB_def, ← ENNReal.ofReal_mul (pow_nonneg hρ.le _)]
    have hDγ : D / ρ ≤ max γ 1 :=
      (div_le_iff₀ hρ).2 (hγ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le))
    rw [hBmeas, ← ENNReal.ofReal_inv_of_pos (mul_pos (pow_pos hρ _) hvB),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : (ρ ^ n * vB)⁻¹ * ((m.factorial : ℝ)⁻¹ * (D ^ n / n)) =
        ((m.factorial : ℝ) * n * vB)⁻¹ * (D / ρ) ^ n := by
      rw [div_pow]
      field_simp
    rw [heq]
    gcongr
  have hriesz := setLIntegral_iteratedFDeriv_riesz_le (μ := μ) hΩ hΩD hp hkp hf
  calc (μ (ball x₀ ρ))⁻¹ *
        (ENNReal.ofReal (m.factorial : ℝ)⁻¹ *
          ∫⁻ y in ball x₀ ρ,
            (∫⁻ s in Ioc (0 : ℝ) 1,
              ENNReal.ofReal (s ^ (((m + 1 : ℕ) : ℝ) - 1)) * g (x + s • (y - x))) *
              ‖x - y‖ₑ ^ ((m + 1 : ℕ) : ℝ) ∂μ)
      ≤ (μ (ball x₀ ρ))⁻¹ *
          (ENNReal.ofReal (m.factorial : ℝ)⁻¹ *
            (ENNReal.ofReal (D ^ n / n) *
              ∫⁻ z in Ω, ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ *
                ‖x - z‖ₑ ^ (((m + 1 : ℕ) : ℝ) - n) ∂μ)) := by gcongr
    _ = ((μ (ball x₀ ρ))⁻¹ * (ENNReal.ofReal (m.factorial : ℝ)⁻¹ * ENNReal.ofReal (D ^ n / n))) *
          ∫⁻ z in Ω, ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ *
            ‖x - z‖ₑ ^ (((m + 1 : ℕ) : ℝ) - n) ∂μ := by ring
    _ ≤ _ := mul_le_mul' hpre hriesz
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- Zero-dimensional case of `TauCeti.enorm_le_sum_eLpNorm_of_contDiffOn_of_forall_starConvex`. -/
private theorem enorm_le_sum_eLpNorm_of_contDiffOn_subsingleton [Subsingleton E] {Ω : Set E}
    (hΩ : IsOpen Ω) (γ : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {k : ℕ}
    {f : E → F} (hf : ContDiffOn ℝ k f Ω) {x : E} (hx : x ∈ Ω) :
    ‖f x‖ₑ ≤ ENNReal.ofReal (starConvexSupConst (finrank ℝ E) k p γ (μ.real (ball 0 1))) *
      ∑ j ∈ Finset.range (k + 1),
        ENNReal.ofReal (diam Ω ^ ((j : ℝ) - finrank ℝ E / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω) := by
  set vB := μ.real (ball (0 : E) 1) with hvB_def
  have hn0 : finrank ℝ E = 0 := finrank_zero_of_subsingleton
  have hvB : 0 < vB := Metric.measureReal_ball_pos μ 0 one_pos
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hΩuniv : Ω = Set.univ := eq_univ_of_forall fun z => Subsingleton.elim z x ▸ hx
  have hballuniv : ball (0 : E) 1 = Set.univ :=
    eq_univ_of_forall fun z => by rw [mem_ball, Subsingleton.elim z 0, dist_self]; exact one_pos
  have hμΩ : μ Ω = ENNReal.ofReal vB := by
    rw [hΩuniv, ← hballuniv, hvB_def, ofReal_measureReal measure_ball_lt_top.ne]
  have h0 : ‖f x‖ₑ = ENNReal.ofReal (vB ^ (-1 / p.toReal)) *
      eLpNorm (iteratedFDeriv ℝ 0 f) p (μ.restrict Ω) := by
    have he : eLpNorm (iteratedFDeriv ℝ 0 f) p (μ.restrict Ω) =
        ‖f x‖ₑ * ENNReal.ofReal (vB ^ (1 / p.toReal)) := by
      rw [eLpNorm_congr_norm_ae (g := fun _ => f x)
          ((ContinuousOn.continuousOn_iteratedFDeriv hf hΩ (by simp)).aestronglyMeasurable
            hΩ.measurableSet) aestronglyMeasurable_const
          (.of_forall fun y => by rw [Subsingleton.elim y x, norm_iteratedFDeriv_zero]),
        eLpNorm_const' (f x) hp0 hp, Measure.restrict_apply_univ, hμΩ,
        ENNReal.ofReal_rpow_of_pos hvB]
    have hzero : -1 / p.toReal + 1 / p.toReal = 0 := by ring
    rw [he, ← mul_assoc, mul_comm (ENNReal.ofReal (vB ^ (-1 / p.toReal))), mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hvB, hzero, Real.rpow_zero,
      ENNReal.ofReal_one, mul_one]
  have hconst : starConvexSupConst (finrank ℝ E) k p γ vB = vB ^ (-1 / p.toReal) := by
    simp [starConvexSupConst, starConvexSupConstFin, hp, hn0]
  rw [hconst, h0, Finset.mul_sum]
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le)
    (Finset.mem_range.2 (Nat.succ_pos k)))
  simp [hn0]

/-- **Classical `Cᵏ` supremum estimate on a bounded star-shaped domain.** Let `Ω` be a bounded open
subset of a finite-dimensional real normed space `E` of dimension `n`, star-convex with respect to
every point of `ball x₀ ρ` (`0 < ρ`) with `diam Ω ≤ γ * ρ`. For `1 ≤ p < ∞` and `k : ℕ` with
`n < k * p` or `p = 1 ∧ n ≤ k`, every `Cᵏ` function `f : E → F` on `Ω` into a Banach space `F`
satisfies

`‖f x‖ₑ ≤ C(n, k, p, γ, μ(B(0, 1))) * ∑_{j ≤ k} (diam Ω) ^ (j - n / p) * ‖Dʲ f‖_{Lᵖ(Ω)}`

at every `x ∈ Ω`, with no integrability assumptions. -/
theorem enorm_le_sum_eLpNorm_of_contDiffOn_of_forall_starConvex [CompleteSpace F] {Ω : Set E}
    (hΩ : IsOpen Ω) (hb : IsBounded Ω) {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y Ω) (hγ : diam Ω ≤ γ * ρ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {k : ℕ}
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    {f : E → F} (hf : ContDiffOn ℝ k f Ω) {x : E} (hx : x ∈ Ω) :
    ‖f x‖ₑ ≤ ENNReal.ofReal (starConvexSupConst (finrank ℝ E) k p γ (μ.real (ball 0 1))) *
      ∑ j ∈ Finset.range (k + 1),
        ENNReal.ofReal (diam Ω ^ ((j : ℝ) - finrank ℝ E / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict Ω) := by
  rcases subsingleton_or_nontrivial E with _ | _
  · exact enorm_le_sum_eLpNorm_of_contDiffOn_subsingleton hΩ γ hp hf hx
  set n := finrank ℝ E
  set vB := μ.real (ball (0 : E) 1)
  have hn0 : n ≠ 0 := finrank_pos.ne'
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero fun hk0 => by
    subst hk0
    rcases hkp with h | ⟨_, h⟩
    · simp at h
    · exact hn0 (Nat.le_zero.1 h)
  have hBΩ : ball x₀ ρ ⊆ Ω := fun _ hy => (hstar _ hy).mem ⟨x, hx⟩
  have hB0 : μ (ball x₀ ρ) ≠ 0 := (measure_ball_pos μ x₀ hρ).ne'
  have hBtop : μ (ball x₀ ρ) ≠ ⊤ := measure_ball_lt_top.ne
  -- Integrate the pointwise Taylor bound over `y ∈ ball x₀ ρ`.
  have hmeas_term : ∀ j ∈ Finset.range (m + 1),
      AEMeasurable (fun y => ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * diam Ω ^ j) *
        ‖iteratedFDeriv ℝ j f y‖ₑ) (μ.restrict (ball x₀ ρ)) := fun j hj =>
    ((ContinuousOn.continuousOn_iteratedFDeriv hf hΩ
      (by exact_mod_cast (Finset.mem_range.1 hj).le)).mono hBΩ).eNorm.aemeasurable
      measurableSet_ball |>.const_mul _
  have hint : ‖f x‖ₑ * μ (ball x₀ ρ) ≤
      (∑ j ∈ Finset.range (m + 1),
        ENNReal.ofReal ((j.factorial : ℝ)⁻¹ * diam Ω ^ j) *
          ∫⁻ y in ball x₀ ρ, ‖iteratedFDeriv ℝ j f y‖ₑ ∂μ) +
      ENNReal.ofReal (m.factorial : ℝ)⁻¹ *
        ∫⁻ y in ball x₀ ρ,
          (∫⁻ s in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (s ^ (((m + 1 : ℕ) : ℝ) - 1)) *
              Ω.indicator (fun z => ‖iteratedFDeriv ℝ (m + 1) f z‖ₑ) (x + s • (y - x))) *
            ‖x - y‖ₑ ^ ((m + 1 : ℕ) : ℝ) ∂μ := by
    calc ‖f x‖ₑ * μ (ball x₀ ρ)
        = ∫⁻ _ in ball x₀ ρ, ‖f x‖ₑ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in ball x₀ ρ, _ ∂μ :=
          setLIntegral_mono' measurableSet_ball fun y hy =>
            enorm_le_sum_add_segment_of_contDiffOn hΩ hb hstar hf hx hy
      _ = _ := by
          rw [lintegral_add_left' (Finset.aemeasurable_fun_sum _ hmeas_term),
            lintegral_finsetSum' _ hmeas_term,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact Finset.sum_congr rfl fun j _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Divide by `μ(ball x₀ ρ)` and control the lower-order and top-order terms separately.
  have hfx : ‖f x‖ₑ = (μ (ball x₀ ρ))⁻¹ * (‖f x‖ₑ * μ (ball x₀ ρ)) := by
    rw [mul_left_comm, ENNReal.inv_mul_cancel hB0 hBtop, mul_one]
  have hdiv := hfx.trans_le (mul_le_mul_right hint (μ (ball x₀ ρ))⁻¹)
  set C := starConvexSupConst n (m + 1) p γ vB
  have hC1 : vB ^ (-1 / p.toReal) * (max γ 1) ^ ((n : ℝ) / p.toReal) ≤ C := by
    simp only [C, starConvexSupConst, starConvexSupConstFin, hp, hn0, ite_false]
    exact le_max_left _ _
  have hC2 : (((m.factorial : ℝ) * n * vB)⁻¹ * (max γ 1) ^ n *
      (if p = 1 then 1 else ((n : ℝ) * vB * (p.toReal - 1) /
        (((m + 1 : ℕ) : ℝ) * p.toReal - n)) ^ (1 - 1 / p.toReal))) ≤ C := by
    simp only [C, starConvexSupConst, starConvexSupConstFin, hp, hn0, ite_false,
      Nat.add_sub_cancel]
    exact le_max_right _ _
  refine hdiv.trans ?_
  rw [mul_add, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun j hj => ?_) ?_
  · refine (inv_ball_mul_setLIntegral_iteratedFDeriv_le hΩ hb hρ hBΩ hγ hp
      (Finset.mem_range.1 hj).le hf).trans ?_
    gcongr
  · refine (inv_ball_mul_remainder_le hΩ hb hρ hBΩ hγ hp hkp hf hx).trans ?_
    gcongr

end Classical

end TauCeti

end
