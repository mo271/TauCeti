/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Probability.Moments.Covariance
public import TauCeti.Statistics.ExponentialFamily.Basic

import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.Variance

/-!
# Analyticity, moments, and derivatives of the log partition function

On a finite-dimensional real inner product space `E`, every point `η` in the interior of the
natural parameter space admits a uniform exponential moment `∫ exp (⟪η, x⟫ + r ‖x‖) dν < ∞` for
some `r > 0`. From this domination we derive:

* finite moments of all orders (`MemLp id p` and `MemLp (inner ℝ u ·) p` for all finite `p`)
  under the exponential-family law `exponentialFamilyMeasure ν id η`;
* an explicit power series expansion `HasFPowerSeriesOnBall` for the partition function
  `ζ ↦ ∫ x, exp ⟪ζ, x⟫ dν` around `η`, obtained termwise via
  `MeasureTheory.hasSum_integral_of_dominated_convergence`;
* real analyticity of `logPartition ν id` on `interior (naturalParameterSpace ν id)`
  (`TauCeti.analyticOnNhd_logPartition`);
* the first Fréchet derivative `⟪∫ x dP_η, ·⟫` (`TauCeti.hasFDerivAt_logPartition`);
* the second Fréchet derivative `(u, v) ↦ cov[⟪u, ·⟫, ⟪v, ·⟫; P_η]`
  (`TauCeti.fderiv_fderiv_logPartition_apply`), together with its positive definiteness for minimal
  families (`TauCeti.fderiv_fderiv_logPartition_self_pos`).

This follows Lawrence D. Brown, *Fundamentals of Statistical Exponential Families* (IMS Lecture
Notes–Monograph Series, Vol. 9, 1986, Chapter 2, Theorems 2.2 and 2.7), and Mark J. Schervish,
*Theory of Statistics* (Springer, 1995, Theorem 2.64).
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology Nat

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-! ### Uniform exponential domination and moments of all orders -/

/-- At an interior natural parameter `η`, the identity map `id : E → E` is a.e.-strongly measurable
with respect to `ν`, deduced from the integrability of `exp ⟪ζ, ·⟫` along an orthonormal basis. -/
private lemma aestronglyMeasurable_id_of_mem_interior {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    AEStronglyMeasurable (id : E → E) ν := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hη)
  have hballN : Metric.ball η r₀ ⊆ naturalParameterSpace ν id := hball.trans interior_subset
  let b := stdOrthonormalBasis ℝ E
  set s : ℝ := r₀ / 2
  have hs : 0 < s := by positivity
  have hη_meas : AEMeasurable (fun x : E ↦ inner ℝ η x) ν :=
    aemeasurable_of_aemeasurable_exp
      (mem_naturalParameterSpace_iff.mp (interior_subset hη)).aemeasurable
  have hcoord : ∀ i : Fin (Module.finrank ℝ E), AEMeasurable (fun x : E ↦ inner ℝ (b i) x) ν := by
    intro i
    have hdist : dist (η + s • b i) η < r₀ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
        b.orthonormal.1 i, mul_one]
      dsimp only [s]
      linarith
    have hadd := aemeasurable_of_aemeasurable_exp
      (mem_naturalParameterSpace_iff.mp (hballN hdist)).aemeasurable
    have hsub : (fun x : E ↦ inner ℝ (b i) x) =
        fun x ↦ s⁻¹ * (inner ℝ (η + s • b i) x - inner ℝ η x) := by
      ext x
      rw [inner_add_left, inner_smul_left, RCLike.conj_to_real, add_sub_cancel_left,
        inv_mul_cancel_left₀ hs.ne']
    rw [hsub]
    exact (hadd.sub hη_meas).const_mul s⁻¹
  have hid : (id : E → E) = fun x ↦ ∑ i : Fin (Module.finrank ℝ E), inner ℝ (b i) x • b i := by
    ext x
    exact (b.sum_repr' x).symm
  rw [hid]
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ ↦
    (hcoord i).aestronglyMeasurable.smul_const (b i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
/-- Pointwise domination of `exp (⟪η, x⟫ + (s / (d + 1)) ‖x‖)` by the signed basis exponentials
`exp ⟪η ± s • b i, x⟫`. -/
private lemma exp_add_mul_norm_le_sum_basis {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (η x : E) {s : ℝ} (hs : 0 < s) :
    Real.exp (inner ℝ η x + (s / (d + 1 : ℝ)) * ‖x‖) ≤
      Real.exp (inner ℝ η x) +
        ∑ i : Fin d, (Real.exp (inner ℝ (η + s • b i) x) +
          Real.exp (inner ℝ (η + (-s) • b i) x)) := by
  set r : ℝ := s / (d + 1 : ℝ)
  have hr : 0 < r := by positivity
  have hnorm_le : ‖x‖ ≤ ∑ i : Fin d, |inner ℝ (b i) x| := by
    calc ‖x‖ = ‖∑ i : Fin d, inner ℝ (b i) x • b i‖ := by rw [b.sum_repr' x]
      _ ≤ ∑ i : Fin d, ‖inner ℝ (b i) x • b i‖ := norm_sum_le _ _
      _ = ∑ i : Fin d, |inner ℝ (b i) x| := Finset.sum_congr rfl fun i _ ↦ by
          rw [norm_smul, Real.norm_eq_abs, b.orthonormal.1 i, mul_one]
  rcases (Finset.univ : Finset (Fin d)).eq_empty_or_nonempty with hemp | hne
  · have hx0 : ‖x‖ = 0 := le_antisymm (by simpa [hemp] using hnorm_le) (norm_nonneg x)
    simp [hx0, hemp]
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |inner ℝ (b i) x|) hne
  have hrx : r * ‖x‖ ≤ s * |inner ℝ (b i₀) x| := by
    have hsum : ∑ i : Fin d, |inner ℝ (b i) x| ≤ (d : ℝ) * |inner ℝ (b i₀) x| := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.sum_le_card_nsmul Finset.univ (fun i ↦ |inner ℝ (b i) x|) _ fun i hi ↦ hi₀ i hi
    have hmul : r * (d : ℝ) = s * ((d : ℝ) / (d + 1 : ℝ)) := by ring
    have hrd : r * (d : ℝ) ≤ s := by
      rw [hmul]
      exact mul_le_of_le_one_right hs.le (div_le_one_of_le₀ (by linarith) (by positivity))
    calc r * ‖x‖ ≤ r * ((d : ℝ) * |inner ℝ (b i₀) x|) :=
          mul_le_mul_of_nonneg_left (hnorm_le.trans hsum) hr.le
      _ = (r * (d : ℝ)) * |inner ℝ (b i₀) x| := by ring
      _ ≤ s * |inner ℝ (b i₀) x| := mul_le_mul_of_nonneg_right hrd (abs_nonneg _)
  have hexp : Real.exp (inner ℝ η x + r * ‖x‖) ≤
      Real.exp (inner ℝ (η + s • b i₀) x) + Real.exp (inner ℝ (η + (-s) • b i₀) x) := by
    rcases le_total 0 (inner ℝ (b i₀) x) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hrx
      have h1 : Real.exp (inner ℝ η x + r * ‖x‖) ≤ Real.exp (inner ℝ (η + s • b i₀) x) := by
        rw [inner_add_left, inner_smul_left, RCLike.conj_to_real]
        exact Real.exp_le_exp.mpr (by linarith)
      exact h1.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_nonpos hneg] at hrx
      have h1 : Real.exp (inner ℝ η x + r * ‖x‖) ≤ Real.exp (inner ℝ (η + (-s) • b i₀) x) := by
        rw [inner_add_left, inner_smul_left, RCLike.conj_to_real]
        exact Real.exp_le_exp.mpr (by linarith)
      exact h1.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hsingle := Finset.single_le_sum (f := fun i ↦ Real.exp (inner ℝ (η + s • b i) x) +
      Real.exp (inner ℝ (η + (-s) • b i) x)) (fun i _ ↦ by positivity) (Finset.mem_univ i₀)
  linarith [Real.exp_pos (inner ℝ η x)]

/-- At every point `η` in the interior of the natural parameter space on a finite-dimensional real
inner product space, there exists `r > 0` such that `x ↦ exp (⟪η, x⟫ + r ‖x‖)` is `ν`-integrable. -/
theorem exists_pos_integrable_exp_add_mul_norm {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    ∃ r : ℝ, 0 < r ∧ Integrable (fun x ↦ Real.exp (inner ℝ η x + r * ‖x‖)) ν := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hη)
  have hballN : Metric.ball η r₀ ⊆ naturalParameterSpace ν id := hball.trans interior_subset
  let b := stdOrthonormalBasis ℝ E
  set d : ℕ := Module.finrank ℝ E
  set s : ℝ := r₀ / 2
  set r : ℝ := s / (d + 1 : ℝ)
  have hs : 0 < s := by positivity
  have hr : 0 < r := by positivity
  have hmem_pm : ∀ (σ : ℝ), |σ| = 1 → ∀ i : Fin d,
      Integrable (fun x ↦ Real.exp (inner ℝ (η + (σ * s) • b i) x)) ν := by
    intro σ hσ i
    have hdist : dist (η + (σ * s) • b i) η < r₀ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul, hσ, one_mul,
        abs_of_pos hs, b.orthonormal.1 i, mul_one]
      dsimp only [s]
      linarith
    exact mem_naturalParameterSpace_iff.mp (hballN hdist)
  have hη_int : Integrable (fun x ↦ Real.exp (inner ℝ η x)) ν :=
    mem_naturalParameterSpace_iff.mp (hballN (Metric.mem_ball_self hr₀))
  have hsum_int : Integrable (fun x ↦ ∑ i : Fin d,
      (Real.exp (inner ℝ (η + s • b i) x) + Real.exp (inner ℝ (η + (-s) • b i) x))) ν := by
    refine integrable_finsetSum Finset.univ fun i _ ↦ ?_
    have hp : Integrable (fun x ↦ Real.exp (inner ℝ (η + s • b i) x)) ν := by
      simpa only [one_mul] using hmem_pm 1 (by simp) i
    have hm : Integrable (fun x ↦ Real.exp (inner ℝ (η + (-s) • b i) x)) ν := by
      simpa only [neg_one_mul] using hmem_pm (-1) (by simp) i
    exact hp.add hm
  have hcont : Continuous fun x : E ↦ Real.exp (inner ℝ η x + r * ‖x‖) := by fun_prop
  refine ⟨r, hr, (hη_int.add hsum_int).mono'
    (hcont.comp_aestronglyMeasurable (aestronglyMeasurable_id_of_mem_interior hη))
    (ae_of_all _ fun x ↦ ?_)⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_add_mul_norm_le_sum_basis b η x hs

/-- At every interior natural parameter `η`, `x ↦ ‖x‖ ^ n * exp ⟪η, x⟫` is `ν`-integrable for all
`n : ℕ`. -/
theorem integrable_norm_pow_mul_exp {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (n : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ n * Real.exp (inner ℝ η x)) ν := by
  obtain ⟨r, hr, hdom⟩ := exists_pos_integrable_exp_add_mul_norm hη
  have hcont : Continuous fun x : E ↦ ‖x‖ ^ n * Real.exp (inner ℝ η x) := by fun_prop
  refine (hdom.const_mul ((n ! : ℝ) / r ^ n)).mono'
    (hcont.comp_aestronglyMeasurable (aestronglyMeasurable_id_of_mem_interior hη))
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.exp_add]
  have hpow : (r * ‖x‖) ^ n / (n ! : ℝ) ≤ Real.exp (r * ‖x‖) :=
    Real.pow_div_factorial_le_exp (r * ‖x‖) (by positivity) n
  have h1 : ‖x‖ ^ n ≤ ((n ! : ℝ) / r ^ n) * Real.exp (r * ‖x‖) := by
    rw [mul_pow] at hpow
    have h2 : r ^ n * ‖x‖ ^ n ≤ (n ! : ℝ) * Real.exp (r * ‖x‖) := by
      rwa [div_le_iff₀ (by positivity), mul_comm (Real.exp _)] at hpow
    have hrn : 0 < r ^ n := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hrn, mul_comm (‖x‖ ^ n)]
    exact h2
  calc ‖x‖ ^ n * Real.exp (inner ℝ η x)
      ≤ ((n ! : ℝ) / r ^ n) * Real.exp (r * ‖x‖) * Real.exp (inner ℝ η x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (n ! : ℝ) / r ^ n * (Real.exp (inner ℝ η x) * Real.exp (r * ‖x‖)) := by ring

/-- At every interior natural parameter `η`, `‖x‖ ^ n` is integrable under
`exponentialFamilyMeasure ν id η` for every `n : ℕ`. -/
theorem integrable_norm_pow_exponentialFamilyMeasure {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (n : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ n) (exponentialFamilyMeasure ν id η) := by
  rw [exponentialFamilyMeasure_def, integrable_tilted_iff
    (mem_naturalParameterSpace_iff.mp (interior_subset hη))]
  simpa only [smul_eq_mul, mul_comm (Real.exp _), id_eq] using integrable_norm_pow_mul_exp hη n

/-- At every interior natural parameter `η`, the identity belongs to `Lp` for every finite exponent
`p : ℝ≥0` under `exponentialFamilyMeasure ν id η`. -/
theorem memLp_id_exponentialFamilyMeasure {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (p : ℝ≥0) :
    MemLp id (p : ℝ≥0∞) (exponentialFamilyMeasure ν id η) := by
  have hac : exponentialFamilyMeasure ν id η ≪ ν := by
    rw [exponentialFamilyMeasure_def]
    exact tilted_absolutelyContinuous ν _
  have hid_meas : AEStronglyMeasurable (id : E → E) (exponentialFamilyMeasure ν id η) :=
    (aestronglyMeasurable_id_of_mem_interior hη).mono_ac hac
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [hid_meas]
  rw [← integrable_norm_rpow_iff hid_meas (by simp [hp0]) ENNReal.coe_ne_top]
  simp only [ENNReal.coe_toReal, id_eq]
  set n : ℕ := ⌈(p : ℝ)⌉₊
  have hle : (p : ℝ) ≤ (n : ℝ) := Nat.le_ceil _
  have hdom : Integrable (fun x : E ↦ (1 : ℝ) + ‖x‖ ^ n) (exponentialFamilyMeasure ν id η) :=
    (integrable_const (1 : ℝ)).add (integrable_norm_pow_exponentialFamilyMeasure hη n)
  have hcont : Continuous fun x : E ↦ ‖x‖ ^ (p : ℝ) := by fun_prop
  refine hdom.mono' (hcont.comp_aestronglyMeasurable hid_meas) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  rcases le_total ‖x‖ 1 with hx | hx
  · exact le_add_of_le_of_nonneg (Real.rpow_le_one (norm_nonneg x) hx p.coe_nonneg) (by positivity)
  · exact le_add_of_nonneg_of_le zero_le_one
      ((Real.rpow_le_rpow_of_exponent_le hx hle).trans_eq (Real.rpow_natCast ‖x‖ n))

/-- At every interior natural parameter `η`, the identity is integrable under
`exponentialFamilyMeasure ν id η`. -/
theorem integrable_id_exponentialFamilyMeasure {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    Integrable id (exponentialFamilyMeasure ν id η) := by
  simpa using memLp_one_iff_integrable.mp (memLp_id_exponentialFamilyMeasure hη 1)

/-- At every interior natural parameter `η`, every continuous linear functional `⟪u, ·⟫` belongs to
`Lp` for every finite exponent `p : ℝ≥0` under `exponentialFamilyMeasure ν id η`. -/
theorem memLp_inner_exponentialFamilyMeasure {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (p : ℝ≥0) (u : E) :
    MemLp (fun x ↦ inner ℝ u x) (p : ℝ≥0∞) (exponentialFamilyMeasure ν id η) := by
  have hac : exponentialFamilyMeasure ν id η ≪ ν := by
    rw [exponentialFamilyMeasure_def]
    exact tilted_absolutelyContinuous ν _
  have hid_meas : AEStronglyMeasurable (id : E → E) (exponentialFamilyMeasure ν id η) :=
    (aestronglyMeasurable_id_of_mem_interior hη).mono_ac hac
  refine ((memLp_id_exponentialFamilyMeasure hη p).norm.const_mul ‖u‖).mono'
    ((continuous_const.inner continuous_id).comp_aestronglyMeasurable hid_meas)
    (ae_of_all _ fun x ↦ ?_)
  simpa only [Real.norm_eq_abs, id_eq] using abs_real_inner_le_norm u x

/-! ### Power series of the partition function -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
/-- The `n`-th term inside the Bochner integral defining the power series of the partition function
around `η`: `(n!⁻¹ * exp ⟪η, x⟫) • ((v₁, ..., vₙ) ↦ ∏ i, ⟪x, vᵢ⟫)`. -/
private noncomputable def partitionSeriesTerm (η x : E) (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) ℝ :=
  ((n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x)) •
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (1 : ℝ)).compContinuousLinearMap
      fun _ ↦ innerSL ℝ x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
private lemma partitionSeriesTerm_apply (η x : E) (n : ℕ) (v : Fin n → E) :
    partitionSeriesTerm η x n v =
      (n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) * ∏ i : Fin n, inner ℝ x (v i) := by
  simp [partitionSeriesTerm, smul_eq_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
private lemma norm_partitionSeriesTerm_le (η x : E) (n : ℕ) :
    ‖partitionSeriesTerm η x n‖ ≤ (n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) * ‖x‖ ^ n := by
  rw [partitionSeriesTerm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (1 : ℝ)) (fun _ ↦ innerSL ℝ x)
  rw [ContinuousMultilinearMap.norm_mkPiRing, norm_one, one_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h1
  refine h1.trans (pow_le_pow_left₀ (norm_nonneg _) ?_ n)
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y ↦ abs_real_inner_le_norm x y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
private lemma continuous_partitionSeriesTerm (η : E) (n : ℕ) :
    Continuous (fun x ↦ partitionSeriesTerm η x n) := by
  have h1 : Continuous fun x : E ↦ (n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) := by fun_prop
  have h2 : Continuous fun x : E ↦
      (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (1 : ℝ)).compContinuousLinearMap
        (fun _ ↦ innerSL ℝ x) :=
    (ContinuousMultilinearMap.compContinuousLinearMapLRight
      (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (1 : ℝ))).coe_continuous.comp
      (continuous_pi fun _ ↦ (innerSL ℝ).continuous)
  exact h1.smul h2

private lemma integrable_partitionSeriesTerm {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (n : ℕ) :
    Integrable (fun x ↦ partitionSeriesTerm η x n) ν := by
  have hbound : Integrable (fun x ↦ (n ! : ℝ)⁻¹ * (‖x‖ ^ n * Real.exp (inner ℝ η x))) ν :=
    (integrable_norm_pow_mul_exp hη n).const_mul _
  refine hbound.mono'
    ((continuous_partitionSeriesTerm η n).comp_aestronglyMeasurable
      (aestronglyMeasurable_id_of_mem_interior hη))
    (ae_of_all _ fun x ↦ ?_)
  calc ‖partitionSeriesTerm η x n‖
      ≤ (n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) * ‖x‖ ^ n := norm_partitionSeriesTerm_le η x n
    _ = (n ! : ℝ)⁻¹ * (‖x‖ ^ n * Real.exp (inner ℝ η x)) := by ring

omit [FiniteDimensional ℝ E] in
/-- The power series of the partition function `ζ ↦ ∫ x, exp ⟪ζ, x⟫ ∂ν` centered at `η`. -/
private noncomputable def partitionPowerSeries (ν : Measure E) (η : E) :
    FormalMultilinearSeries ℝ E ℝ :=
  fun n ↦ ∫ x, partitionSeriesTerm η x n ∂ν

private lemma partitionPowerSeries_apply {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (n : ℕ) (v : Fin n → E) :
    partitionPowerSeries ν η n v =
      ∫ x, (n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) * ∏ i : Fin n, inner ℝ x (v i) ∂ν := by
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) ℝ v).integral_comp_comm
    (integrable_partitionSeriesTerm hη n)
  simpa only [partitionPowerSeries, ContinuousMultilinearMap.apply_apply,
    partitionSeriesTerm_apply] using hev.symm

/-- The radius of convergence of `partitionPowerSeries ν η` is at least `r` when
`exp (⟪η, x⟫ + r ‖x‖)` is `ν`-integrable. -/
private lemma le_radius_partitionPowerSeries {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) {r : ℝ} (hr : 0 < r)
    (hdom : Integrable (fun x ↦ Real.exp (inner ℝ η x + r * ‖x‖)) ν) :
    ENNReal.ofReal r ≤ (partitionPowerSeries ν η).radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal hr.le]
  refine FormalMultilinearSeries.le_radius_of_bound (partitionPowerSeries ν η)
    (∫ x, Real.exp (inner ℝ η x + r * ‖x‖) ∂ν) (r := ⟨r, hr.le⟩) fun n ↦ ?_
  calc ‖partitionPowerSeries ν η n‖ * r ^ n
      ≤ (∫ x, ‖partitionSeriesTerm η x n‖ ∂ν) * r ^ n := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ = ∫ x, ‖partitionSeriesTerm η x n‖ * r ^ n ∂ν := (integral_mul_const _ _).symm
    _ ≤ ∫ x, Real.exp (inner ℝ η x + r * ‖x‖) ∂ν := by
        refine integral_mono ((integrable_partitionSeriesTerm hη n).norm.mul_const _) hdom
          fun x ↦ ?_
        rw [Real.exp_add]
        calc ‖partitionSeriesTerm η x n‖ * r ^ n
            ≤ ((n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) * ‖x‖ ^ n) * r ^ n :=
              mul_le_mul_of_nonneg_right (norm_partitionSeriesTerm_le η x n) (by positivity)
          _ = Real.exp (inner ℝ η x) * ((r * ‖x‖) ^ n / (n ! : ℝ)) := by
              rw [mul_pow]; ring
          _ ≤ Real.exp (inner ℝ η x) * Real.exp (r * ‖x‖) :=
              mul_le_mul_of_nonneg_left
                (Real.pow_div_factorial_le_exp (r * ‖x‖) (by positivity) n)
                (Real.exp_pos _).le

/-- Termwise dominated convergence summing `partitionPowerSeries ν η` on the ball of radius `r`. -/
private lemma hasSum_partitionPowerSeries {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) {r : ℝ}
    (hdom : Integrable (fun x ↦ Real.exp (inner ℝ η x + r * ‖x‖)) ν)
    {h : E} (hh : h ∈ Metric.eball 0 (ENNReal.ofReal r)) :
    HasSum (fun n ↦ partitionPowerSeries ν η n fun _ ↦ h)
      (∫ x, Real.exp (inner ℝ (η + h) x) ∂ν) := by
  have hid := aestronglyMeasurable_id_of_mem_interior hη
  have hr : 0 < r := ENNReal.ofReal_pos.mp (bot_le.trans_lt (Metric.mem_eball.mp hh))
  have hnorm : ‖h‖ < r := by
    simpa [Metric.mem_eball, eDist_eq_eNorm_sub, ENNReal.ofReal_lt_ofReal_iff hr,
      eNorm_eq_nnNorm, ← ENNReal.ofReal_coe_nnreal] using hh
  simp_rw [partitionPowerSeries_apply hη, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x : E ↦ (n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) * inner ℝ x h ^ n) ν := fun n ↦
    (by fun_prop : Continuous fun x : E ↦
      (n ! : ℝ)⁻¹ * Real.exp (inner ℝ η x) * inner ℝ x h ^ n).comp_aestronglyMeasurable hid
  refine hasSum_integral_of_dominated_convergence
    (bound := fun n x ↦ Real.exp (inner ℝ η x) * ((‖h‖ * ‖x‖) ^ n / (n ! : ℝ)))
    hF_meas ?_ ?_ ?_ ?_
  · refine fun n ↦ ae_of_all _ fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_pos (Real.exp_pos _), abs_pow, div_eq_inv_mul, mul_left_comm, ← mul_assoc]
    have hcs : |inner ℝ x h| ^ n ≤ (‖h‖ * ‖x‖) ^ n :=
      pow_le_pow_left₀ (abs_nonneg _) (by rw [mul_comm]; exact abs_real_inner_le_norm x h) n
    exact mul_le_mul_of_nonneg_left hcs (by positivity)
  · exact ae_of_all _ fun x ↦
      ((NormedSpace.expSeries_div_hasSum_exp (‖h‖ * ‖x‖)).mul_left _).summable
  · have htsum : (fun x : E ↦ ∑' n : ℕ,
        Real.exp (inner ℝ η x) * ((‖h‖ * ‖x‖) ^ n / (n ! : ℝ))) =
        fun x : E ↦ Real.exp (inner ℝ η x + ‖h‖ * ‖x‖) := by
      ext x
      rw [((NormedSpace.expSeries_div_hasSum_exp (‖h‖ * ‖x‖)).mul_left _).tsum_eq,
        ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    rw [htsum]
    have hcont : Continuous fun x : E ↦ Real.exp (inner ℝ η x + ‖h‖ * ‖x‖) := by fun_prop
    refine hdom.mono' (hcont.comp_aestronglyMeasurable hid) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (add_le_add_right (mul_le_mul_of_nonneg_right hnorm.le (norm_nonneg x)) _)
  · refine ae_of_all _ fun x ↦ ?_
    have hsum : HasSum (fun n : ℕ ↦ Real.exp (inner ℝ η x) * (inner ℝ h x ^ n / (n ! : ℝ)))
        (Real.exp (inner ℝ (η + h) x)) := by
      rw [inner_add_left, Real.exp_add]
      simpa only [← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (inner ℝ h x)).mul_left (Real.exp (inner ℝ η x))
    exact hsum.congr_fun fun n ↦ by rw [real_inner_comm x h]; ring

/-- On a ball of positive radius `r` where `exp (⟪η, x⟫ + r ‖x‖)` is `ν`-integrable, the partition
function has the power series `partitionPowerSeries ν η`. -/
private theorem hasFPowerSeriesOnBall_integral_exp_inner {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) {r : ℝ} (hr : 0 < r)
    (hdom : Integrable (fun x ↦ Real.exp (inner ℝ η x + r * ‖x‖)) ν) :
    HasFPowerSeriesOnBall (fun ζ ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν)
      (partitionPowerSeries ν η) η (ENNReal.ofReal r) where
  r_le := le_radius_partitionPowerSeries hη hr hdom
  r_pos := ENNReal.ofReal_pos.mpr hr
  hasSum hh := hasSum_partitionPowerSeries hη hdom hh

/-! ### Analyticity, gradient, and Hessian of the log partition function -/

/-- The log partition function `logPartition ν id` is real analytic at every point of the interior
of the natural parameter space. -/
theorem analyticAt_logPartition (ν : Measure E) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    AnalyticAt ℝ (logPartition ν id) η := by
  rcases eq_or_ne ν 0 with rfl | hν
  · have hzero : logPartition (0 : Measure E) id = fun _ ↦ (0 : ℝ) := by
      ext ζ; simp
    rw [hzero]
    exact analyticAt_const
  have : NeZero ν := ⟨hν⟩
  obtain ⟨r, hr, hdom⟩ := exists_pos_integrable_exp_add_mul_norm hη
  let Z : E → ℝ := fun ζ ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν
  have hZ : AnalyticAt ℝ Z η :=
    (hasFPowerSeriesOnBall_integral_exp_inner hη hr hdom).analyticAt
  have hfun : logPartition ν id = fun ζ ↦ Real.log (Z ζ) := by
    ext ζ; exact logPartition_def ν id ζ
  rw [hfun]
  have hZpos : 0 < Z η := integral_exp_pos (mem_naturalParameterSpace_iff.mp (interior_subset hη))
  exact (analyticAt_log hZpos).fun_comp hZ

/-- The log partition function `logPartition ν id` is real analytic on the interior of the natural
parameter space. -/
theorem analyticOnNhd_logPartition (ν : Measure E) :
    AnalyticOnNhd ℝ (logPartition ν id) (interior (naturalParameterSpace ν id)) :=
  fun _ hη ↦ analyticAt_logPartition ν hη

/-- First Fréchet derivative of the partition function at an interior natural parameter. -/
private theorem hasFDerivAt_integral_exp_inner {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    HasFDerivAt (fun ζ ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν)
      (innerSL ℝ (∫ x, Real.exp (inner ℝ η x) • x ∂ν)) η := by
  obtain ⟨r, hr, hdom⟩ := exists_pos_integrable_exp_add_mul_norm hη
  have hderiv := (hasFPowerSeriesOnBall_integral_exp_inner hη hr hdom).hasFPowerSeriesAt.hasFDerivAt
  have hint_vec : Integrable (fun x : E ↦ Real.exp (inner ℝ η x) • x) ν := by
    have hnorm : Integrable (fun x : E ↦ ‖x‖ ^ 1 * Real.exp (inner ℝ η x)) ν :=
      integrable_norm_pow_mul_exp hη 1
    have hcont : Continuous fun x : E ↦ Real.exp (inner ℝ η x) • x := by fun_prop
    refine hnorm.mono'
      (hcont.comp_aestronglyMeasurable (aestronglyMeasurable_id_of_mem_interior hη))
      (ae_of_all _ fun x ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_one, mul_comm]
  have heq : continuousMultilinearCurryFin1 ℝ E ℝ (partitionPowerSeries ν η 1) =
      innerSL ℝ (∫ x, Real.exp (inner ℝ η x) • x ∂ν) := by
    ext u
    have hsnoc : (Fin.snoc 0 u : Fin 1 → E) 0 = u := by simp
    simp only [continuousMultilinearCurryFin1_apply, partitionPowerSeries_apply hη,
      Nat.factorial_one, Nat.cast_one, inv_one, one_mul, Fin.prod_univ_one, hsnoc,
      innerSL_apply_apply]
    have hcomm := (innerSL ℝ u).integral_comp_comm hint_vec
    simp only [innerSL_apply_apply, inner_smul_right] at hcomm
    rw [real_inner_comm u (∫ x, Real.exp (inner ℝ η x) • x ∂ν), ← hcomm]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [real_inner_comm u x]
  rwa [heq] at hderiv

/-- **First derivative of the log partition function.** At every point `η` in the interior of the
natural parameter space, the Fréchet derivative of `logPartition ν id` is `u ↦ ⟪∫ x dP_η, u⟫`. -/
theorem hasFDerivAt_logPartition (ν : Measure E) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    HasFDerivAt (logPartition ν id) (innerSL ℝ (∫ x, x ∂exponentialFamilyMeasure ν id η)) η := by
  rcases eq_or_ne ν 0 with rfl | hν
  · have hzero : logPartition (0 : Measure E) id = fun _ ↦ (0 : ℝ) := by ext ζ; simp
    rw [hzero]
    simpa using hasFDerivAt_const (0 : ℝ) η
  have : NeZero ν := ⟨hν⟩
  have hZpos : 0 < ∫ x, Real.exp (inner ℝ η x) ∂ν :=
    integral_exp_pos (mem_naturalParameterSpace_iff.mp (interior_subset hη))
  have hlog : HasFDerivAt (fun ζ ↦ Real.log (∫ x, Real.exp (inner ℝ ζ x) ∂ν))
      ((∫ x, Real.exp (inner ℝ η x) ∂ν)⁻¹ •
        innerSL ℝ (∫ x, Real.exp (inner ℝ η x) • x ∂ν)) η :=
    (hasFDerivAt_integral_exp_inner hη).log hZpos.ne'
  have hfun : logPartition ν id = fun ζ ↦ Real.log (∫ x, Real.exp (inner ℝ ζ x) ∂ν) := by
    ext ζ; exact logPartition_def ν id ζ
  have heq : (∫ x, Real.exp (inner ℝ η x) ∂ν)⁻¹ •
      innerSL ℝ (∫ x, Real.exp (inner ℝ η x) • x ∂ν) =
      innerSL ℝ (∫ x, x ∂exponentialFamilyMeasure ν id η) := by
    rw [← map_smul, exponentialFamilyMeasure_def, integral_tilted]
    congr 1
    rw [← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only [id_eq]
    rw [smul_smul, div_eq_inv_mul]
  rw [hfun, ← heq]
  exact hlog

/-- Explicit formula for `fderiv ℝ (logPartition ν id)` on the interior of the natural parameter
space. -/
theorem fderiv_logPartition (ν : Measure E) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) :
    fderiv ℝ (logPartition ν id) η = innerSL ℝ (∫ x, x ∂exponentialFamilyMeasure ν id η) :=
  (hasFDerivAt_logPartition ν hη).fderiv

/-- Evaluating the quadratic term `partitionPowerSeries ν η 2` on either single-element piecewise
choice of `(u, v)` yields half the weighted second moment. -/
private lemma partitionPowerSeries_two_piecewise {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (u v : E)
    (s : Finset (Fin 2)) (hs : s.card = 1) :
    partitionPowerSeries ν η 2 (s.piecewise (fun _ ↦ u) (fun _ ↦ v)) =
      (2 : ℝ)⁻¹ * ∫ x, Real.exp (inner ℝ η x) * (inner ℝ u x * inner ℝ v x) ∂ν := by
  rw [partitionPowerSeries_apply hη, ← integral_const_mul]
  have h01 : s.piecewise (fun _ ↦ u) (fun _ ↦ v) 0 = u ∧
      s.piecewise (fun _ ↦ u) (fun _ ↦ v) 1 = v ∨
      s.piecewise (fun _ ↦ u) (fun _ ↦ v) 0 = v ∧
      s.piecewise (fun _ ↦ u) (fun _ ↦ v) 1 = u := by
    by_cases h0 : (0 : Fin 2) ∈ s
    · have h1 : (1 : Fin 2) ∉ s := fun h1 ↦ by
        have hcard := Finset.card_le_card (s := Finset.univ) (t := s)
          fun i _ ↦ by fin_cases i <;> assumption
        simp [hs] at hcard
      exact Or.inl ⟨by simp [Finset.piecewise, h0], by simp [Finset.piecewise, h1]⟩
    · have h1 : (1 : Fin 2) ∈ s := by
        by_contra h1
        have hemp : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi ↦ by
          fin_cases i <;> contradiction
        simp [hemp] at hs
      exact Or.inr ⟨by simp [Finset.piecewise, h0], by simp [Finset.piecewise, h1]⟩
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [Fin.prod_univ_two]
  have hprod : inner ℝ x (s.piecewise (fun _ ↦ u) (fun _ ↦ v) 0) *
      inner ℝ x (s.piecewise (fun _ ↦ u) (fun _ ↦ v) 1) = inner ℝ u x * inner ℝ v x := by
    rcases h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1, real_inner_comm u x, real_inner_comm v x]
    · rw [h0, h1, real_inner_comm u x, real_inner_comm v x, mul_comm]
  rw [hprod, Nat.factorial_two, Nat.cast_ofNat]
  ring

/-- Second Fréchet derivative of the partition function at an interior natural parameter. -/
private theorem fderiv_fderiv_integral_exp_inner_apply {ν : Measure E} {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (u v : E) :
    fderiv ℝ (fderiv ℝ fun ζ ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν) η u v =
      ∫ x, Real.exp (inner ℝ η x) * (inner ℝ u x * inner ℝ v x) ∂ν := by
  obtain ⟨r, hr, hdom⟩ := exists_pos_integrable_exp_add_mul_norm hη
  have hZ := hasFPowerSeriesOnBall_integral_exp_inner hη hr hdom
  rw [hZ.fderiv.hasFPowerSeriesAt.fderiv_eq]
  have hsnoc_u : (Fin.snoc 0 u : Fin 1 → E) = fun _ ↦ u := by ext i; fin_cases i; simp
  have hsnoc_v : (Fin.snoc 0 v : Fin 1 → E) = fun _ ↦ v := by ext i; fin_cases i; simp
  have hstep : continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
      ((partitionPowerSeries ν η).derivSeries 1) u v =
      ∑ s : {s : Finset (Fin 2) // s.card = 1},
        partitionPowerSeries ν η 2 (s.1.piecewise (fun _ ↦ u) (fun _ ↦ v)) := by
    simp only [continuousMultilinearCurryFin1_apply, FormalMultilinearSeries.derivSeries,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.changeOriginSeries, hsnoc_u, sum_apply, map_sum,
      FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have h1 : (continuousMultilinearCurryFin1 ℝ E ℝ
        ((partitionPowerSeries ν η).changeOriginSeriesTerm 1 1 s.1 s.2 fun _ ↦ u)) v =
        (partitionPowerSeries ν η).changeOriginSeriesTerm 1 1 s.1 s.2
          (fun _ ↦ u) (fun _ ↦ v) := by
      simpa only [hsnoc_v] using continuousMultilinearCurryFin1_apply
        ((partitionPowerSeries ν η).changeOriginSeriesTerm 1 1 s.1 s.2 fun _ ↦ u) v
    exact h1.trans (FormalMultilinearSeries.changeOriginSeriesTerm_apply _ 1 1 s.1 s.2 u v)
  rw [hstep, Finset.sum_congr rfl fun s _ ↦ partitionPowerSeries_two_piecewise hη u v s.1 s.2,
    Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card {s : Finset (Fin 2) // s.card = 1} = 2 := by decide
  rw [hcard, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- Quotient-rule expansion of the Hessian of `logPartition ν id` in terms of the partition
function `Z` and its first two Fréchet derivatives. -/
private lemma fderiv_fderiv_logPartition_eq_sub {ν : Measure E} (hν : ν ≠ 0) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (u v : E) :
    let Z : E → ℝ := fun ζ ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν
    fderiv ℝ (fderiv ℝ (logPartition ν id)) η u v =
      (Z η)⁻¹ * fderiv ℝ (fderiv ℝ Z) η u v -
        (Z η ^ 2)⁻¹ * (fderiv ℝ Z η u) * (fderiv ℝ Z η v) := by
  intro Z
  have : NeZero ν := ⟨hν⟩
  have hZpos : 0 < Z η := integral_exp_pos (mem_naturalParameterSpace_iff.mp (interior_subset hη))
  have hZ_diff : HasFDerivAt Z (fderiv ℝ Z η) η :=
    (hasFDerivAt_integral_exp_inner hη).differentiableAt.hasFDerivAt
  obtain ⟨r, hr, hdom⟩ := exists_pos_integrable_exp_add_mul_norm hη
  have hZ_ps := (hasFPowerSeriesOnBall_integral_exp_inner hη hr hdom).fderiv
  have hdZ_diff : HasFDerivAt (fderiv ℝ Z) (fderiv ℝ (fderiv ℝ Z) η) η :=
    hZ_ps.hasFPowerSeriesAt.hasFDerivAt.differentiableAt.hasFDerivAt
  have hev : fderiv ℝ (logPartition ν id) =ᶠ[𝓝 η] fun ζ ↦ (Z ζ)⁻¹ • fderiv ℝ Z ζ := by
    filter_upwards [isOpen_interior.mem_nhds hη] with ζ hζ
    have hZζ : 0 < Z ζ := integral_exp_pos (mem_naturalParameterSpace_iff.mp (interior_subset hζ))
    have hfun : logPartition ν id = fun ξ ↦ Real.log (Z ξ) := by
      ext ξ; exact logPartition_def ν id ξ
    rw [hfun]
    exact (((hasFDerivAt_integral_exp_inner hζ).log hZζ.ne').fderiv).trans <| by
      rw [(hasFDerivAt_integral_exp_inner hζ).fderiv]
  have hinv : HasFDerivAt (fun ζ ↦ (Z ζ)⁻¹) ((-(Z η ^ 2)⁻¹) • fderiv ℝ Z η) η :=
    (hasDerivAt_inv hZpos.ne').comp_hasFDerivAt η hZ_diff
  have h2 : fderiv ℝ (fderiv ℝ (logPartition ν id)) η =
      (Z η)⁻¹ • fderiv ℝ (fderiv ℝ Z) η +
        ((-(Z η ^ 2)⁻¹) • fderiv ℝ Z η).smulRight (fderiv ℝ Z η) :=
    ((hinv.smul hdZ_diff).congr_of_eventuallyEq hev).fderiv
  rw [h2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, neg_mul]
  ring

/-- **Second derivative (Hessian) of the log partition function.** At every point `η` in the
interior of the natural parameter space, the second Fréchet derivative of `logPartition ν id` is
the covariance bilinear form `(u, v) ↦ cov[⟪u, ·⟫, ⟪v, ·⟫; P_η]`. -/
theorem fderiv_fderiv_logPartition_apply (ν : Measure E) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) (u v : E) :
    fderiv ℝ (fderiv ℝ (logPartition ν id)) η u v =
      cov[fun x ↦ inner ℝ u x, fun x ↦ inner ℝ v x; exponentialFamilyMeasure ν id η] := by
  rcases eq_or_ne ν 0 with rfl | hν
  · have hzero : logPartition (0 : Measure E) id = fun _ ↦ (0 : ℝ) := by ext ζ; simp
    rw [hzero]
    simp [covariance_zero_measure]
  have : NeZero ν := ⟨hν⟩
  let Z : E → ℝ := fun ζ ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν
  have hZpos : 0 < Z η := integral_exp_pos (mem_naturalParameterSpace_iff.mp (interior_subset hη))
  rw [fderiv_fderiv_logPartition_eq_sub hν hη u v, fderiv_fderiv_integral_exp_inner_apply hη u v]
  have h1 : ∀ w : E, (Z η)⁻¹ * fderiv ℝ Z η w =
      ∫ x, inner ℝ w x ∂exponentialFamilyMeasure ν id η := fun w ↦ by
    have hfun : logPartition ν id = fun ξ ↦ Real.log (Z ξ) := by
      ext ξ; exact logPartition_def ν id ξ
    have hdw' : fderiv ℝ (logPartition ν id) η w = (Z η)⁻¹ * fderiv ℝ Z η w := by
      have hlog : fderiv ℝ (fun ξ ↦ Real.log (Z ξ)) η = (Z η)⁻¹ • fderiv ℝ Z η := by
        rw [((hasFDerivAt_integral_exp_inner hη).log hZpos.ne').fderiv,
          (hasFDerivAt_integral_exp_inner hη).fderiv]
      rw [hfun, hlog]
      rfl
    have hdw := congrArg (fun L : E →L[ℝ] ℝ ↦ L w) (fderiv_logPartition ν hη)
    have hcomm := (innerSL ℝ w).integral_comp_comm (integrable_id_exponentialFamilyMeasure hη)
    simp only [innerSL_apply_apply, id_eq] at hdw hcomm
    rw [← hdw', hdw, real_inner_comm w (∫ x, x ∂exponentialFamilyMeasure ν id η), ← hcomm]
  have hprob : IsProbabilityMeasure (exponentialFamilyMeasure ν id η) := by
    rw [exponentialFamilyMeasure_def]
    exact isProbabilityMeasure_tilted (mem_naturalParameterSpace_iff.mp (interior_subset hη))
  rw [covariance_eq_sub (memLp_inner_exponentialFamilyMeasure hη 2 u)
    (memLp_inner_exponentialFamilyMeasure hη 2 v)]
  have hsq : ∫ x, inner ℝ u x * inner ℝ v x ∂exponentialFamilyMeasure ν id η =
      (Z η)⁻¹ * ∫ x, Real.exp (inner ℝ η x) * (inner ℝ u x * inner ℝ v x) ∂ν := by
    rw [exponentialFamilyMeasure_def, integral_tilted, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [smul_eq_mul, div_eq_inv_mul, id_eq, Z]
    ring
  dsimp only [Pi.mul_apply]
  rw [hsq, ← h1 u, ← h1 v]
  ring

/-- For a minimal natural exponential family, the Hessian of `logPartition ν id` at every interior
parameter is strictly positive definite. -/
theorem fderiv_fderiv_logPartition_self_pos {ν : Measure E}
    (hmin : IsMinimalExponentialFamily ν id) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) {u : E} (hu : u ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (logPartition ν id)) η u u := by
  have hmem2 := memLp_inner_exponentialFamilyMeasure hη 2 u
  have hmeas : AEMeasurable (fun x : E ↦ inner ℝ u x) (exponentialFamilyMeasure ν id η) :=
    hmem2.aestronglyMeasurable.aemeasurable
  rw [fderiv_fderiv_logPartition_apply ν hη u u, covariance_self hmeas]
  refine lt_of_le_of_ne (variance_nonneg _ _) fun hzero ↦ ?_
  have hevar_top : evariance (fun x ↦ inner ℝ u x) (exponentialFamilyMeasure ν id η) ≠ ⊤ :=
    (hmem2.evariance_lt_top).ne
  have hevar_zero : evariance (fun x ↦ inner ℝ u x) (exponentialFamilyMeasure ν id η) = 0 := by
    have hto : (evariance (fun x ↦ inner ℝ u x) (exponentialFamilyMeasure ν id η)).toReal = 0 :=
      hzero.symm
    exact (ENNReal.toReal_eq_zero_iff _).mp hto |>.resolve_right hevar_top
  have hae_P : ∀ᵐ x ∂exponentialFamilyMeasure ν id η,
      inner ℝ u x = ∫ y, inner ℝ u y ∂exponentialFamilyMeasure ν id η :=
    (evariance_eq_zero_iff hmeas).mp hevar_zero
  have hac : ν ≪ exponentialFamilyMeasure ν id η := by
    rw [exponentialFamilyMeasure_def]
    exact absolutelyContinuous_tilted (mem_naturalParameterSpace_iff.mp (interior_subset hη))
  exact isMinimalExponentialFamily_iff.mp hmin u hu
    (∫ y, inner ℝ u y ∂exponentialFamilyMeasure ν id η) (hac.ae_le hae_P)

end TauCeti
