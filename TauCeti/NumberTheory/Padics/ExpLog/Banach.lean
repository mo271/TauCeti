/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Restricted
public import TauCeti.RingTheory.PowerSeries.EvalAt
import TauCeti.Analysis.Normed.Algebra.Logarithm.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Restricted.Subst

/-!
# The `p`-adic exponential and logarithm on ultrametric Banach `ℚ_p`-algebras

Let `p` be a prime and put `r_0 = p ^ (-1 / (p - 1))`. This file develops the convergence,
Gauss norms, norm-preservation, inverse, and homomorphism identities for `PowerSeries.exp ℚ_[p]`,
`PowerSeries.log ℚ_[p]`, `NormedSpace.exp`, and `NormedSpace.log` on the open disc `‖x‖ < r_0` in
an arbitrary complete ultrametric Banach `ℚ_p`-algebra `A`, without requiring `‖1‖ = 1` or
commutativity (except where commutativity is needed for `exp (x + y)` and `log (u * v)`, which are
stated both for commuting elements and for commutative algebras).

## Main results

* `TauCeti.isRestricted_exp_sub_one_padic`, `TauCeti.isRestricted_exp_padic`,
  `TauCeti.gaussNorm_exp_sub_one_padic`, `TauCeti.isRestricted_log_padic`,
  `TauCeti.gaussNorm_log_padic`: for `0 ≤ ρ < p ^ (-1 / (p - 1))`, the formal `exp` and `log`
  series over `ℚ_[p]` are restricted at `ρ`, and `exp - 1` and `log` have exact Gauss norm `ρ`.
* `TauCeti.ofReal_rpow_le_expSeries_radius_padic` and `TauCeti.isUnit_exp_of_norm_lt_padic`:
  the radius of convergence of `NormedSpace.expSeries ℚ_[p] A` is at least `p ^ (-1 / (p - 1))`,
  so `NormedSpace.exp x` is a unit whenever `‖x‖ < p ^ (-1 / (p - 1))`.
* `TauCeti.norm_exp_sub_one_of_norm_lt_padic`, `TauCeti.norm_log_one_add_of_norm_lt_padic`,
  `TauCeti.norm_log_of_norm_sub_one_lt_padic`: on `‖x‖ < p ^ (-1 / (p - 1))` (resp.
  `‖u - 1‖ < p ^ (-1 / (p - 1))`), `‖exp x - 1‖ = ‖x‖` and `‖log u‖ = ‖u - 1‖`, without
  assuming `‖1‖ = 1`.
* `TauCeti.log_exp_of_norm_lt_padic` and `TauCeti.exp_log_of_norm_sub_one_lt_padic`:
  `NormedSpace.exp` and `NormedSpace.log` are mutually inverse on `‖x‖ < p ^ (-1 / (p - 1))` and
  `‖u - 1‖ < p ^ (-1 / (p - 1))`.
* `TauCeti.exp_nsmul_of_norm_lt_padic`, `TauCeti.exp_add_of_commute_of_norm_lt_padic`,
  `TauCeti.exp_add_of_norm_lt_padic`, `TauCeti.log_mul_of_commute_of_norm_sub_one_lt_padic`,
  `TauCeti.log_mul_of_norm_sub_one_lt_padic`: functional equations on the disc of convergence.
* `TauCeti.algebraMap_padic_log_of_norm_sub_one_lt`: `algebraMap ℚ_[p] A` commutes with
  `NormedSpace.log` on the open unit disc `‖u - 1‖ < 1` in `ℚ_[p]`.

## References

* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Chapter 5, §4.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology
open scoped Nat PowerSeries

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

private theorem rpow_neg_inv_sub_one_pos : (0 : ℝ) < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _

private theorem rpow_neg_inv_sub_one_lt_one : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr (inv_pos.mpr (sub_pos.mpr hp1)))

/-- Sharp Legendre lower bound on `‖m!‖` in `ℚ_[p]`: for `m ≠ 0`,
`(p ^ (-1 / (p - 1))) ^ (m - 1) ≤ ‖(m! : ℚ_[p])‖`. -/
private theorem rpow_pow_pred_le_norm_factorial {m : ℕ} (hm : m ≠ 0) :
    ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1) ≤ ‖(m ! : ℚ_[p])‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsum_pos : 1 ≤ (p.digits m).sum := by
    have hne : p.digits m ≠ [] := by simpa [Nat.digits_eq_nil_iff_eq_zero] using hm
    exact (Nat.one_le_iff_ne_zero.mpr (Nat.getLast_digit_ne_zero p hm)).trans
      (List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (List.getLast_mem hne))
  have hleg : (p - 1) * padicValNat p m ! ≤ m - 1 := by
    rw [Nat.padicValNat_def, Nat.Prime.sub_one_mul_multiplicity_factorial hp.out]
    omega
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    Padic.norm_natCast_eq_zpow (Nat.factorial_ne_zero m), ← Real.rpow_intCast]
  refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
  rw [Int.cast_neg, Int.cast_natCast, neg_mul, neg_le_neg_iff, inv_mul_eq_div,
    le_div_iff₀ (sub_pos.mpr hp1), mul_comm]
  have hleg' : ((p - 1 : ℕ) : ℝ) * (padicValNat p m ! : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast hleg
  rwa [Nat.cast_sub hp.out.one_le, Nat.cast_one] at hleg'

/-- Sharp lower bound on `‖m‖` in `ℚ_[p]`: for `m ≠ 0`,
`(p ^ (-1 / (p - 1))) ^ (m - 1) ≤ ‖(m : ℚ_[p])‖`. -/
private theorem rpow_pow_pred_le_norm_natCast {m : ℕ} (hm : m ≠ 0) :
    ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1) ≤ ‖(m : ℚ_[p])‖ := by
  refine (rpow_pow_pred_le_norm_factorial hm).trans ?_
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hm) le_rfl
  rw [hk, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by simpa using Padic.norm_int_le_one (p := p) (k : ℤ))

omit hp in
private theorem inv_rpow_mul_pow_le {c ρ : ℝ} {m : ℕ} (hm : m ≠ 0) (hρ0 : 0 ≤ ρ)
    (hc : c ≤ (((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1))⁻¹) :
    c * ρ ^ m ≤ (ρ / (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1) * ρ := by
  have hpow : ρ ^ m = ρ ^ (m - 1) * ρ := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
  rw [hpow, div_pow, div_eq_inv_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

private theorem norm_coeff_exp_sub_one_le {m : ℕ} (hm : m ≠ 0) :
    ‖PowerSeries.coeff m (PowerSeries.exp ℚ_[p] - 1)‖ ≤
      (((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1))⁻¹ := by
  rw [map_sub, PowerSeries.coeff_one, ite_eq_right fun h ↦ absurd h hm, sub_zero,
    PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, one_div, norm_inv]
  exact inv_anti₀ (pow_pos rpow_neg_inv_sub_one_pos _) (rpow_pow_pred_le_norm_factorial hm)

private theorem norm_coeff_log_le {m : ℕ} (hm : m ≠ 0) :
    ‖PowerSeries.coeff m (PowerSeries.log ℚ_[p])‖ ≤
      (((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1))⁻¹ := by
  rw [PowerSeries.coeff_log, ite_eq_right fun h ↦ absurd h hm, map_div₀, map_pow, map_neg,
    map_one, map_natCast, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
  exact inv_anti₀ (pow_pos rpow_neg_inv_sub_one_pos _) (rpow_pow_pred_le_norm_natCast hm)

/-- Any series `f ∈ ℚ_[p]⟦X⟧` with `‖coeff m f‖ ≤ r_0 ^ (1 - m)` for `m ≥ 1` is restricted at
every radius `0 ≤ ρ < p ^ (-1 / (p - 1))`. -/
private theorem isRestricted_of_coeff_bound {f : ℚ_[p]⟦X⟧}
    (hfb : ∀ {m : ℕ}, m ≠ 0 →
      ‖PowerSeries.coeff m f‖ ≤ (((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1))⁻¹)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    f.IsRestricted ρ := by
  have hr0 : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := rpow_neg_inv_sub_one_pos
  rw [PowerSeries.isRestricted_iff']
  refine squeeze_zero' (.of_forall fun _ ↦ by positivity) ?_
    (((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ0 hr0.le)
      ((div_lt_one hr0).mpr hρ)).comp (tendsto_sub_atTop_nat 1)).mul_const ρ |>.trans (by simp))
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact inv_rpow_mul_pow_le (by omega) hρ0 (hfb (by omega))

/-- If `f ∈ ℚ_[p]⟦X⟧` satisfies `coeff 0 f = 0`, `coeff 1 f = 1`, and
`‖coeff m f‖ ≤ r_0 ^ (1 - m)` for `m ≥ 1`, then `f.gaussNorm norm ρ = ρ` for
`0 ≤ ρ < p ^ (-1 / (p - 1))`. -/
private theorem gaussNorm_of_coeff_bound {f : ℚ_[p]⟦X⟧}
    (hf0 : PowerSeries.coeff 0 f = 0) (hf1 : PowerSeries.coeff 1 f = 1)
    (hfb : ∀ {m : ℕ}, m ≠ 0 →
      ‖PowerSeries.coeff m f‖ ≤ (((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1))⁻¹)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    f.gaussNorm norm ρ = ρ := by
  have hr0 : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := rpow_neg_inv_sub_one_pos
  have hrest := isRestricted_of_coeff_bound hfb hρ0 hρ
  refine le_antisymm ?_ ?_
  · rw [PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun m ↦ ?_) hρ0
    rcases eq_or_ne m 0 with rfl | hm0
    · simp [hf0, hρ0]
    · refine (inv_rpow_mul_pow_le hm0 hρ0 (hfb hm0)).trans ?_
      exact mul_le_of_le_one_left hρ0
        (pow_le_one₀ (div_nonneg hρ0 hr0.le) ((div_le_one hr0).mpr hρ.le))
  · have h1 := PowerSeries.le_gaussNorm norm ρ f (PowerSeries.hasGaussNorm_of_isRestricted hrest) 1
    simpa [hf1] using h1

/-- The formal series `exp - 1 ∈ ℚ_[p]⟦X⟧` is restricted at every radius
`0 ≤ ρ < p ^ (-1 / (p - 1))`. -/
theorem isRestricted_exp_sub_one_padic {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    (PowerSeries.exp ℚ_[p] - 1).IsRestricted ρ :=
  isRestricted_of_coeff_bound (fun hm ↦ norm_coeff_exp_sub_one_le hm) hρ0 hρ

/-- The formal exponential series `exp ∈ ℚ_[p]⟦X⟧` is restricted at every radius
`0 ≤ ρ < p ^ (-1 / (p - 1))`. -/
theorem isRestricted_exp_padic {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    (PowerSeries.exp ℚ_[p]).IsRestricted ρ := by
  simpa using (isRestricted_exp_sub_one_padic (p := p) hρ0 hρ).add (PowerSeries.isRestricted_one ρ)

/-- For `0 ≤ ρ < p ^ (-1 / (p - 1))`, `exp - 1 ∈ ℚ_[p]⟦X⟧` has exact Gauss norm `ρ`. -/
theorem gaussNorm_exp_sub_one_padic {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    (PowerSeries.exp ℚ_[p] - 1).gaussNorm norm ρ = ρ :=
  gaussNorm_of_coeff_bound (by simp) (by simp [PowerSeries.coeff_exp])
    (fun hm ↦ norm_coeff_exp_sub_one_le hm) hρ0 hρ

/-- The formal logarithm series `log ∈ ℚ_[p]⟦X⟧` is restricted at every radius
`0 ≤ ρ < p ^ (-1 / (p - 1))`. -/
theorem isRestricted_log_padic {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    (PowerSeries.log ℚ_[p]).IsRestricted ρ :=
  isRestricted_of_coeff_bound (fun hm ↦ norm_coeff_log_le hm) hρ0 hρ

/-- For `0 ≤ ρ < p ^ (-1 / (p - 1))`, `log ∈ ℚ_[p]⟦X⟧` has exact Gauss norm `ρ`. -/
theorem gaussNorm_log_padic {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    (PowerSeries.log ℚ_[p]).gaussNorm norm ρ = ρ :=
  gaussNorm_of_coeff_bound (by simp) (by simp [PowerSeries.coeff_log])
    (fun hm ↦ norm_coeff_log_le hm) hρ0 hρ

section TopologicalAlgebra

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℚ_[p] A]

/-- Evaluating the formal exponential series `PowerSeries.exp ℚ_[p]` at `x : A` agrees with
`NormedSpace.exp x`. -/
theorem evalAt_exp_padic (x : A) :
    (PowerSeries.exp ℚ_[p]).evalAt x = NormedSpace.exp x := by
  rw [PowerSeries.evalAt_def, NormedSpace.exp_eq_tsum ℚ_[p]]
  refine tsum_congr fun n ↦ ?_
  rw [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, one_div]

/-- Evaluating the formal logarithm series `PowerSeries.log ℚ_[p]` at `x : A` agrees with
`NormedSpace.log (1 + x)`. -/
theorem evalAt_log_padic (x : A) :
    (PowerSeries.log ℚ_[p]).evalAt x = NormedSpace.log (1 + x) := by
  rw [PowerSeries.evalAt_def, NormedSpace.log_eq_tsum ℚ_[p]]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [PowerSeries.coeff_log, hn, map_div₀, map_pow]

end TopologicalAlgebra

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A]

/-- The radius of convergence of `NormedSpace.expSeries ℚ_[p] A` is at least
`p ^ (-1 / (p - 1))`. -/
theorem ofReal_rpow_le_expSeries_radius_padic :
    ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ≤ (NormedSpace.expSeries ℚ_[p] A).radius := by
  have hr0 : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := rpow_neg_inv_sub_one_pos
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hrlt : (r : ℝ) < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr0] at hr
  refine FormalMultilinearSeries.le_radius_of_bound _
    (max (r : ℝ) ‖NormedSpace.expSeries ℚ_[p] A 0‖) fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · calc ‖NormedSpace.expSeries ℚ_[p] A n‖ * (r : ℝ) ^ n
        ≤ ‖((n ! : ℚ_[p])⁻¹)‖ * (r : ℝ) ^ n := by
          gcongr
          rw [NormedSpace.expSeries_eq_ofScalars]
          exact FormalMultilinearSeries.ofScalars_norm_le A _ n hn
      _ ≤ ((r : ℝ) / (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (n - 1) * (r : ℝ) := by
          rw [norm_inv]
          exact inv_rpow_mul_pow_le hn.ne' r.2
            (inv_anti₀ (pow_pos hr0 _) (rpow_pow_pred_le_norm_factorial hn.ne'))
      _ ≤ (r : ℝ) := mul_le_of_le_one_left r.2
          (pow_le_one₀ (div_nonneg r.2 hr0.le) ((div_le_one hr0).mpr hrlt.le))
      _ ≤ max (r : ℝ) ‖NormedSpace.expSeries ℚ_[p] A 0‖ := le_max_left _ _

/-- Every `x : A` with `‖x‖ < p ^ (-1 / (p - 1))` lies inside the open ball of convergence of
`NormedSpace.expSeries ℚ_[p] A`. -/
theorem mem_eball_expSeries_of_norm_lt_padic {x : A}
    (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    x ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℚ_[p] A).radius := by
  refine Metric.eball_subset_eball (ofReal_rpow_le_expSeries_radius_padic (p := p) (A := A)) ?_
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff rpow_neg_inv_sub_one_pos).mpr hx

/-- For `u : ℚ_[p]` with `‖u - 1‖ < 1`, `algebraMap ℚ_[p] A` commutes with `NormedSpace.log`. -/
theorem algebraMap_padic_log_of_norm_sub_one_lt {u : ℚ_[p]} (hu : ‖u - 1‖ < 1) :
    algebraMap ℚ_[p] A (NormedSpace.log u) = NormedSpace.log (algebraMap ℚ_[p] A u) := by
  have hsum : HasSum (fun n : ℕ ↦ ((-1 : ℚ_[p]) ^ (n + 1) / n) • (u - 1) ^ n)
      (NormedSpace.log u) := by
    rw [NormedSpace.log_eq_tsum ℚ_[p]]
    exact (NormedSpace.logSeries_summable_of_norm_lt_one ℚ_[p] ℚ_[p] hu).hasSum
  have hmap := hsum.map (algebraMap ℚ_[p] A) (continuous_algebraMap ℚ_[p] A)
  rw [← hmap.tsum_eq, NormedSpace.log_eq_tsum ℚ_[p]]
  refine tsum_congr fun n ↦ ?_
  simp only [Function.comp_def, smul_eq_mul, map_mul, map_pow, map_sub, map_one, Algebra.smul_def]

variable [CompleteSpace A]

/-- For `‖x‖ < p ^ (-1 / (p - 1))`, `NormedSpace.exp x` is a unit of `A`. -/
theorem isUnit_exp_of_norm_lt_padic {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    IsUnit (NormedSpace.exp x) :=
  NormedSpace.isUnit_exp_of_mem_ball (mem_eball_expSeries_of_norm_lt_padic hx)

/-- For commuting elements `x, y : A` with `‖x‖, ‖y‖ < p ^ (-1 / (p - 1))`,
`exp (x + y) = exp x * exp y`. -/
theorem exp_add_of_commute_of_norm_lt_padic {x y : A} (hxy : Commute x y)
    (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_commute_of_mem_ball hxy (mem_eball_expSeries_of_norm_lt_padic hx)
    (mem_eball_expSeries_of_norm_lt_padic hy)

variable [IsUltrametricDist A]

/-- Any series `f ∈ ℚ_[p]⟦X⟧` with `coeff 0 = 0`, `coeff 1 = 1`, and
`‖coeff m‖ ≤ r_0 ^ (1 - m)` preserves norms on `‖x‖ < p ^ (-1 / (p - 1))` in `A`, without
requiring `‖1‖ = 1`. -/
private theorem norm_evalAt_of_coeff_bound {f : ℚ_[p]⟦X⟧}
    (hf0 : PowerSeries.coeff 0 f = 0) (hf1 : PowerSeries.coeff 1 f = 1)
    (hfb : ∀ {m : ℕ}, m ≠ 0 →
      ‖PowerSeries.coeff m f‖ ≤ (((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (m - 1))⁻¹)
    {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖f.evalAt x‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [PowerSeries.evalAt_at_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
  have hr0 : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := rpow_neg_inv_sub_one_pos
  have hsum := (isRestricted_of_coeff_bound hfb (norm_nonneg x) hx).hasSum_evalAt (b := x) le_rfl
  have htail : HasSum (fun n : ℕ ↦ PowerSeries.coeff (n + 2) f • x ^ (n + 2)) (f.evalAt x - x) := by
    have h2 := (hasSum_nat_add_iff' 2).mpr hsum
    simpa [Finset.sum_range_succ, hf0, hf1] using h2
  have hbound (n : ℕ) :
      ‖PowerSeries.coeff (n + 2) f • x ^ (n + 2)‖ ≤
        (‖x‖ / (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) * ‖x‖ := by
    rw [norm_smul]
    refine (mul_le_mul_of_nonneg_left (norm_pow_le' x (by omega)) (norm_nonneg _)).trans ?_
    refine (inv_rpow_mul_pow_le (by omega) (norm_nonneg x) (hfb (by omega))).trans ?_
    gcongr
    exact pow_le_of_le_one (div_nonneg (norm_nonneg x) hr0.le) ((div_le_one hr0).mpr hx.le)
      (by omega)
  have htail_lt : ‖f.evalAt x - x‖ < ‖x‖ := by
    rw [← htail.tsum_eq]
    exact (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) hbound).trans_lt
      (mul_lt_of_lt_one_left (norm_pos_iff.mpr hx0) ((div_lt_one hr0).mpr hx))
  have hsplit : f.evalAt x = x + (f.evalAt x - x) := by abel
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm htail_lt.ne',
    max_eq_left htail_lt.le]

/-- Evaluating `PowerSeries.exp ℚ_[p] - 1` at `x : A` with `‖x‖ < p ^ (-1 / (p - 1))` gives
`NormedSpace.exp x - 1`. -/
theorem evalAt_exp_sub_one_padic {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    (PowerSeries.exp ℚ_[p] - 1).evalAt x = NormedSpace.exp x - 1 := by
  have hhom := map_sub (PowerSeries.IsRestricted.evalAtHom (A := A) ℚ_[p] (b := x) le_rfl)
    ⟨PowerSeries.exp ℚ_[p], isRestricted_exp_padic (norm_nonneg x) hx⟩
    ⟨1, PowerSeries.isRestricted_one ‖x‖⟩
  simpa [evalAt_exp_padic] using hhom

/-- On `‖x‖ < p ^ (-1 / (p - 1))` in an ultrametric Banach `ℚ_[p]`-algebra,
`‖exp x - 1‖ = ‖x‖`, without assuming `‖1‖ = 1`. -/
theorem norm_exp_sub_one_of_norm_lt_padic {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - 1‖ = ‖x‖ := by
  rw [← evalAt_exp_sub_one_padic hx]
  exact norm_evalAt_of_coeff_bound (by simp) (by simp [PowerSeries.coeff_exp])
    (fun hm ↦ norm_coeff_exp_sub_one_le hm) hx

/-- On `‖u‖ < p ^ (-1 / (p - 1))` in an ultrametric Banach `ℚ_[p]`-algebra,
`‖log (1 + u)‖ = ‖u‖`, without assuming `‖1‖ = 1`. -/
theorem norm_log_one_add_of_norm_lt_padic {u : A} (hu : ‖u‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.log (1 + u)‖ = ‖u‖ := by
  rw [← evalAt_log_padic (p := p) u]
  exact norm_evalAt_of_coeff_bound (by simp) (by simp [PowerSeries.coeff_log])
    (fun hm ↦ norm_coeff_log_le hm) hu

/-- On `‖u - 1‖ < p ^ (-1 / (p - 1))` in an ultrametric Banach `ℚ_[p]`-algebra,
`‖log u‖ = ‖u - 1‖`, without assuming `‖1‖ = 1`. -/
theorem norm_log_of_norm_sub_one_lt_padic {u : A} (hu : ‖u - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.log u‖ = ‖u - 1‖ := by
  simpa only [add_sub_cancel] using norm_log_one_add_of_norm_lt_padic hu

/-- On `‖x‖ < p ^ (-1 / (p - 1))`, `log (exp x) = x`. -/
theorem log_exp_of_norm_lt_padic {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.log (NormedSpace.exp x) = x := by
  have hev := PowerSeries.IsRestricted.evalAt_subst (R := ℚ_[p]) (S := ℚ_[p]) (A := A)
    (isRestricted_log_padic (norm_nonneg x) hx) (isRestricted_exp_sub_one_padic (norm_nonneg x) hx)
    (by simp) (norm_nonneg x) (gaussNorm_exp_sub_one_padic (norm_nonneg x) hx).le (x := x) le_rfl
  rw [PowerSeries.subst_log_exp_sub_one, PowerSeries.evalAt_X, evalAt_exp_sub_one_padic hx,
    evalAt_log_padic, add_sub_cancel] at hev
  exact hev.symm

/-- On `‖u - 1‖ < p ^ (-1 / (p - 1))`, `exp (log u) = u`. -/
theorem exp_log_of_norm_sub_one_lt_padic {u : A} (hu : ‖u - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (NormedSpace.log u) = u := by
  set x := u - 1
  have hev := PowerSeries.IsRestricted.evalAt_subst (R := ℚ_[p]) (S := ℚ_[p]) (A := A)
    (isRestricted_exp_padic (norm_nonneg x) hu) (isRestricted_log_padic (norm_nonneg x) hu)
    PowerSeries.constantCoeff_log (norm_nonneg x) (gaussNorm_log_padic (norm_nonneg x) hu).le
    (x := x) le_rfl
  rw [PowerSeries.subst_exp_log, evalAt_log_padic, evalAt_exp_padic] at hev
  have hlhs : ((1 + PowerSeries.X : ℚ_[p]⟦X⟧)).evalAt x = 1 + x := by
    have hX : (PowerSeries.X : ℚ_[p]⟦X⟧).IsRestricted ‖x‖ :=
      MvPowerSeries.isRestricted_X (fun _ ↦ ‖x‖) ()
    simpa using PowerSeries.IsRestricted.evalAt_add (PowerSeries.isRestricted_one ‖x‖) hX
      (b := x) le_rfl
  rw [hlhs, add_sub_cancel] at hev
  exact hev.symm

/-- For `‖x‖ < p ^ (-1 / (p - 1))` and `n : ℕ`, `exp (n • x) = exp x ^ n`. -/
theorem exp_nsmul_of_norm_lt_padic {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    NormedSpace.exp (n • x) = NormedSpace.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : ‖n • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
      (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx
    rw [succ_nsmul, exp_add_of_commute_of_norm_lt_padic ((Commute.refl x).smul_left n) hn hx,
      ih, pow_succ]

/-- For commuting elements `u, v : A` with `‖u - 1‖, ‖v - 1‖ < p ^ (-1 / (p - 1))`,
`log (u * v) = log u + log v`. -/
theorem log_mul_of_commute_of_norm_sub_one_lt_padic {u v : A} (huv : Commute u v)
    (hu : ‖u - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hv : ‖v - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.log (u * v) = NormedSpace.log u + NormedSpace.log v := by
  have hlu : ‖NormedSpace.log u‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rwa [norm_log_of_norm_sub_one_lt_padic hu]
  have hlv : ‖NormedSpace.log v‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rwa [norm_log_of_norm_sub_one_lt_padic hv]
  have hsum : ‖NormedSpace.log u + NormedSpace.log v‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hlu hlv)
  have hcomm_log : Commute (NormedSpace.log u) (NormedSpace.log v) := by
    have hcomm_tsum {a b : A} (hab : Commute a b) (hb : ‖b - 1‖ < 1) :
        Commute a (NormedSpace.log b) := by
      have hhs : HasSum (fun n : ℕ ↦ ((-1 : ℚ_[p]) ^ (n + 1) / n) • (b - 1) ^ n)
          (NormedSpace.log b) := by
        rw [NormedSpace.log_eq_tsum ℚ_[p]]
        exact (NormedSpace.logSeries_summable_of_norm_lt_one ℚ_[p] A hb).hasSum
      have hL := hhs.map (AddMonoidHom.mulLeft a) (continuous_const_mul a)
      have hR := hhs.map (AddMonoidHom.mulRight a) (continuous_mul_const a)
      have hterm : (AddMonoidHom.mulLeft a ∘ fun n : ℕ ↦ ((-1 : ℚ_[p]) ^ (n + 1) / n) •
          (b - 1) ^ n) = (AddMonoidHom.mulRight a ∘ fun n : ℕ ↦
            ((-1 : ℚ_[p]) ^ (n + 1) / n) • (b - 1) ^ n) := by
        funext n
        simp only [Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.mulRight_apply,
          mul_smul_comm, smul_mul_assoc]
        congr 1
        exact (hab.sub_right (Commute.one_right a)).pow_right n
      rw [hterm] at hL
      exact hL.unique hR
    have h1 : Commute u (NormedSpace.log v) :=
      hcomm_tsum huv (hv.trans rpow_neg_inv_sub_one_lt_one)
    exact (hcomm_tsum h1.symm (hu.trans rpow_neg_inv_sub_one_lt_one)).symm
  have hexp : NormedSpace.exp (NormedSpace.log u + NormedSpace.log v) = u * v := by
    rw [exp_add_of_commute_of_norm_lt_padic hcomm_log hlu hlv,
      exp_log_of_norm_sub_one_lt_padic hu, exp_log_of_norm_sub_one_lt_padic hv]
  rw [← hexp, log_exp_of_norm_lt_padic hsum]

end BanachAlgebra

section CommBanachAlgebra

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]

/-- In a commutative Banach `ℚ_[p]`-algebra, `exp (x + y) = exp x * exp y` for
`‖x‖, ‖y‖ < p ^ (-1 / (p - 1))`. -/
theorem exp_add_of_norm_lt_padic {x y : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  exp_add_of_commute_of_norm_lt_padic (Commute.all x y) hx hy

/-- In a commutative ultrametric Banach `ℚ_[p]`-algebra, `log (u * v) = log u + log v` for
`‖u - 1‖, ‖v - 1‖ < p ^ (-1 / (p - 1))`. -/
theorem log_mul_of_norm_sub_one_lt_padic [IsUltrametricDist A] {u v : A}
    (hu : ‖u - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hv : ‖v - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.log (u * v) = NormedSpace.log u + NormedSpace.log v :=
  log_mul_of_commute_of_norm_sub_one_lt_padic (Commute.all u v) hu hv

end CommBanachAlgebra

end TauCeti
