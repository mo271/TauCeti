/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Restricted
public import TauCeti.NumberTheory.Padics.WeightSpace.AnalyticLevel
public import TauCeti.RingTheory.PowerSeries.EvalAt
import Mathlib.Analysis.Normed.Ring.Units
import TauCeti.Analysis.Normed.Ring.CompactMonoid
import TauCeti.Analysis.Normed.Ring.UnitBall
import TauCeti.NumberTheory.Padics.ExpLog.Banach
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Restricted.Subst

/-!
# Scalar analytic factors of locally analytic weights

Let `p` be a prime, put `k = TauCeti.padicUnitsDepth p` (so `k = 1` for odd `p` and `k = 2` for
`p = 2`), and for `j : ℕ` set `h = k + j`. Let `A` be a complete ultrametric commutative Banach
algebra over `ℚ_p`, and let `κ : ℤ_pˣ →ₜ* Aˣ` be a weight satisfying the level-`h` analyticity
criterion

`‖κ(exp (p ^ h)) - 1‖ < r_0 = p ^ (-1 / (p - 1))`,

where `exp (p ^ h) = γ ^ (p ^ j)` (`TauCeti.WeightSpace.levelCoord`). This file extends `κ`
analytically from `ℤ_pˣ` to the subgroup `ℤ_pˣ (1 + pʰ 𝒪_A)` of `Aˣ`, constructs the restricted
power series expanding the scalar automorphic factor `z ↦ κ(c z + d)`, and establishes its
convergence radii, Gauss norm, coefficient bounds, and algebraic-weight specialization.

## Construction

1. **Extended domain.** The principal unit ball `1 + pʰ 𝒪_A`
   (`TauCeti.WeightSpace.principalUnitsBall p h A`) is a subgroup of `Aˣ`, and together with the
   image of `ℤ_pˣ` it generates the subgroup `ℤ_pˣ (1 + pʰ 𝒪_A) ≤ Aˣ`
   (`TauCeti.WeightSpace.extendedDomain p h A`). Multiplication by any element of this subgroup
   preserves norms in `A`, even without `‖1‖ = 1` (`TauCeti.WeightSpace.norm_mul_extendedDomain`).
2. **Analytic extension.** Define the slope `α = p⁻ʰ log (κ(exp (p ^ h)))`
   (`TauCeti.WeightSpace.weightSlope`). On `1 + pʰ 𝒪_A`, the map `u ↦ exp (α log u)`
   (`TauCeti.WeightSpace.principalExt`, bundled as `TauCeti.WeightSpace.principalExtHom`) is a group
   homomorphism whose values satisfy `‖principalExt u - 1‖ = ‖α log u‖ ≤ ‖t_h‖ < r_0 < 1` and
   `‖principalExt u‖ = ‖(1 : A)‖`. Continuity and density of `ℕ` in `ℤ_p` show that it agrees with
   `κ` on `1 + pʰ ℤ_p`, so `κ` and `principalExtHom` glue uniquely to a homomorphism
   `TauCeti.WeightSpace.extendedWeight : ℤ_pˣ (1 + pʰ 𝒪_A) →* Aˣ`.
3. **Scalar factor expansion.** For `d ∈ ℤ_pˣ (1 + pʰ 𝒪_A)` and `c ∈ A`, we expand
   `κ(c z + d) = κ(d) exp (α log (1 + c d⁻¹ z))` by composing restricted power series
   (`TauCeti.WeightSpace.scalarFactorSeries`). For every radius `r ≥ 0` satisfying

   `r ‖c‖ < r_0` and `r ‖c‖ ‖t_h‖ < p⁻ʰ r_0`,

   the series is restricted at `r`, has exact Gauss norm `‖κ(d)‖` (which equals `‖κ(d₀)‖` when
   `d = d₀ u₀` with `d₀ ∈ ℤ_pˣ` and `u₀ ∈ 1 + pʰ 𝒪_A`), has coefficients bounded by
   `‖a_n‖ ≤ ‖κ(d)‖ r⁻ⁿ` (for `r > 0`), and evaluates to `κ(d) exp (α log (1 + c d⁻¹ z))` on
   `‖z‖ ≤ r`. When `‖c‖ ≤ p⁻ʰ`, the radius `r = 1` satisfies these inequalities, and on `‖z‖ ≤ 1`
   the series evaluates to `extendedWeight (c z + d)`.
4. **Multiplicative norms and fields.** When `A` has a multiplicative norm with `‖1‖ = 1` (for
   instance any complete ultrametric normed field extension of `ℚ_p`), compactness of `ℤ_pˣ` forces
   `‖κ(x)‖ = 1` for all `x ∈ ℤ_pˣ` (`ContinuousMonoidHom.norm_apply_eq_one_of_compactSpace`), hence
   `‖extendedWeight d‖ = 1`, Gauss norm equal to `1` on the closed unit disc and at every admissible
   radius `r`, and coefficient bounds `‖a_n‖ ≤ r⁻ⁿ`.
5. **Nonnegative algebraic weights.** For `κ(x) = x ^ k` (`k : ℕ`), `weightSlope` equals `k`, the
   extended weight is `d ↦ d ^ k`, and `scalarFactorSeries` coincides formally with the polynomial
   `(d + c X) ^ k`, evaluating to `(c z + d) ^ k` everywhere.

## Main definitions

* `TauCeti.WeightSpace.principalUnitsBall`: the subgroup `1 + pʰ 𝒪_A ≤ Aˣ`.
* `TauCeti.WeightSpace.extendedDomain`: the subgroup `ℤ_pˣ (1 + pʰ 𝒪_A) ≤ Aˣ`.
* `TauCeti.WeightSpace.levelCoord`: the level-`h` coordinate `t_h = κ(exp (p ^ h)) - 1`.
* `TauCeti.WeightSpace.weightSlope`: the analytic slope `p⁻ʰ log (1 + t_h)`.
* `TauCeti.WeightSpace.principalExt` and `TauCeti.WeightSpace.principalExtHom`: the analytic
  extension of `κ` to `1 + pʰ 𝒪_A`.
* `TauCeti.WeightSpace.extendedWeight`: the extension of `κ` to `ℤ_pˣ (1 + pʰ 𝒪_A)`.
* `TauCeti.WeightSpace.scalarFactorSeries`: the power series expanding `z ↦ κ(c z + d)`.

## Main results

* `TauCeti.WeightSpace.extendedWeight_unique`: uniqueness of `extendedWeight` as a homomorphism
  extending `κ` and `principalExtHom`.
* `TauCeti.WeightSpace.norm_principalExt_sub_one`,
  `TauCeti.WeightSpace.norm_principalExt_sub_one_le`, `TauCeti.WeightSpace.norm_principalExt`,
  `TauCeti.WeightSpace.norm_extendedWeight_mk`: Banach-algebra norm identities and bounds for the
  analytic character and constant factor.
* `TauCeti.WeightSpace.norm_extendedWeight_eq_one`: the extended weight has unit norm for
  multiplicative norms with `‖1‖ = 1`.
* `TauCeti.WeightSpace.isRestricted_scalarFactorSeries`,
  `TauCeti.WeightSpace.gaussNorm_scalarFactorSeries`,
  `TauCeti.WeightSpace.norm_coeff_scalarFactorSeries_le`,
  `TauCeti.WeightSpace.evalAt_scalarFactorSeries`: convergence, exact Gauss norm, coefficient
  bounds, and evaluation of `scalarFactorSeries` at any admissible radius `r ≥ 0`.
* `TauCeti.WeightSpace.isRestricted_scalarFactorSeries_one`,
  `TauCeti.WeightSpace.gaussNorm_scalarFactorSeries_one`,
  `TauCeti.WeightSpace.evalAt_scalarFactorSeries_eq_extendedWeight`,
  `TauCeti.WeightSpace.evalAt_scalarFactorSeries_padicInt`: specialization to the closed unit disc
  when `‖c‖ ≤ p⁻ʰ`.
* `TauCeti.WeightSpace.gaussNorm_scalarFactorSeries_eq_one`,
  `TauCeti.WeightSpace.gaussNorm_scalarFactorSeries_one_eq_one`,
  `TauCeti.WeightSpace.norm_coeff_scalarFactorSeries_le_inv_pow`: unit Gauss norm and `r⁻ⁿ`
  coefficient bounds for multiplicative norms.
* `TauCeti.WeightSpace.scalarFactorSeries_inclusion_pow` and
  `TauCeti.WeightSpace.evalAt_scalarFactorSeries_inclusion_pow`: agreement with `(c z + d) ^ k` for
  nonnegative algebraic weights.

## References

* G. Stevens, *Rigid analytic modular symbols*, preprint (1994).
* R. Pollack and G. Stevens, *Overconvergent modular symbols and p-adic L-functions*, Ann. Sci. Éc.
  Norm. Supér. 44 (2011), §3.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra
  Number Theory 13 (2019), §2.
-/

public section

open Filter Topology
open scoped Nat PowerSeries

namespace TauCeti.WeightSpace

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Private radius bridges and normalized power series `exp (α log (1 + w X))` -/

section ExpLogSeries

omit hp in
private theorem amiceRadius_zero_eq :
    amiceRadius p 0 = (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  rw [amiceRadius_def, pow_zero, mul_one, one_div]

/-- For every `j : ℕ`, `p ^ (-(padicUnitsDepth p + j)) < amiceRadius p 0`. -/
private theorem zpow_neg_padicUnitsDepth_add_lt_amiceRadius (j : ℕ) :
    (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) < amiceRadius p 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsub : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
  have hk : (1 : ℝ) < ((p : ℝ) - 1) * (padicUnitsDepth p : ℝ) := by
    have := (Nat.one_lt_cast (α := ℝ)).mpr (one_lt_sub_one_mul_padicUnitsDepth (p := p))
    rwa [Nat.cast_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one] at this
  have hle : (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) ≤
      (p : ℝ) ^ (-(padicUnitsDepth p : ℤ)) :=
    zpow_le_zpow_right₀ hp1.le (by omega)
  refine hle.trans_lt ?_
  rw [amiceRadius_def, ← Real.rpow_intCast]
  refine Real.rpow_lt_rpow_of_exponent_lt hp1 ?_
  rw [pow_zero, mul_one, Int.cast_neg, Int.cast_natCast, neg_lt_neg_iff, div_lt_iff₀ hsub]
  linarith

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A]

/-- The formal power series `exp (α log (1 + w X))` in `A⟦X⟧`. -/
private noncomputable def expLogSeries (α w : A) : A⟦X⟧ :=
  (PowerSeries.exp ℚ_[p]).subst
    (PowerSeries.C α * (PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X))

private theorem constantCoeff_log_subst_C_mul_X (w : A) :
    PowerSeries.constantCoeff
      ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X) : A⟦X⟧) = 0 := by
  rw [PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero
      (by rw [← PowerSeries.constantCoeff_eq]; simp),
    PowerSeries.constantCoeff_log, map_zero]

private theorem constantCoeff_expLogSeries (α w : A) :
    PowerSeries.constantCoeff (expLogSeries (p := p) α w) = 1 := by
  rw [expLogSeries, PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero
      (by rw [← PowerSeries.constantCoeff_eq]; simp [constantCoeff_log_subst_C_mul_X]),
    PowerSeries.constantCoeff_exp, map_one]

section Estimates

variable [IsUltrametricDist A]

private theorem isRestricted_C_mul_X {r : ℝ} (w : A) :
    (PowerSeries.C w * PowerSeries.X : A⟦X⟧).IsRestricted r :=
  (PowerSeries.isRestricted_C r w).mul (MvPowerSeries.isRestricted_X (fun _ ↦ r) ())

private theorem gaussNorm_C_mul_X {r : ℝ} (hr : 0 ≤ r) (w : A) :
    (PowerSeries.C w * PowerSeries.X : A⟦X⟧).gaussNorm norm r = r * ‖w‖ := by
  refine le_antisymm ?_ ?_
  · rw [PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun n ↦ ?_) (by positivity)
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    split_ifs with h
    · subst h; simp [mul_comm]
    · simp [mul_nonneg hr (norm_nonneg w)]
  · have h1 := PowerSeries.le_gaussNorm norm r (PowerSeries.C w * PowerSeries.X)
      (PowerSeries.hasGaussNorm_of_isRestricted (isRestricted_C_mul_X w)) 1
    simpa [mul_comm] using h1

private theorem isRestricted_C_mul_log_subst {α w : A} {r : ℝ} (hr : 0 ≤ r)
    (h1 : r * ‖w‖ < amiceRadius p 0) :
    (PowerSeries.C α * (PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X) :
      A⟦X⟧).IsRestricted r := by
  rw [amiceRadius_zero_eq] at h1
  exact (PowerSeries.isRestricted_C r α).mul
    (PowerSeries.IsRestricted.subst (isRestricted_log_padic (by positivity) h1)
      (isRestricted_C_mul_X w) (by simp) hr (gaussNorm_C_mul_X hr w).le)

private theorem gaussNorm_C_mul_log_subst_le {α w : A} {r : ℝ} (hr : 0 ≤ r)
    (h1 : r * ‖w‖ < amiceRadius p 0) :
    (PowerSeries.C α * (PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X) :
      A⟦X⟧).gaussNorm norm r ≤ r * ‖w‖ * ‖α‖ := by
  rw [amiceRadius_zero_eq] at h1
  have hX : (PowerSeries.C w * PowerSeries.X : A⟦X⟧).HasGaussNorm norm r :=
    PowerSeries.hasGaussNorm_of_isRestricted (isRestricted_C_mul_X w)
  have hlog : (PowerSeries.log ℚ_[p]).HasGaussNorm norm (r * ‖w‖) :=
    PowerSeries.hasGaussNorm_of_isRestricted (isRestricted_log_padic (by positivity) h1)
  have hL_has : PowerSeries.HasGaussNorm norm r
      ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X)) :=
    PowerSeries.hasGaussNorm_subst (by simp) hr hlog hX (gaussNorm_C_mul_X hr w).le
  have hL_le : PowerSeries.gaussNorm norm r
      ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X)) ≤ r * ‖w‖ := by
    refine (PowerSeries.gaussNorm_subst_le_max (by simp) hr hlog hX
      (gaussNorm_C_mul_X hr w).le).trans ?_
    simp [gaussNorm_log_padic (by positivity) h1, mul_nonneg hr (norm_nonneg w)]
  rw [PowerSeries.gaussNorm_eq]
  refine Real.iSup_le (fun n ↦ ?_) (by positivity)
  rw [PowerSeries.coeff_C_mul]
  calc ‖α * PowerSeries.coeff n
          ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X))‖ * r ^ n
      ≤ ‖α‖ * (‖PowerSeries.coeff n
          ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X))‖ * r ^ n) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (pow_nonneg hr n)
    _ ≤ ‖α‖ * PowerSeries.gaussNorm norm r
          ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X)) :=
        mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm r _ hL_has n) (norm_nonneg α)
    _ ≤ ‖α‖ * (r * ‖w‖) := mul_le_mul_of_nonneg_left hL_le (norm_nonneg α)
    _ = r * ‖w‖ * ‖α‖ := mul_comm _ _

private theorem isRestricted_expLogSeries {α w : A} {r : ℝ} (hr : 0 ≤ r)
    (h1 : r * ‖w‖ < amiceRadius p 0) (h2 : r * ‖w‖ * ‖α‖ < amiceRadius p 0) :
    PowerSeries.IsRestricted r (expLogSeries (p := p) α w) :=
  PowerSeries.IsRestricted.subst
    (isRestricted_exp_padic (by positivity) (by rwa [← amiceRadius_zero_eq]))
    (isRestricted_C_mul_log_subst hr h1) (by simp [constantCoeff_log_subst_C_mul_X]) hr
    (gaussNorm_C_mul_log_subst_le hr h1)

private theorem norm_coeff_expLogSeries_mul_pow_le {α w : A} {r : ℝ} (hr : 0 ≤ r)
    (h1 : r * ‖w‖ < amiceRadius p 0) (h2 : r * ‖w‖ * ‖α‖ < amiceRadius p 0)
    {n : ℕ} (hn : n ≠ 0) :
    ‖PowerSeries.coeff n (expLogSeries (p := p) α w)‖ * r ^ n ≤ r * ‖w‖ * ‖α‖ := by
  have h2' : r * ‖w‖ * ‖α‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by rwa [← amiceRadius_zero_eq]
  have hexp : (PowerSeries.exp ℚ_[p]).HasGaussNorm norm (r * ‖w‖ * ‖α‖) :=
    PowerSeries.hasGaussNorm_of_isRestricted (isRestricted_exp_padic (by positivity) h2')
  have hg := PowerSeries.hasGaussNorm_of_isRestricted (isRestricted_C_mul_log_subst (α := α) hr h1)
  have h := PowerSeries.norm_coeff_subst_mul_pow_le_sub_const
    (by simp [constantCoeff_log_subst_C_mul_X]) hr hexp hg
    (gaussNorm_C_mul_log_subst_le hr h1) hn
  simpa [expLogSeries, gaussNorm_exp_sub_one_padic (by positivity) h2'] using h

private theorem evalAt_expLogSeries [CompleteSpace A] {α w z : A} {r : ℝ} (hr : 0 ≤ r)
    (h1 : r * ‖w‖ < amiceRadius p 0) (h2 : r * ‖w‖ * ‖α‖ < amiceRadius p 0) (hz : ‖z‖ ≤ r) :
    PowerSeries.evalAt (expLogSeries (p := p) α w) z =
      NormedSpace.exp (α * NormedSpace.log (1 + w * z)) := by
  have h1' : r * ‖w‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by rwa [← amiceRadius_zero_eq]
  have h2' : r * ‖w‖ * ‖α‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by rwa [← amiceRadius_zero_eq]
  have hX : (PowerSeries.C w * PowerSeries.X : A⟦X⟧).IsRestricted r :=
    isRestricted_C_mul_X w
  have hL : PowerSeries.IsRestricted r
      ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X)) :=
    PowerSeries.IsRestricted.subst (isRestricted_log_padic (by positivity) h1') hX (by simp) hr
      (gaussNorm_C_mul_X hr w).le
  have hX_ev : (PowerSeries.C w * PowerSeries.X : A⟦X⟧).evalAt z = w * z := by
    have hXr : (PowerSeries.X : A⟦X⟧).IsRestricted r := MvPowerSeries.isRestricted_X (fun _ ↦ r) ()
    rw [PowerSeries.IsRestricted.evalAt_mul (PowerSeries.isRestricted_C r w) hXr hz,
      PowerSeries.evalAt_C, PowerSeries.evalAt_X]
    simp
  have hL_ev : PowerSeries.evalAt
      ((PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X)) z =
      NormedSpace.log (1 + w * z) := by
    rw [PowerSeries.IsRestricted.evalAt_subst (isRestricted_log_padic (by positivity) h1') hX
      (by simp) hr (gaussNorm_C_mul_X hr w).le hz, hX_ev, evalAt_log_padic]
  have hαL_ev : PowerSeries.evalAt
      (PowerSeries.C α * (PowerSeries.log ℚ_[p]).subst (PowerSeries.C w * PowerSeries.X)) z =
      α * NormedSpace.log (1 + w * z) := by
    rw [PowerSeries.IsRestricted.evalAt_mul (PowerSeries.isRestricted_C r α) hL hz,
      PowerSeries.evalAt_C, hL_ev]
    simp
  rw [expLogSeries, PowerSeries.IsRestricted.evalAt_subst
    (isRestricted_exp_padic (by positivity) h2') (isRestricted_C_mul_log_subst hr h1)
    (by simp [constantCoeff_log_subst_C_mul_X]) hr (gaussNorm_C_mul_log_subst_le hr h1) hz,
    hαL_ev, evalAt_exp_padic]

end Estimates

/-- For a natural number `k`, the formal series `expLogSeries k w` equals `(1 + C w * X) ^ k`. -/
private theorem expLogSeries_natCast (k : ℕ) (w : A) :
    expLogSeries (p := p) (k : A) w = (1 + PowerSeries.C w * PowerSeries.X) ^ k := by
  let _ : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℚ_[p])
  have hlog_eq (g : A⟦X⟧) (hg : PowerSeries.constantCoeff g = 0) :
      ((PowerSeries.log ℚ_[p]).subst g : A⟦X⟧) = (PowerSeries.log A).subst g := by
    ext n
    rw [PowerSeries.coeff_subst_eq_sum_range _ hg, PowerSeries.coeff_subst_eq_sum_range _ hg]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [PowerSeries.coeff_log, PowerSeries.coeff_log, Algebra.smul_def, Algebra.smul_def]
    split_ifs with hm
    · simp
    · congr 1
  have hexp_eq (g : A⟦X⟧) (hg : PowerSeries.constantCoeff g = 0) :
      ((PowerSeries.exp ℚ_[p]).subst g : A⟦X⟧) = (PowerSeries.exp A).subst g := by
    ext n
    rw [PowerSeries.coeff_subst_eq_sum_range _ hg, PowerSeries.coeff_subst_eq_sum_range _ hg]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [PowerSeries.coeff_exp, PowerSeries.coeff_exp, Algebra.smul_def, Algebra.smul_def]
    rfl
  have hpow_log :
      PowerSeries.logOf ((1 + PowerSeries.C w * PowerSeries.X) ^ k) =
        k • PowerSeries.logOf (1 + PowerSeries.C w * PowerSeries.X) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, PowerSeries.logOf_mul (by simp) (by simp), ih, succ_nsmul]
  have hconst_log :
      PowerSeries.constantCoeff
        (PowerSeries.C (k : A) * (PowerSeries.log A).subst (PowerSeries.C w * PowerSeries.X)) =
        0 := by
    rw [map_mul, ← hlog_eq _ (by simp), constantCoeff_log_subst_C_mul_X, mul_zero]
  rw [expLogSeries, hlog_eq _ (by simp), hexp_eq _ hconst_log]
  have h1 : (PowerSeries.log A).subst (PowerSeries.C w * PowerSeries.X) =
      PowerSeries.logOf (1 + PowerSeries.C w * PowerSeries.X) := by
    rw [PowerSeries.logOf_eq, add_sub_cancel_left]
  rw [h1, map_natCast, ← nsmul_eq_mul, ← hpow_log, PowerSeries.subst_exp_logOf (by simp)]

end ExpLogSeries

/-! ### Principal unit balls and extended weight domains -/

section Domains

variable (p) in
/-- **The principal unit ball `1 + pʰ 𝒪_A`** of an ultrametric normed ring `A`: the subgroup of
`Aˣ` consisting of units whose distance (together with that of their inverse) to `1` is at most
`p ^ (-h)`. For `h ≠ 0` and convergent geometric series, the bound on the inverse is automatic
(`TauCeti.WeightSpace.mem_principalUnitsBall_iff_norm_sub_one_le`). -/
def principalUnitsBall (h : ℕ) (A : Type*) [NormedRing A] [IsUltrametricDist A] : Subgroup Aˣ where
  carrier := {u : Aˣ |
    ‖(u : A) - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ)) ∧ ‖((u⁻¹ : Aˣ) : A) - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ))}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have hM1 : (p : ℝ) ^ (-(h : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)
    have hstep {a b : A} (ha : ‖a - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ)))
        (hb : ‖b - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ))) :
        ‖a * b - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ)) := by
      have hid : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        abel
      rw [hid]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine (norm_mul_le _ _).trans ((mul_le_mul ha hb (norm_nonneg _)
          (zpow_nonneg (Nat.cast_nonneg p) _)).trans ?_)
        exact mul_le_of_le_one_right (zpow_nonneg (Nat.cast_nonneg p) _) hM1
      · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    exact ⟨hstep hu.1 hv.1, by simpa [mul_inv_rev] using hstep hv.2 hu.2⟩
  inv_mem' {u} hu := by
    simpa only [Set.mem_ofPred_eq, inv_inv] using And.symm hu

/-- Membership in `principalUnitsBall p h A` in terms of the norms of `u - 1` and `u⁻¹ - 1`. -/
theorem mem_principalUnitsBall {h : ℕ} {A : Type*} [NormedRing A] [IsUltrametricDist A]
    {u : Aˣ} :
    u ∈ principalUnitsBall p h A ↔
      ‖(u : A) - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ)) ∧ ‖((u⁻¹ : Aˣ) : A) - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ)) :=
  Iff.rfl

/-- For `h ≠ 0` in an ultrametric normed ring with summable geometric series, a unit belongs to
`1 + pʰ 𝒪_A` iff `‖(u : A) - 1‖ ≤ p ^ (-h)`. -/
theorem mem_principalUnitsBall_iff_norm_sub_one_le {h : ℕ} {A : Type*} [NormedRing A]
    [IsUltrametricDist A] [HasSummableGeomSeries A] (hh : h ≠ 0) {u : Aˣ} :
    u ∈ principalUnitsBall p h A ↔ ‖(u : A) - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ)) := by
  refine ⟨fun hu ↦ hu.1, fun hu ↦ ⟨hu, ?_⟩⟩
  have hlt : ‖1 - (u : A)‖ < 1 := by
    rw [norm_sub_rev]
    exact hu.trans_lt (zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt)
      (by simpa using Nat.pos_of_ne_zero hh))
  have hinv := TauCeti.norm_inverse_one_sub_sub_one hlt
  rw [sub_sub_cancel, Ring.inverse_unit, norm_sub_rev] at hinv
  rw [← norm_sub_rev 1, hinv, norm_sub_rev]
  exact hu

/-- Construct an element of `1 + pʰ 𝒪_A` (`h ≠ 0`) from any `x : A` with `‖x - 1‖ ≤ p ^ (-h)`. -/
noncomputable def principalUnitsBall.mk {h : ℕ} {A : Type*} [NormedRing A] [IsUltrametricDist A]
    [HasSummableGeomSeries A] (hh : h ≠ 0) {x : A}
    (hx : ‖x - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ))) : principalUnitsBall p h A := by
  have hlt : ‖1 - x‖ < 1 := by
    rw [norm_sub_rev]
    exact hx.trans_lt (zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt)
      (by simpa using Nat.pos_of_ne_zero hh))
  have hu : IsUnit x := by
    simpa only [sub_sub_cancel] using IsUnit.one_sub_of_norm_lt_one hlt
  exact ⟨hu.unit, (mem_principalUnitsBall_iff_norm_sub_one_le hh).mpr (by simpa using hx)⟩

@[simp]
theorem principalUnitsBall.coe_mk {h : ℕ} {A : Type*} [NormedRing A] [IsUltrametricDist A]
    [HasSummableGeomSeries A] (hh : h ≠ 0) {x : A}
    (hx : ‖x - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ))) :
    ((principalUnitsBall.mk hh hx : Aˣ) : A) = x := by
  simp [principalUnitsBall.mk]

variable (p) in
/-- **The extended weight domain `ℤ_pˣ (1 + pʰ 𝒪_A)`** inside `Aˣ`: the subgroup generated by the
image of `ℤ_pˣ` under `TauCeti.padicIntAlgebraMap` and the principal unit ball
`1 + pʰ 𝒪_A`. -/
noncomputable def extendedDomain (h : ℕ) (A : Type*) [NormedCommRing A] [NormedAlgebra ℚ_[p] A]
    [IsUltrametricDist A] : Subgroup Aˣ :=
  (Units.map (padicIntAlgebraMap p A).toMonoidHom).range ⊔ principalUnitsBall p h A

section ExtendedDomainAPI

variable {h : ℕ} {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A]

/-- Elements of `ℤ_pˣ (1 + pʰ 𝒪_A)` are products `d₀ u₀` with `d₀ ∈ ℤ_pˣ` and
`u₀ ∈ 1 + pʰ 𝒪_A`. -/
theorem mem_extendedDomain_iff {d : Aˣ} :
    d ∈ extendedDomain p h A ↔
      ∃ (d₀ : ℤ_[p]ˣ) (u₀ : principalUnitsBall p h A),
        Units.map (padicIntAlgebraMap p A).toMonoidHom d₀ * (u₀ : Aˣ) = d := by
  rw [extendedDomain, Subgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨d₀, rfl⟩, u, hu, rfl⟩
    exact ⟨d₀, ⟨u, hu⟩, rfl⟩
  · rintro ⟨d₀, u₀, rfl⟩
    exact ⟨_, ⟨d₀, rfl⟩, u₀, u₀.2, rfl⟩

/-- Embed the `p`-adic units `ℤ_pˣ` into `ℤ_pˣ (1 + pʰ 𝒪_A)` as a group homomorphism. -/
noncomputable def extendedDomain.ofPadicIntUnits : ℤ_[p]ˣ →* extendedDomain p h A where
  toFun d₀ := ⟨Units.map (padicIntAlgebraMap p A).toMonoidHom d₀, Subgroup.mem_sup_left ⟨d₀, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' d₁ d₂ := Subtype.ext (map_mul _ d₁ d₂)

@[simp]
theorem extendedDomain.coe_ofPadicIntUnits (d₀ : ℤ_[p]ˣ) :
    ((extendedDomain.ofPadicIntUnits (h := h) (A := A) d₀ : Aˣ) : A) =
      padicIntAlgebraMap p A d₀ := by
  simp [extendedDomain.ofPadicIntUnits]

/-- Embed the principal unit ball `1 + pʰ 𝒪_A` into `ℤ_pˣ (1 + pʰ 𝒪_A)` as a group homomorphism. -/
noncomputable def extendedDomain.ofPrincipal :
    principalUnitsBall p h A →* extendedDomain p h A :=
  Subgroup.inclusion le_sup_right

@[simp]
theorem extendedDomain.coe_ofPrincipal (u₀ : principalUnitsBall p h A) :
    ((extendedDomain.ofPrincipal u₀ : Aˣ) : A) = ((u₀ : Aˣ) : A) := by
  rw [extendedDomain.ofPrincipal]
  rfl

/-- Form the product `d₀ u₀` in `ℤ_pˣ (1 + pʰ 𝒪_A)`. -/
noncomputable def extendedDomain.mk (d₀ : ℤ_[p]ˣ) (u₀ : principalUnitsBall p h A) :
    extendedDomain p h A :=
  extendedDomain.ofPadicIntUnits d₀ * extendedDomain.ofPrincipal u₀

@[simp]
theorem extendedDomain.coe_mk (d₀ : ℤ_[p]ˣ) (u₀ : principalUnitsBall p h A) :
    ((extendedDomain.mk d₀ u₀ : Aˣ) : A) = padicIntAlgebraMap p A d₀ * ((u₀ : Aˣ) : A) := by
  simp [extendedDomain.mk]

/-- Multiplication by an element of `ℤ_pˣ (1 + pʰ 𝒪_A)` (`h ≠ 0`) preserves norms in `A`, without
requiring `‖1‖ = 1`. -/
theorem norm_mul_extendedDomain (hh : h ≠ 0) (d : extendedDomain p h A) (c : A) :
    ‖c * ((d : Aˣ) : A)‖ = ‖c‖ := by
  obtain ⟨d₀, u₀, hd⟩ := mem_extendedDomain_iff.mp d.2
  have hd' : ((d : Aˣ) : A) = padicIntAlgebraMap p A d₀ * ((u₀ : Aˣ) : A) := by
    simpa using congrArg Units.val hd.symm
  have hu : ‖((u₀ : Aˣ) : A) - 1‖ < 1 :=
    u₀.2.1.trans_lt (zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt)
      (by simpa using Nat.pos_of_ne_zero hh))
  rw [hd', ← mul_assoc, mul_comm (c * _), ← add_sub_cancel 1 ((u₀ : Aˣ) : A),
    TauCeti.norm_one_add_mul_of_norm_lt_one hu, mul_comm, padicIntAlgebraMap_apply,
    ← Algebra.smul_def, norm_smul, ← PadicInt.norm_def, PadicInt.norm_units, one_mul]

/-- Multiplication by the inverse of an element of `ℤ_pˣ (1 + pʰ 𝒪_A)` (`h ≠ 0`) preserves norms
in `A`, without requiring `‖1‖ = 1`. -/
theorem norm_mul_inv_extendedDomain (hh : h ≠ 0) (d : extendedDomain p h A) (c : A) :
    ‖c * (((d : Aˣ)⁻¹ : Aˣ) : A)‖ = ‖c‖ :=
  norm_mul_extendedDomain hh d⁻¹ c

/-- For `d ∈ ℤ_pˣ (1 + pʰ 𝒪_A)` (`h ≠ 0`), `‖c‖ ≤ p ^ (-h)`, and `‖z‖ ≤ 1`, the element
`c * z + d` again lies in `ℤ_pˣ (1 + pʰ 𝒪_A)`. -/
noncomputable def extendedDomain.addMul [HasSummableGeomSeries A] (hh : h ≠ 0)
    (d : extendedDomain p h A) {c z : A} (hc : ‖c‖ ≤ (p : ℝ) ^ (-(h : ℤ))) (hz : ‖z‖ ≤ 1) :
    extendedDomain p h A :=
  d * extendedDomain.ofPrincipal
    (principalUnitsBall.mk hh (x := 1 + c * (((d : Aˣ)⁻¹ : Aˣ) : A) * z) (by
      rw [add_sub_cancel_left]
      refine (norm_mul_le _ _).trans ?_
      rw [norm_mul_inv_extendedDomain hh d c]
      exact (mul_le_of_le_one_right (norm_nonneg c) hz).trans hc))

@[simp]
theorem extendedDomain.coe_addMul [HasSummableGeomSeries A] (hh : h ≠ 0)
    (d : extendedDomain p h A) {c z : A} (hc : ‖c‖ ≤ (p : ℝ) ^ (-(h : ℤ))) (hz : ‖z‖ ≤ 1) :
    ((extendedDomain.addMul hh d hc hz : Aˣ) : A) = c * z + ((d : Aˣ) : A) := by
  simp only [extendedDomain.addMul, Subgroup.coe_mul, Units.val_mul,
    extendedDomain.coe_ofPrincipal, principalUnitsBall.coe_mk, mul_add, mul_one]
  have hcancel : ((d : Aˣ) : A) * (c * (((d : Aˣ)⁻¹ : Aˣ) : A) * z) = c * z := by
    calc ((d : Aˣ) : A) * (c * (((d : Aˣ)⁻¹ : Aˣ) : A) * z)
        = c * (((d : Aˣ) : A) * (((d : Aˣ)⁻¹ : Aˣ) : A)) * z := by ring
      _ = c * z := by simp
  rw [hcancel, add_comm]

end ExtendedDomainAPI

end Domains

/-! ### Level-`h` analytic extension of weights -/

section Extension

section BasicDefs

variable {A : Type*} [Ring A] [TopologicalSpace A]

/-- **The level-`h` coordinate** `t_h = κ(exp (p ^ h)) - 1 = κ(γ ^ (p ^ j)) - 1` of a weight `κ`,
where `h = padicUnitsDepth p + j`. -/
noncomputable def levelCoord (κ : WeightSpace p A) (j : ℕ) : A :=
  (κ (padicUnitsGenerator p ^ p ^ j) : A) - 1

theorem levelCoord_def (κ : WeightSpace p A) (j : ℕ) :
    κ.levelCoord j = (κ (padicUnitsGenerator p ^ p ^ j) : A) - 1 :=
  (rfl)

@[simp]
theorem levelCoord_zero (κ : WeightSpace p A) : κ.levelCoord 0 = κ.coord := by
  simp [levelCoord_def, coord_def]

@[simp]
theorem one_add_levelCoord (κ : WeightSpace p A) (j : ℕ) :
    1 + κ.levelCoord j = (κ (padicUnitsGenerator p ^ p ^ j) : A) := by
  rw [levelCoord_def, add_sub_cancel]

/-- **The analytic slope** `α = p⁻ʰ log (κ(exp (p ^ h)))` of a weight `κ` at level
`h = padicUnitsDepth p + j`. -/
noncomputable def weightSlope [IsTopologicalRing A] [Algebra ℚ_[p] A] (κ : WeightSpace p A)
    (j : ℕ) : A :=
  ((p : ℚ_[p]) ^ (padicUnitsDepth p + j))⁻¹ • NormedSpace.log (1 + κ.levelCoord j)

theorem weightSlope_def [IsTopologicalRing A] [Algebra ℚ_[p] A] (κ : WeightSpace p A) (j : ℕ) :
    κ.weightSlope j =
      ((p : ℚ_[p]) ^ (padicUnitsDepth p + j))⁻¹ • NormedSpace.log (1 + κ.levelCoord j) :=
  (rfl)

/-- **The analytic principal-unit character** `u ↦ exp (α log u)` associated to a weight `κ` at
level `h = padicUnitsDepth p + j`, where `α = κ.weightSlope j`. -/
noncomputable def principalExt [IsTopologicalRing A] [Algebra ℚ_[p] A] (κ : WeightSpace p A)
    (j : ℕ) (u : A) : A :=
  NormedSpace.exp (κ.weightSlope j * NormedSpace.log u)

theorem principalExt_def [IsTopologicalRing A] [Algebra ℚ_[p] A] (κ : WeightSpace p A) (j : ℕ)
    (u : A) :
    κ.principalExt j u = NormedSpace.exp (κ.weightSlope j * NormedSpace.log u) :=
  (rfl)

end BasicDefs

section LevelCoordCriteria

/-- In an ultrametric normed ring with bounded `ℚ_[p]`-action, `‖κ.coord‖ < r_j` implies
`‖κ.levelCoord j‖ < r_0`. -/
theorem norm_levelCoord_lt_of_norm_coord_lt {A : Type*} [NormedRing A] [Module ℚ_[p] A]
    [IsBoundedSMul ℚ_[p] A] [IsUltrametricDist A] (κ : WeightSpace p A) {j : ℕ}
    (h : ‖κ.coord‖ < amiceRadius p j) :
    ‖κ.levelCoord j‖ < amiceRadius p 0 := by
  rw [levelCoord_def, apply_padicUnitsGenerator_pow]
  exact norm_one_add_pow_sub_one_lt_of_norm_lt h

/-- For a multiplicative ultrametric norm with `‖1‖ = 1`, `‖κ.levelCoord j‖ < r_0` is equivalent
to `‖κ.coord‖ < r_j`. -/
theorem norm_levelCoord_lt_iff {K : Type*} [NormedRing K] [NormMulClass K] [NormOneClass K]
    [Module ℚ_[p] K] [NormSMulClass ℚ_[p] K] [IsUltrametricDist K] (κ : WeightSpace p K) (j : ℕ) :
    ‖κ.levelCoord j‖ < amiceRadius p 0 ↔ ‖κ.coord‖ < amiceRadius p j :=
  norm_apply_padicUnitsGenerator_pow_sub_one_lt_iff κ j

end LevelCoordCriteria

section BanachExtension

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A]
  [CompleteSpace A]

/-- The norm of the slope `α = p⁻ʰ log (1 + t_h)` is `‖t_h‖ / p ^ (-h)`. -/
theorem norm_weightSlope (κ : WeightSpace p A) {j : ℕ} (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) :
    ‖κ.weightSlope j‖ =
      ‖κ.levelCoord j‖ / (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) := by
  rw [weightSlope_def, norm_smul, norm_inv, Padic.norm_p_pow,
    norm_log_one_add_of_norm_lt_padic (by rwa [← amiceRadius_zero_eq]), inv_mul_eq_div]

private theorem norm_weightSlope_mul_log_le (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (u : principalUnitsBall p (padicUnitsDepth p + j) A) :
    ‖κ.weightSlope j * NormedSpace.log ((u : Aˣ) : A)‖ ≤ ‖κ.levelCoord j‖ := by
  have hu_lt : ‖((u : Aˣ) : A) - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rw [← amiceRadius_zero_eq]
    exact u.2.1.trans_lt (zpow_neg_padicUnitsDepth_add_lt_amiceRadius j)
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) :=
    zpow_pos (by exact_mod_cast hp.out.pos) _
  calc ‖κ.weightSlope j * NormedSpace.log ((u : Aˣ) : A)‖
      ≤ ‖κ.weightSlope j‖ * ‖NormedSpace.log ((u : Aˣ) : A)‖ := norm_mul_le _ _
    _ = ‖κ.levelCoord j‖ / (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) *
          ‖((u : Aˣ) : A) - 1‖ := by
        rw [norm_weightSlope κ ht, norm_log_of_norm_sub_one_lt_padic hu_lt]
    _ ≤ ‖κ.levelCoord j‖ / (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) *
          (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) := by gcongr; exact u.2.1
    _ = ‖κ.levelCoord j‖ := div_mul_cancel₀ _ hpos.ne'

/-- On `1 + pʰ 𝒪_A`, `‖principalExt u - 1‖ = ‖weightSlope * log u‖`. -/
theorem norm_principalExt_sub_one (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (u : principalUnitsBall p (padicUnitsDepth p + j) A) :
    ‖κ.principalExt j ((u : Aˣ) : A) - 1‖ =
      ‖κ.weightSlope j * NormedSpace.log ((u : Aˣ) : A)‖ := by
  rw [principalExt_def]
  exact norm_exp_sub_one_of_norm_lt_padic
    (by rw [← amiceRadius_zero_eq]; exact (norm_weightSlope_mul_log_le κ ht u).trans_lt ht)

/-- On `1 + pʰ 𝒪_A`, `‖principalExt u - 1‖ ≤ ‖κ.levelCoord j‖` (which is `< r_0 < 1`). -/
theorem norm_principalExt_sub_one_le (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (u : principalUnitsBall p (padicUnitsDepth p + j) A) :
    ‖κ.principalExt j ((u : Aˣ) : A) - 1‖ ≤ ‖κ.levelCoord j‖ := by
  rw [norm_principalExt_sub_one κ ht u]
  exact norm_weightSlope_mul_log_le κ ht u

/-- On `1 + pʰ 𝒪_A`, the analytic character has constant norm `‖(1 : A)‖`. -/
theorem norm_principalExt (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (u : principalUnitsBall p (padicUnitsDepth p + j) A) :
    ‖κ.principalExt j ((u : Aˣ) : A)‖ = ‖(1 : A)‖ := by
  have hlt : ‖κ.principalExt j ((u : Aˣ) : A) - 1‖ < 1 :=
    (norm_principalExt_sub_one_le κ ht u).trans_lt (ht.trans (amiceRadius_lt_one 0))
  simpa using TauCeti.norm_one_add_mul_of_norm_lt_one hlt (1 : A)

/-- When `‖1‖ = 1`, the analytic character on `1 + pʰ 𝒪_A` has norm `1`. -/
theorem norm_principalExt_eq_one [NormOneClass A] (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (u : principalUnitsBall p (padicUnitsDepth p + j) A) :
    ‖κ.principalExt j ((u : Aˣ) : A)‖ = 1 := by
  rw [norm_principalExt κ ht u, norm_one]

/-- **The analytic principal-unit homomorphism** `1 + pʰ 𝒪_A →* Aˣ`, sending `u` to
`exp (weightSlope * log u)`. -/
noncomputable def principalExtHom (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) :
    principalUnitsBall p (padicUnitsDepth p + j) A →* Aˣ where
  toFun u :=
    (isUnit_exp_of_norm_lt_padic
      (by rw [← amiceRadius_zero_eq]; exact (norm_weightSlope_mul_log_le κ ht u).trans_lt ht)).unit
  map_one' := Units.ext <| by simp
  map_mul' u v := Units.ext <| by
    have hu : ‖((u : Aˣ) : A) - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rw [← amiceRadius_zero_eq]
      exact u.2.1.trans_lt (zpow_neg_padicUnitsDepth_add_lt_amiceRadius j)
    have hv : ‖((v : Aˣ) : A) - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rw [← amiceRadius_zero_eq]
      exact v.2.1.trans_lt (zpow_neg_padicUnitsDepth_add_lt_amiceRadius j)
    have hwu : ‖κ.weightSlope j * NormedSpace.log ((u : Aˣ) : A)‖ <
        (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rw [← amiceRadius_zero_eq]
      exact (norm_weightSlope_mul_log_le κ ht u).trans_lt ht
    have hwv : ‖κ.weightSlope j * NormedSpace.log ((v : Aˣ) : A)‖ <
        (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rw [← amiceRadius_zero_eq]
      exact (norm_weightSlope_mul_log_le κ ht v).trans_lt ht
    simp only [Subgroup.coe_mul, Units.val_mul, IsUnit.unit_spec]
    rw [log_mul_of_norm_sub_one_lt_padic hu hv, mul_add, exp_add_of_norm_lt_padic hwu hwv]

@[simp]
theorem coe_principalExtHom_apply (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (u : principalUnitsBall p (padicUnitsDepth p + j) A) :
    (κ.principalExtHom j ht u : A) = κ.principalExt j ((u : Aˣ) : A) := by
  simp [principalExtHom, principalExt_def]

/-- On `ℤ_p`, `s ↦ κ(exp (p^h s))` agrees with `s ↦ exp (s • log (1 + t_h))`. -/
private theorem principalChar_prime_pow_mul_eq_exp (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) (s : ℤ_[p]) :
    κ.principalChar ((p : ℤ_[p]) ^ j * s) =
      NormedSpace.exp ((s : ℚ_[p]) • NormedSpace.log (1 + κ.levelCoord j)) := by
  have ht' : ‖κ.levelCoord j‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by rwa [← amiceRadius_zero_eq]
  let f₁ : ℤ_[p] → A := fun t ↦ κ.principalChar ((p : ℤ_[p]) ^ j * t)
  let f₂ : ℤ_[p] → A := fun t ↦ NormedSpace.exp ((t : ℚ_[p]) • NormedSpace.log (1 + κ.levelCoord j))
  have hf₁ : Continuous f₁ := κ.continuous_principalChar.comp (continuous_const.mul continuous_id)
  have hmem (t : ℤ_[p]) :
      (t : ℚ_[p]) • NormedSpace.log (1 + κ.levelCoord j) ∈
        Metric.eball (0 : A) (NormedSpace.expSeries ℚ_[p] A).radius := by
    refine mem_eball_expSeries_of_norm_lt_padic ?_
    rw [norm_smul, norm_log_one_add_of_norm_lt_padic ht', ← PadicInt.norm_def]
    exact (mul_le_of_le_one_left (norm_nonneg _) t.norm_le_one).trans_lt ht'
  have hf₂ : Continuous f₂ :=
    NormedSpace.continuousOn_exp.comp_continuous
      ((PadicInt.isEmbedding_coe_ringHom.continuous).smul continuous_const) hmem
  have hnat (n : ℕ) : f₁ n = f₂ n := by
    have hmul : ((p : ℤ_[p]) ^ j * (n : ℤ_[p])) = ((p ^ j * n : ℕ) : ℤ_[p]) := by push_cast; rfl
    have h1 : f₁ n = (1 + κ.levelCoord j) ^ n := by
      dsimp only [f₁]
      rw [hmul, ← nsmul_one (p ^ j * n), AddChar.map_nsmul_eq_pow, principalChar_one,
        ← Units.val_pow_eq_pow_val, ← map_pow, pow_mul, map_pow, Units.val_pow_eq_pow_val,
        one_add_levelCoord]
    have h2 : f₂ n = (1 + κ.levelCoord j) ^ n := by
      have hlog_lt : ‖NormedSpace.log (1 + κ.levelCoord j)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
        rwa [norm_log_one_add_of_norm_lt_padic ht']
      dsimp only [f₂]
      rw [PadicInt.coe_natCast, Nat.cast_smul_eq_nsmul, exp_nsmul_of_norm_lt_padic hlog_lt,
        exp_log_of_norm_sub_one_lt_padic (p := p) (by rw [add_sub_cancel_left]; exact ht')]
    rw [h1, h2]
  exact congrFun (PadicInt.denseRange_natCast.equalizer hf₁ hf₂ (funext hnat)) s

/-- **Agreement of `principalExt` with `κ` on `1 + pʰ ℤ_p`.** For every `v ∈ unitsPrincipal p h`,
`principalExt κ j (padicIntAlgebraMap p A v) = κ v`. -/
theorem principalExt_eq_apply_of_mem_unitsPrincipal (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) {v : ℤ_[p]ˣ}
    (hv : v ∈ unitsPrincipal p (padicUnitsDepth p + j)) :
    κ.principalExt j (padicIntAlgebraMap p A v) = (κ v : A) := by
  set h := padicUnitsDepth p + j with hh_def
  have hv_norm : ‖((v : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(h : ℤ)) := by
    rw [← PadicInt.coe_one, ← PadicInt.coe_sub, ← PadicInt.norm_def]
    exact mem_unitsPrincipal_iff_norm.mp hv
  have hv_lt : ‖((v : ℤ_[p]) : ℚ_[p]) - 1‖ < amiceRadius p 0 :=
    hv_norm.trans_lt (zpow_neg_padicUnitsDepth_add_lt_amiceRadius j)
  let s : ℤ_[p] := ⟨NormedSpace.log ((v : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ h, by
    rw [PadicInt.mem_subring_iff, norm_div, Padic.norm_p_pow,
      div_le_one (zpow_pos (by exact_mod_cast hp.out.pos) _),
      norm_log_of_norm_sub_one_lt_padic (by rwa [← amiceRadius_zero_eq])]
    exact hv_norm⟩
  have hs_coe : (s : ℚ_[p]) = NormedSpace.log ((v : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ h := rfl
  have hfs1 : κ.principalChar ((p : ℤ_[p]) ^ j * s) = (κ v : A) := by
    have hv' : v ∈ unitsPrincipal p (padicUnitsDepth p) :=
      unitsPrincipal_antitone p (Nat.le_add_right _ _) hv
    have hlog_eq : unitsPrincipalLogEquiv p ⟨v, hv'⟩ = .ofAdd ((p : ℤ_[p]) ^ j * s) := by
      refine Multiplicative.toAdd.injective (PadicInt.ext ?_)
      rw [coe_unitsPrincipalLogEquiv_apply, toAdd_ofAdd, PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast, hs_coe, hh_def, pow_add]
      have hpne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      field_simp [hpne]
    rw [principalChar_apply, ← hlog_eq, ContinuousMulEquiv.symm_apply_apply]
  have hfs2 : NormedSpace.exp ((s : ℚ_[p]) • NormedSpace.log (1 + κ.levelCoord j)) =
      κ.principalExt j (padicIntAlgebraMap p A v) := by
    rw [hs_coe, div_eq_mul_inv, mul_smul, ← weightSlope_def, Algebra.smul_def,
      algebraMap_padic_log_of_norm_sub_one_lt (hv_lt.trans (amiceRadius_lt_one 0)), mul_comm,
      ← padicIntAlgebraMap_apply, ← principalExt_def]
  rw [← hfs2, ← principalChar_prime_pow_mul_eq_exp κ ht s, hfs1]

/-- Well-definedness of `extendedWeight` on products `d₀ u₀` in `ℤ_pˣ (1 + pʰ 𝒪_A)`. -/
private theorem extendedWeight_wellDefined (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    {d₁ d₂ : ℤ_[p]ˣ} {u₁ u₂ : principalUnitsBall p (padicUnitsDepth p + j) A}
    (h : Units.map (padicIntAlgebraMap p A).toMonoidHom d₁ * (u₁ : Aˣ) =
      Units.map (padicIntAlgebraMap p A).toMonoidHom d₂ * (u₂ : Aˣ)) :
    κ d₁ * κ.principalExtHom j ht u₁ = κ d₂ * κ.principalExtHom j ht u₂ := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact Subsingleton.elim _ _
  set v : ℤ_[p]ˣ := d₂⁻¹ * d₁
  set w : principalUnitsBall p (padicUnitsDepth p + j) A := u₂ * u₁⁻¹
  have hvw : Units.map (padicIntAlgebraMap p A).toMonoidHom v = (w : Aˣ) := by
    simp only [v, w, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_assoc, mul_inv_cancel, mul_one]
  have hval : padicIntAlgebraMap p A v = ((w : Aˣ) : A) := by
    simpa using congrArg Units.val hvw
  have hv_mem : v ∈ unitsPrincipal p (padicUnitsDepth p + j) := by
    rw [mem_unitsPrincipal_iff_norm]
    have hsub_eq : ((w : Aˣ) : A) - 1 = ((((v : ℤ_[p]) - 1 : ℤ_[p]) : ℚ_[p])) • (1 : A) := by
      simp [← hval, padicIntAlgebraMap_apply, Algebra.algebraMap_eq_smul_one, sub_smul]
    calc ‖(v : ℤ_[p]) - 1‖
        ≤ ‖(v : ℤ_[p]) - 1‖ * ‖(1 : A)‖ :=
          le_mul_of_one_le_right (norm_nonneg _) (one_le_norm_one A)
      _ = ‖((w : Aˣ) : A) - 1‖ := by rw [hsub_eq, norm_smul, ← PadicInt.norm_def]
      _ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) := w.2.1
  have hagree : κ v = κ.principalExtHom j ht w := Units.ext <| by
    rw [coe_principalExtHom_apply, ← hval]
    exact (principalExt_eq_apply_of_mem_unitsPrincipal κ ht hv_mem).symm
  simp only [v, w, map_mul, map_inv] at hagree
  rw [inv_mul_eq_iff_eq_mul] at hagree
  rw [hagree]
  group

/-- **Analytic extension of a weight `κ` to `ℤ_pˣ (1 + pʰ 𝒪_A)`.** It coincides with `κ` on `ℤ_pˣ`
and with `principalExtHom` on `1 + pʰ 𝒪_A`. -/
noncomputable def extendedWeight (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) :
    extendedDomain p (padicUnitsDepth p + j) A →* Aˣ where
  toFun d :=
    let h := mem_extendedDomain_iff.mp d.2
    κ h.choose * κ.principalExtHom j ht h.choose_spec.choose
  map_one' := by
    set h := mem_extendedDomain_iff.mp (1 : extendedDomain p (padicUnitsDepth p + j) A).2
    simpa using extendedWeight_wellDefined κ j ht (d₂ := 1) (u₂ := 1)
      (by simpa using h.choose_spec.choose_spec)
  map_mul' d₁ d₂ := by
    set h₁ := mem_extendedDomain_iff.mp d₁.2
    set h₂ := mem_extendedDomain_iff.mp d₂.2
    set h₁₂ := mem_extendedDomain_iff.mp (d₁ * d₂).2
    have hprod :
        Units.map (padicIntAlgebraMap p A).toMonoidHom h₁₂.choose *
            (h₁₂.choose_spec.choose : Aˣ) =
          Units.map (padicIntAlgebraMap p A).toMonoidHom (h₁.choose * h₂.choose) *
            ((h₁.choose_spec.choose * h₂.choose_spec.choose :
              principalUnitsBall p (padicUnitsDepth p + j) A) : Aˣ) := by
      calc Units.map (padicIntAlgebraMap p A).toMonoidHom h₁₂.choose *
              (h₁₂.choose_spec.choose : Aˣ)
          = (d₁ : Aˣ) * (d₂ : Aˣ) := h₁₂.choose_spec.choose_spec
        _ = (Units.map (padicIntAlgebraMap p A).toMonoidHom h₁.choose *
              (h₁.choose_spec.choose : Aˣ)) *
            (Units.map (padicIntAlgebraMap p A).toMonoidHom h₂.choose *
              (h₂.choose_spec.choose : Aˣ)) := by
            rw [h₁.choose_spec.choose_spec, h₂.choose_spec.choose_spec]
        _ = Units.map (padicIntAlgebraMap p A).toMonoidHom (h₁.choose * h₂.choose) *
              ((h₁.choose_spec.choose * h₂.choose_spec.choose :
                principalUnitsBall p (padicUnitsDepth p + j) A) : Aˣ) := by
            rw [map_mul, Subgroup.coe_mul]
            exact mul_mul_mul_comm _ _ _ _
    rw [extendedWeight_wellDefined κ j ht hprod, map_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _

@[simp]
theorem extendedWeight_mk (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) (d₀ : ℤ_[p]ˣ)
    (u₀ : principalUnitsBall p (padicUnitsDepth p + j) A) :
    κ.extendedWeight j ht (extendedDomain.mk d₀ u₀) = κ d₀ * κ.principalExtHom j ht u₀ := by
  set h := mem_extendedDomain_iff.mp (extendedDomain.mk d₀ u₀).2
  exact extendedWeight_wellDefined κ j ht h.choose_spec.choose_spec

@[simp]
theorem extendedWeight_ofPadicIntUnits (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) (d₀ : ℤ_[p]ˣ) :
    κ.extendedWeight j ht (extendedDomain.ofPadicIntUnits d₀) = κ d₀ := by
  have h : extendedDomain.ofPadicIntUnits (h := padicUnitsDepth p + j) (A := A) d₀ =
      extendedDomain.mk d₀ 1 := by
    ext
    simp
  rw [h, extendedWeight_mk, map_one, mul_one]

@[simp]
theorem extendedWeight_ofPrincipal (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (u₀ : principalUnitsBall p (padicUnitsDepth p + j) A) :
    κ.extendedWeight j ht (extendedDomain.ofPrincipal u₀) = κ.principalExtHom j ht u₀ := by
  have h : extendedDomain.ofPrincipal u₀ = extendedDomain.mk 1 u₀ := by
    ext
    simp
  rw [h, extendedWeight_mk, map_one, one_mul]

/-- **Uniqueness of `extendedWeight`.** Any group homomorphism on `ℤ_pˣ (1 + pʰ 𝒪_A)` agreeing with
`κ` on `ℤ_pˣ` and with `principalExtHom` on `1 + pʰ 𝒪_A` equals `extendedWeight`. -/
theorem extendedWeight_unique (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (f : extendedDomain p (padicUnitsDepth p + j) A →* Aˣ)
    (h₁ : ∀ d₀ : ℤ_[p]ˣ, f (extendedDomain.ofPadicIntUnits d₀) = κ d₀)
    (h₂ : ∀ u₀ : principalUnitsBall p (padicUnitsDepth p + j) A,
      f (extendedDomain.ofPrincipal u₀) = κ.principalExtHom j ht u₀) :
    f = κ.extendedWeight j ht := by
  ext d
  obtain ⟨d₀, u₀, hd⟩ := mem_extendedDomain_iff.mp d.2
  have hd_eq : d = extendedDomain.mk d₀ u₀ := Subtype.ext hd.symm
  rw [hd_eq, extendedWeight_mk, extendedDomain.mk, map_mul, h₁, h₂]

/-- In any ultrametric Banach `ℚ_[p]`-algebra, multiplying `κ(d₀)` by the analytic character on
`1 + pʰ 𝒪_A` preserves its norm: `‖extendedWeight (d₀ u₀)‖ = ‖κ d₀‖`. -/
theorem norm_extendedWeight_mk (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) (d₀ : ℤ_[p]ˣ)
    (u₀ : principalUnitsBall p (padicUnitsDepth p + j) A) :
    ‖(κ.extendedWeight j ht (extendedDomain.mk d₀ u₀) : A)‖ = ‖(κ d₀ : A)‖ := by
  rw [extendedWeight_mk, Units.val_mul, coe_principalExtHom_apply, mul_comm,
    ← add_sub_cancel 1 (κ.principalExt j ((u₀ : Aˣ) : A))]
  exact TauCeti.norm_one_add_mul_of_norm_lt_one
    ((norm_principalExt_sub_one_le κ ht u₀).trans_lt (ht.trans (amiceRadius_lt_one 0))) (κ d₀ : A)

end BanachExtension

section NormMulClass

/-- Over a complete ultrametric commutative Banach `ℚ_[p]`-algebra with multiplicative norm and
`‖1‖ = 1`, the extended weight takes values of norm `1`. -/
theorem norm_extendedWeight_eq_one {K : Type*} [NormedCommRing K] [NormMulClass K]
    [NormOneClass K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
    (κ : WeightSpace p K) (j : ℕ) (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) K) :
    ‖(κ.extendedWeight j ht d : K)‖ = 1 := by
  obtain ⟨d₀, u₀, hd⟩ := mem_extendedDomain_iff.mp d.2
  have hd_eq : d = extendedDomain.mk d₀ u₀ := Subtype.ext hd.symm
  rw [hd_eq, norm_extendedWeight_mk, ContinuousMonoidHom.norm_apply_eq_one_of_compactSpace]

end NormMulClass

end Extension

/-! ### Scalar analytic factor power series `κ(c z + d)` -/

section ScalarFactor

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A]
  [CompleteSpace A]

/-- **The scalar analytic factor power series** expanding `z ↦ κ(c z + d)` for
`d ∈ ℤ_pˣ (1 + pʰ 𝒪_A)` and `c ∈ A`, namely
`κ(d) · exp (α log (1 + c d⁻¹ X))` with `α = κ.weightSlope j`. -/
noncomputable def scalarFactorSeries (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) (c : A) : A⟦X⟧ :=
  PowerSeries.C (κ.extendedWeight j ht d : A) *
    expLogSeries (p := p) (κ.weightSlope j) (c * (((d : Aˣ)⁻¹ : Aˣ) : A))

@[simp]
theorem constantCoeff_scalarFactorSeries (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) (c : A) :
    PowerSeries.constantCoeff (κ.scalarFactorSeries j ht d c) = (κ.extendedWeight j ht d : A) := by
  rw [scalarFactorSeries, map_mul, PowerSeries.constantCoeff_C, constantCoeff_expLogSeries, mul_one]

@[simp]
theorem scalarFactorSeries_zero (κ : WeightSpace p A) (j : ℕ)
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) :
    κ.scalarFactorSeries j ht d 0 = PowerSeries.C (κ.extendedWeight j ht d : A) := by
  simp [scalarFactorSeries, expLogSeries, PowerSeries.subst_zero_eq_C_constantCoeff]

private theorem radius_mul_slope_lt (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c : A} {r : ℝ}
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) :
    r * ‖c * (((d : Aˣ)⁻¹ : Aˣ) : A)‖ * ‖κ.weightSlope j‖ < amiceRadius p 0 := by
  have hh : padicUnitsDepth p + j ≠ 0 := by have := padicUnitsDepth_pos p; omega
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) :=
    zpow_pos (by exact_mod_cast hp.out.pos) _
  rw [norm_mul_inv_extendedDomain hh d c, norm_weightSlope κ ht, mul_div_assoc',
    div_lt_iff₀ hpos, mul_comm (amiceRadius p 0)]
  exact hr2

/-- **Convergence of `κ(c z + d)` at an admissible radius `r`.** If `0 ≤ r`, `r ‖c‖ < r_0`, and
`r ‖c‖ ‖t_h‖ < p⁻ʰ r_0`, then `scalarFactorSeries` is restricted at radius `r`. -/
theorem isRestricted_scalarFactorSeries (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c : A} {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r * ‖c‖ < amiceRadius p 0)
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) :
    (κ.scalarFactorSeries j ht d c).IsRestricted r := by
  have hh : padicUnitsDepth p + j ≠ 0 := by have := padicUnitsDepth_pos p; omega
  have h1 : r * ‖c * (((d : Aˣ)⁻¹ : Aˣ) : A)‖ < amiceRadius p 0 := by
    rwa [norm_mul_inv_extendedDomain hh d c]
  exact (PowerSeries.isRestricted_C r _).mul
    (isRestricted_expLogSeries hr h1 (radius_mul_slope_lt κ ht d hr2))

/-- **Exact Gauss norm of `κ(c z + d)` over a Banach algebra.** At any admissible radius `r ≥ 0`,
the Gauss norm of `scalarFactorSeries` equals `‖extendedWeight d‖`. -/
theorem gaussNorm_scalarFactorSeries (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c : A} {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r * ‖c‖ < amiceRadius p 0)
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) :
    (κ.scalarFactorSeries j ht d c).gaussNorm norm r = ‖(κ.extendedWeight j ht d : A)‖ := by
  have hh : padicUnitsDepth p + j ≠ 0 := by have := padicUnitsDepth_pos p; omega
  have h1 : r * ‖c * (((d : Aˣ)⁻¹ : Aˣ) : A)‖ < amiceRadius p 0 := by
    rwa [norm_mul_inv_extendedDomain hh d c]
  have h2 := radius_mul_slope_lt κ ht d hr2
  have hrest := isRestricted_scalarFactorSeries κ ht d hr hr1 hr2
  refine le_antisymm ?_ ?_
  · rw [PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun n ↦ ?_) (norm_nonneg _)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · rw [scalarFactorSeries, PowerSeries.coeff_C_mul]
      calc ‖(κ.extendedWeight j ht d : A) *
              PowerSeries.coeff n (expLogSeries (p := p) (κ.weightSlope j)
                (c * (((d : Aˣ)⁻¹ : Aˣ) : A)))‖ * r ^ n
          ≤ ‖(κ.extendedWeight j ht d : A)‖ *
              (‖PowerSeries.coeff n (expLogSeries (p := p) (κ.weightSlope j)
                (c * (((d : Aˣ)⁻¹ : Aˣ) : A)))‖ * r ^ n) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (pow_nonneg hr n)
        _ ≤ ‖(κ.extendedWeight j ht d : A)‖ *
              (r * ‖c * (((d : Aˣ)⁻¹ : Aˣ) : A)‖ * ‖κ.weightSlope j‖) :=
            mul_le_mul_of_nonneg_left (norm_coeff_expLogSeries_mul_pow_le hr h1 h2 hn)
              (norm_nonneg _)
        _ ≤ ‖(κ.extendedWeight j ht d : A)‖ :=
            mul_le_of_le_one_right (norm_nonneg _) (h2.le.trans (amiceRadius_lt_one 0).le)
  · have h0 := PowerSeries.le_gaussNorm norm r (κ.scalarFactorSeries j ht d c)
      (PowerSeries.hasGaussNorm_of_isRestricted hrest) 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0

/-- For `d = d₀ u₀ ∈ ℤ_pˣ (1 + pʰ 𝒪_A)`, the Gauss norm of `scalarFactorSeries` equals `‖κ d₀‖`. -/
theorem gaussNorm_scalarFactorSeries_mk (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) (d₀ : ℤ_[p]ˣ)
    (u₀ : principalUnitsBall p (padicUnitsDepth p + j) A) {c : A} {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r * ‖c‖ < amiceRadius p 0)
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) :
    (κ.scalarFactorSeries j ht (extendedDomain.mk d₀ u₀) c).gaussNorm norm r = ‖(κ d₀ : A)‖ := by
  rw [gaussNorm_scalarFactorSeries κ ht _ hr hr1 hr2, norm_extendedWeight_mk]

/-- **Coefficient bounds for `κ(c z + d)` over a Banach algebra.** At any positive admissible
radius `r > 0`, the `n`-th coefficient satisfies `‖a_n‖ ≤ ‖extendedWeight d‖ * r⁻¹ ^ n`. -/
theorem norm_coeff_scalarFactorSeries_le (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c : A} {r : ℝ} (hr : 0 < r)
    (hr1 : r * ‖c‖ < amiceRadius p 0)
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) (n : ℕ) :
    ‖PowerSeries.coeff n (κ.scalarFactorSeries j ht d c)‖ ≤
      ‖(κ.extendedWeight j ht d : A)‖ * r⁻¹ ^ n := by
  have hle := PowerSeries.le_gaussNorm norm r (κ.scalarFactorSeries j ht d c)
    (PowerSeries.hasGaussNorm_of_isRestricted
      (isRestricted_scalarFactorSeries κ ht d hr.le hr1 hr2)) n
  rw [gaussNorm_scalarFactorSeries κ ht d hr.le hr1 hr2] at hle
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hr n)]
  exact hle

/-- **Evaluation of `scalarFactorSeries` at any point of the closed disc `‖z‖ ≤ r`.** -/
theorem evalAt_scalarFactorSeries (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c z : A} {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r * ‖c‖ < amiceRadius p 0)
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) (hz : ‖z‖ ≤ r) :
    (κ.scalarFactorSeries j ht d c).evalAt z =
      (κ.extendedWeight j ht d : A) *
        NormedSpace.exp (κ.weightSlope j *
          NormedSpace.log (1 + c * (((d : Aˣ)⁻¹ : Aˣ) : A) * z)) := by
  have hh : padicUnitsDepth p + j ≠ 0 := by have := padicUnitsDepth_pos p; omega
  have h1 : r * ‖c * (((d : Aˣ)⁻¹ : Aˣ) : A)‖ < amiceRadius p 0 := by
    rwa [norm_mul_inv_extendedDomain hh d c]
  have h2 := radius_mul_slope_lt κ ht d hr2
  rw [scalarFactorSeries, PowerSeries.IsRestricted.evalAt_mul
    (PowerSeries.isRestricted_C r _) (isRestricted_expLogSeries hr h1 h2) hz,
    PowerSeries.evalAt_C, evalAt_expLogSeries hr h1 h2 hz]
  simp

/-! ### Closed unit disc (`r = 1`) specialization -/

omit [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A] [CompleteSpace A] in
private theorem one_mul_norm_lt_amiceRadius {j : ℕ} {c : A}
    (hc : ‖c‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ))) :
    1 * ‖c‖ < amiceRadius p 0 := by
  rw [one_mul]
  exact hc.trans_lt (zpow_neg_padicUnitsDepth_add_lt_amiceRadius j)

omit [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A] [CompleteSpace A] in
private theorem one_mul_norm_mul_levelCoord_lt (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) {c : A}
    (hc : ‖c‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ))) :
    1 * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0 := by
  rw [one_mul]
  calc ‖c‖ * ‖κ.levelCoord j‖
      ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * ‖κ.levelCoord j‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ < (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0 :=
        mul_lt_mul_of_pos_left ht (zpow_pos (by exact_mod_cast hp.out.pos) _)

/-- For `‖c‖ ≤ p ^ (-h)`, `scalarFactorSeries` is restricted on the closed unit disc `r = 1`. -/
theorem isRestricted_scalarFactorSeries_one (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c : A}
    (hc : ‖c‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ))) :
    (κ.scalarFactorSeries j ht d c).IsRestricted 1 :=
  isRestricted_scalarFactorSeries κ ht d zero_le_one (one_mul_norm_lt_amiceRadius hc)
    (one_mul_norm_mul_levelCoord_lt κ ht hc)

/-- For `‖c‖ ≤ p ^ (-h)`, the unit-disc Gauss norm of `scalarFactorSeries` equals
`‖extendedWeight d‖`. -/
theorem gaussNorm_scalarFactorSeries_one (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c : A}
    (hc : ‖c‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ))) :
    (κ.scalarFactorSeries j ht d c).gaussNorm norm 1 = ‖(κ.extendedWeight j ht d : A)‖ :=
  gaussNorm_scalarFactorSeries κ ht d zero_le_one (one_mul_norm_lt_amiceRadius hc)
    (one_mul_norm_mul_levelCoord_lt κ ht hc)

/-- **Evaluation on the closed unit disc agrees with `extendedWeight (c z + d)`.** For
`d ∈ ℤ_pˣ (1 + pʰ 𝒪_A)`, `‖c‖ ≤ p ^ (-h)`, and `‖z‖ ≤ 1`, `scalarFactorSeries` evaluates at `z` to
`extendedWeight (c z + d)`. -/
theorem evalAt_scalarFactorSeries_eq_extendedWeight (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) {c z : A}
    (hc : ‖c‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ))) (hz : ‖z‖ ≤ 1) :
    (κ.scalarFactorSeries j ht d c).evalAt z =
      (κ.extendedWeight j ht
        (extendedDomain.addMul (by have := padicUnitsDepth_pos p; omega) d hc hz) : A) := by
  rw [evalAt_scalarFactorSeries κ ht d zero_le_one (one_mul_norm_lt_amiceRadius hc)
    (one_mul_norm_mul_levelCoord_lt κ ht hc) hz, extendedDomain.addMul, map_mul,
    extendedWeight_ofPrincipal, Units.val_mul, coe_principalExtHom_apply, principalUnitsBall.coe_mk,
    principalExt_def]

/-- **Evaluation at `ℤ_p`-points recovers `κ(c₀ z₀ + d₀)`.** When `‖1‖ = 1`, for `d₀ ∈ ℤ_pˣ`,
`c₀ ∈ pʰ ℤ_p`, `z₀ ∈ ℤ_p`, and `u : ℤ_pˣ` with `u = c₀ z₀ + d₀`, `scalarFactorSeries` evaluates at
`z₀` to `κ(u)`. -/
theorem evalAt_scalarFactorSeries_padicInt [NormOneClass A] (κ : WeightSpace p A) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0) (d₀ : ℤ_[p]ˣ) {c₀ : ℤ_[p]}
    (hc₀ : ‖c₀‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ))) (z₀ : ℤ_[p])
    {u : ℤ_[p]ˣ} (hu : (u : ℤ_[p]) = c₀ * z₀ + d₀) :
    (κ.scalarFactorSeries j ht (extendedDomain.ofPadicIntUnits d₀)
        (padicIntAlgebraMap p A c₀)).evalAt (padicIntAlgebraMap p A z₀) = (κ u : A) := by
  have hc : ‖padicIntAlgebraMap p A c₀‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) := by
    rwa [norm_padicIntAlgebraMap]
  have hz : ‖padicIntAlgebraMap p A z₀‖ ≤ 1 := norm_padicIntAlgebraMap_le_one z₀
  rw [evalAt_scalarFactorSeries_eq_extendedWeight κ ht _ hc hz]
  have heq : extendedDomain.addMul (by have := padicUnitsDepth_pos p; omega)
      (extendedDomain.ofPadicIntUnits d₀) hc hz = extendedDomain.ofPadicIntUnits u := by
    ext
    simp [hu]
  rw [heq, extendedWeight_ofPadicIntUnits]

/-! ### Multiplicative-norm and field specialization -/

section MultiplicativeNorm

variable {K : Type*} [NormedCommRing K] [NormMulClass K] [NormOneClass K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

/-- **Unit Gauss norm at any admissible radius** for a multiplicative ultrametric norm (in
particular, over any complete ultrametric normed field extension of `ℚ_[p]`). -/
theorem gaussNorm_scalarFactorSeries_eq_one (κ : WeightSpace p K) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) K) {c : K} {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r * ‖c‖ < amiceRadius p 0)
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) :
    (κ.scalarFactorSeries j ht d c).gaussNorm norm r = 1 := by
  rw [gaussNorm_scalarFactorSeries κ ht d hr hr1 hr2, norm_extendedWeight_eq_one]

/-- **Unit Gauss norm on the closed unit disc** for a multiplicative ultrametric norm when
`‖c‖ ≤ p ^ (-h)`. -/
theorem gaussNorm_scalarFactorSeries_one_eq_one (κ : WeightSpace p K) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) K) {c : K}
    (hc : ‖c‖ ≤ (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ))) :
    (κ.scalarFactorSeries j ht d c).gaussNorm norm 1 = 1 := by
  rw [gaussNorm_scalarFactorSeries_one κ ht d hc, norm_extendedWeight_eq_one]

/-- **Sharp coefficient bounds `‖a_n‖ ≤ r⁻¹ ^ n`** for a multiplicative ultrametric norm at any
positive admissible radius `r > 0`. -/
theorem norm_coeff_scalarFactorSeries_le_inv_pow (κ : WeightSpace p K) {j : ℕ}
    (ht : ‖κ.levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) K) {c : K} {r : ℝ} (hr : 0 < r)
    (hr1 : r * ‖c‖ < amiceRadius p 0)
    (hr2 : r * ‖c‖ * ‖κ.levelCoord j‖ <
      (p : ℝ) ^ (-((padicUnitsDepth p + j : ℕ) : ℤ)) * amiceRadius p 0) (n : ℕ) :
    ‖PowerSeries.coeff n (κ.scalarFactorSeries j ht d c)‖ ≤ r⁻¹ ^ n := by
  simpa [norm_extendedWeight_eq_one] using
    norm_coeff_scalarFactorSeries_le κ ht d hr hr1 hr2 n

end MultiplicativeNorm

/-! ### Nonnegative algebraic weights -/

section AlgebraicWeights

omit [CompleteSpace A] in
/-- When `‖1‖ = 1`, every nonnegative algebraic weight `x ↦ x ^ k` satisfies the level-`h`
analyticity criterion `‖levelCoord j‖ < r_0` at every `j : ℕ`. -/
theorem norm_levelCoord_inclusion_pow_lt [NormOneClass A] (k j : ℕ) :
    ‖(inclusion (p := p) A ^ k).levelCoord j‖ < amiceRadius p 0 := by
  have hu : padicUnitsGenerator p ^ p ^ j ∈ unitsPrincipal p (padicUnitsDepth p + j) :=
    pow_pow_mem_unitsPrincipal (padicUnitsDepth_pos p) padicUnitsGenerator_mem_unitsPrincipal j
  have hpow : (padicUnitsGenerator p ^ p ^ j) ^ k ∈ unitsPrincipal p (padicUnitsDepth p + j) :=
    Subgroup.pow_mem _ hu k
  rw [levelCoord_def, ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val,
    ← Units.val_pow_eq_pow_val, ← map_pow, norm_coe_inclusion_apply_sub_one]
  exact (mem_unitsPrincipal_iff_norm.mp hpow).trans_lt
    (zpow_neg_padicUnitsDepth_add_lt_amiceRadius j)

omit [CompleteSpace A] in
/-- The analytic slope of the algebraic weight `x ↦ x ^ k` (`k : ℕ`) is `k`. -/
theorem weightSlope_inclusion_pow (k j : ℕ) :
    (inclusion (p := p) A ^ k).weightSlope j = (k : A) := by
  set h := padicUnitsDepth p + j with hh_def
  have hph : ‖(p : ℚ_[p]) ^ h‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rw [Padic.norm_p_pow, ← amiceRadius_zero_eq]
    exact zpow_neg_padicUnitsDepth_add_lt_amiceRadius j
  have hkph : ‖k • ((p : ℚ_[p]) ^ h)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    (IsUltrametricDist.norm_nsmul_le _ k).trans_lt hph
  have hval : 1 + (inclusion (p := p) A ^ k).levelCoord j =
      algebraMap ℚ_[p] A (NormedSpace.exp (k • ((p : ℚ_[p]) ^ h))) := by
    rw [one_add_levelCoord, ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val,
      coe_inclusion_apply, padicIntAlgebraMap_apply, coe_padicUnitsGenerator_pow_prime_pow,
      ← map_pow, exp_nsmul_of_norm_lt_padic hph]
  have hsub : ‖NormedSpace.exp (k • ((p : ℚ_[p]) ^ h)) - 1‖ < 1 := by
    rw [norm_exp_sub_one_of_norm_lt_padic hkph]
    exact (by rwa [← amiceRadius_zero_eq] at hkph : _ < amiceRadius p 0).trans
      (amiceRadius_lt_one 0)
  have hpne : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero h (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [weightSlope_def, hval, ← algebraMap_padic_log_of_norm_sub_one_lt hsub,
    log_exp_of_norm_lt_padic hkph, Algebra.smul_def, ← map_mul, nsmul_eq_mul, ← hh_def,
    mul_left_comm, inv_mul_cancel₀ hpne, mul_one, map_natCast]

/-- On `1 + pʰ 𝒪_A`, the analytic extension of the algebraic weight `x ↦ x ^ k` is `u ↦ u ^ k`. -/
theorem principalExt_inclusion_pow (k j : ℕ)
    (u : principalUnitsBall p (padicUnitsDepth p + j) A) :
    (inclusion (p := p) A ^ k).principalExt j ((u : Aˣ) : A) = ((u : Aˣ) : A) ^ k := by
  have hu : ‖((u : Aˣ) : A) - 1‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rw [← amiceRadius_zero_eq]
    exact u.2.1.trans_lt (zpow_neg_padicUnitsDepth_add_lt_amiceRadius j)
  have hlu : ‖NormedSpace.log ((u : Aˣ) : A)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rwa [norm_log_of_norm_sub_one_lt_padic hu]
  rw [principalExt_def, weightSlope_inclusion_pow, ← nsmul_eq_mul, exp_nsmul_of_norm_lt_padic hlu,
    exp_log_of_norm_sub_one_lt_padic hu]

/-- On `ℤ_pˣ (1 + pʰ 𝒪_A)`, the extended weight of `x ↦ x ^ k` is `d ↦ d ^ k`. -/
theorem extendedWeight_inclusion_pow (k j : ℕ)
    (ht : ‖(inclusion (p := p) A ^ k).levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) :
    (inclusion (p := p) A ^ k).extendedWeight j ht d = (d : Aˣ) ^ k := by
  obtain ⟨d₀, u₀, hd⟩ := mem_extendedDomain_iff.mp d.2
  have hd_eq : d = extendedDomain.mk d₀ u₀ := Subtype.ext hd.symm
  rw [hd_eq, extendedWeight_mk]
  refine Units.ext ?_
  simp only [Units.val_mul, ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val,
    coe_inclusion_apply, coe_principalExtHom_apply, principalExt_inclusion_pow,
    extendedDomain.coe_mk, mul_pow]

/-- **Algebraic-weight identity for `scalarFactorSeries`.** For `κ(x) = x ^ k` (`k : ℕ`), the
power series expanding `κ(c z + d)` equals the polynomial `(d + c X) ^ k`. -/
theorem scalarFactorSeries_inclusion_pow (k j : ℕ)
    (ht : ‖(inclusion (p := p) A ^ k).levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) (c : A) :
    (inclusion (p := p) A ^ k).scalarFactorSeries j ht d c =
      (PowerSeries.C ((d : Aˣ) : A) + PowerSeries.C c * PowerSeries.X) ^ k := by
  rw [scalarFactorSeries, extendedWeight_inclusion_pow, Units.val_pow_eq_pow_val,
    weightSlope_inclusion_pow, expLogSeries_natCast, map_pow, ← mul_pow, mul_add, mul_one,
    ← mul_assoc, ← map_mul]
  have hcancel : ((d : Aˣ) : A) * (c * (((d : Aˣ)⁻¹ : Aˣ) : A)) = c := by
    calc ((d : Aˣ) : A) * (c * (((d : Aˣ)⁻¹ : Aˣ) : A))
        = c * (((d : Aˣ) : A) * (((d : Aˣ)⁻¹ : Aˣ) : A)) := by ring
      _ = c := by simp
  rw [hcancel]

/-- **Evaluation of `scalarFactorSeries` for a nonnegative algebraic weight `x ↦ x ^ k`** agrees
with `(c * z + d) ^ k` at every `z ∈ A`. -/
theorem evalAt_scalarFactorSeries_inclusion_pow (k j : ℕ)
    (ht : ‖(inclusion (p := p) A ^ k).levelCoord j‖ < amiceRadius p 0)
    (d : extendedDomain p (padicUnitsDepth p + j) A) (c z : A) :
    ((inclusion (p := p) A ^ k).scalarFactorSeries j ht d c).evalAt z =
      (c * z + ((d : Aˣ) : A)) ^ k := by
  rw [scalarFactorSeries_inclusion_pow]
  have hpoly :
      (PowerSeries.C ((d : Aˣ) : A) + PowerSeries.C c * PowerSeries.X) ^ k =
        (((Polynomial.C ((d : Aˣ) : A) + Polynomial.C c * Polynomial.X) ^ k : Polynomial A) :
          A⟦X⟧) := by
    simp
  rw [hpoly, PowerSeries.evalAt_coe]
  simp [add_comm]

end AlgebraicWeights

end ScalarFactor

end TauCeti.WeightSpace
