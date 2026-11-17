/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Topology.Order.Interval

/-!
# Volterra integral equations with separable kernel bounds

Let `I ⊆ ℝ` be an open interval (`IsOpen I`, `I.OrdConnected`, covering all `(a, b)` with
`-∞ ≤ a < b ≤ ∞`), let `K x v` be a kernel continuous on `{(x, v) | x ∈ I ∧ v ∈ I ∧ x < v}`
with a separable bound `‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are continuous on `I`,
and let `J`, `ψ` be continuous on `I` such that the tail integrals
`Φ x = ∫ v in I ∩ Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖` converge
for every `x ∈ I`. Then the Volterra integral equation
`h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)` has a continuous solution `h` on `I` with
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)`. It is the unique continuous solution satisfying `h = O(P)` on some
upper tail `I ∩ Ici x₀`, and every such solution automatically obeys the same a priori bound. When
`P` is a nonnegative constant `P₀` and `‖J‖ ≤ ‖ψ‖` (e.g. `J = ψ`), every bounded continuous solution
satisfies `‖h x‖ ≤ exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖) - 1`.

If in addition `K` is continuous up to the diagonal with `K x x = 0` and its partial derivative
`K₁ = ∂K/∂x` satisfies `‖K₁ x v‖ ≤ P₁ x * Q v` for continuous `P₁`, then every continuous `O(P)`
solution is differentiable with derivative `∫ v in I ∩ Ioi x, K₁ x v • (J v + ψ v • h v)` and obeys
`‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)` (or `P₁ x / P₀ * (exp (P₀ * ∫ Q * ‖ψ‖) - 1)` in the sharper
case, where both sides vanish when `P₀ = 0`); if `K₁` is continuous on `{x < v}`, then `h` is `C¹`.

This is Olver's theorem on Volterra integral equations (Chapter 6, Theorem 10.1), proved over any
normed field `𝕜` and real normed `𝕜`-space `E` (completeness is assumed only for existence, and real
linearity of `𝕜` only for differentiation). For the discrete analogue, see
`TauCeti.exists_discrete_volterra_solution`.

## Main results

On a general open interval `I`:
* `TauCeti.exists_volterra_solution_on`: existence of a continuous solution with
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.isBigO_of_norm_le_volterra_bound_on`: any function obeying that bound on `I ∩ Ici x₀`
  is `O(P)` there.
* `TauCeti.volterra_solution_unique_on`: uniqueness among continuous solutions that are `O(P)` on
  some upper tail.
* `TauCeti.norm_volterra_solution_le_on`: a priori bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.norm_volterra_solution_le_exp_sub_one_on`: sharper bound
  `‖h x‖ ≤ exp (P₀ * ∫ Q * ‖ψ‖) - 1` for constant `P₀ ≥ 0` and `‖J‖ ≤ ‖ψ‖`.
* `TauCeti.hasDerivAt_volterra_solution_on`, `TauCeti.contDiffOn_volterra_solution_on`,
  `TauCeti.norm_deriv_volterra_solution_le_on`,
  `TauCeti.norm_deriv_volterra_solution_le_exp_sub_one_on`: `C¹` regularity and derivative bounds.

Specializations to half-lines `(a, ∞)` (`TauCeti.exists_volterra_solution`,
`TauCeti.volterra_solution_unique`, `TauCeti.norm_volterra_solution_le`,
`TauCeti.norm_volterra_solution_le_exp_sub_one`, `TauCeti.hasDerivAt_volterra_solution`,
`TauCeti.contDiffOn_volterra_solution`, `TauCeti.norm_deriv_volterra_solution_le`,
`TauCeti.norm_deriv_volterra_solution_le_exp_sub_one`) and bounded open intervals `(a, b)`
(`*_Ioo`) follow directly from the general theorems.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10.
* NIST Digital Library of Mathematical Functions, §2.7(iii), <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Filter Set MeasureTheory Function
open scoped Nat Topology

namespace TauCeti

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

/-! ### Basic kernel and weight estimates -/

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- The forcing weights `Q v * ‖J v‖` are nonnegative on `I`. -/
private lemma forcing_weight_nonneg (hQ0 : ∀ v ∈ I, 0 ≤ Q v) :
    ∀ v ∈ I, 0 ≤ Q v * ‖J v‖ :=
  fun v hv ↦ mul_nonneg (hQ0 v hv) (norm_nonneg _)

/-- The coefficient weights `P v * Q v * ‖ψ v‖` are nonnegative on `I`. -/
private lemma coeff_weight_nonneg (hP0 : ∀ v ∈ I, 0 ≤ P v) (hQ0 : ∀ v ∈ I, 0 ≤ Q v) :
    ∀ v ∈ I, 0 ≤ P v * Q v * ‖ψ v‖ :=
  fun v hv ↦ mul_nonneg (mul_nonneg (hP0 v hv) (hQ0 v hv)) (norm_nonneg _)

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
private lemma integral_forcing_nonneg (hI : MeasurableSet I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v) (x : ℝ) :
    0 ≤ ∫ u in I ∩ Ioi x, Q u * ‖J u‖ :=
  setIntegral_nonneg (hI.inter measurableSet_Ioi) fun u hu ↦ forcing_weight_nonneg hQ0 u hu.1

private lemma integral_coeff_nonneg (hI : MeasurableSet I) (hP0 : ∀ v ∈ I, 0 ≤ P v)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) (x : ℝ) : 0 ≤ ∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖ :=
  setIntegral_nonneg (hI.inter measurableSet_Ioi) fun u hu ↦ coeff_weight_nonneg hP0 hQ0 u hu.1

omit [NormedSpace ℝ E] in
private lemma continuousOn_forcing_add (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I)
    {h : ℝ → E} (hh : ContinuousOn h I) : ContinuousOn (fun v ↦ J v + ψ v • h v) I :=
  hJ.add (hψ.smul hh)

omit [NormedSpace ℝ E] in
/-- The separable bound for `v ↦ K x v • y` on `I ∩ Ioi x`. -/
private lemma norm_kernel_smul_le (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v)
    {x v : ℝ} (hx : x ∈ I) (hv : v ∈ I) (hxv : x < v) (y : E) :
    ‖K x v • y‖ ≤ P x * (Q v * ‖y‖) := by
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hKle x v hx hv hxv) (norm_nonneg _)

omit [NormedSpace ℝ E] in
/-- If `F` is continuous on `I` and `Q * ‖F‖` is integrable on `I ∩ Ioi x`, then so is
`v ↦ K x v • F v`. -/
private lemma integrableOn_kernel_smul (hI : IsOpen I)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E}
    (hF : ContinuousOn F I) {x : ℝ} (hx : x ∈ I)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    IntegrableOn (fun v ↦ K x v • F v) (I ∩ Ioi x) := by
  have hmeas : MeasurableSet (I ∩ Ioi x) := hI.measurableSet.inter measurableSet_Ioi
  have hKx : ContinuousOn (fun v ↦ K x v) (I ∩ Ioi x) :=
    hK.comp (continuous_const.prodMk continuous_id).continuousOn fun v hv ↦ ⟨hx, hv.1, hv.2⟩
  refine Integrable.mono' (hFint.const_mul (P x))
    ((hKx.smul (hF.mono inter_subset_left)).aestronglyMeasurable hmeas) ?_
  filter_upwards [ae_restrict_mem hmeas] with v hv
  exact norm_kernel_smul_le hKle hx hv.1 hv.2 _

/-- The separable bound for the integral `∫ v in I ∩ Ioi x, K x v • F v`. -/
private lemma norm_integral_kernel_smul_le (hI : IsOpen I)
    (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E} {x : ℝ} (hx : x ∈ I)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    ‖∫ v in I ∩ Ioi x, K x v • F v‖ ≤ P x * ∫ v in I ∩ Ioi x, Q v * ‖F v‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hFint.const_mul (P x)) ?_
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  exact norm_kernel_smul_le hKle hx hv.1 hv.2 _

/-- If `F` is continuous on `I` and `Q * ‖F‖` is integrable on every tail `I ∩ Ioi x`,
then `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` is continuous on `I`. -/
private lemma continuousOn_integral_kernel_smul (hI : IsOpen I)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v) (hP : ContinuousOn P I)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) {F : ℝ → E} (hF : ContinuousOn F I)
    (hFint : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    ContinuousOn (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) I := by
  intro x₀ hx₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨c, d, _, hmem, hcd⟩ := exists_Icc_mem_subset_of_mem_nhds (hI.mem_nhds hx₀)
  obtain ⟨hcx, hxd⟩ : x₀ ∈ Ioo c d := by
    simpa only [interior_Icc] using (mem_interior_iff_mem_nhds.2 hmem : x₀ ∈ interior (Icc c d))
  have hcI : c ∈ I := hcd ⟨le_rfl, (hcx.trans hxd).le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hcd)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ ⟨hcx.le, hxd.le⟩)
  -- Extend integrands by zero to the fixed tail `I ∩ Ioi c`.
  have heq : (fun x ↦ ∫ v in I ∩ Ioi c, (Ioi x).indicator (fun v ↦ K x v • F v) v) =ᶠ[𝓝 x₀]
      fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v := by
    filter_upwards [Ioi_mem_nhds hcx] with x hx
    rw [setIntegral_indicator measurableSet_Ioi, inter_assoc, Ioi_inter_Ioi, sup_eq_right.2 hx.le]
  have hmeas : MeasurableSet (I ∩ Ioi c) := hI.measurableSet.inter measurableSet_Ioi
  refine (continuousAt_of_dominated (bound := fun v ↦ M * (Q v * ‖F v‖)) ?_ ?_
    ((hFint c hcI).const_mul M) ?_).congr heq
  · filter_upwards [Ioo_mem_nhds hcx hxd] with x hx
    have hxI : x ∈ I := hcd ⟨hx.1.le, hx.2.le⟩
    have hint : IntegrableOn (fun v ↦ K x v • F v) (Ioi x) (volume.restrict (I ∩ Ioi c)) := by
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi, inter_comm, inter_assoc,
        Ioi_inter_Ioi, sup_eq_right.2 hx.1.le]
      exact integrableOn_kernel_smul hI hK hKle hF hxI (hFint x hxI)
    exact ((integrable_indicator_iff measurableSet_Ioi).2 hint).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds hcx hxd] with x hx
    refine (ae_restrict_iff' hmeas).2 (ae_of_all _ fun v hv ↦ ?_)
    have hQF : 0 ≤ Q v * ‖F v‖ := mul_nonneg (hQ0 v hv.1) (norm_nonneg _)
    by_cases hxv : x < v
    · rw [indicator_of_mem hxv]
      exact (norm_kernel_smul_le hKle (hcd ⟨hx.1.le, hx.2.le⟩) hv.1 hxv _).trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hM x ⟨hx.1.le, hx.2.le⟩)) hQF)
    · rw [indicator_of_notMem hxv, norm_zero]; exact mul_nonneg hM0 hQF
  · filter_upwards [ae_restrict_mem hmeas, ae_restrict_of_ae (Measure.ae_ne volume x₀)] with
      v hv hne
    rcases hne.lt_or_gt with hlt | hgt
    · refine (continuousAt_const (y := (0 : E))).congr ?_
      filter_upwards [Ioi_mem_nhds hlt] with x hx; rw [indicator_of_notMem (notMem_Ioi.2 hx.le)]
    · have hopen : IsOpen {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2} :=
        (hI.preimage continuous_fst).inter
          ((hI.preimage continuous_snd).inter (isOpen_lt continuous_fst continuous_snd))
      have hKv : ContinuousAt (fun x ↦ K x v) x₀ :=
        (hK.continuousAt (hopen.mem_nhds ⟨hx₀, hv.1, hgt⟩)).comp (f := fun x ↦ (x, v)) (by fun_prop)
      refine (hKv.fun_smul (continuousAt_const (y := F v))).congr ?_
      filter_upwards [gt_mem_nhds hgt] with x hx; rw [indicator_of_mem (mem_Ioi.2 hx)]

/-! ### Picard iteration and existence -/

/-- The increments of the Picard iteration for the Volterra equation on `I`: the `0`-th is
`x ↦ ∫ v in I ∩ Ioi x, K x v • J v`, and each further one applies
`F ↦ (x ↦ ∫ v in I ∩ Ioi x, K x v • ψ v • F v)` to the previous one. -/
private noncomputable def picardTerm (I : Set ℝ) (K : ℝ → ℝ → 𝕜) (J : ℝ → E) (ψ : ℝ → 𝕜) :
    ℕ → ℝ → E
  | 0, x => ∫ v in I ∩ Ioi x, K x v • J v
  | k + 1, x => ∫ v in I ∩ Ioi x, K x v • ψ v • picardTerm I K J ψ k v

section Iteration

variable (hI : IsOpen I) (hIo : I.OrdConnected)
  (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
  (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I)
  (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
  (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
  (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
  (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))

omit [NormedSpace ℝ E] in
include hI hψ hQ hQ0 hΨ in
/-- If `F` is continuous on `I` with `‖F v‖ ≤ C * P v` for `v ∈ I ∩ Ioi x`, then
`Q * ‖ψ • F‖` is integrable on `I ∩ Ioi x`. -/
private lemma integrableOn_weight_smul {F : ℝ → E} (hF : ContinuousOn F I) {x C : ℝ}
    (hx : x ∈ I) (hFle : ∀ v ∈ I ∩ Ioi x, ‖F v‖ ≤ C * P v) :
    IntegrableOn (fun v ↦ Q v * ‖ψ v • F v‖) (I ∩ Ioi x) := by
  have hmeas : MeasurableSet (I ∩ Ioi x) := hI.measurableSet.inter measurableSet_Ioi
  have hcont : ContinuousOn (fun v ↦ Q v * ‖ψ v • F v‖) (I ∩ Ioi x) :=
    (hQ.mul (hψ.smul hF).norm).mono inter_subset_left
  refine Integrable.mono' ((hΨ x hx).const_mul C) (hcont.aestronglyMeasurable hmeas) ?_
  filter_upwards [ae_restrict_mem hmeas] with v hv
  have hQψ : 0 ≤ Q v * ‖ψ v‖ := mul_nonneg (hQ0 v hv.1) (norm_nonneg _)
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (hQ0 v hv.1)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))), ← mul_assoc]
  calc Q v * ‖ψ v‖ * ‖F v‖ ≤ Q v * ‖ψ v‖ * (C * P v) :=
        mul_le_mul_of_nonneg_left (hFle v hv) hQψ
    _ = C * (P v * Q v * ‖ψ v‖) := by ring

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
include hI hP0 hQ0 hΦ hΨ in
/-- For `x, v ∈ I` with `x ≤ v` and `f` monotone and nonnegative on `[0, ∞)`, the bound
`P v * Φ v * f (Ψ v)` at `v` is at most `Φ x * f (Ψ x) * P v`. -/
private lemma mul_tail_le_of_le {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0))
    (hf0 : ∀ t, 0 ≤ t → 0 ≤ f t) {x v : ℝ} (hx : x ∈ I) (hvI : v ∈ I) (hv : x ≤ v) :
    P v * (∫ u in I ∩ Ioi v, Q u * ‖J u‖) * f (∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖) ≤
      (∫ u in I ∩ Ioi x, Q u * ‖J u‖) * f (∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖) * P v := by
  have hPv := hP0 v hvI
  have hΦx : 0 ≤ ∫ u in I ∩ Ioi x, Q u * ‖J u‖ :=
    integral_forcing_nonneg hI.measurableSet hQ0 x
  have hΨv : 0 ≤ ∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖ :=
    integral_coeff_nonneg hI.measurableSet hP0 hQ0 v
  have hΨle := antitoneOn_integral_inter_Ioi hI.measurableSet (coeff_weight_nonneg hP0 hQ0)
    hΨ hx hvI hv
  have hfv := hf0 _ hΨv
  calc _ ≤ P v * (∫ u in I ∩ Ioi x, Q u * ‖J u‖) * f (∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖) := by
        gcongr P v * ?_ * ?_
        · exact antitoneOn_integral_inter_Ioi hI.measurableSet (forcing_weight_nonneg hQ0)
            hΦ hx hvI hv
        · exact hf hΨv (hΨv.trans hΨle) hΨle
    _ = _ := by ring

include hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ

/-- The Picard increments are continuous on `I`, and the `k`-th is bounded by
`P x * Φ x * (Ψ x ^ k / k!)`. -/
private lemma picardTerm_spec (k : ℕ) :
    ContinuousOn (picardTerm I K J ψ k) I ∧ ∀ x ∈ I, ‖picardTerm I K J ψ k x‖ ≤
      P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        ((∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !) := by
  induction k with
  | zero =>
    refine ⟨continuousOn_integral_kernel_smul hI hK hKle hP hQ0 hJ hΦ, fun x hx ↦ ?_⟩
    simpa [picardTerm] using norm_integral_kernel_smul_le hI hKle hx (hΦ x hx)
  | succ k ih =>
    obtain ⟨hcont, hle⟩ := ih
    have hFint : ∀ x ∈ I,
        IntegrableOn (fun v ↦ Q v * ‖ψ v • picardTerm I K J ψ k v‖) (I ∩ Ioi x) := fun x hx ↦
      integrableOn_weight_smul hI hψ hQ hQ0 hΨ hcont hx (C := (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        ((∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !)) fun v hv ↦
        (hle v hv.1).trans (mul_tail_le_of_le hI hP0 hQ0 hΦ hΨ (f := fun t ↦ t ^ k / k !)
          (fun s (hs : 0 ≤ s) _ _ hst ↦ by dsimp only; gcongr) (fun _ _ ↦ by positivity)
          hx hv.1 hv.2.le)
    refine ⟨continuousOn_integral_kernel_smul hI hK hKle hP hQ0 (hψ.smul hcont) hFint,
      fun x hx ↦ ?_⟩
    set Φx := ∫ v in I ∩ Ioi x, Q v * ‖J v‖
    set g : ℝ → ℝ := fun v ↦ P v * Q v * ‖ψ v‖ with hg
    refine (norm_integral_kernel_smul_le hI hKle hx (hFint x hx)).trans ?_
    have hint : ∫ v in I ∩ Ioi x, Q v * ‖ψ v • picardTerm I K J ψ k v‖ ≤
        Φx / k ! * ∫ v in I ∩ Ioi x, g v * (∫ u in I ∩ Ioi v, g u) ^ k := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hFint x hx)
        (((hΨ x hx).mul_pow_integral_inter_Ioi hI hIo hx k).const_mul _)
        (hI.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_
      have := hP0 v hv.1
      have := hQ0 v hv.1
      have := integral_coeff_nonneg (ψ := ψ) hI.measurableSet hP0 hQ0 v
      have hΦle : ∫ u in I ∩ Ioi v, Q u * ‖J u‖ ≤ Φx :=
        antitoneOn_integral_inter_Ioi hI.measurableSet (forcing_weight_nonneg hQ0)
          hΦ hx hv.1 hv.2.le
      rw [norm_smul, ← mul_assoc]
      calc Q v * ‖ψ v‖ * ‖picardTerm I K J ψ k v‖
          ≤ Q v * ‖ψ v‖ * (P v * Φx * ((∫ u in I ∩ Ioi v, g u) ^ k / k !)) := by
            grw [hle v hv.1, hΦle]
        _ = Φx / k ! * (g v * (∫ u in I ∩ Ioi v, g u) ^ k) := by simp only [hg]; ring
    rw [(hΨ x hx).integral_inter_Ioi_mul_pow_integral_inter_Ioi hI hIo hx k] at hint
    calc P x * ∫ v in I ∩ Ioi x, Q v * ‖ψ v • picardTerm I K J ψ k v‖
        ≤ P x * (Φx / k ! * ((∫ u in I ∩ Ioi x, g u) ^ (k + 1) / (k + 1))) :=
          mul_le_mul_of_nonneg_left hint (hP0 x hx)
      _ = P x * Φx * ((∫ u in I ∩ Ioi x, g u) ^ (k + 1) / (k + 1)!) := by
          rw [Nat.factorial_succ]; push_cast; field_simp

/-- At points `v ∈ I` with `x ≤ v`, the `k`-th Picard increment is at most
`Φ x * (Ψ x ^ k / k!) * P v`. -/
private lemma norm_picardTerm_le_of_le (k : ℕ) {x v : ℝ} (hx : x ∈ I) (hvI : v ∈ I) (hv : x ≤ v) :
    ‖picardTerm I K J ψ k v‖ ≤ (∫ u in I ∩ Ioi x, Q u * ‖J u‖) *
      ((∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖) ^ k / k !) * P v :=
  ((picardTerm_spec hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 v hvI).trans
    (mul_tail_le_of_le hI hP0 hQ0 hΦ hΨ (f := fun t ↦ t ^ k / k !)
      (fun s (hs : 0 ≤ s) _ _ hst ↦ by dsimp only; gcongr) (fun _ _ ↦ by positivity) hx hvI hv)

/-- The sum of the Picard increments is bounded by `P x * Φ x * exp (Ψ x)`. -/
private lemma norm_tsum_picardTerm_le {x : ℝ} (hx : x ∈ I) :
    ‖∑' k, picardTerm I K J ψ k x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) :=
  tsum_of_norm_bounded (by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)).mul_left
      (P x * ∫ v in I ∩ Ioi x, Q v * ‖J v‖))
    fun k ↦ (picardTerm_spec hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 x hx

variable [CompleteSpace E]

/-- The Picard increments are summable at every point of `I`. -/
private lemma summable_picardTerm {x : ℝ} (hx : x ∈ I) :
    Summable fun k ↦ picardTerm I K J ψ k x :=
  ((Real.summable_pow_div_factorial (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)).mul_left
    (P x * ∫ v in I ∩ Ioi x, Q v * ‖J v‖)).of_norm_bounded
    fun k ↦ (picardTerm_spec hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 x hx

/-- The sum of the Picard increments is continuous on `I`: near each `x₀ ∈ I` the series
converges uniformly, being dominated by an exponential series. -/
private lemma continuousOn_tsum_picardTerm :
    ContinuousOn (fun x ↦ ∑' k, picardTerm I K J ψ k x) I := by
  intro x₀ hx₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨c, d, _, hmem, hcd⟩ := exists_Icc_mem_subset_of_mem_nhds (hI.mem_nhds hx₀)
  obtain ⟨hcx, hxd⟩ : x₀ ∈ Ioo c d := by
    simpa only [interior_Icc] using (mem_interior_iff_mem_nhds.2 hmem : x₀ ∈ interior (Icc c d))
  have hcI : c ∈ I := hcd ⟨le_rfl, (hcx.trans hxd).le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hcd)
  refine (continuousOn_tsum
    (fun k ↦ (picardTerm_spec hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).1.mono hcd)
    ((Real.summable_pow_div_factorial (∫ v in I ∩ Ioi c, P v * Q v * ‖ψ v‖)).mul_left
      ((∫ v in I ∩ Ioi c, Q v * ‖J v‖) * M))
    fun k x hx ↦ ?_).continuousAt hmem
  have := integral_forcing_nonneg (J := J) hI.measurableSet hQ0 c
  have := integral_coeff_nonneg (ψ := ψ) hI.measurableSet hP0 hQ0 c
  refine (norm_picardTerm_le_of_le hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hcI (hcd hx)
    hx.1).trans ?_
  calc _ ≤ (∫ u in I ∩ Ioi c, Q u * ‖J u‖) *
          ((∫ u in I ∩ Ioi c, P u * Q u * ‖ψ u‖) ^ k / k !) * M :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM x hx)) (by positivity)
    _ = _ := by ring

/-- The sum of the Picard increments solves the Volterra equation on `I`. -/
private lemma tsum_picardTerm_eq {x : ℝ} (hx : x ∈ I) :
    ∑' k, picardTerm I K J ψ k x = ∫ v in I ∩ Ioi x,
      K x v • (J v + ψ v • ∑' k, picardTerm I K J ψ k v) := by
  set T := picardTerm I K J ψ
  set h : ℝ → E := fun x ↦ ∑' k, T k x with h_def
  set Φx := ∫ u in I ∩ Ioi x, Q u * ‖J u‖
  set Ψx := ∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖
  have hspec := picardTerm_spec hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hcont : ContinuousOn h I :=
    continuousOn_tsum_picardTerm hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hψh : IntegrableOn (fun v ↦ Q v * ‖ψ v • h v‖) (I ∩ Ioi x) :=
    integrableOn_weight_smul hI hψ hQ hQ0 hΨ hcont hx (C := Φx * Real.exp Ψx) fun v hv ↦
      (norm_tsum_picardTerm_le hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hv.1).trans
        (mul_tail_le_of_le hI hP0 hQ0 hΦ hΨ (Real.exp_monotone.monotoneOn _)
          (fun _ _ ↦ (Real.exp_pos _).le) hx hv.1 hv.2.le)
  have hKJ := integrableOn_kernel_smul hI hK hKle hJ hx (hΦ x hx)
  have hKψh : IntegrableOn (fun v ↦ K x v • ψ v • h v) (I ∩ Ioi x) :=
    integrableOn_kernel_smul hI hK hKle (hψ.smul hcont) hx hψh
  simp only [smul_add]; rw [integral_add hKJ hKψh]
  have hTle (k : ℕ) (v : ℝ) (hvI : v ∈ I) (hv : x ≤ v) :
      ‖T k v‖ ≤ Φx * (Ψx ^ k / k !) * P v :=
    norm_picardTerm_le_of_le hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hx hvI hv
  have hFk (k : ℕ) : IntegrableOn (fun v ↦ K x v • ψ v • T k v) (I ∩ Ioi x) :=
    integrableOn_kernel_smul hI hK hKle (hψ.smul (hspec k).1) hx
      (integrableOn_weight_smul hI hψ hQ hQ0 hΨ (hspec k).1 hx fun v hv ↦ hTle k v hv.1 hv.2.le)
  have hsum : Summable fun k ↦ ∫ v in I ∩ Ioi x, ‖K x v • ψ v • T k v‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial Ψx).mul_left (P x * Φx * Ψx))
    refine (setIntegral_mono_on (hFk k).norm ((hΨ x hx).const_mul (P x * Φx * (Ψx ^ k / k !)))
      (hI.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_).trans_eq
      (by rw [integral_const_mul]; ring)
    refine (norm_kernel_smul_le hKle hx hv.1 hv.2 _).trans ?_
    rw [norm_smul]; have := hP0 x hx; have := hQ0 v hv.1
    calc P x * (Q v * (‖ψ v‖ * ‖T k v‖))
        ≤ P x * (Q v * (‖ψ v‖ * (Φx * (Ψx ^ k / k !) * P v))) := by grw [hTle k v hv.1 hv.2.le]
      _ = P x * Φx * (Ψx ^ k / k !) * (P v * Q v * ‖ψ v‖) := by ring
  have hser := hasSum_integral_of_summable_integral_norm hFk hsum
  have hinner (v : ℝ) : ∑' k, K x v • ψ v • T k v = K x v • ψ v • h v := by
    rw [h_def, tsum_const_smul'', tsum_const_smul'']
  simp only [hinner] at hser
  calc h x = T 0 x + ∑' k, T (k + 1) x := (summable_picardTerm hI hIo hK hJ hψ hP hQ hP0 hQ0
        hKle hΦ hΨ hx).tsum_eq_zero_add
    _ = _ := by rw [← hser.tsum_eq]; simp only [T, picardTerm]

/-- **Volterra integral equations on an open interval, existence.** Let `I ⊆ ℝ` be an open
interval, let `K` be continuous on `{(x, v) | x ∈ I ∧ v ∈ I ∧ x < v}` with
`‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are continuous on `I`, and let `J`, `ψ` be
continuous on `I` such that `Φ x = ∫ v in I ∩ Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖` converge for every `x ∈ I`. Then the Volterra integral
equation `h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)` has a continuous solution `h` on `I`
with `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x ∈ I` (Olver, Chapter 6, Theorem 10.1). -/
theorem exists_volterra_solution_on :
    ∃ h : ℝ → E, ContinuousOn h I ∧
      (∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) :=
  ⟨fun x ↦ ∑' k, picardTerm I K J ψ k x,
    continuousOn_tsum_picardTerm hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ,
    fun _ hx ↦ tsum_picardTerm_eq hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hx,
    fun _ hx ↦ norm_tsum_picardTerm_le hI hIo hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hx⟩

end Iteration

/-! ### Uniqueness and a priori bounds -/

/-- Any function satisfying the Volterra exponential bound on an upper tail `I ∩ Ici x₀` is `O(P)`
there. -/
theorem isBigO_of_norm_le_volterra_bound_on {F G : Type*} [SeminormedAddCommGroup F]
    [SeminormedAddCommGroup G] {J h : ℝ → G} {ψ : ℝ → F} {x₀ : ℝ} (hI : MeasurableSet I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x₀))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x₀))
    (hle : ∀ x ∈ I ∩ Ici x₀, ‖h x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)) :
    h =O[𝓟 (I ∩ Ici x₀)] P := by
  refine Asymptotics.isBigO_iff.2 ⟨(∫ u in I ∩ Ioi x₀, Q u * ‖J u‖) *
    Real.exp (∫ u in I ∩ Ioi x₀, P u * Q u * ‖ψ u‖), eventually_principal.2 fun v hv ↦ ?_⟩
  rw [Real.norm_of_nonneg (hP0 v hv.1)]
  have hmeas : MeasurableSet (I ∩ Ioi x₀) := hI.inter measurableSet_Ioi
  have hsub : I ∩ Ioi v ≤ᵐ[volume] I ∩ Ioi x₀ :=
    (inter_subset_inter_right I (Ioi_subset_Ioi hv.2)).eventuallySubset
  have hΦle := setIntegral_mono_set hΦ ((ae_restrict_iff' hmeas).2
    (ae_of_all _ fun u hu ↦ mul_nonneg (hQ0 u hu.1) (norm_nonneg _))) hsub
  have hΨle := setIntegral_mono_set hΨ ((ae_restrict_iff' hmeas).2
    (ae_of_all _ fun u hu ↦ mul_nonneg (mul_nonneg (hP0 u hu.1) (hQ0 u hu.1)) (norm_nonneg _))) hsub
  have hΦ0 : 0 ≤ ∫ u in I ∩ Ioi x₀, Q u * ‖J u‖ :=
    setIntegral_nonneg hmeas fun u hu ↦ mul_nonneg (hQ0 u hu.1) (norm_nonneg _)
  have := hP0 v hv.1
  calc ‖h v‖ ≤ P v * (∫ u in I ∩ Ioi v, Q u * ‖J u‖) *
          Real.exp (∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖) := hle v hv
    _ ≤ P v * (∫ u in I ∩ Ioi x₀, Q u * ‖J u‖) *
          Real.exp (∫ u in I ∩ Ioi x₀, P u * Q u * ‖ψ u‖) := by gcongr
    _ = _ := by ring

/-- When `‖K x v‖ ≤ 0 * Q v` above `x ∈ I`, any Volterra solution vanishes at `x`. -/
private lemma eq_zero_of_bound_zero
    (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ 0 * Q v)
    {h : ℝ → E} (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x : ℝ} (hx : x ∈ I) : h x = 0 := by
  rw [heq x hx]
  refine setIntegral_eq_zero_of_forall_eq_zero fun v hv ↦ ?_
  have hK0 : ‖K x v‖ ≤ 0 := by simpa only [zero_mul] using hKle x v hx hv.1 hv.2
  rw [norm_le_zero_iff.1 hK0, zero_smul]

/-- Exponential Grönwall bound on an upper tail `I ∩ Ici x`: if `w v ≤ C * p v` on `I ∩ Ici x`
and the operator `M ↦ p v * (A + ∫ u in I ∩ Ioi v, g u * (B + M u))` dominates `w` whenever
`w ≤ p * M` on `I ∩ Ioi v`, then `w x ≤ p x * (A * exp (Ψ x) + B * (exp (Ψ x) - 1))`. -/
private lemma volterra_gronwall_inter_Ioi (hI : IsOpen I) (hIo : I.OrdConnected)
    {p g w : ℝ → ℝ} (hp0 : ∀ v ∈ I, 0 ≤ p v) (hg0 : ∀ v ∈ I, 0 ≤ g v)
    (hg : ∀ v ∈ I, IntegrableOn g (I ∩ Ioi v))
    {A B C x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : x ∈ I)
    (hC : ∀ v ∈ I ∩ Ici x, w v ≤ C * p v)
    (hstep : ∀ v ∈ I ∩ Ici x, ∀ M : ℝ → ℝ, (∀ u ∈ I ∩ Ioi v, w u ≤ p u * M u) →
      IntegrableOn (fun u ↦ g u * (B + M u)) (I ∩ Ioi v) →
      w v ≤ p v * (A + ∫ u in I ∩ Ioi v, g u * (B + M u))) :
    w x ≤ p x * (A * Real.exp (∫ u in I ∩ Ioi x, g u) +
      B * (Real.exp (∫ u in I ∩ Ioi x, g u) - 1)) := by
  set Ψ : ℝ → ℝ := fun v ↦ ∫ u in I ∩ Ioi v, g u
  set T : ℝ → ℝ := fun v ↦ A * Real.exp (Ψ v) + B * (Real.exp (Ψ v) - 1)
  have hΨ0 (v : ℝ) : 0 ≤ Ψ v :=
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi) fun u hu ↦ hg0 u hu.1
  -- By induction on `k`, iterating the bound shrinks the `O(p)` error by `Ψ ^ k / k!`.
  have hind (k : ℕ) : ∀ v ∈ I ∩ Ici x, w v ≤ p v * (T v + C * (Ψ v ^ k / k !)) := by
    induction k with
    | zero =>
      intro v hv
      have hT0 : 0 ≤ T v := add_nonneg (mul_nonneg hA (Real.exp_pos _).le)
        (mul_nonneg hB (sub_nonneg.2 (Real.one_le_exp (hΨ0 v))))
      simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] using
        (hC v hv).trans (mul_comm C (p v) ▸
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hT0) (hp0 v hv.1))
    | succ k ih =>
      intro v hv
      set M : ℝ → ℝ := fun u ↦ T u + C * (Ψ u ^ k / k !)
      have hBM (u : ℝ) : g u * (B + M u) =
          (A + B) * (g u * Real.exp (Ψ u)) + C / k ! * (g u * Ψ u ^ k) := by dsimp only [M, T]; ring
      have hexp := ((hg v hv.1).mul_exp_integral_inter_Ioi hI hIo hv.1).const_mul (A + B)
      have hpow := ((hg v hv.1).mul_pow_integral_inter_Ioi hI hIo hv.1 k).const_mul (C / k !)
      have hint : IntegrableOn (fun u ↦ g u * (B + M u)) (I ∩ Ioi v) :=
        (hexp.add hpow).congr (ae_of_all _ fun u ↦ (hBM u).symm)
      refine (hstep v hv M (fun u hu ↦ ih u ⟨hu.1, hv.2.trans hu.2.le⟩) hint).trans_eq ?_
      rw [setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi) fun u _ ↦ hBM u,
        integral_add hexp hpow, integral_const_mul, integral_const_mul]
      dsimp only [T, Ψ]
      rw [(hg v hv.1).integral_inter_Ioi_mul_exp_integral_inter_Ioi hI hIo hv.1,
        (hg v hv.1).integral_inter_Ioi_mul_pow_integral_inter_Ioi hI hIo hv.1 k]
      congr 1; rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have htend : Tendsto (fun k : ℕ ↦ p x * T x + p x * C * (Ψ x ^ k / k !))
      atTop (𝓝 (p x * T x)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
      ((Real.summable_pow_div_factorial (Ψ x)).tendsto_atTop_zero.const_mul (p x * C))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend fun k ↦ by
    simpa only [mul_add, mul_assoc] using hind k x ⟨hx, le_rfl⟩

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- Reduction for the sharper constant-`P₀` case (`P₀ > 0`, `‖J‖ ≤ ‖ψ‖`): derives integrability of
`Q * ‖J‖` and `P₀ * Q * ‖ψ‖`, and rescales `h = O(1)` to `h = O(P₀)`. -/
private lemma sharp_volterra_setup (hI : IsOpen I) (hJ : ContinuousOn J I) (hQ : ContinuousOn Q I)
    (hQ0 : ∀ x ∈ I, 0 ≤ Q x) {P₀ : ℝ} (hP₀pos : 0 < P₀) (hJle : ∀ x ∈ I, ‖J x‖ ≤ ‖ψ x‖)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} {x₀ : ℝ} (hO : h =O[𝓟 (I ∩ Ici x₀)] (fun _ ↦ (1 : ℝ))) :
    (∀ y ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi y)) ∧
    (∀ y ∈ I, IntegrableOn (fun v ↦ P₀ * Q v * ‖ψ v‖) (I ∩ Ioi y)) ∧
    h =O[𝓟 (I ∩ Ici x₀)] (fun _ ↦ P₀) := by
  refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_, hO.trans ?_⟩
  · have hmeas : MeasurableSet (I ∩ Ioi y) := hI.measurableSet.inter measurableSet_Ioi
    refine Integrable.mono' (hΦ y hy)
      (((hQ.mul hJ.norm).mono inter_subset_left).aestronglyMeasurable hmeas) ?_
    filter_upwards [ae_restrict_mem hmeas] with v hv
    rw [Real.norm_of_nonneg (mul_nonneg (hQ0 v hv.1) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hJle v hv.1) (hQ0 v hv.1)
  · exact ((hΦ y hy).const_mul P₀).congr (ae_of_all _ fun _ ↦ (mul_assoc _ _ _).symm)
  · exact Asymptotics.isBigO_iff.2 ⟨P₀⁻¹, eventually_principal.2 fun _ _ ↦ by
      rw [norm_one, Real.norm_of_nonneg hP₀pos.le, inv_mul_cancel₀ hP₀pos.ne']⟩

section Uniqueness

variable (hI : IsOpen I) (hIo : I.OrdConnected)
  (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
  (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
  (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
  (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
  (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))

include hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- A continuous Volterra solution that is `O(P)` on a single upper tail `I ∩ Ici x₀` has
`Q * ‖J + ψ • h‖` integrable on every upper tail `I ∩ Ioi x` and is `O(P)` on every upper tail
`I ∩ Ici x`. -/
private lemma exists_bound_and_integrableOn_of_isBigO {h : ℝ → E} (hh : ContinuousOn h I)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hO : h =O[𝓟 (I ∩ Ici x₀)] P) :
    (∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v + ψ v • h v‖) (I ∩ Ioi x)) ∧
    ∀ x ∈ I, ∃ C ≥ 0, ∀ v ∈ I ∩ Ici x, ‖h v‖ ≤ C * P v := by
  obtain ⟨C₀, hC₀⟩ := Asymptotics.isBigO_iff.1 hO
  set C := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ v ∈ I ∩ Ici x₀, ‖h v‖ ≤ C * P v := fun v hv ↦ by
    have h1 := eventually_principal.1 hC₀ v hv
    rw [Real.norm_of_nonneg (hP0 v hv.1)] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hP0 v hv.1))
  have hcontF := hQ.mul (continuousOn_forcing_add hJ hψ hh).norm
  -- Step 1: integrability on tails starting at `x ≥ x₀`, then propagated left across `(x, x₀]`.
  have hint_ge (x : ℝ) (hx : x ∈ I) (hxx₀ : x₀ ≤ x) :
      IntegrableOn (fun v ↦ Q v * ‖J v + ψ v • h v‖) (I ∩ Ioi x) := by
    have hmeas : MeasurableSet (I ∩ Ioi x) := hI.measurableSet.inter measurableSet_Ioi
    refine Integrable.mono' ((hΦ x hx).add ((hΨ x hx).const_mul C))
      ((hcontF.mono inter_subset_left).aestronglyMeasurable hmeas) ?_
    filter_upwards [ae_restrict_mem hmeas] with v hv
    have hQv := hQ0 v hv.1
    rw [Real.norm_of_nonneg (mul_nonneg hQv (norm_nonneg _))]
    calc Q v * ‖J v + ψ v • h v‖ ≤ Q v * (‖J v‖ + ‖ψ v‖ * ‖h v‖) := by
          gcongr; exact (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ Q v * (‖J v‖ + ‖ψ v‖ * (C * P v)) := by gcongr; exact hC v ⟨hv.1, hxx₀.trans hv.2.le⟩
      _ = Q v * ‖J v‖ + C * (P v * Q v * ‖ψ v‖) := by ring
  have hint (x : ℝ) (hx : x ∈ I) : IntegrableOn (fun v ↦ Q v * ‖J v + ψ v • h v‖) (I ∩ Ioi x) := by
    rcases le_or_gt x₀ x with hle | hlt
    · exact hint_ge x hx hle
    · rw [hIo.inter_Ioi_eq_Ioc_union hx hx₀ hlt.le]
      exact ((hcontF.mono (hIo.out hx hx₀)).integrableOn_Icc.mono_set Ioc_subset_Icc_self).union
        (hint_ge x₀ hx₀ le_rfl)
  -- Step 2: propagate the `O(P)` bound left from `x₀` using the integral equation itself.
  refine ⟨hint, fun x hx ↦ ?_⟩
  rcases le_or_gt x₀ x with hle | _
  · exact ⟨C, hC0, fun v hv ↦ hC v ⟨hv.1, hle.trans hv.2⟩⟩
  · set M := ∫ v in I ∩ Ioi x, Q v * ‖J v + ψ v • h v‖
    refine ⟨max C M, hC0.trans (le_max_left _ _), fun v hv ↦ ?_⟩
    rcases le_or_gt x₀ v with hge | _
    · exact (hC v ⟨hv.1, hge⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hP0 v hv.1))
    · rw [heq v hv.1]
      refine (norm_integral_kernel_smul_le hI hKle hv.1 (hint v hv.1)).trans ?_
      have hMle := antitoneOn_integral_inter_Ioi hI.measurableSet
        (fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _)) hint hx hv.1 hv.2
      calc P v * ∫ u in I ∩ Ioi v, Q u * ‖J u + ψ u • h u‖ ≤ P v * M :=
            mul_le_mul_of_nonneg_left hMle (hP0 v hv.1)
        _ ≤ max C M * P v := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hP0 v hv.1)

include hI hIo hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on an open interval, uniqueness.** Two continuous solutions on an
open interval `I` that are `O(P)` on (possibly different) upper tails agree everywhere on `I`
(Olver, Chapter 6, Theorem 10.1). -/
theorem volterra_solution_unique_on {h₁ h₂ : ℝ → E}
    (hh₁ : ContinuousOn h₁ I) (hh₂ : ContinuousOn h₂ I)
    (heq₁ : ∀ x ∈ I, h₁ x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h₁ v))
    (heq₂ : ∀ x ∈ I, h₂ x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h₂ v))
    {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ I) (hx₂ : x₂ ∈ I)
    (hO₁ : h₁ =O[𝓟 (I ∩ Ici x₁)] P) (hO₂ : h₂ =O[𝓟 (I ∩ Ici x₂)] P) :
    EqOn h₁ h₂ I := by
  obtain ⟨hint₁, hbd₁⟩ :=
    exists_bound_and_integrableOn_of_isBigO hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh₁ heq₁ hx₁ hO₁
  obtain ⟨hint₂, hbd₂⟩ :=
    exists_bound_and_integrableOn_of_isBigO hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh₂ heq₂ hx₂ hO₂
  intro x hx
  obtain ⟨C₁, _, hC₁⟩ := hbd₁ x hx
  obtain ⟨C₂, _, hC₂⟩ := hbd₂ x hx
  have hC (v : ℝ) (hv : v ∈ I ∩ Ici x) : ‖h₁ v - h₂ v‖ ≤ (C₁ + C₂) * P v :=
    (norm_sub_le _ _).trans (by simpa only [add_mul] using add_le_add (hC₁ v hv) (hC₂ v hv))
  -- `h₁ - h₂` solves the homogeneous Volterra equation on `I`.
  have hdeq : ∀ v ∈ I, h₁ v - h₂ v = ∫ u in I ∩ Ioi v, K v u • (ψ u • (h₁ u - h₂ u)) := by
    intro v hv
    have hi₁ := integrableOn_kernel_smul hI hK hKle (continuousOn_forcing_add hJ hψ hh₁) hv
      (hint₁ v hv)
    have hi₂ := integrableOn_kernel_smul hI hK hKle (continuousOn_forcing_add hJ hψ hh₂) hv
      (hint₂ v hv)
    rw [heq₁ v hv, heq₂ v hv, ← integral_sub hi₁ hi₂]
    refine setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi) fun u _ ↦ ?_
    simp only [smul_add, add_sub_add_left_eq_sub, ← smul_sub]
  refine sub_eq_zero.1 (norm_le_zero_iff.1 ?_)
  have hgr := volterra_gronwall_inter_Ioi hI hIo hP0 (coeff_weight_nonneg hP0 hQ0) hΨ
    le_rfl le_rfl hx (w := fun v ↦ ‖h₁ v - h₂ v‖) (C := C₁ + C₂) hC fun v hv M hM hintM ↦ by
      have hFint : IntegrableOn (fun u ↦ Q u * ‖ψ u • (h₁ u - h₂ u)‖) (I ∩ Ioi v) :=
        integrableOn_weight_smul hI hψ hQ hQ0 hΨ (hh₁.sub hh₂) hv.1 (C := C₁ + C₂)
          fun u hu ↦ hC u ⟨hu.1, hv.2.trans hu.2.le⟩
      rw [hdeq v hv.1, zero_add]
      refine (norm_integral_kernel_smul_le hI hKle hv.1 hFint).trans
        (mul_le_mul_of_nonneg_left (setIntegral_mono_on hFint hintM
          (hI.measurableSet.inter measurableSet_Ioi) fun u hu ↦ ?_) (hP0 v hv.1))
      rw [norm_smul, ← mul_assoc]
      calc Q u * ‖ψ u‖ * ‖h₁ u - h₂ u‖ ≤ Q u * ‖ψ u‖ * (P u * M u) :=
            mul_le_mul_of_nonneg_left (hM u hu) (mul_nonneg (hQ0 u hu.1) (norm_nonneg _))
        _ = P u * Q u * ‖ψ u‖ * (0 + M u) := by ring
  simpa only [zero_mul, add_zero, mul_zero] using hgr

include hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on an open interval, a priori bound.** Every continuous solution
`h` on an open interval `I` with `h = O(P)` on some upper tail `I ∩ Ici x₀` obeys
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)` at every `x ∈ I` (Olver, Chapter 6, Theorem 10.1). -/
theorem norm_volterra_solution_le_on {h : ℝ → E} (hh : ContinuousOn h I)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hO : h =O[𝓟 (I ∩ Ici x₀)] P) {x : ℝ} (hx : x ∈ I) :
    ‖h x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨hint, hbd⟩ :=
    exists_bound_and_integrableOn_of_isBigO hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh heq hx₀ hO
  obtain ⟨C, _, hC⟩ := hbd x hx
  have hgr := volterra_gronwall_inter_Ioi hI hIo hP0 (coeff_weight_nonneg hP0 hQ0) hΨ
    (integral_forcing_nonneg (J := J) hI.measurableSet hQ0 x) le_rfl hx (w := fun v ↦ ‖h v‖)
    (C := C) hC fun v hv M hM hintM ↦ by
      rw [heq v hv.1]
      refine (norm_integral_kernel_smul_le hI hKle hv.1 (hint v hv.1)).trans
        (mul_le_mul_of_nonneg_left ?_ (hP0 v hv.1))
      have hstep : ∫ u in I ∩ Ioi v, Q u * ‖J u + ψ u • h u‖ ≤
          ∫ u in I ∩ Ioi v, (Q u * ‖J u‖ + P u * Q u * ‖ψ u‖ * (0 + M u)) :=
        setIntegral_mono_on (hint v hv.1) ((hΦ v hv.1).add hintM)
          (hI.measurableSet.inter measurableSet_Ioi) fun u hu ↦ by
            have hQu := hQ0 u hu.1
            calc Q u * ‖J u + ψ u • h u‖ ≤ Q u * (‖J u‖ + ‖ψ u‖ * ‖h u‖) := by
                  gcongr; exact (norm_add_le _ _).trans (by rw [norm_smul])
              _ ≤ Q u * (‖J u‖ + ‖ψ u‖ * (P u * M u)) := by gcongr; exact hM u hu
              _ = Q u * ‖J u‖ + P u * Q u * ‖ψ u‖ * (0 + M u) := by ring
      rw [integral_add (hΦ v hv.1) hintM] at hstep
      exact hstep.trans (add_le_add (antitoneOn_integral_inter_Ioi hI.measurableSet
        (forcing_weight_nonneg hQ0) hΦ hx hv.1 hv.2) le_rfl)
  simpa only [zero_mul, add_zero, ← mul_assoc] using hgr

include hI hIo hJ hψ hQ hQ0 in
/-- **Volterra integral equations on an open interval, sharper bound.** When `P` is a nonnegative
constant `P₀` and `‖J‖ ≤ ‖ψ‖` on `I` (in particular when `J = ψ`), every continuous solution `h`
that is bounded on some upper tail `I ∩ Ici x₀` satisfies
`‖h x‖ ≤ exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖) - 1` (Olver, Chapter 6, Theorem 10.1). -/
theorem norm_volterra_solution_le_exp_sub_one_on {P₀ : ℝ} (hP₀ : 0 ≤ P₀)
    (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hJle : ∀ x ∈ I, ‖J x‖ ≤ ‖ψ x‖)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hO : h =O[𝓟 (I ∩ Ici x₀)] (fun _ ↦ (1 : ℝ))) {x : ℝ} (hx : x ∈ I) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖) - 1 := by
  rcases hP₀.eq_or_lt with rfl | hP₀pos
  · simp [eq_zero_of_bound_zero hKle heq hx]
  obtain ⟨hΦJ, hΨ, hOP₀⟩ := sharp_volterra_setup hI hJ hQ hQ0 hP₀pos hJle hΦ hO
  obtain ⟨hint, hbd⟩ := exists_bound_and_integrableOn_of_isBigO (P := fun _ ↦ P₀)
    hI hIo hJ hψ hQ (fun _ _ ↦ hP₀pos.le) hQ0 hKle hΦJ hΨ hh heq hx₀ hOP₀
  obtain ⟨C', _, hC'⟩ := hbd x hx
  have hgr := volterra_gronwall_inter_Ioi hI hIo (p := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ zero_le_one)
    (coeff_weight_nonneg (P := fun _ ↦ P₀) (fun _ _ ↦ hP₀pos.le) hQ0) hΨ le_rfl zero_le_one hx
    (w := fun v ↦ ‖h v‖) (C := C' * P₀) (fun v hv ↦ by simpa only [mul_one] using hC' v hv)
    fun v hv M hM hintM ↦ by
      rw [heq v hv.1, one_mul, zero_add]
      refine (norm_integral_kernel_smul_le (P := fun _ ↦ P₀) hI hKle hv.1 (hint v hv.1)).trans ?_
      rw [← integral_const_mul]
      refine setIntegral_mono_on ((hint v hv.1).const_mul P₀) hintM
        (hI.measurableSet.inter measurableSet_Ioi) fun u hu ↦ ?_
      have hQu := hQ0 u hu.1
      calc P₀ * (Q u * ‖J u + ψ u • h u‖)
          ≤ P₀ * (Q u * (‖ψ u‖ + ‖ψ u‖ * ‖h u‖)) := by
            gcongr; exact (norm_add_le _ _).trans (add_le_add (hJle u hu.1) (by rw [norm_smul]))
        _ ≤ P₀ * (Q u * (‖ψ u‖ + ‖ψ u‖ * (1 * M u))) := by gcongr; exact hM u hu
        _ = P₀ * Q u * ‖ψ u‖ * (1 + M u) := by ring
  simpa only [one_mul, zero_mul, zero_add, mul_assoc, integral_const_mul] using hgr

end Uniqueness

/-! ### Differentiability, `C¹` regularity, and derivative bounds -/

section Differentiability

variable [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 E]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Mean value bound for the difference quotient of `u ↦ K u v`: on `[c, d] ⊆ I`, if `x ≠ x₀` and
`max x x₀ < v`, then `‖slope (fun u ↦ K u v) x₀ x • F v‖ ≤ M₁ * (Q v * ‖F v‖)`. -/
private lemma norm_slope_kernel_smul_le {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} {F : ℝ → E}
    {c d x₀ x v M₁ : ℝ} (hcd : Icc c d ⊆ I)
    (hKderiv : ∀ u w, u ∈ I → w ∈ I → u < w → HasDerivAt (fun t ↦ K t w) (K₁ u w) u)
    (hK₁le : ∀ u w, u ∈ I → w ∈ I → u < w → ‖K₁ u w‖ ≤ P₁ u * Q w)
    (hP₁M : ∀ u ∈ Icc c d, P₁ u ≤ M₁) (hQ0 : 0 ≤ Q v)
    (hx₀ : x₀ ∈ Icc c d) (hx : x ∈ Icc c d) (hne : x ≠ x₀) (hvI : v ∈ I)
    (hmax : max x x₀ < v) :
    ‖slope (fun u ↦ K u v) x₀ x • F v‖ ≤ M₁ * (Q v * ‖F v‖) := by
  have huIcc : uIcc x₀ x ⊆ Icc c d := uIcc_subset_Icc hx₀ hx
  have hmvt : ‖K x v - K x₀ v‖ ≤ (M₁ * Q v) * ‖x - x₀‖ :=
    (convex_uIcc x₀ x).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu ↦ (hKderiv u v (hcd (huIcc hu)) hvI
        (lt_of_le_of_lt (hu.2.trans (by simp [max_comm])) hmax)).hasDerivWithinAt)
      (fun u hu ↦ (hK₁le u v (hcd (huIcc hu)) hvI
        (lt_of_le_of_lt (hu.2.trans (by simp [max_comm])) hmax)).trans
        (mul_le_mul_of_nonneg_right (hP₁M u (huIcc hu)) hQ0))
      left_mem_uIcc right_mem_uIcc
  rw [slope_def_module, norm_smul, norm_smul, norm_inv, Real.norm_eq_abs, ← mul_assoc]
  have hq : |x - x₀|⁻¹ * ‖K x v - K x₀ v‖ ≤ M₁ * Q v := by
    calc |x - x₀|⁻¹ * ‖K x v - K x₀ v‖
        ≤ |x - x₀|⁻¹ * ((M₁ * Q v) * |x - x₀|) := by
          gcongr; simpa only [Real.norm_eq_abs] using hmvt
      _ = M₁ * Q v := by field_simp [(abs_pos.2 (sub_ne_zero.2 hne)).ne']
  exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)

omit [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] in
/-- The boundary integrals from shifting the lower limit of `∫ v in I ∩ Ioi x, K x v • F v`
vanish after dividing by `x - x₀` when `K x₀ x₀ = 0` and `K` is continuous up to the diagonal. -/
private lemma tendsto_inv_smul_integral_Ioc_zero
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0) {F : ℝ → E} (hF : ContinuousOn F I)
    {x₀ c d : ℝ} (hx₀ : x₀ ∈ I) (hcx : c < x₀) (hxd : x₀ < d) (hcd : Icc c d ⊆ I) :
    Tendsto (fun x ↦ (x - x₀)⁻¹ • ∫ v in Ioc x₀ x, K x₀ v • F v) (𝓝[>] x₀) (𝓝 0) ∧
    Tendsto (fun x ↦ (x - x₀)⁻¹ • ∫ v in Ioc x x₀, K x v • F v) (𝓝[<] x₀) (𝓝 0) := by
  set S : Set (ℝ × ℝ) := {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2}
  have hG0 : ContinuousWithinAt (fun p : ℝ × ℝ ↦ K p.1 p.2 • F p.2) S (x₀, x₀) :=
    (hK.smul (hF.comp continuous_snd.continuousOn fun _ hp ↦ hp.2.1)) (x₀, x₀) ⟨hx₀, hx₀, le_rfl⟩
  have hGval : K x₀ x₀ • F x₀ = 0 := by rw [hKdiag x₀ hx₀, zero_smul]
  have hbound : ∀ ε > 0, ∃ δ > 0, ∀ p ∈ S, dist p (x₀, x₀) < δ → ‖K p.1 p.2 • F p.2‖ ≤ ε / 2 := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhdsWithin_nhds.1 hG0.tendsto (ε / 2) (half_pos hε)
    exact ⟨δ, hδ, fun p hp hdist ↦ (by simpa [hGval] using (h hp hdist).le)⟩
  have hstep {r ε a b : ℝ} {g : ℝ → E} (hr : 0 < r) (hε : 0 < ε) (hab : a ≤ b) (hlen : b - a = r)
      (hgn : ∀ v ∈ Ioc a b, ‖g v‖ ≤ ε / 2) : r⁻¹ * ‖∫ v in Ioc a b, g v‖ < ε := by
    have hint : ‖∫ v in Ioc a b, g v‖ ≤ (ε / 2) * r := by
      simpa only [Real.volume_real_Ioc_of_le hab, hlen] using
        norm_setIntegral_le_of_norm_le_const (measure_Ioc_lt_top (μ := volume)) hgn
    calc r⁻¹ * ‖∫ v in Ioc a b, g v‖ ≤ r⁻¹ * ((ε / 2) * r) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hr.le)
      _ = ε / 2 := by field_simp [hr.ne']
      _ < ε := half_lt_self hε
  constructor
  · refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hδle⟩ := hbound ε hε
    refine ⟨min δ (d - x₀), lt_min hδ (sub_pos.2 hxd), fun x (hx : x₀ < x) hdist ↦ ?_⟩
    obtain ⟨hdx, hxd'⟩ : x - x₀ < δ ∧ x - x₀ < d - x₀ :=
      lt_min_iff.1 (by simpa [Real.dist_eq, abs_of_pos (sub_pos.2 hx)] using hdist)
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (sub_pos.2 hx)]
    refine hstep (sub_pos.2 hx) hε hx.le rfl fun v hv ↦
      hδle (x₀, v) ⟨hx₀, hcd ⟨hcx.le.trans hv.1.le, hv.2.trans (by linarith)⟩, hv.1.le⟩ ?_
    rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_pos (sub_pos.2 hv.1),
      max_eq_right (sub_pos.2 hv.1).le]; linarith [hv.2]
  · refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hδle⟩ := hbound ε hε
    refine ⟨min δ (x₀ - c), lt_min hδ (sub_pos.2 hcx), fun x (hx : x < x₀) hdist ↦ ?_⟩
    obtain ⟨hdx, hcx'⟩ : x₀ - x < δ ∧ x₀ - x < x₀ - c :=
      lt_min_iff.1 (by simpa [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hx)] using hdist)
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_sub_comm,
      abs_of_pos (sub_pos.2 hx)]
    refine hstep (sub_pos.2 hx) hε hx.le rfl fun v hv ↦
      hδle (x, v) ⟨hcd ⟨by linarith, hx.le.trans hxd.le⟩,
        hcd ⟨by linarith [hv.1], hv.2.trans hxd.le⟩, hv.1.le⟩ ?_
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, abs_sub_comm, abs_sub_comm v,
      abs_of_pos (sub_pos.2 hx), abs_of_nonneg (sub_nonneg.2 hv.2)]
    exact max_lt hdx (by linarith [hv.1])

section Slope

variable {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} {F : ℝ → E}
  (hI : IsOpen I) (hIo : I.OrdConnected)
  (hKderiv : ∀ x v, x ∈ I → v ∈ I → x < v → HasDerivAt (fun u ↦ K u v) (K₁ x v) x)
  (hK₁le : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
  (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
  (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v)
  (hF : ContinuousOn F I)
  (hFint : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x))

private lemma slope_kernel_smul_eq (x₀ x v : ℝ) (y : E) :
    slope (fun u ↦ K u v) x₀ x • y = (x - x₀)⁻¹ • (K x v • y - K x₀ v • y) := by
  rw [slope_def_module, smul_assoc, sub_smul]

include hI hIo hKderiv hK₁le hQ0 hKle hF hFint

/-- Left difference quotient of `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` converges to
`∫ v in I ∩ Ioi x₀, K₁ x₀ v • F v`. -/
private lemma tendsto_slope_left_integral_kernel_smul
    (hKlt : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    {x₀ c d M₁ : ℝ} (hx₀ : x₀ ∈ I) (hcx : c < x₀) (hxd : x₀ < d) (hcd : Icc c d ⊆ I)
    (hP₁M : ∀ u ∈ Icc c d, P₁ u ≤ M₁)
    (hbdr : Tendsto (fun x ↦ (x - x₀)⁻¹ • ∫ v in Ioc x x₀, K x v • F v) (𝓝[<] x₀) (𝓝 0)) :
    Tendsto (slope (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) x₀) (𝓝[<] x₀)
      (𝓝 (∫ v in I ∩ Ioi x₀, K₁ x₀ v • F v)) := by
  have hmeas : MeasurableSet (I ∩ Ioi x₀) := hI.measurableSet.inter measurableSet_Ioi
  have hKx₀ := integrableOn_kernel_smul hI hKlt hKle hF hx₀ (hFint x₀ hx₀)
  have heq : slope (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) x₀ =ᶠ[𝓝[<] x₀]
      fun x ↦ (∫ v in I ∩ Ioi x₀, slope (fun u ↦ K u v) x₀ x • F v) +
        (x - x₀)⁻¹ • ∫ v in Ioc x x₀, K x v • F v := by
    filter_upwards [Ioo_mem_nhdsLT hcx] with x hx
    have hxI : x ∈ I := hcd ⟨hx.1.le, hx.2.le.trans hxd.le⟩
    have hKx := integrableOn_kernel_smul hI hKlt hKle hF hxI (hFint x hxI)
    rw [slope_def_module, ← hKx.integral_Ioc_add_inter_Ioi hI.measurableSet hIo hxI hx₀ hx.2.le,
      add_sub_assoc, smul_add, add_comm, ← integral_sub
        (hKx.mono_set (inter_subset_inter_right I (Ioi_subset_Ioi hx.2.le))) hKx₀, ← integral_smul]
    exact congrArg (· + _) (setIntegral_congr_fun hmeas fun v _ ↦
      (slope_kernel_smul_eq x₀ x v _).symm)
  refine Tendsto.congr' heq.symm ?_
  rw [← add_zero (∫ v in I ∩ Ioi x₀, K₁ x₀ v • F v)]
  refine (tendsto_integral_filter_of_dominated_convergence (fun v ↦ M₁ * (Q v * ‖F v‖))
    ?_ ?_ ((hFint x₀ hx₀).const_mul M₁) ?_).add hbdr
  · filter_upwards [Ioo_mem_nhdsLT hcx] with x hx
    have hxI : x ∈ I := hcd ⟨hx.1.le, hx.2.le.trans hxd.le⟩
    have h1 := (integrableOn_kernel_smul hI hKlt hKle hF hxI (hFint x hxI)).mono_set
      (inter_subset_inter_right I (Ioi_subset_Ioi hx.2.le))
    simp_rw [slope_kernel_smul_eq]
    exact ((h1.sub hKx₀).smul (x - x₀)⁻¹).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT hcx] with x hx
    filter_upwards [ae_restrict_mem hmeas] with v hv
    exact norm_slope_kernel_smul_le hcd hKderiv hK₁le hP₁M (hQ0 v hv.1) ⟨hcx.le, hxd.le⟩
      ⟨hx.1.le, hx.2.le.trans hxd.le⟩ hx.2.ne hv.1 (max_lt (hx.2.trans hv.2) hv.2)
  · filter_upwards [ae_restrict_mem hmeas] with v hv
    exact ((hasDerivAt_iff_tendsto_slope.1 (hKderiv x₀ v hx₀ hv.1 hv.2)).smul_const
      (F v)).mono_left (nhdsWithin_mono x₀ fun _ h ↦ ne_of_lt h)

/-- Right difference quotient of `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` converges to
`∫ v in I ∩ Ioi x₀, K₁ x₀ v • F v`. -/
private lemma tendsto_slope_right_integral_kernel_smul
    (hKlt : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    {x₀ c d M₁ : ℝ} (hx₀ : x₀ ∈ I) (hcx : c < x₀) (hxd : x₀ < d) (hcd : Icc c d ⊆ I)
    (hM₁0 : 0 ≤ M₁) (hP₁M : ∀ u ∈ Icc c d, P₁ u ≤ M₁)
    (hbdr : Tendsto (fun x ↦ (x - x₀)⁻¹ • ∫ v in Ioc x₀ x, K x₀ v • F v) (𝓝[>] x₀) (𝓝 0)) :
    Tendsto (slope (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) x₀) (𝓝[>] x₀)
      (𝓝 (∫ v in I ∩ Ioi x₀, K₁ x₀ v • F v)) := by
  have hmeas : MeasurableSet (I ∩ Ioi x₀) := hI.measurableSet.inter measurableSet_Ioi
  have hKx₀ := integrableOn_kernel_smul hI hKlt hKle hF hx₀ (hFint x₀ hx₀)
  have heq : slope (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) x₀ =ᶠ[𝓝[>] x₀]
      fun x ↦ (∫ v in I ∩ Ioi x₀, (Ioi x).indicator (fun v ↦ slope (fun u ↦ K u v) x₀ x • F v) v) -
        (x - x₀)⁻¹ • ∫ v in Ioc x₀ x, K x₀ v • F v := by
    filter_upwards [Ioo_mem_nhdsGT hxd] with x hx
    have hxI : x ∈ I := hcd ⟨hcx.le.trans hx.1.le, hx.2.le⟩
    have hKx := integrableOn_kernel_smul hI hKlt hKle hF hxI (hFint x hxI)
    rw [slope_def_module, ← hKx₀.integral_Ioc_add_inter_Ioi hI.measurableSet hIo hx₀ hxI hx.1.le,
      sub_add_eq_sub_sub_swap, smul_sub, ← integral_sub hKx
        (hKx₀.mono_set (inter_subset_inter_right I (Ioi_subset_Ioi hx.1.le))), ← integral_smul,
      setIntegral_indicator measurableSet_Ioi, inter_assoc, Ioi_inter_Ioi, sup_eq_right.2 hx.1.le]
    exact congrArg (· - _) (setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi)
      fun v _ ↦ (slope_kernel_smul_eq x₀ x v _).symm)
  refine Tendsto.congr' heq.symm ?_
  rw [← sub_zero (∫ v in I ∩ Ioi x₀, K₁ x₀ v • F v)]
  refine (tendsto_integral_filter_of_dominated_convergence (fun v ↦ M₁ * (Q v * ‖F v‖))
    ?_ ?_ ((hFint x₀ hx₀).const_mul M₁) ?_).sub hbdr
  · filter_upwards [Ioo_mem_nhdsGT hxd] with x hx
    have hxI : x ∈ I := hcd ⟨hcx.le.trans hx.1.le, hx.2.le⟩
    have h1 := integrableOn_kernel_smul hI hKlt hKle hF hxI (hFint x hxI)
    have h2 := hKx₀.mono_set (inter_subset_inter_right I (Ioi_subset_Ioi hx.1.le))
    have hint : IntegrableOn (fun v ↦ slope (fun u ↦ K u v) x₀ x • F v) (Ioi x)
        (volume.restrict (I ∩ Ioi x₀)) := by
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi, inter_comm, inter_assoc,
        Ioi_inter_Ioi, sup_eq_right.2 hx.1.le]
      simp_rw [slope_kernel_smul_eq]; exact (h1.sub h2).smul (x - x₀)⁻¹
    exact ((integrable_indicator_iff measurableSet_Ioi).2 hint).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT hxd] with x hx
    filter_upwards [ae_restrict_mem hmeas] with v hv
    by_cases hxv : x < v
    · rw [indicator_of_mem hxv]
      exact norm_slope_kernel_smul_le hcd hKderiv hK₁le hP₁M (hQ0 v hv.1) ⟨hcx.le, hxd.le⟩
        ⟨hcx.le.trans hx.1.le, hx.2.le⟩ hx.1.ne' hv.1 (max_lt hxv hv.2)
    · rw [indicator_of_notMem hxv, norm_zero]
      exact mul_nonneg hM₁0 (mul_nonneg (hQ0 v hv.1) (norm_nonneg _))
  · filter_upwards [ae_restrict_mem hmeas] with v hv
    refine (((hasDerivAt_iff_tendsto_slope.1 (hKderiv x₀ v hx₀ hv.1 hv.2)).smul_const
      (F v)).mono_left (nhdsWithin_mono x₀ fun _ h ↦ ne_of_gt h)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hv.2] with x hx; rw [indicator_of_mem hx.2]

/-- Differentiation under the Volterra integral sign when `K x x = 0`. -/
private lemma hasDerivAt_integral_kernel_smul
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0) (hP₁ : ContinuousOn P₁ I) {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    HasDerivAt (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v)
      (∫ v in I ∩ Ioi x₀, K₁ x₀ v • F v) x₀ := by
  have hKlt : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2} :=
    hK.mono fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.le⟩
  obtain ⟨c, d, _, hmem, hcd⟩ := exists_Icc_mem_subset_of_mem_nhds (hI.mem_nhds hx₀)
  obtain ⟨hcx, hxd⟩ : x₀ ∈ Ioo c d := by
    simpa only [interior_Icc] using (mem_interior_iff_mem_nhds.2 hmem : x₀ ∈ interior (Icc c d))
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP₁.mono hcd)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ x₀ ⟨hcx.le, hxd.le⟩)
  have hP₁M : ∀ u ∈ Icc c d, P₁ u ≤ M₁ := fun u hu ↦ (le_abs_self _).trans (hM₁ u hu)
  obtain ⟨hbdr_right, hbdr_left⟩ :=
    tendsto_inv_smul_integral_Ioc_zero hK hKdiag hF hx₀ hcx hxd hcd
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  exact ⟨tendsto_slope_left_integral_kernel_smul hI hIo hKderiv hK₁le hQ0 hKle hF hFint hKlt hx₀
      hcx hxd hcd hP₁M hbdr_left,
    tendsto_slope_right_integral_kernel_smul hI hIo hKderiv hK₁le hQ0 hKle hF hFint hKlt hx₀
      hcx hxd hcd hM₁0 hP₁M hbdr_right⟩

end Slope

omit [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] in
/-- If `P₁ x < 0` in `‖K₁ x v‖ ≤ P₁ x * Q v` with `Q ≥ 0`, then both `K₁ x v` and `Q v` vanish on
`I ∩ Ioi x`, so the corresponding tail integrals vanish. -/
private lemma integrals_eq_zero_of_bound_neg {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}
    (hK₁le : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    {x : ℝ} (hx : x ∈ I) (hneg : P₁ x < 0) (F : ℝ → E) (f : ℝ → ℝ) :
    (∫ v in I ∩ Ioi x, K₁ x v • F v) = 0 ∧ (∫ v in I ∩ Ioi x, Q v * f v) = 0 := by
  have hzero (v : ℝ) (hv : v ∈ I ∩ Ioi x) : Q v = 0 ∧ K₁ x v = 0 := by
    have hQv : Q v = 0 := by
      by_contra hne
      linarith [norm_nonneg (K₁ x v), hK₁le x v hx hv.1 hv.2,
        mul_neg_of_neg_of_pos hneg (lt_of_le_of_ne (hQ0 v hv.1) (Ne.symm hne))]
    exact ⟨hQv, norm_le_zero_iff.1 (by simpa [hQv] using hK₁le x v hx hv.1 hv.2)⟩
  exact ⟨setIntegral_eq_zero_of_forall_eq_zero fun v hv ↦ by rw [(hzero v hv).2, zero_smul],
    setIntegral_eq_zero_of_forall_eq_zero fun v hv ↦ by rw [(hzero v hv).1, zero_mul]⟩

section GeneralDeriv

variable {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}
  (hI : IsOpen I) (hIo : I.OrdConnected)
  (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
  (hKdiag : ∀ x ∈ I, K x x = 0)
  (hKderiv : ∀ x v, x ∈ I → v ∈ I → x < v → HasDerivAt (fun u ↦ K u v) (K₁ x v) x)
  (hK₁ : ContinuousOn (uncurry K₁) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
  (hK₁le : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
  (hP₁ : ContinuousOn P₁ I) (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I)
  (hQ : ContinuousOn Q I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
  (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
  (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))

include hI hIo hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on an open interval, derivative formula.** When `K` is continuous
up to the diagonal with `K x x = 0`, and its partial derivative `K₁ = ∂K/∂x` satisfies
`‖K₁ x v‖ ≤ P₁ x * Q v` with continuous `P₁`, every continuous `O(P)` solution `h` is
differentiable at every `x ∈ I` with derivative `∫ v in I ∩ Ioi x, K₁ x v • (J v + ψ v • h v)`
(Olver, Chapter 6, Theorem 10.1). -/
theorem hasDerivAt_volterra_solution_on {h : ℝ → E} (hh : ContinuousOn h I)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hO : h =O[𝓟 (I ∩ Ici x₀)] P) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt h (∫ v in I ∩ Ioi x, K₁ x v • (J v + ψ v • h v)) x := by
  obtain ⟨hint, _⟩ :=
    exists_bound_and_integrableOn_of_isBigO hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh heq hx₀ hO
  refine (hasDerivAt_integral_kernel_smul hI hIo hKderiv hK₁le hQ0 hKle
    (continuousOn_forcing_add hJ hψ hh) hint hK hKdiag hP₁ hx).congr_of_eventuallyEq ?_
  filter_upwards [hI.mem_nhds hx] with y hy
  exact heq y hy

include hI hIo hK hKdiag hKderiv hK₁ hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on an open interval, `C¹` regularity.** Under the hypotheses of
`TauCeti.hasDerivAt_volterra_solution_on` together with continuity of `K₁ = ∂K/∂x` on `{x < v}`,
every continuous `O(P)` solution `h` is `C¹` on `I` (Olver, Chapter 6, Theorem 10.1). -/
theorem contDiffOn_volterra_solution_on {h : ℝ → E} (hh : ContinuousOn h I)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hO : h =O[𝓟 (I ∩ Ici x₀)] P) :
    ContDiffOn ℝ 1 h I := by
  obtain ⟨hint, _⟩ :=
    exists_bound_and_integrableOn_of_isBigO hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh heq hx₀ hO
  have hderiv : ∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Ioi x, K₁ x v • (J v + ψ v • h v)) x :=
    fun x hx ↦ hasDerivAt_volterra_solution_on hI hIo hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0
      hKle hΦ hΨ hh heq hx₀ hO hx
  rw [contDiffOn_one_iff_derivWithin hI.uniqueDiffOn]
  refine ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt, ?_⟩
  refine (continuousOn_integral_kernel_smul hI hK₁ hK₁le hP₁ hQ0
    (continuousOn_forcing_add hJ hψ hh) hint).congr fun x hx ↦ ?_
  rw [derivWithin_of_isOpen hI hx, (hderiv x hx).deriv]

include hI hIo hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on an open interval, derivative bound.** Under the hypotheses of
`TauCeti.hasDerivAt_volterra_solution_on`, the derivative satisfies
`‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)` for every `x ∈ I` (Olver, Chapter 6, Theorem 10.1). -/
theorem norm_deriv_volterra_solution_le_on {h : ℝ → E} (hh : ContinuousOn h I)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hO : h =O[𝓟 (I ∩ Ici x₀)] P) {x : ℝ} (hx : x ∈ I) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨hint, _⟩ :=
    exists_bound_and_integrableOn_of_isBigO hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh heq hx₀ hO
  rw [(hasDerivAt_volterra_solution_on hI hIo hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ
    hΨ hh heq hx₀ hO hx).deriv]
  rcases lt_or_ge (P₁ x) 0 with hneg | hP₁0
  · obtain ⟨hL0, hR0⟩ := integrals_eq_zero_of_bound_neg hK₁le hQ0 hx hneg
      (fun v ↦ J v + ψ v • h v) (fun v ↦ ‖J v‖)
    rw [hL0, hR0]; simp
  refine (norm_integral_kernel_smul_le hI hK₁le hx (hint x hx)).trans ?_
  set Φx := ∫ u in I ∩ Ioi x, Q u * ‖J u‖
  set g : ℝ → ℝ := fun u ↦ P u * Q u * ‖ψ u‖ with hg
  have hmeas : MeasurableSet (I ∩ Ioi x) := hI.measurableSet.inter measurableSet_Ioi
  have hstep : ∫ v in I ∩ Ioi x, Q v * ‖J v + ψ v • h v‖ ≤
      ∫ v in I ∩ Ioi x, (Q v * ‖J v‖ + Φx * (g v * Real.exp (∫ u in I ∩ Ioi v, g u))) := by
    refine setIntegral_mono_on (hint x hx)
      ((hΦ x hx).add (((hΨ x hx).mul_exp_integral_inter_Ioi hI hIo hx).const_mul Φx))
      hmeas fun v hv ↦ ?_
    have hΦle : ∫ u in I ∩ Ioi v, Q u * ‖J u‖ ≤ Φx :=
      antitoneOn_integral_inter_Ioi hI.measurableSet (forcing_weight_nonneg hQ0) hΦ hx hv.1 hv.2.le
    have hhv := norm_volterra_solution_le_on hI hIo hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh heq hx₀ hO hv.1
    have := hQ0 v hv.1; have := hP0 v hv.1
    calc Q v * ‖J v + ψ v • h v‖ ≤ Q v * (‖J v‖ + ‖ψ v‖ * ‖h v‖) := by
          gcongr; exact (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ Q v * (‖J v‖ + ‖ψ v‖ * (P v * Φx * Real.exp (∫ u in I ∩ Ioi v, g u))) := by
          grw [hhv, hΦle]
      _ = Q v * ‖J v‖ + Φx * (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by simp only [hg]; ring
  rw [integral_add (hΦ x hx) (((hΨ x hx).mul_exp_integral_inter_Ioi hI hIo hx).const_mul Φx),
    integral_const_mul, (hΨ x hx).integral_inter_Ioi_mul_exp_integral_inter_Ioi hI hIo hx] at hstep
  calc P₁ x * ∫ v in I ∩ Ioi x, Q v * ‖J v + ψ v • h v‖
      ≤ P₁ x * (Φx + Φx * (Real.exp (∫ u in I ∩ Ioi x, g u) - 1)) :=
        mul_le_mul_of_nonneg_left hstep hP₁0
    _ = P₁ x * Φx * Real.exp (∫ u in I ∩ Ioi x, g u) := by ring

include hI hIo hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hQ0 in
/-- **Volterra integral equations on an open interval, sharper derivative bound.** When `P` is a
nonnegative constant `P₀`, `‖J‖ ≤ ‖ψ‖` on `I`, `K x x = 0`, and `‖∂K/∂x (x, v)‖ ≤ P₁ x * Q v`,
every bounded continuous solution `h` satisfies
`‖deriv h x‖ ≤ P₁ x / P₀ * (exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖) - 1)` for every `x ∈ I`.
When `P₀ = 0`, `K` vanishes identically above each point, so `h = 0` near `x` and both sides are
`0`. -/
theorem norm_deriv_volterra_solution_le_exp_sub_one_on {P₀ : ℝ} (hP₀ : 0 ≤ P₀)
    (hKle : ∀ x v, x ∈ I → v ∈ I → x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hJle : ∀ x ∈ I, ‖J x‖ ≤ ‖ψ x‖)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hO : h =O[𝓟 (I ∩ Ici x₀)] (fun _ ↦ (1 : ℝ))) {x : ℝ} (hx : x ∈ I) :
    ‖deriv h x‖ ≤ P₁ x / P₀ * (Real.exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖) - 1) := by
  rcases hP₀.eq_or_lt with rfl | hP₀pos
  · have hzero : h =ᶠ[𝓝 x] 0 := by
      filter_upwards [hI.mem_nhds hx] with y hy; exact eq_zero_of_bound_zero hKle heq hy
    rw [hzero.deriv_eq]; simp
  obtain ⟨hΦJ, hΨ, hOP₀⟩ := sharp_volterra_setup hI hJ hQ hQ0 hP₀pos hJle hΦ hO
  obtain ⟨hint, _⟩ := exists_bound_and_integrableOn_of_isBigO (P := fun _ ↦ P₀)
    hI hIo hJ hψ hQ (fun _ _ ↦ hP₀pos.le) hQ0 hKle hΦJ hΨ hh heq hx₀ hOP₀
  rw [(hasDerivAt_volterra_solution_on (P := fun _ ↦ P₀) hI hIo hK hKdiag hKderiv hK₁le hP₁ hJ hψ
    hQ (fun _ _ ↦ hP₀pos.le) hQ0 hKle hΦJ hΨ hh heq hx₀ hOP₀ hx).deriv]
  rcases lt_or_ge (P₁ x) 0 with hneg | hP₁0
  · obtain ⟨hL0, hR0⟩ := integrals_eq_zero_of_bound_neg hK₁le hQ0 hx hneg
      (fun v ↦ J v + ψ v • h v) (fun v ↦ ‖ψ v‖)
    rw [hL0, hR0]; simp
  refine (norm_integral_kernel_smul_le hI hK₁le hx (hint x hx)).trans ?_
  set g : ℝ → ℝ := fun u ↦ P₀ * Q u * ‖ψ u‖ with hg
  have hΨ_eq (y : ℝ) : ∫ u in I ∩ Ioi y, g u = P₀ * ∫ u in I ∩ Ioi y, Q u * ‖ψ u‖ := by
    simp only [hg, mul_assoc, integral_const_mul]
  have hstep : ∫ v in I ∩ Ioi x, Q v * ‖J v + ψ v • h v‖ ≤
      ∫ v in I ∩ Ioi x, P₀⁻¹ * (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by
    refine setIntegral_mono_on (hint x hx)
      (((hΨ x hx).mul_exp_integral_inter_Ioi hI hIo hx).const_mul P₀⁻¹)
      (hI.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_
    have hhv := norm_volterra_solution_le_exp_sub_one_on hI hIo hJ hψ hQ hQ0 hP₀pos.le hKle hJle hΦ
      hh heq hx₀ hO hv.1
    rw [← hΨ_eq v] at hhv
    have := hQ0 v hv.1
    calc Q v * ‖J v + ψ v • h v‖ ≤ Q v * (‖ψ v‖ + ‖ψ v‖ * ‖h v‖) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add (hJle v hv.1) (by rw [norm_smul]))
      _ ≤ Q v * (‖ψ v‖ + ‖ψ v‖ * (Real.exp (∫ u in I ∩ Ioi v, g u) - 1)) := by gcongr
      _ = P₀⁻¹ * (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by
          simp only [hg]; field_simp [hP₀pos.ne']; ring
  rw [integral_const_mul,
    (hΨ x hx).integral_inter_Ioi_mul_exp_integral_inter_Ioi hI hIo hx, hΨ_eq x] at hstep
  calc P₁ x * ∫ v in I ∩ Ioi x, Q v * ‖J v + ψ v • h v‖
      ≤ P₁ x * (P₀⁻¹ * (Real.exp (P₀ * ∫ u in I ∩ Ioi x, Q u * ‖ψ u‖) - 1)) :=
        mul_le_mul_of_nonneg_left hstep hP₁0
    _ = P₁ x / P₀ * (Real.exp (P₀ * ∫ u in I ∩ Ioi x, Q u * ‖ψ u‖) - 1) := by
        rw [div_eq_mul_inv, mul_assoc]

end GeneralDeriv

end Differentiability

/-! ### Specializations to a half-line `(a, ∞)` -/

section HalfLine

variable {a : ℝ}

private lemma Ioi_inter_Ioi_of_mem {x : ℝ} (hx : x ∈ Ioi a) : Ioi a ∩ Ioi x = Ioi x :=
  inter_eq_right.2 (Ioi_subset_Ioi hx.le)

private lemma integrableOn_Ioi_inter {α : Type*} [NormedAddCommGroup α] {f : ℝ → α}
    (hf : ∀ x ∈ Ioi a, IntegrableOn f (Ioi x)) : ∀ x ∈ Ioi a, IntegrableOn f (Ioi a ∩ Ioi x) :=
  fun x hx ↦ by rw [Ioi_inter_Ioi_of_mem hx]; exact hf x hx

private lemma volterra_eq_Ioi_inter {h : ℝ → E}
    (heq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ Ioi a, h x = ∫ v in Ioi a ∩ Ioi x, K x v • (J v + ψ v • h v) :=
  fun x hx ↦ by simpa only [Ioi_inter_Ioi_of_mem hx] using heq x hx

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
private lemma exists_isBigO_Ioi_inter_Ici_of_atTop {f : ℝ → E} {g : ℝ → ℝ} (hO : f =O[atTop] g) :
    ∃ x₀ ∈ Ioi a, f =O[𝓟 (Ioi a ∩ Ici x₀)] g := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.1 hO
  obtain ⟨M, hM⟩ := eventually_atTop.1 hC
  exact ⟨max (a + 1) M, lt_of_lt_of_le (lt_add_one a) (le_max_left _ _),
    Asymptotics.isBigO_iff.2
      ⟨C, eventually_principal.2 fun v hv ↦ hM v ((le_max_right _ _).trans hv.2)⟩⟩

section Basic

variable (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 < p.2})
  (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
  (hP : ContinuousOn P (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
  (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
  (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
  (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))

include hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, ∞)`, existence.** Let `K` be continuous on
`{(x, v) | a < x < v}` with `‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are continuous on
`(a, ∞)`, and let `J`, `ψ` be continuous on `(a, ∞)` such that
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for
every `x > a`. Then `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has a continuous solution `h`
on `(a, ∞)` with `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x > a`
(Olver, Chapter 6, Theorem 10.1). -/
theorem exists_volterra_solution [CompleteSpace E] :
    ∃ h : ℝ → E, ContinuousOn h (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨h, hcont, heq, hle⟩ := exists_volterra_solution_on isOpen_Ioi ordConnected_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ hP hQ hP0 hQ0 (fun x v hx _ ↦ hKle x v hx)
    (integrableOn_Ioi_inter hΦ) (integrableOn_Ioi_inter hΨ)
  exact ⟨h, hcont, fun x hx ↦ by simpa only [Ioi_inter_Ioi_of_mem hx] using heq x hx,
    fun x hx ↦ by simpa only [Ioi_inter_Ioi_of_mem hx] using hle x hx⟩

include hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, ∞)`, uniqueness.** Two continuous solutions on `(a, ∞)`
that are `O(P)` at `+∞` agree everywhere on `(a, ∞)`. -/
theorem volterra_solution_unique {h₁ h₂ : ℝ → E}
    (hh₁ : ContinuousOn h₁ (Ioi a)) (hh₂ : ContinuousOn h₂ (Ioi a))
    (heq₁ : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (heq₂ : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (hO₁ : h₁ =O[atTop] P) (hO₂ : h₂ =O[atTop] P) : EqOn h₁ h₂ (Ioi a) := by
  obtain ⟨x₁, hx₁, hO₁'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO₁
  obtain ⟨x₂, hx₂, hO₂'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO₂
  exact volterra_solution_unique_on isOpen_Ioi ordConnected_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩)
    hJ hψ hQ hP0 hQ0 (fun x v hx _ ↦ hKle x v hx) (integrableOn_Ioi_inter hΦ)
    (integrableOn_Ioi_inter hΨ) hh₁ hh₂ (volterra_eq_Ioi_inter heq₁) (volterra_eq_Ioi_inter heq₂)
    hx₁ hx₂ hO₁' hO₂'

include hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, ∞)`, a priori bound.** Every continuous solution `h` on
`(a, ∞)` with `h = O(P)` at `+∞` obeys `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x > a`. -/
theorem norm_volterra_solution_le {h : ℝ → E} (hh : ContinuousOn h (Ioi a))
    (heq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hO : h =O[atTop] P) {x : ℝ} (hx : a < x) :
    ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) * Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO
  simpa only [Ioi_inter_Ioi_of_mem hx] using norm_volterra_solution_le_on isOpen_Ioi
    ordConnected_Ioi hJ hψ hQ hP0 hQ0 (fun x v hx _ ↦ hKle x v hx) (integrableOn_Ioi_inter hΦ)
    (integrableOn_Ioi_inter hΨ) hh (volterra_eq_Ioi_inter heq) hx₀ hO' hx

include hJ hψ hQ hQ0 in
/-- **Volterra integral equations on `(a, ∞)`, sharper bound.** When `P` is a nonnegative constant
`P₀` and `‖J‖ ≤ ‖ψ‖` on `(a, ∞)`, every continuous solution bounded at `+∞` satisfies
`‖h x‖ ≤ exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1`. -/
theorem norm_volterra_solution_le_exp_sub_one {P₀ : ℝ} (hP₀ : 0 ≤ P₀)
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hJle : ∀ x ∈ Ioi a, ‖J x‖ ≤ ‖ψ x‖)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h (Ioi a))
    (heq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hO : h =O[atTop] (fun _ ↦ (1 : ℝ))) {x : ℝ} (hx : a < x) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO
  simpa only [Ioi_inter_Ioi_of_mem hx] using norm_volterra_solution_le_exp_sub_one_on isOpen_Ioi
    ordConnected_Ioi hJ hψ hQ hQ0 hP₀ (fun x v hx _ ↦ hKle x v hx) hJle
    (integrableOn_Ioi_inter hΦ) hh (volterra_eq_Ioi_inter heq) hx₀ hO' hx

end Basic

section Deriv

variable [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}
  (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2}) (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
  (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun u ↦ K u v) (K₁ x v) x)
  (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 < p.2})
  (hK₁le : ∀ x v, a < x → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v) (hP₁ : ContinuousOn P₁ (Ioi a))
  (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
  (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
  (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
  (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))

include hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, ∞)`, derivative formula.** -/
theorem hasDerivAt_volterra_solution {h : ℝ → E} (hh : ContinuousOn h (Ioi a))
    (heq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hO : h =O[atTop] P) {x : ℝ} (hx : a < x) :
    HasDerivAt h (∫ v in Ioi x, K₁ x v • (J v + ψ v • h v)) x := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO
  simpa only [Ioi_inter_Ioi_of_mem hx] using hasDerivAt_volterra_solution_on isOpen_Ioi
    ordConnected_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag (fun x v hx _ ↦ hKderiv x v hx)
    (fun x v hx _ ↦ hK₁le x v hx) hP₁ hJ hψ hQ hP0 hQ0 (fun x v hx _ ↦ hKle x v hx)
    (integrableOn_Ioi_inter hΦ) (integrableOn_Ioi_inter hΨ) hh (volterra_eq_Ioi_inter heq)
    hx₀ hO' hx

include hK hKdiag hKderiv hK₁ hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, ∞)`, `C¹` regularity.** -/
theorem contDiffOn_volterra_solution {h : ℝ → E} (hh : ContinuousOn h (Ioi a))
    (heq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hO : h =O[atTop] P) : ContDiffOn ℝ 1 h (Ioi a) := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO
  exact contDiffOn_volterra_solution_on isOpen_Ioi ordConnected_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag (fun x v hx _ ↦ hKderiv x v hx)
    (hK₁.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) (fun x v hx _ ↦ hK₁le x v hx) hP₁ hJ hψ hQ hP0 hQ0
    (fun x v hx _ ↦ hKle x v hx) (integrableOn_Ioi_inter hΦ) (integrableOn_Ioi_inter hΨ)
    hh (volterra_eq_Ioi_inter heq) hx₀ hO'

include hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, ∞)`, derivative bound.** -/
theorem norm_deriv_volterra_solution_le {h : ℝ → E} (hh : ContinuousOn h (Ioi a))
    (heq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hO : h =O[atTop] P) {x : ℝ} (hx : a < x) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO
  simpa only [Ioi_inter_Ioi_of_mem hx] using norm_deriv_volterra_solution_le_on isOpen_Ioi
    ordConnected_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag (fun x v hx _ ↦ hKderiv x v hx)
    (fun x v hx _ ↦ hK₁le x v hx) hP₁ hJ hψ hQ hP0 hQ0 (fun x v hx _ ↦ hKle x v hx)
    (integrableOn_Ioi_inter hΦ) (integrableOn_Ioi_inter hΨ) hh (volterra_eq_Ioi_inter heq)
    hx₀ hO' hx

include hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hQ0 in
/-- **Volterra integral equations on `(a, ∞)`, sharper derivative bound.** -/
theorem norm_deriv_volterra_solution_le_exp_sub_one {P₀ : ℝ} (hP₀ : 0 ≤ P₀)
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hJle : ∀ x ∈ Ioi a, ‖J x‖ ≤ ‖ψ x‖)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h (Ioi a))
    (heq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hO : h =O[atTop] (fun _ ↦ (1 : ℝ))) {x : ℝ} (hx : a < x) :
    ‖deriv h x‖ ≤ P₁ x / P₀ * (Real.exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1) := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioi_inter_Ici_of_atTop (a := a) hO
  simpa only [Ioi_inter_Ioi_of_mem hx] using norm_deriv_volterra_solution_le_exp_sub_one_on
    isOpen_Ioi ordConnected_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag
    (fun x v hx _ ↦ hKderiv x v hx) (fun x v hx _ ↦ hK₁le x v hx) hP₁ hJ hψ hQ hQ0 hP₀
    (fun x v hx _ ↦ hKle x v hx) hJle (integrableOn_Ioi_inter hΦ) hh (volterra_eq_Ioi_inter heq)
    hx₀ hO' hx

end Deriv

end HalfLine

/-! ### Specializations to a bounded open interval `(a, b)` -/

section BoundedInterval

variable {a b : ℝ}

private lemma Ioo_inter_Ioi_of_mem {x : ℝ} (hx : x ∈ Ioo a b) : Ioo a b ∩ Ioi x = Ioo x b := by
  rw [← Ioi_inter_Iio, inter_right_comm, Ioi_inter_Ioi, sup_eq_right.2 hx.1.le, Ioi_inter_Iio]

private lemma integrableOn_Ioo_inter {α : Type*} [NormedAddCommGroup α] {f : ℝ → α}
    (hf : ∀ x ∈ Ioo a b, IntegrableOn f (Ioo x b)) :
    ∀ x ∈ Ioo a b, IntegrableOn f (Ioo a b ∩ Ioi x) :=
  fun x hx ↦ by rw [Ioo_inter_Ioi_of_mem hx]; exact hf x hx

private lemma volterra_eq_Ioo_inter {h : ℝ → E}
    (heq : ∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ Ioo a b, h x = ∫ v in Ioo a b ∩ Ioi x, K x v • (J v + ψ v • h v) :=
  fun x hx ↦ by simpa only [Ioo_inter_Ioi_of_mem hx] using heq x hx

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
private lemma exists_isBigO_Ioo_inter_Ici_of_nhdsLT (hab : a < b) {f : ℝ → E} {g : ℝ → ℝ}
    (hO : f =O[𝓝[<] b] g) : ∃ x₀ ∈ Ioo a b, f =O[𝓟 (Ioo a b ∩ Ici x₀)] g := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.1 hO
  obtain ⟨c, hcb, hce⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hC
  obtain ⟨x₀, hmax, hx₀b⟩ := exists_between (max_lt hab hcb)
  refine ⟨x₀, ⟨lt_of_le_of_lt (le_max_left _ _) hmax, hx₀b⟩, Asymptotics.isBigO_iff.2
    ⟨C, eventually_principal.2 fun v hv ↦ hce ⟨?_, hv.1.2⟩⟩⟩
  exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hmax) hv.2

section Basic

variable (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b})
  (hJ : ContinuousOn J (Ioo a b)) (hψ : ContinuousOn ψ (Ioo a b))
  (hP : ContinuousOn P (Ioo a b)) (hQ : ContinuousOn Q (Ioo a b))
  (hP0 : ∀ x ∈ Ioo a b, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioo a b, 0 ≤ Q x)
  (hKle : ∀ x v, a < x → x < v → v < b → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioo x b))
  (hΨ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioo x b))

include hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, b)`, existence.** -/
theorem exists_volterra_solution_Ioo [CompleteSpace E] :
    ∃ h : ℝ → E, ContinuousOn h (Ioo a b) ∧
      (∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioo a b, ‖h x‖ ≤ P x * (∫ v in Ioo x b, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioo x b, P v * Q v * ‖ψ v‖) := by
  obtain ⟨h, hcont, heq, hle⟩ := exists_volterra_solution_on isOpen_Ioo ordConnected_Ioo
    (hK.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hJ hψ hP hQ hP0 hQ0
    (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2)
    (integrableOn_Ioo_inter hΦ) (integrableOn_Ioo_inter hΨ)
  exact ⟨h, hcont, fun x hx ↦ by simpa only [Ioo_inter_Ioi_of_mem hx] using heq x hx,
    fun x hx ↦ by simpa only [Ioo_inter_Ioi_of_mem hx] using hle x hx⟩

include hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, b)`, uniqueness.** Two continuous solutions on `(a, b)`
that are `O(P)` as `x → b⁻` agree everywhere on `(a, b)`. -/
theorem volterra_solution_unique_Ioo {h₁ h₂ : ℝ → E}
    (hh₁ : ContinuousOn h₁ (Ioo a b)) (hh₂ : ContinuousOn h₂ (Ioo a b))
    (heq₁ : ∀ x ∈ Ioo a b, h₁ x = ∫ v in Ioo x b, K x v • (J v + ψ v • h₁ v))
    (heq₂ : ∀ x ∈ Ioo a b, h₂ x = ∫ v in Ioo x b, K x v • (J v + ψ v • h₂ v))
    (hO₁ : h₁ =O[𝓝[<] b] P) (hO₂ : h₂ =O[𝓝[<] b] P) : EqOn h₁ h₂ (Ioo a b) := by
  rcases le_or_gt b a with hba | hab
  · simp [Ioo_eq_empty_of_le hba]
  obtain ⟨x₁, hx₁, hO₁'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT hab hO₁
  obtain ⟨x₂, hx₂, hO₂'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT hab hO₂
  exact volterra_solution_unique_on isOpen_Ioo ordConnected_Ioo
    (hK.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hJ hψ hQ hP0 hQ0
    (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2) (integrableOn_Ioo_inter hΦ)
    (integrableOn_Ioo_inter hΨ) hh₁ hh₂ (volterra_eq_Ioo_inter heq₁) (volterra_eq_Ioo_inter heq₂)
    hx₁ hx₂ hO₁' hO₂'

include hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, b)`, a priori bound.** -/
theorem norm_volterra_solution_le_Ioo {h : ℝ → E} (hh : ContinuousOn h (Ioo a b))
    (heq : ∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v))
    (hO : h =O[𝓝[<] b] P) {x : ℝ} (hx : x ∈ Ioo a b) :
    ‖h x‖ ≤ P x * (∫ v in Ioo x b, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioo x b, P v * Q v * ‖ψ v‖) := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT (hx.1.trans hx.2) hO
  simpa only [Ioo_inter_Ioi_of_mem hx] using norm_volterra_solution_le_on isOpen_Ioo
    ordConnected_Ioo hJ hψ hQ hP0 hQ0 (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2)
    (integrableOn_Ioo_inter hΦ) (integrableOn_Ioo_inter hΨ) hh (volterra_eq_Ioo_inter heq)
    hx₀ hO' hx

include hJ hψ hQ hQ0 in
/-- **Volterra integral equations on `(a, b)`, sharper bound.** -/
theorem norm_volterra_solution_le_exp_sub_one_Ioo {P₀ : ℝ} (hP₀ : 0 ≤ P₀)
    (hKle : ∀ x v, a < x → x < v → v < b → ‖K x v‖ ≤ P₀ * Q v)
    (hJle : ∀ x ∈ Ioo a b, ‖J x‖ ≤ ‖ψ x‖)
    (hΦ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioo x b))
    {h : ℝ → E} (hh : ContinuousOn h (Ioo a b))
    (heq : ∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v))
    (hO : h =O[𝓝[<] b] (fun _ ↦ (1 : ℝ))) {x : ℝ} (hx : x ∈ Ioo a b) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in Ioo x b, Q v * ‖ψ v‖) - 1 := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT (hx.1.trans hx.2) hO
  simpa only [Ioo_inter_Ioi_of_mem hx] using norm_volterra_solution_le_exp_sub_one_on isOpen_Ioo
    ordConnected_Ioo hJ hψ hQ hQ0 hP₀ (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2) hJle
    (integrableOn_Ioo_inter hΦ) hh (volterra_eq_Ioo_inter heq) hx₀ hO' hx

end Basic

section Deriv

variable [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}
  (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2 ∧ p.2 < b})
  (hKdiag : ∀ x ∈ Ioo a b, K x x = 0)
  (hKderiv : ∀ x v, a < x → x < v → v < b → HasDerivAt (fun u ↦ K u v) (K₁ x v) x)
  (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b})
  (hK₁le : ∀ x v, a < x → x < v → v < b → ‖K₁ x v‖ ≤ P₁ x * Q v)
  (hP₁ : ContinuousOn P₁ (Ioo a b))
  (hJ : ContinuousOn J (Ioo a b)) (hψ : ContinuousOn ψ (Ioo a b)) (hQ : ContinuousOn Q (Ioo a b))
  (hP0 : ∀ x ∈ Ioo a b, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioo a b, 0 ≤ Q x)
  (hKle : ∀ x v, a < x → x < v → v < b → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioo x b))
  (hΨ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioo x b))

include hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, b)`, derivative formula.** -/
theorem hasDerivAt_volterra_solution_Ioo {h : ℝ → E} (hh : ContinuousOn h (Ioo a b))
    (heq : ∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v))
    (hO : h =O[𝓝[<] b] P) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt h (∫ v in Ioo x b, K₁ x v • (J v + ψ v • h v)) x := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT (hx.1.trans hx.2) hO
  simpa only [Ioo_inter_Ioi_of_mem hx] using hasDerivAt_volterra_solution_on isOpen_Ioo
    ordConnected_Ioo (hK.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hKdiag
    (fun x v hx hv hxv ↦ hKderiv x v hx.1 hxv hv.2) (fun x v hx hv hxv ↦ hK₁le x v hx.1 hxv hv.2)
    hP₁ hJ hψ hQ hP0 hQ0 (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2) (integrableOn_Ioo_inter hΦ)
    (integrableOn_Ioo_inter hΨ) hh (volterra_eq_Ioo_inter heq) hx₀ hO' hx

include hK hKdiag hKderiv hK₁ hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, b)`, `C¹` regularity.** -/
theorem contDiffOn_volterra_solution_Ioo {h : ℝ → E} (hh : ContinuousOn h (Ioo a b))
    (heq : ∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v))
    (hO : h =O[𝓝[<] b] P) : ContDiffOn ℝ 1 h (Ioo a b) := by
  rcases le_or_gt b a with hba | hab
  · rw [Ioo_eq_empty_of_le hba]; exact contDiffOn_empty
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT hab hO
  exact contDiffOn_volterra_solution_on isOpen_Ioo ordConnected_Ioo
    (hK.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hKdiag
    (fun x v hx hv hxv ↦ hKderiv x v hx.1 hxv hv.2) (hK₁.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩)
    (fun x v hx hv hxv ↦ hK₁le x v hx.1 hxv hv.2) hP₁ hJ hψ hQ hP0 hQ0
    (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2) (integrableOn_Ioo_inter hΦ)
    (integrableOn_Ioo_inter hΨ) hh (volterra_eq_Ioo_inter heq) hx₀ hO'

include hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hP0 hQ0 hKle hΦ hΨ in
/-- **Volterra integral equations on `(a, b)`, derivative bound.** -/
theorem norm_deriv_volterra_solution_le_Ioo {h : ℝ → E} (hh : ContinuousOn h (Ioo a b))
    (heq : ∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v))
    (hO : h =O[𝓝[<] b] P) {x : ℝ} (hx : x ∈ Ioo a b) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in Ioo x b, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioo x b, P v * Q v * ‖ψ v‖) := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT (hx.1.trans hx.2) hO
  simpa only [Ioo_inter_Ioi_of_mem hx] using norm_deriv_volterra_solution_le_on isOpen_Ioo
    ordConnected_Ioo (hK.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hKdiag
    (fun x v hx hv hxv ↦ hKderiv x v hx.1 hxv hv.2) (fun x v hx hv hxv ↦ hK₁le x v hx.1 hxv hv.2)
    hP₁ hJ hψ hQ hP0 hQ0 (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2) (integrableOn_Ioo_inter hΦ)
    (integrableOn_Ioo_inter hΨ) hh (volterra_eq_Ioo_inter heq) hx₀ hO' hx

include hK hKdiag hKderiv hK₁le hP₁ hJ hψ hQ hQ0 in
/-- **Volterra integral equations on `(a, b)`, sharper derivative bound.** -/
theorem norm_deriv_volterra_solution_le_exp_sub_one_Ioo {P₀ : ℝ} (hP₀ : 0 ≤ P₀)
    (hKle : ∀ x v, a < x → x < v → v < b → ‖K x v‖ ≤ P₀ * Q v)
    (hJle : ∀ x ∈ Ioo a b, ‖J x‖ ≤ ‖ψ x‖)
    (hΦ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioo x b))
    {h : ℝ → E} (hh : ContinuousOn h (Ioo a b))
    (heq : ∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v))
    (hO : h =O[𝓝[<] b] (fun _ ↦ (1 : ℝ))) {x : ℝ} (hx : x ∈ Ioo a b) :
    ‖deriv h x‖ ≤ P₁ x / P₀ * (Real.exp (P₀ * ∫ v in Ioo x b, Q v * ‖ψ v‖) - 1) := by
  obtain ⟨x₀, hx₀, hO'⟩ := exists_isBigO_Ioo_inter_Ici_of_nhdsLT (hx.1.trans hx.2) hO
  simpa only [Ioo_inter_Ioi_of_mem hx] using norm_deriv_volterra_solution_le_exp_sub_one_on
    isOpen_Ioo ordConnected_Ioo (hK.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hKdiag
    (fun x v hx hv hxv ↦ hKderiv x v hx.1 hxv hv.2) (fun x v hx hv hxv ↦ hK₁le x v hx.1 hxv hv.2)
    hP₁ hJ hψ hQ hQ0 hP₀ (fun x v hx hv hxv ↦ hKle x v hx.1 hxv hv.2) hJle
    (integrableOn_Ioo_inter hΦ) hh (volterra_eq_Ioo_inter heq) hx₀ hO' hx

end Deriv

end BoundedInterval

/-! ### Degenerate check (`K = 0`) -/

/-- When `K = 0`, the unique continuous `O(P)` solution on any open interval `I` is `h = 0`, and
the Volterra bound reduces to `0 ≤ P x * Φ x * exp (Ψ x)`. -/
example [CompleteSpace E] (hI : IsOpen I) (hIo : I.OrdConnected)
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ h : ℝ → E, EqOn h 0 I ∧
      ∀ x ∈ I, (0 : ℝ) ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨h, hcont, heq, hle⟩ := exists_volterra_solution_on (K := fun _ _ : ℝ ↦ (0 : 𝕜))
    hI hIo continuousOn_const hJ hψ hP hQ hP0 hQ0
    (fun x v hx hv _ ↦ by simpa using mul_nonneg (hP0 x hx) (hQ0 v hv)) hΦ hΨ
  have hzero : EqOn h 0 I := volterra_solution_unique_on (K := fun _ _ : ℝ ↦ (0 : 𝕜))
    hI hIo continuousOn_const hJ hψ hQ hP0 hQ0
    (fun x v hx hv _ ↦ by simpa using mul_nonneg (hP0 x hx) (hQ0 v hv)) hΦ hΨ
    hcont continuousOn_const heq (fun x _ ↦ by simp) hx₀ hx₀
    (isBigO_of_norm_le_volterra_bound_on hI.measurableSet hP0 hQ0 (hΦ x₀ hx₀) (hΨ x₀ hx₀)
      fun x hx ↦ hle x hx.1)
    (Asymptotics.isBigO_zero _ _)
  exact ⟨h, hzero, fun x hx ↦ by simpa [hzero hx] using hle x hx⟩

end TauCeti
