/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Dynamics.BirkhoffSum.Average
import TauCeti.Probability.Ergodic.MaximalErgodic
import TauCeti.Probability.Ergodic.PointwiseErgodic

/-!
# The `Lᵖ` and `L¹` ergodic theorems

This file establishes `Lᵖ` (`1 ≤ p < ∞`) and `L¹` convergence of Birkhoff averages to the
invariant conditional expectation `μ[f | MeasurableSpace.invariants T]` for Banach-space-valued
observables of a measure-preserving map `T`, together with the ergodic specialization to the space
average `⨍ y, f y ∂μ`.

## Main results

* `MeasureTheory.MeasurePreserving.tendsto_eLpNorm_birkhoffAverage_sub_condExp` — `Lᵖ` ergodic
  convergence (`1 ≤ p < ∞`) to `μ[f | MeasurableSpace.invariants T]` whenever
  `μ.trim (MeasurableSpace.invariants_le T)` is σ-finite and `f ∈ Lᵖ(μ; E) ∩ L¹(μ; E)`;
* `MeasureTheory.MeasurePreserving.tendsto_integral_norm_birkhoffAverage_sub_condExp` — `L¹`
  ergodic convergence in integral-of-norm form;
* `Ergodic.tendsto_eLpNorm_birkhoffAverage_sub_average` — `Lᵖ` ergodic convergence (`1 ≤ p < ∞`)
  to the constant space average for an ergodic map on a finite measure space.

## References

* U. Krengel, *Ergodic Theorems*, de Gruyter Studies in Mathematics 6, 1985, Chapter 1.
* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer GTM 259,
  2011, Section 2.6.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set TauCeti
open scoped ENNReal MeasureTheory Topology

namespace MeasureTheory.MeasurePreserving

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Dominated `Lᵖ` convergence (`1 ≤ p < ∞`) on a finite measure space for a bounded integrable
observable. -/
private theorem tendsto_eLpNorm_birkhoffAverage_sub_condExp_of_bound
    [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    {s : Ω → E} (hs_int : Integrable s μ) {M : ℝ} (hM : ∀ x, ‖s x‖ ≤ M) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T s n -
        μ[s | MeasurableSpace.invariants T]) p μ) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hsm (n : ℕ) : AEStronglyMeasurable
      (birkhoffAverage ℝ T s n - μ[s | MeasurableSpace.invariants T]) μ :=
    (aestronglyMeasurable_birkhoffAverage hT.quasiMeasurePreserving hs_int.1).sub
      integrable_condExp.1
  simp_rw [fun n ↦ eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top (hsm n)]
  have hlim_int : Tendsto (fun n ↦ ∫⁻ x, ‖(birkhoffAverage ℝ T s n -
      μ[s | MeasurableSpace.invariants T]) x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _x, (0 : ℝ≥0∞) ∂μ := by simp
    rw [h0]
    refine tendsto_lintegral_of_dominated_convergence'
      (fun _ ↦ ENNReal.ofReal (2 * M) ^ p.toReal)
      (fun n ↦ (hsm n).eNorm.pow_const p.toReal)
      (fun n ↦ ?_)
      (by
        rw [lintegral_const]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp_pos.le ENNReal.ofReal_ne_top)
          (measure_ne_top μ univ)) ?_
    · filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (m := MeasurableSpace.invariants T)
          (ae_of_all _ hM)] with x hce
      rw [Pi.sub_apply, ← ofReal_norm]
      have havg := norm_birkhoffAverage_le_of_norm_le T hM n x
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith)))
        hp_pos.le
    · filter_upwards [hT.ae_tendsto_birkhoffAverage_condExp hs_int] with x hx
      have hsub : Tendsto (fun n ↦ ‖birkhoffAverage ℝ T s n x -
          μ[s | MeasurableSpace.invariants T] x‖ₑ) atTop (𝓝 0) := by
        simpa using (hx.sub (tendsto_const_nhds (x := μ[s | MeasurableSpace.invariants T] x))).eNorm
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp_pos] using
        ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp hsub
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hp_pos)] using
    ((ENNReal.continuous_rpow_const (y := p.toReal⁻¹)).tendsto 0).comp hlim_int

/-- `Lᵖ` ergodic convergence on a finite measure space for `1 ≤ p < ∞`. -/
private theorem tendsto_eLpNorm_birkhoffAverage_sub_condExp_of_isFiniteMeasure
    [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : Ω → E} (hf : MemLp f p μ) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T f n -
        μ[f | MeasurableSpace.invariants T]) p μ) atTop (𝓝 0) := by
  have hf_int : Integrable f μ := hf.integrable hp1
  refine ENNReal.tendsto_atTop_zero.mpr fun ε hε ↦ eventually_atTop.mp ?_
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ 3 * δ ≤ ε :=
    ⟨min (ε / 4) 1, lt_min (ENNReal.div_pos hε.ne' (by norm_num)) one_pos, by
      calc 3 * min (ε / 4) 1 ≤ 3 * (ε / 4) := by gcongr; exact min_le_left _ _
        _ ≤ 4 * (ε / 4) := by gcongr; norm_num
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)⟩
  obtain ⟨s, hs_lt, hs_lp⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt hp_top hδ0.ne'
  have hs_int : Integrable (⇑s) μ := hs_lp.integrable hp1
  obtain ⟨M, hM⟩ := s.exists_forall_norm_le
  have hs_tend :=
    hT.tendsto_eLpNorm_birkhoffAverage_sub_condExp_of_bound hp1 hp_top hs_int hM
  filter_upwards [hs_tend.eventually (gt_mem_nhds hδ0)] with n hn
  have hce_sub : μ[f | MeasurableSpace.invariants T] - μ[⇑s | MeasurableSpace.invariants T] =ᵐ[μ]
      μ[f - ⇑s | MeasurableSpace.invariants T] :=
    (condExp_sub hf_int hs_int _).symm
  have hsplit : birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T] =ᵐ[μ]
      (birkhoffAverage ℝ T (f - ⇑s) n + (birkhoffAverage ℝ T (⇑s) n -
        μ[⇑s | MeasurableSpace.invariants T])) - μ[f - ⇑s | MeasurableSpace.invariants T] := by
    filter_upwards [hce_sub] with x hx
    simp only [Pi.sub_apply, Pi.add_apply, birkhoffAverage_sub_apply] at hx ⊢
    rw [← hx]; abel
  calc
    eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) p μ
      = eLpNorm ((birkhoffAverage ℝ T (f - ⇑s) n + (birkhoffAverage ℝ T (⇑s) n -
          μ[⇑s | MeasurableSpace.invariants T])) -
          μ[f - ⇑s | MeasurableSpace.invariants T]) p μ :=
          eLpNorm_congr_ae hsplit
    _ ≤ eLpNorm (birkhoffAverage ℝ T (f - ⇑s) n + (birkhoffAverage ℝ T (⇑s) n -
          μ[⇑s | MeasurableSpace.invariants T])) p μ +
          eLpNorm (μ[f - ⇑s | MeasurableSpace.invariants T]) p μ :=
          eLpNorm_sub_le hp1
    _ ≤ eLpNorm (birkhoffAverage ℝ T (f - ⇑s) n) p μ +
          eLpNorm (birkhoffAverage ℝ T (⇑s) n - μ[⇑s | MeasurableSpace.invariants T]) p μ +
          eLpNorm (μ[f - ⇑s | MeasurableSpace.invariants T]) p μ := by
          gcongr; exact eLpNorm_add_le hp1
    _ ≤ δ + δ + δ :=
          add_le_add
            (add_le_add ((hT.eLpNorm_birkhoffAverage_le hp1 (f - ⇑s) n).trans hs_lt.le) hn.le)
            ((eLpNorm_condExp_le_eLpNorm (f - ⇑s) hp1).trans hs_lt.le)
    _ = 3 * δ := by ring
    _ ≤ ε := hδ

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- For `f ∈ Lᵖ(μ)` (`0 < p < ∞`), the `Lᵖ` seminorm on the complements of spanning sets of a
σ-finite trimmed measure tends to `0`. -/
private theorem tendsto_eLpNorm_restrict_compl_spanningSets
    [SigmaFinite (μ.trim (MeasurableSpace.invariants_le T))] {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp_top : p ≠ ∞) {f : Ω → E} (hf : MemLp f p μ) :
    Tendsto (fun k ↦ eLpNorm f p (μ.restrict
      (spanningSets (μ.trim (MeasurableSpace.invariants_le T)) k)ᶜ)) atTop (𝓝 0) := by
  let hm := MeasurableSpace.invariants_le T
  let S := spanningSets (μ.trim hm)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hSm (k : ℕ) : MeasurableSet (S k) := (measurableSet_spanningSets (μ.trim hm) k).1
  have hlim_int : Tendsto (fun k ↦ ∫⁻ x, (S k)ᶜ.indicator (fun y ↦ ‖f y‖ₑ ^ p.toReal) x ∂μ)
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _x, (0 : ℝ≥0∞) ∂μ := by simp
    rw [h0]
    refine tendsto_lintegral_of_dominated_convergence' (fun y ↦ ‖f y‖ₑ ^ p.toReal)
      (fun k ↦ (hf.aestronglyMeasurable.eNorm.pow_const p.toReal).indicator (hSm k).compl)
      (fun k ↦ ae_of_all _ fun y ↦ indicator_le_self _ _ y)
      (by
        have hlt := hf.eLpNorm_lt_top
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hf.aestronglyMeasurable] at hlt
        by_contra htop
        rw [htop, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp_pos)] at hlt
        exact lt_irrefl ∞ hlt) ?_
    refine ae_of_all _ fun y ↦ ?_
    have hy : y ∈ ⋃ k, S k := by rw [iUnion_spanningSets]; trivial
    obtain ⟨k₀, hk₀⟩ := mem_iUnion.mp hy
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with k hk
    rw [indicator_of_notMem (not_not.mpr (monotone_spanningSets (μ.trim hm) hk hk₀))]
  have hrpow : Tendsto
      (fun k ↦ (∫⁻ x, (S k)ᶜ.indicator (fun y ↦ ‖f y‖ₑ ^ p.toReal) x ∂μ) ^ (1 / p.toReal))
      atTop (𝓝 0) := by
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hp_pos)] using
      ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hlim_int
  refine hrpow.congr fun k ↦ ?_
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hf.aestronglyMeasurable.restrict,
    lintegral_indicator (hSm k).compl]

/-- Bound the `Lᵖ` distance on `μ` by its restriction to an invariant set `S` plus twice the `Lᵖ`
norm of `f` on `Sᶜ`. -/
private theorem eLpNorm_birkhoffAverage_sub_condExp_le_add_compl (hT : MeasurePreserving T μ μ)
    [SigmaFinite (μ.trim (MeasurableSpace.invariants_le T))] {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {f : Ω → E} (hf_int : Integrable f μ) {S : Set Ω}
    (hS : MeasurableSet[MeasurableSpace.invariants T] S) (n : ℕ) :
    eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) p μ ≤
      eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) p (μ.restrict S) +
        2 * eLpNorm f p (μ.restrict Sᶜ) := by
  let d : Ω → E := birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]
  have hTSc : MeasurePreserving T (μ.restrict Sᶜ) (μ.restrict Sᶜ) := by
    have h := hT.restrict_preimage hS.1.compl
    rwa [hS.compl.2] at h
  have hsplit : eLpNorm d p μ ≤ eLpNorm d p (μ.restrict S) + eLpNorm d p (μ.restrict Sᶜ) := by
    calc
      eLpNorm d p μ
        = eLpNorm (S.indicator d + Sᶜ.indicator d) p μ := by rw [Set.indicator_self_add_compl]
      _ ≤ eLpNorm (S.indicator d) p μ + eLpNorm (Sᶜ.indicator d) p μ := eLpNorm_add_le hp1
      _ = eLpNorm d p (μ.restrict S) + eLpNorm d p (μ.restrict Sᶜ) := by
            rw [eLpNorm_indicator_eq_eLpNorm_restrict hS.1.nullMeasurableSet,
              eLpNorm_indicator_eq_eLpNorm_restrict hS.1.compl.nullMeasurableSet]
  have hcompl_le : eLpNorm d p (μ.restrict Sᶜ) ≤ 2 * eLpNorm f p (μ.restrict Sᶜ) := by
    calc
      eLpNorm d p (μ.restrict Sᶜ)
        ≤ eLpNorm (birkhoffAverage ℝ T f n) p (μ.restrict Sᶜ) +
            eLpNorm (μ[f | MeasurableSpace.invariants T]) p (μ.restrict Sᶜ) := eLpNorm_sub_le hp1
      _ = eLpNorm (birkhoffAverage ℝ T f n) p (μ.restrict Sᶜ) +
            eLpNorm ((μ.restrict Sᶜ)[f | MeasurableSpace.invariants T]) p (μ.restrict Sᶜ) := by
            congr 1
            exact eLpNorm_congr_ae (condExp_restrict_ae_eq_restrict
              (MeasurableSpace.invariants_le T) hS.compl hf_int).symm
      _ ≤ eLpNorm f p (μ.restrict Sᶜ) + eLpNorm f p (μ.restrict Sᶜ) := by
            gcongr
            · exact hTSc.eLpNorm_birkhoffAverage_le hp1 f n
            · exact eLpNorm_condExp_le_eLpNorm f hp1
      _ = 2 * eLpNorm f p (μ.restrict Sᶜ) := (two_mul _).symm
  exact hsplit.trans (add_le_add_right hcompl_le _)

/-- **The `Lᵖ` ergodic theorem (`1 ≤ p < ∞`).**
For a measure-preserving map `T` whose invariant-trimmed measure
`μ.trim (MeasurableSpace.invariants_le T)` is σ-finite and any integrable `f ∈ Lᵖ(μ; E)` valued in
a real Banach space, the Birkhoff averages converge in `Lᵖ` to
`μ[f | MeasurableSpace.invariants T]`. -/
theorem tendsto_eLpNorm_birkhoffAverage_sub_condExp (hT : MeasurePreserving T μ μ)
    [SigmaFinite (μ.trim (MeasurableSpace.invariants_le T))] {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp_top : p ≠ ∞) {f : Ω → E} (hf : MemLp f p μ) (hf_int : Integrable f μ) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T f n -
        μ[f | MeasurableSpace.invariants T]) p μ) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  let hm := MeasurableSpace.invariants_le T
  let S : ℕ → Set Ω := spanningSets (μ.trim hm)
  have hSm (k : ℕ) : MeasurableSet[MeasurableSpace.invariants T] (S k) :=
    measurableSet_spanningSets (μ.trim hm) k
  have hS_fin (k : ℕ) : μ (S k) < ∞ := by
    rw [← trim_measurableSet_eq hm (hSm k)]
    exact measure_spanningSets_lt_top (μ.trim hm) k
  refine ENNReal.tendsto_atTop_zero.mpr fun ε hε ↦ eventually_atTop.mp ?_
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨k, hk⟩ :=
    ((tendsto_eLpNorm_restrict_compl_spanningSets (T := T) hp0 hp_top hf).eventually
      (gt_mem_nhds hε3)).exists
  have : IsFiniteMeasure (μ.restrict (S k)) := isFiniteMeasure_restrict.mpr (hS_fin k).ne
  have hTk : MeasurePreserving T (μ.restrict (S k)) (μ.restrict (S k)) := by
    have h := hT.restrict_preimage (hSm k).1
    rwa [(hSm k).2] at h
  have hpiece_tend : Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T f n -
      μ[f | MeasurableSpace.invariants T]) p (μ.restrict (S k))) atTop (𝓝 0) := by
    refine (hTk.tendsto_eLpNorm_birkhoffAverage_sub_condExp_of_isFiniteMeasure hp1 hp_top
      (hf.restrict (S k))).congr fun n ↦ eLpNorm_congr_ae ?_
    filter_upwards [condExp_restrict_ae_eq_restrict hm (hSm k) hf_int] with x hx
    simp [Pi.sub_apply, hx]
  filter_upwards [hpiece_tend.eventually (gt_mem_nhds hε3)] with n hn
  calc
    eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) p μ
      ≤ eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) p
          (μ.restrict (S k)) + 2 * eLpNorm f p (μ.restrict (S k)ᶜ) :=
          hT.eLpNorm_birkhoffAverage_sub_condExp_le_add_compl hp1 hf_int (hSm k) n
    _ ≤ ε / 3 + 2 * (ε / 3) := add_le_add hn.le (by gcongr)
    _ = 3 * (ε / 3) := by ring
    _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- **The `L¹` ergodic theorem.**
For a measure-preserving map `T` whose invariant-trimmed measure
`μ.trim (MeasurableSpace.invariants_le T)` is σ-finite and any integrable Banach-space-valued
observable `f : Ω → E`, the `L¹` distance between `birkhoffAverage ℝ T f n` and
`μ[f | MeasurableSpace.invariants T]` tends to `0`. -/
theorem tendsto_integral_norm_birkhoffAverage_sub_condExp (hT : MeasurePreserving T μ μ)
    [SigmaFinite (μ.trim (MeasurableSpace.invariants_le T))] {f : Ω → E} (hf : Integrable f μ) :
    Tendsto (fun n ↦ ∫ x, ‖birkhoffAverage ℝ T f n x -
        μ[f | MeasurableSpace.invariants T] x‖ ∂μ) atTop (𝓝 0) := by
  have h1 := hT.tendsto_eLpNorm_birkhoffAverage_sub_condExp le_rfl ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hf) hf
  have hreal : Tendsto (fun n ↦ (eLpNorm (birkhoffAverage ℝ T f n -
      μ[f | MeasurableSpace.invariants T]) 1 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  refine hreal.congr fun n ↦ ?_
  have hsub : Integrable (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) μ :=
    (integrable_birkhoffAverage hT hf).sub integrable_condExp
  rw [eLpNorm_one_eq_lintegral_eNorm hsub.1, ← ofReal_integral_norm_eq_lintegral_eNorm hsub,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
  rfl

end MeasureTheory.MeasurePreserving

namespace Ergodic

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The `Lᵖ` ergodic theorem for ergodic maps on a finite measure space.**
For an ergodic map `T` on a finite measure space and `f ∈ Lᵖ(μ; E)` (`1 ≤ p < ∞`), the Birkhoff
averages converge in `Lᵖ` to the constant space average `⨍ y, f y ∂μ`. -/
theorem tendsto_eLpNorm_birkhoffAverage_sub_average [IsFiniteMeasure μ] (hT : Ergodic T μ)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞) {f : Ω → E} (hf : MemLp f p μ) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T f n - fun _ ↦ ⨍ y, f y ∂μ) p μ)
      atTop (𝓝 0) := by
  refine (hT.toMeasurePreserving.tendsto_eLpNorm_birkhoffAverage_sub_condExp hp1 hp_top hf
    (hf.integrable hp1)).congr fun n ↦ eLpNorm_congr_ae ?_
  filter_upwards [hT.toPreErgodic.condExp_invariants_ae_eq_average f] with x hx
  simp [Pi.sub_apply, hx]

end Ergodic
