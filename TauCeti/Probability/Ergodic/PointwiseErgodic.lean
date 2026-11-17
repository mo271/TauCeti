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

import Mathlib.Dynamics.BirkhoffSum.Maximal
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Dynamics.BirkhoffSum.Average
import TauCeti.Probability.Ergodic.MaximalErgodic

/-!
# Birkhoff's pointwise ergodic theorem

This file proves Birkhoff's pointwise ergodic theorem for integrable observables valued in a
complete real seminormed or Banach space, identifies the almost-everywhere limit with the
conditional expectation `μ[f | MeasurableSpace.invariants T]` given the invariant σ-algebra, and
specializes the result to ergodic transformations on both finite and infinite measure spaces.

## Main results

* `MeasureTheory.MeasurePreserving.ae_exists_tendsto_birkhoffAverage` — Birkhoff's pointwise
  almost-everywhere convergence for integrable observables valued in any complete real seminormed
  space on an arbitrary measure space;
* `MeasureTheory.MeasurePreserving.setIntegral_birkhoffAverage_of_invariants` — integrating a
  Birkhoff average (`n ≠ 0`) over an invariant measurable set recovers the set integral of the
  observable;
* `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_condExp` — identification of the
  almost-everywhere limit with `μ[f | MeasurableSpace.invariants T]` whenever the trimmed measure
  `μ.trim (MeasurableSpace.invariants_le T)` is σ-finite;
* `PreErgodic.condExp_invariants_ae_eq_average` — unconditional identification of the invariant
  conditional expectation of a pre-ergodic map with the constant space average `⨍ y, f y ∂μ`;
* `Ergodic.ae_tendsto_birkhoffAverage_average` and `Ergodic.ae_tendsto_birkhoffAverage_integral` —
  Birkhoff's pointwise ergodic theorem for ergodic maps on arbitrary measure spaces and on
  probability spaces.

## References

* G. D. Birkhoff, *Proof of the ergodic theorem*, Proc. Natl. Acad. Sci. USA 17 (1931), 656–660.
* U. Krengel, *Ergodic Theorems*, de Gruyter Studies in Mathematics 6, 1985, Chapter 1.
* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer GTM 259,
  2011, Section 2.6.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set TauCeti
open scoped ENNReal MeasureTheory Topology

namespace MeasureTheory.MeasurePreserving

/-! ## Almost-everywhere convergence on an arbitrary measure space -/

section AEConvergence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

private theorem lintegral_ofReal_lt_top_of_integrable {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂μ < ∞ :=
  (lintegral_mono fun x ↦ by
    rw [Real.eNorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)).trans_lt hg.2

/-- On a finite measure space where `b < limsup (A_n g)` everywhere, `b * μ.real univ ≤ ∫ g`. -/
private theorem mul_measureReal_le_integral_of_lt_limsup [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : Ω → ℝ} (hg : Integrable g μ) {b : ℝ}
    (hb : ∀ᵐ x ∂μ, (b : EReal) <
      limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop) :
    b * μ.real univ ≤ ∫ x, g x ∂μ := by
  have hae : ∀ᵐ x ∂μ, 0 < birkhoffSumSup T (g - fun _ ↦ b) x := by
    filter_upwards [hb] with x hx
    obtain ⟨n, hnb, hn1⟩ :=
      ((frequently_lt_of_lt_limsup (by isBoundedDefault) hx).and_eventually
        (eventually_ge_atTop 1)).exists
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hlt : b < birkhoffAverage ℝ T g n x := EReal.coe_lt_coe_iff.mp hnb
    rw [birkhoffAverage, smul_eq_mul, inv_mul_eq_div, lt_div_iff₀ hpos] at hlt
    have hsum : 0 < birkhoffSum T (g - fun _ ↦ b) n x := by
      rw [birkhoffSum_sub_apply, birkhoffSum_const, Pi.smul_apply, nsmul_eq_mul]; linarith
    exact (EReal.coe_pos.mpr hsum).trans_le
      (le_iSup (fun k ↦ ((birkhoffSum T (g - fun _ ↦ b) k x : ℝ) : EReal)) n)
  have h := setIntegral_birkhoffSumSup_nonneg μ hT (hg.sub (integrable_const b))
  rw [Measure.restrict_eq_self_of_ae_mem hae] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub hg (integrable_const b), integral_const, smul_eq_mul, mul_comm] at h
  linarith

/-- On a finite measure space where `liminf (A_n g) < a` everywhere, `∫ g ≤ a * μ.real univ`. -/
private theorem integral_le_mul_measureReal_of_liminf_lt [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : Ω → ℝ} (hg : Integrable g μ) {a : ℝ}
    (ha : ∀ᵐ x ∂μ, liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop <
      (a : EReal)) :
    ∫ x, g x ∂μ ≤ a * μ.real univ := by
  have hae : ∀ᵐ x ∂μ, ((-a : ℝ) : EReal) <
      limsup (fun n ↦ ((birkhoffAverage ℝ T (-g) n x : ℝ) : EReal)) atTop := by
    filter_upwards [ha] with x hx
    have h1 : ((-a : ℝ) : EReal) <
        -liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_neg_iff.mpr hx
    have h2 : -liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop =
        limsup (fun n ↦ ((birkhoffAverage ℝ T (-g) n x : ℝ) : EReal)) atTop := by
      rw [← EReal.limsup_neg]
      congr 1; funext n; simp [birkhoffAverage_neg_apply]
    exact h2 ▸ h1
  have h := hT.mul_measureReal_le_integral_of_lt_limsup hg.neg hae
  simp only [Pi.neg_apply, integral_neg] at h
  linarith

/-- On an invariant measurable set where the `liminf` lies below `a` and the `limsup` exceeds `b`
with `a < b`, the measure is zero. -/
private theorem measure_liminf_lt_and_lt_limsup_eq_zero (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg_int : Integrable g μ) {a b : ℝ} (hab : a < b) :
    μ {x | liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop < (a : EReal) ∧
      (b : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop} = 0 := by
  let L : Ω → EReal := fun x ↦ liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  let U : Ω → EReal := fun x ↦ limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  let E : Set Ω := {x | L x < (a : EReal) ∧ (b : EReal) < U x}
  have hL_meas : Measurable L := Measurable.liminf fun n ↦
    measurable_coe_real_ereal.comp (measurable_birkhoffAverage hT.measurable hg_meas)
  have hU_meas : Measurable U := Measurable.limsup fun n ↦
    measurable_coe_real_ereal.comp (measurable_birkhoffAverage hT.measurable hg_meas)
  have hE_meas : MeasurableSet E :=
    (measurableSet_lt hL_meas measurable_const).inter (measurableSet_lt measurable_const hU_meas)
  have hE_inv : T ⁻¹' E = E := by
    ext x
    simp only [E, L, U, mem_preimage, mem_ofPred_eq, liminf_birkhoffAverage_comp,
      limsup_birkhoffAverage_comp]
  have hE_fin : μ E < ∞ := by
    rcases lt_or_ge 0 b with hb | hb
    · refine (measure_mono fun x hx ↦ ?_).trans_lt
        (hT.measure_lt_birkhoffAverageSup_lt_top hg_meas.aemeasurable
          (lintegral_ofReal_lt_top_of_integrable hg_int) hb)
      exact hx.2.trans_le limsup_le_iSup
    · refine (measure_mono fun x hx ↦ ?_).trans_lt
        (hT.measure_lt_birkhoffAverageSup_lt_top hg_meas.neg.aemeasurable
          (lintegral_ofReal_lt_top_of_integrable hg_int.neg) (by linarith : 0 < -a))
      have h1 : ((-a : ℝ) : EReal) < -L x := by
        rw [EReal.coe_neg]; exact EReal.neg_lt_neg_iff.mpr hx.1
      have h2 : -L x = limsup (fun n ↦ ((birkhoffAverage ℝ T (-g) n x : ℝ) : EReal)) atTop := by
        simp only [L, ← EReal.limsup_neg]
        congr 1; funext n; simp [birkhoffAverage_neg_apply]
      exact (h2 ▸ h1).trans_le limsup_le_iSup
  let ν : Measure Ω := μ.restrict E
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hE_fin.ne
  have hTν : MeasurePreserving T ν ν := by
    have h := hT.restrict_preimage hE_meas
    rwa [hE_inv] at h
  have hb_le := hTν.mul_measureReal_le_integral_of_lt_limsup hg_int.integrableOn
    (ae_restrict_of_forall_mem hE_meas fun _ hx ↦ hx.2)
  have ha_ge := hTν.integral_le_mul_measureReal_of_liminf_lt hg_int.integrableOn
    (ae_restrict_of_forall_mem hE_meas fun _ hx ↦ hx.1)
  have hreal0 : ν.real univ = 0 := by nlinarith [measureReal_nonneg (μ := ν) (s := univ)]
  have hν0 : ν univ = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp hreal0 |>.resolve_right (measure_ne_top ν univ)
  simpa [ν, Measure.restrict_apply_univ] using hν0

/-- The set where `liminf (A_n g) < limsup (A_n g)` is null for measurable integrable `g`. -/
private theorem measure_liminf_lt_limsup_eq_zero (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg_int : Integrable g μ) :
    μ {x | liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop <
      limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop} = 0 := by
  refine measure_mono_null (t := ⋃ (a : ℚ) (b : ℚ) (_ : a < b),
    {x | liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop < ((a : ℝ) : EReal) ∧
      ((b : ℝ) : EReal) <
        limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop}) ?_ ?_
  · intro x hx
    obtain ⟨r1, hr1, hr2⟩ := EReal.exists_between_coe_real hx
    obtain ⟨r2, hr3, hr4⟩ := EReal.exists_between_coe_real hr2
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.mp hr3)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
    refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨by exact_mod_cast hb1, ?_⟩⟩⟩
    exact ⟨hr1.trans (EReal.coe_lt_coe_iff.mpr ha1), (EReal.coe_lt_coe_iff.mpr hb2).trans hr4⟩
  · refine measure_iUnion_null fun a ↦ measure_iUnion_null fun b ↦
      measure_iUnion_null fun hab ↦ ?_
    exact hT.measure_liminf_lt_and_lt_limsup_eq_zero hg_meas hg_int (by exact_mod_cast hab)

/-- For a measurable integrable real observable `g`, `birkhoffAverageSup T (|g ·|)` is finite
almost everywhere. -/
private theorem ae_birkhoffAverageSup_abs_lt_top (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg_int : Integrable g μ) :
    ∀ᵐ x ∂μ, birkhoffAverageSup T (fun y ↦ |g y|) x < ⊤ := by
  have hnull : μ {x | birkhoffAverageSup T (fun y ↦ |g y|) x = ⊤} = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) zero_le
    rw [zero_add]
    have hint_abs : ∫⁻ y, ENNReal.ofReal |g y| ∂μ < ∞ := by
      have hcongr : ∫⁻ y, ENNReal.ofReal |g y| ∂μ = ∫⁻ y, ‖g y‖ₑ ∂μ :=
        lintegral_congr fun y ↦ (Real.eNorm_eq_ofReal_abs (g y)).symm
      rw [hcongr]
      exact hg_int.2
    have hdiv_tend : Tendsto (fun m : ℕ ↦ (∫⁻ y, ENNReal.ofReal |g y| ∂μ) /
        ENNReal.ofReal ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have htop : Tendsto (fun m : ℕ ↦ ENNReal.ofReal ((m + 1 : ℕ) : ℝ)) atTop (𝓝 ⊤) := by
        simpa only [Function.comp_def, ENNReal.ofReal_natCast] using
          ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat 1)
      simpa [ENNReal.div_top] using
        ENNReal.Tendsto.const_div (a := ∫⁻ y, ENNReal.ofReal |g y| ∂μ) htop (Or.inr hint_abs.ne)
    obtain ⟨m, hm⟩ := (hdiv_tend.eventually (gt_mem_nhds hε)).exists
    have hsub : {x | birkhoffAverageSup T (fun y ↦ |g y|) x = ⊤} ⊆
        {x | (((m + 1 : ℕ) : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ |g y|) x} := by
      intro x hx
      rw [mem_ofPred_eq, hx]
      exact EReal.coe_lt_top _
    have hmax := hT.ofReal_mul_measure_lt_birkhoffAverageSup_le_lintegral
      (continuous_abs.measurable.comp hg_meas).aemeasurable ((m + 1 : ℕ) : ℝ)
    have hpos : ENNReal.ofReal ((m + 1 : ℕ) : ℝ) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hle : μ {x | (((m + 1 : ℕ) : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ |g y|) x} ≤
        (∫⁻ y, ENNReal.ofReal |g y| ∂μ) / ENNReal.ofReal ((m + 1 : ℕ) : ℝ) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)).mpr
        (by rwa [mul_comm])
    exact ((measure_mono hsub).trans hle).trans hm.le
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
  exact lt_top_iff_ne_top.mpr hx

/-- Real-valued Birkhoff pointwise convergence on an arbitrary measure space. -/
private theorem ae_exists_tendsto_birkhoffAverage_real (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∃ c : ℝ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 c) := by
  let g := hf.aestronglyMeasurable.mk f
  have hg_meas : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg_eq : g =ᵐ[μ] f := hf.aestronglyMeasurable.ae_eq_mk.symm
  have hg_int : Integrable g μ := hf.congr hg_eq.symm
  have havg_eq : ∀ᵐ x ∂μ, ∀ n, birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T g n x :=
    ae_all_iff.mpr fun n ↦ hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hg_eq.symm n
  have heq_lim : ∀ᵐ x ∂μ,
      liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop =
        limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
    filter_upwards [compl_mem_ae_iff.mpr (hT.measure_liminf_lt_limsup_eq_zero hg_meas hg_int)]
      with x hx
    exact le_antisymm liminf_le_limsup (not_lt.mp hx)
  filter_upwards [havg_eq, heq_lim, hT.ae_birkhoffAverageSup_abs_lt_top hg_meas hg_int] with
    x hx_eq hx_lim hx_fin
  have hbdd (n : ℕ) :
      |birkhoffAverage ℝ T g n x| ≤ (birkhoffAverageSup T (fun y ↦ |g y|) x).toReal := by
    have h1 : |birkhoffAverage ℝ T g n x| ≤ birkhoffAverage ℝ T (fun y ↦ |g y|) n x :=
      norm_birkhoffAverage_le T g n x
    have h2 : ((birkhoffAverage ℝ T (fun y ↦ |g y|) n x : ℝ) : EReal) ≤
        birkhoffAverageSup T (fun y ↦ |g y|) x :=
      le_iSup (fun k ↦ ((birkhoffAverage ℝ T (fun y ↦ |g y|) k x : ℝ) : EReal)) n
    have h0 : (0 : EReal) ≤ birkhoffAverageSup T (fun y ↦ |g y|) x :=
      (EReal.coe_nonneg.mpr (by simp : (0 : ℝ) ≤ birkhoffAverage ℝ T (fun y ↦ |g y|) 0 x)).trans
        (le_iSup (fun k ↦ ((birkhoffAverage ℝ T (fun y ↦ |g y|) k x : ℝ) : EReal)) 0)
    exact h1.trans (EReal.coe_le_coe_iff.mp <| h2.trans_eq
      (EReal.coe_toReal hx_fin.ne (ne_of_gt ((EReal.bot_lt_coe 0).trans_le h0))).symm)
  set C := (birkhoffAverageSup T (fun y ↦ |g y|) x).toReal
  set L := limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  have hL_le : L ≤ (C : EReal) := limsup_le_of_le (by isBoundedDefault) <|
    Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hbdd n))
  have hL_ge : ((-C : ℝ) : EReal) ≤ L := by
    rw [← hx_lim]
    exact le_liminf_of_le (by isBoundedDefault) <|
      Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le (hbdd n))
  have hL_eq : (L.toReal : EReal) = L :=
    EReal.coe_toReal (lt_of_le_of_lt hL_le (EReal.coe_lt_top C)).ne
      (lt_of_lt_of_le (EReal.bot_lt_coe (-C)) hL_ge).ne'
  refine ⟨L.toReal, ?_⟩
  have ht_ereal : Tendsto (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
      (𝓝 (L.toReal : EReal)) := by
    rw [hL_eq]
    exact tendsto_of_le_liminf_of_limsup_le hx_lim.ge le_rfl
  exact (EReal.tendsto_coe.mp ht_ereal).congr fun n ↦ (hx_eq n).symm

/-- Almost-everywhere convergence of Birkhoff averages for an integrable simple function taking
values in a real normed space. -/
private theorem ae_exists_tendsto_birkhoffAverage_simpleFunc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hT : MeasurePreserving T μ μ) (s : SimpleFunc Ω E) (hs : Integrable s μ) :
    ∀ᵐ x ∂μ, ∃ c : E, Tendsto (fun n ↦ birkhoffAverage ℝ T s n x) atTop (𝓝 c) := by
  classical
  let S := s.range.erase 0
  have hdec (x : Ω) : s x = ∑ c ∈ S, (s ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ)) x • c := by
    by_cases hx : s x = 0
    · rw [hx, eq_comm]
      refine Finset.sum_eq_zero fun c hc ↦ ?_
      have hne : s x ≠ c := by rw [hx]; exact (Finset.mem_erase.mp hc).1.symm
      simp [hne]
    · rw [Finset.sum_eq_single (s x)]
      · simp
      · intro c _ hne; simp [hne.symm]
      · intro hnot; exact absurd (Finset.mem_erase.mpr ⟨hx, s.mem_range_self x⟩) hnot
  have hphi_int (c : E) (hc : c ∈ S) :
      Integrable ((s ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_indicator_iff (s.measurableSet_fiber c)).mpr <|
      integrableOn_const (s.measure_preimage_lt_top_of_integrable hs (Finset.mem_erase.mp hc).1).ne
  have hae : ∀ᵐ x ∂μ, ∀ c ∈ S, ∃ l : ℝ,
      Tendsto (fun n ↦ birkhoffAverage ℝ T ((s ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ))) n x)
        atTop (𝓝 l) :=
    (ae_ball_iff S.countable_toSet).mpr fun c hc ↦
      hT.ae_exists_tendsto_birkhoffAverage_real (hphi_int c hc)
  filter_upwards [hae] with x hx
  choose l hl using hx
  refine ⟨∑ c ∈ S.attach, l c.1 c.2 • c.1, ?_⟩
  have havg (n : ℕ) : birkhoffAverage ℝ T s n x =
      ∑ c ∈ S.attach,
        birkhoffAverage ℝ T ((s ⁻¹' {c.1}).indicator (fun _ ↦ (1 : ℝ))) n x • c.1 := by
    rw [birkhoffAverage, birkhoffSum]
    simp_rw [hdec, ← Finset.sum_attach S]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [← Finset.sum_smul, smul_smul, birkhoffAverage, birkhoffSum, smul_eq_mul]
  simp_rw [havg]
  exact tendsto_finsetSum _ fun c _ ↦ (hl c.1 c.2).smul_const c.1

omit [MeasurableSpace Ω] in
/-- Pointwise inclusion controlling failure of the `ε`-Cauchy condition by failure of the Cauchy
condition for an approximant `s` and the maximal function of `‖f - s‖`. -/
private theorem not_cauchy_birkhoffAverage_subset {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Ω → Ω) (f s : Ω → E) {ε : ℝ} (hε : 0 < ε) :
    {x | ¬ ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ‖birkhoffAverage ℝ T f m x - birkhoffAverage ℝ T f n x‖ < ε} ⊆
      {x | CauchySeq (fun n ↦ birkhoffAverage ℝ T s n x)}ᶜ ∪
        {x | ((ε / 3 : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ ‖(f - s) y‖) x} := by
  intro x hx
  by_contra hnot
  rw [mem_union, mem_compl_iff, not_or, not_not] at hnot
  obtain ⟨hxG, hxB⟩ := hnot
  apply hx
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hxG (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hnorm_le (k : ℕ) : ‖birkhoffAverage ℝ T (f - s) k x‖ ≤ ε / 3 := by
    have h2 : ((birkhoffAverage ℝ T (fun y ↦ ‖(f - s) y‖) k x : ℝ) : EReal) ≤
        ((ε / 3 : ℝ) : EReal) :=
      (le_iSup (fun j ↦ ((birkhoffAverage ℝ T (fun y ↦ ‖(f - s) y‖) j x : ℝ) : EReal)) k).trans
        (not_lt.mp hxB)
    exact (norm_birkhoffAverage_le T (f - s) k x).trans (EReal.coe_le_coe_iff.mp h2)
  have hid : birkhoffAverage ℝ T f m x - birkhoffAverage ℝ T f n x =
      (birkhoffAverage ℝ T (f - s) m x +
        (birkhoffAverage ℝ T s m x - birkhoffAverage ℝ T s n x)) -
        birkhoffAverage ℝ T (f - s) n x := by
    simp [birkhoffAverage_sub_apply]
  have hs_dist : ‖birkhoffAverage ℝ T s m x - birkhoffAverage ℝ T s n x‖ < ε / 3 := by
    simpa [dist_eq_norm] using hN m hm n hn
  rw [hid]
  linarith [hnorm_le m, hnorm_le n,
    norm_sub_le (birkhoffAverage ℝ T (f - s) m x +
      (birkhoffAverage ℝ T s m x - birkhoffAverage ℝ T s n x))
      (birkhoffAverage ℝ T (f - s) n x),
    norm_add_le (birkhoffAverage ℝ T (f - s) m x)
      (birkhoffAverage ℝ T s m x - birkhoffAverage ℝ T s n x)]

/-- For any `ε > 0`, the set of points where the Birkhoff averages of an integrable `f` fail the
`ε`-Cauchy condition has measure zero. -/
private theorem measure_not_cauchy_birkhoffAverage_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hT : MeasurePreserving T μ μ) {f : Ω → E} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ {x | ¬ ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ‖birkhoffAverage ℝ T f m x - birkhoffAverage ℝ T f n x‖ < ε} = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ ↦ ?_) zero_le
  rw [zero_add]
  have hε3 : 0 < ε / 3 := by positivity
  have hprod_ne : ENNReal.ofReal (ε / 3) * δ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hε3).ne' hδ.ne'
  obtain ⟨s, hs_lt, hs_lp⟩ :=
    (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top hprod_ne
  have hs_int : Integrable (⇑s) μ := memLp_one_iff_integrable.mp hs_lp
  let Good : Set Ω := {x | CauchySeq (fun n ↦ birkhoffAverage ℝ T (⇑s) n x)}
  let Big : Set Ω :=
    {x | ((ε / 3 : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ ‖(f - ⇑s) y‖) x}
  have hGood_compl : μ Goodᶜ = 0 := by
    rw [← compl_mem_ae_iff, compl_compl]
    filter_upwards [hT.ae_exists_tendsto_birkhoffAverage_simpleFunc s hs_int] with x ⟨c, hc⟩
    exact hc.cauchySeq
  have hmax := hT.ofReal_mul_measure_lt_birkhoffAverageSup_le_lintegral
    (hf.sub hs_int).norm.aemeasurable (ε / 3)
  have hBig : μ Big ≤ δ := by
    have hlint : ∫⁻ y, ENNReal.ofReal ‖(f - ⇑s) y‖ ∂μ = eLpNorm (f - ⇑s) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_eNorm (hf.sub hs_int).1]
      exact lintegral_congr fun y ↦ ofReal_norm _
    rw [hlint] at hmax
    have hc0 : ENNReal.ofReal (ε / 3) ≠ 0 := (ENNReal.ofReal_pos.mpr hε3).ne'
    calc
      μ Big = (ENNReal.ofReal (ε / 3))⁻¹ * (ENNReal.ofReal (ε / 3) * μ Big) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (ε / 3))⁻¹ * (ENNReal.ofReal (ε / 3) * δ) :=
          mul_le_mul' le_rfl (hmax.trans hs_lt.le)
      _ = δ := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
  exact ((measure_mono (not_cauchy_birkhoffAverage_subset T f (⇑s) hε)).trans
    (measure_union_le Goodᶜ Big)).trans (by simpa [hGood_compl] using hBig)

/-- Birkhoff pointwise almost-everywhere convergence in a real Banach space. -/
private theorem ae_exists_tendsto_birkhoffAverage_of_normed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hT : MeasurePreserving T μ μ) {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∃ c : E, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 c) := by
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ‖birkhoffAverage ℝ T f m x - birkhoffAverage ℝ T f n x‖ < ((k + 1 : ℕ) : ℝ)⁻¹ :=
    ae_all_iff.mpr fun k ↦ by
      rw [ae_iff]
      exact hT.measure_not_cauchy_birkhoffAverage_eq_zero hf
        (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos k)))
  filter_upwards [hall] with x hx
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hx k
  exact ⟨N, fun m hm n hn ↦ by
    rw [dist_eq_norm]
    exact (hN m hm n hn).trans (by simpa [one_div] using hk)⟩

/-- **Birkhoff's pointwise ergodic theorem (almost-everywhere convergence).**
For any measure-preserving map `T` on an arbitrary measure space `(Ω, μ)` and any integrable
function `f : Ω → E` valued in a complete real seminormed space, the Birkhoff averages
`birkhoffAverage ℝ T f n x` converge as `n → ∞` for `μ`-almost every `x`. -/
theorem ae_exists_tendsto_birkhoffAverage {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hT : MeasurePreserving T μ μ) {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∃ c : E, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 c) := by
  let q := SeparationQuotient.mkCLM ℝ E
  have hqf : Integrable (q ∘ f) μ :=
    ⟨q.continuous.comp_aestronglyMeasurable hf.1, by
      simpa [HasFiniteIntegral, q, ← ofReal_norm, SeparationQuotient.norm_mk] using hf.2⟩
  filter_upwards [hT.ae_exists_tendsto_birkhoffAverage_of_normed hqf] with x ⟨c', hc'⟩
  obtain ⟨c, rfl⟩ := SeparationQuotient.surjective_mk c'
  refine ⟨c, SeparationQuotient.isInducing_mk.tendsto_nhds_iff.mpr ?_⟩
  exact hc'.congr fun n ↦ (map_birkhoffAverage ℝ ℝ q.toAddMonoidHom T f n x).symm

end AEConvergence

/-! ## Identification of the pointwise limit with conditional expectation -/

section CondExpLimit

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Fatou bound for the almost-everywhere limit of Birkhoff averages. -/
private theorem lintegral_eNorm_le_eLpNorm_of_ae_tendsto (hT : MeasurePreserving T μ μ)
    {h L : Ω → E} (hh : Integrable h μ)
    (hL : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T h n x) atTop (𝓝 (L x))) :
    ∫⁻ x, ‖L x‖ₑ ∂μ ≤ eLpNorm h 1 μ := by
  have hlim : ∀ᵐ x ∂μ, ‖L x‖ₑ = liminf (fun n ↦ ‖birkhoffAverage ℝ T h n x‖ₑ) atTop := by
    filter_upwards [hL] with x hx
    exact hx.eNorm.liminf_eq.symm
  calc
    ∫⁻ x, ‖L x‖ₑ ∂μ
      = ∫⁻ x, liminf (fun n ↦ ‖birkhoffAverage ℝ T h n x‖ₑ) atTop ∂μ := lintegral_congr_ae hlim
    _ ≤ liminf (fun n ↦ ∫⁻ x, ‖birkhoffAverage ℝ T h n x‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' fun n ↦
          (aestronglyMeasurable_birkhoffAverage hT.quasiMeasurePreserving hh.1).eNorm
    _ ≤ eLpNorm h 1 μ := by
        have hle : liminf (fun n ↦ ∫⁻ x, ‖birkhoffAverage ℝ T h n x‖ₑ ∂μ) atTop ≤
            limsup (fun n ↦ ∫⁻ x, ‖birkhoffAverage ℝ T h n x‖ₑ ∂μ) atTop :=
          liminf_le_limsup
        refine hle.trans (limsup_le_of_le (by isBoundedDefault)
          (Eventually.of_forall fun n ↦ ?_))
        rw [← eLpNorm_one_eq_lintegral_eNorm
          (aestronglyMeasurable_birkhoffAverage hT.quasiMeasurePreserving hh.1)]
        exact hT.eLpNorm_birkhoffAverage_le le_rfl h n

/-- The set of points where the Birkhoff averages of a strongly measurable observable form a
Cauchy sequence is measurable and strictly `T`-invariant. -/
private theorem measurableSet_cauchySeq_birkhoffAverage (hT : Measurable T)
    {g : Ω → E} (hg_sm : StronglyMeasurable g) :
    MeasurableSet[MeasurableSpace.invariants T]
      {x | CauchySeq (fun n ↦ birkhoffAverage ℝ T g n x)} := by
  have havg_sm (j : ℕ) : StronglyMeasurable (birkhoffAverage ℝ T g j) := by
    have hEq : birkhoffAverage ℝ T g j = (j : ℝ)⁻¹ • ∑ i ∈ Finset.range j, g ∘ T^[i] := by
      ext x; simp [birkhoffAverage, birkhoffSum]
    rw [hEq]
    exact (Finset.stronglyMeasurable_sum _ fun i _ ↦
      hg_sm.comp_measurable (hT.iterate i)).const_smul ((j : ℝ)⁻¹)
  refine ⟨?_, ?_⟩
  · have hC_eq : {x | CauchySeq (fun n ↦ birkhoffAverage ℝ T g n x)} =
        ⋂ k : ℕ, ⋃ N : ℕ, ⋂ m ≥ N, ⋂ n ≥ N,
          {x | dist (birkhoffAverage ℝ T g m x) (birkhoffAverage ℝ T g n x) <
            ((k + 1 : ℕ) : ℝ)⁻¹} := by
      ext x
      simp only [mem_ofPred_eq, Metric.cauchySeq_iff, mem_iInter, mem_iUnion]
      refine ⟨fun h k ↦ h _ (by positivity), fun h ε hε ↦ ?_⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      exact ⟨N, fun m hm n hn ↦ (hN m hm n hn).trans (by simpa [one_div] using hk)⟩
    rw [hC_eq]
    refine MeasurableSet.iInter fun k ↦ MeasurableSet.iUnion fun N ↦
      MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦
        MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun _ ↦ ?_
    exact measurableSet_lt ((havg_sm m).dist (havg_sm n)).measurable measurable_const
  · ext x
    simp only [mem_preimage, mem_ofPred_eq]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete h
      exact ((tendsto_birkhoffAverage_comp_iff T g x c).mp hc).cauchySeq
    · obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete h
      exact ((tendsto_birkhoffAverage_comp_iff T g x c).mpr hc).cauchySeq

/-- Construct a strictly invariant, `(invariants T)`-strongly measurable, integrable limit
representative for a strongly measurable integrable observable `g`. -/
private theorem exists_invariants_stronglyMeasurable_limit (hT : MeasurePreserving T μ μ)
    {g : Ω → E} (hg_sm : StronglyMeasurable g) (hg_int : Integrable g μ) :
    ∃ L : Ω → E, StronglyMeasurable[MeasurableSpace.invariants T] L ∧ Integrable L μ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 (L x)) := by
  have havg_sm (j : ℕ) : StronglyMeasurable (birkhoffAverage ℝ T g j) := by
    have hEq : birkhoffAverage ℝ T g j = (j : ℝ)⁻¹ • ∑ i ∈ Finset.range j, g ∘ T^[i] := by
      ext x; simp [birkhoffAverage, birkhoffSum]
    rw [hEq]
    exact (Finset.stronglyMeasurable_sum _ fun i _ ↦
      hg_sm.comp_measurable (hT.measurable.iterate i)).const_smul ((j : ℝ)⁻¹)
  let C : Set Ω := {x | CauchySeq (fun n ↦ birkhoffAverage ℝ T g n x)}
  have hC : MeasurableSet[MeasurableSpace.invariants T] C :=
    measurableSet_cauchySeq_birkhoffAverage hT.measurable hg_sm
  let L : Ω → E := C.indicator fun x ↦ limUnder atTop (fun n ↦ birkhoffAverage ℝ T g n x)
  have hL_tend (x : Ω) :
      Tendsto (fun n ↦ C.indicator (birkhoffAverage ℝ T g n) x) atTop (𝓝 (L x)) := by
    by_cases hx : x ∈ C
    · simp only [L, indicator_of_mem hx]
      exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hx)
    · simp only [L, indicator_of_notMem hx]
      exact tendsto_const_nhds
  have hL_comp : L ∘ T = L := by
    funext x
    simp only [comp_apply]
    by_cases hx : x ∈ C
    · have hTx : T x ∈ C := by rwa [← mem_preimage, hC.2]
      have h1 : Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 (L x)) := by
        simpa [indicator_of_mem hx] using hL_tend x
      have h2 : Tendsto (fun n ↦ birkhoffAverage ℝ T g n (T x)) atTop (𝓝 (L (T x))) := by
        simpa [indicator_of_mem hTx] using hL_tend (T x)
      exact tendsto_nhds_unique h2 ((tendsto_birkhoffAverage_comp_iff T g x (L x)).mpr h1)
    · have hTx : T x ∉ C := by rwa [← mem_preimage, hC.2]
      simp [L, indicator_of_notMem hx, indicator_of_notMem hTx]
  have hL_sm : StronglyMeasurable L :=
    stronglyMeasurable_of_tendsto atTop (fun n ↦ (havg_sm n).indicator hC.1)
      (tendsto_pi_nhds.mpr hL_tend)
  have hL_inv_sm : StronglyMeasurable[MeasurableSpace.invariants T] L := by
    borelize E
    obtain ⟨hL_m, t, ht_sep, ht_sub⟩ := stronglyMeasurable_iff_measurable_separable.mp hL_sm
    exact stronglyMeasurable_iff_measurable_separable.mpr
      ⟨MeasurableSpace.measurable_invariants_dom.mpr
        ⟨hL_m, fun s _ ↦ congrArg (· ⁻¹' s) hL_comp⟩, t, ht_sep, ht_sub⟩
  have hL_ae_tend : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 (L x)) := by
    filter_upwards [hT.ae_exists_tendsto_birkhoffAverage hg_int] with x ⟨c, hc⟩
    have hx : x ∈ C := hc.cauchySeq
    simpa [indicator_of_mem hx] using hL_tend x
  have hL_int : Integrable L μ :=
    ⟨hL_sm.aestronglyMeasurable,
      (hT.lintegral_eNorm_le_eLpNorm_of_ae_tendsto hg_int hL_ae_tend).trans_lt
        (memLp_one_iff_integrable.mpr hg_int).eLpNorm_lt_top⟩
  exact ⟨L, hL_inv_sm, hL_int, hL_ae_tend⟩

omit [CompleteSpace E] in
/-- Dominated `L¹` convergence on a finite measure space for a uniformly bounded observable. -/
private theorem tendsto_eLpNorm_one_birkhoffAverage_sub_of_bound [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {s Ls : Ω → E} (hs_sm : AEStronglyMeasurable s μ)
    (hLs_sm : AEStronglyMeasurable Ls μ) {M : ℝ} (hM : ∀ x, ‖s x‖ ≤ M)
    (hLs_tend : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T s n x) atTop (𝓝 (Ls x))) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T s n - Ls) 1 μ) atTop (𝓝 0) := by
  have hsm (n : ℕ) : AEStronglyMeasurable (birkhoffAverage ℝ T s n - Ls) μ :=
    (aestronglyMeasurable_birkhoffAverage hT.quasiMeasurePreserving hs_sm).sub hLs_sm
  simp_rw [fun n ↦ eLpNorm_one_eq_lintegral_eNorm (hsm n)]
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _x, (0 : ℝ≥0∞) ∂μ := by simp
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence' (fun _ ↦ ENNReal.ofReal (2 * M))
    (fun n ↦ (hsm n).eNorm) (fun n ↦ ?_)
    (by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ univ)) ?_
  · filter_upwards [hLs_tend] with x hx
    have hLs_le : ‖Ls x‖ ≤ M :=
      le_of_tendsto hx.norm (Eventually.of_forall fun k ↦
        norm_birkhoffAverage_le_of_norm_le T hM k x)
    rw [Pi.sub_apply, ← ofReal_norm]
    have havg := norm_birkhoffAverage_le_of_norm_le T hM n x
    exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith))
  · filter_upwards [hLs_tend] with x hx
    simpa [Pi.sub_apply] using (hx.sub (tendsto_const_nhds (x := Ls x))).eNorm

omit [CompleteSpace E] in
/-- On a finite measure space, Birkhoff averages converge in `L¹` to their almost-everywhere
limit. -/
private theorem tendsto_eLpNorm_one_birkhoffAverage_sub_of_isFiniteMeasure
    [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {g L : Ω → E}
    (hg_int : Integrable g μ) (hL_sm : AEStronglyMeasurable L μ)
    (hL_ae : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop (𝓝 (L x))) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T g n - L) 1 μ) atTop (𝓝 0) := by
  refine ENNReal.tendsto_atTop_zero.mpr fun ε hε ↦ eventually_atTop.mp ?_
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ 3 * δ ≤ ε :=
    ⟨min (ε / 4) 1, lt_min (ENNReal.div_pos hε.ne' (by norm_num)) one_pos, by
      calc 3 * min (ε / 4) 1 ≤ 3 * (ε / 4) := by gcongr; exact min_le_left _ _
        _ ≤ 4 * (ε / 4) := by gcongr; norm_num
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)⟩
  obtain ⟨s, hs_lt, hs_lp⟩ :=
    (memLp_one_iff_integrable.mpr hg_int).exists_simpleFunc_eLpNorm_sub_lt
      ENNReal.one_ne_top hδ0.ne'
  have hs_int : Integrable (⇑s) μ := memLp_one_iff_integrable.mp hs_lp
  let Ls : Ω → E := fun x ↦ limUnder atTop (fun n ↦ birkhoffAverage ℝ T (⇑s) n x)
  have hLs_tend : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T (⇑s) n x) atTop (𝓝 (Ls x)) := by
    filter_upwards [hT.ae_exists_tendsto_birkhoffAverage_simpleFunc s hs_int] with x hx
    exact tendsto_nhds_limUnder hx
  have hLs_sm : AEStronglyMeasurable Ls μ := aestronglyMeasurable_of_tendsto_ae atTop
    (fun k ↦ aestronglyMeasurable_birkhoffAverage hT.quasiMeasurePreserving hs_int.1) hLs_tend
  obtain ⟨M, hM⟩ := s.exists_forall_norm_le
  have hs_dom := hT.tendsto_eLpNorm_one_birkhoffAverage_sub_of_bound hs_int.1 hLs_sm hM hLs_tend
  have hLsub_le : eLpNorm (L - Ls) 1 μ ≤ δ := by
    rw [eLpNorm_one_eq_lintegral_eNorm (hL_sm.sub hLs_sm)]
    refine (hT.lintegral_eNorm_le_eLpNorm_of_ae_tendsto (hg_int.sub hs_int) ?_).trans hs_lt.le
    filter_upwards [hL_ae, hLs_tend] with x hx1 hx2
    simpa [birkhoffAverage_sub_apply, Pi.sub_apply] using hx1.sub hx2
  filter_upwards [hs_dom.eventually (gt_mem_nhds hδ0)] with n hn
  have hsplit : birkhoffAverage ℝ T g n - L =
      (birkhoffAverage ℝ T (g - ⇑s) n + (birkhoffAverage ℝ T (⇑s) n - Ls)) - (L - Ls) := by
    ext x; simp [birkhoffAverage_sub_apply]
  calc
    eLpNorm (birkhoffAverage ℝ T g n - L) 1 μ
      ≤ eLpNorm (birkhoffAverage ℝ T (g - ⇑s) n + (birkhoffAverage ℝ T (⇑s) n - Ls)) 1 μ +
          eLpNorm (L - Ls) 1 μ := by
          rw [hsplit]; exact eLpNorm_sub_le le_rfl
    _ ≤ eLpNorm (birkhoffAverage ℝ T (g - ⇑s) n) 1 μ +
          eLpNorm (birkhoffAverage ℝ T (⇑s) n - Ls) 1 μ + eLpNorm (L - Ls) 1 μ := by
        gcongr; exact eLpNorm_add_le le_rfl
    _ ≤ δ + δ + δ :=
        add_le_add
          (add_le_add ((hT.eLpNorm_birkhoffAverage_le le_rfl (g - ⇑s) n).trans hs_lt.le) hn.le)
          hLsub_le
    _ = 3 * δ := by ring
    _ ≤ ε := hδ

omit [CompleteSpace E] in
/-- Integrating a Birkhoff average over an invariant measurable set recovers the set integral of
the observable for every `n ≠ 0`. -/
theorem setIntegral_birkhoffAverage_of_invariants (hT : MeasurePreserving T μ μ)
    {f : Ω → E} {s : Set Ω} (hs : MeasurableSet[MeasurableSpace.invariants T] s)
    (hf : IntegrableOn f s μ) {n : ℕ} (hn : n ≠ 0) :
    ∫ x in s, birkhoffAverage ℝ T f n x ∂μ = ∫ x in s, f x ∂μ := by
  have hTs : MeasurePreserving T (μ.restrict s) (μ.restrict s) := by
    have h := hT.restrict_preimage hs.1
    rwa [hs.2] at h
  have h1 : ∫ x in s, birkhoffAverage ℝ T f n x ∂μ =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, ∫ x in s, f (T^[k] x) ∂μ := by
    simp_rw [birkhoffAverage, birkhoffSum, integral_smul]
    rw [integral_finsetSum _ (f := fun k x ↦ f (T^[k] x)) fun k _ ↦
      (hTs.iterate k).integrable_comp_of_integrable hf]
  rw [h1]
  have h2 (k : ℕ) : ∫ x in s, f (T^[k] x) ∂μ = ∫ x in s, f x ∂μ := by
    have hk := hTs.iterate k
    rw [← integral_map hk.aemeasurable (hk.map_eq.symm ▸ hf.1), hk.map_eq]
  simp_rw [h2, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero (R := ℝ).mpr hn), one_smul]

omit [CompleteSpace E] in
/-- If `birkhoffAverage ℝ T g n → L` in `L¹`, then `L` and `g` have the same integral over every
invariant measurable set. -/
private theorem setIntegral_eq_of_tendsto_eLpNorm_one (hT : MeasurePreserving T μ μ)
    {g L : Ω → E} (hg_int : Integrable g μ) (hL_int : Integrable L μ)
    (hL1 : Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T g n - L) 1 μ) atTop (𝓝 0))
    {s : Set Ω} (hs : MeasurableSet[MeasurableSpace.invariants T] s) :
    ∫ x in s, L x ∂μ = ∫ x in s, g x ∂μ := by
  have hdiff_tend :
      Tendsto (fun n ↦ ‖∫ x in s, birkhoffAverage ℝ T g n x ∂μ - ∫ x in s, L x ∂μ‖)
        atTop (𝓝 0) := by
    have hreal : Tendsto (fun n ↦ (eLpNorm (birkhoffAverage ℝ T g n - L) 1 μ).toReal)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hreal
    have hint_sub : Integrable (birkhoffAverage ℝ T g n - L) μ :=
      (integrable_birkhoffAverage hT hg_int).sub hL_int
    calc
      ‖∫ x in s, birkhoffAverage ℝ T g n x ∂μ - ∫ x in s, L x ∂μ‖
        = ‖∫ x in s, (birkhoffAverage ℝ T g n x - L x) ∂μ‖ := by
            rw [integral_sub (integrable_birkhoffAverage hT hg_int).integrableOn
              hL_int.integrableOn]
      _ ≤ ∫ x in s, ‖birkhoffAverage ℝ T g n x - L x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖birkhoffAverage ℝ T g n x - L x‖ ∂μ :=
            setIntegral_le_integral hint_sub.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
      _ = (eLpNorm (birkhoffAverage ℝ T g n - L) 1 μ).toReal := by
            rw [eLpNorm_one_eq_lintegral_eNorm hint_sub.1,
              ← ofReal_integral_norm_eq_lintegral_eNorm hint_sub,
              ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
            rfl
  have hconst : Tendsto (fun n ↦ ‖∫ x in s, birkhoffAverage ℝ T g n x ∂μ - ∫ x in s, L x ∂μ‖)
      atTop (𝓝 ‖∫ x in s, g x ∂μ - ∫ x in s, L x ∂μ‖) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [hT.setIntegral_birkhoffAverage_of_invariants hs hg_int.integrableOn hn]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hconst hdiff_tend))).symm

/-- Birkhoff's pointwise ergodic theorem on a finite measure space. -/
private theorem ae_tendsto_birkhoffAverage_condExp_of_isFiniteMeasure
    [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop
      (𝓝 (μ[f | MeasurableSpace.invariants T] x)) := by
  let g := hf.aestronglyMeasurable.mk f
  have hg_sm : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hg_eq : g =ᵐ[μ] f := hf.aestronglyMeasurable.ae_eq_mk.symm
  have hg_int : Integrable g μ := hf.congr hg_eq.symm
  obtain ⟨L, hL_inv_sm, hL_int, hL_ae_tend⟩ :=
    hT.exists_invariants_stronglyMeasurable_limit hg_sm hg_int
  have hL1_tend :=
    hT.tendsto_eLpNorm_one_birkhoffAverage_sub_of_isFiniteMeasure hg_int hL_int.1 hL_ae_tend
  have hL_eq_condExp : L =ᵐ[μ] μ[f | MeasurableSpace.invariants T] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (MeasurableSpace.invariants_le T) hf
      (fun _ _ _ ↦ hL_int.integrableOn) (fun s hs _ ↦ ?_) hL_inv_sm.aestronglyMeasurable
    exact (hT.setIntegral_eq_of_tendsto_eLpNorm_one hg_int hL_int hL1_tend hs).trans
      (setIntegral_congr_ae hs.1 (hg_eq.mono fun _ hx _ ↦ hx))
  have havg_eq : ∀ᵐ x ∂μ, ∀ n, birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T g n x :=
    ae_all_iff.mpr fun n ↦ hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hg_eq.symm n
  filter_upwards [havg_eq, hL_ae_tend, hL_eq_condExp] with x hx_eq hx_tend hx_ce
  rw [← hx_ce]
  exact hx_tend.congr fun n ↦ (hx_eq n).symm

/-- **Birkhoff's pointwise ergodic theorem.**
For a measure-preserving map `T` whose invariant-trimmed measure
`μ.trim (MeasurableSpace.invariants_le T)` is σ-finite and any integrable Banach-space-valued
observable `f : Ω → E`, the Birkhoff averages `birkhoffAverage ℝ T f n x` converge almost
everywhere to the conditional expectation `μ[f | MeasurableSpace.invariants T] x`. -/
theorem ae_tendsto_birkhoffAverage_condExp (hT : MeasurePreserving T μ μ)
    [SigmaFinite (μ.trim (MeasurableSpace.invariants_le T))] {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop
      (𝓝 (μ[f | MeasurableSpace.invariants T] x)) := by
  let hm := MeasurableSpace.invariants_le T
  let S : ℕ → Set Ω := spanningSets (μ.trim hm)
  have hSm (k : ℕ) : MeasurableSet[MeasurableSpace.invariants T] (S k) :=
    measurableSet_spanningSets (μ.trim hm) k
  have hS_fin (k : ℕ) : μ (S k) < ∞ := by
    rw [← trim_measurableSet_eq hm (hSm k)]
    exact measure_spanningSets_lt_top (μ.trim hm) k
  have hpiece (k : ℕ) : ∀ᵐ x ∂μ.restrict (S k),
      Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop
        (𝓝 (μ[f | MeasurableSpace.invariants T] x)) := by
    have : IsFiniteMeasure (μ.restrict (S k)) := isFiniteMeasure_restrict.mpr (hS_fin k).ne
    have hTk : MeasurePreserving T (μ.restrict (S k)) (μ.restrict (S k)) := by
      have h := hT.restrict_preimage (hSm k).1
      rwa [(hSm k).2] at h
    filter_upwards [hTk.ae_tendsto_birkhoffAverage_condExp_of_isFiniteMeasure hf.integrableOn,
      condExp_restrict_ae_eq_restrict hm (hSm k) hf] with x hx hce
    rwa [← hce]
  rw [ae_iff]
  have hcov : {x | ¬ Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop
      (𝓝 (μ[f | MeasurableSpace.invariants T] x))} =
      ⋃ k, {x | ¬ Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop
        (𝓝 (μ[f | MeasurableSpace.invariants T] x))} ∩ S k := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  rw [hcov]
  refine measure_iUnion_null fun k ↦ ?_
  have hk := ae_iff.mp (hpiece k)
  rwa [Measure.restrict_apply' (hSm k).1] at hk

end CondExpLimit

end MeasureTheory.MeasurePreserving

/-! ## Ergodic specializations -/

namespace PreErgodic

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- On an infinite pre-ergodic measure space, the measure trimmed to the invariant σ-algebra is
never σ-finite. -/
private theorem not_sigmaFinite_trim_invariants (hT : PreErgodic T μ) (hinf : μ univ = ∞) :
    ¬ SigmaFinite (μ.trim (MeasurableSpace.invariants_le T)) := by
  intro hsf
  let hm := MeasurableSpace.invariants_le T
  have h0 (n : ℕ) : μ (spanningSets (μ.trim hm) n) = 0 := by
    have hsm := measurableSet_spanningSets (μ.trim hm) n
    have hlt : μ (spanningSets (μ.trim hm) n) < ∞ := by
      rw [← trim_measurableSet_eq hm hsm]
      exact measure_spanningSets_lt_top (μ.trim hm) n
    rcases hT.measure_self_or_compl_eq_zero hsm.1.nullMeasurableSet
        hsm.2.eventuallyEqSet with h | hc
    · exact h
    · exfalso
      have htop : μ univ ≤ μ (spanningSets (μ.trim hm) n) + μ (spanningSets (μ.trim hm) n)ᶜ := by
        calc μ univ = μ (spanningSets (μ.trim hm) n ∪ (spanningSets (μ.trim hm) n)ᶜ) := by
              rw [union_compl_self]
          _ ≤ μ (spanningSets (μ.trim hm) n) + μ (spanningSets (μ.trim hm) n)ᶜ :=
              measure_union_le _ _
      rw [hinf, hc, add_zero] at htop
      exact hlt.not_ge htop
  have huniv : μ univ = 0 := by
    rw [← iUnion_spanningSets (μ.trim hm)]
    exact measure_iUnion_null h0
  rw [hinf] at huniv
  exact ENNReal.top_ne_zero huniv

/-- For a pre-ergodic map `T`, the conditional expectation of any observable `f` given the
invariant σ-algebra is almost everywhere equal to the constant space average `⨍ y, f y ∂μ`.
This holds unconditionally without finiteness of `μ` or integrability of `f`. -/
theorem condExp_invariants_ae_eq_average (hT : PreErgodic T μ) (f : Ω → E) :
    μ[f | MeasurableSpace.invariants T] =ᵐ[μ] fun _ ↦ ⨍ y, f y ∂μ := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp [Filter.EventuallyEq]
  rcases eq_or_ne (μ univ) ∞ with hinf | hfin
  · rw [condExp_of_not_sigmaFinite (MeasurableSpace.invariants_le T)
      (hT.not_sigmaFinite_trim_invariants hinf)]
    simp [average_eq, Measure.real, hinf, Filter.EventuallyEq]
  · have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hfin⟩
    by_cases hf : Integrable f μ
    · refine (ae_eq_condExp_of_forall_setIntegral_eq (MeasurableSpace.invariants_le T) hf
        (fun _ _ _ ↦ (integrable_const _).integrableOn) (fun s hs _ ↦ ?_)
        aestronglyMeasurable_const).symm
      rcases hT.measure_self_or_compl_eq_zero hs.1.nullMeasurableSet
          hs.2.eventuallyEqSet with h0 | hc
      · simp [setIntegral_measure_zero _ h0]
      · have hrest : μ.restrict s = μ :=
          Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hc)
        have hpos : μ.real univ ≠ 0 := by
          rw [Measure.real, ne_eq, ENNReal.toReal_eq_zero_iff]
          push Not
          exact ⟨Measure.measure_univ_ne_zero.mpr hμ0, hfin⟩
        rw [hrest, integral_const, average_eq, smul_smul, mul_inv_cancel₀ hpos, one_smul]
    · rw [condExp_of_not_integrable hf]
      simp [average_eq, integral_undef hf, Filter.EventuallyEq]

end PreErgodic

namespace Ergodic

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- On an infinite ergodic measure space, any positive superlevel set of
`limsup (birkhoffAverage ℝ T (‖g ·‖))` has measure zero. -/
private theorem measure_lt_limsup_norm_eq_zero (hT : Ergodic T μ) (hinf : μ univ = ∞)
    {g : Ω → E} (hg_meas : Measurable (fun y ↦ ‖g y‖)) (hg_int : Integrable g μ)
    {ε : ℝ} (hε : 0 < ε) :
    μ {x | (ε : EReal) <
      limsup (fun n ↦ ((birkhoffAverage ℝ T (fun y ↦ ‖g y‖) n x : ℝ) : EReal)) atTop} = 0 := by
  let E : Set Ω := {x | (ε : EReal) <
    limsup (fun n ↦ ((birkhoffAverage ℝ T (fun y ↦ ‖g y‖) n x : ℝ) : EReal)) atTop}
  have hE_meas : MeasurableSet E := measurableSet_lt measurable_const <|
    Measurable.limsup fun n ↦
      measurable_coe_real_ereal.comp (measurable_birkhoffAverage hT.measurable hg_meas)
  have hE_inv : T ⁻¹' E = E := by
    ext x; simp only [E, mem_preimage, mem_ofPred_eq, limsup_birkhoffAverage_comp]
  have hfin : ∫⁻ y, ENNReal.ofReal ‖g y‖ ∂μ < ∞ :=
    (lintegral_congr fun _ ↦ ofReal_norm _).trans_lt hg_int.2
  have hE_fin : μ E < ∞ := by
    refine (measure_mono fun x hx ↦ ?_).trans_lt
      (hT.toMeasurePreserving.measure_lt_birkhoffAverageSup_lt_top hg_meas.aemeasurable hfin hε)
    dsimp only [E, mem_ofPred_eq] at hx
    exact hx.trans_le limsup_le_iSup
  rcases hT.measure_self_or_compl_eq_zero hE_meas.nullMeasurableSet
      hE_inv.eventuallyEqSet with h0 | hc
  · exact h0
  · exfalso
    have htop : μ univ ≤ μ E + μ Eᶜ := by
      calc μ univ = μ (E ∪ Eᶜ) := by rw [union_compl_self]
        _ ≤ μ E + μ Eᶜ := measure_union_le _ _
    rw [hinf, hc, add_zero] at htop
    exact hE_fin.not_ge htop

omit [CompleteSpace E] in
/-- On an infinite ergodic measure space, Birkhoff averages of any integrable observable vanish
almost everywhere. -/
private theorem ae_tendsto_birkhoffAverage_zero_of_measure_univ_eq_top (hT : Ergodic T μ)
    (hinf : μ univ = ∞) {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 0) := by
  let g := hf.aestronglyMeasurable.mk f
  have hg_meas : Measurable (fun y ↦ ‖g y‖) :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.norm.measurable
  have hg_eq : g =ᵐ[μ] f := hf.aestronglyMeasurable.ae_eq_mk.symm
  have hg_int : Integrable g μ := hf.congr hg_eq.symm
  have havg_eq : ∀ᵐ x ∂μ, ∀ n, birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T g n x :=
    ae_all_iff.mpr fun n ↦ hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hg_eq.symm n
  have hlim_le : ∀ᵐ x ∂μ, ∀ k : ℕ,
      limsup (fun n ↦ ((birkhoffAverage ℝ T (fun y ↦ ‖g y‖) n x : ℝ) : EReal)) atTop ≤
        ((((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) :=
    ae_all_iff.mpr fun k ↦ by
      have h0 := hT.measure_lt_limsup_norm_eq_zero hinf hg_meas hg_int
        (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos k)))
      filter_upwards [compl_mem_ae_iff.mpr h0] with x hx
      exact not_lt.mp hx
  filter_upwards [havg_eq, hlim_le] with x hx_eq hx_lim
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  have hlt : limsup (fun n ↦ ((birkhoffAverage ℝ T (fun y ↦ ‖g y‖) n x : ℝ) : EReal)) atTop <
      (δ : EReal) :=
    (hx_lim k).trans_lt (EReal.coe_lt_coe_iff.mpr (by simpa [one_div] using hk))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right, hx_eq n]
  exact (norm_birkhoffAverage_le T g n x).trans_lt (EReal.coe_lt_coe_iff.mp (hN n hn))

/-- **Birkhoff's pointwise ergodic theorem for ergodic maps.**
For an ergodic map `T` on an arbitrary measure space `(Ω, μ)` (finite or infinite) and any
integrable Banach-space-valued observable `f : Ω → E`, the Birkhoff averages converge almost
everywhere to the space average `⨍ y, f y ∂μ` (which equals `0` when `μ univ = ∞`). -/
theorem ae_tendsto_birkhoffAverage_average (hT : Ergodic T μ) {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 (⨍ y, f y ∂μ)) := by
  rcases eq_or_ne (μ univ) ∞ with hinf | hfin
  · simpa [average_eq, Measure.real, hinf] using
      hT.ae_tendsto_birkhoffAverage_zero_of_measure_univ_eq_top hinf hf
  · have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hfin⟩
    filter_upwards [hT.toMeasurePreserving.ae_tendsto_birkhoffAverage_condExp hf,
      hT.toPreErgodic.condExp_invariants_ae_eq_average f] with x hx hce
    rwa [← hce]

/-- **Birkhoff's pointwise ergodic theorem on a probability space.**
For an ergodic transformation `T` on a probability space `(Ω, μ)` and any integrable
Banach-space-valued observable `f : Ω → E`, the Birkhoff averages converge almost everywhere to
the integral `∫ y, f y ∂μ`. -/
theorem ae_tendsto_birkhoffAverage_integral [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
  simpa [average_eq_integral] using hT.ae_tendsto_birkhoffAverage_average hf

end Ergodic
