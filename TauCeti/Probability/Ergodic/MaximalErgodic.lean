/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Maximal

import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Maximal ergodic inequality on arbitrary measure spaces and `Lᵖ` contraction

Mathlib's `mul_measureReal_lt_birkhoffAverageSup_le_integral` states the maximal ergodic weak-type
inequality under `[IsFiniteMeasure μ]` and `Integrable g μ`. This file removes both restrictions,
establishing the `ENNReal` weak-type inequality on an arbitrary measure space for any
a.e.-measurable real observable, together with finiteness of positive superlevel sets and the `Lᵖ`
(`1 ≤ p ≤ ∞`) contraction property of Birkhoff averages.

## Main results

* `MeasureTheory.MeasurePreserving.ofReal_mul_measure_lt_birkhoffAverageSup_le_lintegral` —
  the maximal ergodic weak-type inequality on an arbitrary (not necessarily finite) measure space
  for any a.e.-measurable real observable and any real threshold;
* `MeasureTheory.MeasurePreserving.measure_lt_birkhoffAverageSup_lt_top` — finiteness of the
  superlevel set `{x | b < birkhoffAverageSup T g x}` for `b > 0` whenever
  `∫⁻ x, ENNReal.ofReal (g x) ∂μ < ∞`;
* `MeasureTheory.MeasurePreserving.eLpNorm_birkhoffAverage_le` — `Lᵖ` contraction (`1 ≤ p ≤ ∞`)
  of Birkhoff averages in any real seminormed space.

## References

* A. M. Garsia, *A simple proof of E. Hopf's maximal ergodic theorem*, J. Math. Mech. 14 (1965),
  381–382.
* U. Krengel, *Ergodic Theorems*, de Gruyter Studies in Mathematics 6, 1985, Chapter 1.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace MeasureTheory.MeasurePreserving

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-- Markov finiteness for the positive level sets `{((k + 1) : ℝ)⁻¹ ≤ h x}` of a measurable
nonnegative integrable function `h`. -/
private theorem measure_inv_le_lt_top {h : Ω → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (hint : Integrable h μ) (k : ℕ) :
    μ {x | ((k + 1 : ℝ)⁻¹) ≤ h x} < ∞ := by
  have hpos : ENNReal.ofReal ((k + 1 : ℝ)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hmk : ENNReal.ofReal ((k + 1 : ℝ)⁻¹) * μ {x | ((k + 1 : ℝ)⁻¹) ≤ h x} ≤
      ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
    have h1 := mul_meas_ge_le_lintegral₀ (μ := μ)
      hm.ennreal_ofReal.aemeasurable (ENNReal.ofReal ((k + 1 : ℝ)⁻¹))
    refine le_trans ?_ h1
    exact mul_le_mul_right (measure_mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx) _
  have hlt : ∫⁻ x, ENNReal.ofReal (h x) ∂μ < ∞ := by
    have hcongr : ∫⁻ x, ENNReal.ofReal (h x) ∂μ = ∫⁻ x, ‖h x‖ₑ ∂μ :=
      lintegral_congr fun x ↦ (Real.eNorm_eq_ofReal (h0 x)).symm
    rw [hcongr]
    exact hint.2
  refine lt_top_iff_ne_top.mpr fun htop ↦ ?_
  rw [htop, ENNReal.mul_top hpos] at hmk
  exact hlt.not_ge hmk

/-- Increasing measurable finite-measure cover of the superlevel set `{a < birkhoffAverageSup T h}`
for a measurable nonnegative integrable `h` and `a > 0`. -/
private theorem exists_monotone_cover_birkhoffAverageSup (hT : MeasurePreserving T μ μ)
    {h : Ω → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (hint : Integrable h μ)
    {a : ℝ} (ha : 0 < a) :
    ∃ U : ℕ → Set Ω, Monotone U ∧ (∀ m, MeasurableSet (U m)) ∧ (∀ m, μ (U m) < ∞) ∧
      {x | (a : EReal) < birkhoffAverageSup T h x} ⊆ ⋃ m, U m := by
  let A : ℕ → Set Ω := fun k ↦ {x | ((k + 1 : ℝ)⁻¹) ≤ h x}
  have hA_meas (k : ℕ) : MeasurableSet (A k) := measurableSet_le measurable_const hm
  refine ⟨fun m ↦ ⋃ i ≤ m, ⋃ j ≤ m, (T^[i]) ⁻¹' A j, ?_, ?_, ?_, ?_⟩
  · intro m n hmn x hx
    simp only [mem_iUnion] at hx ⊢
    rcases hx with ⟨i, hi, j, hj, hmem⟩
    exact ⟨i, hi.trans hmn, j, hj.trans hmn, hmem⟩
  · intro m
    exact MeasurableSet.biUnion (to_countable _) fun i _ ↦
      MeasurableSet.biUnion (to_countable _) fun j _ ↦ (hT.measurable.iterate i) (hA_meas j)
  · intro m
    refine measure_biUnion_lt_top (finite_le_nat m) fun i _ ↦
      measure_biUnion_lt_top (finite_le_nat m) fun j _ ↦ ?_
    rw [(hT.iterate i).measure_preimage (hA_meas j).nullMeasurableSet]
    exact measure_inv_le_lt_top hm h0 hint j
  · intro x hx
    simp only [mem_ofPred_eq, birkhoffAverageSup, lt_iSup_iff, EReal.coe_lt_coe_iff] at hx
    obtain ⟨n, hn⟩ := hx
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn; linarith
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hsum_pos : 0 < ∑ i ∈ Finset.range n, h (T^[i] x) := by
      have h1 := ha.trans hn
      rw [birkhoffAverage, smul_eq_mul, inv_mul_eq_div, lt_div_iff₀ hpos] at h1
      simpa [birkhoffSum] using h1
    obtain ⟨i, _, hi_pos⟩ : ∃ i ∈ Finset.range n, 0 < h (T^[i] x) := by
      by_contra! hle
      exact hsum_pos.not_ge (Finset.sum_nonpos fun i hi ↦ hle i hi)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hi_pos
    simp only [mem_iUnion, mem_preimage]
    exact ⟨max i j, i, le_max_left i j, j, le_max_right i j, by simpa [A, one_div] using hj.le⟩

/-- Maximal ergodic bound localized to any finite-measure measurable set `U`. -/
private theorem ofReal_mul_measure_inter_lt_birkhoffAverageSup_le_lintegral
    (hT : MeasurePreserving T μ μ) {h : Ω → ℝ} (h0 : ∀ x, 0 ≤ h x) (hint : Integrable h μ)
    {a : ℝ} (ha : 0 < a) {U : Set Ω} (hU_meas : MeasurableSet U) (hU_fin : μ U < ∞) :
    ENNReal.ofReal a * μ ({x | (a : EReal) < birkhoffAverageSup T h x} ∩ U) ≤
      ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
  let E : Set Ω := {x | (a : EReal) < birkhoffAverageSup T h x}
  let w : Ω → ℝ := h - U.indicator (fun _ ↦ a)
  have hind_int : Integrable (U.indicator (fun _ ↦ a)) μ :=
    (integrable_indicator_iff hU_meas).mpr (integrableOn_const hU_fin.ne)
  have hw_int : Integrable w μ := hint.sub hind_int
  let F : Set Ω := {x | 0 < birkhoffSumSup T w x}
  have hEF : E ⊆ F := by
    intro x hx
    dsimp only [E, F, mem_ofPred_eq] at hx ⊢
    rw [lt_birkhoffAverageSup_iff_lt_birkhoffSumSup ha.le] at hx
    refine hx.trans_le (iSup_mono fun n ↦ EReal.coe_le_coe_iff.mpr ?_)
    exact Finset.sum_le_sum fun k _ ↦
      sub_le_sub_left (Set.indicator_le_self' (fun _ _ ↦ ha.le) _) _
  have hnonneg : 0 ≤ ∫ x in F, w x ∂μ := setIntegral_birkhoffSumSup_nonneg μ hT hw_int
  have hbound : a * μ.real (F ∩ U) ≤ ∫ x, h x ∂μ := by
    have hind : ∫ x in F, U.indicator (fun _ ↦ a) x ∂μ = a * μ.real (F ∩ U) := by
      rw [setIntegral_indicator hU_meas, setIntegral_const, smul_eq_mul, mul_comm]
    have hw_int_eq : (∫ x in F, w x ∂μ) =
        ∫ x in F, h x ∂μ - ∫ x in F, U.indicator (fun _ ↦ a) x ∂μ :=
      integral_sub (μ := μ.restrict F) hint.integrableOn hind_int.integrableOn
    rw [hw_int_eq, hind] at hnonneg
    exact (sub_nonneg.mp hnonneg).trans (setIntegral_le_integral hint (ae_of_all _ h0))
  have hEU_fin : μ (E ∩ U) ≠ ∞ := ((measure_mono inter_subset_right).trans_lt hU_fin).ne
  have hreal : a * μ.real (E ∩ U) ≤ ∫ x, h x ∂μ := by
    refine (mul_le_mul_of_nonneg_left ?_ ha.le).trans hbound
    exact measureReal_mono (inter_subset_inter_left U hEF)
      ((measure_mono inter_subset_right).trans_lt hU_fin).ne
  calc
    ENNReal.ofReal a * μ (E ∩ U)
      = ENNReal.ofReal (a * μ.real (E ∩ U)) := by
          rw [ENNReal.ofReal_mul ha.le, Measure.real, ENNReal.ofReal_toReal hEU_fin]
    _ ≤ ENNReal.ofReal (∫ x, h x ∂μ) := ENNReal.ofReal_le_ofReal hreal
    _ = ∫⁻ x, ENNReal.ofReal (h x) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)

/-- Auxiliary maximal ergodic bound for a measurable nonnegative integrable observable on an
arbitrary measure space. -/
private theorem ofReal_mul_measure_lt_birkhoffAverageSup_le_lintegral_of_nonneg
    (hT : MeasurePreserving T μ μ) {h : Ω → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (hint : Integrable h μ) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * μ {x | (a : EReal) < birkhoffAverageSup T h x} ≤
      ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
  let E : Set Ω := {x | (a : EReal) < birkhoffAverageSup T h x}
  obtain ⟨U, hU_mono, hU_meas, hU_fin, hE_sub⟩ :=
    hT.exists_monotone_cover_birkhoffAverageSup hm h0 hint ha
  have htend : Tendsto (fun m ↦ ENNReal.ofReal a * μ (E ∩ U m)) atTop
      (𝓝 (ENNReal.ofReal a * μ E)) := by
    have hUeq : ⋃ m, (E ∩ U m) = E := by rw [← inter_iUnion, inter_eq_left.mpr hE_sub]
    have hμt : Tendsto (fun m ↦ μ (E ∩ U m)) atTop (𝓝 (μ E)) := by
      simpa only [hUeq, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ)
        (fun _ _ hmn ↦ inter_subset_inter_right E (hU_mono hmn))
    exact ENNReal.Tendsto.const_mul hμt (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto' htend fun m ↦
    hT.ofReal_mul_measure_inter_lt_birkhoffAverageSup_le_lintegral h0 hint ha (hU_meas m) (hU_fin m)

/-- **Maximal ergodic weak-type inequality on an arbitrary measure space.**
For any measure-preserving map `T`, a.e.-measurable real observable `g`, and threshold `a : ℝ`,
`ENNReal.ofReal a * μ {x | a < birkhoffAverageSup T g x} ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ`.
Neither finiteness of `μ`, integrability of `g`, nor `0 ≤ a` is required. -/
theorem ofReal_mul_measure_lt_birkhoffAverageSup_le_lintegral
    (hT : MeasurePreserving T μ μ) {g : Ω → ℝ} (hg : AEMeasurable g μ) (a : ℝ) :
    ENNReal.ofReal a * μ {x | (a : EReal) < birkhoffAverageSup T g x} ≤
      ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  by_cases ha : 0 < a
  swap
  · rw [ENNReal.ofReal_of_nonpos (not_lt.mp ha), zero_mul]; exact zero_le
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ∞
  · rw [hfin]; exact le_top
  let h : Ω → ℝ := fun x ↦ max (hg.mk g x) 0
  have hm : Measurable h := hg.measurable_mk.max measurable_const
  have h0 : ∀ x, 0 ≤ h x := fun x ↦ le_max_right _ _
  have hlint : ∫⁻ x, ENNReal.ofReal (h x) ∂μ = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hg.ae_eq_mk] with x hx
    simp only [h, ← hx]
    rcases le_total (g x) 0 with hle | hge
    · rw [max_eq_right hle, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hle]
    · rw [max_eq_left hge]
  have hint : Integrable h μ := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    have : ∫⁻ x, ‖h x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
      rw [← hlint]
      exact lintegral_congr fun x ↦ Real.eNorm_eq_ofReal (h0 x)
    rw [HasFiniteIntegral, this]
    exact lt_top_iff_ne_top.mpr hfin
  have hle_ae : ∀ᵐ x ∂μ, birkhoffAverageSup T g x ≤ birkhoffAverageSup T h x := by
    have hiter : ∀ᵐ x ∂μ, ∀ k : ℕ, g (T^[k] x) ≤ h (T^[k] x) := by
      rw [ae_all_iff]
      intro k
      filter_upwards [(hT.quasiMeasurePreserving.iterate k).ae hg.ae_eq_mk] with x hx
      simp [h, ← hx]
    filter_upwards [hiter] with x hx
    refine iSup_mono fun n ↦ EReal.coe_le_coe_iff.mpr ?_
    rw [birkhoffAverage, birkhoffAverage, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hx k) (by positivity)
  have hmeas_le : μ {x | (a : EReal) < birkhoffAverageSup T g x} ≤
      μ {x | (a : EReal) < birkhoffAverageSup T h x} :=
    measure_mono_ae (hle_ae.mono fun x hx hlt ↦ hlt.trans_le hx)
  calc
    ENNReal.ofReal a * μ {x | (a : EReal) < birkhoffAverageSup T g x}
      ≤ ENNReal.ofReal a * μ {x | (a : EReal) < birkhoffAverageSup T h x} := by gcongr
    _ ≤ ∫⁻ x, ENNReal.ofReal (h x) ∂μ :=
        hT.ofReal_mul_measure_lt_birkhoffAverageSup_le_lintegral_of_nonneg hm h0 hint ha
    _ = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := hlint

/-- For an a.e.-measurable real observable `g` with finite positive-part integral and any `b > 0`,
the superlevel set `{x | b < birkhoffAverageSup T g x}` has finite measure. -/
theorem measure_lt_birkhoffAverageSup_lt_top (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : AEMeasurable g μ) (hfin : ∫⁻ x, ENNReal.ofReal (g x) ∂μ < ∞)
    {b : ℝ} (hb : 0 < b) :
    μ {x | (b : EReal) < birkhoffAverageSup T g x} < ∞ := by
  have hmax := hT.ofReal_mul_measure_lt_birkhoffAverageSup_le_lintegral hg b
  refine lt_top_iff_ne_top.mpr fun htop ↦ ?_
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hb).ne'] at hmax
  exact hfin.not_ge hmax

/-- Birkhoff averages are contractions on `Lᵖ` for every `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_birkhoffAverage_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (hT : MeasurePreserving T μ μ) {p : ℝ≥0∞} (hp : 1 ≤ p) (f : Ω → E) (n : ℕ) :
    eLpNorm (birkhoffAverage ℝ T f n) p μ ≤ eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]; exact le_top
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hsum : birkhoffAverage ℝ T f n =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, (f ∘ T^[k]) := by
    ext x; simp [birkhoffAverage, birkhoffSum]
  have hsum_eq : ∑ k ∈ Finset.range n, eLpNorm (f ∘ T^[k]) p μ = n * eLpNorm f p μ := by
    calc
      ∑ k ∈ Finset.range n, eLpNorm (f ∘ T^[k]) p μ
        = ∑ _k ∈ Finset.range n, eLpNorm f p μ :=
            Finset.sum_congr rfl fun k _ ↦ eLpNorm_comp_measurePreserving hf (hT.iterate k)
      _ = n * eLpNorm f p μ := by simp
  calc
    eLpNorm (birkhoffAverage ℝ T f n) p μ
      = eLpNorm ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, (f ∘ T^[k])) p μ := by rw [hsum]
    _ ≤ ‖(n : ℝ)⁻¹‖ₑ * eLpNorm (∑ k ∈ Finset.range n, f ∘ T^[k]) p μ :=
          eLpNorm_const_smul_le'
    _ ≤ ‖(n : ℝ)⁻¹‖ₑ * ∑ k ∈ Finset.range n, eLpNorm (f ∘ T^[k]) p μ := by
          gcongr
          exact eLpNorm_sum_le hp
    _ = (n : ℝ≥0∞)⁻¹ * (n * eLpNorm f p μ) := by
          rw [hsum_eq, Real.eNorm_eq_ofReal (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹),
            ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)),
            ENNReal.ofReal_natCast]
    _ = eLpNorm f p μ := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn)
            (ENNReal.natCast_ne_top n), one_mul]

end MeasureTheory.MeasurePreserving
