/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping

/-!
# Localization, existence, stopping, and local martingale property of the Brownian Itô integral

For a predictable integrand `H` with almost surely finite pathwise square energy on every finite
horizon (`TauCeti.LocallyBrownianIntegrable ℱ P H`) and an almost surely continuous filtered
pre-Brownian motion `B`, this file constructs a strongly predictable Itô integral on the raw
filtration `ℱ` without completeness or right-continuity assumptions on `ℱ`:

* `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral`: closed-level hits of the repaired
  accumulated energy clock localize `H` into `TauCeti.BrownianIntegrable` stages; their `L²` Itô
  integrals agree up to each lifetime by optional stopping and uniqueness, patch via
  `TauCeti.exists_isStronglyProgressive_patch_stoppedProcess`, upgrade to a strongly predictable
  version, and form a native local martingale (`ProbabilityTheory.Locally`) satisfying
  `TauCeti.IsItoIntegral ℱ P B H I`.
* `TauCeti.IsItoIntegral.locally_martingale`: any strongly progressive Itô integral against an
  almost surely continuous filtered pre-Brownian motion is a native local martingale on `ℱ`.
* `TauCeti.IsItoIntegral.stoppedProcess`: stopping any Itô integral at an `ℱ`-stopping time `σ`
  yields an Itô integral of the cutoff integrand `1_{[0, σ]} H`, without moment or adaptedness
  hypotheses on the integral process.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {B H I : ℝ≥0 → Ω → ℝ}

/-- Stopping times tending almost surely to `⊤` exceed any fixed deterministic horizon outside an
event of vanishing probability. -/
private theorem tendsto_measure_lt_of_tendsto_top [IsFiniteMeasure P]
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ_stop : ∀ k, IsStoppingTime ℱ (τ k))
    (hτ_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)) (t : ℝ≥0) :
    Tendsto (fun k ↦ P {ω | τ k ω < t}) atTop (𝓝 0) := by
  have hm (k : ℕ) : MeasurableSet {ω | τ k ω < t} :=
    (hτ_stop k).measurableSpace_le _ ((hτ_stop k).measurableSet_lt' t)
  have hconv := tendsto_lintegral_of_dominated_convergence (μ := P) (fun _ : Ω ↦ (1 : ℝ≥0∞))
    (fun k ↦ measurable_one.indicator (hm k))
    (fun _ ↦ .of_forall fun _ ↦ indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ zero_le))
    (by simp [measure_ne_top P])
    (by
      filter_upwards [hτ_top] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))] with k hk
      have hnot : ω ∉ {ω' | τ k ω' < t} := not_lt_of_ge hk.le
      exact (indicator_of_notMem hnot _).symm)
  simpa only [lintegral_zero, lintegral_indicator_one (hm _)] using hconv

/-- Almost-sure convergence to zero of pathwise square-energy errors implies convergence to zero of
their tail probabilities at every positive threshold. -/
private theorem tendsto_measure_lintegral_ge_of_ae_tendsto [IsFiniteMeasure P]
    (hH : IsStronglyPredictable ℱ H) {t : ℝ≥0}
    {n : ℕ → ℕ} {τg : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (τg m j)] (a m j))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun m ↦ ∫⁻ s,
      ‖Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun m ↦ P {ω | ε ≤ ∫⁻ s,
      ‖Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  let E (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
      ∂Probability.timeMeasure t
  have hE_meas (m : ℕ) : Measurable (E m) :=
    ((((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH).mono
      ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).lintegral_prod_left'
  let f (m : ℕ) (ω : Ω) : ℝ := (min (E m ω) 1).toReal
  have hf_asm (m : ℕ) : AEStronglyMeasurable (f m) P :=
    (((hE_meas m).min measurable_const).ennreal_toReal).aestronglyMeasurable
  have hf_ae : ∀ᵐ ω ∂P, Tendsto (fun m ↦ f m ω) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    have hmin : Tendsto (fun m ↦ min (E m ω) 1) atTop (𝓝 0) := by
      simpa only [min_eq_left (zero_le (a := (1 : ℝ≥0∞)))] using
        hω.min (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmin
  have htm := tendstoInMeasure_of_tendsto_ae hf_asm hf_ae
  let r : ℝ := (min ε 1).toReal
  have hr : 0 < r := ENNReal.toReal_pos (lt_min hε zero_lt_one).ne'
    ((min_le_right ε 1).trans_lt ENNReal.one_lt_top).ne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoInMeasure_iff_norm.1 htm r hr) (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω hω ↦ ?_
  rw [mem_ofPred_eq]
  dsimp only [Pi.zero_apply, f, r, E]
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono ((min_le_right _ 1).trans_lt ENNReal.one_lt_top).ne
    (min_le_min_right 1 hω)

/-- Localization transfer for `IsItoIntegral`: if an almost surely continuous process `I` agrees at
every stage lifetime `τ k` with an Itô integral `U k` of `H_stage k`, and outside one null set
`(t : WithTop ℝ≥0) ≤ τ k ω` forces pathwise agreement of `H_stage k` with `H` on `[0, t]`, then
`I` is an Itô integral of `H`. -/
private theorem isItoIntegral_of_localizing
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ_stop : ∀ k, IsStoppingTime ℱ (τ k))
    (hτ_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    {H_stage U : ℕ → ℝ≥0 → Ω → ℝ}
    (hU : ∀ k, IsItoIntegral ℱ P B (H_stage k) (U k))
    (hlocal : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ k : ℕ, (t : WithTop ℝ≥0) ≤ τ k ω →
      EqOn (fun s ↦ H_stage k s ω) (fun s ↦ H s ω) (Iic t) ∧ I t ω = U k t ω) :
    IsItoIntegral ℱ P B H I := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨hH.isStronglyPredictable, hIcont, fun t ↦ ?_⟩
  have hH₂ : ∀ᵐ ω ∂P, MemLp (fun s ↦ H s ω) 2 (Probability.timeMeasure t) := by
    filter_upwards [hH.ae_memLp] with ω hω
    simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hω t
  obtain ⟨n, τg, a, C, -, hτg_strict, ha, hb, hae_err⟩ :=
    hH.isStronglyPredictable.exists_seq_simpleHolding_ae_tendsto_lintegral_eNorm_sub_sq t hH₂
  have hτg (m : ℕ) : MonotoneOn (τg m) (Iic (n m)) := (hτg_strict m).monotoneOn
  have henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := fun _ hε ↦
    tendsto_measure_lintegral_ge_of_ae_tendsto hH.isStronglyPredictable ha hae_err hε
  refine ⟨n, τg, a, hτg, ha, fun m j hj ↦ ⟨C m, hb m j hj⟩, henergy, ?_⟩
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  let r : ℝ := (min η 1).toReal / 6
  have hmin_pos : 0 < min η 1 := lt_min hη zero_lt_one
  have hmin_fin : min η 1 ≠ ∞ := ((min_le_right η 1).trans_lt ENNReal.one_lt_top).ne
  have hr : 0 < r := div_pos (ENNReal.toReal_pos hmin_pos.ne' hmin_fin) (by norm_num)
  have hr_enn : 0 < ENNReal.ofReal r := ENNReal.ofReal_pos.2 hr
  have htau_lim := tendsto_measure_lt_of_tendsto_top hτ_stop hτ_top t
  obtain ⟨N, hN_le⟩ := (htau_lim.eventually (eventually_le_nhds hr_enn)).exists
  obtain ⟨n', τg', a', hτg', ha', -, henergy', hgains'⟩ := (hU N).exists_approx t
  choose kg gg bg hgg hbg hsum_eq henergy_eq using fun m ↦
    Finance.exists_clipped_grid_simpleGains_sub (hτg m) (hτg' m) (ha m) (ha' m) B t
  let δ : ℝ := r * (ε / 2) ^ 2
  have hδ : 0 < δ := by positivity
  have hδ_div : ENNReal.ofReal (δ / (ε / 2) ^ 2) = ENNReal.ofReal r := by
    rw [mul_div_cancel_right₀ r (pow_ne_zero 2 (half_pos hε).ne')]
  let η_δ : ℝ≥0∞ := min (ENNReal.ofReal δ / 4) 1
  have hη_δ : 0 < η_δ :=
    lt_min (ENNReal.div_pos (ENNReal.ofReal_pos.2 hδ).ne' (by norm_num)) zero_lt_one
  let Z : Set Ω := {ω | ∀ k : ℕ, (t : WithTop ℝ≥0) ≤ τ k ω →
    EqOn (fun s ↦ H_stage k s ω) (fun s ↦ H s ω) (Iic t) ∧ I t ω = U k t ω}
  have hPZ : P Zᶜ = 0 := ae_iff.1 (hlocal t)
  have hg'_ev := (tendstoInMeasure_iff_norm.1 hgains' (ε / 2) (half_pos hε)).eventually
    (eventually_le_nhds hr_enn)
  have he_ev := (henergy η_δ hη_δ).eventually (eventually_le_nhds hr_enn)
  have he'_ev := (henergy' η_δ hη_δ).eventually (eventually_le_nhds hr_enn)
  filter_upwards [hg'_ev, he_ev, he'_ev] with m hm_g' hm_e hm_e'
  let G := Finance.simpleGains (τg m) (n m) (a m) B t
  let G' := Finance.simpleGains (τg' m) (n' m) (a' m) B t
  let S (ω : Ω) := ∑ j ∈ range (kg m), bg m j ω * (B (gg m (j + 1)) ω - B (gg m j) ω)
  let E (ω : Ω) := ∫⁻ s, ‖Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
    ∂Probability.timeMeasure t
  let E' (ω : Ω) := ∫⁻ s, ‖Finance.simpleHolding (τg' m) (n' m) (a' m) s ω - H_stage N s ω‖ₑ ^ 2
    ∂Probability.timeMeasure t
  have hinc₁ : {ω | ε ≤ ‖G ω - I t ω‖} ⊆
      Zᶜ ∪ {ω | τ N ω < t} ∪ {ω | ε / 2 ≤ ‖G' ω - U N t ω‖} ∪ {ω | ε / 2 ≤ |S ω|} := by
    intro ω hω
    by_cases hZ : ω ∈ Z
    · by_cases hτN : τ N ω < t
      · exact Or.inl (Or.inl (Or.inr hτN))
      · obtain ⟨-, hIU⟩ := hZ N (not_lt.1 hτN)
        by_contra hnot
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_le] at hnot
        have hdecomp : G ω - I t ω = S ω + (G' ω - U N t ω) := by
          dsimp only [G, G', S]
          rw [hsum_eq m ω, hIU]
          ring
        have htri : ‖G ω - I t ω‖ ≤ |S ω| + ‖G' ω - U N t ω‖ := by
          rw [hdecomp, ← Real.norm_eq_abs]
          exact norm_add_le _ _
        have hω' : ε ≤ ‖G ω - I t ω‖ := hω
        linarith [hω', hnot.1.2, hnot.2]
    · exact Or.inl (Or.inl (Or.inl hZ))
  have hinc₂ : {ω | δ < Probability.elementaryEnergy (gg m) (bg m) (kg m) ω} ⊆
      Zᶜ ∪ {ω | τ N ω < t} ∪ {ω | η_δ ≤ E ω} ∪ {ω | η_δ ≤ E' ω} := by
    intro ω hω
    by_cases hZ : ω ∈ Z
    · by_cases hτN : τ N ω < t
      · exact Or.inl (Or.inl (Or.inr hτN))
      · obtain ⟨heq_on, -⟩ := hZ N (not_lt.1 hτN)
        by_contra hnot
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_le] at hnot
        have hsm₁ : Measurable (fun s ↦
            ‖Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω‖ₑ ^ 2) :=
          ((((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
            hH.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
              (measurable_id.prodMk measurable_const)).eNorm.pow_const 2
        have hpt : ∀ᵐ s ∂Probability.timeMeasure t,
            ‖Finance.simpleHolding (τg m) (n m) (a m) s ω -
              Finance.simpleHolding (τg' m) (n' m) (a' m) s ω‖ₑ ^ 2 ≤
              2 * (‖Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω‖ₑ ^ 2 +
                ‖Finance.simpleHolding (τg' m) (n' m) (a' m) s ω - H_stage N s ω‖ₑ ^ 2) := by
          filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
          have hHs : H_stage N s ω = H s ω := heq_on hs.2
          rw [hHs]
          simp only [Real.enorm_sq_eq_ofReal_sq]
          rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hsq : (Finance.simpleHolding (τg m) (n m) (a m) s ω -
              Finance.simpleHolding (τg' m) (n' m) (a' m) s ω) ^ 2 =
              ((Finance.simpleHolding (τg m) (n m) (a m) s ω - H s ω) +
                (H s ω - Finance.simpleHolding (τg' m) (n' m) (a' m) s ω)) ^ 2 := by ring
          rw [hsq]
          exact add_sq_le.trans_eq (by ring)
        have hω' : δ < Probability.elementaryEnergy (gg m) (bg m) (kg m) ω := hω
        have hle : ENNReal.ofReal δ ≤ 2 * (E ω + E' ω) := by
          calc ENNReal.ofReal δ
              ≤ ENNReal.ofReal (Probability.elementaryEnergy (gg m) (bg m) (kg m) ω) :=
                ENNReal.ofReal_le_ofReal hω'.le
            _ = _ := henergy_eq m ω
            _ ≤ _ := by
                refine (lintegral_mono_ae hpt).trans ?_
                rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_add_left hsm₁]
        have hfin₁ := hnot.1.2.trans_le (min_le_right _ _)
        have hfin₂ := hnot.2.trans_le (min_le_right _ _)
        have h₁ := (ENNReal.toReal_lt_toReal hfin₁.ne_top (by finiteness)).2
          (hnot.1.2.trans_le (min_le_left _ _))
        have h₂ := (ENNReal.toReal_lt_toReal hfin₂.ne_top (by finiteness)).2
          (hnot.2.trans_le (min_le_left _ _))
        have hle_real := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).2 hle
        rw [ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
          ENNReal.toReal_add hfin₁.ne_top hfin₂.ne_top] at hle_real
        rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofNat] at h₁ h₂
        linarith
    · exact Or.inl (Or.inl (Or.inl hZ))
  have hS_bound : P {ω | ε / 2 ≤ |S ω|} ≤
      ENNReal.ofReal r + P {ω | δ < Probability.elementaryEnergy (gg m) (bg m) (kg m) ω} := by
    rw [← hδ_div]
    exact hB.measure_abs_sum_mul_sub_ge_le (hgg m) (hbg m) (half_pos hε) hδ.le
  have h6r : ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r +
      ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r ≤ η := by
    repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hsum_r : r + r + r + r + r + r = (min η 1).toReal := by
      dsimp only [r]
      ring
    rw [hsum_r, ENNReal.ofReal_toReal hmin_fin]
    exact min_le_left η 1
  calc P {ω | ε ≤ ‖G ω - I t ω‖}
      ≤ P (Zᶜ ∪ {ω | τ N ω < t} ∪ {ω | ε / 2 ≤ ‖G' ω - U N t ω‖} ∪ {ω | ε / 2 ≤ |S ω|}) :=
        measure_mono hinc₁
    _ ≤ P Zᶜ + P {ω | τ N ω < t} + P {ω | ε / 2 ≤ ‖G' ω - U N t ω‖} + P {ω | ε / 2 ≤ |S ω|} := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal r + ENNReal.ofReal r +
        (ENNReal.ofReal r + P (Zᶜ ∪ {ω | τ N ω < t} ∪ {ω | η_δ ≤ E ω} ∪ {ω | η_δ ≤ E' ω})) := by
        rw [hPZ]
        exact add_le_add (add_le_add (add_le_add le_rfl hN_le) hm_g')
          (hS_bound.trans (add_le_add le_rfl (measure_mono hinc₂)))
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r +
        ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r := by
        have htail : P (Zᶜ ∪ {ω | τ N ω < t} ∪ {ω | η_δ ≤ E ω} ∪ {ω | η_δ ≤ E' ω}) ≤
            ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r := by
          calc P (Zᶜ ∪ {ω | τ N ω < t} ∪ {ω | η_δ ≤ E ω} ∪ {ω | η_δ ≤ E' ω})
              ≤ P Zᶜ + P {ω | τ N ω < t} + P {ω | η_δ ≤ E ω} + P {ω | η_δ ≤ E' ω} := by
                refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
                refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
                exact measure_union_le _ _
            _ ≤ ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r := by
                rw [hPZ, zero_add]
                exact add_le_add (add_le_add hN_le hm_e) hm_e'
        calc 0 + ENNReal.ofReal r + ENNReal.ofReal r +
              (ENNReal.ofReal r + P (Zᶜ ∪ {ω | τ N ω < t} ∪ {ω | η_δ ≤ E ω} ∪ {ω | η_δ ≤ E' ω}))
            ≤ 0 + ENNReal.ofReal r + ENNReal.ofReal r +
              (ENNReal.ofReal r + (ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r)) :=
              add_le_add le_rfl (add_le_add le_rfl htail)
          _ = ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r +
              ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r := by
              simp only [zero_add, add_assoc]
    _ ≤ η := h6r

/-- Construct the closed-level energy-localized `L²` stage integrals and a strongly predictable
patched integral for `H ∈ LocallyBrownianIntegrable ℱ P H`. -/
private theorem LocallyBrownianIntegrable.exists_energyLocalizer_patch
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    let τ : ℕ → Ω → WithTop ℝ≥0 := fun k ↦ nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
    let H_stage : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω ↦
      if (t : WithTop ℝ≥0) ≤ τ k ω then nnvolume.finiteEnergyCutoff H t ω else 0
    ∃ (I : ℝ≥0 → Ω → ℝ) (U : ℕ → ℝ≥0 → Ω → ℝ),
      IsItoIntegral ℱ P B H I ∧
      IsStronglyPredictable ℱ I ∧
      Locally (fun V ↦ Martingale V ℱ P) ℱ I P ∧
      (∀ k, BrownianIntegrable ℱ P (H_stage k)) ∧
      (∀ k, IsItoIntegral ℱ P B (H_stage k) (U k)) ∧
      (∀ k, IsStronglyPredictable ℱ (U k)) ∧
      (∀ k, stoppedProcess I (τ k) ≡ᵐ[P] U k) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  intro τ H_stage
  have hτ : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hH_stage (k : ℕ) : BrownianIntegrable ℱ P (H_stage k) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  choose U hU_ito hU_pred hU_mart using fun k ↦ (hH_stage k).exists_isItoIntegral hB hcont
  have hcompat (k l : ℕ) (hkl : k ≤ l) : stoppedProcess (U l) (τ k) ≡ᵐ[P] U k := by
    have hstop_ito := (hU_ito l).stoppedProcess_of_brownianIntegrable hB (hH_stage l)
      (hU_pred l).isStronglyProgressive.stronglyAdapted (hτ.isStoppingTime k)
    have hstage_eq :
        (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ τ k ω then H_stage l t ω else 0) =
          H_stage k := by
      ext t ω
      have hτ_le : τ k ω ≤ τ l ω :=
        nnvolume.monotone_energyLocalizer H ω (add_le_add (Nat.cast_le.2 hkl) le_rfl)
      dsimp only [H_stage]
      by_cases ht : (t : WithTop ℝ≥0) ≤ τ k ω
      · rw [ite_eq_left ht, ite_eq_left (ht.trans hτ_le), ite_eq_left ht]
      · rw [ite_eq_right ht, ite_eq_right ht]
    rw [hstage_eq] at hstop_ito
    exact hstop_ito.indist hB (hU_ito k)
  obtain ⟨I₀, hI₀_prog, hI₀_cont, hI₀_stop⟩ :=
    exists_isStronglyProgressive_patch_stoppedProcess hτ.tendsto_top
      (fun k ↦ (hU_pred k).isStronglyProgressive) (fun k ↦ (hU_ito k).ae_continuous) hcompat
  obtain ⟨I, hI_pred, hI_cont, hII₀⟩ :=
    hI₀_prog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_continuous hI₀_cont
  have hI_stop (k : ℕ) : stoppedProcess I (τ k) ≡ᵐ[P] U k :=
    (Indistinguishable.stoppedProcess hII₀ (τ k)).trans (hI₀_stop k)
  have hI_loc : Locally (fun V ↦ Martingale V ℱ P) ℱ I P := by
    refine hI_pred.isStronglyProgressive.locally_martingale_of_ae_stopped_eq hτ hU_mart fun k t ↦ ?_
    have hpos_univ : {ω : Ω | (⊥ : WithTop ℝ≥0) < τ k ω} = Set.univ :=
      eq_univ_of_forall fun ω ↦ by
        rw [mem_ofPred_eq, ← WithTop.coe_bot, bot_eq_zero, WithTop.coe_zero]
        exact nnvolume.energyLocalizer_pos H (by positivity : (0 : ℝ≥0) < (k : ℝ≥0) + 1) ω
    simpa only [hpos_univ, indicator_univ] using ((hI_stop k).ae_eq_eval t).symm
  have hI_ito : IsItoIntegral ℱ P B H I := by
    refine isItoIntegral_of_localizing hB hH hI_cont hτ.isStoppingTime hτ.tendsto_top hU_ito
      fun t ↦ ?_
    filter_upwards [hH.ae_accumulatedEnergy_lt_top,
      ae_all_iff.2 fun k ↦ (hI_stop k).ae_eq_eval t] with ω hfin hstop_eq k htk
    refine ⟨fun s hs ↦ ?_, ?_⟩
    · have hsk : (s : WithTop ℝ≥0) ≤ τ k ω := (WithTop.coe_le_coe.2 (mem_Iic.1 hs)).trans htk
      dsimp only [H_stage]
      rw [ite_eq_left hsk]
      exact nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
    · have hst : stoppedProcess I (τ k) t ω = I t ω := stoppedProcess_eq_of_le htk
      exact hst.symm.trans (hstop_eq k)
  exact ⟨I, U, hI_ito, hI_pred, hI_loc, hH_stage, hU_ito, hU_pred, hI_stop⟩

/-- **Existence of the local Brownian Itô integral.** When `B` has almost surely continuous paths,
every `H` in `LocallyBrownianIntegrable ℱ P H` admits a strongly predictable Itô integral `I` on the
raw filtration `ℱ` that is a native local martingale on `ℱ`. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P B H I ∧ IsStronglyPredictable ℱ I ∧
      Locally (fun V ↦ Martingale V ℱ P) ℱ I P := by
  obtain ⟨I, -, hI_ito, hI_pred, hI_loc, -⟩ := hH.exists_energyLocalizer_patch hB hcont
  exact ⟨I, hI_ito, hI_pred, hI_loc⟩

namespace IsItoIntegral

/-- Any strongly progressive Itô integral against an almost surely continuous filtered pre-Brownian
motion is a native local martingale on the raw filtration `ℱ`. -/
theorem locally_martingale
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω))
    (hI : IsItoIntegral ℱ P B H I)
    (hProg : IsStronglyProgressive ℱ I) :
    Locally (fun V ↦ Martingale V ℱ P) ℱ I P := by
  obtain ⟨J, hJ_ito, -, hJ_loc⟩ := hI.locallyBrownianIntegrable.exists_isItoIntegral hB hcont
  exact hProg.locally_martingale_of_indist hJ_loc (hJ_ito.indist hB hI)

/-- **Optional stopping for the Brownian Itô integral.** Against an almost surely continuous
filtered pre-Brownian motion, stopping any Itô integral `I` of `H` at an `ℱ`-stopping time `σ`
yields an Itô integral of the cutoff integrand `1_{[0, σ]} H`. Neither finite expected energy of `H`
nor adaptedness of `I` is assumed. -/
theorem stoppedProcess
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω))
    (hI : IsItoIntegral ℱ P B H I)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P B (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I σ) := by
  let hH := hI.locallyBrownianIntegrable
  obtain ⟨J, U, hJ_ito, -, -, hH_stage, hU_ito, hU_pred, hJ_stop⟩ :=
    hH.exists_energyLocalizer_patch hB hcont
  let τ : ℕ → Ω → WithTop ℝ≥0 := fun k ↦ nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hτ : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hI_stop (k : ℕ) : MeasureTheory.stoppedProcess I (τ k) ≡ᵐ[P] U k :=
    (Indistinguishable.stoppedProcess (hI.indist hB hJ_ito) (τ k)).trans (hJ_stop k)
  let Hσ_stage : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω ↦
    if (t : WithTop ℝ≥0) ≤ σ ω then
      (if (t : WithTop ℝ≥0) ≤ τ k ω then nnvolume.finiteEnergyCutoff H t ω else 0) else 0
  let V : ℕ → ℝ≥0 → Ω → ℝ := fun k ↦ MeasureTheory.stoppedProcess (U k) σ
  have hV_ito (k : ℕ) : IsItoIntegral ℱ P B (Hσ_stage k) (V k) :=
    (hU_ito k).stoppedProcess_of_brownianIntegrable hB (hH_stage k)
      (hU_pred k).isStronglyProgressive.stronglyAdapted hσ
  have hV_stop (k : ℕ) :
      MeasureTheory.stoppedProcess (MeasureTheory.stoppedProcess I σ) (τ k) ≡ᵐ[P] V k := by
    have hcomm : MeasureTheory.stoppedProcess (MeasureTheory.stoppedProcess I σ) (τ k) =
        MeasureTheory.stoppedProcess (MeasureTheory.stoppedProcess I (τ k)) σ := by
      rw [stoppedProcess_stoppedProcess, inf_comm, ← stoppedProcess_stoppedProcess]
    rw [hcomm]
    exact Indistinguishable.stoppedProcess (hI_stop k) σ
  have hstop_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ MeasureTheory.stoppedProcess I σ t ω) := by
    filter_upwards [hI.ae_continuous] with ω hω
    exact hω.stoppedProcess
  refine isItoIntegral_of_localizing hB (hH.ite_le hσ) hstop_cont hτ.isStoppingTime hτ.tendsto_top
    hV_ito fun t ↦ ?_
  filter_upwards [hH.ae_accumulatedEnergy_lt_top,
    ae_all_iff.2 fun k ↦ (hV_stop k).ae_eq_eval t] with ω hfin hstop_eq k htk
  refine ⟨fun s hs ↦ ?_, ?_⟩
  · have hsk : (s : WithTop ℝ≥0) ≤ τ k ω := (WithTop.coe_le_coe.2 (mem_Iic.1 hs)).trans htk
    have hcut : nnvolume.finiteEnergyCutoff H s ω = H s ω :=
      nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
    dsimp only [Hσ_stage]
    rw [ite_eq_left hsk, hcut]
  · have hst : MeasureTheory.stoppedProcess (MeasureTheory.stoppedProcess I σ) (τ k) t ω =
        MeasureTheory.stoppedProcess I σ t ω := stoppedProcess_eq_of_le htk
    exact hst.symm.trans (hstop_eq k)

end IsItoIntegral

end TauCeti
