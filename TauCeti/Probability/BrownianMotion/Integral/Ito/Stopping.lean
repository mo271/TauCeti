/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Process.Stopping

/-!
# Optional stopping of L² Brownian Itô integrals

Stopping a strongly adapted Itô integral `I` of a Brownian-integrable process `H` at an arbitrary
stopping time `τ` yields an Itô integral of the cutoff integrand `1_{[0, τ]} H`
(`TauCeti.IsItoIntegral.stoppedProcess_of_brownianIntegrable`). No completeness, right-continuity
of the filtration, or path continuity of the integrator `B` is required.

The proof works in three stages at each deterministic horizon `t`:
1. Subdivide each elementary interval `(s, u]` along the finite `2⁻ᵏ` mesh clipped at `t` to
   identify `l2Integral` of `1_{[0, dyadicCeilTime k τ]} 1_{(s, u]} ξ` with the `dyadicCeilTime k τ`
   stopped increment `ξ * (B_{u ∧ t ∧ σ_k} - B_{s ∧ t ∧ σ_k})`.
2. Sum over finite grids and pass to the `L²` limit of bounded predictable simple strategies at a
   fixed dyadic level `k`, using the finiteness of the clipped `2⁻ᵏ` range to pass `L²(P)`
   convergence through `stoppedProcess · (dyadicCeilTime k τ) t`.
3. Pass `k → ∞` using dyadic martingale stopping
   (`Martingale.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime`) on the integral side and dominated
   convergence on the integrand side.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {B H I : ℝ≥0 → Ω → ℝ}

private theorem exists_dyadicGrid_index (t : ℝ≥0) (k : ℕ) (w : WithTop ℝ≥0) :
    let M := ⌊t * 2 ^ k⌋₊ + 1
    let g : ℕ → ℝ≥0 := fun j ↦ min t ((j : ℝ≥0) / 2 ^ k)
    ∃ j₀ ≤ M, (min (t : WithTop ℝ≥0) (dyadicCeilTime k w)).untopA = g j₀ ∧
      (∀ j < j₀, ¬ dyadicCeilTime k w ≤ g j) ∧
      (∀ j, j₀ ≤ j → j < M → g j < g (j + 1) → dyadicCeilTime k w ≤ g j) := by
  intro M g
  have hgM : g M = t := by
    dsimp only [M, g]
    refine min_eq_left ?_
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast (Nat.lt_floor_add_one (t * 2 ^ k)).le
  cases w with
  | top =>
    refine ⟨M, le_rfl, ?_, fun j _ ↦ ?_, fun j hj₁ hj₂ ↦ (not_lt_of_ge hj₁ hj₂).elim⟩
    · rw [dyadicCeilTime_top, min_top_right,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, hgM]
    · rw [dyadicCeilTime_top]
      exact WithTop.not_top_le_coe _
  | coe r =>
    let m := ⌈r * 2 ^ k⌉₊
    refine ⟨min M m, min_le_left M m, ?_, fun j hj ↦ ?_, fun j hj₁ hj₂ hlt ↦ ?_⟩
    · rw [dyadicCeilTime_coe, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      rcases le_or_gt m M with hmM | hMm
      · rw [min_eq_right hmM]
      · have ht_le : t ≤ (m : ℝ≥0) / 2 ^ k := by
          calc t = g M := hgM.symm
            _ ≤ (M : ℝ≥0) / 2 ^ k := min_le_right _ _
            _ ≤ (m : ℝ≥0) / 2 ^ k :=
              div_le_div_of_nonneg_right (Nat.cast_le.2 hMm.le) (by positivity)
        rw [min_eq_left ht_le, min_eq_left hMm.le, hgM]
    · rw [dyadicCeilTime_coe, WithTop.coe_le_coe, not_le]
      have hjm : j < m := (lt_min_iff.1 hj).2
      calc g j ≤ (j : ℝ≥0) / 2 ^ k := min_le_right _ _
        _ < (m : ℝ≥0) / 2 ^ k :=
          div_lt_div_of_pos_right (Nat.cast_lt.2 hjm) (by positivity)
    · rw [dyadicCeilTime_coe, WithTop.coe_le_coe]
      have hmM : m ≤ M := by
        by_contra! hMm
        rw [min_eq_left hMm.le] at hj₁
        exact not_lt_of_ge hj₁ hj₂
      rw [min_eq_right hmM] at hj₁
      have hgj_lt_t : (j : ℝ≥0) / 2 ^ k < t := by
        by_contra! hge
        have h1 : g j = t := min_eq_left hge
        have h2 : g (j + 1) ≤ t := min_le_left _ _
        exact not_lt_of_ge (h2.trans_eq h1.symm) hlt
      have hgj_eq : g j = (j : ℝ≥0) / 2 ^ k := min_eq_right hgj_lt_t.le
      rw [hgj_eq]
      exact div_le_div_of_nonneg_right (Nat.cast_le.2 hj₁) (by positivity)

/-- Subdividing a single predictable interval `(s, u]` along the `2⁻ᵏ` mesh identifies `l2Integral`
of the `dyadicCeilTime k τ`-cutoff holding with the stopped Brownian increment. -/
private theorem coeFn_l2Integral_ite_dyadicCeilTime_indicator_Ioc
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {s u : ℝ≥0} (hsu : s ≤ u) {ξ : Ω → ℝ} {C : ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∀ ω, ‖ξ ω‖ ≤ C) (t : ℝ≥0) (k : ℕ) :
    letI := (hB.hasLaw_eval 0).isProbabilityMeasure
    ∃ f : Lp ℝ 2 (ℱ.predictableMeasure P t),
      (f : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P t]
        (fun p ↦ if (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) then
          (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1 else 0) ∧
      (hB.l2Integral t f : Ω → ℝ) =ᵐ[P] fun ω ↦
        ξ ω * (B (min u (min (t : WithTop ℝ≥0) (dyadicCeilTime k (τ ω))).untopA) ω -
          B (min s (min (t : WithTop ℝ≥0) (dyadicCeilTime k (τ ω))).untopA) ω) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
  have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
  let M := ⌊t * 2 ^ k⌋₊ + 1
  let g : ℕ → ℝ≥0 := fun j ↦ min t ((j : ℝ≥0) / 2 ^ k)
  have hg0 : g 0 = 0 := by simp [g]
  have hgM : g M = t := by
    dsimp only [M, g]
    refine min_eq_left ?_
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast (Nat.lt_floor_add_one (t * 2 ^ k)).le
  have hg_mono : Monotone g := fun j₁ j₂ hj ↦
    min_le_min_left t (div_le_div_of_nonneg_right (Nat.cast_le.2 hj) (by positivity))
  let u₀ := min s t
  let v₀ := min u t
  have huv : u₀ ≤ v₀ := min_le_min_right t hsu
  have hvt : v₀ ≤ t := min_le_right _ _
  let d : ℕ → ℝ≥0 := fun j ↦ max u₀ (min v₀ (g j))
  let b : ℕ → Ω → ℝ := fun j ω ↦
    if d j < d (j + 1) then (if ¬ σ ω ≤ g j then ξ ω else 0) else 0
  have hd_mono : MonotoneOn d (Iic M) := fun j₁ _ j₂ _ hj ↦
    max_le_max_left u₀ (min_le_min_left v₀ (hg_mono hj))
  have hb_meas (j : ℕ) (_ : j < M) : StronglyMeasurable[ℱ (d j)] (b j) := by
    by_cases hlt : d j < d (j + 1)
    · have hvg : g j < v₀ := by
        by_contra! hge
        have h1 : min v₀ (g j) = v₀ := min_eq_left hge
        have h2 : min v₀ (g (j + 1)) = v₀ := min_eq_left (hge.trans (hg_mono (Nat.le_succ j)))
        simp [d, h1, h2] at hlt
      have hgj_le : g j ≤ d j := (le_min hvg.le le_rfl).trans (le_max_right _ _)
      have hs_lt_t : s < t := by
        by_contra! hge
        have hu_eq : u₀ = t := min_eq_right hge
        have hd1 : d (j + 1) ≤ t := max_le hu_eq.le ((min_le_left _ _).trans hvt)
        exact not_lt_of_ge (hd1.trans (hu_eq ▸ le_max_left _ _)) hlt
      have hs_le : s ≤ d j := min_eq_left hs_lt_t.le ▸ le_max_left u₀ _
      have hset : MeasurableSet[ℱ (d j)] {ω | ¬ σ ω ≤ g j} :=
        (ℱ.mono hgj_le _ (hσ (g j))).compl
      have hite : StronglyMeasurable[ℱ (d j)]
          (fun ω ↦ if ¬ σ ω ≤ g j then ξ ω else 0) := by
        convert (hξ.mono (ℱ.mono hs_le)).indicator hset using 1
        ext ω
        by_cases hω : ¬ σ ω ≤ g j
        · rw [ite_eq_left hω, indicator_of_mem hω]
        · rw [ite_eq_right hω, indicator_of_notMem hω]
      simpa only [b, hlt, ↓reduceIte] using hite
    · simpa only [b, hlt, ↓reduceIte] using
        (stronglyMeasurable_const : StronglyMeasurable[ℱ (d j)] (fun _ : Ω ↦ (0 : ℝ)))
  have hb₂ (j : ℕ) (hj : j < M) : MemLp (b j) 2 P :=
    MemLp.of_bound ((hb_meas j hj).mono (ℱ.le _)).aestronglyMeasurable (max C 0)
      (.of_forall fun ω ↦ by
        dsimp only [b]
        by_cases h1 : d j < d (j + 1)
        · rw [ite_eq_left h1]
          by_cases h2 : ¬ σ ω ≤ g j
          · rw [ite_eq_left h2]
            exact (hb ω).trans (le_max_left _ _)
          · rw [ite_eq_right h2, norm_zero]
            exact le_max_right C 0
        · rw [ite_eq_right h1, norm_zero]
          exact le_max_right C 0)
  refine ⟨(Finance.memLp_simpleHolding_predictableMeasure hb_meas hb₂ t).toLp
    (Function.uncurry (Finance.simpleHolding d M b)), ?_, ?_⟩
  · refine ((Finance.memLp_simpleHolding_predictableMeasure hb_meas hb₂ t).coeFn_toLp).trans ?_
    have hpred₁ : Measurable[ℱ.predictable] (Function.uncurry (Finance.simpleHolding d M b)) :=
      (Finance.isStronglyPredictable_simpleHolding hb_meas).measurable
    have hpred₂ : Measurable[ℱ.predictable]
        (fun p : ℝ≥0 × Ω ↦ if (p.1 : WithTop ℝ≥0) ≤ σ p.2 then
          (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1 else 0) :=
      ((isStronglyPredictable_indicator_Ioc hξ).ite
        hσ.measurableSet_predictable_ge stronglyMeasurable_const).measurable
    rw [ℱ.ae_eq_predictableMeasure_iff P hpred₁ hpred₂ t]
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := Probability.timeMeasure t)
      (ν := P)).ae (Probability.ae_mem_Ioc_timeMeasure t)] with p hp
    obtain ⟨j₀, -, hq_eq, hj_lt, hj_ge⟩ := exists_dyadicGrid_index t k (τ p.2)
    have hd0 : d 0 = u₀ := by simp [d, hg0]
    have hdM : d M = v₀ := by simp [d, hgM, min_eq_left hvt, max_eq_right huv]
    have hIoc_eq : p.1 ∈ Ioc u₀ v₀ ↔ p.1 ∈ Ioc s u := by
      dsimp only [u₀, v₀]
      simp only [Set.mem_Ioc, min_lt_iff, le_min_iff]
      have hp2 : p.1 ≤ t := hp.2
      constructor
      · rintro ⟨hs | ht, hu, _⟩
        · exact ⟨hs, hu⟩
        · exact (not_lt_of_ge hp2 ht).elim
      · exact fun ⟨hs, hu⟩ ↦ ⟨Or.inl hs, hu, hp2⟩
    by_cases hmem : p.1 ∈ Ioc u₀ v₀
    · have hmem' : p.1 ∈ Ioc (d 0) (d M) := by rwa [hd0, hdM]
      obtain ⟨j, hjM, hjp⟩ := exists_lt_mem_Ioc_of_mem_Ioc hmem'
      have hlt : d j < d (j + 1) := hjp.1.trans_le hjp.2
      rw [Function.uncurry_apply_pair, Finance.simpleHolding_of_mem_Ioc hd_mono hjM hjp]
      simp only [b, hlt, ↓reduceIte, hIoc_eq.1 hmem, indicator_of_mem]
      rcases lt_or_ge j j₀ with hjj₀ | hjj₀
      · have hnle : ¬ σ p.2 ≤ g j := hj_lt j hjj₀
        have hd_le_g : d (j + 1) ≤ g (j + 1) := by
          have hu_lt : u₀ < d (j + 1) := (le_max_left u₀ _).trans_lt hlt
          have hmin : u₀ ≤ min v₀ (g (j + 1)) := by
            by_contra! hgt
            simp [d, max_eq_left hgt.le] at hu_lt
          calc d (j + 1) = min v₀ (g (j + 1)) := max_eq_right hmin
            _ ≤ g (j + 1) := min_le_right _ _
        have hs_le_q : p.1 ≤ g j₀ :=
          hjp.2.trans (hd_le_g.trans (hg_mono (Nat.succ_le_of_lt hjj₀)))
        have hs_le_σ : (p.1 : WithTop ℝ≥0) ≤ σ p.2 := by
          have hfin : min (t : WithTop ℝ≥0) (σ p.2) ≠ ⊤ :=
            ne_of_lt ((min_le_left _ _).trans_lt (WithTop.coe_lt_top t))
          have hq_le : ((min (t : WithTop ℝ≥0) (σ p.2)).untopA : WithTop ℝ≥0) ≤ σ p.2 := by
            rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
            exact min_le_right _ _
          exact (WithTop.coe_le_coe.2 (hs_le_q.trans_eq hq_eq.symm)).trans hq_le
        rw [ite_eq_left hnle, ite_eq_left hs_le_σ]
      · have hgj_lt : g j < g (j + 1) := by
          by_contra! hge
          exact not_lt_of_ge (max_le_max_left u₀ (min_le_min_left v₀ hge)) hlt
        have hle_σ : σ p.2 ≤ g j := hj_ge j hjj₀ hjM hgj_lt
        have hgj_lt_v : g j < v₀ := by
          by_contra! hge
          have h1 : min v₀ (g j) = v₀ := min_eq_left hge
          have h2 : min v₀ (g (j + 1)) = v₀ :=
            min_eq_left (hge.trans (hg_mono (Nat.le_succ j)))
          simp [d, h1, h2] at hlt
        have hgj_lt_s : g j < p.1 :=
          ((le_min hgj_lt_v.le le_rfl).trans (le_max_right _ _)).trans_lt hjp.1
        have hnot_s : ¬ (p.1 : WithTop ℝ≥0) ≤ σ p.2 :=
          not_le_of_gt (hle_σ.trans_lt (WithTop.coe_lt_coe.2 hgj_lt_s))
        rw [ite_eq_right (not_not.2 hle_σ), ite_eq_right hnot_s]
    · have hmem' : p.1 ∉ Ioc (d 0) (d M) := by rwa [hd0, hdM]
      rw [Function.uncurry_apply_pair, Finance.simpleHolding_of_notMem_Ioc hd_mono hmem',
        indicator_of_notMem (hIoc_eq.not.1 hmem), ite_self]
  · filter_upwards [hB.coeFn_l2Integral_simpleHolding hd_mono hb_meas hb₂ t] with ω hω
    rw [hω, Finance.simpleGains_def]
    obtain ⟨j₀, hj₀M, hq_eq, hj_lt, hj_ge⟩ := exists_dyadicGrid_index t k (τ ω)
    let q := (min (t : WithTop ℝ≥0) (σ ω)).untopA
    have hdt (j : ℕ) : min (d j) t = d j :=
      min_eq_left (max_le (min_le_right _ _) ((min_le_left _ _).trans hvt))
    have hsplit :
        (∑ j ∈ range M, b j ω * (B (min (d (j + 1)) t) ω - B (min (d j) t) ω)) =
          ∑ j ∈ range j₀, ξ ω * (B (d (j + 1)) ω - B (d j) ω) := by
      rw [← sum_range_add_sum_Ico _ hj₀M]
      have htail_zero :
          (∑ j ∈ Ico j₀ M, b j ω * (B (min (d (j + 1)) t) ω - B (min (d j) t) ω)) = 0 := by
        refine sum_eq_zero fun j hj ↦ ?_
        obtain ⟨hj₁, hj₂⟩ := mem_Ico.1 hj
        by_cases hlt : d j < d (j + 1)
        · have hgj_lt : g j < g (j + 1) := by
            by_contra! hge
            exact not_lt_of_ge (max_le_max_left u₀ (min_le_min_left v₀ hge)) hlt
          have hσ_le : σ ω ≤ g j := hj_ge j hj₁ hj₂ hgj_lt
          dsimp only [b]
          rw [ite_eq_left hlt, ite_eq_right (not_not.2 hσ_le), zero_mul]
        · dsimp only [b]
          rw [ite_eq_right hlt, zero_mul]
      rw [htail_zero, add_zero]
      refine sum_congr rfl fun j hj ↦ ?_
      have hjM : j < M := (mem_range.1 hj).trans_le hj₀M
      rw [hdt (j + 1), hdt j]
      by_cases hlt : d j < d (j + 1)
      · have hnσ_le : ¬ σ ω ≤ g j := hj_lt j (mem_range.1 hj)
        dsimp only [b]
        rw [ite_eq_left hlt, ite_eq_left hnσ_le]
      · have heq_d : d (j + 1) = d j :=
          le_antisymm (le_of_not_gt hlt) (hd_mono hjM.le hjM (Nat.le_succ j))
        simp only [heq_d, sub_self, mul_zero]
    rw [hsplit, ← mul_sum, sum_range_sub (fun j ↦ B (d j) ω) j₀]
    have hd0 : d 0 = u₀ := by simp [d, hg0]
    have hdj0 : d j₀ = max u₀ (min v₀ q) := by
      dsimp only [d, q, σ, g]
      rw [hq_eq]
    have hfin : min (t : WithTop ℝ≥0) (σ ω) ≠ ⊤ :=
      ne_of_lt ((min_le_left _ _).trans_lt (WithTop.coe_lt_top t))
    have hqt : q ≤ t := by
      rw [← WithTop.coe_le_coe]
      dsimp only [q]
      rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
      exact min_le_left _ _
    have hu_min : min u₀ q = min s q := by simp only [u₀, min_assoc, min_eq_right hqt]
    have hv_min : min v₀ q = min u q := by simp only [v₀, min_assoc, min_eq_right hqt]
    rw [hd0, hdj0, sub_max_min_eq (X := fun r ↦ B r ω) huv, hu_min, hv_min]

/-- On any finite monotone grid with bounded adapted heights, `l2Integral` of the
`dyadicCeilTime k τ`-cutoff holding agrees almost everywhere with `stoppedProcess` of its
elementary gains. -/
private theorem coeFn_l2Integral_ite_dyadicCeilTime_simpleHolding
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {n : ℕ} {τg : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ} {C : ℝ}
    (hτg : MonotoneOn τg (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τg j)] (a j))
    (hb : ∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) (t : ℝ≥0) (k : ℕ) :
    letI := (hB.hasLaw_eval 0).isProbabilityMeasure
    have ha₂ : ∀ j < n, MemLp (a j) 2 P := fun j hj ↦
      MemLp.of_bound ((ha j hj).mono (ℱ.le _)).aestronglyMeasurable C (.of_forall (hb j hj))
    have hBkm : BrownianIntegrable ℱ P (fun s ω ↦
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then
          Finance.simpleHolding τg n a s ω else 0) :=
      BrownianIntegrable.ite_le
        ⟨Finance.isStronglyPredictable_simpleHolding ha, fun T ↦ by
          simpa only [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def,
            ← ℱ.memLp_predictableMeasure_iff P
              (Finance.isStronglyPredictable_simpleHolding ha) T 2] using
            Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T⟩
        (hτ.dyadicCeilTime k)
    hB.l2Integral t ((hBkm.memLp_predictableMeasure t).toLp
      (Function.uncurry fun s ω ↦
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then
          Finance.simpleHolding τg n a s ω else 0)) =ᵐ[P]
      stoppedProcess (Finance.simpleGains τg n a B) (fun ω ↦ dyadicCeilTime k (τ ω)) t := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  extract_lets _ hBkm
  choose f_term hf_term_ae hf_term_int using fun i : Fin n ↦
    coeFn_l2Integral_ite_dyadicCeilTime_indicator_Ioc hB hτ
      (hτg i.2.le i.2 (Nat.le_succ i)) (ha i i.2) (hb i i.2) t k
  have hsum_f : (hBkm.memLp_predictableMeasure t).toLp _ = ∑ i : Fin n, f_term i := by
    apply Lp.ext
    filter_upwards [(hBkm.memLp_predictableMeasure t).coeFn_toLp,
      Lp.coeFn_finsetSum univ f_term,
      (ae_ball_iff (Finset.countable_toSet _)).2 fun i _ ↦ hf_term_ae i] with p hp hsum hall
    rw [hp, hsum, Finset.sum_apply, Function.uncurry_apply_pair]
    simp only [Finance.simpleHolding_def]
    rw [← Fin.sum_univ_eq_sum_range]
    by_cases hs : (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2)
    · rw [ite_eq_left hs]
      exact sum_congr rfl fun i _ ↦ by
        have hi := hall i (mem_univ i)
        rw [ite_eq_left hs] at hi
        exact hi.symm
    · rw [ite_eq_right hs]
      symm
      exact sum_eq_zero fun i _ ↦ by
        have hi := hall i (mem_univ i)
        rw [ite_eq_right hs] at hi
        exact hi
  rw [hsum_f, map_sum]
  filter_upwards [Lp.coeFn_finsetSum univ (fun i ↦ hB.l2Integral t (f_term i)),
    (ae_ball_iff (Finset.countable_toSet _)).2 fun i _ ↦ hf_term_int i] with ω hsum hall
  rw [hsum, Finset.sum_apply]
  simp only [MeasureTheory.stoppedProcess, Finance.simpleGains_def]
  rw [← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun i _ ↦ hall i (mem_univ i)

private theorem eLpNorm_l2Integral_sub (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (t : ℝ≥0) {H₁ H₂ : ℝ≥0 → Ω → ℝ}
    (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂) :
    letI := (hB.hasLaw_eval 0).isProbabilityMeasure
    eLpNorm
      (⇑(hB.l2Integral t ((hH₁.memLp_predictableMeasure t).toLp (Function.uncurry H₁))) -
        ⇑(hB.l2Integral t ((hH₂.memLp_predictableMeasure t).toLp (Function.uncurry H₂)))) 2 P =
      eLpNorm (Function.uncurry H₁ - Function.uncurry H₂) 2
        ((Probability.timeMeasure t).prod P) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hsub_ae := ((hH₁.memLp_predictableMeasure t).coeFn_toLp).sub
    ((hH₂.memLp_predictableMeasure t).coeFn_toLp)
  rw [← Lp.edist_def, (hB.l2Integral t).isometry.edist_eq, Lp.edist_def,
    eLpNorm_congr_ae hsub_ae, ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod (hH₁.isStronglyPredictable.sub
      hH₂.isStronglyPredictable)]

namespace IsItoIntegral

/-- Stopping a strongly adapted Itô integral of a Brownian-integrable process `H` at any stopping
time `τ` yields an Itô integral of the cutoff integrand `1_{[0, τ]} H`. -/
theorem stoppedProcess_of_brownianIntegrable
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P B H I)
    (hAdapt : StronglyAdapted ℱ I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P B (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  let Hτ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0
  have hHτ : BrownianIntegrable ℱ P Hτ := hH.ite_le hτ
  have hstop_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ stoppedProcess I τ t ω) := by
    filter_upwards [hI.ae_continuous] with ω hω
    exact hω.stoppedProcess
  refine (hHτ.isItoIntegral_iff_ae_eq_l2Integral hB).2 ⟨hstop_cont, fun t ↦ ?_⟩
  obtain ⟨n, τg, a, C, -, hτg_strict, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hτg (m : ℕ) : MonotoneOn (τg m) (Iic (n m)) := (hτg_strict m).monotoneOn
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  let σ (k : ℕ) (ω : Ω) : WithTop ℝ≥0 := dyadicCeilTime k (τ ω)
  have hσ (k : ℕ) : IsStoppingTime ℱ (σ k) := hτ.dyadicCeilTime k
  -- Pass `m → ∞` at each fixed dyadic level `k`, using finiteness of the clipped `2⁻ᵏ` range.
  have hstep_dyadic (k : ℕ) :
      let Hk : ℝ≥0 → Ω → ℝ := fun s ω ↦ if (s : WithTop ℝ≥0) ≤ σ k ω then H s ω else 0
      stoppedProcess I (σ k) t =ᵐ[P]
        hB.l2Integral t (((hH.ite_le (hσ k)).memLp_predictableMeasure t).toLp
          (Function.uncurry Hk)) := by
    intro Hk
    let M := ⌊t * 2 ^ k⌋₊ + 1
    let g : ℕ → ℝ≥0 := fun j ↦ min t ((j : ℝ≥0) / 2 ^ k)
    let G (m : ℕ) := Finance.simpleGains (τg m) (n m) (a m) B
    have hG_adapt (m : ℕ) : StronglyAdapted ℱ (G m) :=
      Finance.stronglyAdapted_simpleGains (hτg m) (ha m) hB.adapted.stronglyAdapted
    have hGI_lim (r : ℝ≥0) : Tendsto (fun m ↦ eLpNorm (G m r - I r) 2 P) atTop (𝓝 0) := by
      refine (hB.tendsto_eLpNorm_simpleGains_sub_l2Integral hH hτg ha ha₂ (herr r)).congr
        fun m ↦ eLpNorm_congr_ae ?_
      exact EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hB hH r).symm
    have hstop_lim : Tendsto
        (fun m ↦ eLpNorm (stoppedProcess (G m) (σ k) t - stoppedProcess I (σ k) t) 2 P)
        atTop (𝓝 0) := by
      have hsum_lim : Tendsto
          (fun m ↦ ∑ j ∈ range (M + 1), eLpNorm (G m (g j) - I (g j)) 2 P)
          atTop (𝓝 0) := by
        simpa using tendsto_finsetSum (range (M + 1)) fun j _ ↦ hGI_lim (g j)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_lim
        (fun _ ↦ zero_le) fun m ↦ ?_
      have hadapt_diff : AEStronglyMeasurable
          (stoppedProcess (G m) (σ k) t - stoppedProcess I (σ k) t) P := by
        have hsm₁ := (((hG_adapt m).stoppedProcess_of_countable_range (hσ k)
          (countable_range_dyadicCeilTime τ k)) t).mono (ℱ.le t)
        have hsm₂ := ((hAdapt.stoppedProcess_of_countable_range (hσ k)
          (countable_range_dyadicCeilTime τ k)) t).mono (ℱ.le t)
        exact (hsm₁.sub hsm₂).aestronglyMeasurable
      have hdom :
          eLpNorm (stoppedProcess (G m) (σ k) t - stoppedProcess I (σ k) t) 2 P ≤
            eLpNorm (∑ j ∈ range (M + 1), fun ω ↦ ‖(G m (g j) - I (g j)) ω‖) 2 P := by
        refine eLpNorm_mono_eNorm hadapt_diff fun ω ↦ ?_
        obtain ⟨j₀, hj₀M, hq_eq, -, -⟩ := exists_dyadicGrid_index t k (τ ω)
        dsimp only [Pi.sub_apply, MeasureTheory.stoppedProcess, σ, M, g]
        rw [hq_eq]
        simp only [Finset.sum_apply, Real.eNorm_eq_ofReal_abs,
          abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.norm_eq_abs]
        exact single_le_sum (f := fun j ↦ ‖G m (g j) ω - I (g j) ω‖)
          (fun _ _ ↦ norm_nonneg _) (mem_range.2 (Nat.lt_succ_of_le hj₀M))
      exact hdom.trans ((eLpNorm_sum_le one_le_two).trans_eq
        (sum_congr rfl fun j _ ↦ eLpNorm_norm (G m (g j) - I (g j))
          (((hG_adapt m (g j)).sub (hAdapt (g j))).mono (ℱ.le (g j))).aestronglyMeasurable))
    have hint_lim : Tendsto
        (fun m ↦ eLpNorm
          (stoppedProcess (G m) (σ k) t -
            ⇑(hB.l2Integral t (((hH.ite_le (hσ k)).memLp_predictableMeasure t).toLp
              (Function.uncurry Hk)))) 2 P)
        atTop (𝓝 0) := by
      have hlp_lim : Tendsto
          (fun m ↦ eLpNorm
            (fun p : ℝ≥0 × Ω ↦
              (if (p.1 : WithTop ℝ≥0) ≤ σ k p.2 then
                Finance.simpleHolding (τg m) (n m) (a m) p.1 p.2 else 0) - Hk p.1 p.2) 2
            ((Probability.timeMeasure t).prod P)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (herr t)
          (fun _ ↦ zero_le) fun m ↦ ?_
        have hpred_sub : Measurable[ℱ.predictable]
            (fun p : ℝ≥0 × Ω ↦
              (if (p.1 : WithTop ℝ≥0) ≤ σ k p.2 then
                Finance.simpleHolding (τg m) (n m) (a m) p.1 p.2 else 0) - Hk p.1 p.2) :=
          (((Finance.isStronglyPredictable_simpleHolding (ha m)).ite
            (hσ k).measurableSet_predictable_ge stronglyMeasurable_const).sub
              (hH.ite_le (hσ k)).isStronglyPredictable).measurable
        refine eLpNorm_mono_eNorm
          (hpred_sub.mono ℱ.predictable_le_prod le_rfl).aestronglyMeasurable fun p ↦ ?_
        dsimp only [Hk]
        by_cases hs : (p.1 : WithTop ℝ≥0) ≤ σ k p.2
        · rw [ite_eq_left hs, ite_eq_left hs]
        · rw [ite_eq_right hs, ite_eq_right hs, sub_self, eNorm_zero]
          exact zero_le
      refine hlp_lim.congr fun m ↦ ?_
      have hstep_km := coeFn_l2Integral_ite_dyadicCeilTime_simpleHolding hB hτ
        (hτg m) (ha m) (hb m) t k
      let Hkm : ℝ≥0 → Ω → ℝ := fun s ω ↦
        if (s : WithTop ℝ≥0) ≤ σ k ω then Finance.simpleHolding (τg m) (n m) (a m) s ω else 0
      have hBkm : BrownianIntegrable ℱ P Hkm :=
        BrownianIntegrable.ite_le
          ⟨Finance.isStronglyPredictable_simpleHolding (ha m), fun T ↦ by
            simpa only [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def,
              ← ℱ.memLp_predictableMeasure_iff P
                (Finance.isStronglyPredictable_simpleHolding (ha m)) T 2] using
              Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T⟩
          (hσ k)
      exact (eLpNorm_l2Integral_sub hB t hBkm (hH.ite_le (hσ k))).symm.trans
        (eLpNorm_congr_ae (hstep_km.sub EventuallyEq.rfl))
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hstop_lim)
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hint_lim)
  -- Pass `k → ∞` using dyadic martingale stopping on the left and dominated convergence on the
  -- right.
  have hImart : Martingale I ℱ P := hI.martingale hB hH hAdapt
  have hright_cont : ∀ᵐ ω ∂P, IsRightContinuous (fun s ↦ I s ω) := by
    filter_upwards [hI.ae_continuous] with ω hω
    exact hω.isRightContinuous
  have hstop_k_lim : Tendsto
      (fun k ↦ eLpNorm (stoppedProcess I (σ k) t - stoppedProcess I τ t) 2 P) atTop (𝓝 0) :=
    hImart.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime hright_cont hτ t one_le_two
      (by norm_num) (hI.memLp_two hB hH t)
  have hint_k_lim : Tendsto
      (fun k ↦ eLpNorm
        (stoppedProcess I (σ k) t -
          ⇑(hB.l2Integral t ((hHτ.memLp_predictableMeasure t).toLp (Function.uncurry Hτ)))) 2 P)
      atTop (𝓝 0) := by
    have hprod_H : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp t
    have hdom_k : Tendsto
        (fun k ↦ eLpNorm
          ((fun p : ℝ≥0 × Ω ↦ if (p.1 : WithTop ℝ≥0) ≤ σ k p.2 then H p.1 p.2 else 0) -
            Function.uncurry Hτ) 2 ((Probability.timeMeasure t).prod P))
        atTop (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
        (.of_forall fun k ↦ ((hH.ite_le (hσ k)).isStronglyPredictable.mono
          ℱ.predictable_le_prod).aestronglyMeasurable)
        hprod_H (.of_forall fun k ↦ .of_forall fun p ↦ ?_) (.of_forall fun p ↦ ?_)
      · dsimp only [Hτ, Function.uncurry]
        rw [ENNReal.coe_one, one_mul]
        by_cases h1 : (p.1 : WithTop ℝ≥0) ≤ τ p.2
        · rw [ite_eq_left (h1.trans (le_dyadicCeilTime k (τ p.2))), ite_eq_left h1,
            sub_self, eNorm_zero]
          exact zero_le
        · rw [ite_eq_right h1, sub_zero]
          by_cases h2 : (p.1 : WithTop ℝ≥0) ≤ σ k p.2
          · rw [ite_eq_left h2]
          · rw [ite_eq_right h2, eNorm_zero]
            exact zero_le
      · dsimp only [Hτ, Function.uncurry]
        by_cases h1 : (p.1 : WithTop ℝ≥0) ≤ τ p.2
        · rw [ite_eq_left h1]
          exact tendsto_const_nhds.congr fun n ↦
            (ite_eq_left (h1.trans (le_dyadicCeilTime n (τ p.2)))).symm
        · rw [ite_eq_right h1]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [(tendsto_dyadicCeilTime (τ p.2)).eventually
            (eventually_lt_nhds (lt_of_not_ge h1))] with n hn
          exact (ite_eq_right (not_le_of_gt hn)).symm
    refine hdom_k.congr fun k ↦ ?_
    exact (eLpNorm_l2Integral_sub hB t (hH.ite_le (hσ k)) hHτ).symm.trans
      (eLpNorm_congr_ae ((hstep_dyadic k).symm.sub EventuallyEq.rfl))
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hstop_k_lim)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hint_k_lim)

end IsItoIntegral

end TauCeti
