/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.Indistinguishable

/-!
# The Itô integral predicate, algebraic closure, and uniqueness

`TauCeti.IsItoIntegral ℱ P B H I` states that `I` is an Itô stochastic integral of a strongly
predictable integrand `H` against an integrator `B` on `(Ω, ℱ, P)`: almost every path of `I` is
continuous and, at each observation time `t`, some sequence of bounded predictable simple strategies
approximates `H` on `(0, t]` in pathwise lower Lebesgue square energy in probability while its
elementary gains at `t` converge in probability to `I t`.

Requiring `IsStronglyPredictable ℱ H` ensures that time sections and square-energy errors are
genuinely measurable; using the lower Lebesgue integral `∫⁻ s, ‖K_m s ω - H s ω‖ₑ ^ 2` rather than
a Bochner integral prevents non-square-integrable errors from collapsing to the junk value zero.
Indeed, any integrand admitting an Itô integral automatically belongs to
`TauCeti.LocallyBrownianIntegrable` (`TauCeti.IsItoIntegral.locallyBrownianIntegrable`).

Elementary holdings with bounded left-measurable heights integrate to their elementary gains
whenever `B` has almost surely continuous paths (`TauCeti.IsItoIntegral.simpleHolding`), and initial
random variables constant in time integrate to `ξ * (B_t - B_0)` under a finite measure without any
moment assumption (`TauCeti.IsItoIntegral.const_of_stronglyMeasurable_zero`). The predicate is
closed under scalar multiplication, negation, addition, subtraction, indistinguishable modification
of the integral, separate-time a.e. modification of the integrator, and product-a.e. replacement of
predictable integrands.

Against a filtered pre-Brownian integrator `B`, the elementary energy-to-probability bound forces
any Itô integral of the zero integrand to vanish almost everywhere at each fixed time, which by
linearity and path continuity makes the Itô integral unique up to indistinguishability
(`TauCeti.IsItoIntegral.indist`) and invariant under `(timeMeasure t).prod P`-almost-everywhere
replacement of predictable integrands (`TauCeti.IsItoIntegral.indist_of_ae_eq`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {B W H K I J : ℝ≥0 → Ω → ℝ}

/-- `I` is an Itô stochastic integral of `H` against `B` relative to `(ℱ, P)`: `H` is strongly
predictable, `I` has almost surely continuous paths, and at each horizon `t` a sequence of bounded
predictable simple strategies approximates `H` in pathwise square energy in probability while its
elementary gains at `t` converge in measure to `I t`. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is predictable with respect to `ℱ`. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every sample path of the integral process is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At every finite time `t`, bounded predictable simple holdings approximate `H` on `(0, t]`
  in lower square energy in measure while their elementary gains converge in measure to `I t`. -/
  exists_approx : ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
    (∀ m, MonotoneOn (τ m) (Iic (n m))) ∧
    (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
    (∀ m j, j < n m → ∃ C : ℝ, ∀ ω, ‖a m j ω‖ ≤ C) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ m) (n m) (a m) B t) atTop (I t)

/-- Unfolding characterization of `IsItoIntegral`. -/
theorem isItoIntegral_iff :
    IsItoIntegral ℱ P B H I ↔
      IsStronglyPredictable ℱ H ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) ∧
      ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
        (∀ m, MonotoneOn (τ m) (Iic (n m))) ∧
        (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
        (∀ m j, j < n m → ∃ C : ℝ, ∀ ω, ‖a m j ω‖ ≤ C) ∧
        (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
          ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
        TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ m) (n m) (a m) B t) atTop (I t) :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

namespace IsItoIntegral

/-! ### Congruence and structural properties -/

/-- Indistinguishable modifications of an Itô integral remain Itô integrals of the same
integrand. -/
theorem congr_right (hI : IsItoIntegral ℱ P B H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P B H J := by
  refine ⟨hI.isStronglyPredictable, ?_, fun t ↦ ?_⟩
  · filter_upwards [hI.ae_continuous, hIJ] with ω hcont hω
    simpa only [← hω] using hcont
  · obtain ⟨n, τ, a, hτ, ha, hbdd, henergy, hgains⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, ha, hbdd, henergy, hgains.congr_right (hIJ.mono fun ω hω ↦ hω t)⟩

/-- Replacing the integrator by a modification preserves `IsItoIntegral`. -/
theorem congr_integrator (hI : IsItoIntegral ℱ P B H I) (hBW : ∀ s, B s =ᵐ[P] W s) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hI.isStronglyPredictable, hI.ae_continuous, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hbdd, henergy, hgains⟩ := hI.exists_approx t
  refine ⟨n, τ, a, hτ, ha, hbdd, henergy, hgains.congr_left fun m ↦ ?_⟩
  have hgrid : ∀ᵐ ω ∂P, ∀ j ∈ range (n m + 1), B (min (τ m j) t) ω = W (min (τ m j) t) ω :=
    (ae_ball_iff (Finset.countable_toSet _)).2 fun j _ ↦ hBW _
  filter_upwards [hgrid] with ω hω
  exact Finance.simpleGains_congr_price ω fun j hj ↦ hω j (mem_range.2 (Nat.lt_succ_of_le hj))

/-- For s-finite `P`, replacing a predictable integrand by another predictable process that agrees
with it `(timeMeasure t).prod P`-almost everywhere on every finite horizon preserves
`IsItoIntegral`. -/
theorem congr_ae_of_isStronglyPredictable [SFinite P] (hI : IsItoIntegral ℱ P B H I)
    (hK : IsStronglyPredictable ℱ K)
    (heq : ∀ t : ℝ≥0,
      Function.uncurry H =ᵐ[(Probability.timeMeasure t).prod P] Function.uncurry K) :
    IsItoIntegral ℱ P B K I := by
  refine ⟨hK, hI.ae_continuous, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hbdd, henergy, hgains⟩ := hI.exists_approx t
  have hslice : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] (fun s ↦ K s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := P)
        (ν := Probability.timeMeasure t)).quasiMeasurePreserving.ae_eq_comp (heq t))
  refine ⟨n, τ, a, hτ, ha, hbdd, fun ε hε ↦ (henergy ε hε).congr fun m ↦ ?_, hgains⟩
  refine measure_congr (hslice.mono fun ω hω ↦ ?_)
  have hlint :
      ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t =
      ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - K s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t :=
    lintegral_congr_ae (hω.mono fun s hs ↦ by
      dsimp only at hs ⊢
      rw [hs])
  simp only [mem_ofPred_eq]
  rw [hlint]

/-- At time zero any Itô integral vanishes almost everywhere, with no assumption on `B` or `P`. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P B H I) : I 0 =ᵐ[P] 0 := by
  obtain ⟨n, τ, a, hτ, -, -, -, hgains⟩ := hI.exists_approx 0
  have hzero : (fun m ω ↦ Finance.simpleGains (τ m) (n m) (a m) B 0 ω) = fun _ _ ↦ 0 := by
    ext m ω
    exact Finance.simpleGains_of_le (hτ m) zero_le B ω
  rw [hzero] at hgains
  exact tendstoInMeasure_ae_unique hgains (tendstoInMeasure_const 0)

/-- Any integrand admitting an Itô integral has finite pathwise square energy on every finite
horizon almost everywhere. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P B H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun k ↦ ?_⟩
  obtain ⟨n, τ, a, -, ha, hbdd, henergy, -⟩ := hI.exists_approx k
  let μ := Probability.timeMeasure k
  have hμeq : (volume.restrict (Ioc 0 (k : ℝ))).comap ((↑) : ℝ≥0 → ℝ) = μ := by
    rw [← NNReal.coe_natCast k,
      NNReal.comap_volume_restrict_Ioc (k : ℝ≥0), ← Probability.timeMeasure_def]
  rw [hμeq]
  have hnull : P {ω | ∀ m,
      ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2 ∂μ = ∞} = 0 := by
    refine le_antisymm (ge_of_tendsto' (henergy 1 one_pos) fun m ↦ measure_mono fun ω hω ↦ ?_)
      zero_le
    simp only [mem_ofPred_eq] at hω ⊢
    rw [hω m]
    exact le_top
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) hnull
  intro m
  by_contra hlt
  have hsmH : Measurable (fun s ↦ H s ω) :=
    (hI.isStronglyPredictable.mono ℱ.predictable_le_prod).measurable.comp
      (measurable_id.prodMk measurable_const)
  have hsmK : Measurable (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω) :=
    ((Finance.isStronglyPredictable_simpleHolding (ha m)).mono
      ℱ.predictable_le_prod).measurable.comp (measurable_id.prodMk measurable_const)
  have hdiff : MemLp (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω) 2 μ :=
    (hsmK.sub hsmH).aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.2
      (lt_top_iff_ne_top.2 hlt)
  choose C hC using fun j : Fin (n m) ↦ hbdd m j j.2
  have hK_lp : MemLp (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω) 2 μ := by
    refine MemLp.of_bound hsmK.aestronglyMeasurable (∑ j : Fin (n m), C j)
      (.of_forall fun s ↦ ?_)
    rw [Finance.simpleHolding_def, ← Fin.sum_univ_eq_sum_range]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
    by_cases hs : s ∈ Ioc (τ m j) (τ m (j + 1))
    · simpa [hs] using hC j ω
    · simpa [hs] using (norm_nonneg (a m j ω)).trans (hC j ω)
  have hH_lp : MemLp (fun s ↦ H s ω) 2 μ := by
    convert hK_lp.sub hdiff using 1
    ext s
    simp
  exact hω hH_lp

/-! ### Elementary and constant integrands -/

/-- The zero process is an Itô integral of the zero integrand. -/
theorem zero : IsItoIntegral ℱ P B 0 0 := by
  refine ⟨stronglyMeasurable_const, .of_forall fun _ ↦ continuous_const,
    fun t ↦ ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0, fun _ _ _ _ _ _ ↦ le_rfl,
      fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim,
      fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun ε hε ↦ ?_, ?_⟩⟩
  · simp [Finance.simpleHolding_def, hε.not_ge]
  · have hgains : (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ _ ↦ 0) B t) =
        fun _ ↦ (0 : Ω → ℝ) := by
      ext _ _
      simp [Finance.simpleGains_def]
    simpa only [hgains, Pi.zero_apply] using tendstoInMeasure_const (0 : Ω → ℝ)

/-- Against any integrator with almost surely continuous paths, a simple predictable strategy with
bounded heights has its elementary gains as an Itô integral. -/
theorem simpleHolding (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω))
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hbdd : ∀ j < n, ∃ C : ℝ, ∀ ω, ‖a j ω‖ ≤ C) :
    IsItoIntegral ℱ P B (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a B) := by
  refine ⟨Finance.isStronglyPredictable_simpleHolding ha, ?_,
    fun t ↦ ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha, fun _ ↦ hbdd,
      fun ε hε ↦ ?_, tendstoInMeasure_const _⟩⟩
  · filter_upwards [hcont] with ω hω
    simp only [Finance.simpleGains_def]
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
      ((hω.comp (continuous_const.min continuous_id)).sub
        (hω.comp (continuous_const.min continuous_id)))
  · simp [hε.not_ge]

/-- A deterministic constant `c` integrates to `t ↦ c * (B t - B 0)` whenever `B` has almost
surely continuous paths. -/
theorem const (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω)) (c : ℝ) :
    IsItoIntegral ℱ P B (fun _ _ ↦ c) (fun t ω ↦ c * (B t ω - B 0 ω)) := by
  refine ⟨stronglyMeasurable_const, ?_, fun t ↦ ?_⟩
  · filter_upwards [hcont] with ω hω
    exact continuous_const.mul (hω.sub continuous_const)
  · let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then 0 else t
    have hτ : MonotoneOn τ (Iic 1) := by
      intro i _ j _ hij
      dsimp only [τ]
      split_ifs with hi hj hj
      · exact le_rfl
      · exact zero_le
      · omega
      · exact le_rfl
    refine ⟨fun _ ↦ 1, fun _ ↦ τ, fun _ _ _ ↦ c, fun _ ↦ hτ,
      fun _ _ _ ↦ stronglyMeasurable_const, fun _ _ _ ↦ ⟨‖c‖, fun _ ↦ le_rfl⟩,
      fun ε hε ↦ ?_, ?_⟩
    · have hhold (ω : Ω) :
          ∫⁻ s, ‖Finance.simpleHolding τ 1 (fun _ _ ↦ c) s ω - c‖ₑ ^ 2
            ∂Probability.timeMeasure t = 0 := by
        refine (lintegral_congr_ae
          ((Probability.ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ ?_)).trans lintegral_zero
        have hs' : s ∈ Ioc (τ 0) (τ 1) := by simpa [τ] using hs
        simp [Finance.simpleHolding_of_mem_Ioc hτ Nat.zero_lt_one hs']
      simp [hhold, hε.not_ge]
    · have hgains : Finance.simpleGains τ 1 (fun _ _ ↦ c) B t = fun ω ↦ c * (B t ω - B 0 ω) := by
        ext ω
        simp [Finance.simpleGains_def, τ]
      simpa only [hgains] using tendstoInMeasure_const (fun ω ↦ c * (B t ω - B 0 ω))

/-- Under a finite measure, any `ℱ 0`-measurable random variable `ξ` held constant in time
integrates to `t ↦ ξ * (B t - B 0)` without any moment assumption on `ξ`. -/
theorem const_of_stronglyMeasurable_zero [IsFiniteMeasure P]
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω))
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P B (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * (B t ω - B 0 ω)) := by
  refine ⟨((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable, ?_,
    fun t ↦ ?_⟩
  · filter_upwards [hcont] with ω hω
    exact continuous_const.mul (hω.sub continuous_const)
  · let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then 0 else t
    let a : ℕ → ℕ → Ω → ℝ := fun m _ ↦ {ω | ‖ξ ω‖ ≤ m}.indicator ξ
    have hτ : MonotoneOn τ (Iic 1) := by
      intro i _ j _ hij
      dsimp only [τ]
      split_ifs with hi hj hj
      · exact le_rfl
      · exact zero_le
      · omega
      · exact le_rfl
    have ha (m j : ℕ) (hj : j < 1) : StronglyMeasurable[ℱ (τ j)] (a m j) := by
      have hj0 : j = 0 := Nat.lt_one_iff.1 hj
      subst hj0
      simpa only [τ, ↓reduceIte, a] using
        hξ.indicator (measurableSet_le hξ.norm.measurable measurable_const)
    have hbdd (m j : ℕ) (_ : j < 1) : ∃ C : ℝ, ∀ ω, ‖a m j ω‖ ≤ C :=
      ⟨m, fun ω ↦ by
        simp only [a, indicator_apply, mem_ofPred_eq]
        split_ifs with h
        · exact h
        · simp⟩
    have htail : Tendsto (fun m : ℕ ↦ P {ω | (m : ℝ) < ‖ξ ω‖}) atTop (𝓝 0) := by
      have hmeas (m : ℕ) : MeasurableSet {ω | (m : ℝ) < ‖ξ ω‖} :=
        measurableSet_lt measurable_const (hξ.mono (ℱ.le 0)).norm.measurable
      have hanti : Antitone (fun m : ℕ ↦ {ω | (m : ℝ) < ‖ξ ω‖}) := by
        intro m₁ m₂ hm ω hω
        simp only [mem_ofPred_eq] at hω ⊢
        exact (Nat.cast_le.2 hm).trans_lt hω
      have hempty : (⋂ m : ℕ, {ω | (m : ℝ) < ‖ξ ω‖}) = ∅ := by
        ext ω
        simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
        exact exists_nat_ge ‖ξ ω‖
      simpa only [Function.comp_def, hempty, measure_empty] using
        tendsto_measure_iInter_atTop (fun m ↦ (hmeas m).nullMeasurableSet)
          hanti ⟨0, measure_ne_top P _⟩
    refine ⟨fun _ ↦ 1, fun _ ↦ τ, a, fun _ ↦ hτ, ha, hbdd, fun ε hε ↦ ?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
        (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω hω ↦ ?_
      simp only [mem_ofPred_eq] at hω ⊢
      by_contra! hle
      rw [Real.norm_eq_abs] at hle
      have hzero :
          ∫⁻ s, ‖Finance.simpleHolding τ 1 (a m) s ω - ξ ω‖ₑ ^ 2
            ∂Probability.timeMeasure t = 0 := by
        refine (lintegral_congr_ae
          ((Probability.ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ ?_)).trans lintegral_zero
        have hs' : s ∈ Ioc (τ 0) (τ 1) := by simpa [τ] using hs
        simp [Finance.simpleHolding_of_mem_Ioc hτ Nat.zero_lt_one hs', a, hle]
      exact absurd (hε.trans_le (hω.trans_eq hzero)) (lt_irrefl 0)
    · rw [tendstoInMeasure_iff_norm]
      intro ε hε
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
        (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω hω ↦ ?_
      simp only [mem_ofPred_eq] at hω ⊢
      by_contra! hle
      rw [Real.norm_eq_abs] at hle
      have heq : Finance.simpleGains τ 1 (a m) B t ω = ξ ω * (B t ω - B 0 ω) := by
        simp [Finance.simpleGains_def, τ, a, hle]
      exact absurd (hε.trans_le (hω.trans_eq (by simp [heq]))) (lt_irrefl 0)

/-! ### Algebraic closure -/

/-- Scalar multiplication of an integrand scales its Itô integral. -/
theorem const_mul (hI : IsItoIntegral ℱ P B H I) (c : ℝ) :
    IsItoIntegral ℱ P B (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) := by
  refine ⟨hI.isStronglyPredictable.const_mul c,
    hI.ae_continuous.mono fun ω hω ↦ continuous_const.mul hω, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hbdd, henergy, hgains⟩ := hI.exists_approx t
  refine ⟨n, τ, fun m ↦ c • a m, hτ, fun m j hj ↦ (ha m j hj).const_smul c,
    fun m j hj ↦ ?_, fun ε hε ↦ ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hbdd m j hj
    exact ⟨‖c‖ * max C 0, fun ω ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left ((hC ω).trans (le_max_left _ _)) (norm_nonneg c)⟩
  · have hscale (m : ℕ) (ω : Ω) :
        ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (c • a m) s ω - c * H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t =
        ‖c‖ₑ ^ 2 * ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
      have hpt (s : ℝ≥0) :
          ‖Finance.simpleHolding (τ m) (n m) (c • a m) s ω - c * H s ω‖ₑ ^ 2 =
            ‖c‖ₑ ^ 2 * ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2 := by
        rw [Finance.simpleHolding_smul, ← mul_sub, eNorm_mul, mul_pow]
      simp_rw [hpt]
      exact lintegral_const_mul' _ _ (by finiteness)
    simp_rw [hscale]
    by_cases hc : c = 0
    · subst hc
      simp [hε.not_ge]
    · have hc_zero : ‖c‖ₑ ^ 2 ≠ 0 := pow_ne_zero 2 (eNorm_ne_zero.2 hc)
      have hc_top : ‖c‖ₑ ^ 2 ≠ ∞ := by finiteness
      have hpos : 0 < ε / ‖c‖ₑ ^ 2 := ENNReal.div_pos hε.ne' hc_top
      refine (henergy (ε / ‖c‖ₑ ^ 2) hpos).congr fun m ↦ ?_
      congr 1
      ext ω
      simp only [mem_ofPred_eq]
      rw [mul_comm (‖c‖ₑ ^ 2)]
      exact ENNReal.div_le_iff_le_mul (.inl hc_zero) (.inl hc_top)
  · have hgains_eq : (fun m ↦ Finance.simpleGains (τ m) (n m) (c • a m) B t) =
        fun m ω ↦ c • Finance.simpleGains (τ m) (n m) (a m) B t ω := by
      ext m ω
      exact Finance.simpleGains_smul (τ m) (n m) c (a m) B t ω
    rw [hgains_eq]
    simpa only [smul_eq_mul] using hgains.const_smul c

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P B H I) :
    IsItoIntegral ℱ P B (-H) (-I) := by
  convert hI.const_mul (-1) using 1 <;> ext t ω <;> simp

/-- Adding two integrands adds their Itô integrals. -/
theorem add (hI : IsItoIntegral ℱ P B H I) (hJ : IsItoIntegral ℱ P B K J) :
    IsItoIntegral ℱ P B (H + K) (I + J) := by
  refine ⟨hI.isStronglyPredictable.add hJ.isStronglyPredictable,
    (hI.ae_continuous.and hJ.ae_continuous).mono fun ω ⟨h₁, h₂⟩ ↦ h₁.add h₂, fun t ↦ ?_⟩
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hbdd₁, henergy₁, hgains₁⟩ := hI.exists_approx t
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hbdd₂, henergy₂, hgains₂⟩ := hJ.exists_approx t
  -- Refine both elementary strategies onto one common trading grid at each step `m`.
  have href (m : ℕ) : ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ j < n, ∃ C : ℝ, ∀ ω, ‖b j ω‖ ≤ C) ∧
      (∀ s ω, Finance.simpleHolding τ n b s ω =
        Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω +
          Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω) ∧
      (∀ ω, Finance.simpleGains τ n b B t ω =
        Finance.simpleGains (τ₁ m) (n₁ m) (a₁ m) B t ω +
          Finance.simpleGains (τ₂ m) (n₂ m) (a₂ m) B t ω) := by
    let κ := Fin (n₁ m) ⊕ Fin (n₂ m)
    let l : κ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ m i) (fun j ↦ τ₂ m j)
    let u : κ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ m (i + 1)) (fun j ↦ τ₂ m (j + 1))
    let c : κ → Ω → ℝ := Sum.elim (fun i ↦ a₁ m i) (fun j ↦ a₂ m j)
    have hc : ∀ x ∈ (univ : Finset κ), StronglyMeasurable[ℱ (l x)] (c x) := by
      rintro (i | j) _
      · exact ha₁ m i i.2
      · exact ha₂ m j j.2
    obtain ⟨n, τ, b, -, hτ, hb_meas, hb_norm, hb_hold, hb_gains⟩ :=
      Finance.exists_simpleHolding_simpleGains_eq_sum ℱ univ l u c hc
    choose C₁ hC₁ using fun i : Fin (n₁ m) ↦ hbdd₁ m i i.2
    choose C₂ hC₂ using fun j : Fin (n₂ m) ↦ hbdd₂ m j j.2
    refine ⟨n, τ, b, hτ.monotoneOn, hb_meas,
      fun j hj ↦ ⟨(∑ i : Fin (n₁ m), C₁ i) + ∑ i : Fin (n₂ m), C₂ i, fun ω ↦ ?_⟩,
      fun s ω ↦ ?_, fun ω ↦ ?_⟩
    · refine (hb_norm j hj ω).trans ?_
      rw [Fintype.sum_sum_type]
      exact add_le_add (sum_le_sum fun i _ ↦ hC₁ i ω) (sum_le_sum fun i _ ↦ hC₂ i ω)
    · rw [hb_hold, Fintype.sum_sum_type]
      simp only [l, u, c, Sum.elim_inl, Sum.elim_inr, Finance.simpleHolding_def]
      exact congrArg₂ (· + ·)
        (Fin.sum_univ_eq_sum_range
          (fun j ↦ (Ioc (τ₁ m j) (τ₁ m (j + 1))).indicator (fun _ ↦ a₁ m j ω) s) (n₁ m))
        (Fin.sum_univ_eq_sum_range
          (fun j ↦ (Ioc (τ₂ m j) (τ₂ m (j + 1))).indicator (fun _ ↦ a₂ m j ω) s) (n₂ m))
    · rw [hb_gains B t ω, Fintype.sum_sum_type]
      have hlu₁ (i : Fin (n₁ m)) : τ₁ m i ≤ τ₁ m (i + 1) :=
        hτ₁ m i.2.le i.2 (Nat.le_succ i)
      have hlu₂ (j : Fin (n₂ m)) : τ₂ m j ≤ τ₂ m (j + 1) :=
        hτ₂ m j.2.le j.2 (Nat.le_succ j)
      simp only [l, u, c, Sum.elim_inl, Sum.elim_inr, hlu₁, hlu₂, ↓reduceIte,
        Finance.simpleGains_def]
      exact congrArg₂ (· + ·)
        (Fin.sum_univ_eq_sum_range
          (fun j ↦ a₁ m j ω * (B (min (τ₁ m (j + 1)) t) ω - B (min (τ₁ m j) t) ω)) (n₁ m))
        (Fin.sum_univ_eq_sum_range
          (fun j ↦ a₂ m j ω * (B (min (τ₂ m (j + 1)) t) ω - B (min (τ₂ m j) t) ω)) (n₂ m))
  choose n τ b hτ hb_meas hb_bdd hb_hold hb_gains using href
  refine ⟨n, τ, b, hτ, hb_meas, hb_bdd, fun ε hε ↦ ?_, ?_⟩
  · let δ : ℝ≥0∞ := min (ε / 4) 1
    have hδ : 0 < δ := lt_min (ENNReal.div_pos hε.ne' (by norm_num)) one_pos
    have hsum := (henergy₁ δ hδ).add (henergy₂ δ hδ)
    rw [zero_add] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun m ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    by_contra! hlt
    have hsm₁ : Measurable (fun s ↦
        ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2) :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha₁ m)).sub
        hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
          (measurable_id.prodMk measurable_const)).eNorm.pow_const 2
    have hpt (s : ℝ≥0) :
        ‖Finance.simpleHolding (τ m) (n m) (b m) s ω - (H + K) s ω‖ₑ ^ 2 ≤
          2 * (‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2 +
            ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - K s ω‖ₑ ^ 2) := by
      rw [hb_hold m s ω, Pi.add_apply, Pi.add_apply, add_sub_add_comm]
      simp only [Real.enorm_sq_eq_ofReal_sq]
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal add_sq_le
    have hle :
        ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (b m) s ω - (H + K) s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t ≤
        2 * (∫⁻ s, ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t +
          ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - K s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t) := by
      refine (lintegral_mono hpt).trans ?_
      rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_add_left hsm₁]
    have hfin₁ :
        ∫⁻ s, ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t < 1 := hlt.1.trans_le (min_le_right _ _)
    have hfin₂ :
        ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - K s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t < 1 := hlt.2.trans_le (min_le_right _ _)
    have hε_le := hω.trans hle
    by_cases hε_top : ε = ∞
    · rw [hε_top, top_le_iff] at hε_le
      exact (by finiteness : 2 * (_ + _) ≠ (∞ : ℝ≥0∞)) hε_le
    · have h₁ : (∫⁻ s, ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t).toReal < (ε / 4).toReal :=
        (ENNReal.toReal_lt_toReal hfin₁.ne_top (by finiteness)).2
          (hlt.1.trans_le (min_le_left _ _))
      have h₂ : (∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - K s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t).toReal < (ε / 4).toReal :=
        (ENNReal.toReal_lt_toReal hfin₂.ne_top (by finiteness)).2
          (hlt.2.trans_le (min_le_left _ _))
      have hle_real := (ENNReal.toReal_le_toReal hε_top (by finiteness)).2 hε_le
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
        ENNReal.toReal_add hfin₁.ne_top hfin₂.ne_top] at hle_real
      rw [ENNReal.toReal_div, ENNReal.toReal_ofNat] at h₁ h₂
      linarith
  · have hgains_eq : (fun m ↦ Finance.simpleGains (τ m) (n m) (b m) B t) =
        (fun m ↦ Finance.simpleGains (τ₁ m) (n₁ m) (a₁ m) B t) +
          fun m ↦ Finance.simpleGains (τ₂ m) (n₂ m) (a₂ m) B t := by
      ext m ω
      exact hb_gains m ω
    rw [hgains_eq]
    exact hgains₁.add hgains₂

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P B H I) (hJ : IsItoIntegral ℱ P B K J) :
    IsItoIntegral ℱ P B (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-! ### Uniqueness and local congruence -/

end IsItoIntegral

/-- Refine the difference of two adapted finite grids and clip at horizon `t`, expressing the
difference of `Finance.simpleGains` at `t` as a single Brownian increment sum whose
`Probability.elementaryEnergy` equals the `Probability.timeMeasure t` square-norm integral of the
holding difference. -/
theorem Finance.exists_clipped_grid_simpleGains_sub
    {τ₁ τ₂ : ℕ → ℝ≥0} {n₁ n₂ : ℕ} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Iic n₂))
    (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j))
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    ∃ (k : ℕ) (g : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn g (Iic k) ∧
      (∀ j < k, StronglyMeasurable[ℱ (g j)] (b j)) ∧
      (∀ ω, ∑ j ∈ range k, b j ω * (B (g (j + 1)) ω - B (g j) ω) =
        Finance.simpleGains τ₁ n₁ a₁ B t ω - Finance.simpleGains τ₂ n₂ a₂ B t ω) ∧
      (∀ ω, ENNReal.ofReal (Probability.elementaryEnergy g b k ω) =
        ∫⁻ s, ‖Finance.simpleHolding τ₁ n₁ a₁ s ω -
          Finance.simpleHolding τ₂ n₂ a₂ s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) := by
  let κ := Fin n₁ ⊕ Fin n₂
  let l : κ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ i) (fun j ↦ τ₂ j)
  let u : κ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ (i + 1)) (fun j ↦ τ₂ (j + 1))
  let c : κ → Ω → ℝ := Sum.elim (fun i ↦ a₁ i) (fun j ↦ -a₂ j)
  have hc : ∀ x ∈ (univ : Finset κ), StronglyMeasurable[ℱ (l x)] (c x) := by
    rintro (i | j) _
    · exact ha₁ i i.2
    · exact (ha₂ j j.2).neg
  obtain ⟨k, g₀, b₀, -, hg₀, hb₀, -, hhold₀, hgains₀⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ univ l u c hc
  let g : ℕ → ℝ≥0 := fun j ↦ min (g₀ j) t
  let b : ℕ → Ω → ℝ := fun j ↦ if g₀ j ≤ t then b₀ j else 0
  have hg : MonotoneOn g (Iic k) := fun i hi j hj hij ↦
    min_le_min_right t (hg₀.monotoneOn hi hj hij)
  have hb_m (j : ℕ) (hj : j < k) : StronglyMeasurable[ℱ (g j)] (b j) := by
    by_cases hle : g₀ j ≤ t
    · have hge : g j = g₀ j := min_eq_left hle
      rw [hge]
      simpa only [b, hle, ↓reduceIte] using hb₀ j hj
    · simpa only [b, hle, ↓reduceIte] using
        (stronglyMeasurable_zero : StronglyMeasurable[ℱ (g j)] (fun _ : Ω ↦ (0 : ℝ)))
  have hhold_diff (s : ℝ≥0) (ω : Ω) :
      Finance.simpleHolding g₀ k b₀ s ω =
        Finance.simpleHolding τ₁ n₁ a₁ s ω - Finance.simpleHolding τ₂ n₂ a₂ s ω := by
    rw [hhold₀, Fintype.sum_sum_type]
    have hneg_ind (j : Fin n₂) :
        (Ioc (τ₂ j) (τ₂ (j + 1))).indicator (fun _ ↦ (-a₂ j) ω) s =
          -(Ioc (τ₂ j) (τ₂ (j + 1))).indicator (fun _ ↦ a₂ j ω) s := by
      by_cases hs : s ∈ Ioc (τ₂ j) (τ₂ (j + 1)) <;> simp [hs]
    simp only [l, u, c, Sum.elim_inl, Sum.elim_inr, hneg_ind, sum_neg_distrib,
      ← sub_eq_add_neg, Finance.simpleHolding_def]
    exact congrArg₂ (· - ·)
      (Fin.sum_univ_eq_sum_range
        (fun j ↦ (Ioc (τ₁ j) (τ₁ (j + 1))).indicator (fun _ ↦ a₁ j ω) s) n₁)
      (Fin.sum_univ_eq_sum_range
        (fun j ↦ (Ioc (τ₂ j) (τ₂ (j + 1))).indicator (fun _ ↦ a₂ j ω) s) n₂)
  have hgains_diff (ω : Ω) :
      Finance.simpleGains g₀ k b₀ B t ω =
        Finance.simpleGains τ₁ n₁ a₁ B t ω - Finance.simpleGains τ₂ n₂ a₂ B t ω := by
    rw [hgains₀ B t ω, Fintype.sum_sum_type]
    have hlu₁ (i : Fin n₁) : τ₁ i ≤ τ₁ (i + 1) := hτ₁ i.2.le i.2 (Nat.le_succ i)
    have hlu₂ (j : Fin n₂) : τ₂ j ≤ τ₂ (j + 1) := hτ₂ j.2.le j.2 (Nat.le_succ j)
    simp only [l, u, c, Sum.elim_inl, Sum.elim_inr, hlu₁, hlu₂, ↓reduceIte, Pi.neg_apply,
      neg_mul, sum_neg_distrib, ← sub_eq_add_neg, Finance.simpleGains_def]
    exact congrArg₂ (· - ·)
      (Fin.sum_univ_eq_sum_range
        (fun j ↦ a₁ j ω * (B (min (τ₁ (j + 1)) t) ω - B (min (τ₁ j) t) ω)) n₁)
      (Fin.sum_univ_eq_sum_range
        (fun j ↦ a₂ j ω * (B (min (τ₂ (j + 1)) t) ω - B (min (τ₂ j) t) ω)) n₂)
  refine ⟨k, g, b, hg, hb_m, fun ω ↦ ?_, fun ω ↦ ?_⟩
  · rw [← hgains_diff ω, Finance.simpleGains_def]
    refine sum_congr rfl fun j hj ↦ ?_
    by_cases hle : g₀ j ≤ t
    · simp only [b, g, hle, ↓reduceIte]
    · have hj' : g₀ j ≤ g₀ (j + 1) := hg₀.monotoneOn (mem_range.1 hj).le (mem_range.1 hj)
        (Nat.le_succ j)
      have ht₁ : t ≤ g₀ j := le_of_not_ge hle
      simp [b, g, hle, min_eq_right ht₁, min_eq_right (ht₁.trans hj')]
  · simp_rw [← hhold_diff]
    rw [Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hg₀.monotoneOn t ω,
      Probability.elementaryEnergy_def,
      ENNReal.ofReal_sum_of_nonneg fun j hj ↦ mul_nonneg (sq_nonneg _)
        (sub_nonneg.2 (NNReal.coe_le_coe.2
          (hg (mem_range.1 hj).le (mem_range.1 hj) (Nat.le_succ j))))]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hle : g₀ j ≤ t
    · simp only [b, g, hle, ↓reduceIte, min_eq_left hle, Real.enorm_sq_eq_ofReal_sq]
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
    · simp [b, hle, le_of_not_ge hle]

/-- At a fixed horizon `t`, any two sequences of adapted simple strategies that both approximate a
strongly predictable integrand `H` in pathwise square energy in probability and whose elementary
gains at `t` converge in probability have almost everywhere equal gain limits. -/
theorem Probability.IsFilteredPreBrownianReal.ae_eq_of_tendstoInMeasure_simpleGains
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : IsStronglyPredictable ℱ H) {t : ℝ≥0}
    {n₁ n₂ : ℕ → ℕ} {τ₁ τ₂ : ℕ → ℕ → ℝ≥0} {a₁ a₂ : ℕ → ℕ → Ω → ℝ}
    (hτ₁ : ∀ m, MonotoneOn (τ₁ m) (Iic (n₁ m)))
    (hτ₂ : ∀ m, MonotoneOn (τ₂ m) (Iic (n₂ m)))
    (ha₁ : ∀ m j, j < n₁ m → StronglyMeasurable[ℱ (τ₁ m j)] (a₁ m j))
    (ha₂ : ∀ m j, j < n₂ m → StronglyMeasurable[ℱ (τ₂ m j)] (a₂ m j))
    (henergy₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (henergy₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0))
    {X Y : Ω → ℝ}
    (hgains₁ : TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ₁ m) (n₁ m) (a₁ m) B t) atTop X)
    (hgains₂ : TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ₂ m) (n₂ m) (a₂ m) B t) atTop Y) :
    X =ᵐ[P] Y := by
  choose k g b hg hb hsum_eq henergy_eq using fun m ↦
    Finance.exists_clipped_grid_simpleGains_sub (hτ₁ m) (hτ₂ m) (ha₁ m) (ha₂ m) B t
  have henergy_zero : TendstoInMeasure P
      (fun m ↦ Probability.elementaryEnergy (g m) (b m) (k m)) atTop (fun _ ↦ 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro δ hδ
    let η : ℝ≥0∞ := min (ENNReal.ofReal δ / 4) 1
    have hη : 0 < η := lt_min (ENNReal.div_pos (ENNReal.ofReal_pos.2 hδ).ne' (by norm_num)) one_pos
    have hsum := (henergy₁ η hη).add (henergy₂ η hη)
    rw [zero_add] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun m ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
    simp only [mem_ofPred_eq, mem_union, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (Probability.elementaryEnergy_nonneg (hg m) ω)] at hω ⊢
    by_contra! hlt
    have hsm₁ : Measurable (fun s ↦
        ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2) :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha₁ m)).sub hH).mono
        ℱ.predictable_le_prod).measurable.comp
          (measurable_id.prodMk measurable_const)).eNorm.pow_const 2
    have hpt (s : ℝ≥0) :
        ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω -
          Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω‖ₑ ^ 2 ≤
          2 * (‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2 +
            ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - H s ω‖ₑ ^ 2) := by
      simp only [Real.enorm_sq_eq_ofReal_sq]
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsq : (Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω -
          Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω) ^ 2 =
          ((Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω) +
            (H s ω - Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω)) ^ 2 := by ring
      rw [hsq]
      exact add_sq_le.trans_eq (by ring)
    have hle : ENNReal.ofReal δ ≤
        2 * (∫⁻ s, ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t +
          ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - H s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t) := by
      calc ENNReal.ofReal δ
          ≤ ENNReal.ofReal (Probability.elementaryEnergy (g m) (b m) (k m) ω) :=
            ENNReal.ofReal_le_ofReal hω
        _ = _ := henergy_eq m ω
        _ ≤ _ := by
            refine (lintegral_mono hpt).trans ?_
            rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_add_left hsm₁]
    have hfin₁ := hlt.1.trans_le (min_le_right _ _)
    have hfin₂ := hlt.2.trans_le (min_le_right _ _)
    have h₁ := (ENNReal.toReal_lt_toReal hfin₁.ne_top (by finiteness)).2
      (hlt.1.trans_le (min_le_left _ _))
    have h₂ := (ENNReal.toReal_lt_toReal hfin₂.ne_top (by finiteness)).2
      (hlt.2.trans_le (min_le_left _ _))
    have hle_real := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).2 hle
    rw [ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_add hfin₁.ne_top hfin₂.ne_top] at hle_real
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofNat] at h₁ h₂
    linarith
  have hdG_lim₂ := hB.tendstoInMeasure_sum_mul_sub_of_energy hg hb henergy_zero
  simp_rw [hsum_eq] at hdG_lim₂
  filter_upwards [tendstoInMeasure_ae_unique (hgains₁.sub hgains₂) hdG_lim₂] with ω hω
  exact sub_eq_zero.1 hω

namespace IsItoIntegral

/-- Two Itô integrals of the same integrand against a filtered pre-Brownian integrator agree
almost everywhere at each fixed time. -/
theorem ae_eq_eval (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hI : IsItoIntegral ℱ P B H I) (hJ : IsItoIntegral ℱ P B H J) (t : ℝ≥0) :
    I t =ᵐ[P] J t := by
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, -, henergy₁, hgains₁⟩ := hI.exists_approx t
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, -, henergy₂, hgains₂⟩ := hJ.exists_approx t
  exact hB.ae_eq_of_tendstoInMeasure_simpleGains hI.isStronglyPredictable
    hτ₁ hτ₂ ha₁ ha₂ henergy₁ henergy₂ hgains₁ hgains₂

/-- Against a filtered pre-Brownian integrator, any Itô integral of the zero integrand vanishes
almost everywhere at each fixed observation time. -/
theorem ae_eq_zero_eval_of_zero (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hI : IsItoIntegral ℱ P B 0 I) (t : ℝ≥0) : I t =ᵐ[P] 0 :=
  hI.ae_eq_eval hB .zero t

/-- **Uniqueness of the Itô integral.** Against a filtered pre-Brownian integrator, any two Itô
integrals of the same integrand are indistinguishable. -/
theorem indist (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hI : IsItoIntegral ℱ P B H I) (hJ : IsItoIntegral ℱ P B H J) :
    I ≡ᵐ[P] J :=
  Indistinguishable.of_ae_eq_eval_of_ae_continuous hI.ae_continuous hJ.ae_continuous
    (hI.ae_eq_eval hB hJ)

/-- **Representative independence of the Itô integral.** Against a filtered pre-Brownian
integrator, Itô integrals of predictable integrands that agree `(timeMeasure t).prod P`-almost
everywhere on every finite horizon are indistinguishable. -/
theorem indist_of_ae_eq (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hI : IsItoIntegral ℱ P B H I) (hJ : IsItoIntegral ℱ P B K J)
    (heq : ∀ t : ℝ≥0,
      Function.uncurry H =ᵐ[(Probability.timeMeasure t).prod P] Function.uncurry K) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (hI.congr_ae_of_isStronglyPredictable hJ.isStronglyPredictable heq).indist hB hJ

end IsItoIntegral

end TauCeti
