/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.Lp.Product
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# The L² Brownian Itô integral, isometry, martingale property, and existence

On the expected-square-energy domain `TauCeti.BrownianIntegrable ℱ P H`, the pathwise-energy
predicate `TauCeti.IsItoIntegral ℱ P B H I` is identified at every deterministic horizon `t` with
the Hilbert-space terminal integral `TauCeti.Probability.IsFilteredPreBrownianReal.l2Integral`:
an almost surely continuous process `I` satisfies `IsItoIntegral ℱ P B H I` if and only if
`I t` agrees almost everywhere with `hB.l2Integral t` of `H` at every `t`
(`TauCeti.BrownianIntegrable.isItoIntegral_iff_ae_eq_l2Integral`).

From this identification follow:
* `TauCeti.Probability.IsFilteredPreBrownianReal.coeFn_l2Integral_simpleHolding`: on any finite
  monotone grid with square-integrable left-measurable heights, `l2Integral` agrees almost
  everywhere with `TauCeti.Finance.simpleGains`.
* `TauCeti.IsItoIntegral.memLp_two`, `TauCeti.IsItoIntegral.integral_eq_zero`, and
  `TauCeti.IsItoIntegral.integral_sq`: square integrability, zero mean, and the Itô isometry
  `∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P`, without assuming adaptedness of
  the chosen version `I` or path continuity of `B`.
* `TauCeti.IsItoIntegral.martingale`: any strongly adapted Itô integral of a Brownian-integrable
  process is a true martingale on `ℱ`.
* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `B` has almost surely continuous paths,
  every `H` in `BrownianIntegrable ℱ P H` admits a strongly predictable Itô integral that is a
  martingale on the raw filtration `ℱ`, with no completeness or right-continuity assumption on `ℱ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti

private theorem exists_simple_approx_l2 {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {ξ : α → ℝ} (hξ : StronglyMeasurable ξ)
    (hξ₂ : eLpNorm ξ 2 ν < ∞) :
    ∃ (φ : ℕ → α → ℝ) (R : ℕ → Finset ℝ),
      (∀ k, StronglyMeasurable (φ k)) ∧
      (∀ k x, MeasurableSet (φ k ⁻¹' {x})) ∧
      (∀ k ω, ‖φ k ω‖ ≤ ∑ x ∈ R k, ‖x‖) ∧
      (∀ k ω, φ k ω = ∑ x ∈ R k, (φ k ⁻¹' {x}).indicator (fun _ ↦ x) ω) ∧
      Tendsto (fun k ↦ eLpNorm (φ k - ξ) 2 ν) atTop (𝓝 0) := by
  let ψ : ℕ → SimpleFunc α ℝ := fun k ↦
    SimpleFunc.approxOn ξ hξ.measurable univ 0 (mem_univ 0) k
  refine ⟨fun k ↦ ⇑(ψ k), fun k ↦ (ψ k).range,
    fun k ↦ (ψ k).stronglyMeasurable,
    fun k x ↦ (ψ k).measurableSet_fiber x,
    fun k ω ↦ single_le_sum (fun x _ ↦ norm_nonneg x) ((ψ k).mem_range_self ω),
    fun k ω ↦ ?_,
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hξ.measurable (mem_univ 0) (by norm_num)
      (.of_forall fun _ ↦ subset_closure (mem_univ _))
      (by simpa only [sub_zero] using hξ₂)⟩
  symm
  rw [sum_eq_single (ψ k ω)]
  · simp
  · intro x _ hx
    exact indicator_of_notMem (by simp [hx.symm]) _
  · intro hnot
    exact (hnot ((ψ k).mem_range_self ω)).elim

private theorem integral_sq_lp {α : Type*} [MeasurableSpace α] (μ₀ : Measure α) (g : Lp ℝ 2 μ₀) :
    ∫ x, (g : α → ℝ) x ^ 2 ∂μ₀ = ‖g‖ ^ 2 := by
  open scoped InnerProductSpace in
  simpa only [RCLike.inner_apply, conj_trivial, sq] using
    (L2.inner_def (𝕜 := ℝ) g g).symm.trans (real_inner_self_eq_norm_sq g)

private theorem integral_sq_eq_norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ₀ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ₀) :
    ∫ x, f x ^ 2 ∂μ₀ = ‖hf.toLp f‖ ^ 2 := by
  refine (integral_congr_ae ?_).trans (integral_sq_lp μ₀ (hf.toLp f))
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {B H I : ℝ≥0 → Ω → ℝ}

/-- A Brownian-integrable process belongs to `L²` of the finite-horizon predictable measure at
every horizon `T`. -/
theorem BrownianIntegrable.memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) := by
  rw [ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2]
  simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp T

/-! ### Agreement of `l2Integral` with elementary strategies -/

/-- Clipping an increment `X u - X s` with `s ≤ u` at `T` via `max s (min u T)` equals the
difference of `T`-clipped evaluations `X (min u T) - X (min s T)`. -/
theorem sub_max_min_eq {ι G : Type*} [LinearOrder ι] [AddGroup G]
    {X : ι → G} {s u T : ι} (hsu : s ≤ u) :
    X (max s (min u T)) - X s = X (min u T) - X (min s T) := by
  by_cases hsT : s ≤ T
  · rw [min_eq_left hsT, max_eq_right (le_min hsu hsT)]
  · have hTs : T ≤ s := le_of_not_ge hsT
    rw [min_eq_right hTs, min_eq_right (hTs.trans hsu), max_eq_left hTs, sub_self, sub_self]

/-- A single predictable holding `(Ioc s u).indicator (fun _ ↦ ξ ω) t` with `ℱ s`-strongly
measurable `ξ` is strongly predictable. -/
theorem isStronglyPredictable_indicator_Ioc {s u : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsStronglyPredictable ℱ (fun r ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) r) := by
  have h1 := Finance.isStronglyPredictable_simpleHolding (ℱ := ℱ)
    (τ := fun j ↦ match j with | 0 => s | _ => u) (n := 1) (a := fun _ ↦ ξ)
    (fun j hj ↦ by obtain rfl : j = 0 := Nat.lt_one_iff.1 hj; exact hξ)
  convert h1 using 1
  ext r ω
  rw [Finance.simpleHolding_def, sum_range_one]
  rfl

/-- A single predictable holding `(Ioc s u).indicator (fun _ ↦ ξ ω) t` with `ℱ s`-strongly
measurable `ξ ∈ Lᵖ(P)` belongs to `Lᵖ` of `ℱ.predictableMeasure P T`. -/
theorem memLp_indicator_Ioc_predictableMeasure [SFinite P] {p : ℝ≥0∞} {s : ℝ≥0} (u T : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξp : MemLp ξ p P) :
    MemLp (fun q : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ q.2) q.1) p
      (ℱ.predictableMeasure P T) := by
  have h1 := Finance.memLp_simpleHolding_predictableMeasure (ℱ := ℱ) (P := P) (p := p)
    (τ := fun j ↦ match j with | 0 => s | _ => u) (n := 1) (a := fun _ ↦ ξ)
    (fun j hj ↦ by obtain rfl : j = 0 := Nat.lt_one_iff.1 hj; exact hξ)
    (fun _ _ ↦ hξp) T
  simpa only [Function.uncurry_def, Finance.simpleHolding_def, sum_range_one] using h1

namespace Probability.IsFilteredPreBrownianReal

/-- On a single predictable interval `(s, u]` with `s ≤ u`, the terminal `L²` Brownian integral at
horizon `T` of a square-integrable `ℱ s`-measurable random height `ξ` is
`ξ * (B (u ⊓ T) - B (s ⊓ T))` almost everywhere. -/
theorem coeFn_l2Integral_indicator_Ioc (hB : IsFilteredPreBrownianReal ℱ B P)
    {s u : ℝ≥0} (hsu : s ≤ u) (T : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    letI := (hB.hasLaw_eval 0).isProbabilityMeasure
    hB.l2Integral T ((memLp_indicator_Ioc_predictableMeasure u T hξ hξ₂).toLp
      (fun p ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1)) =ᵐ[P]
      fun ω ↦ ξ ω * (B (min u T) ω - B (min s T) ω) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  let hold (f : Ω → ℝ) (p : ℝ≥0 × Ω) : ℝ := (Ioc s u).indicator (fun _ ↦ f p.2) p.1
  by_cases hsT : s ≤ T
  · -- Approximate `ξ` in `L²(P)` by `ℱ s`-measurable finite-range functions.
    have hξ_trim := (eLpNorm_trim (ℱ.le s) hξ).trans_lt hξ₂.eLpNorm_lt_top
    obtain ⟨φ, R, hφ_sm, hφ_fib, hφ_bdd, hφ_sum, hφ_lim_trim⟩ :=
      @exists_simple_approx_l2 Ω (ℱ s) (P.trim (ℱ.le s)) ξ hξ hξ_trim
    have hφ_lp (k : ℕ) : MemLp (φ k) 2 P :=
      MemLp.of_bound ((hφ_sm k).mono (ℱ.le s)).aestronglyMeasurable
        (∑ x ∈ R k, ‖x‖) (.of_forall (hφ_bdd k))
    have hφ_lim : Tendsto (fun k ↦ eLpNorm (φ k - ξ) 2 P) atTop (𝓝 0) :=
      hφ_lim_trim.congr fun k ↦ eLpNorm_trim (ℱ.le s) ((hφ_sm k).sub hξ)
    have hsuT : s ≤ min u T := le_min hsu hsT
    -- On each finite-range `φ k`, decompose into fiber rectangles and apply the rectangle formula.
    have hφ_eq (k : ℕ) :
        hB.l2Integral T
          ((memLp_indicator_Ioc_predictableMeasure u T (hφ_sm k) (hφ_lp k)).toLp (hold (φ k))) =
          (hB.memLp_mul_sub hsuT (hφ_sm k) (hφ_lp k)).toLp
            (fun ω ↦ φ k ω * (B (min u T) ω - B s ω)) := by
      let rectLp (x : ℝ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
        indicatorConstLp 2
          (measurableSet_predictable_Ioc_prod s u (hφ_fib k x))
          (measure_ne_top _ _) x
      have hdecomp :
          (memLp_indicator_Ioc_predictableMeasure u T (hφ_sm k) (hφ_lp k)).toLp (hold (φ k)) =
            ∑ x ∈ R k, rectLp x := by
        apply Lp.ext
        have hcoe_each : ∀ x ∈ R k, (rectLp x : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
            fun p ↦ (Ioc s u ×ˢ (φ k ⁻¹' {x})).indicator (fun _ ↦ x) p := fun _ _ ↦
          indicatorConstLp_coeFn
        filter_upwards [(memLp_indicator_Ioc_predictableMeasure u T (hφ_sm k) (hφ_lp k)).coeFn_toLp,
          Lp.coeFn_finsetSum (R k) rectLp,
          (ae_ball_iff (Finset.countable_toSet _)).2 hcoe_each] with p hp hsum hall
        rw [hp, hsum, Finset.sum_apply]
        have hpt : (Ioc s u).indicator (fun _ ↦ φ k p.2) p.1 =
            ∑ x ∈ R k, (Ioc s u ×ˢ (φ k ⁻¹' {x})).indicator (fun _ ↦ x) p := by
          by_cases ht : p.1 ∈ Ioc s u
          · simp only [ht, indicator_of_mem, hφ_sum k p.2]
            refine sum_congr rfl fun x _ ↦ ?_
            by_cases hx : p.2 ∈ φ k ⁻¹' {x} <;> simp [ht, hx]
          · simp [ht]
        rw [hpt]
        exact sum_congr rfl fun x hx ↦ (hall x hx).symm
      rw [hdecomp, map_sum]
      apply Lp.ext
      have hterm_ae : ∀ x ∈ R k,
          (hB.l2Integral T (rectLp x) : Ω → ℝ) =ᵐ[P]
            fun ω ↦ (φ k ⁻¹' {x}).indicator (fun _ ↦ x) ω * (B (min u T) ω - B s ω) := by
        intro x _
        simpa only [max_eq_right hsuT] using
          hB.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s u (hφ_fib k x) x
      filter_upwards [Lp.coeFn_finsetSum (R k) (fun x ↦ hB.l2Integral T (rectLp x)),
        (hB.memLp_mul_sub hsuT (hφ_sm k) (hφ_lp k)).coeFn_toLp,
        (ae_ball_iff (Finset.countable_toSet _)).2 hterm_ae] with ω hsum hrhs hall
      rw [hsum, hrhs, Finset.sum_apply, hφ_sum k ω, sum_mul]
      exact sum_congr rfl fun x hx ↦ hall x hx
    -- Pass `k → ∞` on both sides in `Lp ℝ 2 P`.
    have hconv_lhs : Tendsto
        (fun k ↦ hB.l2Integral T
          ((memLp_indicator_Ioc_predictableMeasure u T (hφ_sm k) (hφ_lp k)).toLp (hold (φ k))))
        atTop (𝓝 (hB.l2Integral T
          ((memLp_indicator_Ioc_predictableMeasure u T hξ hξ₂).toLp (hold ξ)))) := by
      refine (hB.l2Integral T).continuous.tendsto _ |>.comp ?_
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
      have hbound (k : ℕ) :
          eLpNorm (hold (φ k) - hold ξ) 2 (ℱ.predictableMeasure P T) ≤
            eLpNorm (fun _ : ℝ≥0 ↦ (1 : ℝ)) 2 (timeMeasure T) *
              eLpNorm (φ k - ξ) 2 P := by
        have hpred : StronglyMeasurable[ℱ.predictable] (hold (φ k) - hold ξ) :=
          (isStronglyPredictable_indicator_Ioc (hφ_sm k)).sub
            (isStronglyPredictable_indicator_Ioc hξ)
        rw [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hpred]
        refine (eLpNorm_mono_eNorm (g := fun p : ℝ≥0 × Ω ↦ (1 : ℝ) * (φ k - ξ) p.2)
          (hpred.mono ℱ.predictable_le_prod).aestronglyMeasurable fun p ↦ ?_).trans
          (eLpNorm_mul_prod_le aestronglyMeasurable_const
            (((hφ_sm k).sub hξ).mono (ℱ.le s)).aestronglyMeasurable)
        dsimp only [hold, Pi.sub_apply]
        by_cases hr : p.1 ∈ Ioc s u <;> simp [hr]
      have hlim_prod := ENNReal.Tendsto.const_mul hφ_lim
        (Or.inr (memLp_const (p := 2) (1 : ℝ) (μ := timeMeasure T)).eLpNorm_lt_top.ne)
      rw [mul_zero] at hlim_prod
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_prod
        (fun _ ↦ zero_le) hbound
    have hconv_rhs : Tendsto
        (fun k ↦ (hB.memLp_mul_sub hsuT (hφ_sm k) (hφ_lp k)).toLp
          (fun ω ↦ φ k ω * (B (min u T) ω - B s ω)))
        atTop (𝓝 ((hB.memLp_mul_sub hsuT hξ hξ₂).toLp
          (fun ω ↦ ξ ω * (B (min u T) ω - B s ω)))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hnorm_eq (k : ℕ) :
          ‖(hB.memLp_mul_sub hsuT (hφ_sm k) (hφ_lp k)).toLp
              (fun ω ↦ φ k ω * (B (min u T) ω - B s ω)) -
            (hB.memLp_mul_sub hsuT hξ hξ₂).toLp
              (fun ω ↦ ξ ω * (B (min u T) ω - B s ω))‖ =
            Real.sqrt ((eLpNorm (φ k - ξ) 2 P).toReal ^ 2 * (((min u T : ℝ≥0) : ℝ) - s)) := by
        have hm₁ := hB.memLp_mul_sub hsuT ((hφ_sm k).sub hξ) ((hφ_lp k).sub hξ₂)
        have hm₂ := (hφ_lp k).sub hξ₂
        have hsub :
            (hB.memLp_mul_sub hsuT (hφ_sm k) (hφ_lp k)).toLp
                (fun ω ↦ φ k ω * (B (min u T) ω - B s ω)) -
              (hB.memLp_mul_sub hsuT hξ hξ₂).toLp
                (fun ω ↦ ξ ω * (B (min u T) ω - B s ω)) =
            hm₁.toLp (fun ω ↦ (φ k - ξ) ω * (B (min u T) ω - B s ω)) := by
          apply Lp.ext
          filter_upwards [Lp.coeFn_sub (E := ℝ) _ _,
            (hB.memLp_mul_sub hsuT (hφ_sm k) (hφ_lp k)).coeFn_toLp,
            (hB.memLp_mul_sub hsuT hξ hξ₂).coeFn_toLp, hm₁.coeFn_toLp] with ω h1 h2 h3 h4
          rw [h1, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, sub_mul]
        rw [hsub, ← Real.sqrt_sq (norm_nonneg _), ← integral_sq_eq_norm_toLp_sq hm₁,
          hB.integral_sq_mul_sub hsuT ((hφ_sm k).sub hξ), integral_sq_eq_norm_toLp_sq hm₂,
          Lp.norm_toLp]
      simp_rw [hnorm_eq]
      have htoReal : Tendsto (fun k ↦ (eLpNorm (φ k - ξ) 2 P).toReal) atTop (𝓝 0) := by
        simpa only [Function.comp_def, ENNReal.toReal_zero] using
          (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hφ_lim
      simpa only [Function.comp_def, zero_pow two_ne_zero, zero_mul, Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp
          ((htoReal.pow 2).mul_const (((min u T : ℝ≥0) : ℝ) - s))
    simp_rw [hφ_eq] at hconv_lhs
    dsimp only [hold] at hconv_lhs
    rw [tendsto_nhds_unique hconv_lhs hconv_rhs]
    filter_upwards [(hB.memLp_mul_sub hsuT hξ hξ₂).coeFn_toLp] with ω hω
    simpa only [min_eq_left hsT] using hω
  · -- When `T < s ≤ u`, `(s, u]` misses `(0, T]` completely and both sides vanish.
    have hTs : T ≤ s := le_of_not_ge hsT
    have hzero_lp : (memLp_indicator_Ioc_predictableMeasure u T hξ hξ₂).toLp
        (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) = 0 := by
      apply Lp.ext
      have hnull : ℱ.predictableMeasure P T (Ioc s u ×ˢ (univ : Set Ω)) = 0 := by
        rw [ℱ.predictableMeasure_Ioc_prod P T s u MeasurableSet.univ,
          min_eq_right (hTs.trans hsu), ENNReal.ofReal_of_nonpos
            (sub_nonpos.2 (NNReal.coe_le_coe.2 hTs)), zero_mul]
      have hae : ∀ᵐ p ∂ℱ.predictableMeasure P T, p ∉ Ioc s u ×ˢ (univ : Set Ω) := by
        rw [eventually_iff, ← compl_compl {p | p ∉ _}]
        exact measure_mono_null (fun p hp ↦ by simpa using hp) hnull
      filter_upwards [(memLp_indicator_Ioc_predictableMeasure u T hξ hξ₂).coeFn_toLp,
        Lp.coeFn_zero ℝ 2 (ℱ.predictableMeasure P T), hae] with p hp hz hnot
      have hp1 : p.1 ∉ Ioc s u := fun h ↦ hnot ⟨h, mem_univ _⟩
      rw [hp, hz, Pi.zero_apply, indicator_of_notMem hp1]
    rw [hzero_lp, map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hz
    rw [hz, Pi.zero_apply, min_eq_right hTs, min_eq_right (hTs.trans hsu), sub_self, mul_zero]

/-- On any monotone finite grid with square-integrable left-measurable heights, the terminal `L²`
Brownian integral at horizon `T` agrees almost everywhere with `Finance.simpleGains`. -/
theorem coeFn_l2Integral_simpleHolding (hB : IsFilteredPreBrownianReal ℱ B P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    letI := (hB.hasLaw_eval 0).isProbabilityMeasure
    hB.l2Integral T
        ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
          (Function.uncurry (Finance.simpleHolding τ n a))) =ᵐ[P]
      Finance.simpleGains τ n a B T := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  let term (j : ℕ) (p : ℝ≥0 × Ω) : ℝ := (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1
  let termLp (j : ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    if hj : j < n then
      (memLp_indicator_Ioc_predictableMeasure (τ (j + 1)) T (ha j hj) (ha₂ j hj)).toLp (term j)
    else 0
  have hdecomp :
      (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
        (Function.uncurry (Finance.simpleHolding τ n a)) =
      ∑ j ∈ range n, termLp j := by
    apply Lp.ext
    have hcoe_each : ∀ j ∈ range n, (termLp j : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
        term j := by
      intro j hj
      have hj' := mem_range.1 hj
      simpa only [termLp, hj', ↓reduceDIte] using
        (memLp_indicator_Ioc_predictableMeasure (τ (j + 1)) T (ha j hj') (ha₂ j hj')).coeFn_toLp
    filter_upwards [(Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp,
      Lp.coeFn_finsetSum (range n) termLp,
      (ae_ball_iff (Finset.countable_toSet _)).2 hcoe_each] with p hp hsum hall
    rw [hp, hsum, Finset.sum_apply, Function.uncurry_apply_pair, Finance.simpleHolding_def]
    exact sum_congr rfl fun j hj ↦ (hall j hj).symm
  rw [hdecomp, map_sum]
  have hterm_int : ∀ j ∈ range n, (hB.l2Integral T (termLp j) : Ω → ℝ) =ᵐ[P]
      fun ω ↦ a j ω * (B (min (τ (j + 1)) T) ω - B (min (τ j) T) ω) := by
    intro j hj
    have hj' := mem_range.1 hj
    simp only [termLp, hj', ↓reduceDIte]
    exact hB.coeFn_l2Integral_indicator_Ioc (hτ hj'.le hj' (Nat.le_succ j)) T
      (ha j hj') (ha₂ j hj')
  filter_upwards [Lp.coeFn_finsetSum (range n) (fun j ↦ hB.l2Integral T (termLp j)),
    (ae_ball_iff (Finset.countable_toSet _)).2 hterm_int] with ω hsum hall
  rw [hsum, Finset.sum_apply, Finance.simpleGains_def]
  exact sum_congr rfl fun j hj ↦ hall j hj

/-- If a sequence of square-integrable predictable simple strategies converges to a
Brownian-integrable `H` in `L²((timeMeasure t).prod P)`, then its elementary gains at `t` converge
in `L²(P)` to `hB.l2Integral t` of `H`. -/
theorem tendsto_eLpNorm_simpleGains_sub_l2Integral
    (hB : IsFilteredPreBrownianReal ℱ B P) (hH : BrownianIntegrable ℱ P H)
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ m, MonotoneOn (τ m) (Iic (n m)))
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j))
    (ha₂ : ∀ m j, j < n m → MemLp (a m j) 2 P) {t : ℝ≥0}
    (herr : Tendsto (fun m ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
      ((timeMeasure t).prod P)) atTop (𝓝 0)) :
    Tendsto (fun m ↦ eLpNorm
      (Finance.simpleGains (τ m) (n m) (a m) B t -
        ⇑(hB.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)))) 2 P)
      atTop (𝓝 0) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hlp_lim : Tendsto
      (fun m ↦ hB.l2Integral t
        ((Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) t).toLp
          (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))))
      atTop (𝓝 (hB.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)))) := by
    refine (hB.l2Integral t).continuous.tendsto _ |>.comp ?_
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    refine herr.congr fun m ↦ ?_
    have hpred : StronglyMeasurable[ℱ.predictable]
        (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)) - Function.uncurry H) :=
      (Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH.isStronglyPredictable
    rw [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hpred]
    rfl
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hlp_lim
  refine hlp_lim.congr fun m ↦ eLpNorm_congr_ae ?_
  exact (hB.coeFn_l2Integral_simpleHolding (hτ m) (ha m) (ha₂ m) t).sub EventuallyEq.rfl

end Probability.IsFilteredPreBrownianReal

/-! ### Identification, isometry, martingale property, and existence on `BrownianIntegrable` -/

/-- **L² characterization of `IsItoIntegral`.** For a Brownian-integrable `H`, an almost surely
continuous process `I` is an Itô integral of `H` against `B` if and only if at every horizon `t`
its evaluation `I t` agrees almost everywhere with `hB.l2Integral t` of `H`. -/
theorem BrownianIntegrable.isItoIntegral_iff_ae_eq_l2Integral
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : BrownianIntegrable ℱ P H) :
    IsItoIntegral ℱ P B H I ↔
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) ∧
      ∀ t : ℝ≥0, I t =ᵐ[P]
        hB.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ_strict, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hτ (m : ℕ) : MonotoneOn (τ m) (Iic (n m)) := (hτ_strict m).monotoneOn
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  have henergy_prob (t : ℝ≥0) (ε : ℝ≥0∞) (hε : 0 < ε) :
      Tendsto (fun m ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    let E (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
      ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t
    have hmeas (m : ℕ) : Measurable
        (fun p : ℝ≥0 × Ω ↦ ‖Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2‖ₑ ^ 2) :=
      (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
    have hE_meas (m : ℕ) : Measurable (E m) := (hmeas m).lintegral_prod_left'
    have hlint_E (m : ℕ) : ∫⁻ ω, E m ω ∂P =
        eLpNorm (fun p : ℝ≥0 × Ω ↦
          Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure t).prod P) ^ 2 := by
      rw [← lintegral_lintegral_swap (hmeas m).aemeasurable,
        ← lintegral_prod _ (hmeas m).aemeasurable]
      exact TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow (n := 2) (by decide)
        (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
          hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable
    have hlim_lint : Tendsto (fun m ↦ ∫⁻ ω, E m ω ∂P) atTop (𝓝 0) := by
      simp_rw [hlint_E]
      simpa [Function.comp_def] using ((ENNReal.continuous_pow 2).tendsto 0).comp (herr t)
    by_cases hε_top : ε = ∞
    · subst hε_top
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim_lint.eventually (eventually_lt_nhds zero_lt_one)] with m hm
      symm
      have hae_lt : ∀ᵐ ω ∂P, E m ω < ∞ :=
        ae_lt_top (hE_meas m) (hm.trans_le le_top).ne
      rw [ae_iff] at hae_lt
      exact measure_mono_null (fun ω hω ↦ not_lt_of_ge hω) hae_lt
    · have hdiv := ENNReal.Tendsto.mul_const hlim_lint (Or.inr (ENNReal.inv_ne_top.2 hε.ne'))
      rw [zero_mul] at hdiv
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
        (fun _ ↦ zero_le) fun m ↦ ?_
      simpa only [div_eq_mul_inv] using
        meas_ge_le_lintegral_div (hE_meas m).aemeasurable hε.ne' hε_top
  have hgains_inm (t : ℝ≥0) : TendstoInMeasure P
      (fun m ↦ Finance.simpleGains (τ m) (n m) (a m) B t) atTop
      (hB.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (hB.tendsto_eLpNorm_simpleGains_sub_l2Integral hH hτ ha ha₂ (herr t))
  constructor
  · intro hI
    refine ⟨hI.ae_continuous, fun t ↦ ?_⟩
    obtain ⟨n', τ', a', hτ', ha', -, henergy', hgains'⟩ := hI.exists_approx t
    exact hB.ae_eq_of_tendstoInMeasure_simpleGains hH.isStronglyPredictable
      hτ' hτ ha' ha henergy' (henergy_prob t) hgains' (hgains_inm t)
  · rintro ⟨hcont, heq⟩
    exact ⟨hH.isStronglyPredictable, hcont, fun t ↦ ⟨n, τ, a, hτ, ha,
      fun m j hj ↦ ⟨C m, hb m j hj⟩, henergy_prob t, (hgains_inm t).congr_right (heq t).symm⟩⟩

namespace IsItoIntegral

/-- At each fixed time `t`, an Itô integral of a Brownian-integrable `H` agrees almost everywhere
with `hB.l2Integral t` of `H`. -/
theorem ae_eq_l2Integral (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P B H I) (t : ℝ≥0) :
    I t =ᵐ[P] hB.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) :=
  (hH.isItoIntegral_iff_ae_eq_l2Integral hB).1 hI |>.2 t

/-- At each fixed time `t`, an Itô integral of a Brownian-integrable `H` belongs to `L²(P)`. -/
theorem memLp_two (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P B H I) (t : ℝ≥0) :
    MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hB hH t).symm

/-- Every Itô integral of a Brownian-integrable integrand has expectation zero at every time. -/
theorem integral_eq_zero (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P B H I) (t : ℝ≥0) :
    ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hB hH t)).trans (hB.integral_l2Integral t _)

/-- **Itô isometry.** The second moment of an Itô integral of a Brownian-integrable integrand `H`
at time `t` equals the expected square energy of `H` on `(0, t]`. Neither adaptedness of `I` nor
path continuity of `B` is required. -/
theorem integral_sq (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P B H I) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure t).prod P := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  let f := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  have heq := hI.ae_eq_l2Integral hB hH t
  have hnorm_lhs : ∫ ω, I t ω ^ 2 ∂P = ‖hB.l2Integral t f‖ ^ 2 := by
    have heq_sq : (fun ω ↦ I t ω ^ 2) =ᵐ[P] fun ω ↦ (hB.l2Integral t f : Ω → ℝ) ω ^ 2 := by
      filter_upwards [heq] with ω hω
      rw [hω]
    rw [integral_congr_ae heq_sq, integral_sq_lp P (hB.l2Integral t f)]
  have hpred_sq : StronglyMeasurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) :=
    hH.isStronglyPredictable.pow 2
  have hnorm_rhs : ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure t).prod P = ‖f‖ ^ 2 := by
    rw [← ℱ.integral_predictableMeasure P hpred_sq t]
    have hf_sq : (fun p ↦ (f : ℝ≥0 × Ω → ℝ) p ^ 2) =ᵐ[ℱ.predictableMeasure P t]
        fun p ↦ H p.1 p.2 ^ 2 := by
      filter_upwards [(hH.memLp_predictableMeasure t).coeFn_toLp] with p hp
      rw [hp, Function.uncurry_apply_pair]
    rw [← integral_congr_ae hf_sq,
      @integral_sq_lp (ℝ≥0 × Ω) ℱ.predictable (ℱ.predictableMeasure P t) f]
  rw [hnorm_lhs, hnorm_rhs, LinearIsometry.norm_map]

/-- Any strongly adapted Itô integral of a Brownian-integrable process is a true martingale on the
raw filtration `ℱ`. -/
theorem martingale (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P B H I)
    (hAdapt : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ_strict, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hτ (m : ℕ) : MonotoneOn (τ m) (Iic (n m)) := (hτ_strict m).monotoneOn
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  have hM (m : ℕ) : Martingale (Finance.simpleGains (τ m) (n m) (a m) B) ℱ P :=
    hB.martingale.simpleGains_of_bdd (hτ m) (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  refine martingale_of_tendsto_eLpNorm_one hM hAdapt fun t ↦ ?_
  refine TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (p := 2) one_le_two ?_
  refine (hB.tendsto_eLpNorm_simpleGains_sub_l2Integral hH hτ ha ha₂ (herr t)).congr fun m ↦
    eLpNorm_congr_ae ?_
  exact EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hB hH t).symm

end IsItoIntegral

/-- **Existence of the L² Brownian Itô integral.** When `B` has almost surely continuous paths,
every `H` in `BrownianIntegrable ℱ P H` admits a strongly predictable Itô integral `I` that is a
martingale on `ℱ`. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hB : Probability.IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ B t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P B H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ_strict, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hτ (m : ℕ) : MonotoneOn (τ m) (Iic (n m)) := (hτ_strict m).monotoneOn
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  let G (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) B
  have hM (m : ℕ) : Martingale (G m) ℱ P :=
    hB.martingale.simpleGains_of_bdd (hτ m) (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  have hGc (m : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ G m t ω) := by
    filter_upwards [hcont] with ω hω
    simp only [G, Finance.simpleGains_def]
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
      ((hω.comp (continuous_const.min continuous_id)).sub
        (hω.comp (continuous_const.min continuous_id)))
  have hG_lp (m : ℕ) (t : ℝ≥0) : MemLp (G m t) 2 P :=
    (Lp.memLp _).ae_eq (hB.coeFn_l2Integral_simpleHolding (hτ m) (ha m) (ha₂ m) t)
  have hG_tendsto (t : ℝ≥0) : Tendsto (fun m ↦ (hG_lp m t).toLp (G m t)) atTop
      (𝓝 (hB.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (hB.tendsto_eLpNorm_simpleGains_sub_l2Integral hH hτ ha ha₂ (herr t)).congr fun m ↦
      eLpNorm_congr_ae ?_
    exact ((hG_lp m t).coeFn_toLp).symm.sub EventuallyEq.rfl
  obtain ⟨I, hImart, hIpred, hIlim, -, ⟨_, -, hIpath⟩⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2) hM hGc hG_lp
      (fun t ↦ (hG_tendsto t).cauchySeq)
  have hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω) := by
    filter_upwards [hIpath] with ω hω
    exact hω.1
  refine ⟨I, (hH.isItoIntegral_iff_ae_eq_l2Integral hB).2 ⟨hIcont, fun t ↦ ?_⟩, hIpred, hImart⟩
  have hI_tendsto : Tendsto (fun m ↦ (hG_lp m t).toLp (G m t)) atTop
      (𝓝 ((hIlim t).1.toLp (I t))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    exact (hIlim t).2
  have heq_lp := tendsto_nhds_unique hI_tendsto (hG_tendsto t)
  exact ((hIlim t).1.coeFn_toLp).symm.trans (heq_lp ▸ EventuallyEq.rfl)

end TauCeti
