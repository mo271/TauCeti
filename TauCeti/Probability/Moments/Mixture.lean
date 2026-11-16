/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Integral.Bind
public import TauCeti.MeasureTheory.Function.Lp.Iterated
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Kernel.Integral

/-!
# Means and covariances of probability mixtures

A mixture's expectation is the expectation of its component means. Its covariance is the
expected component covariance plus the covariance of the component means; taking the same
observable twice gives the law of total variance. For any kernel `κ` and measurable `f`, the
slice variances `a ↦ evariance f (κ a)` and `a ↦ variance f (κ a)` are measurable without
finiteness or s-finiteness hypotheses on `κ`.

The mixing measure is a probability measure and the components need be probability measures
only almost everywhere. Finite second moments of the mixture imply the required integrability
of component means and covariances. The covariance formula applies to any pair of real
observables, including coordinates of a vector-valued law.

The integration steps use Mathlib's kernel-composition theory through
`TauCeti.MeasureTheory.Integral.Bind`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {K : α → Measure β}
  {X Y : β → ℝ}

/-- Component means of a square-integrable real observable are square-integrable under the
mixing law, even when the components are probability measures only almost everywhere. -/
theorem memLp_integral_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) (hX : MemLp X 2 (μ.bind K)) :
    MemLp (fun a ↦ ∫ x, X x ∂K a) 2 μ := by
  have hmean := hX.aestronglyMeasurable.integral_kernel_comp
    (κ := Kernel.const Unit μ) (η := ⟨K, hK⟩) (a := ())
  simp only [Kernel.coe_mk, Kernel.const_apply] at hmean
  apply (memLp_two_iff_integrable_sq hmean).mpr
  obtain ⟨hae, hsecond⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  simp only [Real.norm_eq_abs, sq_abs] at hsecond
  refine hsecond.mono' (hmean.pow 2) ?_
  filter_upwards [hprob, hae] with a hpa hXa
  have hvar := variance_nonneg X (K a)
  rw [variance_eq_sub hXa] at hvar
  simpa only [Real.norm_of_nonneg (sq_nonneg _), Pi.pow_apply] using sub_nonneg.mp hvar

/-- The component covariances of two square-integrable observables are integrable under the
mixing law. -/
theorem integrable_covariance_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    Integrable (fun a ↦ covariance X Y (K a)) μ := by
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans := (memLp_integral_bind hK hprob hX).integrable_mul
    (memLp_integral_bind hK hprob hY)
  simp only [Pi.mul_apply] at hprod hmeans
  refine (hprod.sub hmeans).congr ?_
  obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  obtain ⟨hYae, _⟩ := (Measure.memLp_two_bind_iff hK hY.aestronglyMeasurable).mp hY
  filter_upwards [hprob, hXae, hYae] with a hpa hXa hYa
  exact (covariance_eq_sub hXa hYa).symm

variable [IsProbabilityMeasure μ]

/-- **Law of total covariance**: a probability mixture's covariance is the sum of the expected
component covariance and the covariance of component means. -/
theorem covariance_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    covariance X Y (μ.bind K) =
      (∫ a, covariance X Y (K a) ∂μ) +
        covariance (fun a ↦ ∫ x, X x ∂K a) (fun a ↦ ∫ x, Y x ∂K a) μ := by
  have : IsProbabilityMeasure (μ.bind K) := isProbabilityMeasure_bind hK.aemeasurable hprob
  have hmX := memLp_integral_bind hK hprob hX
  have hmY := memLp_integral_bind hK hprob hY
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans : Integrable (fun a ↦ (∫ x, X x ∂K a) * ∫ x, Y x ∂K a) μ :=
    hmX.integrable_mul hmY
  have hcov : (fun a ↦ covariance X Y (K a)) =ᵐ[μ]
      (fun a ↦ (∫ x, X x * Y x ∂K a) - (∫ x, X x ∂K a) * ∫ x, Y x ∂K a) := by
    obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
    obtain ⟨hYae, _⟩ := (Measure.memLp_two_bind_iff hK hY.aestronglyMeasurable).mp hY
    filter_upwards [hprob, hXae, hYae] with a hpa hXa hYa
    exact covariance_eq_sub hXa hYa
  rw [covariance_eq_sub hX hY, covariance_eq_sub hmX hmY,
    integral_congr_ae hcov]
  simp only [Pi.mul_apply] at hprod hmeans ⊢
  have hXY : (∫ x, X x * Y x ∂μ.bind K) = ∫ a, ∫ x, X x * Y x ∂K a ∂μ :=
    Measure.integral_bind hK.aemeasurable (hX.integrable_mul hY)
  rw [integral_sub hprod hmeans, hXY,
    Measure.integral_bind hK.aemeasurable (hX.integrable one_le_two),
    Measure.integral_bind hK.aemeasurable (hY.integrable one_le_two)]
  ring

/-- **Law of total variance**: a probability mixture's variance is its expected component
variance plus the variance of the component means. -/
theorem variance_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) (hX : MemLp X 2 (μ.bind K)) :
    variance X (μ.bind K) = (∫ a, variance X (K a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂K a) μ := by
  have hae := hX.aestronglyMeasurable.comp (κ := Kernel.const Unit μ) (η := ⟨K, hK⟩) (a := ())
  simp only [Kernel.coe_mk, Kernel.const_apply] at hae
  rw [← covariance_self hX.aestronglyMeasurable.aemeasurable, covariance_bind hK hprob hX hX,
    covariance_self (memLp_integral_bind hK hprob hX).aestronglyMeasurable.aemeasurable]
  congr 1
  exact integral_congr_ae (hae.mono fun a ha ↦ covariance_self ha.aemeasurable)

variable {π : Measure β} [IsProbabilityMeasure π] {F : α × β → ℝ}

/-- The law of total variance on a product of probability spaces: the variance of a square
integrable `F` splits into the average of the variances in the second coordinate and the variance
of the average over the second coordinate. -/
theorem evariance_prod_eq (hL : MemLp F 2 (μ.prod π)) :
    evariance F (μ.prod π) = ∫⁻ a, evariance (fun w => F (a, w)) π ∂μ +
      evariance (fun a => ∫ w, F (a, w) ∂π) μ := by
  let K : α → Measure (α × β) := fun a => π.map (Prod.mk a)
  have hK : Measurable K := Measurable.map_prodMk_left
  have hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a) :=
    .of_forall fun _ => inferInstance
  have hbind : μ.bind K = μ.prod π := (Measure.prod_eq_of_sfinite μ π).symm
  have hX : MemLp F 2 (μ.bind K) := hbind ▸ hL
  have hslice : ∀ᵐ a ∂μ, variance F (K a) = variance (fun w => F (a, w)) π ∧
      ∫ x, F x ∂K a = ∫ w, F (a, w) ∂π ∧ MemLp (fun w => F (a, w)) 2 π := by
    filter_upwards [(Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX |>.1,
      hL.ae_memLp_prod_right] with a ha hsl
    have hm : AEMeasurable F (K a) := ha.aestronglyMeasurable.aemeasurable
    have hmp : AEMeasurable (Prod.mk a) π := measurable_prodMk_left.aemeasurable
    exact ⟨variance_map hm hmp, integral_map hmp ha.aestronglyMeasurable, hsl⟩
  have hmean : MemLp (fun a => ∫ w, F (a, w) ∂π) 2 μ :=
    (memLp_integral_bind hK hprob hX).ae_eq (hslice.mono fun a ha => ha.2.1)
  have hvarint : Integrable (fun a => variance (fun w => F (a, w)) π) μ := by
    refine (integrable_covariance_bind hK hprob hX hX).congr ?_
    filter_upwards [(Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX |>.1,
      hslice] with a ha hs
    rw [covariance_self ha.aestronglyMeasurable.aemeasurable, hs.1]
  have hlint : ∫⁻ a, evariance (fun w => F (a, w)) π ∂μ =
      ENNReal.ofReal (∫ a, variance (fun w => F (a, w)) π ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hvarint
      (Filter.Eventually.of_forall fun a => variance_nonneg _ _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hslice] with a ha
    exact (ofReal_variance ha.2.2).symm
  have hvar := variance_bind hK hprob hX
  rw [hbind] at hvar
  rw [hlint, ← ofReal_variance hmean, ← ofReal_variance hL,
    ← ENNReal.ofReal_add (integral_nonneg fun a => variance_nonneg _ _) (variance_nonneg _ _),
    hvar, integral_congr_ae (hslice.mono fun a ha => ha.1),
    variance_congr (hslice.mono fun a ha => ha.2.1)]

end TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} [IsProbabilityMeasure μ] {X Y : β → ℝ}

/-- The law of total covariance for the composition of a probability measure and a Markov
kernel. -/
theorem covariance_comp (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : MemLp X 2 (κ ∘ₘ μ)) (hY : MemLp Y 2 (κ ∘ₘ μ)) :
    covariance X Y (κ ∘ₘ μ) = (∫ a, covariance X Y (κ a) ∂μ) +
      covariance (fun a ↦ ∫ x, X x ∂κ a) (fun a ↦ ∫ x, Y x ∂κ a) μ := by
  exact TauCeti.Probability.covariance_bind κ.measurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX hY

/-- The law of total variance for the composition of a probability measure and a Markov
kernel. -/
theorem variance_comp (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : MemLp X 2 (κ ∘ₘ μ)) :
    variance X (κ ∘ₘ μ) = (∫ a, variance X (κ a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂κ a) μ := by
  exact TauCeti.Probability.variance_bind κ.measurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX

end ProbabilityTheory.Kernel

section MeasurableVariance

open scoped ENNReal

/-- On an infinite-measure space, any real function with nonzero Bochner integral has infinite
extended variance. -/
theorem ProbabilityTheory.evariance_eq_top_of_measure_univ_eq_top {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hμ : μ Set.univ = ∞) (hm : μ[f] ≠ 0) :
    evariance f μ = ∞ := by
  have hfi : Integrable f μ := by
    by_contra hni
    exact hm (integral_undef hni)
  set g : Ω → ℝ := hfi.1.mk f
  have hfg : f =ᵐ[μ] g := hfi.1.ae_eq_mk
  have hg : Measurable g := hfi.1.stronglyMeasurable_mk.measurable
  have hgi : Integrable g μ := hfi.congr hfg
  have hmg : μ[g] = μ[f] := integral_congr_ae hfg.symm
  rw [evariance_congr hfg]
  set c : ℝ := |μ[g]| / 2
  have hc : 0 < c := half_pos (abs_pos.2 (hmg ▸ hm))
  have hr0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  set A : Set Ω := {ω | ENNReal.ofReal c ≤ ‖g ω‖ₑ}
  set B : Set Ω := {ω | ‖g ω‖ₑ < ENNReal.ofReal c}
  have hB_meas : MeasurableSet B := measurableSet_lt hg.stronglyMeasurable.eNorm measurable_const
  have hmarkov : ENNReal.ofReal c * μ A ≤ ∫⁻ ω, ‖g ω‖ₑ ∂μ :=
    mul_meas_ge_le_lintegral₀ hg.stronglyMeasurable.eNorm.aemeasurable _
  have hA_ne_top : μ A ≠ ∞ := by
    intro htop
    exact hgi.2.ne (top_unique <| (ENNReal.mul_top hr0) ▸ htop ▸ hmarkov)
  have hB_top : μ B = ∞ := by
    have huniv : ∞ ≤ μ A + μ B := by
      calc ∞ = μ Set.univ := hμ.symm
        _ ≤ μ (A ∪ B) := measure_mono fun ω _ ↦ le_or_gt (ENNReal.ofReal c) ‖g ω‖ₑ
        _ ≤ μ A + μ B := measure_union_le A B
    rcases eq_or_ne (μ B) ∞ with hB | hB
    · exact hB
    · exact absurd (top_unique huniv) (ENNReal.add_ne_top.2 ⟨hA_ne_top, hB⟩)
  refine top_unique ?_
  calc ∞ = ENNReal.ofReal c ^ 2 * μ B := by rw [hB_top, ENNReal.mul_top (pow_ne_zero 2 hr0)]
    _ = ∫⁻ _ in B, ENNReal.ofReal c ^ 2 ∂μ := by simp
    _ ≤ ∫⁻ ω in B, ‖g ω - μ[g]‖ₑ ^ 2 ∂μ := by
      refine setLIntegral_mono' hB_meas fun ω hω ↦ ?_
      have hlt : |g ω| < c := by
        rwa [← ENNReal.ofReal_lt_ofReal_iff hc, ← Real.eNorm_eq_ofReal_abs]
      have hge : c ≤ |g ω - μ[g]| := by
        have := abs_sub_abs_le_abs_sub (μ[g]) (g ω)
        rw [abs_sub_comm] at this
        linarith [show c = |μ[g]| / 2 from rfl]
      gcongr
      rw [Real.eNorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal hge
    _ ≤ evariance g μ := lintegral_mono' Measure.restrict_le_self le_rfl

/-- For any kernel `κ` and measurable real function `f`, `a ↦ evariance f (κ a)` is measurable. -/
@[fun_prop]
theorem Measurable.evariance_kernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {κ : Kernel α β} {f : β → ℝ} (hf : Measurable f) :
    Measurable fun a ↦ evariance f (κ a) := by
  classical
  set m : α → ℝ := fun a ↦ ∫ b, f b ∂κ a
  have hm : Measurable m := hf.stronglyMeasurable.integral_kernel.measurable
  have hS : MeasurableSet {a | κ a Set.univ = ∞} :=
    measurableSet_eq_fun (κ.measurable_coe .univ) measurable_const
  have hZ : MeasurableSet {a | m a = 0} := measurableSet_eq_fun hm measurable_const
  have hfin : Measurable fun a ↦
      (1 + κ a Set.univ) * ∫⁻ b, ‖f b - m a‖ₑ ^ 2 ∂κ.normalize a := by
    refine (measurable_const.add (κ.measurable_coe .univ)).mul ?_
    exact ((((hf.comp measurable_snd).sub
      (hm.comp measurable_fst)).stronglyMeasurable.eNorm).pow_const 2).lintegral_kernel_prod_right'
  have hzero : Measurable fun a ↦ ∫⁻ b, ‖f b‖ₑ ^ 2 ∂κ a :=
    (hf.stronglyMeasurable.eNorm.pow_const 2).lintegral_kernel
  have hpiece : Measurable (Set.piecewise {a | κ a Set.univ = ∞}
      (Set.piecewise {a | m a = 0} (fun a ↦ ∫⁻ b, ‖f b‖ₑ ^ 2 ∂κ a) fun _ ↦ ∞)
      (fun a ↦ (1 + κ a Set.univ) * ∫⁻ b, ‖f b - m a‖ₑ ^ 2 ∂κ.normalize a)) :=
    Measurable.piecewise hS (Measurable.piecewise hZ hzero measurable_const) hfin
  convert hpiece using 1
  ext a
  by_cases ha : κ a Set.univ = ∞
  · by_cases hma : m a = 0
    · simp [Set.piecewise, ha, hma, evariance, m]
    · simp [Set.piecewise, ha, hma, evariance_eq_top_of_measure_univ_eq_top ha hma]
  · simp only [Set.piecewise, Set.mem_ofPred_eq, ha, ↓reduceIte]
    exact κ.lintegral_eq_mul_normalize ha _

/-- For any kernel `κ` and measurable real function `f`, `a ↦ variance f (κ a)` is measurable. -/
@[fun_prop]
theorem Measurable.variance_kernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {κ : Kernel α β} {f : β → ℝ} (hf : Measurable f) :
    Measurable fun a ↦ variance f (κ a) :=
  (hf.evariance_kernel (κ := κ)).ennreal_toReal

end MeasurableVariance
