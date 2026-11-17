/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.WithDensity
public import TauCeti.Statistics.ExponentialFamily.Basic

import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Conditional exponential families

For a kernel `κ : Kernel F E` into a real inner product space `E`, this file defines its fibrewise
normalized exponential tilt `TauCeti.conditionalExponentialKernel κ η` and establishes the
conditioning theorem for natural exponential families:

* `TauCeti.conditionalExponentialKernel`: the s-finite kernel
  `s ↦ exp (⟪η, t⟫ - log ∫ exp ⟪η, t'⟫ dκ s) · κ s`.
* `TauCeti.tilted_compProd_eq_fst_compProd_conditionalExponentialKernel` and
  `TauCeti.tilted_compProd_eq_tilted_compProd_conditionalExponentialKernel`: an exponential tilt of
  a composition product `μ ⊗ₘ κ` decomposes as its tilted first marginal composed with
  `conditionalExponentialKernel κ η`.
* `TauCeti.exists_kernel_conditional_exponential_family`: for a natural exponential family with
  pair statistic `(T, S)` (encoded in `WithLp 2 (E × F)`), there is a single parameter-free
  s-finite kernel `κ : Kernel F E` such that at every natural parameter `p = (η, ζ)`, the
  conditional law of `T` given `S` is `conditionalExponentialKernel κ η`, depending only on `η`.

This follows Lawrence D. Brown, *Fundamentals of Statistical Exponential Families* (IMS Lecture
Notes–Monograph Series, Vol. 9, 1986, Chapter 1, Theorem 1.15).
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

section KernelDefs

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [MeasurableSpace F]

/-- The fibrewise normalized exponential tilt of an s-finite kernel `κ : Kernel F E` by a natural
parameter `η : E`: on each fibre `s`, it tilts `κ s` by the density
`t ↦ exp (⟪η, t⟫ - log ∫ exp ⟪η, t'⟫ dκ s)`. -/
noncomputable def conditionalExponentialKernel (κ : Kernel F E) [IsSFiniteKernel κ] (η : E) :
    Kernel F E :=
  κ.withDensity fun s t ↦ ENNReal.ofReal
    (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ η t') ∂κ s)))

theorem conditionalExponentialKernel_def (κ : Kernel F E) [IsSFiniteKernel κ] (η : E) :
    conditionalExponentialKernel κ η =
      κ.withDensity fun s t ↦ ENNReal.ofReal
        (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ η t') ∂κ s))) := by
  rfl

instance isSFiniteKernel_conditionalExponentialKernel (κ : Kernel F E) [IsSFiniteKernel κ]
    (η : E) : IsSFiniteKernel (conditionalExponentialKernel κ η) :=
  Kernel.IsSFiniteKernel.withDensity κ fun _ _ ↦ ENNReal.ofReal_ne_top

@[simp]
theorem conditionalExponentialKernel_zero_kernel (η : E) :
    conditionalExponentialKernel (0 : Kernel F E) η = 0 := by
  rw [conditionalExponentialKernel_def]
  by_cases hmeas : Measurable (Function.uncurry fun s t ↦ ENNReal.ofReal
      (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ η t') ∂(0 : Kernel F E) s))))
  · ext s
    rw [Kernel.withDensity_apply _ hmeas]
    simp
  · exact Kernel.withDensity_of_not_measurable _ hmeas

variable [OpensMeasurableSpace E]

/-- Measurability of the fibrewise normalizing integral `s ↦ ∫ exp ⟪η, t'⟫ dκ s`. -/
private lemma measurable_integral_exp_inner_kernel (κ : Kernel F E) [IsSFiniteKernel κ] (η : E) :
    Measurable fun s : F ↦ ∫ t', Real.exp (inner ℝ η t') ∂κ s := by
  have hinner : Measurable fun t : E ↦ inner ℝ η t :=
    (continuous_const.inner continuous_id).measurable
  have hprod : StronglyMeasurable fun p : F × E ↦ Real.exp (inner ℝ η p.2) :=
    ((Real.measurable_exp.comp hinner).comp measurable_snd).stronglyMeasurable
  exact hprod.integral_kernel_prod_right'.measurable

/-- Joint measurability of the density defining `conditionalExponentialKernel κ η`. -/
private lemma measurable_conditionalExponentialKernel_density (κ : Kernel F E) [IsSFiniteKernel κ]
    (η : E) :
    Measurable (Function.uncurry fun s t ↦ ENNReal.ofReal
      (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ η t') ∂κ s)))) := by
  have hinner : Measurable fun t : E ↦ inner ℝ η t :=
    (continuous_const.inner continuous_id).measurable
  have hlog : Measurable fun s : F ↦ Real.log (∫ t', Real.exp (inner ℝ η t') ∂κ s) :=
    Real.measurable_log.comp (measurable_integral_exp_inner_kernel κ η)
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp ((hinner.comp measurable_snd).sub (hlog.comp measurable_fst)))

theorem conditionalExponentialKernel_apply (κ : Kernel F E) [IsSFiniteKernel κ] (η : E) (s : F) :
    conditionalExponentialKernel κ η s = (κ s).withDensity fun t ↦ ENNReal.ofReal
      (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ η t') ∂κ s))) :=
  Kernel.withDensity_apply κ (measurable_conditionalExponentialKernel_density κ η) s

/-- On every fibre `s` where `t ↦ exp ⟪η, t⟫` is `κ s`-integrable,
`conditionalExponentialKernel κ η s` agrees with the exponential tilt `(κ s).tilted ⟪η, ·⟫`. -/
theorem conditionalExponentialKernel_apply_eq_tilted {κ : Kernel F E} [IsSFiniteKernel κ] {η : E}
    {s : F} (hint : Integrable (fun t ↦ Real.exp (inner ℝ η t)) (κ s)) :
    conditionalExponentialKernel κ η s = (κ s).tilted (fun t ↦ inner ℝ η t) := by
  rw [conditionalExponentialKernel_apply]
  rcases eq_zero_or_neZero (κ s) with h0 | hne
  · simp [h0]
  · have hpos : 0 < ∫ t', Real.exp (inner ℝ η t') ∂κ s := integral_exp_pos hint
    rw [Measure.tilted]
    congr 1
    ext t
    rw [Real.exp_sub, Real.exp_log hpos]

@[simp]
theorem conditionalExponentialKernel_zero (κ : Kernel F E) [IsMarkovKernel κ] :
    conditionalExponentialKernel κ 0 = κ := by
  ext s
  rw [conditionalExponentialKernel_apply]
  simp

/-- Tilting a kernel `κ` first by an unnormalized exponential density `exp (-⟪η₀, t⟫)` and then
taking `conditionalExponentialKernel · η` shifts the natural parameter by `-η₀`. -/
private lemma conditionalExponentialKernel_withDensity_exp_neg (κ : Kernel F E) [IsSFiniteKernel κ]
    (η₀ η : E)
    [IsSFiniteKernel (κ.withDensity fun _ t ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₀ t)))] :
    conditionalExponentialKernel
      (κ.withDensity fun _ t ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₀ t))) η =
      conditionalExponentialKernel κ (η - η₀) := by
  have hinner_meas : Measurable fun t : E ↦ inner ℝ η₀ t :=
    (continuous_const.inner continuous_id).measurable
  have hneg_meas : Measurable (Function.uncurry fun (_ : F) (t : E) ↦
      ENNReal.ofReal (Real.exp (-inner ℝ η₀ t))) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hinner_meas.neg)).comp measurable_snd
  let f : F → E → ℝ≥0 := fun _ t ↦ ⟨Real.exp (-inner ℝ η₀ t), (Real.exp_pos _).le⟩
  have hf_meas : Measurable (Function.uncurry f) :=
    ((Real.measurable_exp.comp hinner_meas.neg).comp measurable_snd).subtype_mk
  have hfun : (fun (_ : F) (t : E) ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₀ t))) =
      fun s t ↦ (f s t : ℝ≥0∞) := by
    funext _ t
    exact ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le
  have hint_eq : ∀ s : F,
      (∫ t', Real.exp (inner ℝ η t') ∂(κ s).withDensity fun t ↦
          ENNReal.ofReal (Real.exp (-inner ℝ η₀ t))) =
        ∫ t', Real.exp (inner ℝ (η - η₀) t') ∂κ s := by
    intro s
    rw [← Kernel.withDensity_apply _ hneg_meas, hfun, Kernel.integral_withDensity hf_meas]
    refine integral_congr_ae (ae_of_all _ fun t' ↦ ?_)
    dsimp only
    have hf_coe : (f s t' : ℝ) = Real.exp (-inner ℝ η₀ t') := rfl
    rw [NNReal.smul_def, smul_eq_mul, hf_coe, ← Real.exp_add, inner_sub_left]
    ring_nf
  ext s : 1
  rw [conditionalExponentialKernel_apply, conditionalExponentialKernel_apply,
    Kernel.withDensity_apply _ hneg_meas, ← withDensity_mul]
  · congr 1
    funext t
    rw [Pi.mul_apply, hint_eq s, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      inner_sub_left]
    ring_nf
  · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hinner_meas.neg)
  · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((continuous_const.inner continuous_id).measurable.sub measurable_const))

end KernelDefs

section CompProdTilt

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [MeasurableSpace F]

/-- Auxiliary calculation of the first marginal of an exponential tilt of `μ ⊗ₘ κ`. -/
private lemma fst_tilted_compProd_eq_withDensity {μ : Measure F} [SFinite μ]
    {κ : Kernel F E} [IsSFiniteKernel κ] {g : F → ℝ} (hg : Measurable g) {η : E}
    (hint : Integrable (fun p : F × E ↦ Real.exp (g p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ)) :
    ((μ ⊗ₘ κ).tilted (fun p ↦ g p.1 + inner ℝ η p.2)).fst =
      μ.withDensity fun s ↦ ENNReal.ofReal (Real.exp (g s) *
        (∫ t, Real.exp (inner ℝ η t) ∂κ s) /
          ∫ p, Real.exp (g p.1 + inner ℝ η p.2) ∂(μ ⊗ₘ κ)) := by
  let C : ℝ := ∫ p, Real.exp (g p.1 + inner ℝ η p.2) ∂(μ ⊗ₘ κ)
  have hinner : Measurable fun t : E ↦ inner ℝ η t :=
    (continuous_const.inner continuous_id).measurable
  have hdens_meas : Measurable fun p : F × E ↦
      ENNReal.ofReal (Real.exp (g p.1 + inner ℝ η p.2) / C) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp
        ((hg.comp measurable_fst).add (hinner.comp measurable_snd))).div_const C)
  have hae_int : ∀ᵐ s ∂μ, Integrable (fun t ↦ Real.exp (g s + inner ℝ η t)) (κ s) :=
    ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint).1
  ext A hA
  rw [Measure.fst_apply hA, ← Set.prod_univ, tilted_apply' _ _ (hA.prod MeasurableSet.univ),
    withDensity_apply _ hA, ← lintegral_indicator (hA.prod MeasurableSet.univ),
    Measure.lintegral_compProd (hdens_meas.indicator (hA.prod MeasurableSet.univ))]
  have hset : (∫⁻ s, ∫⁻ t, (A ×ˢ Set.univ).indicator
        (fun p : F × E ↦ ENNReal.ofReal (Real.exp (g p.1 + inner ℝ η p.2) / C)) (s, t) ∂κ s ∂μ) =
      ∫⁻ s in A, ∫⁻ t, ENNReal.ofReal (Real.exp (g s + inner ℝ η t) / C) ∂κ s ∂μ := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ A <;> simp [hs]
  rw [hset]
  refine setLIntegral_congr_fun_ae hA ?_
  filter_upwards [hae_int] with s hs _
  have hC0 : 0 ≤ C := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal (hs.div_const C)
    (ae_of_all _ fun _ ↦ div_nonneg (Real.exp_pos _).le hC0)]
  congr 1
  have heq : (fun t : E ↦ Real.exp (g s + inner ℝ η t) / C) =
      fun t : E ↦ (Real.exp (g s) / C) * Real.exp (inner ℝ η t) := by
    ext t
    rw [Real.exp_add]
    ring
  rw [heq, integral_const_mul]
  ring

/-- Under `hint : Integrable (fun p ↦ exp (g p.1 + ⟪η, p.2⟫)) (μ ⊗ₘ κ)`, the fibre normalizing
integral `∫ exp ⟪η, t⟫ dκ s` is strictly positive for `(μ ⊗ₘ κ)`-a.e. `(s, t)`. -/
private lemma ae_compProd_integral_exp_inner_pos {μ : Measure F} [SFinite μ]
    {κ : Kernel F E} [IsSFiniteKernel κ] {g : F → ℝ} {η : E}
    (hint : Integrable (fun p : F × E ↦ Real.exp (g p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ)) :
    ∀ᵐ p ∂(μ ⊗ₘ κ), 0 < ∫ t, Real.exp (inner ℝ η t) ∂κ p.1 := by
  let Z : F → ℝ := fun s ↦ ∫ t, Real.exp (inner ℝ η t) ∂κ s
  have hZ_meas : Measurable Z := measurable_integral_exp_inner_kernel κ η
  have hae_int : ∀ᵐ s ∂μ, Integrable (fun t ↦ Real.exp (g s + inner ℝ η t)) (κ s) :=
    ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint).1
  have hae_int_η : ∀ᵐ s ∂μ, Integrable (fun t ↦ Real.exp (inner ℝ η t)) (κ s) := by
    filter_upwards [hae_int] with s hs
    refine (hs.const_mul (Real.exp (-g s))).congr (ae_of_all _ fun t ↦ ?_)
    dsimp only
    rw [← Real.exp_add]
    ring_nf
  let B : Set F := {s : F | ¬ 0 < Z s}
  have hB : MeasurableSet B := (measurableSet_lt measurable_const hZ_meas).compl
  rw [ae_iff]
  have hset : {p : F × E | ¬ 0 < Z p.1} = B ×ˢ Set.univ := by
    ext ⟨s, t⟩
    simp [B]
  rw [hset, Measure.compProd_apply_prod hB MeasurableSet.univ]
  have hae_zero : ∀ᵐ s ∂μ.restrict B, κ s Set.univ = 0 := by
    filter_upwards [ae_restrict_of_ae hae_int_η, ae_restrict_mem hB] with s hs_int hsB
    rcases eq_zero_or_neZero (κ s) with h0 | hne
    · simp [h0]
    · exact absurd (integral_exp_pos hs_int) hsB
  rw [lintegral_congr_ae hae_zero, lintegral_zero]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [OpensMeasurableSpace E] in
/-- Restricting `μ` to the fibres `{s | κ s Set.univ ≠ 0}` does not change `μ ⊗ₘ κ`. -/
private lemma compProd_restrict_ne_zero (μ : Measure F) [SFinite μ] (κ : Kernel F E)
    [IsSFiniteKernel κ] :
    μ.restrict {s | κ s Set.univ ≠ 0} ⊗ₘ κ = μ ⊗ₘ κ := by
  have hS : MeasurableSet {s : F | κ s Set.univ ≠ 0} :=
    (Kernel.measurable_coe κ MeasurableSet.univ (measurableSet_singleton 0)).compl
  ext A hA
  rw [Measure.compProd_apply hA, Measure.compProd_apply hA, ← lintegral_indicator hS]
  refine lintegral_congr fun s ↦ ?_
  by_cases hs : κ s = 0 <;> simp [hs]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [OpensMeasurableSpace E] in
/-- Lifting a `μ`-a.e. equality of functions on `F` to the first coordinate under `μ ⊗ₘ κ`
without assuming measurability of `g` or `g'`. -/
private lemma ae_compProd_fst_eq_of_ae_eq {μ : Measure F} (κ : Kernel F E)
    {g g' : F → ℝ} (h : g =ᵐ[μ] g') :
    (fun p : F × E ↦ g p.1) =ᵐ[μ ⊗ₘ κ] fun p ↦ g' p.1 := by
  obtain ⟨N, hN_sub, hN_meas, hN_zero⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  have hae_N : ∀ᵐ s ∂μ, s ∉ N := ae_iff.mpr (by simpa using hN_zero)
  filter_upwards [Measure.ae_compProd_of_ae_fst κ hN_meas.compl hae_N] with p hp
  by_contra hne
  exact hp (hN_sub hne)

/-- Integrability of `exp (g s + ⟪η, t⟫)` under `μ ⊗ₘ κ` forces `g` to be a.e.-measurable on the
set `{s | κ s Set.univ ≠ 0}` of non-degenerate fibres. -/
private lemma aemeasurable_of_integrable_exp_add_compProd {μ : Measure F} [SFinite μ]
    {κ : Kernel F E} [IsSFiniteKernel κ] {g : F → ℝ} {η : E}
    (hint : Integrable (fun p : F × E ↦ Real.exp (g p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ)) :
    AEMeasurable g (μ.restrict {s | κ s Set.univ ≠ 0}) := by
  let S : Set F := {s : F | κ s Set.univ ≠ 0}
  have hS : MeasurableSet S :=
    (Kernel.measurable_coe κ MeasurableSet.univ (measurableSet_singleton 0)).compl
  let f : F × E → ℝ := hint.aestronglyMeasurable.mk _
  have hf_ae : ∀ᵐ s ∂μ, (fun t ↦ Real.exp (g s + inner ℝ η t)) =ᵐ[κ s] fun t ↦ f (s, t) :=
    Measure.ae_ae_of_ae_compProd hint.aestronglyMeasurable.ae_eq_mk
  have hae_int : ∀ᵐ s ∂μ, Integrable (fun t ↦ Real.exp (g s + inner ℝ η t)) (κ s) :=
    ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint).1
  let Z : F → ℝ := fun s ↦ ∫ t, Real.exp (inner ℝ η t) ∂κ s
  let I : F → ℝ := fun s ↦ ∫ t, f (s, t) ∂κ s
  have hI_meas : Measurable I :=
    hint.aestronglyMeasurable.stronglyMeasurable_mk.integral_kernel_prod_right'.measurable
  have hh_meas : Measurable fun s ↦ Real.log (I s / Z s) :=
    Real.measurable_log.comp (hI_meas.div (measurable_integral_exp_inner_kernel κ η))
  refine hh_meas.aemeasurable.congr ?_
  filter_upwards [ae_restrict_of_ae hf_ae, ae_restrict_of_ae hae_int, ae_restrict_mem hS]
    with s hfs hs_int hsS
  have : NeZero (κ s) := ⟨fun h0 ↦ hsS (by simp [h0])⟩
  have hint_η : Integrable (fun t ↦ Real.exp (inner ℝ η t)) (κ s) := by
    refine (hs_int.const_mul (Real.exp (-g s))).congr (ae_of_all _ fun t ↦ ?_)
    dsimp only
    rw [← Real.exp_add]
    ring_nf
  have hZpos : 0 < Z s := integral_exp_pos hint_η
  have hI_eq : I s = Real.exp (g s) * Z s := by
    dsimp only [I, Z]
    rw [integral_congr_ae hfs.symm]
    have heq : (fun t : E ↦ Real.exp (g s + inner ℝ η t)) =
        fun t : E ↦ Real.exp (g s) * Real.exp (inner ℝ η t) := by
      ext t; exact Real.exp_add _ _
    rw [heq, integral_const_mul]
  rw [hI_eq, mul_div_cancel_right₀ _ hZpos.ne', Real.log_exp]

/-- Product tilting decomposition for a measurable function `g : F → ℝ`. -/
private lemma tilted_compProd_eq_fst_compProd_conditionalExponentialKernel_of_measurable
    {μ : Measure F} [SFinite μ] {κ : Kernel F E} [IsSFiniteKernel κ] {g : F → ℝ}
    (hg : Measurable g) {η : E}
    (hint : Integrable (fun p : F × E ↦ Real.exp (g p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ)) :
    (μ ⊗ₘ κ).tilted (fun p ↦ g p.1 + inner ℝ η p.2) =
      ((μ ⊗ₘ κ).tilted (fun p ↦ g p.1 + inner ℝ η p.2)).fst ⊗ₘ
        conditionalExponentialKernel κ η := by
  let C : ℝ := ∫ p, Real.exp (g p.1 + inner ℝ η p.2) ∂(μ ⊗ₘ κ)
  let Z : F → ℝ := fun s ↦ ∫ t, Real.exp (inner ℝ η t) ∂κ s
  have hZ_meas : Measurable Z := measurable_integral_exp_inner_kernel κ η
  have hfst_meas : Measurable fun s : F ↦ ENNReal.ofReal (Real.exp (g s) * Z s / C) :=
    ENNReal.measurable_ofReal.comp (((Real.measurable_exp.comp hg).mul hZ_meas).div_const C)
  have : IsSFiniteKernel (κ.withDensity fun s t ↦ ENNReal.ofReal
      (Real.exp (inner ℝ η t - Real.log (Z s)))) :=
    Kernel.IsSFiniteKernel.withDensity κ fun _ _ ↦ ENNReal.ofReal_ne_top
  rw [fst_tilted_compProd_eq_withDensity hg hint, conditionalExponentialKernel_def,
    Measure.withDensity_compProd_withDensity hfst_meas
      (measurable_conditionalExponentialKernel_density κ η), Measure.tilted]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_compProd_integral_exp_inner_pos hint] with p hp
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.exp_sub, Real.exp_log hp, Real.exp_add]
  have hpne : (∫ t, Real.exp (inner ℝ η t) ∂κ p.1) ≠ 0 := hp.ne'
  dsimp only [Z, C]
  field_simp [hpne]

/-- **Product tilting decomposition.** An exponential tilt of `μ ⊗ₘ κ` by `g s + ⟪η, t⟫` equals its
tilted first marginal composed with `conditionalExponentialKernel κ η`. -/
theorem tilted_compProd_eq_fst_compProd_conditionalExponentialKernel {μ : Measure F} [SFinite μ]
    {κ : Kernel F E} [IsSFiniteKernel κ] {g : F → ℝ} {η : E}
    (hint : Integrable (fun p : F × E ↦ Real.exp (g p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ)) :
    (μ ⊗ₘ κ).tilted (fun p ↦ g p.1 + inner ℝ η p.2) =
      ((μ ⊗ₘ κ).tilted (fun p ↦ g p.1 + inner ℝ η p.2)).fst ⊗ₘ
        conditionalExponentialKernel κ η := by
  let μ' : Measure F := μ.restrict {s | κ s Set.univ ≠ 0}
  have hμ' : μ' ⊗ₘ κ = μ ⊗ₘ κ := compProd_restrict_ne_zero μ κ
  have hg_ae : AEMeasurable g μ' := aemeasurable_of_integrable_exp_add_compProd hint
  let g' : F → ℝ := hg_ae.mk g
  have hprod_ae : (fun p : F × E ↦ g p.1 + inner ℝ η p.2) =ᵐ[μ' ⊗ₘ κ]
      fun p ↦ g' p.1 + inner ℝ η p.2 :=
    (ae_compProd_fst_eq_of_ae_eq κ hg_ae.ae_eq_mk).mono fun p hp ↦ by simp [g', hp]
  have hint' : Integrable (fun p : F × E ↦ Real.exp (g' p.1 + inner ℝ η p.2)) (μ' ⊗ₘ κ) :=
    (hμ'.symm ▸ hint).congr (hprod_ae.mono fun p hp ↦ by simp [hp])
  rw [← hμ', tilted_congr hprod_ae]
  exact tilted_compProd_eq_fst_compProd_conditionalExponentialKernel_of_measurable
    hg_ae.measurable_mk hint'

/-- Tilted-marginal decomposition for a measurable function `g : F → ℝ`. -/
private lemma tilted_compProd_eq_tilted_compProd_conditionalExponentialKernel_of_measurable
    {μ : Measure F} [SFinite μ] {κ : Kernel F E} [IsSFiniteKernel κ] (hκ : ∀ᵐ s ∂μ, κ s ≠ 0)
    {g : F → ℝ} (hg : Measurable g) {η : E}
    (hint : Integrable (fun p : F × E ↦ Real.exp (g p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ)) :
    (μ ⊗ₘ κ).tilted (fun p ↦ g p.1 + inner ℝ η p.2) =
      (μ.tilted fun s ↦ g s + Real.log (∫ t, Real.exp (inner ℝ η t) ∂κ s)) ⊗ₘ
        conditionalExponentialKernel κ η := by
  let Z : F → ℝ := fun s ↦ ∫ t, Real.exp (inner ℝ η t) ∂κ s
  have hae_int : ∀ᵐ s ∂μ, Integrable (fun t ↦ Real.exp (g s + inner ℝ η t)) (κ s) :=
    ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint).1
  have hae_Zpos : ∀ᵐ s ∂μ, 0 < Z s := by
    filter_upwards [hae_int, hκ] with s hs hκs
    have : NeZero (κ s) := ⟨hκs⟩
    have hint_η : Integrable (fun t ↦ Real.exp (inner ℝ η t)) (κ s) := by
      refine (hs.const_mul (Real.exp (-g s))).congr (ae_of_all _ fun t ↦ ?_)
      dsimp only
      rw [← Real.exp_add]
      ring_nf
    exact integral_exp_pos hint_η
  have hC_eq : (∫ p, Real.exp (g p.1 + inner ℝ η p.2) ∂(μ ⊗ₘ κ)) =
      ∫ s, Real.exp (g s + Real.log (Z s)) ∂μ := by
    rw [Measure.integral_compProd hint]
    refine integral_congr_ae ?_
    filter_upwards [hae_Zpos] with s hs
    have heq : (fun t : E ↦ Real.exp (g s + inner ℝ η t)) =
        fun t : E ↦ Real.exp (g s) * Real.exp (inner ℝ η t) := by
      ext t; exact Real.exp_add _ _
    rw [heq, integral_const_mul, Real.exp_add, Real.exp_log hs]
  rw [tilted_compProd_eq_fst_compProd_conditionalExponentialKernel_of_measurable hg hint,
    fst_tilted_compProd_eq_withDensity hg hint, Measure.tilted]
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [hae_Zpos] with s hs
  rw [hC_eq, Real.exp_add, Real.exp_log hs]

/-- When `κ s ≠ 0` for `μ`-a.e. `s`, the first marginal of `(μ ⊗ₘ κ).tilted (g s + ⟪η, t⟫)` is
`μ.tilted (g s + log ∫ exp ⟪η, t⟫ dκ s)`, so the joint tilt equals that tilted marginal composed
with `conditionalExponentialKernel κ η`. -/
theorem tilted_compProd_eq_tilted_compProd_conditionalExponentialKernel {μ : Measure F} [SFinite μ]
    {κ : Kernel F E} [IsSFiniteKernel κ] (hκ : ∀ᵐ s ∂μ, κ s ≠ 0) {g : F → ℝ} {η : E}
    (hint : Integrable (fun p : F × E ↦ Real.exp (g p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ)) :
    (μ ⊗ₘ κ).tilted (fun p ↦ g p.1 + inner ℝ η p.2) =
      (μ.tilted fun s ↦ g s + Real.log (∫ t, Real.exp (inner ℝ η t) ∂κ s)) ⊗ₘ
        conditionalExponentialKernel κ η := by
  have hμS : μ.restrict {s | κ s Set.univ ≠ 0} = μ :=
    Measure.restrict_eq_self_of_ae_mem (hκ.mono fun s hs ↦ by simpa using hs)
  have hg_ae : AEMeasurable g μ := hμS ▸ aemeasurable_of_integrable_exp_add_compProd hint
  let g' : F → ℝ := hg_ae.mk g
  have hprod_ae : (fun p : F × E ↦ g p.1 + inner ℝ η p.2) =ᵐ[μ ⊗ₘ κ]
      fun p ↦ g' p.1 + inner ℝ η p.2 :=
    (ae_compProd_fst_eq_of_ae_eq κ hg_ae.ae_eq_mk).mono fun p hp ↦ by simp [g', hp]
  have hmarg_ae : (fun s ↦ g s + Real.log (∫ t, Real.exp (inner ℝ η t) ∂κ s)) =ᵐ[μ]
      fun s ↦ g' s + Real.log (∫ t, Real.exp (inner ℝ η t) ∂κ s) :=
    hg_ae.ae_eq_mk.mono fun s hs ↦ by simp [g', hs]
  have hint' : Integrable (fun p : F × E ↦ Real.exp (g' p.1 + inner ℝ η p.2)) (μ ⊗ₘ κ) :=
    hint.congr (hprod_ae.mono fun p hp ↦ by simp [hp])
  rw [tilted_congr hprod_ae, tilted_congr hmarg_ae]
  exact tilted_compProd_eq_tilted_compProd_conditionalExponentialKernel_of_measurable hκ
    hg_ae.measurable_mk hint'

end CompProdTilt

section MainTheorem

variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [StandardBorelSpace E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [OpensMeasurableSpace F]

/-- Conditional exponential family theorem for measurable `T`, `S` with a fixed reference parameter
`p₀` in the natural parameter space. -/
private lemma exists_kernel_conditional_exponential_family_of_mem (ν : Measure X) {T : X → E}
    {S : X → F} (hT : Measurable T) (hS : Measurable S) {p₀ : WithLp 2 (E × F)}
    (hp₀ : p₀ ∈ naturalParameterSpace ν (fun x ↦ WithLp.toLp 2 (T x, S x))) :
    ∃ (κ : Kernel F E) (_ : IsSFiniteKernel κ),
      ∀ p ∈ naturalParameterSpace ν (fun x ↦ WithLp.toLp 2 (T x, S x)),
        let P := exponentialFamilyMeasure ν (fun x ↦ WithLp.toLp 2 (T x, S x)) p
        P.map (fun x ↦ (S x, T x)) =
          P.map S ⊗ₘ conditionalExponentialKernel κ (WithLp.ofLp p).1 := by
  let TS : X → WithLp 2 (E × F) := fun x ↦ WithLp.toLp 2 (T x, S x)
  set η₀ : E := (WithLp.ofLp p₀).1
  let P₀ : Measure X := exponentialFamilyMeasure ν TS p₀
  have hP₀_def : P₀ = ν.tilted fun x ↦ inner ℝ p₀ (TS x) := exponentialFamilyMeasure_def ν TS p₀
  let κ₀ : Kernel F E := condDistrib T S P₀
  let κ : Kernel F E := κ₀.withDensity fun _ t ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₀ t))
  have hκ_sfin : IsSFiniteKernel κ :=
    Kernel.IsSFiniteKernel.withDensity κ₀ fun _ _ ↦ ENNReal.ofReal_ne_top
  refine ⟨κ, hκ_sfin, fun p hp ↦ ?_⟩
  set η : E := (WithLp.ofLp p).1
  let P : Measure X := exponentialFamilyMeasure ν TS p
  let h : F × E → ℝ := fun q ↦ inner ℝ ((WithLp.ofLp p).2 - (WithLp.ofLp p₀).2) q.1 +
    inner ℝ (η - η₀) q.2
  have hinner_diff : ∀ x : X, inner ℝ p (TS x) = inner ℝ p₀ (TS x) + h (S x, T x) := fun x ↦ by
    simp only [TS, h, WithLp.prod_inner_apply, η, η₀, inner_sub_left]
    ring
  have hP_tilt : P = P₀.tilted (h ∘ fun x ↦ (S x, T x)) := by
    have hsum : (fun x : X ↦ inner ℝ p (TS x)) =
        (fun x : X ↦ inner ℝ p₀ (TS x)) + (h ∘ fun x ↦ (S x, T x)) := funext hinner_diff
    dsimp only [P]
    rw [exponentialFamilyMeasure_def, hsum, ← tilted_tilted (mem_naturalParameterSpace_iff.mp hp₀),
      ← hP₀_def]
  have hh_meas : Measurable h :=
    ((continuous_const.inner continuous_id).measurable.comp measurable_fst).add
      ((continuous_const.inner continuous_id).measurable.comp measurable_snd)
  have hmap : P.map (fun x ↦ (S x, T x)) = (P₀.map S ⊗ₘ κ₀).tilted h := by
    rw [hP_tilt, compProd_map_condDistrib hS.aemeasurable hT.aemeasurable]
    exact Measure.map_tilted P₀ (hS.prodMk hT) hh_meas
  have hint_P₀ : Integrable (fun x ↦ Real.exp (h (S x, T x))) P₀ := by
    rw [hP₀_def, integrable_tilted_iff (mem_naturalParameterSpace_iff.mp hp₀)]
    refine (mem_naturalParameterSpace_iff.mp hp).congr (ae_of_all _ fun x ↦ ?_)
    dsimp only [smul_eq_mul]
    rw [hinner_diff x, Real.exp_add]
  have hint_compProd : Integrable (fun q : F × E ↦ Real.exp (h q)) (P₀.map S ⊗ₘ κ₀) := by
    rw [compProd_map_condDistrib hS.aemeasurable hT.aemeasurable]
    exact (integrable_map_measure (Real.measurable_exp.comp hh_meas).aestronglyMeasurable
      (hS.prodMk hT).aemeasurable).mpr hint_P₀
  dsimp only
  rw [conditionalExponentialKernel_withDensity_exp_neg κ₀ η₀ η, hmap,
    tilted_compProd_eq_fst_compProd_conditionalExponentialKernel (μ := P₀.map S) (κ := κ₀)
      hint_compProd,
    ← hmap, Measure.fst_map_prodMk hS hT]

/-- **Conditional exponential families (Brown, Theorem 1.15).** For a natural exponential family
with pair statistic `(T, S)` encoded in `WithLp 2 (E × F)`, there is a single parameter-free
s-finite kernel `κ : Kernel F E` such that, at every natural parameter `p = (η, ζ)`, the
conditional distribution of `T` given `S` is `conditionalExponentialKernel κ η`, depending only
on `η`. -/
theorem exists_kernel_conditional_exponential_family (ν : Measure X) (T : X → E) (S : X → F)
    (hT : AEMeasurable T ν) (hS : AEMeasurable S ν) :
    ∃ (κ : Kernel F E) (_ : IsSFiniteKernel κ),
      ∀ p ∈ naturalParameterSpace ν (fun x ↦ WithLp.toLp 2 (T x, S x)),
        let P := exponentialFamilyMeasure ν (fun x ↦ WithLp.toLp 2 (T x, S x)) p
        P.map (fun x ↦ (S x, T x)) =
          P.map S ⊗ₘ conditionalExponentialKernel κ (WithLp.ofLp p).1 := by
  let T' : X → E := hT.mk T
  let S' : X → F := hS.mk S
  let TS : X → WithLp 2 (E × F) := fun x ↦ WithLp.toLp 2 (T x, S x)
  let TS' : X → WithLp 2 (E × F) := fun x ↦ WithLp.toLp 2 (T' x, S' x)
  have hTS_ae : TS =ᵐ[ν] TS' := by
    filter_upwards [hT.ae_eq_mk, hS.ae_eq_mk] with x hxT hxS
    simp [TS, TS', T', S', hxT, hxS]
  have hN_eq : naturalParameterSpace ν TS = naturalParameterSpace ν TS' := by
    ext p
    rw [mem_naturalParameterSpace_iff, mem_naturalParameterSpace_iff]
    exact integrable_congr (hTS_ae.mono fun x hx ↦ by simp [hx])
  have hP_eq : ∀ p, exponentialFamilyMeasure ν TS p = exponentialFamilyMeasure ν TS' p := fun p ↦ by
    rw [exponentialFamilyMeasure_def, exponentialFamilyMeasure_def]
    exact tilted_congr (hTS_ae.mono fun x hx ↦ by simp [hx])
  by_cases hNne : (naturalParameterSpace ν TS').Nonempty
  · obtain ⟨p₀, hp₀⟩ := hNne
    obtain ⟨κ, hκ, hprop⟩ := exists_kernel_conditional_exponential_family_of_mem ν
      hT.measurable_mk hS.measurable_mk hp₀
    refine ⟨κ, hκ, fun p hp ↦ ?_⟩
    have hp' : p ∈ naturalParameterSpace ν TS' := hN_eq ▸ hp
    have hac : exponentialFamilyMeasure ν TS' p ≪ ν := by
      rw [exponentialFamilyMeasure_def]
      exact tilted_absolutelyContinuous ν _
    have hST_ae : (fun x ↦ (S x, T x)) =ᵐ[exponentialFamilyMeasure ν TS' p] fun x ↦ (S' x, T' x) :=
      hac.ae_le (hS.ae_eq_mk.mp (hT.ae_eq_mk.mono fun x hxT hxS ↦ by simp [T', S', hxT, hxS]))
    dsimp only
    rw [hP_eq p, Measure.map_congr hST_ae, Measure.map_congr (hac.ae_le hS.ae_eq_mk)]
    exact hprop p hp'
  · exact ⟨0, inferInstance, fun p hp ↦ absurd ⟨p, hN_eq ▸ hp⟩ hNne⟩

end MainTheorem

end TauCeti
