/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Hermite
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.UsualFiltration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated
import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.Probability.BrownianMotion.Predictable
import TauCeti.Probability.BrownianMotion.RightContinuity
import TauCeti.Probability.Distributions.Gaussian.Hermite.Expectation
import TauCeti.Probability.Independence.CondExp
import TauCeti.Probability.Independence.Integration
import TauCeti.Probability.Martingale.Convergence
import TauCeti.Probability.Process.ElementaryDensity

/-!
# Terminal `L²` Brownian martingale representation

Every square-integrable random variable measurable, up to null sets, with respect to Brownian
observations up to a finite horizon `T` admits a unique decomposition into its expectation plus
the terminal predictable `L²` stochastic integral `l2Integral T f` of a predictable integrand
`f ∈ Lp ℝ 2 (ℱ.predictableMeasure P T)`.

## Proof architecture

1. **Orthogonal decomposition (`l2RepresentableSubmodule`)**: For any filtered pre-Brownian motion
   `hW : IsFilteredPreBrownianReal ℱ W P`, centeredness `integral_l2Integral` makes constants and
   the isometric range of `hW.l2Integral T` orthogonal in `Lp ℝ 2 P`, so their sum
   `hW.l2RepresentableSubmodule T` is closed and gives unique integrand recovery.
2. **Explicit Hermite-increment integrands (`hermiteIncrementIntegrand`)**: For a strongly
   predictable version `W` and `s < t ≤ T`, the `(m + 1)`-th Hermite polynomial of the standardized
   increment `(W t - W s) / √(t - s)`, weighted by any `ℱ s`-measurable `L²` random variable, is
   represented explicitly by `m`-th Hermite polynomials of intermediate increments on `(s, t]`.
3. **Finite grids to arbitrary observation families**: Induction over strictly increasing grids
   places every multidimensional Hermite product `gaussianVectorHermite` into
   `hW.l2RepresentableSubmodule T` (transferring from a predictable modification via
   `exists_isStronglyPredictable_ae_eq` and `l2Integral_congr`, with no path-continuity
   hypothesis). Finite-grid Hermite completeness, countable coordinate reduction
   (`Measurable.exists_countable_iSup`), and `L²` martingale convergence of conditional
   expectations (`MemLp.tendsto_eLpNorm_condExp`) extend representation to any observation family
   `t : ι → ℝ≥0` bounded by `T`.
4. **Natural and usual Brownian filtrations**: Specializing to `[0, T]` yields terminal `L²`
   representation on the raw natural filtration, its original-space `ambientNullAugmentation`, and
   (for continuous-path Brownian motion) both the original-space and completed usual
   right-continuous natural Brownian filtrations.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4, Theorem 3.4.15.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition, Springer,
  1999, Chapter V, Theorem 3.5.
-/

public section

noncomputable section

open Filter MeasureTheory Polynomial ProbabilityTheory Set TauCeti TauCeti.Probability
open scoped NNReal ENNReal InnerProductSpace Topology

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Dividing a Brownian increment over a nonempty interval `(s, t]` by `√(t - s)` produces a
standard Gaussian random variable. -/
theorem hasLaw_sub_div_sqrt (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s < t) :
    HasLaw (fun ω ↦ (B t ω - B s ω) / Real.sqrt ((t : ℝ) - s)) (gaussianReal 0 1) P := by
  have hlt : (s : ℝ) < t := hst
  have hvar : (t - s : ℝ≥0) / NNReal.mk (Real.sqrt ((t : ℝ) - s) ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.coe_injective
    simp [NNReal.coe_sub hst.le, Real.sq_sqrt (sub_nonneg.mpr hlt.le),
      div_self (sub_ne_zero.mpr hlt.ne')]
  convert! gaussianReal_div_const (hB.hasLaw_sub_of_le hst.le) (Real.sqrt ((t : ℝ) - s)) using 1
  exact congrArg₂ gaussianReal (zero_div _).symm hvar.symm

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-! ### Closedness and uniqueness of constant-plus-integral representations -/

/-- The subspace of `Lp ℝ 2 P` consisting of square-integrable random variables representable at
horizon `T` as a constant plus a predictable `L²` Brownian stochastic integral. -/
def l2RepresentableSubmodule (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0) :
    Submodule ℝ (Lp ℝ 2 P) :=
  letI := (hW.hasLaw_eval 0).isProbabilityMeasure
  Submodule.span ℝ {Lp.const 2 P (1 : ℝ)} ⊔ LinearMap.range (hW.l2Integral T).toLinearMap

private theorem inner_const_one_eq_integral [IsFiniteMeasure P] (u : Lp ℝ 2 P) :
    ⟪Lp.const 2 P (1 : ℝ), u⟫_ℝ = ∫ ω, u ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const 2 P (1 : ℝ)] with ω hω
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hω, Function.const_apply, mul_one]

/-- Membership in `l2RepresentableSubmodule T` means agreeing `P`-almost everywhere with a
constant plus a predictable `L²` stochastic integral. -/
theorem mem_l2RepresentableSubmodule_iff (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0)
    (u : Lp ℝ 2 P) :
    u ∈ hW.l2RepresentableSubmodule T ↔
      ∃ (c : ℝ) (f : Lp ℝ 2 (ℱ.predictableMeasure P T)),
        ⇑u =ᵐ[P] fun ω ↦ c + hW.l2Integral T f ω := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  rw [l2RepresentableSubmodule, Submodule.mem_sup]
  constructor
  · rintro ⟨v, hv, w, ⟨f, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨c, f, ?_⟩
    simp only [LinearIsometry.coe_toLinearMap]
    filter_upwards [Lp.coeFn_add (c • Lp.const 2 P (1 : ℝ)) (hW.l2Integral T f),
      Lp.coeFn_smul c (Lp.const 2 P (1 : ℝ)), Lp.coeFn_const 2 P (1 : ℝ)] with ω hadd hsmul hc
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hc, Function.const_apply, smul_eq_mul, mul_one]
  · rintro ⟨c, f, hu⟩
    refine ⟨c • Lp.const 2 P (1 : ℝ), Submodule.mem_span_singleton.mpr ⟨c, rfl⟩,
      hW.l2Integral T f, ⟨f, rfl⟩, Lp.ext ?_⟩
    filter_upwards [Lp.coeFn_add (c • Lp.const 2 P (1 : ℝ)) (hW.l2Integral T f),
      Lp.coeFn_smul c (Lp.const 2 P (1 : ℝ)), Lp.coeFn_const 2 P (1 : ℝ), hu]
      with ω hadd hsmul hc hω
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hc, Function.const_apply, smul_eq_mul, mul_one,
      ← hω]

/-- Almost-surely constant `L²` classes belong to `l2RepresentableSubmodule T`. -/
theorem const_mem_l2RepresentableSubmodule (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0)
    {u : Lp ℝ 2 P} {c : ℝ} (hu : ⇑u =ᵐ[P] fun _ ↦ c) :
    u ∈ hW.l2RepresentableSubmodule T := by
  rw [hW.mem_l2RepresentableSubmodule_iff]
  refine ⟨c, 0, ?_⟩
  rw [map_zero]
  filter_upwards [hu, Lp.coeFn_zero ℝ 2 P] with ω hω hz
  rw [hω, hz, Pi.zero_apply, add_zero]

/-- Every terminal predictable `L²` Brownian integral belongs to `l2RepresentableSubmodule T`. -/
theorem l2Integral_mem_l2RepresentableSubmodule (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    hW.l2Integral T f ∈ hW.l2RepresentableSubmodule T := by
  rw [hW.mem_l2RepresentableSubmodule_iff]
  exact ⟨0, f, by simp⟩

/-- In a constant-plus-stochastic-integral representation, both the constant and the predictable
`L²` integrand are uniquely determined. -/
theorem eq_and_eq_of_ae_eq_add_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0}
    {u : Lp ℝ 2 P} {c₁ c₂ : ℝ} {f₁ f₂ : Lp ℝ 2 (ℱ.predictableMeasure P T)}
    (h₁ : ⇑u =ᵐ[P] fun ω ↦ c₁ + hW.l2Integral T f₁ ω)
    (h₂ : ⇑u =ᵐ[P] fun ω ↦ c₂ + hW.l2Integral T f₂ ω) :
    c₁ = c₂ ∧ f₁ = f₂ := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hint₁ : ∫ ω, u ω ∂P = c₁ := by
    rw [integral_congr_ae h₁,
      integral_add (integrable_const c₁) ((Lp.memLp _).integrable one_le_two),
      integral_const, hW.integral_l2Integral]
    simp
  have hint₂ : ∫ ω, u ω ∂P = c₂ := by
    rw [integral_congr_ae h₂,
      integral_add (integrable_const c₂) ((Lp.memLp _).integrable one_le_two),
      integral_const, hW.integral_l2Integral]
    simp
  have hc : c₁ = c₂ := hint₁.symm.trans hint₂
  refine ⟨hc, (hW.l2Integral T).injective (Lp.ext ?_)⟩
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  linarith [hω₁.symm.trans hω₂]

/-- Every element of `l2RepresentableSubmodule T` admits a unique predictable `L²` integrand
representing its centered part. -/
theorem existsUnique_l2Integral_of_mem_l2RepresentableSubmodule
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} {u : Lp ℝ 2 P}
    (hu : u ∈ hW.l2RepresentableSubmodule T) :
    ∃! f : Lp ℝ 2 (ℱ.predictableMeasure P T),
      ⇑u =ᵐ[P] fun ω ↦ (∫ ω', u ω' ∂P) + hW.l2Integral T f ω := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨c, f, hf⟩ := (hW.mem_l2RepresentableSubmodule_iff T u).mp hu
  have hc : ∫ ω', u ω' ∂P = c := by
    rw [integral_congr_ae hf,
      integral_add (integrable_const c) ((Lp.memLp _).integrable one_le_two),
      integral_const, hW.integral_l2Integral]
    simp
  refine ⟨f, hc ▸ hf, fun g hg ↦ ?_⟩
  exact (hW.eq_and_eq_of_ae_eq_add_l2Integral hg (hc ▸ hf)).2

/-- The subspace of constant-plus-integral representable `L²` claims is closed in `Lp ℝ 2 P`. -/
theorem isClosed_l2RepresentableSubmodule (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0) :
    IsClosed (hW.l2RepresentableSubmodule T : Set (Lp ℝ 2 P)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let one : Lp ℝ 2 P := Lp.const 2 P (1 : ℝ)
  let center : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
    ContinuousLinearMap.id ℝ (Lp ℝ 2 P) - (innerSL ℝ one).smulRight one
  have heq : (hW.l2RepresentableSubmodule T : Set (Lp ℝ 2 P)) =
      center ⁻¹' Set.range (hW.l2Integral T) := by
    ext u
    simp only [SetLike.mem_coe, mem_preimage, mem_range, center, sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, one,
      inner_const_one_eq_integral]
    constructor
    · intro hu
      obtain ⟨f, hf, -⟩ := hW.existsUnique_l2Integral_of_mem_l2RepresentableSubmodule hu
      refine ⟨f, Lp.ext ?_⟩
      filter_upwards [hf, Lp.coeFn_sub u ((∫ ω, u ω ∂P) • Lp.const 2 P (1 : ℝ)),
        Lp.coeFn_smul (∫ ω, u ω ∂P) (Lp.const 2 P (1 : ℝ)), Lp.coeFn_const 2 P (1 : ℝ)]
        with ω hω hsub hsmul hc
      rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hc, Function.const_apply, smul_eq_mul, mul_one]
      linarith
    · rintro ⟨f, hf⟩
      rw [hW.mem_l2RepresentableSubmodule_iff]
      refine ⟨∫ ω, u ω ∂P, f, ?_⟩
      rw [hf]
      filter_upwards [Lp.coeFn_sub u ((∫ ω, u ω ∂P) • Lp.const 2 P (1 : ℝ)),
        Lp.coeFn_smul (∫ ω, u ω ∂P) (Lp.const 2 P (1 : ℝ)), Lp.coeFn_const 2 P (1 : ℝ)]
        with ω hsub hsmul hc
      rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hc, Function.const_apply, smul_eq_mul, mul_one]
      ring
  rw [heq]
  exact (Isometry.isClosedEmbedding (hW.l2Integral T).isometry).isClosed_range.preimage
    center.continuous

/-! ### Explicit Hermite-increment integrands -/

private def scaledHermiteIncrement (W : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (k : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  Real.sqrt ((u : ℝ) - s) ^ k * aeval ((W u ω - W s ω) / Real.sqrt ((u : ℝ) - s)) (hermite k)

/-- The predictable integrand on `(s, t]` whose stochastic integral produces the `(m + 1)`-th
probabilists' Hermite polynomial of `(W t - W s) / √(t - s)`. -/
def hermiteIncrementIntegrand (W : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (p : ℝ≥0 × Ω) : ℝ :=
  (Ioc s t).indicator (fun u ↦
    (m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1) *
      (Real.sqrt ((u : ℝ) - s) ^ m *
        aeval ((W u p.2 - W s p.2) / Real.sqrt ((u : ℝ) - s)) (hermite m))) p.1

/-- For a strongly predictable filtered pre-Brownian motion, `hermiteIncrementIntegrand W s t m`
is strongly measurable with respect to the predictable σ-algebra. -/
theorem stronglyMeasurable_hermiteIncrementIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) (s t : ℝ≥0) (m : ℕ) :
    StronglyMeasurable[ℱ.predictable] (hermiteIncrementIntegrand W s t m) := by
  have hWs : StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ W s p.2) p.1) :=
    (hW.adapted s).stronglyMeasurable.isStronglyPredictable_indicator_Ioc t
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hfst : Measurable (Prod.fst : ℝ≥0 × Ω → ℝ≥0) := ℱ.measurable_fst_predictable
  have hdiv : Measurable (fun p : ℝ≥0 × Ω ↦
      (W p.1 p.2 - (Ioc s t).indicator (fun _ ↦ W s p.2) p.1) / Real.sqrt ((p.1 : ℝ) - s)) :=
    (hpred.sub hWs).measurable.div
      ((NNReal.continuous_coe.measurable.comp hfst).sub_const (s : ℝ)).sqrt
  have hraw : StronglyMeasurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦
      (m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1) *
        (Real.sqrt ((p.1 : ℝ) - s) ^ m *
          aeval ((W p.1 p.2 - (Ioc s t).indicator (fun _ ↦ W s p.2) p.1) /
            Real.sqrt ((p.1 : ℝ) - s)) (hermite m))) :=
    (measurable_const.mul
      ((((NNReal.continuous_coe.measurable.comp hfst).sub_const (s : ℝ)).sqrt.pow_const m).mul
        (((hermite m).continuous_aeval (A := ℝ)).measurable.comp hdiv))).stronglyMeasurable
  have heq : (Ioc s t ×ˢ (univ : Set Ω)).indicator (fun p : ℝ≥0 × Ω ↦
      (m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1) *
        (Real.sqrt ((p.1 : ℝ) - s) ^ m *
          aeval ((W p.1 p.2 - (Ioc s t).indicator (fun _ ↦ W s p.2) p.1) /
            Real.sqrt ((p.1 : ℝ) - s)) (hermite m))) =
      hermiteIncrementIntegrand W s t m := by
    ext ⟨u, ω⟩
    by_cases hu : u ∈ Ioc s t <;>
      simp only [hermiteIncrementIntegrand, mem_prod, mem_univ, and_true, hu, not_false_eq_true,
        indicator_of_mem, indicator_of_notMem]
  exact heq ▸ hraw.indicator (measurableSet_predictable_Ioc_prod s t MeasurableSet.univ)

private theorem stronglyMeasurable_scaledHermiteIncrement (hW : IsFilteredPreBrownianReal ℱ W P)
    {s u : ℝ≥0} (hsu : s ≤ u) (k : ℕ) :
    StronglyMeasurable[ℱ u] (scaledHermiteIncrement W s k u) := by
  let : MeasurableSpace Ω := ℱ u
  have hdiff : Measurable (fun ω : Ω ↦ (W u ω - W s ω) / Real.sqrt ((u : ℝ) - s)) :=
    ((hW.adapted u).sub ((hW.adapted s).mono (ℱ.mono hsu) le_rfl)).div_const _
  exact (measurable_const.mul
    ((hermite k).continuous_aeval.measurable.comp hdiff)).stronglyMeasurable

private theorem memLp_scaledHermiteIncrement (hW : IsFilteredPreBrownianReal ℱ W P)
    {s u : ℝ≥0} (hsu : s ≤ u) (k : ℕ) :
    MemLp (scaledHermiteIncrement W s k u) 2 P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  rcases hsu.eq_or_lt with rfl | hlt
  · have hconst : scaledHermiteIncrement W s k s =
        fun _ ↦ (0 : ℝ) ^ k * aeval 0 (hermite k) := by
      ext ω; simp [scaledHermiteIncrement]
    exact hconst ▸ memLp_const _
  · have hgauss : MemLp (fun z : ℝ ↦ aeval z (hermite k)) 2 (gaussianReal 0 1) :=
      (memLp_congr_ae (ae_of_all _ fun z ↦ by simp)).mp
        (memLp_two_aeval_comp_affine_gaussianReal (hermite k) 0 1 0 1)
    exact ((hW.hasLaw_sub_div_sqrt hlt).memLp_fun_comp hgauss).const_mul
      (Real.sqrt ((u : ℝ) - s) ^ k)

private theorem integral_sq_scaledHermiteIncrement (hW : IsFilteredPreBrownianReal ℱ W P)
    {s u : ℝ≥0} (hlt : s < u) (k : ℕ) :
    (∫ ω, scaledHermiteIncrement W s k u ω ^ 2 ∂P) =
      ((u : ℝ) - s) ^ k * (k.factorial : ℝ) := by
  have hm : Measurable (fun x : ℝ ↦ aeval x (hermite k)) :=
    ((hermite k).continuous_aeval (A := ℝ)).measurable
  have hlaw := (hW.hasLaw_sub_div_sqrt hlt).integral_comp
    (f := fun z : ℝ ↦ (Real.sqrt ((u : ℝ) - s) ^ k * aeval z (hermite k)) ^ 2)
    ((measurable_const.mul hm).pow_const 2).aestronglyMeasurable
  rw [Function.comp_def] at hlaw
  have hrew (z : ℝ) : (Real.sqrt ((u : ℝ) - s) ^ k * aeval z (hermite k)) ^ 2 =
      ((u : ℝ) - s) ^ k * (aeval z (hermite k) * aeval z (hermite k)) := by
    have hsq : (Real.sqrt ((u : ℝ) - s) ^ k) ^ 2 = ((u : ℝ) - s) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul,
        Real.sq_sqrt (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hlt.le))]
    calc (Real.sqrt ((u : ℝ) - s) ^ k * aeval z (hermite k)) ^ 2
      _ = (Real.sqrt ((u : ℝ) - s) ^ k) ^ 2 * (aeval z (hermite k) * aeval z (hermite k)) := by
        ring
      _ = ((u : ℝ) - s) ^ k * (aeval z (hermite k) * aeval z (hermite k)) := by rw [hsq]
  dsimp only [scaledHermiteIncrement]
  rw [hlaw]
  simp_rw [hrew]
  rw [integral_const_mul, integral_hermite_mul_hermite_gaussianReal k k]
  simp

/-- For a strongly predictable filtered pre-Brownian motion, `hermiteIncrementIntegrand W s t m`
belongs to `Lp ℝ 2 (ℱ.predictableMeasure P T)` on every horizon `T`. -/
theorem memLp_hermiteIncrementIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) (s t T : ℝ≥0) (m : ℕ) :
    MemLp (hermiteIncrementIntegrand W s t m) 2 (ℱ.predictableMeasure P T) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hsm := hW.stronglyMeasurable_hermiteIncrementIntegrand hpred s t m
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hsm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hm : Measurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ ‖hermiteIncrementIntegrand W s t m p‖ₑ ^ 2) := hsm.eNorm.pow_const 2
  rw [ℱ.lintegral_predictableMeasure P hm T]
  let C : ℝ := ((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) ^ 2 *
    (((t : ℝ) - s) ^ m * (m.factorial : ℝ))
  have hbound (u : ℝ≥0) :
      ∫⁻ ω, ‖hermiteIncrementIntegrand W s t m (u, ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (max C 0) := by
    by_cases hu : u ∈ Ioc s t
    · have hfn : (fun ω ↦ ‖hermiteIncrementIntegrand W s t m (u, ω)‖ₑ ^ 2) =
          fun ω ↦ ENNReal.ofReal (((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) ^ 2 *
            scaledHermiteIncrement W s m u ω ^ 2) := by
        ext ω; rw [Real.enorm_sq_eq_ofReal_sq]
        simp only [hermiteIncrementIntegrand, indicator_of_mem hu, scaledHermiteIncrement]
        congr 1; ring
      rw [hfn, ← ofReal_integral_eq_lintegral_ofReal
        ((hW.memLp_scaledHermiteIncrement hu.1.le m).integrable_sq.const_mul _)
        (ae_of_all _ fun _ ↦ by positivity), integral_const_mul,
        hW.integral_sq_scaledHermiteIncrement hu.1 m]
      refine ENNReal.ofReal_le_ofReal ((le_max_left C 0).trans' ?_)
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
        (sq_nonneg _)
      exact pow_le_pow_left₀ (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hu.1.le))
        (sub_le_sub_right (NNReal.coe_le_coe.mpr hu.2) _) m
    · simp only [hermiteIncrementIntegrand, indicator_of_notMem hu, eNorm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, lintegral_const, zero_mul, zero_le]
  calc ∫⁻ u, ∫⁻ ω, ‖hermiteIncrementIntegrand W s t m (u, ω)‖ₑ ^ 2 ∂P ∂timeMeasure T
    _ ≤ ∫⁻ _, ENNReal.ofReal (max C 0) ∂timeMeasure T := lintegral_mono hbound
    _ = ENNReal.ofReal (max C 0) * T := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top

private def weightedHermiteIntegrand (W : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ) (s t : ℝ≥0) (m : ℕ)
    (p : ℝ≥0 × Ω) : ℝ :=
  (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1 * hermiteIncrementIntegrand W s t m p

private theorem stronglyMeasurable_weightedHermiteIntegrand
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    {ξ : Ω → ℝ} {s : ℝ≥0} (hξ : StronglyMeasurable[ℱ s] ξ) (t : ℝ≥0) (m : ℕ) :
    StronglyMeasurable[ℱ.predictable] (weightedHermiteIntegrand W ξ s t m) :=
  StronglyMeasurable.mul (hξ.isStronglyPredictable_indicator_Ioc t)
    (hW.stronglyMeasurable_hermiteIncrementIntegrand hpred s t m)

private theorem setIntegral_pow_sub_timeMeasure {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    (m : ℕ) :
    (∫ u in Ioc s t, ((u : ℝ) - s) ^ m ∂timeMeasure T) =
      ((t : ℝ) - s) ^ (m + 1) / (m + 1 : ℝ) := by
  have hrest : (timeMeasure T).restrict (Ioc s t) = nnvolume.restrict (Ioc s t) := by
    rw [timeMeasure_def, ← nnvolume_def, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc (zero_le : (0 : ℝ≥0) ≤ s) htT)]
  have hpre : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (s : ℝ) t = Ioc s t := by ext u; simp
  rw [hrest, ← hpre,
    ← NNReal.isClosedEmbedding_coe.measurableEmbedding.setIntegral_map (fun x : ℝ ↦ (x - s) ^ m)
      (Ioc (s : ℝ) t),
    map_coe_nnvolume, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr ((Ioc_subset_Icc_self.trans Icc_subset_Ici_self).trans
      (Ici_subset_Ici.mpr s.coe_nonneg)),
    ← intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hst),
    intervalIntegral.integral_comp_sub_right (· ^ m), sub_self, integral_pow]
  simp

private theorem indepFun_scaledHermiteIncrement (hW : IsFilteredPreBrownianReal ℱ W P)
    {ξ : Ω → ℝ} {s u : ℝ≥0} (hξ : Measurable[ℱ s] ξ) (hsu : s ≤ u) (k : ℕ) :
    IndepFun ξ (scaledHermiteIncrement W s k u) P := by
  have hm : Measurable (fun x : ℝ ↦ aeval x (hermite k)) :=
    ((hermite k).continuous_aeval (A := ℝ)).measurable
  have hp : Measurable (fun x : ℝ ↦ Real.sqrt ((u : ℝ) - s) ^ k *
      aeval (x / Real.sqrt ((u : ℝ) - s)) (hermite k)) :=
    measurable_const.mul (hm.comp (measurable_id.div_const _))
  exact (hW.indepFun_sub hsu hξ).comp measurable_id hp

private theorem integral_sq_weightedHermiteIntegrand_slice (hW : IsFilteredPreBrownianReal ℱ W P)
    {ξ : Ω → ℝ} {s t u : ℝ≥0} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hu : u ∈ Ioc s t) (m : ℕ) :
    (∫ ω, weightedHermiteIntegrand W ξ s t m (u, ω) ^ 2 ∂P) =
      (∫ ω, ξ ω ^ 2 ∂P) * (((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) ^ 2 *
        (((u : ℝ) - s) ^ m * (m.factorial : ℝ))) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let c : ℝ := (m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)
  have hind : IndepFun (fun ω ↦ ξ ω ^ 2)
      (fun ω ↦ c ^ 2 * scaledHermiteIncrement W s m u ω ^ 2) P :=
    (hW.indepFun_scaledHermiteIncrement hξ.measurable hu.1.le m).comp
      (measurable_id.pow_const 2) ((measurable_id.pow_const 2).const_mul (c ^ 2))
  have hfn : (fun ω ↦ weightedHermiteIntegrand W ξ s t m (u, ω) ^ 2) =
      fun ω ↦ ξ ω ^ 2 * (c ^ 2 * scaledHermiteIncrement W s m u ω ^ 2) := by
    ext ω
    simp only [weightedHermiteIntegrand, hermiteIncrementIntegrand, indicator_of_mem hu,
      scaledHermiteIncrement, c]
    ring
  rw [hfn, hind.integral_fun_mul_eq_mul_integral
    ((hξ.mono (ℱ.le s)).pow 2).aestronglyMeasurable
    ((((hW.stronglyMeasurable_scaledHermiteIncrement hu.1.le m).mono (ℱ.le u)).pow 2).const_mul
      _).aestronglyMeasurable,
    integral_const_mul, hW.integral_sq_scaledHermiteIncrement hu.1 m]

private theorem memLp_weightedHermiteIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) {ξ : Ω → ℝ} {s : ℝ≥0}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) (t T : ℝ≥0) (m : ℕ) :
    MemLp (weightedHermiteIntegrand W ξ s t m) 2 (ℱ.predictableMeasure P T) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hsm := hW.stronglyMeasurable_weightedHermiteIntegrand hpred hξ t m
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hsm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hm : Measurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ ‖weightedHermiteIntegrand W ξ s t m p‖ₑ ^ 2) := hsm.eNorm.pow_const 2
  rw [ℱ.lintegral_predictableMeasure P hm T]
  let K : ℝ := (∫ ω, ξ ω ^ 2 ∂P) * (((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) ^ 2 *
    (((t : ℝ) - s) ^ m * (m.factorial : ℝ)))
  have hbound (u : ℝ≥0) :
      ∫⁻ ω, ‖weightedHermiteIntegrand W ξ s t m (u, ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (max K 0) := by
    by_cases hu : u ∈ Ioc s t
    · have hint : Integrable (fun ω ↦ weightedHermiteIntegrand W ξ s t m (u, ω) ^ 2) P := by
        have h2 := ((hW.indepFun_scaledHermiteIncrement hξ.measurable hu.1.le m).memLp_two_mul
          hξ₂ (hW.memLp_scaledHermiteIncrement hu.1.le m)).const_mul
          ((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1))
        refine h2.integrable_sq.congr (ae_of_all _ fun ω ↦ ?_)
        simp only [Pi.mul_apply, weightedHermiteIntegrand, hermiteIncrementIntegrand,
          indicator_of_mem hu, scaledHermiteIncrement]; ring
      simp_rw [Real.enorm_sq_eq_ofReal_sq]
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _),
        hW.integral_sq_weightedHermiteIntegrand_slice hξ hu m]
      refine ENNReal.ofReal_le_ofReal ((le_max_left K 0).trans' ?_)
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ?_ (by positivity)) (sq_nonneg _))
        (integral_nonneg fun _ ↦ sq_nonneg _)
      exact pow_le_pow_left₀ (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hu.1.le))
        (sub_le_sub_right (NNReal.coe_le_coe.mpr hu.2) _) m
    · simp only [weightedHermiteIntegrand, indicator_of_notMem hu, zero_mul, eNorm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, lintegral_const, zero_le]
  calc ∫⁻ u, ∫⁻ ω, ‖weightedHermiteIntegrand W ξ s t m (u, ω)‖ₑ ^ 2 ∂P ∂timeMeasure T
    _ ≤ ∫⁻ _, ENNReal.ofReal (max K 0) ∂timeMeasure T := lintegral_mono hbound
    _ = ENNReal.ofReal (max K 0) * T := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top

private theorem integral_sq_weightedHermiteIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) {ξ : Ω → ℝ} {s t T : ℝ≥0}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) (hst : s < t) (htT : t ≤ T) (m : ℕ) :
    (∫ p, weightedHermiteIntegrand W ξ s t m p ^ 2 ∂ℱ.predictableMeasure P T) =
      (∫ ω, ξ ω ^ 2 ∂P) * ((m + 1).factorial : ℝ) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hsm := hW.stronglyMeasurable_weightedHermiteIntegrand hpred hξ t m
  have hsm2 : StronglyMeasurable[ℱ.predictable]
      (fun p ↦ weightedHermiteIntegrand W ξ s t m p ^ 2) := hsm.pow 2
  have hmem := hW.memLp_weightedHermiteIntegrand hpred hξ hξ₂ t T m
  have hpos : 0 < (t : ℝ) - s := sub_pos.mpr (NNReal.coe_lt_coe.mpr hst)
  have hprod := (ℱ.memLp_predictableMeasure_iff P hsm T 2).mp hmem
  rw [ℱ.integral_predictableMeasure P hsm2 T, integral_prod _ hprod.integrable_sq]
  have hinner (u : ℝ≥0) : (∫ ω, weightedHermiteIntegrand W ξ s t m (u, ω) ^ 2 ∂P) =
      (Ioc s t).indicator (fun v ↦ ((∫ ω, ξ ω ^ 2 ∂P) *
        (((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) ^ 2 * (m.factorial : ℝ))) *
          ((v : ℝ) - s) ^ m) u := by
    by_cases hu : u ∈ Ioc s t
    · simp only [indicator_of_mem hu, hW.integral_sq_weightedHermiteIntegrand_slice hξ hu m]; ring
    · simp only [weightedHermiteIntegrand, indicator_of_notMem hu, zero_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Ioc, integral_const_mul,
    setIntegral_pow_sub_timeMeasure hst.le htT m]
  have hsq : (Real.sqrt ((t : ℝ) - s) ^ (m + 1)) ^ 2 = ((t : ℝ) - s) ^ (m + 1) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hpos.le]
  rw [div_pow, hsq, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hne : ((t : ℝ) - s) ^ (m + 1) ≠ 0 := pow_ne_zero _ hpos.ne'
  have hmne : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hne, hmne]

private theorem decomp_sub_div_sqrt {s a b : ℝ≥0} (hsa : s ≤ a) (hab : a < b) (W : ℝ≥0 → Ω → ℝ)
    (ω : Ω) :
    let α := Real.sqrt ((a : ℝ) - s) / Real.sqrt ((b : ℝ) - s)
    let β := Real.sqrt ((b : ℝ) - a) / Real.sqrt ((b : ℝ) - s)
    (W b ω - W s ω) / Real.sqrt ((b : ℝ) - s) =
      α * ((W a ω - W s ω) / Real.sqrt ((a : ℝ) - s)) +
        β * ((W b ω - W a ω) / Real.sqrt ((b : ℝ) - a)) ∧ α ^ 2 + β ^ 2 = 1 := by
  dsimp only
  have hbs : 0 < (b : ℝ) - s := sub_pos.mpr (NNReal.coe_lt_coe.mpr (hsa.trans_lt hab))
  have hba : 0 < (b : ℝ) - a := sub_pos.mpr (NNReal.coe_lt_coe.mpr hab)
  have has : 0 ≤ (a : ℝ) - s := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hsa)
  have hsq : (Real.sqrt ((a : ℝ) - s) / Real.sqrt ((b : ℝ) - s)) ^ 2 +
      (Real.sqrt ((b : ℝ) - a) / Real.sqrt ((b : ℝ) - s)) ^ 2 = 1 := by
    rw [div_pow, div_pow, Real.sq_sqrt has, Real.sq_sqrt hba.le, Real.sq_sqrt hbs.le, ← add_div,
      sub_add_sub_cancel', div_self hbs.ne']
  refine ⟨?_, hsq⟩
  rcases hsa.eq_or_lt with rfl | hlt
  · simp [div_self (Real.sqrt_pos.mpr hba).ne']
  · have has' : Real.sqrt ((a : ℝ) - s) ≠ 0 :=
      (Real.sqrt_pos.mpr (sub_pos.mpr (NNReal.coe_lt_coe.mpr hlt))).ne'
    have hba' : Real.sqrt ((b : ℝ) - a) ≠ 0 := (Real.sqrt_pos.mpr hba).ne'
    have hbs' : Real.sqrt ((b : ℝ) - s) ≠ 0 := (Real.sqrt_pos.mpr hbs).ne'
    field_simp [has', hba', hbs']
    ring

private theorem indep_comap_sub_div_sqrt (hW : IsFilteredPreBrownianReal ℱ W P) {a b : ℝ≥0}
    (hab : a ≤ b) :
    Indep (MeasurableSpace.comap (fun ω ↦ (W b ω - W a ω) / Real.sqrt ((b : ℝ) - a)) inferInstance)
      (ℱ a) P := by
  have hle : MeasurableSpace.comap
        (fun ω ↦ (W b ω - W a ω) / Real.sqrt ((b : ℝ) - a)) inferInstance ≤
      MeasurableSpace.comap (W b - W a) inferInstance := by
    change MeasurableSpace.comap
        ((fun x ↦ x / Real.sqrt ((b : ℝ) - a)) ∘ (W b - W a)) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_id.div_const _).comap_le
  exact indep_of_indep_of_le_left (hW.indep_sub hab) hle

private theorem condExp_scaledHermiteIncrement (hW : IsFilteredPreBrownianReal ℱ W P)
    {s a u : ℝ≥0} (hsa : s ≤ a) (hau : a ≤ u) (k : ℕ) :
    P[scaledHermiteIncrement W s k u | ℱ a] =ᵐ[P] scaledHermiteIncrement W s k a := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  rcases hau.eq_or_lt with rfl | hlt
  · exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (ℱ.le a)
      (hW.stronglyMeasurable_scaledHermiteIncrement hsa k)
      ((hW.memLp_scaledHermiteIncrement hsa k).integrable one_le_two))
  · let α := Real.sqrt ((a : ℝ) - s) / Real.sqrt ((u : ℝ) - s)
    let β := Real.sqrt ((u : ℝ) - a) / Real.sqrt ((u : ℝ) - s)
    let X : Ω → ℝ := fun ω ↦ (W a ω - W s ω) / Real.sqrt ((a : ℝ) - s)
    let Z : Ω → ℝ := fun ω ↦ (W u ω - W a ω) / Real.sqrt ((u : ℝ) - a)
    let φ : ℝ × ℝ → ℝ := fun q ↦
      Real.sqrt ((u : ℝ) - s) ^ k * aeval (α * q.1 + β * q.2) (hermite k)
    have hdec := fun ω ↦ decomp_sub_div_sqrt hsa hlt W ω
    have hfn : scaledHermiteIncrement W s k u = fun ω ↦ φ (X ω, Z ω) :=
      funext fun ω ↦ congrArg (fun r ↦ Real.sqrt ((u : ℝ) - s) ^ k * aeval r (hermite k))
        (hdec ω).1
    have hX : Measurable[ℱ a] X :=
      ((hW.adapted a).sub ((hW.adapted s).mono (ℱ.mono hsa) le_rfl)).div_const _
    have hZ : Measurable Z :=
      (((hW.adapted u).mono (ℱ.le u) le_rfl).sub
        ((hW.adapted a).mono (ℱ.le a) le_rfl)).div_const _
    have hφ : StronglyMeasurable φ :=
      (continuous_const.mul ((hermite k).continuous_aeval.comp
        ((continuous_const.mul continuous_fst).add
          (continuous_const.mul continuous_snd)))).stronglyMeasurable
    have hce := condExp_comp_prodMk_ae_eq_integral_of_indep (ℱ.le a) hX hZ
      (hW.indep_comap_sub_div_sqrt hlt.le) hφ
      (hfn ▸ (hW.memLp_scaledHermiteIncrement (hsa.trans hlt.le) k).integrable one_le_two)
    rw [← hfn, (hW.hasLaw_sub_div_sqrt hlt).map_eq] at hce
    refine hce.trans (ae_of_all _ fun ω ↦ ?_)
    dsimp only [φ]
    rw [integral_const_mul, integral_aeval_hermite_mul_add_mul_gaussianReal (hdec ω).2]
    dsimp only [scaledHermiteIncrement, X, α]
    have hus : Real.sqrt ((u : ℝ) - s) ≠ 0 :=
      (Real.sqrt_pos.mpr (sub_pos.mpr (NNReal.coe_lt_coe.mpr (hsa.trans_lt hlt)))).ne'
    rw [div_pow, ← mul_assoc, mul_div_cancel₀ _ (pow_ne_zero k hus)]

private theorem mul_sqrt_pow_cancel {x y z H : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (m : ℕ) :
    Real.sqrt x * Real.sqrt y ^ (m + 1) *
        ((m + 1 : ℝ) * (Real.sqrt x / Real.sqrt y) * (z / Real.sqrt y) ^ m * H) =
      (m + 1 : ℝ) * x * (z ^ m * H) := by
  have hy' : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  rw [pow_succ, div_pow]
  calc Real.sqrt x * (Real.sqrt y ^ m * Real.sqrt y) *
        ((m + 1 : ℝ) * (Real.sqrt x / Real.sqrt y) * (z ^ m / Real.sqrt y ^ m) * H)
    _ = (m + 1 : ℝ) * (Real.sqrt x * Real.sqrt x) * (z ^ m * H) *
        (Real.sqrt y / Real.sqrt y) * (Real.sqrt y ^ m / Real.sqrt y ^ m) := by ring
    _ = (m + 1 : ℝ) * x * (z ^ m * H) := by
      rw [Real.mul_self_sqrt hx, div_self hy', div_self (pow_ne_zero m hy'), mul_one, mul_one]

private theorem condExp_mul_sub_scaledHermiteIncrement_succ
    (hW : IsFilteredPreBrownianReal ℱ W P) {s a b : ℝ≥0} (hsa : s ≤ a) (hab : a < b) (m : ℕ) :
    P[fun ω ↦ (W b ω - W a ω) * scaledHermiteIncrement W s (m + 1) b ω | ℱ a] =ᵐ[P]
      fun ω ↦ (m + 1 : ℝ) * ((b : ℝ) - a) * scaledHermiteIncrement W s m a ω := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let α := Real.sqrt ((a : ℝ) - s) / Real.sqrt ((b : ℝ) - s)
  let β := Real.sqrt ((b : ℝ) - a) / Real.sqrt ((b : ℝ) - s)
  let X : Ω → ℝ := fun ω ↦ (W a ω - W s ω) / Real.sqrt ((a : ℝ) - s)
  let Z : Ω → ℝ := fun ω ↦ (W b ω - W a ω) / Real.sqrt ((b : ℝ) - a)
  let φ : ℝ × ℝ → ℝ := fun q ↦ Real.sqrt ((b : ℝ) - a) * Real.sqrt ((b : ℝ) - s) ^ (m + 1) *
    (q.2 * aeval (α * q.1 + β * q.2) (hermite (m + 1)))
  have hba : 0 < (b : ℝ) - a := sub_pos.mpr (NNReal.coe_lt_coe.mpr hab)
  have hbs : 0 < (b : ℝ) - s := sub_pos.mpr (NNReal.coe_lt_coe.mpr (hsa.trans_lt hab))
  have hdec := fun ω ↦ decomp_sub_div_sqrt hsa hab W ω
  have hfn : (fun ω ↦ (W b ω - W a ω) * scaledHermiteIncrement W s (m + 1) b ω) =
      fun ω ↦ φ (X ω, Z ω) := by
    ext ω
    have hz : W b ω - W a ω = Real.sqrt ((b : ℝ) - a) * Z ω :=
      (mul_div_cancel₀ _ (Real.sqrt_pos.mpr hba).ne').symm
    have hdecX : (W b ω - W s ω) / Real.sqrt ((b : ℝ) - s) = α * X ω + β * Z ω := (hdec ω).1
    simp only [scaledHermiteIncrement, hdecX, φ]; rw [hz]; ring
  have hX : Measurable[ℱ a] X :=
    ((hW.adapted a).sub ((hW.adapted s).mono (ℱ.mono hsa) le_rfl)).div_const _
  have hZ : Measurable Z :=
    (((hW.adapted b).mono (ℱ.le b) le_rfl).sub
      ((hW.adapted a).mono (ℱ.le a) le_rfl)).div_const _
  have hφ : StronglyMeasurable φ :=
    (continuous_const.mul (continuous_snd.mul ((hermite (m + 1)).continuous_aeval.comp
      ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd))))).stronglyMeasurable
  have hsub₂ : MemLp (W b - W a) 2 P := by
    simpa using (hW.hasLaw_sub_of_le hab.le).memLp (memLp_id_gaussianReal 2)
  have hint : Integrable (fun ω ↦ (W b ω - W a ω) * scaledHermiteIncrement W s (m + 1) b ω) P :=
    hsub₂.integrable_mul (hW.memLp_scaledHermiteIncrement (hsa.trans hab.le) (m + 1))
  have hce := condExp_comp_prodMk_ae_eq_integral_of_indep (ℱ.le a) hX hZ
    (hW.indep_comap_sub_div_sqrt hab.le) hφ (hfn ▸ hint)
  rw [← hfn, (hW.hasLaw_sub_div_sqrt hab).map_eq] at hce
  refine hce.trans (ae_of_all _ fun ω ↦ ?_)
  dsimp only [φ]
  rw [integral_const_mul, integral_mul_aeval_hermite_succ_mul_add_mul_gaussianReal (hdec ω).2]
  exact mul_sqrt_pow_cancel hba.le hbs m

private theorem integral_mul_condExp_congr [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {f g k : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (fun ω ↦ f ω * g ω) P) (hg : Integrable g P)
    (hk : P[g | m] =ᵐ[P] k) :
    (∫ ω, f ω * g ω ∂P) = ∫ ω, f ω * k ω ∂P := by
  have : IsFiniteMeasure (P.trim hm) := isFiniteMeasure_trim hm
  rw [← integral_condExp hm (f := fun ω ↦ f ω * g ω)]
  exact (integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hf hfg hg)).trans
    (integral_congr_ae (hk.mono fun ω h ↦ congrArg (f ω * ·) h))

private theorem integral_indicator_mul_sub_hermite_succ (hW : IsFilteredPreBrownianReal ℱ W P)
    {ξ : Ω → ℝ} {s t a b : ℝ≥0} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P)
    (hsa : s ≤ a) (hab : a < b) (hbt : b ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ a] A) (m : ℕ) :
    (∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) *
        (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1))) ∂P) =
      ((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) * ((b : ℝ) - a) *
        ∫ ω, A.indicator ξ ω * scaledHermiteIncrement W s m a ω ∂P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hts' : Real.sqrt ((t : ℝ) - s) ^ (m + 1) ≠ 0 := pow_ne_zero _
    (Real.sqrt_pos.mpr (sub_pos.mpr (NNReal.coe_lt_coe.mpr ((hsa.trans_lt hab).trans_le hbt)))).ne'
  have hηa : StronglyMeasurable[ℱ a] (A.indicator ξ) := (hξ.mono (ℱ.mono hsa)).indicator hA
  have hη₂ : MemLp (A.indicator ξ) 2 P := hξ₂.indicator (ℱ.le a A hA).nullMeasurableSet
  have hηb : StronglyMeasurable[ℱ b] (fun ω ↦ A.indicator ξ ω * (W b ω - W a ω)) :=
    (hηa.mono (ℱ.mono hab.le)).mul
      ((hW.adapted b).sub ((hW.adapted a).mono (ℱ.mono hab.le) le_rfl)).stronglyMeasurable
  have hηb₂ : MemLp (fun ω ↦ A.indicator ξ ω * (W b ω - W a ω)) 2 P :=
    hW.memLp_mul_sub hab.le hηa hη₂
  have hrw1 : (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) *
        (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)))) =
      fun ω ↦ (1 / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) *
        ((A.indicator ξ ω * (W b ω - W a ω)) * scaledHermiteIncrement W s (m + 1) t ω) := by
    ext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, scaledHermiteIncrement]; field_simp [hts']
    · simp only [indicator_of_notMem hω, zero_mul, mul_zero]
  have hst_mem := hW.memLp_scaledHermiteIncrement (hsa.trans (hab.le.trans hbt)) (m + 1)
  rw [hrw1, integral_const_mul, integral_mul_condExp_congr (ℱ.le b) hηb
    (hηb₂.integrable_mul hst_mem) (hst_mem.integrable one_le_two)
    (hW.condExp_scaledHermiteIncrement (hsa.trans hab.le) hbt (m + 1))]
  have hprod_int : Integrable (fun ω ↦ A.indicator ξ ω *
      ((W b ω - W a ω) * scaledHermiteIncrement W s (m + 1) b ω)) P :=
    (hηb₂.integrable_mul (hW.memLp_scaledHermiteIncrement (hsa.trans hab.le) (m + 1))).congr
      (ae_of_all _ fun _ ↦ by dsimp only [Pi.mul_apply]; ring)
  have hsub₂ : MemLp (W b - W a) 2 P := by
    simpa using (hW.hasLaw_sub_of_le hab.le).memLp (memLp_id_gaussianReal 2)
  have hg_int : Integrable (fun ω ↦ (W b ω - W a ω) *
      scaledHermiteIncrement W s (m + 1) b ω) P :=
    hsub₂.integrable_mul (hW.memLp_scaledHermiteIncrement (hsa.trans hab.le) (m + 1))
  have hrw2 : (fun ω ↦ (A.indicator ξ ω * (W b ω - W a ω)) *
        scaledHermiteIncrement W s (m + 1) b ω) =
      fun ω ↦ A.indicator ξ ω *
        ((W b ω - W a ω) * scaledHermiteIncrement W s (m + 1) b ω) := funext fun _ ↦ by ring
  rw [hrw2, integral_mul_condExp_congr (ℱ.le a) hηa hprod_int hg_int
    (hW.condExp_mul_sub_scaledHermiteIncrement_succ hsa hab m)]
  have hrw3 : (fun ω ↦ A.indicator ξ ω *
        ((m + 1 : ℝ) * ((b : ℝ) - a) * scaledHermiteIncrement W s m a ω)) =
      fun ω ↦ ((m + 1 : ℝ) * ((b : ℝ) - a)) *
        (A.indicator ξ ω * scaledHermiteIncrement W s m a ω) := funext fun _ ↦ by ring
  rw [hrw3, integral_const_mul]; ring

private theorem integral_indicator_mul_weighted_inside (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) {ξ : Ω → ℝ} {s t a b T : ℝ≥0}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P)
    (hsa : s ≤ a) (hab : a < b) (hbt : b ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[ℱ a] A) (m : ℕ) :
    (∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) *
        (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1))) ∂P) =
      ∫ p in Ioc a b ×ˢ A, weightedHermiteIntegrand W ξ s t m p ∂ℱ.predictableMeasure P T := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hηa : StronglyMeasurable[ℱ a] (A.indicator ξ) := (hξ.mono (ℱ.mono hsa)).indicator hA
  have hη₂ : MemLp (A.indicator ξ) 2 P := hξ₂.indicator (ℱ.le a A hA).nullMeasurableSet
  rw [hW.integral_indicator_mul_sub_hermite_succ hξ hξ₂ hsa hab hbt hA m,
    ← integral_indicator (measurableSet_predictable_Ioc_prod a b hA)]
  have hsm := (hW.stronglyMeasurable_weightedHermiteIntegrand hpred hξ t m).indicator
    (measurableSet_predictable_Ioc_prod a b hA)
  have hmem := ((ℱ.memLp_predictableMeasure_iff P hsm T 2).mp
    ((hW.memLp_weightedHermiteIntegrand hpred hξ hξ₂ t T m).indicator
      (measurableSet_predictable_Ioc_prod a b hA).nullMeasurableSet)).integrable one_le_two
  rw [ℱ.integral_predictableMeasure P hsm T, integral_prod _ hmem]
  have hslice (u : ℝ≥0) :
      (∫ ω, (Ioc a b ×ˢ A).indicator (weightedHermiteIntegrand W ξ s t m) (u, ω) ∂P) =
        (Ioc a b).indicator (fun _ ↦ ((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) *
          ∫ ω, A.indicator ξ ω * scaledHermiteIncrement W s m a ω ∂P) u := by
    by_cases hu : u ∈ Ioc a b
    · have hust : u ∈ Ioc s t := ⟨hsa.trans_lt hu.1, hu.2.trans hbt⟩
      have hfn : (fun ω ↦ (Ioc a b ×ˢ A).indicator
            (weightedHermiteIntegrand W ξ s t m) (u, ω)) =
          fun ω ↦ ((m + 1 : ℝ) / Real.sqrt ((t : ℝ) - s) ^ (m + 1)) *
            (A.indicator ξ ω * scaledHermiteIncrement W s m u ω) := by
        ext ω
        by_cases hω : ω ∈ A
        · simp only [mem_prod, hu, hω, and_self, indicator_of_mem, weightedHermiteIntegrand,
            hermiteIncrementIntegrand, hust, scaledHermiteIncrement]
          ring
        · simp only [mem_prod, hu, hω, and_false, not_false_eq_true, indicator_of_notMem,
            zero_mul, mul_zero]
      rw [indicator_of_mem hu, hfn, integral_const_mul,
        integral_mul_condExp_congr (ℱ.le a) hηa
          (hη₂.integrable_mul (hW.memLp_scaledHermiteIncrement hust.1.le m))
          ((hW.memLp_scaledHermiteIncrement hust.1.le m).integrable one_le_two)
          (hW.condExp_scaledHermiteIncrement hsa hu.1.le m)]
    · simp only [indicator_of_notMem hu]
      exact integral_eq_zero_of_ae (ae_of_all _ fun ω ↦
        indicator_of_notMem (fun h : (u, ω) ∈ Ioc a b ×ˢ A ↦ hu h.1) _)
  simp_rw [hslice]
  have hlen : (timeMeasure T).real (Ioc a b) = (b : ℝ) - a := by
    rw [measureReal_def, timeMeasure_Ioc, min_eq_left (hbt.trans htT),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hab.le))]
  rw [integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul, hlen]
  ring

private theorem setIntegral_weightedHermiteIntegrand_eq_zero (W : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ)
    {s t a b T : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ a] A) (m : ℕ) (hout : b ≤ s ∨ t ≤ a) :
    (∫ p in Ioc a b ×ˢ A,
      weightedHermiteIntegrand W ξ s t m p ∂ℱ.predictableMeasure P T) = 0 := by
  have hdisj : Disjoint (Ioc a b) (Ioc s t) := by
    rcases hout with hbs | hta
    · exact Set.disjoint_left.mpr fun u hu hst' ↦ not_lt_of_ge (hu.2.trans hbs) hst'.1
    · exact Set.disjoint_left.mpr fun u hu hst' ↦ not_lt_of_ge (hst'.2.trans hta) hu.1
  rw [← integral_indicator (measurableSet_predictable_Ioc_prod a b hA)]
  refine integral_eq_zero_of_ae (ae_of_all _ fun ⟨u, ω⟩ ↦ ?_)
  by_cases hu : u ∈ Ioc a b
  · have hnot : u ∉ Ioc s t := Set.disjoint_left.mp hdisj hu
    by_cases hω : ω ∈ A
    · have hp : (u, ω) ∈ Ioc a b ×ˢ A := ⟨hu, hω⟩
      simp only [Pi.zero_apply, indicator_of_mem hp, weightedHermiteIntegrand,
        hermiteIncrementIntegrand, indicator_of_notMem hnot, mul_zero]
    · exact indicator_of_notMem (fun h : (u, ω) ∈ Ioc a b ×ˢ A ↦ hω h.2) _
  · exact indicator_of_notMem (fun h : (u, ω) ∈ Ioc a b ×ˢ A ↦ hu h.1) _

private theorem integral_indicator_mul_weighted_outside (hW : IsFilteredPreBrownianReal ℱ W P)
    {ξ : Ω → ℝ} {s t a b T : ℝ≥0} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hst : s < t) (hab : a < b) {A : Set Ω} (hA : MeasurableSet[ℱ a] A) (m : ℕ)
    (hout : b ≤ s ∨ t ≤ a) :
    (∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) *
        (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1))) ∂P) = 0 ∧
      (∫ p in Ioc a b ×ˢ A,
        weightedHermiteIntegrand W ξ s t m p ∂ℱ.predictableMeasure P T) = 0 := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨?_, setIntegral_weightedHermiteIntegrand_eq_zero W ξ hA m hout⟩
  have hm : Measurable (fun x : ℝ ↦ aeval x (hermite (m + 1))) :=
    ((hermite (m + 1)).continuous_aeval (A := ℝ)).measurable
  rcases hout with hbs | hta
  · have hleft_meas : Measurable[ℱ s]
        (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) * ξ ω) :=
      (((measurable_const.indicator (ℱ.mono (hab.le.trans hbs) _ hA)).mul
        (((hW.adapted b).mono (ℱ.mono hbs) le_rfl).sub
          ((hW.adapted a).mono (ℱ.mono (hab.le.trans hbs)) le_rfl))).mul hξ.measurable)
    have hind : IndepFun (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) * ξ ω)
        (fun ω ↦ aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1))) P :=
      (hW.indepFun_sub hst.le hleft_meas).comp measurable_id
        (hm.comp (measurable_id.div_const _))
    have hrw : (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) *
          (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)))) =
        fun ω ↦ (A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) * ξ ω) *
          aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)) :=
      funext fun _ ↦ by ring
    have hmean : (∫ ω, aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s))
        (hermite (m + 1)) ∂P) = 0 := by
      have hl := (hW.hasLaw_sub_div_sqrt hst).integral_comp
        (f := fun z ↦ aeval z (hermite (m + 1))) hm.aestronglyMeasurable
      simpa only [Function.comp_def, integral_aeval_hermite_gaussianReal,
        Nat.succ_ne_zero, ↓reduceIte] using hl
    rw [hrw, hind.integral_fun_mul_eq_mul_integral
      (hleft_meas.mono (ℱ.le s) le_rfl).aestronglyMeasurable
      ((hm.comp ((((hW.adapted t).mono (ℱ.le t) le_rfl).sub
        ((hW.adapted s).mono (ℱ.le s) le_rfl)).div_const _)).aestronglyMeasurable),
      hmean, mul_zero]
  · have hY_meas : StronglyMeasurable[ℱ a]
        (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω *
          (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)))) := by
      let : MeasurableSpace Ω := ℱ a
      have hinc : Measurable (fun ω : Ω ↦ (W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) :=
        (((hW.adapted t).mono (ℱ.mono hta) le_rfl).sub
          ((hW.adapted s).mono (ℱ.mono (hst.le.trans hta)) le_rfl)).div_const _
      exact (stronglyMeasurable_const.indicator hA).mul
        ((hξ.mono (ℱ.mono (hst.le.trans hta))).mul (hm.comp hinc).stronglyMeasurable)
    have hrw : (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) *
          (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)))) =
        fun ω ↦ (A.indicator (fun _ ↦ (1 : ℝ)) ω *
          (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)))) *
          (W b ω - W a ω) := funext fun _ ↦ by ring
    rw [hrw]
    exact hW.integral_mul_sub_eq_zero hab.le hY_meas

private def weightedHermiteIntegrandLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) {ξ : Ω → ℝ} {s : ℝ≥0}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) (t T : ℝ≥0) (m : ℕ) :
    Lp ℝ 2 (ℱ.predictableMeasure P T) :=
  (hW.memLp_weightedHermiteIntegrand hpred hξ hξ₂ t T m).toLp
    (weightedHermiteIntegrand W ξ s t m)

private theorem inner_weightedHermiteIntegrand_indicatorConstLp [IsFiniteMeasure P]
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    {ξ : Ω → ℝ} {s t T a b : ℝ≥0} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P)
    (hst : s < t) (htT : t ≤ T) (hab : a < b) (hbT : b ≤ T) {A : Set Ω}
    (hA : MeasurableSet[ℱ a] A) (m : ℕ)
    (hY₂ : MemLp (fun ω ↦ ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s))
      (hermite (m + 1))) 2 P)
    (hcase : b ≤ s ∨ t ≤ a ∨ (s ≤ a ∧ b ≤ t)) :
    (innerSL ℝ (hW.weightedHermiteIntegrandLp hpred hξ hξ₂ t T m))
        (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod a b hA)
          (measure_ne_top (ℱ.predictableMeasure P T) _) (1 : ℝ)) =
      ((innerSL ℝ (hY₂.toLp _)).comp (hW.l2Integral T).toContinuousLinearMap)
        (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod a b hA)
          (measure_ne_top _ _) (1 : ℝ)) := by
  let fLp := hW.weightedHermiteIntegrandLp hpred hξ hξ₂ t T m
  let yLp : Lp ℝ 2 P := hY₂.toLp _
  change (innerSL ℝ fLp) _ = ((innerSL ℝ yLp).comp (hW.l2Integral T).toContinuousLinearMap) _
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    innerSL_apply_apply]
  rw [real_inner_comm _ fLp, L2.inner_indicatorConstLp_one, real_inner_comm _ yLp]
  have hlhs : (∫ p in Ioc a b ×ˢ A, fLp p ∂ℱ.predictableMeasure P T) =
      ∫ p in Ioc a b ×ˢ A, weightedHermiteIntegrand W ξ s t m p ∂ℱ.predictableMeasure P T :=
    setIntegral_congr_ae (measurableSet_predictable_Ioc_prod a b hA)
      (((hW.memLp_weightedHermiteIntegrand hpred hξ hξ₂ t T m).coeFn_toLp).mono fun _ h _ ↦ h)
  have hrhs : ⟪hW.l2Integral T (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod a b hA)
        (measure_ne_top _ _) (1 : ℝ)), yLp⟫_ℝ =
      ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω * (W b ω - W a ω) *
        (ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1))) ∂P := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hab.le hbT hA 1,
      hY₂.coeFn_toLp] with ω h1 h2
    change yLp ω = _ at h2
    simp only [RCLike.inner_apply, conj_trivial]
    rw [h1, h2, mul_comm]
  rw [hlhs, hrhs]
  rcases hcase with hbs | hta | ⟨hsa, hbt⟩
  · have h0 := hW.integral_indicator_mul_weighted_outside (T := T) hξ hst hab hA m (Or.inl hbs)
    exact h0.2.trans h0.1.symm
  · have h0 := hW.integral_indicator_mul_weighted_outside (T := T) hξ hst hab hA m (Or.inr hta)
    exact h0.2.trans h0.1.symm
  · exact (hW.integral_indicator_mul_weighted_inside hpred hξ hξ₂ hsa hab hbt htT hA m).symm

private theorem innerSL_weightedHermiteIntegrand_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) {ξ : Ω → ℝ} {s t T : ℝ≥0}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) (hst : s < t) (htT : t ≤ T) (m : ℕ)
    (hY₂ : MemLp (fun ω ↦ ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s))
      (hermite (m + 1))) 2 P) :
    innerSL ℝ (hW.weightedHermiteIntegrandLp hpred hξ hξ₂ t T m) =
      (innerSL ℝ (hY₂.toLp _)).comp (hW.l2Integral T).toContinuousLinearMap := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure_of_cut T s
    (fun a b hab hbs A hA ↦
      hW.inner_weightedHermiteIntegrand_indicatorConstLp hpred hξ hξ₂ hst htT hab
        (hbs.trans (min_le_right s T)) hA m hY₂ (Or.inl (hbs.trans (min_le_left s T)))) ?_
  intro a b hsa hab hbT A hA
  rcases le_or_gt b t with hbt | hbt
  · exact hW.inner_weightedHermiteIntegrand_indicatorConstLp hpred hξ hξ₂ hst htT hab hbT hA m hY₂
      (Or.inr (Or.inr ⟨hsa, hbt⟩))
  rcases le_or_gt t a with hta | hta
  · exact hW.inner_weightedHermiteIntegrand_indicatorConstLp hpred hξ hξ₂ hst htT hab hbT hA m hY₂
      (Or.inr (Or.inl hta))
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hA' : MeasurableSet[ℱ t] A := ℱ.mono hta.le A hA
  have hsplit : indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
        (measurableSet_predictable_Ioc_prod a b hA) (measure_ne_top _ _) (1 : ℝ) =
      indicatorConstLp 2 (measurableSet_predictable_Ioc_prod a t hA) (measure_ne_top _ _) 1 +
        indicatorConstLp 2 (measurableSet_predictable_Ioc_prod t b hA') (measure_ne_top _ _) 1 := by
    have hdisj : Disjoint (Ioc a t ×ˢ A) (Ioc t b ×ˢ A) :=
      (Ioc_disjoint_Ioc_of_le le_rfl).set_prod_left _ _
    have hunion : Ioc a b ×ˢ A = (Ioc a t ×ˢ A) ∪ (Ioc t b ×ˢ A) := by
      rw [← union_prod, Ioc_union_Ioc_eq_Ioc hta.le hbt.le]
    refine (Lp.ext ?_).trans (indicatorConstLp_disjoint_union
      (measurableSet_predictable_Ioc_prod a t hA) (measurableSet_predictable_Ioc_prod t b hA')
      (measure_ne_top _ _) (measure_ne_top _ _) hdisj (1 : ℝ))
    filter_upwards [indicatorConstLp_coeFn (μ := ℱ.predictableMeasure P T) (p := 2)
      (hs := measurableSet_predictable_Ioc_prod a b hA) (hμs := measure_ne_top _ _) (c := (1 : ℝ)),
      indicatorConstLp_coeFn (μ := ℱ.predictableMeasure P T) (p := 2)
        (hs := (measurableSet_predictable_Ioc_prod a t hA).union
          (measurableSet_predictable_Ioc_prod t b hA'))
        (hμs := measure_ne_top _ _) (c := (1 : ℝ))] with p hp1 hp2
    rw [hp1, hp2, hunion]
  rw [hsplit, map_add, map_add,
    hW.inner_weightedHermiteIntegrand_indicatorConstLp hpred hξ hξ₂ hst htT hta htT hA m hY₂
      (Or.inr (Or.inr ⟨hsa, le_rfl⟩)),
    hW.inner_weightedHermiteIntegrand_indicatorConstLp hpred hξ hξ₂ hst htT hbt hbT hA' m hY₂
      (Or.inr (Or.inl le_rfl))]

private theorem memLp_and_norm_sq_mul_hermite_sub_div_sqrt (hW : IsFilteredPreBrownianReal ℱ W P)
    {ξ : Ω → ℝ} {s t : ℝ≥0} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P)
    (hst : s < t) (m : ℕ) :
    ∃ hY₂ : MemLp (fun ω ↦ ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s))
        (hermite (m + 1))) 2 P,
      ‖hY₂.toLp _‖ ^ 2 = (∫ ω, ξ ω ^ 2 ∂P) * ((m + 1).factorial : ℝ) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm : Measurable (fun x : ℝ ↦ aeval x (hermite (m + 1))) :=
    ((hermite (m + 1)).continuous_aeval (A := ℝ)).measurable
  have hg : MemLp (fun z : ℝ ↦ aeval z (hermite (m + 1))) 2 (gaussianReal 0 1) :=
    (memLp_congr_ae (ae_of_all _ fun z ↦ by simp)).mp
      (memLp_two_aeval_comp_affine_gaussianReal (hermite (m + 1)) 0 1 0 1)
  have hZ₂ := (hW.hasLaw_sub_div_sqrt hst).memLp_fun_comp hg
  have hindY : IndepFun ξ (fun ω ↦ aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s))
      (hermite (m + 1))) P :=
    (hW.indepFun_sub hst.le hξ.measurable).comp measurable_id (hm.comp (measurable_id.div_const _))
  have hY₂ : MemLp (fun ω ↦ ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s))
      (hermite (m + 1))) 2 P := hindY.memLp_two_mul hξ₂ hZ₂
  refine ⟨hY₂, ?_⟩
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hsq_ind : IndepFun (fun ω ↦ ξ ω ^ 2)
      (fun ω ↦ aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)) ^ 2) P :=
    hindY.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hZsq : (∫ ω, aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s))
      (hermite (m + 1)) ^ 2 ∂P) = ((m + 1).factorial : ℝ) := by
    have hl := (hW.hasLaw_sub_div_sqrt hst).integral_comp
      (f := fun z ↦ aeval z (hermite (m + 1)) * aeval z (hermite (m + 1)))
      (hm.mul hm).aestronglyMeasurable
    simpa only [Function.comp_def, sq, integral_hermite_mul_hermite_gaussianReal, ↓reduceIte]
      using hl
  refine (integral_congr_ae ?_).trans
    ((hsq_ind.integral_fun_mul_eq_mul_integral
      ((hξ.mono (ℱ.le s)).pow 2).aestronglyMeasurable
      (hZ₂.aestronglyMeasurable.pow 2)).trans (by rw [hZsq]))
  filter_upwards [hY₂.coeFn_toLp] with ω hω
  simp only [RCLike.inner_apply, conj_trivial, hω]; ring

private theorem coeFn_l2Integral_weightedHermiteIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) {ξ : Ω → ℝ} {s t T : ℝ≥0}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) (hst : s < t) (htT : t ≤ T) (m : ℕ) :
    hW.l2Integral T ((hW.memLp_weightedHermiteIntegrand hpred hξ hξ₂ t T m).toLp
      (weightedHermiteIntegrand W ξ s t m)) =ᵐ[P]
      fun ω ↦ ξ ω * aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)) := by
  let fLp := hW.weightedHermiteIntegrandLp hpred hξ hξ₂ t T m
  obtain ⟨hY₂, hnorm_y⟩ := hW.memLp_and_norm_sq_mul_hermite_sub_div_sqrt hξ hξ₂ hst m
  let yLp : Lp ℝ 2 P := hY₂.toLp _
  have hinner : ⟪yLp, hW.l2Integral T fLp⟫_ℝ = ‖fLp‖ ^ 2 := by
    have heval := congrArg (fun L : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] ℝ ↦ L fLp)
      (hW.innerSL_weightedHermiteIntegrand_eq hpred hξ hξ₂ hst htT m hY₂)
    dsimp only [fLp] at heval ⊢
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      innerSL_apply_apply, real_inner_self_eq_norm_sq] at heval
    exact heval.symm
  have hnorm_f : ‖fLp‖ ^ 2 = (∫ ω, ξ ω ^ 2 ∂P) * ((m + 1).factorial : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine (integral_congr_ae ?_).trans
      (hW.integral_sq_weightedHermiteIntegrand hpred hξ hξ₂ hst htT m)
    filter_upwards [(hW.memLp_weightedHermiteIntegrand hpred hξ hξ₂ t T m).coeFn_toLp] with p hp
    change fLp p = _ at hp
    simp only [RCLike.inner_apply, conj_trivial, hp, sq]
  have hsub : ‖yLp - hW.l2Integral T fLp‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hinner, (hW.l2Integral T).norm_map, hnorm_y, hnorm_f]; ring
  have heq : hW.l2Integral T fLp = yLp :=
    (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsub))).symm
  exact (Filter.EventuallyEq.of_eq (congrArg (⇑) heq)).trans hY₂.coeFn_toLp

/-- For `s < t ≤ T` and a strongly predictable filtered pre-Brownian motion `W`, the terminal
`L²` stochastic integral of `hermiteIncrementIntegrand W s t m` equals the `(m + 1)`-th
probabilists' Hermite polynomial of `(W t - W s) / √(t - s)`. -/
theorem coeFn_l2Integral_hermiteIncrementIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (hpred : IsStronglyPredictable ℱ W) {s t T : ℝ≥0} (hst : s < t) (htT : t ≤ T) (m : ℕ) :
    hW.l2Integral T ((hW.memLp_hermiteIncrementIntegrand hpred s t T m).toLp
      (hermiteIncrementIntegrand W s t m)) =ᵐ[P]
      fun ω ↦ aeval ((W t ω - W s ω) / Real.sqrt ((t : ℝ) - s)) (hermite (m + 1)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have h1 := hW.coeFn_l2Integral_weightedHermiteIntegrand hpred
    (ξ := fun _ ↦ (1 : ℝ)) stronglyMeasurable_const (memLp_const 1) hst htT m
  have hlpeq : (hW.memLp_weightedHermiteIntegrand hpred (ξ := fun _ ↦ (1 : ℝ))
        stronglyMeasurable_const (memLp_const 1) t T m).toLp
        (weightedHermiteIntegrand W (fun _ ↦ 1) s t m) =
      (hW.memLp_hermiteIncrementIntegrand hpred s t T m).toLp
        (hermiteIncrementIntegrand W s t m) := by
    apply Lp.ext
    filter_upwards [(hW.memLp_weightedHermiteIntegrand hpred (ξ := fun _ ↦ (1 : ℝ))
      stronglyMeasurable_const (memLp_const 1) t T m).coeFn_toLp,
      (hW.memLp_hermiteIncrementIntegrand hpred s t T m).coeFn_toLp] with p hp1 hp2
    rw [hp1, hp2]
    by_cases hp : p.1 ∈ Ioc s t <;>
      simp only [weightedHermiteIntegrand, hermiteIncrementIntegrand, hp, not_false_eq_true,
        indicator_of_mem, indicator_of_notMem, one_mul, zero_mul]
  simpa only [hlpeq, one_mul] using h1

/-! ### Finite-grid and arbitrary observation-family `L²` representation -/

private theorem stronglyMeasurable_prod_normalizedBrownianIncrements
    (hW : IsFilteredPreBrownianReal ℱ W P) {n : ℕ} {t' : Fin (n + 1) → ℝ≥0} {s : ℝ≥0}
    (ht' : Monotone t') (hs : ∀ i : Fin n, t' i.succ ≤ s) (a' : Fin n → ℕ) :
    StronglyMeasurable[ℱ s] (fun ω ↦ ∏ i : Fin n,
      aeval (normalizedBrownianIncrements W t' ω i) (hermite (a' i)) /
        Real.sqrt ((a' i).factorial : ℝ)) := by
  let : MeasurableSpace Ω := ℱ s
  refine (Finset.measurable_prod Finset.univ fun i _ ↦ ?_).stronglyMeasurable
  have hi1 : t' i.succ ≤ s := hs i
  have hi0 : t' i.castSucc ≤ s := (ht' Fin.castSucc_lt_succ.le).trans hi1
  have hinc : Measurable (fun ω : Ω ↦ normalizedBrownianIncrements W t' ω i) := by
    rw [funext fun ω ↦ normalizedBrownianIncrements_apply ω i]
    exact (((hW.adapted _).mono (ℱ.mono hi1) le_rfl).sub
      ((hW.adapted _).mono (ℱ.mono hi0) le_rfl)).div_const _
  exact (((hermite (a' i)).continuous_aeval (A := ℝ)).measurable.comp hinc).div_const _

private theorem gaussianVectorHermite_succ_mem_of_isStronglyPredictable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W) {T : ℝ≥0}
    {n : ℕ} {t : Fin (n + 2) → ℝ≥0} (ht : StrictMono t) (htT : ∀ i : Fin (n + 1), t i.succ ≤ T)
    (a : Fin (n + 1) → ℕ)
    (ih : ∀ {t' : Fin (n + 1) → ℝ≥0} (ht' : StrictMono t'), (∀ i : Fin n, t' i.succ ≤ T) →
      ∀ a' : Fin n → ℕ,
      (hW.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht').gaussianVectorHermite
        (measurable_normalizedBrownianIncrements fun i ↦ (hW.adapted _).mono (ℱ.le _) le_rfl) a' ∈
        hW.l2RepresentableSubmodule T) :
    (hW.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
      (measurable_normalizedBrownianIncrements fun i ↦ (hW.adapted _).mono (ℱ.le _) le_rfl) a ∈
      hW.l2RepresentableSubmodule T := by
  let t' : Fin (n + 1) → ℝ≥0 := t ∘ Fin.castSucc
  let a' : Fin n → ℕ := a ∘ Fin.castSucc
  have ht' : StrictMono t' := ht.comp Fin.strictMono_castSucc
  have htT' (i : Fin n) : t' i.succ ≤ T := by
    simpa only [t', Function.comp_apply, ← Fin.castSucc_succ] using htT i.castSucc
  let hmeas := measurable_normalizedBrownianIncrements (B := W) (t := t)
    fun i ↦ (hW.adapted _).mono (ℱ.le _) le_rfl
  let hmeas' := measurable_normalizedBrownianIncrements (B := W) (t := t')
    fun i ↦ (hW.adapted _).mono (ℱ.le _) le_rfl
  let v := (hW.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
    hmeas a
  let v' := (hW.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht').gaussianVectorHermite
    hmeas' a'
  let s : ℝ≥0 := t (Fin.castSucc (Fin.last n))
  let r : ℝ≥0 := t (Fin.last n).succ
  let ξ : Ω → ℝ := fun ω ↦ ∏ i : Fin n,
    aeval (normalizedBrownianIncrements W t' ω i) (hermite (a' i)) /
      Real.sqrt ((a' i).factorial : ℝ)
  have hξ_ae : ⇑v' =ᵐ[P] ξ := HasLaw.coeFn_gaussianVectorHermite _ hmeas' a'
  have hξ_meas : StronglyMeasurable[ℱ s] ξ :=
    hW.stronglyMeasurable_prod_normalizedBrownianIncrements ht'.monotone
      (fun i ↦ ht.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i.succ))) a'
  have hξ₂ : MemLp ξ 2 P := (memLp_congr_ae hξ_ae).mp (Lp.memLp v')
  have hv_ae : ⇑v =ᵐ[P] fun ω ↦ ξ ω *
      (aeval ((W r ω - W s ω) / Real.sqrt ((r : ℝ) - s)) (hermite (a (Fin.last n))) /
        Real.sqrt ((a (Fin.last n)).factorial : ℝ)) := by
    filter_upwards [HasLaw.coeFn_gaussianVectorHermite _ hmeas a] with ω hω
    change v ω = _ at hω; rw [hω, Fin.prod_univ_castSucc]
    simp only [ξ, normalizedBrownianIncrements_apply, t', a', Function.comp_apply,
      Fin.castSucc_succ, r, s]
  change v ∈ hW.l2RepresentableSubmodule T
  rcases hp : a (Fin.last n) with _ | m
  · have heq : v = v' := Lp.ext <| by
      filter_upwards [hv_ae, hξ_ae] with ω hω hω'; simp [hω, hω', hp]
    exact heq ▸ ih ht' htT' a'
  · let c : ℝ := (Real.sqrt ((m + 1).factorial : ℝ))⁻¹
    let fLp := hW.weightedHermiteIntegrandLp hpred hξ_meas hξ₂ r T m
    have heq : v = c • hW.l2Integral T fLp := Lp.ext <| by
      filter_upwards [hv_ae, Lp.coeFn_smul c (hW.l2Integral T fLp),
        hW.coeFn_l2Integral_weightedHermiteIntegrand hpred hξ_meas hξ₂ (ht Fin.castSucc_lt_succ)
          (htT (Fin.last n)) m] with ω hω hsmul hint
      change (hW.l2Integral T fLp) ω = _ at hint
      rw [hω, hp, hsmul, Pi.smul_apply, smul_eq_mul, hint]; dsimp only [c]; ring
    exact heq ▸ (hW.l2RepresentableSubmodule T).smul_mem c
      (hW.l2Integral_mem_l2RepresentableSubmodule T fLp)

private theorem gaussianVectorHermite_mem_of_isStronglyPredictable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W) {T : ℝ≥0} :
    ∀ {n : ℕ} {t : Fin (n + 1) → ℝ≥0} (ht : StrictMono t) (_ : ∀ i : Fin n, t i.succ ≤ T)
      (a : Fin n → ℕ),
      (hW.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
        (measurable_normalizedBrownianIncrements fun i ↦ (hW.adapted _).mono (ℱ.le _) le_rfl) a ∈
        hW.l2RepresentableSubmodule T
  | 0, t, ht, _, a => by
    refine hW.const_mem_l2RepresentableSubmodule T (c := 1) ?_
    filter_upwards [HasLaw.coeFn_gaussianVectorHermite
      (hW.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht)
      (measurable_normalizedBrownianIncrements fun i ↦ (hW.adapted _).mono (ℱ.le _) le_rfl) a]
      with ω hω
    simpa using hω
  | n + 1, t, ht, htT, a =>
    hW.gaussianVectorHermite_succ_mem_of_isStronglyPredictable hpred ht htT a
      (gaussianVectorHermite_mem_of_isStronglyPredictable hW hpred)

/-- On any strictly increasing finite grid with right endpoint at most `T`, every multidimensional
Hermite product of standardized Brownian increments belongs to `l2RepresentableSubmodule T`. No
path continuity or predictability assumption on `B` is needed. -/
theorem gaussianVectorHermite_mem_l2RepresentableSubmodule {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredPreBrownianReal ℱ B P) {T : ℝ≥0} {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : StrictMono t) (htT : ∀ i : Fin n, t i.succ ≤ T) (a : Fin n → ℕ) :
    (hB.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
      (measurable_normalizedBrownianIncrements fun i ↦ (hB.adapted _).mono (ℱ.le _) le_rfl) a ∈
      hB.l2RepresentableSubmodule T := by
  obtain ⟨W, hWpred, hW, hae⟩ := hB.exists_isStronglyPredictable_ae_eq
  have hsub : hB.l2RepresentableSubmodule T = hW.l2RepresentableSubmodule T := by
    simp only [l2RepresentableSubmodule, hB.l2Integral_congr hW fun s _ ↦ (hae s).symm]
  have hinc : normalizedBrownianIncrements B t =ᵐ[P] normalizedBrownianIncrements W t := by
    have hall : ∀ᵐ ω ∂P, ∀ i : Fin (n + 1), W (t i) ω = B (t i) ω :=
      ae_all_iff.mpr fun i ↦ hae (t i)
    filter_upwards [hall] with ω hω
    ext i
    simp only [normalizedBrownianIncrements_apply, hω]
  let hmeasB := measurable_normalizedBrownianIncrements (B := B) (t := t)
    fun i ↦ (hB.adapted _).mono (ℱ.le _) le_rfl
  let hmeasW := measurable_normalizedBrownianIncrements (B := W) (t := t)
    fun i ↦ (hW.adapted _).mono (ℱ.le _) le_rfl
  have hv : (hB.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
        hmeasB a =
      (hW.toIsPreBrownianReal.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
        hmeasW a := by
    apply Lp.ext
    filter_upwards [HasLaw.coeFn_gaussianVectorHermite _ hmeasB a,
      HasLaw.coeFn_gaussianVectorHermite _ hmeasW a, hinc] with ω h1 h2 h3
    rw [h1, h2, h3]
  rw [hsub, hv]
  exact hW.gaussianVectorHermite_mem_of_isStronglyPredictable hWpred ht htT a

private theorem mem_l2RepresentableSubmodule_of_finite_comap
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} {ι : Type*} [Finite ι] {t : ι → ℝ≥0}
    (htT : ∀ i, t i ≤ T) {u : Lp ℝ 2 P}
    (hu : AEStronglyMeasurable[MeasurableSpace.comap (fun ω i ↦ W (t i) ω) inferInstance] u P) :
    u ∈ hW.l2RepresentableSubmodule T := by
  classical
  cases nonempty_fintype ι
  let S : Finset ℝ≥0 := insert 0 (Finset.univ.image t)
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨0, Finset.mem_insert_self 0 _⟩)
  let grid : Fin (m + 1) → ℝ≥0 := S.orderEmbOfFin hm
  have hgrid_mono : StrictMono grid := (S.orderEmbOfFin hm).strictMono
  have hgrid0 : grid 0 = 0 := by
    have h0 : grid 0 = S.min' ⟨0, Finset.mem_insert_self 0 _⟩ :=
      S.orderEmbOfFin_zero hm (Nat.succ_pos m)
    exact le_antisymm (h0 ▸ Finset.min'_le S 0 (Finset.mem_insert_self 0 _)) bot_le
  have hgridT (j : Fin m) : grid j.succ ≤ T := by
    have hmem : grid j.succ ∈ S := Finset.orderEmbOfFin_mem S hm j.succ
    rcases Finset.mem_insert.mp hmem with h0 | himg
    · exact h0.le.trans bot_le
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp himg
      exact hi ▸ htT i
  have hle : MeasurableSpace.comap (fun ω i ↦ W (t i) ω) inferInstance ≤
      MeasurableSpace.comap (fun ω j ↦ W (grid j) ω) inferInstance := by
    simp only [MeasurableSpace.comap_process_pi]
    refine iSup_le fun i ↦ ?_
    have hmem : t i ∈ Set.range grid := by
      rw [Finset.range_orderEmbOfFin S hm]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem t (Finset.mem_univ i))
    obtain ⟨j, hj⟩ := hmem
    exact hj ▸ le_iSup (fun j ↦ MeasurableSpace.comap (W (grid j)) inferInstance) j
  let hmeas := measurable_normalizedBrownianIncrements (B := W) (t := grid)
    fun j ↦ (hW.adapted _).mono (ℱ.le _) le_rfl
  have hsum := hW.toIsPreBrownianReal.hasSum_gaussianVectorHermite_of_aestronglyMeasurable_comap
    hgrid_mono hgrid0 hmeas u (hu.mono hle)
  exact (hW.isClosed_l2RepresentableSubmodule T).mem_of_tendsto hsum
    (Eventually.of_forall fun F ↦ Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
      (hW.gaussianVectorHermite_mem_l2RepresentableSubmodule hgrid_mono hgridT a))

private theorem mem_l2RepresentableSubmodule_of_nat_comap
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} {s : ℕ → ℝ≥0} (hsT : ∀ n, s n ≤ T)
    {u : Lp ℝ 2 P}
    (hu : AEStronglyMeasurable[⨆ n : ℕ, MeasurableSpace.comap (W (s n)) inferInstance] u P) :
    u ∈ hW.l2RepresentableSubmodule T := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let 𝒢 : Filtration ℕ mΩ :=
    { seq N := ⨆ j : Fin N, MeasurableSpace.comap (W (s j)) inferInstance
      mono' M N hMN := iSup_le fun j ↦
        le_iSup (fun k : Fin N ↦ MeasurableSpace.comap (W (s k)) inferInstance) (j.castLE hMN)
      le' N := iSup_le fun j ↦ ((hW.adapted _).mono (ℱ.le _) le_rfl).comap_le }
  have hiSup : (⨆ N, 𝒢 N) = ⨆ n : ℕ, MeasurableSpace.comap (W (s n)) inferInstance :=
    le_antisymm
      (iSup_le fun N ↦ iSup_le fun j ↦
        le_iSup (fun n : ℕ ↦ MeasurableSpace.comap (W (s n)) inferInstance) j.1)
      (iSup_le fun n ↦ le_iSup_of_le (n + 1)
        (le_iSup (fun j : Fin (n + 1) ↦ MeasurableSpace.comap (W (s j)) inferInstance)
          (Fin.last n)))
  have hu_sup : AEStronglyMeasurable[⨆ N, 𝒢 N] u P := hiSup ▸ hu
  have hmem (N : ℕ) : MemLp (P[u | 𝒢 N]) 2 P := (Lp.memLp u).condExp (m := 𝒢 N) one_le_two
  let uSeq (N : ℕ) : Lp ℝ 2 P := (hmem N).toLp (P[u | 𝒢 N])
  have huSeq_mem (N : ℕ) : uSeq N ∈ hW.l2RepresentableSubmodule T := by
    have hmN : AEStronglyMeasurable[MeasurableSpace.comap
        (fun ω (j : Fin N) ↦ W (s j) ω) inferInstance] (uSeq N) P := by
      rw [MeasurableSpace.comap_process_pi]
      exact stronglyMeasurable_condExp.aestronglyMeasurable.congr (hmem N).coeFn_toLp.symm
    exact hW.mem_l2RepresentableSubmodule_of_finite_comap (t := fun j : Fin N ↦ s j)
      (fun j ↦ hsT j) hmN
  have htend : Tendsto uSeq atTop (𝓝 u) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hce := condExp_of_aestronglyMeasurable' (iSup_le 𝒢.le) hu_sup
      ((Lp.memLp u).integrable one_le_two)
    refine ((Lp.memLp u).tendsto_eLpNorm_condExp (ℱ := 𝒢) ENNReal.ofNat_ne_top).congr fun N ↦ ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hmem N).coeFn_toLp, hce] with ω h1 h2
    change uSeq N ω = _ at h1
    simp only [Pi.sub_apply, h1, h2]
  exact (hW.isClosed_l2RepresentableSubmodule T).mem_of_tendsto htend
    (Eventually.of_forall huSeq_mem)

/-- Every square-integrable random variable measurable, up to null sets, from any family of
Brownian observations at times bounded by `T` belongs to `l2RepresentableSubmodule T`. The index
type `ι` may be finite, countable, or uncountable, and no path continuity is assumed. -/
theorem mem_l2RepresentableSubmodule_of_aestronglyMeasurable_comap
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} {ι : Type*} {t : ι → ℝ≥0}
    (htT : ∀ i, t i ≤ T) {u : Lp ℝ 2 P}
    (hu : AEStronglyMeasurable[MeasurableSpace.comap (fun ω i ↦ W (t i) ω) inferInstance] u P) :
    u ∈ hW.l2RepresentableSubmodule T := by
  have hu_mk : Measurable[⨆ i : ι, MeasurableSpace.comap (W (t i)) inferInstance] (hu.mk u) := by
    rw [← MeasurableSpace.comap_process_pi]
    exact hu.stronglyMeasurable_mk.measurable
  obtain ⟨I, hIcount, hImeas⟩ := hu_mk.exists_countable_iSup
  rcases I.eq_empty_or_nonempty with rfl | hInonempty
  · have hle : (⨆ i ∈ (∅ : Set ι), MeasurableSpace.comap (W (t i)) inferInstance) ≤
        MeasurableSpace.comap (fun ω (i : Fin 0) ↦ W (i.elim0) ω) inferInstance := by
      simp only [mem_empty_iff_false, iSup_false, iSup_bot, bot_le]
    exact hW.mem_l2RepresentableSubmodule_of_finite_comap (t := Fin.elim0) (fun i ↦ i.elim0)
      ((hImeas.mono hle le_rfl).stronglyMeasurable.aestronglyMeasurable.congr hu.ae_eq_mk.symm)
  · obtain ⟨idx, rfl⟩ := hIcount.exists_eq_range hInonempty
    have hle : (⨆ i ∈ Set.range idx, MeasurableSpace.comap (W (t i)) inferInstance) ≤
        ⨆ n : ℕ, MeasurableSpace.comap (W (t (idx n))) inferInstance := by
      rw [iSup_range]
    exact hW.mem_l2RepresentableSubmodule_of_nat_comap (fun n ↦ htT (idx n))
      ((hImeas.mono hle le_rfl).stronglyMeasurable.aestronglyMeasurable.congr hu.ae_eq_mk.symm)

/-- **Terminal `L²` Brownian representation for arbitrary observation families.** Every `u ∈ L²(P)`
measurable, up to `P`-null sets, with respect to Brownian observations at times `t i ≤ T` admits a
unique predictable `L²` integrand `f` representing `u - E[u]`. -/
theorem existsUnique_l2Integral_of_aestronglyMeasurable_comap
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} {ι : Type*} {t : ι → ℝ≥0}
    (htT : ∀ i, t i ≤ T) {u : Lp ℝ 2 P}
    (hu : AEStronglyMeasurable[MeasurableSpace.comap (fun ω i ↦ W (t i) ω) inferInstance] u P) :
    ∃! f : Lp ℝ 2 (ℱ.predictableMeasure P T),
      ⇑u =ᵐ[P] fun ω ↦ (∫ ω', u ω' ∂P) + hW.l2Integral T f ω :=
  hW.existsUnique_l2Integral_of_mem_l2RepresentableSubmodule
    (hW.mem_l2RepresentableSubmodule_of_aestronglyMeasurable_comap htT hu)

end TauCeti.Probability.IsFilteredPreBrownianReal

/-! ### Natural and usual Brownian filtration representations -/

private theorem aestronglyMeasurable_of_forall_exists_ae_eq
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ mΩ)
    (h : ∀ s, MeasurableSet[m₂] s → ∃ t, MeasurableSet[m₁] t ∧ s =ᵐ[P] t)
    {u : Lp ℝ 2 P} (hu : AEStronglyMeasurable[m₂] u P) :
    AEStronglyMeasurable[m₁] u P := by
  have : IsFiniteMeasure (P.trim (hm₁₂.trans hm₂)) := isFiniteMeasure_trim (hm₁₂.trans hm₂)
  have hce₁ := TauCeti.MeasureTheory.condExp_ae_eq_of_forall_exists_ae_eq (f := (u : Ω → ℝ))
    hm₁₂ hm₂ h
  have hce₂ := condExp_of_aestronglyMeasurable' hm₂ hu ((Lp.memLp u).integrable one_le_two)
  exact stronglyMeasurable_condExp.aestronglyMeasurable.congr (hce₁.symm.trans hce₂)

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- **Terminal `L²` martingale representation on the raw natural Brownian filtration.** Every
square-integrable claim measurable, up to `P`-null sets, with respect to
`Filtration.natural W hmeas T` admits a unique predictable `L²` integrand on
`(Filtration.natural W hmeas).predictableMeasure P T`. No path continuity is required. -/
theorem existsUnique_l2Integral_natural (hW : IsPreBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (T : ℝ≥0) {u : Lp ℝ 2 P}
    (hu : AEStronglyMeasurable[Filtration.natural W hmeas T] u P) :
    ∃! f : Lp ℝ 2 ((Filtration.natural W hmeas).predictableMeasure P T),
      ⇑u =ᵐ[P] fun ω ↦
        (∫ ω', u ω' ∂P) + (hW.isFilteredPreBrownianReal_natural hmeas).l2Integral T f ω := by
  rw [Filtration.natural_eq_comap] at hu
  exact (hW.isFilteredPreBrownianReal_natural hmeas)
    |>.existsUnique_l2Integral_of_aestronglyMeasurable_comap (fun s : Iic T ↦ s.2) hu

/-- **Terminal `L²` martingale representation on the ambient-null-augmented natural Brownian
filtration.** Every square-integrable claim measurable, up to `P`-null sets, with respect to
`(Filtration.natural W hmeas).ambientNullAugmentation P T` admits a unique predictable `L²`
integrand on that filtration, without completing the ambient measurable space or assuming path
continuity. -/
theorem existsUnique_l2Integral_ambientNullAugmentation_natural (hW : IsPreBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (T : ℝ≥0) {u : Lp ℝ 2 P}
    (hu : AEStronglyMeasurable[(Filtration.natural W hmeas).ambientNullAugmentation P T] u P) :
    ∃! f : Lp ℝ 2
        (((Filtration.natural W hmeas).ambientNullAugmentation P).predictableMeasure P T),
      ⇑u =ᵐ[P] fun ω ↦ (∫ ω', u ω' ∂P) +
        (hW.isFilteredPreBrownianReal_natural hmeas).ambientNullAugmentation.l2Integral T f ω := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ℱ := Filtration.natural W hmeas
  have hu' : AEStronglyMeasurable[ℱ T] u P :=
    aestronglyMeasurable_of_forall_exists_ae_eq (ℱ.le_ambientNullAugmentation P T)
      ((ℱ.ambientNullAugmentation P).le T)
      (fun s hs ↦ ((ℱ.measurableSet_ambientNullAugmentation_iff P T s).mp hs).2) hu
  rw [Filtration.natural_eq_comap] at hu'
  exact (hW.isFilteredPreBrownianReal_natural hmeas).ambientNullAugmentation
    |>.existsUnique_l2Integral_of_aestronglyMeasurable_comap (fun s : Iic T ↦ s.2) hu'

end ProbabilityTheory.IsPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- **Terminal `L²` martingale representation on the original-space right-continuous augmented
natural Brownian filtration.** -/
theorem existsUnique_l2Integral_rightCont_ambientNullAugmentation_natural
    (hW : IsBrownianReal W P) (hmeas : ∀ t, StronglyMeasurable (W t)) (T : ℝ≥0) {u : Lp ℝ 2 P}
    (hu : AEStronglyMeasurable[((Filtration.natural W
      hmeas).ambientNullAugmentation P).rightCont T] u P) :
    let hWF := ((hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural
      hmeas).ambientNullAugmentation).rightCont
      (fun _ ↦ hW.cont.mono fun _ hω ↦ hω.continuousAt.continuousWithinAt)
    ∃! f : Lp ℝ 2
        ((((Filtration.natural W hmeas).ambientNullAugmentation P).rightCont).predictableMeasure
          P T),
      ⇑u =ᵐ[P] fun ω ↦ (∫ ω', u ω' ∂P) + hWF.l2Integral T f ω := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ℱ := Filtration.natural W hmeas
  let 𝒢 := (ℱ.ambientNullAugmentation P).rightCont
  have hrc : (ℱ.nullAugment P).IsRightContinuous := hW.isRightContinuous_nullAugment_natural hmeas
  have hle : 𝒢 T ≤ ℱ.nullAugment P T := by
    calc 𝒢 T ≤ (ℱ.nullAugment P).rightCont T := by
          rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
          exact iInf₂_mono fun r _ ↦ by
            rw [Filtration.ambientNullAugmentation_apply]; exact inf_le_right
      _ = ℱ.nullAugment P T := by rw [Filtration.IsRightContinuous.eq]
  have hu' : AEStronglyMeasurable[ℱ T] u P :=
    aestronglyMeasurable_of_forall_exists_ae_eq
      ((ℱ.le_ambientNullAugmentation P T).trans ((ℱ.ambientNullAugmentation P).le_rightCont T))
      (𝒢.le T) (fun s hs ↦ (ℱ.measurableSet_nullAugment_iff P T s).mp (hle s hs)) hu
  rw [Filtration.natural_eq_comap] at hu'
  exact (((hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural
      hmeas).ambientNullAugmentation).rightCont
      (fun _ ↦ hW.cont.mono fun _ hω ↦ hω.continuousAt.continuousWithinAt))
    |>.existsUnique_l2Integral_of_aestronglyMeasurable_comap (fun s : Iic T ↦ s.2) hu'

/-- **Terminal `L²` martingale representation on the usual completed right-continuous natural
Brownian filtration.** For any Brownian motion `W` on `(Ω, mΩ, P)` with measurable evaluations,
every `u ∈ L²(P.completion)` measurable, up to null sets, with respect to
`((Filtration.natural W hmeas).nullAugment P).rightCont T` admits a unique predictable `L²`
integrand representing `u - E[u]` on that usual Brownian filtration. -/
theorem existsUnique_l2Integral_rightCont_nullAugment_natural
    (hW : IsBrownianReal W P) (hmeas : ∀ t, StronglyMeasurable (W t)) (T : ℝ≥0)
    {u : Lp ℝ 2 P.completion}
    (hu : @AEStronglyMeasurable (NullMeasurableSpace Ω P) ℝ _
      (((Filtration.natural W hmeas).nullAugment P).rightCont T) _ u P.completion) :
    ∃! f : Lp ℝ 2
        ((((Filtration.natural W hmeas).nullAugment P).rightCont).predictableMeasure
          P.completion T),
      ⇑u =ᵐ[P.completion] fun ω ↦ (∫ ω', u ω' ∂P.completion) +
        (hW.isFilteredPreBrownianReal_rightCont_nullAugment_natural hmeas).l2Integral T f ω := by
  let hWF := hW.isFilteredPreBrownianReal_rightCont_nullAugment_natural hmeas
  let := (hWF.hasLaw_eval 0).isProbabilityMeasure
  let ℱ := Filtration.natural W hmeas
  let 𝒰 := (ℱ.nullAugment P).rightCont
  have hrc : (ℱ.nullAugment P).IsRightContinuous := hW.isRightContinuous_nullAugment_natural hmeas
  have h𝒰 : 𝒰 T = ℱ.nullAugment P T := by
    dsimp only [𝒰]
    rw [Filtration.IsRightContinuous.eq]
  have hu' : @AEStronglyMeasurable (NullMeasurableSpace Ω P) ℝ _ (ℱ T) _ u P.completion :=
    @aestronglyMeasurable_of_forall_exists_ae_eq (NullMeasurableSpace Ω P) (ℱ T) (𝒰 T)
      inferInstance P.completion _
      ((ℱ.le_nullAugment P T).trans (ℱ.nullAugment P |>.le_rightCont T)) (𝒰.le T)
      (fun s hs ↦ by
        obtain ⟨t, ht, hst⟩ := (ℱ.measurableSet_nullAugment_iff P T s).mp (h𝒰 ▸ hs)
        exact ⟨t, ht, P.ae_completion.symm ▸ hst⟩) u hu
  rw [Filtration.natural_eq_comap] at hu'
  exact hWF.existsUnique_l2Integral_of_aestronglyMeasurable_comap (fun s : Iic T ↦ s.2) hu'

end ProbabilityTheory.IsBrownianReal
