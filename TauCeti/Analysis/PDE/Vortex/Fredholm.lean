/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import TauCeti.Analysis.PDE.Vortex.KernelDimension
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Fredholm property and index of the gauge-fixed vortex operator on `H¹`

At a plane field `x = (b₁, b₂, p, q)` with `L∞` class `a`, the gauge-fixed vortex operator
`L_x = d₀* ⊕ d₁` is realized as a bounded real-linear operator
`TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`
on four-component `W^{1,2}(ℂ)` fields. At a `C¹` vortex with `|α| → 1` and `∇₁ α → 0` at infinity,
`TauCeti.Analysis.PDE.Vortex.SobolevRealization` shows by a Gårding estimate and Rellich
compactness that its kernel is finite dimensional and its range is closed. This file completes the
Fredholm theory of `L_x` on `H¹`: it proves that the cokernel vanishes with a bounded `H¹` right
inverse, identifies the `H¹` kernel with the classical `C²` kernel `TauCeti.Vortex.gaugeFixedKernel`
and with the space of principal parts at the zero divisor of `α`, and computes the real Fredholm
index `2 |D|` (hence `2m` in degree `m`).

## Mathematical overview

1. **Weak formulation (`integral_inner_sobolevGaugeFixedOperator`).** Test fields are dense in
   `H¹(ℂ)⁴`, so Green's identity `TauCeti.Vortex.integral_inner_gaugeFixedOperator` extends from
   smooth compactly supported variations to all `y ∈ H¹(ℂ)⁴`, first for `a = 0` by continuity of
   the `L²` pairings and then for general `a ∈ L∞` by adding the pointwise zeroth-order pairing.
   Thus `sobolevGaugeFixedOperator a y = f` holds if and only if the coordinate values of `y` solve
   `L_x y = f` weakly against smooth compactly supported test fields
   (`sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq`).

2. **Surjectivity and bounded right inverse (`surjective_sobolevGaugeFixedOperator`,
   `exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id`).** At a `C¹` vortex `x` with
   `|α| → 1` at infinity and `L∞` class `a`, the coordinates of `x` are bounded by `‖a‖`. The weak
   right inverse `Q` on `L²`
   (`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`)
   takes values in `H¹` by elliptic regularity
   (`TauCeti.Vortex.mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`), hence lifts by
   Calderón's theorem (`TemperedDistribution.exists_w1p_value_ae_eq_of_mem_realSobolevFunctions`) to
   `H¹(ℂ)⁴`. Since weak gradients are determined by values (`TauCeti.W1p.ext_value`), the lifted
   map is linear and has sequentially closed graph over `L²`, so the closed graph theorem makes it a
   bounded right inverse `R : L²(ℂ; ℝ⁴) →L[ℝ] H¹(ℂ)⁴`, `L²`-orthogonal to the `H¹` kernel and
   satisfying the exponentially weighted `L²` bound of
   `TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq` for rates
   `|c| < 1 / 2`.

3. **Kernel identification (`ofGaugeFixedKernel`, `kerSobolevGaugeFixedOperatorEquiv`,
   `principalPartMap_bijective`).** Every element of the classical `C²` square-integrable kernel
   `gaugeFixedKernel x` is a weak `L²` kernel element, hence lies in `H¹` when `x` is continuous and
   bounded (`ofGaugeFixedKernel`). Conversely, when `x` is smooth with bounded derivatives through
   order `3`, the elliptic bootstrap puts every weak `L²` kernel element in `H⁴(ℂ)⁴`, which embeds
   into `C²(ℂ)⁴` by Sobolev embedding
   (`TemperedDistribution.exists_contDiff_ae_eq_of_mem_realSobolevFunctions`),
   yielding a linear isomorphism `kerSobolevGaugeFixedOperatorEquiv` between
   `(sobolevGaugeFixedOperator a).ker` and `gaugeFixedKernel x`. At a smooth field with vanishing
   holomorphicity rows, `|α| → 1`, and zero divisor `D`, `gaugeFixedKernel x` has real dimension
   `2 |D|` (`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`), matching the real dimension
   of `D.ToType → ℂ`; hence Samols's injective principal-part map `TauCeti.Vortex.principalPartMap`
   is bijective (`principalPartMap_bijective`) and identifies `(sobolevGaugeFixedOperator a).ker`
   with `ℂ^|D|` (`exists_ker_sobolevGaugeFixedOperator_linearEquiv`).

4. **Fredholmness and real index `2 |D|` (`isFredholm_sobolevGaugeFixedOperator`,
   `index_sobolevGaugeFixedOperator_eq_two_mul_card`,
   `index_sobolevGaugeFixedOperator_eq_two_mul`).** At a `C²` vortex with `|α| → 1`, exponential
   decay of `d_a α` (`TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp`) supplies
   `∇₁ α → 0` automatically, so finite-dimensional kernel and surjectivity make
   `sobolevGaugeFixedOperator a` Fredholm. At a smooth vortex with bounded derivatives through order
   `3` (in particular at any continuous vortex lying in every framed Sobolev space `A_m^k`), its
   kernel has real dimension `2 |D|` (`2m` in degree `m`) and its real Fredholm index is `2 |D|`
   (`2m` in degree `m`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient NNReal RealInnerProductSpace Topology

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### Weak formulation of the `H¹` realization -/

/-- Assembles the `L²` values of the four coordinates of an `H¹` variation into an `L²` field
with values in `ℝ⁴`. -/
private def sobolevValueL :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  ∑ j : Fin 4, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).compLpL 2 μ⊤).comp
      ((W1p.valueL).comp (ContinuousLinearMap.proj j))

private theorem sobolevValueL_apply_ae (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevValueL y =ᵐ[μ⊤] fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z := by
  have hv : ∀ᵐ z ∂μ⊤, ∀ j : Fin 4,
      (ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j))) z =
          W1p.value (y j) z • EuclideanSpace.single j (1 : ℝ) :=
    ae_all_iff.2 fun j ↦ (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).coeFn_compLpL (W1p.value (y j))
  filter_upwards [Lp.coeFn_finsetSum (μ := μ⊤) (p := 2) Finset.univ fun j : Fin 4 ↦
    ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j)), hv] with z hsum hz
  simp only [sobolevValueL, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, W1p.valueL_apply]
  rw [hsum, Finset.sum_apply, Finset.sum_congr rfl fun j _ ↦ hz j]
  ext i
  simp [EuclideanSpace.single, Pi.single_apply]

private theorem integral_inner_sobolevGaugeFixedOperator_zero_ofTestFunction
    (φ : Fin 4 → 𝓓(⊤, ℝ)) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ z, ⟪sobolevGaugeFixedOperator 0 (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z, η z⟫) =
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z),
        gaugeFixedAdjoint 0 η z⟫ := by
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ φ j z
  have hY : ContDiff ℝ 1 Y := (contDiff_euclidean.2 fun j ↦ (φ j).contDiff).of_le (by simp)
  have ha0 : (0 : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) =ᵐ[μ⊤] (0 : ℂ → EuclideanSpace ℝ (Fin 4)) :=
    Lp.coeFn_zero _ _ _
  have hL := sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator ha0 hY
    fun j ↦ W1p.value_ofTestFunctionₗ_ae (φ j)
  have hV : ∀ᵐ z ∂volume,
      (WithLp.toLp 2 fun j ↦ W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z) = Y z := by
    filter_upwards [ae_all_iff.2 fun j ↦
      W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) (φ j)] with z hz
    ext j; exact hz j
  simp only [Opens.coe_top, Measure.restrict_univ] at hL
  have hint₁ : (∫ z, ⟪sobolevGaugeFixedOperator 0
      (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z, η z⟫) =
        ∫ z, ⟪gaugeFixedOperator 0 Y z, η z⟫ :=
    integral_congr_ae (hL.mono fun z hz ↦ congrArg (⟪·, η z⟫) hz)
  have hint₂ : (∫ z, ⟪WithLp.toLp 2
      (fun j ↦ W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z),
        gaugeFixedAdjoint 0 η z⟫) =
        ∫ z, ⟪Y z, gaugeFixedAdjoint 0 η z⟫ :=
    integral_congr_ae (hV.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint 0 η z⟫) hz)
  rw [hint₁, hint₂]
  exact integral_inner_gaugeFixedOperator continuous_zero hY hη (.inr hηc)

/-- At zero background field, integration by parts holds on `H¹(ℂ)⁴` against compactly supported
`C¹` test fields, by density of smooth test functions in `H¹(ℂ)`. -/
private theorem integral_inner_sobolevGaugeFixedOperator_zero
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevGaugeFixedOperator 0 y z, η z⟫ =
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint 0 η z⟫ := by
  have : μ⊤.IsAddHaarMeasure := by rw [Opens.coe_top, Measure.restrict_univ]; infer_instance
  have hηL : MemLp η 2 μ⊤ := hη.continuous.memLp_of_hasCompactSupport hηc
  have hAηL : MemLp (gaugeFixedAdjoint 0 η) 2 μ⊤ :=
    (continuous_gaugeFixedAdjoint continuous_zero hη).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  have hLHS (v : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      (∫ z, ⟪sobolevGaugeFixedOperator 0 v z, η z⟫) =
        ⟪sobolevGaugeFixedOperator 0 v, hηL.toLp η⟫ := by
    rw [L2.inner_toLp (sobolevGaugeFixedOperator 0 v) hηL]
    simp [Opens.coe_top, Measure.restrict_univ]
  have hRHS (v : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      (∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (v j) z), gaugeFixedAdjoint 0 η z⟫) =
        ⟪sobolevValueL v, hAηL.toLp (gaugeFixedAdjoint 0 η)⟫ := by
    rw [L2.inner_toLp (sobolevValueL v) hAηL]
    have hv := sobolevValueL_apply_ae v
    simp only [Opens.coe_top, Measure.restrict_univ] at hv ⊢
    exact integral_congr_ae (hv.mono fun z hz ↦ by dsimp only at hz ⊢; rw [hz])
  have hc₁ : Continuous fun v ↦ ⟪sobolevGaugeFixedOperator 0 v, hηL.toLp η⟫ :=
    (sobolevGaugeFixedOperator 0).continuous.inner continuous_const
  have hc₂ : Continuous fun v ↦ ⟪sobolevValueL v, hAηL.toLp (gaugeFixedAdjoint 0 η)⟫ :=
    sobolevValueL.continuous.inner continuous_const
  rw [hLHS, hRHS]
  refine congr_fun ((DenseRange.piMap fun _ : Fin 4 ↦
    W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).equalizer
      hc₁ hc₂ (funext fun φ ↦ ?_)) y
  change ⟪sobolevGaugeFixedOperator 0 (Pi.map _ φ), hηL.toLp η⟫ =
    ⟪sobolevValueL (Pi.map _ φ), hAηL.toLp (gaugeFixedAdjoint 0 η)⟫
  rw [← hLHS, ← hRHS]
  exact integral_inner_sobolevGaugeFixedOperator_zero_ofTestFunction φ hη hηc

/-- **Formal adjoint identity for the `H¹` realization.** If `a` is the `L∞` class of a field `x`,
then `sobolevGaugeFixedOperator a y` pairs against every compactly supported `C¹` test field `η` as
the coordinate values of `y` against `gaugeFixedAdjoint x η`. No continuity of `x` is required. -/
theorem integral_inner_sobolevGaugeFixedOperator_of_ae_eq
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hax : a =ᵐ[μ⊤] x) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevGaugeFixedOperator a y z, η z⟫ =
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ := by
  have hηL : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hL (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
      Integrable (fun z ↦ ⟪sobolevGaugeFixedOperator b y z, η z⟫) volume := by
    have hb : MemLp (sobolevGaugeFixedOperator b y) 2 volume := by
      simpa [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevGaugeFixedOperator b y)
    exact hb.integrable_inner hηL
  have hA0 : Integrable (fun z ↦
      ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint 0 η z⟫) volume := by
    have hv : MemLp (sobolevValueL y) 2 volume := by
      simpa [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevValueL y)
    have hAη : MemLp (gaugeFixedAdjoint 0 η) 2 volume :=
      (continuous_gaugeFixedAdjoint continuous_zero hη).memLp_of_hasCompactSupport
        (hasCompactSupport_gaugeFixedAdjoint hηc)
    have hveq := sobolevValueL_apply_ae y
    simp only [Opens.coe_top, Measure.restrict_univ] at hveq
    exact (hv.integrable_inner hAη).congr (hveq.mono fun z hz ↦ by dsimp only at hz ⊢; rw [hz])
  have hdiff : (fun z ↦ ⟪sobolevGaugeFixedOperator a y z, η z⟫ -
      ⟪sobolevGaugeFixedOperator 0 y z, η z⟫) =ᵐ[volume] fun z ↦
        ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ -
          ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint 0 η z⟫ := by
    have hsub := sobolevGaugeFixedOperator_sub_apply_ae a 0 y
    have h0 : (0 : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) =ᵐ[μ⊤] (0 : ℂ → EuclideanSpace ℝ (Fin 4)) :=
      Lp.coeFn_zero _ _ _
    have hlp := Lp.coeFn_sub (sobolevGaugeFixedOperator a y) (sobolevGaugeFixedOperator 0 y)
    simp only [Opens.coe_top, Measure.restrict_univ] at hax hsub h0 hlp
    filter_upwards [hax, hsub, h0, hlp] with z hz₁ hz₂ hz₃ hz₄
    rw [sub_apply, hz₄, Pi.sub_apply] at hz₂
    rw [← inner_sub_left, hz₂, hz₁, hz₃, Pi.zero_apply, sub_zero,
      inner_gaugeFixedAdjoint_eq_add_inner_gaugeFixedZerothOrder x 0 η z]
    simp [sub_zero]
  have hint_diff : Integrable (fun z ↦ ⟪sobolevGaugeFixedOperator a y z, η z⟫ -
      ⟪sobolevGaugeFixedOperator 0 y z, η z⟫) volume := (hL a).sub (hL 0)
  have hint_x : Integrable (fun z ↦
      ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫) volume :=
    ((hint_diff.congr hdiff).add hA0).congr (ae_of_all _ fun z ↦ sub_add_cancel _ _)
  have heq := integral_congr_ae hdiff
  rw [integral_sub (hL a) (hL 0), integral_sub hint_x hA0,
    integral_inner_sobolevGaugeFixedOperator_zero y hη hηc] at heq
  linarith

/-- **Formal adjoint identity for the `H¹` realization** in terms of the `L∞` coefficient `a`
itself. -/
theorem integral_inner_sobolevGaugeFixedOperator
    (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevGaugeFixedOperator a y z, η z⟫ =
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint a η z⟫ :=
  integral_inner_sobolevGaugeFixedOperator_of_ae_eq Filter.EventuallyEq.rfl y hη hηc

/-- **Weak-solution characterization of `sobolevGaugeFixedOperator`.** For `a =ᵐ x`, an `H¹`
variation `y` satisfies `sobolevGaugeFixedOperator a y = f` in `L²` if and only if its coordinate
values form a weak solution of `L_x y = f` against smooth compactly supported test fields. -/
theorem sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hax : a =ᵐ[μ⊤] x) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    sobolevGaugeFixedOperator a y = f ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪f z, η z⟫ := by
  refine ⟨fun h η hη hηc ↦ ?_, fun h ↦ Lp.ext ?_⟩
  · rw [← h, integral_inner_sobolevGaugeFixedOperator_of_ae_eq hax y (hη.of_le (by simp)) hηc]
  · have hloc (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
        LocallyIntegrableOn g (⊤ : Opens ℂ) volume := by
      have hg : MemLp g 2 volume := by simpa [Opens.coe_top, Measure.restrict_univ] using Lp.memLp g
      exact (hg.locallyIntegrable one_le_two).locallyIntegrableOn _
    refine ae_eq_of_forall_integral_inner_eq (hloc _) (hloc _) fun φ ↦ ?_
    simp only [Opens.coe_top]
    simpa only [real_inner_comm] using
      (integral_inner_sobolevGaugeFixedOperator_of_ae_eq hax y
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport).trans (h φ φ.contDiff φ.hasCompactSupport)

/-- **Weak-kernel characterization of `sobolevGaugeFixedOperator`.** For `a =ᵐ x`, an `H¹`
variation lies in the kernel of `sobolevGaugeFixedOperator a` if and only if its coordinate values
lie in the weak kernel of `L_x`. -/
theorem mem_ker_sobolevGaugeFixedOperator_iff
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hax : a =ᵐ[μ⊤] x) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    y ∈ (sobolevGaugeFixedOperator a).ker ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq hax y 0]
  simp

/-! ### Lifting `H¹` Bessel-potential fields to `W^{1,2}(ℂ)⁴` -/

/-- Every `L²` field lying in `sobolevFields 1` is represented almost everywhere by the coordinate
values of a unique `W^{1,2}(ℂ)⁴` variation, by Calderón's theorem. -/
private theorem exists_w1p_ae_eq_of_mem_sobolevFields_one {Y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hY : Y ∈ sobolevFields 1) :
    ∃ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
      ∀ j, (W1p.value (y j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ Y z j := by
  choose y hy using fun j : Fin 4 ↦
    exists_w1p_value_ae_eq_of_mem_realSobolevFunctions (p := 2) (by norm_num) (by norm_num)
      le_rfl (mem_sobolevFields.1 hY j)
  exact ⟨y, hy⟩

/-- Two `W^{1,2}(ℂ)⁴` variations whose coordinate values agree almost everywhere are equal. -/
private theorem w1p_pi_ext_of_value_ae_eq {y₁ y₂ : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (h : ∀ j, (W1p.value (y₁ j) : ℂ → ℝ) =ᵐ[volume] W1p.value (y₂ j)) : y₁ = y₂ := by
  funext j
  apply W1p.ext_value
  apply Lp.ext
  simpa [Opens.coe_top, Measure.restrict_univ] using h j

/-- Given a bounded operator `Q` on `L²` whose outputs lie in `sobolevFields 1`, lifting each
output to `W^{1,2}(ℂ)⁴` produces a bounded linear operator `L² →L[ℝ] H¹(ℂ)⁴` by uniqueness of weak
gradients and the closed graph theorem. -/
private theorem exists_continuousLinearMap_w1p_of_mem_sobolevFields_one
    (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
    (hQ₁ : ∀ f, (Q f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields 1) :
    ∃ R : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
      ∀ f j, (W1p.value (R f j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ Q f z j := by
  choose R₀ hR₀ using fun f ↦ exists_w1p_ae_eq_of_mem_sobolevFields_one (hQ₁ f)
  let proj (j : Fin 4) : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ := EuclideanSpace.proj j
  have hval_eq (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (j : Fin 4) :
      W1p.value (R₀ f j) = ((proj j).compLpL 2 μ⊤) (Q f) := by
    apply Lp.ext
    have h₁ : (W1p.value (R₀ f j) : ℂ → ℝ) =ᵐ[μ⊤] fun z ↦ Q f z j := by
      simpa [Opens.coe_top, Measure.restrict_univ] using hR₀ f j
    exact h₁.trans ((proj j).coeFn_compLpL (Q f)).symm
  let Rₗ : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →ₗ[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
    { toFun := R₀
      map_add' := fun f g ↦ by
        funext j; apply W1p.ext_value
        rw [Pi.add_apply, W1p.value_add, hval_eq, hval_eq, hval_eq, map_add, map_add]
      map_smul' := fun c f ↦ by
        funext j; apply W1p.ext_value
        rw [Pi.smul_apply, W1p.value_smul, hval_eq, hval_eq, map_smul, map_smul,
          RingHom.id_apply] }
  refine ⟨ContinuousLinearMap.ofSeqClosedGraph (g := Rₗ) fun u f y hu hy ↦ ?_, hR₀⟩
  funext j; apply W1p.ext_value
  have h₁ : Tendsto (fun n ↦ W1p.value (Rₗ (u n) j)) atTop (𝓝 (W1p.value (y j))) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, W1p.valueL_apply] using
      ((W1p.valueL.comp (ContinuousLinearMap.proj j)).continuous.tendsto y).comp hy
  have h₂ : Tendsto (fun n ↦ (((proj j).compLpL 2 μ⊤).comp Q) (u n)) atTop
      (𝓝 ((((proj j).compLpL 2 μ⊤).comp Q) f)) :=
    ((((proj j).compLpL 2 μ⊤).comp Q).continuous.tendsto f).comp hu
  simp only [Rₗ, LinearMap.coe_mk, AddHom.coe_mk, hval_eq] at h₁ ⊢
  exact tendsto_nhds_unique h₁ h₂

/-! ### Surjectivity and the bounded `H¹` right inverse -/

section RightInverse

variable {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

private theorem integral_inner_sobolevValueL_gaugeFixedAdjoint_eq_zero_of_mem_ker
    (hax : a =ᵐ[μ⊤] x) {u : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (hu : u ∈ (sobolevGaugeFixedOperator a).ker) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevValueL u z, gaugeFixedAdjoint x η z⟫ ∂μ⊤ = 0 := by
  have hv := sobolevValueL_apply_ae u
  have hu0 : sobolevGaugeFixedOperator a u = 0 := hu
  simp only [Opens.coe_top, Measure.restrict_univ] at hv ⊢
  have hint : ∫ z, ⟪sobolevValueL u z, gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (u j) z), gaugeFixedAdjoint x η z⟫ :=
    integral_congr_ae (hv.mono fun z hz ↦ by dsimp only at hz ⊢; rw [hz])
  rw [hint, ← integral_inner_sobolevGaugeFixedOperator_of_ae_eq hax u (hη.of_le one_le_two) hηc,
    hu0]
  simp

/-- **Bounded `H¹` right inverse of the gauge-fixed operator at a plane vortex.** Let `x` be a `C¹`
solution of the plane vortex equation with `|α| → 1` at infinity and `L∞` class `a`. There is a
bounded right inverse `R : L²(ℂ; ℝ⁴) →L[ℝ] H¹(ℂ)⁴` of `sobolevGaugeFixedOperator a` whose outputs
are `L²`-orthogonal to `(sobolevGaugeFixedOperator a).ker` and satisfy the exponentially weighted
`L²` estimate at every rate `|c| < 1 / 2`. -/
theorem exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    ∃ R : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
      (sobolevGaugeFixedOperator a).comp R = ContinuousLinearMap.id ℝ _ ∧
      (∀ f, ∀ u ∈ (sobolevGaugeFixedOperator a).ker,
        ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (R f j) z),
          WithLp.toLp 2 (fun j ↦ W1p.value (u j) z)⟫ = 0) ∧
      ∀ {c : ℝ}, |c| < 1 / 2 → ∃ K : ℝ≥0, ∀ f,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
          WithLp.toLp 2 (fun j ↦ W1p.value (R f j) z)) 2 volume ≤
            K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  have : μ⊤.IsAddHaarMeasure := by rw [Opens.coe_top, Measure.restrict_univ]; infer_instance
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt
  obtain ⟨Q, hQ, hQK⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := μ⊤) hx hsol hlim
  have hQ₁ (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      (Q f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields 1 := by
    have hQf : MemLp (Q f) 2 volume := by
      simpa [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (Q f)
    have hf : MemLp f 2 volume := by simpa [Opens.coe_top, Measure.restrict_univ] using Lp.memLp f
    refine mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
      hx.continuous.aestronglyMeasurable (ae_of_all _ hM) hQf hf fun η hη hηc ↦ ?_
    simpa [Opens.coe_top, Measure.restrict_univ] using hQ f η (hη.of_le (by simp)) hηc
  obtain ⟨R, hR⟩ := exists_continuousLinearMap_w1p_of_mem_sobolevFields_one Q hQ₁
  have hR_vec (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      ∀ᵐ z ∂volume, (WithLp.toLp 2 fun j ↦ W1p.value (R f j) z) = Q f z := by
    filter_upwards [ae_all_iff.2 (hR f)] with z hz
    ext j; exact hz j
  refine ⟨R, ContinuousLinearMap.ext fun f ↦ ?_, fun f u hu ↦ ?_, fun {c} hc ↦ ?_⟩
  · refine (sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
      hax (R f) f).2 fun η hη hηc ↦ ?_
    have hint : ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (R f j) z), gaugeFixedAdjoint x η z⟫ =
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ :=
      integral_congr_ae ((hR_vec f).mono fun z hz ↦ by dsimp only; rw [hz])
    rw [hint]
    simpa [Opens.coe_top, Measure.restrict_univ] using hQ f η (hη.of_le (by simp)) hηc
  · have horth := hQK f (sobolevValueL u) fun η hη hηc ↦
      integral_inner_sobolevValueL_gaugeFixedAdjoint_eq_zero_of_mem_ker hax hu hη hηc
    have hvu := sobolevValueL_apply_ae u
    simp only [Opens.coe_top, Measure.restrict_univ] at horth hvu
    rw [← horth]
    exact integral_congr_ae
      ((hR_vec f).mp (hvu.mono fun z h₁ h₂ ↦ by dsimp only at h₁ h₂ ⊢; rw [h₁, h₂]))
  · obtain ⟨K, hK⟩ := exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
      (μ := μ⊤) hx hsol hlim hc
    refine ⟨K, fun f ↦ ?_⟩
    have bound := hK f (Q f) (hQ f) (hQK f)
    simp only [Opens.coe_top, Measure.restrict_univ] at bound
    have heq : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
          WithLp.toLp 2 (fun j ↦ W1p.value (R f j) z)) 2 volume =
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • Q f z) 2 volume :=
      eLpNorm_congr_ae ((hR_vec f).mono fun z hz ↦ by dsimp only; rw [hz])
    rwa [heq]

/-- **Surjectivity of `sobolevGaugeFixedOperator` at a plane vortex.** Let `x` be a `C¹` solution
of the plane vortex equation with `|α| → 1` at infinity and `L∞` class `a`. Then
`sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is surjective, so its cokernel vanishes. -/
theorem surjective_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (sobolevGaugeFixedOperator a) := by
  obtain ⟨R, hR, -⟩ :=
    exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id hx hsol hlim hax
  exact fun f ↦ ⟨R f, ContinuousLinearMap.ext_iff.1 hR f⟩

/-- **The range of `sobolevGaugeFixedOperator` is the whole `L²` space** at a `C¹` plane vortex
with `|α| → 1` at infinity and `L∞` class `a`. -/
theorem range_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).range = ⊤ :=
  LinearMap.range_eq_top.2 (surjective_sobolevGaugeFixedOperator hx hsol hlim hax)

end RightInverse

/-! ### Comparison with the classical kernel and the principal-part map -/

section KernelComparison

variable {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

private theorem mem_sobolevFields_one_of_mem_gaugeFixedKernel (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x) {Y : ℂ → EuclideanSpace ℝ (Fin 4)} (hY : Y ∈ gaugeFixedKernel x) :
    Y ∈ sobolevFields 1 := by
  obtain ⟨hYc, hY₂, hker⟩ := mem_gaugeFixedKernel.1 hY
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuousAt
  have hweak := (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx
    (hYc.of_le one_le_two) continuous_zero).2 hker
  refine mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq hx.aestronglyMeasurable
    (ae_of_all _ hM) hY₂ MemLp.zero fun η hη hηc ↦ ?_
  simpa using hweak η hη hηc

private theorem exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel
    (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) (Y : gaugeFixedKernel x) :
    ∃ y : (sobolevGaugeFixedOperator a).ker, ∀ j,
      (W1p.value (y.1 j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ (Y : ℂ → EuclideanSpace ℝ (Fin 4)) z j := by
  obtain ⟨y, hy⟩ := exists_w1p_ae_eq_of_mem_sobolevFields_one
    (mem_sobolevFields_one_of_mem_gaugeFixedKernel hx hax Y.2)
  obtain ⟨hYc, -, hker⟩ := mem_gaugeFixedKernel.1 Y.2
  have hmem : y ∈ (sobolevGaugeFixedOperator a).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    apply Lp.ext
    have hae := sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax (hYc.of_le one_le_two)
      fun j ↦ by simpa [Opens.coe_top, Measure.restrict_univ] using hy j
    have hker_ae : gaugeFixedOperator x Y =ᵐ[μ⊤] (0 : ℂ → EuclideanSpace ℝ (Fin 4)) :=
      ae_of_all _ hker
    exact hae.trans (hker_ae.trans (Lp.coeFn_zero _ _ _).symm)
  exact ⟨⟨y, hmem⟩, hy⟩

/-- **Inclusion of the classical `C²` kernel into the `H¹` kernel.** At a continuous field `x`
with `L∞` class `a`, every square-integrable `C²` solution of `L_x Y = 0` lies in `H¹(ℂ)⁴` by
elliptic regularity and defines a unique element of `(sobolevGaugeFixedOperator a).ker`. -/
def ofGaugeFixedKernel (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) :
    gaugeFixedKernel x →ₗ[ℝ] (sobolevGaugeFixedOperator a).ker where
  toFun Y := (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y).choose
  map_add' Y₁ Y₂ := by
    apply Subtype.ext
    refine w1p_pi_ext_of_value_ae_eq fun j ↦ ?_
    let u₁ := (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y₁).choose
    let u₂ := (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y₂).choose
    let u₁₂ := (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax
      (Y₁ + Y₂)).choose
    have h₁ : (W1p.value (u₁.1 j) : ℂ → ℝ) =ᵐ[volume]
        fun z ↦ (Y₁ : ℂ → EuclideanSpace ℝ (Fin 4)) z j :=
      (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y₁).choose_spec j
    have h₂ : (W1p.value (u₂.1 j) : ℂ → ℝ) =ᵐ[volume]
        fun z ↦ (Y₂ : ℂ → EuclideanSpace ℝ (Fin 4)) z j :=
      (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y₂).choose_spec j
    have h₁₂ : (W1p.value (u₁₂.1 j) : ℂ → ℝ) =ᵐ[volume]
        fun z ↦ ((Y₁ + Y₂ : gaugeFixedKernel x) : ℂ → EuclideanSpace ℝ (Fin 4)) z j :=
      (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax
        (Y₁ + Y₂)).choose_spec j
    have hadd : (W1p.value (u₁.1 j + u₂.1 j) : ℂ → ℝ) =ᵐ[volume]
        (W1p.value (u₁.1 j) : ℂ → ℝ) + W1p.value (u₂.1 j) := by
      simpa [Opens.coe_top, Measure.restrict_univ] using W1p.value_add_ae (u₁.1 j) (u₂.1 j)
    filter_upwards [h₁, h₂, h₁₂, hadd] with z hz₁ hz₂ hz₁₂ hzadd
    change W1p.value (u₁₂.1 j) z = W1p.value (u₁.1 j + u₂.1 j) z
    rw [hz₁₂, hzadd, Pi.add_apply, hz₁, hz₂]
    simp
  map_smul' c Y := by
    apply Subtype.ext
    refine w1p_pi_ext_of_value_ae_eq fun j ↦ ?_
    let u := (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y).choose
    let uc :=
      (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax (c • Y)).choose
    have h₁ : (W1p.value (u.1 j) : ℂ → ℝ) =ᵐ[volume]
        fun z ↦ (Y : ℂ → EuclideanSpace ℝ (Fin 4)) z j :=
      (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y).choose_spec j
    have hc : (W1p.value (uc.1 j) : ℂ → ℝ) =ᵐ[volume]
        fun z ↦ ((c • Y : gaugeFixedKernel x) : ℂ → EuclideanSpace ℝ (Fin 4)) z j :=
      (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax (c • Y)).choose_spec
        j
    have hsmul : (W1p.value (c • u.1 j) : ℂ → ℝ) =ᵐ[volume] c • (W1p.value (u.1 j) : ℂ → ℝ) := by
      simpa [Opens.coe_top, Measure.restrict_univ] using W1p.value_smul_ae c (u.1 j)
    filter_upwards [h₁, hc, hsmul] with z hz₁ hzc hzsmul
    change W1p.value (uc.1 j) z = W1p.value (c • u.1 j) z
    rw [hzc, hzsmul, Pi.smul_apply, hz₁]
    simp

/-- The coordinate values of `ofGaugeFixedKernel hx hax Y` agree almost everywhere with the
coordinates of `Y`. -/
theorem value_ofGaugeFixedKernel_ae (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (Y : gaugeFixedKernel x) (j : Fin 4) :
    (W1p.value ((ofGaugeFixedKernel hx hax Y).1 j) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ (Y : ℂ → EuclideanSpace ℝ (Fin 4)) z j :=
  (exists_mem_ker_sobolevGaugeFixedOperator_of_mem_gaugeFixedKernel hx hax Y).choose_spec j

/-- The inclusion `ofGaugeFixedKernel` is injective: a continuous classical kernel element whose
`H¹` class vanishes is identically zero. -/
theorem ofGaugeFixedKernel_injective (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) :
    Function.Injective (ofGaugeFixedKernel hx hax) := by
  rw [injective_iff_map_eq_zero]
  intro Y hY
  apply Subtype.ext
  have hYc := (mem_gaugeFixedKernel.1 Y.2).1.continuous
  refine (hYc.ae_eq_iff_eq volume continuous_zero).1 ?_
  have hzero (j : Fin 4) : (fun z ↦ (Y : ℂ → EuclideanSpace ℝ (Fin 4)) z j) =ᵐ[volume] 0 := by
    have hv := (value_ofGaugeFixedKernel_ae hx hax Y j).symm
    rw [hY] at hv
    refine hv.trans ?_
    simpa [Opens.coe_top, Measure.restrict_univ] using Lp.coeFn_zero ℝ 2 μ⊤
  filter_upwards [ae_all_iff.2 hzero] with z hz
  ext j; exact hz j

/-- At a smooth field with bounded derivatives through order `3`, every element of
`(sobolevGaugeFixedOperator a).ker` has a `C²` classical representative in `gaugeFixedKernel x`, by
the elliptic bootstrap to `H⁴(ℂ)⁴` and Sobolev embedding into `C²(ℂ)⁴`. -/
private theorem ofGaugeFixedKernel_surjective (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (ofGaugeFixedKernel hx.continuous hax) := by
  intro ⟨y, hy⟩
  set u : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z
  have huL : MemLp u 2 volume := by
    have hv : MemLp (sobolevValueL y) 2 volume := by
      simpa [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevValueL y)
    have hveq := sobolevValueL_apply_ae y
    simp only [Opens.coe_top, Measure.restrict_univ] at hveq
    exact hv.ae_eq hveq
  have hu_weak := (mem_ker_sobolevGaugeFixedOperator_iff hax y).1 hy
  have hu4 : u ∈ sobolevFields ((3 : ℕ) + 1) :=
    mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq 3 hx hbound huL
      (zero_mem _) fun η hη hηc ↦ by simpa using hu_weak η hη hηc
  have hs : (finrank ℝ ℂ : ℝ) + 2 * 2 < 2 * ((3 : ℕ) + 1) := by
    rw [Complex.finrank_real_complex]; norm_num
  choose g hg hug using fun j : Fin 4 ↦
    exists_contDiff_ae_eq_of_mem_realSobolevFunctions hs (mem_sobolevFields.1 hu4 j)
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ g j z
  have hY : ContDiff ℝ 2 Y := contDiff_euclidean.2 hg
  have huY : u =ᵐ[volume] Y := by
    filter_upwards [ae_all_iff.2 hug] with z hz
    ext j; exact hz j
  have hker : ∀ z, gaugeFixedOperator x Y z = 0 :=
    (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx.continuous
      (hY.of_le one_le_two) continuous_zero).1 fun η hη hηc ↦ by
        have hint : ∫ z, ⟪Y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ :=
          integral_congr_ae (huY.symm.mono fun z hz ↦ by dsimp only; rw [hz])
        rw [hint, hu_weak η hη hηc]
        simp
  refine ⟨⟨Y, mem_gaugeFixedKernel.2 ⟨hY, huL.ae_eq huY, hker⟩⟩, Subtype.ext ?_⟩
  exact w1p_pi_ext_of_value_ae_eq fun j ↦
    (value_ofGaugeFixedKernel_ae hx.continuous hax _ j).trans (hug j).symm

/-- **Equivalence between the `H¹` kernel and the classical `C²` kernel.** At a smooth field `x`
whose coordinates have bounded derivatives through order `3` and `L∞` class `a`, the kernel of
`sobolevGaugeFixedOperator a` is linearly isomorphic to `gaugeFixedKernel x`: every `H¹` kernel
element has a unique `C²` classical representative. -/
def kerSobolevGaugeFixedOperatorEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] gaugeFixedKernel x :=
  (LinearEquiv.ofBijective (σ₂₁ := RingHom.id ℝ) (ofGaugeFixedKernel hx.continuous hax)
    ⟨ofGaugeFixedKernel_injective hx.continuous hax,
      ofGaugeFixedKernel_surjective hx hbound hax⟩).symm

/-- The inverse of `kerSobolevGaugeFixedOperatorEquiv` is the canonical inclusion
`ofGaugeFixedKernel` from the classical `C²` kernel into the `H¹` kernel. -/
theorem kerSobolevGaugeFixedOperatorEquiv_symm_apply (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (Y : gaugeFixedKernel x) :
    (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm Y =
      ofGaugeFixedKernel hx.continuous hax Y :=
  (DFunLike.congr_fun (LinearEquiv.symm_symm _) Y).trans
    (LinearEquiv.ofBijective_apply (σ₂₁ := RingHom.id ℝ)
      (ofGaugeFixedKernel hx.continuous hax) Y)

/-- The coordinates of `kerSobolevGaugeFixedOperatorEquiv hx hbound hax y` represent the coordinate
values of `y` almost everywhere. -/
theorem value_ae_eq_kerSobolevGaugeFixedOperatorEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) (j : Fin 4) :
    (W1p.value (y.1 j) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ (kerSobolevGaugeFixedOperatorEquiv hx hbound hax y :
        ℂ → EuclideanSpace ℝ (Fin 4)) z j := by
  conv_lhs =>
    rw [← (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm_apply_apply y,
      kerSobolevGaugeFixedOperatorEquiv_symm_apply]
  exact value_ofGaugeFixedKernel_ae hx.continuous hax _ j

/-- **Bijectivity of the principal-part map on the classical kernel.** Let `x` be a smooth field
with vanishing holomorphicity rows `∂bar_a α = 0`, `|α|² → 1` at infinity, and zero divisor `D`,
and let `ν` be a `C²` integrating factor solving `∂bar ν = (b₂ - i b₁) / 2`. Then
`principalPartMap` on `gaugeFixedKernel x` is bijective onto `D.ToType → ℂ`: every collection of
principal parts of `δα / α` at the zeros of `α` is realized by a unique kernel element. -/
theorem principalPartMap_bijective {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    Function.Bijective (principalPartMap hD hν.continuous hdec) := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (contDiff_euclidean.1 hx i).of_le (by simp)
  have hlin (y) (hy : y ∈ gaugeFixedKernel x) :
      ContDiff ℝ 2 (fun w ↦ y w 0) ∧ ContDiff ℝ 2 (fun w ↦ y w 1) ∧
        Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
        ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
    obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
    have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.1 hyc i
    refine ⟨hyi 0, hyi 1, (hyi 2).differentiable (by simp), (hyi 3).differentiable (by simp),
      fun w ↦ ⟨?_, ?_⟩⟩
    · rw [← gaugeFixedOperator_apply_two, hker w, PiLp.zero_apply]
    · rw [← gaugeFixedOperator_apply_three, hker w, PiLp.zero_apply]
  have hinj : Function.Injective (principalPartMap hD hν.continuous hdec) :=
    principalPartMap_injective (k := 2) (by norm_num) (hxi 0) (hxi 1)
      ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hD hν hνeq hlin
      hdec fun y hy η hη hyη ↦
        eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
          (hx.of_le (by simp)) hhol hlim (mem_gaugeFixedKernel.1 hy).1.continuous
          (mem_gaugeFixedKernel.1 hy).2.1 (mem_gaugeFixedKernel.1 hy).2.2 hη hyη
  have : FiniteDimensional ℝ (gaugeFixedKernel x) :=
    finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by simp)) hhol hlim
      hD fun _ ↦ mem_gaugeFixedKernel.1
  have hdim : finrank ℝ (gaugeFixedKernel x) = finrank ℝ (D.ToType → ℂ) := by
    rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD, Module.finrank_pi_fintype,
      Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul, Finset.card_univ,
      Multiset.card_coe, mul_comm]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

/-- **Identification of the `H¹` kernel with the space of principal parts.** At a smooth field `x`
with bounded derivatives through order `3`, vanishing holomorphicity rows, `|α|² → 1` at infinity,
zero divisor `D`, and `L∞` class `a`, there is a smooth integrating factor `ν` such that
`(sobolevGaugeFixedOperator a).ker` is linearly isomorphic to `D.ToType → ℂ` via the principal
parts of `δα / α` on classical representatives. -/
theorem exists_ker_sobolevGaugeFixedOperator_linearEquiv {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hax : a =ᵐ[μ⊤] x) :
    ∃ (ν : ℂ → ℂ) (e : (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] (D.ToType → ℂ)),
      ContDiff ℝ ∞ ν ∧
      (∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) ∧
      ∀ (y : (sobolevGaugeFixedOperator a).ker) (i : D.ToType),
        e y i = principalPart x ν (kerSobolevGaugeFixedOperatorEquiv hx hbound hax y) i.1 i.2 := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := (⊤ : ℕ∞)) le_top
    (contDiff_connectionCoeff (hxi 0) (hxi 1))
  have hdec (y) (hy : y ∈ gaugeFixedKernel x) : ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
    obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
    have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.1 hyc i
    have hlin (w : ℂ) : linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
      rw [← gaugeFixedOperator_apply_two, ← gaugeFixedOperator_apply_three, hker w]
      simp
    obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
      ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol
      (hν.differentiable (by simp)) hνeq (hyi 0) (hyi 1) ((hyi 2).differentiable (by simp))
      ((hyi 3).differentiable (by simp)) hlin
    exact ⟨G, hG.continuous, H, hH, hGH⟩
  have hbij := principalPartMap_bijective hx hhol hlim hD (hν.of_le (by simp)) hνeq hdec
  let e₁ := kerSobolevGaugeFixedOperatorEquiv hx hbound hax
  let P := principalPartMap hD hν.continuous hdec
  let e₂ := LinearEquiv.ofBijective (σ₂₁ := RingHom.id ℝ) P hbij
  exact ⟨ν, e₁ ≪≫ₗ e₂, hν, hνeq, fun y i ↦
    (congrFun ((LinearEquiv.trans_apply y).trans
      (LinearEquiv.ofBijective_apply (σ₂₁ := RingHom.id ℝ) P (e₁ y))) i).trans
      (principalPartMap_apply hD hν.continuous hdec (e₁ y) i)⟩

end KernelComparison

/-! ### Fredholmness, kernel dimension, and Fredholm index -/

section FredholmIndex

variable {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Fredholmness of `sobolevGaugeFixedOperator` at a `C¹` vortex** with `|α| → 1` and
`∇₁ α → 0` at infinity and `L∞` class `a`. -/
theorem isFredholm_sobolevGaugeFixedOperator_of_tendsto_covariantDerivative (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm := by
  have hker := finiteDimensional_ker_sobolevGaugeFixedOperator hx hsol hlim hcov hax
  have hsurj := surjective_sobolevGaugeFixedOperator hx hsol hlim hax
  have hcoker : FiniteDimensional ℝ
      (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ⧸ (sobolevGaugeFixedOperator a).range) := by
    have : Subsingleton
        (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ⧸ (sobolevGaugeFixedOperator a).range) :=
      Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hsurj)
    infer_instance
  exact ContinuousLinearMap.IsFredholm.of_finite_ker_coker _ hker hcoker

/-- **Fredholmness of `sobolevGaugeFixedOperator` at a `C²` plane vortex.** Let `x` be a `C²`
solution of the plane vortex equation with `|α| → 1` at infinity and `L∞` class `a`. Then
`sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is Fredholm: exponential decay of the covariant
derivative supplies `∇₁ α → 0` automatically. -/
theorem isFredholm_sobolevGaugeFixedOperator (hx : ContDiff ℝ 2 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨K, hK⟩ := exists_norm_covariantDerivative_le_mul_exp (hxi 0).continuous (hxi 2) (hxi 3)
    hsol hlim (c := 4⁻¹) (by norm_num)
  have hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0) := by
    refine squeeze_zero_norm (fun z ↦ by simpa using hK z 1) ?_
    simpa [Function.comp_def] using (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp
        (tendsto_norm_cocompact_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 4⁻¹)))).const_mul K
  exact isFredholm_sobolevGaugeFixedOperator_of_tendsto_covariantDerivative (hx.of_le one_le_two)
    hsol hlim hcov hax

/-- **Dimension `2 |D|` of the `H¹` kernel.** Let `x` be a smooth field whose coordinates have
bounded derivatives through order `3`, with vanishing holomorphicity rows `∂bar_a α = 0`,
`|α|² → 1` at infinity, zero divisor `D`, and `L∞` class `a`. Then the kernel of
`sobolevGaugeFixedOperator a` has real dimension `2 |D|`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card {D : Multiset ℂ}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * Multiset.card D := by
  rw [(kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD]

/-- **Dimension `2m` of the `H¹` kernel at a framed field.** Let `x` be a smooth field whose
coordinates have bounded derivatives through order `3`, with vanishing holomorphicity rows, the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, and `L∞` class `a`. Then the kernel of
`sobolevGaugeFixedOperator a` has real dimension `2m`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m := by
  rw [(kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe]

/-- **Fredholm index `2 |D|` of `sobolevGaugeFixedOperator`.** At a smooth plane vortex `x` whose
coordinates have bounded derivatives through order `3`, with `|α|² → 1` at infinity, zero divisor
`D`, and `L∞` class `a`, the realization `sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` has
real Fredholm index `2 |D|`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul_card {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * (Multiset.card D : ℤ) := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
    (surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol hlim hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card hx hbound
      (fun w ↦ by simp [hsol w]) hlim hD hax]
  push_cast
  rfl

/-- **Fredholm index `2m` of `sobolevGaugeFixedOperator` at a framed degree-`m` vortex.** At a
smooth plane vortex `x` whose coordinates have bounded derivatives through order `3`, with the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` and `L∞` class `a`, the realization
`sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` has real Fredholm index `2m`, the real dimension
of `Sym^m ℂ`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * (m : ℤ) := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
    (surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol
      (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul hx hbound
      (fun w ↦ by simp [hsol w]) hframe hax]
  push_cast
  rfl

end FredholmIndex

/-! ### Vortices in the framed affine Sobolev space -/

section FramedFieldSpace

variable {ρ : ContDiffBump (0 : ℝ)} {m : ℕ} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
  {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- At a `C¹` vortex lying in `framedFieldSpace ρ m s` with `s > 1`, `sobolevGaugeFixedOperator a`
is surjective. -/
theorem surjective_sobolevGaugeFixedOperator_of_mem_framedFieldSpace {s : ℝ} (hs : 1 < s)
    (hx : ContDiff ℝ 1 x) (hmem : x ∈ framedFieldSpace ρ m s) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (sobolevGaugeFixedOperator a) :=
  surjective_sobolevGaugeFixedOperator hx hsol
    (tendsto_normSq_of_mem_framedFieldSpace hs hmem hx.continuous) hax

/-- At a `C²` vortex lying in `framedFieldSpace ρ m s` with `s > 1`, `sobolevGaugeFixedOperator a`
is Fredholm. -/
theorem isFredholm_sobolevGaugeFixedOperator_of_mem_framedFieldSpace {s : ℝ} (hs : 1 < s)
    (hx : ContDiff ℝ 2 x) (hmem : x ∈ framedFieldSpace ρ m s) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm :=
  isFredholm_sobolevGaugeFixedOperator hx hsol
    (tendsto_normSq_of_mem_framedFieldSpace hs hmem hx.continuous) hax

/-- At a continuous vortex lying in `framedFieldSpace ρ m k` for every `k`, the kernel of
`sobolevGaugeFixedOperator a` has real dimension `2m`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k)
    (hsol : ∀ z, equation x z = 0) (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m :=
  finrank_ker_sobolevGaugeFixedOperator_eq_two_mul
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    (fun w ↦ by simp [hsol w])
    (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx) hax

/-- At a continuous vortex lying in `framedFieldSpace ρ m k` for every `k`,
`sobolevGaugeFixedOperator a` has real Fredholm index `2m`. -/
theorem index_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k)
    (hsol : ∀ z, equation x z = 0) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * (m : ℤ) :=
  index_sobolevGaugeFixedOperator_eq_two_mul
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    hsol (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx) hax

end FramedFieldSpace

end TauCeti.Vortex
