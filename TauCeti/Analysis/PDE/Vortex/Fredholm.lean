/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import TauCeti.Analysis.PDE.Vortex.SobolevScale
public import TauCeti.Analysis.PDE.Vortex.KernelDimension
public import TauCeti.Analysis.PDE.Vortex.Bootstrap
public import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Fredholmness and index `2m` of the gauge-fixed plane vortex operator

At a field `x = (b₁, b₂, p, q)`, the gauge-fixed linearized vortex operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) and its formal adjoint `L_x*`
(`TauCeti.Vortex.gaugeFixedAdjoint`) govern the local moduli theory of plane vortices. Building on
coercivity (`SobolevRealization.lean`), the spectral gap and elliptic regularity across `H^k`
(`RightInverse.lean`, `EllipticRegularity.lean`, `SobolevScale.lean`), and the classical kernel
dimension (`PrincipalPart.lean`, `KernelDimension.lean`), this file establishes the Fredholm and
index theory of `L_x` on `H¹` and across the Sobolev scale `W^{k+1,2}(ℂ)⁴ → W^{k,2}(ℂ)⁴`:

* **Weak integration by parts, surjectivity, and Fredholmness on `H¹`**:
  `integral_inner_sobolevGaugeFixedOperator` and
  `sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq` identify
  `sobolevGaugeFixedOperator a` with the distributional operator dual to `L_x*`. At any `C¹` vortex
  with `|α|² → 1` at infinity (without assuming `∇₁ α → 0`), `surjective_sobolevGaugeFixedOperator`
  and `exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id` yield surjectivity and a
  bounded `L²`-orthogonal right inverse `L²(ℂ; ℝ⁴) →L[ℝ] H¹(ℂ)⁴`. At `C²` vortices, exponential
  decay (`tendsto_covariantDerivative_cocompact`) supplies `∇₁ α → 0`, giving
  `isFredholm_sobolevGaugeFixedOperator`.
* **Principal-part isomorphism, kernel equivalence, and index `2m` on `H¹`**:
  `principalPartEquiv` upgrades `principalPartMap` to `gaugeFixedKernel x ≃ₗ[ℝ] (D → ℂ)`, and
  elliptic regularity into `H⁴ ↪ C²` identifies `(sobolevGaugeFixedOperator a).ker` with
  `gaugeFixedKernel x` (`kerSobolevGaugeFixedOperatorEquiv`), yielding kernel dimension `2 |D|` /
  `2m`, degree-zero isomorphism (`sobolevGaugeFixedEquiv`), and Fredholm index `2 |D|` / `2m`
  (`index_sobolevGaugeFixedOperator_eq_two_mul_card`, `index_sobolevGaugeFixedOperator_eq_two_mul`).
* **Higher-order realization `W^{k+1,2}(ℂ)⁴ →L[ℝ] W^{k,2}(ℂ)⁴` and framed plane vortices**:
  `wkpGaugeFixedOperator` realizes `L_x` on `TauCeti.Wkp` at every order `k`, both for smooth
  bounded-derivative fields and for configurations in `framedFieldSpace f m n` (`n > 1`, `k ≤ n`).
  At smooth vortices—including framed vortices in every `A_m^j` and `C¹` Coulomb-slice vortices in
  `A_m^n` (`n ≥ 2`) via `Bootstrap.lean`—it is surjective with a bounded `L²`-orthogonal right
  inverse, Fredholm, has kernel canonically isomorphic to `gaugeFixedKernel x`, and has Fredholm
  index `2m` (`isFredholm_wkpGaugeFixedOperator_of_forall_mem_framedFieldSpace`,
  `index_wkpGaugeFixedOperator_eq_two_mul_of_forall_mem_framedFieldSpace`,
  `index_wkpGaugeFixedOperator_eq_two_mul_of_equation_eq_zero`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary `N`-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. **72** (1980), 277–292.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. **145** (1992), 149–179.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric Module TemperedDistribution TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace RealInnerProductSpace Topology

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### Measure-restriction and Banach-lifting helpers -/

private theorem restrict_top_eq_volume : μ⊤ = (volume : Measure ℂ) := by simp [Opens.coe_top]

private theorem ae_volume_iff {p : ℂ → Prop} : (∀ᵐ z ∂μ⊤, p z) ↔ ∀ᵐ z ∂volume, p z := by
  simp [Opens.coe_top]

private theorem ae_eq_volume_iff {α : Type*} {f g : ℂ → α} : f =ᵐ[μ⊤] g ↔ f =ᵐ[volume] g :=
  ae_volume_iff

private def castTopToVolumeCLM :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) :=
  (castLpₗᵢ (𝕜 := ℝ) restrict_top_eq_volume).toLinearIsometry.toContinuousLinearMap

private theorem coeFn_castTopToVolumeCLM (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (z : ℂ) :
    castTopToVolumeCLM f z = f z := by
  rw [castTopToVolumeCLM, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, coeFn_castLpₗᵢ]

/-- Assemble four scalar `L²` values into an `L²(ℂ; ℝ⁴)` field along `valL : X →L[ℝ] Lp ℝ 2 μ⊤`. -/
private def tupleToLp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (valL : X →L[ℝ] Lp ℝ 2 μ⊤) : (Fin 4 → X) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  ∑ j : Fin 4, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).compLpL 2 μ⊤).comp (valL.comp (ContinuousLinearMap.proj j))

private theorem tupleToLp_apply_ae {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (valL : X →L[ℝ] Lp ℝ 2 μ⊤) (y : Fin 4 → X) :
    (tupleToLp valL y : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[μ⊤]
      fun z ↦ WithLp.toLp 2 fun j ↦ valL (y j) z := by
  have hv : ∀ᵐ z ∂μ⊤, ∀ j : Fin 4,
      (ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (valL (y j))) z =
          valL (y j) z • EuclideanSpace.single j (1 : ℝ) :=
    ae_all_iff.2 fun j ↦ (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).coeFn_compLpL (valL (y j))
  simp only [tupleToLp, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  filter_upwards [Lp.coeFn_finsetSum (μ := μ⊤) (p := 2) Finset.univ fun j : Fin 4 ↦
    ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))) (valL (y j)), hv] with z hsum h
  rw [hsum]
  simp only [Finset.sum_apply, h]
  ext i
  simp [WithLp.ofLp_sum, EuclideanSpace.single, Pi.single_apply]

private theorem memLp_value_tuple (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z) 2 volume :=
  (by simpa [Opens.coe_top] using Lp.memLp (tupleToLp W1p.valueL y) :
    MemLp (tupleToLp W1p.valueL y : ℂ → _) 2 volume).ae_eq
    ((ae_eq_volume_iff.1 (tupleToLp_apply_ae W1p.valueL y)).mono fun _ hz ↦ by
      simpa only [W1p.valueL_apply] using hz)

section LiftToTuple

variable {Y X : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private def liftToTupleAux {valL : X →L[ℝ] Lp ℝ 2 μ⊤}
    {T : Y →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hex : ∀ y (j : Fin 4), ∃ x : X, (valL x : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j)
    (y : Y) (j : Fin 4) : X :=
  (hex y j).choose

private theorem valL_liftToTupleAux_ae {valL : X →L[ℝ] Lp ℝ 2 μ⊤}
    {T : Y →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hex : ∀ y (j : Fin 4), ∃ x : X, (valL x : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j)
    (y : Y) (j : Fin 4) :
    (valL (liftToTupleAux hex y j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j :=
  (hex y j).choose_spec

/-- Linear map lifting `T : Y →L[ℝ] L²(ℂ; ℝ⁴)` into `Fin 4 → X` along an injective value map
`valL : X →L[ℝ] Lp ℝ 2 μ⊤`. -/
private def liftToTupleLinear (valL : X →L[ℝ] Lp ℝ 2 μ⊤) (hinj : Function.Injective valL)
    (T : Y →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))
    (hex : ∀ y (j : Fin 4), ∃ x : X, (valL x : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j) :
    Y →ₗ[ℝ] (Fin 4 → X) where
  toFun := liftToTupleAux hex
  map_add' y₁ y₂ := funext fun j ↦ hinj <| Lp.ext <| ae_eq_volume_iff.2 <| by
    rw [Pi.add_apply, map_add]
    filter_upwards [valL_liftToTupleAux_ae hex (y₁ + y₂) j,
      ae_eq_volume_iff.1 (Lp.coeFn_add (valL (liftToTupleAux hex y₁ j))
        (valL (liftToTupleAux hex y₂ j))),
      Lp.coeFn_add (T y₁) (T y₂), valL_liftToTupleAux_ae hex y₁ j,
      valL_liftToTupleAux_ae hex y₂ j] with z h₀ h₁ h₂ h₃ h₄
    rw [h₀, map_add, h₂, h₁]
    simp only [Pi.add_apply, PiLp.add_apply, h₃, h₄]
  map_smul' c y := funext fun j ↦ hinj <| Lp.ext <| ae_eq_volume_iff.2 <| by
    rw [RingHom.id_apply, Pi.smul_apply, map_smul]
    filter_upwards [valL_liftToTupleAux_ae hex (c • y) j,
      ae_eq_volume_iff.1 (Lp.coeFn_smul c (valL (liftToTupleAux hex y j))),
      Lp.coeFn_smul c (T y), valL_liftToTupleAux_ae hex y j] with z h₀ h₁ h₂ h₃
    rw [h₀, map_smul, h₂, h₁]
    simp only [Pi.smul_apply, PiLp.smul_apply, h₃, smul_eq_mul]

private theorem liftToTupleLinear_apply (valL : X →L[ℝ] Lp ℝ 2 μ⊤)
    (hinj : Function.Injective valL)
    (T : Y →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))
    (hex : ∀ y (j : Fin 4), ∃ x : X, (valL x : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j) (y : Y) :
    liftToTupleLinear valL hinj T hex y = liftToTupleAux hex y := rfl

/-- Upgrade `liftToTupleLinear` to a continuous linear map via the closed graph theorem. -/
private def liftToTupleCLM [CompleteSpace Y] [CompleteSpace X] (valL : X →L[ℝ] Lp ℝ 2 μ⊤)
    (hinj : Function.Injective valL)
    (T : Y →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))
    (hex : ∀ y (j : Fin 4), ∃ x : X, (valL x : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j) :
    Y →L[ℝ] (Fin 4 → X) :=
  ContinuousLinearMap.ofSeqClosedGraph (g := liftToTupleLinear valL hinj T hex)
    fun u y w hu hw ↦ funext fun j ↦ by
      let R₀ := liftToTupleLinear valL hinj T hex
      let Pj : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ] Lp ℝ 2 μ⊤ :=
        (castLpₗᵢ (𝕜 := ℝ) restrict_top_eq_volume.symm).toLinearIsometry.toContinuousLinearMap.comp
          ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 (volume : Measure ℂ))
      have hPj (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :
          (Pj f : ℂ → ℝ) =ᵐ[volume] fun z ↦ f z j := by
        filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL f] with z hz
        dsimp only [Pj]
        rw [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometryEquiv.coe_toLinearIsometry, coeFn_castLpₗᵢ, hz]
        rfl
      have hval (n : ℕ) : valL (R₀ (u n) j) = Pj (T (u n)) := by
        dsimp only [R₀]
        rw [liftToTupleLinear_apply]
        exact Lp.ext (ae_eq_volume_iff.2 ((valL_liftToTupleAux_ae hex (u n) j).trans
          (hPj (T (u n))).symm))
      have ht₁ : Tendsto (fun n ↦ valL (R₀ (u n) j)) atTop (𝓝 (valL (w j))) :=
        (valL.continuous.tendsto (w j)).comp ((tendsto_pi_nhds.1 hw) j)
      have ht₂ : Tendsto (fun n ↦ valL (R₀ (u n) j)) atTop (𝓝 (Pj (T y))) := by
        simp_rw [hval]
        exact ((Pj.comp T).continuous.tendsto y).comp hu
      have hw_eq : valL (w j) = Pj (T y) := tendsto_nhds_unique ht₁ ht₂
      refine hinj (Lp.ext (ae_eq_volume_iff.2 ?_))
      rw [hw_eq, liftToTupleLinear_apply]
      exact (hPj (T y)).trans (valL_liftToTupleAux_ae hex y j).symm

private theorem valL_liftToTupleCLM_ae [CompleteSpace Y] [CompleteSpace X]
    (valL : X →L[ℝ] Lp ℝ 2 μ⊤) (hinj : Function.Injective valL)
    (T : Y →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))
    (hex : ∀ y (j : Fin 4), ∃ x : X, (valL x : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j)
    (y : Y) (j : Fin 4) :
    (valL (liftToTupleCLM valL hinj T hex y j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ T y z j :=
  (hex y j).choose_spec

end LiftToTuple

/-! ### Weak formulation and integration by parts on `H¹` -/

/-- **Integration by parts for the `H¹` realization of `L_x`.** At a continuous field `x` with
`L∞` class `a`, pairing `sobolevGaugeFixedOperator a y` in `L²` against a compactly supported `C¹`
field `η` moves `L_x` to the formal adjoint `L_x*` on `η`. -/
theorem integral_inner_sobolevGaugeFixedOperator {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevGaugeFixedOperator a y z, η z⟫ =
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ := by
  have hηL : MemLp η 2 μ⊤ := hη.continuous.memLp_of_hasCompactSupport hηc
  have hAL : MemLp (gaugeFixedAdjoint x η) 2 μ⊤ :=
    (continuous_gaugeFixedAdjoint hx hη).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  have hL (u : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ∫ z, ⟪sobolevGaugeFixedOperator a u z, η z⟫ =
        ⟪sobolevGaugeFixedOperator a u, hηL.toLp η⟫ := by
    rw [L2.inner_def]
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_congr_ae ((ae_eq_volume_iff.1 hηL.coeFn_toLp).mono fun z hz ↦ by
      dsimp only; rw [hz])
  have hR (u : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (u j) z), gaugeFixedAdjoint x η z⟫ =
        ⟪tupleToLp W1p.valueL u, hAL.toLp (gaugeFixedAdjoint x η)⟫ := by
    rw [L2.inner_def]
    simp only [Opens.coe_top, Measure.restrict_univ]
    refine integral_congr_ae ?_
    filter_upwards [ae_eq_volume_iff.1 (tupleToLp_apply_ae W1p.valueL u),
      ae_eq_volume_iff.1 hAL.coeFn_toLp] with z h₁ h₂
    rw [h₁, h₂]
    simp only [W1p.valueL_apply]
  simp_rw [hL, hR]
  refine (DenseRange.piMap fun _ : Fin 4 ↦
    W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on y
      (isClosed_eq ((sobolevGaugeFixedOperator a).continuous.inner continuous_const)
        ((tupleToLp W1p.valueL).continuous.inner continuous_const)) fun φ ↦ ?_
  set u : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2 :=
    Pi.map (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2)) φ
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ φ j z
  have hY : ContDiff ℝ 1 Y :=
    contDiff_euclidean.2 fun j ↦ (φ j).contDiff.of_le (by exact_mod_cast le_top)
  rw [← hL, ← hR]
  have hsob := ae_eq_volume_iff.1 (sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax
    (y := u) hY fun j ↦ W1p.value_ofTestFunctionₗ_ae (φ j))
  have h₁ : ∫ z, ⟪sobolevGaugeFixedOperator a u z, η z⟫ = ∫ z, ⟪gaugeFixedOperator x Y z, η z⟫ :=
    integral_congr_ae (hsob.mono fun z hz ↦ by dsimp only; rw [hz])
  have h₂ : ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (u j) z), gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪Y z, gaugeFixedAdjoint x η z⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 fun j : Fin 4 ↦
      W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) (φ j)] with z hz
    have hY' : (WithLp.toLp 2 fun j ↦ W1p.value (u j) z) = Y z := by ext j; exact hz j
    rw [hY']
  rw [h₁, h₂, integral_inner_gaugeFixedOperator hx hY hη (.inr hηc)]

/-- **Weak-solution characterization of `sobolevGaugeFixedOperator`.** At a continuous field `x`
with `L∞` class `a`, an `H¹` variation `y` satisfies `sobolevGaugeFixedOperator a y = f` in `L²`
if and only if its value tuple is a weak solution of `L_x y = f`. -/
theorem sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    sobolevGaugeFixedOperator a y = f ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪f z, η z⟫ := by
  refine ⟨fun h η hη hηc ↦ ?_, fun hweak ↦ Lp.ext (ae_eq_volume_iff.2 ?_)⟩
  · subst h
    exact (integral_inner_sobolevGaugeFixedOperator hx hax y
      (hη.of_le (by exact_mod_cast le_top)) hηc).symm
  · have hloc₁ : LocallyIntegrableOn (sobolevGaugeFixedOperator a y : ℂ → _)
        (⊤ : Opens ℂ) volume := Lp.locallyIntegrableOn (sobolevGaugeFixedOperator a y) Fact.out
    have hloc₂ : LocallyIntegrableOn (f : ℂ → _) (⊤ : Opens ℂ) volume :=
      Lp.locallyIntegrableOn f Fact.out
    simpa using ae_eq_of_forall_integral_inner_eq (Ω := ⊤) hloc₁ hloc₂ fun φ ↦ by
      have h₁ := integral_inner_sobolevGaugeFixedOperator hx hax y
        (φ.contDiff.of_le (by exact_mod_cast le_top)) φ.hasCompactSupport
      have h₂ := hweak φ φ.contDiff φ.hasCompactSupport
      simpa only [real_inner_comm] using h₁.trans h₂

/-- **Weak-kernel characterization of `sobolevGaugeFixedOperator`.** At a continuous field `x`
with `L∞` class `a`, an `H¹` variation lies in `(sobolevGaugeFixedOperator a).ker` if and only if
its value tuple is orthogonal in `L²` to `L_x* η` for every smooth compactly supported test field
`η`. -/
theorem mem_ker_sobolevGaugeFixedOperator_iff {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    y ∈ (sobolevGaugeFixedOperator a).ker ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ = 0 := by
  have hzero (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
      ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z, η z⟫ = 0 := by
    have hz := ae_eq_volume_iff.1 (Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
    refine (integral_congr_ae (g := fun _ ↦ 0) (hz.mono fun z h ↦ ?_)).trans (integral_zero ℂ ℝ)
    dsimp only; rw [h, Pi.zero_apply, inner_zero_left]
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq hx hax y 0]
  exact forall₃_congr fun η _ _ ↦ by rw [hzero η]

private theorem integral_inner_gaugeFixedAdjoint_eq_zero_of_mem_ker
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (hy : y ∈ (sobolevGaugeFixedOperator a).ker) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ = 0 := by
  have hy0 : sobolevGaugeFixedOperator a y = 0 := by
    rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
  have hparts := (integral_inner_sobolevGaugeFixedOperator hx hax y (hη.of_le one_le_two) hηc).symm
  have hz := ae_eq_volume_iff.1 (Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
  rw [hy0] at hparts
  refine hparts.trans ((integral_congr_ae (g := fun _ ↦ 0) (hz.mono fun z h ↦ ?_)).trans
    (integral_zero ℂ ℝ))
  dsimp only; rw [h, Pi.zero_apply, inner_zero_left]

/-! ### Surjectivity, bounded right inverse, and Fredholmness on `H¹` -/

section FirstOrderVortex

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- **Surjectivity of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` at a plane vortex.** Let `x` be a `C¹` solution
of the plane vortex equation with `|α|² → 1` at infinity and `L∞` class `a`. Then
`sobolevGaugeFixedOperator a` is surjective; no decay hypothesis on `∇α` is required. -/
theorem surjective_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) : Function.Surjective (sobolevGaugeFixedOperator a) := by
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt
  intro f
  have hf : MemLp (f : ℂ → EuclideanSpace ℝ (Fin 4)) 2 volume := by
    simpa [Opens.coe_top] using Lp.memLp f
  obtain ⟨Y, hY, hweak⟩ :=
    exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq hx hM hsol hlim hf
  choose y hy using fun j : Fin 4 ↦
    exists_w1p_value_ae_eq_of_mem_realSobolevFunctions (by norm_num) (by norm_num) le_rfl
      (mem_sobolevFields.1 hY j)
  refine ⟨y, (sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
    hx.continuous hax y f).2 fun η hη hηc ↦ ?_⟩
  rw [← hweak η (hη.of_le (by norm_cast)) hηc]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hy] with z hz
  have hYz : (WithLp.toLp 2 fun j ↦ W1p.value (y j) z) = Y z := by ext j; exact hz j
  rw [hYz]

/-- **Bounded `L²`-orthogonal right inverse `L²(ℂ; ℝ⁴) →L[ℝ] H¹(ℂ)⁴` at a plane vortex.** Let `x`
be a `C¹` solution of the plane vortex equation with `|α|² → 1` at infinity and `L∞` class `a`.
Then `sobolevGaugeFixedOperator a` admits a continuous linear right inverse `R` whose image on
every `f ∈ L²` is orthogonal in `L²` to `(sobolevGaugeFixedOperator a).ker`. -/
theorem exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    ∃ R : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
      (sobolevGaugeFixedOperator a).comp R = ContinuousLinearMap.id ℝ _ ∧
      ∀ f (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
        y ∈ (sobolevGaugeFixedOperator a).ker →
          ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (R f j) z),
            WithLp.toLp 2 (fun j ↦ W1p.value (y j) z)⟫ = 0 := by
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt
  obtain ⟨Q, hQ, hQK⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := volume) hx hsol hlim
  set Q' := Q.comp castTopToVolumeCLM
  have hinj : Function.Injective (W1p.valueL : W1p (volume : Measure ℂ) ⊤ 2 →L[ℝ] Lp ℝ 2 μ⊤) :=
    fun _ _ h ↦ W1p.ext_value (by rwa [W1p.valueL_apply, W1p.valueL_apply] at h)
  have hex (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (j : Fin 4) :
      ∃ w : W1p (volume : Measure ℂ) ⊤ 2,
        (W1p.valueL w : ℂ → ℝ) =ᵐ[volume] fun z ↦ Q' f z j := by
    obtain ⟨w, hw⟩ := exists_w1p_value_ae_eq_of_mem_realSobolevFunctions (by norm_num) (by norm_num)
      le_rfl (mem_sobolevFields.1 (mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
        hx.continuous.aestronglyMeasurable (.of_forall hM) (Lp.memLp (Q' f))
        (Lp.memLp (castTopToVolumeCLM f))
        fun η hη hηc ↦ hQ (castTopToVolumeCLM f) η (hη.of_le (by norm_cast)) hηc) j)
    exact ⟨w, by rwa [W1p.valueL_apply]⟩
  set R := liftToTupleCLM W1p.valueL hinj Q' hex
  have hRval (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (R f j) z) =ᵐ[volume]
        (Q' f : ℂ → EuclideanSpace ℝ (Fin 4)) := by
    filter_upwards [ae_all_iff.2 (valL_liftToTupleCLM_ae W1p.valueL hinj Q' hex f)] with z hz
    ext j; simpa only [W1p.valueL_apply] using hz j
  refine ⟨R, ContinuousLinearMap.ext fun f ↦ ?_, fun f y hy ↦ ?_⟩
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
        hx.continuous hax (R f) f]
    intro η hη hηc
    have hQ'f : Q' f = Q (castTopToVolumeCLM f) := rfl
    rw [integral_congr_ae ((hRval f).mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz),
      hQ'f, hQ _ η (hη.of_le (by norm_cast)) hηc]
    exact integral_congr_ae (.of_forall fun z ↦ congrArg (⟪·, η z⟫) (coeFn_castTopToVolumeCLM f z))
  · set u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) :=
      castTopToVolumeCLM (tupleToLp W1p.valueL y)
    have hu_ae : (u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
        fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z := by
      filter_upwards [ae_eq_volume_iff.1 (tupleToLp_apply_ae W1p.valueL y)] with z hz
      simpa only [u, coeFn_castTopToVolumeCLM, W1p.valueL_apply] using hz
    have hu_ker (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η)
        (hηc : HasCompactSupport η) : ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
      rw [integral_congr_ae (hu_ae.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)]
      exact integral_inner_gaugeFixedAdjoint_eq_zero_of_mem_ker hx.continuous hax hy hη hηc
    rw [← hQK (castTopToVolumeCLM f) u hu_ker]
    refine integral_congr_ae ?_
    filter_upwards [hRval f, hu_ae] with z h₁ h₂
    rw [h₁, h₂]; rfl

/-- **Fredholmness of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` at a `C¹` vortex with `∇₁ α → 0`.** -/
theorem isFredholm_sobolevGaugeFixedOperator_of_tendsto_covariantDerivative (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) : (sobolevGaugeFixedOperator a).IsFredholm := by
  have := finiteDimensional_ker_sobolevGaugeFixedOperator hx hsol hlim hcov hax
  exact ContinuousLinearMap.IsFredholm.of_surjective
    (surjective_sobolevGaugeFixedOperator hx hsol hlim hax)

/-- **The covariant derivative of a `C²` plane vortex vanishes at infinity.** Exponential decay
(`exists_norm_covariantDerivative_le_mul_exp`) implies `∇_v α(z) → 0` along `cocompact ℂ` without
assuming derivative decay in advance. -/
theorem tendsto_covariantDerivative_cocompact (hx : ContDiff ℝ 2 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (v : ℂ) :
    Tendsto (fun z ↦ covariantDerivative x z v) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_norm_covariantDerivative_le_mul_exp
    (contDiff_euclidean.1 hx 0).continuous (contDiff_euclidean.1 hx 2) (contDiff_euclidean.1 hx 3)
    hsol hlim (c := 1 / 4) (by norm_num)
  have hbot : Tendsto (fun z : ℂ ↦ -(1 / 4 * ‖z‖)) (cocompact ℂ) atBot :=
    tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4) tendsto_norm_cocompact_atTop)
  have hexp : Tendsto (fun z : ℂ ↦ K * ‖v‖ * Real.exp (-(1 / 4 * ‖z‖))) (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_atBot.comp hbot).const_mul (K * ‖v‖)
  exact squeeze_zero_norm (fun z ↦ hK z v) hexp

/-- **The kernel of `sobolevGaugeFixedOperator` is finite dimensional at a `C²` vortex**, without
assuming `∇₁ α → 0` separately. -/
theorem finiteDimensional_ker_sobolevGaugeFixedOperator_of_contDiff_two (hx : ContDiff ℝ 2 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) : FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker :=
  finiteDimensional_ker_sobolevGaugeFixedOperator (hx.of_le one_le_two) hsol hlim
    (tendsto_covariantDerivative_cocompact hx hsol hlim 1) hax

/-- **Fredholmness of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` at a `C²` plane vortex.** Let `x` be a `C²`
solution of the plane vortex equation with `|α|² → 1` at infinity and `L∞` class `a`. Then
`sobolevGaugeFixedOperator a` is a surjective Fredholm operator. -/
theorem isFredholm_sobolevGaugeFixedOperator (hx : ContDiff ℝ 2 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) : (sobolevGaugeFixedOperator a).IsFredholm :=
  isFredholm_sobolevGaugeFixedOperator_of_tendsto_covariantDerivative (hx.of_le one_le_two) hsol
    hlim (tendsto_covariantDerivative_cocompact hx hsol hlim 1) hax

end FirstOrderVortex

/-! ### Principal-part isomorphism, kernel identification, and Fredholm index on `H¹` -/

section PrincipalPartEquiv

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ}

/-- **Bijectivity of the principal-part map on `gaugeFixedKernel`.** At a smooth field satisfying
the holomorphicity rows `∂bar_a α = 0` with `|α|² → 1` at infinity and zero divisor `D`, every
tuple of principal-part coefficients in `ℂ^|D|` is realized by a unique classical `C² ∩ L²`
element of `ker L_x`. -/
theorem bijective_principalPartMap_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z D) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν) (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    Function.Bijective (principalPartMap hD hν.continuous hdec) := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := (contDiff_euclidean.1 hx i).of_le (by simp)
  have hlin (y : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : y ∈ gaugeFixedKernel x) :
      ContDiff ℝ 2 (fun w ↦ y w 0) ∧ ContDiff ℝ 2 (fun w ↦ y w 1) ∧
        Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
        ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
    obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
    have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.1 hyc i
    exact ⟨hyi 0, hyi 1, (hyi 2).differentiable (by norm_num),
      (hyi 3).differentiable (by norm_num), fun w ↦ by
        rw [← gaugeFixedOperator_apply_two, ← gaugeFixedOperator_apply_three, hker w]; simp⟩
  have hinj : Function.Injective (principalPartMap hD hν.continuous hdec) :=
    principalPartMap_injective (k := 2) (by norm_num) (hi 0) (hi 1)
      ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hD hν hνeq
      hlin hdec fun y hy η hη hyη ↦
        eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
          (hx.of_le (by simp)) hhol hlim (mem_gaugeFixedKernel.1 hy).1.continuous
          (mem_gaugeFixedKernel.1 hy).2.1 (mem_gaugeFixedKernel.1 hy).2.2 hη hyη
  have := FiniteDimensional.of_injective (principalPartMap hD hν.continuous hdec) hinj
  have hdim : finrank ℝ (gaugeFixedKernel x) = finrank ℝ (Multiset.ToType D → ℂ) := by
    rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD, Module.finrank_pi_fintype,
      Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul, Finset.card_univ,
      Multiset.card_coe, mul_comm]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

/-- **The principal-part isomorphism `ker L_x ≃ₗ[ℝ] ℂ^|D|`.** At a smooth field satisfying
`∂bar_a α = 0` with `|α|² → 1` at infinity and zero divisor `D`, the principal-part map identifies
`gaugeFixedKernel x` linearly over `ℝ` with `Multiset.ToType D → ℂ`, the real tangent space to the
symmetric product `Sym^|D| ℂ` at `D`. -/
def principalPartEquiv (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z D) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν) (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ) :=
  LinearEquiv.ofBijective (principalPartMap hD hν.continuous hdec)
    (bijective_principalPartMap_gaugeFixedKernel hx hhol hlim hD hν hνeq hdec)

@[simp]
theorem principalPartEquiv_apply (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z D) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν) (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (y : gaugeFixedKernel x) (i : Multiset.ToType D) :
    principalPartEquiv hx hhol hlim hD hν hνeq hdec y i = principalPart x ν y i.1 i.2 := by
  simp [principalPartEquiv]

end PrincipalPartEquiv

section SobolevKernelAndIndex

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

private theorem mem_sobolevFields_one_of_mem_gaugeFixedKernel (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x) {Y : ℂ → EuclideanSpace ℝ (Fin 4)} (hY : Y ∈ gaugeFixedKernel x) :
    Y ∈ sobolevFields 1 := by
  obtain ⟨hYc, hYL, hker⟩ := mem_gaugeFixedKernel.1 hY
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ := Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuousAt
  have hweak := (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx
    (hYc.of_le one_le_two) continuous_zero).2 hker
  exact mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq hx.aestronglyMeasurable
    (.of_forall hM) hYL MemLp.zero hweak

private theorem mem_ker_of_ae_eq_gaugeFixedKernel {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (hax : a =ᵐ[μ⊤] x) {Y : ℂ → EuclideanSpace ℝ (Fin 4)} (hY : Y ∈ gaugeFixedKernel x)
    (hy : ∀ j, (W1p.value (y j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ Y z j) :
    y ∈ (sobolevGaugeFixedOperator a).ker := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine Lp.ext ?_
  have h₁ := sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax (y := y)
    ((mem_gaugeFixedKernel.1 hY).1.of_le one_le_two) fun j ↦ ae_eq_volume_iff.2 (hy j)
  filter_upwards [h₁, Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ⊤] with z hz₁ hz₀
  rw [hz₁, (mem_gaugeFixedKernel.1 hY).2.2 z, hz₀, Pi.zero_apply]

private def gaugeFixedKernelToSobolevAux (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (Y : gaugeFixedKernel x) (j : Fin 4) : W1p (volume : Measure ℂ) ⊤ 2 :=
  (exists_w1p_value_ae_eq_of_mem_realSobolevFunctions (p := 2) (by norm_num) (by norm_num) le_rfl
    (mem_sobolevFields.1 (mem_sobolevFields_one_of_mem_gaugeFixedKernel hx hax Y.2) j)).choose

private theorem value_gaugeFixedKernelToSobolevAux_ae (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (Y : gaugeFixedKernel x) (j : Fin 4) :
    (W1p.value (gaugeFixedKernelToSobolevAux hx hax Y j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ Y.1 z j :=
  (exists_w1p_value_ae_eq_of_mem_realSobolevFunctions (p := 2) (by norm_num) (by norm_num) le_rfl
    (mem_sobolevFields.1 (mem_sobolevFields_one_of_mem_gaugeFixedKernel hx hax Y.2) j)).choose_spec

private theorem gaugeFixedKernelToSobolevAux_add (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (Y₁ Y₂ : gaugeFixedKernel x) :
    gaugeFixedKernelToSobolevAux hx hax (Y₁ + Y₂) =
      gaugeFixedKernelToSobolevAux hx hax Y₁ + gaugeFixedKernelToSobolevAux hx hax Y₂ :=
  funext fun j ↦ W1p.ext_value <| Lp.ext <| ae_eq_volume_iff.2 <| by
    rw [Pi.add_apply, W1p.value_add]
    filter_upwards [value_gaugeFixedKernelToSobolevAux_ae hx hax (Y₁ + Y₂) j,
      ae_eq_volume_iff.1 (Lp.coeFn_add (W1p.value (gaugeFixedKernelToSobolevAux hx hax Y₁ j))
        (W1p.value (gaugeFixedKernelToSobolevAux hx hax Y₂ j))),
      value_gaugeFixedKernelToSobolevAux_ae hx hax Y₁ j,
      value_gaugeFixedKernelToSobolevAux_ae hx hax Y₂ j] with z h₀ h₁ h₂ h₃
    rw [h₀, h₁, Pi.add_apply, h₂, h₃]; simp only [Submodule.coe_add, Pi.add_apply, PiLp.add_apply]

private theorem gaugeFixedKernelToSobolevAux_smul (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) (c : ℝ)
    (Y : gaugeFixedKernel x) :
    gaugeFixedKernelToSobolevAux hx hax (c • Y) = c • gaugeFixedKernelToSobolevAux hx hax Y :=
  funext fun j ↦ W1p.ext_value <| Lp.ext <| ae_eq_volume_iff.2 <| by
    rw [Pi.smul_apply, W1p.value_smul]
    filter_upwards [value_gaugeFixedKernelToSobolevAux_ae hx hax (c • Y) j,
      ae_eq_volume_iff.1 (Lp.coeFn_smul c (W1p.value (gaugeFixedKernelToSobolevAux hx hax Y j))),
      value_gaugeFixedKernelToSobolevAux_ae hx hax Y j] with z h₀ h₁ h₂
    rw [h₀, h₁, Pi.smul_apply, h₂]
    simp only [Submodule.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]

/-- Inclusion of the classical `C² ∩ L²` kernel `gaugeFixedKernel x` into the Sobolev kernel
`(sobolevGaugeFixedOperator a).ker` at any continuous field `x` with `L∞` class `a`. -/
def gaugeFixedKernelToSobolevKer (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) :
    gaugeFixedKernel x →ₗ[ℝ] (sobolevGaugeFixedOperator a).ker where
  toFun Y := ⟨gaugeFixedKernelToSobolevAux hx hax Y,
    mem_ker_of_ae_eq_gaugeFixedKernel hax Y.2 (value_gaugeFixedKernelToSobolevAux_ae hx hax Y)⟩
  map_add' Y₁ Y₂ := Subtype.ext (gaugeFixedKernelToSobolevAux_add hx hax Y₁ Y₂)
  map_smul' c Y := Subtype.ext (gaugeFixedKernelToSobolevAux_smul hx hax c Y)

/-- The coordinates of `gaugeFixedKernelToSobolevKer hx hax Y` represent `Y` almost everywhere. -/
theorem value_gaugeFixedKernelToSobolevKer_ae (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (Y : gaugeFixedKernel x) (j : Fin 4) :
    (W1p.value ((gaugeFixedKernelToSobolevKer hx hax Y).1 j) : ℂ → ℝ) =ᵐ[volume] fun z ↦ Y.1 z j :=
  value_gaugeFixedKernelToSobolevAux_ae hx hax Y j

/-- The inclusion `gaugeFixedKernelToSobolevKer` is injective at every continuous field `x`. -/
theorem gaugeFixedKernelToSobolevKer_injective (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) :
    Function.Injective (gaugeFixedKernelToSobolevKer hx hax) := by
  refine (injective_iff_map_eq_zero _).2 fun Y hY ↦ Subtype.ext ?_
  have hY0 (j : Fin 4) : (fun z ↦ Y.1 z j) = 0 := by
    have hval : (gaugeFixedKernelToSobolevKer hx hax Y).1 j = 0 := by
      simpa using congrFun (congrArg Subtype.val hY) j
    have hae : (fun z ↦ Y.1 z j) =ᵐ[volume] 0 := by
      refine (value_gaugeFixedKernelToSobolevKer_ae hx hax Y j).symm.trans ?_
      rw [hval, W1p.value_zero]; exact ae_eq_volume_iff.1 (Lp.coeFn_zero ℝ 2 μ⊤)
    exact ((contDiff_euclidean.1 (mem_gaugeFixedKernel.1 Y.2).1 j).continuous.ae_eq_iff_eq
      volume continuous_zero).1 hae
  ext z j; exact congrFun (hY0 j) z

private theorem surjective_gaugeFixedKernelToSobolevKer (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) : Function.Surjective (gaugeFixedKernelToSobolevKer hx.continuous hax) := by
  rintro ⟨y, hy⟩
  set u : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z
  have hweak := (mem_ker_sobolevGaugeFixedOperator_iff hx.continuous hax y).1 hy
  have hu4 : u ∈ sobolevFields (4 : ℕ) := by
    convert mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq 3 hx hbound
      (memLp_value_tuple y) (zero_mem _) (fun η hη hηc ↦ by simpa using hweak η hη hηc) using 2
    norm_num
  have hdim : (finrank ℝ ℂ : ℝ) + 2 * (2 : ℕ) < 2 * ((4 : ℕ) : ℝ) := by
    rw [Complex.finrank_real_complex]; norm_num
  choose g hg hgu using fun j : Fin 4 ↦
    exists_contDiff_ae_eq_of_mem_realSobolevFunctions hdim (mem_sobolevFields.1 hu4 j)
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ g j z
  have hYc : ContDiff ℝ 2 Y := contDiff_euclidean.2 hg
  have huY : u =ᵐ[volume] Y := (ae_all_iff.2 hgu).mono fun z hz ↦ by ext j; exact hz j
  have hYK : Y ∈ gaugeFixedKernel x := by
    refine mem_gaugeFixedKernel.2 ⟨hYc, (memLp_value_tuple y).ae_eq huY, ?_⟩
    refine (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx.continuous
      (hYc.of_le one_le_two) continuous_zero).1 fun η hη hηc ↦ ?_
    simp only [Pi.zero_apply, inner_zero_left, integral_zero]
    rw [← hweak η hη hηc]
    exact integral_congr_ae (huY.symm.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)
  refine ⟨⟨Y, hYK⟩, Subtype.ext <| funext fun j ↦ W1p.ext_value <| Lp.ext ?_⟩
  exact ae_eq_volume_iff.2
    ((value_gaugeFixedKernelToSobolevKer_ae hx.continuous hax ⟨Y, hYK⟩ j).trans (hgu j).symm)

/-- **Equivalence between the Sobolev `H¹` kernel and the classical kernel `gaugeFixedKernel x`.**
At a smooth field whose coordinates have bounded derivatives through order `3`, elliptic regularity
into `H⁴(ℂ) ↪ C²(ℂ)` identifies `(sobolevGaugeFixedOperator a).ker` canonically with
`gaugeFixedKernel x`. Neither the vortex equation nor an asymptotic framing is required. -/
def kerSobolevGaugeFixedOperatorEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) : (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] gaugeFixedKernel x :=
  (LinearEquiv.ofBijective (gaugeFixedKernelToSobolevKer hx.continuous hax)
    ⟨gaugeFixedKernelToSobolevKer_injective hx.continuous hax,
      surjective_gaugeFixedKernelToSobolevKer hx hbound hax⟩).symm

/-- The inverse of `kerSobolevGaugeFixedOperatorEquiv` is `gaugeFixedKernelToSobolevKer`. -/
theorem kerSobolevGaugeFixedOperatorEquiv_symm_apply (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (Y : gaugeFixedKernel x) :
    (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm Y =
      gaugeFixedKernelToSobolevKer hx.continuous hax Y := (rfl)

/-- Every `y ∈ (sobolevGaugeFixedOperator a).ker` has `kerSobolevGaugeFixedOperatorEquiv ... y` as
its unique `C²` classical representative almost everywhere. -/
theorem value_kerSobolevGaugeFixedOperatorEquiv_ae (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) (j : Fin 4) :
    (W1p.value (y.1 j) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ ((kerSobolevGaugeFixedOperatorEquiv hx hbound hax y).1 z j) := by
  set Y := kerSobolevGaugeFixedOperatorEquiv hx hbound hax y
  have hy : gaugeFixedKernelToSobolevKer hx.continuous hax Y = y :=
    (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm_apply_apply y
  simpa only [hy] using value_gaugeFixedKernelToSobolevKer_ae hx.continuous hax Y j

/-- **The `H¹` kernel has real dimension `2 |D|`.** At a smooth field with bounded derivatives
through order `3`, vanishing holomorphicity rows `∂bar_a α = 0`, `|α|² → 1` at infinity, and zero
divisor `D`, `(sobolevGaugeFixedOperator a).ker` has real dimension `2 * Multiset.card D`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * Multiset.card D :=
  (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD)

/-- **The `H¹` kernel at a framed degree-`m` field has real dimension `2m`.** -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) : finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m :=
  (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe)

/-- **Fredholm index `2 |D|` on `H¹`.** At a smooth plane vortex with bounded derivatives through
order `3`, `|α|² → 1` at infinity, and zero divisor `D`, `sobolevGaugeFixedOperator a` has
Fredholm index `2 * |D|`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul_card {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * (Multiset.card D : ℤ) := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
      (surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol hlim hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card hx hbound
      (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hlim hD hax]
  push_cast; rfl

/-- **Fredholm index `2m` on `H¹` at a framed degree-`m` vortex.** At a smooth plane vortex with
bounded derivatives through order `3` and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`,
`sobolevGaugeFixedOperator a` has Fredholm index `2m`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) : (sobolevGaugeFixedOperator a).index = 2 * (m : ℤ) := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
      (surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol
        (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul hx hbound
      (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hframe hax]
  push_cast; rfl

/-! #### Degree zero: vanishing kernel and Banach-space isomorphism -/

/-- When `α` has no zeros, `(sobolevGaugeFixedOperator a).ker` is trivial. -/
theorem ker_sobolevGaugeFixedOperator_eq_bot_of_forall_sectionValue_ne_zero (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker = ⊥ := by
  have hbot := gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero (hx.of_le (by simp)) hhol
    hlim hne
  rw [Submodule.eq_bot_iff]
  intro y hy
  let e := kerSobolevGaugeFixedOperatorEquiv hx hbound hax
  have hY : e ⟨y, hy⟩ = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hbot _ (e ⟨y, hy⟩).2)
  exact congrArg Subtype.val (e.injective (hY.trans e.map_zero.symm))

/-- **Bijectivity of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` at a vortex without zeros.** -/
theorem bijective_sobolevGaugeFixedOperator_of_forall_sectionValue_ne_zero (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) (hax : a =ᵐ[μ⊤] x) :
    Function.Bijective (sobolevGaugeFixedOperator a) :=
  ⟨LinearMap.ker_eq_bot.1 (ker_sobolevGaugeFixedOperator_eq_bot_of_forall_sectionValue_ne_zero hx
      hbound (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hlim hne hax),
    surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol hlim hax⟩

private theorem bijective_sobolevGaugeFixedOperator_of_tendsto_one (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0) (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) : Function.Bijective (sobolevGaugeFixedOperator a) := by
  have hframe₀ : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ 0)⁻¹) (cocompact ℂ)
      (𝓝 1) := by simpa using hframe
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe₀
  exact (sobolevGaugeFixedOperator a).bijective_of_surjective_of_index_eq_zero
    (finiteDimensional_ker_sobolevGaugeFixedOperator_of_contDiff_two (hx.of_le (by simp)) hsol
      hlim hax)
    (surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol hlim hax)
    (by simpa using index_sobolevGaugeFixedOperator_eq_two_mul hx hbound hsol hframe₀ hax)

/-- **Topological isomorphism `H¹(ℂ)⁴ ≃L[ℝ] L²(ℂ; ℝ⁴)` in degree zero.** At a smooth degree-zero
vortex with `α → 1` at infinity and bounded derivatives through order `3`, `L_x` has neither zero
modes nor cokernel and defines a continuous linear equivalence by Banach's open mapping theorem. -/
def sobolevGaugeFixedEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0) (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) ≃L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  have hbij := bijective_sobolevGaugeFixedOperator_of_tendsto_one hx hbound hsol hframe hax
  ContinuousLinearEquiv.ofBijective (sobolevGaugeFixedOperator a)
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)

/-- Applying `sobolevGaugeFixedEquiv` agrees with `sobolevGaugeFixedOperator`. -/
theorem sobolevGaugeFixedEquiv_apply (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0) (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedEquiv hx hbound hsol hframe hax y = sobolevGaugeFixedOperator a y := (rfl)

end SobolevKernelAndIndex

/-! ### Higher-order Sobolev realization `W^{k+1,2}(ℂ)⁴ →L[ℝ] W^{k,2}(ℂ)⁴` -/

/-- The constant-coefficient first-order leading part of `L_x` on `W^{k+1,2}(ℂ)⁴`, built from the
directional weak derivatives `Wkp.lineDerivL` along `1` and `I`. -/
def wkpGaugeFixedFirstOrder (k : ℕ) :
    (Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) →L[ℝ]
      (Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) :=
  ContinuousLinearMap.pi fun i ↦
    match i with
    | 0 => (Wkp.lineDerivL (1 : ℂ) k).comp (ContinuousLinearMap.proj 0) +
        (Wkp.lineDerivL I k).comp (ContinuousLinearMap.proj 1)
    | 1 => (Wkp.lineDerivL I k).comp (ContinuousLinearMap.proj 0) -
        (Wkp.lineDerivL (1 : ℂ) k).comp (ContinuousLinearMap.proj 1)
    | 2 => (Wkp.lineDerivL (1 : ℂ) k).comp (ContinuousLinearMap.proj 2) -
        (Wkp.lineDerivL I k).comp (ContinuousLinearMap.proj 3)
    | 3 => (Wkp.lineDerivL (1 : ℂ) k).comp (ContinuousLinearMap.proj 3) +
        (Wkp.lineDerivL I k).comp (ContinuousLinearMap.proj 2)

private theorem value_lineDerivL_ae_eq_inner_gradient (v : ℂ) (k : ℕ)
    (w : Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) :
    (Wkp.value k (Wkp.lineDerivL v k w) : ℂ → ℝ) =ᵐ[μ⊤]
      fun z ↦ ⟪W1p.gradient (Wkp.firstOrder k w) z, v⟫_ℝ := by
  have h₁ := Wkp.hasWeakLineDerivOn_lineDerivL v k w
  have h₂ := (W1p.hasWeakFDerivOn (Wkp.firstOrder k w)).hasWeakLineDerivOn v
  rw [Wkp.value_firstOrder] at h₂
  filter_upwards [h₁.ae_eq h₂] with z hz
  simpa only [innerSL_apply_apply] using hz

/-- Almost everywhere, `wkpGaugeFixedFirstOrder k y` evaluates to `gaugeFixedFirstOrder` applied to
the weak gradients of the first-order parts of `y`. -/
theorem value_wkpGaugeFixedFirstOrder_ae (k : ℕ)
    (y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) (i : Fin 4) :
    (Wkp.value k (wkpGaugeFixedFirstOrder k y i) : ℂ → ℝ) =ᵐ[μ⊤]
      fun z ↦ gaugeFixedFirstOrder (fun j ↦ W1p.gradient (Wkp.firstOrder k (y j)) z) i := by
  have hd (j : Fin 4) (v : ℂ) := value_lineDerivL_ae_eq_inner_gradient v k (y j)
  fin_cases i <;>
    simp only [wkpGaugeFixedFirstOrder, ContinuousLinearMap.pi_apply, Fin.isValue, add_apply,
      sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Wkp.value_add,
      Wkp.value_sub]
  · filter_upwards [Lp.coeFn_add (Wkp.value k (Wkp.lineDerivL 1 k (y 0)))
      (Wkp.value k (Wkp.lineDerivL I k (y 1))), hd 0 1, hd 1 I] with z h h₀ h₁
    rw [h, Pi.add_apply, h₀, h₁]; simp
  · filter_upwards [Lp.coeFn_sub (Wkp.value k (Wkp.lineDerivL I k (y 0)))
      (Wkp.value k (Wkp.lineDerivL 1 k (y 1))), hd 0 I, hd 1 1] with z h h₀ h₁
    rw [h, Pi.sub_apply, h₀, h₁]; simp
  · filter_upwards [Lp.coeFn_sub (Wkp.value k (Wkp.lineDerivL 1 k (y 2)))
      (Wkp.value k (Wkp.lineDerivL I k (y 3))), hd 2 1, hd 3 I] with z h h₂ h₃
    rw [h, Pi.sub_apply, h₂, h₃]; simp
  · filter_upwards [Lp.coeFn_add (Wkp.value k (Wkp.lineDerivL 1 k (y 3)))
      (Wkp.value k (Wkp.lineDerivL I k (y 2))), hd 3 1, hd 2 I] with z h h₃ h₂
    rw [h, Pi.add_apply, h₃, h₂]; simp

private theorem value_mem_realSobolevFunctions (k : ℕ) (u : Wkp (volume : Measure ℂ) ⊤ 2 k) :
    (Wkp.value k u : ℂ → ℝ) ∈ realSobolevFunctions ℂ k 2 := by
  set u₀ : Lp ℝ 2 (volume : Measure ℂ) := castLpₗᵢ (𝕜 := ℝ) restrict_top_eq_volume (Wkp.value k u)
  have hu₀ : MemSobolev (k : ℝ) 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u₀)) :=
    (Lp.memSobolev_natCast_iff_exists_wkp_value_eq (by norm_num) (by norm_num) k u₀).2
      ⟨u, .of_forall fun z ↦ (coeFn_castLpₗᵢ restrict_top_eq_volume (Wkp.value k u) z).symm⟩
  exact mem_realSobolevFunctions.2
    ⟨u₀, .of_forall fun z ↦ coeFn_castLpₗᵢ restrict_top_eq_volume _ z, hu₀⟩

private theorem exists_wkp_value_ae_eq_of_mem_realSobolevFunctions (k : ℕ) {g : ℂ → ℝ}
    (hg : g ∈ realSobolevFunctions ℂ k 2) :
    ∃ w : Wkp (volume : Measure ℂ) ⊤ 2 k, (Wkp.value k w : ℂ → ℝ) =ᵐ[volume] g := by
  obtain ⟨u, hug, hu⟩ := mem_realSobolevFunctions.1 hg
  obtain ⟨w, hwu⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq (by norm_num) (by norm_num) k
    u).1 hu
  exact ⟨w, hwu.trans hug⟩

section WkpStepSMul

variable (k : ℕ) {ψ : ℂ → ℝ}
  (hmul : ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2, (fun z ↦ ψ z * g z) ∈ realSobolevFunctions ℂ k 2)

private def wkpStepSMulAux (u : Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) :
    Wkp (volume : Measure ℂ) ⊤ 2 k :=
  (exists_wkp_value_ae_eq_of_mem_realSobolevFunctions k
    (hmul _ (by simpa using value_mem_realSobolevFunctions (k + 1) u))).choose

private theorem value_wkpStepSMulAux_ae (u : Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) :
    (Wkp.value k (wkpStepSMulAux k hmul u) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ ψ z * Wkp.value (k + 1) u z :=
  (exists_wkp_value_ae_eq_of_mem_realSobolevFunctions k
    (hmul _ (by simpa using value_mem_realSobolevFunctions (k + 1) u))).choose_spec

private def wkpStepSMulLinear :
    Wkp (volume : Measure ℂ) ⊤ 2 (k + 1) →ₗ[ℝ] Wkp (volume : Measure ℂ) ⊤ 2 k where
  toFun := wkpStepSMulAux k hmul
  map_add' u v := Wkp.ext k <| Lp.ext <| ae_eq_volume_iff.2 <| by
    rw [Wkp.value_add]
    filter_upwards [value_wkpStepSMulAux_ae k hmul (u + v),
      ae_eq_volume_iff.1 (Lp.coeFn_add (Wkp.value k (wkpStepSMulAux k hmul u))
        (Wkp.value k (wkpStepSMulAux k hmul v))),
      ae_eq_volume_iff.1 (Lp.coeFn_add (Wkp.value (k + 1) u) (Wkp.value (k + 1) v)),
      value_wkpStepSMulAux_ae k hmul u, value_wkpStepSMulAux_ae k hmul v] with z h₀ h₁ h₂ h₃ h₄
    rw [h₀, Wkp.value_add, h₁, h₂, Pi.add_apply, Pi.add_apply, h₃, h₄, mul_add]
  map_smul' c u := Wkp.ext k <| Lp.ext <| ae_eq_volume_iff.2 <| by
    rw [RingHom.id_apply, Wkp.value_smul]
    filter_upwards [value_wkpStepSMulAux_ae k hmul (c • u),
      ae_eq_volume_iff.1 (Lp.coeFn_smul c (Wkp.value k (wkpStepSMulAux k hmul u))),
      ae_eq_volume_iff.1 (Lp.coeFn_smul c (Wkp.value (k + 1) u)),
      value_wkpStepSMulAux_ae k hmul u] with z h₀ h₁ h₂ h₃
    rw [h₀, Wkp.value_smul, h₁, h₂, Pi.smul_apply, Pi.smul_apply, h₃, smul_eq_mul, smul_eq_mul,
      mul_left_comm]

private theorem wkpStepSMulLinear_apply (u : Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) :
    wkpStepSMulLinear k hmul u = wkpStepSMulAux k hmul u := rfl

/-- Scalar multiplication `W^{k+1,2}(ℂ) →L[ℝ] W^{k,2}(ℂ)` by an `L∞` coefficient `ψ` that maps
`H^{k+1}(ℂ)` into `H^k(ℂ)`, constructed via `Wkp.ext` and `ContinuousLinearMap.ofSeqClosedGraph`. -/
private def wkpStepSMulL (hψ : MemLp ψ ∞ volume) :
    Wkp (volume : Measure ℂ) ⊤ 2 (k + 1) →L[ℝ] Wkp (volume : Measure ℂ) ⊤ 2 k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := wkpStepSMulLinear k hmul) fun u v w hu hw ↦ by
    let M₀ := wkpStepSMulLinear k hmul
    have hC : ∀ᵐ z ∂μ⊤, ‖ψ z‖ ≤ max ‖hψ.toLp ψ‖ 0 := by
      filter_upwards [ae_eq_volume_iff.2 hψ.coeFn_toLp.symm,
        ae_volume_iff.2 (Lp.ae_norm_le_norm_top (hψ.toLp ψ))] with z h₁ h₂
      rw [h₁]; exact h₂.trans (le_max_left _ _)
    have hval : Tendsto (fun n ↦ Wkp.value k (M₀ (u n))) atTop (𝓝 (Wkp.value k (M₀ v))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n ↦ max ‖hψ.toLp ψ‖ 0 * ‖u n - v‖) atTop
          (𝓝 (max ‖hψ.toLp ψ‖ 0 * 0)) := (tendsto_iff_norm_sub_tendsto_zero.1 hu).const_mul _
      rw [mul_zero] at hlim
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hlim
      have hsub : Wkp.value k (M₀ (u n)) - Wkp.value k (M₀ v) = Wkp.value k (M₀ (u n - v)) := by
        simp only [← Wkp.valueL_apply, map_sub]
      rw [hsub]; dsimp only [M₀]; rw [wkpStepSMulLinear_apply]
      exact (Lp.norm_le_mul_norm_of_ae_eq_smul hC
        (by simpa only [smul_eq_mul] using
          ae_eq_volume_iff.2 (value_wkpStepSMulAux_ae k hmul (u n - v)))).trans
        (mul_le_mul_of_nonneg_left (Wkp.norm_value_le (k + 1) _) (le_max_right _ _))
    have hw' : Tendsto (fun n ↦ Wkp.value k (M₀ (u n))) atTop (𝓝 (Wkp.value k w)) := by
      simpa only [Function.comp_def, Wkp.valueL_apply] using
        ((Wkp.valueL k).continuous.tendsto w).comp hw
    exact Wkp.ext k (tendsto_nhds_unique hw' hval)

private theorem value_wkpStepSMulL_ae (hψ : MemLp ψ ∞ volume)
    (u : Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) :
    (Wkp.value k (wkpStepSMulL k hmul hψ u) : ℂ → ℝ) =ᵐ[μ⊤]
      fun z ↦ ψ z * Wkp.value (k + 1) u z :=
  ae_eq_volume_iff.2 (value_wkpStepSMulAux_ae k hmul u)

end WkpStepSMul

private theorem memLp_and_mul_gaugeFixedZerothOrderMatrix (k : ℕ)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) (i j : Fin 4) :
    MemLp (fun z ↦ gaugeFixedZerothOrderMatrix (x z) i j) ∞ volume ∧
      ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
        (fun z ↦ gaugeFixedZerothOrderMatrix (x z) i j * g z) ∈ realSobolevFunctions ℂ k 2 := by
  have hxa (a : Fin 4) : MemLp (fun z ↦ x z a) ∞ volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' hx
  have hneg {ψ : ℂ → ℝ} (h₁ : MemLp ψ ∞ volume)
      (h₂ : ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
        (fun z ↦ ψ z * g z) ∈ realSobolevFunctions ℂ k 2) :
      MemLp (-ψ) ∞ volume ∧ ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
        (fun z ↦ (-ψ) z * g z) ∈ realSobolevFunctions ℂ k 2 :=
    ⟨h₁.neg, fun g hg ↦ by convert neg_mem (h₂ g hg) using 1; ext z; simp [Pi.neg_apply]⟩
  have hzero : MemLp (0 : ℂ → ℝ) ∞ volume ∧ ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ (0 : ℂ → ℝ) z * g z) ∈ realSobolevFunctions ℂ k 2 :=
    ⟨MemLp.zero, fun _ _ ↦ by convert zero_mem (realSobolevFunctions ℂ k 2) using 1; ext z; simp⟩
  fin_cases i <;> fin_cases j <;>
    first | exact hzero | exact ⟨hxa _, hmul _⟩ | exact hneg (hxa _) (hmul _)

/-- **The realization `W^{k+1,2}(ℂ)⁴ →L[ℝ] W^{k,2}(ℂ)⁴` of the gauge-fixed vortex operator.**
At any essentially bounded field `x` whose coordinates multiply `H^{k+1}(ℂ)` into `H^k(ℂ)` (for
instance, any smooth field with bounded derivatives through order `k` or any framed configuration
in `framedFieldSpace f m n` with `n > 1` and `k ≤ n`), `L_x` acts as a bounded linear operator from
order `k + 1` to order `k` on the `Wkp` Sobolev scale. -/
def wkpGaugeFixedOperator (k : ℕ) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) :
    (Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) →L[ℝ]
      (Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) :=
  wkpGaugeFixedFirstOrder k + ContinuousLinearMap.pi fun i ↦ ∑ j : Fin 4,
    (wkpStepSMulL k (memLp_and_mul_gaugeFixedZerothOrderMatrix k hx hmul i j).2
      (memLp_and_mul_gaugeFixedZerothOrderMatrix k hx hmul i j).1).comp (ContinuousLinearMap.proj j)

/-- Almost everywhere, the `i`-th coordinate of `wkpGaugeFixedOperator k hx hmul y` is the `i`-th
coordinate of `L_x` evaluated on the weak gradients and values of `y`. -/
theorem value_wkpGaugeFixedOperator_ae (k : ℕ) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    (y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) (i : Fin 4) :
    (Wkp.value k (wkpGaugeFixedOperator k hx hmul y i) : ℂ → ℝ) =ᵐ[μ⊤]
      fun z ↦ (gaugeFixedFirstOrder (fun j ↦ W1p.gradient (Wkp.firstOrder k (y j)) z) +
        gaugeFixedZerothOrder (x z) (WithLp.toLp 2 fun j ↦ Wkp.value (k + 1) (y j) z)) i := by
  set M := fun j : Fin 4 ↦ wkpStepSMulL k
    (memLp_and_mul_gaugeFixedZerothOrderMatrix k hx hmul i j).2
    (memLp_and_mul_gaugeFixedZerothOrderMatrix k hx hmul i j).1 (y j)
  simp only [wkpGaugeFixedOperator, add_apply, Pi.add_apply, ContinuousLinearMap.pi_apply,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Wkp.value_add]
  filter_upwards [Lp.coeFn_add (Wkp.value k (wkpGaugeFixedFirstOrder k y i))
      (Wkp.value k (∑ j, M j)), value_wkpGaugeFixedFirstOrder_ae k y i,
    Wkp.value_finsetSum_ae k Finset.univ M, ae_all_iff.2 fun j ↦ value_wkpStepSMulL_ae k
      (memLp_and_mul_gaugeFixedZerothOrderMatrix k hx hmul i j).2
      (memLp_and_mul_gaugeFixedZerothOrderMatrix k hx hmul i j).1 (y j)] with z hadd hF hsum hM
  rw [hadd, Pi.add_apply, hF, hsum, PiLp.add_apply, gaugeFixedZerothOrder_apply]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun j _ ↦ hM j)

/-- Compatibility with `sobolevGaugeFixedOperator`: almost everywhere, the `i`-th coordinate of
`wkpGaugeFixedOperator k hx hmul y` agrees with the `i`-th coordinate of
`sobolevGaugeFixedOperator a` applied to the first-order parts of `y`. -/
theorem value_wkpGaugeFixedOperator_ae_eq_sobolevGaugeFixedOperator (k : ℕ)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x)
    (y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) (i : Fin 4) :
    (Wkp.value k (wkpGaugeFixedOperator k hx hmul y i) : ℂ → ℝ) =ᵐ[μ⊤]
      fun z ↦ sobolevGaugeFixedOperator a (fun j ↦ Wkp.firstOrder k (y j)) z i := by
  filter_upwards [value_wkpGaugeFixedOperator_ae k hx hmul y i,
    sobolevGaugeFixedOperator_apply_ae a (fun j ↦ Wkp.firstOrder k (y j)), hax] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃]; simp only [Wkp.value_firstOrder]

/-- On a variation `y` with a `C¹` representative `Y`, `wkpGaugeFixedOperator` agrees almost
everywhere with the classical operator `gaugeFixedOperator x Y`. -/
theorem value_wkpGaugeFixedOperator_ae_eq_gaugeFixedOperator (k : ℕ)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)} {Y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hY : ContDiff ℝ 1 Y) (hyY : ∀ j, Wkp.value (k + 1) (y j) =ᵐ[μ⊤] fun z ↦ Y z j) (i : Fin 4) :
    (Wkp.value k (wkpGaugeFixedOperator k hx hmul y i) : ℂ → ℝ) =ᵐ[μ⊤]
      fun z ↦ gaugeFixedOperator x Y z i := by
  have hx' : MemLp x ∞ μ⊤ := by simpa [Opens.coe_top] using hx
  have h₁ :=
    value_wkpGaugeFixedOperator_ae_eq_sobolevGaugeFixedOperator k hx hmul hx'.coeFn_toLp y i
  have h₂ := sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hx'.coeFn_toLp
    (y := fun j ↦ Wkp.firstOrder k (y j)) hY fun j ↦ by simpa [Wkp.value_firstOrder] using hyY j
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  rw [hz₁, hz₂]

/-- `wkpGaugeFixedOperator` commutes with forgetting the highest weak derivative
`Wkp.lowerOrder`. -/
theorem lowerOrder_wkpGaugeFixedOperator (k : ℕ) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : MemLp x ∞ volume)
    (hmul₁ : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ ((k + 1 : ℕ) + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ (k + 1 : ℕ) 2)
    (hmul₀ : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    (y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 2)) (i : Fin 4) :
    Wkp.lowerOrder k (wkpGaugeFixedOperator (k + 1) hx hmul₁ y i) =
      wkpGaugeFixedOperator k hx hmul₀ (fun j ↦ Wkp.lowerOrder (k + 1) (y j)) i := by
  refine Wkp.ext k (Lp.ext ?_)
  rw [← Wkp.value_succ]
  have hx' : MemLp x ∞ μ⊤ := by simpa [Opens.coe_top] using hx
  have h₁ := value_wkpGaugeFixedOperator_ae_eq_sobolevGaugeFixedOperator (k + 1) hx hmul₁
    hx'.coeFn_toLp y i
  have h₂ := value_wkpGaugeFixedOperator_ae_eq_sobolevGaugeFixedOperator k hx hmul₀
    hx'.coeFn_toLp (fun j ↦ Wkp.lowerOrder (k + 1) (y j)) i
  simp_rw [Wkp.firstOrder_succ] at h₁
  exact h₁.trans h₂.symm

/-! #### Framed fields as `Wkp` multipliers -/

/-- **Every configuration in `framedFieldSpace f m n` (`n > 1`) is essentially bounded**, without
assuming continuity of `x`: `x - x_m ∈ H^n(ℂ) ↪ L∞(ℂ)` and `x_m` is bounded. -/
theorem memLp_top_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m n : ℕ} (hn : 1 < n)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m n) : MemLp x ∞ volume := by
  have hs : (finrank ℝ ℂ : ℝ) < 2 * (n : ℝ) := by
    rw [Complex.finrank_real_complex]; exact_mod_cast Nat.mul_lt_mul_of_pos_left hn two_pos
  obtain ⟨K, -, hK⟩ :=
    exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (E := ℂ) (F := ℂ) hs
  have hcoord (i : Fin 4) : MemLp (fun z ↦ x z i) ∞ volume := by
    obtain ⟨u, hu, huS⟩ := mem_realSobolevFunctions.1
      (mem_sobolevFields.1 (mem_framedFieldSpace.1 hx) i)
    obtain ⟨B, hB⟩ := exists_norm_iteratedFDeriv_referenceField_apply_le f m i 0
    have hu_bound : ∀ᵐ z ∂volume, ‖u z‖ ≤ K * ‖huS.toBesselPotentialSpace‖ := by
      filter_upwards [hK huS, Complex.ofRealCLM.coeFn_compLp u] with z hz hre; simpa [hre] using hz
    have hdiff : MemLp (fun z ↦ (x - referenceField f m) z i) ∞ volume :=
      (memLp_top_of_bound (Lp.aestronglyMeasurable u) _ hu_bound).ae_eq hu
    have href : MemLp (fun z ↦ referenceField f m z i) ∞ volume := memLp_top_of_bound
      (contDiff_euclidean.1 (contDiff_referenceField f m) i).continuous.aestronglyMeasurable B
      (.of_forall fun z ↦ by simpa [norm_iteratedFDeriv_zero] using hB z)
    convert hdiff.add href using 1; ext z; simp
  have hsum : MemLp (fun z ↦ ∑ i : Fin 4, x z i • EuclideanSpace.single i (1 : ℝ)) ∞ volume :=
    memLp_finsetSum Finset.univ fun i _ ↦
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).comp_memLp'
        (hcoord i)
  convert hsum using 1; ext z i; simp [WithLp.ofLp_sum, EuclideanSpace.single, Pi.single_apply]

/-- **Coordinates of any `x ∈ framedFieldSpace f m n` (`n > 1`, `k ≤ n`) multiply `H^{k+1}(ℂ)` into
`H^k(ℂ)`.** At `k = 0` this uses `x ∈ L∞`; at `k = 1` it uses the algebra property of `H^2(ℂ)`; at
`k ≥ 2` it uses `framedFieldSpace_mono` and `mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`.
-/
theorem mul_mem_realSobolevFunctions_of_mem_framedFieldSpace_le {f : ContDiffBump (0 : ℝ)}
    {m n k : ℕ} (hn : 1 < n) (hkn : k ≤ n) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m n) (a : Fin 4) {g : ℂ → ℝ}
    (hg : g ∈ realSobolevFunctions ℂ (k + 1) 2) :
    (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2 := by
  rcases k with _ | _ | k
  · have hxa : MemLp (fun z ↦ x z a) ∞ volume :=
      (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' (memLp_top_of_mem_framedFieldSpace hn hx)
    obtain ⟨u, hug, -⟩ := mem_realSobolevFunctions.1 hg
    have hprod : MemLp (fun z ↦ x z a * g z) 2 volume := hxa.fun_mul ((Lp.memLp u).ae_eq hug)
    exact mem_realSobolevFunctions.2
      ⟨hprod.toLp _, hprod.coeFn_toLp, by simpa using (memSobolev_zero_iff (p := 2)).2 ⟨_, rfl⟩⟩
  · have hx₂ : x ∈ framedFieldSpace f m (2 : ℕ) :=
      framedFieldSpace_mono f m (by exact_mod_cast hn) hx
    have hg₂ : g ∈ realSobolevFunctions ℂ (2 : ℕ) 2 := by norm_num at hg ⊢; exact hg
    exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by norm_num)
      (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace one_lt_two hx₂ a hg₂)
  · have hxk : x ∈ framedFieldSpace f m (k + 2 : ℕ) :=
      framedFieldSpace_mono f m (by exact_mod_cast hkn) hx
    exact mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hxk a
      (realSobolevFunctions_mono (by norm_num) (by norm_num) (by norm_cast; omega) hg)

/-! ### Fredholmness, right inverse, kernel equivalence, and index `2m` on `W^{k+1,2} → W^{k,2}` -/

section HigherSobolevVortex

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

private def wkpValuesToLp (k : ℕ) : (Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) :=
  castTopToVolumeCLM.comp (tupleToLp (Wkp.valueL k))

private theorem wkpValuesToLp_apply_ae (k : ℕ) (g : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) :
    (wkpValuesToLp k g : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
      fun z ↦ WithLp.toLp 2 fun j ↦ Wkp.value k (g j) z := by
  filter_upwards [ae_eq_volume_iff.1 (tupleToLp_apply_ae (Wkp.valueL k) g)] with z hz
  simpa only [wkpValuesToLp, ContinuousLinearMap.comp_apply, coeFn_castTopToVolumeCLM,
    Wkp.valueL_apply] using hz

private theorem wkpValuesToLp_mem_sobolevFields (k : ℕ)
    (g : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) :
    (wkpValuesToLp k g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields k :=
  mem_sobolevFields_of_ae_eq (mem_sobolevFields.2 fun j ↦ value_mem_realSobolevFunctions k (g j))
    (wkpValuesToLp_apply_ae k g).symm

/-- Canonical injection of `(wkpGaugeFixedOperator k hx hmul).ker` into
`(sobolevGaugeFixedOperator a).ker` via `Wkp.firstOrder k`. -/
def kerWkpToSobolevKer (k : ℕ) (hx : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x) :
    (wkpGaugeFixedOperator k hx hmul).ker →ₗ[ℝ] (sobolevGaugeFixedOperator a).ker where
  toFun y := ⟨fun j ↦ Wkp.firstOrder k (y.1 j), by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine Lp.ext ?_
    have hy0 : wkpGaugeFixedOperator k hx hmul y.1 = 0 := by
      have h := y.2; rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h
    have hi (i : Fin 4) :
        (fun z ↦ sobolevGaugeFixedOperator a (fun j ↦ Wkp.firstOrder k (y.1 j)) z i) =ᵐ[μ⊤] 0 := by
      have h₁ := (value_wkpGaugeFixedOperator_ae_eq_sobolevGaugeFixedOperator k hx hmul hax y.1
        i).symm
      rw [congrFun hy0 i, Pi.zero_apply, ← Wkp.valueL_apply, map_zero] at h₁
      exact h₁.trans (Lp.coeFn_zero ℝ 2 μ⊤)
    filter_upwards [ae_all_iff.2 hi, Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ⊤] with z h₁ h₀
    ext i; rw [h₁ i, h₀]; simp only [Pi.zero_apply, PiLp.zero_apply]⟩
  map_add' y₁ y₂ := Subtype.ext <| funext fun j ↦ by simp [← Wkp.firstOrderL_apply]
  map_smul' c y := Subtype.ext <| funext fun j ↦ by simp [← Wkp.firstOrderL_apply]

/-- Coordinates of `kerWkpToSobolevKer` are given by `Wkp.firstOrder k`. -/
theorem coe_kerWkpToSobolevKer_apply (k : ℕ) (hx : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x)
    (y : (wkpGaugeFixedOperator k hx hmul).ker) (j : Fin 4) :
    (kerWkpToSobolevKer k hx hmul hax y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) j =
      Wkp.firstOrder k ((y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)) j) := (rfl)

/-- `kerWkpToSobolevKer` is unconditionally injective at every order `k`, by uniqueness of weak
derivatives (`Wkp.ext`). -/
theorem kerWkpToSobolevKer_injective (k : ℕ) (hx : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x) :
    Function.Injective (kerWkpToSobolevKer k hx hmul hax) := by
  intro y₁ y₂ h
  refine Subtype.ext (funext fun j ↦ Wkp.ext (k + 1) ?_)
  simpa only [coe_kerWkpToSobolevKer_apply, Wkp.value_firstOrder] using
    congrArg W1p.value (congrFun (congrArg Subtype.val h) j)

/-- **Finite dimensionality of the `W^{k+1,2}` kernel at any `C²` vortex**, without assuming
higher regularity of `x`: `Wkp.firstOrder k` embeds the kernel into the `H¹` kernel. -/
theorem finiteDimensional_ker_wkpGaugeFixedOperator (k : ℕ) (hx : ContDiff ℝ 2 x)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (wkpGaugeFixedOperator k hxb hmul).ker := by
  have hx' : MemLp x ∞ μ⊤ := by simpa [Opens.coe_top] using hxb
  let a₀ : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ := hx'.toLp x
  have ha₀ : a₀ =ᵐ[μ⊤] x := hx'.coeFn_toLp
  have : FiniteDimensional ℝ (sobolevGaugeFixedOperator a₀).ker :=
    finiteDimensional_ker_sobolevGaugeFixedOperator_of_contDiff_two hx hsol hlim ha₀
  exact FiniteDimensional.of_injective (V₂ := (sobolevGaugeFixedOperator a₀).ker)
    (kerWkpToSobolevKer k hxb hmul (a := a₀) ha₀)
    (kerWkpToSobolevKer_injective k hxb hmul (a := a₀) ha₀)

private theorem surjective_kerWkpToSobolevKer (k : ℕ) (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (kerWkpToSobolevKer k hxb hmul hax) := by
  rintro ⟨z, hz⟩
  have hweak := (mem_ker_sobolevGaugeFixedOperator_iff hx.continuous hax z).1 hz
  have huk : (fun w ↦ WithLp.toLp 2 fun j ↦ W1p.value (z j) w) ∈
      sobolevFields ((k + 1 : ℕ) : ℝ) := by
    simpa using mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
      hbound (memLp_value_tuple z) (zero_mem _) fun η hη hηc ↦ by simpa using hweak η hη hηc
  choose y hy using fun j : Fin 4 ↦
    exists_wkp_value_ae_eq_of_mem_realSobolevFunctions (k + 1) (mem_sobolevFields.1 huk j)
  have hy_first (j : Fin 4) : Wkp.firstOrder k (y j) = z j :=
    W1p.ext_value (Lp.ext (by rw [Wkp.value_firstOrder]; exact ae_eq_volume_iff.2 (hy j)))
  have hy_ker : y ∈ (wkpGaugeFixedOperator k hxb hmul).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    funext i; refine Wkp.ext k (Lp.ext ?_)
    rw [Pi.zero_apply, ← Wkp.valueL_apply k 0, map_zero]
    have h₁ := value_wkpGaugeFixedOperator_ae_eq_sobolevGaugeFixedOperator k hxb hmul hax y i
    simp_rw [hy_first] at h₁
    have hz0 : sobolevGaugeFixedOperator a z = 0 := by
      rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hz
    rw [hz0] at h₁
    filter_upwards [h₁, Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ⊤,
      Lp.coeFn_zero ℝ 2 μ⊤] with w hw₁ hw₀ hw₀'
    rw [hw₁, hw₀, hw₀']; simp only [Pi.zero_apply, PiLp.zero_apply]
  exact ⟨⟨y, hy_ker⟩, Subtype.ext (funext hy_first)⟩

/-- **Equivalence between the `W^{k+1,2}` kernel and the `H¹` kernel.** At a smooth field with
bounded derivatives through order `k`, `Wkp.firstOrder k` is a linear isomorphism between
`(wkpGaugeFixedOperator k hxb hmul).ker` and `(sobolevGaugeFixedOperator a).ker`. -/
def kerWkpGaugeFixedOperatorToSobolevEquiv (k : ℕ) (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x) :
    (wkpGaugeFixedOperator k hxb hmul).ker ≃ₗ[ℝ] (sobolevGaugeFixedOperator a).ker :=
  LinearEquiv.ofBijective (kerWkpToSobolevKer k hxb hmul hax)
    ⟨kerWkpToSobolevKer_injective k hxb hmul hax,
      surjective_kerWkpToSobolevKer k hx hbound hxb hmul hax⟩

/-- Applying `kerWkpGaugeFixedOperatorToSobolevEquiv` agrees with `kerWkpToSobolevKer`. -/
theorem kerWkpGaugeFixedOperatorToSobolevEquiv_apply (k : ℕ) (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x)
    (y : (wkpGaugeFixedOperator k hxb hmul).ker) :
    kerWkpGaugeFixedOperatorToSobolevEquiv k hx hbound hxb hmul hax y =
      kerWkpToSobolevKer k hxb hmul hax y := (rfl)

/-- **Equivalence between the `W^{k+1,2}` kernel and `gaugeFixedKernel x`.** At a smooth field with
bounded derivatives through order `max k 3`, the `W^{k+1,2}` kernel of `L_x` is canonically
isomorphic to the classical `C² ∩ L²` kernel `gaugeFixedKernel x`. -/
def kerWkpGaugeFixedOperatorEquiv (k : ℕ) (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ max k 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) :
    (wkpGaugeFixedOperator k hxb hmul).ker ≃ₗ[ℝ] gaugeFixedKernel x :=
  have hx' : MemLp x ∞ μ⊤ := by simpa [Opens.coe_top] using hxb
  (kerWkpGaugeFixedOperatorToSobolevEquiv k hx
    (fun i n hn ↦ hbound i n (hn.trans (le_max_left k 3))) hxb hmul hx'.coeFn_toLp).trans
    (kerSobolevGaugeFixedOperatorEquiv hx
      (fun i n hn ↦ hbound i n (hn.trans (le_max_right k 3))) hx'.coeFn_toLp)

private theorem integral_inner_wkpValuesToLp_gaugeFixedAdjoint_eq_zero (k : ℕ) (hx : Continuous x)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    {y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)}
    (hy : y ∈ (wkpGaugeFixedOperator k hxb hmul).ker) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪wkpValuesToLp (k + 1) y z, gaugeFixedAdjoint x η z⟫ = 0 := by
  have hx' : MemLp x ∞ μ⊤ := by simpa [Opens.coe_top] using hxb
  set y₁ := kerWkpToSobolevKer k hxb hmul hx'.coeFn_toLp ⟨y, hy⟩
  have hy_ae : (wkpValuesToLp (k + 1) y : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
      fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y₁.1 j) z := by
    filter_upwards [wkpValuesToLp_apply_ae (k + 1) y] with z hz
    rw [hz]; ext j; change Wkp.value (k + 1) (y j) z = W1p.value (Wkp.firstOrder k (y j)) z
    rw [Wkp.value_firstOrder]
  rw [integral_congr_ae (hy_ae.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)]
  exact integral_inner_gaugeFixedAdjoint_eq_zero_of_mem_ker hx hx'.coeFn_toLp y₁.2 hη hηc

/-- **Bounded `L²`-orthogonal right inverse `W^{k,2}(ℂ)⁴ →L[ℝ] W^{k+1,2}(ℂ)⁴` at a smooth
vortex.** Let `x` be a smooth solution of the plane vortex equation with bounded derivatives
through order `k` and `|α|² → 1` at infinity. Then `wkpGaugeFixedOperator` admits a continuous
linear right inverse whose image is orthogonal in `L²` to the kernel. -/
theorem exists_continuousLinearMap_wkpGaugeFixedOperator_comp_eq_id (k : ℕ) (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ R : (Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) →L[ℝ]
        (Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)),
      (wkpGaugeFixedOperator k hxb hmul).comp R = ContinuousLinearMap.id ℝ _ ∧
      ∀ g (y : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 (k + 1)),
        y ∈ (wkpGaugeFixedOperator k hxb hmul).ker →
          ∫ z, ⟪WithLp.toLp 2 (fun j ↦ Wkp.value (k + 1) (R g j) z),
            WithLp.toLp 2 (fun j ↦ Wkp.value (k + 1) (y j) z)⟫ = 0 := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) (hx.of_le (by simp)) hsol hlim
  set Q' := Q.comp (wkpValuesToLp k)
  have hinj : Function.Injective
      (Wkp.valueL (k + 1) : Wkp (volume : Measure ℂ) ⊤ 2 (k + 1) →L[ℝ] Lp ℝ 2 μ⊤) :=
    fun _ _ h ↦ Wkp.ext (k + 1) (by rwa [Wkp.valueL_apply, Wkp.valueL_apply] at h)
  have hex (g : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) (j : Fin 4) :
      ∃ w : Wkp (volume : Measure ℂ) ⊤ 2 (k + 1),
        (Wkp.valueL (k + 1) w : ℂ → ℝ) =ᵐ[volume] fun z ↦ Q' g z j := by
    have hreg : (Q' g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields ((k + 1 : ℕ) : ℝ) := by
      simpa using mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
        hbound (Lp.memLp (Q' g)) (wkpValuesToLp_mem_sobolevFields k g)
        fun η hη hηc ↦ hQ (wkpValuesToLp k g) η (hη.of_le (by norm_cast)) hηc
    obtain ⟨w, hw⟩ :=
      exists_wkp_value_ae_eq_of_mem_realSobolevFunctions (k + 1) (mem_sobolevFields.1 hreg j)
    exact ⟨w, by rwa [Wkp.valueL_apply]⟩
  set R := liftToTupleCLM (Wkp.valueL (k + 1)) hinj Q' hex
  have hx' : MemLp x ∞ μ⊤ := by simpa [Opens.coe_top] using hxb
  have hRval (g : Fin 4 → Wkp (volume : Measure ℂ) ⊤ 2 k) :
      (fun z ↦ WithLp.toLp 2 fun j ↦ Wkp.value (k + 1) (R g j) z) =ᵐ[volume]
        (Q' g : ℂ → EuclideanSpace ℝ (Fin 4)) := by
    filter_upwards [ae_all_iff.2 (valL_liftToTupleCLM_ae (Wkp.valueL (k + 1)) hinj Q' hex g)]
      with z hz
    ext j; change Wkp.value (k + 1) (R g j) z = (Q' g z).ofLp j
    rw [← Wkp.valueL_apply]; exact hz j
  refine ⟨R, ContinuousLinearMap.ext fun g ↦ funext fun i ↦ Wkp.ext k (Lp.ext ?_),
    fun g y hy ↦ ?_⟩
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    have hsobeq : sobolevGaugeFixedOperator (hx'.toLp x) (fun j ↦ Wkp.firstOrder k (R g j)) =
        castLpₗᵢ (𝕜 := ℝ) restrict_top_eq_volume.symm (wkpValuesToLp k g) := by
      rw [sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
        hx.continuous hx'.coeFn_toLp]
      intro η hη hηc
      simp_rw [Wkp.value_firstOrder]
      have hQ'g : Q' g = Q (wkpValuesToLp k g) := rfl
      rw [integral_congr_ae ((hRval g).mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz),
        hQ'g, hQ _ η (hη.of_le (by norm_cast)) hηc]
      exact integral_congr_ae (.of_forall fun z ↦
        congrArg (⟪·, η z⟫) (coeFn_castLpₗᵢ restrict_top_eq_volume.symm _ z).symm)
    filter_upwards [value_wkpGaugeFixedOperator_ae_eq_sobolevGaugeFixedOperator k hxb hmul
      hx'.coeFn_toLp (R g) i, ae_eq_volume_iff.2 (wkpValuesToLp_apply_ae k g)] with z h₁ h₂
    rw [h₁, hsobeq, coeFn_castLpₗᵢ, h₂]
  · rw [← hQK (wkpValuesToLp k g) (wkpValuesToLp (k + 1) y) fun η hη hηc ↦
      integral_inner_wkpValuesToLp_gaugeFixedAdjoint_eq_zero k hx.continuous hxb hmul hy hη hηc]
    refine integral_congr_ae ?_
    filter_upwards [hRval g, wkpValuesToLp_apply_ae (k + 1) y] with z h₁ h₂
    rw [h₁, h₂]; rfl

/-- **Surjectivity of `L_x : W^{k+1,2}(ℂ)⁴ → W^{k,2}(ℂ)⁴` at a smooth vortex.** -/
theorem surjective_wkpGaugeFixedOperator (k : ℕ) (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Function.Surjective (wkpGaugeFixedOperator k hxb hmul) := by
  obtain ⟨R, hR, -⟩ := exists_continuousLinearMap_wkpGaugeFixedOperator_comp_eq_id k hx hbound hxb
    hmul hsol hlim
  exact fun g ↦ ⟨R g, congrFun (congrArg DFunLike.coe hR) g⟩

/-- **Fredholmness of `L_x : W^{k+1,2}(ℂ)⁴ →L[ℝ] W^{k,2}(ℂ)⁴` at a smooth plane vortex.** -/
theorem isFredholm_wkpGaugeFixedOperator (k : ℕ) (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    (wkpGaugeFixedOperator k hxb hmul).IsFredholm := by
  have := finiteDimensional_ker_wkpGaugeFixedOperator k (hx.of_le (by simp)) hxb hmul hsol hlim
  exact ContinuousLinearMap.IsFredholm.of_surjective
    (surjective_wkpGaugeFixedOperator k hx hbound hxb hmul hsol hlim)

/-- **The `W^{k+1,2}` kernel has real dimension `2 |D|`.** -/
theorem finrank_ker_wkpGaugeFixedOperator_eq_two_mul_card (k : ℕ) {D : Multiset ℂ}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ max k 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    finrank ℝ (wkpGaugeFixedOperator k hxb hmul).ker = 2 * Multiset.card D :=
  (kerWkpGaugeFixedOperatorEquiv k hx hbound hxb hmul).finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD)

/-- **The `W^{k+1,2}` kernel at a framed degree-`m` field has real dimension `2m`.** -/
theorem finrank_ker_wkpGaugeFixedOperator_eq_two_mul (k : ℕ) {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ max k 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    finrank ℝ (wkpGaugeFixedOperator k hxb hmul).ker = 2 * m :=
  (kerWkpGaugeFixedOperatorEquiv k hx hbound hxb hmul).finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe)

/-- **Fredholm index `2 |D|` on `W^{k+1,2}(ℂ)⁴ → W^{k,2}(ℂ)⁴`.** -/
theorem index_wkpGaugeFixedOperator_eq_two_mul_card (k : ℕ) {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ max k 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    (wkpGaugeFixedOperator k hxb hmul).index = 2 * (Multiset.card D : ℤ) := by
  rw [(wkpGaugeFixedOperator k hxb hmul).index_of_surjective (surjective_wkpGaugeFixedOperator k hx
        (fun i n hn ↦ hbound i n (hn.trans (le_max_left k 3))) hxb hmul hsol hlim),
    finrank_ker_wkpGaugeFixedOperator_eq_two_mul_card k hx hbound hxb hmul
      (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hlim hD]
  push_cast; rfl

/-- **Fredholm index `2m` on `W^{k+1,2}(ℂ)⁴ → W^{k,2}(ℂ)⁴` at a framed degree-`m` vortex.** -/
theorem index_wkpGaugeFixedOperator_eq_two_mul (k : ℕ) {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ max k 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hxb : MemLp x ∞ volume) (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    (wkpGaugeFixedOperator k hxb hmul).index = 2 * (m : ℤ) := by
  rw [(wkpGaugeFixedOperator k hxb hmul).index_of_surjective (surjective_wkpGaugeFixedOperator k hx
        (fun i n hn ↦ hbound i n (hn.trans (le_max_left k 3))) hxb hmul hsol
        (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)),
    finrank_ker_wkpGaugeFixedOperator_eq_two_mul k hx hbound hxb hmul
      (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hframe]
  push_cast; rfl

/-! #### Framed plane vortices on the affine Sobolev scale `A_m^n` -/

/-- **Fredholmness on `W^{k+1,2} → W^{k,2}` at a vortex lying in every `framedFieldSpace`.** -/
theorem isFredholm_wkpGaugeFixedOperator_of_forall_mem_framedFieldSpace
    {ρ : ContDiffBump (0 : ℝ)} {m : ℕ} (k : ℕ) (hx : Continuous x)
    (hmem : ∀ j : ℕ, x ∈ framedFieldSpace ρ m j) (hsol : ∀ z, equation x z = 0) :
    (wkpGaugeFixedOperator k
      (memLp_top_of_mem_framedFieldSpace (by omega : 1 < max k 2) (hmem (max k 2)))
      (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace_le (by omega : 1 < max k 2)
        (le_max_left k 2) (hmem (max k 2)))).IsFredholm :=
  isFredholm_wkpGaugeFixedOperator k (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2))) _ _
    hsol (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx)

/-- **Fredholm index `2m` on `W^{k+1,2} → W^{k,2}` at a vortex in every `framedFieldSpace`.** -/
theorem index_wkpGaugeFixedOperator_eq_two_mul_of_forall_mem_framedFieldSpace
    {ρ : ContDiffBump (0 : ℝ)} {m : ℕ} (k : ℕ) (hx : Continuous x)
    (hmem : ∀ j : ℕ, x ∈ framedFieldSpace ρ m j) (hsol : ∀ z, equation x z = 0) :
    (wkpGaugeFixedOperator k
      (memLp_top_of_mem_framedFieldSpace (by omega : 1 < max k 2) (hmem (max k 2)))
      (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace_le (by omega : 1 < max k 2)
        (le_max_left k 2) (hmem (max k 2)))).index = 2 * (m : ℤ) :=
  index_wkpGaugeFixedOperator_eq_two_mul k (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2))) _ _
    hsol (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx)

/-- **Fredholmness on `W^{k+1,2} → W^{k,2}` at any `C¹` Coulomb-slice vortex in `A_m^n`,
`n ≥ 2`.** By `mem_framedFieldSpace_of_equation_eq_zero`, a `C¹` vortex `x ∈ A_m^n` (`n > 1`) in
the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` relative to a `C¹` base field `x₀` in every `A_m^j` is
smooth and lies in every `A_m^j`, so `L_x` is Fredholm at every order `k`. -/
theorem isFredholm_wkpGaugeFixedOperator_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)} {m n : ℕ}
    (hn : 1 < n) (k : ℕ) {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m n) (hxc : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) (hxb : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) :
    (wkpGaugeFixedOperator k hxb hmul).IsFredholm :=
  isFredholm_wkpGaugeFixedOperator_of_forall_mem_framedFieldSpace k hxc.continuous
    (mem_framedFieldSpace_of_equation_eq_zero hn hx₀ hx₀c hx hxc hsol hgauge) hsol

/-- **Fredholm index `2m` on `W^{k+1,2} → W^{k,2}` at any `C¹` Coulomb-slice vortex in `A_m^n`,
`n ≥ 2`.** Taking `n = k + 1` (`k ≥ 1`), `hxb = memLp_top_of_mem_framedFieldSpace hn hx`, and
`hmul = mul_mem_realSobolevFunctions_of_mem_framedFieldSpace_le hn (Nat.le_succ k) hx` gives
Fredholm index `2m` on the tangent space `W^{k+1,2}(ℂ)⁴ →L[ℝ] W^{k,2}(ℂ)⁴` of `A_m^(k+1)`. -/
theorem index_wkpGaugeFixedOperator_eq_two_mul_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)}
    {m n : ℕ} (hn : 1 < n) (k : ℕ) {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m n) (hxc : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) (hxb : MemLp x ∞ volume)
    (hmul : ∀ a : Fin 4, ∀ g ∈ realSobolevFunctions ℂ (k + 1) 2,
      (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ k 2) :
    (wkpGaugeFixedOperator k hxb hmul).index = 2 * (m : ℤ) :=
  index_wkpGaugeFixedOperator_eq_two_mul_of_forall_mem_framedFieldSpace k hxc.continuous
    (mem_framedFieldSpace_of_equation_eq_zero hn hx₀ hx₀c hx hxc hsol hgauge) hsol

end HigherSobolevVortex

end TauCeti.Vortex
