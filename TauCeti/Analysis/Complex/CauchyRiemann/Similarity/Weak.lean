/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.Scalar
public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Examples
public import TauCeti.Analysis.Complex.Wirtinger.Weak
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.RankOne
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The Sobolev similarity principle for weak linear Cauchy–Riemann equations

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open, and `2 < p < ∞`. Suppose
`J : ℂ → V →L[ℝ] V` is continuous and belongs to `W^{1,p}_loc(Ω)` with `J(z)² = -1` on `Ω`, and
`C : ℂ → V →L[ℝ] V` belongs to `Lᵖ_loc(Ω)`. Let `ξ : ℂ → V` solve the weak linear Cauchy–Riemann
equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

on `Ω`, in the coordinate `z = s + i t` (`TauCeti.IsWeakLinearCauchyRiemannOn p Ω J C ξ`).
The **vector similarity principle** (Carleman; McDuff–Salamon, Theorem 2.3.5) says that around
every point `z₀ ∈ Ω` there is a closed disc `closedBall z₀ r ⊆ Ω` (`r > 0`) on which `ξ` factors
as `ξ = Φ σ`, where `Φ : ℂ → V →L[ℝ] V` is continuous and of class `W^{1,p}_loc` on the closed
disc, invertible there, and intertwines `J` with `i` (`J(z) Φ(z) = Φ(z) i`), while `σ : ℂ → V` is
continuous on the closed disc and holomorphic on the open disc
(`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann`).

The proof has three stages:

1. **Supercritical Cauchy integral equation** (`TauCeti.exists_cauchyTransform_eq_of_memLp`):
   for `q < 2` conjugate to `p` (`p > 2`), a complex-linear coefficient `D ∈ Lᵖ` on a closed disc
   such that `2⁻¹ π⁻¹ ‖K_{2r}‖_{L^q} ‖D‖_{Lᵖ} ≤ 1/4` yields a contraction `Ψ ↦ 1 + T (½ Ψ D)` on
   `C(closedBall c r, E →L[ℂ] E)`, by `TauCeti.norm_cauchyTransform_le` and
   `TauCeti.continuous_cauchyTransform_of_memLp`. Its fixed point `Ψ = 1 + T g` has `g ∈ Lᵖ`
   supported in the disc and `‖T g‖ < 1` there.
2. **Constant complex structure `i`**
   (`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn`,
   `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann_I_smul_id`): after transporting `V` to a
   Euclidean space, the real-linear term `C ξ` is absorbed into the complex-linear rank-one field
   `D w = ‖ξ‖⁻² ⟪ξ, w⟫ C ξ` (`MeasureTheory.MemLp.rankOneDivNormSq_apply`), whose `Lᵖ` norm does
   not exceed that of `C`. Because `‖K_{2r}‖_{L^q} → 0` as `r → 0`
   (`TauCeti.tendsto_eLpNorm_truncatedCauchyKernel_nhds_zero`), a sufficiently small closed disc
   satisfies the contraction bound. Interior `W^{1,p}` regularity for `bar∂`
   (`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_one`) places both `Ψ` and `ξ` in `W^{1,p}_loc`,
   and the mixed-exponent Sobolev Leibniz rule (`TauCeti.HasWeakFDerivOn.bilin_of_memLpLoc`) shows
   that `σ = Ψ ξ` satisfies `bar∂σ = 0` weakly on the open disc, hence is holomorphic by Weyl's
   lemma. Pointwise inversion in `W^{1,p}_loc` (`TauCeti.MemWkpLoc.ring_inverse`) produces
   `Φ = Ψ⁻¹`.
3. **Variable complex structure `J`**
   (`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann`): at `z₀`, a real-linear automorphism
   `Φ₁` conjugates `J(z₀)` to `i`
   (`ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`). The standard frame
   `Φ₀(z) = ½(1 - J(z) J(z₀)) Φ₁` (`TauCeti.standardFrame`) lies in `W^{1,p}_loc` with `J`, is
   invertible near `z₀`, intertwines `J` with `i`, and reduces the equation to `η = Φ₀⁻¹ ξ` for
   `J = i` with an `Lᵖ_loc` coefficient `C'`
   (`TauCeti.isWeakLinearCauchyRiemannOn_iff_standardFrame`, `TauCeti.memLpLoc_frameCoeff_iff`).
   Composing `Φ₀` with the complex-linear factor of `η` yields the intertwining `W^{1,p}` factor
   for `ξ`.

From `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`, every weak solution on a
preconnected open domain inherits unique continuation (from open sets, neighbourhoods, and
infinite-order zeros), isolated zeros, and well-defined positive integer orders at its zeros.
The closing sections compare the `n = 1` case with the scalar `Cᵏ` integrating-factor construction
and establish calibrating examples and counterexamples (including impossibility of an `Lᵖ_loc`
coefficient for the flat function `exp (-1 / ‖z‖²)`).

## Main results

* `TauCeti.exists_cauchyTransform_eq_of_memLp`: the supercritical `Lᵖ` Cauchy integral equation on
  a closed disc.
* `TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn` and
  `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann_I_smul_id`: the `W^{1,p}` complex-linear
  similarity principle for the constant structure `i`.
* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann`: the vector similarity principle for a
  variable `W^{1,p}_loc` complex structure `J` and an `Lᵖ_loc` coefficient `C` (`2 < p < ∞`).
* `TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemann_of_eventually_eq_zero`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemann_of_eqOn_zero`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemann_of_forall_isBigO`,
  `TauCeti.eventually_ne_zero_of_isWeakLinearCauchyRiemann`,
  `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemann`, and
  `TauCeti.exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemann`: unique continuation, isolated
  zeros, and positive integer orders of zeros.
* `TauCeti.not_exists_memLpLoc_isWeakLinearCauchyRiemannOn_expNegInvNormSq`: `exp (-1 / ‖z‖²)`
  admits no `Lᵖ_loc` coefficient (`2 < p < ∞`) on any open neighbourhood of `0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 and Appendix B.4.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex ComplexConjugate ContinuousLinearMap Filter Function MeasureTheory Metric
  Set Topology TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

/-! ### The supercritical Cauchy integral equation -/

section CauchyEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The source term `½ Ψ D` of the Cauchy integral equation, for `Ψ` given on a closed disc and
extended by `0` outside it. -/
private def cauchySourceLp {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) (z : ℂ) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (extend Subtype.val Ψ 0 z).comp (D z)

/-- On `closedBall c r`, `cauchySourceLp D Ψ z = ½ (Ψ z) ∘ (D z)`. -/
private theorem cauchySourceLp_of_mem {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) {z : ℂ} (hz : z ∈ closedBall c r) :
    cauchySourceLp D Ψ z = (2 : ℂ)⁻¹ • (Ψ ⟨z, hz⟩).comp (D z) := by
  rw [cauchySourceLp, Subtype.val_injective.extend_apply Ψ 0 ⟨z, hz⟩]

/-- Outside `closedBall c r`, `cauchySourceLp D Ψ` vanishes. -/
private theorem cauchySourceLp_of_notMem {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) {z : ℂ} (hz : z ∉ closedBall c r) :
    cauchySourceLp D Ψ z = 0 := by
  rw [cauchySourceLp, extend_apply' _ _ _ fun ⟨w, hw⟩ ↦ hz (hw ▸ w.2)]
  simp

/-- The support of `cauchySourceLp D Ψ` is contained in `closedBall c r`. -/
private theorem support_cauchySourceLp_subset {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) : support (cauchySourceLp D Ψ) ⊆ closedBall c r :=
  fun _ hz ↦ by_contra fun h ↦ hz (cauchySourceLp_of_notMem D Ψ h)

/-- `cauchySourceLp D` preserves subtraction in `Ψ`. -/
private theorem cauchySourceLp_sub {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) :
    cauchySourceLp D (Ψ - Ψ') = cauchySourceLp D Ψ - cauchySourceLp D Ψ' := by
  ext1 z
  by_cases hz : z ∈ closedBall c r
  · simp only [Pi.sub_apply, cauchySourceLp_of_mem D _ hz, ContinuousMap.sub_apply,
      ContinuousLinearMap.sub_comp, smul_sub]
  · simp [cauchySourceLp_of_notMem D _ hz]

/-- `cauchySourceLp D Ψ` is a.e. strongly measurable on `ℂ` when `D` is on `closedBall c r`. -/
private theorem aestronglyMeasurable_cauchySourceLp {c : ℂ} {r : ℝ} {D : ℂ → E →L[ℂ] E}
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (Ψ : C(closedBall c r, E →L[ℂ] E)) : AEStronglyMeasurable (cauchySourceLp D Ψ) volume := by
  have he : ContinuousOn (extend Subtype.val Ψ 0) (closedBall c r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert Ψ.continuous using 1
    ext1 z
    exact Subtype.val_injective.extend_apply Ψ 0 z
  have heq : cauchySourceLp D Ψ = (closedBall c r).indicator (cauchySourceLp D Ψ) :=
    (indicator_eq_self.2 (support_cauchySourceLp_subset D Ψ)).symm
  rw [heq, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
  exact ((ContinuousLinearMap.compL ℂ E E E).aestronglyMeasurable_comp₂
    (he.aestronglyMeasurable measurableSet_closedBall) hD).const_smul (2 : ℂ)⁻¹

/-- Extended `Lᵖ` bound for `cauchySourceLp D Ψ` in terms of a uniform bound `B` on `Ψ`. -/
private theorem eLpNorm_cauchySourceLp_le {p : ℝ≥0∞} {c : ℂ} {r B : ℝ} {D : ℂ → E →L[ℂ] E}
    (hB : 0 ≤ B) (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    {Ψ : C(closedBall c r, E →L[ℂ] E)} (hΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    eLpNorm (cauchySourceLp D Ψ) p volume ≤
      ENNReal.ofReal (2⁻¹ * B) * eLpNorm D p (volume.restrict (closedBall c r)) := by
  have heq : cauchySourceLp D Ψ = (closedBall c r).indicator (cauchySourceLp D Ψ) :=
    (indicator_eq_self.2 (support_cauchySourceLp_subset D Ψ)).symm
  have hm : NullMeasurableSet (closedBall c r) volume := measurableSet_closedBall.nullMeasurableSet
  rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict (f := cauchySourceLp D Ψ) (p := p) hm]
  let C₀ : ℝ≥0 := ⟨2⁻¹ * B, by positivity⟩
  have hC₀ : (C₀ : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ * B) :=
    (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
  rw [← hC₀, ← smul_eq_mul]
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (aestronglyMeasurable_cauchySourceLp hD Ψ).restrict ?_ p
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm,
    cauchySourceLp_of_mem D Ψ hz, norm_smul, norm_inv, Complex.norm_ofNat]
  change 2⁻¹ * ‖(Ψ ⟨z, hz⟩).comp (D z)‖ ≤ 2⁻¹ * B * ‖D z‖
  rw [mul_assoc]
  gcongr
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hΨ ⟨z, hz⟩) (norm_nonneg _))

/-- `cauchySourceLp D Ψ` belongs to `Lᵖ(ℂ)` whenever `D` belongs to `Lᵖ(closedBall c r)`. -/
private theorem memLp_cauchySourceLp {p : ℝ≥0∞} {c : ℂ} {r : ℝ} {D : ℂ → E →L[ℂ] E}
    (hD : MemLp D p (volume.restrict (closedBall c r))) (Ψ : C(closedBall c r, E →L[ℂ] E)) :
    MemLp (cauchySourceLp D Ψ) p volume :=
  (eLpNorm_cauchySourceLp_le (norm_nonneg Ψ) hD.aestronglyMeasurable
    Ψ.norm_coe_le_norm).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD.eLpNorm_lt_top)

/-- Real-valued `Lᵖ` bound for `cauchySourceLp D Ψ`. -/
private theorem toReal_eLpNorm_cauchySourceLp_le {p : ℝ≥0∞} {c : ℂ} {r B : ℝ} {D : ℂ → E →L[ℂ] E}
    (hB : 0 ≤ B) (hD : MemLp D p (volume.restrict (closedBall c r)))
    {Ψ : C(closedBall c r, E →L[ℂ] E)} (hΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    (eLpNorm (cauchySourceLp D Ψ) p volume).toReal ≤
      2⁻¹ * B * (eLpNorm D p (volume.restrict (closedBall c r))).toReal := by
  have hfin : ENNReal.ofReal (2⁻¹ * B) * eLpNorm D p (volume.restrict (closedBall c r)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2⁻¹ * B)] using
    ENNReal.toReal_mono hfin (eLpNorm_cauchySourceLp_le hB hD.aestronglyMeasurable hΨ)

/-- Sup-norm bound on `closedBall c r` for the Cauchy transform of `cauchySourceLp D Ψ`. -/
private theorem norm_cauchyTransform_cauchySourceLp_le {p q : ℝ≥0∞}
    [p.HolderConjugate q] (hq : q < 2) {c : ℂ} {r B : ℝ} (hB : 0 ≤ B) {D : ℂ → E →L[ℂ] E}
    (hD : MemLp D p (volume.restrict (closedBall c r))) {Ψ : C(closedBall c r, E →L[ℂ] E)}
    (hΨ : ∀ x, ‖Ψ x‖ ≤ B) {w : ℂ} (hw : w ∈ closedBall c r) :
    ‖cauchyTransform (cauchySourceLp D Ψ) w‖ ≤
      (2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
        (eLpNorm D p (volume.restrict (closedBall c r))).toReal) * B := by
  refine (norm_cauchyTransform_le (p := p) (q := q) hq (memLp_cauchySourceLp hD Ψ)
    (support_cauchySourceLp_subset D Ψ) hw).trans ?_
  calc Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
        (eLpNorm (cauchySourceLp D Ψ) p volume).toReal
      ≤ Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
          (2⁻¹ * B * (eLpNorm D p (volume.restrict (closedBall c r))).toReal) := by
        gcongr
        exact toReal_eLpNorm_cauchySourceLp_le hB hD hΨ
    _ = (2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
          (eLpNorm D p (volume.restrict (closedBall c r))).toReal) * B := by ring

/-- **The supercritical Cauchy integral equation.** Let `q < 2` be Hölder conjugate to `p`
(`2 < p ≤ ∞`) and let `D` be an `Lᵖ` field of complex-linear endomorphisms of a finite-dimensional
space `E` on `closedBall c r`. If
`2⁻¹ * π⁻¹ * ‖truncatedCauchyKernel (r + r)‖_{L^q} * ‖D‖_{Lᵖ(closedBall c r)} ≤ 1 / 4`, then
there is `g : ℂ → E →L[ℂ] E` in `Lᵖ`, supported in `closedBall c r`, whose Cauchy transform is
continuous on `ℂ` and satisfies `g = ½ (1 + T g) D` and `‖T g‖ < 1` on `closedBall c r`. -/
theorem exists_cauchyTransform_eq_of_memLp [FiniteDimensional ℂ E] {p q : ℝ≥0∞}
    [p.HolderConjugate q] (hq : q < 2) {D : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hD : MemLp D p (volume.restrict (closedBall c r)))
    (hsmall : 2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
      (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤ 4⁻¹) :
    ∃ g : ℂ → E →L[ℂ] E, support g ⊆ closedBall c r ∧ MemLp g p volume ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  have := FiniteDimensional.completeSpace ℂ E
  set K := 2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
    (eLpNorm D p (volume.restrict (closedBall c r))).toReal
  have hK0 : 0 ≤ K := by positivity
  have hsupp := support_cauchySourceLp_subset (c := c) (r := r) D
  have hLp := memLp_cauchySourceLp hD
  have hcont (Ψ : C(closedBall c r, E →L[ℂ] E)) :
      Continuous (cauchyTransform (cauchySourceLp D Ψ)) :=
    continuous_cauchyTransform_of_memLp (p := p) (q := q) hq (hLp Ψ) (hsupp Ψ)
  have hT (Ψ : C(closedBall c r, E →L[ℂ] E)) {B : ℝ} (hB : 0 ≤ B) (hΨ : ∀ x, ‖Ψ x‖ ≤ B) (w : ℂ)
      (hw : w ∈ closedBall c r) : ‖cauchyTransform (cauchySourceLp D Ψ) w‖ ≤ K * B :=
    norm_cauchyTransform_cauchySourceLp_le hq hB hD hΨ hw
  let op (Ψ : C(closedBall c r, E →L[ℂ] E)) : C(closedBall c r, E →L[ℂ] E) :=
    ⟨fun w ↦ 1 + cauchyTransform (cauchySourceLp D Ψ) w,
      (continuous_const.add (hcont Ψ)).comp continuous_subtype_val⟩
  have hop : ContractingWith K.toNNReal op := by
    refine ⟨by rw [Real.toNNReal_lt_one]; linarith, LipschitzWith.of_dist_le_mul fun Ψ Ψ' ↦ ?_⟩
    rw [Real.coe_toNNReal _ hK0]
    refine (ContinuousMap.dist_le (by positivity)).2 fun w ↦ ?_
    simp only [op, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub,
      ← Pi.sub_apply (cauchyTransform _) (cauchyTransform _),
      ← cauchyTransform_sub_of_memLp hq (hLp Ψ) (hsupp Ψ) (hLp Ψ') (hsupp Ψ'),
      ← cauchySourceLp_sub]
    refine hT _ dist_nonneg (fun x ↦ ?_) w w.2
    rw [ContinuousMap.sub_apply, ← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist x
  set Ψ₀ := ContractingWith.fixedPoint op hop
  set g := cauchySourceLp D Ψ₀ with hg
  have hΨ₀ (z : ℂ) (hz : z ∈ closedBall c r) : Ψ₀ ⟨z, hz⟩ = 1 + cauchyTransform g z := by
    simpa only [op, ContinuousMap.coe_mk, hg] using
      congrFun (congrArg DFunLike.coe (ContractingWith.fixedPoint_isFixedPt hop).symm) ⟨z, hz⟩
  have hnorm : ‖Ψ₀‖ ≤ 4 / 3 := by
    have h1 : ‖Ψ₀‖ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
      rw [hΨ₀ w w.2]
      exact (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le
        ((hT _ (norm_nonneg Ψ₀) Ψ₀.norm_coe_le_norm w w.2).trans (by gcongr)))
    linarith
  refine ⟨g, hsupp Ψ₀, hLp Ψ₀, hcont Ψ₀, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hg, cauchySourceLp_of_mem D Ψ₀ hz, hΨ₀ z hz]
  · exact (hT _ (norm_nonneg Ψ₀) Ψ₀.norm_coe_le_norm z hz).trans_lt
      ((mul_le_mul hsmall hnorm (norm_nonneg Ψ₀) (by positivity)).trans_lt (by norm_num))

end CauchyEquation

/-! ### The constant complex structure `i` -/

section ConstantStructure

/-- For `2 < p`, the Hölder conjugate exponent `q = p.conjExponent` is positive and strictly less
than `2`. -/
private theorem conjExponent_ne_zero_and_lt_two {p : ℝ≥0∞} (hp : 2 < p) :
    p.conjExponent ≠ 0 ∧ p.conjExponent < 2 := by
  rw [ENNReal.conjExponent]
  refine ⟨by simp, ?_⟩
  rcases eq_or_ne p ⊤ with rfl | hpt
  · norm_num
  · lift p to ℝ≥0 using hpt
    have hp' : 2 < p := mod_cast hp
    have hp1 : (1 : ℝ≥0∞) < (p : ℝ≥0∞) - 1 := by
      rw [← ENNReal.coe_one, ← ENNReal.coe_sub]
      exact_mod_cast lt_tsub_iff_right.2 (by simpa only [one_add_one_eq_two] using hp')
    simpa only [one_add_one_eq_two] using
      ENNReal.add_lt_add_left ENNReal.one_ne_top (ENNReal.inv_lt_one.2 hp1)

/-- Choosing a small closed disc inside `Ω` on which the supercritical Cauchy-equation contraction
bound holds for the rank-one absorption of `C`. -/
private theorem exists_closedBall_cauchy_small {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {p : ℝ≥0∞} (hp : 2 < p) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {C : ℂ → E →L[ℝ] E} (hC : MemLpLoc p Ω C) {ξ : ℂ → E} (hξc : ContinuousOn ξ Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, closedBall z₀ r ⊆ Ω ∧
      MemLp (fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)) p
        (volume.restrict (closedBall z₀ r)) ∧
      2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) p.conjExponent volume).toReal *
        (eLpNorm (fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)) p
          (volume.restrict (closedBall z₀ r))).toReal ≤ 4⁻¹ := by
  obtain ⟨hq0, hq2⟩ := conjExponent_ne_zero_and_lt_two hp
  obtain ⟨R, hR, hRΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz₀)
  have hCR : MemLp C p (volume.restrict (closedBall z₀ R)) :=
    memLpLoc_iff.1 hC _ hRΩ (isCompact_closedBall z₀ R)
  have htend : Tendsto (fun r : ℝ ↦ 2⁻¹ * Real.pi⁻¹ *
      (eLpNorm (truncatedCauchyKernel (r + r)) p.conjExponent volume).toReal *
        (eLpNorm C p (volume.restrict (closedBall z₀ R))).toReal) (𝓝 0) (𝓝 0) := by
    have hadd : Tendsto (fun r : ℝ ↦ r + r) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).add tendsto_id
    have hker := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      ((tendsto_eLpNorm_truncatedCauchyKernel_nhds_zero hq0 hq2).comp hadd)
    simpa using (hker.const_mul (2⁻¹ * Real.pi⁻¹)).mul_const
      (eLpNorm C p (volume.restrict (closedBall z₀ R))).toReal
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.tendsto_nhds_nhds.1 htend (4⁻¹ : ℝ) (by positivity)
  set r := min R (δ / 2)
  have hr : 0 < r := lt_min hR (half_pos hδ)
  have hrR : closedBall z₀ r ⊆ closedBall z₀ R := closedBall_subset_closedBall (min_le_left _ _)
  have hrΩ : closedBall z₀ r ⊆ Ω := hrR.trans hRΩ
  have hξm : AEStronglyMeasurable ξ (volume.restrict (closedBall z₀ r)) :=
    (hξc.mono hrΩ).aestronglyMeasurable measurableSet_closedBall
  have hCr : MemLp C p (volume.restrict (closedBall z₀ r)) :=
    hCR.mono_measure (Measure.restrict_mono hrR le_rfl)
  have hD : MemLp (fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)) p
      (volume.restrict (closedBall z₀ r)) := hCr.rankOneDivNormSq_apply hξm
  refine ⟨r, hr, hrΩ, hD, ?_⟩
  have hle : (eLpNorm (fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)) p
      (volume.restrict (closedBall z₀ r))).toReal ≤
        (eLpNorm C p (volume.restrict (closedBall z₀ R))).toReal :=
    ENNReal.toReal_mono hCR.eLpNorm_ne_top
      ((TauCeti.MeasureTheory.eLpNorm_rankOneDivNormSq_apply_le hCr.aestronglyMeasurable hξm
        p).trans (eLpNorm_mono_measure C (Measure.restrict_mono hrR le_rfl)))
  have hrδ : dist r 0 < δ := by
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg hr.le]
    exact (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hval := hδsmall hrδ
  rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (by positivity)] at hval
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hval.le

/-- Weak holomorphy of `σ = Ψ ξ` on `ball z₀ r` when `Ψ = 1 + T g` solves the Cauchy integral
equation on `closedBall z₀ r` and `ξ` solves `bar∂ξ = -½ C ξ` weakly. -/
private theorem differentiableOn_apply_of_cauchyTransform_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {p : ℝ≥0} (hp : 2 < p) {z₀ : ℂ} {r : ℝ}
    {C : ℂ → E →L[ℝ] E} {D g : ℂ → E →L[ℂ] E} {ξ : ℂ → E}
    (hTg : Continuous (cauchyTransform g))
    (hgbar : HasWeakConjWirtingerDerivOn volume ⊤ (cauchyTransform g) g)
    (hΨw : MemWkpLoc p (ball z₀ r) 1 (fun z ↦ 1 + cauchyTransform g z))
    (hgeq : ∀ z ∈ closedBall z₀ r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z))
    (hDC : ∀ z, D z (ξ z) = C z (ξ z))
    (hξc : ContinuousOn ξ (ball z₀ r)) (hξw : MemWkpLoc p (ball z₀ r) 1 ξ)
    (hξ : HasWeakConjWirtingerDerivOn volume ⟨ball z₀ r, isOpen_ball⟩ ξ
      (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))) :
    DifferentiableOn ℂ (fun z ↦ (1 + cauchyTransform g z) (ξ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  have hp1 : 1 < p := one_lt_two.trans hp
  let U : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z
  have hΨc : Continuous Ψ := continuous_const.add hTg
  have hΨwU : MemWkpLoc p U 1 Ψ := hΨw
  have hξwU : MemWkpLoc p U 1 ξ := hξw
  obtain ⟨DΨ, hDΨ, hDΨp⟩ := hΨwU.exists_weakFDeriv_of_isOpen
  obtain ⟨Dξ, hDξ, hDξp⟩ := hξwU.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDΨp hDξp
  let B : (E →L[ℂ] E) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℂ).restrictScalars ℝ
  have hleib := hDΨ.bilin_of_memLpLoc B hp hp1 le_rfl hΨc.continuousOn.memLpLoc hDΨp
    hDξ hξc.memLpLoc hDξp
  have hΨbar : HasWeakConjWirtingerDerivOn volume U Ψ g := by
    simpa only [Ψ, Pi.add_def, zero_add] using
      ((differentiableOn_const (1 : E →L[ℂ] E)).hasWeakConjWirtingerDerivOn_zero).add
        (hgbar.mono (subset_univ _))
  have h0 : HasWeakConjWirtingerDerivOn volume U (fun z ↦ Ψ z (ξ z)) 0 := by
    refine hleib.hasWeakConjWirtingerDerivOn.congr_ae_deriv ?_
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      hDΨ.hasWeakConjWirtingerDerivOn.ae_eq hΨbar,
      hDξ.hasWeakConjWirtingerDerivOn.ae_eq hξ] with z hz hzΨ hzξ
    have halg : (2 : ℂ)⁻¹ • ((DΨ z 1 (ξ z) + Ψ z (Dξ z 1)) +
        I • (DΨ z I (ξ z) + Ψ z (Dξ z I))) =
        ((2 : ℂ)⁻¹ • (DΨ z 1 + I • DΨ z I)) (ξ z) +
          Ψ z ((2 : ℂ)⁻¹ • (Dξ z 1 + I • Dξ z I)) := by
      simp only [add_apply, smul_apply, map_add, map_smul, smul_add]
      abel_nf
    change (2 : ℂ)⁻¹ • ((DΨ z 1 (ξ z) + Ψ z (Dξ z 1)) +
      I • (DΨ z I (ξ z) + Ψ z (Dξ z I))) = 0
    rw [halg, hzΨ, hzξ, hgeq z (ball_subset_closedBall hz)]
    change (2 : ℂ)⁻¹ • Ψ z (D z (ξ z)) + Ψ z (-(2 : ℂ)⁻¹ • C z (ξ z)) = 0
    rw [hDC z, map_smul, neg_smul, add_neg_cancel]
  exact h0.differentiableOn (hΨc.continuousOn.clm_apply hξc)

/-- The constant-`i` similarity principle on a finite-dimensional complex inner product space. -/
private theorem exists_similarity_of_hasWeakConjWirtingerDerivOn_of_innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {C : ℂ → E →L[ℝ] E} (hC : MemLpLoc p Ω C) {ξ : ℂ → E} (hξc : ContinuousOn ξ Ω)
    (hξ : HasWeakConjWirtingerDerivOn volume ⟨Ω, hΩ⟩ ξ (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)))
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, closedBall z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (closedBall z₀ r) ∧ MemWkpLoc p (closedBall z₀ r) 1 Φ ∧
      (∀ z ∈ closedBall z₀ r, IsUnit (Φ z)) ∧ ContinuousOn σ (closedBall z₀ r) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (closedBall z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  lift p to ℝ≥0 using hp_top
  have hp' : 2 < p := by exact_mod_cast hp
  have hp1' : (1 : ℝ≥0∞) < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨hp1'.le⟩
  obtain ⟨_, hq2⟩ := conjExponent_ne_zero_and_lt_two hp
  obtain ⟨r, hr, hrΩ, hD, hsmall⟩ := exists_closedBall_cauchy_small hp hΩ hC hξc hz₀
  obtain ⟨g, hgs, hgp, hTg, hgeq, hTg1⟩ := exists_cauchyTransform_eq_of_memLp hq2 hD hsmall
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z with hΨ
  have hΨc : Continuous Ψ := continuous_const.add hTg
  have hgbar : HasWeakConjWirtingerDerivOn volume ⊤ (cauchyTransform g) g :=
    hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp (r := ⟨r, hr.le⟩) hp1'.le
      (hgp.mono_measure Measure.restrict_le_self) hgs ⊤
  have hΨw : MemWkpLoc p (closedBall z₀ r) 1 Ψ :=
    ((memWkpLoc_const (1 : E →L[ℂ] E)).add
      (hgbar.memWkpLoc_one hp1' ENNReal.coe_ne_top hTg.continuousOn.memLpLoc
        (memLpLoc_iff.2 fun _ _ _ ↦ hgp.mono_measure Measure.restrict_le_self))).mono
      (subset_univ _)
  have hunit (z : ℂ) (hz : z ∈ closedBall z₀ r) : IsUnit (Ψ z) := by
    by_contra h
    refine nonunits.subset_compl_ball h ?_
    rw [mem_ball_iff_norm, hΨ, add_sub_cancel_left]
    exact hTg1 z hz
  have hs (x : E) : -(2 : ℂ)⁻¹ • x = (-(2 : ℝ)⁻¹) • x := by
    rw [← Complex.coe_smul]
    norm_num
  have hf : MemLpLoc p Ω (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) := by
    simp only [hs]
    exact (hC.clm_apply_continuousOn hξc).const_smul (-(2 : ℝ)⁻¹)
  have hξw : MemWkpLoc p (⟨Ω, hΩ⟩ : Opens ℂ) 1 ξ :=
    hξ.memWkpLoc_one hp1' ENNReal.coe_ne_top hξc.memLpLoc hf
  have hballΩ : ball z₀ r ⊆ Ω := ball_subset_closedBall.trans hrΩ
  refine ⟨r, hr, hrΩ, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z),
    fun z hz ↦ ?_, hΨw.ring_inverse hΨc.continuousOn hunit, fun z hz ↦ ?_,
    hΨc.continuousOn.clm_apply (hξc.mono hrΩ),
    differentiableOn_apply_of_cauchyTransform_eq hp' hTg hgbar (hΨw.mono ball_subset_closedBall)
      hgeq (fun z ↦ (C z).rankOneDivNormSq_apply_map (ξ z)) (hξc.mono hballΩ)
      (hξw.mono hballΩ) (hξ.mono hballΩ),
    fun z hz ↦ ?_⟩
  · have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp hΨc.continuousAt).continuousWithinAt
  · obtain ⟨u, hu⟩ := hunit z hz
    simpa only [← hu, Ring.inverse_unit] using u⁻¹.isUnit
  · simp only [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ (hunit z hz), one_apply_eq_self]

/-- **The Sobolev similarity principle for `bar∂ξ = -½ C ξ`.** Let `V` be a finite-dimensional
complex normed space, `Ω ⊆ ℂ` open, and `2 < p < ∞`. If `C ∈ Lᵖ_loc(Ω)` is a field of real-linear
endomorphisms and `ξ` is continuous on `Ω` and solves `bar∂ξ = -½ C ξ` weakly on `Ω`, then around
every `z₀ ∈ Ω` there is a closed disc `closedBall z₀ r ⊆ Ω` (`r > 0`) on which `ξ = Φ σ`, with
`Φ : ℂ → V →L[ℂ] V` continuous, invertible, and in `W^{1,p}_loc` on the closed disc, and `σ`
continuous on the closed disc and holomorphic on the open disc. No `W^{1,p}_loc` assumption on `ξ`
is needed: it follows from interior `bar∂` regularity. -/
theorem exists_similarity_of_hasWeakConjWirtingerDerivOn {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {C : ℂ → V →L[ℝ] V} (hC : MemLpLoc p Ω C) {ξ : ℂ → V}
    (hξc : ContinuousOn ξ Ω)
    (hξ : HasWeakConjWirtingerDerivOn volume ⟨Ω, hΩ⟩ ξ (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)))
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, closedBall z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (closedBall z₀ r) ∧ MemWkpLoc p (closedBall z₀ r) 1 Φ ∧
      (∀ z ∈ closedBall z₀ r, IsUnit (Φ z)) ∧ ContinuousOn σ (closedBall z₀ r) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (closedBall z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  let E := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let e : V ≃L[ℂ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eR : V →L[ℝ] E := (e : V →L[ℂ] E).restrictScalars ℝ
  let eR' : E →L[ℝ] V := (e.symm : E →L[ℂ] V).restrictScalars ℝ
  let conjL : (V →L[ℝ] V) →L[ℝ] (E →L[ℝ] E) :=
    (compL ℝ E V E eR).comp ((compL ℝ E V V).flip eR')
  have hC' : MemLpLoc p Ω (fun z ↦ conjL (C z)) := hC.clm_comp conjL
  have hξ' : HasWeakConjWirtingerDerivOn volume ⟨Ω, hΩ⟩ (fun z ↦ e (ξ z))
      (fun z ↦ -(2 : ℂ)⁻¹ • conjL (C z) (e (ξ z))) := by
    refine (hξ.clm_comp (e : V →L[ℂ] E)).congr_ae_deriv (Eventually.of_forall fun z ↦ ?_)
    simp [conjL, eR, eR']
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hΦu, hσc, hσ, hξσ⟩ :=
    exists_similarity_of_hasWeakConjWirtingerDerivOn_of_innerProductSpace hp hp_top hΩ hC'
      (e.continuous.comp_continuousOn hξc) hξ' hz₀
  let backL : (E →L[ℂ] E) →L[ℝ] (V →L[ℂ] V) :=
    ((compL ℂ V E V (e.symm : E →L[ℂ] V)).comp
      ((compL ℂ V E E).flip (e : V →L[ℂ] E))).restrictScalars ℝ
  have hback : (fun z ↦ e.symm.conjContinuousAlgEquiv (Φ z)) = fun z ↦ backL (Φ z) := by
    ext z v
    simp [backL, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  refine ⟨r, hr, hrΩ, fun z ↦ e.symm.conjContinuousAlgEquiv (Φ z), fun z ↦ e.symm (σ z),
    hback ▸ backL.continuous.comp_continuousOn hΦc, hback ▸ hΦw.clm_comp backL,
    fun z hz ↦ (hΦu z hz).map _, e.symm.continuous.comp_continuousOn hσc,
    ((e.symm : E →L[ℂ] V).differentiable.comp_differentiableOn hσ).congr fun _ _ ↦ rfl,
    fun z hz ↦ ?_⟩
  simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply] using congrArg e.symm (hξσ hz)

/-- **The Sobolev similarity principle for `∂ₛξ + i ∂ₜξ + C ξ = 0`.** The specialization of
`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn` to `TauCeti.IsWeakLinearCauchyRiemannOn`
with the constant complex structure `i`. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemann_I_smul_id {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω) {C : ℂ → V →L[ℝ] V}
    (hC : MemLpLoc p Ω C) {ξ : ℂ → V}
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, closedBall z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (closedBall z₀ r) ∧ MemWkpLoc p (closedBall z₀ r) 1 Φ ∧
      (∀ z ∈ closedBall z₀ r, IsUnit (Φ z)) ∧ ContinuousOn σ (closedBall z₀ r) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (closedBall z₀ r) := by
  have hξ' : IsWeakLinearCauchyRiemannOn p (⟨Ω, hΩ⟩ : Opens ℂ)
      (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ := hξ
  have hw := hξ'.hasWeakConjWirtingerDerivOn
  simp only [smul_neg, ← neg_smul] at hw
  exact exists_similarity_of_hasWeakConjWirtingerDerivOn hp hp_top hΩ hC hξ.continuousOn hw hz₀

end ConstantStructure

/-! ### The variable-structure vector similarity principle -/

section VariableStructure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **The vector similarity principle** (Carleman; McDuff–Salamon, Theorem 2.3.5). Let `V` be a
finite-dimensional complex normed space, `Ω ⊆ ℂ` open, and `2 < p < ∞`. Let `J : ℂ → V →L[ℝ] V`
be continuous and belong to `W^{1,p}_loc(Ω)` with `J(z)² = -1` on `Ω`, let `C : ℂ → V →L[ℝ] V`
belong to `Lᵖ_loc(Ω)`, and let `ξ : ℂ → V` solve `∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0` weakly on `Ω`.
Then around every point `z₀ ∈ Ω` there exist `r > 0` with `closedBall z₀ r ⊆ Ω`, a family
`Φ : ℂ → V →L[ℝ] V` continuous and in `W^{1,p}_loc` on `closedBall z₀ r`, invertible there and
satisfying `J(z) Φ(z) = Φ(z) i`, and a map `σ : ℂ → V` continuous on `closedBall z₀ r` and
holomorphic on `ball z₀ r`, such that `ξ z = Φ z (σ z)` on `closedBall z₀ r`. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemann {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {J C : ℂ → V →L[ℝ] V} (hJc : ContinuousOn J Ω)
    (hJw : MemWkpLoc p Ω 1 J) (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) {ξ : ℂ → V} (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, closedBall z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V),
      ContinuousOn Φ (closedBall z₀ r) ∧ MemWkpLoc p (closedBall z₀ r) 1 Φ ∧
      (∀ z ∈ closedBall z₀ r, IsUnit (Φ z)) ∧
      (∀ z ∈ closedBall z₀ r, J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      ContinuousOn σ (closedBall z₀ r) ∧ DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (closedBall z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  lift p to ℝ≥0 using hp_top
  have hp' : 2 < p := by exact_mod_cast hp
  have hp1 : 1 < p := one_lt_two.trans hp'
  obtain ⟨Φ₁, hΦ₁⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul (hJ z₀ hz₀)
  obtain ⟨R, hR, hRΩ, hRu⟩ := exists_ball_isUnit_standardFrame (Φ₁ := Φ₁) hΩ hz₀ hJc (hJ z₀ hz₀)
  let B : Opens ℂ := ⟨ball z₀ R, isOpen_ball⟩
  set Φ₀ := standardFrame J z₀ Φ₁
  have hΦ₀w : MemWkpLoc p B 1 Φ₀ := memWkpLoc_standardFrame (hJw.mono hRΩ)
  obtain ⟨DΦ₀, hDΦ₀, hDΦ₀p⟩ := hΦ₀w.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDΦ₀p
  have hη : IsWeakLinearCauchyRiemannOn p B (fun _ ↦ I • ContinuousLinearMap.id ℝ V)
      (frameCoeff J C Φ₀ DΦ₀) (fun z ↦ Ring.inverse (Φ₀ z) (ξ z)) :=
    (isWeakLinearCauchyRiemannOn_iff_standardFrame hp' (hJc.mono hRΩ) (fun z hz ↦ hJ z (hRΩ hz))
      (hJ z₀ hz₀) hΦ₁ hRu hDΦ₀ hDΦ₀p).1 (hξ.mono hRΩ)
  have hC' : MemLpLoc p B (frameCoeff J C Φ₀ DΦ₀) :=
    (memLpLoc_frameCoeff_iff isOpen_ball.measurableSet (continuousOn_standardFrame (hJc.mono hRΩ))
      hDΦ₀p hRu (hJc.mono hRΩ)).2 (hC.mono_set hRΩ)
  obtain ⟨r, hr, hrB, Ψ, σ, hΨc, hΨw, hΨu, hσc, hσ, hησ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemann_I_smul_id hp ENNReal.coe_ne_top isOpen_ball hC'
      hη (mem_ball_self hR)
  let R_L : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℂ).restrictScalars ℝ
  set Φ : ℂ → V →L[ℝ] V := fun z ↦ Φ₀ z ∘L R_L (Ψ z)
  have hsub : closedBall z₀ (r / 2) ⊆ ball z₀ r := closedBall_subset_ball (half_lt_self hr)
  have hsubc : closedBall z₀ (r / 2) ⊆ closedBall z₀ r := hsub.trans ball_subset_closedBall
  have hsubB : ball z₀ r ⊆ B := ball_subset_closedBall.trans hrB
  have hΦc : ContinuousOn Φ (closedBall z₀ (r / 2)) :=
    (continuousOn_standardFrame (hJc.mono (hsubc.trans (hrB.trans hRΩ)))).clm_comp
      (R_L.continuous.comp_continuousOn (hΨc.mono hsubc))
  have hΦw : MemWkpLoc p (closedBall z₀ (r / 2)) 1 Φ :=
    (((hΦ₀w.mono hsubB).bilin (Ω := ⟨ball z₀ r, isOpen_ball⟩) (compL ℝ V V V) hp' hp1 le_rfl
      ((hΨw.mono ball_subset_closedBall).clm_comp R_L)).mono hsub)
  refine ⟨r / 2, half_pos hr, hsubc.trans (hrB.trans hRΩ), Φ, σ, hΦc, hΦw, ?_, ?_,
    hσc.mono hsubc, hσ.mono (ball_subset_ball (half_lt_self hr).le), ?_⟩
  · intro z hz
    obtain ⟨u, hu⟩ := hΨu z (hsubc hz)
    exact (hRu z (hrB (hsubc hz))).mul
      (hu ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ V u).restrictScalars ℝ).toUnit, rfl⟩)
  · intro z hz
    ext v
    simpa [Φ, R_L] using
      congr($(comp_standardFrame (hJ z (hRΩ (hrB (hsubc hz)))) (hJ z₀ hz₀) hΦ₁) (Ψ z v))
  · intro z hz
    have hinv : Φ₀ z (Ring.inverse (Φ₀ z) (ξ z)) = ξ z := by
      simpa using congr($(Ring.mul_inverse_cancel _ (hRu z (hrB (hsubc hz)))) (ξ z))
    simpa [Φ, R_L, hinv] using congrArg (Φ₀ z) (hησ (hsubc hz))

end VariableStructure

/-! ### Unique continuation, isolated zeros, and positive orders -/

section UniqueContinuation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {p : ℝ≥0∞} {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- Every weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` (`2 < p < ∞`, `J ∈ W^{1,p}_loc` continuous
with `J² = -1`, `C ∈ Lᵖ_loc`) admits a `TauCeti.HasSimilarityFactorizationAt` at every point of
`Ω` (not only at its zeros). -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, hΦu, -, -, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJw hJ hC hξ hz₀
  exact .of_eqOn_ball hr (hΦc.mono ball_subset_closedBall)
    (hΦu z₀ (mem_closedBall_self hr.le)) hσ (hξσ.mono ball_subset_closedBall)

/-- **Unique continuation from a neighbourhood.** On a preconnected open set `Ω`, a weak solution
vanishing near one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemann_of_eventually_eq_zero (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, ξ z = 0) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJw hJ
      hC hξ hz) hz₀ h₀

/-- **Unique continuation from an open subset.** On a preconnected open set `Ω`, a weak solution
vanishing on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemann_of_eqOn_zero (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJw hJ
      hC hξ hz) hU hUne hUΩ h₀

/-- **Unique continuation from an infinite-order zero.** On a preconnected open set `Ω`, a weak
solution satisfying `ξ = O((z - z₀)ⁿ)` for all `n` at one point `z₀ ∈ Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemann_of_forall_isBigO (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJw hJ
      hC hξ hz) hz₀ h₀

/-- **Punctured-neighbourhood nonvanishing.** On a preconnected open set `Ω`, a weak solution not
identically zero on `Ω` is nonzero on a punctured neighbourhood of every point of `Ω`. -/
theorem eventually_ne_zero_of_isWeakLinearCauchyRiemann (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω) :
    ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eventually_ne_zero_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJw hJ
      hC hξ hz) hne hz₀

/-- **Isolated zeros.** On a preconnected open set `Ω`, the zeros of a weak solution not
identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemann (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω)
    (hJw : MemWkpLoc p Ω 1 J) (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJw hJ
      hC hξ hz) hne

/-- **Positive integer orders of zeros.** On a preconnected open set `Ω`, at every zero `z₀ ∈ Ω`
of a weak solution not identically zero on `Ω`, there is a positive integer `m` such that
`‖ξ z‖ ≍ ‖z - z₀‖ ^ m` near `z₀` and `analyticOrderAt σ z₀ = m` for every local similarity
factorization `ξ = Φ σ` at `z₀`. -/
theorem exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemann (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0)
    (hz₀ : z₀ ∈ Ω) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  have := FiniteDimensional.completeSpace ℂ V
  exact exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJw hJ
      hC hξ hz) hne hz₀ hξ₀

end UniqueContinuation

/-! ### Comparison with the scalar `Cᵏ` similarity principle and calibrating examples -/

section ComparisonAndExamples

/-- **Comparison with the scalar equation.** A `C¹` scalar solution `f : ℂ → ℂ` of `bar∂ f = a f`
on an open set `U` solves `IsWeakLinearCauchyRiemannOn p U (fun _ ↦ I • id) (fun w ↦ (-2 * a w) •
id) f` for every exponent `p`, and for `a` of class `Cᵏ` (`1 ≤ k`) the holomorphic factor
`exp (-g) * f` produced by the scalar integrating factor `g` has the same analytic order at any
point `z₀ ∈ U` as the holomorphic factor `σ` of any vector similarity factorization `f = Φ σ`. -/
theorem isWeakLinearCauchyRiemannOn_of_conjWirtingerDeriv_apply_one_eq_mul {p : ℝ≥0∞} {U : Set ℂ}
    (hU : IsOpen U) {a f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f U)
    (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w) :
    IsWeakLinearCauchyRiemannOn p U (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ)
      (fun w ↦ (-2 * a w) • ContinuousLinearMap.id ℝ ℂ) f := by
  refine isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨U, hU⟩) hf fun w hw ↦ ?_
  have hw' := heq w hw
  simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] at hw'
  simp only [smul_apply, id_apply, smul_eq_mul, neg_mul]
  linear_combination 2 * hw'

/-- At any point `z₀` where `f` has both a scalar integrating-factor representation `exp (-g) * f`
analytic at `z₀` and a vector similarity factorization `f = Φ σ`, the two holomorphic factors have
equal analytic order at `z₀`. -/
theorem analyticOrderAt_exp_neg_mul_eq_of_eventually_eq_clm_apply {g f : ℂ → ℂ} {z₀ : ℂ}
    (hg : ContinuousAt g z₀) (hσ₀ : AnalyticAt ℂ (fun w ↦ cexp (-g w) * f w) z₀)
    {Φ : ℂ → ℂ →L[ℝ] ℂ} {σ : ℂ → ℂ} (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀))
    (hσ : AnalyticAt ℂ σ z₀) (hfΦ : ∀ᶠ w in 𝓝 z₀, f w = Φ w (σ w)) :
    analyticOrderAt (fun w ↦ cexp (-g w) * f w) z₀ = analyticOrderAt σ z₀ :=
  analyticOrderAt_eq_of_eventually_eq_clm_apply (ξ := f)
    (Φ := fun w ↦ cexp (g w) • ContinuousLinearMap.id ℝ ℂ)
    ((Complex.continuous_exp.continuousAt.comp hg).smul continuousAt_const)
    (ContinuousLinearMap.isUnit_smul_id_of_ne_zero (exp_ne_zero _)) hσ₀
    (Eventually.of_forall fun w ↦ by simp [← mul_assoc, ← exp_add]) hΦ hΦ₀ hσ hfΦ

/-- **Check 1 (non-holomorphic `W^{1,p}` factor).** On every open set `Ω`, `z ↦ z * e^{-conj z}`
solves `∂ₛξ + i ∂ₜξ + 2 ξ = 0` weakly and factors globally as `Φ z (σ z)` with
`Φ z = e^{-conj z} • id` in `W^{1,p}_loc` and nowhere holomorphic, and `σ = id` of analytic order
`1` at `0`. -/
theorem isWeakLinearCauchyRiemannOn_mul_cexp_neg_conj {p : ℝ≥0∞} {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ)
      (fun _ ↦ (2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) (fun z : ℂ ↦ z * cexp (-conj z)) ∧
      MemWkpLoc p Ω 1 (fun z : ℂ ↦ cexp (-conj z) • ContinuousLinearMap.id ℂ ℂ) ∧
      (∀ z : ℂ, ¬ DifferentiableAt ℂ (fun w : ℂ ↦ cexp (-conj w)) z) ∧
      analyticOrderAt (id : ℂ → ℂ) 0 = 1 := by
  have hd : ContDiff ℝ 1 fun z : ℂ ↦ z * cexp (-conj z) := by
    simpa only [conjCLE_apply, id_eq] using contDiff_id.mul conjCLE.contDiff.neg.cexp
  refine ⟨isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨Ω, hΩ⟩) hd.contDiffOn fun z _ ↦ ?_,
    (memWkpLoc_cexp_neg_conj p Ω 1).clm_comp
      (((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)).flip
        (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ),
    not_differentiableAt_cexp_neg_conj,
    by simp⟩
  have h := fderiv_mul_cexp_neg_conj_add_eq_zero z
  simp only [smul_apply, id_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  linear_combination h

/-- **Check 2a (`exp (-1 / ‖z‖²)` away from `0`).** On `ℂ \ {0}`, the flat function
`TauCeti.expNegInvNormSq` solves `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly for the smooth coefficient
`C z = expNegInvNormSqCoeff z • id`. -/
theorem isWeakLinearCauchyRiemannOn_compl_singleton_zero_expNegInvNormSq {p : ℝ≥0∞} :
    IsWeakLinearCauchyRiemannOn p ({0}ᶜ : Set ℂ) (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ)
      (fun z ↦ expNegInvNormSqCoeff z • ContinuousLinearMap.id ℝ ℂ) expNegInvNormSq := by
  refine isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨{0}ᶜ, isOpen_compl_singleton⟩)
    (contDiff_expNegInvNormSq.of_le (by simp)).contDiffOn fun z _ ↦ ?_
  have h := two_mul_conjWirtingerDeriv_expNegInvNormSq_add_eq_zero z
  simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] at h
  simp only [smul_apply, id_apply, smul_eq_mul]
  linear_combination h

/-- **Check 2b (`MemLpLoc p Ω C` cannot be dropped).** For `2 < p < ∞` and any open set `Ω`
containing `0`, there is NO coefficient field `C ∈ Lᵖ_loc(Ω)` for which `TauCeti.expNegInvNormSq`
solves `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω`: unique continuation from its infinite-order zero at
`0` would force it to vanish on a disc about `0`. -/
theorem not_exists_memLpLoc_isWeakLinearCauchyRiemannOn_expNegInvNormSq {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω) (h0 : (0 : ℂ) ∈ Ω) :
    ¬ ∃ C : ℂ → ℂ →L[ℝ] ℂ, MemLpLoc p Ω C ∧
      IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ) C
        expNegInvNormSq := by
  rintro ⟨C, hC, hξ⟩
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ 0 h0
  have hzero : EqOn expNegInvNormSq 0 (ball 0 r) :=
    eqOn_zero_of_isWeakLinearCauchyRiemann_of_forall_isBigO hp hp_top isOpen_ball
      (convex_ball 0 r).isPreconnected continuousOn_const (memWkpLoc_const _)
      (fun _ _ ↦ by ext w; simp [smul_smul]) (hC.mono_set hrΩ) (hξ.mono hrΩ) (mem_ball_self hr)
      fun n ↦ by
        simpa only [sub_zero, ← norm_pow, isBigO_norm_right] using
          (expNegInvNormSq_isLittleO_pow n).isBigO
  have hmem : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos hr).le]
    exact half_lt_self hr
  exact expNegInvNormSq_ne_zero (Complex.ofReal_ne_zero.2 (half_pos hr).ne') (hzero hmem)

/-- **Check 3 (non-constant complex structure `J = Φ i Φ⁻¹`).** For any `C¹` family
`Φ : ℂ → V ≃L[ℝ] V` on an open set `Ω` with continuous inverse on `Ω` and any holomorphic
`σ : ℂ → V` on `Ω`, `z ↦ Φ z (σ z)` solves the weak linear equation on `Ω` for
`J = transportedComplexStructure Φ` and `C = transportedCoeff Φ ∈ Lᵖ_loc(Ω)`. -/
theorem isWeakLinearCauchyRiemannOn_transportedComplexStructure {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {p : ℝ≥0∞} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {Φ : ℂ → V ≃L[ℝ] V} (hΦ : ContDiffOn ℝ 1 (fun w ↦ (Φ w : V →L[ℝ] V)) Ω)
    (hΨ : ContinuousOn (fun w ↦ ((Φ w).symm : V →L[ℝ] V)) Ω) {σ : ℂ → V}
    (hσ : DifferentiableOn ℂ σ Ω) :
    MemLpLoc p Ω (transportedCoeff Φ) ∧
      IsWeakLinearCauchyRiemannOn p Ω (transportedComplexStructure Φ) (transportedCoeff Φ)
        (fun z ↦ Φ z (σ z)) := by
  refine ⟨memLpLoc_transportedCoeff hΩ hΦ hΨ p, ?_⟩
  have hξd : ContDiffOn ℝ 1 (fun z ↦ Φ z (σ z)) Ω :=
    hΦ.clm_apply ((hσ.contDiffOn hΩ).restrict_scalars ℝ)
  exact isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨Ω, hΩ⟩) hξd fun z hz ↦
    add_eq_zero_iff_eq_neg.1 (fderiv_apply_add_transportedComplexStructure_add_eq_zero
      ((hΦ.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz))
      (hσ.differentiableAt (hΩ.mem_nhds hz)))

/-- **Check 4 (preservation of arbitrary integer zero orders).** For any `v ≠ 0`, any `m : ℕ`,
and any family `Φ` continuous and invertible at `z₀`, the map `z ↦ Φ z ((z - z₀) ^ m • v)` has
holomorphic factor of analytic order `m` at `z₀`, satisfies
`‖Φ z ((z - z₀) ^ m • v)‖ ≍ ‖z - z₀‖ ^ m` near `z₀`, and is nonzero on a punctured neighbourhood
of `z₀`. -/
theorem isTheta_clm_apply_pow_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {v : V} (hv : v ≠ 0) {Φ : ℂ → V →L[ℝ] V} {z₀ : ℂ} (hΦ : ContinuousAt Φ z₀)
    (hΦ₀ : IsUnit (Φ z₀)) (m : ℕ) :
    analyticOrderAt (fun z : ℂ ↦ (z - z₀) ^ m • v) z₀ = m ∧
      ((fun z ↦ Φ z ((z - z₀) ^ m • v)) =Θ[𝓝 z₀] fun z : ℂ ↦ (z - z₀) ^ m) ∧
      ∀ᶠ z in 𝓝[≠] z₀, Φ z ((z - z₀) ^ m • v) ≠ 0 := by
  have hσ : AnalyticAt ℂ (fun z : ℂ ↦ (z - z₀) ^ m • v) z₀ := by fun_prop
  have hord : analyticOrderAt (fun z : ℂ ↦ (z - z₀) ^ m • v) z₀ = m := by
    exact_mod_cast (hσ.analyticOrderAt_eq_natCast (n := m)).2
      ⟨fun _ ↦ v, analyticAt_const, hv, by simp⟩
  refine ⟨hord,
    (analyticOrderAt_eq_natCast_iff_isTheta_of_eventually_eq_clm_apply
      (ξ := fun z ↦ Φ z ((z - z₀) ^ m • v)) hΦ hΦ₀ hσ (Eventually.of_forall fun _ ↦ rfl)).1 hord,
    ?_⟩
  have hfac : HasSimilarityFactorizationAt (fun z ↦ Φ z ((z - z₀) ^ m • v)) z₀ :=
    hasSimilarityFactorizationAt_iff.2 ⟨Φ, _, hΦ, hΦ₀, hσ, Eventually.of_forall fun _ ↦ rfl⟩
  refine hfac.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h ↦ ?_
  have htop := (analyticOrderAt_eq_top_iff_of_eventually_eq_clm_apply hΦ hΦ₀
    (Eventually.of_forall fun _ ↦ rfl)).2 h
  rw [hord] at htop
  exact ENat.natCast_ne_top m htop

end ComparisonAndExamples

end TauCeti
