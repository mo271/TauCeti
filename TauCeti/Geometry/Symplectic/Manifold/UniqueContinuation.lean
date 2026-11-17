/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Unique continuation and isolatedness for pseudoholomorphic curves on manifolds

Let `S` be a Riemann surface (`[ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]`), let `X` be a smooth
boundaryless manifold modelled on a finite-dimensional real normed space `E`, and let
`J : ContMDiffAlmostComplexStructure I n X` be a `C^n` almost complex structure on `X` (`1 ≤ n`).
A map `u : S → X` satisfies the nonlinear Cauchy–Riemann equation when

`mfderiv 𝓘(ℝ, ℂ) I u z I = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z 1)`

for all `z : S`.

This file lifts the planar local unique continuation and critical-point isolatedness results of
`TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation` (McDuff–Salamon, Section 2.4,
Lemma 2.4.1) from open subsets of `ℂ` to Riemann surfaces and almost complex manifolds, working
directly in a complex chart of `S` and an extended chart of `X`:

* **Pointwise complex-linear algebra** (no finite-dimensionality, boundarylessness, or separation
  hypotheses):
  * `TauCeti.Pseudoholomorphic.mfderiv_apply_I_mul_eq_of_apply_I`
  * `TauCeti.Pseudoholomorphic.mfderiv_eq_zero_iff_apply_one_eq_zero`
  * `TauCeti.Pseudoholomorphic.injective_mfderiv_iff_ne_zero`
* **Chart-transfer bridges** (reused by local factorization on manifolds):
  * `TauCeti.Pseudoholomorphic.fderiv_extChartAt_comp_chartAt_symm_add_inChart_eq_zero`
  * `TauCeti.Pseudoholomorphic.fderiv_extChartAt_comp_chartAt_symm_eq_zero_iff_mfderiv_eq_zero`
* **Two `C¹` pseudoholomorphic curves**:
  * `TauCeti.Pseudoholomorphic.eventually_eq_or_eventually_ne_of_eq`: local dichotomy at a
    coincidence point (no separation or connectedness assumptions).
  * `TauCeti.Pseudoholomorphic.eq_of_eqOn` and `TauCeti.Pseudoholomorphic.eq_of_eventuallyEq`:
    agreement on a nonempty open set implies global equality on a preconnected Riemann surface
    (requiring `[T2Space X]`).
  * `TauCeti.Pseudoholomorphic.setOf_ne_mem_codiscrete` and
    `TauCeti.Pseudoholomorphic.finite_setOf_eq`: distinct curves have discrete coincidences, and
    finitely many on a compact Riemann surface.
* **Fibres of a `C¹` pseudoholomorphic curve** (only `[T1Space X]` needed):
  * `TauCeti.Pseudoholomorphic.eq_const_of_eventuallyEq_const`
  * `TauCeti.Pseudoholomorphic.setOf_ne_const_mem_codiscrete`
  * `TauCeti.Pseudoholomorphic.finite_preimage_singleton`
* **Critical points of a `C²` pseudoholomorphic curve** (no separation assumption on `X` needed
  for the critical set itself):
  * `TauCeti.Pseudoholomorphic.eventually_mfderiv_eq_zero_or_eventually_ne_zero`
  * `TauCeti.Pseudoholomorphic.mfderiv_eq_zero_of_eventually_mfderiv_eq_zero`
  * `TauCeti.Pseudoholomorphic.apply_eq_of_eventually_mfderiv_eq_zero` and
    `TauCeti.Pseudoholomorphic.apply_eq_of_mfderiv_eqOn_zero`
  * `TauCeti.Pseudoholomorphic.setOf_mfderiv_ne_zero_mem_codiscrete` and
    `TauCeti.Pseudoholomorphic.setOf_injective_mfderiv_mem_codiscrete`
  * `TauCeti.Pseudoholomorphic.finite_setOf_mfderiv_eq_zero`
  * `TauCeti.Pseudoholomorphic.finite_preimage_image_setOf_mfderiv_eq_zero`: on a compact
    preconnected Riemann surface into a `T₁` target, the preimage `u⁻¹(u(Crit u))` of the critical
    values is finite.
* **Dot-notation wrappers for `IsPseudoholomorphicAt` and `IsPseudoholomorphic`** on smooth
  almost complex manifolds (`SmoothAlmostComplexStructure`), specialising via `J.toContMDiff ⊤`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4 (Lemma 2.4.1).
* C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*, Section 2.5.
-/

public noncomputable section

open Filter Function Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.Pseudoholomorphic

section Algebra

variable {E H X S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S] [ChartedSpace ℂ S] {n : ℕ∞}

/-- If `mfderiv 𝓘(ℝ, ℂ) I u z` satisfies the Cauchy–Riemann equation at `1`, it intertwines
multiplication by `I` with `J (u z)` on all of `ℂ`. -/
theorem mfderiv_apply_I_mul_eq_of_apply_I (J : ContMDiffAlmostComplexStructure I n X)
    {u : S → X} {z : S}
    (hCR : mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (w : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I * w) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z w) := by
  have hsq : ∀ v, (J.toEndomorphism (u z)).toLinearMap ((J.toEndomorphism (u z)).toLinearMap v) =
      -v := fun v ↦ J.apply_apply (u z) v
  have hadd : (mfderiv 𝓘(ℝ, ℂ) I u z).toLinearMap (1 : ℂ) +
      (J.toEndomorphism (u z)).toLinearMap ((mfderiv 𝓘(ℝ, ℂ) I u z).toLinearMap Complex.I) = 0 :=
    ((mfderiv 𝓘(ℝ, ℂ) I u z).toLinearMap.add_apply_I_eq_zero_iff_apply_I_eq hsq).2 hCR
  exact (LinearMap.forall_apply_I_mul_eq_iff (mfderiv 𝓘(ℝ, ℂ) I u z).toLinearMap
    (A := (J.toEndomorphism (u z)).toLinearMap) hsq).2 hadd w

/-- A complex-linear manifold differential out of a Riemann surface vanishes iff it vanishes at
`1`. -/
theorem mfderiv_eq_zero_iff_apply_one_eq_zero (J : ContMDiffAlmostComplexStructure I n X)
    {u : S → X} {z : S}
    (hCR : mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ))) :
    mfderiv 𝓘(ℝ, ℂ) I u z = 0 ↔ mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ) = 0 := by
  let L : ℂ →L[ℝ] TangentSpace I (u z) := mfderiv 𝓘(ℝ, ℂ) I u z
  have h := L.toLinearMap.eq_zero_iff_apply_one_eq_zero_of_apply_I_mul_eq
    (A := (J.toEndomorphism (u z)).toLinearMap) (mfderiv_apply_I_mul_eq_of_apply_I J hCR)
  refine ⟨fun h0 ↦ by rw [h0]; rfl, fun h1 ↦ ContinuousLinearMap.ext fun (w : ℂ) ↦ ?_⟩
  have h0 : L.toLinearMap = 0 := h.2 h1
  exact (congrArg (fun M : ℂ →ₗ[ℝ] TangentSpace I (u z) ↦ M w) h0).trans (LinearMap.zero_apply w)

/-- A complex-linear manifold differential out of a Riemann surface is injective iff it is
nonzero. -/
theorem injective_mfderiv_iff_ne_zero (J : ContMDiffAlmostComplexStructure I n X)
    {u : S → X} {z : S}
    (hCR : mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ))) :
    Injective (mfderiv 𝓘(ℝ, ℂ) I u z) ↔ mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0 := by
  let L : ℂ →L[ℝ] TangentSpace I (u z) := mfderiv 𝓘(ℝ, ℂ) I u z
  have hsq : ∀ v, (J.toEndomorphism (u z)).toLinearMap ((J.toEndomorphism (u z)).toLinearMap v) =
      -v := fun v ↦ J.apply_apply (u z) v
  have h := L.toLinearMap.injective_iff_ne_zero_of_apply_I_mul_eq hsq
    (mfderiv_apply_I_mul_eq_of_apply_I J hCR)
  refine h.trans ⟨fun hne h0 ↦ hne (by change L = 0 at h0; rw [h0]; rfl), fun hne h0 ↦ hne ?_⟩
  exact ContinuousLinearMap.ext fun (w : ℂ) ↦
    (congrArg (fun M : ℂ →ₗ[ℝ] TangentSpace I (u z) ↦ M w) h0).trans (LinearMap.zero_apply w)

end Algebra

section ChartHelpers

variable {E H X S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S] {n : ℕ∞}

/-- At the image of `y` in the extended chart at `x`, a finite-regularity structure read in the
chart equals `J y` conjugated by the chart derivatives. -/
private theorem inChart_extChartAt_apply_eq_mfderiv (J : ContMDiffAlmostComplexStructure I n X)
    (x : X) {y : X} (hy : y ∈ (extChartAt I x).source) (w : E) :
    J.inChart x (extChartAt I x y) w =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) y
        (J y (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
          (extChartAt I x y) w)) := by
  have hy' : y ∈ (chartAt H x).source := by rwa [← extChartAt_source I]
  rw [J.inChart_def, (extChartAt I x).left_inv hy, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt hy',
    TangentBundle.symmL_trivializationAt hy']
  rfl

/-- Chart-transfer of a pointwise derivative intertwining relation for a finite-regularity almost
complex structure `J`. -/
private theorem fderiv_extChartAt_comp_apply_eq_inChart (J : ContMDiffAlmostComplexStructure I n X)
    (x : X) {g : ℂ → X} {w : ℂ} (hg : ContinuousAt g w) (hw : g w ∈ (extChartAt I x).source)
    {a b : ℂ} (h : mfderiv 𝓘(ℝ, ℂ) I g w a = J (g w) (mfderiv 𝓘(ℝ, ℂ) I g w b)) :
    fderiv ℝ (extChartAt I x ∘ g) w a =
      J.inChart x ((extChartAt I x ∘ g) w) (fderiv ℝ (extChartAt I x ∘ g) w b) := by
  have hinv := congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hw)
    (mfderiv 𝓘(ℝ, ℂ) I g w b))
  rw [hg.fderiv_extChartAt_comp_apply hw, hg.fderiv_extChartAt_comp_apply hw,
    Function.comp_apply, h]
  exact (congrArg _ (congrArg _ hinv)).symm.trans
    (inChart_extChartAt_apply_eq_mfderiv J x hw _).symm

/-- Reading a pseudoholomorphic curve `u : S → X` in the chart `chartAt ℂ z₀` on `S` and
`extChartAt I x` on `X` yields a planar curve `v` solving the coordinate Cauchy–Riemann equation
`∂ₛv + J_x(v) ∂ₜv = 0`. -/
theorem fderiv_extChartAt_comp_chartAt_symm_add_inChart_eq_zero
    (J : ContMDiffAlmostComplexStructure I n X)
    {u : S → X} (hu : MDifferentiable 𝓘(ℝ, ℂ) I u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (z₀ : S) (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ z₀).target)
    (hux : u ((chartAt ℂ z₀).symm w) ∈ (extChartAt I x).source) :
    fderiv ℝ (extChartAt I x ∘ u ∘ (chartAt ℂ z₀).symm) w 1 +
      J.inChart x ((extChartAt I x ∘ u ∘ (chartAt ℂ z₀).symm) w)
        (fderiv ℝ (extChartAt I x ∘ u ∘ (chartAt ℂ z₀).symm) w Complex.I) = 0 := by
  let c := chartAt ℂ z₀
  let y : S := c.symm w
  have hw_ext : w ∈ (extChartAt 𝓘(ℝ, ℂ) z₀).target := by
    simpa [extChartAt_target] using hw
  have hcs_mdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm w :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := z₀) w hw).mdifferentiableWithinAt
      (by simp) |>.mdifferentiableAt ((chartAt ℂ z₀).open_target.mem_nhds hw)
  let v1 : ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm w (1 : ℂ)
  let vI : ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm w Complex.I
  have hcs_smul : vI = Complex.I * v1 := by
    have hsm := TauCeti.mfderivWithin_extChartAt_symm_smul (𝕜 := ℝ) (𝕜' := ℂ) (E := ℂ)
      (x := z₀) hw_ext Complex.I (1 : ℂ)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] at hsm
    exact hsm
  have hg_cont : ContinuousAt (u ∘ c.symm) w :=
    (hu y).continuousAt.comp hcs_mdiff.continuousAt
  have hcomp_I : mfderiv 𝓘(ℝ, ℂ) I (u ∘ c.symm) w (Complex.I : TangentSpace 𝓘(ℝ, ℂ) w) =
      mfderiv 𝓘(ℝ, ℂ) I u y vI :=
    mfderiv_comp_apply w (hu y) hcs_mdiff (Complex.I : TangentSpace 𝓘(ℝ, ℂ) w)
  have hcomp_1 : mfderiv 𝓘(ℝ, ℂ) I (u ∘ c.symm) w ((1 : ℂ) : TangentSpace 𝓘(ℝ, ℂ) w) =
      mfderiv 𝓘(ℝ, ℂ) I u y v1 :=
    mfderiv_comp_apply w (hu y) hcs_mdiff ((1 : ℂ) : TangentSpace 𝓘(ℝ, ℂ) w)
  have hg_cr : mfderiv 𝓘(ℝ, ℂ) I (u ∘ c.symm) w (Complex.I : ℂ) =
      J (u y) (mfderiv 𝓘(ℝ, ℂ) I (u ∘ c.symm) w (1 : ℂ)) := by
    calc mfderiv 𝓘(ℝ, ℂ) I (u ∘ c.symm) w (Complex.I : ℂ)
        = mfderiv 𝓘(ℝ, ℂ) I u y vI := hcomp_I
      _ = mfderiv 𝓘(ℝ, ℂ) I u y (Complex.I * v1) := congrArg _ hcs_smul
      _ = J (u y) (mfderiv 𝓘(ℝ, ℂ) I u y v1) :=
          mfderiv_apply_I_mul_eq_of_apply_I J (hCR y) v1
      _ = J (u y) (mfderiv 𝓘(ℝ, ℂ) I (u ∘ c.symm) w (1 : ℂ)) := congrArg (J (u y)) hcomp_1.symm
  have hIeq : fderiv ℝ (extChartAt I x ∘ u ∘ c.symm) w Complex.I =
      J.inChart x (extChartAt I x (u y)) (fderiv ℝ (extChartAt I x ∘ u ∘ c.symm) w 1) :=
    fderiv_extChartAt_comp_apply_eq_inChart J x hg_cont hux hg_cr
  have hzt : extChartAt I x (u y) ∈ (extChartAt I x).target := (extChartAt I x).map_source hux
  have hsq : J.inChart x (extChartAt I x (u y))
      (J.inChart x (extChartAt I x (u y))
        (fderiv ℝ (extChartAt I x ∘ u ∘ c.symm) w 1)) =
      -fderiv ℝ (extChartAt I x ∘ u ∘ c.symm) w 1 := J.inChart_inChart x hzt _
  change fderiv ℝ (extChartAt I x ∘ u ∘ c.symm) w 1 +
    J.inChart x (extChartAt I x (u y))
      (fderiv ℝ (extChartAt I x ∘ u ∘ c.symm) w Complex.I) = 0
  rw [hIeq, hsq, add_neg_cancel]

/-- The coordinate expression `extChartAt I x ∘ u ∘ (chartAt ℂ z₀).symm` has vanishing Fréchet
derivative at `w` iff `mfderiv 𝓘(ℝ, ℂ) I u ((chartAt ℂ z₀).symm w) = 0`. -/
theorem fderiv_extChartAt_comp_chartAt_symm_eq_zero_iff_mfderiv_eq_zero {u : S → X}
    (hu : MDifferentiable 𝓘(ℝ, ℂ) I u) (z₀ : S) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ z₀).target)
    (hux : u ((chartAt ℂ z₀).symm w) ∈ (extChartAt I x).source) :
    fderiv ℝ (extChartAt I x ∘ u ∘ (chartAt ℂ z₀).symm) w = 0 ↔
      mfderiv 𝓘(ℝ, ℂ) I u ((chartAt ℂ z₀).symm w) = 0 := by
  let c := chartAt ℂ z₀
  let y : S := c.symm w
  have hy_src : y ∈ c.source := c.map_target hw
  have hcs_mdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm w :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := z₀) w hw).mdifferentiableWithinAt
      (by simp) |>.mdifferentiableAt (c.open_target.mem_nhds hw)
  have hc_mdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c y :=
    (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := z₀) y hy_src).mdifferentiableWithinAt
      (by simp) |>.mdifferentiableAt (c.open_source.mem_nhds hy_src)
  have hg_cont : ContinuousAt (u ∘ c.symm) w := (hu y).continuousAt.comp hcs_mdiff.continuousAt
  have hcomp_apply (v : ℂ) : fderiv ℝ (extChartAt I x ∘ u ∘ c.symm) w v =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) (u y)
        (mfderiv 𝓘(ℝ, ℂ) I u y (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm w v)) := by
    rw [hg_cont.fderiv_extChartAt_comp_apply hux]
    exact congrArg (mfderiv I 𝓘(ℝ, E) (extChartAt I x) (u y))
      (mfderiv_comp_apply w (hu y) hcs_mdiff (v : TangentSpace 𝓘(ℝ, ℂ) w))
  constructor
  · intro h0
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hleft : ∀ q, c (c.symm w) = q →
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm q (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c y v) = v := by
      rintro q rfl
      exact c.mfderiv_symm_apply_mfderiv_apply hy_src hc_mdiff (by rwa [c.right_inv hw]) v
    have hcv : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm w (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c y v) = v :=
      hleft w (c.right_inv hw)
    let u0 : ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c y v
    have hv0 : mfderiv I 𝓘(ℝ, E) (extChartAt I x) (u y) (mfderiv 𝓘(ℝ, ℂ) I u y v) = 0 := by
      have h1 := hcomp_apply u0
      rw [h0, zero_apply] at h1
      have h2 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) c.symm w u0 = v := hcv
      rw [h2] at h1
      exact h1.symm
    have hinv := congrArg (fun L ↦ L (mfderiv 𝓘(ℝ, ℂ) I u y v))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hux)
    simp only [ContinuousLinearMap.comp_apply] at hinv
    rw [hv0, map_zero] at hinv
    exact hinv.symm
  · intro h0
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [hcomp_apply v, h0]
    change mfderiv I 𝓘(ℝ, E) (extChartAt I x) (u y) 0 = 0
    exact map_zero _

omit [IsManifold 𝓘(ℂ) ∞ S] in
/-- Pulling back a `𝓝 (chartAt ℂ z₀ z₀)` property through `chartAt ℂ z₀`. -/
private theorem eventually_nhds_of_chart {P : S → Prop} {z₀ : S}
    (h : ∀ᶠ w in 𝓝 (chartAt ℂ z₀ z₀), P ((chartAt ℂ z₀).symm w)) :
    ∀ᶠ z in 𝓝 z₀, P z := by
  let c := chartAt ℂ z₀
  filter_upwards [(c.continuousAt (mem_chart_source ℂ z₀)).eventually h,
    c.open_source.mem_nhds (mem_chart_source ℂ z₀)] with z hz hzs
  rwa [c.left_inv hzs] at hz

omit [IsManifold 𝓘(ℂ) ∞ S] in
/-- Pulling back a punctured neighborhood `𝓝[≠] (chartAt ℂ z₀ z₀)` property through
`chartAt ℂ z₀`. -/
private theorem eventually_nhdsNE_of_chart {P : S → Prop} {z₀ : S}
    (h : ∀ᶠ w in 𝓝[≠] (chartAt ℂ z₀ z₀), P ((chartAt ℂ z₀).symm w)) :
    ∀ᶠ z in 𝓝[≠] z₀, P z := by
  let c := chartAt ℂ z₀
  rw [eventually_nhdsWithin_iff] at h ⊢
  filter_upwards [(c.continuousAt (mem_chart_source ℂ z₀)).eventually h,
    c.open_source.mem_nhds (mem_chart_source ℂ z₀)] with z hz hzs hne
  have hcw : c z ≠ c z₀ := fun heq ↦ hne (c.injOn hzs (mem_chart_source ℂ z₀) heq)
  have hP := hz hcw
  rwa [c.left_inv hzs] at hP

omit [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S] in
/-- If `z ∈ closure A` and `∀ᶠ y in 𝓝[≠] z, y ∉ A`, then `z ∈ A`. -/
private theorem mem_of_mem_closure_of_eventually_nhdsNE_notMem {A : Set S} {z : S}
    (hz : z ∈ closure A) (hev : ∀ᶠ y in 𝓝[≠] z, y ∉ A) : z ∈ A := by
  by_contra hzA
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨y, hy_ev, hyA⟩ := mem_closure_iff_nhds.1 hz _ hev
  exact hy_ev (fun h ↦ hzA (h ▸ hyA)) hyA

end ChartHelpers

section TwoCurves

variable {E H X S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {n : ℕ∞} {J : ContMDiffAlmostComplexStructure I n X}

/-- **Local dichotomy at a coincidence point** (McDuff–Salamon, Lemma 2.4.1 on manifolds). If two
`C¹` pseudoholomorphic curves `u₁, u₂ : S → X` agree at `z₀`, then either they agree on a
neighbourhood of `z₀` or they disagree on a punctured neighbourhood of `z₀`. No separation
assumptions on `X` or `S` are needed. -/
theorem eventually_eq_or_eventually_ne_of_eq (hn : 1 ≤ n)
    {u₁ u₂ : S → X} (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    (hCR₁ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₁ z (Complex.I : ℂ) = J (u₁ z) (mfderiv 𝓘(ℝ, ℂ) I u₁ z (1 : ℂ)))
    (hCR₂ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₂ z (Complex.I : ℂ) = J (u₂ z) (mfderiv 𝓘(ℝ, ℂ) I u₂ z (1 : ℂ)))
    {z₀ : S} (heq : u₁ z₀ = u₂ z₀) :
    (∀ᶠ z in 𝓝 z₀, u₁ z = u₂ z) ∨ (∀ᶠ z in 𝓝[≠] z₀, u₁ z ≠ u₂ z) := by
  let x : X := u₁ z₀
  let c := chartAt ℂ z₀
  let φ := extChartAt I x
  let Ω : Set ℂ := c.target ∩ c.symm ⁻¹' (u₁ ⁻¹' φ.source ∩ u₂ ⁻¹' φ.source)
  let v₁ : ℂ → E := φ ∘ u₁ ∘ c.symm
  let v₂ : ℂ → E := φ ∘ u₂ ∘ c.symm
  have hΩ_open : IsOpen Ω := by
    have hV : IsOpen (u₁ ⁻¹' φ.source ∩ u₂ ⁻¹' φ.source) :=
      (isOpen_extChartAt_source x).preimage hu₁.continuous |>.inter
        ((isOpen_extChartAt_source x).preimage hu₂.continuous)
    exact c.continuousOn_invFun.isOpen_inter_preimage c.open_target hV
  have hw₀ : c z₀ ∈ Ω := by
    refine ⟨mem_chart_target ℂ z₀, ?_, ?_⟩
    · simp only [mem_preimage, c.left_inv (mem_chart_source ℂ z₀)]
      exact mem_extChartAt_source x
    · simp only [mem_preimage, c.left_inv (mem_chart_source ℂ z₀), ← heq]
      exact mem_extChartAt_source x
  have hJ_cd : ContDiffOn ℝ 1 (J.inChart x) φ.target :=
    (J.contDiffOn_inChart x).of_le (by exact_mod_cast hn)
  have hJJ : ∀ y ∈ φ.target, J.inChart x y ∘L J.inChart x y = -ContinuousLinearMap.id ℝ E :=
    fun y hy ↦ ContinuousLinearMap.ext fun v ↦ by
      simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply]
      exact J.inChart_inChart x hy v
  have hv₁_cd : ContDiffOn ℝ 1 v₁ Ω := by
    refine contMDiffOn_iff_contDiffOn.1 ?_
    have h1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 c.symm Ω :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := z₀)).of_le (by simp) |>.mono
        inter_subset_left
    have h2 : ContMDiffOn 𝓘(ℝ, ℂ) I 1 (u₁ ∘ c.symm) Ω := hu₁.comp_contMDiffOn h1
    exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).of_le (by simp) |>.comp h2
      fun w hw ↦ by
        have h : u₁ (c.symm w) ∈ φ.source := hw.2.1
        rwa [extChartAt_source] at h
  have hv₂_cd : ContDiffOn ℝ 1 v₂ Ω := by
    refine contMDiffOn_iff_contDiffOn.1 ?_
    have h1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 c.symm Ω :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := z₀)).of_le (by simp) |>.mono
        inter_subset_left
    have h2 : ContMDiffOn 𝓘(ℝ, ℂ) I 1 (u₂ ∘ c.symm) Ω := hu₂.comp_contMDiffOn h1
    exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).of_le (by simp) |>.comp h2
      fun w hw ↦ by
        have h : u₂ (c.symm w) ∈ φ.source := hw.2.2
        rwa [extChartAt_source] at h
  have hm₁ : MapsTo v₁ Ω φ.target := fun w hw ↦ φ.map_source hw.2.1
  have hCR₁' : ∀ w ∈ Ω, fderiv ℝ v₁ w 1 + J.inChart x (v₁ w) (fderiv ℝ v₁ w Complex.I) = 0 :=
    fun w hw ↦ fderiv_extChartAt_comp_chartAt_symm_add_inChart_eq_zero J
      (hu₁.mdifferentiable one_ne_zero) hCR₁ z₀ x hw.1 hw.2.1
  have hCR₂' : ∀ w ∈ Ω, fderiv ℝ v₂ w 1 + J.inChart x (v₂ w) (fderiv ℝ v₂ w Complex.I) = 0 :=
    fun w hw ↦ fderiv_extChartAt_comp_chartAt_symm_add_inChart_eq_zero J
      (hu₂.mdifferentiable one_ne_zero) hCR₂ z₀ x hw.1 hw.2.2
  have hv_eq : v₁ (c z₀) = v₂ (c z₀) := by
    simp only [v₁, v₂, Function.comp_apply, c.left_inv (mem_chart_source ℂ z₀), heq]
  have hdich := JHolomorphic.eventually_eq_or_eventually_ne_of_eq (isOpen_extChartAt_target x)
    hJ_cd hJJ hΩ_open hv₁_cd hv₂_cd hm₁ hCR₁' hCR₂' hw₀ hv_eq
  rcases hdich with hsame | hdiff
  · left
    refine eventually_nhds_of_chart ?_
    filter_upwards [hsame, hΩ_open.mem_nhds hw₀] with w hw hmem
    exact φ.injOn hmem.2.1 hmem.2.2 hw
  · right
    refine eventually_nhdsNE_of_chart ?_
    filter_upwards [hdiff] with w hw hEq
    exact hw (congrArg φ hEq)

/-- **Unique continuation (open set)** for two `C¹` pseudoholomorphic curves on a preconnected
Riemann surface into a Hausdorff boundaryless almost complex manifold. -/
theorem eq_of_eqOn [T2Space X] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u₁ u₂ : S → X} (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    (hCR₁ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₁ z (Complex.I : ℂ) = J (u₁ z) (mfderiv 𝓘(ℝ, ℂ) I u₁ z (1 : ℂ)))
    (hCR₂ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₂ z (Complex.I : ℂ) = J (u₂ z) (mfderiv 𝓘(ℝ, ℂ) I u₂ z (1 : ℂ)))
    {U : Set S} (hU : IsOpen U) (hUne : U.Nonempty) (heq : EqOn u₁ u₂ U) :
    u₁ = u₂ := by
  let A : Set S := interior {z | u₁ z = u₂ z}
  have hA_open : IsOpen A := isOpen_interior
  have hA_ne : A.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hUne
    exact ⟨z₀, mem_interior.2 ⟨U, heq, hU, hz₀⟩⟩
  have hA_closed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro z hz
    have heqz : u₁ z = u₂ z := by
      have hcl : IsClosed {w : S | u₁ w = u₂ w} := isClosed_eq hu₁.continuous hu₂.continuous
      exact hcl.closure_subset (closure_mono interior_subset hz)
    rcases eventually_eq_or_eventually_ne_of_eq hn hu₁ hu₂ hCR₁ hCR₂ heqz with hsame | hdiff
    · exact mem_interior_iff_mem_nhds.2 hsame
    · exact mem_of_mem_closure_of_eventually_nhdsNE_notMem hz
        (hdiff.mono fun y hy hyA ↦ hy (interior_subset hyA))
  have hA_univ : A = univ := (isClopen_iff.1 ⟨hA_closed, hA_open⟩).resolve_left hA_ne.ne_empty
  funext z
  exact interior_subset (hA_univ.symm ▸ mem_univ z)

/-- **Unique continuation (germ)** for two `C¹` pseudoholomorphic curves on a preconnected Riemann
surface into a Hausdorff boundaryless almost complex manifold. -/
theorem eq_of_eventuallyEq [T2Space X] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u₁ u₂ : S → X} (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    (hCR₁ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₁ z (Complex.I : ℂ) = J (u₁ z) (mfderiv 𝓘(ℝ, ℂ) I u₁ z (1 : ℂ)))
    (hCR₂ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₂ z (Complex.I : ℂ) = J (u₂ z) (mfderiv 𝓘(ℝ, ℂ) I u₂ z (1 : ℂ)))
    {z₀ : S} (heq : u₁ =ᶠ[𝓝 z₀] u₂) : u₁ = u₂ := by
  obtain ⟨U, hUsub, hUopen, hz₀U⟩ := _root_.mem_nhds_iff.1 heq
  exact eq_of_eqOn hn hu₁ hu₂ hCR₁ hCR₂ hUopen ⟨z₀, hz₀U⟩ hUsub

/-- Distinct `C¹` pseudoholomorphic curves on a preconnected Riemann surface into a Hausdorff
boundaryless almost complex manifold coincide only on a closed discrete set. -/
theorem setOf_ne_mem_codiscrete [T2Space X] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u₁ u₂ : S → X} (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    (hCR₁ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₁ z (Complex.I : ℂ) = J (u₁ z) (mfderiv 𝓘(ℝ, ℂ) I u₁ z (1 : ℂ)))
    (hCR₂ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₂ z (Complex.I : ℂ) = J (u₂ z) (mfderiv 𝓘(ℝ, ℂ) I u₂ z (1 : ℂ)))
    (hne : u₁ ≠ u₂) :
    {z | u₁ z ≠ u₂ z} ∈ codiscrete S := by
  rw [mem_codiscrete_iff_forall_mem_nhdsNE]
  intro z
  by_cases h : u₁ z = u₂ z
  · rcases eventually_eq_or_eventually_ne_of_eq hn hu₁ hu₂ hCR₁ hCR₂ h with hsame | hdiff
    · exact (hne (eq_of_eventuallyEq hn hu₁ hu₂ hCR₁ hCR₂ hsame)).elim
    · exact hdiff
  · exact nhdsWithin_le_nhds ((isOpen_ne_fun hu₁.continuous hu₂.continuous).mem_nhds h)

/-- Distinct `C¹` pseudoholomorphic curves on a compact preconnected Riemann surface into a
Hausdorff boundaryless almost complex manifold agree at only finitely many points. -/
theorem finite_setOf_eq [T2Space X] [CompactSpace S] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u₁ u₂ : S → X} (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    (hCR₁ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₁ z (Complex.I : ℂ) = J (u₁ z) (mfderiv 𝓘(ℝ, ℂ) I u₁ z (1 : ℂ)))
    (hCR₂ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₂ z (Complex.I : ℂ) = J (u₂ z) (mfderiv 𝓘(ℝ, ℂ) I u₂ z (1 : ℂ)))
    (hne : u₁ ≠ u₂) :
    {z | u₁ z = u₂ z}.Finite := by
  have hcod : {z | u₁ z ≠ u₂ z} ∈ codiscrete S :=
    setOf_ne_mem_codiscrete hn hu₁ hu₂ hCR₁ hCR₂ hne
  have hfin : {z | u₁ z ≠ u₂ z}ᶜ.Finite := cofinite_le_codiscrete hcod
  simpa only [compl_ofPred, not_not] using hfin

end TwoCurves

section Fibres

variable {E H X S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {n : ℕ∞} {J : ContMDiffAlmostComplexStructure I n X}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold 𝓘(ℂ) ∞ S] in
private theorem mfderiv_const_CR (x : X) (z : S) :
    mfderiv 𝓘(ℝ, ℂ) I (fun _ : S ↦ x) z (Complex.I : ℂ) =
      J x (mfderiv 𝓘(ℝ, ℂ) I (fun _ : S ↦ x) z (1 : ℂ)) := by
  rw [mfderiv_const]
  change (0 : TangentSpace I x) = J x (0 : TangentSpace I x)
  exact (map_zero (J.toEndomorphism x)).symm

/-- If a `C¹` pseudoholomorphic curve on a preconnected Riemann surface into a `T₁` boundaryless
almost complex manifold is locally constant near a point, then it is globally constant. -/
theorem eq_const_of_eventuallyEq_const [T1Space X] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {z₀ : S} {x : X} (heq : u =ᶠ[𝓝 z₀] fun _ ↦ x) :
    ∀ z, u z = x := by
  let A : Set S := interior (u ⁻¹' {x})
  have hA_open : IsOpen A := isOpen_interior
  have hA_ne : A.Nonempty := ⟨z₀, mem_interior_iff_mem_nhds.2 heq⟩
  have hA_closed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro z hz
    have heqz : u z = x :=
      (isClosed_singleton.preimage hu.continuous).closure_subset (closure_mono interior_subset hz)
    rcases eventually_eq_or_eventually_ne_of_eq hn hu contMDiff_const hCR
        (mfderiv_const_CR (J := J) x) heqz with hsame | hdiff
    · exact mem_interior_iff_mem_nhds.2 hsame
    · exact mem_of_mem_closure_of_eventually_nhdsNE_notMem hz
        (hdiff.mono fun y hy hyA ↦ hy (interior_subset hyA))
  have hA_univ : A = univ := (isClopen_iff.1 ⟨hA_closed, hA_open⟩).resolve_left hA_ne.ne_empty
  exact fun z ↦ interior_subset (hA_univ.symm ▸ mem_univ z)

/-- A `C¹` pseudoholomorphic curve on a preconnected Riemann surface into a `T₁` boundaryless
almost complex manifold that is not identically `x` has isolated `x`-preimages. -/
theorem setOf_ne_const_mem_codiscrete [T1Space X] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {x : X} (hne : ∃ z, u z ≠ x) :
    {z | u z ≠ x} ∈ codiscrete S := by
  rw [mem_codiscrete_iff_forall_mem_nhdsNE]
  intro z
  by_cases h : u z = x
  · rcases eventually_eq_or_eventually_ne_of_eq hn hu contMDiff_const hCR
        (mfderiv_const_CR (J := J) x) h with hsame | hdiff
    · obtain ⟨z', hz'⟩ := hne
      exact (hz' (eq_const_of_eventuallyEq_const hn hu hCR hsame z')).elim
    · exact hdiff
  · exact nhdsWithin_le_nhds ((isOpen_compl_singleton.preimage hu.continuous).mem_nhds h)

/-- Every fibre `u ⁻¹' {x}` of a `C¹` pseudoholomorphic curve on a compact preconnected Riemann
surface into a `T₁` boundaryless almost complex manifold that is not identically `x` is finite. -/
theorem finite_preimage_singleton [T1Space X] [CompactSpace S] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {x : X} (hne : ∃ z, u z ≠ x) :
    (u ⁻¹' {x}).Finite := by
  have hcod : {z | u z ≠ x} ∈ codiscrete S := setOf_ne_const_mem_codiscrete hn hu hCR hne
  have hfin : {z | u z ≠ x}ᶜ.Finite := cofinite_le_codiscrete hcod
  have heq : {z | u z ≠ x}ᶜ = u ⁻¹' {x} := by
    ext z
    simp
  rwa [heq] at hfin

end Fibres

section CriticalPoints

variable {E H X S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {n : ℕ∞} {J : ContMDiffAlmostComplexStructure I n X}

/-- **Local dichotomy at a critical point** of a `C²` pseudoholomorphic curve: either the
differential vanishes on a neighbourhood of `z₀`, or it is nonzero on a punctured neighbourhood of
`z₀`. No separation assumption on `X` or `S` is required. -/
theorem eventually_mfderiv_eq_zero_or_eventually_ne_zero (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (z₀ : S) :
    (∀ᶠ z in 𝓝 z₀, mfderiv 𝓘(ℝ, ℂ) I u z = 0) ∨
      (∀ᶠ z in 𝓝[≠] z₀, mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0) := by
  let x : X := u z₀
  let c := chartAt ℂ z₀
  let φ := extChartAt I x
  let Ω : Set ℂ := c.target ∩ c.symm ⁻¹' (u ⁻¹' φ.source)
  let v : ℂ → E := φ ∘ u ∘ c.symm
  have hΩ_open : IsOpen Ω :=
    c.continuousOn_invFun.isOpen_inter_preimage c.open_target
      ((isOpen_extChartAt_source x).preimage hu.continuous)
  have hw₀ : c z₀ ∈ Ω := by
    refine ⟨mem_chart_target ℂ z₀, ?_⟩
    simp only [mem_preimage, c.left_inv (mem_chart_source ℂ z₀)]
    exact mem_extChartAt_source x
  obtain ⟨r, hr, hball_sub⟩ := Metric.isOpen_iff.1 hΩ_open (c z₀) hw₀
  set B : Set ℂ := Metric.ball (c z₀) r
  have hJ_cd : ContDiffOn ℝ 1 (J.inChart x) φ.target :=
    (J.contDiffOn_inChart x).of_le (by exact_mod_cast hn)
  have hJJ : ∀ y ∈ φ.target, J.inChart x y ∘L J.inChart x y = -ContinuousLinearMap.id ℝ E :=
    fun y hy ↦ ContinuousLinearMap.ext fun w ↦ by
      simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply]
      exact J.inChart_inChart x hy w
  have hv_cd : ContDiffOn ℝ 2 v B := by
    refine contMDiffOn_iff_contDiffOn.1 ?_
    have h1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 2 c.symm B :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := z₀)).of_le (by simp) |>.mono
        (hball_sub.trans inter_subset_left)
    have h2 : ContMDiffOn 𝓘(ℝ, ℂ) I 2 (u ∘ c.symm) B := hu.comp_contMDiffOn h1
    exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).of_le (by simp) |>.comp h2
      fun w hw ↦ by
        have h : u (c.symm w) ∈ φ.source := (hball_sub hw).2
        rwa [extChartAt_source] at h
  have hm : MapsTo v B φ.target := fun w hw ↦ φ.map_source (hball_sub hw).2
  have hCR' : ∀ w ∈ B, fderiv ℝ v w 1 + J.inChart x (v w) (fderiv ℝ v w Complex.I) = 0 :=
    fun w hw ↦ fderiv_extChartAt_comp_chartAt_symm_add_inChart_eq_zero J
      (hu.mdifferentiable two_ne_zero) hCR z₀ x (hball_sub hw).1 (hball_sub hw).2
  have hiff (w : ℂ) (hw : w ∈ B) :
      fderiv ℝ v w = 0 ↔ mfderiv 𝓘(ℝ, ℂ) I u (c.symm w) = 0 :=
    fderiv_extChartAt_comp_chartAt_symm_eq_zero_iff_mfderiv_eq_zero
      (hu.mdifferentiable two_ne_zero) z₀ x (hball_sub hw).1 (hball_sub hw).2
  by_cases hconst : ∀ w ∈ B, v w = v (c z₀)
  · left
    refine eventually_nhds_of_chart ?_
    filter_upwards [Metric.ball_mem_nhds (c z₀) hr] with w hw
    have hfv : fderiv ℝ v w = 0 := by
      have hev : v =ᶠ[𝓝 w] fun _ ↦ v (c z₀) :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hw) hconst
      rw [hev.fderiv_eq]
      exact (hasFDerivAt_const (v (c z₀)) w).fderiv
    exact (hiff w hw).1 hfv
  · right
    push Not at hconst
    obtain ⟨w₁, hw₁, hw₁_ne⟩ := hconst
    have hnc : ∃ a ∈ B, ∃ b ∈ B, v a ≠ v b := ⟨w₁, hw₁, c z₀, Metric.mem_ball_self hr, hw₁_ne⟩
    have hdisc := JHolomorphic.setOf_fderiv_ne_zero_mem_codiscreteWithin
      (isOpen_extChartAt_target x) hJ_cd hJJ Metric.isOpen_ball
      (convex_ball (c z₀) r).isPreconnected hv_cd hm hCR' hnc
    have hmem : ∀ᶠ w in 𝓝[≠] (c z₀), w ∉ B \ {w | fderiv ℝ v w ≠ 0} :=
      disjoint_principal_right.1 (mem_codiscreteWithin.1 hdisc (c z₀) (Metric.mem_ball_self hr))
    refine eventually_nhdsNE_of_chart ?_
    filter_upwards [hmem, nhdsWithin_le_nhds (Metric.ball_mem_nhds (c z₀) hr)] with w hw hwB
    have hne : fderiv ℝ v w ≠ 0 := by
      by_contra h0
      exact hw ⟨hwB, fun h ↦ h h0⟩
    exact mt (hiff w hwB).2 hne

/-- If the differential of a `C²` pseudoholomorphic curve vanishes on a neighbourhood of a point
of a preconnected Riemann surface, then it vanishes everywhere. No separation assumption on `X` is
needed. -/
theorem mfderiv_eq_zero_of_eventually_mfderiv_eq_zero [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {z₀ : S} (h0 : ∀ᶠ z in 𝓝 z₀, mfderiv 𝓘(ℝ, ℂ) I u z = 0) (z : S) :
    mfderiv 𝓘(ℝ, ℂ) I u z = 0 := by
  let A : Set S := interior {w | mfderiv 𝓘(ℝ, ℂ) I u w = 0}
  have hA_open : IsOpen A := isOpen_interior
  have hA_ne : A.Nonempty := ⟨z₀, mem_interior_iff_mem_nhds.2 h0⟩
  have hA_closed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro w hw
    rcases eventually_mfderiv_eq_zero_or_eventually_ne_zero hn hu hCR w with hsame | hdiff
    · exact mem_interior_iff_mem_nhds.2 hsame
    · exact mem_of_mem_closure_of_eventually_nhdsNE_notMem hw
        (hdiff.mono fun y hy hyA ↦ hy (interior_subset hyA))
  have hA_univ : A = univ := (isClopen_iff.1 ⟨hA_closed, hA_open⟩).resolve_left hA_ne.ne_empty
  exact interior_subset (hA_univ.symm ▸ mem_univ z)

/-- A `C²` pseudoholomorphic curve on a preconnected Riemann surface whose differential vanishes
near a point is constant. No separation assumption on `X` is needed. -/
theorem apply_eq_of_eventually_mfderiv_eq_zero [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {z₀ : S} (h0 : ∀ᶠ z in 𝓝 z₀, mfderiv 𝓘(ℝ, ℂ) I u z = 0) (z₁ z₂ : S) :
    u z₁ = u z₂ :=
  (hu.mdifferentiable two_ne_zero).apply_eq_of_mfderiv_eq_zero
    (mfderiv_eq_zero_of_eventually_mfderiv_eq_zero hn hu hCR h0) z₁ z₂

/-- A `C²` pseudoholomorphic curve on a preconnected Riemann surface whose differential vanishes on
a nonempty open set is constant. -/
theorem apply_eq_of_mfderiv_eqOn_zero [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {U : Set S} (hU : IsOpen U) (hUne : U.Nonempty)
    (h0 : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℂ) I u z = 0) (z₁ z₂ : S) :
    u z₁ = u z₂ := by
  obtain ⟨z₀, hz₀⟩ := hUne
  exact apply_eq_of_eventually_mfderiv_eq_zero hn hu hCR
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) h0) z₁ z₂

/-- A nonconstant `C²` pseudoholomorphic curve on a preconnected Riemann surface has isolated
critical points: `{z | mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0} ∈ codiscrete S`. -/
theorem setOf_mfderiv_ne_zero_mem_codiscrete [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    {z | mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0} ∈ codiscrete S := by
  rw [mem_codiscrete_iff_forall_mem_nhdsNE]
  intro z
  rcases eventually_mfderiv_eq_zero_or_eventually_ne_zero hn hu hCR z with hsame | hdiff
  · obtain ⟨z₁, z₂, hne⟩ := hnc
    exact (hne (apply_eq_of_eventually_mfderiv_eq_zero hn hu hCR hsame z₁ z₂)).elim
  · exact hdiff

/-- For a nonconstant `C²` pseudoholomorphic curve on a preconnected Riemann surface, the points
where the differential is injective form a codiscrete subset of `S`. -/
theorem setOf_injective_mfderiv_mem_codiscrete [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    {z | Injective (mfderiv 𝓘(ℝ, ℂ) I u z)} ∈ codiscrete S := by
  have heq : {z | Injective (mfderiv 𝓘(ℝ, ℂ) I u z)} = {z | mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0} :=
    Set.ext fun z ↦ injective_mfderiv_iff_ne_zero J (hCR z)
  rw [heq]
  exact setOf_mfderiv_ne_zero_mem_codiscrete hn hu hCR hnc

/-- A nonconstant `C²` pseudoholomorphic curve on a compact preconnected Riemann surface has only
finitely many critical points. -/
theorem finite_setOf_mfderiv_eq_zero [CompactSpace S] [PreconnectedSpace S] (hn : 1 ≤ n)
    {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0}.Finite := by
  have hcod := setOf_mfderiv_ne_zero_mem_codiscrete hn hu hCR hnc
  have hfin : {z | mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0}ᶜ.Finite := cofinite_le_codiscrete hcod
  simpa only [compl_ofPred, not_not] using hfin

/-- For a nonconstant `C²` pseudoholomorphic curve on a compact preconnected Riemann surface into a
`T₁` boundaryless almost complex manifold, the exceptional set `u⁻¹(u(Crit u))` is finite. -/
theorem finite_preimage_image_setOf_mfderiv_eq_zero [T1Space X] [CompactSpace S]
    [PreconnectedSpace S] (hn : 1 ≤ n) {u : S → X} (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    (u ⁻¹' (u '' {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0})).Finite := by
  have hcrit : {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0}.Finite :=
    finite_setOf_mfderiv_eq_zero hn hu hCR hnc
  have himg : (u '' {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0}).Finite := hcrit.image u
  have hbi : u ⁻¹' (u '' {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0}) =
      ⋃ x ∈ u '' {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0}, u ⁻¹' {x} := by
    ext z
    simp only [mem_preimage, mem_image, mem_ofPred_eq, mem_iUnion, mem_singleton_iff, exists_prop]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨u a, ⟨a, ha, rfl⟩, h.symm⟩,
      fun ⟨_, ⟨a, ha, rfl⟩, h⟩ ↦ ⟨a, ha, h.symm⟩⟩
  rw [hbi]
  refine himg.biUnion fun x _ ↦ ?_
  have hne : ∃ z, u z ≠ x := by
    obtain ⟨z₁, z₂, h⟩ := hnc
    by_cases h1 : u z₁ = x
    · exact ⟨z₂, fun h2 ↦ h (h1.trans h2.symm)⟩
    · exact ⟨z₁, h1⟩
  exact finite_preimage_singleton hn (hu.of_le (by norm_num)) hCR hne

end CriticalPoints

end TauCeti.Pseudoholomorphic

/-! ### Dot-notation wrappers for `IsPseudoholomorphicAt` and `IsPseudoholomorphic` -/

namespace TauCeti

section SmoothWrappers

variable {E H X S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {J : SmoothAlmostComplexStructure I X}

private theorem IsPseudoholomorphicAt.mfderiv_apply_I {u : S → X} {z : S}
    (hu : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u z) :
    mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) =
      (J.toContMDiff ⊤) (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)) := by
  have h := hu.mfderiv_apply_commute (1 : ℂ)
  rw [SmoothAlmostComplexStructure.ofComplexManifold_apply (E := ℂ) z (1 : ℂ),
    smul_eq_mul, mul_one] at h
  exact h.trans (SmoothAlmostComplexStructure.toContMDiff_apply J ⊤ (u z) _).symm

/-- At a point where a map from a Riemann surface is pseudoholomorphic, its manifold differential
is injective iff it is nonzero. -/
theorem IsPseudoholomorphicAt.injective_mfderiv_iff_ne_zero {u : S → X} {z : S}
    (hu : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u z) :
    Injective (mfderiv 𝓘(ℝ, ℂ) I u z) ↔ mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0 :=
  Pseudoholomorphic.injective_mfderiv_iff_ne_zero (J.toContMDiff ⊤) hu.mfderiv_apply_I

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- Unique continuation (germ) for two `C¹` pseudoholomorphic curves on a preconnected Riemann
surface into a Hausdorff smooth almost complex manifold. -/
theorem IsPseudoholomorphic.eq_of_eventuallyEq [T2Space X] [PreconnectedSpace S] {u₁ u₂ : S → X}
    (hu₁ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u₁)
    (hu₂ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u₂)
    (hc₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hc₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    {z₀ : S} (heq : u₁ =ᶠ[𝓝 z₀] u₂) : u₁ = u₂ :=
  Pseudoholomorphic.eq_of_eventuallyEq (J := J.toContMDiff ⊤) le_top hc₁ hc₂
    (fun z ↦ (isPseudoholomorphic_iff.1 hu₁ z).mfderiv_apply_I)
    (fun z ↦ (isPseudoholomorphic_iff.1 hu₂ z).mfderiv_apply_I) heq

/-- Distinct `C¹` pseudoholomorphic curves on a preconnected Riemann surface coincide only on a
closed discrete set. -/
theorem IsPseudoholomorphic.setOf_ne_mem_codiscrete [T2Space X] [PreconnectedSpace S]
    {u₁ u₂ : S → X}
    (hu₁ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u₁)
    (hu₂ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u₂)
    (hc₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hc₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    (hne : u₁ ≠ u₂) : {z | u₁ z ≠ u₂ z} ∈ codiscrete S :=
  Pseudoholomorphic.setOf_ne_mem_codiscrete (J := J.toContMDiff ⊤) le_top hc₁ hc₂
    (fun z ↦ (isPseudoholomorphic_iff.1 hu₁ z).mfderiv_apply_I)
    (fun z ↦ (isPseudoholomorphic_iff.1 hu₂ z).mfderiv_apply_I) hne

/-- Distinct `C¹` pseudoholomorphic curves on a compact preconnected Riemann surface agree at only
finitely many points. -/
theorem IsPseudoholomorphic.finite_setOf_eq [T2Space X] [CompactSpace S] [PreconnectedSpace S]
    {u₁ u₂ : S → X}
    (hu₁ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u₁)
    (hu₂ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u₂)
    (hc₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hc₂ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₂)
    (hne : u₁ ≠ u₂) : {z | u₁ z = u₂ z}.Finite :=
  Pseudoholomorphic.finite_setOf_eq (J := J.toContMDiff ⊤) le_top hc₁ hc₂
    (fun z ↦ (isPseudoholomorphic_iff.1 hu₁ z).mfderiv_apply_I)
    (fun z ↦ (isPseudoholomorphic_iff.1 hu₂ z).mfderiv_apply_I) hne

/-- Every fibre of a `C¹` pseudoholomorphic curve on a compact preconnected Riemann surface into a
`T₁` smooth almost complex manifold that is not constantly equal to `x` is finite. -/
theorem IsPseudoholomorphic.finite_preimage_singleton [T1Space X] [CompactSpace S]
    [PreconnectedSpace S] {u : S → X}
    (hu : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u)
    (hc : ContMDiff 𝓘(ℝ, ℂ) I 1 u) {x : X} (hne : ∃ z, u z ≠ x) :
    (u ⁻¹' {x}).Finite :=
  Pseudoholomorphic.finite_preimage_singleton (J := J.toContMDiff ⊤) le_top hc
    (fun z ↦ (isPseudoholomorphic_iff.1 hu z).mfderiv_apply_I) hne

/-- A nonconstant `C²` pseudoholomorphic curve on a preconnected Riemann surface has isolated
critical points. -/
theorem IsPseudoholomorphic.setOf_mfderiv_ne_zero_mem_codiscrete [PreconnectedSpace S] {u : S → X}
    (hu : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u)
    (hc : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    {z | mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0} ∈ codiscrete S :=
  Pseudoholomorphic.setOf_mfderiv_ne_zero_mem_codiscrete (J := J.toContMDiff ⊤) le_top hc
    (fun z ↦ (isPseudoholomorphic_iff.1 hu z).mfderiv_apply_I) hnc

/-- A nonconstant `C²` pseudoholomorphic curve on a compact preconnected Riemann surface has only
finitely many critical points. -/
theorem IsPseudoholomorphic.finite_setOf_mfderiv_eq_zero [CompactSpace S] [PreconnectedSpace S]
    {u : S → X}
    (hu : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u)
    (hc : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0}.Finite :=
  Pseudoholomorphic.finite_setOf_mfderiv_eq_zero (J := J.toContMDiff ⊤) le_top hc
    (fun z ↦ (isPseudoholomorphic_iff.1 hu z).mfderiv_apply_I) hnc

/-- For a nonconstant `C²` pseudoholomorphic curve on a compact preconnected Riemann surface into a
`T₁` smooth almost complex manifold, the exceptional set `u⁻¹(u(Crit u))` is finite. -/
theorem IsPseudoholomorphic.finite_preimage_image_setOf_mfderiv_eq_zero [T1Space X]
    [CompactSpace S] [PreconnectedSpace S] {u : S → X}
    (hu : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u)
    (hc : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    (u ⁻¹' (u '' {z | mfderiv 𝓘(ℝ, ℂ) I u z = 0})).Finite :=
  Pseudoholomorphic.finite_preimage_image_setOf_mfderiv_eq_zero (J := J.toContMDiff ⊤) le_top hc
    (fun z ↦ (isPseudoholomorphic_iff.1 hu z).mfderiv_apply_I) hnc

end SmoothWrappers

end TauCeti
