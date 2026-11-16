/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import Mathlib.Order.Disjointed
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Operations
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Integrating functions against the Riemannian volume form

On an oriented Riemannian manifold `M`, a function `f : M → ℝ` is integrated as the top form
`f vol`, where `vol = TauCeti.riemannianVolumeForm o` is the Riemannian volume form of the
orientation `o`: `∫_M f vol = integralTopForm o (fun x ↦ f x • vol x)`. This file records the
basic properties of this integral that pointwise estimates need: it is nonnegative on nonnegative
functions, strictly positive when a continuous compactly supported nonnegative function is positive
at one point, commutes with constant factors, and on a compact manifold is additive and monotone on
continuous functions. All statements hold in every dimension, including dimension `0`, because in
every chart the orientation sign cancels the sign of the volume form to leave the positive chart
volume density `TauCeti.chartVolumeDensity`.

## Main results

* `TauCeti.integralTopForm_smul_riemannianVolumeForm_nonneg`: `0 ≤ f` gives `0 ≤ ∫_M f vol`.
* `TauCeti.integralTopForm_riemannianVolumeForm_nonneg`: `0 ≤ ∫_M vol`.
* `TauCeti.integralTopForm_mul_smul_riemannianVolumeForm`: `∫_M c f vol = c ∫_M f vol`.
* `TauCeti.isSmoothForm_smul_riemannianVolumeForm`: `f vol` is a continuous top form when `f`
  is continuous.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_pos`: for a continuous compactly supported
  nonnegative `f` that is positive at some point, `0 < ∫_M f vol`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_eq_zero_iff_of_hasCompactSupport`,
  `TauCeti.integralTopForm_smul_riemannianVolumeForm_eq_zero_iff`: a continuous compactly supported
  nonnegative `f` satisfies `∫_M f vol = 0` iff `f = 0` everywhere.
* `TauCeti.integralTopForm_riemannianVolumeForm_pos`: on a compact nonempty manifold,
  `0 < ∫_M vol`.
* `TauCeti.integralTopForm_add_smul_riemannianVolumeForm`: on a compact manifold,
  `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_mono`: on a compact manifold, `f ≤ g`
  gives `∫_M f vol ≤ ∫_M g vol` for continuous `f` and `g`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6 and Proposition 15.29.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ} (o : Manifold.Orientation I M (Fin m))

/-- In the chart at `α`, the coefficient of the Riemannian volume form on the reindexed standard
model basis is the volume form on the coordinate frame. -/
private theorem inChartAt_riemannianVolumeForm
    (σ : Fin (finrank ℝ E) ≃ Fin m) (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    (riemannianVolumeForm o).inChartAt α y ((finBasis ℝ E).reindex σ) =
      riemannianVolumeForm o ((extChartAt I α).symm y)
        (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) α (σ.symm i)
          ((extChartAt I α).symm y)) := by
  have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  have hframe : (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y
      ((finBasis ℝ E).reindex σ i)) =
      fun i ↦
        Riemannian.Tensor.chartLocalFrame (I := I) α (σ.symm i) ((extChartAt I α).symm y) := by
    funext i
    rw [Riemannian.Tensor.chartLocalFrame_eq_symmL, TangentBundle.symmL_trivializationAt hx,
      (extChartAt I α).right_inv hy, Module.Basis.reindex_apply]
    rfl
  rw [RoughForm.inChartAt_apply, hframe]

/-- In the chart at `α`, the signed coefficient of `f vol`, multiplied by the sign of the model
basis, is `chartVolumeDensity α x * f x` in every dimension, including dimension `0`. -/
private theorem signBasis_mul_signedInChartAt_smul_riemannianVolumeForm
    (l : Manifold.OrientationLift I M (Fin m)) (σ : Fin (finrank ℝ E) ≃ Fin m) (f : M → ℝ)
    (α : M) {x : M} (hx : x ∈ (extChartAt I α).source) :
    (Orientation.signBasis l.modelOrientation ((finBasis ℝ E).reindex σ) : ℝ) *
        RoughForm.signedInChartAt
          (fun z ↦ f z • riemannianVolumeForm (Manifold.Orientation.mk l) z)
          ((finBasis ℝ E).reindex σ) α (fun z ↦ l.signAt α z) (extChartAt I α x) =
      chartVolumeDensity (I := I) α x * f x := by
  rw [RoughForm.signedInChartAt_fun_smul, (extChartAt I α).left_inv hx,
    RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx,
    inChartAt_riemannianVolumeForm _ σ α ((extChartAt I α).map_source hx),
    (extChartAt I α).left_inv hx,
    ← signBasis_mul_signAt_mul_riemannianVolumeForm_chartLocalFrame l σ
      (by simpa only [extChartAt_source] using hx)]
  ring

/-- Every chart integrand computing `∫_M f vol` for `0 ≤ f` is nonnegative. -/
private theorem signBasis_mul_signedInChartAt_smul_riemannianVolumeForm_nonneg
    (l : Manifold.OrientationLift I M (Fin m)) (σ : Fin (finrank ℝ E) ≃ Fin m)
    {f : M → ℝ} (hf : ∀ x, 0 ≤ f x) (α : M) (y : E) :
    0 ≤ (Orientation.signBasis l.modelOrientation ((finBasis ℝ E).reindex σ) : ℝ) *
      RoughForm.signedInChartAt
        (fun z ↦ f z • riemannianVolumeForm (Manifold.Orientation.mk l) z)
        ((finBasis ℝ E).reindex σ) α (fun z ↦ l.signAt α z) y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [← (extChartAt I α).right_inv hy,
      signBasis_mul_signedInChartAt_smul_riemannianVolumeForm l σ f α
        ((extChartAt I α).map_target hy)]
    exact mul_nonneg (chartVolumeDensity_nonneg α _) (hf _)
  · rw [RoughForm.signedInChartAt_apply, dite_eq_right hy, mul_zero]

/-- The integral `∫_M f vol` of a nonnegative function against the Riemannian volume form is
nonnegative in every dimension, including dimension `0`. -/
theorem integralTopForm_smul_riemannianVolumeForm_nonneg {f : M → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) := by
  set φ : RoughForm I M ℝ m := fun x ↦ f x • riemannianVolumeForm o x
  by_cases hi : IntegrableTopForm φ
  swap
  · rw [integralTopForm_eq_zero_of_not_integrable o φ hi]
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨l, rfl⟩ := o.exists_lift
  let σ : Fin (finrank ℝ E) ≃ Fin m := finCongr (by simpa using l.card_eq.symm)
  let b := (finBasis ℝ E).reindex σ
  obtain ⟨k, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hu i).1)
    (fun i ↦ (hu i).2.1) hcover, Finset.mul_sum]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [← integral_const_mul]
  exact integral_nonneg fun y ↦
    signBasis_mul_signedInChartAt_smul_riemannianVolumeForm_nonneg l σ hf (α i) y

/-- The integral `∫_M vol` of the Riemannian volume form is nonnegative in every dimension,
including on noncompact manifolds where nonintegrable forms integrate to zero. -/
theorem integralTopForm_riemannianVolumeForm_nonneg :
    0 ≤ integralTopForm o (riemannianVolumeForm o) := by
  simpa only [one_smul] using
    integralTopForm_smul_riemannianVolumeForm_nonneg o (f := fun _ ↦ (1 : ℝ)) fun _ ↦ zero_le_one

/-- Constant factors come out of the integral against the Riemannian volume form:
`∫_M c f vol = c ∫_M f vol`. -/
theorem integralTopForm_mul_smul_riemannianVolumeForm (c : ℝ) (f : M → ℝ) :
    integralTopForm o (fun x ↦ (c * f x) • riemannianVolumeForm o x) =
      c * integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_smul]
  congr 1
  funext x
  rw [Pi.smul_apply, mul_smul]

section Continuous

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- For a continuous function `f`, the top form `f vol` is continuous. -/
theorem isSmoothForm_smul_riemannianVolumeForm {f : M → ℝ} (hf : Continuous f) :
    IsSmoothForm I 0 (fun x ↦ f x • riemannianVolumeForm o x) := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  exact (isSmoothForm_riemannianVolumeForm o).fun_smul (contMDiff_zero_iff.2 hf)

/-- **Strict positivity of the integral against the Riemannian volume form.** In every dimension
(including dimension `0`), if `f : M → ℝ` is continuous, compactly supported, nonnegative
everywhere, and strictly positive at some point, then `0 < ∫_M f vol`. -/
theorem integralTopForm_smul_riemannianVolumeForm_pos {f : M → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hnn : ∀ x, 0 ≤ f x) (hpos : ∃ x, 0 < f x) :
    0 < integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨l, rfl⟩ := o.exists_lift
  obtain ⟨x₀, hfx₀⟩ := hpos
  let σ : Fin (finrank ℝ E) ≃ Fin m := finCongr (by simpa using l.card_eq.symm)
  let b := (finBasis ℝ E).reindex σ
  set φ : RoughForm I M ℝ m := fun x ↦ f x • riemannianVolumeForm (Manifold.Orientation.mk l) x
  have hφ : IsSmoothForm I 0 φ := isSmoothForm_smul_riemannianVolumeForm _ hf
  have hsupp : _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) φ ⊆ tsupport f :=
    closure_mono fun x hx ↦ Function.mem_support.2 fun h ↦ hx (by simp [φ, h]; rfl)
  have hcφ : IsCompact (_root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) φ) :=
    hc.of_isClosed_subset isClosed_closure hsupp
  have hi : IntegrableTopForm φ := hφ.integrableTopForm hcφ b
  obtain ⟨k, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hcφ
  let α' : Fin (k + 1) → M := Fin.cons x₀ α
  let u' : Fin (k + 1) → Set M := Fin.cons (extChartAt I x₀).source u
  have hu' : ∀ i, IsOpen (u' i) ∧ u' i ⊆ (extChartAt I (α' i)).source := by
    refine Fin.cases ?_ fun i ↦ ?_
    · simpa [α', u'] using isOpen_extChartAt_source (I := I) x₀
    · simpa [α', u'] using And.intro (hu i).1 (hu i).2.1
  have hcover' : _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) φ ⊆ ⋃ i, u' i :=
    hcover.trans (iUnion_subset fun i ↦ by simpa [u'] using subset_iUnion u' i.succ)
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α' u' (fun i ↦ (hu' i).1)
    (fun i ↦ (hu' i).2) hcover', Finset.mul_sum, Fin.sum_univ_succ]
  refine add_pos_of_pos_of_nonneg ?_ (Finset.sum_nonneg fun i _ ↦ ?_)
  swap
  · rw [← integral_const_mul]
    exact integral_nonneg fun y ↦
      signBasis_mul_signedInChartAt_smul_riemannianVolumeForm_nonneg l σ hnn (α' i.succ) y
  have hpiece : (extChartAt I (α' 0)) '' disjointed u' 0 = (extChartAt I (α' 0)).target := by
    rw [← bot_eq_zero, disjointed_bot, bot_eq_zero]
    simp only [α', u', Fin.cons_zero]
    exact (extChartAt I x₀).image_source_eq_target
  rw [hpiece, ← integral_const_mul]
  simp only [α', Fin.cons_zero]
  let g : E → ℝ := fun y ↦ (Orientation.signBasis l.modelOrientation b : ℝ) *
    φ.signedInChartAt b x₀ (fun z ↦ l.signAt x₀ z) y
  have hsign : Continuous (fun z : {z : M // z ∈ (extChartAt I x₀).source} ↦ l.signAt x₀ z) := by
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt x₀
  have hint : Integrable g b.addHaar :=
    ((φ.integrable_signedInChartAt_iff_unsigned b x₀ _ hsign b.addHaar).mpr
      (((integrableTopForm_iff φ).mp hi).2.2 b x₀)).const_mul _
  have hcont : ContinuousOn g (extChartAt I x₀).target :=
    continuousOn_const.mul (φ.continuousOn_signedInChartAt b x₀ _ hsign
      (hφ.continuousOn_inChartAt x₀))
  have hx₀ : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hg₀ : 0 < g (extChartAt I x₀ x₀) := by
    dsimp only [g]
    rw [signBasis_mul_signedInChartAt_smul_riemannianVolumeForm l σ f x₀ hx₀]
    exact mul_pos (chartVolumeDensity_pos x₀ (FiberBundle.mem_baseSet_trivializationAt' x₀)) hfx₀
  exact setIntegral_pos_of_nonneg_of_pos_at_extChartAt_target (μ := b.addHaar) x₀
    (signBasis_mul_signedInChartAt_smul_riemannianVolumeForm_nonneg l σ hnn x₀)
    hint.integrableOn hcont ((extChartAt I x₀).map_source hx₀) hg₀

/-- A continuous compactly supported nonnegative function integrates to zero against the
Riemannian volume form if and only if it vanishes identically. -/
theorem integralTopForm_smul_riemannianVolumeForm_eq_zero_iff_of_hasCompactSupport {f : M → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hnn : ∀ x, 0 ≤ f x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) = 0 ↔ ∀ x, f x = 0 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · by_contra hfx
    exact (integralTopForm_smul_riemannianVolumeForm_pos o hf hc hnn
      ⟨x, (hnn x).lt_of_ne' hfx⟩).ne' h
  · simp_rw [h, zero_smul]
    exact integralTopForm_zero o

variable [CompactSpace M]

/-- On a compact oriented Riemannian manifold of any dimension, a continuous nonnegative function
integrates to zero against the Riemannian volume form if and only if it vanishes everywhere. -/
theorem integralTopForm_smul_riemannianVolumeForm_eq_zero_iff {f : M → ℝ} (hf : Continuous f)
    (hnn : ∀ x, 0 ≤ f x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) = 0 ↔ ∀ x, f x = 0 :=
  integralTopForm_smul_riemannianVolumeForm_eq_zero_iff_of_hasCompactSupport o hf
    (HasCompactSupport.of_compactSpace f) hnn

/-- On a compact nonempty oriented Riemannian manifold of any dimension (including dimension `0`),
the integral `∫_M vol` of the Riemannian volume form is strictly positive. -/
theorem integralTopForm_riemannianVolumeForm_pos [Nonempty M] :
    0 < integralTopForm o (riemannianVolumeForm o) := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  simpa only [one_smul] using integralTopForm_smul_riemannianVolumeForm_pos o
    (f := fun _ ↦ (1 : ℝ)) continuous_const (HasCompactSupport.of_compactSpace _)
    (fun _ ↦ zero_le_one) ⟨x₀, zero_lt_one⟩

/-- On a compact oriented Riemannian manifold, the integral against the Riemannian volume form is
additive on continuous functions: `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol`. -/
theorem integralTopForm_add_smul_riemannianVolumeForm {f g : M → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    integralTopForm o (fun x ↦ (f x + g x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) +
        integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_add_of_compactSpace o (isSmoothForm_smul_riemannianVolumeForm o hf)
    (isSmoothForm_smul_riemannianVolumeForm o hg)]
  congr 1
  funext x
  rw [Pi.add_apply, add_smul]

/-- **Monotonicity of the integral against the Riemannian volume form**: on a compact oriented
Riemannian manifold of any dimension, continuous functions with `f ≤ g` satisfy
`∫_M f vol ≤ ∫_M g vol`. -/
theorem integralTopForm_smul_riemannianVolumeForm_mono {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  have h :=
    integralTopForm_add_smul_riemannianVolumeForm o (g := fun x ↦ g x - f x) hf (hg.sub hf)
  simp only [add_sub_cancel] at h
  rw [h, le_add_iff_nonneg_right]
  exact integralTopForm_smul_riemannianVolumeForm_nonneg o fun x ↦ sub_nonneg.2 (hfg x)

end Continuous

end TauCeti
