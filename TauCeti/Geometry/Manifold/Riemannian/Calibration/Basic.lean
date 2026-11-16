/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CalibratedFrame
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Smooth calibrations on Riemannian manifolds

A smooth differential `k`-form `φ` on a manifold `M` equipped with a smooth Riemannian metric `g`
is a *calibration* (`TauCeti.IsCalibration g φ`) when `φ` is smooth, closed (`mextDeriv φ = 0`),
and has comass at most one at every point: `|φ x v| ≤ 1` for every `g_x`-orthonormal `k`-frame `v`
in `TangentSpace I x`. In degree zero, where the unique empty frame is vacuously orthonormal, a
calibration is a smooth locally constant function taking values in `[-1, 1]`.

Because `ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal` identifies the supremum over
orthonormal frames with the native operator norm on alternating maps, the pointwise bound in
`IsCalibration g φ` is equivalent to `‖φ x‖ ≤ 1` in the fiber inner product induced by `g`
(`TauCeti.isCalibration_iff_norm_le_one`). In positive degree (`[NeZero k]`), negating one slot of
an orthonormal frame flips the sign of `φ x v`, so the two-sided bound `|φ x v| ≤ 1` is equivalent
to the one-sided bound `φ x v ≤ 1` (`TauCeti.isCalibration_iff_le_one_of_neZero`).

## Main definitions

* `TauCeti.IsCalibration`: smooth closed `k`-form of fiberwise comass at most one with respect to
  a smooth Riemannian metric `g`.
* `TauCeti.IsCalibration.toSmoothForm`: bundle the underlying smooth form as a `SmoothForm`.

## Main results

* `TauCeti.isCalibration_iff_orthonormal`, `TauCeti.isCalibration_iff_norm_le_one`: equivalence of
  the explicit Gram-matrix bound with fiberwise `Orthonormal ℝ v` and fiberwise operator norm
  `‖φ x‖ ≤ 1`.
* `TauCeti.isCalibration_iff_le_one_of_neZero`: in positive degree, the one-sided bound `φ x v ≤ 1`
  on orthonormal frames suffices.
* `TauCeti.isCalibration_zero`, `TauCeti.IsCalibration.neg`, `TauCeti.IsCalibration.smul`,
  `TauCeti.IsCalibration.convex`: calibrations form a balanced convex set.
* `TauCeti.IsCalibration.pullback`: pulling a calibration back along a smooth immersion produces a
  calibration for the pullback metric.
* `TauCeti.isCalibration_riemannianVolumeForm`: on a smooth oriented Riemannian `m`-manifold, the
  Riemannian volume form is a calibration.
* `TauCeti.isCalibration_const_iff`, `TauCeti.isCalibration_const_alternatingFormEquiv_ιMulti`: on
  a real inner product space with its flat metric, constant forms of comass at most one (in
  particular, simple unit `k`-forms) are calibrations.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Definition II.4.1.
* D. D. Joyce, *Riemannian Holonomy Groups and Calibrated Geometry*, Oxford University Press, 2007,
  Definition 4.1.1.
-/

public section

noncomputable section

open Bundle Module exteriorPower
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

section OnceDifferentiable

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {k : ℕ}

/-- A smooth calibration for a smooth Riemannian metric `g` on `M`: a smooth closed real `k`-form
`φ` satisfying `|φ x v| ≤ 1` on every `g_x`-orthonormal `k`-frame `v` of `TangentSpace I x`. -/
def IsCalibration (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) : Prop :=
  IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
    ∀ x (v : Fin k → TangentSpace I x),
      (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → |φ x v| ≤ 1

/-- Definitional unfolding of `TauCeti.IsCalibration`. -/
theorem isCalibration_def (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) :
    IsCalibration g φ =
      (IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
        ∀ x (v : Fin k → TangentSpace I x),
          (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → |φ x v| ≤ 1) :=
  (rfl)

/-- Smoothness of a calibration. -/
theorem IsCalibration.isSmoothForm
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) : IsSmoothForm I ∞ φ :=
  h.1

/-- Closedness (`mextDeriv φ = 0`) of a calibration. -/
theorem IsCalibration.mextDeriv_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) : mextDeriv φ = 0 :=
  h.2.1

/-- Pointwise comass bound of a calibration on `g_x`-orthonormal frames. -/
theorem IsCalibration.abs_apply_le_one
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) (x : M) (v : Fin k → TangentSpace I x)
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) :
    |φ x v| ≤ 1 :=
  h.2.2 x v hv

/-- Upper comass bound `φ x v ≤ 1` of a calibration on `g_x`-orthonormal frames. -/
theorem IsCalibration.apply_le_one
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) (x : M) (v : Fin k → TangentSpace I x)
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) :
    φ x v ≤ 1 :=
  (le_abs_self _).trans (h.abs_apply_le_one x v hv)

/-- Lower comass bound `-1 ≤ φ x v` of a calibration on `g_x`-orthonormal frames. -/
theorem IsCalibration.neg_one_le_apply
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) (x : M) (v : Fin k → TangentSpace I x)
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) :
    -1 ≤ φ x v :=
  (abs_le.mp (h.abs_apply_le_one x v hv)).1

/-- Bundle a calibration as a `SmoothForm`. -/
def IsCalibration.toSmoothForm
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) : SmoothForm I M ℝ k :=
  ⟨φ, h.isSmoothForm.mem_smoothBundleForms⟩

/-- The underlying rough form of `IsCalibration.toSmoothForm` is `φ`. -/
@[simp]
theorem IsCalibration.coe_toSmoothForm
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) : (h.toSmoothForm : RoughForm I M ℝ k) = φ :=
  (rfl)

/-- The bundled `SmoothForm` of a calibration is closed. -/
theorem IsCalibration.isClosed
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) : h.toSmoothForm.IsClosed :=
  (SmoothForm.isClosed_def _).mpr h.mextDeriv_eq_zero

/-- Express `IsCalibration g φ` using Mathlib's `Orthonormal ℝ` predicate in the fiber inner
product installed by `g`. -/
theorem isCalibration_iff_orthonormal
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) :
    IsCalibration g φ ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
        ∀ x (v : Fin k → TangentSpace I x), Orthonormal ℝ v → |φ x v| ≤ 1 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall_congr' fun x ↦
    forall_congr' fun v ↦ ?_
  have hiff : Orthonormal ℝ v ↔ ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0 := by
    classical
    rw [orthonormal_iff_ite]
    rfl
  rw [hiff]

/-- Express `IsCalibration g φ` using the fiberwise operator norm (comass) `‖φ x‖ ≤ 1` in the
fiber inner product installed by `g`. -/
theorem isCalibration_iff_norm_le_one
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) :
    IsCalibration g φ ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧ ∀ x, ‖φ x‖ ≤ 1 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [isCalibration_iff_orthonormal]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall_congr' fun x ↦ ?_
  simpa only [Real.norm_eq_abs] using
    ((φ x).opNorm_le_iff_le_orthonormal zero_le_one).symm

/-- Every fiber of a calibration has operator norm (comass) at most one in the metric installed by
`g`. -/
theorem IsCalibration.norm_le_one
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) (x : M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ‖φ x‖ ≤ 1 :=
  ((isCalibration_iff_norm_le_one g φ).mp h).2.2 x

/-- Pointwise comass inequality against exterior products: on a finite-dimensional manifold, a
calibration satisfies `|φ x v| ≤ ‖v₁ ∧ ⋯ ∧ vₖ‖` in the fiber metric of `g`. -/
theorem IsCalibration.abs_apply_le_norm_ιMulti [FiniteDimensional ℝ E]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) (x : M) (v : Fin k → TangentSpace I x) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    |φ x v| ≤ ‖ιMulti ℝ k v‖ := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hnorm : ‖φ x‖ ≤ 1 := h.norm_le_one x
  have hle := (φ x).le_opNorm_mul_norm_ιMulti v
  rw [Real.norm_eq_abs] at hle
  exact hle.trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)

/-- In positive degree (`[NeZero k]`), a smooth closed `k`-form is a calibration if and only if
`φ x v ≤ 1` on every `g_x`-orthonormal frame `v`: negating one vector of `v` supplies the lower
bound `-1 ≤ φ x v`. -/
theorem isCalibration_iff_le_one_of_neZero [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) :
    IsCalibration g φ ↔
      IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
        ∀ x (v : Fin k → TangentSpace I x),
          (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → φ x v ≤ 1 := by
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h x v hv ↦ (le_abs_self _).trans (h x v hv), fun h x v hv ↦ ?_⟩
  classical
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hv_orth : Orthonormal ℝ v := orthonormal_iff_ite.mpr hv
  let i₀ : Fin k := ⟨0, NeZero.pos k⟩
  let v' : Fin k → TangentSpace I x := Function.update v i₀ (-v i₀)
  have hv'_orth : Orthonormal ℝ v' :=
    hv_orth.orthonormal_of_forall_eq_or_eq_neg fun j ↦ by by_cases hj : j = i₀ <;> simp [v', hj]
  have hneg : φ x v' = -φ x v := by
    rw [← (φ x).coe_toAlternatingMap, (φ x).toAlternatingMap.map_update_neg,
      Function.update_eq_self, (φ x).coe_toAlternatingMap]
  have hle' : -φ x v ≤ 1 := hneg ▸ h x v' (orthonormal_iff_ite.mp hv'_orth)
  exact abs_le.mpr ⟨neg_le.mp hle', h x v hv⟩

/-- The zero `k`-form is a calibration for every smooth Riemannian metric in every degree. -/
@[simp]
theorem isCalibration_zero (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    IsCalibration g (0 : RoughForm I M ℝ k) :=
  ⟨IsSmoothForm.zero ∞, mextDeriv_zero, fun _ _ _ ↦ by simp⟩

/-- In degree `k` strictly exceeding `finrank ℝ E`, every `RoughForm I M ℝ k` vanishes and is
therefore a calibration. -/
theorem isCalibration_of_finrank_lt [FiniteDimensional ℝ E] (hk : finrank ℝ E < k)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) :
    IsCalibration g φ := by
  have hzero : φ = 0 := by
    funext x
    ext v
    by_cases hv : LinearIndependent ℝ v
    · exact absurd (by simpa using hv.fintype_card_le_finrank) hk.not_ge
    · change φ x v = 0
      simpa only [ContinuousAlternatingMap.coe_toAlternatingMap] using
        (φ x).toAlternatingMap.map_linearDependent v hv
  rw [hzero]
  exact isCalibration_zero g

/-- Negating a calibration produces a calibration. -/
theorem IsCalibration.neg
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) : IsCalibration g (-φ) := by
  refine ⟨h.isSmoothForm.neg, ?_, fun x v hv ↦ by simpa using h.abs_apply_le_one x v hv⟩
  simpa only [SmoothForm.isClosed_def, SmoothForm.neg_toRoughForm, h.coe_toSmoothForm] using
    h.isClosed.neg

/-- Scaling a calibration by a real constant `c` with `|c| ≤ 1` produces a calibration. -/
theorem IsCalibration.smul
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (h : IsCalibration g φ) {c : ℝ} (hc : |c| ≤ 1) :
    IsCalibration g (c • φ) := by
  refine ⟨h.isSmoothForm.smul c, ?_, fun x v hv ↦ ?_⟩
  · simpa only [SmoothForm.isClosed_def, SmoothForm.smul_toRoughForm, h.coe_toSmoothForm] using
      h.isClosed.smul c
  · rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, abs_mul]
    simpa only [one_mul] using mul_le_mul hc (h.abs_apply_le_one x v hv) (abs_nonneg _) zero_le_one

/-- **Convexity of the space of calibrations**: if `φ` and `ψ` are calibrations and `0 ≤ a`,
`0 ≤ b`, `a + b ≤ 1`, then `a • φ + b • ψ` is a calibration. -/
theorem IsCalibration.convex
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ ψ : RoughForm I M ℝ k} (hφ : IsCalibration g φ) (hψ : IsCalibration g ψ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    IsCalibration g (a • φ + b • ψ) := by
  refine ⟨(hφ.isSmoothForm.smul a).add (hψ.isSmoothForm.smul b), ?_, fun x v hv ↦ ?_⟩
  · have hclosed := (hφ.isClosed.smul a).add (hψ.isClosed.smul b)
    simpa only [SmoothForm.isClosed_def, SmoothForm.add_toRoughForm, SmoothForm.smul_toRoughForm,
      hφ.coe_toSmoothForm, hψ.coe_toSmoothForm] using hclosed
  · calc |(a • φ + b • ψ) x v|
        = |a * φ x v + b * ψ x v| := by simp
      _ ≤ |a * φ x v| + |b * ψ x v| := abs_add_le _ _
      _ = a * |φ x v| + b * |ψ x v| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (hφ.abs_apply_le_one x v hv) ha)
          (mul_le_mul_of_nonneg_left (hψ.abs_apply_le_one x v hv) hb)
      _ ≤ 1 := by linarith

end OnceDifferentiable

section Pullback

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 2 N]
  {k : ℕ}

/-- **Pullback of calibrations along immersions**: pulling a calibration `φ` on `(M, g)` back along
a smooth immersion `f : N → M` produces a calibration `mpullback I' I f φ` for the pullback metric
`g.pullback f _ hinj`. -/
theorem IsCalibration.pullback
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (hφ : IsCalibration g φ) {f : N → M} (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) :
    IsCalibration (g.pullback f (by simpa using hf) hinj) (mpullback I' I f φ) := by
  refine ⟨by simpa only [SmoothForm.coe_mpullback, hφ.coe_toSmoothForm] using
      (SmoothForm.mpullback f hf hφ.toSmoothForm).isSmoothForm, ?_, fun x v hv ↦ ?_⟩
  · simpa only [SmoothForm.isClosed_def, SmoothForm.coe_mpullback, hφ.coe_toSmoothForm] using
      hφ.isClosed.mpullback f hf
  · rw [mpullback_apply]
    exact hφ.abs_apply_le_one (f x) (fun i ↦ mfderiv I' I f x (v i)) fun i j ↦ by
      simpa only [ContMDiffRiemannianMetric.pullback_inner] using hv i j

end Pullback

section VolumeForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {m : ℕ}

/-- On a smooth oriented Riemannian `m`-manifold `(M, g, o)`, the Riemannian volume form of `g` and
`o` is a smooth calibration. -/
theorem isCalibration_riemannianVolumeForm
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsCalibration g (riemannianVolumeForm o) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsManifold I (∞ + 1) M := by simpa using ‹IsManifold I ∞ M›
  rw [isCalibration_iff_norm_le_one]
  refine ⟨isSmoothForm_riemannianVolumeForm o,
    mextDeriv_eq_zero_of_finrank_le (by simpa using o.card_eq.symm.le) _, fun x ↦ ?_⟩
  let _ := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def, Orientation.norm_volumeFormL]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem riemannianMetric_eq_of_inner_eq
    {g₁ g₂ : RiemannianMetric (fun x : M ↦ TangentSpace I x)}
    (h : ∀ x v w, g₁.inner x v w = g₂.inner x v w) : g₁ = g₂ := by
  cases g₁
  cases g₂
  congr 1
  funext x
  ext v w
  exact h x v w

/-- Variant of `TauCeti.isCalibration_riemannianVolumeForm` when the metric is already installed via
`RiemannianBundle` and `IsContMDiffRiemannianBundle`. -/
theorem isCalibration_ofIsContMDiffRiemannianBundle_riemannianVolumeForm
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin m)) :
    IsCalibration
      (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E)
        (V := fun x : M ↦ TangentSpace I x))
      (riemannianVolumeForm o) := by
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  convert isCalibration_riemannianVolumeForm g o
  exact (riemannianMetric_eq_of_inner_eq fun x v w ↦
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner x v w).symm

end VolumeForm

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- On a real inner product space `E` equipped with its flat Euclidean metric
`(riemannianMetricVectorSpace E).ofLE le_top`, a constant `k`-form `fun _ ↦ α` is a calibration if
and only if `‖α‖ ≤ 1`. -/
@[simp]
theorem isCalibration_const_iff (α : E [⋀^Fin k]→L[ℝ] ℝ) :
    IsCalibration ((riemannianMetricVectorSpace E).ofLE le_top)
      ((fun _ : E ↦ α) : RoughForm 𝓘(ℝ, E) E ℝ k) ↔ ‖α‖ ≤ 1 := by
  classical
  have horth (x : E) (v : Fin k → TangentSpace 𝓘(ℝ, E) x) :
      (∀ i j, ((riemannianMetricVectorSpace E).ofLE (le_top : (∞ : ℕ∞ω) ≤ ω)).inner x (v i) (v j) =
        if i = j then 1 else 0) ↔ Orthonormal (E := E) ℝ v := by
    simp only [ContMDiffRiemannianMetric.ofLE_inner]
    exact (orthonormal_iff_ite (𝕜 := ℝ) (E := E) (v := v)).symm
  refine ⟨fun h ↦ ?_, fun hα ↦ ⟨isSmoothForm_modelSpace_iff.mpr contDiff_const, mextDeriv_const α,
    fun x v hv ↦ ?_⟩⟩
  · refine (α.opNorm_le_iff_le_orthonormal zero_le_one).mpr fun v hv ↦ ?_
    rw [Real.norm_eq_abs]
    exact h.2.2 0 v ((horth 0 v).mpr hv)
  · have hle := (α.opNorm_le_iff_le_orthonormal zero_le_one).mp hα v ((horth x v).mp hv)
    rw [Real.norm_eq_abs] at hle
    exact hle

/-- On a finite-dimensional real inner product space `E`, the constant simple `k`-form built from
any orthonormal `k`-frame `u : Fin k → E` is a smooth calibration for the flat metric. -/
theorem isCalibration_const_alternatingFormEquiv_ιMulti [FiniteDimensional ℝ E]
    {u : Fin k → E} (hu : Orthonormal ℝ u) :
    IsCalibration ((riemannianMetricVectorSpace E).ofLE le_top)
      ((fun _ : E ↦ alternatingFormEquiv E k (ιMulti ℝ k u)) : RoughForm 𝓘(ℝ, E) E ℝ k) :=
  (isCalibration_const_iff _).mpr <| by
    rw [norm_alternatingFormEquiv_ιMulti, hu.norm_ιMulti]

end ModelSpace

end TauCeti
