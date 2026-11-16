/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Riemannian.Calibration.Basic
public import TauCeti.Geometry.Manifold.Riemannian.FormMetric
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# Immersion volume, calibrated immersions, and the integrated calibration inequality

Let `(M, g)` be a manifold equipped with a smooth Riemannian metric `g`, and let `f : N → M` be a
smooth immersion of an oriented smooth `k`-manifold `(N, o)`. Pulling `g` back along `f` equips `N`
with an induced smooth Riemannian metric `f^* g` (`Bundle.ContMDiffRiemannianMetric.pullback`).

* The *immersion volume* `TauCeti.immersionVolume g f hf hinj o` is the integral over `(N, o)` of
  the Riemannian volume form of `f^* g`. It is nonnegative, strictly positive when `N` is compact
  and nonempty (including in dimension `0`), independent of the orientation `o` (`-o` negates both
  the integration orientation and the volume form), invariant under diffeomorphisms of the domain,
  and on compact Borel manifolds agrees with the total measure `riemannianTotalVolume`.
* The immersion `f` is *calibrated* by a `k`-form `φ` on `M`
  (`TauCeti.IsCalibratedImmersion g φ f hf hinj o`) when `mpullback I' I f φ` equals the Riemannian
  volume form of `(f^* g, o)`. Equivalently, at every point `x : N`, the image `df_x ∘ b` of a
  positively oriented `(f^* g)_x`-orthonormal basis `b` is a calibrated frame
  (`TauCeti.IsCalibratedFrame (φ (f x)) (df_x ∘ b)`).
* Pairing `mpullback I' I f φ` pointwise against `riemannianVolumeForm o` via
  `TauCeti.alternatingFormInner` produces a smooth scalar function, the *calibration density*
  `TauCeti.calibrationDensity g φ f hf hinj o : N → ℝ`, satisfying `(f^* φ)_x = c(x) vol_o(x)`.
  When `φ` is a calibration (`TauCeti.IsCalibration g φ`), `|c(x)| ≤ 1` everywhere, with `c(x) = 1`
  if and only if `(f^* φ)_x = vol_o(x)`. Integrating over a compact `N` yields the **integrated
  calibration inequality** `∫_N f^* φ ≤ Vol(f)` together with its equality characterization:
  `∫_N f^* φ = Vol(f)` if and only if `f` is calibrated by `φ`
  (`TauCeti.IsCalibration.integralTopForm_mpullback_eq_immersionVolume_iff`).

## Main definitions

* `TauCeti.immersionVolume`: induced Riemannian volume `∫_N vol_{f^* g, o}` of an oriented smooth
  immersion `f : N → M`.
* `TauCeti.IsCalibratedImmersion`: `mpullback I' I f φ = riemannianVolumeForm o` for the pullback
  metric `f^* g`.
* `TauCeti.calibrationDensity`: smooth scalar density `x ↦ ⟨vol_{f^* g, o}(x), (f^* φ)_x⟩`.

## Main results

* `TauCeti.immersionVolume_neg`, `TauCeti.immersionVolume_nonneg`, `TauCeti.immersionVolume_pos`,
  `TauCeti.immersionVolume_eq_riemannianTotalVolume`: basic properties of `immersionVolume`.
* `TauCeti.IsCalibratedImmersion.comp_of_isOrientationPreservingAt`,
  `TauCeti.immersionVolume_comp_diffeomorph_of_isOrientationPreservingAt`,
  `TauCeti.immersionVolume_comp_diffeomorph_of_isOrientationReversingAt`,
  `TauCeti.isCalibratedImmersion_comp_diffeomorph_iff`: pullback along orientation-preserving local
  diffeomorphisms and reparametrization invariance along smooth diffeomorphisms.
* `TauCeti.isCalibratedImmersion_iff_forall_isCalibratedFrame`: equivalence of
  `IsCalibratedImmersion` in positive degree with pointwise `IsCalibratedFrame` on positively
  oriented `(f^* g)`-orthonormal bases.
* `TauCeti.IsCalibration.integralTopForm_mpullback_le_immersionVolume`,
  `TauCeti.IsCalibration.abs_integralTopForm_mpullback_le_immersionVolume`,
  `TauCeti.IsCalibration.integralTopForm_mpullback_eq_immersionVolume_iff`: the integrated
  calibration inequality and its rigidity characterization in every degree `k ≥ 0`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Lemma II.3.5 and §II.4.
* D. D. Joyce, *Riemannian Holonomy Groups and Calibrated Geometry*, Oxford University Press, 2007,
  Proposition 4.1.4.
-/

public section

noncomputable section

open Bundle Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

section Immersion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {k : ℕ}

/-- The volume of a smooth immersion `f : N → M` of an oriented `k`-manifold: the integral over
`N`, against its orientation `o`, of the Riemannian volume form of the pulled-back metric `f^* g`.
It does not depend on the orientation chosen (`TauCeti.immersionVolume_neg`). -/
def immersionVolume (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : ℝ :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  integralTopForm o (riemannianVolumeForm o)

/-- Definitional unfolding of `TauCeti.immersionVolume`. -/
theorem immersionVolume_def (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o =
      (letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
       integralTopForm o (riemannianVolumeForm o)) :=
  (rfl)

/-- `immersionVolume` depends on `f` only as a map, not on the regularity or injectivity proofs. -/
theorem immersionVolume_congr
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f₁ f₂ : N → M} (h : f₁ = f₂)
    (hf₁ : ContMDiff I' I ∞ f₁) (hinj₁ : ∀ x, Function.Injective (mfderiv I' I f₁ x))
    (hf₂ : ContMDiff I' I ∞ f₂) (hinj₂ : ∀ x, Function.Injective (mfderiv I' I f₂ x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f₁ hf₁ hinj₁ o = immersionVolume g f₂ hf₂ hinj₂ o := by
  subst h
  rfl

/-- Reversing the orientation `o` leaves `immersionVolume` unchanged, because both the integration
orientation and `riemannianVolumeForm` flip sign. -/
@[simp]
theorem immersionVolume_neg
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj (-o) = immersionVolume g f hf hinj o := by
  let _ : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have hneg : (-riemannianVolumeForm o : RoughForm I' N ℝ k) = (-1 : ℝ) • riemannianVolumeForm o :=
    (neg_one_smul ℝ (riemannianVolumeForm o)).symm
  rw [immersionVolume_def, immersionVolume_def, riemannianVolumeForm_neg, integralTopForm_neg,
    hneg, integralTopForm_smul]
  ring

/-- The immersion volume is nonnegative in every dimension `k ≥ 0`. -/
theorem immersionVolume_nonneg
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 ≤ immersionVolume g f hf hinj o := by
  let _ : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  exact integralTopForm_riemannianVolumeForm_nonneg o

/-- On a compact nonempty manifold `N` of any dimension `k ≥ 0`, the immersion volume is strictly
positive. -/
theorem immersionVolume_pos [CompactSpace N] [Nonempty N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 < immersionVolume g f hf hinj o := by
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.instIsContinuousRiemannianBundle gN.toContinuousRiemannianMetric
  have : IsContMDiffRiemannianBundle I' 0 E' (fun x : N ↦ TangentSpace I' x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  exact integralTopForm_riemannianVolumeForm_pos o

/-- On a compact Borel manifold `N`, `immersionVolume` coincides with the total Riemannian volume
`riemannianTotalVolume` of the pullback metric `f^* g`. -/
theorem immersionVolume_eq_riemannianTotalVolume [CompactSpace N] [MeasurableSpace N]
    [BorelSpace N] (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o =
      (let gN := g.pullback f (by simpa using hf) hinj
       letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
         Bundle.instIsContinuousRiemannianBundle gN.toContinuousRiemannianMetric
       riemannianTotalVolume I' N) := by
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.instIsContinuousRiemannianBundle gN.toContinuousRiemannianMetric
  exact integralTopForm_riemannianVolumeForm o

/-- The oriented smooth immersion `f : N → M` is *calibrated* by the `k`-form `φ` when `f^* φ` is
the Riemannian volume form of the pulled-back metric `f^* g` for the orientation `o`. -/
def IsCalibratedImmersion
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : Prop :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  mpullback I' I f φ = riemannianVolumeForm o

/-- Definitional unfolding of `TauCeti.IsCalibratedImmersion`. -/
theorem isCalibratedImmersion_def
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o =
      (letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
       mpullback I' I f φ = riemannianVolumeForm o) :=
  (rfl)

/-- Pointwise characterization of `IsCalibratedImmersion`. -/
theorem isCalibratedImmersion_iff_forall
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
      ∀ x, mpullback I' I f φ x = riemannianVolumeForm o x :=
  funext_iff

/-- Reversing the orientation of `N` switches calibration by `φ` to calibration by `-φ`. -/
@[simp]
theorem isCalibratedImmersion_neg_orientation_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj (-o) ↔ IsCalibratedImmersion g (-φ) f hf hinj o := by
  let _ : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_def, isCalibratedImmersion_def, riemannianVolumeForm_neg]
  have hneg : mpullback I' I f (-φ) = -mpullback I' I f φ := by
    simpa only [neg_one_smul] using mpullback_smul (I := I') (I' := I) f (-1 : ℝ) φ
  rw [hneg, neg_eq_iff_eq_neg, eq_comm]

/-- A calibrated immersion integrates `f^* φ` directly to its immersion volume, without any
compactness hypothesis on `N`. -/
theorem IsCalibratedImmersion.integralTopForm_mpullback_eq
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    {f : N → M} {hf : ContMDiff I' I ∞ f} {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o := by
  rw [immersionVolume_def]
  exact congrArg (integralTopForm o) hcal

/-- At a point `x : N` equipped with a positively oriented `(f^* g)_x`-orthonormal basis `b`,
`mpullback I' I f φ x` equals `riemannianVolumeForm o x` if and only if `df_x ∘ b` is a
`g_{f x}`-calibrated frame for `φ (f x)`. -/
theorem mpullback_eq_riemannianVolumeForm_iff_isCalibratedFrame
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (b : letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
          ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
         OrthonormalBasis (Fin k) ℝ (TangentSpace I' x))
    (hb : (letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
            ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
           b.toBasis.orientation) = o.orientationAt x) :
    (letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
     mpullback I' I f φ x = riemannianVolumeForm o x) ↔
    (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
     IsCalibratedFrame (φ (f x)) (mfderiv I' I f x ∘ b)) := by
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  have horth : Orthonormal ℝ (mfderiv I' I f x ∘ b) := by
    classical
    rw [orthonormal_iff_ite]
    intro i j
    change g.inner (f x) (mfderiv I' I f x (b i)) (mfderiv I' I f x (b j)) =
      if i = j then 1 else 0
    rw [← g.pullback_inner f (by simpa using hf) hinj x]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  rw [isCalibratedFrame_def]
  refine ⟨fun h ↦ ⟨horth, ?_⟩, fun ⟨_, hφ⟩ ↦ ?_⟩
  · have happ : mpullback I' I f φ x b = riemannianVolumeForm o x b := DFunLike.congr_fun h ⇑b
    rw [mpullback_apply] at happ
    exact happ.trans (riemannianVolumeForm_apply_orthonormal o x b hb)
  · refine eq_riemannianVolumeForm_of_apply_orthonormal o x (mpullback I' I f φ x) b hb ?_
    rw [mpullback_apply]
    exact hφ

/-- Every calibrated immersion sends any `(f^* g)_x`-calibrated tangent frame of
`riemannianVolumeForm o` at `x` to a `g_{f x}`-calibrated tangent frame of `φ (f x)`, in every
degree `k ≥ 0`. -/
theorem IsCalibratedImmersion.isCalibratedFrame_mfderiv_comp
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    {f : N → M} {hf : ContMDiff I' I ∞ f} {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) (x : N) (v : Fin k → TangentSpace I' x)
    (hv : letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
            ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
          IsCalibratedFrame (riemannianVolumeForm o x) v) :
    letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
    IsCalibratedFrame (φ (f x)) (mfderiv I' I f x ∘ v) := by
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  rw [isCalibratedFrame_def] at hv ⊢
  refine ⟨?_, ?_⟩
  · classical
    rw [orthonormal_iff_ite]
    intro i j
    change g.inner (f x) (mfderiv I' I f x (v i)) (mfderiv I' I f x (v j)) =
      if i = j then 1 else 0
    rw [← g.pullback_inner f (by simpa using hf) hinj x]
    exact orthonormal_iff_ite.mp hv.1 i j
  · have hx : mpullback I' I f φ x = riemannianVolumeForm o x :=
      (isCalibratedImmersion_iff_forall g φ f hf hinj o).mp hcal x
    have happ : mpullback I' I f φ x v = riemannianVolumeForm o x v := DFunLike.congr_fun hx v
    rw [mpullback_apply] at happ
    exact happ.trans hv.2

/-- In positive degree (`[NeZero k]`), an oriented smooth immersion `f : N → M` is calibrated by
`φ` if and only if at every point `x : N`, every positively oriented `(f^* g)_x`-orthonormal tangent
frame `v` (characterized by `IsCalibratedFrame (riemannianVolumeForm o x) v`) pushes forward to a
`g_{f x}`-calibrated frame `df_x ∘ v` for `φ (f x)`. -/
theorem isCalibratedImmersion_iff_forall_isCalibratedFrame [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      ∀ x (v : Fin k → TangentSpace I' x),
        (letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
          ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
         IsCalibratedFrame (riemannianVolumeForm o x) v) →
        (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
         IsCalibratedFrame (φ (f x)) (mfderiv I' I f x ∘ v)) := by
  refine ⟨fun hcal x v hv ↦ hcal.isCalibratedFrame_mfderiv_comp x v hv, fun h ↦ ?_⟩
  rw [isCalibratedImmersion_iff_forall]
  intro x
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  let _ := o.fact_finrank_tangentSpace x
  let b₀ : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
    ((stdOrthonormalBasis ℝ (TangentSpace I' x)).reindex (finCongr Fact.out)).adjustToOrientation
      (o.orientationAt x)
  have hb₀ : b₀.toBasis.orientation = o.orientationAt x :=
    OrthonormalBasis.orientation_adjustToOrientation _ _
  have hcal₀ : IsCalibratedFrame (riemannianVolumeForm o x) b₀ := by
    rw [isCalibratedFrame_def]
    exact ⟨b₀.orthonormal, riemannianVolumeForm_apply_orthonormal o x b₀ hb₀⟩
  exact (mpullback_eq_riemannianVolumeForm_iff_isCalibratedFrame g φ f hf hinj o x b₀ hb₀).mpr
    (h x b₀ hcal₀)

/-! ### Calibration density and the integrated calibration inequality -/

/-- The *calibration density* of a `k`-form `φ` along an oriented smooth immersion `f : N → M`: the
pointwise inner product `⟨vol_{f^* g, o}(x), (f^* φ)_x⟩` in the pullback metric `f^* g`. -/
def calibrationDensity
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) : ℝ :=
  letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  alternatingFormInner (TangentSpace I' x) k (riemannianVolumeForm o x) (mpullback I' I f φ x)

/-- Definitional unfolding of `TauCeti.calibrationDensity`. -/
theorem calibrationDensity_def
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) :
    calibrationDensity g φ f hf hinj o x =
      (letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
       alternatingFormInner (TangentSpace I' x) k
        (riemannianVolumeForm o x) (mpullback I' I f φ x)) :=
  (rfl)

/-- Every pulled-back `k`-form along `f` decomposes as its calibration density times the Riemannian
volume form of `(f^* g, o)`, in every dimension `k ≥ 0`. -/
@[simp]
theorem calibrationDensity_smul_riemannianVolumeForm
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) :
    (letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
     calibrationDensity g φ f hf hinj o x • riemannianVolumeForm o x) =
      mpullback I' I f φ x := by
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let _ := o.fact_finrank_tangentSpace x
  rw [calibrationDensity_def, riemannianVolumeForm_def]
  exact (o.orientationAt x).alternatingFormInner_volumeFormL_smul (mpullback I' I f φ x)

/-- Negating `φ` negates `calibrationDensity`. -/
@[simp]
theorem calibrationDensity_neg_form
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) :
    calibrationDensity g (-φ) f hf hinj o x = -calibrationDensity g φ f hf hinj o x := by
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have hneg : mpullback I' I f (-φ) x = -mpullback I' I f φ x := by
    have h := congrFun (mpullback_smul (I := I') (I' := I) f (-1 : ℝ) φ) x
    simpa only [neg_one_smul, Pi.neg_apply] using h
  rw [calibrationDensity_def, calibrationDensity_def, hneg, map_neg]

/-- Reversing the orientation `o` negates `calibrationDensity`. -/
@[simp]
theorem calibrationDensity_neg_orientation
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) :
    calibrationDensity g φ f hf hinj (-o) x = -calibrationDensity g φ f hf hinj o x := by
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [calibrationDensity_def, calibrationDensity_def, riemannianVolumeForm_neg, Pi.neg_apply,
    map_neg, LinearMap.neg_apply]

/-- At each point `x : N`, `calibrationDensity` equals `1` if and only if `(f^* φ)_x` equals the
Riemannian volume form `vol_{f^* g, o}(x)`. -/
theorem calibrationDensity_eq_one_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) :
    calibrationDensity g φ f hf hinj o x = 1 ↔
      (letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
       mpullback I' I f φ x = riemannianVolumeForm o x) := by
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let _ := o.fact_finrank_tangentSpace x
  rw [calibrationDensity_def, riemannianVolumeForm_def]
  exact (o.orientationAt x).alternatingFormInner_volumeFormL_eq_one_iff (mpullback I' I f φ x)

/-- An oriented smooth immersion is calibrated by `φ` if and only if its calibration density is
identically `1`. -/
theorem isCalibratedImmersion_iff_calibrationDensity_eq_one
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      ∀ x, calibrationDensity g φ f hf hinj o x = 1 := by
  rw [isCalibratedImmersion_iff_forall]
  exact forall_congr' fun x ↦ (calibrationDensity_eq_one_iff g φ f hf hinj o x).symm

/-- For any smooth `k`-form `φ`, `calibrationDensity g φ f hf hinj o` is smooth (`C^∞`). -/
theorem IsSmoothForm.contMDiff_calibrationDensity
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (hφ : IsSmoothForm I ∞ φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    ContMDiff I' 𝓘(ℝ) ∞ (calibrationDensity g φ f hf hinj o) := by
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I' ∞ E' (fun y : N ↦ TangentSpace I' y) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  have : IsManifold I' (∞ + 1) N := by simpa using ‹IsManifold I' ∞ N›
  have hvol : IsSmoothForm I' ∞ (riemannianVolumeForm o) := isSmoothForm_riemannianVolumeForm o
  have hpull : IsSmoothForm I' ∞ (TauCeti.mpullback I' I f φ) := by
    simpa only [SmoothForm.coe_mpullback] using
      (SmoothForm.mpullback f hf ⟨φ, hφ.mem_smoothBundleForms⟩).isSmoothForm
  exact hvol.contMDiff_alternatingFormInner hpull

/-- **Pointwise calibration inequality** (Harvey–Lawson, Lemma II.3.5): when `φ` is a calibration
for `g`, its calibration density along every smooth immersion satisfies `|c(x)| ≤ 1` in every
degree `k ≥ 0`. -/
theorem IsCalibration.abs_calibrationDensity_le_one
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) :
    |calibrationDensity g φ f hf hinj o x| ≤ 1 := by
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ := o.fact_finrank_tangentSpace x
  rw [calibrationDensity_def, riemannianVolumeForm_def,
    (o.orientationAt x).abs_alternatingFormInner_volumeFormL]
  refine ((mpullback I' I f φ x).opNorm_le_iff_le_orthonormal zero_le_one).mpr fun v hv ↦ ?_
  rw [Real.norm_eq_abs, mpullback_apply]
  refine hφ.abs_apply_le_one (f x) (fun i ↦ mfderiv I' I f x (v i)) fun i j ↦ ?_
  rw [← g.pullback_inner f (by simpa using hf) hinj x]
  classical
  exact orthonormal_iff_ite.mp hv i j

/-- Upper pointwise bound `calibrationDensity ≤ 1` for a calibration. -/
theorem IsCalibration.calibrationDensity_le_one
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N) :
    calibrationDensity g φ f hf hinj o x ≤ 1 :=
  (le_abs_self _).trans (hφ.abs_calibrationDensity_le_one f hf hinj o x)

/-- **Integrated calibration inequality**: on a compact oriented `k`-manifold `N` (possibly with
boundary or corners, and including degree `k = 0`), any smooth immersion `f : N → M` and smooth
calibration `φ` satisfy `∫_N f^* φ ≤ immersionVolume g f hf hinj o`. -/
theorem IsCalibration.integralTopForm_mpullback_le_immersionVolume [CompactSpace N]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    integralTopForm o (mpullback I' I f φ) ≤ immersionVolume g f hf hinj o := by
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace I' y) :=
    Bundle.instIsContinuousRiemannianBundle gN.toContinuousRiemannianMetric
  have : IsContMDiffRiemannianBundle I' 0 E' (fun y : N ↦ TangentSpace I' y) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have hdecomp : mpullback I' I f φ =
      fun x ↦ calibrationDensity g φ f hf hinj o x • riemannianVolumeForm o x :=
    funext fun x ↦ (calibrationDensity_smul_riemannianVolumeForm g φ f hf hinj o x).symm
  have hc : Continuous (calibrationDensity g φ f hf hinj o) :=
    (hφ.isSmoothForm.contMDiff_calibrationDensity f hf hinj o).continuous
  rw [hdecomp, immersionVolume_def]
  simpa only [one_smul] using integralTopForm_smul_riemannianVolumeForm_mono o hc continuous_const
    (hφ.calibrationDensity_le_one f hf hinj o)

/-- Two-sided integrated calibration inequality: `|∫_N f^* φ| ≤ immersionVolume g f hf hinj o`. -/
theorem IsCalibration.abs_integralTopForm_mpullback_le_immersionVolume [CompactSpace N]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    |integralTopForm o (mpullback I' I f φ)| ≤ immersionVolume g f hf hinj o := by
  refine abs_le.mpr ⟨neg_le.mp ?_, hφ.integralTopForm_mpullback_le_immersionVolume f hf hinj o⟩
  have hneg : mpullback I' I f (-φ) = -mpullback I' I f φ := by
    simpa only [neg_one_smul] using mpullback_smul (I := I') (I' := I) f (-1 : ℝ) φ
  have hle := hφ.neg.integralTopForm_mpullback_le_immersionVolume f hf hinj o
  rw [hneg, ← neg_one_smul ℝ, integralTopForm_smul] at hle
  linarith

/-- **Equality in the integrated calibration inequality**: on a compact oriented `k`-manifold `N`
(in every degree `k ≥ 0`), `∫_N f^* φ = immersionVolume g f hf hinj o` if and only if `f` is a
calibrated immersion for `φ`. -/
theorem IsCalibration.integralTopForm_mpullback_eq_immersionVolume_iff [CompactSpace N]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o ↔
      IsCalibratedImmersion g φ f hf hinj o := by
  refine ⟨fun heq ↦ ?_, fun hcal ↦ hcal.integralTopForm_mpullback_eq⟩
  let gN := g.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace I' y) :=
    Bundle.instIsContinuousRiemannianBundle gN.toContinuousRiemannianMetric
  have : IsContMDiffRiemannianBundle I' 0 E' (fun y : N ↦ TangentSpace I' y) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  set c := calibrationDensity g φ f hf hinj o
  have hc : Continuous c := (hφ.isSmoothForm.contMDiff_calibrationDensity f hf hinj o).continuous
  have hsub_nn (x : N) : 0 ≤ 1 - c x :=
    sub_nonneg.mpr (hφ.calibrationDensity_le_one f hf hinj o x)
  have hdecomp : mpullback I' I f φ = fun x ↦ c x • riemannianVolumeForm o x :=
    funext fun x ↦ (calibrationDensity_smul_riemannianVolumeForm g φ f hf hinj o x).symm
  have hadd := integralTopForm_add_smul_riemannianVolumeForm o (f := fun x ↦ 1 - c x) (g := c)
    (continuous_const.sub hc) hc
  simp only [sub_add_cancel, one_smul] at hadd
  have hzero : integralTopForm o (fun x ↦ (1 - c x) • riemannianVolumeForm o x) = 0 := by
    rw [immersionVolume_def, hdecomp] at heq
    linarith
  have hc_one : ∀ x, c x = 1 := fun x ↦
    (sub_eq_zero.mp ((integralTopForm_smul_riemannianVolumeForm_eq_zero_iff o
      (f := fun y ↦ 1 - c y) (continuous_const.sub hc) hsub_nn).mp hzero x)).symm
  exact (isCalibratedImmersion_iff_calibrationDensity_eq_one g φ f hf hinj o).mpr hc_one

end Immersion

/-! ### Reparametrization along diffeomorphisms -/

section OrientationInjective

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' 1 N']
  {ι : Type*} [Fintype ι]

/-- Precomposing an immersion `f` at `h x` with a differentiable map `h` that preserves orientations
at `x` yields an injective differential `mfderiv I'' I (f ∘ h) x`. -/
theorem Manifold.Orientation.IsOrientationPreservingAt.injective_mfderiv_comp
    {o : Manifold.Orientation I' N ι} {o' : Manifold.Orientation I'' N' ι}
    {f : N → M} {h : N' → N} {x : N'}
    (ho : Manifold.Orientation.IsOrientationPreservingAt o' o h x)
    (hf : MDifferentiableAt I' I f (h x)) (hh : MDifferentiableAt I'' I' h x)
    (hinj : Function.Injective (mfderiv I' I f (h x))) :
    Function.Injective (mfderiv I'' I (f ∘ h) x) := by
  rw [mfderiv_comp x hf hh]
  exact hinj.comp ho.isInvertible_mfderiv.injective

/-- Precomposing an immersion `f` at `h x` with a differentiable map `h` that reverses orientations
at `x` yields an injective differential `mfderiv I'' I (f ∘ h) x`. -/
theorem Manifold.Orientation.IsOrientationReversingAt.injective_mfderiv_comp
    {o : Manifold.Orientation I' N ι} {o' : Manifold.Orientation I'' N' ι}
    {f : N → M} {h : N' → N} {x : N'}
    (ho : Manifold.Orientation.IsOrientationReversingAt o' o h x)
    (hf : MDifferentiableAt I' I f (h x)) (hh : MDifferentiableAt I'' I' h x)
    (hinj : Function.Injective (mfderiv I' I f (h x))) :
    Function.Injective (mfderiv I'' I (f ∘ h) x) := by
  rw [mfderiv_comp x hf hh]
  exact hinj.comp ho.isInvertible_mfderiv.injective

end OrientationInjective

section Reparametrization

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' ∞ N']
  {k : ℕ}

/-- Along any smooth map `h : N' → N` that preserves orientations at every point (in particular
any orientation-preserving smooth diffeomorphism, open embedding, submanifold-with-boundary
inclusion, or covering map), pulling back the Riemannian volume form of `(f^* g, o)` gives the
Riemannian volume form of `((f ∘ h)^* g, o')`. -/
theorem mpullback_riemannianVolumeForm_of_isOrientationPreservingAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    {h : N' → N} (hh : ContMDiff I'' I' ∞ h)
    {o : Manifold.Orientation I' N (Fin k)} {o' : Manifold.Orientation I'' N' (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o' o h x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hinj).toRiemannianMetric⟩
    letI : RiemannianBundle (fun z : N' ↦ TangentSpace I'' z) :=
      ⟨(g.pullback (f ∘ h) ((hf.comp hh).of_le (WithTop.coe_le_coe.mpr le_top))
        (fun x ↦ (ho x).injective_mfderiv_comp
          (hf.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
          (hh.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
          (hinj (h x)))).toRiemannianMetric⟩
    mpullback I'' I' h (riemannianVolumeForm o) = riemannianVolumeForm o' := by
  have hinjh : ∀ x, Function.Injective (mfderiv I'' I (f ∘ h) x) := fun x ↦
    (ho x).injective_mfderiv_comp (hf.mdifferentiableAt (by simp))
      (hh.mdifferentiableAt (by simp)) (hinj (h x))
  let gN := g.pullback f (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hinj
  let gN' := g.pullback (f ∘ h) ((hf.comp hh).of_le (WithTop.coe_le_coe.mpr le_top)) hinjh
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : N' ↦ TangentSpace I'' z) := ⟨gN'.toRiemannianMetric⟩
  funext x
  ext v
  let _ := o.fact_finrank_tangentSpace (h x)
  let _ := o'.fact_finrank_tangentSpace x
  obtain ⟨eL, heL, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).mp (ho x)
  have hinner (u w : TangentSpace I'' x) : ⟪eL u, eL w⟫ = ⟪u, w⟫ := by
    change gN.inner (h x) (eL u) (eL w) = gN'.inner x u w
    have hu : eL u = mfderiv I'' I' h x u := congr($heL u)
    have hw : eL w = mfderiv I'' I' h x w := congr($heL w)
    rw [hu, hw]
    simp only [gN, gN', ContMDiffRiemannianMetric.pullback_inner, Function.comp_apply,
      mfderiv_comp x (hf.mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp)),
      ContinuousLinearMap.comp_apply]
  let e : TangentSpace I'' x ≃ₗᵢ[ℝ] TangentSpace I' (h x) :=
    eL.toLinearEquiv.isometryOfInner hinner
  have he_equiv : e.toLinearEquiv = eL.toLinearEquiv := rfl
  have hcomp : (fun i ↦ mfderiv I'' I' h x (v i)) = e ∘ v := by
    funext i
    exact (congr($heL (v i))).symm
  rw [mpullback_apply, riemannianVolumeForm_apply, riemannianVolumeForm_apply, hcomp, ← hmap,
    ← he_equiv, _root_.Orientation.volumeForm_map]
  congr 1
  funext i
  exact e.symm_apply_apply (v i)

/-- Precomposing a calibrated immersion `f : N → M` with any smooth map `h : N' → N` that preserves
orientations at every point yields a calibrated immersion `f ∘ h : N' → M`. -/
theorem IsCalibratedImmersion.comp_of_isOrientationPreservingAt
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    {f : N → M} {hf : ContMDiff I' I ∞ f} {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)} (hcal : IsCalibratedImmersion g φ f hf hinj o)
    {h : N' → N} (hh : ContMDiff I'' I' ∞ h)
    {o' : Manifold.Orientation I'' N' (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o' o h x) :
    IsCalibratedImmersion g φ (f ∘ h) (hf.comp hh)
      (fun x ↦ (ho x).injective_mfderiv_comp
        (hf.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (hh.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (hinj (h x))) o' := by
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_def,
    ← mpullback_riemannianVolumeForm_of_isOrientationPreservingAt g f hf hinj hh ho,
    mpullback_comp (hh.mdifferentiable (by simp)) (hf.mdifferentiable (by simp))]
  exact congrArg (mpullback I'' I' h) hcal

/-- **Reparametrization invariance of immersion volume** along an orientation-preserving smooth
diffeomorphism `Φ : N' ≃ₘ^∞⟮I'', I'⟯ N`. -/
theorem immersionVolume_comp_diffeomorph_of_isOrientationPreservingAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N)
    {o : Manifold.Orientation I' N (Fin k)} {o' : Manifold.Orientation I'' N' (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o' o Φ x) :
    immersionVolume g (f ∘ Φ) (hf.comp Φ.contMDiff)
      (fun x ↦ (ho x).injective_mfderiv_comp
        (hf.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (Φ.contMDiff.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (hinj (Φ x))) o' =
      immersionVolume g f hf hinj o := by
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def, immersionVolume_def,
    ← mpullback_riemannianVolumeForm_of_isOrientationPreservingAt g f hf hinj Φ.contMDiff ho]
  exact Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
    (fun y _ ↦ ⟨Φ.symm y, Φ.apply_symm_apply y⟩)

/-- Reparametrization invariance of immersion volume along an orientation-reversing smooth
diffeomorphism `Φ : N' ≃ₘ^∞⟮I'', I'⟯ N`. -/
theorem immersionVolume_comp_diffeomorph_of_isOrientationReversingAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N)
    {o : Manifold.Orientation I' N (Fin k)} {o' : Manifold.Orientation I'' N' (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationReversingAt o' o Φ x) :
    immersionVolume g (f ∘ Φ) (hf.comp Φ.contMDiff)
      (fun x ↦ (ho x).injective_mfderiv_comp
        (hf.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (Φ.contMDiff.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (hinj (Φ x))) o' =
      immersionVolume g f hf hinj o := by
  have ho' : ∀ x, Manifold.Orientation.IsOrientationPreservingAt (-o') o Φ x := fun x ↦
    (Manifold.Orientation.isOrientationPreservingAt_neg_left o' o Φ x).mpr (ho x)
  rw [← immersionVolume_neg g (f ∘ Φ) _ _ o']
  exact immersionVolume_comp_diffeomorph_of_isOrientationPreservingAt g f hf hinj Φ ho'

/-- **Reparametrization invariance of calibrated immersions**: precomposing `f` with an
orientation-preserving smooth diffeomorphism `Φ : N' ≃ₘ^∞⟮I'', I'⟯ N` preserves and reflects
`IsCalibratedImmersion`. -/
theorem isCalibratedImmersion_comp_diffeomorph_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N)
    {o : Manifold.Orientation I' N (Fin k)} {o' : Manifold.Orientation I'' N' (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o' o Φ x) :
    IsCalibratedImmersion g φ (f ∘ Φ) (hf.comp Φ.contMDiff)
      (fun x ↦ (ho x).injective_mfderiv_comp
        (hf.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (Φ.contMDiff.mdifferentiableAt (WithTop.coe_ne_zero.mpr WithTop.top_ne_zero))
        (hinj (Φ x))) o' ↔
      IsCalibratedImmersion g φ f hf hinj o := by
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_def, isCalibratedImmersion_def,
    ← mpullback_riemannianVolumeForm_of_isOrientationPreservingAt g f hf hinj Φ.contMDiff ho,
    mpullback_comp (Φ.mdifferentiable (by simp)) (hf.mdifferentiable (by simp))]
  refine ⟨fun h ↦ ?_, fun h ↦ congrArg (mpullback I'' I' Φ) h⟩
  have hsymm := congrArg (mpullback I' I'' Φ.symm) h
  simpa only [mpullback_symm_mpullback (by simp : (∞ : ℕ∞ω) ≠ 0) Φ] using hsymm

end Reparametrization

end TauCeti
