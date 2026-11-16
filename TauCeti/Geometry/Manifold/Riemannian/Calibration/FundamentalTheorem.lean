/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.Orientation.ClosedBall
public import TauCeti.Geometry.Manifold.Riemannian.Calibration.Immersion
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The fundamental theorem of calibrations

Harvey and Lawson's **fundamental theorem of calibrations** asserts that a calibrated submanifold
(or calibrated smooth immersion) minimizes Riemannian volume among all compact oriented competitors
representing the same real homology class (or sharing the period of the calibration `φ`).

Let `(M, g)` be a manifold equipped with a smooth Riemannian metric `g` and a smooth calibration
`φ` of degree `k` (`TauCeti.IsCalibration g φ`), let `f : N → M` be an oriented smooth immersion
calibrated by `φ` (`TauCeti.IsCalibratedImmersion g φ f hf hinj o`), and let `f' : N' → M` be an
oriented smooth immersion of a compact `k`-manifold `N'`:

`Vol(f) = ∫_N f^* φ = ∫_{N'} f'^* φ ≤ Vol(f')`,

with equality `Vol(f) = Vol(f')` if and only if `f'` is itself calibrated by `φ` for the
orientation `o'`. Both the inequality and its equality rigidity hold in every degree `k ≥ 0`
(including `k = 0`) and on arbitrary smooth ambient manifolds `(M, g)` (which need not be
finite-dimensional or boundaryless).

We also prove smooth-homotopy invariance of periods of closed `C¹` `k`-forms in every degree
`k ≥ 0` — both on compact manifolds with boundary when the homotopy is stationary near the
boundary (`TauCeti.integralTopForm_mpullback_eq_of_homotopy_disjoint_boundary`) and on compact
boundaryless manifolds (`TauCeti.integralTopForm_mpullback_eq_of_homotopy`) — via the cylinder
homotopy operator `TauCeti.homotopyOperator` and Stokes' theorem away from the boundary
(`TauCeti.integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary`), deducing homotopic volume
minimization and equality rigidity directly for smooth families of immersions. Finally, we record
three canonical families of calibrated immersions:

* the identity map of any smooth oriented Riemannian manifold `(M, g, o)`, calibrated by
  `TauCeti.riemannianVolumeForm o` (`TauCeti.isCalibratedImmersion_id_riemannianVolumeForm`);
* any linear isometric embedding `e : F →ₗᵢ[ℝ] E` of a `k`-dimensional real inner product space
  into Euclidean space `E`, calibrated by its constant simple unit `k`-form
  (`LinearIsometry.isCalibratedImmersion_const`);
* its restriction `x ↦ e x` to the compact closed unit `k`-ball `Metric.closedBall (0 : F) 1`,
  yielding a compact calibrated flat `k`-disk in `E` that minimizes volume under all smooth
  homotopies stationary near the boundary sphere
  (`LinearIsometry.isCalibratedImmersion_closedBall`,
  `LinearIsometry.immersionVolume_closedBall_le_of_homotopy`).

## Main results

* `TauCeti.IsCalibratedImmersion.immersionVolume_le_of_integralTopForm_mpullback_eq`,
  `TauCeti.IsCalibratedImmersion.immersionVolume_le_of_le_abs_integralTopForm_mpullback`,
  `TauCeti.IsCalibratedImmersion.immersionVolume_eq_iff_of_integralTopForm_mpullback_eq`:
  single-period volume minimization and equality characterization.
* `TauCeti.immersionVolume_le_of_isCalibratedImmersion`,
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion`: the fundamental theorem of calibrations
  in real homology and its equality rigidity.
* `TauCeti.integralTopForm_mpullback_eq_of_homotopy_disjoint_boundary`,
  `TauCeti.integralTopForm_mpullback_eq_of_homotopy`: homotopy invariance of top-form periods of
  closed `C¹` forms in all degrees `k ≥ 0`.
* `TauCeti.immersionVolume_le_of_isCalibratedImmersion_of_homotopy_disjoint_boundary`,
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy_disjoint_boundary`,
  `TauCeti.immersionVolume_le_of_isCalibratedImmersion_of_homotopy`,
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy`: homotopic volume
  minimization with fixed boundary and on closed manifolds.
* `TauCeti.isCalibratedImmersion_id_riemannianVolumeForm`,
  `LinearIsometry.isCalibratedImmersion_const`,
  `LinearIsometry.isCalibratedImmersion_closedBall`,
  `LinearIsometry.immersionVolume_closedBall_le_of_homotopy`: concrete calibrated-immersion
  witnesses.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem II.4.2, p. 59.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998),
  705–747, §2.
* D. D. Joyce, *Riemannian Holonomy Groups and Calibrated Geometry*, Oxford University Press, 2007,
  Theorem 4.1.5.
-/

public section

noncomputable section

open Bundle Module Set exteriorPower
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

/-! ### The fundamental theorem of calibrations and its equality case -/

section FundamentalTheorem

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

/-- **Single-period volume minimization**: if `(N, o, f)` is calibrated by `φ` and a compact
oriented competitor `(N', o', f')` has the same `φ`-period `∫_N f^* φ = ∫_{N'} f'^* φ` (for
instance because `f_* [N] - f'_* [N']` bounds a chain or cobordism on which `dφ = 0` applies by
Stokes' theorem), then `Vol(f) ≤ Vol(f')`. -/
theorem IsCalibratedImmersion.immersionVolume_le_of_integralTopForm_mpullback_eq [CompactSpace N']
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    {f : N → M} {hf : ContMDiff I' I ∞ f} {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) (hφ : IsCalibration g φ)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hperiod : integralTopForm o (mpullback I' I f φ) =
      integralTopForm o' (mpullback I'' I f' φ)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  calc immersionVolume g f hf hinj o
      = integralTopForm o (mpullback I' I f φ) := hcal.integralTopForm_mpullback_eq.symm
    _ = integralTopForm o' (mpullback I'' I f' φ) := hperiod
    _ ≤ immersionVolume g f' hf' hinj' o' :=
        hφ.integralTopForm_mpullback_le_immersionVolume f' hf' hinj' o'

/-- Two-sided single-period bound: if `|∫_{N'} f'^* φ|` is at least `∫_N f^* φ` (for instance when
`∫_{N'} f'^* φ = -∫_N f^* φ` because `f'` represents the opposite homology class), then
`Vol(f) ≤ Vol(f')` still holds. -/
theorem IsCalibratedImmersion.immersionVolume_le_of_le_abs_integralTopForm_mpullback
    [CompactSpace N']
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    {f : N → M} {hf : ContMDiff I' I ∞ f} {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) (hφ : IsCalibration g φ)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hperiod : integralTopForm o (mpullback I' I f φ) ≤
      |integralTopForm o' (mpullback I'' I f' φ)|) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  calc immersionVolume g f hf hinj o
      = integralTopForm o (mpullback I' I f φ) := hcal.integralTopForm_mpullback_eq.symm
    _ ≤ |integralTopForm o' (mpullback I'' I f' φ)| := hperiod
    _ ≤ immersionVolume g f' hf' hinj' o' :=
        hφ.abs_integralTopForm_mpullback_le_immersionVolume f' hf' hinj' o'

/-- **Equality rigidity for single-period competitors**: under `∫_N f^* φ = ∫_{N'} f'^* φ`, a
compact oriented competitor `(N', o', f')` has the same immersion volume as a calibrated immersion
`(N, o, f)` if and only if `f'` is itself calibrated by `φ` with orientation `o'`. -/
theorem IsCalibratedImmersion.immersionVolume_eq_iff_of_integralTopForm_mpullback_eq
    [CompactSpace N']
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}
    {f : N → M} {hf : ContMDiff I' I ∞ f} {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) (hφ : IsCalibration g φ)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hperiod : integralTopForm o (mpullback I' I f φ) =
      integralTopForm o' (mpullback I'' I f' φ)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o' ↔
      IsCalibratedImmersion g φ f' hf' hinj' o' := by
  rw [← hcal.integralTopForm_mpullback_eq, hperiod]
  exact hφ.integralTopForm_mpullback_eq_immersionVolume_iff f' hf' hinj' o'

/-- **The fundamental theorem of calibrations** (Harvey–Lawson 1982, Theorem II.4.2): an oriented
smooth immersion `f : N → M` calibrated by a smooth calibration `φ` has volume at most that of
every compact oriented smooth immersion `f' : N' → M` that pairs with every smooth closed `k`-form
on `M` as `f` does (in particular, every smooth immersion homologous to `f` in real homology). This
holds in every degree `k ≥ 0` and on arbitrary smooth ambient manifolds `(M, g)`. -/
theorem immersionVolume_le_of_isCalibratedImmersion [CompactSpace N']
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  hcal.immersionVolume_le_of_integralTopForm_mpullback_eq hφ f' hf' hinj' o'
    (hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero)

/-- **Equality in the fundamental theorem of calibrations**: under the real-homology period
hypothesis `hhom`, a compact oriented smooth immersion `f' : N' → M` achieves equality
`immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o'` if and only if `f'` is itself
calibrated by `φ` for the orientation `o'`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion [CompactSpace N']
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o' ↔
      IsCalibratedImmersion g φ f' hf' hinj' o' :=
  hcal.immersionVolume_eq_iff_of_integralTopForm_mpullback_eq hφ f' hf' hinj' o'
    (hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero)

end FundamentalTheorem

/-! ### Homotopy invariance of closed-form periods and homotopic volume minimization -/

section Homotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] [CompactSpace N] [T2Space N]
  {k : ℕ}

/-- **Homotopy invariance of top-form periods away from the boundary.** Let `N` be a compact
Hausdorff smooth `k`-manifold (possibly with boundary or corners), `φ` a closed `C¹` `k`-form on a
`C²` manifold `M`, and `Φ : N × [0, 1] → M` a `C²` homotopy that is stationary on a neighborhood
of `I'.boundary N`. Then `∫_N Φ(·, 0)^* φ = ∫_N Φ(·, 1)^* φ` in every degree `k ≥ 0`. -/
theorem integralTopForm_mpullback_eq_of_homotopy_disjoint_boundary
    (o : Manifold.Orientation I' N (Fin k))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I (1 : ℕ∞) φ) (hclosed : mextDeriv φ = 0)
    {Φ : N × Icc (0 : ℝ) 1 → M} (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I 2 Φ)
    (hbdry : Disjoint (closure {x : N | ∃ t : Icc (0 : ℝ) 1, Φ (x, t) ≠ Φ (x, 0)})
      (I'.boundary N)) :
    integralTopForm o (mpullback I' I (fun x ↦ Φ (x, 0)) φ) =
      integralTopForm o (mpullback I' I (fun x ↦ Φ (x, 1)) φ) := by
  cases k with
  | zero =>
    have hφ' : IsSmoothForm I (1 : ℕ∞) (RoughForm.ofFunction I fun z ↦ φ z 0) := by
      rwa [← RoughForm.eq_ofFunction φ]
    have hcl' : mextDeriv (RoughForm.ofFunction I fun z ↦ φ z 0) = 0 := by
      rwa [← RoughForm.eq_ofFunction φ]
    have hloc : IsLocallyConstant (fun z : M ↦ φ z 0) :=
      (mextDeriv_ofFunction_eq_zero_iff
        ((isSmoothForm_ofFunction_iff.mp hφ').mdifferentiable (by simp))).mp hcl'
    have : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
    have heq : mpullback I' I (fun x ↦ Φ (x, 0)) φ = mpullback I' I (fun x ↦ Φ (x, 1)) φ := by
      funext x
      ext v
      rw [mpullback_apply, mpullback_apply,
        Subsingleton.elim (fun i ↦ mfderiv I' I (fun x ↦ Φ (x, 0)) x (v i)) (0 : Fin 0 → E),
        Subsingleton.elim (fun i ↦ mfderiv I' I (fun x ↦ Φ (x, 1)) x (v i)) (0 : Fin 0 → E)]
      exact (hloc.comp_continuous (hΦ.continuous.comp
        (continuous_const.prodMk continuous_id))).apply_eq_of_preconnectedSpace 0 1
    rw [heq]
  | succ n =>
    have : IsManifold I' ((1 : ℕ∞) + 1 : WithTop ℕ∞) N :=
      IsManifold.of_le (n := ∞) (by simp)
    set ψ := mpullback (I'.prod (𝓡∂ 1)) I Φ φ
    have hψ : IsSmoothForm (I'.prod (𝓡∂ 1)) (1 : ℕ∞) ψ := hφ.mpullback (hΦ.of_le (by norm_num))
    have hclψ : mextDeriv ψ = 0 := hφ.mextDeriv_mpullback_eq_zero hclosed hΦ
    have hL : IsSmoothForm I' (1 : ℕ∞) (homotopyOperator ψ) := hψ.homotopyOperator
    have hsupp : _root_.tsupport (α := E' [⋀^Fin n]→L[ℝ] ℝ) (homotopyOperator ψ) ⊆
        closure {x : N | ∃ t : Icc (0 : ℝ) 1, Φ (x, t) ≠ Φ (x, 0)} := by
      refine closure_mono fun x hx ↦ ?_
      by_contra hstat
      exact hx (homotopyOperator_mpullback_apply_eq_zero
        (fun t ↦ of_not_not fun hne ↦ hstat ⟨t, hne⟩) φ)
    have hzero : integralTopForm o (mextDeriv (homotopyOperator ψ)) = 0 :=
      integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary o hL
        (_root_.isClosed_tsupport _).isCompact (hbdry.mono_left hsupp)
    have hslice (c : Icc (0 : ℝ) 1) :
        mpullback I' (I'.prod (𝓡∂ 1)) (fun x ↦ (x, c)) ψ =
          mpullback I' I (fun x ↦ Φ (x, c)) φ :=
      (mpullback_comp ((contMDiff_id.prodMk contMDiff_const :
        ContMDiff I' (I'.prod (𝓡∂ 1)) ∞ fun x : N ↦ (x, c)).mdifferentiable (by simp))
        (hΦ.mdifferentiable (by simp)) φ).symm
    have hdL : mextDeriv (homotopyOperator ψ) =
        mpullback I' I (fun x ↦ Φ (x, 1)) φ - mpullback I' I (fun x ↦ Φ (x, 0)) φ := by
      rw [← hslice 1, ← hslice 0]
      exact funext (mextDeriv_homotopyOperator hψ hclψ)
    have hφ₀ : IsSmoothForm I' 0 (mpullback I' I (fun x ↦ Φ (x, 0)) φ) :=
      (hφ.of_le (by simp)).mpullback
        ((hΦ.comp (contMDiff_id.prodMk contMDiff_const)).of_le (by norm_num))
    have hsplit : mpullback I' I (fun x ↦ Φ (x, 1)) φ =
        mextDeriv (homotopyOperator ψ) + mpullback I' I (fun x ↦ Φ (x, 0)) φ := by
      rw [hdL, sub_add_cancel]
    rw [hsplit, integralTopForm_add_of_compactSpace o hL.continuous_mextDeriv hφ₀, hzero, zero_add]

/-- **Homotopy invariance of top-form periods on closed manifolds.** On a compact boundaryless
Hausdorff smooth `k`-manifold `N`, every `C²` homotopy `Φ : N × [0, 1] → M` preserves the top-form
period of every closed `C¹` `k`-form `φ` on `M`, in every degree `k ≥ 0`. -/
theorem integralTopForm_mpullback_eq_of_homotopy [BoundarylessManifold I' N]
    (o : Manifold.Orientation I' N (Fin k))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I (1 : ℕ∞) φ) (hclosed : mextDeriv φ = 0)
    {Φ : N × Icc (0 : ℝ) 1 → M} (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I 2 Φ) :
    integralTopForm o (mpullback I' I (fun x ↦ Φ (x, 0)) φ) =
      integralTopForm o (mpullback I' I (fun x ↦ Φ (x, 1)) φ) :=
  integralTopForm_mpullback_eq_of_homotopy_disjoint_boundary o hφ hclosed hΦ
    (by simp only [ModelWithCorners.Boundaryless.boundary_eq_empty, disjoint_empty])

/-- **Fixed-boundary homotopic volume minimization**: on a compact Hausdorff smooth `k`-manifold
`N` (possibly with boundary or corners), a calibrated smooth immersion `f : N → M` minimizes
`immersionVolume` against every smooth immersion `f' : N → M` joined to `f` by a `C²` homotopy
stationary near `I'.boundary N`. -/
theorem immersionVolume_le_of_isCalibratedImmersion_of_homotopy_disjoint_boundary
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N → M) (hf' : ContMDiff I' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
    {Φ : N × Icc (0 : ℝ) 1 → M} (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I 2 Φ)
    (hΦ₀ : ∀ x, Φ (x, 0) = f x) (hΦ₁ : ∀ x, Φ (x, 1) = f' x)
    (hbdry : Disjoint (closure {x : N | ∃ t : Icc (0 : ℝ) 1, Φ (x, t) ≠ Φ (x, 0)})
      (I'.boundary N)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o := by
  refine hcal.immersionVolume_le_of_integralTopForm_mpullback_eq hφ f' hf' hinj' o ?_
  rw [← funext hΦ₀, ← funext hΦ₁]
  exact integralTopForm_mpullback_eq_of_homotopy_disjoint_boundary o
    (hφ.isSmoothForm.of_le (by simp)) hφ.mextDeriv_eq_zero hΦ hbdry

/-- Equality in fixed-boundary homotopic volume minimization holds if and only if `f'` is itself
calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy_disjoint_boundary
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N → M) (hf' : ContMDiff I' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
    {Φ : N × Icc (0 : ℝ) 1 → M} (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I 2 Φ)
    (hΦ₀ : ∀ x, Φ (x, 0) = f x) (hΦ₁ : ∀ x, Φ (x, 1) = f' x)
    (hbdry : Disjoint (closure {x : N | ∃ t : Icc (0 : ℝ) 1, Φ (x, t) ≠ Φ (x, 0)})
      (I'.boundary N)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o ↔
      IsCalibratedImmersion g φ f' hf' hinj' o := by
  refine hcal.immersionVolume_eq_iff_of_integralTopForm_mpullback_eq hφ f' hf' hinj' o ?_
  rw [← funext hΦ₀, ← funext hΦ₁]
  exact integralTopForm_mpullback_eq_of_homotopy_disjoint_boundary o
    (hφ.isSmoothForm.of_le (by simp)) hφ.mextDeriv_eq_zero hΦ hbdry

/-- **Homotopic volume minimization on closed manifolds**: on a compact boundaryless Hausdorff
smooth `k`-manifold `N`, a calibrated smooth immersion `f : N → M` has volume at most that of
every smooth immersion `f' : N → M` joined to `f` by a `C²` homotopy, in every degree `k ≥ 0`. -/
theorem immersionVolume_le_of_isCalibratedImmersion_of_homotopy [BoundarylessManifold I' N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N → M) (hf' : ContMDiff I' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
    {Φ : N × Icc (0 : ℝ) 1 → M} (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I 2 Φ)
    (hΦ₀ : ∀ x, Φ (x, 0) = f x) (hΦ₁ : ∀ x, Φ (x, 1) = f' x) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o :=
  immersionVolume_le_of_isCalibratedImmersion_of_homotopy_disjoint_boundary g φ hφ f hf hinj o
    hcal f' hf' hinj' hΦ hΦ₀ hΦ₁
    (by simp only [ModelWithCorners.Boundaryless.boundary_eq_empty, disjoint_empty])

/-- Equality in homotopic volume minimization on a closed manifold holds if and only if `f'` is
itself calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy [BoundarylessManifold I' N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N → M) (hf' : ContMDiff I' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
    {Φ : N × Icc (0 : ℝ) 1 → M} (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I 2 Φ)
    (hΦ₀ : ∀ x, Φ (x, 0) = f x) (hΦ₁ : ∀ x, Φ (x, 1) = f' x) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o ↔
      IsCalibratedImmersion g φ f' hf' hinj' o :=
  immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy_disjoint_boundary g φ hφ f hf hinj o
    hcal f' hf' hinj' hΦ hΦ₀ hΦ₁
    (by simp only [ModelWithCorners.Boundaryless.boundary_eq_empty, disjoint_empty])

end Homotopy

/-! ### Canonical calibrated immersions -/

section Examples

/-- On any smooth oriented Riemannian `m`-manifold `(M, g, o)`, the identity map `id : M → M` is a
calibrated immersion for the top-degree calibration `riemannianVolumeForm o`. -/
theorem isCalibratedImmersion_id_riemannianVolumeForm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {m : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsCalibratedImmersion g (riemannianVolumeForm o) id contMDiff_id
      (fun x ↦ (mfderiv_id (I := I) (x := x)).symm ▸ Function.injective_id) o := by
  have hinj : ∀ x : M, Function.Injective (mfderiv I I id x) :=
    fun x ↦ (mfderiv_id (I := I) (x := x)).symm ▸ Function.injective_id
  have hg : g.pullback id (by simpa using contMDiff_id) hinj = g := by
    ext x v w
    simp
  rw [isCalibratedImmersion_def, hg, mpullback_id]

end Examples

end TauCeti

/-! ### Calibrated planes and disks in Euclidean space -/

section LinearIsometryMFDeriv

open TauCeti

variable {F E : Type*} [NormedAddCommGroup F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The manifold derivative of a real linear isometry `e : F →ₗᵢ[ℝ] E` at any point `x` is
`e.toContinuousLinearMap`. -/
theorem LinearIsometry.mfderiv_eq [NormedSpace ℝ F] (e : F →ₗᵢ[ℝ] E) (x : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e x = e.toContinuousLinearMap :=
  (e.toContinuousLinearMap.hasFDerivAt :
    HasFDerivAt e e.toContinuousLinearMap x).hasMFDerivAt.mfderiv

/-- Every real linear isometry `e : F →ₗᵢ[ℝ] E` has injective manifold derivative at every point. -/
theorem LinearIsometry.injective_mfderiv [NormedSpace ℝ F] (e : F →ₗᵢ[ℝ] E) (x : F) :
    Function.Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e x) := by
  rw [e.mfderiv_eq x]
  exact e.injective

/-- Restricting a linear isometric embedding `e : F →ₗᵢ[ℝ] E` in positive dimension (`[NeZero k]`)
to the closed unit `k`-ball gives an immersion with injective manifold derivative at every point,
including the boundary sphere. -/
theorem LinearIsometry.injective_mfderiv_comp_subtypeVal_closedBall [InnerProductSpace ℝ F]
    {k : ℕ} [NeZero k] [Fact (finrank ℝ F = k)] (e : F →ₗᵢ[ℝ] E)
    (x : Metric.closedBall (0 : F) 1) :
    Function.Injective (mfderiv (𝓡∂ k) 𝓘(ℝ, E) (e ∘ Subtype.val) x) := by
  have he : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ e := e.contDiff.contMDiff
  rw [mfderiv_comp x (he.mdifferentiableAt (by simp))
    ((contMDiff_subtypeVal_closedBall (n := k) (k := ∞)).mdifferentiableAt (by simp)),
    e.mfderiv_eq]
  exact e.injective.comp (injective_mfderiv_subtypeVal_closedBall (n := k) x)

end LinearIsometryMFDeriv

section EuclideanPlanes

open TauCeti

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}

/-- Every linear isometric embedding `e : F →ₗᵢ[ℝ] E` of an oriented `k`-dimensional real inner
product space `F` (oriented by an orthonormal basis `b`) into a finite-dimensional real inner
product space `E` is a calibrated immersion for the flat Euclidean metric and the constant simple
calibration `fun _ ↦ alternatingFormEquiv E k (e (b 0) ∧ ⋯ ∧ e (b (k - 1)))`, in every degree
`k ≥ 0`. -/
theorem LinearIsometry.isCalibratedImmersion_const [Fact (finrank ℝ F = k)]
    (e : F →ₗᵢ[ℝ] E) (b : OrthonormalBasis (Fin k) ℝ F) :
    IsCalibratedImmersion ((riemannianMetricVectorSpace E).ofLE le_top)
      (fun _ ↦ alternatingFormEquiv E k (ιMulti ℝ k (e ∘ b)))
      e e.contDiff.contMDiff e.injective_mfderiv
      (Manifold.Orientation.model (I := 𝓘(ℝ, F)) b.toBasis.orientation
        (by simp [(Fact.out : finrank ℝ F = k)])) := by
  set gE := (riemannianMetricVectorSpace E).ofLE (m := ∞) le_top
  set φ : RoughForm 𝓘(ℝ, E) E ℝ k :=
    fun _ ↦ alternatingFormEquiv E k (ιMulti ℝ k (e ∘ b))
  set o := Manifold.Orientation.model (I := 𝓘(ℝ, F)) b.toBasis.orientation
    (by simp [(Fact.out : finrank ℝ F = k)])
  rw [isCalibratedImmersion_iff_forall]
  let gF := gE.pullback e (by simpa using (e.contDiff (n := ∞)).contMDiff) e.injective_mfderiv
  let _ : RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) := ⟨gF.toRiemannianMetric⟩
  intro x
  have hderiv : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e x = e.toContinuousLinearMap := e.mfderiv_eq x
  let isoL : F ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, F) x := LinearEquiv.refl ℝ F
  have hinner (u w : F) : ⟪isoL u, isoL w⟫ = ⟪u, w⟫ := by
    change gF.inner x (isoL u) (isoL w) = ⟪u, w⟫
    rw [ContMDiffRiemannianMetric.pullback_inner, hderiv, ContMDiffRiemannianMetric.ofLE_inner]
    exact e.inner_map_map u w
  let iso : F ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ, F) x := isoL.isometryOfInner hinner
  let bx : OrthonormalBasis (Fin k) ℝ (TangentSpace 𝓘(ℝ, F) x) := b.map iso
  have hbx_orient : bx.toBasis.orientation = o.orientationAt x := by
    have hiso : iso.toLinearEquiv = isoL := rfl
    rw [b.toBasis_map iso, hiso, Basis.orientation_map, Manifold.Orientation.orientationAt_model]
    exact congrArg (· b.toBasis.orientation) (_root_.Orientation.map_refl (R := ℝ) (M := F) (Fin k))
  refine eq_riemannianVolumeForm_of_apply_orthonormal o x
    (mpullback 𝓘(ℝ, F) 𝓘(ℝ, E) e φ x) bx hbx_orient ?_
  rw [mpullback_apply]
  have hframe : (fun i ↦ mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e x (bx i)) = e ∘ b := by
    funext i
    rw [hderiv]
    exact congrArg (⇑e) ((OrthonormalBasis.map_apply b iso i).trans rfl)
  rw [hframe]
  exact (isCalibratedFrame_alternatingFormEquiv_ιMulti_self
    (e.orthonormal_comp_iff.mpr b.orthonormal)).apply_eq_one

/-- Restricting a linear isometric embedding `e : F →ₗᵢ[ℝ] E` in positive dimension (`[NeZero k]`)
to the compact closed unit `k`-ball `Metric.closedBall (0 : F) 1` produces a compact calibrated
flat `k`-disk in Euclidean space `E`. -/
theorem LinearIsometry.isCalibratedImmersion_closedBall [NeZero k] [Fact (finrank ℝ F = k)]
    (e : F →ₗᵢ[ℝ] E) (b : OrthonormalBasis (Fin k) ℝ F) :
    IsCalibratedImmersion ((riemannianMetricVectorSpace E).ofLE le_top)
      (fun _ ↦ alternatingFormEquiv E k (ιMulti ℝ k (e ∘ b)))
      (e ∘ Subtype.val)
      (e.contDiff.contMDiff.comp (contMDiff_subtypeVal_closedBall (n := k) (k := ∞)))
      e.injective_mfderiv_comp_subtypeVal_closedBall
      (Manifold.Orientation.closedBall b.toBasis.orientation) := by
  have ho : ∀ x : Metric.closedBall (0 : F) 1,
      Manifold.Orientation.IsOrientationPreservingAt
        (Manifold.Orientation.closedBall b.toBasis.orientation)
        (Manifold.Orientation.model (I := 𝓘(ℝ, F)) b.toBasis.orientation
          (by simp [(Fact.out : finrank ℝ F = k)]))
        Subtype.val x := fun x ↦ by
    refine (Manifold.Orientation.isOrientationPreservingAt_iff _ _ Subtype.val x).mpr
      ⟨subtypeValClosedBallTangentEquiv (n := k) x,
        subtypeValClosedBallTangentEquiv_toContinuousLinearMap (n := k) x, ?_⟩
    rw [Manifold.Orientation.orientationAt_model]
    exact Manifold.Orientation.map_orientationAt_closedBall b.toBasis.orientation x
  exact (e.isCalibratedImmersion_const b).comp_of_isOrientationPreservingAt
    (contMDiff_subtypeVal_closedBall (n := k) (k := ∞)) ho

/-- **Volume minimization of flat `k`-disks in Euclidean space**: for any linear isometric embedding
`e : F →ₗᵢ[ℝ] E` in positive dimension (`[NeZero k]`), the flat unit `k`-disk
`e ∘ Subtype.val : Metric.closedBall (0 : F) 1 → E` minimizes `immersionVolume` among all smooth
immersions `f' : Metric.closedBall (0 : F) 1 → E` joined to it by a `C²` homotopy stationary near
the boundary sphere `S^{k - 1}`. -/
theorem LinearIsometry.immersionVolume_closedBall_le_of_homotopy [NeZero k]
    [Fact (finrank ℝ F = k)] (e : F →ₗᵢ[ℝ] E) (b : OrthonormalBasis (Fin k) ℝ F)
    (f' : Metric.closedBall (0 : F) 1 → E) (hf' : ContMDiff (𝓡∂ k) 𝓘(ℝ, E) ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv (𝓡∂ k) 𝓘(ℝ, E) f' x))
    {Φ : Metric.closedBall (0 : F) 1 × Icc (0 : ℝ) 1 → E}
    (hΦ : ContMDiff ((𝓡∂ k).prod (𝓡∂ 1)) 𝓘(ℝ, E) 2 Φ)
    (hΦ₀ : ∀ x, Φ (x, 0) = e x) (hΦ₁ : ∀ x, Φ (x, 1) = f' x)
    (hbdry : Disjoint
      (closure {x : Metric.closedBall (0 : F) 1 | ∃ t : Icc (0 : ℝ) 1, Φ (x, t) ≠ Φ (x, 0)})
      ((𝓡∂ k).boundary (Metric.closedBall (0 : F) 1))) :
    immersionVolume ((riemannianMetricVectorSpace E).ofLE le_top)
      (e ∘ Subtype.val)
      (e.contDiff.contMDiff.comp (contMDiff_subtypeVal_closedBall (n := k) (k := ∞)))
      e.injective_mfderiv_comp_subtypeVal_closedBall
      (Manifold.Orientation.closedBall b.toBasis.orientation) ≤
      immersionVolume ((riemannianMetricVectorSpace E).ofLE le_top) f' hf' hinj'
        (Manifold.Orientation.closedBall b.toBasis.orientation) := by
  have : CompactSpace (Metric.closedBall (0 : F) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall (x := (0 : F)) (r := 1))
  exact immersionVolume_le_of_isCalibratedImmersion_of_homotopy_disjoint_boundary
    ((riemannianMetricVectorSpace E).ofLE le_top)
    (fun _ ↦ alternatingFormEquiv E k (ιMulti ℝ k (e ∘ b)))
    (isCalibration_const_alternatingFormEquiv_ιMulti (e.orthonormal_comp_iff.mpr
      b.orthonormal))
    _ _ _ _ (e.isCalibratedImmersion_closedBall b) f' hf' hinj' hΦ hΦ₀ hΦ₁ hbdry

end EuclideanPlanes
