/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.SmallBall
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Scaling
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Norm
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Normalized initial metrics

Following Morgan–Tian (Definition 4.10), a smooth Riemannian metric `g` on a smooth manifold `M`
of real dimension `n = finrank ℝ E` is a *normalized initial metric*
(`Bundle.ContMDiffRiemannianMetric.IsNormalizedInitialMetric`) if at every point `x : M`:

1. **Curvature tensor bound:** `|Rm_g(x)| ≤ 1`, where `|Rm|` is the Hilbert–Schmidt norm
   `√(∑ᵢ ∑ⱼ ∑ₖ ‖R(eᵢ, eⱼ) eₖ‖²) = 2 ‖Rop‖_F`.
2. **Curvature operator lower bound:** `⟪Rop_g(x) z, z⟫ ≥ -‖z‖²` for all `z : ⋀² T_x M`
   (equivalently, the smallest eigenvalue `ν` of the curvature operator satisfies `ν ≥ -1`).
3. **Uniform small-ball non-collapsing:** for every radius `0 < r ≤ 1`,
   `vol_g(B_g(x, r)) ≥ (1 / 2) ω_n r ^ n`, where `ω_n` is the volume of the Euclidean unit ball in
   `ℝ^n` (so in dimension three, `(1 / 2) ω₃ r³ = (2 / 3) π r³`).

With the Hilbert–Schmidt normalization `|Rm| = 2 ‖Rop‖_F`, condition (1) automatically implies
`|⟪Rop z, z⟫| ≤ (1 / 2) ‖z‖²` and hence condition (2) (`of_curvatureTensorNorm_le_one`), as well
as `|K(u, v)| ≤ 1 / 2`, `|μ| ≤ 1 / 2` for every eigenvalue `μ` of `Rop`, and
`|Scal| ≤ √(n (n - 1) / 2)`. Condition (2) directly yields `-(n (n - 1)) ≤ Scal`; in dimension
three this gives `-6 ≤ Scal`, matching the initial hypothesis of
`TauCeti.neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin_of_neg_six_le`.

On any closed (compact, boundaryless, Hausdorff) smooth manifold `M`, any smooth metric `g` can be
normalized by a sufficiently large constant positive rescaling `c g`
(`exists_pos_forall_isNormalizedInitialMetric_rescale_const`): curvature scales down as `c⁻¹` while
geodesic balls of radius `r ≤ 1` correspond to `g`-balls of radius `r / √c`, where the uniform
small-ball volume estimate (`TauCeti.Manifold.exists_pos_forall_riemannianVolume_ball_bounds`)
forces `vol_g(B_g(x, s)) ≥ (1 / 2) ω_n s ^ n`. Combining this with partition-of-unity metric
existence (`TauCeti.nonempty_contMDiffRiemannianMetric`) yields a normalized initial metric on
every closed smooth manifold (`TauCeti.exists_isNormalizedInitialMetric`).

The file also establishes exact scaling and diffeomorphism-pullback laws for every condition, and
verifies three geometric checks:

* **Upward scaling:** scaling a normalized metric up (`1 ≤ c`) preserves the all-small-radii volume
  lower bound and the full `IsNormalizedInitialMetric` predicate.
* **Round spheres:** on `Sⁿ`, `|Rm| = √(2 n (n - 1))` (`2 √3` on `S³`), so rescaling by any
  `c ≥ √(2 n (n - 1))` satisfies the curvature bounds (with `Rop ≥ 0`), and a sufficiently large
  rescaling is a full normalized initial metric.
* **Collapsed flat tori:** on any nonempty compact flat manifold of dimension `n ≥ 1` — and in
  particular on the flat three-torus `T³ = S¹ × (S¹ × S¹)` — all sufficiently small rescalings
  `0 < c < c₀` satisfy both curvature bounds (`|Rm| = 0 ≤ 1`, `Rop = 0 ≥ -Id`) yet fail the
  normalized volume lower bound at radius `1`.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.IsNormalizedInitialMetric`: the normalized initial metric
  conditions (curvature norm bound, curvature operator lower bound, and small-ball volume bound).
* `TauCeti.flatThreeTorusMetric`: the flat product metric on `S¹ × (S¹ × S¹)`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.IsNormalizedInitialMetric.of_curvatureTensorNorm_le_one`:
  smart constructor discharging the curvature-operator lower bound from `|Rm| ≤ 1`.
* `Bundle.ContMDiffRiemannianMetric.IsNormalizedInitialMetric.neg_six_le_scalarCurvature`:
  in dimension three, a normalized initial metric satisfies `-6 ≤ Scal`.
* `Bundle.ContMDiffRiemannianMetric.IsNormalizedInitialMetric.volume_ball_ge_three`:
  in dimension three, `vol(B(x, r)) ≥ (2 / 3) π r³` for `0 < r ≤ 1`.
* `Bundle.ContMDiffRiemannianMetric.isNormalizedInitialMetric_rescale_const_iff`: exact scaling
  characterization under constant positive rescaling `c g`.
* `Bundle.ContMDiffRiemannianMetric.IsNormalizedInitialMetric.volume_ball_ge_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.IsNormalizedInitialMetric.rescale_const`: scaling up (`1 ≤ c`)
  preserves the small-ball volume bound and normalization.
* `Bundle.ContMDiffRiemannianMetric.isNormalizedInitialMetric_pullback_iff`: invariance under
  pullback along smooth diffeomorphisms.
* `Bundle.ContMDiffRiemannianMetric.exists_pos_forall_isNormalizedInitialMetric_rescale_const`:
  on a closed manifold, all sufficiently large constant rescalings of any smooth metric are
  normalized.
* `TauCeti.exists_isNormalizedInitialMetric` and `TauCeti.exists_isNormalizedInitialMetric_three`:
  every closed smooth manifold (and closed smooth three-manifold) admits a normalized initial
  metric.
* `TauCeti.curvatureTensorNorm_sphereRoundMetric_ofLE`,
  `TauCeti.sphereRoundMetric_ofLE_rescale_curvature_bounds`, and
  `TauCeti.exists_pos_isNormalizedInitialMetric_sphereRoundMetric_rescale`: round sphere checks.
* `Bundle.ContMDiffRiemannianMetric.exists_pos_forall_lt_not_isNormalizedInitialMetric_of_flat` and
  `TauCeti.exists_pos_flatThreeTorusMetric_curvature_le_and_not_isNormalizedInitialMetric`:
  collapsed flat manifold and flat three-torus counterexamples showing curvature bounds alone do
  not imply the normalized volume bound.

## References

* J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 4.10 (normalized initial metrics).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold MeasureTheory Module Metric Set
open scoped ContDiff ENNReal Manifold RealInnerProductSpace

private theorem volume_ball_euclideanSpace_of_eq_three {k : ℕ} (hk : k = 3) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) =
      ENNReal.ofReal (4 / 3 * Real.pi) := by
  subst hk
  simp only [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  congr 1
  ring

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Definition

/-- **Normalized initial metric** (Morgan–Tian, Definition 4.10).

A smooth Riemannian metric `g` on a Hausdorff Lindelöf smooth manifold `M` of dimension
`n = finrank ℝ E` is normalized if at every point `x : M`:
1. `|Rm_g(x)| ≤ 1`,
2. the curvature operator satisfies `-(‖z‖²) ≤ ⟪Rop_g(x) z, z⟫` for every bivector
   `z : ⋀² T_x M` (minimum eigenvalue `ν ≥ -1`), and
3. every geodesic ball `B_g(x, r)` of radius `0 < r ≤ 1` satisfies
   `vol_g(B_g(x, r)) ≥ (1 / 2) ω_n r ^ n`, where `ω_n` is the Euclidean unit-ball volume in `ℝ^n`.
-/
structure IsNormalizedInitialMetric [T2Space M] [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) : Prop where
  /-- Pointwise Hilbert–Schmidt curvature tensor norm bound `|Rm| ≤ 1`. -/
  curvatureTensorNorm_le_one : ∀ x : M, g.curvatureTensorNorm x ≤ 1
  /-- Pointwise curvature-operator lower bound `Rop ≥ -Id` (`ν ≥ -1`). -/
  neg_le_inner_curvatureEndomorphism : ∀ x : M,
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      -(‖z‖ ^ 2) ≤
        ⟪(leviCivitaConnection I M).curvatureEndomorphism
          (isMetricCompatible_leviCivitaConnection I) x z, z⟫
  /-- Uniform small-ball volume lower bound `vol(B(x, r)) ≥ (1 / 2) ω_n r ^ n` for `0 < r ≤ 1`. -/
  volume_ball_ge : ∀ x : M, ∀ {r : ℝ}, 0 < r → r ≤ 1 →
    ENNReal.ofReal ((1 / 2 : ℝ) * r ^ finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
      TauCeti.riemannianVolume I (TauCeti.WithMetric g)
        {y | Manifold.riemannianEDist I (TauCeti.WithMetric.toWithMetric g x) y <
          ENNReal.ofReal r}

variable [T2Space M] [LindelofSpace M]
  {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- **Smart constructor for `IsNormalizedInitialMetric`.** Under the Hilbert–Schmidt convention
`|Rm| = 2 ‖Rop‖_F`, the bound `|Rm| ≤ 1` automatically forces `⟪Rop z, z⟫ ≥ -(1 / 2) ‖z‖² ≥ -‖z‖²`,
so the curvature-operator lower bound need not be verified separately. -/
theorem IsNormalizedInitialMetric.of_curvatureTensorNorm_le_one
    (hRm : ∀ x : M, g.curvatureTensorNorm x ≤ 1)
    (hvol : ∀ x : M, ∀ {r : ℝ}, 0 < r → r ≤ 1 →
      ENNReal.ofReal ((1 / 2 : ℝ) * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
        TauCeti.riemannianVolume I (TauCeti.WithMetric g)
          {y | Manifold.riemannianEDist I (TauCeti.WithMetric.toWithMetric g x) y <
            ENNReal.ofReal r}) :
    g.IsNormalizedInitialMetric where
  curvatureTensorNorm_le_one := hRm
  neg_le_inner_curvatureEndomorphism x := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    have _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle g
    intro z
    have h1 := (leviCivitaConnection I M)
      |>.neg_half_curvatureTensorNorm_le_inner_curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection I) x z
    have h2 : (leviCivitaConnection I M).curvatureTensorNorm x ≤ 1 := by
      rw [← g.curvatureTensorNorm_eq_curvatureTensorNorm_leviCivitaConnection rfl x]
      exact hRm x
    nlinarith [sq_nonneg ‖z‖]
  volume_ball_ge := hvol

/-- From `|Rm| ≤ 1`, a normalized initial metric satisfies the sharper curvature-operator lower
bound `⟪Rop z, z⟫ ≥ -(1 / 2) ‖z‖²`. -/
theorem IsNormalizedInitialMetric.neg_half_le_inner_curvatureEndomorphism
    (hg : g.IsNormalizedInitialMetric) (x : M) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      -(1 / 2 : ℝ) * ‖z‖ ^ 2 ≤
        ⟪(leviCivitaConnection I M).curvatureEndomorphism
          (isMetricCompatible_leviCivitaConnection I) x z, z⟫ := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  intro z
  have h1 := (leviCivitaConnection I M)
    |>.neg_half_curvatureTensorNorm_le_inner_curvatureEndomorphism
      (isMetricCompatible_leviCivitaConnection I) x z
  have h2 : (leviCivitaConnection I M).curvatureTensorNorm x ≤ 1 := by
    rw [← g.curvatureTensorNorm_eq_curvatureTensorNorm_leviCivitaConnection rfl x]
    exact hg.curvatureTensorNorm_le_one x
  nlinarith [sq_nonneg ‖z‖]

/-- Every normalized initial metric satisfies `Rop_g(x) ≥ -(1 / 2) • Id`. -/
theorem IsNormalizedInitialMetric.hasCurvatureOperatorLowerBoundAt_neg_half
    (hg : g.IsNormalizedInitialMetric) (x : M) :
    g.HasCurvatureOperatorLowerBoundAt x (-(1 / 2 : ℝ)) := by
  simpa using g.hasCurvatureOperatorLowerBoundAt_of_curvatureTensorNorm_le
    (hg.curvatureTensorNorm_le_one x)

/-- Every normalized initial metric satisfies `Rop_g(x) ≥ -Id` (`ν ≥ -1`). -/
theorem IsNormalizedInitialMetric.hasCurvatureOperatorLowerBoundAt
    (hg : g.IsNormalizedInitialMetric) (x : M) :
    g.HasCurvatureOperatorLowerBoundAt x (-1) :=
  (hg.hasCurvatureOperatorLowerBoundAt_neg_half x).mono (by norm_num)

/-- Every eigenvalue `μ` of the curvature endomorphism of a normalized initial metric satisfies
`|μ| ≤ 1 / 2`. -/
theorem IsNormalizedInitialMetric.abs_le_half_of_hasEigenvalue
    (hg : g.IsNormalizedInitialMetric) {x : M} {μ : ℝ}
    (hμ : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ((leviCivitaConnection I M).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection I) x).HasEigenvalue μ)) :
    |μ| ≤ 1 / 2 := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have h1 := (leviCivitaConnection I M).abs_le_half_curvatureTensorNorm_of_hasEigenvalue
    (isMetricCompatible_leviCivitaConnection I) hμ
  have h2 : (leviCivitaConnection I M).curvatureTensorNorm x ≤ 1 := by
    rw [← g.curvatureTensorNorm_eq_curvatureTensorNorm_leviCivitaConnection rfl x]
    exact hg.curvatureTensorNorm_le_one x
  linarith

/-- Every eigenvalue `μ` of the curvature endomorphism of a normalized initial metric satisfies
`-1 ≤ μ`. -/
theorem IsNormalizedInitialMetric.neg_one_le_of_hasEigenvalue
    (hg : g.IsNormalizedInitialMetric) {x : M} {μ : ℝ}
    (hμ : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ((leviCivitaConnection I M).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection I) x).HasEigenvalue μ)) :
    -1 ≤ μ := by
  have h := (abs_le.1 (hg.abs_le_half_of_hasEigenvalue hμ)).1
  linarith

/-- Every sectional curvature of a normalized initial metric satisfies `|K(u, v)| ≤ 1 / 2`. -/
theorem IsNormalizedInitialMetric.abs_sectionalCurvature_le_half
    (hg : g.IsNormalizedInitialMetric) (x : M) (u v : TangentSpace I x) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      |(leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v|) ≤ 1 / 2 := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have h1 := (leviCivitaConnection I M).abs_sectionalCurvature_le_half_curvatureTensorNorm
    (isMetricCompatible_leviCivitaConnection I) x u v
  have h2 : (leviCivitaConnection I M).curvatureTensorNorm x ≤ 1 := by
    rw [← g.curvatureTensorNorm_eq_curvatureTensorNorm_leviCivitaConnection rfl x]
    exact hg.curvatureTensorNorm_le_one x
  linarith

/-- Sharp scalar curvature magnitude bound `|Scal| ≤ √(n (n - 1) / 2)` for a normalized initial
metric. -/
theorem IsNormalizedInitialMetric.abs_scalarCurvature_le
    (hg : g.IsNormalizedInitialMetric) (x : M) :
    |g.scalarCurvature x| ≤ Real.sqrt ((finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) / 2) := by
  rw [scalarCurvature_def]
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have h1 := (leviCivitaConnection I M).abs_scalarCurvature_le_mul_curvatureTensorNorm
    (isMetricCompatible_leviCivitaConnection I) x
  have h2 : (leviCivitaConnection I M).curvatureTensorNorm x ≤ 1 := by
    rw [← g.curvatureTensorNorm_eq_curvatureTensorNorm_leviCivitaConnection rfl x]
    exact hg.curvatureTensorNorm_le_one x
  calc |(leviCivitaConnection I M).scalarCurvature x|
      ≤ Real.sqrt ((finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) / 2) *
          (leviCivitaConnection I M).curvatureTensorNorm x := h1
    _ ≤ Real.sqrt ((finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) / 2) * 1 :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = Real.sqrt ((finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) / 2) := mul_one _

/-- Lower bound `-(n (n - 1)) ≤ Scal` for a normalized initial metric, directly from the
curvature-operator bound `Rop ≥ -Id`. -/
theorem IsNormalizedInitialMetric.neg_mul_le_scalarCurvature
    (hg : g.IsNormalizedInitialMetric) (x : M) :
    -((finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1)) ≤ g.scalarCurvature x := by
  rw [scalarCurvature_def]
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have h := (leviCivitaConnection I M).le_scalarCurvature_of_le_curvatureEndomorphism
    (isMetricCompatible_leviCivitaConnection I) x (α := -1) fun z ↦ by
      simpa only [neg_one_mul] using hg.neg_le_inner_curvatureEndomorphism x z
  linarith

/-- On a three-manifold, a normalized initial metric satisfies `-6 ≤ Scal` everywhere, matching
the initial hypothesis of the Ricci-flow scalar curvature comparison principle. -/
theorem IsNormalizedInitialMetric.neg_six_le_scalarCurvature
    (hg : g.IsNormalizedInitialMetric) (hdim : finrank ℝ E = 3) (x : M) :
    -6 ≤ g.scalarCurvature x := by
  have h := hg.neg_mul_le_scalarCurvature x
  rw [hdim] at h
  norm_num at h
  exact h

/-- On a three-manifold, every geodesic ball of radius `0 < r ≤ 1` in a normalized initial metric
has volume at least `(2 / 3) π r³`. -/
theorem IsNormalizedInitialMetric.volume_ball_ge_three
    (hg : g.IsNormalizedInitialMetric) (hdim : finrank ℝ E = 3) (x : M)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (2 / 3 * Real.pi * r ^ 3) ≤
      TauCeti.riemannianVolume I (TauCeti.WithMetric g)
        {y | Manifold.riemannianEDist I (TauCeti.WithMetric.toWithMetric g x) y <
          ENNReal.ofReal r} := by
  have hvol := hg.volume_ball_ge x hr0 hr1
  rw [volume_ball_euclideanSpace_of_eq_three hdim, hdim] at hvol
  have hcalc :
      ENNReal.ofReal ((1 / 2 : ℝ) * r ^ 3) * ENNReal.ofReal (4 / 3 * Real.pi) =
        ENNReal.ofReal (2 / 3 * Real.pi * r ^ 3) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rwa [hcalc] at hvol

end Definition

section Scaling

variable [T2Space M] [LindelofSpace M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

omit [T2Space M] in
private theorem half_mul_le_riemannianVolume_ball_rescale_const_iff
    {c : ℝ} (hc : 0 < c) (x : M) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((1 / 2 : ℝ) * r ^ finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
      TauCeti.riemannianVolume I
        (TauCeti.WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        {y | Manifold.riemannianEDist I
          (TauCeti.WithMetric.toWithMetric
            (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x) y <
          ENNReal.ofReal r} ↔
    ENNReal.ofReal ((1 / 2 : ℝ) * (r / Real.sqrt c) ^ finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
      TauCeti.riemannianVolume I (TauCeti.WithMetric g)
        {y | Manifold.riemannianEDist I (TauCeti.WithMetric.toWithMetric g x) y <
          ENNReal.ofReal (r / Real.sqrt c)} := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hL : ENNReal.ofReal ((1 / 2 : ℝ) * r ^ finrank ℝ E) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) =
    ENNReal.ofReal (r ^ finrank ℝ E) *
      (ENNReal.ofReal (1 / 2) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)) := by
    rw [mul_comm (1 / 2 : ℝ), ENNReal.ofReal_mul (pow_nonneg hr.le _), mul_assoc]
  have hR : ENNReal.ofReal ((1 / 2 : ℝ) * (r / Real.sqrt c) ^ finrank ℝ E) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) =
    ENNReal.ofReal ((r / Real.sqrt c) ^ finrank ℝ E) *
      (ENNReal.ofReal (1 / 2) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)) := by
    rw [mul_comm (1 / 2 : ℝ),
      ENNReal.ofReal_mul (pow_nonneg (div_nonneg hr.le hsqrt.le) _), mul_assoc]
  rw [hL, hR]
  exact TauCeti.WithMetric.mul_le_riemannianVolume_ball_rescale_const_iff g hc x r _

/-- **Exact scaling characterization of normalized initial metrics.** For `c > 0`, the constant
rescaling `c g` is a normalized initial metric if and only if:
1. `|Rm_g(x)| ≤ c` everywhere,
2. `-(c * ‖z‖²) ≤ ⟪Rop_g(x) z, z⟫` everywhere, and
3. `vol_g(B_g(x, r / √c)) ≥ (1 / 2) ω_n (r / √c) ^ n` for all `x : M` and `0 < r ≤ 1`. -/
theorem isNormalizedInitialMetric_rescale_const_iff {c : ℝ} (hc : 0 < c) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).IsNormalizedInitialMetric ↔
      (∀ x : M, g.curvatureTensorNorm x ≤ c) ∧
      (∀ x : M,
        letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
        ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
          -(c * ‖z‖ ^ 2) ≤
            ⟪(leviCivitaConnection I M).curvatureEndomorphism
              (isMetricCompatible_leviCivitaConnection I) x z, z⟫) ∧
      (∀ x : M, ∀ {r : ℝ}, 0 < r → r ≤ 1 →
        ENNReal.ofReal ((1 / 2 : ℝ) * (r / Real.sqrt c) ^ finrank ℝ E) *
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
          TauCeti.riemannianVolume I (TauCeti.WithMetric g)
            {y | Manifold.riemannianEDist I (TauCeti.WithMetric.toWithMetric g x) y <
              ENNReal.ofReal (r / Real.sqrt c)}) := by
  constructor
  · intro h
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x r hr0 hr1 ↦ ?_⟩
    · have h1 := h.curvatureTensorNorm_le_one x
      rw [g.curvatureTensorNorm_rescale_const hc x] at h1
      rwa [inv_mul_le_iff₀ hc, mul_one] at h1
    · have h1 := (g.le_inner_curvatureEndomorphism_rescale_const_iff hc x (-1)).1
        (by simpa only [neg_one_mul] using h.neg_le_inner_curvatureEndomorphism x)
      simpa only [mul_neg_one, neg_mul] using h1
    · exact (g.half_mul_le_riemannianVolume_ball_rescale_const_iff hc x hr0).1
        (h.volume_ball_ge x hr0 hr1)
  · rintro ⟨hRm, hRop, hvol⟩
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x r hr0 hr1 ↦ ?_⟩
    · rw [g.curvatureTensorNorm_rescale_const hc x, inv_mul_le_iff₀ hc, mul_one]
      exact hRm x
    · have h1 := (g.le_inner_curvatureEndomorphism_rescale_const_iff hc x (-1)).2
        (by simpa only [mul_neg_one, neg_mul] using hRop x)
      simpa only [neg_one_mul] using h1
    · exact (g.half_mul_le_riemannianVolume_ball_rescale_const_iff hc x hr0).2
        (hvol x hr0 hr1)

variable {g}

/-- **Scaling up preserves the small-ball volume lower bound.** If `g` satisfies
`vol_g(B_g(x, s)) ≥ (1 / 2) ω_n s ^ n` for all `0 < s ≤ 1`, then for every constant `1 ≤ c`,
the scaled metric `c g` satisfies the same bound for all `0 < r ≤ 1`. -/
theorem IsNormalizedInitialMetric.volume_ball_ge_rescale_const
    (hg : g.IsNormalizedInitialMetric) {c : ℝ} (hc : 1 ≤ c) (x : M)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((1 / 2 : ℝ) * r ^ finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
      TauCeti.riemannianVolume I
        (TauCeti.WithMetric
          (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ lt_of_lt_of_le one_pos hc))
        {y | Manifold.riemannianEDist I
          (TauCeti.WithMetric.toWithMetric
            (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ lt_of_lt_of_le one_pos hc) x) y <
          ENNReal.ofReal r} := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hsqrt_ge : 1 ≤ Real.sqrt c := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hc
  have hs0 : 0 < r / Real.sqrt c := div_pos hr0 (Real.sqrt_pos.2 hcpos)
  have hs1 : r / Real.sqrt c ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.2 hcpos)]
    exact hr1.trans hsqrt_ge
  exact (g.half_mul_le_riemannianVolume_ball_rescale_const_iff hcpos x hr0).2
    (hg.volume_ball_ge x hs0 hs1)

/-- **Scaling up preserves normalization.** If `g` is a normalized initial metric and `1 ≤ c`,
then the rescaled metric `c g` is also a normalized initial metric. -/
theorem IsNormalizedInitialMetric.rescale_const
    (hg : g.IsNormalizedInitialMetric) {c : ℝ} (hc : 1 ≤ c) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦
      lt_of_lt_of_le one_pos hc).IsNormalizedInitialMetric := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  refine IsNormalizedInitialMetric.of_curvatureTensorNorm_le_one (fun x ↦ ?_)
    (fun x r hr0 hr1 ↦ hg.volume_ball_ge_rescale_const hc x hr0 hr1)
  rw [g.curvatureTensorNorm_rescale_const hcpos x, inv_mul_le_iff₀ hcpos, mul_one]
  exact (hg.curvatureTensorNorm_le_one x).trans hc

end Scaling

section Pullback

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [T2Space M] [LindelofSpace M] [T2Space N] [LindelofSpace N]

/-- **Diffeomorphism invariance of normalized initial metrics.** Pulling back a smooth metric `g`
along a smooth diffeomorphism `Φ : M ≃ₘ^∞⟮I, I'⟯ N` preserves and reflects
`IsNormalizedInitialMetric`. -/
theorem isNormalizedInitialMetric_pullback_iff
    (g : ContMDiffRiemannianMetric I' ∞ E (fun y : N ↦ TangentSpace I' y))
    (Φ : M ≃ₘ^∞⟮I, I'⟯ N) (hf : ContMDiff I I' ((∞ : ℕ∞ω) + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I I' Φ x)) :
    (g.pullback Φ hf hinj).IsNormalizedInitialMetric ↔ g.IsNormalizedInitialMetric := by
  have hinv : ∀ x, (mfderiv I I' Φ x).IsInvertible := fun x ↦ Φ.isInvertible_mfderiv (by simp)
  constructor
  · intro h
    refine ⟨fun y ↦ ?_, fun y ↦ ?_, fun y r hr0 hr1 ↦ ?_⟩
    · have h1 := h.curvatureTensorNorm_le_one (Φ.symm y)
      rw [g.curvatureTensorNorm_pullback Φ hf hinj (Φ.symm y), Φ.apply_symm_apply] at h1
      exact h1
    · have h1 := (g.le_inner_curvatureEndomorphism_pullback_of_isInvertible_iff hf hinv
        (Φ.symm y) (-1)).1 (by
          simpa only [neg_one_mul] using h.neg_le_inner_curvatureEndomorphism (Φ.symm y))
      rw [Φ.apply_symm_apply] at h1
      simpa only [neg_one_mul] using h1
    · have h1 := h.volume_ball_ge (Φ.symm y) hr0 hr1
      rw [TauCeti.WithMetric.riemannianVolume_ball_pullback g Φ hf hinj (Φ.symm y),
        Φ.apply_symm_apply] at h1
      exact h1
  · intro h
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x r hr0 hr1 ↦ ?_⟩
    · rw [g.curvatureTensorNorm_pullback Φ hf hinj x]
      exact h.curvatureTensorNorm_le_one (Φ x)
    · have h1 := (g.le_inner_curvatureEndomorphism_pullback_of_isInvertible_iff hf hinv x (-1)).2
        (by simpa only [neg_one_mul] using h.neg_le_inner_curvatureEndomorphism (Φ x))
      simpa only [neg_one_mul] using h1
    · rw [TauCeti.WithMetric.riemannianVolume_ball_pullback g Φ hf hinj x]
      exact h.volume_ball_ge (Φ x) hr0 hr1

/-- The pullback of a normalized initial metric along a smooth diffeomorphism is a normalized
initial metric. -/
theorem IsNormalizedInitialMetric.pullback
    {g : ContMDiffRiemannianMetric I' ∞ E (fun y : N ↦ TangentSpace I' y)}
    (hg : g.IsNormalizedInitialMetric) (Φ : M ≃ₘ^∞⟮I, I'⟯ N)
    (hf : ContMDiff I I' ((∞ : ℕ∞ω) + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I I' Φ x)) :
    (g.pullback Φ hf hinj).IsNormalizedInitialMetric :=
  (isNormalizedInitialMetric_pullback_iff g Φ hf hinj).2 hg

end Pullback

section Normalization

variable [CompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Normalization by constant rescaling.** On any closed (compact, boundaryless, Hausdorff)
smooth manifold, every smooth Riemannian metric `g` admits a threshold `c₀ > 0` such that the
rescaled metric `c g` is a normalized initial metric for every constant `c ≥ c₀`. -/
theorem exists_pos_forall_isNormalizedInitialMetric_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    ∃ (c₀ : ℝ) (hc₀ : 0 < c₀), ∀ {c : ℝ} (hc : c₀ ≤ c),
      (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦
        lt_of_lt_of_le hc₀ hc).IsNormalizedInitialMetric := by
  obtain ⟨C, _, hC⟩ := g.exists_curvatureTensorNorm_le
  obtain ⟨r₀, hr₀, hvol⟩ :=
    TauCeti.Manifold.exists_pos_forall_riemannianVolume_ball_bounds
      (I := I) (M := TauCeti.WithMetric g) (a := 1 / 2) (c := 2) (by norm_num) (by norm_num)
  let c₀ : ℝ := max (max C 1) (r₀⁻¹ ^ 2)
  have hc₀ : 0 < c₀ := lt_of_lt_of_le one_pos ((le_max_right C 1).trans (le_max_left _ _))
  refine ⟨c₀, hc₀, fun {c} hc ↦ ?_⟩
  have hcpos : 0 < c := lt_of_lt_of_le hc₀ hc
  have hCc : C ≤ c := ((le_max_left C 1).trans (le_max_left _ _)).trans hc
  have hr₀_sq : r₀⁻¹ ^ 2 ≤ c := (le_max_right _ _).trans hc
  have hr₀_sqrt : r₀⁻¹ ≤ Real.sqrt c := by
    rw [← Real.sqrt_sq (inv_nonneg.2 hr₀.le)]
    exact Real.sqrt_le_sqrt hr₀_sq
  refine IsNormalizedInitialMetric.of_curvatureTensorNorm_le_one (fun x ↦ ?_) (fun x r hr0 hr1 ↦ ?_)
  · rw [g.curvatureTensorNorm_rescale_const hcpos x, inv_mul_le_iff₀ hcpos, mul_one]
    exact (hC x).trans hCc
  · rw [g.half_mul_le_riemannianVolume_ball_rescale_const_iff hcpos x hr0]
    have hs0 : 0 < r / Real.sqrt c := div_pos hr0 (Real.sqrt_pos.2 hcpos)
    have hsr₀ : r / Real.sqrt c ≤ r₀ := by
      have hinv : (Real.sqrt c)⁻¹ ≤ r₀ := by
        rw [inv_le_comm₀ (Real.sqrt_pos.2 hcpos) hr₀]
        exact hr₀_sqrt
      calc r / Real.sqrt c
          = r * (Real.sqrt c)⁻¹ := div_eq_mul_inv r (Real.sqrt c)
        _ ≤ 1 * r₀ := mul_le_mul hr1 hinv (inv_nonneg.2 (Real.sqrt_nonneg c)) zero_le_one
        _ = r₀ := one_mul r₀
    exact (hvol (TauCeti.WithMetric.toWithMetric g x) hs0 hsr₀).1

/-- Every smooth Riemannian metric on a closed smooth manifold has a positive constant rescaling
that is a normalized initial metric. -/
theorem exists_pos_isNormalizedInitialMetric_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    ∃ (c : ℝ) (hc : 0 < c),
      (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).IsNormalizedInitialMetric := by
  obtain ⟨c₀, hc₀, h⟩ := g.exists_pos_forall_isNormalizedInitialMetric_rescale_const
  exact ⟨c₀, hc₀, h le_rfl⟩

end Normalization

section FlatCollapse

variable [CompactSpace M] [Nonempty M] [T2Space M]

/-- **Curvature bounds alone do not imply the normalized volume bound.**
On any nonempty compact flat smooth manifold `(M, g)` of positive dimension (`finrank ℝ E > 0`),
there is a threshold `c₀ > 0` such that for every `0 < c < c₀`, the collapsed metric `c g` has
identically vanishing curvature tensor (`|Rm| = 0 ≤ 1`, `Rop = 0 ≥ -Id`) yet fails to be a
normalized initial metric (its total volume falls strictly below `(1 / 2) ω_n`, violating the unit
ball lower bound). -/
theorem exists_pos_forall_lt_not_isNormalizedInitialMetric_of_flat
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hdim : 0 < finrank ℝ E) (hflat : ∀ x : M, g.curvatureTensorNorm x = 0) :
    ∃ c₀ > 0, ∀ {c : ℝ} (hc : 0 < c), c < c₀ →
      let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
      (∀ x : M, gc.curvatureTensorNorm x = 0) ∧
      (∀ x : M, gc.HasCurvatureOperatorLowerBoundAt x (-1)) ∧
      ¬ gc.IsNormalizedInitialMetric := by
  set V : ℝ := TauCeti.riemannianTotalVolume I (TauCeti.WithMetric g)
  have hV : 0 < V := TauCeti.riemannianTotalVolume_pos (I := I) (M := TauCeti.WithMetric g)
  set ω_n : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)
  have hω_pos : 0 < ω_n.toReal := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) zero_lt_one).ne'
    MeasureTheory.measure_ball_lt_top.ne
  let c₀ : ℝ := min 1 ((ω_n.toReal / (4 * V)) ^ 2)
  have hc₀ : 0 < c₀ := lt_min one_pos (sq_pos_of_pos (div_pos hω_pos (by positivity)))
  refine ⟨c₀, hc₀, fun {c} hc hlt ↦ ?_⟩
  let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have hRm0 : ∀ x : M, gc.curvatureTensorNorm x = 0 := fun x ↦ by
    rw [g.curvatureTensorNorm_rescale_const hc x, hflat x, mul_zero]
  refine ⟨hRm0, fun x ↦ ?_, fun hnorm ↦ ?_⟩
  · exact (gc.hasCurvatureOperatorLowerBoundAt_of_curvatureTensorNorm_le (hRm0 x).le).mono
      (by norm_num)
  · obtain ⟨x₀⟩ := ‹Nonempty M›
    have hc1 : c ≤ 1 := (hlt.trans_le (min_le_left _ _)).le
    have hcsq : c < (ω_n.toReal / (4 * V)) ^ 2 := hlt.trans_le (min_le_right _ _)
    have hsqrt : Real.sqrt c < ω_n.toReal / (4 * V) := by
      rw [← Real.sqrt_sq (div_nonneg hω_pos.le (by positivity))]
      exact Real.sqrt_lt_sqrt hc.le hcsq
    have hexp : (1 : ℝ) / 2 ≤ (finrank ℝ E : ℝ) / 2 := by
      have : (1 : ℝ) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hdim
      linarith
    have hpow : c ^ ((finrank ℝ E : ℝ) / 2) ≤ Real.sqrt c := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hc hc1 hexp
    have hVtot : TauCeti.riemannianTotalVolume I (TauCeti.WithMetric gc) < ω_n.toReal / 4 := by
      rw [TauCeti.WithMetric.riemannianTotalVolume_rescale_const g hc]
      calc c ^ ((finrank ℝ E : ℝ) / 2) * V
          ≤ Real.sqrt c * V := mul_le_mul_of_nonneg_right hpow hV.le
        _ < (ω_n.toReal / (4 * V)) * V := mul_lt_mul_of_pos_right hsqrt hV
        _ = ω_n.toReal / 4 := by field_simp [hV.ne']
    have hball : ENNReal.ofReal ((1 / 2 : ℝ) * (1 : ℝ) ^ finrank ℝ E) * ω_n ≤
        TauCeti.riemannianVolume I (TauCeti.WithMetric gc) univ :=
      (hnorm.volume_ball_ge x₀ zero_lt_one le_rfl).trans (measure_mono (subset_univ _))
    rw [one_pow, mul_one, ← TauCeti.ofReal_riemannianTotalVolume] at hball
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hball
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (TauCeti.riemannianTotalVolume_nonneg (I := I)
        (M := TauCeti.WithMetric gc))] at hreal
    linarith

end FlatCollapse

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

section Existence

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Existence of normalized initial metrics on every closed smooth manifold.**
Combining partition-of-unity metric existence (`TauCeti.nonempty_contMDiffRiemannianMetric`) with
constant rescaling normalization yields a normalized initial metric on any compact boundaryless
Hausdorff smooth manifold. -/
theorem exists_isNormalizedInitialMetric :
    ∃ g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x),
      g.IsNormalizedInitialMetric := by
  obtain ⟨g₀⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  obtain ⟨c, hc, hg⟩ := g₀.exists_pos_isNormalizedInitialMetric_rescale_const
  exact ⟨g₀.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc, hg⟩

/-- **Existence of normalized initial metrics on every closed smooth three-manifold.**
Produces a smooth metric `g` with `|Rm| ≤ 1`, `Rop ≥ -Id`, `-6 ≤ Scal`, and
`vol(B(x, r)) ≥ (2 / 3) π r³` for every `x : M` and `0 < r ≤ 1`. -/
theorem exists_isNormalizedInitialMetric_three {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] :
    ∃ g : ContMDiffRiemannianMetric (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3))
        (fun x : M ↦ TangentSpace (𝓡 3) x),
      g.IsNormalizedInitialMetric ∧
      (∀ x : M, -6 ≤ g.scalarCurvature x) ∧
      (∀ x : M, ∀ {r : ℝ}, 0 < r → r ≤ 1 →
        ENNReal.ofReal (2 / 3 * Real.pi * r ^ 3) ≤
          riemannianVolume (𝓡 3) (WithMetric g)
            {y | Manifold.riemannianEDist (𝓡 3) (WithMetric.toWithMetric g x) y <
              ENNReal.ofReal r}) := by
  obtain ⟨g, hg⟩ := exists_isNormalizedInitialMetric (I := 𝓡 3) (M := M)
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  exact ⟨g, hg, fun x ↦ hg.neg_six_le_scalarCurvature hdim x,
    fun x r hr0 hr1 ↦ hg.volume_ball_ge_three hdim x hr0 hr1⟩

end Existence

section SphereChecks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The Hilbert–Schmidt curvature tensor norm of the unit round `n`-sphere is
`√(2 n (n - 1))`. -/
@[simp]
theorem curvatureTensorNorm_sphereRoundMetric_ofLE (p : Metric.sphere (0 : E) 1) :
    ((sphereRoundMetric (E := E) (n := n)).ofLE le_top).curvatureTensorNorm p =
      Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
  have hconst := isConstantCurvatureTensor_sphereRoundMetric_ofLE (E := E) (n := n)
  rw [hconst.curvatureTensorNorm_eq p, finrank_euclideanSpace_fin, abs_one, mul_one]

/-- On the unit round three-sphere `S³`, `|Rm| = 2 √3`. -/
theorem curvatureTensorNorm_sphereRoundMetric_ofLE_three
    [Fact (finrank ℝ E = 3 + 1)] (p : Metric.sphere (0 : E) 1) :
    ((sphereRoundMetric (E := E) (n := 3)).ofLE le_top).curvatureTensorNorm p =
      2 * Real.sqrt 3 := by
  rw [curvatureTensorNorm_sphereRoundMetric_ofLE]
  have : (2 : ℝ) * (3 : ℕ) * ((3 : ℕ) - 1) = 2 ^ 2 * 3 := by norm_num
  rw [this, Real.sqrt_mul (sq_nonneg 2), Real.sqrt_sq (by norm_num)]

/-- On the unit circle `S¹`, `|Rm| = 0`. -/
theorem curvatureTensorNorm_sphereRoundMetric_ofLE_one
    [Fact (finrank ℝ E = 1 + 1)] (p : Metric.sphere (0 : E) 1) :
    ((sphereRoundMetric (E := E) (n := 1)).ofLE le_top).curvatureTensorNorm p = 0 := by
  rw [curvatureTensorNorm_sphereRoundMetric_ofLE]
  norm_num

/-- **Rescaling the unit round sphere satisfies the curvature bound.** For any `c > 0` with
`√(2 n (n - 1)) ≤ c`, the rescaled round metric `c g_{Sⁿ}` satisfies `|Rm| ≤ 1` and `Rop ≥ 0`
(hence `Rop ≥ -Id`). -/
theorem sphereRoundMetric_ofLE_rescale_curvature_bounds {c : ℝ} (hc : 0 < c)
    (hbound : Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) ≤ c) (p : Metric.sphere (0 : E) 1) :
    let g := ((sphereRoundMetric (E := E) (n := n)).ofLE le_top).rescale
      (fun _ ↦ c) contMDiff_const fun _ ↦ hc
    g.curvatureTensorNorm p ≤ 1 ∧
      (letI : RiemannianBundle (fun y : Metric.sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y) :=
          ⟨g.toRiemannianMetric⟩
        ∀ z : ⋀[ℝ]^2 (TangentSpace (𝓡 n) p),
          0 ≤ ⟪(leviCivitaConnection (𝓡 n) (Metric.sphere (0 : E) 1)).curvatureEndomorphism
            (isMetricCompatible_leviCivitaConnection (𝓡 n)) p z, z⟫) := by
  dsimp only
  let g₀ := (sphereRoundMetric (E := E) (n := n)).ofLE (m := ∞) le_top
  constructor
  · rw [ContMDiffRiemannianMetric.curvatureTensorNorm_rescale_const _ hc p,
      curvatureTensorNorm_sphereRoundMetric_ofLE, inv_mul_le_iff₀ hc, mul_one]
    exact hbound
  · have hpos :
        (letI : RiemannianBundle (fun y : Metric.sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y) :=
            ⟨g₀.toRiemannianMetric⟩;
          ∀ z : ⋀[ℝ]^2 (TangentSpace (𝓡 n) p),
            (c * 0) * ‖z‖ ^ 2 ≤
              ⟪(leviCivitaConnection (𝓡 n) (Metric.sphere (0 : E) 1)).curvatureEndomorphism
                (isMetricCompatible_leviCivitaConnection (𝓡 n)) p z, z⟫) := by
      let _ : RiemannianBundle (fun y : Metric.sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y) :=
        ⟨g₀.toRiemannianMetric⟩
      have _ : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
          (fun y : Metric.sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y) :=
        Bundle.instIsContMDiffRiemannianBundle g₀
      intro z
      have hconst := isConstantCurvatureTensor_sphereRoundMetric_ofLE (E := E) (n := n)
      have hsec := (leviCivitaConnection (𝓡 n) (Metric.sphere (0 : E) 1))
        |>.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub
          (isMetricCompatible_leviCivitaConnection (𝓡 n)) 1
          ((g₀.isConstantCurvatureTensor_iff 1).1 hconst)
      have hat := ((leviCivitaConnection (𝓡 n) (Metric.sphere (0 : E) 1))
        |>.hasConstantSectionalCurvature_iff
          (isMetricCompatible_leviCivitaConnection (𝓡 n)) 1).1 hsec p
      have hrop := hat.curvatureEndomorphism_eq_smul_id
        (torsion_leviCivitaConnection_eq_zero (𝓡 n))
      have heq :
          (leviCivitaConnection (𝓡 n) (Metric.sphere (0 : E) 1)).curvatureEndomorphism
            (isMetricCompatible_leviCivitaConnection (𝓡 n)) p z = z := by
        rw [hrop, LinearMap.smul_apply, one_smul, LinearMap.id_apply]
      rw [mul_zero, zero_mul, heq, real_inner_self_eq_norm_sq]
      exact sq_nonneg ‖z‖
    have h0 := (g₀.le_inner_curvatureEndomorphism_rescale_const_iff hc p 0).2 hpos
    simpa only [zero_mul] using h0

/-- The unit round `n`-sphere can be rescaled by a positive constant to a full normalized initial
metric. -/
theorem exists_pos_isNormalizedInitialMetric_sphereRoundMetric_rescale [FiniteDimensional ℝ E] :
    ∃ (c : ℝ) (hc : 0 < c),
      (((sphereRoundMetric (E := E) (n := n)).ofLE (m := ∞) le_top).rescale
        (fun _ ↦ c) contMDiff_const fun _ ↦ hc).IsNormalizedInitialMetric :=
  ((sphereRoundMetric (E := E) (n := n)).ofLE (m := ∞) le_top)
    |>.exists_pos_isNormalizedInitialMetric_rescale_const

end SphereChecks

section FlatTorusCheck

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Model smooth flat three-torus `T³ = S¹ × (S¹ × S¹)` formed from the unit circle in a
two-dimensional real inner product space `E` (such as `ℂ` or `EuclideanSpace ℝ (Fin 2)`). -/
abbrev FlatThreeTorus : Type _ :=
  Metric.sphere (0 : E) 1 × (Metric.sphere (0 : E) 1 × Metric.sphere (0 : E) 1)

/-- The model with corners for the product atlas on `FlatThreeTorus E`. -/
abbrev flatThreeTorusModel :
    ModelWithCorners ℝ
      (EuclideanSpace ℝ (Fin 1) × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      (ModelProd (EuclideanSpace ℝ (Fin 1))
        (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))) :=
  (𝓡 1).prod ((𝓡 1).prod (𝓡 1))

/-- The standard flat product metric on the three-torus `T³ = S¹ × (S¹ × S¹)`. -/
def flatThreeTorusMetric [Fact (finrank ℝ E = 1 + 1)] :
    ContMDiffRiemannianMetric flatThreeTorusModel ∞
      (EuclideanSpace ℝ (Fin 1) × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      (fun x : FlatThreeTorus E ↦ TangentSpace flatThreeTorusModel x) :=
  let g₁ := (sphereRoundMetric (E := E) (n := 1)).ofLE (m := ∞) le_top
  g₁.prodTangentSpace (g₁.prodTangentSpace g₁)

variable {E}

/-- The standard product metric on `T³` is flat: `|Rm| = 0` everywhere. -/
@[simp]
theorem curvatureTensorNorm_flatThreeTorusMetric [Fact (finrank ℝ E = 1 + 1)]
    (p : FlatThreeTorus E) :
    (flatThreeTorusMetric E).curvatureTensorNorm p = 0 := by
  let g₁ := (sphereRoundMetric (E := E) (n := 1)).ofLE (m := ∞) le_top
  refine ContMDiffRiemannianMetric.curvatureTensorNorm_prodTangentSpace_eq_zero g₁
    (g₁.prodTangentSpace g₁) (curvatureTensorNorm_sphereRoundMetric_ofLE_one p.1) ?_
  exact ContMDiffRiemannianMetric.curvatureTensorNorm_prodTangentSpace_eq_zero g₁ g₁
    (curvatureTensorNorm_sphereRoundMetric_ofLE_one p.2.1)
    (curvatureTensorNorm_sphereRoundMetric_ofLE_one p.2.2)

/-- The real dimension of the model space of `FlatThreeTorus` is `3`. -/
theorem finrank_flatThreeTorus_model :
    finrank ℝ
      (EuclideanSpace ℝ (Fin 1) × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) = 3 := by
  simp [Module.finrank_prod]

/-- **Collapsed flat three-tori fail the normalized volume bound.**
For any two-dimensional real inner product space `E` (so `FlatThreeTorus E` is the smooth
three-torus `S¹ × (S¹ × S¹)`), there is a threshold `c₀ > 0` such that for every `0 < c < c₀`, the
rescaled flat metric `c g_{T³}` satisfies `|Rm| = 0 ≤ 1` and `Rop = 0 ≥ -Id` everywhere, yet is not
a normalized initial metric (its total volume is strictly less than `(1 / 2) ω₃ = (2 / 3) π`). -/
theorem exists_pos_flatThreeTorusMetric_curvature_le_and_not_isNormalizedInitialMetric
    [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 1 + 1)] :
    ∃ c₀ > 0, ∀ {c : ℝ} (hc : 0 < c), c < c₀ →
      let g := (flatThreeTorusMetric E).rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
      (∀ x : FlatThreeTorus E, g.curvatureTensorNorm x = 0) ∧
      (∀ x : FlatThreeTorus E, g.HasCurvatureOperatorLowerBoundAt x (-1)) ∧
      ¬ g.IsNormalizedInitialMetric := by
  have hpos : 0 < finrank ℝ E := by
    rw [Fact.out (p := finrank ℝ E = 1 + 1)]
    norm_num
  have : Nontrivial E := finrank_pos_iff.1 hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have : Nonempty (Metric.sphere (0 : E) 1) :=
    ⟨⟨‖v‖⁻¹ • v, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]⟩⟩
  exact (flatThreeTorusMetric E).exists_pos_forall_lt_not_isNormalizedInitialMetric_of_flat
    (by rw [finrank_flatThreeTorus_model]; norm_num)
    curvatureTensorNorm_flatThreeTorusMetric

end FlatTorusCheck

end TauCeti

end
