/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Uniform small-ball volume estimates

On a smooth boundaryless Hausdorff Riemannian manifold `M` of dimension `n`, the differential of
the exponential map `exp_q : T_q M → M` at the origin is the identity. Reading `exp_q` through a
local smooth orthonormal frame over a neighbourhood of a point `p` exhibits the norm determinant
`LinearMap.normDet (d(exp_q)_v)` as a continuous function of `(q, v)` equal to `1` at `(p, 0)`.

Combining this with uniformly normal neighbourhoods
(`TauCeti.Manifold.exists_mem_nhds_forall_isNormalDomain_ball`), the change-of-variables formula
for `TauCeti.riemannianVolume` (`PartialDiffeomorph.setLIntegral_riemannianVolume_eq`), and the
identification of normal exponential balls with Riemannian distance balls yields two-sided
small-ball volume bounds that are uniform in both the centre `q` and all sufficiently small radii
`r > 0`: for every compact `K ⊆ M` and every `a < 1 < c`, there exists `r₀ > 0` such that for all
`q ∈ K` and `0 < r ≤ r₀`,

`a * r ^ n * ω_n ≤ vol(B(q, r)) ≤ c * r ^ n * ω_n`,

where `ω_n = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)` is the Euclidean unit-ball
volume. Equivalently, `vol(B(q, r)) / (r ^ n * ω_n) → 1` as `r → 0⁺`, uniformly on compact sets.

The estimates are stated for all finite dimensions `n ≥ 0` (including `n = 0`) and require no
inner-product structure on the model space `E`, no curvature bound, no completeness, and no
ambient `EMetricSpace` structure on `M`.

## Main results

* `OrthonormalBasis.addHaar_ball`: the Haar measure of an orthonormal basis assigns every metric
  ball the Euclidean ball volume of the same radius.
* `TauCeti.Manifold.IsNormalDomain.image_riemannianExp_ball_eq_setOf_riemannianEDist`: a normal
  exponential ball is the open Riemannian distance ball, requiring only `[T2Space M]`.
* `TauCeti.Manifold.IsNormalDomain.riemannianVolume_image_ball`: the Riemannian volume of a normal
  exponential ball is the integral of the norm determinant of `d(exp_q)` against the orthonormal
  Haar measure.
* `TauCeti.Manifold.exists_mem_nhds_forall_normDet_mfderiv_riemannianExp_mem_Ioo`: uniform
  two-sided control of the exponential Jacobian and normal radius on a neighbourhood of a point.
* `TauCeti.Manifold.exists_mem_nhds_forall_riemannianVolume_ball_bounds`: uniform small-ball volume
  bounds on a neighbourhood of a point.
* `IsCompact.exists_pos_forall_riemannianVolume_ball_bounds`: uniform small-ball volume bounds
  over any compact subset `K ⊆ M` (with `IsCompact.exists_pos_forall_riemannianVolume_eball_bounds`
  for `EMetricSpace` manifolds).
* `IsCompact.exists_pos_forall_abs_riemannianVolume_ball_div_sub_one_lt`: uniform real-ratio limit
  `|vol(B(q, r)) / (r ^ n * ω_n) - 1| < ε` on compact sets.
* `TauCeti.Manifold.tendsto_riemannianVolume_ball_div`: pointwise limit
  `vol(B(p, r)) / (r ^ n * ω_n) → 1` as `r → 0⁺`.
* `TauCeti.Manifold.exists_pos_forall_riemannianVolume_ball_bounds`: global uniform small-ball
  volume bounds on a compact manifold.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 6
  (normal neighbourhoods and the exponential map).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Ch. 3, §3.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Manifold MeasureTheory Module Set
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

section EuclideanBall

/-- The Haar measure of an orthonormal basis of a finite-dimensional real inner product space
assigns every open ball the Euclidean volume of the ball of the same radius. Unlike
`OrthonormalBasis.addHaar_eq_volume`, this requires no `MeasureSpace` instance on `V`. -/
theorem _root_.OrthonormalBasis.addHaar_ball {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (b : OrthonormalBasis ι ℝ V) (x : V) (r : ℝ) :
    b.toBasis.addHaar (Metric.ball x r) =
      volume (Metric.ball (0 : EuclideanSpace ℝ ι) r) := by
  classical
  let e : EuclideanSpace ℝ ι ≃L[ℝ] V := b.repr.symm.toContinuousLinearEquiv
  have hmap : (EuclideanSpace.basisFun ι ℝ).toBasis.map e.toLinearEquiv = b.toBasis := by
    ext i
    simp only [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      OrthonormalBasis.coe_toBasis, e, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    change b.repr.symm (EuclideanSpace.basisFun ι ℝ i) = b i
    rw [EuclideanSpace.basisFun_apply, ← b.repr_self i, LinearIsometryEquiv.symm_apply_apply]
  have hμ : Measure.map e (volume : Measure (EuclideanSpace ℝ ι)) = b.toBasis.addHaar := by
    rw [← (EuclideanSpace.basisFun ι ℝ).addHaar_eq_volume, Module.Basis.map_addHaar _ e, hmap]
  rw [← hμ, Measure.map_apply e.continuous.measurable Metric.isOpen_ball.measurableSet]
  have hpre : e ⁻¹' Metric.ball x r = Metric.ball (b.repr x) r := by
    ext y
    simp only [mem_preimage, Metric.mem_ball]
    change dist (b.repr.symm y) x < r ↔ dist y (b.repr x) < r
    rw [← b.repr.symm.isometry.dist_eq y (b.repr x), LinearIsometryEquiv.symm_apply_apply]
  rw [hpre, Measure.addHaar_ball_center]

private theorem volume_ball_euclideanSpace_eq_ofReal_pow_mul (n : ℕ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      ENNReal.ofReal (r ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  simpa only [finrank_euclideanSpace_fin] using
    Measure.addHaar_ball_of_pos (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) 0 hr

end EuclideanBall

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

section NormalBall

/-- **Geodesic balls are Riemannian distance balls.** Without assuming an ambient `EMetricSpace`
structure on `M`, the exponential image of an open tangent ball inside a normal domain equals the
open ball for `riemannianEDist`. -/
theorem IsNormalDomain.image_riemannianExp_ball_eq_setOf_riemannianEDist
    {p : M} {U : Set (TangentSpace I p)} {r : ℝ}
    (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U) :
    riemannianExp I M p '' Metric.ball 0 r =
      {y : M | riemannianEDist I p y < ENNReal.ofReal r} := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have : IsRiemannianManifold I M := ⟨fun _ _ ↦ rfl⟩
  rw [h.image_riemannianExp_ball hU]
  ext y
  rw [Metric.mem_eball', mem_ofPred_eq, IsRiemannianManifold.out (I := I)]

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [T2Space M] in
/-- The Riemannian volume of a normal exponential ball is the integral of the norm determinant of
the exponential differential against the Haar measure of any orthonormal basis of `T_p M`. -/
theorem IsNormalDomain.riemannianVolume_image_ball
    {p : M} {r : ℝ} (h : IsNormalDomain I M p (Metric.ball 0 r))
    [MeasurableSpace (TangentSpace I p)] [BorelSpace (TangentSpace I p)]
    (o : OrthonormalBasis (Fin (finrank ℝ E)) ℝ (TangentSpace I p)) :
    riemannianVolume I M (riemannianExp I M p '' Metric.ball 0 r) =
      ∫⁻ v in Metric.ball (0 : TangentSpace I p) r,
        ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap)
        ∂o.toBasis.addHaar := by
  let Φ : PartialDiffeomorph 𝓘(ℝ, TangentSpace I p) I (TangentSpace I p) M 1 :=
    h.toPartialDiffeomorph.ofLE (by simp)
  have hcov := Φ.setLIntegral_riemannianVolume_eq o.toBasis rfl (φ := fun _ ↦ 1) measurable_const
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at hcov
  have hpeq := PartialDiffeomorph.ofLE_toPartialEquiv h.toPartialDiffeomorph
    (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hsrc : Φ.source = Metric.ball (0 : TangentSpace I p) r :=
    (congrArg PartialEquiv.source hpeq).trans h.toPartialDiffeomorph_source
  have htgt : Φ.target = riemannianExp I M p '' Metric.ball (0 : TangentSpace I p) r :=
    (congrArg PartialEquiv.target hpeq).trans h.toPartialDiffeomorph_target
  have hcoe : (Φ.toPartialEquiv : TangentSpace I p → M) = riemannianExp I M p :=
    (congrArg (fun f : PartialEquiv (TangentSpace I p) M ↦ (f : TangentSpace I p → M)) hpeq).trans
      h.coe_toPartialDiffeomorph
  rw [htgt, hsrc, hcoe] at hcov
  rw [hcov]
  refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet fun v _ ↦ ?_
  rw [riemannianJacobian_eq_normDet]

/-- Two-sided volume bounds for a normal geodesic ball from two-sided bounds on the norm
determinant of the exponential differential. -/
theorem IsNormalDomain.riemannianVolume_ball_bounds_of_normDet_bounds
    {p : M} {r a c : ℝ} (hr : 0 < r) (h : IsNormalDomain I M p (Metric.ball 0 r))
    (hlo : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
      a ≤ LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap)
    (hhi : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
      LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap ≤ c) :
    ENNReal.ofReal (a * r ^ finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
      riemannianVolume I M {y | riemannianEDist I p y < ENNReal.ofReal r} ∧
    riemannianVolume I M {y | riemannianEDist I p y < ENNReal.ofReal r} ≤
      ENNReal.ofReal (c * r ^ finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
  let _ : MeasurableSpace (TangentSpace I p) := borel (TangentSpace I p)
  have : BorelSpace (TangentSpace I p) := ⟨rfl⟩
  let o : OrthonormalBasis (Fin (finrank ℝ E)) ℝ (TangentSpace I p) :=
    stdOrthonormalBasis ℝ (TangentSpace I p)
  have hball : o.toBasis.addHaar (Metric.ball (0 : TangentSpace I p) r) =
      ENNReal.ofReal (r ^ finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
    rw [o.addHaar_ball 0 r, volume_ball_euclideanSpace_eq_ofReal_pow_mul _ hr]
  rw [← h.image_riemannianExp_ball_eq_setOf_riemannianEDist Subset.rfl,
    h.riemannianVolume_image_ball o]
  constructor
  · calc
      ENNReal.ofReal (a * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)
        = ENNReal.ofReal a *
            (ENNReal.ofReal (r ^ finrank ℝ E) *
              volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)) := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hr.le _), mul_assoc]
      _ = ENNReal.ofReal a * o.toBasis.addHaar (Metric.ball (0 : TangentSpace I p) r) := by
          rw [hball]
      _ = ∫⁻ _ in Metric.ball (0 : TangentSpace I p) r, ENNReal.ofReal a ∂o.toBasis.addHaar := by
          rw [setLIntegral_const]
      _ ≤ _ := setLIntegral_mono' Metric.isOpen_ball.measurableSet fun v hv ↦
          ENNReal.ofReal_le_ofReal (hlo v hv)
  · calc
      _ ≤ ∫⁻ _ in Metric.ball (0 : TangentSpace I p) r, ENNReal.ofReal c ∂o.toBasis.addHaar :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet fun v hv ↦
            ENNReal.ofReal_le_ofReal (hhi v hv)
      _ = ENNReal.ofReal c * o.toBasis.addHaar (Metric.ball (0 : TangentSpace I p) r) := by
          rw [setLIntegral_const]
      _ = ENNReal.ofReal c *
            (ENNReal.ofReal (r ^ finrank ℝ E) *
              volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)) := by
          rw [hball]
      _ = ENNReal.ofReal (c * r ^ finrank ℝ E) *
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul' (pow_nonneg hr.le _)]

end NormalBall

section LocalJacobian

/-- **Uniform exponential Jacobian near a point.** For any `p : M` and `a < 1 < c`, there exist
a positive radius `r₀ > 0` and a neighbourhood `W ∈ 𝓝 p` such that for every `q ∈ W`:
1. `Metric.ball (0 : TangentSpace I q) r₀` is a normal domain at `q`, and
2. for every `v ∈ Metric.ball (0 : TangentSpace I q) r₀`, the norm determinant of
   `mfderiv (riemannianExp I M q) v` lies in `Ioo a c`. -/
theorem exists_mem_nhds_forall_normDet_mfderiv_riemannianExp_mem_Ioo
    (p : M) {a c : ℝ} (ha : a < 1) (hc : 1 < c) :
    ∃ r₀ > 0, ∃ W ∈ 𝓝 p, ∀ q ∈ W,
      IsNormalDomain I M q (Metric.ball 0 r₀) ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I q) r₀,
        LinearMap.normDet (U := TangentSpace I q)
          (mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) v).toLinearMap ∈ Ioo a c := by
  classical
  let n := finrank ℝ E
  let e := trivializationAt E (TangentSpace I) p
  let b₀ : Module.Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let chart := extChartAt I p
  have htgt_open : IsOpen chart.target := isOpen_extChartAt_target p
  have hbase_eq : e.baseSet = chart.source := by
    rw [TangentBundle.trivializationAt_baseSet, extChartAt_source]
  let u : Fin n → ∀ q : M, TangentSpace I q := fun i q ↦
    if hq : q ∈ e.baseSet then e.orthonormalBasis b₀ ⟨q, hq⟩ i else 0
  let base : E × EuclideanSpace ℝ (Fin n) → M := fun z ↦ chart.symm z.1
  let vec : E × EuclideanSpace ℝ (Fin n) → TangentBundle I M := fun z ↦
    TotalSpace.mk' E (base z) (∑ i : Fin n, z.2 i • u i (base z))
  let Ψ : E × EuclideanSpace ℝ (Fin n) → M := fun z ↦
    riemannianExp I M (base z) (vec z).2
  let S : Set (E × EuclideanSpace ℝ (Fin n)) := chart.target ×ˢ univ
  have hS_open : IsOpen S := htgt_open.prod isOpen_univ
  have hbase_maps : MapsTo base S e.baseSet := fun z hz ↦ by
    rw [hbase_eq]
    exact chart.map_target hz.1
  have hbase_smooth : ContMDiffOn 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) I ∞ base S :=
    (contMDiffOn_extChartAt_symm p).comp
      (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin n))).contDiff.contMDiff.contMDiffOn
      fun _ hz ↦ hz.1
  have hu_smooth : ∀ i : Fin n, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q ↦ TotalSpace.mk' E q (u i q)) e.baseSet := fun i ↦
    e.contMDiffOn_orthonormalBasis b₀ i
  have hvec_smooth : ContMDiffOn 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) (I.prod 𝓘(ℝ, E)) ∞ vec S := by
    refine ContMDiffOn.sum_sectionAlong Finset.univ
      (fun i (z : E × EuclideanSpace ℝ (Fin n)) ↦ z.2 i • u i (base z)) hbase_smooth fun i _ ↦ ?_
    have hproj : ContMDiffOn 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞
        (fun z : E × EuclideanSpace ℝ (Fin n) ↦ z.2 i) S :=
      ((EuclideanSpace.proj i).contDiff.comp_contMDiff
        (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin n))).contDiff.contMDiff).contMDiffOn
    exact hproj.smul_totalSpace ((hu_smooth i).comp hbase_smooth hbase_maps)
  let Ω : Set (E × EuclideanSpace ℝ (Fin n)) :=
    S ∩ vec ⁻¹' {w : TangentBundle I M | w.2 ∈ expDomain I M w.proj}
  have hΩ_open : IsOpen Ω :=
    hvec_smooth.continuousOn.isOpen_inter_preimage hS_open isOpen_setOfPred_mem_expDomain
  have hp_mem : (chart p, (0 : EuclideanSpace ℝ (Fin n))) ∈ Ω := by
    refine ⟨⟨mem_extChartAt_target p, mem_univ _⟩, ?_⟩
    change (∑ i : Fin n, (0 : EuclideanSpace ℝ (Fin n)) i • u i (chart.symm (chart p))) ∈
      expDomain I M (chart.symm (chart p))
    simp only [PiLp.zero_apply, zero_smul, Finset.sum_const_zero]
    exact zero_mem_expDomain _
  have hΨ_smooth : ContMDiffOn 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) I ∞ Ψ Ω :=
    contMDiffOn_riemannianExp_tangentBundle.comp (hvec_smooth.mono inter_subset_left)
      fun _ hz ↦ hz.2
  -- Compute the vertical directional derivatives of `Ψ` in the local orthonormal frame.
  let ξ : Fin n → E × EuclideanSpace ℝ (Fin n) := fun i ↦ (0, EuclideanSpace.single i 1)
  have hmfderiv (x : E) (y : EuclideanSpace ℝ (Fin n)) (hxy : (x, y) ∈ Ω) (i : Fin n) :
      mfderiv 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) I Ψ (x, y) (ξ i) =
        mfderiv 𝓘(ℝ, TangentSpace I (chart.symm x)) I (riemannianExp I M (chart.symm x))
          ((e.orthonormalBasis b₀ ⟨chart.symm x, hbase_maps hxy.1⟩).repr.symm y)
          (e.orthonormalBasis b₀ ⟨chart.symm x, hbase_maps hxy.1⟩ i) := by
    set q := chart.symm x
    have hq : q ∈ e.baseSet := hbase_maps hxy.1
    set o := e.orthonormalBasis b₀ ⟨q, hq⟩
    have hsum_eq (y' : EuclideanSpace ℝ (Fin n)) :
        (vec (x, y')).2 = o.repr.symm y' := by
      change ∑ j : Fin n, y' j • u j q = o.repr.symm y'
      rw [← o.sum_repr_symm y']
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [u, hq, ↓reduceDIte, o]
    let ι : EuclideanSpace ℝ (Fin n) → E × EuclideanSpace ℝ (Fin n) := fun y' ↦ (x, y')
    have hι : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n))
        ι y (ContinuousLinearMap.inr ℝ E (EuclideanSpace ℝ (Fin n))) :=
      ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)).hasMFDerivAt
    have hΨd : MDifferentiableAt 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) I Ψ (x, y) :=
      (hΨ_smooth.contMDiffAt (hΩ_open.mem_nhds hxy)).mdifferentiableAt (by simp)
    have hcomp₁ :
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (Ψ ∘ ι) y (EuclideanSpace.single i 1) =
          mfderiv 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) I Ψ (x, y) (ξ i) := by
      have h := mfderiv_comp_apply y hΨd hι.mdifferentiableAt (EuclideanSpace.single i 1)
      rw [hι.mfderiv] at h
      exact h
    have hfun : Ψ ∘ ι = riemannianExp I M q ∘ o.repr.symm := by
      funext y'
      simp only [Function.comp_apply, Ψ, ι, base, hsum_eq y']
      rfl
    have hexp_mem : o.repr.symm y ∈ expDomain I M q := by
      rw [← hsum_eq y]
      exact hxy.2
    have hexpd : MDifferentiableAt 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) (o.repr.symm y) :=
      (contMDiffAt_riemannianExp hexp_mem).mdifferentiableAt (by simp)
    let L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace I q :=
      o.repr.symm.toContinuousLinearMap
    have hreprd : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, TangentSpace I q)
        o.repr.symm y L :=
      hasMFDerivAt_iff_hasFDerivAt.2 (ContinuousLinearMap.hasFDerivAt L)
    have hcomp₂ :
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (riemannianExp I M q ∘ o.repr.symm) y
            (EuclideanSpace.single i 1) =
          mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) (o.repr.symm y) (o i) := by
      have h := mfderiv_comp_apply y hexpd hreprd.mdifferentiableAt (EuclideanSpace.single i 1)
      rw [hreprd.mfderiv] at h
      have hsingle : L (EuclideanSpace.single i 1) = o i := by
        change o.repr.symm (EuclideanSpace.single i 1) = o i
        rw [← o.repr_self i, LinearIsometryEquiv.symm_apply_apply]
      exact h.trans (congrArg _ hsingle)
    rw [← hcomp₁, hfun, hcomp₂]
  -- Continuity of the vertical Gram determinant `J` on `Ω`.
  let J : E × EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦
    Real.sqrt (Matrix.gram ℝ
      (fun i : Fin n ↦ mfderiv 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) I Ψ z (ξ i))).det
  have hJ_eq (x : E) (y : EuclideanSpace ℝ (Fin n)) (hxy : (x, y) ∈ Ω) :
      J (x, y) = LinearMap.normDet (U := TangentSpace I (chart.symm x))
        (mfderiv 𝓘(ℝ, TangentSpace I (chart.symm x)) I (riemannianExp I M (chart.symm x))
          ((e.orthonormalBasis b₀ ⟨chart.symm x, hbase_maps hxy.1⟩).repr.symm y)).toLinearMap := by
    set q := chart.symm x
    have hq : q ∈ e.baseSet := hbase_maps hxy.1
    set o := e.orthonormalBasis b₀ ⟨q, hq⟩
    have hΨeq : Ψ (x, y) = riemannianExp I M q (o.repr.symm y) := by
      simp only [Ψ, base, q]
      congr 1
      change ∑ j : Fin n, y j • u j q = o.repr.symm y
      rw [← o.sum_repr_symm y]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [u, hq, ↓reduceDIte, o]
    rw [← riemannianJacobian_eq_normDet (I := I) o, riemannianJacobian_eq_sqrt_det_gram]
    dsimp only [J]
    congr 2
    ext i j
    simp only [Matrix.gram_apply, OrthonormalBasis.coe_toBasis]
    exact inner_tangentSpace_congr hΨeq (hmfderiv x y hxy i) (hmfderiv x y hxy j)
  have hJ_cont : ContinuousOn J Ω := by
    have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
    have hgram : ContinuousOn (fun z ↦ Matrix.gram ℝ
        (fun i : Fin n ↦ mfderiv 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) I Ψ z (ξ i))) Ω :=
      continuousOn_pi.mpr fun i ↦ continuousOn_pi.mpr fun j ↦ by
        simpa only [Matrix.gram_apply] using
          (hΨ_smooth.contDiffOn_inner_mfderiv (m := 0) (by simp) hΩ_open (ξ i) (ξ j)).continuousOn
    exact Real.continuous_sqrt.comp_continuousOn (continuous_id.matrix_det.comp_continuousOn hgram)
  have hJ_zero : J (chart p, 0) = 1 := by
    rw [hJ_eq (chart p) 0 hp_mem, map_zero]
    set q := chart.symm (chart p)
    have hq : q ∈ e.baseSet := hbase_maps hp_mem.1
    set o := e.orthonormalBasis b₀ ⟨q, hq⟩
    rw [← riemannianJacobian_eq_normDet (I := I) o, riemannianJacobian_eq_sqrt_det_gram]
    have hgram : Matrix.gram ℝ (fun i : Fin n ↦
        mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) 0 (o.toBasis i)) = 1 := by
      ext i j
      rw [Matrix.gram_apply, Matrix.one_apply]
      exact (inner_tangentSpace_congr (riemannianExp_zero q)
        (mfderiv_riemannianExp_apply_zero q (o.toBasis i))
        (mfderiv_riemannianExp_apply_zero q (o.toBasis j))).trans
        (by
          simpa only [OrthonormalBasis.coe_toBasis] using
            orthonormal_iff_ite.mp o.orthonormal i j)
    rw [hgram, Matrix.det_one, Real.sqrt_one]
  -- Extract a product neighbourhood of `(chart p, 0)` where `J ∈ Ioo a c`.
  have hnhds : Ω ∩ J ⁻¹' Ioo a c ∈ 𝓝 (chart p, (0 : EuclideanSpace ℝ (Fin n))) :=
    inter_mem (hΩ_open.mem_nhds hp_mem)
      ((hJ_cont.continuousAt (hΩ_open.mem_nhds hp_mem)).preimage_mem_nhds
        (hJ_zero.symm ▸ Ioo_mem_nhds ha hc))
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_nhds_prod_iff.1 hnhds
  obtain ⟨δ, hδ, hδV₂⟩ := Metric.mem_nhds_iff.1 hV₂
  obtain ⟨rN, hrN, W_N, hWN, hN⟩ := exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p
  have hW₁ : chart.source ∩ chart ⁻¹' V₁ ∈ 𝓝 p :=
    inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt p).preimage_mem_nhds hV₁)
  refine ⟨min rN δ, lt_min hrN hδ, W_N ∩ (chart.source ∩ chart ⁻¹' V₁), inter_mem hWN hW₁,
    fun q hq ↦ ⟨?_, ?_⟩⟩
  · exact (hN q hq.1).1.ball (Metric.ball_subset_ball (min_le_left _ _)) (lt_min hrN hδ)
  · intro v hv
    have hq_src : q ∈ chart.source := hq.2.1
    have hq_base : q ∈ e.baseSet := hbase_eq.symm ▸ hq_src
    set o := e.orthonormalBasis b₀ ⟨q, hq_base⟩
    set y : EuclideanSpace ℝ (Fin n) := o.repr v
    have hy : y ∈ Metric.ball 0 δ := by
      rw [mem_ball_zero_iff]
      simpa only [y, LinearIsometryEquiv.norm_map] using
        (mem_ball_zero_iff.1 hv).trans_le (min_le_right _ _)
    have hmem := hV (mk_mem_prod hq.2.2 (hδV₂ hy))
    have hleft : chart.symm (chart q) = q := chart.left_inv hq_src
    have hJval := hJ_eq (chart q) y hmem.1
    have hbound : J (chart q, y) ∈ Ioo a c := hmem.2
    rw [hJval] at hbound
    -- Transport the identity across `chart.symm (chart q) = q` and `o.repr.symm y = v`.
    have hEq : LinearMap.normDet (U := TangentSpace I (chart.symm (chart q)))
          (mfderiv 𝓘(ℝ, TangentSpace I (chart.symm (chart q))) I
            (riemannianExp I M (chart.symm (chart q)))
            ((e.orthonormalBasis b₀ ⟨chart.symm (chart q), hbase_maps hmem.1.1⟩).repr.symm y)
          ).toLinearMap =
        LinearMap.normDet (U := TangentSpace I q)
          (mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) v).toLinearMap := by
      have hsymm : ∀ (q' : M) (hq' : q' ∈ e.baseSet), q' = q →
          LinearMap.normDet (U := TangentSpace I q')
            (mfderiv 𝓘(ℝ, TangentSpace I q') I (riemannianExp I M q')
              ((e.orthonormalBasis b₀ ⟨q', hq'⟩).repr.symm y)).toLinearMap =
          LinearMap.normDet (U := TangentSpace I q)
            (mfderiv 𝓘(ℝ, TangentSpace I q) I (riemannianExp I M q) v).toLinearMap := by
        rintro _ hq' rfl
        have : (e.orthonormalBasis b₀ ⟨_, hq'⟩).repr.symm y = v :=
          (e.orthonormalBasis b₀ ⟨_, hq'⟩).repr.symm_apply_apply v
        rw [this]
      exact hsymm (chart.symm (chart q)) (hbase_maps hmem.1.1) hleft
    rwa [hEq] at hbound

end LocalJacobian

section SmallBallVolume

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Uniform small-ball volume bounds near a point.** For every `p : M` and every `a < 1 < c`,
there exist `r₀ > 0` and a neighbourhood `W ∈ 𝓝 p` such that for all `q ∈ W` and all
`0 < r ≤ r₀`, the Riemannian volume of the open geodesic ball of radius `r` centred at `q` lies
between `a * r ^ n * ω_n` and `c * r ^ n * ω_n`. -/
theorem exists_mem_nhds_forall_riemannianVolume_ball_bounds
    (p : M) {a c : ℝ} (ha : a < 1) (hc : 1 < c) :
    ∃ r₀ > 0, ∃ W ∈ 𝓝 p, ∀ q ∈ W, ∀ {r : ℝ}, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
        riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r} ∧
      riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r} ≤
        ENNReal.ofReal (c * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
  obtain ⟨r₀, hr₀, W, hW, hbound⟩ :=
    exists_mem_nhds_forall_normDet_mfderiv_riemannianExp_mem_Ioo (I := I) (M := M) p ha hc
  refine ⟨r₀, hr₀, W, hW, fun q hq r hr hrr₀ ↦ ?_⟩
  have hnorm : IsNormalDomain I M q (Metric.ball 0 r) :=
    (hbound q hq).1.ball (Metric.ball_subset_ball hrr₀) hr
  exact hnorm.riemannianVolume_ball_bounds_of_normDet_bounds hr
    (fun v hv ↦ ((hbound q hq).2 v (Metric.ball_subset_ball hrr₀ hv)).1.le)
    (fun v hv ↦ ((hbound q hq).2 v (Metric.ball_subset_ball hrr₀ hv)).2.le)

/-- **Uniform small-ball volume bounds on a compact set.** For any compact set `K ⊆ M` and any
`a < 1 < c`, there exists `r₀ > 0` such that for all `q ∈ K` and all `0 < r ≤ r₀`, the Riemannian
volume of the open geodesic ball of radius `r` centred at `q` lies between `a * r ^ n * ω_n` and
`c * r ^ n * ω_n`. -/
theorem _root_.IsCompact.exists_pos_forall_riemannianVolume_ball_bounds
    {K : Set M} (hK : IsCompact K) {a c : ℝ} (ha : a < 1) (hc : 1 < c) :
    ∃ r₀ > 0, ∀ q ∈ K, ∀ {r : ℝ}, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
        riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r} ∧
      riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r} ≤
        ENNReal.ofReal (c * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
  choose! R hR W hW hRW using fun p : M ↦
    exists_mem_nhds_forall_riemannianVolume_ball_bounds (I := I) (M := M) p ha hc
  obtain ⟨t, -, hKt⟩ :=
    hK.elim_nhds_subcover (fun p ↦ interior (W p)) fun p _ ↦ interior_mem_nhds.2 (hW p)
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨1, one_pos, fun q hq ↦ (by simpa using hKt hq : False).elim⟩
  have hRt : 0 < t.inf' ht R := (Finset.lt_inf'_iff ht).2 fun p _ ↦ hR p
  refine ⟨t.inf' ht R, hRt, fun q hq r hr hrr₀ ↦ ?_⟩
  obtain ⟨p, hpt, hqp⟩ := mem_iUnion₂.1 (hKt hq)
  exact hRW p q (interior_subset hqp) hr (hrr₀.trans (Finset.inf'_le R hpt))

/-- **Uniform small-ball volume limit on a compact set (real-ratio form).** For any compact set
`K ⊆ M` and every `ε > 0`, there exists `r₀ > 0` such that for all `q ∈ K` and `r ∈ Ioc 0 r₀`,
the ratio of the geodesic ball volume to `r ^ n * ω_n` is within `ε` of `1`. -/
theorem _root_.IsCompact.exists_pos_forall_abs_riemannianVolume_ball_div_sub_one_lt
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ > 0, ∀ q ∈ K, ∀ r ∈ Ioc 0 r₀,
      |(riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r}).toReal /
        (r ^ finrank ℝ E *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)).toReal) - 1| < ε := by
  let δ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ_lt : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hlo : 1 - δ < 1 := by linarith
  have hhi : 1 < 1 + δ := by linarith
  have h1sub : 0 ≤ 1 - δ := by
    have : δ ≤ 1 / 2 := min_le_right _ _
    linarith
  obtain ⟨r₀, hr₀, hbound⟩ := hK.exists_pos_forall_riemannianVolume_ball_bounds
    (I := I) hlo hhi
  refine ⟨r₀, hr₀, fun q hq r ⟨hr0, hrr₀⟩ ↦ ?_⟩
  obtain ⟨hle, hge⟩ := hbound q hq hr0 hrr₀
  set v₁ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)
  have hv₁_top : v₁ ≠ ⊤ := MeasureTheory.measure_ball_lt_top.ne
  have hv₁_pos : 0 < v₁.toReal := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) zero_lt_one).ne'
    hv₁_top
  set V := riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r}
  have hhi_top : ENNReal.ofReal ((1 + δ) * r ^ finrank ℝ E) * v₁ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv₁_top
  have hV_top : V ≠ ⊤ := ne_top_of_le_ne_top hhi_top hge
  have hlo_real : (1 - δ) * (r ^ finrank ℝ E * v₁.toReal) ≤ V.toReal := by
    have h1 := ENNReal.toReal_mono hV_top hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg h1sub (pow_nonneg hr0.le _)),
      mul_assoc] at h1
    exact h1
  have hhi_real : V.toReal ≤ (1 + δ) * (r ^ finrank ℝ E * v₁.toReal) := by
    have h1 := ENNReal.toReal_mono hhi_top hge
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by linarith) (pow_nonneg hr0.le _)),
      mul_assoc] at h1
    exact h1
  have hden : 0 < r ^ finrank ℝ E * v₁.toReal := mul_pos (pow_pos hr0 _) hv₁_pos
  rw [abs_sub_lt_iff]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hden]
    nlinarith [hhi_real, hden, hδ_lt]
  · rw [sub_lt_iff_lt_add]
    have : 1 - δ ≤ V.toReal / (r ^ finrank ℝ E * v₁.toReal) :=
      (le_div_iff₀ hden).2 hlo_real
    linarith

/-- **Pointwise small-ball volume limit.** At every point `p : M`, the ratio of the Riemannian
volume of the geodesic ball of radius `r` around `p` to `r ^ n * ω_n` tends to `1` as `r → 0⁺`. -/
theorem tendsto_riemannianVolume_ball_div (p : M) :
    Tendsto
      (fun r : ℝ ↦
        (riemannianVolume I M {y | riemannianEDist I p y < ENNReal.ofReal r}).toReal /
          (r ^ finrank ℝ E *
            (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)).toReal))
      (𝓝[>] 0) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r₀, hr₀, hbound⟩ :=
    isCompact_singleton (x := p)
      |>.exists_pos_forall_abs_riemannianVolume_ball_div_sub_one_lt (I := I) hε
  filter_upwards [Ioc_mem_nhdsGT hr₀] with r hr
  simpa only [Real.dist_eq] using hbound p (mem_singleton p) r hr

/-- **Uniform small-ball volume bounds on a compact manifold.** On a compact boundaryless Hausdorff
smooth Riemannian manifold `M`, for every `a < 1 < c` there exists `r₀ > 0` such that for every
`q : M` and every `0 < r ≤ r₀`, the Riemannian volume of `B(q, r)` lies between
`a * r ^ n * ω_n` and `c * r ^ n * ω_n`. -/
theorem exists_pos_forall_riemannianVolume_ball_bounds [CompactSpace M]
    {a c : ℝ} (ha : a < 1) (hc : 1 < c) :
    ∃ r₀ > 0, ∀ q : M, ∀ {r : ℝ}, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
        riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r} ∧
      riemannianVolume I M {y | riemannianEDist I q y < ENNReal.ofReal r} ≤
        ENNReal.ofReal (c * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
  obtain ⟨r₀, hr₀, hbound⟩ :=
    (isCompact_univ (X := M)).exists_pos_forall_riemannianVolume_ball_bounds (I := I) ha hc
  exact ⟨r₀, hr₀, fun q r hr hrr₀ ↦ hbound q (mem_univ q) hr hrr₀⟩

end SmallBallVolume

section EMetric

variable {M' : Type*} [EMetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M' ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M' ↦ TangentSpace I x)]
  [IsRiemannianManifold I M'] [MeasurableSpace M'] [BorelSpace M'] [LindelofSpace M']

/-- **Uniform small-ball volume bounds for `Metric.eball` on a compact set.** -/
theorem _root_.IsCompact.exists_pos_forall_riemannianVolume_eball_bounds
    {K : Set M'} (hK : IsCompact K) {a c : ℝ} (ha : a < 1) (hc : 1 < c) :
    ∃ r₀ > 0, ∀ q ∈ K, ∀ {r : ℝ}, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) ≤
        riemannianVolume I M' (Metric.eball q (ENNReal.ofReal r)) ∧
      riemannianVolume I M' (Metric.eball q (ENNReal.ofReal r)) ≤
        ENNReal.ofReal (c * r ^ finrank ℝ E) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
  obtain ⟨r₀, hr₀, hbound⟩ :=
    hK.exists_pos_forall_riemannianVolume_ball_bounds (I := I) ha hc
  refine ⟨r₀, hr₀, fun q hq r hr hrr₀ ↦ ?_⟩
  have hset : Metric.eball q (ENNReal.ofReal r) =
      {y : M' | riemannianEDist I q y < ENNReal.ofReal r} := by
    ext y
    rw [Metric.mem_eball', mem_ofPred_eq, IsRiemannianManifold.out (I := I)]
  rw [hset]
  exact hbound q hq hr hrr₀

end EMetric

end TauCeti.Manifold

end
