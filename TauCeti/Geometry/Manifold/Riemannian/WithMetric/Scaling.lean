/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance

/-!
# Distance and ball-volume scaling under constant rescaling and pullback

Let `g` be a Riemannian metric on a manifold `M` of real dimension `n`, and let `c > 0` be a
constant. Multiplying `g` by `c` scales tangent norms by `√c`, so the extended length of every
`C¹` curve scales by `√c`, and therefore the intrinsic Riemannian extended distance scales by
`√c`:

`d_{c g}(x, y) = √c · d_g(x, y)`.

Consequently the open geodesic ball of radius `r` in `(M, c g)` is the open geodesic ball of
radius `r / √c` in `(M, g)`. Combining this with the conformal volume formula
`dV_{c g} = c^(n / 2) dV_g` (`TauCeti.WithMetric.riemannianVolume_rescale`) yields the exact
ball-volume scaling law

`vol_{c g}(B_{c g}(x, r)) = c^(n / 2) · vol_g(B_g(x, r / √c))`,

so the normalized volume ratio `vol(B(x, r)) / r^n` for `c g` at radius `r` equals that for `g`
at radius `r / √c`. In particular, scaling up (`1 ≤ c`) preserves any all-small-radii lower bound
`κ r^n ≤ vol(B(x, r))` for `0 < r ≤ 1`. On a compact manifold, the total volume scales as
`Vol(c g) = c^(n / 2) Vol(g)`.

Along a smooth diffeomorphism `Φ : M ≃ₘ^∞ N`, the pullback metric `Φ^* g` makes `Φ` a Riemannian
isometry, so distances and geodesic ball volumes pull back identically:
`d_{Φ^* g}(x, y) = d_g(Φ x, Φ y)` and `vol_{Φ^* g}(B_{Φ^* g}(x, r)) = vol_g(B_g(Φ x, r))`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.pathELength_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.riemannianEDist_rescale_const`: constant rescaling of curve
  lengths and Riemannian extended distances by `√c`.
* `Bundle.ContMDiffRiemannianMetric.riemannianEDist_pullback`: `riemannianEDist` along a
  diffeomorphism for the pullback metric `Φ^* g`.
* `TauCeti.WithMetric.riemannianEDist_eq_ofWithMetric`: `ofWithMetric` preserves `riemannianEDist`.
* `TauCeti.WithMetric.riemannianEDist_rescale_const`: `riemannianEDist` on `WithMetric (c • g)`
  equals `√c` times `riemannianEDist` on `WithMetric g`.
* `TauCeti.WithMetric.riemannianVolume_rescale_const`: `vol_{c g}` is `c^(n/2) • map vol_g`.
* `TauCeti.WithMetric.riemannianVolume_ball_rescale_const`: exact ball-volume scaling under
  constant rescaling.
* `TauCeti.WithMetric.mul_le_riemannianVolume_ball_rescale_const_iff`: scale-invariant volume
  ratio comparison `r^n * a ≤ vol_{c g}(B_{c g}(x, r)) ↔ (r / √c)^n * a ≤ vol_g(B_g(x, r / √c))`.
* `TauCeti.WithMetric.riemannianTotalVolume_rescale_const`: `Vol(c g) = c^(n/2) Vol(g)`.
* `TauCeti.WithMetric.riemannianEDist_pullback` and
  `TauCeti.WithMetric.riemannianVolume_ball_pullback`: invariance of geodesic distance and ball
  volumes under diffeomorphisms.
* `TauCeti.Manifold.setOf_riemannianEDist_lt_eq_eball` and
  `TauCeti.Manifold.setOf_riemannianEDist_lt_ofReal_eq_ball`: identification of intrinsic geodesic
  balls with `Metric.eball` and `Metric.ball` under `IsRiemannianManifold`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- On a manifold carrying its Riemannian extended distance, the intrinsic open geodesic ball
`{y | riemannianEDist I x y < r}` coincides with `Metric.eball x r`. -/
@[simp]
theorem setOf_riemannianEDist_lt_eq_eball {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    (x : M) (r : ℝ≥0∞) :
    {y : M | riemannianEDist I x y < r} = Metric.eball x r := by
  ext y
  rw [Metric.mem_eball, edist_comm, IsRiemannianManifold.out (I := I)]
  rfl

/-- On a manifold carrying its Riemannian metric distance, the intrinsic open geodesic ball of
radius `ENNReal.ofReal r` coincides with `Metric.ball x r`. -/
theorem setOf_riemannianEDist_lt_ofReal_eq_ball {M : Type*} [PseudoMetricSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] (x : M) (r : ℝ) :
    {y : M | riemannianEDist I x y < ENNReal.ofReal r} = Metric.ball x r := by
  rw [setOf_riemannianEDist_lt_eq_eball, Metric.eball_ofReal]

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Constant rescaling of a metric by `c > 0` scales tangent norms by `√c`. -/
theorem norm_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) (v : TangentSpace I x) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖) =
    Real.sqrt c * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ‖v‖) := by
  have h1 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖ ^ 2) = c * g.inner x v v := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    rw [← real_inner_self_eq_norm_sq, inner_riemannianBundle, rescale_inner]
  have h2 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ‖v‖ ^ 2) = g.inner x v v := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    rw [← real_inner_self_eq_norm_sq, inner_riemannianBundle]
  have hsq : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖ ^ 2) =
    (Real.sqrt c *
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        ‖v‖)) ^ 2 := by
    rw [h1, mul_pow, Real.sq_sqrt hc.le, h2]
  have hnn1 : 0 ≤ (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    exact norm_nonneg v
  have hnn2 : 0 ≤ Real.sqrt c *
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        ‖v‖) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    exact mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg v)
  exact (sq_eq_sq₀ hnn1 hnn2).1 hsq

/-- Constant rescaling of a metric by `c > 0` scales tangent `enorm`s by `ENNReal.ofReal (√c)`. -/
theorem enorm_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) (v : TangentSpace I x) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖ₑ) =
    ENNReal.ofReal (Real.sqrt c) *
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩; ‖v‖ₑ) := by
  have he1 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖ₑ) = ENNReal.ofReal
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; ‖v‖) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    exact (ofReal_norm v).symm
  have he2 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ‖v‖ₑ) = ENNReal.ofReal
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩; ‖v‖) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    exact (ofReal_norm v).symm
  rw [he1, he2, g.norm_rescale_const hc x v, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]

/-- **Scaling of curve length.** Multiplying a metric by `c > 0` multiplies `pathELength` by
`ENNReal.ofReal (√c)`. -/
theorem pathELength_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (γ : ℝ → M) (a b : ℝ) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      Manifold.pathELength I γ a b) =
    ENNReal.ofReal (Real.sqrt c) *
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        Manifold.pathELength I γ a b) := by
  have h1 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      Manifold.pathELength I γ a b) =
      ∫⁻ t in Ioo a b,
        (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
          ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    exact Manifold.pathELength_eq_lintegral_mfderiv_Ioo
  have h2 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I γ a b) =
      ∫⁻ t in Ioo a b,
        (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    exact Manifold.pathELength_eq_lintegral_mfderiv_Ioo
  rw [h1, h2]
  simp_rw [g.enorm_rescale_const hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **Scaling of Riemannian extended distance.** Multiplying a metric by `c > 0` multiplies
`riemannianEDist` by `ENNReal.ofReal (√c)`, including when the distance is infinite. -/
theorem riemannianEDist_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x y : M) :
    (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      Manifold.riemannianEDist I x y) =
    ENNReal.ofReal (Real.sqrt c) *
      (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩;
        Manifold.riemannianEDist I x y) := by
  have hs0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hc)).ne'
  have hst : ENNReal.ofReal (Real.sqrt c) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine le_antisymm ?_ ?_
  · rw [← ENNReal.inv_mul_le_iff hs0 hst]
    let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
    refine TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength fun γ h0 h1 hγ ↦ ?_
    rw [ENNReal.inv_mul_le_iff hs0 hst, ← g.pathELength_rescale_const hc γ 0 1]
    let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one
  · let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    refine TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength fun γ h0 h1 hγ ↦ ?_
    rw [g.pathELength_rescale_const hc γ 0 1]
    gcongr
    let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one

/-- **Pullback of Riemannian extended distance.** Along a diffeomorphism `Φ : M ≃ₘ^∞ N`, the
Riemannian extended distance of `Φ^* g` equals the Riemannian extended distance of `g` applied to
the images. -/
theorem riemannianEDist_pullback [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (n + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) (x y : M) :
    (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(g.pullback Φ hf hinj).toRiemannianMetric⟩;
      Manifold.riemannianEDist I x y) =
    (letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨g.toRiemannianMetric⟩;
      Manifold.riemannianEDist J (Φ x) (Φ y)) := by
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨(g.pullback Φ hf hinj).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨g.toRiemannianMetric⟩
  have h := (g.pullbackRiemannianIsometry Φ hf hinj).riemannianEDist_eq x y
  simpa only [coe_pullbackRiemannianIsometry] using h.symm

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section Distance

/-- The tautological map `ofWithMetric : WithMetric g → M` as a Riemannian isometry onto `M`
equipped with `g` as its `RiemannianBundle` instance. -/
def riemannianIsometryOfWithMetric
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    TauCeti.RiemannianIsometry I I (WithMetric g) M :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  { toDiffeomorph := diffeomorph g ∞
    inner_mfderiv' := fun x v w ↦ by
      rw [coe_diffeomorph]
      exact (inner_def x v w).symm }

/-- The underlying map of `riemannianIsometryOfWithMetric g` is `ofWithMetric`. -/
@[simp]
theorem coe_riemannianIsometryOfWithMetric
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ⇑(riemannianIsometryOfWithMetric g) = ofWithMetric := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact coe_diffeomorph ∞

/-- The Riemannian extended distance on `WithMetric g` agrees with the Riemannian extended
distance on `M` with `g` installed. -/
theorem riemannianEDist_eq_ofWithMetric
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (x y : WithMetric g) :
    Manifold.riemannianEDist I x y =
      (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩;
        Manifold.riemannianEDist I x.ofWithMetric y.ofWithMetric) := by
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  have h := (riemannianIsometryOfWithMetric g).riemannianEDist_eq x y
  simpa only [coe_riemannianIsometryOfWithMetric] using h.symm

/-- **Scaling of Riemannian extended distance on `WithMetric`.** Multiplying `g` by a positive
constant `c` multiplies `riemannianEDist` on `WithMetric` by `ENNReal.ofReal (√c)`. -/
theorem riemannianEDist_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x y : M) :
    Manifold.riemannianEDist I
        (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x)
        (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) y) =
      ENNReal.ofReal (Real.sqrt c) *
        Manifold.riemannianEDist I (toWithMetric g x) (toWithMetric g y) := by
  rw [riemannianEDist_eq_ofWithMetric, riemannianEDist_eq_ofWithMetric]
  exact g.riemannianEDist_rescale_const hc x y

/-- An open geodesic ball of radius `r` for `c g` (`c > 0`) contains `y` if and only if the open
geodesic ball of radius `r / √c` for `g` contains `y`. -/
theorem riemannianEDist_lt_rescale_const_iff
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x y : M) (r : ℝ) :
    Manifold.riemannianEDist I
        (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x)
        (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) y) < ENNReal.ofReal r ↔
      Manifold.riemannianEDist I (toWithMetric g x) (toWithMetric g y) <
        ENNReal.ofReal (r / Real.sqrt c) := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hs0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 := (ENNReal.ofReal_pos.2 hsqrt).ne'
  rw [riemannianEDist_rescale_const g hc x y]
  by_cases hr : 0 ≤ r
  · have hof : ENNReal.ofReal r =
        ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (r / Real.sqrt c) := by
      rw [← ENNReal.ofReal_mul hsqrt.le, mul_div_cancel₀ _ hsqrt.ne']
    rw [hof]
    constructor
    · intro h
      have h' := ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
        (ENNReal.inv_ne_top.2 hs0) h
      simpa [← mul_assoc, ENNReal.inv_mul_cancel hs0 ENNReal.ofReal_ne_top] using h'
    · exact ENNReal.mul_lt_mul_right hs0 ENNReal.ofReal_ne_top
  · push Not at hr
    have hdiv : r / Real.sqrt c ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr.le hsqrt.le
    simp [ENNReal.ofReal_of_nonpos hr.le, ENNReal.ofReal_of_nonpos hdiv]

/-- Pulling a metric back along a diffeomorphism preserves Riemannian extended distances on
`WithMetric`. -/
theorem riemannianEDist_pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (n + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) (x y : M) :
    Manifold.riemannianEDist I
        (toWithMetric (g.pullback Φ hf hinj) x)
        (toWithMetric (g.pullback Φ hf hinj) y) =
      Manifold.riemannianEDist J (toWithMetric g (Φ x)) (toWithMetric g (Φ y)) := by
  rw [riemannianEDist_eq_ofWithMetric, riemannianEDist_eq_ofWithMetric]
  exact g.riemannianEDist_pullback Φ hf hinj x y

end Distance

section Volume

/-- **Measure scaling under constant rescaling.** Multiplying `g` by a constant `c > 0` scales
the Riemannian volume measure by `c ^ (n / 2)`, where `n = Module.finrank ℝ E`. -/
theorem riemannianVolume_rescale_const [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) :
    riemannianVolume I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)) =
      ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) •
        (riemannianVolume I (WithMetric g)).map
          (fun x ↦ toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
            x.ofWithMetric) := by
  rw [riemannianVolume_rescale, MeasureTheory.withDensity_const, Measure.map_smul]
  exact (measurableEmbedding_toWithMetric_ofWithMetric (g := g) _).measurable.aemeasurable

/-- For any set `s`, multiplying `g` by a constant `c > 0` scales the volume of `s` by
`c ^ (n / 2)`. -/
theorem riemannianVolume_rescale_const_apply [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (s : Set M) :
    riemannianVolume I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (ofWithMetric ⁻¹' s) =
      ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) *
        riemannianVolume I (WithMetric g) (ofWithMetric ⁻¹' s) := by
  rw [riemannianVolume_rescale_const g hc, smul_apply, smul_eq_mul,
    (measurableEmbedding_toWithMetric_ofWithMetric (g := g) _).map_apply]
  rfl

/-- **Geodesic ball volume under constant rescaling.** In real dimension `N`,
`vol_{c g}(B_{c g}(x, r)) = c ^ (N / 2) * vol_g(B_g(x, r / √c))`. -/
theorem riemannianVolume_ball_rescale_const [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ) :
    riemannianVolume I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        {y | Manifold.riemannianEDist I
          (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x) y <
          ENNReal.ofReal r} =
      ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) *
        riemannianVolume I (WithMetric g)
          {y | Manifold.riemannianEDist I (toWithMetric g x) y <
            ENNReal.ofReal (r / Real.sqrt c)} := by
  set gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set s : Set M := {y | Manifold.riemannianEDist I (toWithMetric g x) (toWithMetric g y) <
    ENNReal.ofReal (r / Real.sqrt c)}
  have h1 : {y : WithMetric gc | Manifold.riemannianEDist I (toWithMetric gc x) y <
      ENNReal.ofReal r} = ofWithMetric ⁻¹' s := by
    ext y
    simpa [s, gc] using riemannianEDist_lt_rescale_const_iff g hc x y.ofWithMetric r
  have h2 : {y : WithMetric g | Manifold.riemannianEDist I (toWithMetric g x) y <
      ENNReal.ofReal (r / Real.sqrt c)} = ofWithMetric ⁻¹' s := by
    ext y
    rfl
  rw [h1, h2]
  exact riemannianVolume_rescale_const_apply g hc s

/-- **Scale-invariance of the normalized ball-volume ratio.** For any constant `a : ℝ≥0∞`,
`c > 0`, and `r : ℝ`, the lower bound `r^N * a ≤ vol_{c g}(B_{c g}(x, r))` holds if and only if
`(r / √c)^N * a ≤ vol_g(B_g(x, r / √c))`. -/
theorem mul_le_riemannianVolume_ball_rescale_const_iff [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ) (a : ℝ≥0∞) :
    ENNReal.ofReal (r ^ Module.finrank ℝ E) * a ≤
      riemannianVolume I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        {y | Manifold.riemannianEDist I
          (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x) y <
          ENNReal.ofReal r} ↔
    ENNReal.ofReal ((r / Real.sqrt c) ^ Module.finrank ℝ E) * a ≤
      riemannianVolume I (WithMetric g)
        {y | Manifold.riemannianEDist I (toWithMetric g x) y <
          ENNReal.ofReal (r / Real.sqrt c)} := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hcpow : c ^ ((Module.finrank ℝ E : ℝ) / 2) = (Real.sqrt c) ^ Module.finrank ℝ E := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (c ^ (1 / 2 : ℝ)), ← Real.rpow_mul hc.le]
    ring_nf
  have hpow : r ^ Module.finrank ℝ E =
      c ^ ((Module.finrank ℝ E : ℝ) / 2) * (r / Real.sqrt c) ^ Module.finrank ℝ E := by
    rw [hcpow, ← mul_pow, mul_div_cancel₀ _ hsqrt.ne']
  have hcpos : 0 < c ^ ((Module.finrank ℝ E : ℝ) / 2) := Real.rpow_pos_of_pos hc _
  have hcf0 : ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 hcpos).ne'
  set B : Set (WithMetric g) :=
    {y | Manifold.riemannianEDist I (toWithMetric g x) y < ENNReal.ofReal (r / Real.sqrt c)}
  rw [riemannianVolume_ball_rescale_const g hc x r, hpow,
    ENNReal.ofReal_mul hcpos.le, mul_assoc]
  constructor
  · intro h
    have h' : (ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)))⁻¹ *
        (ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) *
          (ENNReal.ofReal ((r / Real.sqrt c) ^ Module.finrank ℝ E) * a)) ≤
        (ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)))⁻¹ *
        (ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) *
          riemannianVolume I (WithMetric g) B) := by
      gcongr
    simpa [← mul_assoc, ENNReal.inv_mul_cancel hcf0 ENNReal.ofReal_ne_top] using h'
  · intro h
    gcongr

/-- **Total volume under constant rescaling.** On a compact manifold of real dimension `N`,
multiplying `g` by a constant `c > 0` multiplies total volume by `c ^ (N / 2)`. -/
@[simp]
theorem riemannianTotalVolume_rescale_const [CompactSpace M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) :
    riemannianTotalVolume I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)) =
      c ^ ((Module.finrank ℝ E : ℝ) / 2) * riemannianTotalVolume I (WithMetric g) := by
  rw [riemannianTotalVolume_rescale, integral_const, smul_eq_mul, mul_comm,
    riemannianTotalVolume_def]

/-- Pulling a metric back along a diffeomorphism `Φ : M ≃ₘ^∞ N` (between manifolds modeled over
the same vector space `E`) preserves the Riemannian volume measure on `WithMetric`. -/
theorem measurePreserving_pullback [LindelofSpace M]
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N] [LindelofSpace N]
    (g : ContMDiffRiemannianMetric I' n E (fun y : N ↦ TangentSpace I' y))
    (Φ : M ≃ₘ^∞⟮I, I'⟯ N) (hf : ContMDiff I I' (n + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I I' Φ x)) :
    MeasurePreserving
      (fun x : WithMetric (g.pullback Φ hf hinj) ↦ toWithMetric g (Φ x.ofWithMetric))
      (riemannianVolume I (WithMetric (g.pullback Φ hf hinj)))
      (riemannianVolume I' (WithMetric g)) := by
  let ψ : WithMetric (g.pullback Φ hf hinj) ≃ₜ WithMetric g :=
    ((homeomorph (g.pullback Φ hf hinj)).trans Φ.toHomeomorph).trans (homeomorph g).symm
  have hcoe : (ψ : WithMetric (g.pullback Φ hf hinj) → WithMetric g) =
      fun x ↦ toWithMetric g (Φ x.ofWithMetric) := by
    funext x
    simp [ψ]
  have hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' ψ x v, mfderiv I I' ψ x w⟫_ℝ = ⟪v, w⟫_ℝ := by
    intro x v w
    rw [hcoe]
    have hdiff₁ : MDifferentiableAt I I' (Φ ∘ ofWithMetric) x :=
      (Φ.contMDiff.mdifferentiable (by simp) _).comp x
        (hasMFDerivAt_ofWithMetric x).mdifferentiableAt
    have hmf : mfderiv I I' (fun y : WithMetric (g.pullback Φ hf hinj) ↦
          toWithMetric g (Φ y.ofWithMetric)) x =
        (mfderiv I' I' (toWithMetric g) (Φ x.ofWithMetric)).comp
          ((mfderiv I I' Φ x.ofWithMetric).comp (mfderiv I I ofWithMetric x)) := by
      change mfderiv I I' (toWithMetric g ∘ (Φ ∘ ofWithMetric)) x = _
      rw [mfderiv_comp x (hasMFDerivAt_toWithMetric _).mdifferentiableAt hdiff₁,
        mfderiv_comp_ofWithMetric]
      rfl
    rw [hmf, inner_def, inner_def]
    simp only [mfderiv_ofWithMetric, mfderiv_toWithMetric]
    exact (g.pullback_inner Φ hf hinj x.ofWithMetric v w).symm
  simpa only [hcoe] using ψ.measurePreserving_riemannianVolume hinner

/-- **Diffeomorphism invariance of geodesic ball volumes.** Pulling back a metric along a
diffeomorphism `Φ : M ≃ₘ^∞ N` preserves the Riemannian volume of every open geodesic ball. -/
theorem riemannianVolume_ball_pullback [LindelofSpace M]
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N] [LindelofSpace N]
    (g : ContMDiffRiemannianMetric I' n E (fun y : N ↦ TangentSpace I' y))
    (Φ : M ≃ₘ^∞⟮I, I'⟯ N) (hf : ContMDiff I I' (n + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I I' Φ x)) (x : M) (r : ℝ≥0∞) :
    riemannianVolume I (WithMetric (g.pullback Φ hf hinj))
        {y | Manifold.riemannianEDist I (toWithMetric (g.pullback Φ hf hinj) x) y < r} =
      riemannianVolume I' (WithMetric g)
        {y | Manifold.riemannianEDist I' (toWithMetric g (Φ x)) y < r} := by
  let ψ : WithMetric (g.pullback Φ hf hinj) ≃ₜ WithMetric g :=
    ((homeomorph (g.pullback Φ hf hinj)).trans Φ.toHomeomorph).trans (homeomorph g).symm
  have hcoe : (ψ : WithMetric (g.pullback Φ hf hinj) → WithMetric g) =
      fun x ↦ toWithMetric g (Φ x.ofWithMetric) := by
    funext y
    simp [ψ]
  have hmp : MeasurePreserving ψ
      (riemannianVolume I (WithMetric (g.pullback Φ hf hinj)))
      (riemannianVolume I' (WithMetric g)) := by
    simpa only [← hcoe] using measurePreserving_pullback g Φ hf hinj
  have hpre : ψ ⁻¹' {y | Manifold.riemannianEDist I' (toWithMetric g (Φ x)) y < r} =
      {y | Manifold.riemannianEDist I (toWithMetric (g.pullback Φ hf hinj) x) y < r} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hcoe]
    rw [← riemannianEDist_pullback g Φ hf hinj x y.ofWithMetric]
  rw [← hmp.map_eq, ψ.measurableEmbedding.map_apply, hpre]

end Volume

end TauCeti.WithMetric

end
