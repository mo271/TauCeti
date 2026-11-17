/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.Deriv
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Strongly geodesically convex neighbourhoods

A set `W` in a Riemannian manifold is *uniformly normal* (`TauCeti.Manifold.IsUniformlyNormal`)
if it is open and contained in a normal ball `exp_q '' B(0, r)` about each of its points `q ∈ W`.
It is *strongly geodesically convex* (`TauCeti.Manifold.IsStronglyGeodesicallyConvex`) if every
pair of points `x, y ∈ W` is joined by a unique globally minimizing geodesic segment on `[0, 1]`
and that segment stays in `W`. Uniform normality passes to open subsets, and strong geodesic
convexity passes to nonempty intersections; hence both properties pass to nonempty finite
intersections.

Following Lee (*Introduction to Riemannian Manifolds*, 2nd ed., Chapter 6, Lemma 6.16 and
Theorem 6.17), we prove that every point `p` has positive normal and strong-convexity radii
`r, δ > 0` such that every open Riemannian ball `Metric.eball q (ENNReal.ofReal ε)` with
`q ∈ Metric.eball p (ENNReal.ofReal δ)` and `0 < ε ≤ δ` is both uniformly normal and strongly
geodesically convex. Rather than computing Hessians in local coordinates, we evaluate the second
time derivative at `t = 0` of the smooth parametric squared-distance function
`G((q, z), t) = ‖log_q (exp_{z.proj} (t • z.2))‖²` near `(p, ⟨p, v⟩, 0)`: at `q = z.proj = p` it
reduces to `t² ‖v‖²`, whose second derivative at `0` is `2 ‖v‖² > 0`. By continuity of the second
time derivative and compactness of the unit sphere in a local trivialization, strict positivity
persists on a neighbourhood of `p`, yielding strict convexity of squared radial distance along
short geodesics and hence strong geodesic convexity of small balls. Covering a compact set by
finitely many such balls yields uniform positive normal and strong-convexity radii near any
compact set.

## Main definitions and results

* `TauCeti.Manifold.IsUniformlyNormal`: open sets lying inside a normal ball of each of their
  points, closed under open subsets and nonempty finite intersections.
* `TauCeti.Manifold.IsStronglyGeodesicallyConvex`: sets in which every pair of points is joined by
  a unique globally minimizing geodesic segment on `[0, 1]`, lying inside the set; closed under
  nonempty intersections.
* `TauCeti.Manifold.IsNormalDomain.eqOn_riemannianExp_smul_of_isGeodesicCurveOn_Icc_pathELength_eq`:
  unconditional uniqueness of globally minimizing geodesic segments on `[0, 1]` from the centre of
  a normal ball.
* `TauCeti.Manifold.exists_isOpen_strictConvexOn_norm_sq_riemannianLog`: strict convexity of
  squared local radial distance along nonconstant geodesics in a small neighbourhood (Lee,
  Lemma 6.16).
* `TauCeti.Manifold.exists_pos_forall_isNormalDomain_and_isStronglyGeodesicallyConvex_eball`:
  existence of locally uniform normal and strong-convexity radii (Lee, Theorem 6.17).
* `IsCompact.exists_pos_forall_isNormalDomain_and_isStronglyGeodesicallyConvex_eball`: uniform
  positive normal and strong-convexity radii near any compact set.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6,
  Lemma 6.16 and Theorem 6.17.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §4, Proposition 4.2.
-/

public section

noncomputable section

open Bundle Filter Function Manifold Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti.Manifold

/-! ### Parametric second time derivative -/

section ParametricDeriv

/-- For a `C²` function `f : E × ℝ → ℝ` near `(u₀, 0)`, the second partial derivative in the time
variable at `t = 0` is continuous in the spatial variable at `u₀`. -/
private theorem continuousAt_deriv_deriv_zero_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u₀ : E} (hf : ContDiffAt ℝ 2 f (u₀, 0)) :
    ContinuousAt (fun u : E ↦ deriv^[2] (fun t : ℝ ↦ f (u, t)) 0) u₀ := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) (u₀, 0) :=
    hf.fderiv_right (m := 1) (by norm_num)
  have h2cont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) (u₀, 0) :=
    h1.continuousAt_fderiv one_ne_zero
  -- Candidate continuous limit: `u ↦ ((D² f)(u, 0) (0, 1)) (0, 1)`.
  let g : E → ℝ :=
    fun u ↦ (fderiv ℝ (fderiv ℝ f) (u, 0) ((0 : E), (1 : ℝ))) ((0 : E), (1 : ℝ))
  have hg_cont : ContinuousAt g u₀ := by
    have hpair : ContinuousAt (fun u : E ↦ (u, (0 : ℝ))) u₀ :=
      continuousAt_id.prodMk continuousAt_const
    have hev1 : ContinuousAt
        (fun u : E ↦ fderiv ℝ (fderiv ℝ f) (u, 0) ((0 : E), (1 : ℝ))) u₀ :=
      (ContinuousLinearMap.apply ℝ (E × ℝ →L[ℝ] ℝ)
        ((0 : E), (1 : ℝ))).continuous.continuousAt.comp
        (h2cont.comp (f := fun u : E ↦ (u, (0 : ℝ))) hpair)
    exact (ContinuousLinearMap.apply ℝ ℝ ((0 : E), (1 : ℝ))).continuous.continuousAt.comp hev1
  -- On a neighbourhood of `(u₀, 0)`, `f` and `fderiv ℝ f` are differentiable.
  have hev : ∀ᶠ p : E × ℝ in 𝓝 (u₀, 0),
      DifferentiableAt ℝ f p ∧ DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.eventually (by norm_num)).and (h1.eventually (by norm_num))).mono fun p ⟨hfp, h1p⟩ ↦
      ⟨hfp.differentiableAt (by norm_num), h1p.differentiableAt one_ne_zero⟩
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hev
  have hV0 : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
  refine hg_cont.congr ?_
  filter_upwards [hU] with u hu
  have hd1 : deriv (fun t : ℝ ↦ f (u, t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ ↦ fderiv ℝ f (u, t) ((0 : E), (1 : ℝ)) := by
    filter_upwards [hV] with t ht
    have hι : HasDerivAt (fun s : ℝ ↦ (u, s)) ((0 : E), (1 : ℝ)) t :=
      (hasDerivAt_const t u).prodMk (hasDerivAt_id t)
    exact ((hUV (mk_mem_prod hu ht)).1.hasFDerivAt.comp_hasDerivAt t hι).deriv
  have hd2 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ f (u, t) ((0 : E), (1 : ℝ))) (g u) 0 := by
    have hι : HasDerivAt (fun s : ℝ ↦ (u, s)) ((0 : E), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) u).prodMk (hasDerivAt_id 0)
    have hdf : HasDerivAt (fun t : ℝ ↦ fderiv ℝ f (u, t))
        (fderiv ℝ (fderiv ℝ f) (u, 0) ((0 : E), (1 : ℝ))) 0 :=
      (hUV (mk_mem_prod hu hV0)).2.hasFDerivAt.comp_hasDerivAt 0 hι
    exact (ContinuousLinearMap.apply ℝ ℝ ((0 : E), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt 0 hdf
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  exact (hd1.deriv_eq.trans hd2.deriv).symm

/-- For a `C²` function `F : X × ℝ → ℝ` on a boundaryless manifold `X`, the second time
derivative at `t = 0` is continuous in the spatial point `x`. -/
private theorem continuousAt_deriv_deriv_zero_of_contMDiffAt
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [IX.Boundaryless]
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {F : X × ℝ → ℝ} {x₀ : X}
    (hF : ContMDiffAt (IX.prod 𝓘(ℝ)) 𝓘(ℝ) 2 F (x₀, 0)) :
    ContinuousAt (fun x : X ↦ deriv^[2] (fun t : ℝ ↦ F (x, t)) 0) x₀ := by
  let e := extChartAt IX x₀
  let f : EX × ℝ → ℝ := fun p ↦ F (e.symm p.1, p.2)
  have hf : ContDiffAt ℝ 2 f (e x₀, 0) := by
    rw [contMDiffAt_iff] at hF
    have hfun :
        (extChartAt 𝓘(ℝ) (F (x₀, 0)) ∘ F ∘ (extChartAt (IX.prod 𝓘(ℝ)) (x₀, 0)).symm) = f :=
      funext fun ⟨_, _⟩ ↦ rfl
    have hchart : ContDiffWithinAt ℝ 2 f (range (IX.prod 𝓘(ℝ))) (e x₀, 0) := by
      have h2 := hF.2
      rw [hfun] at h2
      simpa [e, extChartAt_prod, extChartAt_model_space_eq_id] using h2
    have hrange : range (IX.prod 𝓘(ℝ)) = univ := by
      rw [ModelWithCorners.range_prod, IX.range_eq_univ,
        (modelWithCornersSelf ℝ ℝ).range_eq_univ, univ_prod_univ]
    rwa [hrange, contDiffWithinAt_univ] at hchart
  have hcont_f : ContinuousAt (fun u : EX ↦ deriv^[2] (fun t : ℝ ↦ f (u, t)) 0) (e x₀) :=
    continuousAt_deriv_deriv_zero_of_contDiffAt hf
  have hcomp : ContinuousAt (fun x : X ↦ deriv^[2] (fun t : ℝ ↦ f (e x, t)) 0) x₀ :=
    hcont_f.comp (continuousAt_extChartAt x₀)
  refine hcomp.congr ?_
  filter_upwards
    [(isOpen_extChartAt_source (I := IX) x₀).mem_nhds (mem_extChartAt_source (I := IX) x₀)] with
    x hx
  simp only [f, e, (extChartAt IX x₀).left_inv hx]

/-- Scaling the input of a `C²` function `g : ℝ → ℝ` at `0` by `c` scales its second derivative
at `0` by `c ^ 2`. -/
private theorem deriv_deriv_comp_mul_zero {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0) (c : ℝ) :
    deriv^[2] (fun t : ℝ ↦ g (c * t)) 0 = c ^ 2 * deriv^[2] g 0 := by
  have hg1 : ContDiffAt ℝ 1 (deriv g) 0 := by
    have h := hg.fderiv_right (m := 1) (by norm_num)
    exact ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.contDiffAt.comp 0 h
      ).congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hdiff_g : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ g s :=
    (hg.eventually (by norm_num)).mono fun _ hs ↦ hs.differentiableAt (by norm_num)
  have hd1 :
      deriv (fun t : ℝ ↦ g (c * t)) =ᶠ[𝓝 (0 : ℝ)] fun t : ℝ ↦ c * deriv g (c * t) := by
    have hmul : ContinuousAt (fun t : ℝ ↦ c * t) 0 := continuousAt_const.mul continuousAt_id
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ g (c * t) :=
      hmul.eventually (by simpa only [mul_zero] using hdiff_g)
    filter_upwards [hmem] with t ht
    have hlin : HasDerivAt (fun s : ℝ ↦ c * s) c t := by
      simpa only [mul_one] using (hasDerivAt_id' t).const_mul c
    have hcomp := ht.hasDerivAt.comp t hlin
    simpa [Function.comp_def, mul_comm] using hcomp.deriv
  have hd2 : HasDerivAt (fun t : ℝ ↦ c * deriv g (c * t)) (c ^ 2 * deriv (deriv g) 0) 0 := by
    have hlin : HasDerivAt (fun s : ℝ ↦ c * s) c 0 := by
      simpa only [mul_one] using (hasDerivAt_id' (0 : ℝ)).const_mul c
    have hdg0 : HasDerivAt (deriv g) (deriv (deriv g) 0) (c * 0) := by
      rw [mul_zero]
      exact (hg1.differentiableAt one_ne_zero).hasDerivAt
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ c * deriv g (c * t)) (c * (deriv (deriv g) 0 * c)) 0 :=
      (hdg0.comp 0 hlin).const_mul c
    convert hcomp using 1
    ring
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  exact hd1.deriv_eq.trans hd2.deriv

end ParametricDeriv

/-! ### Uniformly normal and strongly geodesically convex sets -/

section UniformlyNormal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- A subset `W` of a Riemannian manifold is **uniformly normal** if it is open and, for every
point `q ∈ W`, there exists a positive radius `r` such that the tangent ball `Metric.ball 0 r` at
`q` is a normal domain whose exponential image contains `W`. -/
structure IsUniformlyNormal (W : Set M) : Prop where
  /-- A uniformly normal set is open. -/
  isOpen : IsOpen W
  /-- At every point `q ∈ W`, some normal ball has exponential image containing `W`. -/
  exists_radius : ∀ q ∈ W, ∃ r : ℝ, 0 < r ∧ IsNormalDomain I M q (Metric.ball 0 r) ∧
    W ⊆ riemannianExp I M q '' Metric.ball 0 r

namespace IsUniformlyNormal

variable {V W : Set M}

/-- An open subset of a uniformly normal set is uniformly normal. -/
theorem mono (hW : IsUniformlyNormal I M W) (hVW : V ⊆ W) (hVo : IsOpen V) :
    IsUniformlyNormal I M V where
  isOpen := hVo
  exists_radius q hq := by
    obtain ⟨r, hr, hN, hsub⟩ := hW.exists_radius q (hVW hq)
    exact ⟨r, hr, hN, hVW.trans hsub⟩

/-- The intersection of two uniformly normal sets is uniformly normal. -/
theorem inter (hV : IsUniformlyNormal I M V) (hW : IsUniformlyNormal I M W) :
    IsUniformlyNormal I M (V ∩ W) :=
  hV.mono inter_subset_left (hV.isOpen.inter hW.isOpen)

/-- A nonempty finite intersection of uniformly normal sets is uniformly normal. -/
theorem biInter {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {U : ι → Set M}
    (hU : ∀ i ∈ s, IsUniformlyNormal I M (U i)) :
    IsUniformlyNormal I M (⋂ i ∈ s, U i) := by
  obtain ⟨i₀, hi₀⟩ := hs
  exact (hU i₀ hi₀).mono (biInter_subset_of_mem hi₀)
    (isOpen_biInter_finset fun i hi ↦ (hU i hi).isOpen)

end IsUniformlyNormal

end UniformlyNormal

/-! ### Strict convexity of squared radial distance (Lee, Lemma 6.16) -/

section StrictConvexity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Auxiliary parametric squared radial distance along a geodesic starting at `z`:
`G((q, z), t) = ‖log_q (exp_{z.proj} (t • z.2))‖²`. -/
private def sqLogExp (r : ℝ) (a : (M × TangentBundle I M) × ℝ) : ℝ :=
  ‖riemannianLog I M a.1.1 (Metric.ball 0 r)
    (riemannianExp I M a.1.2.proj (a.2 • a.1.2.2))‖ ^ 2

/-- At `q = z.proj = p`, the second time derivative of `sqLogExp r` at `0` is `2 * ‖v‖²`. -/
private theorem deriv_deriv_sqLogExp_self {p : M} {r : ℝ} (hr : 0 < r)
    (hN : IsNormalDomain I M p (Metric.ball 0 r)) (v : TangentSpace I p) :
    deriv^[2] (fun t : ℝ ↦ sqLogExp (I := I) (M := M) r ((p, TotalSpace.mk' E p v), t)) 0 =
      2 * ‖v‖ ^ 2 := by
  have hev : (fun t : ℝ ↦
        sqLogExp (I := I) (M := M) r ((p, TotalSpace.mk' E p v), t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ ↦ t ^ 2 * ‖v‖ ^ 2 := by
    have hball : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t • v ∈ Metric.ball (0 : TangentSpace I p) r := by
      have hcont : ContinuousAt (fun t : ℝ ↦ t • v) 0 :=
        continuousAt_id.smul continuousAt_const
      refine hcont.eventually ?_
      dsimp only
      rw [zero_smul]
      exact Metric.ball_mem_nhds 0 hr
    filter_upwards [hball] with t ht
    simp only [sqLogExp, hN.riemannianLog_riemannianExp ht, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
  rw [← iteratedDeriv_eq_iterate, hev.iteratedDeriv_eq 2, iteratedDeriv_mul_const_field,
    iteratedDeriv_pow]
  norm_num

variable [I.Boundaryless] [T2Space M]

/-- The radial geodesic `t ↦ exp_p (t • v)` on `[0, 1]` for a vector `v` in a normal domain is a
geodesic segment on `[0, 1]`. -/
private theorem IsNormalDomain.isGeodesicCurveOn_riemannianExp_smul
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    {v : TangentSpace I p} (hv : v ∈ U) :
    IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    fun t ht ↦ h.mem_geodesicInterval hv ht.1 ht.2
  have hmax : IsGeodesicCurveOn I (maximalGeodesic I M p v) (Icc 0 1) :=
    ((isGeodesicCurveOnFrom_maximalGeodesic (I := I) p v).mono
      (uniqueDiffOn_Icc zero_lt_one) hsub (left_mem_Icc.2 zero_le_one)).isGeodesicCurveOn
  have hfun : (fun t : ℝ ↦ riemannianExp I M p (t • v)) = maximalGeodesic I M p v :=
    funext fun t ↦ riemannianExp_smul p v t
  rwa [hfun]

/-- `sqLogExp r` is smooth at `((q, z), 0)` whenever `q` lies in an open set `W` of uniform normal
radius `r` and `z.proj ∈ exp_q '' B(0, r)`. -/
private theorem contMDiffAt_sqLogExp_zero {W : Set M} {r : ℝ}
    (hWo : IsOpen W) (hW : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r))
    {q : M} (hq : q ∈ W) (z : TangentBundle I M)
    (hz : z.proj ∈ riemannianExp I M q '' Metric.ball 0 r) :
    ContMDiffAt ((I.prod I.tangent).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (sqLogExp (I := I) (M := M) r)
      ((q, z), 0) := by
  -- Step 1: `((q, z), t) ↦ ⟨z.proj, t • z.2⟩` is smooth.
  have hsmul : ContMDiffAt ((I.prod I.tangent).prod 𝓘(ℝ)) I.tangent ∞
      (fun a : (M × TangentBundle I M) × ℝ ↦
        (TotalSpace.mk' E a.1.2.proj (a.2 • a.1.2.2) : TangentBundle I M))
      ((q, z), 0) :=
    contMDiffAt_snd.smul_totalSpace (contMDiffAt_snd.comp ((q, z), 0) contMDiffAt_fst)
  -- Step 2: `exp` is smooth at `⟨z.proj, 0 • z.2⟩ = ⟨z.proj, 0⟩`.
  have h0dom : (TotalSpace.mk' E z.proj ((0 : ℝ) • z.2) : TangentBundle I M) ∈
      {w : TangentBundle I M | w.2 ∈ expDomain I M w.proj} := by
    simpa only [mem_ofPred_eq, zero_smul] using zero_mem_expDomain (I := I) (M := M) z.proj
  have hexp : ContMDiffAt ((I.prod I.tangent).prod 𝓘(ℝ)) I ∞
      (fun a : (M × TangentBundle I M) × ℝ ↦ riemannianExp I M a.1.2.proj (a.2 • a.1.2.2))
      ((q, z), 0) :=
    (contMDiffOn_riemannianExp_tangentBundle.contMDiffAt
      (isOpen_setOfPred_mem_expDomain.mem_nhds h0dom)).comp ((q, z), 0) hsmul
  -- Step 3: `(q, exp_{z.proj}(t • z.2)) ↦ ⟨q, log_q (exp_{z.proj}(t • z.2))⟩` is smooth.
  have hpair : ContMDiffAt ((I.prod I.tangent).prod 𝓘(ℝ)) (I.prod I) ∞
      (fun a : (M × TangentBundle I M) × ℝ ↦
        (a.1.1, riemannianExp I M a.1.2.proj (a.2 • a.1.2.2)))
      ((q, z), 0) :=
    (contMDiffAt_fst.comp ((q, z), 0) contMDiffAt_fst).prodMk hexp
  have hPopen :
      IsOpen {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} :=
    isOpen_setOf_mem_riemannianExp_image_ball hWo
      (fun x hx ↦ (hW x hx).subset_expDomain) (fun x hx ↦ (hW x hx).isLocalDiffeomorphOn)
  have hPmem : (q, riemannianExp I M z.proj ((0 : ℝ) • z.2)) ∈
      {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} := by
    simpa only [mem_ofPred_eq, zero_smul, riemannianExp_zero] using ⟨hq, hz⟩
  have hlog : ContMDiffAt ((I.prod I.tangent).prod 𝓘(ℝ)) I.tangent ∞
      (fun a : (M × TangentBundle I M) × ℝ ↦
        (⟨a.1.1, riemannianLog I M a.1.1 (Metric.ball 0 r)
          (riemannianExp I M a.1.2.proj (a.2 • a.1.2.2))⟩ : TangentBundle I M))
      ((q, z), 0) :=
    ((contMDiffOn_totalSpaceMk_riemannianLog hWo hW).contMDiffAt (hPopen.mem_nhds hPmem)).comp
      ((q, z), 0) hpair
  -- Step 4: compose with `w ↦ ‖w.2‖² = inner ℝ w.2 w.2`.
  have hsq : ContMDiff I.tangent 𝓘(ℝ) ∞ (fun w : TangentBundle I M ↦ ‖w.2‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using
      (contMDiff_id (I := I.tangent) (n := ∞)).inner_bundle contMDiff_id
  exact (hsq.contMDiffAt).comp ((q, z), 0) hlog

/-- Continuity and strict positivity at `(p, p, w)` (`‖w‖ = 1`) of the second time derivative of
`sqLogExp r` pulled back through the preferred local trivialization `trivializationAt` at `p`. -/
private theorem continuousAt_and_pos_deriv_deriv_sqLogExp_trivializationAt
    {p : M} {r : ℝ} (hr : 0 < r) {W : Set M} (hWo : IsOpen W) (hpW : p ∈ W)
    (hWN : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r))
    (hWsub : ∀ q ∈ W, W ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    let e := trivializationAt E (TangentSpace I) p
    let Φ : (M × M) × E → ℝ := fun a ↦
      deriv^[2] (fun t : ℝ ↦
        sqLogExp (I := I) (M := M) r ((a.1.1, e.toOpenPartialHomeomorph.symm (a.1.2, a.2)), t)) 0
    (∀ w ∈ Metric.sphere (0 : E) 1, 0 < Φ ((p, p), w)) ∧
      (∀ w : E, ContinuousAt Φ ((p, p), w)) := by
  intro e Φ
  have hpe : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
  let H : M × TangentBundle I M → ℝ :=
    fun a ↦ deriv^[2] (fun t : ℝ ↦ sqLogExp (I := I) (M := M) r (a, t)) 0
  refine ⟨fun w hw ↦ ?_, fun w ↦ ?_⟩
  · have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hw
      exact zero_ne_one hw
    have hv0 : e.symm p w ≠ 0 := by
      rw [← e.linearEquivAt_symm_apply (R := ℝ) p hpe]
      exact (e.linearEquivAt ℝ p hpe).symm.map_ne_zero_iff.2 hw0
    dsimp only [Φ]
    rw [← e.mk_symm hpe w, deriv_deriv_sqLogExp_self hr (hWN p hpW) (e.symm p w)]
    positivity
  · have hH_cont : ContinuousAt H (p, e.toOpenPartialHomeomorph.symm (p, w)) := by
      have hzproj : (e.toOpenPartialHomeomorph.symm (p, w)).proj = p := e.symm_coe_proj hpe
      have hG := contMDiffAt_sqLogExp_zero hWo hWN hpW
        (e.toOpenPartialHomeomorph.symm (p, w)) (hzproj.symm ▸ hWsub p hpW hpW)
      exact continuousAt_deriv_deriv_zero_of_contMDiffAt (hG.of_le (by simp))
    have htarget : (p, w) ∈ e.toOpenPartialHomeomorph.target := by
      rw [e.target_eq]
      exact ⟨hpe, mem_univ w⟩
    have hcs : ContinuousAt (fun z : M × E ↦ e.toOpenPartialHomeomorph.symm z) (p, w) :=
      e.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
        (e.toOpenPartialHomeomorph.open_target.mem_nhds htarget)
    have h1 : ContinuousAt (fun a : (M × M) × E ↦ a.1.1) ((p, p), w) :=
      continuousAt_fst.comp continuousAt_fst
    have h2 : ContinuousAt (fun a : (M × M) × E ↦ (a.1.2, a.2)) ((p, p), w) :=
      (continuousAt_snd.comp continuousAt_fst).prodMk continuousAt_snd
    have hcs2 : ContinuousAt (fun a : (M × M) × E ↦
        e.toOpenPartialHomeomorph.symm (a.1.2, a.2)) ((p, p), w) :=
      hcs.comp (f := fun a : (M × M) × E ↦ (a.1.2, a.2)) h2
    exact hH_cont.comp (f := fun a : (M × M) × E ↦
      (a.1.1, e.toOpenPartialHomeomorph.symm (a.1.2, a.2))) (h1.prodMk hcs2)

/-- Homogeneity of the second time derivative of `sqLogExp r` at `t = 0`: positivity along
`c⁻¹ • v` with `0 < c` implies positivity along `v`. -/
private theorem deriv_deriv_sqLogExp_pos_of_pos_inv_smul {W : Set M} {r : ℝ}
    (hWo : IsOpen W) (hWN : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r))
    {q x : M} (hq : q ∈ W) (hx : x ∈ riemannianExp I M q '' Metric.ball 0 r)
    {v : TangentSpace I x} {c : ℝ} (hc : 0 < c)
    (hpos : 0 < deriv^[2] (fun t : ℝ ↦
      sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E x (c⁻¹ • v)), t)) 0) :
    0 < deriv^[2] (fun t : ℝ ↦
      sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E x v), t)) 0 := by
  have hG_smooth : ContMDiffAt ((I.prod I.tangent).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (sqLogExp (I := I) (M := M) r) ((q, TotalSpace.mk' E x (c⁻¹ • v)), 0) :=
    contMDiffAt_sqLogExp_zero hWo hWN hq (TotalSpace.mk' E x (c⁻¹ • v)) hx
  have hg_contDiff : ContDiffAt ℝ 2 (fun t : ℝ ↦
      sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E x (c⁻¹ • v)), t)) 0 :=
    contMDiffAt_iff_contDiffAt.1
      ((hG_smooth.of_le (by simp)).comp 0 (contMDiffAt_const.prodMk contMDiffAt_id))
  have hscale : (fun t : ℝ ↦ sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E x v), t)) =
      fun t : ℝ ↦
        sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E x (c⁻¹ • v)), c * t) := by
    funext t
    simp only [sqLogExp, smul_smul]
    have hct : c * t * c⁻¹ = t := by field_simp [hc.ne']
    rw [hct]
  rw [hscale, deriv_deriv_comp_mul_zero hg_contDiff c]
  exact mul_pos (sq_pos_of_pos hc) hpos

/-- On a small open neighbourhood `V` of `p`, the second time derivative of `sqLogExp r` at `0` is
strictly positive for every `q, x ∈ V` and every nonzero tangent vector `v ∈ T_x M`. -/
private theorem exists_isOpen_deriv_deriv_sqLogExp_pos (p : M) :
    ∃ r > 0, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      (∀ q ∈ V, IsNormalDomain I M q (Metric.ball 0 r) ∧
        V ⊆ riemannianExp I M q '' Metric.ball 0 r) ∧
      (∀ q ∈ V, ∀ x ∈ V, ∀ v : TangentSpace I x, v ≠ 0 →
        0 < deriv^[2] (fun t : ℝ ↦
          sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E x v), t)) 0) := by
  obtain ⟨r, hr, W₀, hW₀, hRW₀⟩ :=
    exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p
  set W : Set M := interior W₀
  have hWo : IsOpen W := isOpen_interior
  have hpW : p ∈ W := mem_interior_iff_mem_nhds.2 hW₀
  have hWN : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r) :=
    fun q hq ↦ (hRW₀ q (interior_subset hq)).1
  have hWsub : ∀ q ∈ W, W ⊆ riemannianExp I M q '' Metric.ball 0 r :=
    fun q hq ↦ interior_subset.trans (hRW₀ q (interior_subset hq)).2
  let e := trivializationAt E (TangentSpace I) p
  have hpe : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
  let Φ : (M × M) × E → ℝ := fun a ↦
    deriv^[2] (fun t : ℝ ↦
      sqLogExp (I := I) (M := M) r ((a.1.1, e.toOpenPartialHomeomorph.symm (a.1.2, a.2)), t)) 0
  obtain ⟨hΦ_pos, hΦ_cont⟩ :=
    continuousAt_and_pos_deriv_deriv_sqLogExp_trivializationAt hr hWo hpW hWN hWsub
  -- Compactness of `sphere (0 : E) 1` produces a single open neighbourhood `V` of `p`.
  have htube : ∀ w ∈ Metric.sphere (0 : E) 1,
      ∃ U₁ : Set M, IsOpen U₁ ∧ p ∈ U₁ ∧ ∃ O : Set E, IsOpen O ∧ w ∈ O ∧
        ∀ q ∈ U₁, ∀ x ∈ U₁, ∀ u ∈ O, 0 < Φ ((q, x), u) := by
    intro w hw
    have hnhds : {a : (M × M) × E | 0 < Φ a} ∈ 𝓝 ((p, p), w) :=
      (hΦ_cont w).eventually (isOpen_Ioi.mem_nhds (hΦ_pos w hw))
    obtain ⟨A, hA, O₀, hO₀, hAO⟩ := mem_nhds_prod_iff.1 hnhds
    obtain ⟨U₁, hU₁, U₂, hU₂, hU₁₂⟩ := mem_nhds_prod_iff.1 hA
    refine ⟨interior (U₁ ∩ U₂), isOpen_interior,
      mem_interior_iff_mem_nhds.2 (inter_mem hU₁ hU₂), interior O₀, isOpen_interior,
      mem_interior_iff_mem_nhds.2 hO₀, fun q hq x hx u hu ↦
        hAO (mk_mem_prod (hU₁₂ (mk_mem_prod (interior_subset hq).1 (interior_subset hx).2))
          (interior_subset hu))⟩
  choose U₁ hU₁_open hpU₁ O hO_open hwO hpos using htube
  obtain ⟨t, ht_cov⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover
    (fun w : {w : E // w ∈ Metric.sphere (0 : E) 1} ↦ O w.1 w.2)
    (fun w ↦ hO_open w.1 w.2) (fun w hw ↦ mem_iUnion.2 ⟨⟨w, hw⟩, hwO w hw⟩)
  set V : Set M := W ∩ e.baseSet ∩ ⋂ w ∈ t, U₁ w.1 w.2
  refine ⟨r, hr, V,
    (hWo.inter e.open_baseSet).inter (isOpen_biInter_finset fun w _ ↦ hU₁_open w.1 w.2),
    ⟨⟨hpW, hpe⟩, mem_iInter₂.2 fun w _ ↦ hpU₁ w.1 w.2⟩,
    fun q hq ↦
      ⟨hWN q hq.1.1, (inter_subset_left.trans inter_subset_left).trans (hWsub q hq.1.1)⟩,
    fun q hq x hx v hv ↦ ?_⟩
  let L := e.linearEquivAt ℝ x hx.1.2
  have hw₀ : L v ≠ 0 := L.map_ne_zero_iff.2 hv
  set c : ℝ := ‖L v‖
  have hc : 0 < c := norm_pos_iff.2 hw₀
  have hu_sphere : c⁻¹ • L v ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
  obtain ⟨w, hwt, huO⟩ := mem_iUnion₂.1 (ht_cov hu_sphere)
  have hpos_u : 0 < Φ ((q, x), c⁻¹ • L v) :=
    hpos w.1 w.2 q (mem_iInter₂.1 hq.2 w hwt) x (mem_iInter₂.1 hx.2 w hwt) (c⁻¹ • L v) huO
  have heu :
      e.toOpenPartialHomeomorph.symm (x, c⁻¹ • L v) = TotalSpace.mk' E x (c⁻¹ • v) := by
    rw [← e.mk_symm hx.1.2, ← e.linearEquivAt_symm_apply (R := ℝ) x hx.1.2, map_smul]
    exact congrArg (TotalSpace.mk' E x) (by rw [L.symm_apply_apply v])
  dsimp only [Φ] at hpos_u
  rw [heu] at hpos_u
  exact deriv_deriv_sqLogExp_pos_of_pos_inv_smul hWo hWN hq.1.1 (hWsub q hq.1.1 hx.1.1) hc hpos_u

/-- **Strict convexity of squared local radial distance along short geodesics** (Lee, Lemma 6.16).
Every point `p` has a radius `r > 0` and an open neighbourhood `V` of `p` such that, for every
`q ∈ V`, `Metric.ball 0 r` is a normal domain at `q` with `V ⊆ exp_q '' B(0, r)`, and for every
nonconstant geodesic segment `γ(t) = maximalGeodesic I M x v t` on `[a, b]` lying in `V`, the
squared local radial distance `t ↦ ‖log_q (γ t)‖²` is strictly convex on `[a, b]`. -/
theorem exists_isOpen_strictConvexOn_norm_sq_riemannianLog (p : M) :
    ∃ r > 0, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      (∀ q ∈ V, IsNormalDomain I M q (Metric.ball 0 r) ∧
        V ⊆ riemannianExp I M q '' Metric.ball 0 r) ∧
      ∀ q ∈ V, ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 →
        ∀ a b : ℝ, Icc a b ⊆ geodesicInterval I M x v →
          MapsTo (maximalGeodesic I M x v) (Icc a b) V →
          StrictConvexOn ℝ (Icc a b) (fun t : ℝ ↦
            ‖riemannianLog I M q (Metric.ball 0 r) (maximalGeodesic I M x v t)‖ ^ 2) := by
  obtain ⟨r, hr, V, hVo, hpV, hVN, hpos⟩ :=
    exists_isOpen_deriv_deriv_sqLogExp_pos (I := I) (M := M) p
  refine ⟨r, hr, V, hVo, hpV, hVN, fun q hq x v hv a b hJ hmaps ↦ ?_⟩
  set γ := maximalGeodesic I M x v
  set φ : ℝ → ℝ := fun t ↦ ‖riemannianLog I M q (Metric.ball 0 r) (γ t)‖ ^ 2
  have hφ_cont : ContinuousOn φ (Icc a b) := by
    have hγ_cont : ContinuousOn γ (Icc a b) :=
      ((isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) x v).isGeodesicCurveOn.contMDiffOn
        ).continuousOn.mono hJ
    have hlog_cont : ContinuousOn (riemannianLog I M q (Metric.ball 0 r)) V :=
      (hVN q hq).1.continuousOn_riemannianLog.mono (hVN q hq).2
    exact (hlog_cont.comp hγ_cont hmaps).norm.pow 2
  refine strictConvexOn_of_deriv2_pos (convex_Icc a b) hφ_cont fun s hs ↦ ?_
  have hsab : s ∈ Icc a b := interior_subset hs
  have hsJ : s ∈ geodesicInterval I M x v := hJ hsab
  set w : TangentSpace I (γ s) := curveVelocityWithin I γ (geodesicInterval I M x v) s
  have hw0 : w ≠ 0 := by
    have hmax := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) x v
    have hnorm : ‖w‖ = ‖v‖ := by
      rw [hmax.isGeodesicCurveOn.norm_curveVelocityWithin_eq isPreconnected_geodesicInterval hsJ
        zero_mem_geodesicInterval]
      exact congrArg (fun z : TangentBundle I M ↦ ‖z.2‖) hmax.initial_eq
    rw [← norm_ne_zero_iff, hnorm]
    exact norm_ne_zero_iff.2 hv
  have hev : (fun t : ℝ ↦ φ (s + t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ ↦ sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E (γ s) w), t) := by
    have hnhds : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), s + t ∈ geodesicInterval I M x v := by
      have hcont : ContinuousAt (fun t : ℝ ↦ s + t) 0 := continuousAt_const.add continuousAt_id
      refine hcont.eventually ?_
      dsimp only
      rw [add_zero]
      exact isOpen_geodesicInterval.mem_nhds hsJ
    filter_upwards [hnhds] with t ht
    simp only [φ, sqLogExp, riemannianExp_smul, ← maximalGeodesic_add hsJ ht, γ, w]
  have hd2 : deriv^[2] φ s = deriv^[2] (fun t : ℝ ↦
      sqLogExp (I := I) (M := M) r ((q, TotalSpace.mk' E (γ s) w), t)) 0 := by
    have hshift := congrFun (iteratedDeriv_comp_const_add 2 φ s) 0
    rw [add_zero] at hshift
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate, ← hshift]
    exact hev.iteratedDeriv_eq 2
  rw [hd2]
  exact hpos q hq (γ s) (hmaps hsab) w hw0

end StrictConvexity

section StrongConvexity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- A subset `W` of a Riemannian manifold is **strongly geodesically convex** (in Lee's sense) if
every pair of points `x, y ∈ W` is joined by a globally minimizing geodesic segment on `[0, 1]`
lying entirely in `W`, and every globally minimizing geodesic segment on `[0, 1]` in `M` from `x`
to `y` agrees with it on `[0, 1]`. -/
def IsStronglyGeodesicallyConvex (W : Set M) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W,
    ∃ γ : ℝ → M,
      IsGeodesicCurveOn I γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
        pathELength I γ 0 1 = edist x y ∧ MapsTo γ (Icc 0 1) W ∧
      ∀ δ : ℝ → M,
        IsGeodesicCurveOn I δ (Icc 0 1) → δ 0 = x → δ 1 = y →
          pathELength I δ 0 1 = edist x y → EqOn δ γ (Icc 0 1)

namespace IsStronglyGeodesicallyConvex

/-- The intersection of two strongly geodesically convex sets is strongly geodesically convex. -/
theorem inter {V W : Set M}
    (hV : IsStronglyGeodesicallyConvex I M V) (hW : IsStronglyGeodesicallyConvex I M W) :
    IsStronglyGeodesicallyConvex I M (V ∩ W) := by
  intro x hx y hy
  obtain ⟨γ, hγ, hγ0, hγ1, hlen, hγV, huniqV⟩ := hV x hx.1 y hy.1
  obtain ⟨γ', hγ', hγ'0, hγ'1, hlen', hγ'W, _⟩ := hW x hx.2 y hy.2
  have heq : EqOn γ' γ (Icc 0 1) := huniqV γ' hγ' hγ'0 hγ'1 hlen'
  exact ⟨γ, hγ, hγ0, hγ1, hlen, fun t ht ↦ ⟨hγV ht, heq ht ▸ hγ'W ht⟩, huniqV⟩

/-- A nonempty intersection of strongly geodesically convex sets is strongly geodesically
convex. -/
theorem iInter {ι : Type*} [Nonempty ι] {U : ι → Set M}
    (hU : ∀ i, IsStronglyGeodesicallyConvex I M (U i)) :
    IsStronglyGeodesicallyConvex I M (⋂ i, U i) := by
  intro x hx y hy
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨γ, hγ, hγ0, hγ1, hlen, _, huniq⟩ :=
    hU i₀ x (mem_iInter.1 hx i₀) y (mem_iInter.1 hy i₀)
  refine ⟨γ, hγ, hγ0, hγ1, hlen, fun t ht ↦ mem_iInter.2 fun i ↦ ?_, huniq⟩
  obtain ⟨γi, hγi, hγi0, hγi1, hleni, hγiU, _⟩ :=
    hU i x (mem_iInter.1 hx i) y (mem_iInter.1 hy i)
  exact (huniq γi hγi hγi0 hγi1 hleni ht) ▸ hγiU ht

/-- A nonempty finite intersection of strongly geodesically convex sets is strongly geodesically
convex. -/
theorem biInter {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {U : ι → Set M}
    (hU : ∀ i ∈ s, IsStronglyGeodesicallyConvex I M (U i)) :
    IsStronglyGeodesicallyConvex I M (⋂ i ∈ s, U i) := by
  have : Nonempty {i // i ∈ s} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  simpa only [iInter_subtype] using
    iInter (U := fun i : {i // i ∈ s} ↦ U i.1) fun i ↦ hU i.1 i.2

end IsStronglyGeodesicallyConvex

/-! ### Uniqueness of minimizing geodesic segments on `[0, 1]` -/

variable [I.Boundaryless] [IsRiemannianManifold I M]

/-- **Uniqueness of globally minimizing geodesic segments on `[0, 1]` from the centre of a normal
ball.** Any geodesic segment on `[0, 1]` from `p` to `exp_p v` (with `v ∈ Metric.ball 0 r` inside
a normal ball) whose length equals `edist p (exp_p v)` coincides with `t ↦ exp_p (t • v)` on
`[0, 1]`. The competitor is not assumed to stay in the normal ball or to extend past `[0, 1]`. -/
theorem IsNormalDomain.eqOn_riemannianExp_smul_of_isGeodesicCurveOn_Icc_pathELength_eq
    {p : M} {r : ℝ} (h : IsNormalDomain I M p (Metric.ball (0 : TangentSpace I p) r))
    {v : TangentSpace I p} (hv : v ∈ Metric.ball (0 : TangentSpace I p) r)
    {γ : ℝ → M} (hγ : IsGeodesicCurveOn I γ (Icc 0 1)) (hγ0 : γ 0 = p)
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 = edist p (riemannianExp I M p v)) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  subst hγ0
  set u : TangentSpace I (γ 0) := curveVelocityWithin I γ (Icc 0 1) 0
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hlen_u : pathELength I γ 0 1 = ‖u‖ₑ := by
    simpa [u] using hγ.pathELength_eq isPreconnected_Icc h0 h1 h0
  have hnorm : ‖u‖ = ‖v‖ := by
    have he : ‖u‖ₑ = ‖v‖ₑ := by
      rw [← hlen_u, hlen, h.edist_riemannianExp_eq_of_mem_ball subset_rfl hv]
    exact eNorm_eq_iff_norm_eq.mp he
  have hu : u ∈ Metric.ball (0 : TangentSpace I (γ 0)) r := by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hv
  have hfrom : IsGeodesicCurveOnFrom I γ (Icc 0 1) (γ 0) u :=
    ⟨hγ, h0, rfl⟩
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M (γ 0) u :=
    fun t ht ↦ h.mem_geodesicInterval hu ht.1 ht.2
  have heq : EqOn (maximalGeodesic I M (γ 0) u) γ (Icc 0 1) :=
    hfrom.eqOn_maximalGeodesic_of_subset isPreconnected_Icc hsub
  have huv : u = v := h.injOn hu hv (by
    rw [riemannianExp_def, heq h1, hγ1])
  intro t ht
  rw [← heq ht, huv, ← riemannianExp_smul]

/-- In a strongly geodesically convex set `W` contained in a normal ball `exp_q '' B(0, r)` at
`q ∈ W`, every radial geodesic segment `t ↦ exp_q (t • log_q x)` for `x ∈ W`, `t ∈ [0, 1]` stays
in `W`. -/
theorem IsStronglyGeodesicallyConvex.mapsTo_riemannianExp_smul_riemannianLog
    {W : Set M} (hW : IsStronglyGeodesicallyConvex I M W)
    {q : M} (hq : q ∈ W) {r : ℝ} (hN : IsNormalDomain I M q (Metric.ball 0 r))
    (hWr : W ⊆ riemannianExp I M q '' Metric.ball 0 r) {x : M} (hx : x ∈ W) :
    MapsTo (fun t : ℝ ↦ riemannianExp I M q (t • riemannianLog I M q (Metric.ball 0 r) x))
      (Icc 0 1) W := by
  set v := riemannianLog I M q (Metric.ball 0 r) x
  have hv : v ∈ Metric.ball (0 : TangentSpace I q) r := riemannianLog_mem (hWr hx)
  have hexp_v : riemannianExp I M q v = x := riemannianExp_riemannianLog (hWr hx)
  obtain ⟨γ, _, _, _, _, hγW, huniq⟩ := hW q hq x hx
  have hrad_geo : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M q (t • v)) (Icc 0 1) :=
    hN.isGeodesicCurveOn_riemannianExp_smul hv
  have hrad_len :
      pathELength I (fun t : ℝ ↦ riemannianExp I M q (t • v)) 0 1 = edist q x := by
    simpa only [hexp_v] using hN.pathELength_riemannianExp_smul_eq_edist_of_mem_ball subset_rfl hv
  have heq : EqOn (fun t : ℝ ↦ riemannianExp I M q (t • v)) γ (Icc 0 1) :=
    huniq _ hrad_geo (by simp) (by simp [hexp_v]) hrad_len
  intro t ht
  exact heq ht ▸ hγW ht

/-! ### Strongly geodesically convex balls (Lee, Theorem 6.17) -/

/-- The radial geodesic between two points of `Metric.eball q (ENNReal.ofReal ε)` stays inside
`Metric.eball p (ENNReal.ofReal (4 * δ))` whenever `q ∈ Metric.eball p (ENNReal.ofReal δ)` and
`0 < ε ≤ δ`. -/
private theorem mapsTo_maximalGeodesic_of_mem_eball
    {p q x y : M} {r δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hq : q ∈ Metric.eball p (ENNReal.ofReal δ))
    (hx : x ∈ Metric.eball q (ENNReal.ofReal ε))
    (hy : y ∈ Metric.eball q (ENNReal.ofReal ε))
    (hNx : IsNormalDomain I M x (Metric.ball 0 r))
    (hy_img : y ∈ riemannianExp I M x '' Metric.ball 0 r) :
    MapsTo (maximalGeodesic I M x (riemannianLog I M x (Metric.ball 0 r) y)) (Icc 0 1)
      (Metric.eball p (ENNReal.ofReal (4 * δ))) := by
  set v : TangentSpace I x := riemannianLog I M x (Metric.ball 0 r) y
  have hv : v ∈ Metric.ball (0 : TangentSpace I x) r := riemannianLog_mem hy_img
  have hv_lt : ‖v‖ < 2 * ε := by
    have h1 : ‖v‖ₑ = edist x y :=
      (hNx.edist_eq_enorm_riemannianLog_of_mem_ball subset_rfl hy_img).symm
    have h2 : edist x y < ENNReal.ofReal (2 * ε) := by
      rw [Metric.mem_eball'] at hx hy
      calc edist x y ≤ edist x q + edist q y := edist_triangle x q y
        _ = edist q x + edist q y := by rw [edist_comm]
        _ < ENNReal.ofReal ε + ENNReal.ofReal ε := ENNReal.add_lt_add hx hy
        _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε.le hε.le, two_mul]
    rw [← h1, ← ofReal_norm] at h2
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h2
  intro t ht
  rw [Metric.mem_eball'] at hq hx ⊢
  have htv : t • v ∈ Metric.ball (0 : TangentSpace I x) r := hNx.smul_mem hv ht.1 ht.2
  have hdist_xt : edist x (maximalGeodesic I M x v t) < ENNReal.ofReal (2 * ε) := by
    rw [← riemannianExp_smul, hNx.edist_riemannianExp_eq_of_mem_ball subset_rfl htv,
      ← ofReal_norm, norm_smul, Real.norm_of_nonneg ht.1]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      ((mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt hv_lt)
  calc edist p (maximalGeodesic I M x v t)
      ≤ edist p q + (edist q x + edist x (maximalGeodesic I M x v t)) :=
        (edist_triangle _ _ _).trans (add_le_add le_rfl (edist_triangle _ _ _))
    _ < ENNReal.ofReal δ + (ENNReal.ofReal ε + ENNReal.ofReal (2 * ε)) :=
        ENNReal.add_lt_add hq (ENNReal.add_lt_add hx hdist_xt)
    _ = ENNReal.ofReal (δ + (ε + 2 * ε)) := by
        rw [← ENNReal.ofReal_add hε.le (by positivity),
          ← ENNReal.ofReal_add hδ.le (by positivity)]
    _ ≤ ENNReal.ofReal (4 * δ) := ENNReal.ofReal_le_ofReal (by linarith)

/-- Any radial geodesic joining two points of `Metric.eball q (ENNReal.ofReal ε)` stays in that
ball whenever the squared radial distance from `q` is strictly convex along geodesics in a
surrounding normal neighbourhood `V`. -/
private theorem mapsTo_riemannianExp_smul_eball_of_strictConvexOn
    {p q x y : M} {r δ ε : ℝ} {V : Set M}
    (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (h4δV : Metric.eball p (ENNReal.ofReal (4 * δ)) ⊆ V)
    (hVN : ∀ z ∈ V, IsNormalDomain I M z (Metric.ball 0 r) ∧
      V ⊆ riemannianExp I M z '' Metric.ball 0 r)
    (hstrict : ∀ z ∈ V, ∀ a : M, ∀ v : TangentSpace I a, v ≠ 0 →
      Icc (0 : ℝ) 1 ⊆ geodesicInterval I M a v →
        MapsTo (maximalGeodesic I M a v) (Icc 0 1) V →
        StrictConvexOn ℝ (Icc 0 1) (fun t : ℝ ↦
          ‖riemannianLog I M z (Metric.ball 0 r) (maximalGeodesic I M a v t)‖ ^ 2))
    (hq : q ∈ Metric.eball p (ENNReal.ofReal δ))
    (hx : x ∈ Metric.eball q (ENNReal.ofReal ε))
    (hy : y ∈ Metric.eball q (ENNReal.ofReal ε))
    (hNx : IsNormalDomain I M x (Metric.ball 0 r))
    (hy_img : y ∈ riemannianExp I M x '' Metric.ball 0 r) :
    MapsTo (fun t : ℝ ↦ riemannianExp I M x (t • riemannianLog I M x (Metric.ball 0 r) y))
      (Icc 0 1) (Metric.eball q (ENNReal.ofReal ε)) := by
  set v : TangentSpace I x := riemannianLog I M x (Metric.ball 0 r) y
  have hv : v ∈ Metric.ball (0 : TangentSpace I x) r := riemannianLog_mem hy_img
  have hexp_v : riemannianExp I M x v = y := riemannianExp_riemannianLog hy_img
  rcases eq_or_ne x y with rfl | hxy
  · intro t _
    simpa [v, hNx.riemannianLog_self] using hx
  have hv0 : v ≠ 0 := fun h0 ↦ hxy (by rw [← hexp_v, h0, riemannianExp_zero])
  have hγV : MapsTo (maximalGeodesic I M x v) (Icc 0 1) V :=
    (mapsTo_maximalGeodesic_of_mem_eball hδ hε hεδ hq hx hy hNx hy_img).mono_right h4δV
  have hqV : q ∈ V :=
    h4δV (Metric.eball_subset_eball (ENNReal.ofReal_le_ofReal (by linarith)) hq)
  have hNq : IsNormalDomain I M q (Metric.ball 0 r) := (hVN q hqV).1
  have hconv :=
    (hstrict q hqV x v hv0 (fun t ht ↦ hNx.mem_geodesicInterval hv ht.1 ht.2) hγV).convexOn
  have hnorm_lt {z : M} (hzV : z ∈ V) (hz : z ∈ Metric.eball q (ENNReal.ofReal ε)) :
      ‖riemannianLog I M q (Metric.ball 0 r) z‖ ^ 2 < ε ^ 2 := by
    have he := hNq.edist_eq_enorm_riemannianLog_of_mem_ball subset_rfl ((hVN q hqV).2 hzV)
    rw [Metric.mem_eball', he, ← ofReal_norm] at hz
    have hlt : ‖riemannianLog I M q (Metric.ball 0 r) z‖ < ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).1 hz
    exact sq_lt_sq' (by linarith [norm_nonneg (riemannianLog I M q (Metric.ball 0 r) z)]) hlt
  intro t ht
  have h01 := hconv.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at h01
  have h0 :
      ‖riemannianLog I M q (Metric.ball 0 r) (maximalGeodesic I M x v 0)‖ ^ 2 < ε ^ 2 := by
    simpa only [maximalGeodesic_zero] using
      hnorm_lt (by simpa using hγV (left_mem_Icc.2 zero_le_one)) hx
  have h1 :
      ‖riemannianLog I M q (Metric.ball 0 r) (maximalGeodesic I M x v 1)‖ ^ 2 < ε ^ 2 := by
    simpa only [← riemannianExp_smul, one_smul, hexp_v] using
      hnorm_lt (by simpa [← riemannianExp_smul, hexp_v] using hγV (right_mem_Icc.2 zero_le_one)) hy
  have hsq_lt :
      ‖riemannianLog I M q (Metric.ball 0 r) (maximalGeodesic I M x v t)‖ ^ 2 < ε ^ 2 :=
    h01.trans_lt <| by
      rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · simpa using h0
      · have hm1 := mul_lt_mul_of_pos_left h1 ht0
        have hm0 := mul_le_mul_of_nonneg_left h0.le (sub_nonneg.2 ht.2)
        linarith
  have hlt_norm :
      ‖riemannianLog I M q (Metric.ball 0 r) (riemannianExp I M x (t • v))‖ < ε := by
    rw [riemannianExp_smul]
    nlinarith [norm_nonneg (riemannianLog I M q (Metric.ball 0 r) (maximalGeodesic I M x v t))]
  rw [Metric.mem_eball', hNq.edist_eq_enorm_riemannianLog_of_mem_ball subset_rfl
    ((hVN q hqV).2 (by simpa only [riemannianExp_smul] using hγV ht)), ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hlt_norm

/-- **Existence of strongly geodesically convex balls** (Lee, Theorem 6.17). Every point `p` has
positive radii `r, δ > 0` such that:
1. for every `q ∈ Metric.eball p (ENNReal.ofReal δ)`, `Metric.ball 0 r` is a normal domain at `q`;
2. for every `q ∈ Metric.eball p (ENNReal.ofReal δ)` and every `0 < ε ≤ δ`, the Riemannian open
   ball `Metric.eball q (ENNReal.ofReal ε)` is both uniformly normal and strongly geodesically
   convex. -/
theorem exists_pos_forall_isNormalDomain_and_isStronglyGeodesicallyConvex_eball (p : M) :
    ∃ r > 0, ∃ δ > 0,
      (∀ q ∈ Metric.eball p (ENNReal.ofReal δ), IsNormalDomain I M q (Metric.ball 0 r)) ∧
      (∀ q ∈ Metric.eball p (ENNReal.ofReal δ), ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsUniformlyNormal I M (Metric.eball q (ENNReal.ofReal ε)) ∧
        IsStronglyGeodesicallyConvex I M (Metric.eball q (ENNReal.ofReal ε))) := by
  obtain ⟨r, hr, V, hVo, hpV, hVN, hstrict⟩ :=
    exists_isOpen_strictConvexOn_norm_sq_riemannianLog (I := I) (M := M) p
  obtain ⟨R, hR, hRsub⟩ := EMetric.isOpen_iff.1 hVo p hpV
  obtain ⟨δ₀, hδ₀, hδ₀R⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ENNReal.ofReal (4 * δ₀) ≤ R := by
    rcases eq_or_ne R ∞ with rfl | hRtop
    · exact ⟨1, one_pos, le_top⟩
    · refine ⟨R.toReal / 4, div_pos (ENNReal.toReal_pos hR.ne' hRtop) (by norm_num), ?_⟩
      rw [mul_div_cancel₀ _ (by norm_num), ENNReal.ofReal_toReal hRtop]
  set δ : ℝ := min δ₀ (r / 4)
  have hδ : 0 < δ := lt_min hδ₀ (div_pos hr (by norm_num))
  have h4δr : 4 * δ ≤ r := by linarith [min_le_right δ₀ (r / 4)]
  have h4δV : Metric.eball p (ENNReal.ofReal (4 * δ)) ⊆ V :=
    (Metric.eball_subset_eball
      ((ENNReal.ofReal_le_ofReal (by linarith [min_le_left δ₀ (r / 4)])).trans hδ₀R)).trans
      hRsub
  refine ⟨r, hr, δ, hδ,
    fun q hq ↦ (hVN q (h4δV (Metric.eball_subset_eball
      (ENNReal.ofReal_le_ofReal (by linarith)) hq))).1,
    fun q hq ε hε hεδ ↦ ?_⟩
  set B : Set M := Metric.eball q (ENNReal.ofReal ε)
  have hBV : B ⊆ V := fun x hx ↦ h4δV <| by
    rw [Metric.mem_eball'] at hq hx ⊢
    calc edist p x ≤ edist p q + edist q x := edist_triangle p q x
      _ < ENNReal.ofReal δ + ENNReal.ofReal ε := ENNReal.add_lt_add hq hx
      _ = ENNReal.ofReal (δ + ε) := (ENNReal.ofReal_add hδ.le hε.le).symm
      _ ≤ ENNReal.ofReal (4 * δ) := ENNReal.ofReal_le_ofReal (by linarith)
  have hB_img : ∀ x ∈ B, B ⊆ riemannianExp I M x '' Metric.ball 0 r := by
    intro x hx y hy
    rw [(hVN x (hBV hx)).1.image_riemannianExp_ball subset_rfl, Metric.mem_eball']
    rw [Metric.mem_eball'] at hx hy
    calc edist x y ≤ edist x q + edist q y := edist_triangle x q y
      _ = edist q x + edist q y := by rw [edist_comm]
      _ < ENNReal.ofReal ε + ENNReal.ofReal ε := ENNReal.add_lt_add hx hy
      _ = ENNReal.ofReal (ε + ε) := (ENNReal.ofReal_add hε.le hε.le).symm
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨⟨Metric.isOpen_eball, fun x hx ↦ ⟨r, hr, (hVN x (hBV hx)).1, hB_img x hx⟩⟩,
    fun x hx y hy ↦ ?_⟩
  have hNx : IsNormalDomain I M x (Metric.ball 0 r) := (hVN x (hBV hx)).1
  have hy_img : y ∈ riemannianExp I M x '' Metric.ball 0 r := hB_img x hx hy
  set v : TangentSpace I x := riemannianLog I M x (Metric.ball 0 r) y
  have hv : v ∈ Metric.ball (0 : TangentSpace I x) r := riemannianLog_mem hy_img
  have hexp_v : riemannianExp I M x v = y := riemannianExp_riemannianLog hy_img
  refine ⟨fun t ↦ riemannianExp I M x (t • v), hNx.isGeodesicCurveOn_riemannianExp_smul hv,
    by simp, by simp [hexp_v],
    (by simpa only [hexp_v] using
      hNx.pathELength_riemannianExp_smul_eq_edist_of_mem_ball subset_rfl hv),
    mapsTo_riemannianExp_smul_eball_of_strictConvexOn hδ hε hεδ h4δV hVN
      (fun z hz a u hu hJ hmaps ↦ hstrict z hz a u hu 0 1 hJ hmaps) hq hx hy hNx hy_img,
    fun γ' hγ' hγ'0 hγ'1 hlen' ↦
      hNx.eqOn_riemannianExp_smul_of_isGeodesicCurveOn_Icc_pathELength_eq hv hγ' hγ'0
        (hγ'1.trans hexp_v.symm) (hlen'.trans (congrArg (edist x) hexp_v.symm))⟩

/-- **Uniform normal and strong-convexity radii near a compact set.** For any compact subset `K` of
a Riemannian manifold, there exist radii `r, δ > 0` and an open superset `U ⊇ K` such that:
1. the tangent ball `Metric.ball 0 r` is a normal domain at every `q ∈ U`;
2. every Riemannian ball `Metric.eball q (ENNReal.ofReal ε)` with `q ∈ U` and `0 < ε ≤ δ` is
   uniformly normal and strongly geodesically convex. -/
theorem _root_.IsCompact.exists_pos_forall_isNormalDomain_and_isStronglyGeodesicallyConvex_eball
    {K : Set M} (hK : IsCompact K) :
    ∃ r > 0, ∃ δ > 0, ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧
      (∀ q ∈ U, IsNormalDomain I M q (Metric.ball 0 r)) ∧
      (∀ q ∈ U, ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsUniformlyNormal I M (Metric.eball q (ENNReal.ofReal ε)) ∧
        IsStronglyGeodesicallyConvex I M (Metric.eball q (ENNReal.ofReal ε))) := by
  choose! R hR D hD hRN hDconv using
    TauCeti.Manifold.exists_pos_forall_isNormalDomain_and_isStronglyGeodesicallyConvex_eball
      (I := I) (M := M)
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover
    (fun p ↦ Metric.eball p (ENNReal.ofReal (D p)))
    fun p _ ↦ Metric.eball_mem_nhds p (ENNReal.ofReal_pos.2 (hD p))
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨1, one_pos, 1, one_pos, ∅, isOpen_empty, by simpa using hKt,
      fun _ h ↦ h.elim, fun _ h ↦ h.elim⟩
  have hRt : 0 < t.inf' ht R := (Finset.lt_inf'_iff ht).2 fun p _ ↦ hR p
  have hDt : 0 < t.inf' ht D := (Finset.lt_inf'_iff ht).2 fun p _ ↦ hD p
  refine ⟨t.inf' ht R, hRt, t.inf' ht D, hDt,
    ⋃ p ∈ t, Metric.eball p (ENNReal.ofReal (D p)),
    isOpen_biUnion fun _ _ ↦ Metric.isOpen_eball, hKt,
    fun q hq ↦ ?_, fun q hq ε hε hεδ ↦ ?_⟩
  · obtain ⟨p, hpt, hqp⟩ := mem_iUnion₂.1 hq
    exact (hRN p q hqp).ball (Metric.ball_subset_ball (Finset.inf'_le R hpt)) hRt
  · obtain ⟨p, hpt, hqp⟩ := mem_iUnion₂.1 hq
    exact hDconv p q hqp ε hε (hεδ.trans (Finset.inf'_le D hpt))

end StrongConvexity

end TauCeti.Manifold

end
