/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import TauCeti.Analysis.Calculus.FDeriv.ImageCone
import TauCeti.Geometry.MeasureTheory.Rectifiable.Subspace
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Tangent cones and countable rectifiability

Almost every point of a bi-Lipschitz image of a subset of a Euclidean space has a
plane of the parameter dimension about which the entire patch lies locally in arbitrarily
narrow cones. This is stronger than the vanishing of the measure outside each such cone.

The plane is the range of the derivative of a Lipschitz extension of the parametrization.
Rademacher's theorem and the zero-Jacobian image theorem remove the points where that range
might not have the required dimension. No local finiteness assumption is needed for this
patchwise assertion. It does not assert tangency of an arbitrary larger rectifiable set:
other patches must still be controlled by measure differentiation. The derivative-range
form is also used to construct measurable tangent projections in `Rectifiable.MeasurableTangent`.

Conversely, `TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_le` proves
Federer's geometric cone criterion: a subset of a finite-dimensional real inner product space
that locally lies, around each of its points, inside a cone of aperture strictly less than `1`
about some `k`-dimensional subspace is countably `k`-rectifiable. Stratifying by the cone
margin and radius and covering both the space and the set of orthogonal projections by
countably many small balls reduces to pieces on which the orthogonal projection onto a fixed
`k`-plane is anti-Lipschitz, hence has Lipschitz inverse.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11, Lemma 11.5 (cone criterion and tangents
  to rectifiable sets).
* H. Federer, *Geometric Measure Theory*, §3.2.29 (rectifiability from cone containment and
  decomposition of parametrizations).
-/

public section

open Set MeasureTheory Metric
open scoped NNReal ENNReal

/-- At Hausdorff-almost every point of a bi-Lipschitz patch, the derivative range of a
Lipschitz parametrization has the parameter dimension and contains the patch locally in
every cone. The parameter domain need not be measurable. -/
theorem LipschitzWith.ae_exists_fderiv_range_forall_infDist_le
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {K L : ℝ≥0} (hf : LipschitzWith K f)
    (hi : AntilipschitzWith L (s.domRestrict f)) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V), y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ Module.finrank ℝ (fderiv ℝ f x).range = Module.finrank ℝ U ∧
        ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ f '' s, dist z y < r →
          infDist (z - y) ((fderiv ℝ f x).range : Set V) ≤ ε * dist z y := by
  have hgood : ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V),
      y ∉ f '' {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}ᶜ :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using
      hf.euclideanHausdorffMeasure_image_compl_setOf_regular)
  filter_upwards [hgood] with y hreg hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxreg : DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0 := by
    by_contra h
    exact hreg ⟨x, h, rfl⟩
  refine ⟨x, hx, rfl, ?_, ?_⟩
  · exact LinearMap.finrank_range_of_inj
      (((fderiv ℝ f x).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hxreg.2)
  · intro ε hε
    exact hxreg.1.hasFDerivAt.hasFDerivWithinAt.exists_pos_forall_infDist_range_le hx hi hε

/-- At Hausdorff-almost every point of a bi-Lipschitz patch, the patch is locally
contained in every cone about some plane of the parameter dimension. Hausdorff measure
has the normalized Euclidean convention. -/
theorem LipschitzOnWith.ae_exists_submodule_forall_infDist_le
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hi : AntilipschitzWith L (s.domRestrict f)) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V), y ∈ f '' s →
      ∃ P : Submodule ℝ V, Module.finrank ℝ P = Module.finrank ℝ U ∧
        ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ f '' s, dist z y < r →
          infDist (z - y) (P : Set V) ≤ ε * dist z y := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_finite_dimension
  have himage : f '' s = g '' s := image_congr hfg
  have hi' : AntilipschitzWith L (s.domRestrict g) := by
    intro x y
    simpa only [domRestrict_apply, ← hfg x.property, ← hfg y.property] using hi x y
  rw [himage]
  filter_upwards [hg.ae_exists_fderiv_range_forall_infDist_le hi'] with y hy hyimage
  obtain ⟨x, _, _, hdim, hcone⟩ := hy hyimage
  exact ⟨(fderiv ℝ g x).range, hdim, hcone⟩

namespace TauCeti

/-- A set `t` whose secants `y - x` all lie in a cone of aperture `γ < 1` around a fixed
`k`-dimensional subspace `P₀` is countably `k`-rectifiable: orthogonal projection onto `P₀` is
`(1 - γ)⁻¹`-anti-Lipschitz on `t`, so `t` is a Lipschitz image of a subset of `P₀`. -/
private theorem countablyRectifiable_of_forall_infDist_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {t : Set V} {P₀ : Submodule ℝ V}
    (hdim : Module.finrank ℝ P₀ = k) {γ : ℝ} (hγ : γ < 1)
    (hcone : ∀ x ∈ t, ∀ y ∈ t, infDist (y - x) (P₀ : Set V) ≤ γ * dist y x) :
    CountablyRectifiable k t := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | hne
  · exact .empty
  have := hne.to_subtype
  have h1γ : 0 < 1 - γ := sub_pos.mpr hγ
  set c : ℝ≥0 := ⟨(1 - γ)⁻¹, inv_nonneg.mpr h1γ.le⟩
  let f : t → P₀ := t.domRestrict P₀.orthogonalProjectionOnto
  have hf : AntilipschitzWith c f := by
    refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
    have hle : (1 - γ) * dist (y : V) x ≤ dist (f y) (f x) := by
      have htri : dist (y : V) x ≤
          dist ((y : V) - x) (P₀.starProjection ((y : V) - x)) + dist (f y) (f x) := by
        simpa only [dist_eq_norm, Subtype.dist_eq, f, domRestrict_apply, ← map_sub,
          P₀.starProjection_apply, Submodule.norm_coe, sub_add_cancel] using
          norm_add_le ((y : V) - x - P₀.starProjection ((y : V) - x))
            (P₀.starProjection ((y : V) - x))
      rw [P₀.dist_starProjection_eq_infDist] at htri
      linarith [hcone x x.2 y y.2]
    rw [dist_comm, Subtype.dist_eq, show (c : ℝ) = (1 - γ)⁻¹ from rfl, inv_mul_eq_div,
      le_div_iff₀' h1γ, dist_comm (f x)]
    exact hle
  have hinv : RightInvOn (Function.invFun f) f (range f) := fun _ hy ↦ Function.invFun_eq hy
  have hLip : LipschitzOnWith c (Subtype.val ∘ Function.invFun f) (range f) := by
    simpa only [one_mul] using (LipschitzWith.subtype_val t).lipschitzOnWith.comp
      (lipschitzOnWith_iff_restrict.mpr (hf.to_rightInvOn hinv)) (mapsTo_univ _ _)
  have himg : (Subtype.val ∘ Function.invFun f) '' range f = t := by
    rw [← range_comp]
    have hcomp : (Subtype.val ∘ Function.invFun f) ∘ f = Subtype.val :=
      funext fun x ↦ congrArg Subtype.val (Function.leftInverse_invFun hf.injective x)
    rw [hcomp, Subtype.range_coe]
  rw [← hdim, ← himg]
  exact (CountablyRectifiable.of_finiteDimensional (range f)).image hLip

/-- **Geometric cone criterion for countable rectifiability.** If around every point `x` of a
subset `s` of a finite-dimensional real inner product space there is a `k`-dimensional subspace `P`
and a cone of aperture `α < 1` around `P` containing `s` near `x`, then `s` is countably
`k`-rectifiable. Neither measurability nor local finiteness of `μHE[k]` on `s` is needed. -/
theorem CountablyRectifiable.of_forall_exists_submodule_infDist_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {s : Set V}
    (h : ∀ x ∈ s, ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
      ∃ α < (1 : ℝ), ∃ r > (0 : ℝ), ∀ y ∈ s, dist y x < r →
        infDist (y - x) (P : Set V) ≤ α * dist y x) :
    CountablyRectifiable k s := by
  let Q : Set (V →L[ℝ] V) :=
    {A | ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧ A = P.starProjection}
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense V
  obtain ⟨C, hCc, hCd⟩ := TopologicalSpace.exists_countable_dense Q
  have := hDc.to_subtype
  have := hCc.to_subtype
  let δ (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  let T (m : ℕ) (z : D) (A : C) : Set V :=
    {x ∈ s | x ∈ ball (z : V) (δ m / 2) ∧ ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
      ‖P.starProjection - ((A : Q) : V →L[ℝ] V)‖ ≤ δ m / 2 ∧
      ∀ y ∈ s, dist y x < δ m → infDist (y - x) (P : Set V) ≤ (1 - δ m) * dist y x}
  have hcov : s ⊆ ⋃ (m : ℕ) (z : D) (A : C), T m z A := by
    intro x hxs
    obtain ⟨P, hdim, α, hα, r, hr, hcone⟩ := h x hxs
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min (sub_pos.mpr hα) hr)
    have hδpos : 0 < δ m := one_div_pos.mpr (by positivity)
    obtain ⟨z, hzD, hxz⟩ := hDd.exists_dist_lt x (half_pos hδpos)
    obtain ⟨A, hAC, hPA⟩ :=
      hCd.exists_dist_lt ⟨P.starProjection, P, hdim, rfl⟩ (half_pos hδpos)
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨z, hzD⟩, mem_iUnion.mpr ⟨⟨A, hAC⟩,
      hxs, mem_ball.mpr hxz, P, hdim, ?_, fun y hys hyx ↦ ?_⟩⟩⟩
    · simpa only [Subtype.dist_eq, dist_eq_norm', norm_sub_rev] using hPA.le
    · have hm1 : δ m < 1 - α := hm.trans_le (min_le_left _ _)
      have hm2 : δ m < r := hm.trans_le (min_le_right _ _)
      exact (hcone y hys (hyx.trans hm2)).trans
        (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  refine (CountablyRectifiable.iUnion fun m ↦ CountablyRectifiable.iUnion fun z ↦
    CountablyRectifiable.iUnion fun A ↦ ?_).mono hcov
  obtain ⟨P₀, hdim₀, hA₀⟩ := (A : Q).2
  have hδpos : 0 < δ m := one_div_pos.mpr (by positivity)
  refine countablyRectifiable_of_forall_infDist_le hdim₀ (γ := 1 - δ m / 2) (by linarith)
    fun x ⟨_, hxz, P, _, hPA, hPx⟩ y ⟨hys, hyz, _⟩ ↦ ?_
  have hyx : dist y x < δ m :=
    calc dist y x ≤ dist y (z : V) + dist (z : V) x := dist_triangle _ _ _
      _ < δ m / 2 + δ m / 2 := add_lt_add (mem_ball.mp hyz) (mem_ball'.mp hxz)
      _ = δ m := add_halves _
  calc infDist (y - x) (P₀ : Set V)
      = dist (y - x) (P₀.starProjection (y - x)) := (P₀.dist_starProjection_eq_infDist _).symm
    _ ≤ dist (y - x) (P.starProjection (y - x)) +
          dist (P.starProjection (y - x)) (P₀.starProjection (y - x)) := dist_triangle _ _ _
    _ ≤ (1 - δ m) * dist y x + (δ m / 2) * dist y x := by
        rw [P.dist_starProjection_eq_infDist, dist_eq_norm, ← hA₀, ← sub_apply]
        refine add_le_add (hPx y hys hyx) ?_
        simpa only [dist_eq_norm] using
          (ContinuousLinearMap.le_opNorm _ (y - x)).trans
            (mul_le_mul_of_nonneg_right hPA (norm_nonneg _))
    _ = (1 - δ m / 2) * dist y x := by ring

end TauCeti
