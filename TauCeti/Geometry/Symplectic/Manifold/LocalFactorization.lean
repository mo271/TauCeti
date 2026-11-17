/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Geometry.Symplectic.JHolomorphic.LocalFactorization
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Geometry.Symplectic.Manifold.UniqueContinuation

/-!
# Local factorization of pseudoholomorphic curves on manifolds

This file lifts the planar local factorization lemma of
`TauCeti.Geometry.Symplectic.JHolomorphic.LocalFactorization` (McDuff–Salamon, Lemma 2.4.3)
from open subsets of `ℂ` to Riemann surfaces and almost complex manifolds.

Let `S₀`, `S₁` be Riemann surfaces (`[ChartedSpace ℂ Sᵢ] [IsManifold 𝓘(ℂ) ∞ Sᵢ]`), let `X` be a
smooth boundaryless manifold modelled on a finite-dimensional real normed space `E`, and let
`J : ContMDiffAlmostComplexStructure I n X` with `2 ≤ n`. Suppose:

* `u₀ : S₀ → X` is a `C²` pseudoholomorphic curve with `mfderiv 𝓘(ℝ, ℂ) I u₀ z₀ ≠ 0`,
* `u₁ : S₁ → X` is a `C¹` pseudoholomorphic curve (possibly critical at `ζ₀`) with
  `u₀ z₀ = u₁ ζ₀`, and
* `(z₀, ζ₀)` lies in the closure of `{(z, ζ) | ζ ≠ ζ₀ ∧ u₀ z = u₁ ζ}`.

Then on an open neighbourhood `U ⊆ S₁` of `ζ₀` there exists a holomorphic map `φ : S₁ → S₀`
(`ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ φ U`) with `φ ζ₀ = z₀` and `u₁ ζ = u₀ (φ ζ)` for all `ζ ∈ U`.
No separation, compactness, or connectedness hypotheses are required on `X`, `S₀`, or `S₁`.

## Main results

* `TauCeti.Pseudoholomorphic.exists_holomorphic_factorization_of_mem_closure`: closure form for
  a `C^n` almost complex structure (`2 ≤ n`).
* `TauCeti.Pseudoholomorphic.exists_holomorphic_factorization_of_tendsto`: sequential form via
  converging sequences `z ν → z₀` and `ζ ν → ζ₀`.
* `TauCeti.IsPseudoholomorphic.exists_holomorphic_factorization_of_mem_closure` and
  `TauCeti.IsPseudoholomorphic.exists_holomorphic_factorization_of_tendsto`: dot-notation wrappers
  for `SmoothAlmostComplexStructure`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4, Lemma 2.4.3.
* C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*, Section 2.5.
-/

public noncomputable section

open Filter Function Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.Pseudoholomorphic

variable {E H X S₀ S₁ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ∞ S₀]
  [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ∞ S₁]
  {n : ℕ∞} {J : ContMDiffAlmostComplexStructure I n X}

/-- **Local factorization of pseudoholomorphic curves** (McDuff–Salamon, Lemma 2.4.3, closure form).
Let `J` be a `C^n` almost complex structure (`2 ≤ n`) on a boundaryless manifold `X`, let
`u₀ : S₀ → X` be a `C²` pseudoholomorphic curve immersed at `z₀` (`mfderiv 𝓘(ℝ, ℂ) I u₀ z₀ ≠ 0`),
and let `u₁ : S₁ → X` be a `C¹` pseudoholomorphic curve (possibly critical at `ζ₀`) with
`u₀ z₀ = u₁ ζ₀`. If `(z₀, ζ₀)` lies in the closure of `{p : S₀ × S₁ | p.2 ≠ ζ₀ ∧ u₀ p.1 = u₁ p.2}`,
then there exist an open neighbourhood `U` of `ζ₀` and a holomorphic map `φ : S₁ → S₀`
(`ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ φ U`) such that `φ ζ₀ = z₀` and `u₁ ζ = u₀ (φ ζ)` for all `ζ ∈ U`. -/
theorem exists_holomorphic_factorization_of_mem_closure (hn : 2 ≤ n)
    {u₀ : S₀ → X} (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hCR₀ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₀ z (Complex.I : ℂ) = J (u₀ z) (mfderiv 𝓘(ℝ, ℂ) I u₀ z (1 : ℂ)))
    {u₁ : S₁ → X} (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hCR₁ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₁ z (Complex.I : ℂ) = J (u₁ z) (mfderiv 𝓘(ℝ, ℂ) I u₁ z (1 : ℂ)))
    {z₀ : S₀} {ζ₀ : S₁} (hnd : mfderiv 𝓘(ℝ, ℂ) I u₀ z₀ ≠ 0) (heq₀ : u₀ z₀ = u₁ ζ₀)
    (hacc : (z₀, ζ₀) ∈ closure {p : S₀ × S₁ | p.2 ≠ ζ₀ ∧ u₀ p.1 = u₁ p.2}) :
    ∃ U : Set S₁, IsOpen U ∧ ζ₀ ∈ U ∧
      ∃ φ : S₁ → S₀, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ φ U ∧ φ ζ₀ = z₀ ∧
        ∀ ζ ∈ U, u₁ ζ = u₀ (φ ζ) := by
  let x : X := u₀ z₀
  let c₀ := chartAt ℂ z₀
  let c₁ := chartAt ℂ ζ₀
  let ψ := extChartAt I x
  let Ω₀ : Set ℂ := c₀.target ∩ c₀.symm ⁻¹' (u₀ ⁻¹' ψ.source)
  let Ω₁ : Set ℂ := c₁.target ∩ c₁.symm ⁻¹' (u₁ ⁻¹' ψ.source)
  let v₀ : ℂ → E := ψ ∘ u₀ ∘ c₀.symm
  let v₁ : ℂ → E := ψ ∘ u₁ ∘ c₁.symm
  have hΩ₀_open : IsOpen Ω₀ :=
    c₀.continuousOn_invFun.isOpen_inter_preimage c₀.open_target
      ((isOpen_extChartAt_source x).preimage hu₀.continuous)
  have hΩ₁_open : IsOpen Ω₁ :=
    c₁.continuousOn_invFun.isOpen_inter_preimage c₁.open_target
      ((isOpen_extChartAt_source x).preimage hu₁.continuous)
  have hw₀ : c₀ z₀ ∈ Ω₀ := by
    refine ⟨mem_chart_target ℂ z₀, ?_⟩
    simp only [mem_preimage, c₀.left_inv (mem_chart_source ℂ z₀)]
    exact mem_extChartAt_source x
  have hw₁ : c₁ ζ₀ ∈ Ω₁ := by
    refine ⟨mem_chart_target ℂ ζ₀, ?_⟩
    simp only [mem_preimage, c₁.left_inv (mem_chart_source ℂ ζ₀), ← heq₀]
    exact mem_extChartAt_source x
  have hJ_cd : ContDiffOn ℝ 2 (J.inChart x) ψ.target :=
    (J.contDiffOn_inChart x).of_le (WithTop.coe_le_coe.2 hn)
  have hJJ : ∀ y ∈ ψ.target, J.inChart x y ∘L J.inChart x y = -ContinuousLinearMap.id ℝ E :=
    fun y hy ↦ ContinuousLinearMap.ext fun w ↦ by
      simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply]
      exact J.inChart_inChart x hy w
  have hv₀_cd : ContDiffOn ℝ 2 v₀ Ω₀ := by
    refine contMDiffOn_iff_contDiffOn.1 ?_
    have h1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 2 c₀.symm Ω₀ :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := z₀)).of_le (by simp) |>.mono
        inter_subset_left
    have h2 : ContMDiffOn 𝓘(ℝ, ℂ) I 2 (u₀ ∘ c₀.symm) Ω₀ := hu₀.comp_contMDiffOn h1
    exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).of_le (by simp) |>.comp h2
      fun w hw ↦ by
        have h : u₀ (c₀.symm w) ∈ ψ.source := hw.2
        rwa [extChartAt_source] at h
  have hv₁_cd : ContDiffOn ℝ 1 v₁ Ω₁ := by
    refine contMDiffOn_iff_contDiffOn.1 ?_
    have h1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 c₁.symm Ω₁ :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := ζ₀)).of_le (by simp) |>.mono
        inter_subset_left
    have h2 : ContMDiffOn 𝓘(ℝ, ℂ) I 1 (u₁ ∘ c₁.symm) Ω₁ := hu₁.comp_contMDiffOn h1
    exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).of_le (by simp) |>.comp h2
      fun w hw ↦ by
        have h : u₁ (c₁.symm w) ∈ ψ.source := hw.2
        rwa [extChartAt_source] at h
  have hm₀ : MapsTo v₀ Ω₀ ψ.target := fun w hw ↦ ψ.map_source hw.2
  have hCR₀' : ∀ w ∈ Ω₀, fderiv ℝ v₀ w 1 + J.inChart x (v₀ w) (fderiv ℝ v₀ w Complex.I) = 0 :=
    fun w hw ↦ fderiv_extChartAt_comp_chartAt_symm_add_inChart_eq_zero J
      (hu₀.mdifferentiable two_ne_zero) hCR₀ z₀ x hw.1 hw.2
  have hCR₁' : ∀ w ∈ Ω₁, fderiv ℝ v₁ w 1 + J.inChart x (v₁ w) (fderiv ℝ v₁ w Complex.I) = 0 :=
    fun w hw ↦ fderiv_extChartAt_comp_chartAt_symm_add_inChart_eq_zero J
      (hu₁.mdifferentiable one_ne_zero) hCR₁ ζ₀ x hw.1 hw.2
  have hnd' : fderiv ℝ v₀ (c₀ z₀) ≠ 0 := by
    intro h0
    have hiff := fderiv_extChartAt_comp_chartAt_symm_eq_zero_iff_mfderiv_eq_zero
      (hu₀.mdifferentiable two_ne_zero) z₀ x hw₀.1 hw₀.2
    have hmz : mfderiv 𝓘(ℝ, ℂ) I u₀ (c₀.symm (c₀ z₀)) = 0 := hiff.1 h0
    rw [c₀.left_inv (mem_chart_source ℂ z₀)] at hmz
    exact hnd hmz
  have hveq : v₀ (c₀ z₀) = v₁ (c₁ ζ₀) := by
    simp only [v₀, v₁, Function.comp_apply, c₀.left_inv (mem_chart_source ℂ z₀),
      c₁.left_inv (mem_chart_source ℂ ζ₀), heq₀]
  have hacc' : (c₀ z₀, c₁ ζ₀) ∈ closure {p : ℂ × ℂ | p.2 ≠ c₁ ζ₀ ∧ v₀ p.1 = v₁ p.2} := by
    rw [mem_closure_iff_nhds]
    intro N hN
    let F : S₀ × S₁ → ℂ × ℂ := fun p ↦ (c₀ p.1, c₁ p.2)
    have hF_cont : ContinuousAt F (z₀, ζ₀) :=
      ((c₀.continuousAt (mem_chart_source ℂ z₀)).comp continuousAt_fst).prodMk
        ((c₁.continuousAt (mem_chart_source ℂ ζ₀)).comp continuousAt_snd)
    have hsrc : c₀.source ×ˢ c₁.source ∈ 𝓝 (z₀, ζ₀) :=
      prod_mem_nhds (c₀.open_source.mem_nhds (mem_chart_source ℂ z₀))
        (c₁.open_source.mem_nhds (mem_chart_source ℂ ζ₀))
    have hpre : F ⁻¹' N ∩ (c₀.source ×ˢ c₁.source) ∈ 𝓝 (z₀, ζ₀) :=
      Filter.inter_mem (hF_cont.preimage_mem_nhds hN) hsrc
    obtain ⟨⟨z, ζ⟩, ⟨hFN, hz_src, hζ_src⟩, hζ_ne, hu_eq⟩ :=
      mem_closure_iff_nhds.1 hacc _ hpre
    refine ⟨(c₀ z, c₁ ζ), hFN, ?_, ?_⟩
    · intro hceq
      exact hζ_ne (c₁.injOn hζ_src (mem_chart_source ℂ ζ₀) hceq)
    · simp only [v₀, v₁, Function.comp_apply, c₀.left_inv hz_src, c₁.left_inv hζ_src, hu_eq]
  obtain ⟨V, hV_open, hw₁V, hV_sub, g, hg_diff, hg_eq, hg_maps, hg_fac⟩ :=
    JHolomorphic.exists_holomorphic_factorization_of_mem_closure (isOpen_extChartAt_target x)
      hJ_cd hJJ hΩ₀_open hv₀_cd hm₀ hCR₀' hΩ₁_open hv₁_cd hCR₁' hw₀ hw₁ hnd' hveq hacc'
  let U : Set S₁ := c₁.source ∩ c₁ ⁻¹' V
  let φ : S₁ → S₀ := c₀.symm ∘ g ∘ c₁
  have hU_open : IsOpen U := c₁.continuousOn_toFun.isOpen_inter_preimage c₁.open_source hV_open
  have hζ₀U : ζ₀ ∈ U := ⟨mem_chart_source ℂ ζ₀, hw₁V⟩
  have hφ_md : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ φ U := by
    have hg_cd : ContDiffOn ℂ ∞ g V := hg_diff.contDiffOn hV_open
    have hg_md : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g V := contMDiffOn_iff_contDiffOn.2 hg_cd
    have hc₁_md : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c₁ U :=
      (contMDiffOn_chart (I := 𝓘(ℂ)) (n := ∞) (x := ζ₀)).mono inter_subset_left
    have hgc₁ : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (g ∘ c₁) U :=
      hg_md.comp hc₁_md fun _ h ↦ h.2
    exact (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ∞) (x := z₀)).comp hgc₁
      fun ζ hζ ↦ (hg_maps hζ.2).1
  refine ⟨U, hU_open, hζ₀U, φ, hφ_md, ?_, ?_⟩
  · simp only [φ, Function.comp_apply, hg_eq, c₀.left_inv (mem_chart_source ℂ z₀)]
  · intro ζ hζ
    have hw_V : c₁ ζ ∈ V := hζ.2
    have hw_Ω₁ : c₁ ζ ∈ Ω₁ := hV_sub hw_V
    have hgw_Ω₀ : g (c₁ ζ) ∈ Ω₀ := hg_maps hw_V
    have hu₁_src : u₁ ζ ∈ ψ.source := by
      have h : u₁ (c₁.symm (c₁ ζ)) ∈ ψ.source := hw_Ω₁.2
      rwa [c₁.left_inv hζ.1] at h
    have hu₀_src : u₀ (φ ζ) ∈ ψ.source := hgw_Ω₀.2
    have hψ_eq : ψ (u₁ ζ) = ψ (u₀ (φ ζ)) := by
      calc ψ (u₁ ζ) = v₁ (c₁ ζ) := by
            simp only [v₁, Function.comp_apply, c₁.left_inv hζ.1]
        _ = v₀ (g (c₁ ζ)) := hg_fac (c₁ ζ) hw_V
        _ = ψ (u₀ (φ ζ)) := rfl
    exact ψ.injOn hu₁_src hu₀_src hψ_eq

/-- **Local factorization of pseudoholomorphic curves** (McDuff–Salamon, Lemma 2.4.3, sequential
form). If `z ν → z₀` and `ζ ν → ζ₀` with `ζ ν ≠ ζ₀` and `u₀ (z ν) = u₁ (ζ ν)` for all `ν`, then
`u₁` factors locally through `u₀` via a holomorphic map `φ` near `ζ₀`. -/
theorem exists_holomorphic_factorization_of_tendsto (hn : 2 ≤ n)
    {u₀ : S₀ → X} (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hCR₀ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₀ z (Complex.I : ℂ) = J (u₀ z) (mfderiv 𝓘(ℝ, ℂ) I u₀ z (1 : ℂ)))
    {u₁ : S₁ → X} (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hCR₁ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u₁ z (Complex.I : ℂ) = J (u₁ z) (mfderiv 𝓘(ℝ, ℂ) I u₁ z (1 : ℂ)))
    {z₀ : S₀} {ζ₀ : S₁} (hnd : mfderiv 𝓘(ℝ, ℂ) I u₀ z₀ ≠ 0) (heq₀ : u₀ z₀ = u₁ ζ₀)
    {z : ℕ → S₀} {ζ : ℕ → S₁} (hz : Tendsto z atTop (𝓝 z₀)) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hne : ∀ ν, ζ ν ≠ ζ₀) (hmatch : ∀ ν, u₀ (z ν) = u₁ (ζ ν)) :
    ∃ U : Set S₁, IsOpen U ∧ ζ₀ ∈ U ∧
      ∃ φ : S₁ → S₀, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ φ U ∧ φ ζ₀ = z₀ ∧
        ∀ ζ ∈ U, u₁ ζ = u₀ (φ ζ) :=
  exists_holomorphic_factorization_of_mem_closure hn hu₀ hCR₀ hu₁ hCR₁ hnd heq₀
    (mem_closure_of_tendsto (hz.prodMk_nhds hζ)
      (Filter.Eventually.of_forall fun ν ↦ ⟨hne ν, hmatch ν⟩))

end TauCeti.Pseudoholomorphic

/-! ### Dot-notation wrappers for `IsPseudoholomorphic` -/

namespace TauCeti

section SmoothWrappers

variable {E H X S₀ S₁ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ∞ S₀]
  [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ∞ S₁]
  {J : SmoothAlmostComplexStructure I X}

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem isPseudoholomorphic_mfderiv_apply_I {S : Type*} [TopologicalSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S] {u : S → X}
    (hu : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S) J u) (z : S) :
    mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) =
      (J.toContMDiff ⊤) (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)) := by
  have h := (isPseudoholomorphic_iff.1 hu z).mfderiv_apply_commute (1 : ℂ)
  rw [SmoothAlmostComplexStructure.ofComplexManifold_apply (E := ℂ) z (1 : ℂ),
    smul_eq_mul, mul_one] at h
  exact h.trans (SmoothAlmostComplexStructure.toContMDiff_apply J ⊤ (u z) _).symm

/-- **Local factorization of pseudoholomorphic curves** (closure form) on a smooth almost complex
manifold. -/
theorem IsPseudoholomorphic.exists_holomorphic_factorization_of_mem_closure
    {u₀ : S₀ → X} {u₁ : S₁ → X}
    (hu₀ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S₀) J u₀)
    (hu₁ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S₁) J u₁)
    (hc₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀) (hc₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    {z₀ : S₀} {ζ₀ : S₁} (hnd : mfderiv 𝓘(ℝ, ℂ) I u₀ z₀ ≠ 0) (heq₀ : u₀ z₀ = u₁ ζ₀)
    (hacc : (z₀, ζ₀) ∈ closure {p : S₀ × S₁ | p.2 ≠ ζ₀ ∧ u₀ p.1 = u₁ p.2}) :
    ∃ U : Set S₁, IsOpen U ∧ ζ₀ ∈ U ∧
      ∃ φ : S₁ → S₀, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ φ U ∧ φ ζ₀ = z₀ ∧
        ∀ ζ ∈ U, u₁ ζ = u₀ (φ ζ) :=
  Pseudoholomorphic.exists_holomorphic_factorization_of_mem_closure (J := J.toContMDiff ⊤) le_top
    hc₀ (isPseudoholomorphic_mfderiv_apply_I hu₀) hc₁ (isPseudoholomorphic_mfderiv_apply_I hu₁)
    hnd heq₀ hacc

/-- **Local factorization of pseudoholomorphic curves** (sequential form) on a smooth almost complex
manifold. -/
theorem IsPseudoholomorphic.exists_holomorphic_factorization_of_tendsto
    {u₀ : S₀ → X} {u₁ : S₁ → X}
    (hu₀ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S₀) J u₀)
    (hu₁ : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ S₁) J u₁)
    (hc₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀) (hc₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    {z₀ : S₀} {ζ₀ : S₁} (hnd : mfderiv 𝓘(ℝ, ℂ) I u₀ z₀ ≠ 0) (heq₀ : u₀ z₀ = u₁ ζ₀)
    {z : ℕ → S₀} {ζ : ℕ → S₁} (hz : Tendsto z atTop (𝓝 z₀)) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hne : ∀ ν, ζ ν ≠ ζ₀) (hmatch : ∀ ν, u₀ (z ν) = u₁ (ζ ν)) :
    ∃ U : Set S₁, IsOpen U ∧ ζ₀ ∈ U ∧
      ∃ φ : S₁ → S₀, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ φ U ∧ φ ζ₀ = z₀ ∧
        ∀ ζ ∈ U, u₁ ζ = u₀ (φ ζ) :=
  Pseudoholomorphic.exists_holomorphic_factorization_of_tendsto (J := J.toContMDiff ⊤) le_top
    hc₀ (isPseudoholomorphic_mfderiv_apply_I hu₀) hc₁ (isPseudoholomorphic_mfderiv_apply_I hu₁)
    hnd heq₀ hz hζ hne hmatch

end SmoothWrappers

end TauCeti
