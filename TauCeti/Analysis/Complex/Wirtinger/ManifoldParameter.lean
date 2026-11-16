/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Complex.Wirtinger.MixedParameter
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Global mixed-parameter `\bar∂` solver over smooth parameter manifolds

This file globalizes the mixed-parameter one-variable `\bar∂` solver from open subsets of
finite-dimensional normed spaces (`TauCeti.Analysis.Complex.Wirtinger.MixedParameter`) to an
arbitrary Hausdorff second-countable smooth boundaryless finite-dimensional manifold `P` of real
parameters, paired with an arbitrary open domain `Q` in a finite-dimensional complex normed space
`E` and an arbitrary open plane domain `Ω ⊆ ℂ`.

Because the `\bar∂_z` operator and the holomorphy condition in `q ∈ Q` act fiberwise over `p ∈ P`
and commute with multiplication by real-valued smooth functions of `p` alone, local solutions built
on extended chart targets `(extChartAt I c).target ⊆ EP` via
`TauCeti.exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq` glue directly across
`P` using a smooth partition of unity subordinate to the chart sources
(`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`).

## Main results

* `TauCeti.exists_contMDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq`: Banach-valued
  global one-variable `\bar∂` solver on `(P × E) × ℂ` over `P × Q × Ω`, jointly smooth in
  `(p, q, z)` and holomorphic in `q ∈ Q`.
* `TauCeti.exists_mixed_parameter_dbar_solution`: scalar (`ℂ`-valued) specialization written
  directly in terms of `(fderiv ℝ (u ((p, q), ·)) z 1 + I * fderiv ℝ (u ((p, q), ·)) z I) / 2`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I, Theorem 1.4.4, and Chapter II, Theorem 2.3.3.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter I, §3.
-/

public noncomputable section

open Complex Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

/-- Linearity of `conjWirtingerDeriv` over a finite sum of real-differentiable maps. -/
private theorem conjWirtingerDeriv_sum {ι V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (S : Finset ι) {g : ι → V → W} {x : V}
    (hg : ∀ i ∈ S, DifferentiableAt ℝ (g i) x) :
    conjWirtingerDeriv (fun y ↦ ∑ i ∈ S, g i y) x =
      ∑ i ∈ S, conjWirtingerDeriv (g i) x := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S haS ih =>
    have ha : DifferentiableAt ℝ (g a) x := hg a (Finset.mem_insert_self a S)
    have hS : DifferentiableAt ℝ (fun y ↦ ∑ i ∈ S, g i y) x :=
      DifferentiableAt.fun_sum fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
    have hins :
        (fun y ↦ ∑ i ∈ insert a S, g i y) =
          g a + fun y ↦ ∑ i ∈ S, g i y := by
      ext y
      simp [Finset.sum_insert haS]
    rw [hins, Finset.sum_insert haS, conjWirtingerDeriv_add ha hS,
      ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)]

/-- **Global mixed-parameter one-variable `\bar∂` solver over a smooth manifold.** Let `P` be a
Hausdorff second-countable `C^∞` boundaryless manifold modeled on a finite-dimensional real normed
space `EP`, `E` a finite-dimensional complex normed space, `F` a complex Banach space, and `Q ⊆ E`
and `Ω ⊆ ℂ` arbitrary open sets. Every `f : (P × E) × ℂ → F` that is jointly `C^∞` on
`(univ ×ˢ Q) ×ˢ Ω` and holomorphic in `q ∈ Q` for each `(p, z) ∈ P × Ω` admits a global `C^∞` map
`u : (P × E) × ℂ → F` on `(univ ×ˢ Q) ×ˢ Ω`, holomorphic in `q ∈ Q` for each `(p, z) ∈ P × Ω`,
solving `conjWirtingerDeriv (fun w ↦ u ((p, q), w)) z 1 = f ((p, q), z)` everywhere on
`P × Q × Ω`. -/
theorem exists_contMDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq
    {EP HP P E F : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP] (I : ModelWithCorners ℝ EP HP) [I.Boundaryless]
    [TopologicalSpace P] [ChartedSpace HP P] [IsManifold I ∞ P]
    [T2Space P] [SecondCountableTopology P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {Q : Set E} {Ω : Set ℂ} (hQ : IsOpen Q) (hΩ : IsOpen Ω)
    {f : (P × E) × ℂ → F}
    (hf : ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ f ((univ ×ˢ Q) ×ˢ Ω))
    (hfhol : ∀ p z, z ∈ Ω → DifferentiableOn ℂ (fun q ↦ f ((p, q), z)) Q) :
    ∃ u : (P × E) × ℂ → F,
      ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ u ((univ ×ˢ Q) ×ˢ Ω) ∧
      (∀ p z, z ∈ Ω → DifferentiableOn ℂ (fun q ↦ u ((p, q), z)) Q) ∧
      (∀ p q, q ∈ Q → ∀ z, z ∈ Ω →
        conjWirtingerDeriv (fun w ↦ u ((p, q), w)) z 1 = f ((p, q), z)) := by
  have : LocallyCompactSpace HP := I.locallyCompactSpace
  have : LocallyCompactSpace P := ChartedSpace.locallyCompactSpace HP P
  -- Step 1: Solve on each extended chart target `(extChartAt I c).target ⊆ EP` using the
  -- normed-space mixed-parameter solver.
  have hloc : ∀ c : P, ∃ vc : (EP × E) × ℂ → F,
      ContDiffOn ℝ ∞ vc (((extChartAt I c).target ×ˢ Q) ×ˢ Ω) ∧
      (∀ p' ∈ (extChartAt I c).target, ∀ z ∈ Ω,
        DifferentiableOn ℂ (fun q ↦ vc ((p', q), z)) Q) ∧
      (∀ p' ∈ (extChartAt I c).target, ∀ q ∈ Q, ∀ z ∈ Ω,
        conjWirtingerDeriv (fun w ↦ vc ((p', q), w)) z 1 =
          f (((extChartAt I c).symm p', q), z)) := by
    intro c
    let Uc : Set EP := (extChartAt I c).target
    have hUc : IsOpen Uc := isOpen_extChartAt_target c
    let ψc : (EP × E) × ℂ → (P × E) × ℂ :=
      fun w ↦ (((extChartAt I c).symm w.1.1, w.1.2), w.2)
    have hψc :
        ContMDiffOn ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ))
          ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞ ψc ((Uc ×ˢ Q) ×ˢ Ω) := by
      have hp' : ContMDiffOn ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) I ∞
          (fun w : (EP × E) × ℂ ↦ (extChartAt I c).symm w.1.1) ((Uc ×ˢ Q) ×ˢ Ω) :=
        (contMDiffOn_extChartAt_symm c).comp (contMDiff_fst.comp contMDiff_fst).contMDiffOn
          fun _ hw ↦ hw.1.1
      have hq' : ContMDiffOn ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) ∞
          (fun w : (EP × E) × ℂ ↦ w.1.2) ((Uc ×ˢ Q) ×ˢ Ω) :=
        (contMDiff_snd.comp contMDiff_fst).contMDiffOn
      exact (hp'.prodMk hq').prodMk contMDiffOn_snd
    have hfc_mdiff :
        ContMDiffOn ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞
          (f ∘ ψc) ((Uc ×ˢ Q) ×ˢ Ω) :=
      hf.comp hψc fun _ hw ↦ ⟨⟨mem_univ _, hw.1.2⟩, hw.2⟩
    have hfc_cdiff : ContDiffOn ℝ ∞ (f ∘ ψc) ((Uc ×ˢ Q) ×ˢ Ω) := by
      rwa [contMDiffOn_prod_prod_modelWithCornersSelf_iff,
        contMDiffOn_prod_modelWithCornersSelf_iff, contMDiffOn_iff_contDiffOn] at hfc_mdiff
    exact exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq
      hUc hQ hΩ hfc_cdiff (fun p' _ z hz ↦ hfhol ((extChartAt I c).symm p') z hz)
  choose v hv_smooth hv_hol hv_dbar using hloc
  -- Step 2: Glue across `P` with a smooth partition of unity subordinate to chart sources.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I P
  let g : P → (P × E) × ℂ → F := fun c w ↦ v c ((extChartAt I c w.1.1, w.1.2), w.2)
  let u : (P × E) × ℂ → F := fun w ↦ ∑ᶠ c : P, ρ c w.1.1 • g c w
  have hmem_tgt : ∀ {c p : P}, c ∈ ρ.finsupport p →
      p ∈ (extChartAt I c).source ∧ extChartAt I c p ∈ (extChartAt I c).target := by
    intro c p hc
    have hp_chart : p ∈ (chartAt HP c).source :=
      hρ c (subset_tsupport (ρ c) (ρ.mem_finsupport p |>.1 hc))
    have hp_src : p ∈ (extChartAt I c).source := by rwa [extChartAt_source]
    exact ⟨hp_src, (extChartAt I c).map_source hp_src⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · -- Joint manifold smoothness of `u` on `(univ ×ˢ Q) ×ˢ Ω`.
    intro w₀ hw₀
    have hlf : LocallyFinite fun c : P ↦ support (fun w : (P × E) × ℂ ↦ ρ c w.1.1 • g c w) := by
      refine (ρ.locallyFinite.preimage_continuous
        (continuous_fst.comp continuous_fst)).subset fun c w hw ↦ ?_
      exact fun h0 ↦ hw (smul_eq_zero_of_left h0 (g c w))
    refine (_root_.contMDiffAt_finsum hlf fun c ↦ ?_).contMDiffWithinAt
    by_cases hpc : w₀.1.1 ∈ tsupport (ρ c)
    · have hp_chart : w₀.1.1 ∈ (chartAt HP c).source := hρ c hpc
      have hp_src : w₀.1.1 ∈ (extChartAt I c).source := by rwa [extChartAt_source]
      have hp_tgt : extChartAt I c w₀.1.1 ∈ (extChartAt I c).target :=
        (extChartAt I c).map_source hp_src
      have hρc : ContMDiffAt ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℝ) ∞
          (fun w : (P × E) × ℂ ↦ ρ c w.1.1) w₀ :=
        ((ρ c).contMDiff.comp (contMDiff_fst.comp contMDiff_fst)).contMDiffAt
      have hext : ContMDiffAt ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, EP) ∞
          (fun w : (P × E) × ℂ ↦ extChartAt I c w.1.1) w₀ :=
        ((contMDiffOn_extChartAt (I := I) (x := c)).contMDiffAt
          ((chartAt HP c).open_source.mem_nhds hp_chart)).comp w₀
          (contMDiffAt_fst.comp w₀ contMDiffAt_fst)
      have hcoord : ContMDiffAt ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ))
          ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞
          (fun w : (P × E) × ℂ ↦ ((extChartAt I c w.1.1, w.1.2), w.2)) w₀ :=
        (hext.prodMk (contMDiffAt_snd.comp w₀ contMDiffAt_fst)).prodMk contMDiffAt_snd
      have hvc_cdiff : ContDiffAt ℝ ∞ (v c) ((extChartAt I c w₀.1.1, w₀.1.2), w₀.2) :=
        (hv_smooth c).contDiffAt
          ((((isOpen_extChartAt_target c).prod hQ).prod hΩ).mem_nhds
            ⟨⟨hp_tgt, hw₀.1.2⟩, hw₀.2⟩)
      have hvc_mdiff :
          ContMDiffAt ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ (v c)
            ((extChartAt I c w₀.1.1, w₀.1.2), w₀.2) := by
        rw [contMDiffAt_prod_prod_modelWithCornersSelf_iff,
          contMDiffAt_prod_modelWithCornersSelf_iff, contMDiffAt_iff_contDiffAt]
        exact hvc_cdiff
      exact hρc.smul (hvc_mdiff.comp w₀ hcoord)
    · refine contMDiffAt_of_notMem ?_ ∞
      intro hw_tsupp
      have hsub : tsupport (fun w : (P × E) × ℂ ↦ ρ c w.1.1 • g c w) ⊆
          (fun w : (P × E) × ℂ ↦ w.1.1) ⁻¹' tsupport (ρ c) :=
        closure_minimal (fun w hw ↦ subset_tsupport (ρ c) fun h0 ↦
            hw (smul_eq_zero_of_left h0 (g c w)))
          ((isClosed_tsupport (ρ c)).preimage (continuous_fst.comp continuous_fst))
      exact hpc (hsub hw_tsupp)
  · -- Holomorphy in `q ∈ Q` for each fixed `p : P` and `z ∈ Ω`.
    intro p z hz
    have heq : (fun q ↦ u ((p, q), z)) =
        fun q ↦ ∑ c ∈ ρ.finsupport p, (ρ c p : ℂ) • v c ((extChartAt I c p, q), z) := by
      ext q
      dsimp only [u, g]
      rw [← ρ.sum_finsupport_smul_eq_finsum p (fun c p' ↦ v c ((extChartAt I c p', q), z))]
      exact Finset.sum_congr rfl fun c _ ↦ (Complex.coe_smul (ρ c p) _).symm
    rw [heq]
    exact DifferentiableOn.fun_sum fun c hc ↦
      (hv_hol c (extChartAt I c p) (hmem_tgt hc).2 z hz).const_smul (ρ c p : ℂ)
  · -- `\bar∂_z` equation for each fixed `p : P`, `q ∈ Q`, and `z ∈ Ω`.
    intro p q hq z hz
    have heq : (fun w ↦ u ((p, q), w)) =
        fun w ↦ ∑ c ∈ ρ.finsupport p, (ρ c p : ℂ) • v c ((extChartAt I c p, q), w) := by
      ext w
      dsimp only [u, g]
      rw [← ρ.sum_finsupport_smul_eq_finsum p (fun c p' ↦ v c ((extChartAt I c p', q), w))]
      exact Finset.sum_congr rfl fun c _ ↦ (Complex.coe_smul (ρ c p) _).symm
    have hdiff_c : ∀ c ∈ ρ.finsupport p,
        DifferentiableAt ℝ (fun w ↦ (ρ c p : ℂ) • v c ((extChartAt I c p, q), w)) z := by
      intro c hc
      have hvc : ContDiffAt ℝ ∞ (fun w ↦ v c ((extChartAt I c p, q), w)) z :=
        ((hv_smooth c).contDiffAt
          ((((isOpen_extChartAt_target c).prod hQ).prod hΩ).mem_nhds
            ⟨⟨(hmem_tgt hc).2, hq⟩, hz⟩)).comp z
          (contDiffAt_const.prodMk contDiffAt_id)
      exact (hvc.differentiableAt (by simp)).const_smul (ρ c p : ℂ)
    rw [heq, conjWirtingerDeriv_sum (ρ.finsupport p) hdiff_c, FunLike.coe_sum, Finset.sum_apply]
    have hterm : ∀ c ∈ ρ.finsupport p,
        conjWirtingerDeriv (fun w ↦ (ρ c p : ℂ) • v c ((extChartAt I c p, q), w)) z 1 =
          ρ c p • f ((p, q), z) := by
      intro c hc
      obtain ⟨hp_src, hp_tgt⟩ := hmem_tgt hc
      -- Rewrite the pointwise scalar multiple as `(ρ c p : ℂ) • fun w ↦ ...`.
      change conjWirtingerDeriv ((ρ c p : ℂ) • fun w ↦ v c ((extChartAt I c p, q), w)) z 1 = _
      rw [conjWirtingerDeriv_const_smul, smul_apply,
        hv_dbar c (extChartAt I c p) hp_tgt q hq z hz, (extChartAt I c).left_inv hp_src,
        Complex.coe_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ρ.sum_finsupport p (mem_univ p), one_smul]

/-- **Joint smooth/holomorphic parameter-dependent one-variable `\bar∂` solver.** For a
finite-dimensional smooth boundaryless Hausdorff second-countable parameter manifold `P`, an open
complex parameter domain `Q` in a finite-dimensional complex normed space `E`, and an open plane
domain `Ω ⊆ ℂ`, every `f : (P × E) × ℂ → ℂ` that is jointly smooth on `(Set.univ ×ˢ Q) ×ˢ Ω` and
holomorphic in `q ∈ Q` admits a jointly smooth `u : (P × E) × ℂ → ℂ`, holomorphic in `q ∈ Q`,
solving `(fderiv ℝ (fun w ↦ u ((p, q), w)) z 1 + I * fderiv ℝ (fun w ↦ u ((p, q), w)) z I) / 2 =
f ((p, q), z)` at every point of `P × Q × Ω`. Neither `Q` nor `Ω` is assumed bounded, connected, or
a polydisc. -/
theorem exists_mixed_parameter_dbar_solution
    {EP HP P E : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP] (I : ModelWithCorners ℝ EP HP) [I.Boundaryless]
    [TopologicalSpace P] [ChartedSpace HP P] [IsManifold I ∞ P]
    [T2Space P] [SecondCountableTopology P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (Q : Set E) (Ω : Set ℂ) (hQ : IsOpen Q) (hΩ : IsOpen Ω)
    (f : (P × E) × ℂ → ℂ)
    (hf : ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ f
      ((Set.univ ×ˢ Q) ×ˢ Ω))
    (hfhol : ∀ p z, z ∈ Ω → DifferentiableOn ℂ (fun q ↦ f ((p, q), z)) Q) :
    ∃ u : (P × E) × ℂ → ℂ,
      ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ u
        ((Set.univ ×ˢ Q) ×ˢ Ω) ∧
      (∀ p z, z ∈ Ω → DifferentiableOn ℂ (fun q ↦ u ((p, q), z)) Q) ∧
      (∀ p q, q ∈ Q → ∀ z, z ∈ Ω →
        (fderiv ℝ (fun w ↦ u ((p, q), w)) z 1 +
          Complex.I * fderiv ℝ (fun w ↦ u ((p, q), w)) z Complex.I) / 2 =
          f ((p, q), z)) := by
  obtain ⟨u, hu_smooth, hu_hol, hu_dbar⟩ :=
    exists_contMDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq I hQ hΩ hf hfhol
  refine ⟨u, hu_smooth, hu_hol, fun p q hq z hz ↦ ?_⟩
  have h2 := fderiv_apply_one_add_I_smul_fderiv_apply_I (fun w ↦ u ((p, q), w)) z
  rw [smul_eq_mul, smul_eq_mul] at h2
  rw [h2, mul_div_cancel_left₀ _ two_ne_zero, hu_dbar p q hq z hz]

end TauCeti
