/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Changing the model space along a diffeomorphism

Let `Φ : H ≃ₘ^n⟮I, I'⟯ H'` be a `C^n` diffeomorphism between two model spaces. Conjugating a
`C^n` chart change of `H` by `Φ` gives a `C^n` chart change of `H'`
(`Diffeomorph.symm_trans_trans_mem_contDiffGroupoid`). Consequently, a `C^n` manifold modelled on
`I` is a `C^n` manifold modelled on `I'` for the composite charts `ChartedSpace.comp H' H M`, where
`H` carries the single chart `Φ` (`Diffeomorph.isManifold_chartedSpaceComp`).

For instance, a model with corners described as a subset of `ℂ` can be compared with Mathlib's
native half-spaces in this way. The identity on `M` then upgrades to a `C^n` diffeomorphism between
the original and transported manifold structures (`Diffeomorph.chartedSpaceCompDiffeomorph`).
-/

public section

open Set
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}

namespace Diffeomorph

/-- Conjugating a member of the `C^n` groupoid of `I` by a `C^n` diffeomorphism of models gives a
member of the `C^n` groupoid of `I'`. -/
theorem symm_trans_trans_mem_contDiffGroupoid (Φ : H ≃ₘ^n⟮I, I'⟯ H')
    {e : OpenPartialHomeomorph H H} (he : e ∈ contDiffGroupoid n I) :
    Φ.toHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        (e ≫ₕ Φ.toHomeomorph.toOpenPartialHomeomorph) ∈ contDiffGroupoid n I' := by
  -- Each groupoid member `f` read through `Φ` is `C^n` where `Φ.symm` lands in its source.
  have key : ∀ f ∈ contDiffGroupoid n I,
      ContMDiffOn I' I' n (Φ ∘ f ∘ Φ.symm) (Φ.symm ⁻¹' f.source) := fun f hf ↦
    Φ.contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_contDiffGroupoid hf).comp Φ.symm.contMDiff.contMDiffOn fun _ hv ↦ hv)
  have hrefl : OpenPartialHomeomorph.refl H' ∈ IsManifold.maximalAtlas I' n H' :=
    StructureGroupoid.subset_maximalAtlas _ (chartedSpaceSelf_atlas.mpr rfl)
  have h := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn hrefl hrefl
    (f := Φ.toHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
      (e ≫ₕ Φ.toHomeomorph.toOpenPartialHomeomorph)) ?_ ?_
  · simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans,
      OpenPartialHomeomorph.trans_refl] using h
  · refine (key e he).congr_mono (fun v _ ↦ ?_) fun v hv ↦ ?_
    · simp [OpenPartialHomeomorph.coe_trans]
    · simpa [OpenPartialHomeomorph.trans_source] using hv
  · refine (key e.symm ((contDiffGroupoid n I).symm he)).congr_mono (fun v _ ↦ ?_)
      fun v hv ↦ ?_
    · simp [OpenPartialHomeomorph.coe_trans_symm]
    · simpa [OpenPartialHomeomorph.trans_target] using hv

/-- A `C^n` manifold modelled on `I` is a `C^n` manifold modelled on `I'` for the composite
charts `ChartedSpace.comp H' H M`, when `H` carries the single chart given by a `C^n`
diffeomorphism of models `Φ`. -/
theorem isManifold_chartedSpaceComp (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I n M] :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    IsManifold I' n M := by
  let := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, φ, hφ, rfl⟩ ⟨c', hc', φ', hφ', rfl⟩
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ hφ
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ' hφ'
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc c.symm]
  exact Φ.symm_trans_trans_mem_contDiffGroupoid (HasGroupoid.compatible hc hc')

/-- The identity on `M` as a `C^n` diffeomorphism from the original manifold structure modelled on
`I` to the transported structure `ChartedSpace.comp H' H M` modelled on `I'`. -/
def chartedSpaceCompDiffeomorph (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    M ≃ₘ^n⟮I, I'⟯ M := by
  letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  letI := ChartedSpace.comp H' H M
  refine
    { toEquiv := Equiv.refl M
      contMDiff_toFun := fun x ↦ ?_
      contMDiff_invFun := fun x ↦ ?_ }
  · -- In the matching charts `c` and `c ≫ₕ Φ`, the identity reads as `Φ` on the range of `c`.
    have hΦ := (contMDiffAt_iff.1 (Φ.contMDiff (chartAt H x x))).2
    rw [contMDiffAt_iff]
    refine ⟨continuousAt_id, ?_⟩
    have hpt : (extChartAt I x) x = extChartAt I (chartAt H x x) (chartAt H x x) := by
      simp [extChartAt]
    rw [hpt]
    refine hΦ.congr_of_eventuallyEq ?_ ?_
    · have hmem : (extChartAt I x).target ∈ 𝓝[Set.range I] (extChartAt I x x) :=
        extChartAt_target_mem_nhdsWithin x
      rw [hpt] at hmem
      filter_upwards [hmem] with v hv
      have hrt : I.symm v ∈ (chartAt H x).target := hv.2
      simp [Function.comp_def, extChartAt, chartAt_comp,
        OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
        (chartAt H x).right_inv hrt]
    · simp [Function.comp_def, extChartAt, chartAt_comp,
        OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
        (chartAt H x).left_inv (mem_chart_source H x)]
  · have hΦ := (contMDiffAt_iff.1 (Φ.symm.contMDiff (Φ (chartAt H x x)))).2
    rw [contMDiffAt_iff]
    refine ⟨continuousAt_id, ?_⟩
    have hpt : (extChartAt I' x) x = extChartAt I' (Φ (chartAt H x x)) (Φ (chartAt H x x)) := by
      simp [extChartAt, chartAt_comp, OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]
    rw [hpt]
    refine hΦ.congr_of_eventuallyEq ?_ ?_
    · have hmem : (extChartAt I' x).target ∈ 𝓝[Set.range I'] (extChartAt I' x x) :=
        extChartAt_target_mem_nhdsWithin x
      rw [hpt] at hmem
      filter_upwards [hmem] with v hv
      have hsub : Φ.symm (I'.symm v) ∈ (chartAt H x).target := by
        have := hv
        simp only [extChartAt, OpenPartialHomeomorph.extend_target, chartAt_comp,
          OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
          OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage] at this
        exact this.1.2
      simp [Function.comp_def, extChartAt, chartAt_comp,
        OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
        (chartAt H x).right_inv hsub]
    · simp [Function.comp_def, extChartAt, chartAt_comp,
        OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
        (chartAt H x).left_inv (mem_chart_source H x)]

@[simp]
theorem coe_chartedSpaceCompDiffeomorph (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    ⇑(chartedSpaceCompDiffeomorph Φ M) = id :=
  (rfl)

@[simp]
theorem coe_chartedSpaceCompDiffeomorph_symm (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    ⇑(chartedSpaceCompDiffeomorph Φ M).symm = id :=
  (rfl)

end Diffeomorph
