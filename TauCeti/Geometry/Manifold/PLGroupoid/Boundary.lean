/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Topological
public import TauCeti.Geometry.Manifold.PLGroupoid.Inverse
public import TauCeti.Geometry.Manifold.PLGroupoid.Simplex.Ball
public import TauCeti.Geometry.Manifold.PLGroupoid.Simplex.Boundary
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# The boundary of a PL manifold is a PL manifold

Let `M` be a charted space modeled on the product half-space `{q : E × ℝ | 0 ≤ q.2}` via
`TauCeti.modelWithCornersHalfSpace E`, where `E` is a finite-dimensional real normed space. By
topological invariance of the boundary (`TauCeti.mem_boundary_modelWithCornersHalfSpace_iff`),
every open partial homeomorphism `e` from `M` to `{q : E × ℝ | 0 ≤ q.2}` detects boundary points by
the vanishing of their normal coordinate `(e x).1.2 = 0`. Deleting that coordinate restricts each
ambient chart to a boundary chart (`TauCeti.halfSpaceBoundaryChart`), equipping
`↥((modelWithCornersHalfSpace E).boundary M)` with a canonical boundaryless charted-space structure
modeled on `E` (`TauCeti.halfSpaceBoundaryChartedSpace`). Because `𝓘(ℝ, E)` is a boundaryless model,
`BoundarylessManifold 𝓘(ℝ, E) ↥((modelWithCornersHalfSpace E).boundary M)` is inferred
automatically.

When `M` is a PL manifold (`HasGroupoid M (PLGroupoid (modelWithCornersHalfSpace E))`), its boundary
inherits a PL manifold structure (`TauCeti.hasGroupoid_PLGroupoid_halfSpaceBoundary`): each boundary
transition map is the ambient transition map conjugated by the continuous affine parametrization and
projection of `E × {0} ⊆ E × ℝ`. The boundary inclusion `Subtype.val` is a PL closed embedding
(`TauCeti.isPLMap_subtypeVal_halfSpaceBoundary`,
`TauCeti.isClosedEmbedding_subtypeVal_halfSpaceBoundary`), and PL maps carrying boundary into
boundary — in particular PL homeomorphisms — restrict to PL maps between the boundaries
(`TauCeti.IsPLMap.restrict_halfSpaceBoundary`, `Homeomorph.halfSpaceBoundary`).

Finally, on the solid coordinate simplex `coordinateSimplex (Option ι)` equipped with its half-space
vertex charts (`TauCeti.coordinateSimplexHalfSpaceChartedSpace`), the manifold boundary coincides
with the geometric frontier `frontier (coordinateSimplex (Option ι))`, and the canonical
coordinate-preserving homeomorphism (`TauCeti.coordinateSimplexHalfSpaceBoundaryHomeomorph`) to
`frontier (coordinateSimplex (Option ι))` with its direct polyhedral sphere atlas
(`TauCeti.coordinateSimplexBoundaryChartedSpace`) is a PL homeomorphism (`IsPLMap` in both
directions).

Whereas `TauCeti.boundaryChartedSpace` in `TauCeti.Geometry.Manifold.Boundary.Charts` equips
`↥((𝓡∂ (n + 1)).boundary M)` with boundary charts under `IsManifold (𝓡∂ (n + 1)) 1 M`, the
construction here works on `TauCeti.modelWithCornersHalfSpace E` with no differentiability
hypothesis on `M`, using topological invariance of the boundary.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 1–2 (PL manifolds and their boundaries).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 1.
-/

public section

open Function Set Filter Topology StructureGroupoid
open scoped Manifold

namespace TauCeti

/-! ### Parametrization and projection of the boundary slice in `{q : E × ℝ | 0 ≤ q.2}` -/

section Slice

variable {E : Type*}

/-- Embed the tangential vector space `E` into the product half-space `{q : E × ℝ | 0 ≤ q.2}` at
height zero. -/
def halfSpaceBoundaryParam (z : E) : {q : E × ℝ | 0 ≤ q.2} :=
  ⟨(z, 0), by rw [mem_ofPred_eq]⟩

/-- Read the tangential coordinate of a point of the product half-space `{q : E × ℝ | 0 ≤ q.2}`. -/
def halfSpaceBoundaryProj (q : {q : E × ℝ | 0 ≤ q.2}) : E :=
  q.1.1

@[simp]
theorem coe_halfSpaceBoundaryParam (z : E) :
    (halfSpaceBoundaryParam z).1 = (z, (0 : ℝ)) := (rfl)

@[simp]
theorem halfSpaceBoundaryProj_apply (q : {q : E × ℝ | 0 ≤ q.2}) :
    halfSpaceBoundaryProj q = q.1.1 := (rfl)

/-- Projecting `TauCeti.halfSpaceBoundaryParam z` back to `E` recovers `z`. -/
theorem halfSpaceBoundaryProj_param (z : E) :
    halfSpaceBoundaryProj (halfSpaceBoundaryParam z) = z := (rfl)

/-- On the height-zero slice of `{q : E × ℝ | 0 ≤ q.2}`, projecting to `E` and reinserting height
zero is the identity. -/
theorem halfSpaceBoundaryParam_proj {q : {q : E × ℝ | 0 ≤ q.2}} (hq : q.1.2 = 0) :
    halfSpaceBoundaryParam (halfSpaceBoundaryProj q) = q :=
  Subtype.ext (Prod.ext rfl hq.symm)

section Topological

variable [TopologicalSpace E]

/-- `TauCeti.halfSpaceBoundaryParam` is continuous. -/
theorem continuous_halfSpaceBoundaryParam : Continuous (halfSpaceBoundaryParam (E := E)) :=
  (continuous_id.prodMk continuous_const).subtype_mk _

/-- `TauCeti.halfSpaceBoundaryProj` is continuous. -/
theorem continuous_halfSpaceBoundaryProj : Continuous (halfSpaceBoundaryProj (E := E)) :=
  continuous_fst.comp continuous_subtype_val

end Topological

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluating `(modelWithCornersHalfSpace E).symm` at `(z, 0)` recovers
`TauCeti.halfSpaceBoundaryParam z`. -/
@[simp]
theorem modelWithCornersHalfSpace_symm_param (z : E) :
    (modelWithCornersHalfSpace E).symm (z, 0) = halfSpaceBoundaryParam z :=
  Subtype.ext ((coe_modelWithCornersHalfSpace_symm_apply E (q := (z, 0)) le_rfl).trans
    (coe_halfSpaceBoundaryParam z).symm)

end Normed

end Slice

/-! ### Boundary charts and charted-space structure -/

section BoundaryCharts

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace {q : E × ℝ | 0 ≤ q.2} M]

private theorem symm_halfSpaceBoundaryParam_mem_boundary
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) {z : E}
    (hz : halfSpaceBoundaryParam z ∈ e.target) :
    e.symm (halfSpaceBoundaryParam z) ∈ (modelWithCornersHalfSpace E).boundary M := by
  rw [mem_boundary_modelWithCornersHalfSpace_iff e (e.map_target hz), e.right_inv hz,
    coe_halfSpaceBoundaryParam]

private theorem halfSpaceBoundaryParam_proj_chart_apply
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) {x : M} (hx : x ∈ e.source)
    (hxM : x ∈ (modelWithCornersHalfSpace E).boundary M) :
    halfSpaceBoundaryParam (halfSpaceBoundaryProj (e x)) = e x :=
  halfSpaceBoundaryParam_proj ((mem_boundary_modelWithCornersHalfSpace_iff e hx).mp hxM)

/-- Restrict any open partial homeomorphism `e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}` to a
chart of the boundary `↥((modelWithCornersHalfSpace E).boundary M)` by reading the tangential
coordinate in `E`. The base point `p` witnesses nonemptiness of the boundary for the junk value of
`e.subtypeCoord` outside the target. -/
noncomputable def halfSpaceBoundaryChart (p : ↥((modelWithCornersHalfSpace E).boundary M))
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) :
    OpenPartialHomeomorph ↥((modelWithCornersHalfSpace E).boundary M) E :=
  e.subtypeCoord ((modelWithCornersHalfSpace E).boundary M) ⟨p⟩
    halfSpaceBoundaryParam halfSpaceBoundaryProj
    (symm_halfSpaceBoundaryParam_mem_boundary e)
    (halfSpaceBoundaryParam_proj_chart_apply e)
    (fun _ _ => halfSpaceBoundaryProj_param _)
    continuous_halfSpaceBoundaryParam
    continuous_halfSpaceBoundaryProj.continuousOn

@[simp]
theorem halfSpaceBoundaryChart_source (p : ↥((modelWithCornersHalfSpace E).boundary M))
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) :
    (halfSpaceBoundaryChart p e).source = Subtype.val ⁻¹' e.source :=
  e.subtypeCoord_source _ _ _ _ _ _ _ _ _

@[simp]
theorem halfSpaceBoundaryChart_target (p : ↥((modelWithCornersHalfSpace E).boundary M))
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) :
    (halfSpaceBoundaryChart p e).target = halfSpaceBoundaryParam ⁻¹' e.target :=
  e.subtypeCoord_target _ _ _ _ _ _ _ _ _

@[simp]
theorem halfSpaceBoundaryChart_apply (p q : ↥((modelWithCornersHalfSpace E).boundary M))
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) :
    halfSpaceBoundaryChart p e q = (e q.1).1.1 :=
  e.subtypeCoord_apply _ _ _ _ _ _ _ _ _ q

@[simp]
theorem coe_halfSpaceBoundaryChart_symm_apply (p : ↥((modelWithCornersHalfSpace E).boundary M))
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) {z : E}
    (hz : halfSpaceBoundaryParam z ∈ e.target) :
    (((halfSpaceBoundaryChart p e).symm z : ↥((modelWithCornersHalfSpace E).boundary M)) : M) =
      e.symm (halfSpaceBoundaryParam z) :=
  e.coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ hz

/-- The canonical boundaryless charted-space structure on the boundary of a charted space modeled
on `TauCeti.modelWithCornersHalfSpace E`, for finite-dimensional `E`. Each preferred chart is
induced by the preferred ambient chart at the same boundary point. -/
@[irreducible, instance] noncomputable def halfSpaceBoundaryChartedSpace :
    ChartedSpace E ↥((modelWithCornersHalfSpace E).boundary M) where
  atlas := range fun p => halfSpaceBoundaryChart p (chartAt {q : E × ℝ | 0 ≤ q.2} p.1)
  chartAt p := halfSpaceBoundaryChart p (chartAt {q : E × ℝ | 0 ≤ q.2} p.1)
  mem_chart_source p := by
    rw [halfSpaceBoundaryChart_source]
    exact mem_chart_source _ p.1
  chart_mem_atlas p := mem_range_self p

variable (M) in
private theorem halfSpaceBoundaryChartedSpace_chartAt
    (p : ↥((modelWithCornersHalfSpace E).boundary M)) :
    chartAt E p = halfSpaceBoundaryChart p (chartAt {q : E × ℝ | 0 ≤ q.2} p.1) := by
  unfold halfSpaceBoundaryChartedSpace
  rfl

variable (M) in
/-- The atlas of `TauCeti.halfSpaceBoundaryChartedSpace` is the range of its preferred charts. -/
theorem halfSpaceBoundaryChartedSpace_atlas :
    atlas E ↥((modelWithCornersHalfSpace E).boundary M) =
      range fun p : ↥((modelWithCornersHalfSpace E).boundary M) => chartAt E p := by
  unfold atlas halfSpaceBoundaryChartedSpace chartAt
  rfl

variable (M) in
/-- The source of the preferred boundary chart at `p` is the trace of the ambient preferred chart's
source on the boundary. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_source
    (p : ↥((modelWithCornersHalfSpace E).boundary M)) :
    (chartAt E p).source = Subtype.val ⁻¹' (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).source := by
  rw [halfSpaceBoundaryChartedSpace_chartAt]
  exact halfSpaceBoundaryChart_source p _

variable (M) in
/-- The target of the preferred boundary chart at `p` is the preimage of the ambient preferred
chart's target under `TauCeti.halfSpaceBoundaryParam`. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_target
    (p : ↥((modelWithCornersHalfSpace E).boundary M)) :
    (chartAt E p).target =
      halfSpaceBoundaryParam ⁻¹' (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target := by
  rw [halfSpaceBoundaryChartedSpace_chartAt]
  exact halfSpaceBoundaryChart_target p _

variable (M) in
/-- The preferred boundary chart at `p` reads the tangential coordinate of the ambient preferred
chart at `p`. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_apply
    (p q : ↥((modelWithCornersHalfSpace E).boundary M)) :
    chartAt E p q = (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M) (q : M)).1.1 := by
  rw [halfSpaceBoundaryChartedSpace_chartAt]
  exact halfSpaceBoundaryChart_apply p q _

variable (M) in
/-- On its target, the inverse of the preferred boundary chart at `p` evaluates the inverse of the
ambient preferred chart at `TauCeti.halfSpaceBoundaryParam z`. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_symm_apply
    (p : ↥((modelWithCornersHalfSpace E).boundary M)) {z : E}
    (hz : halfSpaceBoundaryParam z ∈ (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target) :
    (((chartAt E p).symm z : ↥((modelWithCornersHalfSpace E).boundary M)) : M) =
      (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).symm (halfSpaceBoundaryParam z) := by
  rw [halfSpaceBoundaryChartedSpace_chartAt]
  exact coe_halfSpaceBoundaryChart_symm_apply p _ hz

/-! ### PL compatibility of boundary charts and inclusion -/

/-- If the transition between two ambient half-space charts lies in `PLGroupoid`, then the induced
transition between the corresponding boundary charts lies in `PLGroupoid 𝓘(ℝ, E)`. -/
theorem halfSpaceBoundaryChart_symm_trans_mem_PLGroupoid
    (p q : ↥((modelWithCornersHalfSpace E).boundary M))
    {e₁ e₂ : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}}
    (h12 : e₁.symm.trans e₂ ∈ PLGroupoid (modelWithCornersHalfSpace E)) :
    (halfSpaceBoundaryChart p e₁).symm.trans (halfSpaceBoundaryChart q e₂) ∈
      PLGroupoid 𝓘(ℝ, E) := by
  rw [mem_PLGroupoid_iff_isPLOn (ModelWithCorners.isConvexPolyhedron_range 𝓘(ℝ, E))]
  let I := modelWithCornersHalfSpace E
  let φ := e₁.symm.trans e₂
  let ψ := (halfSpaceBoundaryChart p e₁).symm.trans (halfSpaceBoundaryChart q e₂)
  have hG : IsPLOn (I ∘ φ ∘ I.symm) (I.symm ⁻¹' φ.source ∩ range I) :=
    ((mem_PLGroupoid_iff I).mp h12).1
  let inl : E →ᴬ[ℝ] E × ℝ := ((ContinuousLinearMap.id ℝ E).prod 0).toContinuousAffineMap
  let fst : E × ℝ →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hz₁ {z : E} (hz : z ∈ ψ.source) : halfSpaceBoundaryParam z ∈ e₁.target := by
    simpa only [ψ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_symm, halfSpaceBoundaryChart_target, mem_preimage] using hz.1
  have hmap : ψ.source ⊆ inl ⁻¹' (I.symm ⁻¹' φ.source ∩ range I) := fun z hz => by
    have h₁ := hz₁ hz
    have h₂ : (((halfSpaceBoundaryChart p e₁).symm z :
        ↥((modelWithCornersHalfSpace E).boundary M)) : M) ∈ e₂.source := by
      simpa only [ψ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_symm,
        halfSpaceBoundaryChart_source, mem_preimage] using hz.2
    rw [coe_halfSpaceBoundaryChart_symm_apply p e₁ h₁] at h₂
    refine ⟨?_, by simp [inl, I]⟩
    simpa only [inl, I, mem_preimage, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
      modelWithCornersHalfSpace_symm_param, φ, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source] using ⟨h₁, h₂⟩
  have hcomp : IsPLOn (fst ∘ (I ∘ φ ∘ I.symm) ∘ inl) ψ.source :=
    (isPLOn_continuousAffineMap fst univ).comp
      (hG.comp (isPLOn_continuousAffineMap inl ψ.source) hmap) (fun _ _ => mem_univ _)
  refine (hcomp.congr fun z hz => ?_).mono inter_subset_left
  have h₁ := hz₁ hz
  simp only [φ, I, inl, fst, Function.comp_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
    ContinuousLinearMap.coe_fst', modelWithCornersHalfSpace_symm_param,
    modelWithCornersHalfSpace_apply, halfSpaceBoundaryChart_apply,
    coe_halfSpaceBoundaryChart_symm_apply p e₁ h₁, mfld_simps]

/-- **The boundary of a PL manifold with boundary is a PL manifold** of dimension one less. -/
instance hasGroupoid_PLGroupoid_halfSpaceBoundary
    [HasGroupoid M (PLGroupoid (modelWithCornersHalfSpace E))] :
    HasGroupoid ↥((modelWithCornersHalfSpace E).boundary M) (PLGroupoid 𝓘(ℝ, E)) where
  compatible := by
    rw [halfSpaceBoundaryChartedSpace_atlas]
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    dsimp only
    rw [halfSpaceBoundaryChartedSpace_chartAt M p, halfSpaceBoundaryChartedSpace_chartAt M q]
    exact halfSpaceBoundaryChart_symm_trans_mem_PLGroupoid p q
      (StructureGroupoid.compatible _ (chart_mem_atlas _ p.1) (chart_mem_atlas _ q.1))

/-- Restricting any chart in the maximal PL atlas of `M` to the boundary produces a chart in the
maximal PL atlas of `↥((modelWithCornersHalfSpace E).boundary M)`. -/
theorem halfSpaceBoundaryChart_mem_maximalAtlas
    (p : ↥((modelWithCornersHalfSpace E).boundary M))
    {e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}}
    (he : e ∈ (PLGroupoid (modelWithCornersHalfSpace E)).maximalAtlas M) :
    halfSpaceBoundaryChart p e ∈
      (PLGroupoid 𝓘(ℝ, E)).maximalAtlas ↥((modelWithCornersHalfSpace E).boundary M) := by
  rw [mem_maximalAtlas_iff, halfSpaceBoundaryChartedSpace_atlas M]
  rintro _ ⟨q, rfl⟩
  dsimp only
  rw [halfSpaceBoundaryChartedSpace_chartAt M q]
  obtain ⟨h1, h2⟩ := mem_maximalAtlas_iff.mp he _ (chart_mem_atlas _ q.1)
  exact ⟨halfSpaceBoundaryChart_symm_trans_mem_PLGroupoid p q h1,
    halfSpaceBoundaryChart_symm_trans_mem_PLGroupoid q p h2⟩

variable (M) in
/-- The inclusion of the boundary into `M` is a closed embedding. -/
theorem isClosedEmbedding_subtypeVal_halfSpaceBoundary :
    IsClosedEmbedding (Subtype.val : ↥((modelWithCornersHalfSpace E).boundary M) → M) :=
  (modelWithCornersHalfSpace E).isClosed_boundary_of_finiteDimensional.isClosedEmbedding_subtypeVal

variable (M) in
/-- The inclusion of the boundary into `M` is a PL map. In the preferred boundary and ambient
charts at `p`, it is the linear inclusion `z ↦ (z, 0)`. -/
theorem isPLMap_subtypeVal_halfSpaceBoundary :
    IsPLMap 𝓘(ℝ, E) (modelWithCornersHalfSpace E)
      (Subtype.val : ↥((modelWithCornersHalfSpace E).boundary M) → M) := by
  rw [isPLMap_iff_forall_isPLMapAt]
  intro p
  rw [isPLMapAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  let inl : E →ᴬ[ℝ] E × ℝ := ((ContinuousLinearMap.id ℝ E).prod 0).toContinuousAffineMap
  have hopen : (chartAt E p).target ∈ 𝓝 (chartAt E p p) :=
    (chartAt E p).open_target.mem_nhds (mem_chart_target E p)
  simp only [mfld_simps]
  rw [← isPLWithinAt_inter hopen]
  refine (inl.isPLWithinAt _ _).congr (fun z hz => ?_) ?_
  · have hz' : halfSpaceBoundaryParam z ∈ (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target := by
      simpa only [halfSpaceBoundaryChartedSpace_chartAt_target M p, mem_preimage] using hz.2
    simp only [inl, Function.comp_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
      halfSpaceBoundaryChartedSpace_chartAt_symm_apply M p hz',
      (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).right_inv hz', modelWithCornersHalfSpace_apply,
      coe_halfSpaceBoundaryParam, mfld_simps]
  · simp only [inl, Function.comp_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
      modelWithCornersHalfSpace_apply, mfld_simps]
    exact Prod.ext (halfSpaceBoundaryChartedSpace_chartAt_apply M p p).symm
      ((mem_boundary_modelWithCornersHalfSpace_iff _ (mem_chart_source _ p.1)).mp p.2)

end BoundaryCharts

/-! ### Functoriality on boundary-preserving PL maps and PL homeomorphisms -/

section Morphisms

variable {E M F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace {q : E × ℝ | 0 ≤ q.2} M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace N] [ChartedSpace {q : F × ℝ | 0 ≤ q.2} N]

/-- If `f : M → N` sends the boundary of `M` into the boundary of `N` and is PL at `p.1`, then its
restriction to the boundaries is PL at `p`. -/
theorem IsPLMapAt.restrict_halfSpaceBoundary {f : M → N}
    (hfb : MapsTo f ((modelWithCornersHalfSpace E).boundary M)
      ((modelWithCornersHalfSpace F).boundary N))
    {p : ↥((modelWithCornersHalfSpace E).boundary M)}
    (hf : IsPLMapAt (modelWithCornersHalfSpace E) (modelWithCornersHalfSpace F) f p.1) :
    IsPLMapAt 𝓘(ℝ, E) 𝓘(ℝ, F) (hfb.restrict f _ _) p := by
  rw [isPLMapAt_iff] at hf ⊢
  refine ⟨hf.1.restrict hfb, ?_⟩
  let q : ↥((modelWithCornersHalfSpace F).boundary N) := hfb.restrict f _ _ p
  let c := chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)
  let d := chartAt {q : F × ℝ | 0 ≤ q.2} (q : N)
  let inl : E →ᴬ[ℝ] E × ℝ := ((ContinuousLinearMap.id ℝ E).prod 0).toContinuousAffineMap
  let fst : F × ℝ →ᴬ[ℝ] F := (ContinuousLinearMap.fst ℝ F ℝ).toContinuousAffineMap
  have hpc : (c p.1).1.2 = 0 :=
    (mem_boundary_modelWithCornersHalfSpace_iff c (mem_chart_source _ p.1)).mp p.2
  have hinl_p : inl (chartAt E p p) = modelWithCornersHalfSpace E (c p.1) := by
    simp [inl, c, halfSpaceBoundaryChartedSpace_chartAt_apply M p p, Prod.ext_iff, hpc]
  have hcomp : IsPLWithinAt
      (fst ∘ ((modelWithCornersHalfSpace F) ∘ d ∘ f ∘ c.symm ∘
        (modelWithCornersHalfSpace E).symm) ∘ inl)
      univ (chartAt E p p) := by
    refine (fst.isPLWithinAt univ _).comp ?_ (mapsTo_univ _ _)
    rw [← hinl_p] at hf
    exact hf.2.comp (inl.isPLWithinAt univ (chartAt E p p)) fun z _ => by simp [inl]
  have hopen : (chartAt E p).target ∈ 𝓝 (chartAt E p p) :=
    (chartAt E p).open_target.mem_nhds (mem_chart_target E p)
  simp only [mfld_simps]
  rw [← isPLWithinAt_inter hopen]
  refine (hcomp.mono inter_subset_left).congr (fun z hz => ?_) ?_
  · have hz' : halfSpaceBoundaryParam z ∈ c.target := by
      simpa only [c, halfSpaceBoundaryChartedSpace_chartAt_target M p, mem_preimage] using hz.2
    simp only [inl, fst, q, c, d, Function.comp_apply,
      ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply, ContinuousLinearMap.coe_fst',
      modelWithCornersHalfSpace_symm_param, modelWithCornersHalfSpace_apply,
      halfSpaceBoundaryChartedSpace_chartAt_apply N q, MapsTo.val_restrict_apply,
      halfSpaceBoundaryChartedSpace_chartAt_symm_apply M p hz', mfld_simps]
  · have hparam : halfSpaceBoundaryParam (chartAt E p p) = c p.1 := by
      rw [halfSpaceBoundaryChartedSpace_chartAt_apply M p p]
      exact halfSpaceBoundaryParam_proj hpc
    simp only [inl, fst, q, c, d, Function.comp_apply,
      ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply, ContinuousLinearMap.coe_fst',
      modelWithCornersHalfSpace_symm_param, modelWithCornersHalfSpace_apply,
      halfSpaceBoundaryChartedSpace_chartAt_apply N q, MapsTo.val_restrict_apply, hparam,
      mfld_simps]

/-- A PL map between manifolds modeled on product half-spaces that sends boundary points to boundary
points restricts to a PL map between their boundaries. -/
theorem IsPLMap.restrict_halfSpaceBoundary {f : M → N}
    (hfb : MapsTo f ((modelWithCornersHalfSpace E).boundary M)
      ((modelWithCornersHalfSpace F).boundary N))
    (hf : IsPLMap (modelWithCornersHalfSpace E) (modelWithCornersHalfSpace F) f) :
    IsPLMap 𝓘(ℝ, E) 𝓘(ℝ, F) (hfb.restrict f _ _) :=
  isPLMap_iff_forall_isPLMapAt.mpr fun p => (hf.isPLMapAt p.1).restrict_halfSpaceBoundary hfb

/-- A homeomorphism between finite-dimensional spaces modeled on product half-spaces restricts to a
homeomorphism between their intrinsic boundaries. -/
def _root_.Homeomorph.halfSpaceBoundary (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace {q : E × ℝ | 0 ≤ q.2} M]
    [TopologicalSpace N] [ChartedSpace {q : F × ℝ | 0 ≤ q.2} N]
    (Φ : M ≃ₜ N) :
    ↥((modelWithCornersHalfSpace E).boundary M) ≃ₜ
      ↥((modelWithCornersHalfSpace F).boundary N) :=
  Φ.subtype fun _ => Φ.isBoundaryPoint_iff

@[simp]
theorem _root_.Homeomorph.coe_halfSpaceBoundary_apply (Φ : M ≃ₜ N)
    (p : ↥((modelWithCornersHalfSpace E).boundary M)) :
    (Φ.halfSpaceBoundary E F p : N) = Φ p.1 := (rfl)

@[simp]
theorem _root_.Homeomorph.coe_halfSpaceBoundary_symm_apply (Φ : M ≃ₜ N)
    (q : ↥((modelWithCornersHalfSpace F).boundary N)) :
    ((Φ.halfSpaceBoundary E F).symm q : M) = Φ.symm q.1 := (rfl)

/-- If a homeomorphism between spaces modeled on product half-spaces is PL, then the induced
boundary homeomorphism is PL. -/
theorem IsPLMap.halfSpaceBoundary {Φ : M ≃ₜ N}
    (hΦ : IsPLMap (modelWithCornersHalfSpace E) (modelWithCornersHalfSpace F) Φ) :
    IsPLMap 𝓘(ℝ, E) 𝓘(ℝ, F) (Φ.halfSpaceBoundary E F) :=
  hΦ.restrict_halfSpaceBoundary fun _ hx => Φ.isBoundaryPoint_iff.mp hx

/-- If a homeomorphism between spaces modeled on product half-spaces is PL, then the inverse of the
induced boundary homeomorphism is also PL. -/
theorem IsPLMap.halfSpaceBoundary_symm {Φ : M ≃ₜ N}
    (hΦ : IsPLMap (modelWithCornersHalfSpace E) (modelWithCornersHalfSpace F) Φ) :
    IsPLMap 𝓘(ℝ, F) 𝓘(ℝ, E) (Φ.halfSpaceBoundary E F).symm :=
  hΦ.halfSpaceBoundary.symm (ModelWithCorners.isConvexPolyhedron_range 𝓘(ℝ, E))

end Morphisms

/-! ### Compatibility on the standard coordinate simplex -/

section Simplex

variable {ι : Type*} [Fintype ι]

/-- The tangential component of the simplex half-space coordinate map at vertex `v` is the direct
simplex-boundary projection `TauCeti.coordinateSimplexBoundaryChartProjection v`. -/
@[simp]
theorem coordinateSimplexHalfSpaceMap_fst (v : Option (Option ι)) (x : Option ι → ℝ) :
    (coordinateSimplexHalfSpaceMap v x).1 = coordinateSimplexBoundaryChartProjection v x := by
  cases v with
  | none =>
    ext i
    simp [coordinateSimplexHalfSpaceMap_none]
  | some j =>
    ext i
    simp [coordinateSimplexHalfSpaceMap_some]

/-- Restricting the inverse simplex half-space coordinate map at vertex `v` to height zero recovers
the direct simplex-boundary lift `TauCeti.coordinateSimplexBoundaryChartLift v`. -/
@[simp]
theorem coordinateSimplexHalfSpaceMap_symm_zero (v : Option (Option ι)) (z : ι → ℝ) :
    (coordinateSimplexHalfSpaceMap v).symm (z, 0) = coordinateSimplexBoundaryChartLift v z := by
  have hnone : (coordinateSimplexHalfSpaceMap none).symm (z, 0) =
      coordinateSimplexBoundaryLift z := by
    rw [coordinateSimplexHalfSpaceMap_symm_none, orthantFlattening_symm_apply, orthantLift_def,
      coordinateSimplexBoundaryLift_def]
    funext i
    cases i <;> simp
  cases v with
  | none => rw [hnone, coordinateSimplexBoundaryChartLift_none]
  | some j => rw [coordinateSimplexHalfSpaceMap_symm_some, hnone,
      coordinateSimplexBoundaryChartLift_some]

/-- On `coordinateSimplex (Option ι)` with `TauCeti.coordinateSimplexHalfSpaceChartedSpace`, a point
lies on the manifold boundary iff its ambient coordinate vector lies on the geometric frontier
`frontier (coordinateSimplex (Option ι))`. -/
theorem mem_boundary_coordinateSimplex_iff (x : coordinateSimplex (Option ι)) :
    letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
    x ∈ (modelWithCornersHalfSpace (ι → ℝ)).boundary (coordinateSimplex (Option ι)) ↔
      x.1 ∈ frontier (coordinateSimplex (Option ι)) := by
  let := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
  obtain ⟨v, hv⟩ := exists_mem_coordinateSimplexHalfSpaceChartSource x
  have hv' : x ∈ (coordinateSimplexHalfSpaceChart v).source := by
    rwa [coordinateSimplexHalfSpaceChart_source]
  exact (mem_boundary_modelWithCornersHalfSpace_iff (E := ι → ℝ)
    (coordinateSimplexHalfSpaceChart v) hv').trans
    (mem_frontier_coordinateSimplex_iff_halfSpaceChart_snd_eq_zero v x hv).symm

/-- The canonical coordinate-preserving homeomorphism from the manifold boundary of the solid
coordinate simplex to its geometric frontier. -/
noncomputable def coordinateSimplexHalfSpaceBoundaryHomeomorph :
    letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
    ↥((modelWithCornersHalfSpace (ι → ℝ)).boundary (coordinateSimplex (Option ι))) ≃ₜ
      ↥(frontier (coordinateSimplex (Option ι))) :=
  letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
  { toFun := fun p => ⟨p.1.1, (mem_boundary_coordinateSimplex_iff p.1).mp p.2⟩
    invFun := fun q =>
      let hq : q.1 ∈ coordinateSimplex (Option ι) :=
        (mem_coordinateSimplex (Option ι) q.1).mpr
          ((mem_frontier_coordinateSimplex (Option ι) q.1).mp q.2).1
      ⟨⟨q.1, hq⟩, (mem_boundary_coordinateSimplex_iff ⟨q.1, hq⟩).mpr q.2⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

/-- Applying `TauCeti.coordinateSimplexHalfSpaceBoundaryHomeomorph` preserves the ambient
coordinates in `Option ι → ℝ`. -/
theorem coe_coordinateSimplexHalfSpaceBoundaryHomeomorph_apply :
    letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
    ∀ p : ↥((modelWithCornersHalfSpace (ι → ℝ)).boundary (coordinateSimplex (Option ι))),
      (coordinateSimplexHalfSpaceBoundaryHomeomorph p : Option ι → ℝ) = p.1.1 :=
  fun _ => rfl

/-- Applying the inverse of `TauCeti.coordinateSimplexHalfSpaceBoundaryHomeomorph` preserves the
ambient coordinates in `Option ι → ℝ`. -/
theorem coe_coordinateSimplexHalfSpaceBoundaryHomeomorph_symm_apply :
    letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
    ∀ q : ↥(frontier (coordinateSimplex (Option ι))),
      ((coordinateSimplexHalfSpaceBoundaryHomeomorph.symm q).1 : Option ι → ℝ) = q.1 :=
  fun _ => rfl

/-- **Simplex boundary compatibility.** The canonical homeomorphism from the induced half-space
boundary of `coordinateSimplex (Option ι)` to `frontier (coordinateSimplex (Option ι))` equipped
with `TauCeti.coordinateSimplexBoundaryChartedSpace` is a PL map. In the matching vertex charts at
any vertex whose source contains the point, its coordinate representation is the identity. -/
theorem isPLMap_coordinateSimplexHalfSpaceBoundaryHomeomorph :
    letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
    letI := coordinateSimplexHalfSpace_hasGroupoid (ι := ι)
    letI := coordinateSimplexBoundaryChartedSpace (ι := ι)
    letI := coordinateSimplexBoundary_hasGroupoid (ι := ι)
    IsPLMap 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ)
      (coordinateSimplexHalfSpaceBoundaryHomeomorph (ι := ι)) := by
  let := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
  let := coordinateSimplexHalfSpace_hasGroupoid (ι := ι)
  let := coordinateSimplexBoundaryChartedSpace (ι := ι)
  let := coordinateSimplexBoundary_hasGroupoid (ι := ι)
  rw [isPLMap_iff_forall_isPLMapAt]
  intro p
  obtain ⟨v, hv⟩ := exists_mem_coordinateSimplexHalfSpaceChartSource p.1
  let e := halfSpaceBoundaryChart p (coordinateSimplexHalfSpaceChart v)
  let e' := coordinateSimplexBoundaryChart (ι := ι) v
  have he : e ∈ (PLGroupoid 𝓘(ℝ, ι → ℝ)).maximalAtlas
      ↥((modelWithCornersHalfSpace (ι → ℝ)).boundary (coordinateSimplex (Option ι))) :=
    halfSpaceBoundaryChart_mem_maximalAtlas p
      (subset_maximalAtlas _ (coordinateSimplexHalfSpaceChartedSpace_atlas (ι := ι) ▸
        mem_range_self v))
  have he' : e' ∈ (PLGroupoid 𝓘(ℝ, ι → ℝ)).maximalAtlas
      ↥(frontier (coordinateSimplex (Option ι))) :=
    subset_maximalAtlas _ (coordinateSimplexBoundaryChartedSpace_atlas (ι := ι) ▸
      mem_range_self v)
  have hp : p ∈ e.source := by
    simpa only [e, halfSpaceBoundaryChart_source, coordinateSimplexHalfSpaceChart_source,
      mem_preimage] using hv
  have hfp : coordinateSimplexHalfSpaceBoundaryHomeomorph p ∈ e'.source := by
    cases v with
    | none => simpa only [e', coordinateSimplexBoundaryChart_source,
        coordinateSimplexBoundaryChartSource_none, coordinateSimplexHalfSpaceChartSource_none,
        mem_ofPred_eq, coe_coordinateSimplexHalfSpaceBoundaryHomeomorph_apply] using hv
    | some j => simpa only [e', coordinateSimplexBoundaryChart_source,
        coordinateSimplexBoundaryChartSource_some, coordinateSimplexHalfSpaceChartSource_some,
        mem_ofPred_eq, coe_coordinateSimplexHalfSpaceBoundaryHomeomorph_apply] using hv
  rw [isPLMapAt_iff_of_mem_maximalAtlas he hp he' hfp]
  refine ⟨coordinateSimplexHalfSpaceBoundaryHomeomorph.continuous.continuousAt, ?_⟩
  have hopen : e.target ∈ 𝓝 (e p) := e.open_target.mem_nhds (e.map_source hp)
  simp only [mfld_simps]
  rw [← isPLWithinAt_inter hopen]
  refine ((ContinuousAffineMap.id ℝ (ι → ℝ)).isPLWithinAt _ _).congr (fun z hz => ?_) ?_
  · have hz' : halfSpaceBoundaryParam z ∈ (coordinateSimplexHalfSpaceChart v).target := by
      simpa only [e, halfSpaceBoundaryChart_target, mem_preimage] using hz.2
    have hsymm := coe_coordinateSimplexHalfSpaceChart_symm_apply v hz'
    simp only [e, e', Function.comp_apply, ContinuousAffineMap.coe_id,
      coordinateSimplexBoundaryChart_apply, coe_coordinateSimplexHalfSpaceBoundaryHomeomorph_apply,
      coe_halfSpaceBoundaryChart_symm_apply p _ hz', hsymm, coe_halfSpaceBoundaryParam,
      coordinateSimplexHalfSpaceMap_symm_zero, coordinateSimplexBoundaryChartProjection_lift,
      mfld_simps]
  · rw [Function.comp_apply, Function.comp_apply, e.left_inv hp]
    simp only [e, e', ContinuousAffineMap.coe_id, id_eq, halfSpaceBoundaryChart_apply,
      coe_coordinateSimplexHalfSpaceChart_apply, coordinateSimplexBoundaryChart_apply,
      coe_coordinateSimplexHalfSpaceBoundaryHomeomorph_apply, coordinateSimplexHalfSpaceMap_fst]

/-- The inverse of `TauCeti.coordinateSimplexHalfSpaceBoundaryHomeomorph` is also a PL map, so the
induced boundary PL structure on `coordinateSimplex (Option ι)` and the direct polyhedral sphere PL
structure on `frontier (coordinateSimplex (Option ι))` are PL homeomorphic. -/
theorem isPLMap_coordinateSimplexHalfSpaceBoundaryHomeomorph_symm :
    letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
    letI := coordinateSimplexHalfSpace_hasGroupoid (ι := ι)
    letI := coordinateSimplexBoundaryChartedSpace (ι := ι)
    letI := coordinateSimplexBoundary_hasGroupoid (ι := ι)
    IsPLMap 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ)
      (coordinateSimplexHalfSpaceBoundaryHomeomorph (ι := ι)).symm := by
  let := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
  let := coordinateSimplexHalfSpace_hasGroupoid (ι := ι)
  let := coordinateSimplexBoundaryChartedSpace (ι := ι)
  let := coordinateSimplexBoundary_hasGroupoid (ι := ι)
  exact (isPLMap_coordinateSimplexHalfSpaceBoundaryHomeomorph (ι := ι)).symm
    (ModelWithCorners.isConvexPolyhedron_range 𝓘(ℝ, ι → ℝ))

end Simplex

end TauCeti
