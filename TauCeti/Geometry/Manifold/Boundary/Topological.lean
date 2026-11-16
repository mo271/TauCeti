/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Geometry.Manifold.Instances.HalfSpace

/-!
# Topological invariance of manifold interior and boundary

Mathlib defines `ModelWithCorners.IsInteriorPoint` and `ModelWithCorners.IsBoundaryPoint` on an
arbitrary charted space using the preferred chart at the point, and proves their independence of the
choice of chart — hence openness of `I.interior M` and closedness of `I.boundary M` — only on `C¹`
manifolds via calculus (`DifferentiableAt.mem_interior_convex_of_surjective_fderiv`).

For finite-dimensional real models with corners, Brouwer's invariance of domain removes all
differentiability assumptions:

* Any open partial homeomorphism `φ : OpenPartialHomeomorph H H'` between finite-dimensional real
  model spaces with nonempty source forces `finrank ℝ E = finrank ℝ E'`
  (`ModelWithCorners.finrank_eq_of_openPartialHomeomorph`) and preserves both `interior (range I)`
  and `frontier (range I)` (`ModelWithCorners.mem_interior_range_iff_of_openPartialHomeomorph`,
  `ModelWithCorners.mem_frontier_range_iff_of_openPartialHomeomorph`).
* Consequently, on any charted space `M` over a finite-dimensional real model `(E, H, I)` — with no
  `IsManifold` or `HasGroupoid` assumption — interior and boundary points are detected by *any*
  open partial homeomorphism `e : OpenPartialHomeomorph M H` around the point
  (`ModelWithCorners.isInteriorPoint_iff_of_openPartialHomeomorph`,
  `ModelWithCorners.isBoundaryPoint_iff_of_openPartialHomeomorph`), `I.interior M` is open
  (`ModelWithCorners.isOpen_interior_of_finiteDimensional`), and `I.boundary M` is closed
  (`ModelWithCorners.isClosed_boundary_of_finiteDimensional`).
* Open embeddings and homeomorphisms between finite-dimensional real charted spaces preserve
  interior points, boundary points, and `BoundarylessManifold` without any regularity or explicit
  dimension-equality hypothesis (`Topology.IsOpenEmbedding.isInteriorPoint_iff`,
  `ModelWithCorners.image_interior_of_homeomorph`, `Homeomorph.image_boundary`).
* Finally, we compute the interior and frontier of `range (TauCeti.modelWithCornersHalfSpace E)` and
  specialize topological interior and boundary detection to both `modelWithCornersHalfSpace E` and
  `𝓡∂ d`.

This removes the `k ≠ 0` hypothesis required in `TauCeti.Geometry.Manifold.Boundary.Basic` when the
model is real and finite-dimensional, and generalizes the ambient-subspace boundary invariance of
`TauCeti.Geometry.Manifold.Boundary.Invariance` to arbitrary abstract charted spaces without
requiring an explicit dimension-equality hypothesis.

## References

* L. E. J. Brouwer, *Beweis der Invarianz des n-dimensionalen Gebiets*, Math. Ann. 71 (1912),
  305–313.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2B.3.
-/

public section

open Function Module Set Topology
open scoped Manifold

namespace ModelWithCorners

section ModelInvariance

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']

/-- An open partial homeomorphism with nonempty source between real model spaces with corners, the
second finite-dimensional, forces `finrank ℝ E ≤ finrank ℝ E'`. Because `interior (range I)` is
dense in `range I`, the source meets the interior of the model and embeds openly into `E` and
topologically into `E'`. -/
theorem finrank_le_of_openPartialHomeomorph (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') (φ : OpenPartialHomeomorph H H') {z : H}
    (hz : z ∈ φ.source) : finrank ℝ E ≤ finrank ℝ E' := by
  have hV : IsOpen (I.symm ⁻¹' φ.source) := φ.open_source.preimage I.continuous_symm
  have hzV : I z ∈ I.symm ⁻¹' φ.source := by simpa only [mem_preimage, I.left_inv] using hz
  have hzcl : I z ∈ closure (interior (range I)) :=
    I.range_eq_closure_interior ▸ mem_range_self z
  obtain ⟨y, hyV, hyInt⟩ := mem_closure_iff.mp hzcl _ hV hzV
  set U : Set E := I.symm ⁻¹' φ.source ∩ interior (range I)
  have hU : IsOpen U := hV.inter isOpen_interior
  have : Nonempty U := ⟨⟨y, hyV, hyInt⟩⟩
  let α : U → φ.source := fun u => ⟨I.symm u.1, u.2.1⟩
  have hα : IsEmbedding α := .of_comp
    ((I.continuous_symm.comp continuous_subtype_val).subtype_mk _)
    (I.continuous.comp continuous_subtype_val)
    (by
      convert IsEmbedding.subtypeVal using 1
      ext u
      exact I.right_inv (interior_subset u.2.2))
  exact hU.isOpenEmbedding_subtypeVal.finrank_le_of_isEmbedding
    (I'.isClosedEmbedding.isEmbedding.comp (φ.isOpenEmbedding_restrict.isEmbedding.comp hα))

variable [FiniteDimensional ℝ E]

/-- An open partial homeomorphism with nonempty source between finite-dimensional real model spaces
with corners forces the two model vector spaces to have the same dimension. -/
theorem finrank_eq_of_openPartialHomeomorph (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') (φ : OpenPartialHomeomorph H H') {z : H}
    (hz : z ∈ φ.source) : finrank ℝ E = finrank ℝ E' :=
  (I.finrank_le_of_openPartialHomeomorph I' φ hz).antisymm
    (I'.finrank_le_of_openPartialHomeomorph I φ.symm (φ.map_source hz))

/-- **Topological invariance of model interior.** An open partial homeomorphism between
finite-dimensional real models with corners sends points in the interior of `range I` to points in
the interior of `range I'`. -/
theorem mem_interior_range_of_openPartialHomeomorph (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') (φ : OpenPartialHomeomorph H H') {z : H}
    (hz : z ∈ φ.source) (hiz : I z ∈ interior (range I)) :
    I' (φ z) ∈ interior (range I') := by
  have hdim : finrank ℝ E = finrank ℝ E' := I.finrank_eq_of_openPartialHomeomorph I' φ hz
  set U : Set E := I.symm ⁻¹' φ.source ∩ interior (range I)
  have hU : IsOpen U := (φ.open_source.preimage I.continuous_symm).inter isOpen_interior
  let f : E → E' := I' ∘ φ ∘ I.symm
  have hf : ContinuousOn f U :=
    I'.continuous.comp_continuousOn
      (φ.continuousOn.comp I.continuous_symm.continuousOn fun _ hu => hu.1)
  have hinj : InjOn f U := fun u hu v hv huv => by
    have hφuv : I.symm u = I.symm v := φ.injOn hu.1 hv.1 (I'.injective huv)
    rw [← I.right_inv (interior_subset hu.2), ← I.right_inv (interior_subset hv.2), hφuv]
  refine interior_maximal ?_ (hU.image_of_continuousOn_of_injOn hf hinj hdim)
    ⟨I z, ⟨by simpa only [mem_preimage, I.left_inv] using hz, hiz⟩, by simp [f]⟩
  rintro _ ⟨u, -, rfl⟩
  exact mem_range_self _

/-- An open partial homeomorphism between finite-dimensional real models with corners preserves and
reflects membership in the interior of the model range. -/
theorem mem_interior_range_iff_of_openPartialHomeomorph (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') (φ : OpenPartialHomeomorph H H') {z : H}
    (hz : z ∈ φ.source) :
    I z ∈ interior (range I) ↔ I' (φ z) ∈ interior (range I') :=
  ⟨I.mem_interior_range_of_openPartialHomeomorph I' φ hz, fun h => by
    simpa only [φ.left_inv hz] using
      I'.mem_interior_range_of_openPartialHomeomorph I φ.symm (φ.map_source hz) h⟩

/-- An open partial homeomorphism between finite-dimensional real models with corners preserves and
reflects membership in the frontier of the model range. -/
theorem mem_frontier_range_iff_of_openPartialHomeomorph (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') (φ : OpenPartialHomeomorph H H') {z : H}
    (hz : z ∈ φ.source) :
    I z ∈ frontier (range I) ↔ I' (φ z) ∈ frontier (range I') := by
  rw [I.isClosed_range.frontier_eq, I'.isClosed_range.frontier_eq, mem_sdiff, mem_sdiff,
    and_iff_right (mem_range_self z), and_iff_right (mem_range_self (φ z)),
    I.mem_interior_range_iff_of_openPartialHomeomorph I' φ hz]

end ModelInvariance

section ChartIndependence

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- **Topological chart-independence of interior points.** On a charted space over a
finite-dimensional real model with corners, any open partial homeomorphism into the model detects
whether a point of its source is an intrinsic interior point; the map need not belong to the atlas
and no differentiability assumption on `M` is needed. -/
theorem isInteriorPoint_iff_mem_interior_range_of_finiteDimensional
    (e : OpenPartialHomeomorph M H) {x : M} (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  let φ := (chartAt H x).symm.trans e
  have hxφ : chartAt H x x ∈ φ.source := by
    simp [φ, mem_chart_target H x, (chartAt H x).left_inv (mem_chart_source H x), hx]
  have h := I.mem_interior_range_iff_of_openPartialHomeomorph I φ hxφ
  simpa only [ModelWithCorners.IsInteriorPoint, φ, OpenPartialHomeomorph.trans_apply,
    (chartAt H x).left_inv (mem_chart_source H x), mfld_simps] using h

/-- On a charted space over a finite-dimensional real model with corners, a point of the source of
any open partial homeomorphism `e : OpenPartialHomeomorph M H` is an interior point of `M` iff
`e.extend I` sends it into the interior of `(e.extend I).target`. -/
theorem isInteriorPoint_iff_of_openPartialHomeomorph
    (e : OpenPartialHomeomorph M H) {x : M} (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [I.isInteriorPoint_iff_mem_interior_range_of_finiteDimensional e hx]
  refine ⟨e.mem_interior_extend_target (e.map_source hx), fun h => ?_⟩
  simpa only [mfld_simps] using e.interior_extend_target_subset_interior_range h

/-- **Topological chart-independence of boundary points.** On a charted space over a
finite-dimensional real model with corners, any open partial homeomorphism into the model detects
whether a point of its source is an intrinsic boundary point. -/
theorem isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional
    (e : OpenPartialHomeomorph M H) {x : M} (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint,
    I.isInteriorPoint_iff_mem_interior_range_of_finiteDimensional e hx,
    I.isClosed_range.frontier_eq, mem_sdiff, and_iff_right (mem_range_self (e x))]

/-- On a charted space over a finite-dimensional real model with corners, a point of the source of
any open partial homeomorphism `e : OpenPartialHomeomorph M H` is a boundary point of `M` iff
`e.extend I` sends it into the frontier of `(e.extend I).target`. -/
theorem isBoundaryPoint_iff_of_openPartialHomeomorph
    (e : OpenPartialHomeomorph M H) {x : M} (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ e.extend I x ∈ frontier (e.extend I).target := by
  rw [← not_iff_not, ← I.isInteriorPoint_iff_not_isBoundaryPoint,
    I.isInteriorPoint_iff_of_openPartialHomeomorph e hx, mem_interior_iff_notMem_frontier]
  exact (e.extend I).mapsTo (e.extend_source (I := I) ▸ hx)

/-- The intrinsic interior of any charted space over a finite-dimensional real model with corners is
open. -/
theorem isOpen_interior_of_finiteDimensional : IsOpen (I.interior M) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx =>
    ⟨_, ?_, isOpen_extChartAt_preimage (I := I) x isOpen_interior,
      mem_chart_source H x, I.isInteriorPoint_iff.1 hx⟩
  exact fun y hy =>
    (I.isInteriorPoint_iff_of_openPartialHomeomorph (chartAt H x) hy.1).2 hy.2

/-- The intrinsic boundary of any charted space over a finite-dimensional real model with corners is
closed. -/
theorem isClosed_boundary_of_finiteDimensional : IsClosed (I.boundary M) := by
  rw [← I.compl_interior, isClosed_compl_iff]
  exact I.isOpen_interior_of_finiteDimensional

end ChartIndependence

end ModelWithCorners

/-! ### Preservation of interior and boundary under open embeddings and homeomorphisms -/

section Morphisms

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

namespace Topology.IsOpenEmbedding

/-- An open embedding from a nonempty charted space into another forces their finite-dimensional
real model vector spaces to have the same dimension. -/
theorem finrank_eq_of_chartedSpace [Nonempty M] {f : M → N} (hf : IsOpenEmbedding f)
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H') :
    finrank ℝ E = finrank ℝ E' := by
  obtain ⟨x⟩ := ‹Nonempty M›
  let φ := (chartAt H x).symm.trans ((hf.toOpenPartialHomeomorph f).trans (chartAt H' (f x)))
  have hxφ : chartAt H x x ∈ φ.source := by
    simp [φ, mem_chart_target H x, (chartAt H x).left_inv (mem_chart_source H x),
      mem_chart_source H' (f x)]
  exact I.finrank_eq_of_openPartialHomeomorph I' φ hxφ

/-- An open embedding between charted spaces over finite-dimensional real models with corners
preserves and reflects intrinsic interior points. -/
theorem isInteriorPoint_iff {f : M → N} (hf : IsOpenEmbedding f) {x : M} :
    I.IsInteriorPoint x ↔ I'.IsInteriorPoint (f x) := by
  have : Nonempty M := ⟨x⟩
  let φ := (chartAt H x).symm.trans ((hf.toOpenPartialHomeomorph f).trans (chartAt H' (f x)))
  have hxφ : chartAt H x x ∈ φ.source := by
    simp [φ, mem_chart_target H x, (chartAt H x).left_inv (mem_chart_source H x),
      mem_chart_source H' (f x)]
  have h := I.mem_interior_range_iff_of_openPartialHomeomorph I' φ hxφ
  simpa only [ModelWithCorners.IsInteriorPoint, φ, OpenPartialHomeomorph.trans_apply,
    (chartAt H x).left_inv (mem_chart_source H x), IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    mfld_simps] using h

/-- An open embedding between charted spaces over finite-dimensional real models with corners
preserves and reflects intrinsic boundary points. -/
theorem isBoundaryPoint_iff {f : M → N} (hf : IsOpenEmbedding f) {x : M} :
    I.IsBoundaryPoint x ↔ I'.IsBoundaryPoint (f x) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint, I'.isBoundaryPoint_iff_not_isInteriorPoint,
    hf.isInteriorPoint_iff (I := I) (I' := I')]

/-- A charted space admitting an open embedding into a boundaryless finite-dimensional real charted
space is itself boundaryless. -/
theorem boundarylessManifold {f : M → N} (hf : IsOpenEmbedding f)
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H') [BoundarylessManifold I' N] :
    BoundarylessManifold I M where
  isInteriorPoint' _ := (hf.isInteriorPoint_iff (I := I) (I' := I')).mpr
    BoundarylessManifold.isInteriorPoint

end Topology.IsOpenEmbedding

namespace ModelWithCorners

/-- Pulling back the intrinsic interior along an open embedding gives the intrinsic interior of the
source. -/
theorem preimage_interior_of_isOpenEmbedding (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') {f : M → N} (hf : IsOpenEmbedding f) :
    f ⁻¹' I'.interior N = I.interior M :=
  ext fun _ => (hf.isInteriorPoint_iff (I := I) (I' := I')).symm

/-- Pulling back the intrinsic boundary along an open embedding gives the intrinsic boundary of the
source. -/
theorem preimage_boundary_of_isOpenEmbedding (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') {f : M → N} (hf : IsOpenEmbedding f) :
    f ⁻¹' I'.boundary N = I.boundary M :=
  ext fun _ => (hf.isBoundaryPoint_iff (I := I) (I' := I')).symm

/-- A homeomorphism maps the intrinsic interior of the source onto the intrinsic interior of the
target. -/
theorem image_interior_of_homeomorph (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') (Φ : M ≃ₜ N) :
    Φ '' I.interior M = I'.interior N :=
  (Φ.toEquiv.image_eq_preimage_symm _).trans
    (I'.preimage_interior_of_isOpenEmbedding I Φ.symm.isOpenEmbedding)

/-- A homeomorphism maps the intrinsic boundary of the source onto the intrinsic boundary of the
target. -/
theorem image_boundary_of_homeomorph (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') (Φ : M ≃ₜ N) :
    Φ '' I.boundary M = I'.boundary N :=
  (Φ.toEquiv.image_eq_preimage_symm _).trans
    (I'.preimage_boundary_of_isOpenEmbedding I Φ.symm.isOpenEmbedding)

end ModelWithCorners

namespace Homeomorph

/-- A homeomorphism between charted spaces over finite-dimensional real models with corners
preserves and reflects intrinsic interior points. -/
theorem isInteriorPoint_iff (Φ : M ≃ₜ N) {x : M} :
    I.IsInteriorPoint x ↔ I'.IsInteriorPoint (Φ x) :=
  Φ.isOpenEmbedding.isInteriorPoint_iff

/-- A homeomorphism between charted spaces over finite-dimensional real models with corners
preserves and reflects intrinsic boundary points. -/
theorem isBoundaryPoint_iff (Φ : M ≃ₜ N) {x : M} :
    I.IsBoundaryPoint x ↔ I'.IsBoundaryPoint (Φ x) :=
  Φ.isOpenEmbedding.isBoundaryPoint_iff

/-- A homeomorphism pulls the intrinsic boundary of the target back to the intrinsic boundary of the
source. -/
theorem preimage_boundary (Φ : M ≃ₜ N) (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') : Φ ⁻¹' I'.boundary N = I.boundary M :=
  I.preimage_boundary_of_isOpenEmbedding I' Φ.isOpenEmbedding

/-- A homeomorphism maps the intrinsic boundary of the source onto the intrinsic boundary of the
target. -/
theorem image_boundary (Φ : M ≃ₜ N) (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') : Φ '' I.boundary M = I'.boundary N :=
  I.image_boundary_of_homeomorph I' Φ

/-- Being boundaryless is transported along a homeomorphism between finite-dimensional real charted
spaces. -/
theorem boundarylessManifold (Φ : M ≃ₜ N) (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') [BoundarylessManifold I M] :
    BoundarylessManifold I' N :=
  Φ.symm.isOpenEmbedding.boundarylessManifold I' I

/-- Homeomorphic finite-dimensional real charted spaces are simultaneously boundaryless. -/
theorem boundarylessManifold_iff (Φ : M ≃ₜ N) (I : ModelWithCorners ℝ E H)
    (I' : ModelWithCorners ℝ E' H') :
    BoundarylessManifold I M ↔ BoundarylessManifold I' N :=
  ⟨fun _ => Φ.boundarylessManifold I I', fun _ => Φ.symm.boundarylessManifold I' I⟩

end Homeomorph

end Morphisms

/-! ### Half-space models -/

namespace TauCeti

section HalfSpaceModel

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The interior of the range of `TauCeti.modelWithCornersHalfSpace E` is the open half-space of
points with strictly positive height. -/
theorem interior_range_modelWithCornersHalfSpace :
    interior (range (modelWithCornersHalfSpace E)) = {q : E × ℝ | 0 < q.2} := by
  rw [range_modelWithCornersHalfSpace]
  apply Subset.antisymm
  · intro q hq
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
    have hmem : (q.1, q.2 - ε / 2) ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
      have : |q.2 - ε / 2 - q.2| = ε / 2 := by
        rw [sub_right_comm, sub_self, zero_sub, abs_neg, abs_of_pos (half_pos hε)]
      rw [this, max_eq_right (half_pos hε).le]
      exact half_lt_self hε
    have hle : 0 ≤ q.2 - ε / 2 := by simpa only [mem_ofPred_eq] using hball hmem
    rw [mem_ofPred_eq]
    linarith
  · exact interior_maximal (fun _ h => by
      rw [mem_ofPred_eq] at h ⊢
      exact le_of_lt h) (isOpen_lt continuous_const continuous_snd)

/-- The frontier of the range of `TauCeti.modelWithCornersHalfSpace E` is the hyperplane of height
zero. -/
theorem frontier_range_modelWithCornersHalfSpace :
    frontier (range (modelWithCornersHalfSpace E)) = {q : E × ℝ | q.2 = 0} := by
  rw [(modelWithCornersHalfSpace E).isClosed_range.frontier_eq,
    interior_range_modelWithCornersHalfSpace, range_modelWithCornersHalfSpace]
  ext q
  simp only [mem_sdiff, mem_ofPred_eq, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- Viewed as a charted space over itself, the intrinsic interior of `{q : E × ℝ | 0 ≤ q.2}` is the
open half-space of strictly positive height. -/
@[simp]
theorem interior_modelWithCornersHalfSpace :
    (modelWithCornersHalfSpace E).interior {q : E × ℝ | 0 ≤ q.2} = {q | 0 < q.1.2} := by
  ext q
  rw [ModelWithCorners.interior, mem_ofPred_eq, ModelWithCorners.IsInteriorPoint,
    extChartAt_self_apply, interior_range_modelWithCornersHalfSpace,
    modelWithCornersHalfSpace_apply, mem_ofPred_eq, mem_ofPred_eq]

/-- Viewed as a charted space over itself, the intrinsic boundary of `{q : E × ℝ | 0 ≤ q.2}` is the
hyperplane of height zero. -/
@[simp]
theorem boundary_modelWithCornersHalfSpace :
    (modelWithCornersHalfSpace E).boundary {q : E × ℝ | 0 ≤ q.2} = {q | q.1.2 = 0} := by
  ext q
  rw [ModelWithCorners.boundary, mem_ofPred_eq, ModelWithCorners.IsBoundaryPoint,
    extChartAt_self_apply, frontier_range_modelWithCornersHalfSpace,
    modelWithCornersHalfSpace_apply, mem_ofPred_eq, mem_ofPred_eq]

end HalfSpaceModel

section HalfSpaceDetection

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace {q : E × ℝ | 0 ≤ q.2} M]

/-- On a charted space over `TauCeti.modelWithCornersHalfSpace E`, with `E` finite-dimensional, a
point is an interior point iff any open partial homeomorphism around it gives it strictly positive
height. -/
theorem isInteriorPoint_modelWithCornersHalfSpace_iff
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) {x : M} (hx : x ∈ e.source) :
    (modelWithCornersHalfSpace E).IsInteriorPoint x ↔ 0 < (e x).1.2 := by
  rw [(modelWithCornersHalfSpace E).isInteriorPoint_iff_mem_interior_range_of_finiteDimensional e
      hx,
    interior_range_modelWithCornersHalfSpace, modelWithCornersHalfSpace_apply, mem_ofPred_eq]

/-- On a charted space over `TauCeti.modelWithCornersHalfSpace E`, with `E` finite-dimensional, a
point lies on the boundary iff any open partial homeomorphism around it gives it height zero. -/
theorem mem_boundary_modelWithCornersHalfSpace_iff
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) {x : M} (hx : x ∈ e.source) :
    x ∈ (modelWithCornersHalfSpace E).boundary M ↔ (e x).1.2 = 0 := by
  rw [ModelWithCorners.boundary, mem_ofPred_eq,
    (modelWithCornersHalfSpace E).isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional e hx,
    frontier_range_modelWithCornersHalfSpace, modelWithCornersHalfSpace_apply, mem_ofPred_eq]

/-- On a charted space over the Euclidean half-space `𝓡∂ d`, any open partial homeomorphism around a
point detects whether it is an interior point, with no differentiability assumption. -/
theorem isInteriorPoint_euclideanHalfSpace_iff {d : ℕ} [NeZero d] {N : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace d) N]
    (e : OpenPartialHomeomorph N (EuclideanHalfSpace d)) {x : N} (hx : x ∈ e.source) :
    (𝓡∂ d).IsInteriorPoint x ↔ 0 < (e x).1 0 := by
  rw [(𝓡∂ d).isInteriorPoint_iff_mem_interior_range_of_finiteDimensional e hx,
    interior_range_modelWithCornersEuclideanHalfSpace, modelWithCornersEuclideanHalfSpace_toFun]
  exact Iff.rfl

/-- On a charted space over the Euclidean half-space `𝓡∂ (n + 1)`, any open partial homeomorphism
around a point detects whether it lies on the boundary, with no differentiability assumption. -/
theorem mem_boundary_euclideanHalfSpace_iff {n : ℕ} {N : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]
    (e : OpenPartialHomeomorph N (EuclideanHalfSpace (n + 1))) {x : N} (hx : x ∈ e.source) :
    x ∈ (𝓡∂ (n + 1)).boundary N ↔ (e x).1 0 = 0 := by
  rw [ModelWithCorners.boundary, mem_ofPred_eq,
    (𝓡∂ (n + 1)).isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional e hx,
    frontier_range_modelWithCornersEuclideanHalfSpace, modelWithCornersEuclideanHalfSpace_toFun]
  exact eq_comm

end HalfSpaceDetection

end TauCeti
