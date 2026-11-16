/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import TauCeti.Geometry.Manifold.ContMDiff.Kronecker
public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom
public import TauCeti.Geometry.Manifold.VectorBundle.TensorProduct
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Smooth and holomorphic tensor-product cores

The tensor product of two finite-rank `C^n` bundle cores is `C^n`, on the existing
`FiniteRankBundleCore.tensor` carrier. Its transitions are Kronecker products of the original
transitions in the fixed coordinates `Fin (a * b) → 𝕜`, indexed by `finProdFinEquiv`.
In particular, over a complex manifold at regularity `∞`, this gives the holomorphic tensor
product without changing the underlying continuous bundle.

Tensor products of bundle maps also preserve regularity, both in chart operators and on total
spaces. The chart-operator statement needs no completeness; the total-space statement uses the
finite-dimensional criterion for recovering smooth chart operators from smooth bundle maps.
Identity and composition laws are those of the existing `tensorHom` bifunctor.

Over a complete scalar field, `tensorTotalSpaceDiffeomorph` upgrades `tensorTotalSpaceHomeomorph`
to a `C^n` diffeomorphism (and, over a complex manifold at `n = ∞`, a biholomorphism) between
`(tensor A D).core.TotalSpace` and the total space of the tensor-product vector bundle
`fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x` from
`TauCeti.Geometry.Manifold.VectorBundle.TensorProduct`.
No smoothness assumption on the base atlas or on the cores `A` and `D` is required for this
comparison: in the corresponding bundle charts, `tensorFiberEquiv` reads as the fixed continuous
linear equivalence `ProjectiveTensor.kroneckerEquiv`. Forgetting regularity via
`toHomeomorph_tensorTotalSpaceDiffeomorph` recovers `tensorTotalSpaceHomeomorph`, and
`tensorSectionEquiv` gives the induced `𝕜`-linear equivalence on bundled `C^n` sections.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle Set VectorBundleCore CategoryTheory
open scoped Bundle Manifold ContDiff Topology TensorProduct

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- Tensor products of finite-rank `C^n` cores are `C^n`. For complex scalars and `n = ∞`,
this equips the shared tensor core with its holomorphic structure. -/
instance isContMDiff_tensor (A D : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] :
    (tensor A D).core.IsContMDiff I n where
  contMDiffOn_coordChange i j := by
    simp only [VectorBundleCore.baseSet_at, localTriv_baseSet_tensor]
    exact ((A.core.contMDiffOn_coordChange (n := n) I i j).mono
      (inter_subset_inter inter_subset_left inter_subset_left)).clm_kronecker
        ((D.core.contMDiffOn_coordChange (n := n) I i j).mono
          (inter_subset_inter inter_subset_right inter_subset_right))

variable {A A' D D' : FiniteRankBundleCore 𝕜 B}

/-- Tensoring bundle maps whose chart operators are `C^n` gives `C^n` chart operators on
all tensor chart intersections. Neither regularity of the cores nor completeness is needed. -/
theorem contMDiffOn_inChartCoordinates_tensorHom (f : A ⟶ A') (g : D ⟶ D')
    (hf : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates A'.core i j x (f.fiberMap x))
      (A.core.baseSet i ∩ A'.core.baseSet j))
    (hg : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) n
      (fun x ↦ D.core.inChartCoordinates D'.core i j x (g.fiberMap x))
      (D.core.baseSet i ∩ D'.core.baseSet j)) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin (tensor A D).rank → 𝕜) →L[𝕜] (Fin (tensor A' D').rank → 𝕜)) n
      (fun x ↦ (tensor A D).core.inChartCoordinates (tensor A' D').core i j x
        ((tensorHom f g).fiberMap x))
      ((tensor A D).core.baseSet i ∩ (tensor A' D').core.baseSet j) := by
  simp only [fiberMap_tensorHom, inChartCoordinates_tensor_kronecker,
    VectorBundleCore.baseSet_at, localTriv_baseSet_tensor]
  exact ((hf i j).mono (inter_subset_inter inter_subset_left inter_subset_left)).clm_kronecker
    ((hg i j).mono (inter_subset_inter inter_subset_right inter_subset_right))

/-- Tensor products of `C^n` bundle maps between finite-rank `C^n` cores are `C^n` on total
spaces. In particular, tensor products of holomorphic bundle maps are holomorphic. -/
theorem contMDiff_totalSpaceMap_tensorHom [CompleteSpace 𝕜]
    [A.core.IsContMDiff I n] [A'.core.IsContMDiff I n]
    [D.core.IsContMDiff I n] [D'.core.IsContMDiff I n]
    (f : A ⟶ A') (g : D ⟶ D')
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      f.totalSpaceMap)
    (hg : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      g.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (tensor A D).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (tensor A' D').rank → 𝕜)) n (tensorHom f g).totalSpaceMap :=
  (tensorHom f g).contMDiff_totalSpaceMap
    (contMDiffOn_inChartCoordinates_tensorHom f g
      (f.contMDiff_totalSpaceMap_iff.mp hf) (g.contMDiff_totalSpaceMap_iff.mp hg))

section TensorProductBundle

variable [CompleteSpace 𝕜]

/-- Reading the coordinate vectors of `tensor A D` as elements of
`A.core.Fiber x ⊗[𝕜] D.core.Fiber x` via `tensorFiberEquiv` is `C^n` on total spaces. -/
theorem contMDiff_tensorFiberEquiv (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)] :
    ContMDiff (I.prod 𝓘(𝕜, Fin (tensor A D).rank → 𝕜))
      (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))) n
      (fun p : (tensor A D).core.TotalSpace ↦
        TotalSpace.mk' (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
          (E := fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x) p.proj
          (tensorFiberEquiv A D p.proj p.2)) := by
  intro p
  rw [contMDiffAt_tensorProduct_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hp : p ∈ ((tensor A D).core.localTriv p.proj).source :=
    ((tensor A D).core.mem_localTriv_source p.proj p).2 ((tensor A D).core.mem_baseSet_at p.proj)
  have hU := ((tensor A D).core.localTriv p.proj).open_source.mem_nhds hp
  have hc := Bundle.TotalSpace.contMDiffAt_trivializationAt_snd (IB := I) (n := n) p
  rw [(tensor A D).trivializationAt_core] at hc
  refine ((ProjectiveTensor.kroneckerEquiv 𝕜 A.rank D.rank).contDiff.contMDiff
    |>.contMDiffAt.comp p hc).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  exact tensorFiberEquiv_inCoordinates A D p.proj q.proj
    (((tensor A D).core.mem_localTriv_source p.proj q).1 hq) q.2

/-- Canonical `C^n` diffeomorphism (over `ℂ` at `n = ∞`, biholomorphism) between the reconstructed
total space of `tensor A D` and the total space of the tensor-product vector bundle
`fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x`, over the identity of `B` and by `tensorFiberEquiv`
on each fibre. -/
noncomputable def tensorTotalSpaceDiffeomorph (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)] :
    (tensor A D).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (tensor A D).rank → 𝕜),
      I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))⟯
      TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
        (fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x) :=
  bundleDiffeomorph (tensorFiberEquiv A D) (contMDiff_tensorFiberEquiv (I := I) (n := n) A D)

/-- `tensorTotalSpaceDiffeomorph` acts on each fibre by `tensorFiberEquiv`. -/
@[simp]
theorem tensorTotalSpaceDiffeomorph_apply (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (p : (tensor A D).core.TotalSpace) :
    tensorTotalSpaceDiffeomorph I n A D p = ⟨p.proj, tensorFiberEquiv A D p.proj p.2⟩ :=
  bundleDiffeomorph_apply _ _ p

/-- The inverse of `tensorTotalSpaceDiffeomorph` acts on each fibre by
`(tensorFiberEquiv A D p.proj).symm`. -/
@[simp]
theorem tensorTotalSpaceDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (p : TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x)) :
    (tensorTotalSpaceDiffeomorph I n A D).symm p =
      ⟨p.proj, (tensorFiberEquiv A D p.proj).symm p.2⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

/-- Forgetting `C^n` (or holomorphic) regularity on `tensorTotalSpaceDiffeomorph` recovers the
topological comparison `tensorTotalSpaceHomeomorph`. -/
@[simp]
theorem toHomeomorph_tensorTotalSpaceDiffeomorph (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)] :
    (tensorTotalSpaceDiffeomorph I n A D).toHomeomorph = tensorTotalSpaceHomeomorph A D :=
  Homeomorph.ext fun p ↦ (tensorTotalSpaceDiffeomorph_apply I n A D p).trans
    (tensorTotalSpaceHomeomorph_apply A D p).symm

/-- `tensorTotalSpaceDiffeomorph` intertwines `(tensorHom f g).totalSpaceMap` on tensor cores with
`bundleTensorMap f.fiberMap g.fiberMap` on tensor-product vector bundles. -/
theorem tensorTotalSpaceDiffeomorph_naturality (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (A'.core.Fiber x ⊗[𝕜] D'.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A'.core.Fiber x ⊗[𝕜] D'.core.Fiber x)]
    (f : A ⟶ A') (g : D ⟶ D') (p : (tensor A D).core.TotalSpace) :
    tensorTotalSpaceDiffeomorph I n A' D' ((tensorHom f g).totalSpaceMap p) =
      ⟨p.proj, bundleTensorMap (E₁ := A.core.Fiber) (E₁' := A'.core.Fiber)
        (E₂ := D.core.Fiber) (E₂' := D'.core.Fiber)
        f.fiberMap g.fiberMap p.proj (tensorTotalSpaceDiffeomorph I n A D p).2⟩ := by
  rw [tensorTotalSpaceDiffeomorph_apply, tensorTotalSpaceDiffeomorph_apply]
  rcases p with ⟨x, v⟩
  rw [CoordinateHom.totalSpaceMap_mk]
  exact congrArg (TotalSpace.mk' _ x) (tensorFiberEquiv_fiberMap_tensorHom f g x v)

/-- Canonical `𝕜`-linear equivalence between bundled `C^n` sections of `tensor A D` and bundled
`C^n` sections of the tensor-product vector bundle `fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x`. -/
noncomputable def tensorSectionEquiv (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)] :
    Cₛ^n⟮I; Fin (tensor A D).rank → 𝕜, (tensor A D).core.Fiber⟯ ≃ₗ[𝕜]
      Cₛ^n⟮I; ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜),
        fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x⟯ :=
  let Φ := tensorTotalSpaceDiffeomorph I n A D
  { toFun s := ⟨fun x ↦ tensorFiberEquiv A D x (s x),
      (Φ.contMDiff.comp s.contMDiff).congr fun x ↦ by simp [Φ]⟩
    invFun t := ⟨fun x ↦ (tensorFiberEquiv A D x).symm (t x),
      (Φ.symm.contMDiff.comp t.contMDiff).congr fun x ↦ by simp [Φ]⟩
    left_inv _ := by ext x; simp
    right_inv _ := by ext x; simp
    map_add' _ _ := by ext x; simp
    map_smul' _ _ := by ext x; simp }

/-- `tensorSectionEquiv` acts pointwise on bundled `C^n` sections by `tensorFiberEquiv`. -/
@[simp]
theorem tensorSectionEquiv_apply (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (s : Cₛ^n⟮I; Fin (tensor A D).rank → 𝕜, (tensor A D).core.Fiber⟯) (x : B) :
    tensorSectionEquiv I n A D s x = tensorFiberEquiv A D x (s x) := (rfl)

/-- The inverse of `tensorSectionEquiv` acts pointwise on bundled `C^n` sections by
`(tensorFiberEquiv A D x).symm`. -/
@[simp]
theorem tensorSectionEquiv_symm_apply (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (t : Cₛ^n⟮I; ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜),
      fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x⟯) (x : B) :
    (tensorSectionEquiv I n A D).symm t x = (tensorFiberEquiv A D x).symm (t x) := (rfl)

/-- Under `(tensorSectionEquiv I n A D).symm`, the pure tensor `ContMDiffSection.tmul s t` of two
`C^n` sections evaluates at `finProdFinEquiv (i, j)` to the pointwise product `s x i * t x j`. -/
@[simp]
theorem tensorSectionEquiv_symm_tmul_apply (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (s : Cₛ^n⟮I; Fin A.rank → 𝕜, A.core.Fiber⟯)
    (t : Cₛ^n⟮I; Fin D.rank → 𝕜, D.core.Fiber⟯)
    (x : B) (i : Fin A.rank) (j : Fin D.rank) :
    (tensorSectionEquiv I n A D).symm (ContMDiffSection.tmul s t) x (finProdFinEquiv (i, j)) =
      s x i * t x j := by
  simp

end TensorProductBundle

end TauCeti.FiniteRankBundleCore
