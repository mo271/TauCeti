/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Tensor

/-!
# Smooth coherence equivalences for tensor products of bundle cores

The associator, unitors and symmetry of finite-rank bundle cores are smooth bundle
equivalences. Their underlying maps are exactly those of the existing symmetric monoidal
category, not new identifications of its objects. In particular the naturality, pentagon,
triangle and symmetry laws of that category remain the laws of these smooth comparisons.
Over a complex manifold at regularity `∞` these are biholomorphic bundle equivalences.

The comparisons act in each fibre by the corresponding Kronecker coordinate equivalence.
The tensor product retains the shared core carrier and the tensor unit is the trivial line.
No completeness of the scalar field or manifold structure on the base is required for the core
coherence equivalences themselves. Over a complete scalar field, `tensorTotalSpaceDiffeomorph`
intertwines `tensorBraidingDiffeomorph` and `tensorAssociatorDiffeomorph` with the tensor-product
bundle diffeomorphisms `bundleTensorCommDiffeomorph` and `bundleTensorAssocDiffeomorph`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle VectorBundleCore CategoryTheory ContinuousLinearEquiv ContinuousLinearMap
open scoped Manifold ContDiff MonoidalCategory TensorProduct

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  (A D C : FiniteRankBundleCore 𝕜 B)
  [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [C.core.IsContMDiff I n]

-- The monoidal coherence isomorphisms are definitionally `constIso` with the data below;
-- using the same data lets their total-space maps be identified by the generic coe lemmas.

/-- The tensor associator as a smooth bundle equivalence, over the identity on the base. -/
noncomputable def tensorAssociatorDiffeomorph :
    ((A ⊗ D) ⊗ C).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin ((A ⊗ D) ⊗ C).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (A ⊗ (D ⊗ C)).rank → 𝕜)⟯ (A ⊗ (D ⊗ C)).core.TotalSpace :=
  constIsoDiffeomorph (A := tensor (tensor A D) C) (D := tensor A (tensor D C))
    (fun _ ↦ Set.inter_assoc _ _ _) (kroneckerAssoc 𝕜 A.rank D.rank C.rank)
    fun _ _ _ _ _ ↦ kroneckerAssoc_comp_kronecker _ _ _

/-- The smooth associator has the same map as the monoidal associator. -/
@[simp]
theorem coe_tensorAssociatorDiffeomorph :
    ⇑(tensorAssociatorDiffeomorph (I := I) (n := n) A D C) = (α_ A D C).hom.totalSpaceMap :=
  coe_constIsoDiffeomorph _ _ _

/-- The inverse smooth associator has the same map as the inverse monoidal associator. -/
@[simp]
theorem coe_tensorAssociatorDiffeomorph_symm :
    ⇑(tensorAssociatorDiffeomorph (I := I) (n := n) A D C).symm =
      (α_ A D C).inv.totalSpaceMap :=
  coe_constIsoDiffeomorph_symm _ _ _

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The left tensor unitor as a smooth bundle equivalence. -/
noncomputable def tensorLeftUnitorDiffeomorph :
    ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace :=
  constIsoDiffeomorph (A := tensor (trivial 𝕜 B 1) A) (D := A)
    (fun _ ↦ Set.univ_inter _) (kroneckerLid 𝕜 A.rank)
    fun _ _ _ _ _ ↦ kroneckerLid_comp_kronecker _

/-- The smooth left unitor retains the monoidal left unitor. -/
@[simp]
theorem coe_tensorLeftUnitorDiffeomorph :
    ⇑(tensorLeftUnitorDiffeomorph (I := I) (n := n) A) = (λ_ A).hom.totalSpaceMap :=
  coe_constIsoDiffeomorph _ _ _

/-- The inverse smooth left unitor retains the inverse monoidal left unitor. -/
@[simp]
theorem coe_tensorLeftUnitorDiffeomorph_symm :
    ⇑(tensorLeftUnitorDiffeomorph (I := I) (n := n) A).symm = (λ_ A).inv.totalSpaceMap :=
  coe_constIsoDiffeomorph_symm _ _ _

omit [D.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The right tensor unitor as a smooth bundle equivalence. -/
noncomputable def tensorRightUnitorDiffeomorph :
    (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace :=
  constIsoDiffeomorph (A := tensor A (trivial 𝕜 B 1)) (D := A)
    (fun _ ↦ Set.inter_univ _) (kroneckerRid 𝕜 A.rank)
    fun _ _ _ _ _ ↦ kroneckerRid_comp_kronecker _

/-- The smooth right unitor retains the monoidal right unitor. -/
@[simp]
theorem coe_tensorRightUnitorDiffeomorph :
    ⇑(tensorRightUnitorDiffeomorph (I := I) (n := n) A) = (ρ_ A).hom.totalSpaceMap :=
  coe_constIsoDiffeomorph _ _ _

/-- The inverse smooth right unitor retains the inverse monoidal right unitor. -/
@[simp]
theorem coe_tensorRightUnitorDiffeomorph_symm :
    ⇑(tensorRightUnitorDiffeomorph (I := I) (n := n) A).symm = (ρ_ A).inv.totalSpaceMap :=
  coe_constIsoDiffeomorph_symm _ _ _

omit [C.core.IsContMDiff I n] in
/-- The tensor symmetry as a smooth bundle equivalence. -/
noncomputable def tensorBraidingDiffeomorph :
    (A ⊗ D).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (A ⊗ D).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (D ⊗ A).rank → 𝕜)⟯ (D ⊗ A).core.TotalSpace :=
  constIsoDiffeomorph (A := tensor A D) (D := tensor D A)
    (fun _ ↦ Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
    fun _ _ _ _ _ ↦ kroneckerComm_comp_kronecker _ _

/-- The smooth tensor symmetry retains the monoidal braiding. -/
@[simp]
theorem coe_tensorBraidingDiffeomorph :
    ⇑(tensorBraidingDiffeomorph (I := I) (n := n) A D) = (β_ A D).hom.totalSpaceMap := by
  -- The braiding has one additional named wrapper around the constant isomorphism.
  simpa only [tensorBraidingDiffeomorph, braiding_def] using
    (coe_constIsoDiffeomorph (I := I) (n := n) (A := tensor A D) (D := tensor D A)
      (fun _ ↦ Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
      (fun _ _ _ _ _ ↦ kroneckerComm_comp_kronecker _ _))

/-- The inverse smooth tensor symmetry retains the inverse monoidal braiding. -/
@[simp]
theorem coe_tensorBraidingDiffeomorph_symm :
    ⇑(tensorBraidingDiffeomorph (I := I) (n := n) A D).symm = (β_ A D).inv.totalSpaceMap := by
  simpa only [tensorBraidingDiffeomorph, braiding_def] using
    (coe_constIsoDiffeomorph_symm (I := I) (n := n) (A := tensor A D) (D := tensor D A)
      (fun _ ↦ Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
      (fun _ _ _ _ _ ↦ kroneckerComm_comp_kronecker _ _))

section TensorProductBundle

variable [CompleteSpace 𝕜]

omit [C.core.IsContMDiff I n] in
/-- `tensorTotalSpaceDiffeomorph` intertwines the smooth monoidal braiding
`tensorBraidingDiffeomorph` with `bundleTensorCommDiffeomorph`. -/
theorem tensorTotalSpaceDiffeomorph_tensorBraidingDiffeomorph
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    (p : (A ⊗ D).core.TotalSpace) :
    tensorTotalSpaceDiffeomorph I n D A (tensorBraidingDiffeomorph (I := I) (n := n) A D p) =
      bundleTensorCommDiffeomorph I n (Fin A.rank → 𝕜) A.core.Fiber (Fin D.rank → 𝕜) D.core.Fiber
        (tensorTotalSpaceDiffeomorph I n A D p) := by
  rcases p with ⟨x, v⟩
  have hp : tensorBraidingDiffeomorph (I := I) (n := n) A D ⟨x, v⟩ =
      ⟨x, (β_ A D).hom.fiberMap x v⟩ :=
    (congrFun (coe_tensorBraidingDiffeomorph (I := I) (n := n) A D) ⟨x, v⟩).trans
      (CoordinateHom.totalSpaceMap_mk _ x v)
  rw [hp, tensorTotalSpaceDiffeomorph_apply, tensorTotalSpaceDiffeomorph_apply]
  refine Eq.trans ?_ (bundleTensorCommDiffeomorph_apply (IB := I) (n := n)
    (F₁ := Fin A.rank → 𝕜) (E₁ := A.core.Fiber) (F₂ := Fin D.rank → 𝕜) (E₂ := D.core.Fiber) _).symm
  exact congrArg (TotalSpace.mk' _ x) (tensorFiberEquiv_braiding_hom A D x v)

/-- `tensorTotalSpaceDiffeomorph` and `bundleTensorCongr` intertwine the smooth monoidal associator
`tensorAssociatorDiffeomorph` with `bundleTensorAssocDiffeomorph`. -/
theorem tensorTotalSpaceDiffeomorph_tensorAssociatorDiffeomorph
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (D.core.Fiber x ⊗[𝕜] C.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (D.core.Fiber x ⊗[𝕜] C.core.Fiber x)]
    [∀ x, TopologicalSpace ((A ⊗ D).core.Fiber x ⊗[𝕜] C.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 ((A ⊗ D).core.Fiber x ⊗[𝕜] C.core.Fiber x)]
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] (D ⊗ C).core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] (D ⊗ C).core.Fiber x)]
    [∀ x, TopologicalSpace ((A.core.Fiber x ⊗[𝕜] D.core.Fiber x) ⊗[𝕜] C.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 ((A.core.Fiber x ⊗[𝕜] D.core.Fiber x) ⊗[𝕜] C.core.Fiber x)]
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] (D.core.Fiber x ⊗[𝕜] C.core.Fiber x))]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] (D.core.Fiber x ⊗[𝕜] C.core.Fiber x))]
    (p : ((A ⊗ D) ⊗ C).core.TotalSpace) :
    (⟨p.proj, bundleTensorCongr (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber y))
        (tensorFiberEquiv D C) p.proj
        (tensorTotalSpaceDiffeomorph I n A (D ⊗ C)
          (tensorAssociatorDiffeomorph (I := I) (n := n) A D C p)).2⟩ :
        TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜)
          (ProjectiveTensor 𝕜 (Fin D.rank → 𝕜) (Fin C.rank → 𝕜)))
          (fun x ↦ A.core.Fiber x ⊗[𝕜] (D.core.Fiber x ⊗[𝕜] C.core.Fiber x))) =
      bundleTensorAssocDiffeomorph I n (Fin A.rank → 𝕜) A.core.Fiber
        (Fin D.rank → 𝕜) D.core.Fiber (Fin C.rank → 𝕜) C.core.Fiber
        ⟨p.proj, bundleTensorCongr (tensorFiberEquiv A D)
          (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (C.core.Fiber y)) p.proj
          (tensorTotalSpaceDiffeomorph I n (A ⊗ D) C p).2⟩ := by
  rcases p with ⟨x, v⟩
  let ΦL : TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin (D ⊗ C).rank → 𝕜))
      (fun y ↦ A.core.Fiber y ⊗[𝕜] (D ⊗ C).core.Fiber y) →
      TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜)
        (ProjectiveTensor 𝕜 (Fin D.rank → 𝕜) (Fin C.rank → 𝕜)))
        (fun y ↦ A.core.Fiber y ⊗[𝕜] (D.core.Fiber y ⊗[𝕜] C.core.Fiber y)) :=
    fun q ↦ ⟨x, bundleTensorCongr (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber y))
      (tensorFiberEquiv D C) x q.2⟩
  let ΦR : TotalSpace (ProjectiveTensor 𝕜 (Fin (A ⊗ D).rank → 𝕜) (Fin C.rank → 𝕜))
      (fun y ↦ (A ⊗ D).core.Fiber y ⊗[𝕜] C.core.Fiber y) →
      TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜)
        (ProjectiveTensor 𝕜 (Fin D.rank → 𝕜) (Fin C.rank → 𝕜)))
        (fun y ↦ A.core.Fiber y ⊗[𝕜] (D.core.Fiber y ⊗[𝕜] C.core.Fiber y)) :=
    fun q ↦ bundleTensorAssocDiffeomorph I n (Fin A.rank → 𝕜) A.core.Fiber
      (Fin D.rank → 𝕜) D.core.Fiber (Fin C.rank → 𝕜) C.core.Fiber
      ⟨x, bundleTensorCongr (tensorFiberEquiv A D)
        (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (C.core.Fiber y)) x q.2⟩
  have hL : tensorTotalSpaceDiffeomorph I n A (D ⊗ C)
      (tensorAssociatorDiffeomorph (I := I) (n := n) A D C ⟨x, v⟩) =
      ⟨x, tensorFiberEquiv A (D ⊗ C) x ((α_ A D C).hom.fiberMap x v)⟩ := by
    have hp : tensorAssociatorDiffeomorph (I := I) (n := n) A D C ⟨x, v⟩ =
        ⟨x, (α_ A D C).hom.fiberMap x v⟩ :=
      (congrFun (coe_tensorAssociatorDiffeomorph (I := I) (n := n) A D C) ⟨x, v⟩).trans
        (CoordinateHom.totalSpaceMap_mk _ x v)
    rw [hp, tensorTotalSpaceDiffeomorph_apply]
  have hR : tensorTotalSpaceDiffeomorph I n (A ⊗ D) C ⟨x, v⟩ =
      ⟨x, tensorFiberEquiv (A ⊗ D) C x v⟩ :=
    tensorTotalSpaceDiffeomorph_apply I n (A ⊗ D) C ⟨x, v⟩
  refine (congrArg ΦL hL).trans ?_
  refine Eq.trans ?_ (congrArg ΦR hR).symm
  refine Eq.trans ?_ (bundleTensorAssocDiffeomorph_apply (IB := I) (n := n)
    (F₁ := Fin A.rank → 𝕜) (E₁ := A.core.Fiber) (F₂ := Fin D.rank → 𝕜) (E₂ := D.core.Fiber)
    (F₃ := Fin C.rank → 𝕜) (E₃ := C.core.Fiber) _).symm
  exact congrArg (TotalSpace.mk' _ x) (tensorFiberEquiv_associator_hom A D C x v)

end TensorProductBundle

end TauCeti.FiniteRankBundleCore
