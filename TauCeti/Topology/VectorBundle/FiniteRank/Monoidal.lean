/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The symmetric monoidal category of finite-rank bundle cores

The tensor product `FiniteRankBundleCore.tensor` of point-indexed cores, with the trivial line
bundle `trivial 𝕜 B 1` as unit, makes `FiniteRankBundleCore 𝕜 B` a symmetric monoidal
category in which the tensor product is additive in each variable
(`MonoidalPreadditive`). The structure isomorphisms are actual bundle isomorphisms with a fixed
coordinate matrix on every fibre:

* the associator `(A ⊗ D) ⊗ C ≅ A ⊗ (D ⊗ C)` is `ContinuousLinearEquiv.kroneckerAssoc`;
* the unitors `𝟙 ⊗ A ≅ A` and `A ⊗ 𝟙 ≅ A` are `ContinuousLinearEquiv.kroneckerLid` and
  `ContinuousLinearEquiv.kroneckerRid`;
* the braiding `A ⊗ D ≅ D ⊗ A` is the coordinate swap `ContinuousLinearEquiv.kroneckerComm`.

Each of these coordinate isomorphisms intertwines the Kronecker products of the transition
maps, so it defines an isomorphism of cores by `FiniteRankBundleCore.constIso`. The same
intertwining relations, applied to the fibre maps of bundle morphisms, give naturality, and the
coherence laws hold fibrewise as identities between coordinate permutations.

Together with the Whitney biproducts of `TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`,
this is the structure of a symmetric monoidal preadditive category with binary biproducts, which
is what the commutative ring structure on split Grothendieck groups
(`TauCeti.SplitK0.instCommRing`) consumes: the tensor product of cores descends to the product
of classes, `[A] * [D] = [A ⊗ D]`, with the class of the trivial line bundle as unit. The base is
arbitrary, and the scalar field need not be complete.

Under `FiniteRankBundleCore.tensorFiberEquiv` and `FiniteRankBundleCore.tensorTotalSpaceHomeomorph`,
the braiding, associator, and unitors agree with the fibrewise and total-space symmetry,
associativity, and unit equivalences on tensor-product vector bundles (`bundleTensorCommEquiv`,
`bundleTensorCommHomeomorph`, `bundleTensorAssocEquiv`, `bundleTensorAssocHomeomorph`,
`TensorProduct.lid`, and `TensorProduct.rid`).

For the tensor product of vector bundles and its transition functions see Milnor–Stasheff,
*Characteristic Classes*, §3, and Atiyah, *K-Theory*, §1.2.
-/

public section

open Bundle CategoryTheory VectorBundleCore
open scoped MonoidalCategory TensorProduct

namespace TauCeti.FiniteRankBundleCore

open ContinuousLinearEquiv ContinuousLinearMap

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The tensor product of cores, with the trivial line bundle as unit. The associator and
unitors are the bundle isomorphisms with the Kronecker coherence isomorphisms as their
constant coordinate matrices. -/
instance : MonoidalCategoryStruct (FiniteRankBundleCore 𝕜 B) where
  tensorObj := tensor
  whiskerLeft A _ _ g := tensorHom (𝟙 A) g
  whiskerRight f D := tensorHom f (𝟙 D)
  tensorHom := tensorHom
  tensorUnit := trivial 𝕜 B 1
  associator A D C :=
    constIso (fun _ => Set.inter_assoc _ _ _) (kroneckerAssoc 𝕜 A.rank D.rank C.rank)
      fun _ _ _ _ _ => kroneckerAssoc_comp_kronecker _ _ _
  leftUnitor A :=
    constIso (fun _ => Set.univ_inter _) (kroneckerLid 𝕜 A.rank)
      fun _ _ _ _ _ => kroneckerLid_comp_kronecker _
  rightUnitor A :=
    constIso (fun _ => Set.inter_univ _) (kroneckerRid 𝕜 A.rank)
      fun _ _ _ _ _ => kroneckerRid_comp_kronecker _

variable {A A' D D' C : FiniteRankBundleCore 𝕜 B}

@[simp] theorem rank_tensorObj (A D : FiniteRankBundleCore 𝕜 B) :
    (A ⊗ D).rank = A.rank * D.rank := (rfl)

@[simp] theorem rank_tensorUnit : (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank = 1 := (rfl)

/-- The monoidal tensor product of bundle maps is the Kronecker product on every fibre. -/
@[simp] theorem fiberMap_tensorHom_monoidal (f : A ⟶ A') (g : D ⟶ D') (x : B) :
    (f ⊗ₘ g).fiberMap x = (f.fiberMap x).kronecker (g.fiberMap x) :=
  fiberMap_tensorHom f g x

@[simp] theorem fiberMap_whiskerLeft (A : FiniteRankBundleCore 𝕜 B) (g : D ⟶ D') (x : B) :
    (A ◁ g).fiberMap x = (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker (g.fiberMap x) := by
  rw [← fiberMap_id]
  exact fiberMap_tensorHom (𝟙 A) g x

@[simp] theorem fiberMap_whiskerRight (f : A ⟶ A') (D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (f ▷ D).fiberMap x = (f.fiberMap x).kronecker (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜)) := by
  rw [← fiberMap_id]
  exact fiberMap_tensorHom f (𝟙 D) x

@[simp] theorem fiberMap_associator_hom (A D C : FiniteRankBundleCore 𝕜 B) (x : B) :
    (α_ A D C).hom.fiberMap x = (kroneckerAssoc 𝕜 A.rank D.rank C.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_associator_inv (A D C : FiniteRankBundleCore 𝕜 B) (x : B) :
    (α_ A D C).inv.fiberMap x =
      (kroneckerAssoc 𝕜 A.rank D.rank C.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

@[simp] theorem fiberMap_leftUnitor_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (λ_ A).hom.fiberMap x = (kroneckerLid 𝕜 A.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_leftUnitor_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (λ_ A).inv.fiberMap x = (kroneckerLid 𝕜 A.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

@[simp] theorem fiberMap_rightUnitor_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (ρ_ A).hom.fiberMap x = (kroneckerRid 𝕜 A.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_rightUnitor_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (ρ_ A).inv.fiberMap x = (kroneckerRid 𝕜 A.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

/-- Finite-rank cores form a monoidal category under the tensor product. The coherence laws
hold fibrewise as the coherence laws of the Kronecker coordinate isomorphisms. -/
instance : MonoidalCategory (FiniteRankBundleCore 𝕜 B) where
  tensorHom_def f g := by
    have h := tensorHom_comp_tensorHom f (𝟙 _) (𝟙 _) g
    rw [Category.comp_id, Category.id_comp] at h
    exact h.symm
  id_tensorHom_id := id_tensorHom_id
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  whiskerLeft_id := id_tensorHom_id
  id_whiskerRight := id_tensorHom_id
  associator_naturality f g h := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_tensorHom_monoidal, fiberMap_associator_hom]
    exact kroneckerAssoc_comp_kronecker _ _ _
  leftUnitor_naturality f := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_leftUnitor_hom]
    exact kroneckerLid_comp_kronecker _
  rightUnitor_naturality f := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerRight, fiberMap_rightUnitor_hom]
    exact kroneckerRid_comp_kronecker _
  pentagon A D C E := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_hom]
    exact kroneckerAssoc_pentagon _ _ _ _
  triangle A D := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_hom, fiberMap_leftUnitor_hom, fiberMap_rightUnitor_hom]
    exact kroneckerAssoc_triangle _ _

/-- The tensor product of bundle maps is additive in each variable. -/
instance : MonoidalPreadditive (FiniteRankBundleCore 𝕜 B) where
  whiskerLeft_zero := tensorHom_zero _
  zero_whiskerRight := zero_tensorHom _
  whiskerLeft_add _ _ := tensorHom_add _ _ _
  add_whiskerRight _ _ := add_tensorHom _ _ _

/-- The braiding `A ⊗ D ≅ D ⊗ A` of cores, with the coordinate swap `kroneckerComm` as its
constant coordinate matrix. -/
def tensorComm (A D : FiniteRankBundleCore 𝕜 B) : A ⊗ D ≅ D ⊗ A :=
  constIso (fun _ => Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
    fun _ _ _ _ _ => kroneckerComm_comp_kronecker _ _

@[simp] theorem fiberMap_tensorComm_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (tensorComm A D).hom.fiberMap x = (kroneckerComm 𝕜 A.rank D.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_tensorComm_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (tensorComm A D).inv.fiberMap x = (kroneckerComm 𝕜 D.rank A.rank).toContinuousLinearMap := by
  rw [← kroneckerComm_symm]
  exact fiberMap_constIso_inv _ _ _ x

/-- The braiding `tensorComm` makes the monoidal category of finite-rank cores symmetric. -/
instance : SymmetricCategory (FiniteRankBundleCore 𝕜 B) where
  braiding := tensorComm
  braiding_naturality_right A _ _ g := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_tensorComm_hom]
    exact kroneckerComm_comp_kronecker _ _
  braiding_naturality_left f D := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_tensorComm_hom]
    exact kroneckerComm_comp_kronecker _ _
  hexagon_forward A D C := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_hom, fiberMap_tensorComm_hom]
    exact kroneckerComm_hexagon_forward _ _ _
  hexagon_reverse A D C := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_inv, fiberMap_tensorComm_hom]
    exact kroneckerComm_hexagon_reverse _ _ _
  symmetry A D := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_tensorComm_hom, fiberMap_tensorComm_hom, fiberMap_id,
      ← kroneckerComm_symm]
    exact (kroneckerComm 𝕜 A.rank D.rank).coe_symm_comp_coe

/-- The monoidal braiding is the constant isomorphism induced by the Kronecker swap. -/
theorem braiding_def (A D : FiniteRankBundleCore 𝕜 B) :
    (β_ A D) =
      constIso (fun _ => Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
        (fun _ _ _ _ _ => kroneckerComm_comp_kronecker _ _) := (rfl)

@[simp] theorem fiberMap_braiding_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (β_ A D).hom.fiberMap x = (kroneckerComm 𝕜 A.rank D.rank).toContinuousLinearMap :=
  fiberMap_tensorComm_hom A D x

@[simp] theorem fiberMap_braiding_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (β_ A D).inv.fiberMap x = (kroneckerComm 𝕜 D.rank A.rank).toContinuousLinearMap :=
  fiberMap_tensorComm_inv A D x

section TensorProductBundle

/-- `tensorFiberEquiv` intertwines the monoidal braiding `(β_ A D).hom` with
`bundleTensorCommEquiv`. -/
theorem tensorFiberEquiv_braiding_hom (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    (x : B) (v : (A ⊗ D).core.Fiber x) :
    tensorFiberEquiv D A x ((β_ A D).hom.fiberMap x v) =
      bundleTensorCommEquiv x (tensorFiberEquiv A D x v) := by
  refine (tensorFiberEquiv_apply D A x _).trans ?_
  refine (congrArg (kroneckerTensorEquiv 𝕜 D.rank A.rank)
    (DFunLike.congr_fun (fiberMap_braiding_hom A D x) v)).trans ?_
  refine (kroneckerTensorEquiv_kroneckerComm v).trans ?_
  refine Eq.trans ?_
    (congrArg (bundleTensorCommEquiv x) (tensorFiberEquiv_apply A D x v)).symm
  suffices ∀ t : A.core.Fiber x ⊗[𝕜] D.core.Fiber x,
      _root_.TensorProduct.comm 𝕜 (A.core.Fiber x) (D.core.Fiber x) t =
        bundleTensorCommEquiv x t from
    this (kroneckerTensorEquiv 𝕜 A.rank D.rank v)
  intro t
  induction t using _root_.TensorProduct.inductionOn with
  | tmul u w =>
      exact (bundleTensorCommEquiv_tmul (E₁ := A.core.Fiber) (E₂ := D.core.Fiber) x u w).symm
  | add p q hp hq =>
      rw [_root_.map_add, _root_.map_add, hp, hq]

/-- `tensorFiberEquiv` intertwines the inverse monoidal braiding `(β_ A D).inv` with
`(bundleTensorCommEquiv x).symm`. -/
theorem tensorFiberEquiv_braiding_inv (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    (x : B) (v : (D ⊗ A).core.Fiber x) :
    tensorFiberEquiv A D x ((β_ A D).inv.fiberMap x v) =
      (bundleTensorCommEquiv x).symm (tensorFiberEquiv D A x v) := by
  have hv : ((β_ A D).inv.fiberMap x v : (A ⊗ D).core.Fiber x) = (β_ D A).hom.fiberMap x v :=
    (DFunLike.congr_fun (fiberMap_braiding_inv A D x) v).trans
      (DFunLike.congr_fun (fiberMap_braiding_hom D A x) v).symm
  rw [bundleTensorCommEquiv_symm, ← tensorFiberEquiv_braiding_hom D A x v]
  exact congrArg (tensorFiberEquiv A D x) hv

/-- `tensorTotalSpaceHomeomorph` intertwines `(β_ A D).hom.totalSpaceMap` with
`bundleTensorCommHomeomorph`. -/
theorem tensorTotalSpaceHomeomorph_braiding_hom [CompleteSpace 𝕜]
    (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (D.core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    (p : (A ⊗ D).core.TotalSpace) :
    tensorTotalSpaceHomeomorph D A ((β_ A D).hom.totalSpaceMap p) =
      bundleTensorCommHomeomorph (Fin A.rank → 𝕜) A.core.Fiber (Fin D.rank → 𝕜) D.core.Fiber
        (tensorTotalSpaceHomeomorph A D p) := by
  rcases p with ⟨x, v⟩
  rw [CoordinateHom.totalSpaceMap_mk, tensorTotalSpaceHomeomorph_apply,
    tensorTotalSpaceHomeomorph_apply, bundleTensorCommHomeomorph_apply]
  exact congrArg (TotalSpace.mk' _ x) (tensorFiberEquiv_braiding_hom A D x v)

/-- Iterated `tensorFiberEquiv` intertwines the monoidal associator `(α_ A D C).hom` with
`bundleTensorAssocEquiv`. -/
theorem tensorFiberEquiv_associator_hom (A D C : FiniteRankBundleCore 𝕜 B)
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
    (x : B) (v : ((A ⊗ D) ⊗ C).core.Fiber x) :
    bundleTensorCongr (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber y))
        (tensorFiberEquiv D C) x
        (tensorFiberEquiv A (D ⊗ C) x ((α_ A D C).hom.fiberMap x v)) =
      bundleTensorAssocEquiv x
        (bundleTensorCongr (tensorFiberEquiv A D)
          (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (C.core.Fiber y)) x
          (tensorFiberEquiv (A ⊗ D) C x v)) := by
  let lhs : (Fin ((A ⊗ D) ⊗ C).rank → 𝕜) →ₗ[𝕜]
      A.core.Fiber x ⊗[𝕜] (D.core.Fiber x ⊗[𝕜] C.core.Fiber x) :=
    ((bundleTensorCongr (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber y))
      (tensorFiberEquiv D C) x).toLinearMap.comp
      (tensorFiberEquiv A (D ⊗ C) x).toLinearMap).comp
      ((α_ A D C).hom.fiberMap x).toLinearMap
  let rhs : (Fin ((A ⊗ D) ⊗ C).rank → 𝕜) →ₗ[𝕜]
      A.core.Fiber x ⊗[𝕜] (D.core.Fiber x ⊗[𝕜] C.core.Fiber x) :=
    ((bundleTensorAssocEquiv x).toLinearMap.comp
      (bundleTensorCongr (tensorFiberEquiv A D)
        (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (C.core.Fiber y)) x).toLinearMap).comp
      (tensorFiberEquiv (A ⊗ D) C x).toLinearMap
  have heq : lhs = rhs := LinearMap.pi_ext fun k c ↦ by
    obtain ⟨⟨ij, l⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
    have hL : lhs (Pi.single (finProdFinEquiv (finProdFinEquiv (i, j), l)) c) =
        c • ((Pi.single i 1 : A.core.Fiber x) ⊗ₜ[𝕜]
          ((Pi.single j 1 : D.core.Fiber x) ⊗ₜ[𝕜] (Pi.single l 1 : C.core.Fiber x))) :=
      (congrArg (bundleTensorCongr (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber y))
          (tensorFiberEquiv D C) x)
        ((congrArg (tensorFiberEquiv A (D ⊗ C) x)
          ((DFunLike.congr_fun (fiberMap_associator_hom A D C x) _).trans
            (kroneckerAssoc_single i j l c))).trans
          (tensorFiberEquiv_single A (D ⊗ C) x i (finProdFinEquiv (j, l)) c))).trans
        ((ContinuousLinearEquiv.map_smul _ c _).trans
          (congrArg (c • ·) ((bundleTensorCongr_tmul _ _ x _ _).trans
            (congrArg ((Pi.single i 1 : A.core.Fiber x) ⊗ₜ[𝕜] ·)
              ((tensorFiberEquiv_single D C x j l 1).trans (one_smul 𝕜 _))))))
    have hR : rhs (Pi.single (finProdFinEquiv (finProdFinEquiv (i, j), l)) c) =
        c • ((Pi.single i 1 : A.core.Fiber x) ⊗ₜ[𝕜]
          ((Pi.single j 1 : D.core.Fiber x) ⊗ₜ[𝕜] (Pi.single l 1 : C.core.Fiber x))) :=
      (congrArg (bundleTensorAssocEquiv x)
        ((congrArg (bundleTensorCongr (tensorFiberEquiv A D)
            (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (C.core.Fiber y)) x)
          (tensorFiberEquiv_single (A ⊗ D) C x (finProdFinEquiv (i, j)) l c)).trans
          ((ContinuousLinearEquiv.map_smul _ c _).trans
            (congrArg (c • ·) ((bundleTensorCongr_tmul _ _ x _ _).trans
              (congrArg (· ⊗ₜ[𝕜] (Pi.single l 1 : C.core.Fiber x))
                ((tensorFiberEquiv_single A D x i j 1).trans (one_smul 𝕜 _)))))))).trans
        ((ContinuousLinearEquiv.map_smul _ c _).trans
          (congrArg (c • ·) (bundleTensorAssocEquiv_tmul x _ _ _)))
    exact hL.trans hR.symm
  exact LinearMap.congr_fun heq v

/-- `tensorTotalSpaceHomeomorph` and `bundleTensorCongr` intertwine
`(α_ A D C).hom.totalSpaceMap` with `bundleTensorAssocHomeomorph`. -/
theorem tensorTotalSpaceHomeomorph_associator_hom [CompleteSpace 𝕜]
    (A D C : FiniteRankBundleCore 𝕜 B)
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
        (tensorTotalSpaceHomeomorph A (D ⊗ C) ((α_ A D C).hom.totalSpaceMap p)).2⟩ :
        TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜)
          (ProjectiveTensor 𝕜 (Fin D.rank → 𝕜) (Fin C.rank → 𝕜)))
          (fun x ↦ A.core.Fiber x ⊗[𝕜] (D.core.Fiber x ⊗[𝕜] C.core.Fiber x))) =
      bundleTensorAssocHomeomorph (Fin A.rank → 𝕜) A.core.Fiber
        (Fin D.rank → 𝕜) D.core.Fiber (Fin C.rank → 𝕜) C.core.Fiber
        ⟨p.proj, bundleTensorCongr (tensorFiberEquiv A D)
          (fun y ↦ ContinuousLinearEquiv.refl 𝕜 (C.core.Fiber y)) p.proj
          (tensorTotalSpaceHomeomorph (A ⊗ D) C p).2⟩ := by
  rcases p with ⟨x, v⟩
  rw [CoordinateHom.totalSpaceMap_mk, tensorTotalSpaceHomeomorph_apply,
    tensorTotalSpaceHomeomorph_apply, bundleTensorAssocHomeomorph_apply]
  exact congrArg (TotalSpace.mk' _ x) (tensorFiberEquiv_associator_hom A D C x v)

/-- `tensorFiberEquiv` intertwines the monoidal left unitor `(λ_ A).hom` with `TensorProduct.lid`
along `LinearEquiv.funUnique (Fin 1) 𝕜 𝕜` on the unit fibre. -/
@[simp]
theorem lid_tensorFiberEquiv (A : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace ((𝟙_ (FiniteRankBundleCore 𝕜 B)).core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 ((𝟙_ (FiniteRankBundleCore 𝕜 B)).core.Fiber x ⊗[𝕜] A.core.Fiber x)]
    (x : B) (v : ((𝟙_ (FiniteRankBundleCore 𝕜 B)) ⊗ A).core.Fiber x) :
    _root_.TensorProduct.lid 𝕜 (A.core.Fiber x)
        (_root_.TensorProduct.map (LinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toLinearMap LinearMap.id
          (tensorFiberEquiv (𝟙_ (FiniteRankBundleCore 𝕜 B)) A x v)) =
      (λ_ A).hom.fiberMap x v := by
  rw [tensorFiberEquiv_apply]
  exact (lid_map_funUnique_kroneckerTensorEquiv v).trans
    (congrArg (fun f : (Fin (1 * A.rank) → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) ↦ f v)
      (fiberMap_leftUnitor_hom A x).symm)

/-- `tensorFiberEquiv` intertwines the monoidal right unitor `(ρ_ A).hom` with `TensorProduct.rid`
along `LinearEquiv.funUnique (Fin 1) 𝕜 𝕜` on the unit fibre. -/
@[simp]
theorem rid_tensorFiberEquiv (A : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.Fiber x)]
    (x : B) (v : (A ⊗ (𝟙_ (FiniteRankBundleCore 𝕜 B))).core.Fiber x) :
    _root_.TensorProduct.rid 𝕜 (A.core.Fiber x)
        (_root_.TensorProduct.map LinearMap.id (LinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toLinearMap
          (tensorFiberEquiv A (𝟙_ (FiniteRankBundleCore 𝕜 B)) x v)) =
      (ρ_ A).hom.fiberMap x v := by
  rw [tensorFiberEquiv_apply]
  exact (rid_map_funUnique_kroneckerTensorEquiv v).trans
    (congrArg (fun f : (Fin (A.rank * 1) → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) ↦ f v)
      (fiberMap_rightUnitor_hom A x).symm)

end TensorProductBundle

end TauCeti.FiniteRankBundleCore
