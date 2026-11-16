/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Analysis.Normed.Operator.Kronecker
public import TauCeti.Analysis.Normed.Module.TensorProduct.Kronecker
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations

/-!
# Tensor products of finite-rank bundle cores

The tensor product of two point-indexed cores of ranks `a` and `b` has rank `a * b`, the
intersections of the two charts at each point, and the Kronecker products of the two
transition maps as its transitions (`ContinuousLinearMap.kronecker`, with coordinate pair
`(i, j)` at index `finProdFinEquiv (i, j)`). The mixed-product law for Kronecker products is
exactly the cocycle condition, so this is again a Mathlib `VectorBundleCore`.

Two bundle morphisms have the Kronecker product of their chart operators as tensor product,
a continuous fibrewise linear map whose fibre maps are the Kronecker products of the fibre maps
(`FiniteRankBundleCore.fiberMap_tensorHom`). The construction is a bifunctor: it preserves
identities and composition, is additive in each variable, preserves isomorphisms, and commutes
strictly with pullback along continuous maps of bases (`pullback_tensor`,
`pullbackMap_tensorHom`). The base is arbitrary, and the scalar field need not be complete.

When each algebraic tensor fibre `A.core.Fiber x ⊗[𝕜] D.core.Fiber x` carries the `𝕜`-module
topology, `tensorFiberEquiv` identifies `(tensor A D).core.Fiber x` continuously and `𝕜`-linearly
with `A.core.Fiber x ⊗[𝕜] D.core.Fiber x` via `TauCeti.kroneckerTensorEquiv`, without completeness
of `𝕜`, reading in preferred coordinates as `TauCeti.ProjectiveTensor.kroneckerEquiv`
(`tensorFiberEquiv_inCoordinates`) and intertwining `tensorHom f g` with `TauCeti.bundleTensorMap`
(`tensorFiberEquiv_fiberMap_tensorHom`). Over a complete scalar field, `tensorTotalSpaceHomeomorph`
glues these fibrewise equivalences into a homeomorphism between `(tensor A D).core.TotalSpace` and
the total space of the tensor-product vector bundle `fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x`,
natural in morphisms and compatible with `pullbackLift`.

The construction uses Mathlib's coordinate cores and the coordinate morphisms
`VectorBundleCore.CoordinateHom`.
-/

public section

open Bundle CategoryTheory VectorBundleCore Set
open scoped TensorProduct

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The tensor product, with intersected charts and Kronecker products of the transitions. -/
-- Expose the rank projection so the dependent model reduces to the product coordinates.
@[expose]
def tensor (A D : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B where
  rank := A.rank * D.rank
  core :=
    { baseSet := fun i => A.core.baseSet i ∩ D.core.baseSet i
      isOpen_baseSet := fun i => (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet i)
      indexAt := id
      mem_baseSet_at := fun x => by
        simpa only [mem_inter_iff, id_eq, A.indexAt_eq, D.indexAt_eq] using
          And.intro (A.core.mem_baseSet_at x) (D.core.mem_baseSet_at x)
      coordChange := fun i j x =>
        (A.core.coordChange i j x).kronecker (D.core.coordChange i j x)
      coordChange_self := fun i x hx v => by
        rw [A.core.coordChange_self_eq_id hx.1, D.core.coordChange_self_eq_id hx.2,
          ContinuousLinearMap.id_kronecker_id, ContinuousLinearMap.id_apply]
      continuousOn_coordChange := fun i j =>
        ((A.core.continuousOn_coordChange i j).mono
          (inter_subset_inter inter_subset_left inter_subset_left)).clm_kronecker
          ((D.core.continuousOn_coordChange i j).mono
            (inter_subset_inter inter_subset_right inter_subset_right))
      coordChange_comp := fun i j k x hx v => by
        rw [← ContinuousLinearMap.comp_apply, ContinuousLinearMap.kronecker_comp_kronecker,
          A.core.coordChange_linear_comp i j k x ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩,
          D.core.coordChange_linear_comp i j k x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩] }
  indexAt_eq := fun _ => rfl

@[simp] theorem rank_tensor (A D : FiniteRankBundleCore 𝕜 B) :
    (tensor A D).rank = A.rank * D.rank := (rfl)

@[simp] theorem localTriv_baseSet_tensor (A D : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((tensor A D).core.localTriv i).baseSet = A.core.baseSet i ∩ D.core.baseSet i := (rfl)

/-- The transitions of the tensor product are the Kronecker products of the transitions. -/
@[simp] theorem coordChange_tensor (A D : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    (tensor A D).core.coordChange i j x =
      (A.core.coordChange i j x).kronecker (D.core.coordChange i j x) := (rfl)

variable {A A' A'' D D' D'' : FiniteRankBundleCore 𝕜 B}

/-- Changing frames in a tensor product acts separately on the two operator factors.
The formula holds even outside the chart domains, using the core transition operators there. -/
@[simp]
theorem inChartCoordinates_tensor_kronecker (A A' D D' : FiniteRankBundleCore 𝕜 B)
    (f : (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜))
    (g : (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) (i j x : B) :
    (tensor A D).core.inChartCoordinates (tensor A' D').core i j x (f.kronecker g) =
      (A.core.inChartCoordinates A'.core i j x f).kronecker
        (D.core.inChartCoordinates D'.core i j x g) := by
  -- Normalize the dependent coordinate spaces; the tensor core has indexAt = id and
  -- coordChange = the Kronecker product, which identifies the first frame-change expression.
  dsimp +instances only [tensor]
  calc
    _ = ((A'.core.coordChange x j x).kronecker (D'.core.coordChange x j x)).comp
        ((f.kronecker g).comp
          ((A.core.coordChange i x x).kronecker (D.core.coordChange i x x))) := by
      ext v
      simp only [VectorBundleCore.inChartCoordinates_apply, ContinuousLinearMap.comp_apply]
      rfl
    _ = ((A'.core.coordChange x j x).comp (f.comp (A.core.coordChange i x x))).kronecker
        ((D'.core.coordChange x j x).comp (g.comp (D.core.coordChange i x x))) := by
      rw [ContinuousLinearMap.kronecker_comp_kronecker,
        ContinuousLinearMap.kronecker_comp_kronecker]
    _ = _ := by
      congr 1 <;> ext v <;>
        simp only [VectorBundleCore.inChartCoordinates_apply, ContinuousLinearMap.comp_apply,
          indexAt_eq]

/-- The tensor product of two bundle maps, given in charts by Kronecker products of the chart
operators. -/
def tensorHom (f : A ⟶ A') (g : D ⟶ D') : tensor A D ⟶ tensor A' D' where
  operator i j :=
    ⟨fun x => (f.operator i j ⟨x.1, x.2.1.1, x.2.2.1⟩).kronecker
        (g.operator i j ⟨x.1, x.2.1.2, x.2.2.2⟩),
      ((f.operator i j).continuous.comp (continuous_subtype_val.subtype_mk _)).clm_kronecker
        ((g.operator i j).continuous.comp (continuous_subtype_val.subtype_mk _))⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Both sides are Kronecker products; compare the two factors as operators.
    change ((A'.core.coordChange j j' x).kronecker (D'.core.coordChange j j' x)).comp
        ((f.operator i j ⟨x, hi.1, hj.1⟩).kronecker (g.operator i j ⟨x, hi.2, hj.2⟩)) v =
      ((f.operator i' j' ⟨x, hi'.1, hj'.1⟩).kronecker (g.operator i' j' ⟨x, hi'.2, hj'.2⟩)).comp
        ((A.core.coordChange i i' x).kronecker (D.core.coordChange i i' x)) v
    rw [ContinuousLinearMap.kronecker_comp_kronecker, ContinuousLinearMap.kronecker_comp_kronecker,
      f.coordChange_comp_operator i i' j j' x hi.1 hi'.1 hj.1 hj'.1,
      g.coordChange_comp_operator i i' j j' x hi.2 hi'.2 hj.2 hj'.2]

/-- On every fibre, the tensor product of two bundle maps is the Kronecker product of their
fibre maps. -/
@[simp] theorem fiberMap_tensorHom (f : A ⟶ A') (g : D ⟶ D') (x : B) :
    (tensorHom f g).fiberMap x = (f.fiberMap x).kronecker (g.fiberMap x) := by
  calc
    _ = (f.operator x x ⟨x, A.mem_baseSet_self x, A'.mem_baseSet_self x⟩).kronecker
        (g.operator x x ⟨x, D.mem_baseSet_self x, D'.mem_baseSet_self x⟩) :=
      CoordinateHom.fiberMap_def _ x
    _ = _ := by rw [operator_self, operator_self]

/-- The tensor product of two identity morphisms is the identity. -/
@[simp] theorem id_tensorHom_id (A D : FiniteRankBundleCore 𝕜 B) :
    tensorHom (𝟙 A) (𝟙 D) = 𝟙 (tensor A D) := by
  apply hom_ext
  intro x
  rw [fiberMap_tensorHom, fiberMap_id, fiberMap_id, fiberMap_id]
  exact ContinuousLinearMap.id_kronecker_id

-- In the following proofs the fibre maps of tensor products have the product coordinates as
-- model, which the Kronecker-product lemmas state for `Fin (A.rank * D.rank) → 𝕜`; the exposed
-- rank projection identifies the two models.

/-- Tensor products of morphisms compose factorwise: composing in both factors simultaneously
commutes with forming the tensor product. -/
@[reassoc (attr := simp)] theorem tensorHom_comp_tensorHom (f : A ⟶ A') (f' : A' ⟶ A'')
    (g : D ⟶ D') (g' : D' ⟶ D'') :
    tensorHom f g ≫ tensorHom f' g' = tensorHom (f ≫ f') (g ≫ g') := by
  apply hom_ext
  intro x
  rw [fiberMap_comp, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_comp,
    fiberMap_comp]
  exact ContinuousLinearMap.kronecker_comp_kronecker _ _ _ _

@[simp] theorem add_tensorHom (f f' : A ⟶ A') (g : D ⟶ D') :
    tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  apply hom_ext
  intro x
  rw [fiberMap_add, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_add]
  exact ContinuousLinearMap.add_kronecker _ _ _

@[simp] theorem tensorHom_add (f : A ⟶ A') (g g' : D ⟶ D') :
    tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  apply hom_ext
  intro x
  rw [fiberMap_add, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_add]
  exact ContinuousLinearMap.kronecker_add _ _ _

@[simp] theorem zero_tensorHom (g : D ⟶ D') : tensorHom (0 : A ⟶ A') g = 0 := by
  apply hom_ext
  intro x
  rw [fiberMap_tensorHom, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
  exact ContinuousLinearMap.zero_kronecker _

@[simp] theorem tensorHom_zero (f : A ⟶ A') : tensorHom f (0 : D ⟶ D') = 0 := by
  apply hom_ext
  intro x
  rw [fiberMap_tensorHom, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
  exact ContinuousLinearMap.kronecker_zero _

@[simp] theorem neg_tensorHom (f : A ⟶ A') (g : D ⟶ D') :
    tensorHom (-f) g = -tensorHom f g := by
  rw [eq_neg_iff_add_eq_zero, ← add_tensorHom, neg_add_cancel, zero_tensorHom]

@[simp] theorem tensorHom_neg (f : A ⟶ A') (g : D ⟶ D') :
    tensorHom f (-g) = -tensorHom f g := by
  rw [eq_neg_iff_add_eq_zero, ← tensorHom_add, neg_add_cancel, tensorHom_zero]

/-- The tensor product of two bundle isomorphisms is an isomorphism. -/
instance (f : A ⟶ A') (g : D ⟶ D') [IsIso f] [IsIso g] : IsIso (tensorHom f g) :=
  ⟨tensorHom (inv f) (inv g), by simp, by simp⟩

section TensorProductBundle

/-- Canonical continuous `𝕜`-linear equivalence between the coordinate fibre of `tensor A D` at `x`
and the algebraic tensor product `A.core.Fiber x ⊗[𝕜] D.core.Fiber x` equipped with the `𝕜`-module
topology. No completeness of `𝕜` is required. -/
noncomputable def tensorFiberEquiv (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)] (x : B) :
    (tensor A D).core.Fiber x ≃L[𝕜] (A.core.Fiber x ⊗[𝕜] D.core.Fiber x) :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (kroneckerTensorEquiv 𝕜 A.rank D.rank :
      (tensor A D).core.Fiber x ≃ₗ[𝕜] A.core.Fiber x ⊗[𝕜] D.core.Fiber x)

/-- `tensorFiberEquiv` acts on coordinate vectors by `kroneckerTensorEquiv`. -/
theorem tensorFiberEquiv_apply (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (x : B) (v : (tensor A D).core.Fiber x) :
    tensorFiberEquiv A D x v = kroneckerTensorEquiv 𝕜 A.rank D.rank v :=
  let e : (tensor A D).core.Fiber x ≃ₗ[𝕜] A.core.Fiber x ⊗[𝕜] D.core.Fiber x :=
    kroneckerTensorEquiv 𝕜 A.rank D.rank
  congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology e) v

/-- The inverse of `tensorFiberEquiv` acts by `(kroneckerTensorEquiv 𝕜 A.rank D.rank).symm`. -/
theorem tensorFiberEquiv_symm_apply (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (x : B) (t : A.core.Fiber x ⊗[𝕜] D.core.Fiber x) :
    (tensorFiberEquiv A D x).symm t = (kroneckerTensorEquiv 𝕜 A.rank D.rank).symm t :=
  let e : (tensor A D).core.Fiber x ≃ₗ[𝕜] A.core.Fiber x ⊗[𝕜] D.core.Fiber x :=
    kroneckerTensorEquiv 𝕜 A.rank D.rank
  (congrFun (congrArg DFunLike.coe (LinearEquiv.symm_toContinuousLinearEquivOfIsModuleTopology e))
    t).trans (congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology e.symm) t)

/-- The inverse of `tensorFiberEquiv` evaluates a pure tensor `u ⊗ₜ w` at `finProdFinEquiv (i, j)`
to `u i * w j`. -/
@[simp]
theorem tensorFiberEquiv_symm_tmul_apply (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (x : B) (u : A.core.Fiber x) (w : D.core.Fiber x) (i : Fin A.rank) (j : Fin D.rank) :
    (tensorFiberEquiv A D x).symm (u ⊗ₜ[𝕜] w) (finProdFinEquiv (i, j)) = u i * w j :=
  (congrFun (tensorFiberEquiv_symm_apply A D x (u ⊗ₜ[𝕜] w)) (finProdFinEquiv (i, j))).trans
    (kroneckerTensorEquiv_symm_tmul_apply u w i j)

/-- `tensorFiberEquiv` sends the standard basis vector at `finProdFinEquiv (i, j)` with coefficient
`c` to `c • (Pi.single i 1 ⊗ₜ Pi.single j 1)`. -/
@[simp]
theorem tensorFiberEquiv_single (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (x : B) (i : Fin A.rank) (j : Fin D.rank) (c : 𝕜) :
    tensorFiberEquiv A D x (Pi.single (finProdFinEquiv (i, j)) c) =
      c • ((Pi.single i 1 : A.core.Fiber x) ⊗ₜ[𝕜] (Pi.single j 1 : D.core.Fiber x)) :=
  (tensorFiberEquiv_apply A D x _).trans (kroneckerTensorEquiv_single i j c)

/-- On the common domain of the charts of `A` and `D` at `a`, reading `tensorFiberEquiv A D x v` in
`TensorProduct.inCoordinates` gives `ProjectiveTensor.kroneckerEquiv` applied to the tensor-core
coordinates of `v` in chart `a`. -/
theorem tensorFiberEquiv_inCoordinates (A D : FiniteRankBundleCore 𝕜 B)
    [∀ y, TopologicalSpace (A.core.Fiber y ⊗[𝕜] D.core.Fiber y)]
    [∀ y, IsModuleTopology 𝕜 (A.core.Fiber y ⊗[𝕜] D.core.Fiber y)]
    (a x : B) (hx : x ∈ A.core.baseSet a ∩ D.core.baseSet a)
    (v : (tensor A D).core.Fiber x) :
    TensorProduct.inCoordinates (Fin A.rank → 𝕜) A.core.Fiber (Fin D.rank → 𝕜) D.core.Fiber
        a x a x (tensorFiberEquiv A D x v) =
      ProjectiveTensor.kroneckerEquiv 𝕜 A.rank D.rank
        (((tensor A D).core.localTriv a) ⟨x, v⟩).2 := by
  have hA : x ∈ (trivializationAt (Fin A.rank → 𝕜) A.core.Fiber a).baseSet := by
    rw [A.trivializationAt_core]
    exact hx.1
  have hD : x ∈ (trivializationAt (Fin D.rank → 𝕜) D.core.Fiber a).baseSet := by
    rw [D.trivializationAt_core]
    exact hx.2
  obtain ⟨t, ht⟩ := (kroneckerTensorEquiv 𝕜 A.rank D.rank).symm.surjective v
  let t' : A.core.Fiber x ⊗[𝕜] D.core.Fiber x := t
  have hlhs : tensorFiberEquiv A D x v = t' := by
    rw [← ht]
    exact (tensorFiberEquiv_apply A D x _).trans
      ((kroneckerTensorEquiv 𝕜 A.rank D.rank).apply_symm_apply t)
  have hrhs : ProjectiveTensor.kroneckerEquiv 𝕜 A.rank D.rank
      (((tensor A D).core.localTriv a) ⟨x, v⟩).2 =
      ⟨_root_.TensorProduct.map (A.core.coordChange x a x).toLinearMap
        (D.core.coordChange x a x).toLinearMap t'⟩ := by
    have htriv : (((tensor A D).core.localTriv a) ⟨x, v⟩).2 =
        ((A.core.coordChange x a x).kronecker (D.core.coordChange x a x))
          ((kroneckerTensorEquiv 𝕜 A.rank D.rank).symm t) := by
      simp only [VectorBundleCore.localTriv_apply, (tensor A D).indexAt_eq, coordChange_tensor,
        ← ht]
      rfl
    apply ProjectiveTensor.ext
    rw [htriv, ProjectiveTensor.toTensorProduct_kroneckerEquiv, ← kroneckerTensorEquiv_symm_map,
      LinearEquiv.apply_symm_apply]
  rw [hlhs, hrhs]
  clear_value t'
  clear ht hlhs hrhs t v
  induction t' using _root_.TensorProduct.inductionOn with
  | tmul u w =>
      have htmul := TensorProduct.inCoordinates_tmul_of_mem (𝕜 := 𝕜) hA hD u w
      rw [A.trivializationAt_core, D.trivializationAt_core] at htmul
      refine htmul.trans ?_
      apply ProjectiveTensor.ext
      simp only [VectorBundleCore.localTriv_apply, A.indexAt_eq, D.indexAt_eq]
      exact (_root_.TensorProduct.map_tmul (A.core.coordChange x a x).toLinearMap
        (D.core.coordChange x a x).toLinearMap u w).symm
  | add p q hp hq =>
      rw [map_add, hp, hq, ← ProjectiveTensor.mk_add]
      exact congrArg ProjectiveTensor.mk ((_root_.TensorProduct.map _ _).map_add p q).symm

/-- `tensorFiberEquiv` intertwines the fibre map of `tensorHom f g` with `bundleTensorMap` of the
factor fibre maps. -/
theorem tensorFiberEquiv_fiberMap_tensorHom
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (A'.core.Fiber x ⊗[𝕜] D'.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A'.core.Fiber x ⊗[𝕜] D'.core.Fiber x)]
    (f : A ⟶ A') (g : D ⟶ D') (x : B) (v : (tensor A D).core.Fiber x) :
    tensorFiberEquiv A' D' x ((tensorHom f g).fiberMap x v) =
      bundleTensorMap (E₁ := A.core.Fiber) (E₁' := A'.core.Fiber)
        (E₂ := D.core.Fiber) (E₂' := D'.core.Fiber)
        f.fiberMap g.fiberMap x (tensorFiberEquiv A D x v) := by
  refine (tensorFiberEquiv_apply A' D' x _).trans ?_
  refine (congrArg (kroneckerTensorEquiv 𝕜 A'.rank D'.rank)
    (DFunLike.congr_fun (fiberMap_tensorHom f g x) v)).trans ?_
  refine (kroneckerTensorEquiv_kronecker (f.fiberMap x) (g.fiberMap x) v).trans ?_
  refine Eq.trans ?_ (congrArg (bundleTensorMap (E₁ := A.core.Fiber) (E₁' := A'.core.Fiber)
    (E₂ := D.core.Fiber) (E₂' := D'.core.Fiber) f.fiberMap g.fiberMap x)
    (tensorFiberEquiv_apply A D x v)).symm
  suffices ∀ t : A.core.Fiber x ⊗[𝕜] D.core.Fiber x,
      _root_.TensorProduct.map (f.fiberMap x).toLinearMap (g.fiberMap x).toLinearMap t =
        bundleTensorMap (E₁ := A.core.Fiber) (E₁' := A'.core.Fiber)
          (E₂ := D.core.Fiber) (E₂' := D'.core.Fiber) f.fiberMap g.fiberMap x t from
    this (kroneckerTensorEquiv 𝕜 A.rank D.rank v)
  intro t
  induction t using _root_.TensorProduct.inductionOn with
  | tmul u w =>
      exact (bundleTensorMap_tmul (E₁ := A.core.Fiber) (E₁' := A'.core.Fiber)
        (E₂ := D.core.Fiber) (E₂' := D'.core.Fiber) f.fiberMap g.fiberMap x u w).symm
  | add p q hp hq =>
      rw [map_add, ← hp, ← hq]
      exact (_root_.TensorProduct.map _ _).map_add p q

section TotalSpaceHomeomorph

variable [CompleteSpace 𝕜]

/-- Reading tensor-core coordinate vectors as elements of `A.core.Fiber x ⊗[𝕜] D.core.Fiber x` is
continuous on total spaces. -/
theorem continuous_tensorFiberEquiv (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)] :
    Continuous fun p : (tensor A D).core.TotalSpace ↦
      TotalSpace.mk' (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
        (E := fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x) p.proj
        (tensorFiberEquiv A D p.proj p.2) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [continuousAt_tensorProduct_bundle]
  refine ⟨(tensor A D).core.continuous_proj.continuousAt, ?_⟩
  have hp : p ∈ ((tensor A D).core.localTriv p.proj).source :=
    ((tensor A D).core.mem_localTriv_source p.proj p).2 ((tensor A D).core.mem_baseSet_at p.proj)
  have hU := ((tensor A D).core.localTriv p.proj).open_source.mem_nhds hp
  have hc := (((tensor A D).core.localTriv p.proj).continuousOn.continuousAt hU).snd
  refine ((ProjectiveTensor.kroneckerEquiv 𝕜 A.rank D.rank).continuous.continuousAt.comp hc).congr
    ?_
  filter_upwards [hU] with q hq
  exact (tensorFiberEquiv_inCoordinates A D p.proj q.proj
    (((tensor A D).core.mem_localTriv_source p.proj q).1 hq) q.2).symm

/-- Homeomorphism between the reconstructed total space of `tensor A D` and the total space of the
tensor-product vector bundle `fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x`, over the identity of `B`
and by `tensorFiberEquiv A D` on each fibre. -/
noncomputable def tensorTotalSpaceHomeomorph (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)] :
    (tensor A D).core.TotalSpace ≃ₜ
      TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
        (fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x) :=
  bundleHomeomorph (tensorFiberEquiv A D) (continuous_tensorFiberEquiv A D)

/-- `tensorTotalSpaceHomeomorph` acts on each fibre by `tensorFiberEquiv`. -/
@[simp]
theorem tensorTotalSpaceHomeomorph_apply (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (p : (tensor A D).core.TotalSpace) :
    tensorTotalSpaceHomeomorph A D p = ⟨p.proj, tensorFiberEquiv A D p.proj p.2⟩ :=
  bundleHomeomorph_apply _ _ p

/-- The inverse of `tensorTotalSpaceHomeomorph` acts on each fibre by
`(tensorFiberEquiv A D p.proj).symm`. -/
@[simp]
theorem tensorTotalSpaceHomeomorph_symm_apply (A D : FiniteRankBundleCore 𝕜 B)
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    (p : TotalSpace (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x)) :
    (tensorTotalSpaceHomeomorph A D).symm p = ⟨p.proj, (tensorFiberEquiv A D p.proj).symm p.2⟩ :=
  bundleHomeomorph_symm_apply _ _ p

/-- `tensorTotalSpaceHomeomorph` intertwines `(tensorHom f g).totalSpaceMap` on tensor cores with
`bundleTensorMap f.fiberMap g.fiberMap` on tensor-product vector bundles. -/
theorem tensorTotalSpaceHomeomorph_naturality
    [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
    [∀ x, TopologicalSpace (A'.core.Fiber x ⊗[𝕜] D'.core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 (A'.core.Fiber x ⊗[𝕜] D'.core.Fiber x)]
    (f : A ⟶ A') (g : D ⟶ D') (p : (tensor A D).core.TotalSpace) :
    tensorTotalSpaceHomeomorph A' D' ((tensorHom f g).totalSpaceMap p) =
      ⟨p.proj, bundleTensorMap (E₁ := A.core.Fiber) (E₁' := A'.core.Fiber)
        (E₂ := D.core.Fiber) (E₂' := D'.core.Fiber)
        f.fiberMap g.fiberMap p.proj (tensorTotalSpaceHomeomorph A D p).2⟩ := by
  rcases p with ⟨x, v⟩
  rw [CoordinateHom.totalSpaceMap_mk, tensorTotalSpaceHomeomorph_apply,
    tensorTotalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk' _ x) (tensorFiberEquiv_fiberMap_tensorHom f g x v)

end TotalSpaceHomeomorph

end TensorProductBundle

section Pullback

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back commutes strictly with tensor products of cores. -/
@[simp] theorem pullback_tensor (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (tensor A D).pullback f = tensor (A.pullback f) (D.pullback f) := (rfl)

/-- Pulling back commutes with tensor products of bundle morphisms. -/
@[simp] theorem pullbackMap_tensorHom {A A' D D' : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ A') (b : D ⟶ D') (f : C(X, Y)) :
    pullbackMap (tensorHom a b) f = tensorHom (pullbackMap a f) (pullbackMap b f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_tensorHom, ← fiberMap_pullbackMap a f x,
    ← fiberMap_pullbackMap b f x]
  -- `(tensor A D).pullback f` is definitionally `tensor (A.pullback f) (D.pullback f)`
  -- (`pullback_tensor`), identifying the implicit cores of `fiberMap` on the right.
  exact Eq.symm (fiberMap_tensorHom _ _ x)

/-- On every fibre, `tensorFiberEquiv` on a pulled-back tensor product agrees with
`tensorFiberEquiv` at the image base point. -/
@[simp]
theorem tensorFiberEquiv_pullback_apply (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    [∀ x, TopologicalSpace ((A.pullback f).core.Fiber x ⊗[𝕜] (D.pullback f).core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 ((A.pullback f).core.Fiber x ⊗[𝕜] (D.pullback f).core.Fiber x)]
    [∀ y, TopologicalSpace (A.core.Fiber y ⊗[𝕜] D.core.Fiber y)]
    [∀ y, IsModuleTopology 𝕜 (A.core.Fiber y ⊗[𝕜] D.core.Fiber y)]
    (x : X) (v : (tensor (A.pullback f) (D.pullback f)).core.Fiber x) :
    tensorFiberEquiv (A.pullback f) (D.pullback f) x v = tensorFiberEquiv A D (f x) v := by
  rw [tensorFiberEquiv_apply]
  -- Both fibres are `Fin (A.rank * D.rank) → 𝕜` (`rank_pullback`), matching
  -- `tensorFiberEquiv_apply` on the right.
  exact Eq.symm (tensorFiberEquiv_apply A D (f x) v)

/-- On a pulled-back tensor product, `tensorTotalSpaceHomeomorph` over `X` and over `Y` agree along
`pullbackLift`. -/
theorem tensorTotalSpaceHomeomorph_pullbackLift [CompleteSpace 𝕜]
    (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    [∀ x, TopologicalSpace ((A.pullback f).core.Fiber x ⊗[𝕜] (D.pullback f).core.Fiber x)]
    [∀ x, IsModuleTopology 𝕜 ((A.pullback f).core.Fiber x ⊗[𝕜] (D.pullback f).core.Fiber x)]
    [∀ y, TopologicalSpace (A.core.Fiber y ⊗[𝕜] D.core.Fiber y)]
    [∀ y, IsModuleTopology 𝕜 (A.core.Fiber y ⊗[𝕜] D.core.Fiber y)]
    (p : ((tensor A D).pullback f).core.TotalSpace) :
    tensorTotalSpaceHomeomorph A D ((tensor A D).pullbackLift f p) =
      ⟨f p.proj, (tensorTotalSpaceHomeomorph (A.pullback f) (D.pullback f) p).2⟩ := by
  rcases p with ⟨x, v⟩
  rw [pullbackLift_mk]
  -- Rebind the point across the definitional equality `pullback_tensor` so the pullback-side
  -- `tensorTotalSpaceHomeomorph_apply` matches at reducible transparency.
  let q : (tensor (A.pullback f) (D.pullback f)).core.TotalSpace := ⟨x, v⟩
  change tensorTotalSpaceHomeomorph A D ⟨f x, v⟩ =
    ⟨f x, (tensorTotalSpaceHomeomorph (A.pullback f) (D.pullback f) q).2⟩
  rw [tensorTotalSpaceHomeomorph_apply, tensorTotalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk' _ (f x)) (tensorFiberEquiv_pullback_apply A D f x q.2).symm

end Pullback

end TauCeti.FiniteRankBundleCore
