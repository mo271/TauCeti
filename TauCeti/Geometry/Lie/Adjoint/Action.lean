/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Geometry.Lie.Adjoint.Smooth
public import TauCeti.Geometry.Lie.Subgroup.Commutative

/-!
# The adjoint module of a Lie group

`GroupLieAlgebra I G` is an abbreviation for `TangentSpace I (1 : G)`, which reduces to the
ambient normed model space `E`. Installing a `MulAction G` instance directly on
`GroupLieAlgebra I G` would therefore equip `E` globally with a group action and lose track of
the model with corners `I`.

This file introduces `TauCeti.Lie.AdjointLieAlgebra I G`, a dedicated type copy of
`GroupLieAlgebra I G` carrying the left adjoint action `g • X = Ad_g X` via
`TauCeti.Lie.adjointContinuousLinearMap`, together with its normed-space, Lie-algebra, and smooth
`ContMDiffSMul` structures. This is the model fibre used to form the adjoint bundle `ad(P)` of a
principal `G`-bundle `P` as `TauCeti.AssociatedBundle G P (TauCeti.Lie.AdjointLieAlgebra I G)`.

We also record continuity of the Lie bracket on any finite-dimensional Hausdorff topological Lie
algebra over a complete field, `C^n` smoothness of the Lie bracket on `AdjointLieAlgebra I G`, and
`Ad`-invariance of the Killing form of a Lie group.

## Main definitions

* `LieAlgebra.lieContinuousBilinearMap`: the Lie bracket of a finite-dimensional Hausdorff
  topological Lie algebra over a complete field as a continuous bilinear map.
* `TauCeti.Lie.AdjointLieAlgebra`: type copy of `GroupLieAlgebra I G` carrying the left `Ad`-action
  of `G`.
* `TauCeti.Lie.AdjointLieAlgebra.ofGroupLieAlgebra`: continuous linear equivalence from
  `GroupLieAlgebra I G` to `AdjointLieAlgebra I G`.
* `TauCeti.Lie.AdjointLieAlgebra.lieEquiv`: Lie-algebra equivalence from `GroupLieAlgebra I G` to
  `AdjointLieAlgebra I G`.
* `TauCeti.Lie.AdjointLieAlgebra.smulLieEquiv`: the action of `g : G` on `AdjointLieAlgebra I G`
  as a Lie-algebra automorphism.

## Main results

* `LieAlgebra.continuous_lie`: the Lie bracket on a finite-dimensional Hausdorff topological Lie
  algebra over a complete field is jointly continuous.
* `TauCeti.Lie.AdjointLieAlgebra.contDiff_lie`: the Lie bracket on a finite-dimensional
  `AdjointLieAlgebra I G` over a complete field is `C^n` for every `n` (including `∞` and `ω`).
* `TauCeti.Lie.AdjointLieAlgebra.smul_lie`: the `G`-action on `AdjointLieAlgebra I G` preserves
  the Lie bracket.
* `TauCeti.Lie.AdjointLieAlgebra.smul_eq_self`: the `G`-action is trivial when `G` is commutative.
* `TauCeti.Lie.AdjointLieAlgebra.instContMDiffSMul` and `instContinuousSMul`: joint smoothness and
  continuity of the adjoint action of a real `C^∞` Lie group.
* `TauCeti.Lie.killingForm_adjointContinuousLinearMap`: the Killing form on `GroupLieAlgebra I G`
  is invariant under `adjointContinuousLinearMap`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §§10.7, 10.18.
-/

public section

noncomputable section

open scoped ContDiff Manifold

section FiniteDimensionalLieBracket

namespace LieAlgebra

variable (𝕜 L : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [LieRing L] [LieAlgebra 𝕜 L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul 𝕜 L] [FiniteDimensional 𝕜 L] [T2Space L]

/-- On a finite-dimensional Hausdorff topological Lie algebra over a complete field, the Lie
bracket is a continuous bilinear map. -/
def lieContinuousBilinearMap : L →L[𝕜] L →L[𝕜] L :=
  IsBilinearMap.toContinuousBilinearMap
    { add_left := add_lie
      smul_left := smul_lie
      add_right := lie_add
      smul_right := lie_smul }

@[simp]
theorem lieContinuousBilinearMap_apply (x y : L) :
    lieContinuousBilinearMap 𝕜 L x y = ⁅x, y⁆ :=
  IsBilinearMap.toContinuousBilinearMap_apply _ x y

/-- On a finite-dimensional Hausdorff topological Lie algebra over a complete field, the Lie
bracket is jointly continuous. -/
theorem continuous_lie {𝕜 L : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [LieRing L] [LieAlgebra 𝕜 L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [ContinuousSMul 𝕜 L] [FiniteDimensional 𝕜 L] [T2Space L] :
    Continuous (fun p : L × L ↦ ⁅p.1, p.2⁆) := by
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (L ≃L[𝕜] (Fin n → 𝕜)) :=
    ⟨Module.finrank 𝕜 L, ⟨(Module.finBasis 𝕜 L).equivFunL⟩⟩
  obtain ⟨B, hB⟩ : ∃ B : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜),
      ∀ u v, B u v = e ⁅e.symm u, e.symm v⁆ :=
    ⟨IsBilinearMap.toContinuousBilinearMap
      (f := fun u v ↦ e ⁅e.symm u, e.symm v⁆)
      { add_left := fun _ _ _ ↦ by simp [map_add, add_lie]
        smul_left := fun _ _ _ ↦ by simp [map_smul, smul_lie]
        add_right := fun _ _ _ ↦ by simp [map_add, lie_add]
        smul_right := fun _ _ _ ↦ by simp [map_smul, lie_smul] },
      fun u v ↦ IsBilinearMap.toContinuousBilinearMap_apply _ u v⟩
  have hcont : Continuous (fun p : L × L ↦ e.symm (B (e p.1) (e p.2))) :=
    e.symm.continuous.comp (B.isBoundedBilinearMap.continuous.comp
      (e.continuous.prodMap e.continuous))
  exact hcont.congr fun p ↦ by
    rw [hB, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]

end LieAlgebra

end FiniteDimensionalLieBracket

namespace TauCeti.Lie

section GeneralField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

/-- A type copy of `GroupLieAlgebra I G` carrying the left adjoint action of `G` via
`TauCeti.Lie.adjointContinuousLinearMap`. Isolating this action on a dedicated carrier retains `I`
in the type and avoids equipping the ambient model vector space `E` with a `G`-action. -/
def AdjointLieAlgebra (I : ModelWithCorners 𝕜 E H)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] : Type _ :=
  GroupLieAlgebra I G

namespace AdjointLieAlgebra

variable {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

instance instNormedAddCommGroup : NormedAddCommGroup (AdjointLieAlgebra I G) :=
  inferInstanceAs (NormedAddCommGroup E)

instance instNormedSpace : NormedSpace 𝕜 (AdjointLieAlgebra I G) :=
  inferInstanceAs (NormedSpace 𝕜 E)

instance instFiniteDimensional [FiniteDimensional 𝕜 E] :
    FiniteDimensional 𝕜 (AdjointLieAlgebra I G) :=
  inferInstanceAs (FiniteDimensional 𝕜 E)

instance instCompleteSpace [CompleteSpace E] : CompleteSpace (AdjointLieAlgebra I G) :=
  inferInstanceAs (CompleteSpace E)

variable (I G) in
/-- The canonical continuous linear equivalence identifying `GroupLieAlgebra I G` with its
adjoint-module copy `AdjointLieAlgebra I G`. -/
def ofGroupLieAlgebra : GroupLieAlgebra I G ≃L[𝕜] AdjointLieAlgebra I G where
  toFun X := X
  invFun X := X
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

variable (I G) in
/-- The canonical continuous linear equivalence identifying the model vector space `E` with
`AdjointLieAlgebra I G`. -/
def ofModel : E ≃L[𝕜] AdjointLieAlgebra I G :=
  ContinuousLinearEquiv.refl 𝕜 E

@[simp]
theorem ofModel_symm_ofGroupLieAlgebra (X : GroupLieAlgebra I G) :
    (ofModel I G).symm (ofGroupLieAlgebra I G X) = X := by
  rfl

@[simp]
theorem ofGroupLieAlgebra_symm_ofModel (v : E) :
    (ofGroupLieAlgebra I G).symm (ofModel I G v) = v := by
  rfl

instance instBracket : Bracket (AdjointLieAlgebra I G) (AdjointLieAlgebra I G) where
  bracket X Y := ofGroupLieAlgebra I G
    ⁅(ofGroupLieAlgebra I G).symm X, (ofGroupLieAlgebra I G).symm Y⁆

@[simp]
theorem ofGroupLieAlgebra_lie (X Y : GroupLieAlgebra I G) :
    ofGroupLieAlgebra I G ⁅X, Y⁆ = ⁅ofGroupLieAlgebra I G X, ofGroupLieAlgebra I G Y⁆ := by
  simp [Bracket.bracket]

@[simp]
theorem ofGroupLieAlgebra_symm_lie (X Y : AdjointLieAlgebra I G) :
    (ofGroupLieAlgebra I G).symm ⁅X, Y⁆ =
      ⁅(ofGroupLieAlgebra I G).symm X, (ofGroupLieAlgebra I G).symm Y⁆ := by
  simp [Bracket.bracket]

section LieStructure

variable [CompleteSpace E] [LieGroup I (minSmoothness 𝕜 3) G]

instance instLieRing : LieRing (AdjointLieAlgebra I G) where
  add_lie X Y Z := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [ofGroupLieAlgebra_symm_lie, map_add, add_lie]
  lie_add X Y Z := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [ofGroupLieAlgebra_symm_lie, map_add, lie_add]
  lie_self X := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [ofGroupLieAlgebra_symm_lie, map_zero, lie_self]
  leibniz_lie X Y Z := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [ofGroupLieAlgebra_symm_lie, map_add]
    exact leibniz_lie _ _ _

instance instLieAlgebra : LieAlgebra 𝕜 (AdjointLieAlgebra I G) where
  lie_smul c X Y := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [ofGroupLieAlgebra_symm_lie, map_smul, lie_smul]

instance instIsLieAbelian [IsLieAbelian (GroupLieAlgebra I G)] :
    IsLieAbelian (AdjointLieAlgebra I G) where
  trivial X Y := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [ofGroupLieAlgebra_symm_lie, map_zero, LieModule.IsTrivial.trivial]

variable (I G) in
/-- The canonical Lie-algebra equivalence identifying `GroupLieAlgebra I G` with
`AdjointLieAlgebra I G`. -/
def lieEquiv : GroupLieAlgebra I G ≃ₗ⁅𝕜⁆ AdjointLieAlgebra I G :=
  { (ofGroupLieAlgebra I G).toLinearEquiv with
    map_lie' := fun {_ _} ↦ (ofGroupLieAlgebra_lie _ _).symm }

@[simp]
theorem lieEquiv_apply (X : GroupLieAlgebra I G) :
    lieEquiv I G X = ofGroupLieAlgebra I G X := by
  rfl

@[simp]
theorem lieEquiv_symm_apply (X : AdjointLieAlgebra I G) :
    (lieEquiv I G).symm X = (ofGroupLieAlgebra I G).symm X := by
  rfl

@[simp]
theorem coe_toLinearEquiv_lieEquiv :
    (lieEquiv I G).toLinearEquiv = (ofGroupLieAlgebra I G).toLinearEquiv := by
  ext X
  exact lieEquiv_apply X

/-- On a finite-dimensional Lie group over a complete field, the Lie bracket on
`AdjointLieAlgebra I G` is `C^n` for every regularity `n` (including `∞` and `ω`). -/
theorem contDiff_lie [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] {n : ℕ∞ω} :
    ContDiff 𝕜 n (fun p : AdjointLieAlgebra I G × AdjointLieAlgebra I G ↦ ⁅p.1, p.2⁆) := by
  simpa only [LieAlgebra.lieContinuousBilinearMap_apply] using
    (LieAlgebra.lieContinuousBilinearMap 𝕜
      (AdjointLieAlgebra I G)).isBoundedBilinearMap.contDiff (n := n)

end LieStructure

section Action

variable [LieGroup I 1 G]

instance instSMul : SMul G (AdjointLieAlgebra I G) where
  smul g X := ofGroupLieAlgebra I G
    (adjointContinuousLinearMap (I := I) g ((ofGroupLieAlgebra I G).symm X))

@[simp]
theorem smul_ofGroupLieAlgebra (g : G) (X : GroupLieAlgebra I G) :
    g • ofGroupLieAlgebra I G X =
      ofGroupLieAlgebra I G (adjointContinuousLinearMap (I := I) g X) :=
  congrArg (ofGroupLieAlgebra I G) (congrArg (adjointContinuousLinearMap (I := I) g)
    ((ofGroupLieAlgebra I G).symm_apply_apply X))

@[simp]
theorem ofGroupLieAlgebra_symm_smul (g : G) (X : AdjointLieAlgebra I G) :
    (ofGroupLieAlgebra I G).symm (g • X) =
      adjointContinuousLinearMap (I := I) g ((ofGroupLieAlgebra I G).symm X) :=
  (ofGroupLieAlgebra I G).symm_apply_apply _

instance instDistribMulAction : DistribMulAction G (AdjointLieAlgebra I G) where
  one_smul X := by
    apply (ofGroupLieAlgebra I G).symm.injective
    rw [ofGroupLieAlgebra_symm_smul, adjointContinuousLinearMap_one, ContinuousLinearMap.id_apply]
  mul_smul g h X := by
    apply (ofGroupLieAlgebra I G).symm.injective
    rw [ofGroupLieAlgebra_symm_smul, adjointContinuousLinearMap_mul,
      ContinuousLinearMap.comp_apply, ofGroupLieAlgebra_symm_smul, ofGroupLieAlgebra_symm_smul]
  smul_zero g := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [map_zero, ofGroupLieAlgebra_symm_smul]
  smul_add g X Y := by
    apply (ofGroupLieAlgebra I G).symm.injective
    simp only [map_add, ofGroupLieAlgebra_symm_smul]

instance instSMulCommClass : SMulCommClass G 𝕜 (AdjointLieAlgebra I G) where
  smul_comm g r X := by
    apply (ofGroupLieAlgebra I G).symm.injective
    rw [ofGroupLieAlgebra_symm_smul, (ofGroupLieAlgebra I G).symm.map_smul,
      (ofGroupLieAlgebra I G).symm.map_smul, ofGroupLieAlgebra_symm_smul,
      (adjointContinuousLinearMap (I := I) g).map_smul]

instance instContinuousConstSMul : ContinuousConstSMul G (AdjointLieAlgebra I G) where
  continuous_const_smul g :=
    (ofGroupLieAlgebra I G).continuous.comp <|
      (adjointContinuousLinearMap (I := I) g).continuous.comp
        (ofGroupLieAlgebra I G).symm.continuous

/-- On a commutative Lie group, the adjoint `G`-action on `AdjointLieAlgebra I G` is trivial. -/
@[simp]
theorem smul_eq_self [IsMulCommutative G] (g : G) (X : AdjointLieAlgebra I G) :
    g • X = X := by
  apply (ofGroupLieAlgebra I G).symm.injective
  rw [ofGroupLieAlgebra_symm_smul, adjointContinuousLinearMap_eq_id, ContinuousLinearMap.id_apply]

end Action

section BracketAction

variable [CompleteSpace E] [LieGroup I (minSmoothness 𝕜 3) G]

local instance lieGroupOne : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

/-- The adjoint `G`-action on `AdjointLieAlgebra I G` preserves the Lie bracket. -/
@[simp]
theorem smul_lie (g : G) (X Y : AdjointLieAlgebra I G) :
    g • ⁅X, Y⁆ = ⁅g • X, g • Y⁆ := by
  apply (ofGroupLieAlgebra I G).symm.injective
  rw [ofGroupLieAlgebra_symm_smul, ofGroupLieAlgebra_symm_lie, ofGroupLieAlgebra_symm_lie,
    ofGroupLieAlgebra_symm_smul, ofGroupLieAlgebra_symm_smul, adjointContinuousLinearMap_lie]

/-- The action of `g : G` on `AdjointLieAlgebra I G` packaged as a Lie-algebra automorphism. -/
def smulLieEquiv (g : G) : AdjointLieAlgebra I G ≃ₗ⁅𝕜⁆ AdjointLieAlgebra I G :=
  (lieEquiv I G).symm.trans ((tangentAd (I := I) g).trans (lieEquiv I G))

@[simp]
theorem smulLieEquiv_apply (g : G) (X : AdjointLieAlgebra I G) :
    smulLieEquiv g X = g • X := by
  apply (ofGroupLieAlgebra I G).symm.injective
  rw [smulLieEquiv, LieEquiv.trans_apply, LieEquiv.trans_apply, lieEquiv_apply,
    lieEquiv_symm_apply, ContinuousLinearEquiv.symm_apply_apply, tangentAd_apply,
    ofGroupLieAlgebra_symm_smul]

@[simp]
theorem smulLieEquiv_symm_apply (g : G) (X : AdjointLieAlgebra I G) :
    (smulLieEquiv g).symm X = g⁻¹ • X :=
  (smulLieEquiv g).symm_apply_eq.mpr (by simp)

@[simp]
theorem smulLieEquiv_one :
    smulLieEquiv (1 : G) = LieEquiv.refl (R := 𝕜) (L₁ := AdjointLieAlgebra I G) := by
  ext X
  simp

@[simp]
theorem smulLieEquiv_mul (g h : G) :
    smulLieEquiv (I := I) (g * h) = (smulLieEquiv h).trans (smulLieEquiv g) := by
  ext X
  simp [mul_smul]

@[simp]
theorem smulLieEquiv_inv (g : G) :
    smulLieEquiv (I := I) g⁻¹ = (smulLieEquiv g).symm := by
  ext X
  simp

end BracketAction

end AdjointLieAlgebra

section KillingForm

variable {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [CompleteSpace E] [LieGroup I (minSmoothness 𝕜 3) G]

local instance lieGroupOneKilling : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

/-- The Killing form on the tangent Lie algebra of a Lie group is invariant under the group
adjoint action `adjointContinuousLinearMap`. -/
theorem killingForm_adjointContinuousLinearMap (g : G) (X Y : GroupLieAlgebra I G) :
    killingForm 𝕜 (GroupLieAlgebra I G)
        (adjointContinuousLinearMap (I := I) g X)
        (adjointContinuousLinearMap (I := I) g Y) =
      killingForm 𝕜 (GroupLieAlgebra I G) X Y := by
  rw [← tangentAd_apply, ← tangentAd_apply]
  exact LieAlgebra.killingForm_of_equiv_apply (tangentAd (I := I) g) X Y

/-- The Killing form on `AdjointLieAlgebra I G` is invariant under the `G`-action. -/
@[simp]
theorem AdjointLieAlgebra.killingForm_smul (g : G) (X Y : AdjointLieAlgebra I G) :
    killingForm 𝕜 (AdjointLieAlgebra I G) (g • X) (g • Y) =
      killingForm 𝕜 (AdjointLieAlgebra I G) X Y := by
  rw [← smulLieEquiv_apply, ← smulLieEquiv_apply]
  exact LieAlgebra.killingForm_of_equiv_apply (AdjointLieAlgebra.smulLieEquiv g) X Y

end KillingForm

end GeneralField

section RealSmooth

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

namespace AdjointLieAlgebra

/-- For a real `C^∞` Lie group `G`, the adjoint action `(g, X) ↦ g • X` on
`AdjointLieAlgebra I G` is jointly `C^∞`. -/
theorem contMDiff_smul_adjointLieAlgebra :
    ContMDiff (I.prod 𝓘(ℝ, AdjointLieAlgebra I G)) 𝓘(ℝ, AdjointLieAlgebra I G) ∞
      (fun p : G × AdjointLieAlgebra I G ↦ p.1 • p.2) := by
  let L : E →L[ℝ] AdjointLieAlgebra I G := ofModel I G
  let Lsymm : AdjointLieAlgebra I G →L[ℝ] E := (ofModel I G).symm
  have hact := ((contMDiff_adjointContinuousLinearMap (I := I) (G := G)).comp
    contMDiff_fst).clm_apply (Lsymm.contMDiff.comp contMDiff_snd)
  exact (L.contMDiff.comp hact).congr fun _ ↦ rfl

/-- The adjoint action of a real `C^∞` Lie group on `AdjointLieAlgebra I G` is a `C^∞` smooth
action; Mathlib's monotonicity instances automatically supply `ContMDiffSMul` for every `n ≤ ∞`. -/
instance instContMDiffSMul :
    ContMDiffSMul I 𝓘(ℝ, AdjointLieAlgebra I G) ∞ G (AdjointLieAlgebra I G) where
  contMDiff_smul := contMDiff_smul_adjointLieAlgebra

/-- Joint continuity of the adjoint action of a real `C^∞` Lie group on
`AdjointLieAlgebra I G`. -/
instance instContinuousSMul : ContinuousSMul G (AdjointLieAlgebra I G) :=
  ContMDiffSMul.continuousSMul (I := I) (I' := 𝓘(ℝ, AdjointLieAlgebra I G)) ∞

end AdjointLieAlgebra

end RealSmooth

end TauCeti.Lie
