/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Lie.Adjoint.Action
public import TauCeti.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Pullback
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Associated.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# The adjoint bundle of a principal bundle

For a Lie group `G` modelled on `IG` and a principal `G`-bundle `P` over `B`, the *adjoint bundle*
`ad(P)` (`TauCeti.AdjointBundle IG G P`) is the associated vector bundle
`AssociatedBundle G P (TauCeti.Lie.AdjointLieAlgebra IG G)`.

Because `TauCeti.Lie.AdjointLieAlgebra.smul_lie` shows that the adjoint action of `G` acts by Lie
algebra automorphisms, the Lie bracket on `GroupLieAlgebra IG G` descends unambiguously to every
fibre `AdjointBundle IG G P b`, making each fibre a Lie algebra isomorphic to
`GroupLieAlgebra IG G` via any principal frame (`TauCeti.AdjointBundle.mkLieEquiv`). In finite
dimension over a complete field, the fibrewise Lie bracket varies `C^n`-smoothly in local bundle
charts (`ContMDiffWithinAt.lie_adjointBundle`), equipping bundled `C^n` sections with a Lie-algebra
structure and upgrading the associated-bundle section/equivariant-map correspondence to a Lie
isomorphism (`TauCeti.AdjointBundle.contMDiffSectionLieEquiv`).

We also prove pullback naturality (`TauCeti.AdjointBundle.pullbackLieEquiv`) and show that when `G`
is commutative, `AdjointBundle IG G P` is canonically trivial with frame-independent coordinates
(`TauCeti.AdjointBundle.trivialLieEquiv`, `TauCeti.AdjointBundle.trivialBundleDiffeomorph`) and
vanishing bracket, instantiated explicitly for principal `Circle`-bundles.

## Main definitions

* `TauCeti.AdjointBundle`: the adjoint bundle `P ×_G 𝔤` of a principal `G`-bundle `P`.
* `TauCeti.AdjointBundle.mk`: the class `[p, X]` in `AdjointBundle IG G P b` of `p : P b` and
  `X : GroupLieAlgebra IG G`.
* `TauCeti.AdjointBundle.mkContinuousLinearEquiv` and `TauCeti.AdjointBundle.mkLieEquiv`:
  continuous-linear and Lie-algebra identifications of `GroupLieAlgebra IG G` with a fibre via a
  principal frame.
* `TauCeti.AdjointBundle.EquivariantContMDiffMap` and
  `TauCeti.AdjointBundle.contMDiffSectionLieEquiv`: Lie-algebra isomorphism between `C^n` sections
  of `AdjointBundle IG G P` and `C^n` `Ad⁻¹`-equivariant maps `P → 𝔤`.
* `TauCeti.AdjointBundle.pullbackLieEquiv`: fibrewise Lie-algebra equivalence
  `AdjointBundle IG G (f *ᵖ P) x ≃ₗ⁅𝕜⁆ ((f *ᵖ (AdjointBundle IG G P)) x)`.
* `TauCeti.AdjointBundle.trivialLieEquiv`, `TauCeti.AdjointBundle.trivialBundleHomeomorph`, and
  `TauCeti.AdjointBundle.trivialBundleDiffeomorph`: canonical trivialization when `G` is
  commutative, together with `TauCeti.AdjointBundle.circleTrivialLinearEquiv` for `G = Circle`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5 and
  Chapter II, §§1–5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §§10.7, 10.12,
  10.18.
-/

public section

noncomputable section

open Bundle FiberBundle Filter MulOpposite Set
open scoped ContDiff Manifold Topology

namespace Bundle.Pullback

variable {B B' : Type*} {E : B → Type*} (f : B' → B)

/-- A pullback fibre inherits the bracket of the original fibre. -/
instance instBracket [∀ b, Bracket (E b) (E b)] (x : B') :
    Bracket ((f *ᵖ E) x) ((f *ᵖ E) x) :=
  inferInstanceAs (Bracket (E (f x)) (E (f x)))

/-- A pullback fibre inherits the Lie-ring structure of the original fibre. -/
instance instLieRing [∀ b, LieRing (E b)] (x : B') : LieRing ((f *ᵖ E) x) :=
  inferInstanceAs (LieRing (E (f x)))

/-- A pullback fibre inherits the Lie-algebra structure of the original fibre. -/
instance instLieAlgebra {R : Type*} [CommRing R] [∀ b, LieRing (E b)] [∀ b, LieAlgebra R (E b)]
    (x : B') : LieAlgebra R ((f *ᵖ E) x) :=
  inferInstanceAs (LieAlgebra R (E (f x)))

/-- Pullback preserves abelianness of Lie-algebra fibres. -/
instance instIsLieAbelian [∀ b, LieRing (E b)] [∀ b, IsLieAbelian (E b)] (x : B') :
    IsLieAbelian ((f *ᵖ E) x) :=
  inferInstanceAs (IsLieAbelian (E (f x)))

end Bundle.Pullback

namespace TauCeti

/-- The *adjoint bundle* `ad(P) = P ×_G 𝔤` of a principal `G`-bundle `P`, defined as the associated
bundle with model fibre `TauCeti.Lie.AdjointLieAlgebra IG G` carrying the group adjoint action. -/
abbrev AdjointBundle {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
    {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners 𝕜 EG HG)
    (G : Type*) [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG 1 G]
    [ContinuousSMul G (Lie.AdjointLieAlgebra IG G)]
    (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] : B → Type _ :=
  AssociatedBundle G P (Lie.AdjointLieAlgebra IG G)

namespace AdjointBundle

open TauCeti.Lie

section GeneralField

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]

section Classes

variable [LieGroup IG 1 G] [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

variable (IG G) in
/-- The class `[p, X]` in the adjoint bundle of a principal frame `p : P b` and a tangent Lie
algebra element `X : GroupLieAlgebra IG G`. -/
def mk {b : B} (p : P b) (X : GroupLieAlgebra IG G) : AdjointBundle IG G P b :=
  AssociatedBundle.mk G p (AdjointLieAlgebra.ofGroupLieAlgebra IG G X)

theorem mk_eq_associatedBundleMk {b : B} (p : P b) (X : GroupLieAlgebra IG G) :
    mk IG G p X = AssociatedBundle.mk G p (AdjointLieAlgebra.ofGroupLieAlgebra IG G X) := by
  rfl

/-- Right-translating the principal frame by `g` acts on the Lie-algebra coordinate by `Ad_g`. -/
@[simp]
theorem mk_smul {b : B} (p : P b) (g : G) (X : GroupLieAlgebra IG G) :
    mk IG G (op g • p) X = mk IG G p (adjointContinuousLinearMap (I := IG) g X) := by
  rw [mk_eq_associatedBundleMk, mk_eq_associatedBundleMk, AssociatedBundle.mk_smul,
    AdjointLieAlgebra.smul_ofGroupLieAlgebra]

/-- Invariance of `[p, X]` under simultaneous right translation of `p` by `g` and `Ad_{g⁻¹}` on
`X`. -/
theorem mk_smul_inv_adjoint {b : B} (p : P b) (g : G) (X : GroupLieAlgebra IG G) :
    mk IG G (op g • p) (adjointContinuousLinearMap (I := IG) g⁻¹ X) = mk IG G p X := by
  rw [mk_smul, ← ContinuousLinearMap.comp_apply, ← adjointContinuousLinearMap_mul,
    mul_inv_cancel, adjointContinuousLinearMap_one, ContinuousLinearMap.id_apply]

/-- Two classes over `b` coincide iff their Lie-algebra coordinates are related by `Ad` of the
principal division element. -/
theorem mk_eq_mk_iff {b : B} {p q : P b} {X Y : GroupLieAlgebra IG G} :
    mk IG G p X = mk IG G q Y ↔
      X = adjointContinuousLinearMap (I := IG) (PrincipalBundle.division G p q) Y := by
  rw [mk_eq_associatedBundleMk, mk_eq_associatedBundleMk, AssociatedBundle.mk_eq_mk_iff,
    AdjointLieAlgebra.smul_ofGroupLieAlgebra (I := IG),
    (AdjointLieAlgebra.ofGroupLieAlgebra IG G).injective.eq_iff]

/-- Every principal frame identifies `GroupLieAlgebra IG G` bijectively with the adjoint fibre. -/
theorem mk_bijective {b : B} (p : P b) :
    Function.Bijective (mk IG G p : GroupLieAlgebra IG G → AdjointBundle IG G P b) :=
  (AssociatedBundle.mk_bijective (F := AdjointLieAlgebra IG G) p).comp
    (AdjointLieAlgebra.ofGroupLieAlgebra IG G).bijective

/-- Every vector in `AdjointBundle IG G P b` is of the form `mk IG G p X` for some `p` and `X`. -/
theorem exists_mk {b : B} (u : AdjointBundle IG G P b) :
    ∃ (p : P b) (X : GroupLieAlgebra IG G), mk IG G p X = u := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  obtain ⟨X, hX⟩ := (mk_bijective p).surjective u
  exact ⟨p, X, hX⟩

@[simp]
theorem mk_add {b : B} (p : P b) (X Y : GroupLieAlgebra IG G) :
    mk IG G p (X + Y) = mk IG G p X + mk IG G p Y := by
  rw [mk_eq_associatedBundleMk, map_add, AssociatedBundle.mk_add]
  rfl

@[simp]
theorem mk_smul_scalar {b : B} (p : P b) (r : 𝕜) (X : GroupLieAlgebra IG G) :
    mk IG G p (r • X) = r • mk IG G p X := by
  rw [mk_eq_associatedBundleMk, map_smul, AssociatedBundle.mk_smul_scalar]
  rfl

@[simp]
theorem mk_zero {b : B} (p : P b) : mk IG G p (0 : GroupLieAlgebra IG G) = 0 := by
  rw [mk_eq_associatedBundleMk, map_zero, AssociatedBundle.mk_zero]

/-- In a preferred bundle chart at `b'`, the coordinate of `mk IG G p X` is `Ad_{(e p).2} X`. -/
theorem trivializationAt_mk_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (p : P b) (X : GroupLieAlgebra IG G) :
    (trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) b'
        ⟨b, mk IG G p X⟩).2 =
      AdjointLieAlgebra.ofGroupLieAlgebra IG G
        (adjointContinuousLinearMap (I := IG) (trivializationAt G P b' ⟨b, p⟩).2 X) := by
  rw [mk_eq_associatedBundleMk, AssociatedBundle.trivializationAt_mk_snd hb,
    AdjointLieAlgebra.smul_ofGroupLieAlgebra]

variable (𝕜 IG G) in
/-- Continuous linear equivalence from `GroupLieAlgebra IG G` to the adjoint fibre over `b`
determined by a principal frame `p : P b`. -/
def mkContinuousLinearEquiv {b : B} (p : P b) :
    GroupLieAlgebra IG G ≃L[𝕜] AdjointBundle IG G P b :=
  (AdjointLieAlgebra.ofGroupLieAlgebra IG G).trans
    (AssociatedBundle.mkContinuousLinearEquiv 𝕜 G p)

@[simp]
theorem mkContinuousLinearEquiv_apply {b : B} (p : P b) (X : GroupLieAlgebra IG G) :
    mkContinuousLinearEquiv 𝕜 IG G p X = mk IG G p X := by
  simp [mkContinuousLinearEquiv, mk_eq_associatedBundleMk]

@[simp]
theorem mkContinuousLinearEquiv_symm_apply_mk {b : B} (p q : P b) (X : GroupLieAlgebra IG G) :
    (mkContinuousLinearEquiv 𝕜 IG G p).symm (mk IG G q X) =
      adjointContinuousLinearMap (I := IG) (PrincipalBundle.division G p q) X := by
  simp only [mkContinuousLinearEquiv, ContinuousLinearEquiv.symm_trans_apply,
    mk_eq_associatedBundleMk, AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk,
    AdjointLieAlgebra.smul_ofGroupLieAlgebra, ContinuousLinearEquiv.symm_apply_apply]

end Classes

section LieAlgebraFibres

variable [CompleteSpace EG] [LieGroup IG (minSmoothness 𝕜 3) G]

local instance lieGroupOne : LieGroup IG 1 G :=
  LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

variable [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- The fibrewise Lie bracket on `AdjointBundle IG G P b`, defined via the frame of coordinate `1`
in the preferred chart at `b` and independent of the choice of frame by `mk_lie`. -/
instance instBracket (b : B) : Bracket (AdjointBundle IG G P b) (AdjointBundle IG G P b) where
  bracket u v :=
    let e₀ := AssociatedBundle.mkContinuousLinearEquiv 𝕜 G
      (F := AdjointLieAlgebra IG G) ((FiberBundle.homeomorphAt G P b).symm 1)
    e₀ ⁅e₀.symm u, e₀.symm v⁆

omit [CompleteSpace EG] in
private theorem bracket_def (b : B) (u v : AdjointBundle IG G P b) :
    ⁅u, v⁆ =
      let e₀ := AssociatedBundle.mkContinuousLinearEquiv 𝕜 G
        (F := AdjointLieAlgebra IG G) ((FiberBundle.homeomorphAt G P b).symm 1)
      e₀ ⁅e₀.symm u, e₀.symm v⁆ := by
  rfl

/-- In any principal frame `p : P b`, the associated-bundle class map preserves the Lie bracket. -/
@[simp]
theorem associatedBundleMk_lie {b : B} (p : P b) (X Y : AdjointLieAlgebra IG G) :
    ⁅AssociatedBundle.mk G (P := P) p X, AssociatedBundle.mk G (P := P) p Y⁆ =
      AssociatedBundle.mk G (P := P) p ⁅X, Y⁆ := by
  let p₀ : P b := (FiberBundle.homeomorphAt G P b).symm 1
  let e₀ := AssociatedBundle.mkContinuousLinearEquiv 𝕜 G (F := AdjointLieAlgebra IG G) p₀
  apply e₀.symm.injective
  rw [bracket_def]
  dsimp only
  rw [e₀.symm_apply_apply, AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk, AdjointLieAlgebra.smul_lie]

/-- In any principal frame `p : P b`, `AdjointBundle.mk` preserves the Lie bracket. -/
@[simp]
theorem mk_lie {b : B} (p : P b) (X Y : GroupLieAlgebra IG G) :
    ⁅mk IG G p X, mk IG G p Y⁆ = mk IG G p ⁅X, Y⁆ := by
  rw [mk_eq_associatedBundleMk, mk_eq_associatedBundleMk, mk_eq_associatedBundleMk,
    associatedBundleMk_lie, AdjointLieAlgebra.ofGroupLieAlgebra_lie]

/-- Formula for the fibrewise Lie bracket of classes presented in two possibly distinct frames
`p, q : P b`. -/
theorem mk_lie_mk {b : B} (p q : P b) (X Y : GroupLieAlgebra IG G) :
    ⁅mk IG G p X, mk IG G q Y⁆ =
      mk IG G p ⁅X, adjointContinuousLinearMap (I := IG) (PrincipalBundle.division G p q) Y⁆ := by
  have hq : mk IG G q Y =
      mk IG G p (adjointContinuousLinearMap (I := IG) (PrincipalBundle.division G p q) Y) :=
    (mk_eq_mk_iff.mpr rfl).symm
  rw [hq, mk_lie]

instance instLieRing (b : B) : LieRing (AdjointBundle IG G P b) where
  add_lie u v w := by
    let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    obtain ⟨Z, rfl⟩ := (mk_bijective p).surjective w
    rw [← mk_add, mk_lie, add_lie, mk_add, mk_lie, mk_lie]
  lie_add u v w := by
    let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    obtain ⟨Z, rfl⟩ := (mk_bijective p).surjective w
    rw [← mk_add, mk_lie, lie_add, mk_add, mk_lie, mk_lie]
  lie_self u := by
    let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    rw [mk_lie, lie_self, mk_zero]
  leibniz_lie u v w := by
    let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    obtain ⟨Z, rfl⟩ := (mk_bijective p).surjective w
    simp only [mk_lie]
    rw [leibniz_lie, mk_add]

instance instLieAlgebra (b : B) : LieAlgebra 𝕜 (AdjointBundle IG G P b) where
  lie_smul c u v := by
    let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    rw [← mk_smul_scalar, mk_lie, lie_smul, mk_smul_scalar, mk_lie]

instance instIsLieAbelian [IsLieAbelian (GroupLieAlgebra IG G)] (b : B) :
    IsLieAbelian (AdjointBundle IG G P b) where
  trivial u v := by
    let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    rw [mk_lie, LieModule.IsTrivial.trivial, mk_zero]

variable (𝕜 IG G) in
/-- Every principal frame `p : P b` identifies `GroupLieAlgebra IG G` with the fibre
`AdjointBundle IG G P b` as a `𝕜`-Lie algebra. -/
def mkLieEquiv {b : B} (p : P b) :
    GroupLieAlgebra IG G ≃ₗ⁅𝕜⁆ AdjointBundle IG G P b where
  toFun := mkContinuousLinearEquiv 𝕜 IG G p
  invFun := (mkContinuousLinearEquiv 𝕜 IG G p).symm
  left_inv := (mkContinuousLinearEquiv 𝕜 IG G p).left_inv
  right_inv := (mkContinuousLinearEquiv 𝕜 IG G p).right_inv
  map_add' := map_add (mkContinuousLinearEquiv 𝕜 IG G p)
  map_smul' := map_smul (mkContinuousLinearEquiv 𝕜 IG G p)
  map_lie' := fun {_ _} ↦ by simp

@[simp]
theorem mkLieEquiv_apply {b : B} (p : P b) (X : GroupLieAlgebra IG G) :
    mkLieEquiv 𝕜 IG G p X = mk IG G p X :=
  mkContinuousLinearEquiv_apply p X

@[simp]
theorem mkLieEquiv_symm_apply_mk {b : B} (p q : P b) (X : GroupLieAlgebra IG G) :
    (mkLieEquiv 𝕜 IG G p).symm (mk IG G q X) =
      adjointContinuousLinearMap (I := IG) (PrincipalBundle.division G p q) X :=
  mkContinuousLinearEquiv_symm_apply_mk p q X

/-- Every preferred associated-bundle trivialization preserves the Lie bracket on fibres over its
base set. -/
theorem trivializationAt_lie_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (u v : AdjointBundle IG G P b) :
    (trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) b' ⟨b, ⁅u, v⁆⟩).2 =
      ⁅(trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) b' ⟨b, u⟩).2,
        (trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) b' ⟨b, v⟩).2⁆ := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  obtain ⟨X, rfl⟩ :=
    (AssociatedBundle.mk_bijective (F := AdjointLieAlgebra IG G) p).surjective u
  obtain ⟨Y, rfl⟩ :=
    (AssociatedBundle.mk_bijective (F := AdjointLieAlgebra IG G) p).surjective v
  rw [associatedBundleMk_lie, AssociatedBundle.trivializationAt_mk_snd hb,
    AssociatedBundle.trivializationAt_mk_snd hb, AssociatedBundle.trivializationAt_mk_snd hb,
    AdjointLieAlgebra.smul_lie]

/-- On its base set, the preferred associated-bundle trivialization at `b'` gives a Lie-algebra
isomorphism from each fibre `AdjointBundle IG G P b` to `AdjointLieAlgebra IG G`. -/
def trivializationAtLieEquiv [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EG]
    {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet) :
    AdjointBundle IG G P b ≃ₗ⁅𝕜⁆ AdjointLieAlgebra IG G :=
  have hbA : b ∈ (trivializationAt (AdjointLieAlgebra IG G)
      (AdjointBundle IG G P) b').baseSet := by
    simpa only [AssociatedBundle.baseSet_trivializationAt] using hb
  let eL := (trivializationAt (AdjointLieAlgebra IG G)
    (AdjointBundle IG G P) b').linearEquivAt 𝕜 b hbA
  { toFun := eL
    invFun := eL.symm
    left_inv := eL.left_inv
    right_inv := eL.right_inv
    map_add' := map_add eL
    map_smul' := map_smul eL
    map_lie' := fun {u v} ↦ by
      simp only [eL, Trivialization.linearEquivAt_apply]
      exact trivializationAt_lie_snd hb u v }

end LieAlgebraFibres

section SmoothBracket

variable [CompleteSpace 𝕜] [CompleteSpace EG] [FiniteDimensional 𝕜 EG]
  [LieGroup IG (minSmoothness 𝕜 3) G]

local instance lieGroupOneSmooth : LieGroup IG 1 G :=
  LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

variable [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [ChartedSpace HB B]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {b : M → B} {u v : ∀ m, AdjointBundle IG G P (b m)} {s : Set M} {x : M}

/-- The fibrewise Lie bracket of two `C^n` maps into `AdjointBundle IG G P` over a common base map
is `C^n` within `s` at `x`. -/
theorem _root_.ContMDiffWithinAt.lie_adjointBundle
    (hu : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, ⁅u m, v m⁆⟩ :
        TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s x := by
  obtain ⟨hb, hu'⟩ := contMDiffWithinAt_totalSpace_iff.mp hu
  have hv' := (contMDiffWithinAt_totalSpace_iff.mp hv).2
  refine contMDiffWithinAt_totalSpace_iff.mpr ⟨hb, ?_⟩
  have hx := mem_baseSet_trivializationAt G P (b x)
  have hmem := hb.continuousWithinAt.preimage_mem_nhdsWithin
    ((trivializationAt G P (b x)).open_baseSet.mem_nhds hx)
  refine ((AdjointLieAlgebra.contDiff_lie (I := IG) (G := G) (n := n)).contMDiff.contMDiffAt
    |>.comp_contMDiffWithinAt x (hu'.prodMk_space hv')).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hmem] with y hy
    simpa only [Function.comp_apply] using
      trivializationAt_lie_snd (G := G) (P := P) hy (u y) (v y)
  · simpa only [Function.comp_apply] using
      trivializationAt_lie_snd (G := G) (P := P) hx (u x) (v x)

/-- Pointwise `C^n` version of `ContMDiffWithinAt.lie_adjointBundle`. -/
theorem _root_.ContMDiffAt.lie_adjointBundle
    (hu : ContMDiffAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, ⁅u m, v m⁆⟩ :
        TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) x := by
  rw [← contMDiffWithinAt_univ] at *
  exact hu.lie_adjointBundle hv

/-- Setwise `C^n` version of `ContMDiffWithinAt.lie_adjointBundle`. -/
theorem _root_.ContMDiffOn.lie_adjointBundle
    (hu : ContMDiffOn IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, ⁅u m, v m⁆⟩ :
        TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s :=
  fun x hx ↦ (hu x hx).lie_adjointBundle (hv x hx)

/-- Global `C^n` version of `ContMDiffWithinAt.lie_adjointBundle`: the fibrewise Lie bracket of
two `C^n` maps into `AdjointBundle IG G P` over a common base map is `C^n`. -/
theorem _root_.ContMDiff.lie_adjointBundle
    (hu : ContMDiff IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))))
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P)))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, ⁅u m, v m⁆⟩ :
        TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) :=
  fun x ↦ (hu x).lie_adjointBundle (hv x)

/-- Pointwise Lie bracket of bundled `C^n` sections of `AdjointBundle IG G P`. -/
instance instBracketContMDiffSection :
    Bracket Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯
      Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯ where
  bracket s t := ⟨fun b ↦ ⁅s b, t b⁆, s.contMDiff.lie_adjointBundle t.contMDiff⟩

@[simp]
theorem coe_lie (s t : Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯) :
    (⇑⁅s, t⁆ : ∀ b, AdjointBundle IG G P b) = fun b ↦ ⁅s b, t b⁆ := by
  rfl

@[simp]
theorem lie_apply (s t : Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯) (b : B) :
    ⁅s, t⁆ b = ⁅s b, t b⁆ := by
  rfl

instance instLieRingContMDiffSection :
    LieRing Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯ where
  add_lie s t u := by ext b; exact add_lie (s b) (t b) (u b)
  lie_add s t u := by ext b; exact lie_add (s b) (t b) (u b)
  lie_self s := by ext b; exact lie_self (s b)
  leibniz_lie s t u := by ext b; exact leibniz_lie (s b) (t b) (u b)

instance instLieAlgebraContMDiffSection :
    LieAlgebra 𝕜 Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯ where
  lie_smul c s t := by ext b; exact lie_smul c (s b) (t b)

instance instIsLieAbelianContMDiffSection [IsLieAbelian (GroupLieAlgebra IG G)] :
    IsLieAbelian Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯ where
  trivial s t := by ext b; exact LieModule.IsTrivial.trivial (s b) (t b)

end SmoothBracket

section EquivariantMap

variable {n : ℕ∞ω} {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]

/-- Bundled `C^n` maps `u : ManifoldTotalSpace G P → AdjointLieAlgebra IG G` satisfying the
`Ad⁻¹`-equivariance law `u (p • g) = g⁻¹ • u p`. -/
structure EquivariantContMDiffMap (IB : ModelWithCorners 𝕜 EB HB) [ChartedSpace HB B]
    (IG : ModelWithCorners 𝕜 EG HG)
    (G : Type*) [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG 1 G]
    (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]
    (n : ℕ∞ω) where
  /-- The underlying map on `ManifoldTotalSpace G P`. -/
  toFun : ManifoldTotalSpace G P → AdjointLieAlgebra IG G
  /-- `C^n` smoothness on the manifold total space of `P`. -/
  contMDiff_toFun : ContMDiff (IB.prod IG) 𝓘(𝕜, AdjointLieAlgebra IG G) n toFun
  /-- Inverse-equivariance under the right principal action of `G`. -/
  map_smul_op' : ∀ (b : B) (p : P b) (g : G),
    toFun (ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) =
      g⁻¹ • toFun (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩)

namespace EquivariantContMDiffMap

variable {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]

section Algebraic

variable [LieGroup IG 1 G]

instance instDFunLike :
    DFunLike (EquivariantContMDiffMap IB IG G P n)
      (ManifoldTotalSpace G P) (fun _ ↦ AdjointLieAlgebra IG G) where
  coe := toFun
  coe_injective := by rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl; rfl

@[ext]
theorem ext {u v : EquivariantContMDiffMap IB IG G P n} (h : ∀ p, u p = v p) : u = v :=
  DFunLike.ext u v h

@[simp]
theorem map_smul_op (u : EquivariantContMDiffMap IB IG G P n) (b : B) (p : P b) (g : G) :
    u (ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) =
      g⁻¹ • u (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩) :=
  u.map_smul_op' b p g

instance instZero : Zero (EquivariantContMDiffMap IB IG G P n) :=
  ⟨⟨0, contMDiff_const, fun _ _ _ ↦ by simp⟩⟩

instance instAdd : Add (EquivariantContMDiffMap IB IG G P n) :=
  ⟨fun u v ↦ ⟨u + v, u.contMDiff_toFun.add v.contMDiff_toFun, fun b p g ↦ by
    simp [smul_add]⟩⟩

instance instNeg : Neg (EquivariantContMDiffMap IB IG G P n) :=
  ⟨fun u ↦ ⟨-u, u.contMDiff_toFun.neg, fun b p g ↦ by simp⟩⟩

instance instSub : Sub (EquivariantContMDiffMap IB IG G P n) :=
  ⟨fun u v ↦ ⟨u - v, u.contMDiff_toFun.sub v.contMDiff_toFun, fun b p g ↦ by
    simp [smul_sub]⟩⟩

instance instSMulNat : SMul ℕ (EquivariantContMDiffMap IB IG G P n) :=
  ⟨nsmulRec⟩

instance instSMulInt : SMul ℤ (EquivariantContMDiffMap IB IG G P n) :=
  ⟨zsmulRec⟩

instance instSMul : SMul 𝕜 (EquivariantContMDiffMap IB IG G P n) :=
  ⟨fun c u ↦
    ⟨c • ⇑u,
      ((ContinuousLinearMap.lsmul 𝕜 𝕜 c :
          AdjointLieAlgebra IG G →L[𝕜] AdjointLieAlgebra IG G).contMDiff.comp
        u.contMDiff_toFun),
      fun b p g ↦ by
        simp only [Pi.smul_apply, u.map_smul_op b p g]
        exact (smul_comm g⁻¹ c _).symm⟩⟩

@[simp]
theorem coe_zero : ⇑(0 : EquivariantContMDiffMap IB IG G P n) = 0 := by
  rfl

@[simp]
theorem coe_add (u v : EquivariantContMDiffMap IB IG G P n) : ⇑(u + v) = ⇑u + ⇑v := by
  rfl

@[simp]
theorem coe_neg (u : EquivariantContMDiffMap IB IG G P n) : ⇑(-u) = -⇑u := by
  rfl

@[simp]
theorem coe_sub (u v : EquivariantContMDiffMap IB IG G P n) : ⇑(u - v) = ⇑u - ⇑v := by
  rfl

@[simp]
theorem coe_nsmul (k : ℕ) (u : EquivariantContMDiffMap IB IG G P n) : ⇑(k • u) = k • ⇑u := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

@[simp]
theorem coe_zsmul (z : ℤ) (u : EquivariantContMDiffMap IB IG G P n) : ⇑(z • u) = z • ⇑u := by
  rcases z with k | k
  · refine (coe_nsmul k u).trans ?_
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
  · refine congr(-$(coe_nsmul (k + 1) u)).trans ?_
    simp only [negSucc_zsmul]

@[simp]
theorem coe_smul (c : 𝕜) (u : EquivariantContMDiffMap IB IG G P n) : ⇑(c • u) = c • ⇑u := by
  rfl

instance instAddCommGroup : AddCommGroup (EquivariantContMDiffMap IB IG G P n) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun u k ↦ coe_nsmul k u) (fun u z ↦ coe_zsmul z u)

instance instModule : Module 𝕜 (EquivariantContMDiffMap IB IG G P n) :=
  DFunLike.coe_injective.module 𝕜
    { toFun := (⇑), map_zero' := coe_zero, map_add' := coe_add } coe_smul

end Algebraic

section Lie

variable [CompleteSpace 𝕜] [CompleteSpace EG] [FiniteDimensional 𝕜 EG]
  [LieGroup IG (minSmoothness 𝕜 3) G]

local instance lieGroupOneEqv : LieGroup IG 1 G :=
  LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

instance instBracket :
    Bracket (EquivariantContMDiffMap IB IG G P n) (EquivariantContMDiffMap IB IG G P n) where
  bracket u v :=
    ⟨fun p ↦ ⁅u p, v p⁆,
      (AdjointLieAlgebra.contDiff_lie (I := IG) (G := G) (n := n)).contMDiff.comp
        (u.contMDiff_toFun.prodMk_space v.contMDiff_toFun),
      fun b p g ↦ by simp⟩

@[simp]
theorem lie_apply (u v : EquivariantContMDiffMap IB IG G P n) (p : ManifoldTotalSpace G P) :
    ⁅u, v⁆ p = ⁅u p, v p⁆ := by
  rfl

instance instLieRing : LieRing (EquivariantContMDiffMap IB IG G P n) where
  add_lie u v w := by ext p; exact add_lie (u p) (v p) (w p)
  lie_add u v w := by ext p; exact lie_add (u p) (v p) (w p)
  lie_self u := by ext p; exact lie_self (u p)
  leibniz_lie u v w := by ext p; exact leibniz_lie (u p) (v p) (w p)

instance instLieAlgebra : LieAlgebra 𝕜 (EquivariantContMDiffMap IB IG G P n) where
  lie_smul c u v := by ext p; exact lie_smul c (u p) (v p)

end Lie

end EquivariantContMDiffMap

end EquivariantMap

section SectionCorrespondence

variable [CompleteSpace 𝕜] [CompleteSpace EG] [FiniteDimensional 𝕜 EG]
  [LieGroup IG (minSmoothness 𝕜 3) G]

local instance lieGroupOneSec : LieGroup IG 1 G :=
  LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

variable [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EG] in
/-- The inverse-equivariant representing function of a pointwise sum of sections is the sum of
their representing functions. -/
@[simp]
theorem sectionFunction_add (s t : ∀ b, AdjointBundle IG G P b) (p : TotalSpace G P) :
    AssociatedBundle.sectionFunction (fun b ↦ s b + t b) p =
      AssociatedBundle.sectionFunction s p + AssociatedBundle.sectionFunction t p := by
  rcases p with ⟨b, q⟩
  apply (AssociatedBundle.mk_bijective (G := G) (P := P)
    (F := AdjointLieAlgebra IG G) q).injective
  rw [AssociatedBundle.mk_sectionFunction (G := G) (P := P), AssociatedBundle.mk_add,
    AssociatedBundle.mk_sectionFunction (G := G) (P := P),
    AssociatedBundle.mk_sectionFunction (G := G) (P := P)]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EG] in
/-- The inverse-equivariant representing function of a scalar multiple of a section is the scalar
multiple of its representing function. -/
@[simp]
theorem sectionFunction_smul_scalar (c : 𝕜) (s : ∀ b, AdjointBundle IG G P b)
    (p : TotalSpace G P) :
    AssociatedBundle.sectionFunction (fun b ↦ c • s b) p =
      c • AssociatedBundle.sectionFunction s p := by
  rcases p with ⟨b, q⟩
  apply (AssociatedBundle.mk_bijective (G := G) (P := P)
    (F := AdjointLieAlgebra IG G) q).injective
  rw [AssociatedBundle.mk_sectionFunction (G := G) (P := P), AssociatedBundle.mk_smul_scalar,
    AssociatedBundle.mk_sectionFunction (G := G) (P := P)]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EG] in
/-- The inverse-equivariant representing function of the pointwise bracket of two sections is the
pointwise Lie bracket of their representing functions. -/
@[simp]
theorem sectionFunction_lie (s t : ∀ b, AdjointBundle IG G P b) (p : TotalSpace G P) :
    AssociatedBundle.sectionFunction (fun b ↦ ⁅s b, t b⁆) p =
      ⁅AssociatedBundle.sectionFunction s p, AssociatedBundle.sectionFunction t p⁆ := by
  rcases p with ⟨b, q⟩
  apply (AssociatedBundle.mk_bijective (G := G) (P := P)
    (F := AdjointLieAlgebra IG G) q).injective
  rw [AssociatedBundle.mk_sectionFunction (G := G) (P := P), ← associatedBundleMk_lie,
    AssociatedBundle.mk_sectionFunction (G := G) (P := P),
    AssociatedBundle.mk_sectionFunction (G := G) (P := P)]

section SmoothSectionCorrespondence

variable {n : ℕ∞ω} {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  [LieGroup IG n G]
  [ContMDiffSMul IG 𝓘(𝕜, AdjointLieAlgebra IG G) n G (AdjointLieAlgebra IG G)]

/-- The associated-bundle correspondence upgrades to a Lie-algebra isomorphism between bundled
`C^n` sections of `AdjointBundle IG G P` and bundled `C^n` `Ad⁻¹`-equivariant maps `P → 𝔤`. -/
def contMDiffSectionLieEquiv :
    Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯ ≃ₗ⁅𝕜⁆
      EquivariantContMDiffMap IB IG G P n :=
  let toSubtype (s : Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯) :
      {s : ∀ b, AdjointBundle IG G P b //
        ContMDiff IB (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n fun b ↦
          ManifoldTotalSpace.homeomorph (AdjointLieAlgebra IG G)
            (AdjointBundle IG G P) ⟨b, s b⟩} :=
    ⟨s, (ManifoldTotalSpace.contMDiff_homeomorph n (AdjointLieAlgebra IG G)
      (AdjointBundle IG G P) IB).comp s.contMDiff⟩
  let fromSubtype
      (s : {s : ∀ b, AdjointBundle IG G P b //
        ContMDiff IB (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n fun b ↦
          ManifoldTotalSpace.homeomorph (AdjointLieAlgebra IG G)
            (AdjointBundle IG G P) ⟨b, s b⟩}) :
      Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯ :=
    ⟨s.1, ((ManifoldTotalSpace.contMDiff_homeomorph_symm n (AdjointLieAlgebra IG G)
      (AdjointBundle IG G P) IB).comp s.2).congr fun b ↦
        ((ManifoldTotalSpace.homeomorph (AdjointLieAlgebra IG G)
          (AdjointBundle IG G P)).symm_apply_apply ⟨b, s.1 b⟩).symm⟩
  { toFun s :=
      ⟨fun p ↦ AssociatedBundle.sectionFunction s ((ManifoldTotalSpace.homeomorph G P).symm p),
        AssociatedBundle.contMDiff_sectionFunction s (toSubtype s).2,
        fun b p g ↦ by
          simp only [Homeomorph.symm_apply_apply, AssociatedBundle.sectionFunction_smul]⟩
    invFun u := fromSubtype ((AssociatedBundle.contMDiffSectionEquiv (IG := IG)
      (IF := 𝓘(𝕜, AdjointLieAlgebra IG G))).symm ⟨u, u.contMDiff_toFun, u.map_smul_op'⟩)
    left_inv s := by
      ext b
      let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
      refine (AssociatedBundle.contMDiffSectionEquiv_symm_apply _ p).trans ?_
      change AssociatedBundle.mk G p
        (AssociatedBundle.sectionFunction s
          ((ManifoldTotalSpace.homeomorph G P).symm
            (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩))) = s b
      rw [Homeomorph.symm_apply_apply, AssociatedBundle.mk_sectionFunction]
    right_inv u := by
      ext p
      change AssociatedBundle.sectionFunction
        ((AssociatedBundle.contMDiffSectionEquiv (IG := IG)
          (IF := 𝓘(𝕜, AdjointLieAlgebra IG G))).symm ⟨u, u.contMDiff_toFun, u.map_smul_op'⟩).1
        ((ManifoldTotalSpace.homeomorph G P).symm p) = u p
      rw [AssociatedBundle.contMDiffSectionEquiv_symm_val,
        AssociatedBundle.sectionFunction_sectionEquiv_symm]
      exact congrArg u ((ManifoldTotalSpace.homeomorph G P).apply_symm_apply p)
    map_add' s t := by
      ext p
      exact sectionFunction_add s t ((ManifoldTotalSpace.homeomorph G P).symm p)
    map_smul' c s := by
      ext p
      exact sectionFunction_smul_scalar c s ((ManifoldTotalSpace.homeomorph G P).symm p)
    map_lie' {s t} := by
      ext p
      exact sectionFunction_lie s t ((ManifoldTotalSpace.homeomorph G P).symm p) }

@[simp]
theorem contMDiffSectionLieEquiv_apply
    (s : Cₛ^n⟮IB; AdjointLieAlgebra IG G, AdjointBundle IG G P⟯)
    (p : ManifoldTotalSpace G P) :
    contMDiffSectionLieEquiv (IB := IB) s p =
      AssociatedBundle.sectionFunction s ((ManifoldTotalSpace.homeomorph G P).symm p) := by
  rfl

/-- Evaluate the inverse of `contMDiffSectionLieEquiv` in any principal frame `p : P b`. -/
theorem contMDiffSectionLieEquiv_symm_apply
    (u : EquivariantContMDiffMap IB IG G P n) {b : B} (p : P b) :
    (contMDiffSectionLieEquiv (IB := IB)).symm u b =
      mk IG G p ((AdjointLieAlgebra.ofGroupLieAlgebra IG G).symm
        (u (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩))) := by
  rw [mk_eq_associatedBundleMk, ContinuousLinearEquiv.apply_symm_apply]
  exact AssociatedBundle.contMDiffSectionEquiv_symm_apply ⟨u, u.contMDiff_toFun, u.map_smul_op'⟩ p

end SmoothSectionCorrespondence

end SectionCorrespondence

section Pullback

variable [CompleteSpace EG] [LieGroup IG (minSmoothness 𝕜 3) G]

local instance lieGroupOnePull : LieGroup IG 1 G :=
  LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

variable [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {B' : Type*} [TopologicalSpace B']
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K)

omit [CompleteSpace EG] in
private theorem pullbackEquiv_mk_aux (x : B') (p : P (f x)) (X : GroupLieAlgebra IG G) :
    AssociatedBundle.pullbackEquiv f x
      (mk IG G (P := (f : B' → B) *ᵖ P) (b := x) p X) =
      (mk IG G (P := P) p X : ((f : B' → B) *ᵖ (AdjointBundle IG G P)) x) := by
  have h1 := mk_eq_associatedBundleMk (IG := IG) (G := G) (P := (f : B' → B) *ᵖ P) (b := x) p X
  have h2 := mk_eq_associatedBundleMk (IG := IG) (G := G) (P := P) p X
  rw [h1]
  exact (AssociatedBundle.pullbackEquiv_mk f x p _).trans h2.symm

/-- Forming the adjoint bundle commutes with pullback of principal bundles: the canonical
associated-bundle comparison `AssociatedBundle.pullbackEquiv` is a `𝕜`-Lie algebra isomorphism on
every fibre. -/
def pullbackLieEquiv (x : B') :
    AdjointBundle IG G ((f : B' → B) *ᵖ P) x ≃ₗ⁅𝕜⁆
      ((f : B' → B) *ᵖ (AdjointBundle IG G P)) x where
  toFun := AssociatedBundle.pullbackEquiv f x
  invFun := (AssociatedBundle.pullbackEquiv f x).symm
  left_inv := (AssociatedBundle.pullbackEquiv f x).left_inv
  right_inv := (AssociatedBundle.pullbackEquiv f x).right_inv
  map_add' u v := by
    let p : ((f : B' → B) *ᵖ P) x := (FiberBundle.homeomorphAt G P (f x)).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    rw [← mk_add, pullbackEquiv_mk_aux, pullbackEquiv_mk_aux, pullbackEquiv_mk_aux]
    exact mk_add (P := P) p X Y
  map_smul' c u := by
    let p : ((f : B' → B) *ᵖ P) x := (FiberBundle.homeomorphAt G P (f x)).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    rw [← mk_smul_scalar, pullbackEquiv_mk_aux, pullbackEquiv_mk_aux]
    exact mk_smul_scalar (P := P) p c X
  map_lie' {u v} := by
    let p : ((f : B' → B) *ᵖ P) x := (FiberBundle.homeomorphAt G P (f x)).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    rw [mk_lie, pullbackEquiv_mk_aux, pullbackEquiv_mk_aux, pullbackEquiv_mk_aux]
    exact (mk_lie (P := P) p X Y).symm

@[simp]
theorem coe_pullbackLieEquiv (x : B') (u : AdjointBundle IG G ((f : B' → B) *ᵖ P) x) :
    pullbackLieEquiv f x u = AssociatedBundle.pullbackEquiv f x u := by
  rfl

@[simp]
theorem coe_pullbackLieEquiv_symm (x : B') (u : ((f : B' → B) *ᵖ (AdjointBundle IG G P)) x) :
    (pullbackLieEquiv f x).symm u = (AssociatedBundle.pullbackEquiv f x).symm u := by
  rfl

/-- `pullbackLieEquiv` sends the class `[p, X]` in the pulled-back principal bundle to `[p, X]` in
the pulled-back adjoint bundle. -/
theorem pullbackLieEquiv_mk (x : B') (p : P (f x)) (X : GroupLieAlgebra IG G) :
    pullbackLieEquiv f x (mk IG G (P := (f : B' → B) *ᵖ P) (b := x) p X) =
      (mk IG G (P := P) p X : ((f : B' → B) *ᵖ (AdjointBundle IG G P)) x) :=
  pullbackEquiv_mk_aux f x p X

@[simp]
theorem pullbackLieEquiv_symm_mk (x : B') (p : P (f x)) (X : GroupLieAlgebra IG G) :
    (pullbackLieEquiv f x).symm
      (mk IG G (P := P) p X : ((f : B' → B) *ᵖ (AdjointBundle IG G P)) x) =
      mk IG G (P := (f : B' → B) *ᵖ P) (b := x) p X :=
  (pullbackLieEquiv f x).symm_apply_eq.mpr (pullbackLieEquiv_mk f x p X).symm

/-- The total-space homeomorphism `AssociatedBundle.pullbackHomeomorph` preserves fibrewise Lie
brackets over every base point. -/
theorem pullbackHomeomorph_lie (x : B') (u v : AdjointBundle IG G ((f : B' → B) *ᵖ P) x) :
    AssociatedBundle.pullbackHomeomorph f ⟨x, ⁅u, v⁆⟩ =
      ⟨x, ⁅pullbackLieEquiv f x u, pullbackLieEquiv f x v⁆⟩ :=
  (AssociatedBundle.pullbackHomeomorph_apply f ⟨x, ⁅u, v⁆⟩).trans
    (congrArg (TotalSpace.mk x) ((pullbackLieEquiv f x).map_lie' (x := u) (y := v)))

end Pullback

section Commutative

variable [LieGroup IG 1 G] [ContinuousSMul G (AdjointLieAlgebra IG G)] [IsMulCommutative G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- When `G` is commutative, `[p, X]` is independent of the choice of principal frame `p : P b`. -/
theorem mk_eq_of_isMulCommutative {b : B} (p q : P b) (X : GroupLieAlgebra IG G) :
    mk IG G p X = mk IG G q X := by
  rw [mk_eq_mk_iff, adjointContinuousLinearMap_eq_id, ContinuousLinearMap.id_apply]

variable (𝕜 IG G P) in
/-- When `G` is commutative, every fibre of `AdjointBundle IG G P` is canonically continuously
linearly equivalent to `GroupLieAlgebra IG G`, independently of any choice of frame. -/
def trivialContinuousLinearEquiv (b : B) :
    AdjointBundle IG G P b ≃L[𝕜] GroupLieAlgebra IG G :=
  (mkContinuousLinearEquiv 𝕜 IG G ((FiberBundle.homeomorphAt G P b).symm (1 : G))).symm

@[simp]
theorem trivialContinuousLinearEquiv_mk {b : B} (p : P b) (X : GroupLieAlgebra IG G) :
    trivialContinuousLinearEquiv 𝕜 IG G P b (mk IG G p X) = X := by
  rw [trivialContinuousLinearEquiv, mkContinuousLinearEquiv_symm_apply_mk,
    adjointContinuousLinearMap_eq_id, ContinuousLinearMap.id_apply]

/-- For a commutative Lie group `G`, the inverse of `trivialContinuousLinearEquiv` equals
`mk IG G p` for any principal frame `p : P b`. -/
theorem trivialContinuousLinearEquiv_symm_apply {b : B} (p : P b) (X : GroupLieAlgebra IG G) :
    (trivialContinuousLinearEquiv 𝕜 IG G P b).symm X = mk IG G p X := by
  apply (trivialContinuousLinearEquiv 𝕜 IG G P b).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, trivialContinuousLinearEquiv_mk]

/-- On a commutative Lie group, every preferred trivialization of `AdjointBundle IG G P` reads the
canonical frame-independent coordinate in `AdjointLieAlgebra IG G`. -/
@[simp]
theorem trivializationAt_snd_eq_of_isMulCommutative {b' b : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (u : AdjointBundle IG G P b) :
    (trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) b' ⟨b, u⟩).2 =
      AdjointLieAlgebra.ofGroupLieAlgebra IG G
        (trivialContinuousLinearEquiv 𝕜 IG G P b u) := by
  obtain ⟨p, X, rfl⟩ := exists_mk u
  rw [trivializationAt_mk_snd hb, adjointContinuousLinearMap_eq_id, ContinuousLinearMap.id_apply,
    trivialContinuousLinearEquiv_mk]

variable (IG G P) in
/-- When `G` is commutative, the total space of `AdjointBundle IG G P` is canonically homeomorphic
over `B` to the trivial bundle `Bundle.Trivial B (AdjointLieAlgebra IG G)`. -/
def trivialBundleHomeomorph :
    TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P) ≃ₜ
      TotalSpace (AdjointLieAlgebra IG G)
        (Bundle.Trivial B (AdjointLieAlgebra IG G)) where
  toFun z := ⟨z.proj, AdjointLieAlgebra.ofGroupLieAlgebra IG G
    (trivialContinuousLinearEquiv 𝕜 IG G P z.proj z.2)⟩
  invFun z := ⟨z.proj, (trivialContinuousLinearEquiv 𝕜 IG G P z.proj).symm
    ((AdjointLieAlgebra.ofGroupLieAlgebra IG G).symm z.2)⟩
  left_inv z := by
    rcases z with ⟨b, u⟩
    simp
  right_inv z := by
    rcases z with ⟨b, v⟩
    simp
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    refine (FiberBundle.continuousAt_totalSpace _ _).mpr
      ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
    have hz := mem_baseSet_trivializationAt G P z.proj
    have hcoord := ((trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P)
      z.proj).continuousAt (by
        simpa only [Trivialization.mem_source, AssociatedBundle.baseSet_trivializationAt]
          using hz)).snd
    refine hcoord.congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt
      ((trivializationAt G P z.proj).open_baseSet.mem_nhds hz)] with y hy
    simpa using (trivializationAt_snd_eq_of_isMulCommutative (𝕜 := 𝕜) hy y.2).symm
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    refine (FiberBundle.continuousAt_totalSpace _ _).mpr
      ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
    have hz := mem_baseSet_trivializationAt G P z.proj
    have hcoord : ContinuousAt
        (fun y : TotalSpace (AdjointLieAlgebra IG G)
            (Bundle.Trivial B (AdjointLieAlgebra IG G)) ↦
          (Bundle.Trivial.trivialization B (AdjointLieAlgebra IG G) y).2) z :=
      ((Bundle.Trivial.trivialization B (AdjointLieAlgebra IG G)).continuousAt (by simp)).snd
    refine hcoord.congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt
      ((trivializationAt G P z.proj).open_baseSet.mem_nhds hz)] with y hy
    rcases y with ⟨b, v⟩
    simp [trivializationAt_snd_eq_of_isMulCommutative (𝕜 := 𝕜) hy]

@[simp]
theorem trivialBundleHomeomorph_proj
    (z : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P)) :
    (trivialBundleHomeomorph (𝕜 := 𝕜) IG G P z).proj = z.proj := by
  rfl

@[simp]
theorem trivialBundleHomeomorph_symm_proj
    (z : TotalSpace (AdjointLieAlgebra IG G) (Bundle.Trivial B (AdjointLieAlgebra IG G))) :
    ((trivialBundleHomeomorph (𝕜 := 𝕜) IG G P).symm z).proj = z.proj := by
  rfl

@[simp]
theorem trivialBundleHomeomorph_mk (b : B) (p : P b) (X : GroupLieAlgebra IG G) :
    trivialBundleHomeomorph (𝕜 := 𝕜) IG G P ⟨b, mk IG G p X⟩ =
      ⟨b, AdjointLieAlgebra.ofGroupLieAlgebra IG G X⟩ := by
  simp [trivialBundleHomeomorph]

section CommutativeLie

variable [CompleteSpace EG] [LieGroup IG (minSmoothness 𝕜 3) G]

variable (𝕜 IG G P) in
/-- When `G` is commutative, every fibre of `AdjointBundle IG G P` is canonically isomorphic as a
`𝕜`-Lie algebra to `GroupLieAlgebra IG G`, independently of any choice of frame. -/
def trivialLieEquiv (b : B) :
    AdjointBundle IG G P b ≃ₗ⁅𝕜⁆ GroupLieAlgebra IG G where
  toFun := trivialContinuousLinearEquiv 𝕜 IG G P b
  invFun := (trivialContinuousLinearEquiv 𝕜 IG G P b).symm
  left_inv := (trivialContinuousLinearEquiv 𝕜 IG G P b).left_inv
  right_inv := (trivialContinuousLinearEquiv 𝕜 IG G P b).right_inv
  map_add' := map_add (trivialContinuousLinearEquiv 𝕜 IG G P b)
  map_smul' := map_smul (trivialContinuousLinearEquiv 𝕜 IG G P b)
  map_lie' := fun {u v} ↦ by
    obtain ⟨p, X, rfl⟩ := exists_mk u
    obtain ⟨q, Y, rfl⟩ := exists_mk v
    rw [mk_eq_of_isMulCommutative q p Y, mk_lie, trivialContinuousLinearEquiv_mk,
      trivialContinuousLinearEquiv_mk, trivialContinuousLinearEquiv_mk]

@[simp]
theorem trivialLieEquiv_mk {b : B} (p : P b) (X : GroupLieAlgebra IG G) :
    trivialLieEquiv 𝕜 IG G P b (mk IG G p X) = X :=
  trivialContinuousLinearEquiv_mk p X

end CommutativeLie

end Commutative

end GeneralField

section RealSmooth

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {B : Type*} [TopologicalSpace B]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- For a finite-dimensional real `C^∞` Lie group `G` and a `C^n` principal `G`-bundle `P`
(`n ≤ ∞`), `AdjointBundle IG G P` is a native `C^n` vector bundle; `ContMDiffFiberBundle` follows
automatically via `ContMDiffFiberBundle.ofContMDiffVectorBundle`. -/
instance instContMDiffVectorBundle {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffFiberBundle n G P IB IG] :
    ContMDiffVectorBundle n (AdjointLieAlgebra IG G) (AdjointBundle IG G P) IB :=
  AssociatedBundle.contMDiffVectorBundle IG

section CommutativeReal

variable [IsMulCommutative G]

variable (IB IG G P) in
/-- When `G` is a commutative finite-dimensional real Lie group and `P` is a principal `G`-bundle,
`AdjointBundle IG G P` is canonically `C^n`-diffeomorphic in its total-space manifold chart to the
trivial bundle `B × 𝔤`. -/
def trivialBundleDiffeomorph {n : ℕ∞ω} :
    TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P) ≃ₘ^n⟮
        IB.prod 𝓘(ℝ, AdjointLieAlgebra IG G),
        IB.prod 𝓘(ℝ, AdjointLieAlgebra IG G)⟯
      TotalSpace (AdjointLieAlgebra IG G)
        (Bundle.Trivial B (AdjointLieAlgebra IG G)) where
  toEquiv := (trivialBundleHomeomorph (𝕜 := ℝ) IG G P).toEquiv
  contMDiff_toFun := by
    intro z
    rw [Bundle.Trivial.contMDiffAt_mk_iff]
    refine ⟨Bundle.contMDiffAt_proj (AdjointBundle IG G P), ?_⟩
    have hz := mem_baseSet_trivializationAt G P z.proj
    have hcoord := (Bundle.contMDiffAt_totalSpace_iff.mp
      (contMDiffAt_id (I := IB.prod 𝓘(ℝ, AdjointLieAlgebra IG G)) (n := n) (x := z))).2
    refine hcoord.congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt
      ((trivializationAt G P z.proj).open_baseSet.mem_nhds hz)] with y hy
    simpa [trivialBundleHomeomorph] using
      (trivializationAt_snd_eq_of_isMulCommutative (𝕜 := ℝ) hy y.2).symm
  contMDiff_invFun := by
    intro z
    refine Bundle.contMDiffAt_totalSpace_iff.mpr
      ⟨Bundle.contMDiffAt_proj (Bundle.Trivial B (AdjointLieAlgebra IG G)), ?_⟩
    have hz := mem_baseSet_trivializationAt G P z.proj
    have hcoord := (Bundle.contMDiffAt_totalSpace_iff.mp
      (contMDiffAt_id (I := IB.prod 𝓘(ℝ, AdjointLieAlgebra IG G)) (n := n) (x := z))).2
    refine hcoord.congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt
      ((trivializationAt G P z.proj).open_baseSet.mem_nhds hz)] with y hy
    rcases y with ⟨b, v⟩
    simp [trivialBundleHomeomorph, trivializationAt_snd_eq_of_isMulCommutative (𝕜 := ℝ) hy]

/-- When `G` is a boundaryless commutative real `C^∞` Lie group, every fibre of
`AdjointBundle IG G P` is an abelian Lie algebra. -/
instance instIsLieAbelianOfIsMulCommutative [BoundarylessManifold IG G] (b : B) :
    IsLieAbelian (AdjointBundle IG G P b) := by
  let _ : T2Space G := IG.t2Space_of_lieGroup ∞
  have : IsLieAbelian (GroupLieAlgebra IG G) :=
    isLieAbelian_groupLieAlgebra_of_isMulCommutative (I := IG) (G := G)
  infer_instance

/-- On a boundaryless commutative real `C^∞` Lie group, the fibrewise Lie bracket on
`AdjointBundle IG G P` vanishes identically. -/
@[simp]
theorem lie_eq_zero_of_isMulCommutative [BoundarylessManifold IG G] {b : B}
    (u v : AdjointBundle IG G P b) : ⁅u, v⁆ = 0 :=
  LieModule.IsTrivial.trivial u v

end CommutativeReal

section Circle

variable {Q : B → Type*} [TopologicalSpace (TotalSpace Circle Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle Circle Q] [∀ b, MulAction Circleᵐᵒᵖ (Q b)] [PrincipalBundle Circle Q]

variable (Q) in
/-- For any principal `Circle`-bundle `Q`, every fibre of `AdjointBundle (𝓡 1) Circle Q` is
canonically ℝ-linearly isomorphic to `ℝ`, normalized via `circleLieAlgebraEquiv` so that the
generator of `Circle.exp` has coordinate `1`. -/
def circleTrivialLinearEquiv (b : B) :
    AdjointBundle (𝓡 1) Circle Q b ≃ₗ[ℝ] ℝ :=
  (trivialLieEquiv ℝ (𝓡 1) Circle Q b).toLinearEquiv.trans <|
    (leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓡 1) (G := Circle)
        BoundarylessManifold.isInteriorPoint).symm.trans
      circleLieAlgebraEquiv

/-- In any principal frame `q : Q b`, `circleTrivialLinearEquiv` sends the standard generator
`circleExpGenerator` of `Circle.exp` to `1 : ℝ`. -/
theorem circleTrivialLinearEquiv_mk_generator {b : B} (q : Q b) :
    circleTrivialLinearEquiv Q b
      (mk (𝓡 1) Circle q
        (leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓡 1) (G := Circle)
          BoundarylessManifold.isInteriorPoint circleExpGenerator)) = 1 := by
  rw [circleTrivialLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LieEquiv.coe_toLinearEquiv, trivialLieEquiv_mk, LinearEquiv.symm_apply_apply,
    circleLieAlgebraEquiv_apply_generator]

/-- Every fibre of the adjoint bundle of a principal `Circle`-bundle has identically zero Lie
bracket. -/
theorem circle_lie_eq_zero {b : B} (u v : AdjointBundle (𝓡 1) Circle Q b) : ⁅u, v⁆ = 0 :=
  lie_eq_zero_of_isMulCommutative u v

end Circle

end RealSmooth

end AdjointBundle

end TauCeti
