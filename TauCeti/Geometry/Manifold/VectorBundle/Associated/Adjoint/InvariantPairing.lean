/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Associated.Adjoint.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
public import TauCeti.Algebra.Lie.InvariantForm.Basic
public import TauCeti.Algebra.Lie.Killing.Basic
public import TauCeti.Geometry.Lie.Adjoint.InvariantForm
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.RepresentationTheory.SU2.LieAlgebra
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Ad-invariant bilinear pairings on the adjoint bundle

An `Ad`-invariant continuous bilinear form
`B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜` descends to a well-defined
continuous bilinear form `TauCeti.AdjointBundle.invariantPairing B hB b` on each fibre of the
adjoint bundle `AdjointBundle IG G P`, characterized in *every* principal frame `p : P b` by
`invariantPairing B hB b (mk IG G p X) (mk IG G p Y) = B X Y`.

In every preferred bundle trivialization of `AdjointBundle IG G P`, the descended pairing reads as
the constant model bilinear form `B`, so it varies `C^n`-smoothly at every regularity `n : ℕ∞ω`
without choosing a partition of unity or fibre norms, and defines a bundled `C^n` bilinear field in
`TauCeti.Manifold.BilinearSection`. Descent preserves symmetry, left-separability, nondegeneracy,
topological invertibility into the continuous dual `StrongDual`, positive definiteness, and
negative definiteness, and commutes with pullback of principal bundles. Over `ℝ`, every descended
`Ad`-invariant pairing is infinitesimally `ad`-invariant (`LinearMap.BilinForm.lieInvariant`) on
every fibre without any connectedness hypothesis on `G`.

Specializing to the Killing form `killingForm` produces `TauCeti.AdjointBundle.killingPairing` and
its negative `TauCeti.AdjointBundle.negKillingPairing`. On any principal `SU(2)`-bundle (formalized
for `GLSpecialUnitary (Fin 2) ℂ` with any embedded Lie-subgroup atlas, including the canonical
closed-subgroup structure `glSpecialUnitaryTwoEmbeddedData`), every fibre has real dimension `3`,
`killingPairing` is strictly negative on nonzero fibre vectors (hence nondegenerate, and *not*
positive definite), and `negKillingPairing = -killingPairing` is strictly positive definite,
symmetric, `ad`-invariant, and smooth.

## Main definitions

* `TauCeti.AdjointBundle.invariantPairing`: fibrewise continuous bilinear pairing on
  `AdjointBundle IG G P` descended from an `Ad`-invariant continuous bilinear form `B`.
* `TauCeti.AdjointBundle.invariantPairingSection`: bundled `C^n` bilinear section in
  `TauCeti.Manifold.BilinearSection`.
* `TauCeti.AdjointBundle.killingPairing` and `TauCeti.AdjointBundle.negKillingPairing`: the
  descended Killing form and negative Killing form on `AdjointBundle IG G P`.
* `TauCeti.AdjointBundle.glSpecialUnitaryTwoEmbeddedData`: canonical closed-subgroup Lie structure
  on `GLSpecialUnitary (Fin 2) ℂ`.

## Main results

* `TauCeti.AdjointBundle.invariantPairing_mk`, `invariantPairing_trivializationAt`: frame-free and
  chart-constant evaluation formulas.
* `TauCeti.AdjointBundle.isSymm_toBilinForm_invariantPairing_iff`,
  `nondegenerate_toBilinForm_invariantPairing_iff`, `isInvertible_invariantPairing_iff`:
  preservation of symmetry, nondegeneracy, and the continuous musical isomorphism.
* `TauCeti.AdjointBundle.contMDiff_invariantPairing`,
  `ContMDiffWithinAt.invariantPairing_adjointBundle`: `C^n` smoothness of the bilinear section and
  of pairings of `C^n` bundle-valued maps.
* `TauCeti.AdjointBundle.invariantPairing_pullbackLieEquiv`: naturality under bundle pullback.
* `TauCeti.AdjointBundle.lieInvariant_invariantPairing`: infinitesimal `ad`-invariance on every
  real fibre.
* `TauCeti.AdjointBundle.exists_isSymm_posDef_invariantPairing`: existence of a smooth symmetric
  positive-definite `ad`-invariant fibrewise pairing when `G` is compact.
* `TauCeti.AdjointBundle.killingPairing_GLSpecialUnitary_two_self_neg`,
  `not_posDef_killingPairing_GLSpecialUnitary_two`,
  `negKillingPairing_GLSpecialUnitary_two_self_pos`: on every principal `SU(2)`-bundle, the Killing
  pairing is negative definite while its negative is a positive-definite invariant pairing.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §5, and Vol. II, 1969, Chapter XII, §1.
* I. Kolář, P. W. Michor, and J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10.7.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer, 2012, §§10.4, 12.1.
-/

public noncomputable section

open Bundle Filter MulOpposite Set
open scoped ContDiff Manifold Topology

namespace TauCeti.AdjointBundle

open TauCeti.Lie

section GeneralField

variable {𝕜 B₀ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B₀]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]

section Descent

variable [LieGroup IG 1 G] [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {P : B₀ → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- An `Ad`-invariant continuous bilinear form `B` on `GroupLieAlgebra IG G` descends to a
continuous bilinear form on each fibre of `AdjointBundle IG G P`. It is defined via the unit frame
in the preferred chart at `b` and is independent of that choice by `invariantPairing_mk`. -/
def invariantPairing
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (_hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    AdjointBundle IG G P b →L[𝕜] AdjointBundle IG G P b →L[𝕜] 𝕜 :=
  let e₀ := mkContinuousLinearEquiv 𝕜 IG G ((FiberBundle.homeomorphAt G P b).symm (1 : G))
  (e₀.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) :
      (GroupLieAlgebra IG G →L[𝕜] 𝕜) →L[𝕜] (AdjointBundle IG G P b →L[𝕜] 𝕜)) ∘L
    (B ∘L (e₀.symm : AdjointBundle IG G P b →L[𝕜] GroupLieAlgebra IG G))

private theorem invariantPairing_def
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) (u v : AdjointBundle IG G P b) :
    invariantPairing B hB b u v =
      let e₀ := mkContinuousLinearEquiv 𝕜 IG G ((FiberBundle.homeomorphAt G P b).symm (1 : G))
      B (e₀.symm u) (e₀.symm v) := by
  rfl

/-- In *any* principal frame `p : P b`, the descended pairing evaluates to `B` on Lie-algebra
coordinates. -/
@[simp]
theorem invariantPairing_mk
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    {b : B₀} (p : P b) (X Y : GroupLieAlgebra IG G) :
    invariantPairing B hB b (mk IG G p X) (mk IG G p Y) = B X Y := by
  rw [invariantPairing_def]
  dsimp only
  rw [mkContinuousLinearEquiv_symm_apply_mk, mkContinuousLinearEquiv_symm_apply_mk, hB]

/-- Formula for `invariantPairing` on classes presented in two possibly distinct frames
`p, q : P b`. -/
theorem invariantPairing_mk_mk
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    {b : B₀} (p q : P b) (X Y : GroupLieAlgebra IG G) :
    invariantPairing B hB b (mk IG G p X) (mk IG G q Y) =
      B X (adjointContinuousLinearMap (I := IG) (PrincipalBundle.division G p q) Y) := by
  have hq : mk IG G q Y =
      mk IG G p (adjointContinuousLinearMap (I := IG) (PrincipalBundle.division G p q) Y) :=
    (mk_eq_mk_iff.mpr rfl).symm
  rw [hq, invariantPairing_mk]

/-- In every preferred bundle chart of `AdjointBundle IG G P`, `invariantPairing B hB` reads as the
constant bilinear form `B` transferred to `AdjointLieAlgebra IG G`. -/
theorem invariantPairing_trivializationAt
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    {b' b : B₀} (hb : b ∈ (trivializationAt G P b').baseSet)
    (u v : AdjointBundle IG G P b) :
    invariantPairing B hB b u v =
      B ((AdjointLieAlgebra.ofGroupLieAlgebra IG G).symm
          (trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) b' ⟨b, u⟩).2)
        ((AdjointLieAlgebra.ofGroupLieAlgebra IG G).symm
          (trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) b' ⟨b, v⟩).2) := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
  obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
  rw [invariantPairing_mk, trivializationAt_mk_snd hb, trivializationAt_mk_snd hb,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply, hB]

/-- Symmetry of `B` descends to every fibre of `AdjointBundle IG G P`. -/
theorem invariantPairing_symm
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (hsymm : ∀ X Y, B X Y = B Y X) {b : B₀} (u v : AdjointBundle IG G P b) :
    invariantPairing B hB b u v = invariantPairing B hB b v u := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
  obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
  rw [invariantPairing_mk, invariantPairing_mk, hsymm]

/-- `invariantPairing B hB b` is symmetric if and only if `B` is symmetric. -/
@[simp]
theorem isSymm_toBilinForm_invariantPairing_iff
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (invariantPairing (P := P) B hB b).toBilinForm.IsSymm ↔ B.toBilinForm.IsSymm := by
  rw [ContinuousLinearMap.isSymm_toBilinForm_iff, ContinuousLinearMap.isSymm_toBilinForm_iff]
  refine ⟨fun h X Y ↦ ?_, fun h u v ↦ invariantPairing_symm B hB h u v⟩
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  simpa only [invariantPairing_mk] using h (mk IG G p X) (mk IG G p Y)

/-- `invariantPairing B hB b` is left-separating if and only if `B` is left-separating. -/
@[simp]
theorem separatingLeft_toBilinForm_invariantPairing_iff
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (invariantPairing (P := P) B hB b).toBilinForm.SeparatingLeft ↔
      B.toBilinForm.SeparatingLeft := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  let e := mkContinuousLinearEquiv 𝕜 IG G p
  refine ⟨fun h X hX ↦ e.injective ?_, fun h u hu ↦ ?_⟩
  · rw [map_zero]
    refine h (e X) fun v ↦ ?_
    obtain ⟨Y, rfl⟩ := e.surjective v
    simpa only [e, mkContinuousLinearEquiv_apply, ContinuousLinearMap.toBilinForm_apply,
      invariantPairing_mk] using hX Y
  · obtain ⟨X, rfl⟩ := e.surjective u
    rw [← map_zero e]
    refine congrArg e (h X fun Y ↦ ?_)
    simpa only [e, mkContinuousLinearEquiv_apply, ContinuousLinearMap.toBilinForm_apply,
      invariantPairing_mk] using hu (e Y)

/-- `invariantPairing B hB b` is nondegenerate if and only if `B` is nondegenerate. -/
@[simp]
theorem nondegenerate_toBilinForm_invariantPairing_iff
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (invariantPairing (P := P) B hB b).toBilinForm.Nondegenerate ↔
      B.toBilinForm.Nondegenerate := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  let e := (mkContinuousLinearEquiv 𝕜 IG G p).toLinearEquiv
  have hcongr : (invariantPairing (P := P) B hB b).toBilinForm = B.toBilinForm.congr e := by
    ext u v
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    simp [e]
  rw [hcongr, LinearMap.BilinForm.nondegenerate_congr_iff]

/-- Contraction with `invariantPairing B hB b` is a topological linear isomorphism onto the
continuous dual `AdjointBundle IG G P b →L[𝕜] 𝕜` if and only if `B` is invertible. -/
@[simp]
theorem isInvertible_invariantPairing_iff_isInvertible
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (invariantPairing (P := P) B hB b).IsInvertible ↔ B.IsInvertible := by
  let e₀ := mkContinuousLinearEquiv 𝕜 IG G ((FiberBundle.homeomorphAt G P b).symm (1 : G))
  let eDual : (GroupLieAlgebra IG G →L[𝕜] 𝕜) ≃L[𝕜] (AdjointBundle IG G P b →L[𝕜] 𝕜) :=
    e₀.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  have hfactor : invariantPairing (P := P) B hB b =
      (eDual : (GroupLieAlgebra IG G →L[𝕜] 𝕜) →L[𝕜] (AdjointBundle IG G P b →L[𝕜] 𝕜)) ∘L
        (B ∘L (e₀.symm : AdjointBundle IG G P b →L[𝕜] GroupLieAlgebra IG G)) := by
    rfl
  rw [hfactor, ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv]

/-- In finite dimensions over a complete scalar field, `invariantPairing B hB b` induces a
continuous linear equivalence `AdjointBundle IG G P b ≃L[𝕜] StrongDual 𝕜 (AdjointBundle IG G P b)`
if and only if `B` is nondegenerate. -/
theorem isInvertible_invariantPairing_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EG]
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (invariantPairing (P := P) B hB b).IsInvertible ↔ B.toBilinForm.Nondegenerate := by
  let eG := AdjointLieAlgebra.ofGroupLieAlgebra IG G
  let eDual : (GroupLieAlgebra IG G →L[𝕜] 𝕜) ≃L[𝕜] (AdjointLieAlgebra IG G →L[𝕜] 𝕜) :=
    eG.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let C : AdjointLieAlgebra IG G →L[𝕜] AdjointLieAlgebra IG G →L[𝕜] 𝕜 :=
    (eDual : _ →L[𝕜] _) ∘L (B ∘L (eG.symm : _ →L[𝕜] _))
  have hCB : C.IsInvertible ↔ B.IsInvertible := by
    rw [ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv]
  have hnd : C.toBilinForm.Nondegenerate ↔ B.toBilinForm.Nondegenerate := by
    have hcongr : C.toBilinForm = B.toBilinForm.congr eG.toLinearEquiv := by ext; rfl
    rw [hcongr, LinearMap.BilinForm.nondegenerate_congr_iff]
  rw [isInvertible_invariantPairing_iff_isInvertible, ← hCB,
    C.isInvertible_iff_nondegenerate_toBilinForm, hnd]

end Descent

section Smooth

-- Align normed and seminormed structures on operator spaces for `contMDiffAt_section_iff`.
attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

variable [LieGroup IG 1 G] [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [ChartedSpace HB B₀]
  {P : B₀ → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

section MapPairing

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {b : M → B₀} {u v : ∀ m, AdjointBundle IG G P (b m)} {s : Set M} {x : M}

/-- Pairing two `C^n` maps into `AdjointBundle IG G P` over a common base map via
`invariantPairing B hB` is `C^n` within `s` at `x`. Finite-dimensionality is not required. -/
theorem _root_.ContMDiffWithinAt.invariantPairing_adjointBundle
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (hu : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜) n (fun m ↦ invariantPairing B hB (b m) (u m) (v m)) s x := by
  obtain ⟨hb, hu'⟩ := contMDiffWithinAt_totalSpace_iff.mp hu
  have hv' := (contMDiffWithinAt_totalSpace_iff.mp hv).2
  have hx := mem_baseSet_trivializationAt G P (b x)
  have hmem := hb.continuousWithinAt.preimage_mem_nhdsWithin
    ((trivializationAt G P (b x)).open_baseSet.mem_nhds hx)
  let eG := AdjointLieAlgebra.ofGroupLieAlgebra IG G
  let eDual : (GroupLieAlgebra IG G →L[𝕜] 𝕜) ≃L[𝕜] (AdjointLieAlgebra IG G →L[𝕜] 𝕜) :=
    eG.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let C : AdjointLieAlgebra IG G →L[𝕜] AdjointLieAlgebra IG G →L[𝕜] 𝕜 :=
    (eDual : _ →L[𝕜] _) ∘L (B ∘L (eG.symm : _ →L[𝕜] _))
  apply ((C.isBoundedBilinearMap.contDiff (n := n)).contMDiff.contMDiffAt.comp_contMDiffWithinAt x
    (hu'.prodMk_space hv')).congr_of_eventuallyEq
  · filter_upwards [hmem] with y hy
    exact invariantPairing_trivializationAt B hB hy (u y) (v y)
  · exact invariantPairing_trivializationAt B hB hx (u x) (v x)

/-- Pointwise `C^n` version of `ContMDiffWithinAt.invariantPairing_adjointBundle`. -/
theorem _root_.ContMDiffAt.invariantPairing_adjointBundle
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (hu : ContMDiffAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) x) :
    ContMDiffAt IM 𝓘(𝕜) n (fun m ↦ invariantPairing B hB (b m) (u m) (v m)) x := by
  rw [← contMDiffWithinAt_univ] at *
  exact hu.invariantPairing_adjointBundle B hB hv

/-- Setwise `C^n` version of `ContMDiffWithinAt.invariantPairing_adjointBundle`. -/
theorem _root_.ContMDiffOn.invariantPairing_adjointBundle
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (hu : ContMDiffOn IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))) s) :
    ContMDiffOn IM 𝓘(𝕜) n (fun m ↦ invariantPairing B hB (b m) (u m) (v m)) s :=
  fun x hx ↦ (hu x hx).invariantPairing_adjointBundle B hB (hv x hx)

/-- Global `C^n` version of `ContMDiffWithinAt.invariantPairing_adjointBundle`. -/
theorem _root_.ContMDiff.invariantPairing_adjointBundle
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (hu : ContMDiff IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, u m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P))))
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointLieAlgebra IG G) (AdjointBundle IG G P)))) :
    ContMDiff IM 𝓘(𝕜) n (fun m ↦ invariantPairing B hB (b m) (u m) (v m)) :=
  fun x ↦ (hu x).invariantPairing_adjointBundle B hB (hv x)

end MapPairing

section BilinearField

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EG] {n : ℕ∞ω}

/-- For a finite-dimensional Lie group `G`, `invariantPairing B hB` is a `C^n` section of the
iterated continuous-linear-map bundle on `AdjointBundle IG G P` at every regularity `n : ℕ∞ω`. -/
theorem contMDiff_invariantPairing
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y) :
    ContMDiff IB
      (IB.prod 𝓘(𝕜, AdjointLieAlgebra IG G →L[𝕜] AdjointLieAlgebra IG G →L[𝕜] 𝕜)) n
      (fun b ↦ TotalSpace.mk'
        (AdjointLieAlgebra IG G →L[𝕜] AdjointLieAlgebra IG G →L[𝕜] 𝕜)
        (E := fun y ↦ AdjointBundle IG G P y →L[𝕜] AdjointBundle IG G P y →L[𝕜] 𝕜)
        b (invariantPairing B hB b)) := by
  intro x
  rw [contMDiffAt_section_iff]
  let eG := AdjointLieAlgebra.ofGroupLieAlgebra IG G
  let eDual : (GroupLieAlgebra IG G →L[𝕜] 𝕜) ≃L[𝕜] (AdjointLieAlgebra IG G →L[𝕜] 𝕜) :=
    eG.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let C : AdjointLieAlgebra IG G →L[𝕜] AdjointLieAlgebra IG G →L[𝕜] 𝕜 :=
    (eDual : _ →L[𝕜] _) ∘L (B ∘L (eG.symm : _ →L[𝕜] _))
  have hc : ContMDiffAt IB
      𝓘(𝕜, AdjointLieAlgebra IG G →L[𝕜] AdjointLieAlgebra IG G →L[𝕜] 𝕜) n
      (fun _ : B₀ ↦ C) x := contMDiffAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [(trivializationAt G P x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt G P x)] with y hy
  ext v w
  rw [hom_trivializationAt_apply]
  have hyA : y ∈ (trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) x).baseSet := by
    simpa only [AssociatedBundle.baseSet_trivializationAt] using hy
  rw [inCoordinates_apply_eq₂ hyA hyA (by simp)]
  let e := trivializationAt (AdjointLieAlgebra IG G) (AdjointBundle IG G P) x
  have h := invariantPairing_trivializationAt B hB hy (e.symm y v) (e.symm y w)
  simpa only [C, eDual, eG, e, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply,
    Trivialization.apply_mk_symm _ hyA, Trivial.fiberBundle_trivializationAt',
    Trivial.linearMapAt_trivialization, LinearMap.id_apply] using h

/-- `invariantPairing B hB` packaged as a bundled `C^n` bilinear field in
`TauCeti.Manifold.BilinearSection`. -/
def invariantPairingSection
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y) :
    Manifold.BilinearSection IB (AdjointLieAlgebra IG G) (AdjointBundle IG G P) 𝕜 n :=
  ⟨invariantPairing B hB, contMDiff_invariantPairing B hB⟩

@[simp]
theorem invariantPairingSection_apply
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    invariantPairingSection (IB := IB) (P := P) (n := n) B hB b =
      invariantPairing (P := P) B hB b := by
  rfl

/-- `invariantPairingSection B hB` belongs to `Manifold.symmetricBilinearSections` whenever `B` is
symmetric. -/
theorem invariantPairingSection_mem_symmetricBilinearSections
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (hsymm : ∀ X Y, B X Y = B Y X) :
    invariantPairingSection (IB := IB) (P := P) (n := n) B hB ∈
      Manifold.symmetricBilinearSections :=
  (Manifold.mem_symmetricBilinearSections _).mpr fun _ u v ↦ invariantPairing_symm B hB hsymm u v

end BilinearField

end Smooth

section Pullback

variable [LieGroup IG 1 G] [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {B' : Type*} [TopologicalSpace B']
  {P : B₀ → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {K : Type*} [FunLike K B' B₀] [ContinuousMapClass K B' B₀] (f : K)

/-- Descent of `Ad`-invariant pairings commutes with pullback of principal bundles along `f`. -/
@[simp]
theorem invariantPairing_pullbackEquiv
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (x : B') (u v : AdjointBundle IG G ((f : B' → B₀) *ᵖ P) x) :
    invariantPairing (P := P) B hB (f x)
        (AssociatedBundle.pullbackEquiv f x u)
        (AssociatedBundle.pullbackEquiv f x v) =
      invariantPairing (P := (f : B' → B₀) *ᵖ P) B hB x u v := by
  let p : ((f : B' → B₀) *ᵖ P) x := (FiberBundle.homeomorphAt G P (f x)).symm 1
  obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
  obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
  rw [invariantPairing_mk]
  have hu : AssociatedBundle.pullbackEquiv f x (mk IG G p X) = mk IG G (P := P) p X := by
    rw [mk_eq_associatedBundleMk, mk_eq_associatedBundleMk]
    exact AssociatedBundle.pullbackEquiv_mk f x p _
  have hv : AssociatedBundle.pullbackEquiv f x (mk IG G p Y) = mk IG G (P := P) p Y := by
    rw [mk_eq_associatedBundleMk, mk_eq_associatedBundleMk]
    exact AssociatedBundle.pullbackEquiv_mk f x p _
  rw [hu, hv, invariantPairing_mk]

/-- `pullbackLieEquiv` is an isometry for every descended `Ad`-invariant pairing. -/
theorem invariantPairing_pullbackLieEquiv [CompleteSpace EG] [LieGroup IG (minSmoothness 𝕜 3) G]
    (B : GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IG G →L[𝕜] 𝕜)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (x : B') (u v : AdjointBundle IG G ((f : B' → B₀) *ᵖ P) x) :
    invariantPairing (P := P) B hB (f x)
        (pullbackLieEquiv f x u) (pullbackLieEquiv f x v) =
      invariantPairing (P := (f : B' → B₀) *ᵖ P) B hB x u v := by
  rw [coe_pullbackLieEquiv, coe_pullbackLieEquiv]
  exact invariantPairing_pullbackEquiv f B hB x u v

end Pullback

section KillingGeneral

variable [CompleteSpace 𝕜] [CompleteSpace EG] [FiniteDimensional 𝕜 EG]
  [LieGroup IG (minSmoothness 𝕜 3) G]

local instance lieGroupOneKilling : LieGroup IG 1 G :=
  LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

variable [ContinuousSMul G (AdjointLieAlgebra IG G)]
  {P : B₀ → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

variable (𝕜 IG G P) in
/-- The Killing form of `GroupLieAlgebra IG G` descended to each fibre of `AdjointBundle IG G P`. -/
def killingPairing (b : B₀) :
    AdjointBundle IG G P b →L[𝕜] AdjointBundle IG G P b →L[𝕜] 𝕜 :=
  invariantPairing (killingForm 𝕜 (GroupLieAlgebra IG G)).toContinuousBilinearMap
    (fun g X Y ↦ by
      simp only [LinearMap.toContinuousBilinearMap_apply]
      exact killingForm_adjointContinuousLinearMap (I := IG) g X Y)
    b

variable (𝕜 IG G P) in
/-- Minus the Killing pairing on `AdjointBundle IG G P`; for compact semisimple real Lie groups
such as `SU(2)` this is positive definite whereas `killingPairing` is negative definite. -/
def negKillingPairing (b : B₀) :
    AdjointBundle IG G P b →L[𝕜] AdjointBundle IG G P b →L[𝕜] 𝕜 :=
  -killingPairing 𝕜 IG G P b

@[simp]
theorem killingPairing_mk {b : B₀} (p : P b) (X Y : GroupLieAlgebra IG G) :
    killingPairing 𝕜 IG G P b (mk IG G p X) (mk IG G p Y) =
      killingForm 𝕜 (GroupLieAlgebra IG G) X Y := by
  simp [killingPairing]

@[simp]
theorem negKillingPairing_apply {b : B₀} (u v : AdjointBundle IG G P b) :
    negKillingPairing 𝕜 IG G P b u v = -killingPairing 𝕜 IG G P b u v := by
  rfl

/-- In any principal frame `p : P b`, `negKillingPairing` evaluates to `-killingForm`. -/
theorem negKillingPairing_mk {b : B₀} (p : P b) (X Y : GroupLieAlgebra IG G) :
    negKillingPairing 𝕜 IG G P b (mk IG G p X) (mk IG G p Y) =
      -killingForm 𝕜 (GroupLieAlgebra IG G) X Y := by
  simp [negKillingPairing_apply]

/-- The Killing pairing is symmetric on every fibre of `AdjointBundle IG G P`. -/
theorem killingPairing_symm {b : B₀} (u v : AdjointBundle IG G P b) :
    killingPairing 𝕜 IG G P b u v = killingPairing 𝕜 IG G P b v u :=
  invariantPairing_symm _ _
    (fun X Y ↦ LieModule.traceForm_comm 𝕜 (GroupLieAlgebra IG G) (GroupLieAlgebra IG G) X Y) u v

/-- The negative Killing pairing is symmetric on every fibre of `AdjointBundle IG G P`. -/
theorem negKillingPairing_symm {b : B₀} (u v : AdjointBundle IG G P b) :
    negKillingPairing 𝕜 IG G P b u v = negKillingPairing 𝕜 IG G P b v u := by
  rw [negKillingPairing_apply, negKillingPairing_apply, killingPairing_symm]

/-- `killingPairing` is topologically invertible on `AdjointBundle IG G P b` if and only if
`GroupLieAlgebra IG G` is a Killing Lie algebra (`LieAlgebra.IsKilling`). -/
@[simp]
theorem isInvertible_killingPairing_iff (b : B₀) :
    (killingPairing 𝕜 IG G P b).IsInvertible ↔
      LieAlgebra.IsKilling 𝕜 (GroupLieAlgebra IG G) := by
  rw [killingPairing, isInvertible_invariantPairing_iff,
    LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap,
    ← TauCeti.isKilling_iff_killingForm_nondegenerate]

/-- When `GroupLieAlgebra IG G` is a Killing Lie algebra (for example, semisimple in characteristic
zero), `killingPairing` is nondegenerate and topologically invertible on every fibre. -/
theorem isInvertible_killingPairing [LieAlgebra.IsKilling 𝕜 (GroupLieAlgebra IG G)] (b : B₀) :
    (killingPairing 𝕜 IG G P b).IsInvertible :=
  (isInvertible_killingPairing_iff (P := P) b).mpr inferInstance

end KillingGeneral

end GeneralField

section RealSmooth

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {B₀ : Type*} [TopologicalSpace B₀]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {P : B₀ → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- Over `ℝ`, every descended `Ad`-invariant pairing is infinitesimally `ad`-invariant
(`LinearMap.BilinForm.lieInvariant`) on every fibre of `AdjointBundle IG G P`, without any
connectedness assumption on `G`. -/
theorem lieInvariant_invariantPairing
    (B : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G →L[ℝ] ℝ)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (invariantPairing (P := P) B hB b).toBilinForm.lieInvariant (AdjointBundle IG G P b) := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  let f : AdjointBundle IG G P b →ₗ⁅ℝ⁆ GroupLieAlgebra IG G := (mkLieEquiv ℝ IG G p).symm.toLieHom
  have hpull : (invariantPairing (P := P) B hB b).toBilinForm =
      B.toBilinForm.compl₁₂ f.toLinearMap f.toLinearMap := by
    ext u v
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    have hfX : f (mk IG G p X) = X := by
      rw [← mkLieEquiv_apply (𝕜 := ℝ)]
      exact (mkLieEquiv ℝ IG G p).symm_apply_apply X
    have hfY : f (mk IG G p Y) = Y := by
      rw [← mkLieEquiv_apply (𝕜 := ℝ)]
      exact (mkLieEquiv ℝ IG G p).symm_apply_apply Y
    simp [hfX, hfY]
  rw [hpull]
  exact (lieInvariant_of_adjoint_invariant (I := IG) (G := G) hB).compl₁₂ f

omit [FiniteDimensional ℝ EG] in
/-- Strict diagonal positivity of `B` is preserved under descent to `AdjointBundle IG G P b`. -/
@[simp]
theorem invariantPairing_self_pos_iff
    (B : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G →L[ℝ] ℝ)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (∀ u : AdjointBundle IG G P b, u ≠ 0 → 0 < invariantPairing (P := P) B hB b u u) ↔
      (∀ X : GroupLieAlgebra IG G, X ≠ 0 → 0 < B X X) := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  let e := mkContinuousLinearEquiv ℝ IG G p
  refine ⟨fun h X hX ↦ ?_, fun h u hu ↦ ?_⟩
  · simpa only [e, mkContinuousLinearEquiv_apply, invariantPairing_mk] using
      h (e X) (e.map_ne_zero_iff.mpr hX)
  · obtain ⟨X, rfl⟩ := e.surjective u
    simpa only [e, mkContinuousLinearEquiv_apply, invariantPairing_mk] using
      h X (e.map_ne_zero_iff.mp hu)

omit [FiniteDimensional ℝ EG] in
/-- Strict diagonal negativity of `B` is preserved under descent to `AdjointBundle IG G P b`. -/
@[simp]
theorem invariantPairing_self_neg_iff
    (B : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G →L[ℝ] ℝ)
    (hB : ∀ (g : G) (X Y : GroupLieAlgebra IG G),
      B (adjointContinuousLinearMap (I := IG) g X)
        (adjointContinuousLinearMap (I := IG) g Y) = B X Y)
    (b : B₀) :
    (∀ u : AdjointBundle IG G P b, u ≠ 0 → invariantPairing (P := P) B hB b u u < 0) ↔
      (∀ X : GroupLieAlgebra IG G, X ≠ 0 → B X X < 0) := by
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  let e := mkContinuousLinearEquiv ℝ IG G p
  refine ⟨fun h X hX ↦ ?_, fun h u hu ↦ ?_⟩
  · simpa only [e, mkContinuousLinearEquiv_apply, invariantPairing_mk] using
      h (e X) (e.map_ne_zero_iff.mpr hX)
  · obtain ⟨X, rfl⟩ := e.surjective u
    simpa only [e, mkContinuousLinearEquiv_apply, invariantPairing_mk] using
      h X (e.map_ne_zero_iff.mp hu)

/-- The Killing pairing on any real `C^∞` Lie group's adjoint bundle is infinitesimally
`ad`-invariant on every fibre. -/
theorem lieInvariant_killingPairing (b : B₀) :
    (killingPairing ℝ IG G P b).toBilinForm.lieInvariant (AdjointBundle IG G P b) :=
  lieInvariant_invariantPairing _ _ b

/-- The negative Killing pairing on any real `C^∞` Lie group's adjoint bundle is infinitesimally
`ad`-invariant on every fibre. -/
theorem lieInvariant_negKillingPairing (b : B₀) :
    (negKillingPairing ℝ IG G P b).toBilinForm.lieInvariant (AdjointBundle IG G P b) := by
  intro u v w
  have h := lieInvariant_killingPairing (P := P) b u v w
  simp only [ContinuousLinearMap.toBilinForm_apply, negKillingPairing_apply] at h ⊢
  linarith

/-- For a compact finite-dimensional real `C^∞` Lie group `G`, every principal `G`-bundle `P` over
a charted base `B₀` carries a `C^n` symmetric, positive-definite, fibrewise `ad`-invariant bilinear
section on `AdjointBundle IG G P`. -/
theorem exists_isSymm_posDef_invariantPairing [CompactSpace G]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HB B₀] (n : ℕ∞ω) :
    ∃ g : Manifold.BilinearSection IB (AdjointLieAlgebra IG G) (AdjointBundle IG G P) ℝ n,
      (∀ b u v, g b u v = g b v u) ∧
      (∀ b u, u ≠ 0 → 0 < g b u u) ∧
      (∀ b, (g b).toBilinForm.lieInvariant (AdjointBundle IG G P b)) ∧
      (∀ b, (g b).IsInvertible) := by
  let _ : T2Space G := IG.t2Space_of_lieGroup ∞
  obtain ⟨B, hsymm, hpos, hAd⟩ :=
    exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant (I := IG) (G := G)
  refine ⟨invariantPairingSection B hAd,
    fun b u v ↦ invariantPairing_symm B hAd hsymm u v,
    fun b ↦ (invariantPairing_self_pos_iff B hAd b).mpr hpos,
    fun b ↦ lieInvariant_invariantPairing B hAd b,
    fun b ↦ ?_⟩
  rw [invariantPairingSection_apply, isInvertible_invariantPairing_iff]
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun X hX ↦ ?_
  by_contra hX0
  exact (hpos X hX0).ne' (hX X)

end RealSmooth

section SU2

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The canonical 3-dimensional real model vector space of `GLSpecialUnitary (Fin 2) ℂ`, namely its
Lie subalgebra `𝔰𝔲(2)` inside the derivations of `(Matrix (Fin 2) (Fin 2) ℂ)ˣ`. -/
abbrev GLSpecialUnitaryTwoModel : Type :=
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
    (GLSpecialUnitary (Fin 2) ℂ : Subgroup (Matrix (Fin 2) (Fin 2) ℂ)ˣ)).toSubmodule

instance instNormedAddCommGroupGLSpecialUnitaryTwoModel :
    NormedAddCommGroup GLSpecialUnitaryTwoModel := inferInstance

instance instNormedSpaceGLSpecialUnitaryTwoModel :
    NormedSpace ℝ GLSpecialUnitaryTwoModel := inferInstance

instance instFiniteDimensionalGLSpecialUnitaryTwoModel :
    FiniteDimensional ℝ GLSpecialUnitaryTwoModel :=
  Module.Finite.equiv TauCeti.SU2.pauliLieAlgebraEquiv

/-- Canonical embedded-Lie-subgroup structure on `GLSpecialUnitary (Fin 2) ℂ` provided by the
closed-subgroup theorem. -/
def glSpecialUnitaryTwoEmbeddedData :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ)
      (GLSpecialUnitary (Fin 2) ℂ) GLSpecialUnitaryTwoModel :=
  EmbeddedLieSubgroupData.ofIsClosed (isClosed_GLSpecialUnitary (Fin 2) ℂ)

section AnyEmbeddedModel

variable {B₀ : Type*} [TopologicalSpace B₀]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  (d : EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) (GLSpecialUnitary (Fin 2) ℂ) E')

/-- Any embedded Lie-subgroup atlas `d` on `GLSpecialUnitary (Fin 2) ℂ` identifies its tangent Lie
algebra with the ambient skew-Hermitian trace-free Lie subalgebra `𝔰𝔲(2)`. -/
def glSpecialUnitaryTwoGroupLieEquiv :
    let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
    GroupLieAlgebra 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) ≃ₗ⁅ℝ⁆
      lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
        (GLSpecialUnitary (Fin 2) ℂ) :=
  let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
  (leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := 𝓘(ℝ, E')) (G := GLSpecialUnitary (Fin 2) ℂ)
      BoundarylessManifold.isInteriorPoint).symm.trans
    d.lieEquivLieSubalgebraOfSubgroup

/-- Every fibre of the adjoint bundle of a principal `GLSpecialUnitary (Fin 2) ℂ`-bundle has real
dimension `3`. -/
theorem finrank_adjointBundle_GLSpecialUnitary_two :
    let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
    ∀ {P : B₀ → Type*} [TopologicalSpace (TotalSpace (GLSpecialUnitary (Fin 2) ℂ) P)]
      [∀ b, TopologicalSpace (P b)] [FiberBundle (GLSpecialUnitary (Fin 2) ℂ) P]
      [∀ b, MulAction (GLSpecialUnitary (Fin 2) ℂ)ᵐᵒᵖ (P b)]
      [PrincipalBundle (GLSpecialUnitary (Fin 2) ℂ) P] (b : B₀),
      Module.finrank ℝ (AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b) = 3 := by
  let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
  dsimp only
  intro P _ _ _ _ _ b
  let p : P b := (FiberBundle.homeomorphAt (GLSpecialUnitary (Fin 2) ℂ) P b).symm 1
  let e : AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    (mkLieEquiv ℝ 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) p).symm.toLinearEquiv.trans <|
      (glSpecialUnitaryTwoGroupLieEquiv d).toLinearEquiv.trans
        TauCeti.SU2.pauliLieAlgebraEquiv.symm
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_fin]

/-- Every fibre of the adjoint bundle of a principal `GLSpecialUnitary (Fin 2) ℂ`-bundle is
nontrivial. -/
theorem nontrivial_adjointBundle_GLSpecialUnitary_two :
    let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
    ∀ {P : B₀ → Type*} [TopologicalSpace (TotalSpace (GLSpecialUnitary (Fin 2) ℂ) P)]
      [∀ b, TopologicalSpace (P b)] [FiberBundle (GLSpecialUnitary (Fin 2) ℂ) P]
      [∀ b, MulAction (GLSpecialUnitary (Fin 2) ℂ)ᵐᵒᵖ (P b)]
      [PrincipalBundle (GLSpecialUnitary (Fin 2) ℂ) P] (b : B₀),
      Nontrivial (AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b) := by
  let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
  dsimp only
  intro P _ _ _ _ _ b
  apply Module.nontrivial_of_finrank_pos (R := ℝ)
  rw [finrank_adjointBundle_GLSpecialUnitary_two d b]
  norm_num

/-- On any principal `GLSpecialUnitary (Fin 2) ℂ`-bundle, the Killing pairing on the adjoint bundle
is strictly negative at every nonzero fibre vector (in Pauli coordinates it is `-8` times the
Euclidean dot product). -/
theorem killingPairing_GLSpecialUnitary_two_self_neg :
    let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
    ∀ {P : B₀ → Type*} [TopologicalSpace (TotalSpace (GLSpecialUnitary (Fin 2) ℂ) P)]
      [∀ b, TopologicalSpace (P b)] [FiberBundle (GLSpecialUnitary (Fin 2) ℂ) P]
      [∀ b, MulAction (GLSpecialUnitary (Fin 2) ℂ)ᵐᵒᵖ (P b)]
      [PrincipalBundle (GLSpecialUnitary (Fin 2) ℂ) P] {b : B₀}
      (v : AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b),
      v ≠ 0 →
        killingPairing ℝ 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b v v < 0 := by
  let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
  dsimp only
  intro P _ _ _ _ _ b v hv
  rw [killingPairing]
  refine (invariantPairing_self_neg_iff _ _ b).mpr (fun X hX ↦ ?_) v hv
  simp only [LinearMap.toContinuousBilinearMap_apply]
  let e : GroupLieAlgebra 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) ≃ₗ⁅ℝ⁆
      lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
        (GLSpecialUnitary (Fin 2) ℂ) :=
    glSpecialUnitaryTwoGroupLieEquiv d
  rw [← LieAlgebra.killingForm_of_equiv_apply e X X]
  have heX : e X ≠ 0 := (map_ne_zero_iff e e.injective).mpr hX
  exact TauCeti.SU2.killingForm_self_neg (e X) heX

/-- On any principal `GLSpecialUnitary (Fin 2) ℂ`-bundle, the Killing pairing on `ad(P)` is *not*
positive definite: every fibre is 3-dimensional and the Killing pairing is negative on nonzero
vectors. -/
theorem not_posDef_killingPairing_GLSpecialUnitary_two :
    let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
    ∀ {P : B₀ → Type*} [TopologicalSpace (TotalSpace (GLSpecialUnitary (Fin 2) ℂ) P)]
      [∀ b, TopologicalSpace (P b)] [FiberBundle (GLSpecialUnitary (Fin 2) ℂ) P]
      [∀ b, MulAction (GLSpecialUnitary (Fin 2) ℂ)ᵐᵒᵖ (P b)]
      [PrincipalBundle (GLSpecialUnitary (Fin 2) ℂ) P] (b : B₀),
      ¬ ∀ v : AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b,
        v ≠ 0 → 0 < killingPairing ℝ 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b v v := by
  let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
  dsimp only
  intro P _ _ _ _ _ b hpos
  have : Nontrivial (AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b) :=
    nontrivial_adjointBundle_GLSpecialUnitary_two d b
  obtain ⟨v, hv⟩ := exists_ne (0 : AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b)
  exact not_lt.mpr (killingPairing_GLSpecialUnitary_two_self_neg d v hv).le (hpos v hv)

/-- On any principal `GLSpecialUnitary (Fin 2) ℂ`-bundle, the *negative* Killing pairing
`negKillingPairing = -killingPairing` is strictly positive definite on every fibre of `ad(P)`. -/
theorem negKillingPairing_GLSpecialUnitary_two_self_pos :
    let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
    ∀ {P : B₀ → Type*} [TopologicalSpace (TotalSpace (GLSpecialUnitary (Fin 2) ℂ) P)]
      [∀ b, TopologicalSpace (P b)] [FiberBundle (GLSpecialUnitary (Fin 2) ℂ) P]
      [∀ b, MulAction (GLSpecialUnitary (Fin 2) ℂ)ᵐᵒᵖ (P b)]
      [PrincipalBundle (GLSpecialUnitary (Fin 2) ℂ) P] {b : B₀}
      (v : AdjointBundle 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b),
      v ≠ 0 →
        0 < negKillingPairing ℝ 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b v v := by
  let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
  dsimp only
  intro P _ _ _ _ _ b v hv
  rw [negKillingPairing_apply, neg_pos]
  exact killingPairing_GLSpecialUnitary_two_self_neg d v hv

/-- On any principal `GLSpecialUnitary (Fin 2) ℂ`-bundle, `negKillingPairing` induces a topological
linear equivalence from every fibre of `ad(P)` onto its continuous dual. -/
theorem isInvertible_negKillingPairing_GLSpecialUnitary_two :
    let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
    ∀ {P : B₀ → Type*} [TopologicalSpace (TotalSpace (GLSpecialUnitary (Fin 2) ℂ) P)]
      [∀ b, TopologicalSpace (P b)] [FiberBundle (GLSpecialUnitary (Fin 2) ℂ) P]
      [∀ b, MulAction (GLSpecialUnitary (Fin 2) ℂ)ᵐᵒᵖ (P b)]
      [PrincipalBundle (GLSpecialUnitary (Fin 2) ℂ) P] (b : B₀),
      (negKillingPairing ℝ 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b).IsInvertible := by
  let _ : ChartedSpace E' (GLSpecialUnitary (Fin 2) ℂ) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ (GLSpecialUnitary (Fin 2) ℂ) := d.lieGroup
  dsimp only
  intro P _ _ _ _ _ b
  have heq : negKillingPairing ℝ 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) P b =
      invariantPairing (-killingForm ℝ
          (GroupLieAlgebra 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ))).toContinuousBilinearMap
        (fun g X Y ↦ by
          simp only [LinearMap.toContinuousBilinearMap_apply, LinearMap.neg_apply]
          exact congrArg Neg.neg (killingForm_adjointContinuousLinearMap g X Y))
        b := by
    ext u v
    let p : P b := (FiberBundle.homeomorphAt (GLSpecialUnitary (Fin 2) ℂ) P b).symm 1
    obtain ⟨X, rfl⟩ := (mk_bijective p).surjective u
    obtain ⟨Y, rfl⟩ := (mk_bijective p).surjective v
    simp
  rw [heq, isInvertible_invariantPairing_iff]
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun X hX ↦ ?_
  by_contra hX0
  let p : P b := (FiberBundle.homeomorphAt (GLSpecialUnitary (Fin 2) ℂ) P b).symm 1
  have hm : mk 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) p X ≠ 0 := fun h0 ↦
    hX0 ((mk_bijective p).injective (h0.trans (mk_zero p).symm))
  have hpos := negKillingPairing_GLSpecialUnitary_two_self_pos d
    (mk 𝓘(ℝ, E') (GLSpecialUnitary (Fin 2) ℂ) p X) hm
  rw [negKillingPairing_mk] at hpos
  exact hpos.ne' (by simpa using hX X)

end AnyEmbeddedModel

end SU2

end TauCeti.AdjointBundle
