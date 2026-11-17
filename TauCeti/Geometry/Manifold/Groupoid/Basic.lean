/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic

import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Lie groupoids on total arrows

A Lie groupoid is a categorical groupoid `C` (`[Category C] [IsGroupoid C]`) whose object space
`C` and total-arrow space `Quiver.Total C` carry smooth (`C^∞`) finite-dimensional boundaryless
real manifold structures such that:

* the source map `s = Quiver.Total.left` and target map `t = Quiver.Total.right` are smooth
  submersions;
* the unit section `x ↦ ⟨x, x, 𝟙 x⟩` and inversion `a ↦ ⟨a.right, a.left, inv a.hom⟩` are smooth;
* geometric multiplication `(g, h) ↦ h.comp g` (written `gh`: first `h`, then `g`) is smooth on
  the transverse fibre product `{p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}`
  built from `s` and `t` (`TauCeti.transverseFiberProductChartedSpace`);
* every source fibre `{a : Quiver.Total C // a.left = x}` is Hausdorff in its subspace topology.

Neither `C` nor `Quiver.Total C` is assumed globally Hausdorff or second countable. As in the
Crainic–Fernandes integrability convention, arrow manifolds arising from foliations can be
non-Hausdorff while still being locally Hausdorff with Hausdorff source fibres. Local
Hausdorffness follows automatically from the manifold charts
(`IsLieGroupoid.exists_isOpen_mem_t2Space_objects`,
`IsLieGroupoid.exists_isOpen_mem_t2Space_arrows`).

## Conventions

Following categorical notation in Mathlib and `TauCeti.IsTopologicalGroupoid`, an arrow
`a : Quiver.Total C` runs from `a.left` (`s(a)`) to `a.right` (`t(a)`). Geometric multiplication
`gh` is defined when `s(g) = t(h)` and equals `h.comp g` ("first `h`, then `g`"). Categorical
composition `a.comp b` is defined on `{p // p.1.right = p.2.left}` and obtained from geometric
multiplication via the coordinate swap `IsLieGroupoid.composablePairsSwapDiffeomorph`.

## Main definitions

* `TauCeti.IsLieGroupoid`: the `Prop`-valued typeclass recording a Lie groupoid structure on `C`.
* `TauCeti.IsLieGroupoid.of_source_inverse_mul`: constructor deriving `isSubmersion_target` and
  `contMDiff_unit` automatically from `isSubmersion_source`, `contMDiff_inverse`, and
  `contMDiff_mul`.
* `TauCeti.IsLieGroupoid.of_contMDiff_comp`: constructor taking smoothness of categorical
  composition `a.comp b` on `{p // p.1.right = p.2.left}` in place of geometric multiplication.
* `TauCeti.IsLieGroupoid.inverseDiffeomorph`: arrow inversion as a `C^∞` diffeomorphism of
  `Quiver.Total C`.
* `TauCeti.IsLieGroupoid.composablePairsChartedSpace`: the transverse fibre-product manifold
  structure on geometric composable pairs `{p // p.1.left = p.2.right}`.
* `TauCeti.IsLieGroupoid.categoricalComposablePairsChartedSpace`: the transverse fibre-product
  manifold structure on categorical composable pairs `{p // p.1.right = p.2.left}`.
* `TauCeti.IsLieGroupoid.sourcePairsChartedSpace`: the transverse fibre-product manifold structure
  on source-matched pairs `{p // p.1.left = p.2.left}`.
* `TauCeti.IsLieGroupoid.mulShearDiffeomorph`: the shear diffeomorphism `(g, h) ↦ (gh, h)` from
  `Γ ×_{s,t} Γ` to `Γ ×_{s,s} Γ`, with inverse `(k, h) ↦ (k h⁻¹, h)`.

## Main results

* `TauCeti.IsLieGroupoid.t2Space_targetFiber`: every target fibre is Hausdorff.
* `TauCeti.IsLieGroupoid.isOpenMap_source`, `TauCeti.IsLieGroupoid.isOpenMap_target`: source and
  target are open maps.
* `TauCeti.IsLieGroupoid.finrank_le_finrank_arrows`,
  `TauCeti.IsLieGroupoid.isLocalDiffeomorph_source_iff_finrank_eq`,
  `TauCeti.IsLieGroupoid.isLocalDiffeomorph_target_iff_finrank_eq`: `dim M ≤ dim Γ` for nonempty
  `C`, with equality if and only if `s` (equivalently `t`) is a local diffeomorphism (the étale
  case).
* `TauCeti.IsLieGroupoid.toIsTopologicalGroupoid`: forgetting smoothness yields
  `TauCeti.IsTopologicalGroupoid C` on the same topologies.
* `TauCeti.IsLieGroupoid.isSubmersion_mul`, `TauCeti.IsLieGroupoid.isSubmersion_comp`,
  `TauCeti.IsLieGroupoid.isSubmersion_div_source`: multiplication, composition, and the source
  division map `(k, h) ↦ k h⁻¹` are smooth submersions onto `Quiver.Total C`.

Tangent-space identities at units (the unit embedding, direct-sum splittings, and differentials of
multiplication and inversion) live in `TauCeti.Geometry.Manifold.Groupoid.Tangent`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Chapter 1.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
* M. Crainic and R. L. Fernandes, *Integrability of Lie brackets*, Ann. of Math. (2) **157**
  (2003), 575–620.
-/

public section

open CategoryTheory Function Manifold Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']

/-- A Lie groupoid structure on a categorical groupoid `C` whose object space `C` and total-arrow
space `Quiver.Total C` are smooth finite-dimensional boundaryless real manifolds modelled on `I`
and `J`.

Neither `C` nor `Quiver.Total C` is required to be globally Hausdorff or second countable; local
Hausdorffness holds automatically from charts (`IsLieGroupoid.exists_isOpen_mem_t2Space_arrows`).
Every source fibre `{a : Quiver.Total C // a.left = x}` is required to be Hausdorff in its
subspace topology, matching the Crainic–Fernandes convention. -/
class IsLieGroupoid (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    [I.Boundaryless] [J.Boundaryless]
    (C : Type*) [Category C] [IsGroupoid C]
    [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
    [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
    [IsManifold J ∞ (Quiver.Total C)] : Prop where
  /-- The source map `s = Quiver.Total.left : Quiver.Total C → C` is a smooth submersion. -/
  isSubmersion_source : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C)
  /-- The target map `t = Quiver.Total.right : Quiver.Total C → C` is a smooth submersion. -/
  isSubmersion_target : Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C)
  /-- The unit section `x ↦ ⟨x, x, 𝟙 x⟩` is smooth. -/
  contMDiff_unit : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
  /-- Arrow inversion `a ↦ ⟨a.right, a.left, inv a.hom⟩` is smooth. -/
  contMDiff_inverse : ContMDiff J J ∞ fun a : Quiver.Total C ↦
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C)
  /-- Geometric multiplication `(g, h) ↦ h.comp g` (first `h`, then `g`) is smooth on the
  transverse fibre product `{p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}`. -/
  contMDiff_mul :
    letI := transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
      isSubmersion_source.contMDiff isSubmersion_target.contMDiff
      (transverse_of_isSubmersion_left (by simp) isSubmersion_source)
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        p.1.2.comp p.1.1 p.2.symm
  /-- Every source fibre `s⁻¹(x)` is Hausdorff in its subspace topology. -/
  t2Space_sourceFiber : ∀ x : C, T2Space {a : Quiver.Total C // a.left = x}

end Defs

namespace IsLieGroupoid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']

/-! ### Constructors from minimal axioms -/

section Constructors

variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  [I.Boundaryless] [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]

/-- A Lie groupoid structure requires only that the source map is a submersion, inversion is
smooth, multiplication is smooth, and every source fibre is Hausdorff. Smoothness of the target
submersion follows by conjugation with the inversion diffeomorphism, and smoothness of the unit
section descends along the surjective submersion `s` via `u(s(a)) = a ≫ a⁻¹`. -/
theorem of_source_inverse_mul
    (hs : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (hinv : ContMDiff J J ∞ fun a : Quiver.Total C ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
    (hmul :
      letI := transverseFiberProductChartedSpace
        (f := (Quiver.Total.left : Quiver.Total C → C))
        (g := (Quiver.Total.right : Quiver.Total C → C))
        (n := (∞ : ℕ∞ω)) (by simp)
        hs.contMDiff (hs.contMDiff.comp hinv)
        (transverse_of_isSubmersion_left (by simp) hs)
      ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
        fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
          p.1.2.comp p.1.1 p.2.symm)
    (ht2 : ∀ x : C, T2Space {a : Quiver.Total C // a.left = x}) :
    IsLieGroupoid I J C := by
  let invDiffeo : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C :=
    { toFun := fun a ↦ ⟨a.right, a.left, inv a.hom⟩
      invFun := fun a ↦ ⟨a.right, a.left, inv a.hom⟩
      left_inv := fun a ↦ by cases a; simp
      right_inv := fun a ↦ by cases a; simp
      contMDiff_toFun := hinv
      contMDiff_invFun := hinv }
  have ht : Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
    (Manifold.isSubmersionOfComplement_iff.mpr fun a ↦
      (invDiffeo.isLocalDiffeomorph a).isSubmersionAtOfComplement_comp
        (hs.isSubmersionOfComplement_complement.isSubmersionAt (invDiffeo a))).isSubmersion
  have hunit : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) := by
    rw [← hs.contMDiff_comp_iff Quiver.Total.surjective_left le_rfl]
    let := transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
      hs.contMDiff ht.contMDiff (transverse_of_isSubmersion_left (by simp) hs)
    have hemb := isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
      hs.contMDiff ht.contMDiff (transverse_of_isSubmersion_left (by simp) hs)
    let diag : Quiver.Total C →
        {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
      fun a ↦ ⟨(⟨a.right, a.left, inv a.hom⟩, a), rfl⟩
    have hdiag : ContMDiff J
        𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ diag :=
      hemb.contMDiff_iff_comp.mpr (hinv.prodMk contMDiff_id)
    have heq : (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) ∘ Quiver.Total.left =
        (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
          p.1.2.comp p.1.1 p.2.symm) ∘ diag := by
      funext a
      simp [diag, Function.comp_apply]
    rw [heq]
    exact hmul.comp hdiag
  exact ⟨hs, ht, hunit, hinv, hmul, ht2⟩

/-- Construct `IsLieGroupoid` from smoothness of categorical composition `a.comp b` on
`{p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}` instead of geometric
multiplication. -/
theorem of_contMDiff_comp
    (hs : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hunit : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hinv : ContMDiff J J ∞ fun a : Quiver.Total C ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
    (hcomp :
      letI := transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
        ht.contMDiff hs.contMDiff
        (transverse_of_isSubmersion_left (by simp) ht)
      ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
        fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
          p.1.1.comp p.1.2 p.2)
    (ht2 : ∀ x : C, T2Space {a : Quiver.Total C // a.left = x}) :
    IsLieGroupoid I J C := by
  refine ⟨hs, ht, hunit, hinv, ?_, ht2⟩
  let := transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    hs.contMDiff ht.contMDiff (transverse_of_isSubmersion_left (by simp) hs)
  let := transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    ht.contMDiff hs.contMDiff (transverse_of_isSubmersion_left (by simp) ht)
  have hemb₁ := isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    hs.contMDiff ht.contMDiff (transverse_of_isSubmersion_left (by simp) hs)
  have hemb₂ := isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    ht.contMDiff hs.contMDiff (transverse_of_isSubmersion_left (by simp) ht)
  let swap : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} →
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
    fun p ↦ ⟨(p.1.2, p.1.1), p.2.symm⟩
  have hswap : ContMDiff
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ swap :=
    hemb₂.contMDiff_iff_comp.mpr (hemb₁.contMDiff.snd.prodMk hemb₁.contMDiff.fst)
  exact hcomp.comp hswap

end Constructors

/-! ### Local Hausdorffness -/

omit [FiniteDimensional ℝ E] in
/-- Every object of a charted space modelled on a `ModelWithCorners ℝ E H` has an open Hausdorff
neighbourhood (from its preferred chart). -/
theorem exists_isOpen_mem_t2Space_objects {C : Type*} (I : ModelWithCorners ℝ E H)
    [TopologicalSpace C] [ChartedSpace H C] (x : C) :
    ∃ U : Set C, IsOpen U ∧ x ∈ U ∧ T2Space U := by
  have : T2Space H := I.isClosedEmbedding.toIsEmbedding.t2Space
  exact ChartedSpace.exists_isOpen_mem_t2Space H x

omit [FiniteDimensional ℝ E'] in
/-- Every total arrow has an open Hausdorff neighbourhood (from the preferred chart of
`Quiver.Total C`), even when the total arrow manifold is globally non-Hausdorff. -/
theorem exists_isOpen_mem_t2Space_arrows {C : Type*} [Quiver C] (J : ModelWithCorners ℝ E' H')
    [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)] (a : Quiver.Total C) :
    ∃ U : Set (Quiver.Total C), IsOpen U ∧ a ∈ U ∧ T2Space U := by
  have : T2Space H' := J.isClosedEmbedding.toIsEmbedding.t2Space
  exact ChartedSpace.exists_isOpen_mem_t2Space H' a

section API

variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  [I.Boundaryless] [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

/-! ### Source and target maps -/

/-- The source map `s : Quiver.Total C → C` is smooth. -/
theorem contMDiff_source :
    ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff

/-- The target map `t : Quiver.Total C → C` is smooth. -/
theorem contMDiff_target :
    ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff

include I J in
/-- The source map is continuous. -/
theorem continuous_source : Continuous (Quiver.Total.left : Quiver.Total C → C) :=
  (contMDiff_source I J C).continuous

include I J in
/-- The target map is continuous. -/
theorem continuous_target : Continuous (Quiver.Total.right : Quiver.Total C → C) :=
  (contMDiff_target I J C).continuous

include I J in
/-- The unit section is continuous. -/
theorem continuous_unit : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) :=
  (contMDiff_unit (I := I) (J := J) (C := C)).continuous

include I J in
/-- Arrow inversion is continuous. -/
theorem continuous_inverse :
    Continuous fun a : Quiver.Total C ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C) :=
  (contMDiff_inverse (I := I) (J := J) (C := C)).continuous

include I J in
/-- The source map is an open map. -/
theorem isOpenMap_source : IsOpenMap (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).isOpenMap

include I J in
/-- The target map is an open map. -/
theorem isOpenMap_target : IsOpenMap (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target (I := I) (J := J) (C := C)).isOpenMap

/-- The differential of the source map has a continuous linear right inverse at every arrow. -/
theorem isDiffSubmersionAt_source (a : Quiver.Total C) :
    IsDiffSubmersionAt J I (Quiver.Total.left : Quiver.Total C → C) a :=
  isDiffSubmersionAt_iff.mpr <|
    (isSubmersion_source (I := I) (J := J) (C := C)).hasRightInverse_mfderiv (by simp) a

/-- The differential of the target map has a continuous linear right inverse at every arrow. -/
theorem isDiffSubmersionAt_target (a : Quiver.Total C) :
    IsDiffSubmersionAt J I (Quiver.Total.right : Quiver.Total C → C) a :=
  isDiffSubmersionAt_iff.mpr <|
    (isSubmersion_target (I := I) (J := J) (C := C)).hasRightInverse_mfderiv (by simp) a

/-- Every arrow is a regular point of the source map. -/
theorem isRegularPoint_source (a : Quiver.Total C) :
    IsRegularPoint J I (Quiver.Total.left : Quiver.Total C → C) a :=
  isDiffSubmersionAt_iff_isRegularPoint.mp (isDiffSubmersionAt_source I J C a)

/-- Every arrow is a regular point of the target map. -/
theorem isRegularPoint_target (a : Quiver.Total C) :
    IsRegularPoint J I (Quiver.Total.right : Quiver.Total C → C) a :=
  isDiffSubmersionAt_iff_isRegularPoint.mp (isDiffSubmersionAt_target I J C a)

/-- Every object is a regular value of the source map. -/
theorem isRegularValue_source (x : C) :
    IsRegularValue J I (Quiver.Total.left : Quiver.Total C → C) x :=
  isRegularValue_iff.mpr fun a _ ↦ isRegularPoint_source I J C a

/-- Every object is a regular value of the target map. -/
theorem isRegularValue_target (x : C) :
    IsRegularValue J I (Quiver.Total.right : Quiver.Total C → C) x :=
  isRegularValue_iff.mpr fun a _ ↦ isRegularPoint_target I J C a

include I J in
/-- The dimension of the object manifold is at most the dimension of the arrow manifold whenever
the groupoid is nonempty. -/
theorem finrank_le_finrank_arrows [Nonempty C] : finrank ℝ E ≤ finrank ℝ E' := by
  have : Nonempty (Quiver.Total C) :=
    let x := Classical.arbitrary C; ⟨⟨x, x, 𝟙 x⟩⟩
  exact (isSubmersion_source (I := I) (J := J) (C := C)).finrank_le (by simp)

/-- For a nonempty Lie groupoid, the source map is a local diffeomorphism (the étale case) if and
only if the object and arrow manifolds have the same dimension. -/
theorem isLocalDiffeomorph_source_iff_finrank_eq [Nonempty C] :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      finrank ℝ E' = finrank ℝ E := by
  have : Nonempty (Quiver.Total C) :=
    let x := Classical.arbitrary C; ⟨⟨x, x, 𝟙 x⟩⟩
  exact (isSubmersion_source (I := I) (J := J) (C := C)).isLocalDiffeomorph_iff_finrank_eq (by simp)

/-- For a nonempty Lie groupoid, the target map is a local diffeomorphism if and only if the object
and arrow manifolds have the same dimension. -/
theorem isLocalDiffeomorph_target_iff_finrank_eq [Nonempty C] :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) ↔
      finrank ℝ E' = finrank ℝ E := by
  have : Nonempty (Quiver.Total C) :=
    let x := Classical.arbitrary C; ⟨⟨x, x, 𝟙 x⟩⟩
  exact (isSubmersion_target (I := I) (J := J) (C := C)).isLocalDiffeomorph_iff_finrank_eq (by simp)

/-! ### Inversion diffeomorphism -/

/-- Arrow inversion `a ↦ ⟨a.right, a.left, inv a.hom⟩` is a `C^∞` involutive diffeomorphism of
`Quiver.Total C`. -/
noncomputable def inverseDiffeomorph : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C where
  toFun a := ⟨a.right, a.left, inv a.hom⟩
  invFun a := ⟨a.right, a.left, inv a.hom⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp
  contMDiff_toFun := contMDiff_inverse (I := I) (J := J) (C := C)
  contMDiff_invFun := contMDiff_inverse (I := I) (J := J) (C := C)

@[simp]
theorem inverseDiffeomorph_apply (a : Quiver.Total C) :
    inverseDiffeomorph I J C a = ⟨a.right, a.left, inv a.hom⟩ := (rfl)

@[simp]
theorem inverseDiffeomorph_symm :
    (inverseDiffeomorph I J C).symm = inverseDiffeomorph I J C := (rfl)

/-- Applying the inverse of `inverseDiffeomorph` returns the inverted arrow. -/
theorem inverseDiffeomorph_symm_apply (a : Quiver.Total C) :
    (inverseDiffeomorph I J C).symm a = ⟨a.right, a.left, inv a.hom⟩ := (rfl)

/-- Arrow inversion is an involution on `Quiver.Total C`. -/
theorem inverseDiffeomorph_inverseDiffeomorph (a : Quiver.Total C) :
    inverseDiffeomorph I J C (inverseDiffeomorph I J C a) = a := by
  cases a; simp

/-- The source of the inverse of `a` is the target of `a`. -/
theorem left_inverseDiffeomorph (a : Quiver.Total C) :
    (inverseDiffeomorph I J C a).left = a.right := (rfl)

/-- The target of the inverse of `a` is the source of `a`. -/
theorem right_inverseDiffeomorph (a : Quiver.Total C) :
    (inverseDiffeomorph I J C a).right = a.left := (rfl)

/-- Arrow inversion fixes every unit arrow. -/
theorem inverseDiffeomorph_unit (x : C) :
    inverseDiffeomorph I J C ⟨x, x, 𝟙 x⟩ = ⟨x, x, 𝟙 x⟩ := by
  simp

/-- The source map is a smooth local diffeomorphism if and only if the target map is. -/
theorem isLocalDiffeomorph_source_iff_target :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) := by
  constructor <;> intro h a
  · have hc : Quiver.Total.left ∘ ⇑(inverseDiffeomorph I J C) = Quiver.Total.right :=
      funext (left_inverseDiffeomorph I J C)
    exact hc ▸ ((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp (K := I)
      (hg := h (inverseDiffeomorph I J C a))
  · have hc : Quiver.Total.right ∘ ⇑(inverseDiffeomorph I J C) = Quiver.Total.left :=
      funext (right_inverseDiffeomorph I J C)
    exact hc ▸ ((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp (K := I)
      (hg := h (inverseDiffeomorph I J C a))

include I J in
/-- Every target fibre `t⁻¹(x)` is Hausdorff in its subspace topology (transferred from the
corresponding source fibre by arrow inversion). -/
theorem t2Space_targetFiber (x : C) : T2Space {a : Quiver.Total C // a.right = x} := by
  have := t2Space_sourceFiber (I := I) (J := J) (C := C) x
  let e : {a : Quiver.Total C // a.left = x} ≃ₜ {a : Quiver.Total C // a.right = x} :=
    { toFun := fun a ↦ ⟨inverseDiffeomorph I J C a.1, a.2⟩
      invFun := fun a ↦ ⟨inverseDiffeomorph I J C a.1, a.2⟩
      left_inv := fun a ↦ Subtype.ext (inverseDiffeomorph_inverseDiffeomorph I J C a.1)
      right_inv := fun a ↦ Subtype.ext (inverseDiffeomorph_inverseDiffeomorph I J C a.1)
      continuous_toFun :=
        ((inverseDiffeomorph I J C).continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun :=
        ((inverseDiffeomorph I J C).continuous.comp continuous_subtype_val).subtype_mk _ }
  exact e.t2Space

/-! ### Composable pairs and multiplication -/

/-- The smooth manifold atlas on geometric composable pairs
`{p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}` (`Γ ×_{s,t} Γ`). It uses the
subspace topology and is not installed as a global instance. -/
@[instance_reducible]
noncomputable def composablePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
  transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- The geometric composable pairs `Γ ×_{s,t} Γ` form a smooth manifold of dimension
`2 dim Γ - dim M`. -/
theorem isManifold_composablePairs :
    letI := composablePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
  isManifold_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- The inclusion `Γ ×_{s,t} Γ ↪ Γ × Γ` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} →
        Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- Geometric multiplication `(g, h) ↦ h.comp g` is smooth with respect to
`composablePairsChartedSpace`. -/
theorem contMDiff_mul_composablePairs :
    letI := composablePairsChartedSpace I J C
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        p.1.2.comp p.1.1 p.2.symm :=
  contMDiff_mul (I := I) (J := J) (C := C)

/-- A tangent vector to `Γ × Γ` lies in the image of `Γ ×_{s,t} Γ ↪ Γ × Γ` if and only if
`ds(v₁) = dt(v₂)` after identifying target tangent spaces. -/
theorem mem_range_mfderiv_coe_composablePairs_iff :
    letI := composablePairsChartedSpace I J C
    ∀ (p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})
      (v : TangentSpace (J.prod J) p.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J)
        (Subtype.val : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} →
          Quiver.Total C × Quiver.Total C) p).range ↔
      mfderiv J I (Quiver.Total.left : Quiver.Total C → C) p.1.1 v.1 =
        tangentSpaceCast I p.1.2.right p.1.1.left
          (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) p.1.2 v.2) :=
  mem_range_mfderiv_coe_transverseFiberProduct_iff (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- Every pair `(v, w)` with `ds(v) = dt(w)` arises as the pair of projection differentials of some
tangent vector to `Γ ×_{s,t} Γ`. -/
theorem exists_mfderiv_eq_of_composablePairs :
    letI := composablePairsChartedSpace I J C
    ∀ (p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})
      (v : TangentSpace J p.1.1) (w : TangentSpace J p.1.2),
      mfderiv J I (Quiver.Total.left : Quiver.Total C → C) p.1.1 v =
        tangentSpaceCast I p.1.2.right p.1.1.left
          (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) p.1.2 w) →
      ∃ ξ, mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ q.1.1) p ξ = v ∧
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ q.1.2) p ξ = w :=
  exists_mfderiv_eq_of_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- A tangent vector to `Γ ×_{s,t} Γ` vanishes whenever both projection differentials vanish on
it. -/
theorem eq_zero_of_mfderiv_composablePairs :
    letI := composablePairsChartedSpace I J C
    ∀ (p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})
      (ξ : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) p),
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ q.1.1) p ξ = 0 →
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ q.1.2) p ξ = 0 →
        ξ = 0 :=
  eq_zero_of_mfderiv_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- The first projection `Γ ×_{s,t} Γ → Γ` is a smooth submersion (base change of `t`). -/
theorem isSubmersion_fst_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.1) :=
  isSubmersion_fst_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))
    (isSubmersion_target (I := I) (J := J) (C := C))

/-- The second projection `Γ ×_{s,t} Γ → Γ` is a smooth submersion (base change of `s`). -/
theorem isSubmersion_snd_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.2) :=
  isSubmersion_snd_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))
    (isSubmersion_source (I := I) (J := J) (C := C))

include I in
/-- The product of two smooth families of arrows with matching source and target is smooth. -/
theorem contMDiff_mul_of_contMDiff {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {f g : X → Quiver.Total C} (hf : ContMDiff IX J ∞ f) (hg : ContMDiff IX J ∞ g)
    (h : ∀ x, (f x).left = (g x).right) :
    ContMDiff IX J ∞ fun x ↦ (g x).comp (f x) (h x).symm := by
  let := composablePairsChartedSpace I J C
  have hpair : ContMDiff IX
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun x : X ↦ (⟨(f x, g x), h x⟩ :
        {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})) :=
    (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr (hf.prodMk hg)
  exact (contMDiff_mul (I := I) (J := J) (C := C)).comp hpair

/-- The smooth manifold atlas on categorical composable pairs
`{p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}` (`Γ ×_{t,s} Γ`). -/
@[instance_reducible]
noncomputable def categoricalComposablePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
  transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))

/-- The categorical composable pairs `Γ ×_{t,s} Γ` form a smooth manifold. -/
theorem isManifold_categoricalComposablePairs :
    letI := categoricalComposablePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
  isManifold_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))

/-- The inclusion `Γ ×_{t,s} Γ ↪ Γ × Γ` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_categoricalComposablePairs :
    letI := categoricalComposablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} →
        Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))

/-- The first projection `Γ ×_{t,s} Γ → Γ` is a smooth submersion. -/
theorem isSubmersion_fst_categoricalComposablePairs :
    letI := categoricalComposablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.1) :=
  isSubmersion_fst_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- The second projection `Γ ×_{t,s} Γ → Γ` is a smooth submersion. -/
theorem isSubmersion_snd_categoricalComposablePairs :
    letI := categoricalComposablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.2) :=
  isSubmersion_snd_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))
    (isSubmersion_target (I := I) (J := J) (C := C))

/-- Swapping the two entries identifies geometric composable pairs `(g, h)` (`s(g) = t(h)`) with
categorical composable pairs `(h, g)` (`t(h) = s(g)`). -/
noncomputable def composablePairsSwapDiffeomorph :
    letI := composablePairsChartedSpace I J C
    letI := categoricalComposablePairsChartedSpace I J C
    {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} := by
  letI := composablePairsChartedSpace I J C
  letI := categoricalComposablePairsChartedSpace I J C
  exact
    { toFun := fun p ↦ ⟨(p.1.2, p.1.1), p.2.symm⟩
      invFun := fun p ↦ ⟨(p.1.2, p.1.1), p.2.symm⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      contMDiff_toFun :=
        (isSmoothEmbedding_coe_categoricalComposablePairs I J C).contMDiff_iff_comp.mpr
          ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff.snd.prodMk
            (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.fst)
      contMDiff_invFun :=
        (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
          ((isSmoothEmbedding_coe_categoricalComposablePairs I J C).contMDiff.snd.prodMk
            (isSmoothEmbedding_coe_categoricalComposablePairs I J C).contMDiff.fst) }

@[simp]
theorem composablePairsSwapDiffeomorph_apply
    (p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}) :
    letI := composablePairsChartedSpace I J C
    letI := categoricalComposablePairsChartedSpace I J C
    composablePairsSwapDiffeomorph I J C p = ⟨(p.1.2, p.1.1), p.2.symm⟩ := (rfl)

@[simp]
theorem composablePairsSwapDiffeomorph_symm_apply
    (p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}) :
    letI := composablePairsChartedSpace I J C
    letI := categoricalComposablePairsChartedSpace I J C
    (composablePairsSwapDiffeomorph I J C).symm p = ⟨(p.1.2, p.1.1), p.2.symm⟩ := (rfl)

/-- Categorical composition `(a, b) ↦ a.comp b` is smooth on `Γ ×_{t,s} Γ`. -/
theorem contMDiff_comp :
    letI := categoricalComposablePairsChartedSpace I J C
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2 := by
  let := composablePairsChartedSpace I J C
  let := categoricalComposablePairsChartedSpace I J C
  have heq : (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2) =
      (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        q.1.2.comp q.1.1 q.2.symm) ∘ (composablePairsSwapDiffeomorph I J C).symm := by
    funext p
    simp [Function.comp_apply]
  rw [heq]
  exact (contMDiff_mul (I := I) (J := J) (C := C)).comp
    (composablePairsSwapDiffeomorph I J C).symm.contMDiff

include I in
/-- The categorical composite of two smooth families of arrows with matching target and source
is smooth. -/
theorem contMDiff_comp_of_contMDiff {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {f g : X → Quiver.Total C} (hf : ContMDiff IX J ∞ f) (hg : ContMDiff IX J ∞ g)
    (h : ∀ x, (f x).right = (g x).left) :
    ContMDiff IX J ∞ fun x ↦ (f x).comp (g x) (h x) :=
  contMDiff_mul_of_contMDiff I J C hg hf fun x ↦ (h x).symm

include I J in
/-- Forgetting the smooth structure of a Lie groupoid yields a topological groupoid on the exact
same topologies on `C` and `Quiver.Total C`. This is stated as a theorem rather than an instance
because the model spaces `I` and `J` do not appear in the conclusion. -/
theorem toIsTopologicalGroupoid : IsTopologicalGroupoid C where
  continuous_source := continuous_source I J C
  continuous_target := continuous_target I J C
  continuous_unit := continuous_unit I J C
  continuous_inverse := continuous_inverse I J C
  continuous_comp := by
    let := categoricalComposablePairsChartedSpace I J C
    exact (contMDiff_comp I J C).continuous

/-! ### Source-matched pairs, shear diffeomorphism, and submersion property of multiplication -/

/-- The smooth manifold atlas on source-matched pairs
`{p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left}` (`Γ ×_{s,s} Γ`). -/
@[instance_reducible]
noncomputable def sourcePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} :=
  transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- The source-matched pairs `Γ ×_{s,s} Γ` form a smooth manifold. -/
theorem isManifold_sourcePairs :
    letI := sourcePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} :=
  isManifold_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- The inclusion `Γ ×_{s,s} Γ ↪ Γ × Γ` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_sourcePairs :
    letI := sourcePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} →
        Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- The shear diffeomorphism `(g, h) ↦ (gh, h)` from `Γ ×_{s,t} Γ` to `Γ ×_{s,s} Γ`, with inverse
`(k, h) ↦ (k h⁻¹, h)`. Factoring multiplication as `pr₁ ∘ mulShearDiffeomorph` shows that
multiplication is a submersion. -/
noncomputable def mulShearDiffeomorph :
    letI := composablePairsChartedSpace I J C
    letI := sourcePairsChartedSpace I J C
    {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} := by
  letI := composablePairsChartedSpace I J C
  letI := sourcePairsChartedSpace I J C
  refine
    { toFun := fun p ↦ ⟨(p.1.2.comp p.1.1 p.2.symm, p.1.2), Quiver.Total.comp_left _ _ _⟩
      invFun := fun q ↦
        ⟨((⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ : Quiver.Total C).comp q.1.1 q.2.symm, q.1.2),
          Quiver.Total.comp_left _ _ _⟩
      left_inv := fun p ↦ Subtype.ext <| Prod.ext
        (Quiver.Total.inv_comp_comp p.1.2 p.1.1 p.2.symm _) rfl
      right_inv := fun q ↦ Subtype.ext <| Prod.ext
        (Quiver.Total.comp_inv_comp q.1.2 q.1.1 q.2.symm _) rfl
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (isSmoothEmbedding_coe_sourcePairs I J C).contMDiff_iff_comp.mpr
      ((contMDiff_mul (I := I) (J := J) (C := C)).prodMk
        (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.snd)
  · refine (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr ?_
    have hfst := (isSmoothEmbedding_coe_sourcePairs I J C).contMDiff.fst
    have hsnd := (isSmoothEmbedding_coe_sourcePairs I J C).contMDiff.snd
    have hinv : ContMDiff
        𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
        (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} ↦
          (⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ : Quiver.Total C)) :=
      (contMDiff_inverse (I := I) (J := J) (C := C)).comp hsnd
    exact (contMDiff_mul_of_contMDiff I J C hfst hinv fun q ↦ q.2).prodMk hsnd

@[simp]
theorem mulShearDiffeomorph_apply
    (p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}) :
    letI := composablePairsChartedSpace I J C
    letI := sourcePairsChartedSpace I J C
    (mulShearDiffeomorph I J C p).val = (p.1.2.comp p.1.1 p.2.symm, p.1.2) := (rfl)

@[simp]
theorem mulShearDiffeomorph_symm_apply
    (q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left}) :
    letI := composablePairsChartedSpace I J C
    letI := sourcePairsChartedSpace I J C
    ((mulShearDiffeomorph I J C).symm q).val =
      ((⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ : Quiver.Total C).comp q.1.1 q.2.symm,
        q.1.2) := (rfl)

/-- Geometric multiplication `m : Γ ×_{s,t} Γ → Γ` is a smooth submersion. -/
theorem isSubmersion_mul :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        p.1.2.comp p.1.1 p.2.symm := by
  let := composablePairsChartedSpace I J C
  let := sourcePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_sourcePairs I J C
  have hfst : Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} ↦ q.1.1) :=
    isSubmersion_fst_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
      (contMDiff_source I J C) (contMDiff_source I J C)
      (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))
      (isSubmersion_source (I := I) (J := J) (C := C))
  have heq : (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
      p.1.2.comp p.1.1 p.2.symm) =
      (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} ↦ q.1.1) ∘
        mulShearDiffeomorph I J C := by
    funext p
    simp [Function.comp_apply]
  rw [heq]
  exact (Manifold.isSubmersionOfComplement_iff.mpr fun p ↦
    ((mulShearDiffeomorph I J C).isLocalDiffeomorph p).isSubmersionAtOfComplement_comp
      (hfst.isSubmersionOfComplement_complement.isSubmersionAt
        (mulShearDiffeomorph I J C p))).isSubmersion

include I J in
/-- Geometric multiplication is an open map. -/
theorem isOpenMap_mul :
    IsOpenMap fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
      p.1.2.comp p.1.1 p.2.symm := by
  let := composablePairsChartedSpace I J C
  exact (isSubmersion_mul I J C).isOpenMap

/-- Categorical composition `Γ ×_{t,s} Γ → Γ` is a smooth submersion. -/
theorem isSubmersion_comp :
    letI := categoricalComposablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2 := by
  let := composablePairsChartedSpace I J C
  let := categoricalComposablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_categoricalComposablePairs I J C
  have heq : (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2) =
      (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        q.1.2.comp q.1.1 q.2.symm) ∘ (composablePairsSwapDiffeomorph I J C).symm := by
    funext p
    simp [Function.comp_apply]
  rw [heq]
  let e := (composablePairsSwapDiffeomorph I J C).symm
  exact (Manifold.isSubmersionOfComplement_iff.mpr fun p ↦
    (e.isLocalDiffeomorph p).isSubmersionAtOfComplement_comp
      ((isSubmersion_mul I J C).isSubmersionOfComplement_complement.isSubmersionAt
        (e p))).isSubmersion

include I J in
/-- Categorical composition is an open map. -/
theorem isOpenMap_comp :
    IsOpenMap fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2 := by
  let := categoricalComposablePairsChartedSpace I J C
  exact (isSubmersion_comp I J C).isOpenMap

/-- The division map `(k, h) ↦ k h⁻¹` on source-matched pairs `Γ ×_{s,s} Γ` is a smooth
submersion onto `Quiver.Total C`. -/
theorem isSubmersion_div_source :
    letI := sourcePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} ↦
        (⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ : Quiver.Total C).comp q.1.1 q.2.symm := by
  let := composablePairsChartedSpace I J C
  let := sourcePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_sourcePairs I J C
  have heq : (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} ↦
      (⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ : Quiver.Total C).comp q.1.1 q.2.symm) =
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.1) ∘
        (mulShearDiffeomorph I J C).symm := by
    funext q
    simp [Function.comp_apply]
  rw [heq]
  exact (Manifold.isSubmersionOfComplement_iff.mpr fun q ↦
    ((mulShearDiffeomorph I J C).symm.isLocalDiffeomorph q).isSubmersionAtOfComplement_comp
      ((isSubmersion_fst_composablePairs I J C).isSubmersionOfComplement_complement.isSubmersionAt
        ((mulShearDiffeomorph I J C).symm q))).isSubmersion

end API

end IsLieGroupoid

end TauCeti
