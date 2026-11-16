/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.RingTheory.TensorProduct.Reduced

import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Geometrically.Integral
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Geometric reducedness and geometric integrality via function fields

Let `X` be an integral scheme over a field `k`. Because every nonempty affine chart `U` of `X` has
section ring `Γ(X, U)` a `k`-subalgebra of `k(X)` with fraction field `k(X)`, geometric reducedness
and geometric integrality of the whole scheme `X` over `k` are completely controlled by the function
field `k(X)` as a `k`-algebra, without any Noetherian, finite-type, or properness assumption:

* `X` is geometrically reduced over `k` if and only if `k(X)` is geometrically reduced over `k`
  (`Algebra.IsGeometricallyReduced k X.functionField`).
* `X` is geometrically integral over `k` if and only if `k` is algebraically closed in `k(X)`
  (`IsIntegrallyClosedIn k X.functionField`) and `k(X)` is geometrically reduced over `k`.

In particular, an integral `k`-scheme whose function field has exact constants `k` is geometrically
integral whenever `k(X)` admits a separating element over `k` (for instance, any function field of
one variable that is separably generated), and automatically whenever `k` is perfect.

## Main results

* `TauCeti.AlgebraicGeometry.geometricallyReduced_Spec_iff`: `Spec A ⟶ Spec k` is geometrically
  reduced iff `Algebra.IsGeometricallyReduced k A`.
* `TauCeti.AlgebraicGeometry.geometricallyReduced_iff_isGeometricallyReduced_functionField`: an
  integral `k`-scheme `X` is geometrically reduced iff `k(X)` is geometrically reduced over `k`.
* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_isGeometricallyReduced_functionField` and
  `geometricallyIntegral_iff_isIntegrallyClosedIn_and_isGeometricallyReduced`: whole-scheme
  geometric integrality from exact constants and geometric reducedness of `k(X)`.
* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_separating_functionField` and
  `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_perfectField`: specializations to separably
  generated function fields and perfect base fields.

## References

* A. Grothendieck, *Éléments de géométrie algébrique* IV₂, Proposition 4.6.1.
* [Stacks Project, Tags 035P, 035Q, and 0364](https://stacks.math.columbia.edu/tag/0364)
-/

public section

open CategoryTheory MorphismProperty Limits AlgebraicGeometry
open scoped TensorProduct IntermediateField

namespace TauCeti.AlgebraicGeometry

universe u

/-- Geometric reducedness of morphisms of schemes respects isomorphisms. -/
instance respectsIso_geometricallyReduced : RespectsIso @GeometricallyReduced :=
  IsStableUnderBaseChange.respectsIso

/-- Geometric reducedness is Zariski-local on the source. -/
instance isZariskiLocalAtSource_geometricallyReduced :
    IsZariskiLocalAtSource @GeometricallyReduced := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 ↦ ?_
  simp only [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  exact ⟨fun hf i K _ y ↦ (IsReduced.iff_of_openCover _
      (Scheme.Pullback.openCoverOfLeft 𝒰 f y)).mp (hf K y) i,
    fun hf K _ y ↦ (IsReduced.iff_of_openCover _
      (Scheme.Pullback.openCoverOfLeft 𝒰 f y)).mpr fun i ↦ hf i K y⟩

/-- Over a field `k`, a geometrically reduced commutative `k`-algebra remains reduced after
tensoring with *any* field extension `K / k`: embed `AlgebraicClosure k` into `AlgebraicClosure K`
and use reducedness of tensor products over the perfect field `AlgebraicClosure k`. -/
private theorem isReduced_tensorProduct_of_isGeometricallyReduced {k A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Algebra.IsGeometricallyReduced k A] (K : Type*) [Field K]
    [Algebra k K] : IsReduced (A ⊗[k] K) := by
  let Ω := AlgebraicClosure K
  let j : AlgebraicClosure k →ₐ[k] Ω := IsAlgClosed.lift
  algebraize [j.toRingHom]
  have : IsScalarTower k (AlgebraicClosure k) Ω :=
    .of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have : _root_.IsReduced (AlgebraicClosure k ⊗[k] A) :=
    (Algebra.isGeometricallyReduced_field_iff k A).mp inferInstance
  have : _root_.IsReduced (Ω ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] A)) := inferInstance
  have : _root_.IsReduced (Ω ⊗[k] A) :=
    isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) Ω Ω A).symm
      (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) Ω Ω A).symm.injective
  have : _root_.IsReduced (K ⊗[k] A) :=
    isReduced_of_injective
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K Ω) (AlgHom.id k A))
      (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))
  exact isReduced_of_injective (Algebra.TensorProduct.comm k A K)
    (Algebra.TensorProduct.comm k A K).injective

/-- For a commutative algebra `A` over a field `k`, `Spec A ⟶ Spec k` is geometrically reduced if
and only if `A` is geometrically reduced over `k` (`Algebra.IsGeometricallyReduced k A`). -/
@[stacks 035P]
theorem geometricallyReduced_Spec_iff {k A : Type u} [Field k] [CommRing A] [Algebra k A] :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔
      Algebra.IsGeometricallyReduced k A := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine ⟨fun h ↦ ?_, fun _ K _ _ ↦ ?_⟩
  · have hpb : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
      h (AlgebraicClosure k)
    have hSpec : IsReduced (Spec (.of (A ⊗[k] AlgebraicClosure k))) :=
      isReduced_of_isOpenImmersion (pullbackSpecIso k A (AlgebraicClosure k)).inv
    have : _root_.IsReduced (A ⊗[k] AlgebraicClosure k) :=
      (affine_isReduced_iff (.of (A ⊗[k] AlgebraicClosure k))).mp hSpec
    rw [Algebra.isGeometricallyReduced_field_iff]
    exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) A)
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).injective
  · have : _root_.IsReduced (A ⊗[k] K) := isReduced_tensorProduct_of_isGeometricallyReduced K
    have : IsReduced (Spec (.of (A ⊗[k] K))) :=
      (affine_isReduced_iff (.of (A ⊗[k] K))).mpr inferInstance
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k A K).hom

section FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- If an integral `k`-scheme `X` is geometrically reduced over `k`, then its function field `k(X)`
is geometrically reduced over `k`. -/
theorem isGeometricallyReduced_functionField_of_geometricallyReduced
    [GeometricallyReduced (X ↘ Spec (.of k))] :
    Algebra.IsGeometricallyReduced k X.functionField := by
  obtain ⟨U, hU, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  have hSpec : GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) := by
    rw [← hw]
    exact IsZariskiLocalAtSource.comp ‹GeometricallyReduced (X ↘ Spec (.of k))› hU.fromSpec
  have : Algebra.IsGeometricallyReduced k Γ(X, U) := geometricallyReduced_Spec_iff.mp hSpec
  have : _root_.IsReduced (Γ(X, U) ⊗[k] AlgebraicClosure k) :=
    isReduced_tensorProduct_of_isGeometricallyReduced (AlgebraicClosure k)
  have : _root_.IsReduced (X.functionField ⊗[k] AlgebraicClosure k) :=
    isReduced_tensorProduct_of_isLocalization (nonZeroDivisors Γ(X, U)) X.functionField
      (AlgebraicClosure k)
  exact (Algebra.isGeometricallyReduced_field_iff k X.functionField).mpr
    (isReduced_of_injective
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) X.functionField)
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) X.functionField).injective)

/-- Conversely, if the function field `k(X)` of an integral `k`-scheme `X` is geometrically reduced
over `k`, then `X` is geometrically reduced over `k`. -/
theorem geometricallyReduced_of_isGeometricallyReduced_functionField
    [Algebra.IsGeometricallyReduced k X.functionField] :
    GeometricallyReduced (X ↘ Spec (.of k)) := by
  have hmem (x : X) := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  choose U hU hxU _ using hmem
  have hcov : (⨆ x : X, U x) = ⊤ :=
    top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @GeometricallyReduced) U hcov]
  intro x
  have : Nonempty (U x) := ⟨⟨x, hxU x⟩⟩
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ (U x) le_top
  algebraize [φ.hom]
  have : IsScalarTower k Γ(X, U x) X.functionField :=
    .of_algebraMap_eq' (Scheme.baseRingToFunctionField_eq_comp_appLE k X (U x))
  have := functionField_isFractionRing_of_isAffineOpen X (U x) (hU x)
  have : Algebra.IsGeometricallyReduced k Γ(X, U x) :=
    Algebra.IsGeometricallyReduced.of_injective (IsScalarTower.toAlgHom k Γ(X, U x) X.functionField)
      (IsFractionRing.injective Γ(X, U x) X.functionField)
  rw [← (hU x).isoSpec_hom_fromSpec, Category.assoc,
    cancel_left_of_respectsIso @GeometricallyReduced, (hU x).fromSpec_comp_eq_SpecMap]
  exact (geometricallyReduced_Spec_iff (k := k) (A := Γ(X, U x))).mpr inferInstance

/-- **An integral `k`-scheme is geometrically reduced if and only if its function field is
geometrically reduced over `k`.** -/
@[stacks 035Q]
theorem geometricallyReduced_iff_isGeometricallyReduced_functionField :
    GeometricallyReduced (X ↘ Spec (.of k)) ↔ Algebra.IsGeometricallyReduced k X.functionField :=
  ⟨fun _ ↦ isGeometricallyReduced_functionField_of_geometricallyReduced,
    fun _ ↦ geometricallyReduced_of_isGeometricallyReduced_functionField⟩

/-- If `k` is algebraically closed in `k(X)` and `k(X)` is geometrically reduced over `k`, then the
whole integral scheme `X` is geometrically integral over `k`. -/
@[stacks 0364]
theorem geometricallyIntegral_of_isGeometricallyReduced_functionField
    (hex : IsIntegrallyClosedIn k X.functionField)
    [Algebra.IsGeometricallyReduced k X.functionField] :
    GeometricallyIntegral (X ↘ Spec (.of k)) := by
  have : GeometricallyReduced (X ↘ Spec (.of k)) :=
    geometricallyReduced_of_isGeometricallyReduced_functionField
  have hSpecInt : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k X.functionField))) := by
    rw [geometricallyIntegral_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    have : IsDomain (X.functionField ⊗[k] K) :=
      isDomain_tensorProduct_of_isGeometricallyReduced hex K
    have : IsIntegral (Spec (.of (X.functionField ⊗[k] K))) :=
      (affine_isIntegral_iff (.of (X.functionField ⊗[k] K))).mpr inferInstance
    exact .of_isIso (pullbackSpecIso k X.functionField K).inv
  have hcomp : GeometricallyIrreducible
      (X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (.of k))) := by
    rw [X.fromSpecStalk_genericPoint_comp_over (k := k)]
    infer_instance
  have : GeometricallyIrreducible (X ↘ Spec (.of k)) :=
    GeometricallyIrreducible.of_comp_isDominant (X.fromSpecStalk (genericPoint X)) _
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- **Characterization of geometrically integral schemes via their function field.** An integral
`k`-scheme `X` is geometrically integral over `k` if and only if `k` is algebraically closed in
`k(X)` and `k(X)` is geometrically reduced over `k`. -/
@[stacks 0364]
theorem geometricallyIntegral_iff_isIntegrallyClosedIn_and_isGeometricallyReduced :
    GeometricallyIntegral (X ↘ Spec (.of k)) ↔
      IsIntegrallyClosedIn k X.functionField ∧ Algebra.IsGeometricallyReduced k X.functionField :=
  ⟨fun _ ↦ ⟨isIntegrallyClosedIn_functionField_of_geometricallyIntegral,
      isGeometricallyReduced_functionField_of_geometricallyReduced⟩,
    fun ⟨hex, _⟩ ↦ geometricallyIntegral_of_isGeometricallyReduced_functionField hex⟩

/-- If `k` is algebraically closed in `k(X)` and `k(X)` is separable algebraic over `k(x)` for some
`x ∈ k(X)`, then `X` is geometrically integral over `k`. -/
theorem geometricallyIntegral_of_separating_functionField
    (hex : IsIntegrallyClosedIn k X.functionField) {x : X.functionField}
    [Algebra.IsSeparable k⟮x⟯ X.functionField] :
    GeometricallyIntegral (X ↘ Spec (.of k)) := by
  have : IsDomain (X.functionField ⊗[k] AlgebraicClosure k) :=
    isDomain_tensorProduct_of_separating (x := x) hex (AlgebraicClosure k)
  have : Algebra.IsGeometricallyReduced k X.functionField :=
    (Algebra.isGeometricallyReduced_field_iff k X.functionField).mpr
      (isReduced_of_injective
        (Algebra.TensorProduct.comm k (AlgebraicClosure k) X.functionField)
        (Algebra.TensorProduct.comm k (AlgebraicClosure k) X.functionField).injective)
  exact geometricallyIntegral_of_isGeometricallyReduced_functionField hex

/-- Over a perfect field `k`, an integral `k`-scheme `X` is geometrically integral over `k` as soon
as `k` is algebraically closed in `k(X)`. -/
theorem geometricallyIntegral_of_perfectField [PerfectField k]
    (hex : IsIntegrallyClosedIn k X.functionField) :
    GeometricallyIntegral (X ↘ Spec (.of k)) :=
  geometricallyIntegral_of_isGeometricallyReduced_functionField hex

end FunctionField

end TauCeti.AlgebraicGeometry
