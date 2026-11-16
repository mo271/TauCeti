/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Field
public import TauCeti.FieldTheory.PurelyInseparable.TensorProduct
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import TauCeti.RingTheory.Smooth.Regular
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Smooth.Locus
import TauCeti.RingTheory.RegularLocalRing.Flat
import TauCeti.RingTheory.RegularLocalRing.Smooth
import TauCeti.RingTheory.Smooth.Field

/-!
# Geometrically regular algebras over a field

An algebra `B` over a field `k` is *geometrically regular* if `B` is Noetherian and the base
change `L ⊗[k] B` is a regular ring for every finite purely inseparable extension `L / k`
(Stacks, Definition 10.166.2, in the form of Lemma 10.166.1). Stacks, Lemma 10.166.1, shows that
for arbitrary Noetherian `B` this is equivalent to regularity of `L ⊗[k] B` for every finitely
generated field extension `L / k`; that general non-finite-type equivalence is not proved here.
Geometric regularity of the fibres is the condition defining regular ring maps, G-rings and
excellent rings.

When `B` is of finite type over `k`, geometric regularity is equivalent to smoothness over `k`
(`TauCeti.Excellence.geometricallyRegular_iff_smooth`), and therefore implies regularity of
`K ⊗[k] B` for *every* field extension `K / k`. Indeed, for finite-type `B` each prime of
`K ⊗[k] B` for an arbitrary purely inseparable extension `K / k` is finitely generated, hence
extended from `L ⊗[k] B` for a finite purely inseparable subextension `L / k`, so regularity
ascends to `perfectClosure k (AlgebraicClosure k) ⊗[k] B`; over a perfect field `K`, regularity of
`K ⊗[k] B` implies smoothness over `K` (`TauCeti.formallySmooth_of_isRegularLocalRing`), and
smoothness descends along the faithfully flat map `k → K`.

Regularity of `B` itself does not suffice: a nontrivial finite purely inseparable extension `L / k`
is a field, hence regular, but `L ⊗[k] L` is not reduced, so `L` is not geometrically regular over
`k`.

## Main definitions and results

* `TauCeti.Excellence.GeometricallyRegular k B`: `B` is a geometrically regular `k`-algebra.
* `TauCeti.Excellence.GeometricallyRegular.isRegularRing`: a geometrically regular algebra is a
  regular ring.
* `TauCeti.Excellence.GeometricallyRegular.isRegularRing_tensorProduct'`: the base change to a
  finite purely inseparable extension in any universe is a regular ring.
* `AlgEquiv.geometricallyRegular`: geometric regularity is invariant under isomorphisms of
  `k`-algebras.
* `TauCeti.Excellence.GeometricallyRegular.of_smooth`: a smooth `k`-algebra is geometrically
  regular; this covers `k` itself, the zero algebra and polynomial rings in finitely many
  variables.
* `Algebra.Smooth.of_isRegularRing_of_perfectField` and
  `Algebra.Smooth.of_isRegularRing_tensorProduct_of_perfectField`: a finite-type algebra over `k`
  that becomes regular over a perfect extension `K / k` is smooth over `k`.
* `TauCeti.Excellence.GeometricallyRegular.isRegularRing_of_isPurelyInseparable`: for finite-type
  `B`, geometric regularity persists along arbitrary purely inseparable extensions `K / k`.
* `TauCeti.Excellence.GeometricallyRegular.smooth` and
  `TauCeti.Excellence.geometricallyRegular_iff_smooth`: for finite-type `B`, geometric regularity
  is equivalent to `Algebra.Smooth k B`.
* `TauCeti.Excellence.GeometricallyRegular.isRegularRing_tensorProduct_of_finiteType`,
  `Algebra.Smooth.iff_isRegularRing_tensorProduct_of_perfectField`, and
  `Algebra.Smooth.iff_forall_isRegularRing_tensorProduct`: equivalences with regularity after field
  base change.
* `TauCeti.Excellence.GeometricallyRegular.of_isSeparable`: a finite separable field extension is
  geometrically regular.
* `TauCeti.Excellence.GeometricallyRegular.surjective_algebraMap_of_algHom`: a nonzero
  geometrically regular `k`-algebra receives no `k`-algebra map from a nontrivial finite purely
  inseparable extension of `k`.
* `TauCeti.Excellence.geometricallyRegular_iff_isSeparable`: a finite purely inseparable extension
  is geometrically regular exactly when it is separable, that is, trivial.
* `TauCeti.Excellence.geometricallyRegular_tensorProduct_iff_of_bijective`: geometric regularity
  is unchanged by base change along an isomorphism of fields `k → K`.
* `TauCeti.Excellence.GeometricallyRegular.of_isLocalization`: a localization of a field is
  geometrically regular.
* `TauCeti.Excellence.not_geometricallyRegular_trivSqZeroExt`: the dual numbers `k[ε]/(ε²)` are
  not geometrically regular.

## References

* The Stacks Project, Section 10.140 (Smooth algebras over fields) and Section 10.166
  (Geometrically regular algebras), Lemma 10.166.1 and Definition 10.166.2.
* A. Grothendieck, *Éléments de géométrie algébrique* IV₂, Section 6.7, and IV₄, Section 17.15.
-/

public section

universe u v w

open TensorProduct

namespace TauCeti.Excellence

/-- An algebra `B` over a field `k` is *geometrically regular* if `B` is Noetherian and
`L ⊗[k] B` is a regular ring for every finite purely inseparable field extension `L / k`
(Stacks, Definition 10.166.2, in the form of Lemma 10.166.1). The extensions `L` range over the
universe of `k`; `GeometricallyRegular.isRegularRing_tensorProduct'` removes that restriction. -/
class GeometricallyRegular (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B] :
    Prop where
  /-- A geometrically regular algebra is Noetherian. -/
  isNoetherianRing : IsNoetherianRing B
  /-- The base change of a geometrically regular algebra to a finite purely inseparable extension
  of the base field is a regular ring. -/
  isRegularRing_tensorProduct (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
    [IsPurelyInseparable k L] : IsRegularRing (L ⊗[k] B)

attribute [instance] GeometricallyRegular.isRegularRing_tensorProduct

namespace GeometricallyRegular

variable {k : Type u} {B : Type v} {B' : Type w} [Field k] [CommRing B] [Algebra k B]
  [CommRing B'] [Algebra k B']

variable (k) in
/-- A geometrically regular algebra is a regular ring: take `L = k`. -/
theorem isRegularRing [GeometricallyRegular k B] : IsRegularRing B :=
  .of_ringEquiv (Algebra.TensorProduct.lid k B).toRingEquiv

/-- The extensions `L` in the definition range over the universe of `k`, but the base change to a
finite purely inseparable extension `L / k` in any universe is a regular ring: `L` has a copy
`Shrink L` in the universe of `k`. -/
theorem isRegularRing_tensorProduct' [GeometricallyRegular k B] (L : Type*) [Field L]
    [Algebra k L] [Module.Finite k L] [IsPurelyInseparable k L] : IsRegularRing (L ⊗[k] B) := by
  have : Small.{u} L := Module.Finite.small k L
  let e : Shrink.{u} L ≃ₐ[k] L := Shrink.algEquiv k L
  have : Module.Finite k (Shrink.{u} L) := .equiv e.symm.toLinearEquiv
  have : IsPurelyInseparable k (Shrink.{u} L) := e.symm.isPurelyInseparable
  exact .of_ringEquiv (Algebra.TensorProduct.congr e AlgEquiv.refl).toRingEquiv

/-- Geometric regularity is invariant under isomorphisms of `k`-algebras. -/
theorem _root_.AlgEquiv.geometricallyRegular (e : B ≃ₐ[k] B') [GeometricallyRegular k B] :
    GeometricallyRegular k B' where
  isNoetherianRing :=
    have := ‹GeometricallyRegular k B›.isNoetherianRing
    isNoetherianRing_of_ringEquiv B e.toRingEquiv
  isRegularRing_tensorProduct L _ _ _ _ :=
    .of_ringEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) e).toRingEquiv

/-- A smooth algebra over a field is geometrically regular: its base change to any field is smooth
over that field, hence regular. -/
instance (priority := 100) of_smooth [Algebra.Smooth k B] : GeometricallyRegular k B where
  isNoetherianRing := Algebra.FiniteType.isNoetherianRing k B
  isRegularRing_tensorProduct L _ _ _ _ := IsRegularRing.of_smooth (R := L)

/-- A finite separable field extension is geometrically regular, being étale over the base. -/
instance (priority := 100) of_isSeparable (K : Type v) [Field K] [Algebra k K] [Module.Finite k K]
    [Algebra.IsSeparable k K] : GeometricallyRegular k K :=
  have : Algebra.FormallyEtale k K := .of_isSeparable k K
  have : Algebra.Etale k K :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  inferInstance

/-- A nonzero geometrically regular `k`-algebra `B` receives no `k`-algebra map from a nontrivial
finite purely inseparable extension `L / k`: if `f : L →ₐ[k] B` exists, then `L = k`. Indeed
`L ⊗[k] L` embeds into the regular, hence reduced, ring `L ⊗[k] B`. -/
theorem surjective_algebraMap_of_algHom [GeometricallyRegular k B] [Nontrivial B] (L : Type u)
    [Field L] [Algebra k L] [Module.Finite k L] [IsPurelyInseparable k L] (f : L →ₐ[k] B) :
    Function.Surjective (algebraMap k L) :=
  have : IsReduced (L ⊗[k] L) :=
    isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id k L) f)
      (TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id f.toRingHom.injective)
  IsPurelyInseparable.surjective_algebraMap_of_isReduced_tensorProduct k L

end GeometricallyRegular

/-- A finite purely inseparable extension `L / k` is geometrically regular if and only if it is
separable, that is, if and only if `L = k`. -/
theorem geometricallyRegular_iff_isSeparable {k : Type u} [Field k] (L : Type u) [Field L]
    [Algebra k L] [Module.Finite k L] [IsPurelyInseparable k L] :
    GeometricallyRegular k L ↔ Algebra.IsSeparable k L := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ .of_isSeparable L⟩
  have hs := GeometricallyRegular.surjective_algebraMap_of_algHom L (AlgHom.id k L)
  exact AlgEquiv.Algebra.isSeparable
    (AlgEquiv.ofBijective (Algebra.ofId k L) ⟨(algebraMap k L).injective, hs⟩)

/-- The dual numbers `k[ε]/(ε²)` over a field `k` are not geometrically regular: they are not even
reduced. -/
theorem not_geometricallyRegular_trivSqZeroExt (k : Type u) [Field k] :
    ¬ GeometricallyRegular k (TrivSqZeroExt k k) := by
  intro h
  have := h.isRegularRing k
  have hε : IsNilpotent (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) :=
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  simpa using congrArg TrivSqZeroExt.snd hε.eq_zero

/-- Geometric regularity does not see an isomorphism of base fields: if `algebraMap k K` is
bijective, then `K ⊗[k] B` is geometrically regular over `K` if and only if `B` is geometrically
regular over `k`. -/
theorem geometricallyRegular_tensorProduct_iff_of_bijective {k : Type u} {K : Type w} [Field k]
    [Field K] [Algebra k K] (h : Function.Bijective (algebraMap k K)) (B : Type v) [CommRing B]
    [Algebra k B] : GeometricallyRegular K (K ⊗[k] B) ↔ GeometricallyRegular k B := by
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) h
  let φ : K ⊗[k] B ≃ₐ[k] B :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid k B)
  refine ⟨fun hK ↦ ⟨?_, fun L _ _ _ _ ↦ ?_⟩, fun hk ↦ ⟨?_, fun L _ _ _ _ ↦ ?_⟩⟩
  · have := hK.isNoetherianRing
    exact isNoetherianRing_of_ringEquiv _ φ.toRingEquiv
  · -- Make `L` a `K`-algebra through `K ≃ k`, and cancel the base change along `k → K`.
    let : Algebra K L := ((algebraMap k L).comp e.symm.toRingHom).toAlgebra
    have : IsScalarTower k K L := .of_algebraMap_eq fun x ↦
      congrArg (algebraMap k L) (e.symm_apply_apply x).symm
    have : Module.Finite K L := .of_restrictScalars_finite k K L
    have : IsPurelyInseparable K L := .tower_top k K L
    have := GeometricallyRegular.isRegularRing_tensorProduct' (k := K) (B := K ⊗[k] B) L
    exact .of_ringEquiv (Algebra.TensorProduct.cancelBaseChange k K K L B).toRingEquiv
  · have := hk.isNoetherianRing
    exact isNoetherianRing_of_ringEquiv _ φ.symm.toRingEquiv
  · let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    have : IsScalarTower k K L := .of_algebraMap_eq fun _ ↦ rfl
    have : Module.Finite k K := .of_surjective (Algebra.linearMap k K) h.2
    have : Module.Finite k L := .trans K L
    have : IsPurelyInseparable k K := e.isPurelyInseparable
    have : IsPurelyInseparable k L := .trans k K L
    have := GeometricallyRegular.isRegularRing_tensorProduct' (k := k) (B := B) L
    exact .of_ringEquiv (Algebra.TensorProduct.cancelBaseChange k K K L B).symm.toRingEquiv

/-- A localization of a field `k` is geometrically regular over `k`: it is either zero or `k`
itself, and in both cases smooth over `k`. -/
theorem GeometricallyRegular.of_isLocalization {k : Type u} [Field k] (M : Submonoid k)
    (B : Type v) [CommRing B] [Algebra k B] [IsLocalization M B] : GeometricallyRegular k B := by
  by_cases h0 : (0 : k) ∈ M
  · have := IsLocalization.subsingleton (S := B) h0
    infer_instance
  · have : Algebra.Smooth k B := .of_equiv <| IsLocalization.atUnits k M (S := B) fun x hx ↦
      (isUnit_iff_ne_zero.mpr fun h ↦ h0 (h ▸ hx))
    infer_instance

/-! ### Finite-type algebras: geometric regularity and smoothness -/

/-- **A regular algebra of finite type over a perfect field is smooth.** Every localization at a
prime is a regular local algebra essentially of finite type over a perfect field, hence formally
smooth (`TauCeti.formallySmooth_of_isRegularLocalRing`). -/
theorem _root_.Algebra.Smooth.of_isRegularRing_of_perfectField {k : Type u} {B : Type v} [Field k]
    [PerfectField k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsRegularRing B] :
    Algebra.Smooth k B := by
  have : Algebra.FinitePresentation k B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q ↦ ?_), inferInstance⟩
  exact formallySmooth_of_isRegularLocalRing (k := k) (S := Localization.AtPrime q.asIdeal)

/-- If `B` is of finite type over `k` and `K ⊗[k] B` is regular for a perfect extension `K / k`,
then `B` is smooth over `k`: `K ⊗[k] B` is smooth over `K`, and smoothness descends along the
faithfully flat map `k → K`. -/
theorem _root_.Algebra.Smooth.of_isRegularRing_tensorProduct_of_perfectField {k : Type u}
    {B : Type v} (K : Type w) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    [Field K] [PerfectField K] [Algebra k K] [IsRegularRing (K ⊗[k] B)] :
    Algebra.Smooth k B := by
  have : Algebra.Smooth K (K ⊗[k] B) := .of_isRegularRing_of_perfectField
  exact .of_smooth_tensorProduct_of_faithfullyFlat K

/-- Every finite subset of `K ⊗[k] B`, for an algebraic extension `K / k`, lies in the image of
`L ⊗[k] B` for a finite intermediate field `L` of `K / k`. -/
private theorem exists_finite_intermediateField_subset_range {k : Type u} {B : Type v} {K : Type w}
    [Field k] [CommRing B] [Algebra k B] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (s : Finset (K ⊗[k] B)) :
    ∃ (L : IntermediateField k K), Module.Finite k L ∧
      (s : Set (K ⊗[k] B)) ⊆ Set.range (Algebra.TensorProduct.map L.val (AlgHom.id k B)) := by
  obtain ⟨M, hM, hsM⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite (s : Set (K ⊗[k] B)) s.finite_toSet
  obtain ⟨t, rfl⟩ := Module.Finite.iff_fg.mp hM
  let L : IntermediateField k K := IntermediateField.adjoin k (t : Set K)
  have hfin : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral
  have hle : Submodule.span k (t : Set K) ≤ L.toSubmodule :=
    Submodule.span_le.mpr (IntermediateField.subset_adjoin k (t : Set K))
  let φ : L ⊗[k] B →ₐ[k] K ⊗[k] B := Algebra.TensorProduct.map L.val (AlgHom.id k B)
  have hcomp (w : Submodule.span k (t : Set K) ⊗[k] B) :
      φ ((Submodule.inclusion hle).rTensor B w) =
        (Submodule.span k (t : Set K)).subtype.rTensor B w := by
    induction w with
    | tmul m b => simp [φ]
    | add w₁ w₂ hw₁ hw₂ => simp only [map_add, hw₁, hw₂]
  refine ⟨L, hfin, fun z hz ↦ ?_⟩
  obtain ⟨w, rfl⟩ := hsM hz
  exact ⟨(Submodule.inclusion hle).rTensor B w, hcomp w⟩

/-- If `f : R →+* S` is flat with `R` regular and `(Q.comap f).map f = Q`, then `S_Q` is a regular
local ring. -/
private theorem isRegularLocalRing_of_ringHom_flat {R S : Type*} [CommRing R] [CommRing S]
    [IsRegularRing R] [IsNoetherianRing S] (f : R →+* S) (hf : f.Flat) (Q : Ideal S) [Q.IsPrime]
    (hmap : (Q.comap f).map f = Q) : IsRegularLocalRing (Localization.AtPrime Q) := by
  let P₀ : Ideal R := Q.comap f
  have : P₀.IsPrime := Q.comap_isPrime f
  have := hf.localRingHom Q P₀ rfl
  algebraize [Localization.localRingHom P₀ Q f rfl]
  refine TauCeti.IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq (R := Localization.AtPrime P₀) ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    show (algebraMap (Localization.AtPrime P₀) (Localization.AtPrime Q)).comp
        (algebraMap R (Localization.AtPrime P₀)) =
      (algebraMap S (Localization.AtPrime Q)).comp f
      from RingHom.ext (Localization.localRingHom_to_map P₀ Q f rfl),
    ← Ideal.map_map, hmap, Localization.AtPrime.map_eq_maximalIdeal]

/-- **Geometric regularity of a finite-type algebra persists along arbitrary purely inseparable
extensions.** Every prime `Q` of the Noetherian ring `K ⊗[k] B` is extended from `L ⊗[k] B` for a
finite purely inseparable subextension `L / k`, and regularity ascends along the flat local map
`(L ⊗[k] B)_{Q ∩ (L ⊗[k] B)} → (K ⊗[k] B)_Q`. -/
theorem GeometricallyRegular.isRegularRing_of_isPurelyInseparable {k : Type u} {B : Type v}
    [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [GeometricallyRegular k B]
    (K : Type w) [Field K] [Algebra k K] [IsPurelyInseparable k K] :
    IsRegularRing (K ⊗[k] B) := by
  have : IsNoetherianRing (K ⊗[k] B) := Algebra.FiniteType.isNoetherianRing K (K ⊗[k] B)
  refine isRegularRing_iff.mpr fun Q _ ↦ ?_
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian Q
  obtain ⟨L, _, hrange⟩ := exists_finite_intermediateField_subset_range s
  have : IsPurelyInseparable k L := IsPurelyInseparable.tower_bot k L K
  have := GeometricallyRegular.isRegularRing_tensorProduct' (k := k) (B := B) L
  refine isRegularLocalRing_of_ringHom_flat _ (RingHom.Flat.tensorProductMap (f := L.val)
    (g := AlgHom.id k B) (.of_isField (Field.toIsField L) _) (.id B)) Q ?_
  refine le_antisymm Ideal.map_comap_le (hs ▸ Ideal.span_le.mpr fun z hz ↦ ?_)
  obtain ⟨z₀, rfl⟩ := hrange hz
  exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr (Ideal.subset_span hz))

/-- **A geometrically regular algebra of finite type over a field is smooth.** Base-changing to the
perfect closure of `k` inside `AlgebraicClosure k` yields a regular algebra over a perfect field,
hence smooth, and smoothness descends to `k`. -/
theorem GeometricallyRegular.smooth {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [GeometricallyRegular k B] : Algebra.Smooth k B := by
  have := GeometricallyRegular.isRegularRing_of_isPurelyInseparable (k := k) (B := B)
    (perfectClosure k (AlgebraicClosure k))
  exact .of_isRegularRing_tensorProduct_of_perfectField (perfectClosure k (AlgebraicClosure k))

/-- **For a finite-type algebra over a field, geometric regularity is equivalent to smoothness.** -/
theorem geometricallyRegular_iff_smooth {k : Type u} {B : Type v} [Field k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] :
    GeometricallyRegular k B ↔ Algebra.Smooth k B :=
  ⟨fun _ ↦ GeometricallyRegular.smooth, fun _ ↦ inferInstance⟩

/-- The base change of a geometrically regular finite-type `k`-algebra to *any* field extension
`K / k`, in any universe, is a regular ring. -/
theorem GeometricallyRegular.isRegularRing_tensorProduct_of_finiteType {k : Type u} {B : Type v}
    [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [GeometricallyRegular k B]
    (K : Type w) [Field K] [Algebra k K] : IsRegularRing (K ⊗[k] B) := by
  have := GeometricallyRegular.smooth (k := k) (B := B)
  exact IsRegularRing.of_smooth (R := K)

/-- A finite-type `k`-algebra `B` is smooth over `k` if and only if `K ⊗[k] B` is a regular ring
for a given perfect field extension `K / k`. -/
theorem _root_.Algebra.Smooth.iff_isRegularRing_tensorProduct_of_perfectField {k : Type u}
    {B : Type v} (K : Type w) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    [Field K] [PerfectField K] [Algebra k K] :
    Algebra.Smooth k B ↔ IsRegularRing (K ⊗[k] B) :=
  ⟨fun _ ↦ IsRegularRing.of_smooth (R := K),
    fun _ ↦ .of_isRegularRing_tensorProduct_of_perfectField K⟩

/-- A finite-type `k`-algebra `B` is smooth over `k` if and only if `AlgebraicClosure k ⊗[k] B` is
a regular ring. -/
theorem _root_.Algebra.Smooth.iff_isRegularRing_tensorProduct_algebraicClosure {k : Type u}
    {B : Type v} [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] :
    Algebra.Smooth k B ↔ IsRegularRing (AlgebraicClosure k ⊗[k] B) :=
  Algebra.Smooth.iff_isRegularRing_tensorProduct_of_perfectField (AlgebraicClosure k)

/-- A finite-type `k`-algebra `B` is smooth over `k` if and only if `K ⊗[k] B` is a regular ring
for every field extension `K / k`. -/
theorem _root_.Algebra.Smooth.iff_forall_isRegularRing_tensorProduct {k : Type u} {B : Type v}
    [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] :
    Algebra.Smooth k B ↔ ∀ (K : Type u) [Field K] [Algebra k K], IsRegularRing (K ⊗[k] B) :=
  ⟨fun _ K _ _ ↦ IsRegularRing.of_smooth (R := K),
    fun h ↦ have : GeometricallyRegular k B := ⟨Algebra.FiniteType.isNoetherianRing k B,
      fun L _ _ _ _ ↦ h L⟩; GeometricallyRegular.smooth⟩

/-! ### Checks -/

/-- A field is geometrically regular over itself. -/
example (k : Type u) [Field k] : GeometricallyRegular k k := inferInstance

/-- The zero algebra is geometrically regular. -/
example (k : Type u) [Field k] : GeometricallyRegular k (k ⧸ (⊤ : Ideal k)) := inferInstance

/-- Polynomial rings in finitely many variables are geometrically regular. -/
example (k : Type u) [Field k] (n : ℕ) : GeometricallyRegular k (MvPolynomial (Fin n) k) :=
  inferInstance

/-- A finite purely inseparable extension that is not separable is regular, being a field, but is
not geometrically regular. -/
example (k L : Type u) [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    [IsPurelyInseparable k L] (h : ¬ Algebra.IsSeparable k L) : ¬ GeometricallyRegular k L :=
  (geometricallyRegular_iff_isSeparable L).not.mpr h

end TauCeti.Excellence
