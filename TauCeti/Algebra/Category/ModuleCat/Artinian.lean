/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.Algebra.Category.ModuleCat.FiniteLength
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Artinian modules in `ModuleCat`

Left Artinian modules over a ring `R` form the object property `ModuleCat.isArtinian R` on
`ModuleCat R`. It is a Serre class: closed under subobjects, quotients, extensions, and finite
products, and containing zero objects.

Over a left Noetherian ring the finite-length modules are precisely the finitely generated Artinian
modules (`ModuleCat.isFiniteLength_eq_isFG_inf_isArtinian`), while over a left Artinian ring
Hopkins–Levitzki identifies Artinian, finite-length, and finitely generated modules
(`ModuleCat.isArtinian_eq_isFiniteLength`, `ModuleCat.isArtinian_eq_isFG`). For an algebra `B`
over a commutative ring `R`, the `B`-modules that are Artinian over `R` are the inverse image of
`ModuleCat.isArtinian R` under restriction of scalars
(`ModuleCat.isArtinian_inverseImage_restrictScalars_iff`).
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type v} [Ring R]

variable (R) in
/-- Left Artinian modules, as a property of objects of `ModuleCat R`. -/
def isArtinian : ObjectProperty (ModuleCat.{u} R) := fun M ↦ IsArtinian R M

@[simp]
theorem isArtinian_iff (M : ModuleCat.{u} R) : isArtinian R M ↔ IsArtinian R M :=
  Iff.rfl

instance (M : (isArtinian.{u} R).FullSubcategory) : IsArtinian R M.obj :=
  M.property

instance : (isArtinian.{u} R).IsClosedUnderSubobjects where
  prop_of_mono f _ h := by
    rw [isArtinian_iff] at h ⊢
    exact isArtinian_of_injective f.hom ((ModuleCat.mono_iff_injective f).1 inferInstance)

instance : (isArtinian.{u} R).IsClosedUnderQuotients where
  prop_of_epi {X _} f _ h := by
    rw [isArtinian_iff] at h ⊢
    exact isArtinian_of_surjective X f.hom ((ModuleCat.epi_iff_surjective f).1 inferInstance)

instance : (isArtinian.{u} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    (isArtinian_iff _).mpr inferInstance⟩

instance : (isArtinian.{u} R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    rw [isArtinian_iff] at hM hN ⊢
    have : IsArtinian R (M × N) := inferInstance
    exact isArtinian_of_linearEquiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm

instance : (isArtinian.{u} R).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

instance : (isArtinian.{u} R).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [isArtinian_iff] at h₁ h₃ ⊢
    exact isArtinian_of_range_eq_ker S.f.hom S.g.hom hS.exact.moduleCat_range_eq_ker

/-- Every finite-length module is Artinian. -/
theorem isFiniteLength_le_isArtinian : isFiniteLength.{u} R ≤ isArtinian.{u} R := fun M h ↦
  (isArtinian_iff M).mpr (isFiniteLength_iff_isNoetherian_isArtinian.mp
    ((isFiniteLength_iff M).mp h)).2

/-- Over a left Noetherian ring, the finite-length modules are the finitely generated Artinian
modules. -/
theorem isFiniteLength_eq_isFG_inf_isArtinian [IsNoetherianRing R] :
    isFiniteLength.{u} R = isFG.{u} R ⊓ isArtinian.{u} R :=
  le_antisymm
    (fun M h ↦ by
      obtain ⟨_, hA⟩ :=
        isFiniteLength_iff_isNoetherian_isArtinian.mp ((isFiniteLength_iff M).mp h)
      exact ⟨(isFG_iff M).mpr inferInstance, (isArtinian_iff M).mpr hA⟩)
    (fun M ⟨hFG, hA⟩ ↦ by
      have := (isFG_iff M).mp hFG
      exact (isFiniteLength_iff M).mpr
        (isFiniteLength_iff_isNoetherian_isArtinian.mpr
          ⟨inferInstance, (isArtinian_iff M).mp hA⟩))

/-- Over a left Artinian ring, every Artinian module has finite length. -/
theorem isArtinian_eq_isFiniteLength [IsArtinianRing R] :
    isArtinian.{u} R = isFiniteLength.{u} R :=
  le_antisymm
    (fun M h ↦ by
      have hA : IsArtinian R M := (isArtinian_iff M).mp h
      exact (isFiniteLength_iff M).mpr (isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨IsSemiprimaryRing.isNoetherian_iff_isArtinian.mpr hA, hA⟩))
    isFiniteLength_le_isArtinian

/-- Over a left Artinian ring, a module is Artinian if and only if it is finitely generated. -/
theorem isArtinian_eq_isFG [IsArtinianRing R] :
    isArtinian.{u} R = isFG.{u} R :=
  isArtinian_eq_isFiniteLength.trans isFiniteLength_eq_isFG

section Algebra

attribute [local instance] moduleOfAlgebra

/-- A module over an `R`-algebra lies in the inverse image of the Artinian `R`-modules under
restriction of scalars if and only if it is Artinian over `R`. -/
theorem isArtinian_inverseImage_restrictScalars_iff {R : Type*} [CommRing R] {B : Type*}
    [Ring B] [Algebra R B] (M : ModuleCat.{u} B) :
    (isArtinian.{u} R).inverseImage (restrictScalars.{u} (algebraMap R B)) M ↔
      IsArtinian R M :=
  Iff.rfl

end Algebra

end ModuleCat
