/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Derivations along formally étale extensions

Let `R → S → T` be a tower of commutative rings and `N` a `T`-module. If `T` is formally
unramified over `S`, an `R`-derivation `T → N` is determined by its values on the image of `S`:
the difference of two such derivations agreeing on `S` is an `S`-derivation, hence factors through
`Ω[T⁄S]`, which vanishes. If `T` is formally étale over `S`, every `R`-derivation `S → N` extends
to an `R`-derivation `T → N`: the canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ Ω[T⁄R]`
(`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`) turns the `S`-linear map
`Ω[S⁄R] → N` classifying the derivation into a `T`-linear map `Ω[T⁄R] → N`.

The motivating case is a finite separable field extension `T/S`, which is formally étale by
`Algebra.FormallyEtale.of_isSeparable`: every derivation of `S` extends uniquely to `T`, in every
characteristic. Mathlib's `Differential.uniqueDifferentialAlgebraFiniteDimensional` gives this for
finite extensions of differential fields of characteristic zero, by a primitive element; here the
base and extension are arbitrary commutative rings and the derivations are module-valued.

## Main declarations

* `Derivation.eq_of_formallyUnramified`: two derivations of a formally unramified extension
  agreeing on the base are equal;
* `AlgHom.map_derivation_of_formallyUnramified`: an `S`-algebra homomorphism out of a formally
  unramified `S`-algebra intertwines derivations that agree on `S`;
* `Derivation.extendOfFormallyEtale`: the extension of a derivation to a formally étale
  extension, with `Derivation.extendOfFormallyEtale_algebraMap` stating that it extends,
  `AlgHom.map_extendOfFormallyEtale` its naturality along `S`-algebra homomorphisms, and
  `Derivation.extendOfFormallyEtale_extendOfFormallyEtale` its transitivity in towers.
-/

public section

namespace Derivation

section Unramified

variable {R S T N : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R T] [Algebra S T]
  [AddCommGroup N] [Module T N] [Module R N]

/-- **Derivations of a formally unramified extension are determined on the base.** If `T` is
formally unramified over `S`, two `R`-derivations `T → N` that agree on the image of `S` are
equal. -/
theorem eq_of_formallyUnramified [Algebra.FormallyUnramified S T] {δ₁ δ₂ : Derivation R T N}
    (h : ∀ s : S, δ₁ (algebraMap S T s) = δ₂ (algebraMap S T s)) : δ₁ = δ₂ := by
  let : Module S N := Module.compHom N (algebraMap S T)
  have : IsScalarTower S T N := ⟨fun s t n ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have hS (s : S) (x : T) : (δ₁ - δ₂) (s • x) = s • (δ₁ - δ₂) x := by
    rw [Algebra.smul_def, leibniz, sub_apply _ _ (algebraMap S T s), h, sub_self,
      smul_zero, add_zero, algebraMap_smul]
  -- The difference vanishes on `S`, so it is an `S`-derivation, which factors through
  -- `Ω[T⁄S] = 0`.
  let δ : Derivation S T N :=
    { toFun := δ₁ - δ₂
      map_add' := map_add (δ₁ - δ₂)
      map_smul' := hS
      map_one_eq_zero' := (δ₁ - δ₂).map_one_eq_zero
      leibniz' := (δ₁ - δ₂).leibniz }
  have hδ (x : T) : δ x = 0 := by
    rw [← δ.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D S T x) 0,
      map_zero]
  ext x
  -- `δ x` is `δ₁ x - δ₂ x` by construction of `δ`.
  exact sub_eq_zero.mp (hδ x)

end Unramified

section Etale

variable {R S T N : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [AddCommGroup N] [Module T N] [Module R N] [Module S N]
  [IsScalarTower S T N] [IsScalarTower R S N] [Algebra.FormallyEtale S T]

variable (T) in
/-- The extension of an `R`-derivation `D : S → N` to an `R`-derivation of a formally étale
`S`-algebra `T`, for `N` a `T`-module. It is the `T`-linear extension of the map
`Ω[S⁄R] → N` classifying `D` along `T ⊗[S] Ω[S⁄R] ≃ Ω[T⁄R]`. By
`Derivation.eq_of_formallyUnramified` it is the only derivation of `T` agreeing with `D` on `S`. -/
noncomputable def extendOfFormallyEtale (D : Derivation R S N) : Derivation R T N :=
  haveI : IsScalarTower R T N := .of_algebraMap_smul fun r n ↦ by
    rw [IsScalarTower.algebraMap_apply R S T, algebraMap_smul, algebraMap_smul]
  (D.liftKaehlerDifferential.liftBaseChange T ∘ₗ
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
    (KaehlerDifferential.D R T)

/-- The extension of `D` to the formally étale extension `T` agrees with `D` on the image
of `S`. -/
@[simp]
theorem extendOfFormallyEtale_algebraMap (D : Derivation R S N) (s : S) :
    D.extendOfFormallyEtale T (algebraMap S T s) = D s := by
  simp [extendOfFormallyEtale,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

/-- The extension of `D` to `T` is the unique derivation of `T` agreeing with `D` on `S`. -/
theorem eq_extendOfFormallyEtale (D : Derivation R S N) {δ : Derivation R T N}
    (h : ∀ s : S, δ (algebraMap S T s) = D s) : δ = D.extendOfFormallyEtale T :=
  eq_of_formallyUnramified fun s ↦ by rw [h, extendOfFormallyEtale_algebraMap]

/-- **Transitivity of formally étale derivation extension.** Extending a derivation along `S → T`
and then along `T → U` agrees with extending it directly along `S → U`. -/
@[simp]
theorem extendOfFormallyEtale_extendOfFormallyEtale {U : Type*} [CommRing U]
    [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [IsScalarTower S T U] [IsScalarTower R T U]
    [Module U N] [IsScalarTower R T N] [IsScalarTower T U N] [IsScalarTower S U N]
    [Algebra.FormallyEtale T U] [Algebra.FormallyEtale S U]
    (D : Derivation R S N) :
    (D.extendOfFormallyEtale T).extendOfFormallyEtale U = D.extendOfFormallyEtale U :=
  eq_extendOfFormallyEtale D fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S T U, extendOfFormallyEtale_algebraMap,
      extendOfFormallyEtale_algebraMap]

end Etale

end Derivation

namespace AlgHom

variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra R U] [Algebra S U] [IsScalarTower R S U]

/-- **Naturality of derivations out of a formally unramified extension.** An `S`-algebra
homomorphism `φ : T →ₐ[S] U` out of a formally unramified `S`-algebra intertwines any two
`R`-derivations of `T` and `U` that it intertwines on `S`; no unramifiedness hypothesis on `U` is
needed. -/
theorem map_derivation_of_formallyUnramified [Algebra.FormallyUnramified S T]
    (φ : T →ₐ[S] U) {δ₁ : Derivation R T T} {δ₂ : Derivation R U U}
    (h : ∀ s : S, φ (δ₁ (algebraMap S T s)) = δ₂ (algebraMap S U s)) (x : T) :
    φ (δ₁ x) = δ₂ (φ x) := by
  let _ : Algebra T U := φ.toRingHom.toAlgebra
  have _ : IsScalarTower R T U := .of_algebraMap_eq' (φ.restrictScalars R).comp_algebraMap.symm
  have hδ : (Algebra.linearMap T U).compDer δ₁ = δ₂.compAlgebraMap T :=
    Derivation.eq_of_formallyUnramified (S := S) fun s ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using h s
  exact congr($hδ x)

/-- **Naturality of `Derivation.extendOfFormallyEtale`.** Every `S`-algebra homomorphism between
formally étale `S`-algebras intertwines the étale extensions of a derivation of `S`. -/
@[simp]
theorem map_extendOfFormallyEtale [Algebra.FormallyEtale S T] [Algebra.FormallyEtale S U]
    (φ : T →ₐ[S] U) (D : Derivation R S S) (x : T) :
    φ (((Algebra.linearMap S T).compDer D).extendOfFormallyEtale T x) =
      ((Algebra.linearMap S U).compDer D).extendOfFormallyEtale U (φ x) :=
  φ.map_derivation_of_formallyUnramified (fun s ↦ by simp) x

end AlgHom
