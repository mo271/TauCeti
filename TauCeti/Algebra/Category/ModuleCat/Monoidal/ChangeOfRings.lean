/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Change of rings and tensor products of modules

Restriction of scalars along a morphism of commutative rings is compatible with the symmetric
braiding on module categories.

For a morphism `f : A →+* P` and a `P`-module `M`, tensoring an extension of scalars with `M`
over `P` is tensoring with `M` over `A`: `M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X`, naturally in the
`A`-module `X` (`ModuleCat.extendScalarsCompTensorLeftIso`). Taking `M = P` identifies
`extendScalars f ⋙ restrictScalars f` with `tensorLeft ((restrictScalars f).obj (of P P))`
(`ModuleCat.extendScalarsCompRestrictScalarsIso`), relating the left derived functors of extension
of scalars to `Tor` against `P`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.ModuleCat

universe u

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction of scalars between module categories preserves the symmetric braiding. -/
instance restrictScalarsLaxBraided : (_root_.ModuleCat.restrictScalars f).LaxBraided where
  braided _ _ := _root_.ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl

end

end TauCeti.ModuleCat

namespace ModuleCat

open scoped TensorProduct ChangeOfRings

universe u

variable {A P : Type u} [CommRing A] [CommRing P] (f : A →+* P)

/-- The `A`-linear equivalence `M ⊗[P] (P ⊗[A] X) ≃ M ⊗[A] X`, `m ⊗ (s ⊗ x) ↦ (s • m) ⊗ x`,
where `A` acts through `f`. -/
private noncomputable def tensorExtendScalarsLinearEquiv (M : ModuleCat.{u} P)
    (X : ModuleCat.{u} A) :
    (restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ≃ₗ[A]
      ((restrictScalars f).obj M ⊗ X : ModuleCat A) :=
  letI := f.toAlgebra
  letI : Module A M := Module.compHom M f
  haveI : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A P P M X).restrictScalars A

/-- **Projection formula for extension of scalars.** For `f : A →+* P` and a `P`-module `M`,
`M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X` as `A`-modules, naturally in the `A`-module `X`; it sends
`m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
noncomputable def extendScalarsCompTensorLeftIso (M : ModuleCat.{u} P) :
    extendScalars.{u, u, u} f ⋙ tensorLeft M ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj M) :=
  (NatIso.ofComponents (fun X ↦ (tensorExtendScalarsLinearEquiv f M X).toModuleIso.symm)
    fun _ ↦ by apply MonoidalCategory.tensor_ext; intros; rfl).symm

/-- The forward map of `extendScalarsCompTensorLeftIso` sends `m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_hom_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : M) (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ⟶
        (restrictScalars f).obj M ⊗ X) → _) ((extendScalarsCompTensorLeftIso f M).hom.app X)
        (TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m (s ⊗ₜ[A, f] x)) =
      TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) (s • m) x :=
  (rfl)

/-- The inverse of `extendScalarsCompTensorLeftIso` sends `m ⊗ x` to `m ⊗ (1 ⊗ x)`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_inv_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : (restrictScalars f).obj M) (x : X) :
    (Hom.hom : ((restrictScalars f).obj M ⊗ X ⟶
        (restrictScalars f).obj (M ⊗ (extendScalars f).obj X)) → _)
        ((extendScalarsCompTensorLeftIso f M).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) m x) =
      TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m ((1 : P) ⊗ₜ[A, f] x) :=
  (rfl)

/-- Restricting scalars of `P ⊗[A] X` back along `f : A →+* P` is tensoring `X` over `A` with `P`
viewed as an `A`-module along `f`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj (of P P)) :=
  Functor.isoWhiskerLeft (extendScalars.{u, u, u} f)
      (Functor.isoWhiskerRight (leftUnitorNatIso (ModuleCat.{u} P)).symm (restrictScalars.{u} f)) ≪≫
    extendScalarsCompTensorLeftIso f (of P P)

/-- The forward map of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_hom_app_tmul (X : ModuleCat.{u} A) (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj ((extendScalars f).obj X) ⟶
        (restrictScalars f).obj (of P P) ⊗ X) → _)
        ((extendScalarsCompRestrictScalarsIso f).hom.app X) (s ⊗ₜ[A, f] x) =
      TensorProduct.tmul A (M := (restrictScalars f).obj (of P P)) (N := X) s x := by
  have h : (extendScalarsCompRestrictScalarsIso f).hom.app X =
      (restrictScalars f).map (λ_ ((extendScalars f).obj X)).inv ≫
        (extendScalarsCompTensorLeftIso f (of P P)).hom.app X := by
    simp [extendScalarsCompRestrictScalarsIso]
  refine (congrArg (Hom.hom · (s ⊗ₜ[A, f] x)) h).trans ?_
  refine (ModuleCat.comp_apply _ _ _).trans ?_
  -- `𝟙_ (ModuleCat P)` in `leftUnitor_inv_apply` is definitionally `of P P`.
  refine (congrArg ((extendScalarsCompTensorLeftIso f (of P P)).hom.app X).hom
    ((restrictScalars.map_apply f _ _).trans (MonoidalCategory.leftUnitor_inv_apply _))).trans ?_
  refine (extendScalarsCompTensorLeftIso_hom_app_tmul f (of P P) X (1 : P) s x).trans ?_
  have hs : (s • (1 : of P P) : P) = s := by rw [smul_eq_mul, mul_one]
  exact congrArg (TensorProduct.tmul A (M := (restrictScalars f).obj (of P P)) (N := X) · x) hs

/-- The inverse of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_inv_app_tmul (X : ModuleCat.{u} A) (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (of P P) ⊗ X ⟶
        (restrictScalars f).obj ((extendScalars f).obj X)) → _)
        ((extendScalarsCompRestrictScalarsIso f).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj (of P P)) (N := X) s x) =
      s ⊗ₜ[A, f] x := by
  have h : (extendScalarsCompRestrictScalarsIso f).inv.app X =
      (extendScalarsCompTensorLeftIso f (of P P)).inv.app X ≫
        (restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom := by
    simp [extendScalarsCompRestrictScalarsIso]
  refine (congrArg (Hom.hom · _) h).trans ?_
  refine (ModuleCat.comp_apply _ _ _).trans ?_
  -- `of P P` is definitionally `𝟙_ (ModuleCat P)` in `leftUnitor_hom_apply`.
  refine (congrArg ((restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom).hom
    (extendScalarsCompTensorLeftIso_inv_app_tmul f (of P P) X s x)).trans ?_
  refine (restrictScalars.map_apply f _ _).trans ?_
  refine (MonoidalCategory.leftUnitor_hom_apply (M := ↧((extendScalars f).obj X)) s
    ((1 : P) ⊗ₜ[A, f] x)).trans ?_
  exact (ExtendScalars.smul_tmul f s (1 : P) x).trans (congrArg (· ⊗ₜ[A, f] x) (mul_one s))

end ModuleCat
