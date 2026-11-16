/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.CategoryTheory.CStar.Basic

/-!
# Functors between C⋆-categories

Any additive `ℂ`-linear dagger-preserving functor `F : C ⥤ D` between C⋆-categories is
automatically norm-contractive on every rectangular morphism space `X ⟶ Y`, hence continuous with
closed kernels; if `F` is faithful it is isometric on every `X ⟶ Y` (and conversely), and if `F` is
full and faithful it induces linear isometric equivalences `(X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y)`.

The analytic bounds on rectangular morphisms follow directly from the induced unital `⋆`-algebra
homomorphisms `F.mapEndStarAlgHom ℂ X : End X →⋆ₐ[ℂ] End (F.obj X)` applied to `End.of (f ≫ f†)`
together with the C⋆-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2`, avoiding any auxiliary linking-algebra
construction.

## Main declarations

* `CategoryTheory.Functor.norm_map_le`: `‖F.map f‖ ≤ ‖f‖` for any additive `ℂ`-linear
  dagger-preserving functor `F`.
* `CategoryTheory.Functor.mapCLM`: `F.map` bundled as a continuous `ℂ`-linear map of norm at most
  `1`, with closed kernel (`CategoryTheory.Functor.isClosed_ker_mapLinearMap`).
* `CategoryTheory.Functor.norm_map`, `CategoryTheory.Functor.mapLinearIsometry`,
  `CategoryTheory.Functor.faithful_iff_forall_norm_map`: faithful `ℂ`-linear dagger functors are
  isometric on every Hom space, and this characterizes faithfulness.
* `CategoryTheory.Functor.homLinearIsometryEquiv`: fully faithful `ℂ`-linear dagger functors give
  linear isometric equivalences on Hom spaces.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W⋆-categories*, Pacific J. Math. 120 (1985), 79–109.
-/

public section

open CategoryTheory TauCeti

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [DaggerPreadditive D] [DaggerLinear ℂ D] [CStarCategory D]
variable (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

/-- Any additive `ℂ`-linear dagger-preserving functor between C⋆-categories is norm-contractive on
all morphism spaces. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simpa using NonUnitalStarAlgHom.norm_apply_le (F.mapEndStarAlgHom ℂ X) (End.of (f ≫ dagger f))

/-- `NNNorm` form of `CategoryTheory.Functor.norm_map_le`. -/
theorem nnNorm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ ≤ ‖f‖₊ :=
  F.norm_map_le f

/-- `F.map` bundled as a continuous `ℂ`-linear map `(X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y)`. -/
def mapCLM (X Y : C) : (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  LinearMap.mkContinuous (F.mapLinearMap ℂ) 1 fun f => by simpa using F.norm_map_le f

/-- Evaluation of `Functor.mapCLM`. -/
@[simp] theorem mapCLM_apply {X Y : C} (f : X ⟶ Y) : F.mapCLM X Y f = F.map f := by
  simp [mapCLM]

/-- Underlying `ℂ`-linear map of `Functor.mapCLM`. -/
@[simp] theorem mapCLM_toLinearMap (X Y : C) :
    (F.mapCLM X Y).toLinearMap = F.mapLinearMap ℂ := (rfl)

/-- Operator norm bound `‖F.mapCLM X Y‖ ≤ 1`. -/
theorem norm_mapCLM_le (X Y : C) : ‖F.mapCLM X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Any additive `ℂ`-linear dagger-preserving functor between C⋆-categories acts continuously on
every morphism space. -/
@[fun_prop] theorem continuous_map (X Y : C) :
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  have h : (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) = ⇑(F.mapCLM X Y) := by
    ext f
    simp
  rw [h]
  exact (F.mapCLM X Y).continuous

/-- The kernel of `F.mapLinearMap ℂ` on `X ⟶ Y` is closed. -/
theorem isClosed_ker_mapLinearMap (X Y : C) :
    IsClosed (LinearMap.ker (F.mapLinearMap ℂ : (X ⟶ Y) →ₗ[ℂ] (F.obj X ⟶ F.obj Y)) :
      Set (X ⟶ Y)) := by
  rw [← F.mapCLM_toLinearMap X Y]
  exact (F.mapCLM X Y).isClosed_ker

/-- The set of arrows in `X ⟶ Y` killed by `F` is closed. -/
theorem isClosed_setOf_map_eq_zero (X Y : C) : IsClosed {f : X ⟶ Y | F.map f = 0} :=
  isClosed_eq (F.continuous_map X Y) continuous_const

/-- A faithful additive `ℂ`-linear dagger-preserving functor between C⋆-categories is isometric on
every morphism space. -/
theorem norm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  simpa using NonUnitalStarAlgHom.norm_map (F.mapEndStarAlgHom ℂ X)
    (F.mapEndStarAlgHom_injective ℂ X) (End.of (f ≫ dagger f))

/-- `NNNorm` form of `CategoryTheory.Functor.norm_map`. -/
theorem nnNorm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ = ‖f‖₊ :=
  Subtype.ext (F.norm_map f)

/-- A faithful `ℂ`-linear dagger-preserving functor bundled as a linear isometry on `X ⟶ Y`. -/
def mapLinearIsometry [F.Faithful] (X Y : C) : (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearMap := F.mapLinearMap ℂ
  norm_map' f := by simpa using F.norm_map f

/-- Evaluation of `Functor.mapLinearIsometry`. -/
@[simp] theorem mapLinearIsometry_apply [F.Faithful] {X Y : C} (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := by
  simp [mapLinearIsometry]

/-- `F.map` is an isometry on `X ⟶ Y` whenever `F` is faithful. -/
theorem isometry_map [F.Faithful] (X Y : C) :
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  have h : (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) = ⇑(F.mapLinearIsometry X Y) := by
    ext f
    simp
  rw [h]
  exact (F.mapLinearIsometry X Y).isometry

/-- An additive `ℂ`-linear dagger-preserving functor between C⋆-categories is faithful if and only
if it preserves norms on all morphism spaces. -/
theorem faithful_iff_forall_norm_map :
    F.Faithful ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ‖F.map f‖ = ‖f‖ := by
  refine ⟨fun _ _ _ f => F.norm_map f, fun h => ⟨fun {X Y} f g hfg => ?_⟩⟩
  rw [← sub_eq_zero, ← norm_eq_zero, ← h (f - g)]
  simp [hfg]

/-- A full and faithful additive `ℂ`-linear dagger-preserving functor between C⋆-categories gives a
`ℂ`-linear isometric equivalence on every morphism space. -/
noncomputable def homLinearIsometryEquiv [F.Full] [F.Faithful] (X Y : C) :
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearEquiv := F.homLinearEquiv ℂ X Y
  norm_map' f := by simpa using F.norm_map f

/-- Forward evaluation of `Functor.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_apply [F.Full] [F.Faithful] {X Y : C} (f : X ⟶ Y) :
    F.homLinearIsometryEquiv X Y f = F.map f := by
  simp [homLinearIsometryEquiv]

/-- Inverse evaluation of `Functor.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_symm_apply [F.Full] [F.Faithful] {X Y : C}
    (g : F.obj X ⟶ F.obj Y) : (F.homLinearIsometryEquiv X Y).symm g = F.preimage g :=
  F.homLinearEquiv_symm_apply ℂ g

end CategoryTheory.Functor
