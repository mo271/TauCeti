/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Relative.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Relative half-braidings with left-rigid source are automatically invertible

Given a strong monoidal functor `F : C ⥤ D` and an object `X : D`, a family of morphisms
`γ U : X ⊗ F.obj U ⟶ F.obj U ⊗ X` (not assumed invertible) that is natural in `U : C`,
compatible with the tensor comparisons of `F`, and equal to
`X ◁ η F ≫ (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X` at `𝟙_ C` automatically has a two-sided inverse
`invOfHom F γ Y U` whenever `U` admits a left dual `Y` (`ExactPairing Y U`). In particular, when
`C` is left rigid (`[LeftRigidCategory C]`), every such family `γ` defines an `F`-relative
half-braiding `RelativeHalfBraiding.ofHom`, without any rigidity assumption on `D`.

The proof transports the exact pairing of `(Y, U)` in `C` along the strong monoidal functor `F`
via `CategoryTheory.Functor.mapExactPairing` to obtain an exact pairing of `(F.obj Y, F.obj U)` in
`D`, and then conjugates `γ Y` by its coevaluation and evaluation as in
`TauCeti.CategoryTheory.Monoidal.Center.OfHom`.

## Main declarations

* `CategoryTheory.Functor.RelativeHalfBraiding.invOfHom`: the candidate inverse
  `F.obj U ⊗ X ⟶ X ⊗ F.obj U` associated to an exact pairing `ExactPairing Y U` in `C`;
* `CategoryTheory.Functor.RelativeHalfBraiding.hom_comp_invOfHom` and
  `CategoryTheory.Functor.RelativeHalfBraiding.invOfHom_comp_hom`: `invOfHom` is a two-sided
  inverse of `γ U`;
* `CategoryTheory.Functor.RelativeHalfBraiding.ofHom`: construct `F.RelativeHalfBraiding X` from
  forward morphisms alone when `C` is left rigid;
* `CategoryTheory.Functor.RelativeHalfBraiding.β_inv_eq_invOfHom`: the inverse components of any
  `F`-relative half-braiding are given by `invOfHom` at left duals in `C`.

## References

* A. M. Gainutdinov, J. Haferkamp, C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. **414** (2023), 108853, Lemma 3.2.
-/

public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace CategoryTheory.Functor.RelativeHalfBraiding

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

section Inverse

variable (F : C ⥤ D) [F.Monoidal] {X : D} (γ : ∀ U : C, X ⊗ F.obj U ⟶ F.obj U ⊗ X)

/-- The candidate inverse of `γ U : X ⊗ F.obj U ⟶ F.obj U ⊗ X` associated to an exact pairing
`ExactPairing Y U` in `C`: transport the pairing along `F` via `F.mapExactPairing Y U`, insert its
coevaluation, move `X` past `F.obj Y` with `γ Y`, and evaluate. -/
def invOfHom (Y U : C) [ExactPairing Y U] : F.obj U ⊗ X ⟶ X ⊗ F.obj U :=
  let : ExactPairing (F.obj Y) (F.obj U) := F.mapExactPairing Y U
  𝟙 _ ⊗≫ F.obj U ◁ X ◁ η_ (F.obj Y) (F.obj U) ⊗≫
    F.obj U ◁ γ Y ▷ F.obj U ⊗≫ ε_ (F.obj Y) (F.obj U) ▷ X ▷ F.obj U ⊗≫ 𝟙 _

/-- Explicit expansion of `invOfHom` in terms of the coevaluation and evaluation in `C` and the
monoidal comparisons of `F`. -/
theorem invOfHom_eq (Y U : C) [ExactPairing Y U] :
    invOfHom F γ Y U =
      𝟙 _ ⊗≫ F.obj U ◁ X ◁ (ε F ≫ F.map (η_ Y U) ≫ δ F Y U) ⊗≫
        F.obj U ◁ γ Y ▷ F.obj U ⊗≫
          (μ F U Y ≫ F.map (ε_ Y U) ≫ η F) ▷ X ▷ F.obj U ⊗≫ 𝟙 _ := by
  rw [invOfHom, mapExactPairing_coevaluation, mapExactPairing_evaluation]

variable {F γ}
  (unit : γ (𝟙_ C) = X ◁ η F ≫ (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X)
  (monoidal : ∀ U U' : C, γ (U ⊗ U') =
    X ◁ δ F U U' ≫ (α_ X (F.obj U) (F.obj U')).inv ≫
      γ U ▷ F.obj U' ≫ (α_ (F.obj U) X (F.obj U')).hom ≫
      F.obj U ◁ γ U' ≫ (α_ (F.obj U) (F.obj U') X).inv ≫
      μ F U U' ▷ X)
  (naturality : ∀ {U U' : C} (f : U ⟶ U'), X ◁ F.map f ≫ γ U' = γ U ≫ F.map f ▷ X)
include unit monoidal naturality

/-- `invOfHom F γ Y U` is a right inverse of `γ U` for a unital, monoidal, natural family `γ`. -/
@[reassoc (attr := simp)]
theorem hom_comp_invOfHom (Y U : C) [ExactPairing Y U] :
    γ U ≫ invOfHom F γ Y U = 𝟙 (X ⊗ F.obj U) := by
  let : ExactPairing (F.obj Y) (F.obj U) := F.mapExactPairing Y U
  have h := congrArg (X ◁ μ F U Y ≫ · ≫ η F ▷ X) (naturality (ε_ Y U))
  rw [monoidal, unit] at h
  simp only [Category.assoc, whiskerLeft_μ_δ_assoc, whiskerRight_ε_η, Category.comp_id] at h
  have h' : X ◁ ε_ (F.obj Y) (F.obj U) ≫ (ρ_ X).hom ≫ (λ_ X).inv =
      (α_ _ _ _).inv ≫ γ U ▷ F.obj Y ≫ (α_ _ _ _).hom ≫
        F.obj U ◁ γ Y ≫ (α_ _ _ _).inv ≫ ε_ (F.obj Y) (F.obj U) ▷ X := by
    simpa only [mapExactPairing_evaluation, MonoidalCategory.whiskerLeft_comp,
      comp_whiskerRight, Category.assoc] using h
  calc
    _ = 𝟙 _ ⊗≫ (γ U ▷ 𝟙_ D ≫ (F.obj U ⊗ X) ◁ η_ (F.obj Y) (F.obj U)) ⊗≫
          F.obj U ◁ γ Y ▷ F.obj U ⊗≫
            ε_ (F.obj Y) (F.obj U) ▷ X ▷ F.obj U ⊗≫ 𝟙 _ := by
      rw [invOfHom]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ F.obj U ◁ η_ (F.obj Y) (F.obj U) ⊗≫
          ((α_ _ _ _).inv ≫ γ U ▷ F.obj Y ≫ (α_ _ _ _).hom ≫ F.obj U ◁ γ Y ≫
            (α_ _ _ _).inv ≫ ε_ (F.obj Y) (F.obj U) ▷ X) ▷ F.obj U ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (F.obj U ◁ η_ (F.obj Y) (F.obj U) ⊗≫
          ε_ (F.obj Y) (F.obj U) ▷ F.obj U) ⊗≫ 𝟙 _ := by
      rw [← h']; monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'']; monoidal

/-- `invOfHom F γ Y U` is a left inverse of `γ U` for a unital, monoidal, natural family `γ`. -/
@[reassoc (attr := simp)]
theorem invOfHom_comp_hom (Y U : C) [ExactPairing Y U] :
    invOfHom F γ Y U ≫ γ U = 𝟙 (F.obj U ⊗ X) := by
  let : ExactPairing (F.obj Y) (F.obj U) := F.mapExactPairing Y U
  have h := congrArg (X ◁ ε F ≫ · ≫ δ F Y U ▷ X) (naturality (η_ Y U))
  rw [monoidal, unit] at h
  simp only [Category.assoc, whiskerLeft_ε_η_assoc, whiskerRight_μ_δ, Category.comp_id] at h
  have h' : X ◁ η_ (F.obj Y) (F.obj U) ≫ (α_ _ _ _).inv ≫ γ Y ▷ F.obj U ≫
        (α_ _ _ _).hom ≫ F.obj Y ◁ γ U ≫ (α_ _ _ _).inv =
      (ρ_ X).hom ≫ (λ_ X).inv ≫ η_ (F.obj Y) (F.obj U) ▷ X := by
    simpa only [mapExactPairing_coevaluation, MonoidalCategory.whiskerLeft_comp,
      comp_whiskerRight, Category.assoc] using h
  calc
    _ = 𝟙 _ ⊗≫ F.obj U ◁ X ◁ η_ (F.obj Y) (F.obj U) ⊗≫
          F.obj U ◁ γ Y ▷ F.obj U ⊗≫
          (ε_ (F.obj Y) (F.obj U) ▷ (X ⊗ F.obj U) ≫ 𝟙_ D ◁ γ U) ⊗≫ 𝟙 _ := by
      rw [invOfHom]; monoidal
    _ = 𝟙 _ ⊗≫ F.obj U ◁ (X ◁ η_ (F.obj Y) (F.obj U) ≫ (α_ _ _ _).inv ≫
          γ Y ▷ F.obj U ≫ (α_ _ _ _).hom ≫ F.obj Y ◁ γ U ≫ (α_ _ _ _).inv) ⊗≫
          ε_ (F.obj Y) (F.obj U) ▷ F.obj U ▷ X ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ (F.obj U ◁ η_ (F.obj Y) (F.obj U) ⊗≫
          ε_ (F.obj Y) (F.obj U) ▷ F.obj U) ▷ X ⊗≫ 𝟙 _ := by
      rw [h']; monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'']; monoidal

/-- Construct an `F`-relative half-braiding on `X : D` from a family of morphisms
`γ U : X ⊗ F.obj U ⟶ F.obj U ⊗ X` that is unital, monoidal, and natural in `U`. When `C` is
left rigid, `γ U` is automatically invertible with inverse `invOfHom F γ (ᘁU) U`; no rigidity on
`D` is required. -/
@[expose]
def ofHom [LeftRigidCategory C] : F.RelativeHalfBraiding X where
  β U :=
    { hom := γ U
      inv := invOfHom F γ (ᘁU) U
      hom_inv_id := hom_comp_invOfHom unit monoidal naturality (ᘁU) U
      inv_hom_id := invOfHom_comp_hom unit monoidal naturality (ᘁU) U }
  monoidal := monoidal
  naturality := naturality

/-- The forward components of `RelativeHalfBraiding.ofHom` are the given family `γ`. -/
@[simp]
theorem ofHom_β_hom [LeftRigidCategory C] (U : C) :
    ((ofHom unit monoidal naturality).β U).hom = γ U :=
  rfl

/-- The inverse components of `RelativeHalfBraiding.ofHom` are given by `invOfHom` at left duals. -/
theorem ofHom_β_inv [LeftRigidCategory C] (U : C) :
    ((ofHom unit monoidal naturality).β U).inv = invOfHom F γ (ᘁU) U :=
  rfl

end Inverse

/-- For any `F`-relative half-braiding `b` on `X` and any exact pairing `ExactPairing Y U` in `C`,
the inverse component `(b.β U).inv` is computed from the forward components of `b` by
`invOfHom`. -/
theorem β_inv_eq_invOfHom {F : C ⥤ D} [F.Monoidal] {X : D} (b : F.RelativeHalfBraiding X)
    (Y U : C) [ExactPairing Y U] :
    (b.β U).inv = invOfHom F (fun V ↦ (b.β V).hom) Y U := by
  rw [← cancel_epi (b.β U).hom, Iso.hom_inv_id,
    hom_comp_invOfHom b.β_tensorUnit_hom b.monoidal b.naturality]

end CategoryTheory.Functor.RelativeHalfBraiding
