/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Center

/-!
# Relative half-braidings and the relative centre of a monoidal functor

Given a strong monoidal functor `F : C ⥤ D`, an `F`-*relative half-braiding* on an object `X : D`
is a natural family of isomorphisms `β U : X ⊗ F.obj U ≅ F.obj U ⊗ X` indexed by `U : C` that is
compatible with the tensor comparisons of `F`: up to associators, `(β (U ⊗ U')).hom` factors as
`X ◁ δ F U U'`, followed by `(β U).hom ▷ F.obj U'` and `F.obj U ◁ (β U').hom`, followed by
`μ F U U' ▷ X`. Compatibility with the unit comparisons of `F` is automatic: `(β (𝟙_ C)).hom` is
forced to be `X ◁ η F ≫ (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X`.

The *relative centre* `F.RelativeCenter` (often written `Z_C(D)` when `F : C ⥤ D` is an embedding,
or `Z(F)` in general) is the category of pairs `⟨X, b⟩` consisting of an object `X : D` and an
`F`-relative half-braiding `b` on `X`, with morphisms `f : X.1 ⟶ Y.1` in `D` intertwining the
relative half-braidings at every `U : C`. It is a monoidal category under the tensor product lifted
from `D`, and the forgetful functor `RelativeCenter.forget F : F.RelativeCenter ⥤ D` is faithful,
strong monoidal, and reflects isomorphisms. Unlike the Drinfeld centre `Center C` (the case
`F = 𝟭 C`), `F.RelativeCenter` is in general only monoidal rather than braided, because the
half-braiding of an object of `F.RelativeCenter` is indexed by `C` rather than `D`.

## Main declarations

* `CategoryTheory.Functor.RelativeHalfBraiding`: an `F`-relative half-braiding on `X : D`;
* `CategoryTheory.Functor.RelativeHalfBraiding.β_tensorUnit_hom`: the component at `𝟙_ C` is
  `X ◁ η F ≫ (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X`;
* `CategoryTheory.Functor.RelativeHalfBraiding.monoidal_inv` and
  `CategoryTheory.Functor.RelativeHalfBraiding.naturality_inv`: monoidality and naturality of the
  inverse components;
* `CategoryTheory.Functor.RelativeHalfBraiding.inv_whiskerRight_comp_whiskerLeft`: contracting
  `F.obj U ⊗ X ⊗ F.obj V` against `g : U ⊗ V ⟶ 𝟙_ C` via `μ F U V ≫ F.map g ≫ η F`
  does not depend on which side `X` is moved to;
* `CategoryTheory.Functor.RelativeCenter`: the relative centre of a strong monoidal functor `F`,
  equipped with its `Category` and `MonoidalCategory` instances;
* `CategoryTheory.Functor.RelativeCenter.isoMk`: lift an underlying isomorphism in `D` to an
  isomorphism in `F.RelativeCenter`;
* `CategoryTheory.Functor.RelativeCenter.forget`: the faithful strong monoidal forgetful functor
  `F.RelativeCenter ⥤ D`.

## References

* S. Majid, *Representations, duals and quantum doubles of monoidal categories*, Rend. Circ. Mat.
  Palermo (2) Suppl. **26** (1991), 197–206.
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13.
* A. M. Gainutdinov, J. Haferkamp, C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. **414** (2023), 108853, Definitions 3.1–3.2.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open MonoidalCategory LaxMonoidal OplaxMonoidal Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A relative half-braiding with respect to a strong monoidal functor `F : C ⥤ D` on an object
`X : D` is a natural family of isomorphisms `X ⊗ F.obj U ≅ F.obj U ⊗ X` for `U : C` that is
compatible with the monoidal structure of `F`. -/
structure RelativeHalfBraiding (F : C ⥤ D) [F.Monoidal] (X : D) where
  /-- The family of isomorphisms `X ⊗ F.obj U ≅ F.obj U ⊗ X` indexed by `U : C`. -/
  β : ∀ U : C, X ⊗ F.obj U ≅ F.obj U ⊗ X
  /-- Compatibility of `β` with tensor products in `C` via the comparisons of `F`. -/
  monoidal : ∀ U U' : C, (β (U ⊗ U')).hom =
      X ◁ δ F U U' ≫ (α_ X (F.obj U) (F.obj U')).inv ≫
        (β U).hom ▷ F.obj U' ≫ (α_ (F.obj U) X (F.obj U')).hom ≫
        F.obj U ◁ (β U').hom ≫ (α_ (F.obj U) (F.obj U') X).inv ≫
        μ F U U' ▷ X := by
    cat_disch
  /-- Naturality of `β` in `U : C`. -/
  naturality : ∀ {U U' : C} (f : U ⟶ U'),
      X ◁ F.map f ≫ (β U').hom = (β U).hom ≫ F.map f ▷ X := by
    cat_disch

namespace RelativeHalfBraiding

attribute [reassoc, simp] monoidal
attribute [simp, reassoc] naturality

variable {F : C ⥤ D} [F.Monoidal] {X : D} (b : F.RelativeHalfBraiding X)

/-- Two `F`-relative half-braidings on `X` are equal if their forward components agree. -/
@[ext]
theorem ext {b₁ b₂ : F.RelativeHalfBraiding X} (h : ∀ U, (b₁.β U).hom = (b₂.β U).hom) :
    b₁ = b₂ := by
  cases b₁; cases b₂
  congr
  ext U
  exact h U

/-- The tensor coherence identity in `μ`-form: precomposing `(b.β (U ⊗ U')).hom` with
`X ◁ μ F U U'` clears the oplax comparison `δ F U U'`. -/
@[reassoc]
theorem whiskerLeft_μ_comp_β_hom (U U' : C) :
    X ◁ μ F U U' ≫ (b.β (U ⊗ U')).hom =
      (α_ X (F.obj U) (F.obj U')).inv ≫ (b.β U).hom ▷ F.obj U' ≫
        (α_ (F.obj U) X (F.obj U')).hom ≫ F.obj U ◁ (b.β U').hom ≫
        (α_ (F.obj U) (F.obj U') X).inv ≫ μ F U U' ▷ X := by
  simp

/-- The component of an `F`-relative half-braiding at the unit object `𝟙_ C` is forced by
monoidality and naturality to be `X ◁ η F ≫ (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X`. -/
@[simp]
theorem β_tensorUnit_hom :
    (b.β (𝟙_ C)).hom = X ◁ η F ≫ (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X := by
  -- Naturality at `(λ_ (𝟙_ C)).hom`, expanded via `b.monoidal` and `map_leftUnitor`.
  have h₁ := b.naturality (λ_ (𝟙_ C)).hom
  rw [b.monoidal, map_leftUnitor] at h₁
  simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc,
    whiskerRight_μ_δ_assoc] at h₁
  rw [cancel_epi (X ◁ δ F (𝟙_ C) (𝟙_ C))] at h₁
  -- Slide `F.obj (𝟙_ C) ◁ (b.β (𝟙_ C)).hom` past `η F` and `λ_` to cancel `(b.β (𝟙_ C)).hom`.
  have h₂ : X ◁ (η F ▷ F.obj (𝟙_ C)) ≫ X ◁ (λ_ (F.obj (𝟙_ C))).hom =
      (α_ X (F.obj (𝟙_ C)) (F.obj (𝟙_ C))).inv ≫
        ((b.β (𝟙_ C)).hom ≫ η F ▷ X ≫ (λ_ X).hom) ▷ F.obj (𝟙_ C) := by
    rw [← cancel_mono (b.β (𝟙_ C)).hom, Category.assoc, h₁]
    calc
      _ = (α_ _ _ _).inv ≫ (b.β (𝟙_ C)).hom ▷ F.obj (𝟙_ C) ⊗≫
            ((F.obj (𝟙_ C) ◁ (b.β (𝟙_ C)).hom ≫ η F ▷ (F.obj (𝟙_ C) ⊗ X)) ≫
              (λ_ (F.obj (𝟙_ C) ⊗ X)).hom) := by
        monoidal
      _ = (α_ _ _ _).inv ≫ (b.β (𝟙_ C)).hom ▷ F.obj (𝟙_ C) ⊗≫
            (η F ▷ (X ⊗ F.obj (𝟙_ C)) ≫ (𝟙_ D ◁ (b.β (𝟙_ C)).hom ≫
              (λ_ (F.obj (𝟙_ C) ⊗ X)).hom)) := by
        rw [whisker_exchange, Category.assoc]
      _ = _ := by
        rw [leftUnitor_naturality]
        simp only [comp_whiskerRight]
        monoidal
  have h₃ : ((b.β (𝟙_ C)).hom ≫ η F ▷ X ≫ (λ_ X).hom) ▷ F.obj (𝟙_ C) =
      (X ◁ η F ≫ (ρ_ X).hom) ▷ F.obj (𝟙_ C) := by
    rw [← cancel_epi (α_ X (F.obj (𝟙_ C)) (F.obj (𝟙_ C))).inv, ← h₂, comp_whiskerRight]
    monoidal
  have h₄ : (b.β (𝟙_ C)).hom ≫ η F ▷ X ≫ (λ_ X).hom = X ◁ η F ≫ (ρ_ X).hom := by
    have h₃' := congrArg
      (fun (g : (X ⊗ F.obj (𝟙_ C)) ⊗ F.obj (𝟙_ C) ⟶ X ⊗ F.obj (𝟙_ C)) ↦
        (ρ_ (X ⊗ F.obj (𝟙_ C))).inv ≫ (X ⊗ F.obj (𝟙_ C)) ◁ ε F ≫ g ≫
          X ◁ η F ≫ (ρ_ X).hom) h₃
    simpa only [Category.assoc, whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ε_η, MonoidalCategory.whiskerLeft_id, Category.id_comp,
      ← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id] using h₃'
  rw [← cancel_mono (η F ▷ X ≫ (λ_ X).hom)]
  simpa [Category.assoc] using h₄

/-- The unit coherence identity in `ε`-form: precomposing `(b.β (𝟙_ C)).hom` with `X ◁ ε F`
clears `η F` on the left. -/
@[reassoc]
theorem whiskerLeft_ε_comp_β_tensorUnit_hom :
    X ◁ ε F ≫ (b.β (𝟙_ C)).hom = (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X := by
  simp

/-- The inverse of an `F`-relative half-braiding at the unit object `𝟙_ C`. -/
@[simp]
theorem β_tensorUnit_inv :
    (b.β (𝟙_ C)).inv = η F ▷ X ≫ (λ_ X).hom ≫ (ρ_ X).inv ≫ X ◁ ε F := by
  apply Iso.inv_ext
  simp

/-- The inverse of an `F`-relative half-braiding at a tensor product, computed from the factors. -/
@[simp]
theorem monoidal_inv (U U' : C) :
    (b.β (U ⊗ U')).inv =
      δ F U U' ▷ X ≫ (α_ (F.obj U) (F.obj U') X).hom ≫
        F.obj U ◁ (b.β U').inv ≫ (α_ (F.obj U) X (F.obj U')).inv ≫
        (b.β U).inv ▷ F.obj U' ≫ (α_ X (F.obj U) (F.obj U')).hom ≫
        X ◁ μ F U U' := by
  apply Iso.inv_ext
  simp [b.monoidal]

/-- Naturality of the inverse of an `F`-relative half-braiding. -/
@[reassoc (attr := simp)]
theorem naturality_inv {U U' : C} (f : U ⟶ U') :
    F.map f ▷ X ≫ (b.β U').inv = (b.β U).inv ≫ X ◁ F.map f := by
  rw [Iso.comp_inv_eq, Category.assoc, b.naturality, Iso.inv_hom_id_assoc]

/-- For `g : U ⊗ V ⟶ 𝟙_ C`, moving `X` to the left of `F.obj U` with `(b.β U).inv` and then
contracting `F.obj U ⊗ F.obj V` via `μ F U V ≫ F.map g ≫ η F` agrees with moving `X` to the
right of `F.obj V` with `(b.β V).hom` and contracting on the left. -/
theorem inv_whiskerRight_comp_whiskerLeft {U V : C} (g : U ⊗ V ⟶ 𝟙_ C) :
    (b.β U).inv ▷ F.obj V ⊗≫ X ◁ (μ F U V ≫ F.map g ≫ η F) ⊗≫ 𝟙 X =
      𝟙 _ ⊗≫ F.obj U ◁ (b.β V).hom ⊗≫ (μ F U V ≫ F.map g ≫ η F) ▷ X ⊗≫ 𝟙 X := by
  have h := congrArg (X ◁ μ F U V ≫ · ≫ η F ▷ X) (b.naturality g)
  simp only [Category.assoc, whiskerLeft_μ_comp_β_hom_assoc,
    β_tensorUnit_hom, whiskerRight_ε_η, Category.comp_id] at h
  calc
    _ = (b.β U).inv ▷ F.obj V ⊗≫
          (X ◁ μ F U V ≫ X ◁ F.map g ≫ X ◁ η F ≫ (ρ_ X).hom ≫ (λ_ X).inv) ⊗≫
            𝟙 X := by
      simp only [MonoidalCategory.whiskerLeft_comp]; monoidal
    _ = (b.β U).inv ▷ F.obj V ⊗≫ (b.β U).hom ▷ F.obj V ⊗≫
          F.obj U ◁ (b.β V).hom ⊗≫ (μ F U V ≫ F.map g ≫ η F) ▷ X ⊗≫ 𝟙 X := by
      rw [h]; simp only [comp_whiskerRight]; monoidal
    _ = 𝟙 _ ⊗≫ ((b.β U).inv ▷ F.obj V ≫ (b.β U).hom ▷ F.obj V) ⊗≫
          F.obj U ◁ (b.β V).hom ⊗≫ (μ F U V ≫ F.map g ≫ η F) ▷ X ⊗≫ 𝟙 X := by
      monoidal
    _ = _ := by
      rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]; monoidal

end RelativeHalfBraiding

/-- The relative centre `F.RelativeCenter` of a strong monoidal functor `F : C ⥤ D` has as objects
pairs `⟨X, b⟩` where `X : D` and `b : F.RelativeHalfBraiding X`. -/
@[implicit_reducible, expose]
def RelativeCenter (F : C ⥤ D) [F.Monoidal] :=
  Σ X : D, F.RelativeHalfBraiding X

namespace RelativeCenter

variable {F : C ⥤ D} [F.Monoidal]

/-- A morphism in the relative centre `F.RelativeCenter` is a morphism between the underlying
objects in `D` that commutes with the relative half-braidings at every `U : C`. -/
@[ext]
structure Hom (X Y : F.RelativeCenter) where
  /-- The underlying morphism in `D`. -/
  f : X.1 ⟶ Y.1
  /-- Compatibility with the relative half-braidings. -/
  comm : ∀ U : C, f ▷ F.obj U ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ F.obj U ◁ f := by
    cat_disch

attribute [reassoc (attr := simp)] Hom.comm

instance instQuiver : Quiver F.RelativeCenter where
  Hom := Hom

@[ext]
theorem ext {X Y : F.RelativeCenter} (f g : X ⟶ Y) (w : f.f = g.f) : f = g :=
  Hom.ext w

instance instCategory : Category F.RelativeCenter where
  id X := { f := 𝟙 X.1 }
  comp f g := { f := f.f ≫ g.f }

@[simp]
theorem id_f (X : F.RelativeCenter) : Hom.f (𝟙 X) = 𝟙 X.1 :=
  rfl

@[simp]
theorem comp_f {X Y Z : F.RelativeCenter} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- Morphisms in `F.RelativeCenter` also commute with the inverse components of the relative
half-braidings. -/
@[reassoc (attr := simp)]
theorem Hom.comm_inv {X Y : F.RelativeCenter} (f : X ⟶ Y) (U : C) :
    F.obj U ◁ f.f ≫ (Y.2.β U).inv = (X.2.β U).inv ≫ f.f ▷ F.obj U := by
  rw [Iso.comp_inv_eq, Category.assoc, f.comm, Iso.inv_hom_id_assoc]

/-- Construct an isomorphism in `F.RelativeCenter` from a morphism whose underlying morphism in `D`
is an isomorphism. -/
@[expose, simps]
noncomputable def isoMk {X Y : F.RelativeCenter} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where
  hom := f
  inv :=
    { f := CategoryTheory.inv f.f
      comm U := by
        rw [← cancel_epi (f.f ▷ F.obj U), ← comp_whiskerRight_assoc, IsIso.hom_inv_id,
          id_whiskerRight, Category.id_comp, f.comm_assoc, ← MonoidalCategory.whiskerLeft_comp,
          IsIso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.comp_id] }
  hom_inv_id := by ext; exact IsIso.hom_inv_id f.f
  inv_hom_id := by ext; exact IsIso.inv_hom_id f.f

instance isIso_of_f_isIso {X Y : F.RelativeCenter} (f : X ⟶ Y) [IsIso f.f] : IsIso f :=
  (isoMk f).isIso_hom

/-! ### Monoidal structure on the relative centre -/

/-- The relative half-braiding on the tensor product `X.1 ⊗ Y.1` of two objects of
`F.RelativeCenter`. -/
@[expose, simps]
noncomputable def tensorHalfBraiding (X Y : F.RelativeCenter) :
    F.RelativeHalfBraiding (X.1 ⊗ Y.1) where
  β U :=
    α_ X.1 Y.1 (F.obj U) ≪≫
      whiskerLeftIso X.1 (Y.2.β U) ≪≫ (α_ X.1 (F.obj U) Y.1).symm ≪≫
      whiskerRightIso (X.2.β U) Y.1 ≪≫ α_ (F.obj U) X.1 Y.1
  monoidal U U' := by
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom,
      RelativeHalfBraiding.monoidal]
    calc
      _ = (X.1 ⊗ Y.1) ◁ δ F U U' ⊗≫
            X.1 ◁ (Y.2.β U).hom ▷ F.obj U' ⊗≫
            X.1 ◁ F.obj U ◁ (Y.2.β U').hom ⊗≫
            (X.1 ◁ (μ F U U' ▷ Y.1) ≫ (α_ X.1 (F.obj (U ⊗ U')) Y.1).inv ≫
              (X.1 ◁ δ F U U') ▷ Y.1) ⊗≫
            (X.2.β U).hom ▷ F.obj U' ▷ Y.1 ⊗≫
            F.obj U ◁ (X.2.β U').hom ▷ Y.1 ⊗≫
            μ F U U' ▷ (X.1 ⊗ Y.1) := by
        simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
        monoidal
      _ = (X.1 ⊗ Y.1) ◁ δ F U U' ⊗≫
            X.1 ◁ (Y.2.β U).hom ▷ F.obj U' ⊗≫
            ((X.1 ⊗ F.obj U) ◁ (Y.2.β U').hom ≫ (X.2.β U).hom ▷ (F.obj U' ⊗ Y.1)) ⊗≫
            F.obj U ◁ (X.2.β U').hom ▷ Y.1 ⊗≫
            μ F U U' ▷ (X.1 ⊗ Y.1) := by
        rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight,
          ← MonoidalCategory.whiskerLeft_comp, μ_δ, MonoidalCategory.whiskerLeft_id,
          id_whiskerRight, Category.comp_id]
        monoidal
      _ = _ := by
        rw [whisker_exchange]
        monoidal
  naturality {U U'} f := by
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
    calc
      _ = 𝟙 _ ⊗≫ X.1 ◁ (Y.1 ◁ F.map f ≫ (Y.2.β U').hom) ⊗≫
            (X.2.β U').hom ▷ Y.1 ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ X.1 ◁ (Y.2.β U).hom ⊗≫
            (X.1 ◁ F.map f ≫ (X.2.β U').hom) ▷ Y.1 ⊗≫ 𝟙 _ := by
        rw [RelativeHalfBraiding.naturality]
        monoidal
      _ = _ := by
        rw [RelativeHalfBraiding.naturality]
        monoidal

/-- The canonical `F`-relative half-braiding on `𝟙_ D`, constructed from the unitors of `D`. -/
@[expose, simps]
noncomputable def unitHalfBraiding : F.RelativeHalfBraiding (𝟙_ D) where
  β U := λ_ (F.obj U) ≪≫ (ρ_ (F.obj U)).symm
  monoidal U U' := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    calc
      _ = (λ_ (F.obj (U ⊗ U'))).hom ≫ (δ F U U' ≫ μ F U U') ≫
            (ρ_ (F.obj (U ⊗ U'))).inv := by
        rw [δ_μ, Category.id_comp]
      _ = _ := by
        monoidal
  naturality f := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [leftUnitor_naturality_assoc, rightUnitor_inv_naturality, Category.assoc]

/-- Left whiskering in `D` preserves compatibility with `tensorHalfBraiding`. -/
@[reassoc]
theorem whiskerLeft_comm (X : F.RelativeCenter) {Y₁ Y₂ : F.RelativeCenter} (f : Y₁ ⟶ Y₂) (U : C) :
    (X.1 ◁ f.f) ▷ F.obj U ≫ ((tensorHalfBraiding X Y₂).β U).hom =
      ((tensorHalfBraiding X Y₁).β U).hom ≫ F.obj U ◁ X.1 ◁ f.f := by
  simp only [tensorHalfBraiding_β, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫ X.1 ◁ (f.f ▷ F.obj U ≫ (Y₂.2.β U).hom) ⊗≫
          (X.2.β U).hom ▷ Y₂.1 ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X.1 ◁ (Y₁.2.β U).hom ⊗≫
          ((X.1 ⊗ F.obj U) ◁ f.f ≫ (X.2.β U).hom ▷ Y₂.1) ⊗≫ 𝟙 _ := by
      rw [f.comm]
      monoidal
    _ = _ := by
      rw [whisker_exchange]
      monoidal

/-- Right whiskering in `D` preserves compatibility with `tensorHalfBraiding`. -/
@[reassoc]
theorem whiskerRight_comm {X₁ X₂ : F.RelativeCenter} (f : X₁ ⟶ X₂) (Y : F.RelativeCenter) (U : C) :
    f.f ▷ Y.1 ▷ F.obj U ≫ ((tensorHalfBraiding X₂ Y).β U).hom =
      ((tensorHalfBraiding X₁ Y).β U).hom ≫ F.obj U ◁ f.f ▷ Y.1 := by
  simp only [tensorHalfBraiding_β, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫ (f.f ▷ (Y.1 ⊗ F.obj U) ≫ X₂.1 ◁ (Y.2.β U).hom) ⊗≫
          (X₂.2.β U).hom ▷ Y.1 ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X₁.1 ◁ (Y.2.β U).hom ⊗≫
          (f.f ▷ F.obj U ≫ (X₂.2.β U).hom) ▷ Y.1 ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      monoidal
    _ = _ := by
      rw [f.comm]
      monoidal

noncomputable instance instMonoidalCategoryStruct : MonoidalCategoryStruct F.RelativeCenter where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, tensorHalfBraiding X Y⟩
  whiskerLeft X _ _ f := ⟨X.1 ◁ f.f, whiskerLeft_comm X f⟩
  whiskerRight f Y := ⟨f.f ▷ Y.1, whiskerRight_comm f Y⟩
  tensorHom f g :=
    { f := f.f ⊗ₘ g.f
      comm U := by
        rw [tensorHom_def, comp_whiskerRight_assoc, whiskerLeft_comm, whiskerRight_comm_assoc,
          MonoidalCategory.whiskerLeft_comp] }
  tensorUnit := ⟨𝟙_ D, unitHalfBraiding⟩
  associator X Y Z :=
    { hom :=
        { f := (α_ X.1 Y.1 Z.1).hom
          comm U := by
            simp only [tensorHalfBraiding_β, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
              whiskerRightIso_hom]
            monoidal }
      inv :=
        { f := (α_ X.1 Y.1 Z.1).inv
          comm U := by
            simp only [tensorHalfBraiding_β, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
              whiskerRightIso_hom]
            monoidal }
      hom_inv_id := by ext; exact Iso.hom_inv_id _
      inv_hom_id := by ext; exact Iso.inv_hom_id _ }
  leftUnitor X :=
    { hom :=
        { f := (λ_ X.1).hom
          comm U := by
            simp only [tensorHalfBraiding_β, unitHalfBraiding_β, Iso.trans_hom,
              whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
            monoidal }
      inv :=
        { f := (λ_ X.1).inv
          comm U := by
            simp only [tensorHalfBraiding_β, unitHalfBraiding_β, Iso.trans_hom,
              whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
            monoidal }
      hom_inv_id := by ext; exact Iso.hom_inv_id _
      inv_hom_id := by ext; exact Iso.inv_hom_id _ }
  rightUnitor X :=
    { hom :=
        { f := (ρ_ X.1).hom
          comm U := by
            simp only [tensorHalfBraiding_β, unitHalfBraiding_β, Iso.trans_hom,
              whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
            monoidal }
      inv :=
        { f := (ρ_ X.1).inv
          comm U := by
            simp only [tensorHalfBraiding_β, unitHalfBraiding_β, Iso.trans_hom,
              whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
            monoidal }
      hom_inv_id := by ext; exact Iso.hom_inv_id _
      inv_hom_id := by ext; exact Iso.inv_hom_id _ }

@[simp]
theorem tensor_fst (X Y : F.RelativeCenter) : (X ⊗ Y).1 = X.1 ⊗ Y.1 :=
  rfl

@[simp]
theorem tensor_snd (X Y : F.RelativeCenter) : (X ⊗ Y).2 = tensorHalfBraiding X Y :=
  rfl

theorem tensor_β (X Y : F.RelativeCenter) (U : C) :
    (X ⊗ Y).2.β U =
      α_ X.1 Y.1 (F.obj U) ≪≫
        whiskerLeftIso X.1 (Y.2.β U) ≪≫ (α_ X.1 (F.obj U) Y.1).symm ≪≫
        whiskerRightIso (X.2.β U) Y.1 ≪≫ α_ (F.obj U) X.1 Y.1 :=
  rfl

@[simp]
theorem whiskerLeft_f (X : F.RelativeCenter) {Y₁ Y₂ : F.RelativeCenter} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).f = X.1 ◁ f.f :=
  rfl

@[simp]
theorem whiskerRight_f {X₁ X₂ : F.RelativeCenter} (f : X₁ ⟶ X₂) (Y : F.RelativeCenter) :
    (f ▷ Y).f = f.f ▷ Y.1 :=
  rfl

@[simp]
theorem tensorHom_f {X₁ Y₁ X₂ Y₂ : F.RelativeCenter} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).f = f.f ⊗ₘ g.f :=
  rfl

@[simp]
theorem tensorUnit_fst : (𝟙_ F.RelativeCenter).1 = 𝟙_ D :=
  rfl

@[simp]
theorem tensorUnit_snd : (𝟙_ F.RelativeCenter).2 = unitHalfBraiding :=
  rfl

theorem tensorUnit_β (U : C) :
    (𝟙_ F.RelativeCenter).2.β U = λ_ (F.obj U) ≪≫ (ρ_ (F.obj U)).symm :=
  rfl

@[simp]
theorem associator_hom_f (X Y Z : F.RelativeCenter) :
    Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
  rfl

@[simp]
theorem associator_inv_f (X Y Z : F.RelativeCenter) :
    Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv :=
  rfl

@[simp]
theorem leftUnitor_hom_f (X : F.RelativeCenter) : Hom.f (λ_ X).hom = (λ_ X.1).hom :=
  rfl

@[simp]
theorem leftUnitor_inv_f (X : F.RelativeCenter) : Hom.f (λ_ X).inv = (λ_ X.1).inv :=
  rfl

@[simp]
theorem rightUnitor_hom_f (X : F.RelativeCenter) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
  rfl

@[simp]
theorem rightUnitor_inv_f (X : F.RelativeCenter) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv :=
  rfl

noncomputable instance instMonoidalCategory : MonoidalCategory F.RelativeCenter where
  tensorHom_def f g := by ext; exact MonoidalCategory.tensorHom_def f.f g.f
  id_tensorHom_id X Y := by ext; exact MonoidalCategory.id_tensorHom_id X.1 Y.1
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    ext; exact MonoidalCategory.tensorHom_comp_tensorHom f₁.f f₂.f g₁.f g₂.f
  whiskerLeft_id X Y := by ext; exact MonoidalCategory.whiskerLeft_id X.1 Y.1
  id_whiskerRight X Y := by ext; exact MonoidalCategory.id_whiskerRight X.1 Y.1
  associator_naturality f₁ f₂ f₃ := by
    ext; exact MonoidalCategory.associator_naturality f₁.f f₂.f f₃.f
  leftUnitor_naturality f := by ext; exact MonoidalCategory.leftUnitor_naturality f.f
  rightUnitor_naturality f := by ext; exact MonoidalCategory.rightUnitor_naturality f.f
  pentagon W X Y Z := by ext; exact MonoidalCategory.pentagon W.1 X.1 Y.1 Z.1
  triangle X Y := by ext; exact MonoidalCategory.triangle X.1 Y.1

/-! ### The forgetful functor -/

variable (F) in
/-- The monoidal forgetful functor from the relative centre `F.RelativeCenter` to `D`. -/
@[expose, simps]
def forget : F.RelativeCenter ⥤ D where
  obj X := X.1
  map f := f.f

/-- The forgetful functor `RelativeCenter.forget F : F.RelativeCenter ⥤ D` is faithful. -/
instance instFaithfulForget : (forget F).Faithful where
  map_injective h := ext _ _ h

noncomputable instance instMonoidalForget : (forget F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left _ _ := by dsimp [forget]; simp
      μIso_hom_natural_right _ _ := by dsimp [forget]; simp
      associativity _ _ _ := by dsimp [forget]; simp
      left_unitality _ := by dsimp [forget]; simp
      right_unitality _ := by dsimp [forget]; simp }

@[simp]
theorem forget_ε : ε (forget F) = 𝟙 (𝟙_ D) :=
  rfl

@[simp]
theorem forget_η : η (forget F) = 𝟙 (𝟙_ D) :=
  rfl

@[simp]
theorem forget_μ (X Y : F.RelativeCenter) : μ (forget F) X Y = 𝟙 (X.1 ⊗ Y.1) :=
  rfl

@[simp]
theorem forget_δ (X Y : F.RelativeCenter) : δ (forget F) X Y = 𝟙 (X.1 ⊗ Y.1) :=
  rfl

instance instReflectsIsomorphismsForget : (forget F).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso f.f := ‹IsIso ((forget F).map f)›
    exact isIso_of_f_isIso f

end RelativeCenter

end CategoryTheory.Functor
