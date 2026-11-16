/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.CStar.Basic
public import TauCeti.CategoryTheory.Dagger.FullSubcategory

/-!
# Induced and full subcategories of C⋆-categories

Pulling back a C⋆-category `C` along an object map `F : D → C` equips
`CategoryTheory.InducedCategory C F` with a canonical `CStarCategory` structure induced by the
ambient Hom-space norms. Specializing to `CategoryTheory.ObjectProperty.FullSubcategory.obj` gives
the full C⋆-subcategory `P.FullSubcategory` for any `P : CategoryTheory.ObjectProperty C`.

## Main declarations

* `CategoryTheory.InducedCategory.instCStarCategory`: `CStarCategory (InducedCategory C F)`.
* `CategoryTheory.InducedCategory.norm_hom`, `CategoryTheory.InducedCategory.norm_homMk`: norm
  simplification for morphisms in `InducedCategory C F`.
* `CategoryTheory.ObjectProperty.instCStarCategoryFullSubcategory`:
  `CStarCategory P.FullSubcategory`.
* `CategoryTheory.ObjectProperty.norm_hom`, `CategoryTheory.ObjectProperty.norm_homMk`: norm
  simplification for morphisms in `P.FullSubcategory`.
-/

public section

open CategoryTheory TauCeti

universe v u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]

section InducedCategory

variable {D : Type u'} (F : D → C)

instance InducedCategory.instCStarCategory : CStarCategory (InducedCategory C F) :=
  let mHom (X Y : InducedCategory C F) : MetricSpace (X ⟶ Y) :=
    MetricSpace.induced InducedCategory.Hom.hom InducedCategory.homEquiv.injective inferInstance
  { homNorm := fun _ _ => ⟨fun f => ‖f.hom‖⟩
    homMetricSpace := mHom
    homCompleteSpace := fun X Y =>
      (@IsUniformInducing.completeSpace_congr _ _ (mHom X Y).toUniformSpace inferInstance
        InducedCategory.Hom.hom ⟨rfl⟩ InducedCategory.homEquiv.surjective).mpr inferInstance
    dist_eq := fun f g => dist_eq_norm_neg_add f.hom g.hom
    norm_smul_le := fun r f => norm_smul_le r f.hom
    norm_comp_le := fun f g => CStarCategory.norm_comp_le f.hom g.hom
    norm_mul_self_le := fun f => CStarCategory.norm_mul_self_le f.hom
    exists_comp_dagger_eq := fun f =>
      let ⟨h, hh⟩ := CStarCategory.exists_comp_dagger_eq f.hom
      ⟨InducedCategory.homMk h, InducedCategory.hom_ext hh⟩ }

variable {F}

/-- The norm of a morphism in `InducedCategory C F` is the norm of its underlying morphism. -/
@[simp] theorem InducedCategory.norm_hom {X Y : InducedCategory C F} (f : X ⟶ Y) :
    ‖f‖ = ‖f.hom‖ := (rfl)

/-- Wrapping a morphism in `InducedCategory C F` preserves its norm. Not `@[simp]` since `simp`
proves this via `InducedCategory.norm_hom` and `InducedCategory.homMk_hom`. -/
theorem InducedCategory.norm_homMk {X Y : InducedCategory C F} (f : F X ⟶ F Y) :
    ‖InducedCategory.homMk f‖ = ‖f‖ := (rfl)

end InducedCategory

namespace ObjectProperty

instance instCStarCategoryFullSubcategory (P : ObjectProperty C) :
    CStarCategory P.FullSubcategory :=
  InducedCategory.instCStarCategory ObjectProperty.FullSubcategory.obj

/-- The norm of a morphism in `P.FullSubcategory` is the norm of its underlying morphism. -/
@[simp] theorem norm_hom {P : ObjectProperty C} {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ‖f‖ = ‖f.hom‖ := (rfl)

/-- Constructing a morphism in `P.FullSubcategory` preserves its norm. Not `@[simp]` since `simp`
proves this via `ObjectProperty.norm_hom` and `ObjectProperty.homMk_hom`. -/
theorem norm_homMk {P : ObjectProperty C} {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) :
    ‖P.homMk f‖ = ‖f‖ := (rfl)

end ObjectProperty

end CategoryTheory
