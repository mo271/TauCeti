/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Monoidal functors, equivalences, and closed structures on full monoidal subcategories

If `P` is a monoidal property of objects of a monoidal category `C`, Mathlib equips
`P.FullSubcategory` with the induced monoidal structure, and if `C` is closed monoidal and `P` is
closed under internal Homs, with the induced closed monoidal structure
(`CategoryTheory.ObjectProperty.fullMonoidalClosedSubcategory`), with internal Homs computed in
`C` (`CategoryTheory.ObjectProperty.ihom_obj`, `CategoryTheory.ObjectProperty.ihom_map_hom`).
This file records:

* that lifting a strong monoidal functor through a full monoidal subcategory gives a strong
  monoidal functor (`CategoryTheory.ObjectProperty.liftMonoidal`), with unit and tensor
  comparisons given by those of the original functor;
* that a monoidal equivalence restricts along `CategoryTheory.Equivalence.congrFullSubcategory`
  to a monoidal equivalence between corresponding full monoidal subcategories;
* that evaluation, coevaluation, and precomposition for internal Homs in a closed monoidal full
  subcategory are those of `C`.

## Main declarations

* `CategoryTheory.ObjectProperty.ihom_ev_app_hom` and
  `CategoryTheory.ObjectProperty.ihom_coev_app_hom`: evaluation and coevaluation;
* `CategoryTheory.ObjectProperty.pre_app_hom`: precomposition with a morphism of the
  subcategory;
* `CategoryTheory.ObjectProperty.liftMonoidal`: monoidal instance on `Q.lift F hF`, with
  `lift_ε_hom`, `lift_η_hom`, `lift_μ_hom`, `lift_δ_hom`;
* `CategoryTheory.Equivalence.congrFullSubcategoryFunctorMonoidal`,
  `CategoryTheory.Equivalence.congrFullSubcategoryInverseMonoidal`,
  `CategoryTheory.Equivalence.congrFullSubcategory_isMonoidal`: restriction of a monoidal
  equivalence to full monoidal subcategories, with component lemmas for `ε`, `η`, `μ`, and `δ`.
-/

public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed

universe v u v' u'

namespace ObjectProperty

section Closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (P : ObjectProperty C) [P.IsMonoidal] [P.IsMonoidalClosed]

/-- Evaluation in the closed monoidal full subcategory is evaluation in the ambient category. -/
@[simp]
theorem ihom_ev_app_hom (X Y : P.FullSubcategory) :
    ((ihom.ev X).app Y).hom = (ihom.ev X.obj).app Y.obj :=
  (rfl)

/-- Coevaluation in the closed monoidal full subcategory is coevaluation in the ambient
category. -/
@[simp]
theorem ihom_coev_app_hom (X Y : P.FullSubcategory) :
    ((ihom.coev X).app Y).hom = (ihom.coev X.obj).app Y.obj :=
  (rfl)

variable {P}

/-- Precomposition of internal Homs in the closed monoidal full subcategory is precomposition in
the ambient category. -/
@[simp]
theorem pre_app_hom {X X' : P.FullSubcategory} (f : X ⟶ X') (Y : P.FullSubcategory) :
    ((pre f).app Y).hom = (pre f.hom).app Y.obj := by
  -- Both maps are the transpose of `f ▷ _` followed by evaluation in `C`.
  refine ((eq_curry_iff (A := X.obj) _ _).mpr ?_).trans
    ((curry_eq_iff _ _).mpr (uncurry_pre f.hom Y.obj).symm)
  exact congrArg InducedCategory.Hom.hom (id_tensor_pre_app_comp_ev f Y)

end Closed

section Lift

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (Q : ObjectProperty D) [Q.IsMonoidal]
  (F : C ⥤ D) [F.Monoidal] (hF : ∀ X, Q (F.obj X))

/-- Lifting a strong monoidal functor through a full monoidal subcategory gives a strong monoidal
functor, whose unit and tensor comparisons are those of the original functor. -/
noncomputable instance liftMonoidal : (Q.lift F hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Q.isoMk (Functor.Monoidal.εIso F)
      μIso := fun X Y ↦ Q.isoMk (Functor.Monoidal.μIso F X Y)
      μIso_hom_natural_left := fun f Y ↦ hom_ext _ (Functor.LaxMonoidal.μ_natural_left F f Y)
      μIso_hom_natural_right := fun X f ↦ hom_ext _ (Functor.LaxMonoidal.μ_natural_right F X f)
      associativity := fun X Y Z ↦ hom_ext _ (Functor.LaxMonoidal.associativity F X Y Z)
      left_unitality := fun X ↦ hom_ext _ (Functor.LaxMonoidal.left_unitality F X)
      right_unitality := fun X ↦ hom_ext _ (Functor.LaxMonoidal.right_unitality F X) }

/-- The unit comparison of a lifted monoidal functor is that of the original functor. -/
@[simp]
lemma lift_ε_hom : (Functor.LaxMonoidal.ε (Q.lift F hF)).hom = Functor.LaxMonoidal.ε F := rfl

/-- The inverse unit comparison of a lifted monoidal functor is that of the original functor. -/
@[simp]
lemma lift_η_hom : (Functor.OplaxMonoidal.η (Q.lift F hF)).hom = Functor.OplaxMonoidal.η F := rfl

/-- The tensor comparison of a lifted monoidal functor is that of the original functor. -/
@[simp]
lemma lift_μ_hom (X Y : C) :
    (Functor.LaxMonoidal.μ (Q.lift F hF) X Y).hom = Functor.LaxMonoidal.μ F X Y := rfl

/-- The inverse tensor comparison of a lifted monoidal functor is that of the original functor. -/
@[simp]
lemma lift_δ_hom (X Y : C) :
    (Functor.OplaxMonoidal.δ (Q.lift F hF) X Y).hom = Functor.OplaxMonoidal.δ F X Y := rfl

end Lift

end ObjectProperty

namespace Equivalence

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  [P.IsMonoidal] [Q.IsMonoidal] [Q.IsClosedUnderIsomorphisms]

/-- The forward functor of a monoidal equivalence restricted to corresponding full monoidal
subcategories is strong monoidal. -/
noncomputable instance congrFullSubcategoryFunctorMonoidal (e : C ≌ D) [e.functor.Monoidal]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).functor.Monoidal :=
  inferInstanceAs (Q.lift (P.ι ⋙ e.functor) _).Monoidal

/-- The inverse functor of a monoidal equivalence restricted to corresponding full monoidal
subcategories is strong monoidal. -/
noncomputable instance congrFullSubcategoryInverseMonoidal (e : C ≌ D) [e.inverse.Monoidal]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).inverse.Monoidal :=
  inferInstanceAs (P.lift (Q.ι ⋙ e.inverse) _).Monoidal

/-- The unit comparison of the forward functor of `congrFullSubcategory` is that of `e.functor`. -/
@[simp]
lemma congrFullSubcategory_functor_ε_hom (e : C ≌ D) [e.functor.Monoidal]
    (h : Q.inverseImage e.functor = P) :
    (Functor.LaxMonoidal.ε (e.congrFullSubcategory h).functor).hom =
      Functor.LaxMonoidal.ε e.functor := by
  -- The monoidal instance on `(e.congrFullSubcategory h).functor` is `ObjectProperty.liftMonoidal`.
  change (Functor.LaxMonoidal.ε (Q.lift (P.ι ⋙ e.functor) _)).hom = _
  simp

/-- The inverse unit comparison of the forward functor of `congrFullSubcategory` is that of
`e.functor`. -/
@[simp]
lemma congrFullSubcategory_functor_η_hom (e : C ≌ D) [e.functor.Monoidal]
    (h : Q.inverseImage e.functor = P) :
    (Functor.OplaxMonoidal.η (e.congrFullSubcategory h).functor).hom =
      Functor.OplaxMonoidal.η e.functor := by
  -- The monoidal instance on `(e.congrFullSubcategory h).functor` is `ObjectProperty.liftMonoidal`,
  -- and `Functor.OplaxMonoidal.η P.ι` is definitionally `𝟙 (𝟙_ C)`.
  change (Functor.OplaxMonoidal.η (Q.lift (P.ι ⋙ e.functor) _)).hom = _
  rw [ObjectProperty.lift_η_hom, Functor.OplaxMonoidal.comp_η]
  exact (congrArg (· ≫ _) (e.functor.map_id (𝟙_ C))).trans (Category.id_comp _)

/-- The tensorator of the forward functor of `congrFullSubcategory` is that of `e.functor`. -/
@[simp]
lemma congrFullSubcategory_functor_μ_hom (e : C ≌ D) [e.functor.Monoidal]
    (h : Q.inverseImage e.functor = P) (X Y : P.FullSubcategory) :
    (Functor.LaxMonoidal.μ (e.congrFullSubcategory h).functor X Y).hom =
      Functor.LaxMonoidal.μ e.functor X.obj Y.obj := by
  -- The monoidal instance on `(e.congrFullSubcategory h).functor` is `ObjectProperty.liftMonoidal`.
  change (Functor.LaxMonoidal.μ (Q.lift (P.ι ⋙ e.functor) _) X Y).hom = _
  simp

/-- The inverse tensorator of the forward functor of `congrFullSubcategory` is that of
`e.functor`. -/
@[simp]
lemma congrFullSubcategory_functor_δ_hom (e : C ≌ D) [e.functor.Monoidal]
    (h : Q.inverseImage e.functor = P) (X Y : P.FullSubcategory) :
    (Functor.OplaxMonoidal.δ (e.congrFullSubcategory h).functor X Y).hom =
      Functor.OplaxMonoidal.δ e.functor X.obj Y.obj := by
  -- The monoidal instance on `(e.congrFullSubcategory h).functor` is `ObjectProperty.liftMonoidal`.
  change (Functor.OplaxMonoidal.δ (Q.lift (P.ι ⋙ e.functor) _) X Y).hom = _
  simp

/-- The unit comparison of the inverse functor of `congrFullSubcategory` is that of `e.inverse`. -/
@[simp]
lemma congrFullSubcategory_inverse_ε_hom (e : C ≌ D) [e.inverse.Monoidal]
    (h : Q.inverseImage e.functor = P) :
    (Functor.LaxMonoidal.ε (e.congrFullSubcategory h).inverse).hom =
      Functor.LaxMonoidal.ε e.inverse := by
  -- The monoidal instance on `(e.congrFullSubcategory h).inverse` is `ObjectProperty.liftMonoidal`.
  change (Functor.LaxMonoidal.ε (P.lift (Q.ι ⋙ e.inverse) _)).hom = _
  simp

/-- The tensorator of the inverse functor of `congrFullSubcategory` is that of `e.inverse`. -/
@[simp]
lemma congrFullSubcategory_inverse_μ_hom (e : C ≌ D) [e.inverse.Monoidal]
    (h : Q.inverseImage e.functor = P) (X Y : Q.FullSubcategory) :
    (Functor.LaxMonoidal.μ (e.congrFullSubcategory h).inverse X Y).hom =
      Functor.LaxMonoidal.μ e.inverse X.obj Y.obj := by
  -- The monoidal instance on `(e.congrFullSubcategory h).inverse` is `ObjectProperty.liftMonoidal`.
  change (Functor.LaxMonoidal.μ (P.lift (Q.ι ⋙ e.inverse) _) X Y).hom = _
  simp

/-- A monoidal equivalence restricts along `congrFullSubcategory` to a monoidal equivalence. -/
instance congrFullSubcategory_isMonoidal (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal]
    [e.IsMonoidal] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).IsMonoidal where
  leftAdjoint_ε := ObjectProperty.hom_ext _ <|
    (congrFullSubcategory_inverse_ε_hom e h).trans <|
      (Adjunction.IsMonoidal.leftAdjoint_ε (adj := e.toAdjunction)).trans <|
        congrArg (e.unit.app (𝟙_ C) ≫ e.inverse.map ·)
          (congrFullSubcategory_functor_η_hom e h).symm
  leftAdjoint_μ X Y := ObjectProperty.hom_ext _ <|
    (congrFullSubcategory_inverse_μ_hom e h X Y).trans <|
      (Adjunction.IsMonoidal.leftAdjoint_μ (adj := e.toAdjunction) X.obj Y.obj).trans <|
        congrArg (fun k ↦ e.unit.app _ ≫
            e.inverse.map (k ≫ (e.counit.app X.obj ⊗ₘ e.counit.app Y.obj)))
          (congrFullSubcategory_functor_δ_hom e h
            ((e.congrFullSubcategory h).inverse.obj X)
            ((e.congrFullSubcategory h).inverse.obj Y)).symm

end Equivalence

end CategoryTheory
