/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# Reversal involutions on cosimplicial and augmented simplicial objects

Mathlib defines the covariant involution `SimplicialObject.opFunctor` on simplicial objects by
precomposition with `SimplexCategory.rev.op`, reversing the order of faces and degeneracies.
This file extends that involution to:

* `CategoryTheory.CosimplicialObject.opFunctor`: reversal on cosimplicial objects, obtained by
  precomposition with `SimplexCategory.rev`, together with its termwise identification
  `CosimplicialObject.opObjIso` and equivalence `CosimplicialObject.opEquivalence`;
* `CategoryTheory.SimplicialObject.Augmented.opFunctor`: reversal on augmented simplicial
  objects, reversing the simplicial part and keeping the augmentation object;
* `CategoryTheory.CosimplicialObject.Augmented.opFunctor`: reversal on augmented cosimplicial
  objects, keeping the coaugmentation object and reversing the cosimplicial part.

We also record the compatibility isomorphisms between these involutions, the opposite-category
duality `SimplicialObject.Augmented.rightOp`, and whiskering by an arbitrary functor.

## References

* Mathlib's `Mathlib.AlgebraicTopology.SimplicialObject.Op` for the unaugmented simplicial
  involution `SimplicialObject.opFunctor`.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u v' u'

namespace CategoryTheory

namespace CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The covariant involution on cosimplicial objects induced by
`SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.
Not marked `@[implicit_reducible]` so `(opFunctor.obj X).obj n` stays distinct from `X.obj n`;
transport between them using `opObjIso`. -/
def opFunctor : CosimplicialObject C ⥤ CosimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev

/-- The canonical identification `(opFunctor.obj X).obj n ≅ X.obj n` for a cosimplicial object. -/
def opObjIso {X : CosimplicialObject C} {n : SimplexCategory} :
    (opFunctor.obj X).obj n ≅ X.obj n := Iso.refl _

@[simp]
lemma opFunctor_map_app {X Y : CosimplicialObject C} (f : X ⟶ Y) (n : SimplexCategory) :
    (opFunctor.map f).app n = opObjIso.hom ≫ f.app n ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
lemma opFunctor_obj_map (X : CosimplicialObject C) {n m : SimplexCategory} (f : n ⟶ m) :
    (opFunctor.obj X).map f =
      opObjIso.hom ≫ X.map (SimplexCategory.rev.map f) ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
lemma opFunctor_obj_δ (X : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    (opFunctor.obj X).δ i = opObjIso.hom ≫ X.δ i.rev ≫ opObjIso.inv := by
  simp [opObjIso, CosimplicialObject.δ]

@[simp]
lemma opFunctor_obj_σ (X : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    (opFunctor.obj X).σ i = opObjIso.hom ≫ X.σ i.rev ≫ opObjIso.inv := by
  simp [opObjIso, CosimplicialObject.σ]

/-- Reversing a cosimplicial object twice is naturally isomorphic to the identity. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso SimplexCategory.revCompRevIso ≪≫
    Functor.whiskeringLeftObjIdIso

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_app (X : CosimplicialObject C) (n : SimplexCategory) :
    (opFunctorCompOpFunctorIso.hom.app X).app n = opObjIso.hom ≫ opObjIso.hom := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_app (X : CosimplicialObject C) (n : SimplexCategory) :
    (opFunctorCompOpFunctorIso.inv.app X).app n = opObjIso.inv ≫ opObjIso.inv := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

/-- The reversal involution on cosimplicial objects as an equivalence of categories. -/
@[simps]
def opEquivalence : CosimplicialObject C ≌ CosimplicialObject C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso
  functor_unitIso_comp X := by
    ext n
    simp

/-- Reversing a cosimplicial object commutes with postcomposition by a functor `F`. -/
def opFunctorWhiskeringIso {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (X : CosimplicialObject C) :
    ((whiskering C D).obj F).obj (opFunctor.obj X) ≅
      opFunctor.obj (((whiskering C D).obj F).obj X) :=
  NatIso.ofComponents
    (fun n ↦ F.mapIso (opObjIso (X := X) (n := n)) ≪≫
      (opObjIso (X := ((whiskering C D).obj F).obj X) (n := n)).symm)
    fun {n m} f ↦ by
      dsimp [whiskering]
      simp only [opFunctor_obj_map, Functor.comp_map, Category.assoc, Iso.inv_hom_id_assoc,
        ← F.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
lemma opFunctorWhiskeringIso_hom_app {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (X : CosimplicialObject C) (n : SimplexCategory) :
    (opFunctorWhiskeringIso F X).hom.app n =
      F.map (opObjIso (X := X) (n := n)).hom ≫
        (opObjIso (X := ((whiskering C D).obj F).obj X) (n := n)).inv := (rfl)

@[simp]
lemma opFunctorWhiskeringIso_inv_app {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (X : CosimplicialObject C) (n : SimplexCategory) :
    (opFunctorWhiskeringIso F X).inv.app n =
      (opObjIso (X := ((whiskering C D).obj F).obj X) (n := n)).hom ≫
        F.map (opObjIso (X := X) (n := n)).inv := (rfl)

end CosimplicialObject

namespace SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- The covariant reversal involution on augmented simplicial objects: it precomposes the
simplicial part by `SimplexCategory.rev.op` and leaves the augmentation object unchanged. -/
@[implicit_reducible]
def opFunctor : SimplicialObject.Augmented C ⥤ SimplicialObject.Augmented C where
  obj X :=
    { left := _root_.SimplicialObject.opFunctor.obj X.left
      right := X.right
      hom :=
        { app n := _root_.SimplicialObject.opObjIso.hom ≫ X.hom.app n
          naturality {n m} f := by
            simp only [Category.assoc, Functor.const_obj_map]
            simp } }
  map f :=
    { left := _root_.SimplicialObject.opFunctor.map f.left
      right := f.right
      w := by
        ext n
        simp [SimplicialObject.Augmented.w_app] }

@[simp]
lemma opFunctor_obj_left (X : SimplicialObject.Augmented C) :
    (opFunctor.obj X).left = _root_.SimplicialObject.opFunctor.obj X.left := (rfl)

@[simp]
lemma opFunctor_obj_right (X : SimplicialObject.Augmented C) :
    (opFunctor.obj X).right = X.right := (rfl)

@[simp]
lemma opFunctor_obj_hom_app (X : SimplicialObject.Augmented C) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.obj X).hom.app n = _root_.SimplicialObject.opObjIso.hom ≫ X.hom.app n := (rfl)

@[simp]
lemma opFunctor_map_left {X Y : SimplicialObject.Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = _root_.SimplicialObject.opFunctor.map f.left := (rfl)

@[simp]
lemma opFunctor_map_right {X Y : SimplicialObject.Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = f.right := (rfl)

/-- Reversing an augmented simplicial object twice is naturally isomorphic to the identity. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X ↦ Comma.isoMk (_root_.SimplicialObject.opFunctorCompOpFunctorIso.app X.left)
      (Iso.refl X.right) (by
        ext n
        simp only [Functor.comp_obj, Functor.id_obj, Functor.const_obj_obj, Functor.id_map,
          NatTrans.comp_app, Iso.app_hom,
          _root_.SimplicialObject.opFunctorCompOpFunctorIso_hom_app_app,
          Category.assoc, opFunctor_obj_hom_app, Functor.const_map_app, Iso.refl_hom,
          Iso.cancel_iso_hom_left]
        exact (Category.comp_id (X.hom.app n)).symm))
    fun f ↦ by
      apply SimplicialObject.Augmented.hom_ext
      · exact _root_.SimplicialObject.opFunctorCompOpFunctorIso.hom.naturality f.left
      · exact (Category.comp_id _).trans (Category.id_comp _).symm

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_left (X : SimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).left =
      _root_.SimplicialObject.opFunctorCompOpFunctorIso.hom.app X.left := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_right (X : SimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).right = 𝟙 X.right := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_left (X : SimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).left =
      _root_.SimplicialObject.opFunctorCompOpFunctorIso.inv.app X.left := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_right (X : SimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).right = 𝟙 X.right := (rfl)

/-- The reversal involution on augmented simplicial objects as an equivalence of categories. -/
@[simps]
def opEquivalence : SimplicialObject.Augmented C ≌ SimplicialObject.Augmented C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso
  functor_unitIso_comp X := by
    apply SimplicialObject.Augmented.hom_ext
    · exact _root_.SimplicialObject.opEquivalence.functor_unitIso_comp X.left
    · exact Category.id_comp _

end SimplicialObject.Augmented

namespace CosimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- Construct an isomorphism of augmented cosimplicial objects from isomorphisms on the
coaugmentation object and cosimplicial part commuting with the coaugmentation. -/
@[simps! hom_left hom_right inv_left inv_right]
def isoMk {X Y : CosimplicialObject.Augmented C}
    (eL : X.left ≅ Y.left) (eR : X.right ≅ Y.right)
    (hw : ∀ n : SimplexCategory, eL.hom ≫ Y.hom.app n = X.hom.app n ≫ eR.hom.app n) :
    X ≅ Y :=
  Comma.isoMk eL eR (NatTrans.ext <| funext hw)

/-- The covariant reversal involution on augmented cosimplicial objects: it keeps the
coaugmentation object and precomposes the cosimplicial part by `SimplexCategory.rev`. -/
@[implicit_reducible]
def opFunctor : CosimplicialObject.Augmented C ⥤ CosimplicialObject.Augmented C where
  obj X :=
    { left := X.left
      right := CosimplicialObject.opFunctor.obj X.right
      hom :=
        { app n := X.hom.app n ≫ CosimplicialObject.opObjIso.inv
          naturality {n m} f := by
            have h : X.hom.app m = X.hom.app n ≫ X.right.map (SimplexCategory.rev.map f) := by
              simpa [Functor.const_obj_map] using X.hom.naturality (SimplexCategory.rev.map f)
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.id_obj,
              Functor.id_map]
            rw [Category.id_comp, CosimplicialObject.opFunctor_obj_map, Category.assoc,
              Iso.inv_hom_id_assoc, ← Category.assoc]
            exact congrArg (· ≫ CosimplicialObject.opObjIso.inv) h } }
  map f :=
    { left := f.left
      right := CosimplicialObject.opFunctor.map f.right
      w := by
        ext n
        dsimp only [NatTrans.comp_app, Functor.const_map_app, Functor.id_map]
        rw [CosimplicialObject.opFunctor_map_app, Category.assoc, Iso.inv_hom_id_assoc,
          ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ CosimplicialObject.opObjIso.inv) (congr_app f.w n) }

@[simp]
lemma opFunctor_obj_left (X : CosimplicialObject.Augmented C) :
    (opFunctor.obj X).left = X.left := (rfl)

@[simp]
lemma opFunctor_obj_right (X : CosimplicialObject.Augmented C) :
    (opFunctor.obj X).right = CosimplicialObject.opFunctor.obj X.right := (rfl)

@[simp]
lemma opFunctor_obj_hom_app (X : CosimplicialObject.Augmented C) (n : SimplexCategory) :
    (opFunctor.obj X).hom.app n = X.hom.app n ≫ CosimplicialObject.opObjIso.inv := (rfl)

@[simp]
lemma opFunctor_map_left {X Y : CosimplicialObject.Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = f.left := (rfl)

@[simp]
lemma opFunctor_map_right {X Y : CosimplicialObject.Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = CosimplicialObject.opFunctor.map f.right := (rfl)

/-- Reversing an augmented cosimplicial object twice is naturally isomorphic to the identity. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X ↦ isoMk (Iso.refl X.left)
      (CosimplicialObject.opFunctorCompOpFunctorIso.app X.right) fun n ↦ by
        calc
          (Iso.refl X.left).hom ≫ X.hom.app n
              = X.hom.app n := Category.id_comp _
          _ = X.hom.app n ≫
                (CosimplicialObject.opObjIso.inv ≫ CosimplicialObject.opObjIso.inv) ≫
                  (CosimplicialObject.opObjIso.hom ≫ CosimplicialObject.opObjIso.hom) := by
                rw [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
          _ = ((X.hom.app n ≫ CosimplicialObject.opObjIso.inv) ≫
                  CosimplicialObject.opObjIso.inv) ≫
                (CosimplicialObject.opFunctorCompOpFunctorIso.hom.app X.right).app n := by
                rw [CosimplicialObject.opFunctorCompOpFunctorIso_hom_app_app,
                  Category.assoc, Category.assoc, Category.assoc])
    fun f ↦ by
      apply hom_ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact CosimplicialObject.opFunctorCompOpFunctorIso.hom.naturality f.right

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_left (X : CosimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).left = 𝟙 X.left := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_right (X : CosimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).right =
      CosimplicialObject.opFunctorCompOpFunctorIso.hom.app X.right := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_left (X : CosimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).left = 𝟙 X.left := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_right (X : CosimplicialObject.Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).right =
      CosimplicialObject.opFunctorCompOpFunctorIso.inv.app X.right := (rfl)

/-- The reversal involution on augmented cosimplicial objects as an equivalence of categories. -/
@[simps]
def opEquivalence : CosimplicialObject.Augmented C ≌ CosimplicialObject.Augmented C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso
  functor_unitIso_comp X := by
    apply hom_ext
    · exact Category.id_comp _
    · exact CosimplicialObject.opEquivalence.functor_unitIso_comp X.right

/-- Reversing an augmented cosimplicial object commutes with postcomposition by a functor `F`. -/
def opFunctorWhiskeringObjIso {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (X : CosimplicialObject.Augmented C) :
    (whiskeringObj C D F).obj (opFunctor.obj X) ≅
      opFunctor.obj ((whiskeringObj C D F).obj X) :=
  isoMk (CategoryTheory.eqToIso rfl)
    (CategoryTheory.eqToIso rfl ≪≫
      CosimplicialObject.opFunctorWhiskeringIso F X.right ≪≫
      CategoryTheory.eqToIso rfl)
    fun n ↦ by
      have h : F.map (X.hom.app n) ≫
            (CosimplicialObject.opObjIso
              (X := ((CosimplicialObject.whiskering C D).obj F).obj X.right) (n := n)).inv =
          F.map (X.hom.app n ≫ CosimplicialObject.opObjIso.inv) ≫
            (CosimplicialObject.opFunctorWhiskeringIso F X.right).hom.app n := by
        rw [CosimplicialObject.opFunctorWhiskeringIso_hom_app, ← F.map_comp_assoc,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]
      refine (Category.id_comp _).trans ?_
      refine (congrArg (· ≫ _) (Category.id_comp _)).trans ?_
      refine h.trans ?_
      refine (congrArg (· ≫ _) (Category.id_comp _).symm).trans ?_
      exact congrArg (_ ≫ ·) ((Category.id_comp _).trans (Category.comp_id _)).symm

end CosimplicialObject.Augmented

namespace SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Passing to the opposite category intertwines simplicial reversal and cosimplicial reversal. -/
def opFunctorRightOpIso (X : SimplicialObject C) :
    (_root_.SimplicialObject.opFunctor.obj X).rightOp ≅
      CosimplicialObject.opFunctor.obj X.rightOp :=
  NatIso.ofComponents
    (fun n ↦ (_root_.SimplicialObject.opObjIso (X := X) (n := op n)).op.symm ≪≫
      (CosimplicialObject.opObjIso (X := X.rightOp) (n := n)).symm)
    fun {n m} f ↦ by
      dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.rightOp_map, Quiver.Hom.unop_op]
      rw [_root_.SimplicialObject.opFunctor_obj_map, CosimplicialObject.opFunctor_obj_map,
        Iso.op_inv, Iso.op_inv, op_comp, op_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← op_comp_assoc (f := (_root_.SimplicialObject.opObjIso (X := X) (n := op m)).inv)
        (g := (_root_.SimplicialObject.opObjIso (X := X) (n := op m)).hom),
        Iso.inv_hom_id, op_id, Category.id_comp]
      rfl

@[simp]
lemma opFunctorRightOpIso_hom_app (X : SimplicialObject C) (n : SimplexCategory) :
    (opFunctorRightOpIso X).hom.app n =
      (_root_.SimplicialObject.opObjIso (X := X) (n := op n)).inv.op ≫
        (CosimplicialObject.opObjIso (X := X.rightOp) (n := n)).inv := (rfl)

@[simp]
lemma opFunctorRightOpIso_inv_app (X : SimplicialObject C) (n : SimplexCategory) :
    (opFunctorRightOpIso X).inv.app n =
      (CosimplicialObject.opObjIso (X := X.rightOp) (n := n)).hom ≫
        (_root_.SimplicialObject.opObjIso (X := X) (n := op n)).hom.op := (rfl)

end SimplicialObject

namespace SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- Passing to the opposite category intertwines augmented simplicial reversal and augmented
cosimplicial reversal. -/
def opFunctorRightOpIso (X : SimplicialObject.Augmented C) :
    (opFunctor.obj X).rightOp ≅ CosimplicialObject.Augmented.opFunctor.obj X.rightOp :=
  CosimplicialObject.Augmented.isoMk (CategoryTheory.eqToIso rfl)
    (CategoryTheory.eqToIso rfl ≪≫
      SimplicialObject.opFunctorRightOpIso X.left ≪≫
      CategoryTheory.eqToIso rfl)
    fun n ↦ by
      have h : (X.hom.app (op n)).op ≫
            (CosimplicialObject.opObjIso (X := X.left.rightOp) (n := n)).inv =
          (_root_.SimplicialObject.opObjIso.hom ≫ X.hom.app (op n)).op ≫
            (SimplicialObject.opFunctorRightOpIso X.left).hom.app n := by
        rw [SimplicialObject.opFunctorRightOpIso_hom_app, op_comp, Category.assoc,
          ← op_comp_assoc (f := (_root_.SimplicialObject.opObjIso (X := X.left) (n := op n)).inv)
            (g := (_root_.SimplicialObject.opObjIso (X := X.left) (n := op n)).hom),
          Iso.inv_hom_id, op_id, Category.id_comp]
      refine (Category.id_comp _).trans ?_
      refine h.trans ?_
      exact congrArg (_ ≫ ·) ((Category.id_comp _).trans (Category.comp_id _)).symm

end SimplicialObject.Augmented

end CategoryTheory
