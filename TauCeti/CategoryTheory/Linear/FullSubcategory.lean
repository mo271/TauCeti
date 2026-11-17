/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Additive and linear structure on morphisms of a full subcategory

A full subcategory of a preadditive (resp. `R`-linear) category inherits a preadditive
(resp. `R`-linear) structure. This file records that the underlying morphism of a sum, a
negation, a difference or a scalar multiple of morphisms in the full subcategory is the
corresponding operation applied to the underlying morphisms in the ambient category. The zero
morphism is Mathlib's `CategoryTheory.ObjectProperty.zero_hom`. It also records that lifting an
`R`-linear functor through a full subcategory preserves `R`-linearity, and consequently that an
`R`-linear equivalence restricts to an `R`-linear equivalence between corresponding full
subcategories.

## Main results

* `CategoryTheory.ObjectProperty.add_hom`, `CategoryTheory.ObjectProperty.neg_hom`,
  `CategoryTheory.ObjectProperty.sub_hom`: the underlying morphism of a morphism built from the
  preadditive structure.
* `CategoryTheory.ObjectProperty.smul_hom`: the underlying morphism of a scalar multiple.
* `CategoryTheory.ObjectProperty.nsmul_hom`, `CategoryTheory.ObjectProperty.zsmul_hom`:
  the underlying morphism of a natural or integer multiple in a preadditive category.
* `CategoryTheory.ObjectProperty.lift_linear`: lifting an `R`-linear functor through a full
  subcategory gives an `R`-linear functor.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_linear` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_linear`: an `R`-linear equivalence
  restricts to an `R`-linear equivalence between corresponding full subcategories.
-/

public section

namespace CategoryTheory

universe w v u v' u'

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

section Preadditive

variable [Preadditive C] {X Y : P.FullSubcategory}

/-- The underlying morphism of a sum in a full subcategory is the sum of the underlying
morphisms. -/
@[simp] theorem add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl

/-- The underlying morphism of a negation in a full subcategory is the negation of the underlying
morphism. -/
@[simp] theorem neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl

/-- The underlying morphism of a difference in a full subcategory is the difference of the
underlying morphisms. -/
@[simp] theorem sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl

/-- The underlying morphism of a natural multiple in a full subcategory is the natural
multiple of the underlying morphism. -/
@[simp] theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

/-- The underlying morphism of an integer multiple in a full subcategory is the integer
multiple of the underlying morphism. -/
@[simp] theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

end Preadditive

/-- The underlying morphism of a scalar multiple in a full subcategory of a linear category is the
scalar multiple of the underlying morphism. -/
@[simp] theorem smul_hom {R : Type w} [Semiring R] [Preadditive C] [Linear R C]
    {X Y : P.FullSubcategory} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom := rfl

/-- Lifting an `R`-linear functor through a full subcategory gives an `R`-linear functor. -/
instance lift_linear {D : Type u'} [Category.{v'} D] [Preadditive C] [Preadditive D]
    {R : Type w} [Semiring R] [Linear R C] [Linear R D]
    (Q : ObjectProperty D) (F : C ⥤ D) [F.Linear R] (hF : ∀ X, Q (F.obj X)) :
    (Q.lift F hF).Linear R where
  map_smul f r := by
    ext
    exact F.map_smul r f

end ObjectProperty

namespace Equivalence

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [Preadditive C] [Preadditive D] {R : Type w} [Semiring R] [Linear R C] [Linear R D]
  {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]

/-- The forward functor of an `R`-linear equivalence restricted to corresponding full
subcategories is `R`-linear. -/
instance congrFullSubcategory_functor_linear (e : C ≌ D) [e.functor.Linear R]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).functor.Linear R := by
  rw [congrFullSubcategory_functor]
  infer_instance

/-- The inverse functor of an `R`-linear equivalence restricted to corresponding full
subcategories is `R`-linear. -/
instance congrFullSubcategory_inverse_linear (e : C ≌ D) [e.inverse.Linear R]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).inverse.Linear R := by
  rw [congrFullSubcategory_inverse]
  infer_instance

end Equivalence

end CategoryTheory
