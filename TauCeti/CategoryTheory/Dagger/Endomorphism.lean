/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Linear.FullyFaithful

/-!
# Endomorphism star algebras and functorial star-algebra maps

On each object `X` of a dagger category, `CategoryTheory.End X` carries the star operation induced
by the dagger. This file relates `End.of` to `star`, unitary arrows, self-adjoint endomorphisms,
and star projections, upgrades `CategoryTheory.Functor.mapEndAlgHom` to a unital `⋆`-algebra
homomorphism `CategoryTheory.Functor.mapEndStarAlgHom` for additive `R`-linear dagger-preserving
functors over a commutative semiring `R`, and constructs the `⋆`-algebra equivalence
`CategoryTheory.Functor.endStarAlgEquiv` for full and faithful additive `R`-linear
dagger-preserving functors over any semiring `R`.
-/

public section

open CategoryTheory TauCeti

universe w v v' u u'

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {X : C}

/-- `End.of` commutes with the dagger involution and `star`. -/
@[simp, grind =] theorem of_dagger (f : X ⟶ X) : End.of (dagger f) = star (End.of f) := (rfl)

/-- An element of `End X` belongs to `unitary (End X)` precisely when its underlying arrow is
unitary. -/
theorem mem_unitary_iff (f : End X) : f ∈ unitary (End X) ↔ IsUnitary f.asHom := by
  simp [Unitary.mem_iff, End.ext_iff, isUnitary_iff]

/-- `End.of f` belongs to `unitary (End X)` precisely when `f` is unitary. -/
@[simp] theorem of_mem_unitary_iff (f : X ⟶ X) : End.of f ∈ unitary (End X) ↔ IsUnitary f :=
  mem_unitary_iff (End.of f)

/-- An element of `End X` is self-adjoint precisely when its underlying arrow equals its dagger. -/
theorem isSelfAdjoint_iff (f : End X) : IsSelfAdjoint f ↔ dagger f.asHom = f.asHom := by
  simp [IsSelfAdjoint, End.ext_iff]

/-- `End.of f` is self-adjoint precisely when `dagger f = f`. -/
@[simp] theorem isSelfAdjoint_of_iff (f : X ⟶ X) : IsSelfAdjoint (End.of f) ↔ dagger f = f :=
  isSelfAdjoint_iff (End.of f)

/-- An element of `End X` is a star projection precisely when its underlying arrow is idempotent
and self-adjoint. -/
theorem isStarProjection_iff (f : End X) :
    IsStarProjection f ↔ f.asHom ≫ f.asHom = f.asHom ∧ dagger f.asHom = f.asHom := by
  simp [_root_.isStarProjection_iff, IsIdempotentElem, isSelfAdjoint_iff, End.ext_iff]

/-- `End.of f` is a star projection precisely when `f` is idempotent and self-adjoint. -/
@[simp] theorem isStarProjection_of_iff (f : X ⟶ X) :
    IsStarProjection (End.of f) ↔ f ≫ f = f ∧ dagger f = f :=
  isStarProjection_iff (End.of f)

end CategoryTheory.End

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [DaggerCategory C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [DaggerCategory D]
variable (F : C ⥤ D) (R : Type w)

section CommSemiring

variable [CommSemiring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
variable [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- An additive `R`-linear dagger-preserving functor induces a unital `⋆`-algebra homomorphism on
endomorphism algebras, refining `CategoryTheory.Functor.mapEndAlgHom`. -/
def mapEndStarAlgHom (X : C) : End X →⋆ₐ[R] End (F.obj X) where
  __ := F.mapEndAlgHom R X
  map_star' f := by ext; simp

/-- `Functor.mapEndStarAlgHom` acts on underlying arrows by `F.map`. -/
@[simp] theorem mapEndStarAlgHom_asHom (X : C) (f : End X) :
    (F.mapEndStarAlgHom R X f).asHom = F.map f.asHom := by
  simp [mapEndStarAlgHom]

/-- `Functor.mapEndStarAlgHom` sends `End.of f` to `End.of (F.map f)`. -/
@[simp] theorem mapEndStarAlgHom_of (X : C) (f : X ⟶ X) :
    F.mapEndStarAlgHom R X (End.of f) = End.of (F.map f) := by
  ext
  simp

/-- Forgetting the star compatibility of `Functor.mapEndStarAlgHom` recovers
`Functor.mapEndAlgHom`. -/
@[simp] theorem mapEndStarAlgHom_toAlgHom (X : C) :
    (F.mapEndStarAlgHom R X).toAlgHom = F.mapEndAlgHom R X := by
  ext f : 1
  ext
  simp

/-- A faithful additive linear dagger-preserving functor embeds each endomorphism `⋆`-algebra. -/
theorem mapEndStarAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndStarAlgHom R X) := by
  simpa only [← F.mapEndStarAlgHom_toAlgHom R X, StarAlgHom.coe_toAlgHom] using
    F.mapEndAlgHom_injective R X

end CommSemiring

section Semiring

variable [Semiring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
variable [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- A full and faithful additive `R`-linear dagger-preserving functor induces a `⋆`-algebra
isomorphism on endomorphism algebras. -/
noncomputable def endStarAlgEquiv [F.Full] [F.Faithful] (X : C) :
    End X ≃⋆ₐ[R] End (F.obj X) where
  toEquiv := End.homEquiv.trans ((F.homLinearEquiv R X X).toEquiv.trans End.homEquiv.symm)
  map_mul' f g := by ext; simp
  map_add' f g := by ext; simp
  map_smul' r f := by ext; simp
  map_star' f := by ext; simp

/-- Forward evaluation of `Functor.endStarAlgEquiv` on underlying arrows. -/
@[simp] theorem endStarAlgEquiv_asHom [F.Full] [F.Faithful] (X : C) (f : End X) :
    (F.endStarAlgEquiv R X f).asHom = F.map f.asHom := by
  simp [endStarAlgEquiv]

/-- Forward evaluation of `Functor.endStarAlgEquiv` on `End.of`. -/
@[simp] theorem endStarAlgEquiv_of [F.Full] [F.Faithful] (X : C) (f : X ⟶ X) :
    F.endStarAlgEquiv R X (End.of f) = End.of (F.map f) := by
  ext
  simp

/-- Inverse evaluation of `Functor.endStarAlgEquiv` on underlying arrows. -/
@[simp] theorem endStarAlgEquiv_symm_asHom [F.Full] [F.Faithful] (X : C) (g : End (F.obj X)) :
    ((F.endStarAlgEquiv R X).symm g).asHom = F.preimage g.asHom := by
  simp [endStarAlgEquiv]

/-- Inverse evaluation of `Functor.endStarAlgEquiv` on `End.of`. -/
@[simp] theorem endStarAlgEquiv_symm_of [F.Full] [F.Faithful] (X : C) (g : F.obj X ⟶ F.obj X) :
    (F.endStarAlgEquiv R X).symm (End.of g) = End.of (F.preimage g) := by
  ext
  simp

end Semiring

end CategoryTheory.Functor
