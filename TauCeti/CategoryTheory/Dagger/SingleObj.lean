/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.SingleObj

/-!
# Dagger structure on single-object categories

A star monoid `M` makes `CategoryTheory.SingleObj M` a dagger category in which categorical
composition is opposite to multiplication (`f ≫ g = g * f`), so `dagger` is `star` and
`End (SingleObj.star M)` recovers `M` with its original multiplication and star. When `A` is a
star ring (or a ring with `StarMul` and a central `R`-module action), `SingleObj A` inherits
`DaggerPreadditive`, `DaggerLinear`, and the canonical `⋆`-algebra isomorphism
`SingleObj.toEndStarAlgEquiv`.
-/

public section

open CategoryTheory TauCeti

universe w u v

namespace CategoryTheory.SingleObj

instance instDaggerCategory (M : Type u) [Monoid M] [StarMul M] :
    DaggerCategory (SingleObj M) where
  dagger f := Star.star f
  dagger_id _ := star_one M
  dagger_comp f g := star_mul g f
  dagger_dagger := star_star

/-- In `SingleObj M`, the categorical dagger is the monoid `star`. -/
theorem dagger_as_star {M : Type u} [Monoid M] [StarMul M] {X Y : SingleObj M} (f : X ⟶ Y) :
    dagger f = Star.star f := (rfl)

/-- Unitary arrows in `SingleObj M` are precisely elements of `unitary M`. -/
theorem isUnitary_iff_mem_unitary {M : Type u} [Monoid M] [StarMul M] {X Y : SingleObj M}
    (f : X ⟶ Y) : IsUnitary f ↔ (f : M) ∈ unitary M :=
  (isUnitary_iff f).trans (Unitary.mem_iff (U := (f : M))).symm

instance instDaggerPreadditive (A : Type u) [Ring A] [StarRing A] :
    DaggerPreadditive (SingleObj A) where
  dagger_add := star_add

instance instDaggerLinear (R : Type w) (A : Type u) [Semiring R] [Star R] [Ring A] [StarMul A]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A] :
    DaggerLinear R (SingleObj A) where
  dagger_smul := star_smul

/-- The endomorphism `⋆`-algebra of the unique object of `SingleObj A` is canonically isomorphic
to `A`. -/
def toEndStarAlgEquiv (R : Type w) (A : Type u) [Semiring R] [Ring A] [StarMul A]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] :
    A ≃⋆ₐ[R] End (SingleObj.star A) where
  __ := SingleObj.toEnd A
  map_add' _ _ := by ext; simp [toEnd_def]
  map_smul' _ _ := by ext; simp [toEnd_def]
  map_star' _ := by ext; simp [toEnd_def, dagger_as_star]

/-- Forward evaluation of `SingleObj.toEndStarAlgEquiv`. -/
@[simp] theorem toEndStarAlgEquiv_apply {R : Type w} {A : Type u} [Semiring R] [Ring A]
    [StarMul A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (a : A) :
    toEndStarAlgEquiv R A a = .of a := (rfl)

/-- Inverse evaluation of `SingleObj.toEndStarAlgEquiv`. -/
@[simp] theorem toEndStarAlgEquiv_symm_apply {R : Type w} {A : Type u} [Semiring R] [Ring A]
    [StarMul A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (f : End (SingleObj.star A)) : (toEndStarAlgEquiv R A).symm f = f.asHom := (rfl)

/-- Over a commutative base semiring, forgetting `star` from `SingleObj.toEndStarAlgEquiv` recovers
`SingleObj.toEndAlgEquiv`. -/
@[simp] theorem toEndStarAlgEquiv_toAlgEquiv (R : Type w) (A : Type u) [CommSemiring R] [Ring A]
    [StarMul A] [Algebra R A] :
    (toEndStarAlgEquiv R A).toAlgEquiv = toEndAlgEquiv R A := by
  ext
  simp

/-- A monoid homomorphism commuting with `star` induces a dagger-preserving functor between
single-object categories. -/
theorem preservesDagger_mapHom {M : Type u} {N : Type v} [Monoid M] [StarMul M] [Monoid N]
    [StarMul N] (φ : M →* N) (hφ : ∀ x, φ (Star.star x) = Star.star (φ x)) :
    (SingleObj.mapHom M N φ).PreservesDagger where
  map_dagger := hφ

end CategoryTheory.SingleObj
