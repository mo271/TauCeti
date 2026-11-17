/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Pointwise characterization of monoid-object homomorphisms

In a cartesian monoidal category, a morphism `f : M ⟶ N` between monoid objects is a monoid
homomorphism (`CategoryTheory.IsMonHom f`) if and only if postcomposition by `f` preserves the unit
and multiplication on `X`-points `X ⟶ M` for every object `X`. For group objects, preservation of
inverses then follows automatically from the group laws (`CategoryTheory.GrpObj.inv_comp`).

## Main declarations

* `TauCeti.CategoryTheory.isMonHom_iff_forall_comp`: a morphism between monoid objects in a
  cartesian monoidal category is a monoid homomorphism if and only if postcomposition preserves
  `1` and `*` on all generalized points.
-/

public section

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism `f : M ⟶ N` between monoid objects in a cartesian monoidal category is a monoid
homomorphism if and only if postcomposition by `f` preserves the unit and multiplication on
`X`-points `X ⟶ M` for every `X : C`. -/
@[to_additive
/-- A morphism `f : M ⟶ N` between additive monoid objects in a cartesian monoidal category is an
additive monoid homomorphism if and only if postcomposition by `f` preserves zero and addition on
`X`-points `X ⟶ M` for every `X : C`. -/]
theorem isMonHom_iff_forall_comp {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N) :
    IsMonHom f ↔
      (∀ (X : C), (1 : X ⟶ M) ≫ f = 1) ∧
      (∀ (X : C) (g₁ g₂ : X ⟶ M), (g₁ * g₂) ≫ f = g₁ ≫ f * g₂ ≫ f) := by
  refine ⟨fun _ ↦ ⟨fun _ ↦ MonObj.one_comp f, fun _ _ _ ↦ MonObj.mul_comp _ _ f⟩,
    fun ⟨hone, hmul⟩ ↦ ⟨?_, ?_⟩⟩
  · rw [MonObj.one_eq_one M, MonObj.one_eq_one N]
    exact hone (𝟙_ C)
  · rw [MonObj.mul_eq_mul M, hmul (M ⊗ M) (fst M M) (snd M M), Hom.mul_def]
    congr 1
    ext <;> simp

end TauCeti.CategoryTheory
