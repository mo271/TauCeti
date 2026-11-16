/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Linear structure on the single-object category of an algebra

Mathlib equips `CategoryTheory.SingleObj A` with a category structure for a monoid `A` (with
composition given by reversed multiplication so that `End (SingleObj.star A)` agrees with `A`) and
a preadditive structure when `A` is a ring (`Mathlib/CategoryTheory/Preadditive/SingleObj.lean`).

This file equips `SingleObj A` with its `R`-linear structure whenever `A` is a ring carrying a
compatible `R`-module structure (`SMulCommClass R A A` and `IsScalarTower R A A`, in particular for
any `R`-algebra `A`), upgrades `SingleObj.toEnd` to a ring isomorphism
`SingleObj.toEndRingEquiv : A ≃+* End (SingleObj.star A)` and an `R`-algebra isomorphism
`SingleObj.toEndAlgEquiv : A ≃ₐ[R] End (SingleObj.star A)`, and records additivity of functors
induced by ring homomorphisms.

## Main declarations

* `CategoryTheory.SingleObj.instLinear` and `CategoryTheory.SingleObj.instModuleFiniteHom`:
  `SingleObj A` is `R`-linear, with `R`-module-finite Hom spaces when `A` is `R`-module-finite.
* `CategoryTheory.SingleObj.toEndRingEquiv`: `A ≃+* End (SingleObj.star A)` for a ring `A`.
* `CategoryTheory.SingleObj.toEndAlgEquiv`: `A ≃ₐ[R] End (SingleObj.star A)` for an `R`-algebra
  `A`.
* `CategoryTheory.SingleObj.mapHom_additive` and `CategoryTheory.SingleObj.mapHom_linear`:
  `SingleObj.mapHom` is additive for a ring homomorphism and `R`-linear for an `R`-algebra
  homomorphism.
* `CategoryTheory.SingleObj.instNontrivialEnd` and `CategoryTheory.SingleObj.isUnit_end_of_ne_zero`:
  endomorphism nontriviality for `[Nontrivial A]` and invertibility of nonzero endomorphisms for a
  division ring `D`.
-/

public section

namespace CategoryTheory.SingleObj

universe w u v

section Ring

variable (A : Type u) [Ring A]

/-- For a ring `A`, the endomorphism ring of the unique object of `SingleObj A` is isomorphic to
`A`. -/
def toEndRingEquiv : A ≃+* End (SingleObj.star A) where
  __ := toEnd A
  map_add' _ _ := rfl

@[simp]
theorem toEndRingEquiv_apply (a : A) : toEndRingEquiv A a = End.of a :=
  (rfl)

@[simp]
theorem toEndRingEquiv_symm_apply (f : End (SingleObj.star A)) :
    (toEndRingEquiv A).symm f = f.asHom :=
  (rfl)

@[simp]
theorem coe_toEndRingEquiv : (toEndRingEquiv A : A ≃* End (SingleObj.star A)) = toEnd A :=
  (rfl)

theorem toEndRingEquiv_toMulEquiv : (toEndRingEquiv A).toMulEquiv = toEnd A :=
  (rfl)

/-- A ring homomorphism induces an additive functor between single-object categories. -/
instance mapHom_additive {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B) :
    (mapHom A B f.toMonoidHom).Additive where
  map_add := f.map_add _ _

/-- If `A` is a nontrivial monoid, every endomorphism monoid in `SingleObj A` is nontrivial. -/
instance instNontrivialEnd {A : Type u} [Monoid A] [Nontrivial A] (x : SingleObj A) :
    Nontrivial (End x) := by
  obtain rfl : x = SingleObj.star A := Subsingleton.elim _ _
  exact (toEnd A).symm.toEquiv.nontrivial

/-- In `SingleObj D` for a division ring `D`, every nonzero endomorphism is a unit. -/
theorem isUnit_end_of_ne_zero {D : Type u} [DivisionRing D] {x : SingleObj D}
    {f : End x} (hf : f ≠ 0) : IsUnit f := by
  obtain rfl : x = SingleObj.star D := Subsingleton.elim _ _
  have hne : (toEndRingEquiv D).symm f ≠ 0 :=
    (map_ne_zero_iff (toEndRingEquiv D).symm (RingEquiv.injective _)).mpr hf
  simpa using (isUnit_iff_ne_zero.mpr hne).map (toEndRingEquiv D).toMonoidHom

end Ring

section Linear

variable (R : Type w) [Semiring R] (A : Type u) [Ring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- The single-object category of a ring `A` with a compatible `R`-action is `R`-linear. -/
instance instLinear : Linear R (SingleObj A) where
  homModule _ _ := inferInstanceAs (Module R A)
  smul_comp _ _ _ r f g := mul_smul_comm r g f
  comp_smul _ _ _ f r g := smul_mul_assoc r g f

omit [SMulCommClass R A A] [IsScalarTower R A A] in
/-- If `A` is finite as an `R`-module, every Hom module in `SingleObj A` is finite over `R`. -/
instance instModuleFiniteHom [Module.Finite R A] (X Y : SingleObj A) :
    Module.Finite R (X ⟶ Y) :=
  inferInstanceAs (Module.Finite R A)

end Linear

section Algebra

variable (R : Type w) [CommSemiring R] (A : Type u) [Ring A] [Algebra R A]

/-- For an `R`-algebra `A`, the endomorphism algebra of the unique object of `SingleObj A` is
isomorphic to `A`. -/
def toEndAlgEquiv : A ≃ₐ[R] End (SingleObj.star A) where
  __ := toEndRingEquiv A
  commutes' r := End.ext <| by simp [Algebra.algebraMap_eq_smul_one, id_as_one]

@[simp]
theorem toEndAlgEquiv_apply (a : A) : toEndAlgEquiv R A a = End.of a :=
  (rfl)

@[simp]
theorem toEndAlgEquiv_symm_apply (f : End (SingleObj.star A)) :
    (toEndAlgEquiv R A).symm f = f.asHom :=
  (rfl)

@[simp]
theorem toEndAlgEquiv_toRingEquiv : (toEndAlgEquiv R A).toRingEquiv = toEndRingEquiv A :=
  (rfl)

/-- An `R`-algebra homomorphism induces an `R`-linear functor between single-object categories. -/
instance mapHom_linear {A : Type u} {B : Type v} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : (mapHom A B f.toRingHom.toMonoidHom).Linear R where
  map_smul _ _ := _root_.map_smul f _ _

end Algebra

end CategoryTheory.SingleObj
