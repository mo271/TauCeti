/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.HopfModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Frobenius
public import TauCeti.Algebra.HopfAlgebra.Frobenius
import Mathlib.RingTheory.Finiteness.Small

/-!
# All modules over a finite-dimensional Hopf algebra form a Frobenius category

Let `H` be a finite-dimensional Hopf algebra over a field `k`. By the Larson–Sweedler theorem
(`TauCeti.HopfAlgebra.exists_isFrobeniusFunctional`), `H` admits a Frobenius functional. Combining
this with `ModuleCat.abelian_isFrobenius` shows unconditionally that the canonical exact structure
on the abelian category of **all** left `H`-modules — not only finite-dimensional ones — is a
Frobenius exact structure: projective and injective objects coincide, and there are enough of both.
Its `ProjectiveStableCategory` is therefore triangulated by
`TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`.

We state the result both for `ModuleCat.{w} H` in any universe `w` in which `H` is small and for
`TauCeti.HopfModuleCat k H`, whose carriers live in the universe of `k` so smallness of `H` holds
automatically by `Module.Finite.small`.

## Main results

* `ModuleCat.projective_iff_injective_of_hopfAlgebra` and
  `ModuleCat.abelian_isFrobenius_of_hopfAlgebra`: projective and injective objects of
  `ModuleCat.{w} H` coincide and its canonical abelian exact structure is Frobenius.
* `TauCeti.HopfModuleCat.projective_iff_injective` and
  `TauCeti.HopfModuleCat.abelian_isFrobenius`: the corresponding statements on `HopfModuleCat k H`,
  with no auxiliary `Small` hypothesis.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications **25** (2016), Proposition 1.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. **91** (1969), 75–94.
-/

public noncomputable section

open CategoryTheory TauCeti

namespace ModuleCat

universe w

variable (k : Type*) [Field k]

include k in
/-- **Projective and injective modules over a finite-dimensional Hopf algebra coincide.** Any
object of `ModuleCat.{w} H`, not necessarily finitely generated, is projective if and only if it is
injective. -/
theorem projective_iff_injective_of_hopfAlgebra {H : Type*} [Ring H] [HopfAlgebra k H]
    [FiniteDimensional k H] [Small.{w} H] (X : ModuleCat.{w} H) :
    Projective X ↔ Injective X := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact projective_iff_injective_of_isFrobeniusFunctional hφ X

include k in
/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category.** The canonical
exact structure on `ModuleCat.{w} H` is Frobenius. -/
theorem abelian_isFrobenius_of_hopfAlgebra (H : Type*) [Ring H] [HopfAlgebra k H]
    [FiniteDimensional k H] [Small.{w} H] :
    (ExactStructure.abelian (ModuleCat.{w} H)).IsFrobenius := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact abelian_isFrobenius hφ

end ModuleCat

namespace TauCeti.HopfModuleCat

universe u v

instance (k : Type u) (H : Type v) [Ring H] [Small.{u} H] :
    EnoughProjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughProjectives (ModuleCat.{u} H))

instance (k : Type u) (H : Type v) [Ring H] [Small.{u} H] :
    EnoughInjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughInjectives (ModuleCat.{u} H))

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- Over a finite-dimensional Hopf algebra `H` over `k`, an object of `HopfModuleCat k H` is
projective if and only if it is injective. -/
theorem projective_iff_injective (X : HopfModuleCat k H) : Projective X ↔ Injective X := by
  have : Small.{u} H := Module.Finite.small k H
  exact ModuleCat.projective_iff_injective_of_hopfAlgebra k (X : ModuleCat.{u} H)

variable (k H) in
/-- **All left modules over a finite-dimensional Hopf algebra form a Frobenius category.** On
`HopfModuleCat k H`, the canonical abelian exact structure is Frobenius without any auxiliary
`Small` hypothesis. -/
theorem abelian_isFrobenius :
    (ExactStructure.abelian (HopfModuleCat k H)).IsFrobenius := by
  have : Small.{u} H := Module.Finite.small k H
  exact ModuleCat.abelian_isFrobenius_of_hopfAlgebra k H

end TauCeti.HopfModuleCat
