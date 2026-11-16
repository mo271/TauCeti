/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Lie.Free
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding

/-!
# Embedding a free Lie algebra into the free associative algebra

The universal enveloping algebra of `FreeLieAlgebra R S` is canonically isomorphic to
`FreeAlgebra R S` (`FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra`), and hence to the word
algebra `MonoidAlgebra R (FreeMonoid S)` (`FreeAlgebra.equivMonoidAlgebraFreeMonoid`). Composing the
canonical map into the enveloping algebra with these equivalences gives Lie homomorphisms
`TauCeti.FreeLieAlgebra.toFreeAlgebra` and `TauCeti.FreeLieAlgebra.toMonoidAlgebra` sending each
free generator to the corresponding single-letter generator.

Whenever `FreeLieAlgebra R S` is free as an `R`-module — in particular over every field `R` —
Poincaré–Birkhoff–Witt (`TauCeti.UniversalEnvelopingAlgebra.ι_injective`) implies that both maps are
injective. Over any commutative ring `R`, every element in the image of `toMonoidAlgebra` has zero
constant term (`TauCeti.FreeLieAlgebra.coeff_toMonoidAlgebra_one`).

## Main definitions

* `TauCeti.FreeLieAlgebra.toFreeAlgebra`: the canonical Lie homomorphism
  `FreeLieAlgebra R S →ₗ⁅R⁆ FreeAlgebra R S`.
* `TauCeti.FreeLieAlgebra.toMonoidAlgebra`: the canonical Lie homomorphism
  `FreeLieAlgebra R S →ₗ⁅R⁆ MonoidAlgebra R (FreeMonoid S)`.

## Main results

* `TauCeti.FreeLieAlgebra.toFreeAlgebra_injective` and
  `TauCeti.FreeLieAlgebra.toMonoidAlgebra_injective`: injectivity when `FreeLieAlgebra R S` is free
  as an `R`-module.
* `TauCeti.FreeLieAlgebra.coeff_toMonoidAlgebra_one`: every element in the image of
  `toMonoidAlgebra` has zero coefficient at the empty word `1`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §2.2–2.3.
* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Theorem 1.2.
-/

public section

namespace TauCeti.FreeLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R] (S : Type*)

/-- The canonical Lie homomorphism from `FreeLieAlgebra R S` into `FreeAlgebra R S` sending each
generator `s` to `FreeAlgebra.ι R s`. -/
noncomputable def toFreeAlgebra : _root_.FreeLieAlgebra R S →ₗ⁅R⁆ FreeAlgebra R S :=
  _root_.FreeLieAlgebra.lift R (FreeAlgebra.ι R)

@[simp]
theorem toFreeAlgebra_of (s : S) :
    toFreeAlgebra R S (_root_.FreeLieAlgebra.of R s) = FreeAlgebra.ι R s :=
  _root_.FreeLieAlgebra.lift_of_apply _ s

/-- `toFreeAlgebra R S` factors as `UniversalEnvelopingAlgebra.ι R` followed by
`FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra`. -/
theorem toFreeAlgebra_eq_comp_ι :
    toFreeAlgebra R S =
      (_root_.FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R S).toAlgHom.toLieHom.comp
        (_root_.UniversalEnvelopingAlgebra.ι R) := by
  ext s
  simp [toFreeAlgebra]

/-- When `FreeLieAlgebra R S` is free as an `R`-module (in particular over every field), the
canonical Lie homomorphism into `FreeAlgebra R S` is injective. -/
theorem toFreeAlgebra_injective [Module.Free R (_root_.FreeLieAlgebra R S)] :
    Function.Injective (toFreeAlgebra R S) := by
  rw [toFreeAlgebra_eq_comp_ι, LieHom.coe_comp]
  exact (_root_.FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R S).injective.comp
    (UniversalEnvelopingAlgebra.ι_injective R (_root_.FreeLieAlgebra R S))

/-- The canonical Lie homomorphism from `FreeLieAlgebra R S` into the word algebra
`MonoidAlgebra R (FreeMonoid S)` sending each generator `s` to the single-letter word
`FreeMonoid.of s`. -/
noncomputable def toMonoidAlgebra :
    _root_.FreeLieAlgebra R S →ₗ⁅R⁆ MonoidAlgebra R (FreeMonoid S) :=
  _root_.FreeLieAlgebra.lift R fun s => MonoidAlgebra.of R (FreeMonoid S) (FreeMonoid.of s)

@[simp]
theorem toMonoidAlgebra_of (s : S) :
    toMonoidAlgebra R S (_root_.FreeLieAlgebra.of R s) =
      MonoidAlgebra.of R (FreeMonoid S) (FreeMonoid.of s) :=
  _root_.FreeLieAlgebra.lift_of_apply _ s

/-- `toMonoidAlgebra R S` is `toFreeAlgebra R S` followed by
`FreeAlgebra.equivMonoidAlgebraFreeMonoid`. -/
theorem toMonoidAlgebra_eq_comp_toFreeAlgebra :
    toMonoidAlgebra R S =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := S)).toAlgHom.toLieHom.comp
        (toFreeAlgebra R S) := by
  ext s
  simp [toMonoidAlgebra, FreeAlgebra.equivMonoidAlgebraFreeMonoid]

/-- When `FreeLieAlgebra R S` is free as an `R`-module (in particular over every field), the
canonical Lie homomorphism into `MonoidAlgebra R (FreeMonoid S)` is injective. -/
theorem toMonoidAlgebra_injective [Module.Free R (_root_.FreeLieAlgebra R S)] :
    Function.Injective (toMonoidAlgebra R S) := by
  rw [toMonoidAlgebra_eq_comp_toFreeAlgebra, LieHom.coe_comp]
  exact (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := S)).injective.comp
    (toFreeAlgebra_injective R S)

/-- Every element in the image of `toMonoidAlgebra R S` has zero coefficient at the empty word. -/
@[simp]
theorem coeff_toMonoidAlgebra_one (u : _root_.FreeLieAlgebra R S) :
    (toMonoidAlgebra R S u).coeff 1 = 0 := by
  let ε : MonoidAlgebra R (FreeMonoid S) →ₐ[R] R :=
    FreeAlgebra.algebraMapInv.comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := S)).symm.toAlgHom
  have hε_apply : ∀ p : MonoidAlgebra R (FreeMonoid S), ε p = p.coeff 1 := by
    let c₁ : MonoidAlgebra R (FreeMonoid S) →ₗ[R] R :=
      { toFun := fun p => p.coeff 1
        map_add' := fun _ _ => by simp
        map_smul' := fun _ _ => by simp }
    have hc₁ : ∀ p, c₁ p = p.coeff 1 := fun _ => rfl
    have hlhom : ε.toLinearMap = c₁ := by
      ext w
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MonoidAlgebra.lsingle_apply, hc₁]
      refine FreeMonoid.mulRecOn w ?_ fun s v _ => ?_
      · have h1 : MonoidAlgebra.single (1 : FreeMonoid S) (1 : R) = 1 := rfl
        simp [h1, ε, FreeAlgebra.algebraMapInv]
      · have hmul : MonoidAlgebra.single (FreeMonoid.of s * v) (1 : R) =
            FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι R s) *
              MonoidAlgebra.single v 1 := by
          simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply]
        have hne : (1 : FreeMonoid S) ≠ FreeMonoid.of s * v := by
          intro h
          have := congrArg FreeMonoid.toList h
          simp at this
        rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne, hmul]
        simp [ε, FreeAlgebra.algebraMapInv]
    exact fun p => LinearMap.congr_fun hlhom p
  have hcomp : ε.toLieHom.comp (toMonoidAlgebra R S) = 0 := by
    ext s
    have hsymm : (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := S)).symm
        (MonoidAlgebra.single (FreeMonoid.of s) 1) = FreeAlgebra.ι R s := by
      apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := S)).injective
      simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply]
    simp [ε, hsymm, FreeAlgebra.algebraMapInv]
  rw [← hε_apply]
  exact DFunLike.congr_fun hcomp u

end TauCeti.FreeLieAlgebra
