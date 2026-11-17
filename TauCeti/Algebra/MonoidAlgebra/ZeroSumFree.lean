/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import TauCeti.Algebra.Group.Finsupp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Additive units and zero-sum-free evaluation of monoid algebras

A monoid algebra is additively its coefficient function, by the additive equivalence
`MonoidAlgebra.coeffAddEquiv`. It therefore has trivial additive units whenever its coefficient
semiring does; for commutative coefficient semirings this says that a sum in the monoid algebra
vanishes only when every summand does. The same holds for additive monoid algebras, and so for
multivariate polynomials `MvPolynomial σ R = AddMonoidAlgebra R (σ →₀ ℕ)`.

Consequently, evaluating a monoid algebra into a zero-sum-free semiring via `MonoidAlgebra.liftNC`
involves no cancellation: the value vanishes only on zero as soon as every nonzero monomial maps
to a nonzero element (`MonoidAlgebra.liftNC_eq_zero_iff`, `AddMonoidAlgebra.liftNC_eq_zero_iff`).
-/

public section

namespace TauCeti

/-- Monoid algebras over coefficients with trivial additive units have trivial additive units. -/
@[to_additive instSubsingletonAddUnitsAddMonoidAlgebra
  /-- Additive monoid algebras over coefficients with trivial additive units have
trivial additive units. -/]
instance instSubsingletonAddUnitsMonoidAlgebra {R M : Type*} [Semiring R]
    [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (MonoidAlgebra R M)) :=
  (AddUnits.map_injective (f := MonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
    MonoidAlgebra.coeff_injective).subsingleton

end TauCeti

namespace MonoidAlgebra

/-- Evaluating a monoid algebra into a zero-sum-free semiring vanishes only on zero when every
nonzero monomial evaluates to a nonzero element. -/
theorem liftNC_eq_zero_iff {R S M : Type*} [Semiring R] [NonUnitalNonAssocSemiring S]
    [Subsingleton (AddUnits S)] {f : R →+ S} {g : M → S}
    (hfg : ∀ m r, f r * g m = 0 → r = 0) {x : MonoidAlgebra R M} :
    liftNC f g x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← coeff_inj, coeff_zero, ← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  have hsum : ∑ m ∈ x.coeff.support, f (x.coeff m) * g m = 0 := by
    simpa [liftNC, Finsupp.liftAddHom_apply, Finsupp.sum] using h
  rw [Finset.sum_eq_zero_iff] at hsum
  exact fun m hm ↦ Finsupp.mem_support_iff.mp hm (hfg m (x.coeff m) (hsum m hm))

end MonoidAlgebra

namespace AddMonoidAlgebra

/-- Evaluating an additive monoid algebra into a zero-sum-free semiring vanishes only on zero when
every nonzero monomial evaluates to a nonzero element. -/
theorem liftNC_eq_zero_iff {R S M : Type*} [Semiring R] [NonUnitalNonAssocSemiring S]
    [Subsingleton (AddUnits S)] {f : R →+ S} {g : Multiplicative M → S}
    (hfg : ∀ m r, f r * g (Multiplicative.ofAdd m) = 0 → r = 0) {x : AddMonoidAlgebra R M} :
    liftNC f g x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← coeff_inj, coeff_zero, ← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  have hsum : ∑ m ∈ x.coeff.support, f (x.coeff m) * g (Multiplicative.ofAdd m) = 0 := by
    simpa [liftNC, Finsupp.liftAddHom_apply, Finsupp.sum] using h
  rw [Finset.sum_eq_zero_iff] at hsum
  exact fun m hm ↦ Finsupp.mem_support_iff.mp hm (hfg m (x.coeff m) (hsum m hm))

end AddMonoidAlgebra
