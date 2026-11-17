/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The submonoid of regular elements

An element of a monoid is regular when multiplication by it, on either side, is injective. The
regular elements form the submonoid `TauCeti.regulars M`. Localizing a commutative semiring at
it gives its total quotient semiring.

Every regular element of a monoid with zero is a non-zero-divisor, and in a ring the two
notions agree (`TauCeti.regulars_eq_nonZeroDivisors`). In a semiring they can differ, which is
why localizations of semirings use regular elements. In a monoid with zero whose multiplication
cancels nonzero elements, the regular elements again coincide with the non-zero-divisors
(`TauCeti.regulars_eq_nonZeroDivisors_of_isCancelMulZero`), and when nontrivial they are exactly
the nonzero elements. Multiplicative equivalences preserve and reflect regularity
(`MulEquiv.isRegular_iff`) and carry `regulars` onto `regulars` (`TauCeti.map_regulars`).

The name follows the terminology proposed in Mathlib issue 22997, on non-zero-divisors, regular
elements and localization.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-- The submonoid of regular elements of a monoid: those `a` for which both `(a * ·)` and
`(· * a)` are injective. -/
def regulars (M : Type*) [Monoid M] : Submonoid M where
  carrier := {a | IsRegular a}
  one_mem' := isRegular_one
  mul_mem' ha hb := ha.mul hb

@[simp]
theorem mem_regulars {M : Type*} [Monoid M] {a : M} : a ∈ regulars M ↔ IsRegular a :=
  Iff.rfl

/-- In a ring the regular elements are exactly the non-zero-divisors. -/
theorem regulars_eq_nonZeroDivisors (R : Type*) [Ring R] : regulars R = R⁰ :=
  Submonoid.ext fun _ ↦ isRegular_iff_mem_nonZeroDivisors

/-- In a nontrivial monoid with zero whose multiplication cancels nonzero elements, the regular
elements are exactly the nonzero ones. -/
theorem mem_regulars_iff_ne_zero {M : Type*} [MonoidWithZero M] [IsCancelMulZero M] [Nontrivial M]
    {a : M} : a ∈ regulars M ↔ a ≠ 0 :=
  isRegular_iff_ne_zero

/-- In a monoid with zero whose multiplication cancels nonzero elements, the regular elements
coincide with the non-zero-divisors. -/
theorem regulars_eq_nonZeroDivisors_of_isCancelMulZero (M : Type*) [MonoidWithZero M]
    [IsCancelMulZero M] : regulars M = M⁰ := by
  ext a
  rcases subsingleton_or_nontrivial M with _ | _
  · exact ⟨fun _ ↦ mem_nonZeroDivisors_iff.mpr
      ⟨fun _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩,
      fun _ ↦ ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩⟩
  · rw [mem_regulars_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]

end TauCeti

namespace MulEquiv

/-- A multiplicative equivalence preserves and reflects regularity. -/
@[to_additive /-- An additive equivalence preserves and reflects additive regularity. -/]
theorem isRegular_iff {M N : Type*} [Mul M] [Mul N] (e : M ≃* N) {a : M} :
    IsRegular (e a) ↔ IsRegular a := by
  refine ⟨fun h ↦ ⟨fun x y hxy ↦ e.injective (h.left (by simpa [← map_mul] using congrArg e hxy)),
    fun x y hxy ↦ e.injective (h.right (by simpa [← map_mul] using congrArg e hxy))⟩,
    fun h ↦ ⟨fun x y hxy ↦ e.symm.injective (h.left (e.injective (by simpa [map_mul] using hxy))),
    fun x y hxy ↦ e.symm.injective (h.right (e.injective (by simpa [map_mul] using hxy)))⟩⟩

end MulEquiv

namespace TauCeti

/-- A multiplicative equivalence carries the submonoid of regular elements onto that of the
target. -/
@[simp]
theorem map_regulars {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) :
    (regulars M).map e = regulars N := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨e.symm y, e.isRegular_iff.mp (by simpa using hy), e.apply_symm_apply y⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact e.isRegular_iff.mpr hx

end TauCeti
