/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum

/-!
# Quasiregularity and quasispectra in opposite rings

Quasiregularity is defined by the two-sided equations `y + x + x * y = 0` and `x + y + y * x = 0`,
which passing to the multiplicative opposite swaps. Consequently `MulOpposite.op` and
`MulOpposite.unop` preserve quasiregularity and leave the quasispectrum of every element unchanged.

## Main declarations

* `MulOpposite.isQuasiregular_op`, `MulOpposite.isQuasiregular_unop`: quasiregularity in `Rᵐᵒᵖ`
  agrees with quasiregularity in `R`.
* `MulOpposite.quasispectrum_op`, `MulOpposite.quasispectrum_unop`: the quasispectrum of an
  element in `Aᵐᵒᵖ` agrees with its quasispectrum in `A`.
-/

public section

namespace MulOpposite

/-- An element of the opposite non-unital semiring `Rᵐᵒᵖ` is quasiregular if and only if it is
quasiregular in `R`. -/
@[simp]
theorem isQuasiregular_op {R : Type*} [NonUnitalSemiring R] {x : R} :
    IsQuasiregular (op x) ↔ IsQuasiregular x := by
  simp only [isQuasiregular_iff, MulOpposite.exists, ← op_add, ← op_mul, op_eq_zero_iff, add_comm]
  exact exists_congr fun _ ↦ and_comm

/-- Unwrapping from `Rᵐᵒᵖ` to `R` preserves quasiregularity. -/
@[simp]
theorem isQuasiregular_unop {R : Type*} [NonUnitalSemiring R] {x : Rᵐᵒᵖ} :
    IsQuasiregular (unop x) ↔ IsQuasiregular x := by
  rw [← isQuasiregular_op, op_unop]

/-- Passing to the opposite algebra leaves the quasispectrum unchanged. -/
@[simp]
theorem quasispectrum_op (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
    (a : A) : quasispectrum R (op a) = quasispectrum R a := by
  ext r
  simp [quasispectrum, ← op_smul, ← op_neg, isQuasiregular_op]

/-- Unwrapping from the opposite algebra leaves the quasispectrum unchanged. -/
@[simp]
theorem quasispectrum_unop (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
    (a : Aᵐᵒᵖ) : quasispectrum R (unop a) = quasispectrum R a := by
  rw [← quasispectrum_op R (unop a), op_unop]

end MulOpposite
