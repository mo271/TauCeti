/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
import TauCeti.Algebra.Lie.GeneralLinear.Basic

/-!
# Negative transpose on the special linear Lie algebra

Trace-zero matrices are stable under negative transpose. Restricting the matrix Lie automorphism
`TauCeti.negTransposeLieEquiv` to `LieAlgebra.SpecialLinear.sl n R` produces the involutive Lie
algebra automorphism `X ↦ -Xᵀ`, whose fixed and negated vectors are the skew-symmetric and
symmetric trace-zero matrices respectively.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1.
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]

/-- The involutive Lie algebra automorphism `X ↦ -Xᵀ` of `sl n R`. -/
def cartanInvolution : sl n R ≃ₗ⁅R⁆ sl n R :=
  (TauCeti.negTransposeLieEquiv n R).ofSubalgebras (sl n R) (sl n R) (by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      -- Subalgebra images use the underlying Lie homomorphism; expose its evaluation.
      change TauCeti.negTransposeLieEquiv n R Y ∈ sl n R
      simp [mem_sl_iff.mp hY]
    · intro hX
      refine ⟨-Xᵀ, ?_, by simp⟩
      simp [mem_sl_iff.mp hX])

variable {n R}

/-- The matrix value of `cartanInvolution n R` is negative transpose. -/
@[simp]
theorem coe_cartanInvolution (X : sl n R) :
    (cartanInvolution n R X : Matrix n n R) = -(X : Matrix n n R)ᵀ := by
  simp [cartanInvolution]

/-- Applying `cartanInvolution n R` twice returns the original element. -/
@[simp]
theorem cartanInvolution_cartanInvolution (X : sl n R) :
    cartanInvolution n R (cartanInvolution n R X) = X := by
  apply Subtype.ext
  simp

/-- `cartanInvolution n R` is involutive. -/
theorem involutive_cartanInvolution :
    Function.Involutive (cartanInvolution n R) :=
  cartanInvolution_cartanInvolution

/-- `cartanInvolution n R` is its own inverse. -/
@[simp]
theorem cartanInvolution_symm : (cartanInvolution n R).symm = cartanInvolution n R :=
  LieEquiv.ext fun X ↦ (cartanInvolution n R).symm_apply_eq.mpr
    (cartanInvolution_cartanInvolution X).symm

/-- Fixed vectors of `cartanInvolution n R` are the skew-symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_self_iff (X : sl n R) :
    cartanInvolution n R X = X ↔ (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_cartanInvolution, neg_eq_iff_eq_neg]

/-- Negated vectors of `cartanInvolution n R` are the symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_neg_iff (X : sl n R) :
    cartanInvolution n R X = -X ↔ (X : Matrix n n R)ᵀ = X := by
  rw [← Subtype.coe_inj, coe_cartanInvolution]
  exact neg_inj

end LieAlgebra.SpecialLinear
