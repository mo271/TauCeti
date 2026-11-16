/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Ideal

/-!
# The Krull dimension of a power series ring

For a Noetherian ring `R`, the variable `X` is a non-zero-divisor in the Jacobson radical of
`R⟦X⟧` with quotient `R`, so the Krull dimension of the ring of formal power series is

```text
dim R⟦X⟧ = dim R + 1,
```

and by induction on a finite set of variables `σ`,

```text
dim MvPowerSeries σ R = dim R + Nat.card σ.
```

These are the power series analogues of Mathlib's `Polynomial.ringKrullDim_of_isNoetherianRing` and
`MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.

## Main results

* `PowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R`,
  `dim R⟦X⟧ = dim R + 1`.
* `MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`: for a Noetherian ring `R` and finite
  `σ`, `dim MvPowerSeries σ R = dim R + Nat.card σ`.
* `MvPowerSeries.ringKrullDim_eq_natCard_of_field`: for a field `k` and finite `σ`,
  `dim MvPowerSeries σ k = Nat.card σ`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- **The dimension of a power series ring.** Over a Noetherian ring `R`, adjoining a formal power
series variable raises the Krull dimension by exactly one. -/
theorem ringKrullDim_of_isNoetherianRing [IsNoetherianRing R] :
    ringKrullDim R⟦X⟧ = ringKrullDim R + 1 := by
  -- `X` is a non-zero-divisor in the Jacobson radical, so it cuts the dimension down by one, and
  -- the quotient by `X` is `R` through the constant coefficient
  have hX : IsRegular (X : R⟦X⟧) :=
    isRegular_iff_mem_nonZeroDivisors.mpr MvPowerSeries.X_mem_nonZeroDivisors
  have hJ : (X : R⟦X⟧) ∈ Ring.jacobson R⟦X⟧ :=
    Ring.mem_jacobson_iff.mpr fun _ ↦ isUnit_iff_constantCoeff.mpr (by simp)
  rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    hX.left.isSMulRegular hJ, ← ker_constantCoeff,
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)]

end PowerSeries

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-- **The dimension of a multivariate power series ring.** Over a Noetherian ring `R`, adjoining
finitely many formal power series variables raises the Krull dimension by the number of
variables. -/
@[simp]
theorem ringKrullDim_of_isNoetherianRing_of_finite {σ : Type*} [Finite σ] [IsNoetherianRing R] :
    ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + Nat.card σ := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert ← H using 1
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
    · rw [Nat.card_congr e]
  | h_empty =>
    rw [ringKrullDim_eq_of_ringEquiv (isEmptyEquiv _ R).toRingEquiv]
    simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    rw [ringKrullDim_eq_of_ringEquiv (optionEquivLeft _ _).toRingEquiv,
      PowerSeries.ringKrullDim_of_isNoetherianRing, IH]

/-- Over a field `k`, the formal power series ring in finitely many variables `σ` has Krull
dimension `Nat.card σ`. -/
theorem ringKrullDim_eq_natCard_of_field {k σ : Type*} [Field k] [Finite σ] :
    ringKrullDim (MvPowerSeries σ k) = Nat.card σ := by
  rw [ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add]

end MvPowerSeries
