/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import TauCeti.Algebra.AddCircle
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Complex values of characters of finite fields and residue rings

Mathlib's `AddChar.FiniteField.primitiveChar_to_Complex` is the canonical primitive additive
character of a finite field `F` with values in `ℂ`, and
`AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive` records its primitivity. Its values are
roots of unity, hence algebraic integers, so `F` also has a primitive additive character with
values in the ring `integralClosure ℤ ℂ` of algebraic integers of `ℂ`; Gauss sums of characters of
residue fields of a number field can then be read in a domain containing its ring of integers.

A Legendre symbol `(θ/p) = ±1` is also an eighth root of unity, `e^{2πi · 2(1 - (θ/p))/8}`; this is
the form in which it enters the Gauss-sum invariants of finite quadratic modules, which take values
in `ℤ/8`. Likewise, at an odd integer `d`, the mod-`4` quadratic character `ZMod.χ₄ d = ±1` equals
`exp(π i (d - 1) / 2)`, allowing a factor of `χ₄ d` multiplying `exp(π i x / n)` to be absorbed into
the phase modulo `2 n`.

## Main results

* `TauCeti.exists_primitive_addChar_integralClosure`: `F` has a primitive additive character with
  values in the algebraic integers of `ℂ`.
* `TauCeti.legendreSym_eq_expCircle`: `(θ/p) = e^{2πi · 2(1 - (θ/p))/8}` for `θ` prime to `p`.
* `ZMod.χ₄_intCast_eq_exp_of_odd`,
  `ZMod.χ₄_intCast_mul_exp_pi_mul_I_mul_div_eq_of_odd_of_dvd`: for odd `d : ℤ`,
  `(χ₄ d : ℂ) = exp(π i (d - 1) / 2)`, so `(χ₄ d : ℂ) * exp(π i x / n) = exp(π i y / n)` when
  `n ≠ 0` and `4 n ∣ 2 (x - y) + n (d - 1)`.
-/

public section

namespace TauCeti

variable (F : Type*) [Field F] [Finite F]

/-- A finite field has a primitive additive character with values in the ring of algebraic
integers of `ℂ`: the values of `AddChar.FiniteField.primitiveChar_to_Complex` are roots of unity. -/
theorem exists_primitive_addChar_integralClosure :
    ∃ ψ : AddChar F (integralClosure ℤ ℂ), ψ.IsPrimitive := by
  let ψ₀ := AddChar.FiniteField.primitiveChar_to_Complex F
  refine ⟨{ toFun t := ⟨ψ₀ t, IsIntegral.of_pow Nat.card_pos <| by
              rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
              exact isIntegral_one⟩
            map_zero_eq_one' := Subtype.ext ψ₀.map_zero_eq_one
            map_add_eq_mul' a b := Subtype.ext (ψ₀.map_add_eq_mul a b) }, fun a ha h => ?_⟩
  exact AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F ha <|
    DFunLike.ext _ _ fun t => congrArg Subtype.val (DFunLike.congr_fun h t)

/-- A Legendre symbol `(θ/p) = ±1` is `e^{2πi · 2(1 - (θ/p))/8}`. -/
theorem legendreSym_eq_expCircle {p : ℕ} [Fact p.Prime] {θ : ℤ} (hθ : (θ : ZMod p) ≠ 0) :
    (legendreSym p θ : ℂ) =
      expCircle (ZMod.toRatAddCircle 8 ((2 * (1 - legendreSym p θ) : ℤ) : ZMod 8)) := by
  rcases legendreSym.eq_one_or_neg_one p hθ with h | h <;> rw [h]
  · simp
  · rw [ZMod.toRatAddCircle_intCast, show ((2 * (1 - -1) : ℤ) / (8 : ℕ) : ℚ) = 1 / 2 by norm_num,
      expCircle_one_div_two]
    simp

end TauCeti

namespace ZMod

open Complex Real

/-- For an odd integer `d`, the character value `χ₄ d = ±1` is `exp(π i (d - 1) / 2)`:
`(d - 1) / 2` is even when `d ≡ 1 (mod 4)` and odd when `d ≡ 3 (mod 4)`. The hypothesis `Odd d` is
needed: at `d = 0` the left side is `0` while the right side has norm `1`. -/
theorem χ₄_intCast_eq_exp_of_odd {d : ℤ} (hd : Odd d) :
    (χ₄ d : ℂ) = cexp (π * I * ((d - 1 : ℤ) : ℂ) / 2) := by
  have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by obtain ⟨k, hk⟩ := hd; omega
  rcases hd4 with hd1 | hd3
  · rw [χ₄_int_one_mod_four hd1, Int.cast_one]
    simpa using (Complex.exp_pi_mul_I_mul_div_eq_of_dvd (x := d - 1) (y := 0) (n := 2)
      ⟨d / 4, by omega⟩).symm
  · rw [χ₄_int_three_mod_four hd3, Int.cast_neg, Int.cast_one]
    simpa using (Complex.exp_pi_mul_I_mul_div_eq_neg_of_dvd (x := d - 1) (y := 0) (n := 2)
      (by norm_num) ⟨d / 4, by omega⟩).symm

/-- Absorbing an odd `χ₄ d` sign into a rational-multiple-of-`π i` exponential: for odd `d` and
`n ≠ 0`, `(χ₄ d : ℂ) * exp(π i x / n) = exp(π i y / n)` whenever `4 n ∣ 2 (x - y) + n (d - 1)`.
The hypothesis `n ≠ 0` is needed: at `x = y = n = 0` and `d = 3` the divisibility holds while
`-1 ≠ 1`. -/
theorem χ₄_intCast_mul_exp_pi_mul_I_mul_div_eq_of_odd_of_dvd {x y n d : ℤ} (hd : Odd d)
    (hn : n ≠ 0) (hdvd : 4 * n ∣ 2 * (x - y) + n * (d - 1)) :
    (χ₄ d : ℂ) * cexp (π * I * (x : ℂ) / n) = cexp (π * I * (y : ℂ) / n) := by
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have harg : π * I * ((d - 1 : ℤ) : ℂ) / 2 + π * I * (x : ℂ) / n =
      π * I * ((2 * x + n * (d - 1) : ℤ) : ℂ) / ((2 * n : ℤ) : ℂ) := by
    push_cast
    field_simp
    ring
  have hy : π * I * (y : ℂ) / n = π * I * ((2 * y : ℤ) : ℂ) / ((2 * n : ℤ) : ℂ) := by
    push_cast
    field_simp
  have hdvd' : 2 * (2 * n) ∣ (2 * x + n * (d - 1)) - 2 * y := by
    simpa [show 2 * (2 * n) = 4 * n by ring,
      show 2 * x + n * (d - 1) - 2 * y = 2 * (x - y) + n * (d - 1) by ring] using hdvd
  rw [χ₄_intCast_eq_exp_of_odd hd, ← Complex.exp_add, harg, hy]
  exact Complex.exp_pi_mul_I_mul_div_eq_of_dvd hdvd'

end ZMod
