/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import TauCeti.RingTheory.Perfect.Basic
import TauCeti.RingTheory.WittVector.Primitive.Torsion

/-!
# Checks for bounded `p`-torsion in principal Witt-vector quotients

* Over any perfect ring `S` of characteristic `p` (for instance `𝔽_p × 𝔽_p`), the distinguished
  element `ξ = p` yields `W(S) ⧸ (p)` with all `p`-power torsion killed by `p`.
* Over the non-domain `𝔽_p × 𝔽_p`, the distinguished element `ξ = [(1, 0)] + p` has a
  zero-divisor, non-nilpotent zeroth coordinate, yet `ξ` is a nonzerodivisor in `W(𝔽_p × 𝔽_p)`
  and every `p`-power torsion element of `W(𝔽_p × 𝔽_p) ⧸ (ξ)` is annihilated by `p`.
* Over the non-perfect reduced ring `𝔽_p[X]`, `ξ = [X] + p` is distinguished and a nonzerodivisor
  in `W(𝔽_p[X])`.
* Counterexample without distinguishedness: in `W(𝔽_p) ⧸ (p ^ 2)` (and in particular
  `W(𝔽₂) ⧸ (4)`), `p ^ 2` is not distinguished and the class of `1` satisfies `p ^ 2 * 1 = 0`
  while `p * 1 ≠ 0`.
-/

open Ideal WittVector
open scoped nonZeroDivisors

namespace TauCeti.Examples

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Distinguished quotients -/

-- For `ξ = p` over a perfect ring of characteristic `p`, `p ^ n * x = 0 → p * x = 0`.
example {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p] (n : ℕ)
    (x : WittVector p S ⧸ span {(p : WittVector p S)})
    (hx : (p : WittVector p S ⧸ span {(p : WittVector p S)}) ^ n * x = 0) :
    (p : WittVector p S ⧸ span {(p : WittVector p S)}) * x = 0 :=
  isDistinguished_p.p_mul_eq_zero_of_pow_mul_eq_zero n hx

-- Non-domain case with a zero-divisor, non-nilpotent zeroth coordinate:
-- `ξ = [(1, 0)] + p` in `W(𝔽_p × 𝔽_p)` is distinguished, is a nonzerodivisor, and gives
-- bound-one `p`-torsion in `W(𝔽_p × 𝔽_p) ⧸ (ξ)`.
example :
    let ξ : WittVector p (ZMod p × ZMod p) :=
      teichmuller p ((1 : ZMod p), (0 : ZMod p)) + (p : WittVector p (ZMod p × ZMod p))
    ξ.IsDistinguished ∧ ξ ∈ (WittVector p (ZMod p × ZMod p))⁰ ∧
      ∀ (n : ℕ) (x : WittVector p (ZMod p × ZMod p) ⧸ span {ξ}),
        (p : WittVector p (ZMod p × ZMod p) ⧸ span {ξ}) ^ n * x = 0 →
        (p : WittVector p (ZMod p × ZMod p) ⧸ span {ξ}) * x = 0 := by
  intro ξ
  have : CharP (ZMod p × ZMod p) p := Prod.charP _ _ p
  have hξ : ξ.IsDistinguished := by
    have h1 : (teichmuller p ((1 : ZMod p), (0 : ZMod p)) +
        (p : WittVector p (ZMod p × ZMod p)) * 1).IsDistinguished := by
      rw [isDistinguished_teichmuller_add_p_mul_iff, one_coeff_zero]
      exact isUnit_one
    simpa only [mul_one] using h1
  exact ⟨hξ, hξ.mem_nonZeroDivisors, fun n _ hx ↦ hξ.p_mul_eq_zero_of_pow_mul_eq_zero n hx⟩

-- Non-perfect reduced ring case: `ξ = [X] + p` is a nonzerodivisor in `W(𝔽_p[X])`.
example :
    teichmuller p (Polynomial.X : Polynomial (ZMod p)) + (p : WittVector p (Polynomial (ZMod p))) ∈
      (WittVector p (Polynomial (ZMod p)))⁰ := by
  have h1 : (teichmuller p (Polynomial.X : Polynomial (ZMod p)) +
      (p : WittVector p (Polynomial (ZMod p))) * 1).IsDistinguished := by
    rw [isDistinguished_teichmuller_add_p_mul_iff, one_coeff_zero]
    exact isUnit_one
  exact (by simpa only [mul_one] using h1 : IsDistinguished _).mem_nonZeroDivisors

/-! ### Counterexample without distinguishedness -/

-- In `W(𝔽_p) ⧸ (p ^ 2)`, the generator `p ^ 2` is not distinguished, and `1` is `p ^ 2`-torsion
-- without being `p`-torsion.
example :
    let ξ : WittVector p (ZMod p) := (p : WittVector p (ZMod p)) ^ 2
    ¬ ξ.IsDistinguished ∧
      (p : WittVector p (ZMod p) ⧸ span {ξ}) ^ 2 * 1 = 0 ∧
      (p : WittVector p (ZMod p) ⧸ span {ξ}) * 1 ≠ 0 := by
  intro ξ
  refine ⟨not_isDistinguished_of_mem_span_p_sq (mem_span_singleton_self ξ), ?_, ?_⟩
  · rw [mul_one, ← map_natCast (Ideal.Quotient.mk (span {ξ})), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact mem_span_singleton_self ξ
  · intro h
    rw [mul_one, ← map_natCast (Ideal.Quotient.mk (span {ξ})),
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact not_isDistinguished_of_mem_span_p_sq h isDistinguished_p

-- Specialising to `p = 2`: in `W(𝔽₂) ⧸ (4)`, `2 ^ 2 * 1 = 0` but `2 * 1 ≠ 0`.
example :
    let ξ : WittVector 2 (ZMod 2) := (4 : WittVector 2 (ZMod 2))
    ¬ ξ.IsDistinguished ∧
      (2 : WittVector 2 (ZMod 2) ⧸ span {ξ}) ^ 2 * 1 = 0 ∧
      (2 : WittVector 2 (ZMod 2) ⧸ span {ξ}) * 1 ≠ 0 := by
  intro ξ
  have hξ : ξ = ((2 : ℕ) : WittVector 2 (ZMod 2)) ^ 2 := by norm_num [ξ]
  refine ⟨not_isDistinguished_of_mem_span_p_sq (hξ ▸ mem_span_singleton_self _), ?_, ?_⟩
  · rw [mul_one, ← map_ofNat (Ideal.Quotient.mk (span {ξ})) 2, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    simp [hξ]
  · intro h
    rw [mul_one, ← map_ofNat (Ideal.Quotient.mk (span {ξ})) 2,
      Ideal.Quotient.eq_zero_iff_mem, hξ] at h
    have h' : ((2 : ℕ) : WittVector 2 (ZMod 2)) ∈ span {((2 : ℕ) : WittVector 2 (ZMod 2)) ^ 2} := by
      simpa only [Nat.cast_ofNat] using h
    exact not_isDistinguished_of_mem_span_p_sq h' isDistinguished_p

end TauCeti.Examples
