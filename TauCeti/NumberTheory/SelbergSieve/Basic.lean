/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve

/-!
# Weighted divisibility identities, Legendre's identity, and local sieve bounds

For a `BoundingSieve` `s` with squarefree prime product `P = s.prodPrimes`, arbitrary real divisor
coefficients `c : ℕ → ℝ` satisfy the weighted divisibility interchange
`∑ d ∈ P.divisors, c d * s.multSum d =`
`∑ n ∈ s.support, s.weights n * ∑ d ∈ (gcd P n).divisors, c d`.

Specializing `c` to the Möbius function gives the exact Legendre sieve identity, its factored Euler
main term with signed remainder, and the triangle-inequality error bound. Pointwise inequalities
comparing `∑ d ∈ r.divisors, c d` with the unit indicator `if r = 1 then 1 else 0` on divisors
`r ∣ P` yield lower and upper bounds for `s.siftedSum` in terms of `s.mainSum` and `s.errSum`,
without requiring the divisor inequality outside divisors of `P` (where lower-sieve coefficients
supported on `P.divisors` typically have divisor sum `1` rather than `0`). We also record the
cutoff error estimate on `d ≤ D` and the first Bonferroni lower bound.

## Main results

* `BoundingSieve.sum_divisors_prodPrimes_mul_multSum`: weighted divisibility interchange for
  arbitrary signed divisor coefficients.
* `BoundingSieve.siftedSum_eq_sum_moebius_mul_multSum`: exact Legendre inclusion-exclusion identity.
* `BoundingSieve.siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem` and
  `BoundingSieve.abs_siftedSum_sub_totalMass_mul_prod_le_sum_abs_rem`: Euler-product main term with
  signed remainder and absolute remainder bound.
* `BoundingSieve.sum_mul_multSum_le_siftedSum_of_dvd_prodPrimes` and
  `BoundingSieve.totalMass_mul_mainSum_sub_errSum_le_siftedSum_of_dvd_prodPrimes`: local lower
  sieve bounds assuming the Möbius bracket only on divisors `r ∣ s.prodPrimes` (complementing
  Mathlib's `BoundingSieve.siftedSum_le_sum_of_upperMoebius` and
  `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`).
* `BoundingSieve.errSum_le_mul_sum_filter_le_abs_rem`: integer-cutoff bound on `s.errSum`.
* `BoundingSieve.multSum_one_sub_sum_primeFactors_le_siftedSum`: first Bonferroni lower bound.

## References

* D. R. Heath-Brown (notes by Boris Moroz), *Lectures on sieves*, arXiv:math/0209360v1 (2002),
  Section 1, equations (1.1)–(1.8) and Corollary 1.1.
* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 11: "Revisiting the sieve of
  Eratosthenes", Section 11.2, Lemma 11.1.
-/

public noncomputable section

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace BoundingSieve

/-- Weighted divisibility interchange: summing `c d * s.multSum d` over positive divisors `d` of
`s.prodPrimes` equals summing the divisor sum over `gcd s.prodPrimes n` against `s.weights n`. -/
theorem sum_divisors_prodPrimes_mul_multSum (s : BoundingSieve) (c : ℕ → ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d =
      ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, c d := by
  calc
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d
      = ∑ d ∈ s.prodPrimes.divisors, ∑ n ∈ s.support,
          if d ∣ n then s.weights n * c d else 0 := by
            refine Finset.sum_congr rfl fun d _ ↦ ?_
            rw [multSum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ ↦ ?_
            split_ifs <;> ring
    _ = ∑ n ∈ s.support, ∑ d ∈ s.prodPrimes.divisors,
          if d ∣ n then s.weights n * c d else 0 := Finset.sum_comm
    _ = ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, c d := by
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          rw [Finset.mul_sum, ← Finset.sum_filter]
          congr 1
          rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
            (Nat.gcd_dvd_left s.prodPrimes n)]
          ext d
          simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, s.prodPrimes_ne_zero,
            not_false_eq_true, and_true, Nat.dvd_gcd_iff]
          tauto

/-- Splitting a weighted divisor sum into `s.totalMass * s.mainSum c` plus the signed remainder
sum. -/
theorem sum_divisors_prodPrimes_mul_multSum_eq_totalMass_mul_mainSum_add
    (s : BoundingSieve) (c : ℕ → ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d =
      s.totalMass * s.mainSum c + ∑ d ∈ s.prodPrimes.divisors, c d * s.rem d := by
  rw [mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [s.multSum_eq_main_err d]
  ring

/-- Exact Legendre inclusion-exclusion identity on a `BoundingSieve`. -/
theorem siftedSum_eq_sum_moebius_mul_multSum (s : BoundingSieve) :
    s.siftedSum = ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.multSum d := by
  rw [s.sum_divisors_prodPrimes_mul_multSum, s.siftedSum_eq_sum_support_mul_ite]
  refine Finset.sum_congr rfl fun n _ ↦ congrArg (s.weights n * ·) ?_
  have hconv : ((μ : ArithmeticFunction ℝ) * ζ) (Nat.gcd s.prodPrimes n) =
      (1 : ArithmeticFunction ℝ) (Nat.gcd s.prodPrimes n) := by
    rw [coe_moebius_mul_coe_zeta]
  rw [coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hconv
  simpa only [intCoe_apply] using hconv.symm

/-- The main sum of the Möbius coefficients evaluates to the finite Euler product
`∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)`. -/
theorem mainSum_moebius (s : BoundingSieve) :
    s.mainSum (fun d ↦ (μ d : ℝ)) = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  rw [mainSum, ← s.nu_mult.prodPrimeFactors_one_sub s.nu s.prodPrimes_ne_zero]

/-- Exact Legendre decomposition into the Euler-product main term and the signed remainder sum. -/
theorem siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem (s : BoundingSieve) :
    s.siftedSum = s.totalMass * (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) +
      ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.rem d := by
  rw [s.siftedSum_eq_sum_moebius_mul_multSum,
    s.sum_divisors_prodPrimes_mul_multSum_eq_totalMass_mul_mainSum_add, s.mainSum_moebius]

/-- Absolute Legendre error bound: the difference between `s.siftedSum` and the Euler-product main
term is bounded by the sum of `|s.rem d|` over all positive divisors `d` of `s.prodPrimes`. -/
theorem abs_siftedSum_sub_totalMass_mul_prod_le_sum_abs_rem (s : BoundingSieve) :
    |s.siftedSum - s.totalMass * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
      ∑ d ∈ s.prodPrimes.divisors, |s.rem d| := by
  have hsub : s.siftedSum - s.totalMass * (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) =
      ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.rem d := by
    linarith [s.siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem]
  rw [hsub]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  have hsq : Squarefree d := s.squarefree_of_mem_divisors_prodPrimes hd
  have habs : |(μ d : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
  rw [abs_mul, habs, one_mul]

/-- Lower sieve coefficient inequality: if `∑ d ∈ r.divisors, c d ≤ 1_{r = 1}` for every divisor
`r` of `s.prodPrimes`, then `∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d ≤ s.siftedSum`. -/
theorem sum_mul_multSum_le_siftedSum_of_dvd_prodPrimes (s : BoundingSieve) (c : ℕ → ℝ)
    (hc : ∀ r, r ∣ s.prodPrimes → ∑ d ∈ r.divisors, c d ≤ if r = 1 then 1 else 0) :
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d ≤ s.siftedSum := by
  rw [s.sum_divisors_prodPrimes_mul_multSum, s.siftedSum_eq_sum_support_mul_ite]
  exact Finset.sum_le_sum fun n _ ↦
    mul_le_mul_of_nonneg_left (hc _ (Nat.gcd_dvd_left s.prodPrimes n)) (s.weights_nonneg n)

/-- Lower main-term minus absolute-remainder bound under the local lower coefficient condition on
divisors of `s.prodPrimes`. -/
theorem totalMass_mul_mainSum_sub_errSum_le_siftedSum_of_dvd_prodPrimes
    (s : BoundingSieve) (c : ℕ → ℝ)
    (hc : ∀ r, r ∣ s.prodPrimes → ∑ d ∈ r.divisors, c d ≤ if r = 1 then 1 else 0) :
    s.totalMass * s.mainSum c - s.errSum c ≤ s.siftedSum := by
  refine le_trans ?_ (s.sum_mul_multSum_le_siftedSum_of_dvd_prodPrimes c hc)
  rw [s.sum_divisors_prodPrimes_mul_multSum_eq_totalMass_mul_mainSum_add, sub_eq_add_neg,
    errSum, ← Finset.sum_neg_distrib]
  refine add_le_add_right (Finset.sum_le_sum fun d _ ↦ ?_) _
  rw [← abs_mul]
  exact neg_abs_le _

/-- Remainder bound at an integer coefficient cutoff `D`: if `c` vanishes on divisors above `D` and
`|c d| ≤ C` on divisors `d ≤ D`, then `s.errSum c` is at most `C` times the remainder sum up to `D`.
Nonnegativity of `C` is not assumed: it is automatic when `1 ≤ D` and vacuous when `D = 0`. -/
theorem errSum_le_mul_sum_filter_le_abs_rem (s : BoundingSieve) (c : ℕ → ℝ) (D : ℕ) {C : ℝ}
    (hsupp : ∀ d ∈ s.prodPrimes.divisors, D < d → c d = 0)
    (hbound : ∀ d ∈ s.prodPrimes.divisors, d ≤ D → |c d| ≤ C) :
    s.errSum c ≤ C * ∑ d ∈ s.prodPrimes.divisors.filter (· ≤ D), |s.rem d| := by
  rw [errSum, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not s.prodPrimes.divisors (· ≤ D)]
  have hzero : ∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ ¬d ≤ D), |c d| * |s.rem d| = 0 := by
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
    rw [hsupp d hdP (Nat.lt_of_not_le hdD), abs_zero, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_le_sum fun d hd ↦ ?_
  obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
  exact mul_le_mul_of_nonneg_right (hbound d hdP hdD) (abs_nonneg _)

/-- First Bonferroni lower sieve bound: `s.multSum 1 - ∑ p ∈ s.prodPrimes.primeFactors, s.multSum p`
is at most `s.siftedSum`. -/
theorem multSum_one_sub_sum_primeFactors_le_siftedSum (s : BoundingSieve) :
    s.multSum 1 - ∑ p ∈ s.prodPrimes.primeFactors, s.multSum p ≤ s.siftedSum := by
  have h1 : s.multSum 1 = ∑ n ∈ s.support, s.weights n := by
    simp [multSum]
  have hp_sum : ∑ p ∈ s.prodPrimes.primeFactors, s.multSum p =
      ∑ n ∈ s.support, s.weights n *
        ((s.prodPrimes.primeFactors.filter (· ∣ n)).card : ℝ) := by
    simp only [multSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [h1, hp_sum, ← Finset.sum_sub_distrib, s.siftedSum_eq_sum_support_mul_ite]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  have hpt : 1 - ((s.prodPrimes.primeFactors.filter (· ∣ n)).card : ℝ) ≤
      if Nat.gcd s.prodPrimes n = 1 then 1 else 0 := by
    split_ifs with hcop
    · have h0 : (0 : ℝ) ≤ ((s.prodPrimes.primeFactors.filter (· ∣ n)).card : ℝ) :=
        Nat.cast_nonneg _
      linarith [h0]
    · obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hcop
      obtain ⟨hpP, hpn⟩ := Nat.dvd_gcd_iff.mp hp_dvd
      have hmem : p ∈ s.prodPrimes.primeFactors.filter (· ∣ n) :=
        Finset.mem_filter.mpr
          ⟨(Nat.mem_primeFactors_of_ne_zero s.prodPrimes_ne_zero).mpr ⟨hp_prime, hpP⟩, hpn⟩
      have hpos : 1 ≤ (s.prodPrimes.primeFactors.filter (· ∣ n)).card :=
        Finset.card_pos.mpr ⟨p, hmem⟩
      have hcast : (1 : ℝ) ≤ (s.prodPrimes.primeFactors.filter (· ∣ n)).card := by
        exact_mod_cast hpos
      linarith
  have hfactor : s.weights n - s.weights n *
      ((s.prodPrimes.primeFactors.filter (· ∣ n)).card : ℝ) =
      s.weights n * (1 - ((s.prodPrimes.primeFactors.filter (· ∣ n)).card : ℝ)) := by
    ring
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hpt (s.weights_nonneg n)

end BoundingSieve
