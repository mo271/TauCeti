/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Dirichlet square of the Möbius function and divisor-count inversion

Because the arithmetic divisor-count function `σ 0` (`n ↦ #n.divisors`) is the Dirichlet square
`ζ * ζ` of the arithmetic zeta function, and the Möbius function `μ` is the Dirichlet inverse of
`ζ`, the Dirichlet square `μ * μ` is the convolution inverse of `σ 0`:

```text
(μ * μ) * σ 0 = 1,    σ 0 * (μ * μ) = 1.
```

At prime powers, `(μ * μ) 1 = 1`, `(μ * μ) p = -2`, `(μ * μ) (p ^ 2) = 1`, and
`(μ * μ) (p ^ r) = 0` for `r ≥ 3`. Convolving with `μ * μ` inverts divisor sums weighted by the
divisor-count function `e ↦ #(n / e).divisors`, such as the dimension identity
`dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors · dim S_k(Γ₁(M))ⁿᵉʷ` relating full cusp-form spaces
to newspaces (Diamond–Shurman, Theorem 5.8.3).

Both global and divisor-local inversion theorems are proved, for functions with values in an
additive commutative group (`•`) and in a not-necessarily-associative ring (`*`). The single-level
form `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_smul_of_mem_divisors` requires the
forward identity only on the divisors of a fixed `n ≠ 0`, which is the form needed when the
summands depend on ambient datum defined at level `n` (such as a Dirichlet character modulo `N`).

## Main results

* `ArithmeticFunction.moebius_mul_moebius_apply_prime`,
  `ArithmeticFunction.moebius_mul_moebius_apply_prime_sq`,
  `ArithmeticFunction.moebius_mul_moebius_apply_prime_pow`: explicit values of `μ * μ` at primes
  and prime powers.
* `ArithmeticFunction.moebius_mul_moebius_mul_coe_sigma_zero`,
  `ArithmeticFunction.coe_sigma_zero_mul_moebius_mul_moebius`: `μ * μ` and `σ 0` are Dirichlet
  inverses.
* `ArithmeticFunction.sum_divisors_moebius_mul_moebius_smul_sum_card_divisors_nsmul`,
  `ArithmeticFunction.sum_divisors_card_divisors_nsmul_sum_moebius_mul_moebius_smul`: pointwise
  double-Möbius cancellation at any `n ≠ 0` in an `AddCommGroup`.
* `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_smul_of_mem_divisors`,
  `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_mem_divisors`: divisor-local
  inversion at a single `n ≠ 0`.
* `ArithmeticFunction.sum_card_divisors_nsmul_eq_iff_sum_moebius_mul_moebius_smul_eq_on`,
  `ArithmeticFunction.sum_card_divisors_nsmul_eq_iff_sum_moebius_mul_moebius_smul_eq`: two-way
  inversion equivalences on divisor-closed sets and on all positive integers.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
-/

public section

namespace ArithmeticFunction

open Finset Nat

open scoped Moebius zeta sigma

variable {R M : Type*}

/-! ### Multiplicativity and values of `μ * μ` -/

/-- The Dirichlet square `μ * μ` of the Möbius function is multiplicative. -/
theorem isMultiplicative_moebius_mul_moebius : IsMultiplicative (μ * μ) :=
  isMultiplicative_moebius.mul isMultiplicative_moebius

/-- At `1`, `(μ * μ) 1 = 1`. -/
theorem moebius_mul_moebius_apply_one : (μ * μ) 1 = 1 :=
  isMultiplicative_moebius_mul_moebius.map_one

/-- At a prime `p`, `(μ * μ) p = -2`. -/
theorem moebius_mul_moebius_apply_prime {p : ℕ} (hp : p.Prime) : (μ * μ) p = -2 := by
  rw [ArithmeticFunction.mul_apply, sum_divisorsAntidiagonal' (f := fun x y ↦ μ x * μ y),
    hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [Nat.div_self hp.pos, moebius_apply_prime hp]

/-- At the square of a prime `p`, `(μ * μ) (p ^ 2) = 1`. -/
theorem moebius_mul_moebius_apply_prime_sq {p : ℕ} (hp : p.Prime) : (μ * μ) (p ^ 2) = 1 := by
  have hμ2 : μ (p ^ 2) = 0 := by
    rw [moebius_apply_prime_pow hp two_ne_zero, ite_eq_right (by omega)]
  rw [ArithmeticFunction.mul_apply, sum_divisorsAntidiagonal' (f := fun x y ↦ μ x * μ y),
    sum_divisors_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [Nat.pow_div (by omega) hp.pos, Nat.pow_div (by omega) hp.pos,
    Nat.pow_div (by omega) hp.pos]
  simp [hμ2, moebius_apply_prime hp]

/-- At a prime power `p ^ r` with `3 ≤ r`, `(μ * μ) (p ^ r) = 0`: in every factorisation
`p ^ i * p ^ (r - i) = p ^ r`, at least one exponent is `≥ 2`, where `μ` vanishes. -/
theorem moebius_mul_moebius_apply_prime_pow_eq_zero {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r) :
    (μ * μ) (p ^ r) = 0 := by
  rw [ArithmeticFunction.mul_apply, sum_divisorsAntidiagonal' (f := fun x y ↦ μ x * μ y),
    sum_divisors_prime_pow hp]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.pow_div hir hp.pos]
  by_cases hi2 : 2 ≤ i
  · have hμ : μ (p ^ i) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
    rw [hμ, mul_zero]
  · have hμ : μ (p ^ (r - i)) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
    rw [hμ, zero_mul]

/-- Explicit value of `μ * μ` at any prime power `p ^ r`. -/
theorem moebius_mul_moebius_apply_prime_pow {p r : ℕ} (hp : p.Prime) :
    (μ * μ) (p ^ r) =
      if r = 0 then 1 else if r = 1 then -2 else if r = 2 then 1 else 0 := by
  rcases r with _ | _ | _ | r
  · simp
  · simpa using moebius_mul_moebius_apply_prime hp
  · simpa using moebius_mul_moebius_apply_prime_sq hp
  · simpa using moebius_mul_moebius_apply_prime_pow_eq_zero hp (by omega)

/-! ### Convolution inverse of the divisor-count function `σ 0` -/

/-- `(μ * μ) * σ 0 = 1` in `ArithmeticFunction ℤ`: the Dirichlet square of `μ` inverts the
divisor-count function `σ 0 = ζ * ζ`. -/
@[simp]
theorem moebius_mul_moebius_mul_coe_sigma_zero :
    ((μ * μ) * (σ 0 : ArithmeticFunction ℤ)) = 1 := by
  calc (μ * μ) * (σ 0 : ArithmeticFunction ℤ)
      = μ * (μ * ζ) * ζ := by
        rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta, natCoe_mul, ← mul_assoc, mul_assoc μ μ ζ]
    _ = 1 := by rw [moebius_mul_coe_zeta, mul_one, moebius_mul_coe_zeta]

/-- `σ 0 * (μ * μ) = 1` in `ArithmeticFunction ℤ`. -/
@[simp]
theorem coe_sigma_zero_mul_moebius_mul_moebius :
    ((σ 0 : ArithmeticFunction ℤ) * (μ * μ)) = 1 := by
  rw [mul_comm, moebius_mul_moebius_mul_coe_sigma_zero]

/-- Ring-valued form of `(μ * μ) * σ 0 = 1` in `ArithmeticFunction R`. -/
@[simp]
theorem coe_moebius_mul_coe_moebius_mul_coe_sigma_zero [Ring R] :
    ((μ : ArithmeticFunction R) * μ * σ 0) = 1 := by
  rw [← intCoe_mul, ← coe_coe, ← intCoe_mul, moebius_mul_moebius_mul_coe_sigma_zero, intCoe_one]

/-- Ring-valued form of `σ 0 * (μ * μ) = 1` in `ArithmeticFunction R`. -/
@[simp]
theorem coe_sigma_zero_mul_coe_moebius_mul_coe_moebius [Ring R] :
    ((σ 0 : ArithmeticFunction R) * ((μ : ArithmeticFunction R) * μ)) = 1 := by
  rw [← intCoe_mul, ← coe_coe, ← intCoe_mul, coe_sigma_zero_mul_moebius_mul_moebius, intCoe_one]

/-- Divisor-sum form of `(μ * μ) * σ 0 = 1`. -/
theorem sum_divisors_moebius_mul_moebius_mul_card_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ * μ) (n / d) * (#d.divisors : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f n) moebius_mul_moebius_mul_coe_sigma_zero
  rw [ArithmeticFunction.mul_apply, sum_divisorsAntidiagonal' (f := fun x y ↦ (μ * μ) x *
    (σ 0 : ArithmeticFunction ℤ) y), ArithmeticFunction.one_apply] at h
  simpa only [natCoe_apply, sigma_zero_apply] using h

/-! ### Double-Möbius inversion for divisor-count sums -/

/-- Pointwise cancellation `(μ * μ) • (σ 0 • g) = g` at any `n ≠ 0` for functions with values in
an additive commutative group. -/
theorem sum_divisors_moebius_mul_moebius_smul_sum_card_divisors_nsmul [AddCommGroup M]
    (g : ℕ → M) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ * μ) (n / d) • ∑ e ∈ d.divisors, #(d / e).divisors • g e = g n := by
  let g' : ArithmeticFunction M := ⟨fun x ↦ if x = 0 then 0 else g x, ite_eq_left rfl⟩
  have hg' {k : ℕ} (hk : k ≠ 0) : g' k = g k := ite_eq_right hk
  have hcancel : (μ * μ) • ((σ 0 : ArithmeticFunction ℤ) • g') = g' := by
    rw [← mul_smul, moebius_mul_moebius_mul_coe_sigma_zero, one_smul]
  have hn' := congrArg (fun F : ArithmeticFunction M ↦ F n) hcancel
  rw [ArithmeticFunction.smul_apply, sum_divisorsAntidiagonal' (f := fun x y ↦ (μ * μ) x •
    ((σ 0 : ArithmeticFunction ℤ) • g') y), hg' hn] at hn'
  refine (Finset.sum_congr rfl fun d _ ↦ congrArg ((μ * μ) (n / d) • ·) ?_).trans hn'
  rw [ArithmeticFunction.smul_apply,
    sum_divisorsAntidiagonal' (f := fun x y ↦ (σ 0 : ArithmeticFunction ℤ) x • g' y)]
  exact Finset.sum_congr rfl fun e he ↦ by
    rw [hg' (Nat.pos_of_mem_divisors he).ne', natCoe_apply, sigma_zero_apply, natCast_zsmul]

/-- Pointwise cancellation `σ 0 • ((μ * μ) • f) = f` at any `n ≠ 0` for functions with values in
an additive commutative group. -/
theorem sum_divisors_card_divisors_nsmul_sum_moebius_mul_moebius_smul [AddCommGroup M]
    (f : ℕ → M) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, #(n / d).divisors • ∑ e ∈ d.divisors, (μ * μ) (d / e) • f e = f n := by
  let f' : ArithmeticFunction M := ⟨fun x ↦ if x = 0 then 0 else f x, ite_eq_left rfl⟩
  have hf' {k : ℕ} (hk : k ≠ 0) : f' k = f k := ite_eq_right hk
  have hcancel : (σ 0 : ArithmeticFunction ℤ) • ((μ * μ) • f') = f' := by
    rw [← mul_smul, coe_sigma_zero_mul_moebius_mul_moebius, one_smul]
  have hn' := congrArg (fun F : ArithmeticFunction M ↦ F n) hcancel
  rw [ArithmeticFunction.smul_apply, sum_divisorsAntidiagonal' (f := fun x y ↦
    (σ 0 : ArithmeticFunction ℤ) x • ((μ * μ) • f') y), hf' hn] at hn'
  refine (Finset.sum_congr rfl fun d _ ↦ ?_).trans hn'
  rw [natCoe_apply, sigma_zero_apply, natCast_zsmul]
  congr 1
  rw [ArithmeticFunction.smul_apply, sum_divisorsAntidiagonal' (f := fun x y ↦ (μ * μ) x • f' y)]
  exact Finset.sum_congr rfl fun e he ↦ by rw [hf' (Nat.pos_of_mem_divisors he).ne']

/-- **Divisor-local double-Möbius inversion** in an `AddCommGroup`: if
`f d = ∑_{e ∣ d} #(d / e).divisors • g e` holds at every divisor `d` of `n ≠ 0`, then
`g n = ∑_{d ∣ n} (μ * μ)(n / d) • f d`. -/
theorem eq_sum_divisors_moebius_mul_moebius_smul_of_mem_divisors [AddCommGroup M]
    {f g : ℕ → M} {n : ℕ} (hn : n ≠ 0)
    (h : ∀ d ∈ n.divisors, f d = ∑ e ∈ d.divisors, #(d / e).divisors • g e) :
    g n = ∑ d ∈ n.divisors, (μ * μ) (n / d) • f d := by
  rw [← sum_divisors_moebius_mul_moebius_smul_sum_card_divisors_nsmul g hn]
  exact Finset.sum_congr rfl fun d hd ↦ by rw [h d hd]

/-- **Divisor-local double-Möbius inversion** in a ring: if
`f d = ∑_{e ∣ d} #(d / e).divisors * g e` holds at every divisor `d` of `n ≠ 0`, then
`g n = ∑_{d ∣ n} (μ * μ)(n / d) * f d`. -/
theorem eq_sum_divisors_moebius_mul_moebius_mul_of_mem_divisors [NonAssocRing R]
    {f g : ℕ → R} {n : ℕ} (hn : n ≠ 0)
    (h : ∀ d ∈ n.divisors, f d = ∑ e ∈ d.divisors, (#(d / e).divisors : R) * g e) :
    g n = ∑ d ∈ n.divisors, ((μ * μ) (n / d) : R) * f d := by
  have h' : ∀ d ∈ n.divisors, f d = ∑ e ∈ d.divisors, #(d / e).divisors • g e := fun d hd ↦ by
    simpa only [nsmul_eq_mul] using h d hd
  simpa only [zsmul_eq_mul] using eq_sum_divisors_moebius_mul_moebius_smul_of_mem_divisors hn h'

/-- **Double-Möbius inversion on a divisor-closed set** for functions with values in an
`AddCommGroup`. -/
theorem sum_card_divisors_nsmul_eq_iff_sum_moebius_mul_moebius_smul_eq_on [AddCommGroup M]
    {f g : ℕ → M} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, #(n / d).divisors • g d = f n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (μ * μ) (n / d) • f d = g n := by
  refine ⟨fun h n hn hns ↦ (eq_sum_divisors_moebius_mul_moebius_smul_of_mem_divisors hn.ne'
    fun d hd ↦ (h d (Nat.pos_of_mem_divisors hd) (hs d n (Nat.dvd_of_mem_divisors hd) hns)).symm
      ).symm, fun h n hn hns ↦ ?_⟩
  rw [← sum_divisors_card_divisors_nsmul_sum_moebius_mul_moebius_smul f hn.ne']
  exact Finset.sum_congr rfl fun d hd ↦ by
    rw [h d (Nat.pos_of_mem_divisors hd) (hs d n (Nat.dvd_of_mem_divisors hd) hns)]

/-- **Double-Möbius inversion on a divisor-closed set** for functions with values in a ring. -/
theorem sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq_on [NonAssocRing R]
    {f g : ℕ → R} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (#(n / d).divisors : R) * g d = f n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, ((μ * μ) (n / d) : R) * f d = g n := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul] using
    sum_card_divisors_nsmul_eq_iff_sum_moebius_mul_moebius_smul_eq_on (f := f) (g := g) s hs

/-- **Double-Möbius inversion** on all positive integers for functions with values in an
`AddCommGroup`. -/
theorem sum_card_divisors_nsmul_eq_iff_sum_moebius_mul_moebius_smul_eq [AddCommGroup M]
    {f g : ℕ → M} :
    (∀ n > 0, ∑ d ∈ n.divisors, #(n / d).divisors • g d = f n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors, (μ * μ) (n / d) • f d = g n := by
  simpa using sum_card_divisors_nsmul_eq_iff_sum_moebius_mul_moebius_smul_eq_on Set.univ
    fun _ _ _ _ ↦ trivial

/-- **Double-Möbius inversion** on all positive integers for functions with values in a ring. -/
theorem sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq [NonAssocRing R]
    {f g : ℕ → R} :
    (∀ n > 0, ∑ d ∈ n.divisors, (#(n / d).divisors : R) * g d = f n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors, ((μ * μ) (n / d) : R) * f d = g n := by
  simpa using sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq_on Set.univ
    fun _ _ _ _ ↦ trivial

end ArithmeticFunction
