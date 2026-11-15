/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Gaussian expectations of affine-composed Hermite polynomials

Under the standard Gaussian measure `gaussianReal 0 1`, composing a probabilists' Hermite
polynomial `Polynomial.hermite n` with an affine map `z ↦ c + b * z` preserves all polynomial
integrability properties and satisfies the Stein lowering identity
`∫ z, z * H_{n + 1}(c + b * z) dγ = (n + 1) * b * ∫ z, Hₙ(c + b * z) dγ`.

When the weights satisfy the variance-preserving condition `a ^ 2 + b ^ 2 = 1`, Gaussian
averaging contracts the `n`-th Hermite polynomial homogeneously:
`∫ z, Hₙ(a * x + b * z) dγ = a ^ n * Hₙ(x)`.
Combining the two identities evaluates `∫ z, z * H_{n + 1}(a * x + b * z) dγ` in closed form as
`(n + 1) * b * a ^ n * Hₙ(x)`. All identities hold without sign or nondegeneracy restrictions on
`a` and `b`, including the endpoint cases `a = 0` and `b = 0`.

## Main statements

* `TauCeti.memLp_two_aeval_comp_affine_gaussianReal` and
  `TauCeti.integrable_aeval_comp_affine_gaussianReal`: square-integrability and integrability of
  `z ↦ aeval (c + b * z) p` against `gaussianReal μ v` for any `p : ℤ[X]`.
* `TauCeti.integral_mul_aeval_hermite_succ_comp_affine_gaussianReal`: Stein lowering for
  `z ↦ z * H_{n + 1}(c + b * z)` under `gaussianReal 0 1`.
* `TauCeti.integral_aeval_hermite_mul_add_mul_gaussianReal`: unit-sphere Gaussian averaging
  `∫ z, Hₙ(a * x + b * z) dγ = a ^ n * Hₙ(x)` for `a ^ 2 + b ^ 2 = 1`.
* `TauCeti.integral_aeval_hermite_gaussianReal`: expectation
  `∫ z, Hₙ(z) dγ = if n = 0 then 1 else 0`.
* `TauCeti.integral_mul_aeval_hermite_succ_mul_add_mul_gaussianReal`: closed-form Gaussian
  cross-moment `∫ z, z * H_{n + 1}(a * x + b * z) dγ = (n + 1) * b * a ^ n * Hₙ(x)` for
  `a ^ 2 + b ^ 2 = 1`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4.
* S. Janson, *Gaussian Hilbert Spaces*, Cambridge University Press, 1997, Chapter 3.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

/-- Evaluating an integer polynomial along an affine map gives a square-integrable function under
every real Gaussian measure. -/
theorem memLp_two_aeval_comp_affine_gaussianReal (p : ℤ[X]) (c b μ : ℝ) (v : ℝ≥0) :
    MemLp (fun z : ℝ ↦ aeval (c + b * z) p) 2 (gaussianReal μ v) := by
  let q : ℝ[X] := (p.map (Int.castRingHom ℝ)).comp (C c + C b * X)
  have hq : (fun z : ℝ ↦ q.eval z) = fun z : ℝ ↦ aeval (c + b * z) p := by
    ext z
    simp [q, eval_comp, ← algebraMap_int_eq, eval_map_algebraMap]
  exact hq ▸ memLp_two_eval_gaussianReal μ v q

/-- Evaluating an integer polynomial along an affine map gives an integrable function under every
real Gaussian measure. -/
theorem integrable_aeval_comp_affine_gaussianReal (p : ℤ[X]) (c b μ : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ ↦ aeval (c + b * z) p) (gaussianReal μ v) :=
  (memLp_two_aeval_comp_affine_gaussianReal p c b μ v).integrable one_le_two

/-- **Stein lowering for affine-composed Hermite polynomials.** Under `gaussianReal 0 1`,
multiplying `H_{n + 1}(c + b * z)` by `z` lowers the Hermite index by one and scales by
`(n + 1) * b`, with no constraint on `c` or `b`. -/
theorem integral_mul_aeval_hermite_succ_comp_affine_gaussianReal (n : ℕ) (c b : ℝ) :
    (∫ z : ℝ, z * aeval (c + b * z) (hermite (n + 1)) ∂gaussianReal 0 1) =
      (n + 1 : ℝ) * b * ∫ z : ℝ, aeval (c + b * z) (hermite n) ∂gaussianReal 0 1 := by
  have hd (z : ℝ) : HasDerivAt (fun z : ℝ ↦ aeval (c + b * z) (hermite (n + 1)))
      ((n + 1 : ℝ) * b * aeval (c + b * z) (hermite n)) z := by
    have h1 : HasDerivAt (fun z : ℝ ↦ c + b * z) b z := by
      simpa using ((hasDerivAt_id z).const_mul b).const_add c
    have h2 := ((hermite (n + 1)).hasDerivAt_aeval (c + b * z)).comp z h1
    refine h2.congr_deriv ?_
    rw [derivative_hermite_succ, map_nsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hder : deriv (fun z : ℝ ↦ aeval (c + b * z) (hermite (n + 1))) =
      fun z : ℝ ↦ (n + 1 : ℝ) * b * aeval (c + b * z) (hermite n) :=
    funext fun z ↦ (hd z).deriv
  have hzf : Integrable (fun z : ℝ ↦ z * aeval (c + b * z) (hermite (n + 1)))
      (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_mul
      (memLp_two_aeval_comp_affine_gaussianReal (hermite (n + 1)) c b 0 1)
  have hdf : Integrable (deriv fun z : ℝ ↦ aeval (c + b * z) (hermite (n + 1)))
      (gaussianReal 0 1) := by
    rw [hder]
    exact (integrable_aeval_comp_affine_gaussianReal (hermite n) c b 0 1).const_mul _
  rw [Probability.integral_mul_eq_integral_deriv_gaussianReal _
    (fun z ↦ (hd z).differentiableAt) hzf hdf, hder, integral_const_mul]

/-- **Unit-sphere Gaussian contraction of Hermite polynomials.** Whenever `a ^ 2 + b ^ 2 = 1`,
averaging `Hₙ(a * x + b * z)` against `z ~ N(0, 1)` yields `a ^ n * Hₙ(x)`. Both degenerate
cases `a = 0` and `b = 0` are included. -/
theorem integral_aeval_hermite_mul_add_mul_gaussianReal {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (n : ℕ) (x : ℝ) :
    (∫ z : ℝ, aeval (a * x + b * z) (hermite n) ∂gaussianReal 0 1) =
      a ^ n * aeval x (hermite n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [hermite_one, aeval_X, pow_one]
    have hi : Integrable (fun z : ℝ ↦ b * z) (gaussianReal 0 1) :=
      (integrable_pow_gaussianReal 0 1 1).const_mul b |>.congr (Filter.Eventually.of_forall
        fun z ↦ by simp)
    rw [integral_add (integrable_const (a * x)) hi, integral_const, integral_const_mul,
      integral_id_gaussianReal]
    simp
  | more m ihm ihm1 =>
    have hrec (z : ℝ) : aeval (a * x + b * z) (hermite (m + 2)) =
        (a * x * aeval (a * x + b * z) (hermite (m + 1)) +
          b * (z * aeval (a * x + b * z) (hermite (m + 1)))) -
          (m + 1 : ℝ) * aeval (a * x + b * z) (hermite m) := by
      rw [hermite_add_two m, map_sub, map_mul, aeval_X, map_nsmul, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring
    have hi1 : Integrable (fun z : ℝ ↦ a * x * aeval (a * x + b * z) (hermite (m + 1)))
        (gaussianReal 0 1) :=
      (integrable_aeval_comp_affine_gaussianReal (hermite (m + 1)) (a * x) b 0 1).const_mul _
    have hi2 : Integrable (fun z : ℝ ↦ b * (z * aeval (a * x + b * z) (hermite (m + 1))))
        (gaussianReal 0 1) :=
      ((memLp_id_gaussianReal' 2 (by norm_num)).integrable_mul
        (memLp_two_aeval_comp_affine_gaussianReal (hermite (m + 1)) (a * x) b 0 1)).const_mul b
    have hi12 : Integrable (fun z : ℝ ↦ a * x * aeval (a * x + b * z) (hermite (m + 1)) +
        b * (z * aeval (a * x + b * z) (hermite (m + 1)))) (gaussianReal 0 1) :=
      hi1.add hi2
    have hi3 : Integrable (fun z : ℝ ↦ (m + 1 : ℝ) * aeval (a * x + b * z) (hermite m))
        (gaussianReal 0 1) :=
      (integrable_aeval_comp_affine_gaussianReal (hermite m) (a * x) b 0 1).const_mul _
    simp_rw [hrec]
    rw [integral_sub hi12 hi3, integral_add hi1 hi2, integral_const_mul,
      integral_const_mul, integral_const_mul,
      integral_mul_aeval_hermite_succ_comp_affine_gaussianReal, ihm1, ihm, hermite_add_two m,
      map_sub, map_mul, aeval_X, map_nsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    linear_combination (m + 1 : ℝ) * a ^ m * aeval x (hermite m) * hab

/-- Under the standard Gaussian law, `H₀` has expectation `1` and every higher Hermite polynomial
has expectation `0`. -/
@[simp]
theorem integral_aeval_hermite_gaussianReal (n : ℕ) :
    (∫ z : ℝ, aeval z (hermite n) ∂gaussianReal 0 1) = if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · simp
  · simpa using integral_aeval_hermite_mul_add_mul_gaussianReal (a := 0) (b := 1)
      (by norm_num) (n + 1) 0

/-- **Closed-form Gaussian cross-moment for Hermite polynomials.** Whenever `a ^ 2 + b ^ 2 = 1`,
`∫ z, z * H_{n + 1}(a * x + b * z) dγ = (n + 1) * b * a ^ n * Hₙ(x)`. -/
theorem integral_mul_aeval_hermite_succ_mul_add_mul_gaussianReal {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) (n : ℕ) (x : ℝ) :
    (∫ z : ℝ, z * aeval (a * x + b * z) (hermite (n + 1)) ∂gaussianReal 0 1) =
      (n + 1 : ℝ) * b * a ^ n * aeval x (hermite n) := by
  rw [integral_mul_aeval_hermite_succ_comp_affine_gaussianReal,
    integral_aeval_hermite_mul_add_mul_gaussianReal hab]
  ring

end TauCeti
