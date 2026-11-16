/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.RingTheory.MvPolynomial.Abv.Eval
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Local evaluation bounds for index-concentrated multihomogeneous polynomials

Let `P` be a multihomogeneous polynomial in blocks of variables `X (h, i)` (`h : κ`, `i : ι`) of
multidegree `e` bounded componentwise by a reference multidegree `d` (`e h ≤ d h`), as arises after
taking a Hasse derivative of a multihomogeneous polynomial of multidegree `d`. Suppose the support
of `P` is *index-concentrated* around `μ` with radius `Δ` relative to `d`: every nonzero coefficient
`P.coeff J` satisfies

`|(∑ h, (J (h, i) : ℝ) / d h) - μ| ≤ Δ` for all `i : ι`.

When `P` is evaluated at a point `y` satisfying `v (y (h, i)) ≤ U * Q h ^ c i` for positive block
levels `Q h` whose weighted logarithms `(d h : ℝ) * log (Q h)` lie within `E h` of a common
parameter `D ≥ 0`, every monomial `∏_{h, i} y (h, i) ^ J (h, i)` occurring in `P(y)` has absolute
value at most

`U ^ (∑ h, e h) * exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|)`.

Summing over `P.support` introduces the factor `#P.support * B` at a general absolute value and `B`
at a nonarchimedean absolute value, where `B` bounds the coefficients of `P` under `v`. Separating
`e` from `d` allows `P` to be a Hasse derivative of an auxiliary polynomial of multidegree `d`
whose vanishing conditions are still normalized by `d h`.

## Main results

* `MvPolynomial.coeff_eq_zero_of_lt_abs_sub_of_notMem_Ioo`: vanishing outside an asymmetric open
  interval `Set.Ioo (μ - δ₁) (μ + δ₂)` implies vanishing outside the symmetric closed ball of
  radius `max δ₁ δ₂` around `μ`.
* `MvPolynomial.sum_mul_le_of_concentrated`: the weighted exponent bound
  `∑ h, ∑ i, J (h, i) * c i * q h ≤ D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|`.
* `AbsoluteValue.apply_prod_pow_le_of_concentrated`: single-monomial bound under an absolute value.
* `AbsoluteValue.apply_eval_le_of_isMultiHomogeneous_concentrated`: archimedean evaluation bound
  with `#P.support`.
* `IsNonarchimedean.apply_eval_le_of_isMultiHomogeneous_concentrated` and
  `IsNonarchimedean.apply_eval_le_of_isMultiHomogeneous_concentrated_one`: ultrametric evaluation
  bounds without the support cardinality factor.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  proof of Theorem 7.5.13, Step IV.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Springer (1980),
  Chapter VI, §9.
-/

public section

open Finset MvPolynomial

namespace MvPolynomial

section Concentration

variable {R κ ι : Type*} [CommSemiring R] [Fintype κ]

/-- If the coefficients of `P` vanish whenever some weighted index `∑ h, (J (h, i) : ℝ) / d h` lies
outside `Set.Ioo (μ - δ₁) (μ + δ₂)`, then they vanish whenever some weighted index deviates from
`μ` by strictly more than `max δ₁ δ₂`. -/
theorem coeff_eq_zero_of_lt_abs_sub_of_notMem_Ioo {P : MvPolynomial (κ × ι) R} {d : κ → ℕ}
    {μ δ₁ δ₂ : ℝ}
    (hP : ∀ J : κ × ι →₀ ℕ,
      (∃ i, ∑ h, (J (h, i) : ℝ) / d h ∉ Set.Ioo (μ - δ₁) (μ + δ₂)) → P.coeff J = 0)
    {J : κ × ι →₀ ℕ}
    (hJ : ∃ i, max δ₁ δ₂ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) :
    P.coeff J = 0 := by
  obtain ⟨i, hi⟩ := hJ
  refine hP J ⟨i, fun hmem ↦ ?_⟩
  rcases le_or_gt (∑ h, (J (h, i) : ℝ) / d h - μ) 0 with hneg | hpos
  · linarith [abs_of_nonpos hneg, hmem.1, le_max_left δ₁ δ₂]
  · linarith [abs_of_pos hpos, hmem.2, le_max_right δ₁ δ₂]

/-- **Concentrated bilinear exponent estimate.** Suppose `J` has block sums `∑ i, J (h, i) ≤ d h`,
every weighted index `∑ h, (J (h, i) : ℝ) / d h` lies within `Δ` of `μ`, and every scaled weight
`(d h : ℝ) * q h` lies within `E h` of `D ≥ 0`. Then `∑ h, ∑ i, J (h, i) * c i * q h` is at most
`D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|`. Blocks with `d h = 0` require no
separate positivity hypothesis because `J (h, i) = 0` and `(0 : ℝ) / 0 = 0`. -/
theorem sum_mul_le_of_concentrated [Fintype ι] {J : κ × ι → ℕ} {d : κ → ℕ}
    (hJ : ∀ h, ∑ i, J (h, i) ≤ d h) {μ Δ : ℝ}
    (hconc : ∀ i, |(∑ h, (J (h, i) : ℝ) / d h) - μ| ≤ Δ)
    {D : ℝ} (hD0 : 0 ≤ D) {q E : κ → ℝ} (hD : ∀ h, |(d h : ℝ) * q h - D| ≤ E h)
    (c : ι → ℝ) :
    ∑ h, ∑ i, (J (h, i) : ℝ) * c i * q h ≤
      D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i| := by
  have hident (h : κ) (i : ι) : (J (h, i) : ℝ) * c i * q h =
      c i * ((J (h, i) : ℝ) / d h) * D +
        c i * ((J (h, i) : ℝ) / d h) * ((d h : ℝ) * q h - D) := by
    rcases eq_or_ne (d h) 0 with hd0 | hd0
    · have hJi : J (h, i) = 0 := Nat.eq_zero_of_le_zero <|
        (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i)).trans (hd0 ▸ hJ h)
      simp [hd0, hJi]
    · have _ : (d h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
      field_simp; ring
  have hsplit : ∑ h, ∑ i, (J (h, i) : ℝ) * c i * q h =
      (∑ i, c i * (∑ h, (J (h, i) : ℝ) / d h) * D) +
        ∑ h, ∑ i, c i * ((J (h, i) : ℝ) / d h) * ((d h : ℝ) * q h - D) := by
    simp_rw [hident, sum_add_distrib]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ by rw [mul_sum, sum_mul]
  have hmain : ∑ i, c i * (∑ h, (J (h, i) : ℝ) / d h) * D ≤
      D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) := by
    calc ∑ i, c i * (∑ h, (J (h, i) : ℝ) / d h) * D
        ≤ ∑ i, (c i * μ + |c i| * Δ) * D := sum_le_sum fun i _ ↦ by
          refine mul_le_mul_of_nonneg_right ?_ hD0
          have h1 : c i * ((∑ h, (J (h, i) : ℝ) / d h) - μ) ≤ |c i| * Δ :=
            (le_abs_self _).trans ((abs_mul _ _).trans_le
              (mul_le_mul_of_nonneg_left (hconc i) (abs_nonneg _)))
          linarith
      _ = D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) := by
          rw [← sum_mul, sum_add_distrib, ← sum_mul, ← sum_mul]; ring
  have herr : ∑ h, ∑ i, c i * ((J (h, i) : ℝ) / d h) * ((d h : ℝ) * q h - D) ≤
      (∑ h, E h) * ∑ i, |c i| := by
    calc ∑ h, ∑ i, c i * ((J (h, i) : ℝ) / d h) * ((d h : ℝ) * q h - D)
        ≤ ∑ h, ∑ i, E h * |c i| := sum_le_sum fun h _ ↦ sum_le_sum fun i _ ↦ by
          have hdiv_le : (J (h, i) : ℝ) / d h ≤ 1 := by
            rcases eq_or_ne (d h) 0 with hd0 | hd0
            · simp [hd0]
            · refine (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0))).mpr ?_
              exact_mod_cast (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i)).trans (hJ h)
          have : 0 ≤ E h := (abs_nonneg _).trans (hD h)
          refine (le_abs_self _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (J (h, i) : ℝ) / d h)]
          calc |c i| * ((J (h, i) : ℝ) / d h) * |(d h : ℝ) * q h - D|
              ≤ |c i| * 1 * E h := by gcongr; exact hD h
            _ = E h * |c i| := by ring
      _ = (∑ h, E h) * ∑ i, |c i| := by simp_rw [← mul_sum, ← sum_mul]
  rw [hsplit]
  exact add_le_add hmain herr

end Concentration

end MvPolynomial

namespace AbsoluteValue

variable {R κ ι : Type*} [CommSemiring R] [Fintype κ] [Fintype ι]

/-- **Concentrated monomial bound.** Under an absolute value `v`, if an exponent vector `J` has
block sums `∑ i, J (h, i) = e h` with `e h ≤ d h`, concentrated weighted indices around `μ` with
radius `Δ`, and `v (y (h, i)) ≤ U * Q h ^ c i` for positive block levels `Q h` satisfying
`|(d h : ℝ) * log (Q h) - D| ≤ E h` (`D ≥ 0`), then `v (∏ p, y p ^ J p)` is bounded by
`U ^ (∑ h, e h) * exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|)`. -/
theorem apply_prod_pow_le_of_concentrated (v : AbsoluteValue R ℝ) {J : κ × ι →₀ ℕ} {e d : κ → ℕ}
    (hJe : ∀ h, ∑ i, J (h, i) = e h) (hed : ∀ h, e h ≤ d h) {μ Δ : ℝ}
    (hconc : ∀ i, |(∑ h, (J (h, i) : ℝ) / d h) - μ| ≤ Δ)
    {U : ℝ} {Q : κ → ℝ} (hQ : ∀ h, 0 < Q h)
    {D : ℝ} (hD0 : 0 ≤ D) {E : κ → ℝ} (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    {c : ι → ℝ} {y : κ × ι → R} (hy : ∀ h i, v (y (h, i)) ≤ U * Q h ^ c i) :
    v (∏ p, y p ^ J p) ≤ U ^ (∑ h, e h) *
      Real.exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|) := by
  have hU_pow : 0 ≤ U ^ ∑ h, e h := by
    rcases isEmpty_or_nonempty κ with _ | ⟨⟨h₀⟩⟩
    · simp
    rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
    · simp [← hJe]
    have hpos : 0 < Q h₀ ^ c i₀ := Real.rpow_pos_of_pos (hQ h₀) _
    have hmul : 0 ≤ U * Q h₀ ^ c i₀ := (v.nonneg _).trans (hy h₀ i₀)
    have hU : 0 ≤ U := by nlinarith
    positivity
  rcases subsingleton_or_nontrivial R with _ | _
  · rw [Subsingleton.elim (∏ p, y p ^ J p) 0, map_zero]
    positivity
  rw [map_prod, Fintype.prod_prod_type]
  calc ∏ h, ∏ i, v (y (h, i) ^ J (h, i))
      ≤ ∏ h, ∏ i, (U ^ J (h, i) * (Q h ^ c i) ^ J (h, i)) :=
        prod_le_prod₀ (fun h _ ↦ prod_nonneg fun i _ ↦ v.nonneg _) fun h _ ↦
          prod_le_prod₀ (fun i _ ↦ v.nonneg _) fun i _ ↦ by
            rw [v.map_pow, ← mul_pow]
            exact pow_le_pow_left₀ (v.nonneg _) (hy h i) _
    _ = U ^ (∑ h, e h) *
          Real.exp (∑ h, ∑ i, (J (h, i) : ℝ) * c i * Real.log (Q h)) := by
        simp_rw [prod_mul_distrib]
        congr 1
        · simp_rw [prod_pow_eq_pow_sum, hJe]
        · simp_rw [fun h i ↦ Real.rpow_def_of_pos (hQ h) (c i), ← Real.exp_nat_mul, ← Real.exp_sum]
          congr 1
          refine sum_congr rfl fun h _ ↦ sum_congr rfl fun i _ ↦ ?_
          ring
    _ ≤ U ^ (∑ h, e h) *
          Real.exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|) := by
        gcongr
        exact sum_mul_le_of_concentrated (fun h ↦ (hJe h).le.trans (hed h)) hconc hD0 hD c

/-- **Archimedean evaluation bound for an index-concentrated multihomogeneous polynomial.** If `P`
is multihomogeneous of multidegree `e` with `e h ≤ d h`, coefficients bounded by `B` under `v`, and
support concentrated within `Δ` of `μ` relative to `d`, then `v (eval y P)` is bounded by
`#P.support * B * U ^ (∑ h, e h)` times the concentrated exponential factor. -/
theorem apply_eval_le_of_isMultiHomogeneous_concentrated [DecidableEq κ] (v : AbsoluteValue R ℝ)
    {P : MvPolynomial (κ × ι) R} {e d : κ → ℕ} (hP : P.IsMultiHomogeneous e)
    (hed : ∀ h, e h ≤ d h) {B : ℝ} (hB : ∀ J, v (P.coeff J) ≤ B) {μ Δ : ℝ}
    (hconc : ∀ J, (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → P.coeff J = 0)
    {U : ℝ} {Q : κ → ℝ} (hQ : ∀ h, 0 < Q h)
    {D : ℝ} (hD0 : 0 ≤ D) {E : κ → ℝ} (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    {c : ι → ℝ} {y : κ × ι → R} (hy : ∀ h i, v (y (h, i)) ≤ U * Q h ^ c i) :
    v (eval y P) ≤ #P.support * B * U ^ (∑ h, e h) *
      Real.exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|) := by
  have hB0 : 0 ≤ B := (v.nonneg _).trans (hB 0)
  rw [eval_eq']
  calc v (∑ J ∈ P.support, P.coeff J * ∏ p, y p ^ J p)
      ≤ ∑ J ∈ P.support, v (P.coeff J * ∏ p, y p ^ J p) := v.sum_le _ _
    _ ≤ ∑ _J ∈ P.support, B * (U ^ (∑ h, e h) *
          Real.exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|)) :=
        sum_le_sum fun J hJ ↦ by
          have hJne : P.coeff J ≠ 0 := mem_support_iff.mp hJ
          have hJe : ∀ h, ∑ i, J (h, i) = e h := isMultiHomogeneous_iff.mp hP J hJne
          have hJconc : ∀ i, |(∑ h, (J (h, i) : ℝ) / d h) - μ| ≤ Δ := fun i ↦ by
            by_contra! hlt
            exact hJne (hconc J ⟨i, hlt⟩)
          rw [v.map_mul]
          exact mul_le_mul (hB J)
            (v.apply_prod_pow_le_of_concentrated hJe hed hJconc hQ hD0 hD hy)
            (v.nonneg _) hB0
    _ = #P.support * B * U ^ (∑ h, e h) *
          Real.exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|) := by
        rw [sum_const, nsmul_eq_mul]
        ring

end AbsoluteValue

namespace IsNonarchimedean

variable {R κ ι : Type*} [CommSemiring R] [Fintype κ] [Fintype ι] [DecidableEq κ]

/-- **Nonarchimedean evaluation bound for an index-concentrated multihomogeneous polynomial.** The
ultrametric inequality removes the support cardinality `#P.support` from
`AbsoluteValue.apply_eval_le_of_isMultiHomogeneous_concentrated`. -/
theorem apply_eval_le_of_isMultiHomogeneous_concentrated {v : AbsoluteValue R ℝ}
    (hv : IsNonarchimedean v) {P : MvPolynomial (κ × ι) R} {e d : κ → ℕ}
    (hP : P.IsMultiHomogeneous e) (hed : ∀ h, e h ≤ d h) {B : ℝ} (hB : ∀ J, v (P.coeff J) ≤ B)
    {μ Δ : ℝ} (hconc : ∀ J, (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → P.coeff J = 0)
    {U : ℝ} (hU : 0 ≤ U) {Q : κ → ℝ} (hQ : ∀ h, 0 < Q h)
    {D : ℝ} (hD0 : 0 ≤ D) {E : κ → ℝ} (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    {c : ι → ℝ} {y : κ × ι → R} (hy : ∀ h i, v (y (h, i)) ≤ U * Q h ^ c i) :
    v (eval y P) ≤ B * U ^ (∑ h, e h) *
      Real.exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|) := by
  have hB0 : 0 ≤ B := (v.nonneg _).trans (hB 0)
  rcases P.support.eq_empty_or_nonempty with hP0 | hP0
  · rw [support_eq_empty.mp hP0, map_zero, v.map_zero]
    positivity
  rw [eval_eq']
  refine (hv.apply_sum_le_sup hP0).trans <| sup'_le _ _ fun J hJ ↦ ?_
  have hJne : P.coeff J ≠ 0 := mem_support_iff.mp hJ
  have hJe : ∀ h, ∑ i, J (h, i) = e h := isMultiHomogeneous_iff.mp hP J hJne
  have hJconc : ∀ i, |(∑ h, (J (h, i) : ℝ) / d h) - μ| ≤ Δ := fun i ↦ by
    by_contra! hlt
    exact hJne (hconc J ⟨i, hlt⟩)
  rw [v.map_mul, mul_assoc]
  exact mul_le_mul (hB J) (v.apply_prod_pow_le_of_concentrated hJe hed hJconc hQ hD0 hD hy)
    (v.nonneg _) hB0

/-- Specialization of `IsNonarchimedean.apply_eval_le_of_isMultiHomogeneous_concentrated` to
`U = 1`, as arises for integer linear combinations of points in an approximation domain at a finite
place. -/
theorem apply_eval_le_of_isMultiHomogeneous_concentrated_one {v : AbsoluteValue R ℝ}
    (hv : IsNonarchimedean v) {P : MvPolynomial (κ × ι) R} {e d : κ → ℕ}
    (hP : P.IsMultiHomogeneous e) (hed : ∀ h, e h ≤ d h) {B : ℝ} (hB : ∀ J, v (P.coeff J) ≤ B)
    {μ Δ : ℝ} (hconc : ∀ J, (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → P.coeff J = 0)
    {Q : κ → ℝ} (hQ : ∀ h, 0 < Q h) {D : ℝ} (hD0 : 0 ≤ D) {E : κ → ℝ}
    (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    {c : ι → ℝ} {y : κ × ι → R} (hy : ∀ h i, v (y (h, i)) ≤ Q h ^ c i) :
    v (eval y P) ≤ B *
      Real.exp (D * (μ * ∑ i, c i + Δ * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i|) := by
  simpa using hv.apply_eval_le_of_isMultiHomogeneous_concentrated hP hed hB hconc zero_le_one hQ
    hD0 hD fun h i ↦ by simpa using hy h i

end IsNonarchimedean

/-! ### Examples -/

/-- `0 ≤ D` cannot be dropped in `MvPolynomial.sum_mul_le_of_concentrated`: with `D = -1`, `J = 0`,
`d _ = 1`, `q _ = -1`, `μ = 1`, `Δ = 1` and `c _ = 1`, the sum is `0` while the right-hand side is
`-2`. -/
example :
    let J : Unit × Unit → ℕ := 0
    let d : Unit → ℕ := fun _ ↦ 1
    let q : Unit → ℝ := fun _ ↦ -1
    let E : Unit → ℝ := 0
    let c : Unit → ℝ := fun _ ↦ 1
    (∀ h, ∑ i, J (h, i) ≤ d h) ∧
    (∀ i, |(∑ h, (J (h, i) : ℝ) / d h) - 1| ≤ 1) ∧
    (∀ h, |(d h : ℝ) * q h - (-1)| ≤ E h) ∧
    ¬ ∑ h, ∑ i, (J (h, i) : ℝ) * c i * q h ≤
      (-1 : ℝ) * (1 * ∑ i, c i + 1 * ∑ i, |c i|) + (∑ h, E h) * ∑ i, |c i| := by
  simp

/-- The factor `#P.support` in `AbsoluteValue.apply_eval_le_of_isMultiHomogeneous_concentrated` is
attained at `AbsoluteValue.abs` on `ℝ` by `X (0, 0) + X (0, 1)` evaluated at `1`, where both sides
equal `2`. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 2) ℝ := X (0, 0) + X (0, 1)
    AbsoluteValue.abs (eval (fun _ ↦ (1 : ℝ)) P) =
      #P.support * 1 * (1 : ℝ) ^ (∑ _ : Fin 1, 1) * Real.exp 0 := by
  intro P
  have h01 : (Finsupp.single (0, 0) 1 : Fin 1 × Fin 2 →₀ ℕ) ≠ Finsupp.single (0, 1) 1 := by
    intro h
    have := DFunLike.congr_fun h (0, 0)
    simp at this
  have hsupp : P.support = {Finsupp.single (0, 0) 1, Finsupp.single (0, 1) 1} := by
    ext m
    dsimp only [P]
    rw [← not_iff_not, notMem_support_iff, mem_insert, mem_singleton,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, X, X, coeff_monomial, coeff_monomial]
    split_ifs <;> grind
  rw [hsupp, card_pair h01]
  simp [P]
  norm_num
