/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Sign.Basic
public import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# Positivity of the Markov trace at negative loop parameters

Pulling back Jones's positivity theorem (`TauCeti.Algebra.TemperleyLieb.Positivity`) along the
sign isomorphism `TauCeti.TemperleyLieb.signEquiv` yields the positivity classification at
negative and nonzero real loop parameters:

* **Zero boundary**: over any star-ordered commutative ring, every Markov trace at `δ = 0`
  vanishes on `n > 0` strands and equals `aug` on `0` strands, so the signed forms
  `(-1) ^ n * tr n (star x * x)` are trivially nonnegative
  (`IsMarkovTrace.neg_one_pow_map_star_mul_self_nonneg_of_eq_zero`). Together with
  `zero_notMem_jonesLoopParameters`, this shows that the strict hypothesis `δ < 0` in the
  negative-parameter classification cannot be weakened to `δ ≤ 0`.
* **Negative loop parameters**: for real `δ < 0`, the unsigned trace form fails already on one
  strand (`tr 1 (star 1 * 1) = δ < 0`, `IsMarkovTrace.map_star_one_mul_one_neg`). The signed
  Hermitian forms `(x, y) ↦ (-1) ^ n * tr n (star x * y)` are positive semidefinite for all `n`
  and `x` if and only if `-δ ∈ jonesLoopParameters`
  (`IsMarkovTrace.forall_neg_one_pow_map_star_mul_self_nonneg_iff`). At an inadmissible negative
  loop parameter, positivity fails from level `⌊π / arccos (-δ / 2)⌋` onward
  (`IsMarkovTrace.exists_neg_one_pow_map_star_mul_self_neg`).
* **Unified normalized form**: for any nonzero real `δ ≠ 0`, the normalized Hermitian forms
  `(x, y) ↦ ((δ : ℂ) ^ n)⁻¹ * tr n (star x * y)` are positive semidefinite for all `n` and `x`
  if and only if `|δ| ∈ jonesLoopParameters`
  (`IsMarkovTrace.forall_inv_pow_map_star_mul_self_nonneg_iff`).
* **Positive functionals and radical agreement**: at admissible parameters, the signed and
  normalized traces are bundled as `TauCeti.StarPositiveFunctional`s
  (`IsMarkovTrace.signedPositiveFunctional`, `IsMarkovTrace.normalizedPositiveFunctional`), whose
  trace radicals agree with the unnormalized trace radicals of `tr n` via
  `LinearMap.traceRadical_smul`.
* **Headline theorem**: `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff` proves the
  negative-parameter positivity characterization for `markovTrace q hq` with respect to an
  arbitrary family of conjugate-linear star-ring structures fixing the generators, using uniqueness
  of the analytic adjoint (`TauCeti.TemperleyLieb.star_unique`).

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace.signedPositiveFunctional`: the signed Markov trace
  `((-1 : ℂ) ^ n) • tr n` bundled as a `TauCeti.StarPositiveFunctional` for `δ < 0` with
  `-δ ∈ jonesLoopParameters`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.normalizedPositiveFunctional`: the normalized Markov trace
  `((δ : ℂ) ^ n)⁻¹ • tr n` bundled as a `TauCeti.StarPositiveFunctional` for `δ ≠ 0` with
  `|δ| ∈ jonesLoopParameters`.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.neg_one_pow_map_star_mul_self_nonneg_of_eq_zero`:
  trivial signed positivity at `δ = 0` over any star-ordered commutative ring.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_one_mul_one_neg`: failure of the unsigned form
  on one strand for every real `δ < 0`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.exists_neg_one_pow_map_star_mul_self_neg`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.lt_floor_of_forall_neg_one_pow_nonneg`: threshold for
  failure of signed positivity at inadmissible negative loop parameters.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_map_star_mul_self_nonneg_iff`: Jones's
  positivity theorem at negative real loop parameters for an arbitrary Markov trace.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_inv_pow_map_star_mul_self_nonneg_iff`: unified
  positivity theorem for normalized traces at all nonzero real loop parameters.
* `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`: positivity at negative loop
  parameters for `markovTrace` and any conjugate-linear generator-fixing star structure.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Facts 4.4.14 (TB6), p. 155, and
  Sections 4.3–4.5.
-/

public section

namespace TauCeti.TemperleyLieb

section ZeroParameter

/-- At loop parameter `δ = 0`, the signed Hermitian trace form `(-1) ^ n * tr n (star x * x)` is
trivially positive semidefinite on every number of strands over any star-ordered commutative ring:
on `0` strands the sign is `1`, and on `n > 0` strands the trace vanishes identically. Since
`0 ∉ jonesLoopParameters`, this shows that the strict hypothesis `δ < 0` in
`IsMarkovTrace.forall_neg_one_pow_map_star_mul_self_nonneg_iff` cannot be weakened to `δ ≤ 0`. -/
theorem IsMarkovTrace.neg_one_pow_map_star_mul_self_nonneg_of_eq_zero {R : Type*} [CommRing R]
    [PartialOrder R] [StarRing R] [StarOrderedRing R] {δ : R} [Fact (IsSelfAdjoint δ)]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (hδ : δ = 0) (n : ℕ) (x : TemperleyLieb R δ n) :
    0 ≤ (-1 : R) ^ n * tr n (star x * x) := by
  subst hδ
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa only [pow_zero, one_mul] using htr.map_star_mul_self_nonneg_of_eq_zero rfl 0 x
  · rw [htr.map_eq_zero_of_pos hn, mul_zero]

end ZeroParameter

section NegativePositivity

open scoped ComplexOrder

private theorem exists_map_star_mul_self_neg_of_eq {c : ℝ} {a : ℂ} (ha : a = (c : ℂ))
    [Fact (IsSelfAdjoint a)] {tr' : ∀ n : ℕ, TemperleyLieb ℂ a n →ₗ[ℂ] ℂ}
    (htr' : IsMarkovTrace ℂ a tr') (hc : 0 < c) (hcJ : c ∉ jonesLoopParameters)
    {n : ℕ} (hn : ⌊Real.pi / Real.arccos (c / 2)⌋₊ ≤ n) :
    ∃ y : TemperleyLieb ℂ a n, tr' n (star y * y) < 0 := by
  subst ha
  exact htr'.exists_map_star_mul_self_neg hc hcJ hn

private theorem forall_map_star_mul_self_nonneg_iff_of_eq {c : ℝ} {a : ℂ} (ha : a = (c : ℂ))
    [Fact (IsSelfAdjoint a)] {tr' : ∀ n : ℕ, TemperleyLieb ℂ a n →ₗ[ℂ] ℂ}
    (htr' : IsMarkovTrace ℂ a tr') (hc : 0 < c) :
    (∀ (n : ℕ) (y : TemperleyLieb ℂ a n), 0 ≤ tr' n (star y * y)) ↔
      c ∈ jonesLoopParameters := by
  subst ha
  exact htr'.forall_map_star_mul_self_nonneg_iff hc

namespace IsMarkovTrace

variable {δ : ℝ} [hδ : Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- At every negative real loop parameter `δ < 0`, the unsigned trace form fails already on one
strand: `tr 1 (star 1 * 1) = δ < 0`. -/
theorem map_star_one_mul_one_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδneg : δ < 0) :
    tr 1 (star (1 : TemperleyLieb ℂ (δ : ℂ) 1) * 1) < 0 := by
  rw [star_one, mul_one, htr.map_one, pow_one]
  exact_mod_cast hδneg

/-- **Failure of signed positivity from level `k` on at negative loop parameters.** Let `δ < 0`
be real with `-δ ∉ jonesLoopParameters` and `k = ⌊π / arccos (-δ / 2)⌋`. On every number `n ≥ k`
of strands the signed Hermitian form takes a negative value. -/
theorem exists_neg_one_pow_map_star_mul_self_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) (hδJ : -δ ∉ jonesLoopParameters)
    {n : ℕ} (hn : ⌊Real.pi / Real.arccos (-δ / 2)⌋₊ ≤ n) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, (-1 : ℂ) ^ n * tr n (star x * x) < 0 := by
  have : Fact (IsSelfAdjoint (-(δ : ℂ))) := ⟨hδ.out.neg⟩
  obtain ⟨y, hy⟩ := exists_map_star_mul_self_neg_of_eq (Complex.ofReal_neg δ).symm
    htr.compSignEquivSymm (neg_pos.mpr hδneg) hδJ hn
  refine ⟨(signEquiv (δ : ℂ) n).symm y, ?_⟩
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    smul_eq_mul, map_mul, signEquiv_symm_star] using hy

/-- At an inadmissible negative loop parameter `δ < 0`, the signed Hermitian form on `n` strands
can be positive semidefinite only below level `⌊π / arccos (-δ / 2)⌋`. -/
theorem lt_floor_of_forall_neg_one_pow_nonneg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (h : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    n < ⌊Real.pi / Real.arccos (-δ / 2)⌋₊ := by
  by_contra hn
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_map_star_mul_self_neg hδneg hδJ (not_lt.mp hn)
  exact (h x).not_gt hx

/-- **Jones's positivity theorem at negative loop parameters.** For real `δ < 0`, the signed
Hermitian forms `(x, y) ↦ (-1) ^ n * tr n (star x * y)` of a Markov trace are positive
semidefinite on every number of strands if and only if `-δ` is an admissible loop parameter. -/
theorem forall_neg_one_pow_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) ↔
      -δ ∈ jonesLoopParameters := by
  have : Fact (IsSelfAdjoint (-(δ : ℂ))) := ⟨hδ.out.neg⟩
  rw [← forall_map_star_mul_self_nonneg_iff_of_eq (Complex.ofReal_neg δ).symm
    htr.compSignEquivSymm (neg_pos.mpr hδneg)]
  constructor
  · intro h n y
    simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      smul_eq_mul, map_mul, signEquiv_symm_star] using h n ((signEquiv (δ : ℂ) n).symm y)
  · intro h n x
    have hy := h n (signEquiv (δ : ℂ) n x)
    simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      smul_eq_mul, map_mul, signEquiv_symm_star, AlgEquiv.symm_apply_apply] using hy

/-- **Unified Jones positivity theorem for normalized traces.** For any nonzero real loop
parameter `δ ≠ 0`, the normalized Hermitian forms `(x, y) ↦ ((δ : ℂ) ^ n)⁻¹ * tr n (star x * y)`
are positive semidefinite on every number of strands if and only if `|δ|` is an admissible loop
parameter. -/
theorem forall_inv_pow_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδne : δ ≠ 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ ((δ : ℂ) ^ n)⁻¹ * tr n (star x * x)) ↔
      |δ| ∈ jonesLoopParameters := by
  rcases hδne.lt_or_gt with hneg | hpos
  · rw [abs_of_neg hneg, ← htr.forall_neg_one_pow_map_star_mul_self_nonneg_iff hneg]
    refine forall₂_congr fun n x ↦ ?_
    have hr : (0 : ℂ) < ((((-δ) ^ n)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_pos.mpr (pow_pos (neg_pos.mpr hneg) n)
    have heq : ((δ : ℂ) ^ n)⁻¹ = ((((-δ) ^ n)⁻¹ : ℝ) : ℂ) * (-1 : ℂ) ^ n := by
      have hpow : (δ : ℂ) ^ n = (-1 : ℂ) ^ n * (((-δ) ^ n : ℝ) : ℂ) := by
        push_cast
        rw [← mul_pow, neg_one_mul, neg_neg]
      rw [hpow, mul_inv, mul_comm, Complex.ofReal_inv]
      congr 1
      have hsq : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
      exact inv_eq_of_mul_eq_one_right hsq
    rw [heq, mul_assoc]
    simpa only [mul_zero] using (mul_le_mul_iff_right₀ hr (b := (0 : ℂ)) (c := _))
  · rw [abs_of_pos hpos, ← htr.forall_map_star_mul_self_nonneg_iff hpos]
    refine forall₂_congr fun n x ↦ ?_
    have hr : (0 : ℂ) < (((δ ^ n)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_pos.mpr (pow_pos hpos n)
    have heq : ((δ : ℂ) ^ n)⁻¹ = (((δ ^ n)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [heq]
    simpa only [mul_zero] using (mul_le_mul_iff_right₀ hr (b := (0 : ℂ)) (c := _))

/-- For an admissible negative loop parameter `δ < 0` with `-δ ∈ jonesLoopParameters`, the
signed Markov trace `((-1 : ℂ) ^ n) • tr n` bundled as a `TauCeti.StarPositiveFunctional`. -/
def signedPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) (hmem : -δ ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := ((-1 : ℂ) ^ n) • tr n
  square_nonneg x := by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using
      (htr.forall_neg_one_pow_map_star_mul_self_nonneg_iff hδneg).mpr hmem n x

/-- Evaluation of `signedPositiveFunctional`. -/
@[simp]
theorem signedPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) (hmem : -δ ∈ jonesLoopParameters) (n : ℕ)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.signedPositiveFunctional hδneg hmem n x = (-1 : ℂ) ^ n * tr n x := (rfl)

/-- Evaluation of `signedPositiveFunctional` on `1` is `(-(δ : ℂ)) ^ n`. -/
theorem signedPositiveFunctional_one (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) (hmem : -δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.signedPositiveFunctional hδneg hmem n 1 = (-(δ : ℂ)) ^ n := by
  simp only [signedPositiveFunctional_apply, htr.map_one, ← mul_pow, neg_one_mul]

/-- `signedPositiveFunctional` is tracial. -/
theorem signedPositiveFunctional_mul_comm (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) (hmem : -δ ∈ jonesLoopParameters) (n : ℕ)
    (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.signedPositiveFunctional hδneg hmem n (x * y) =
      htr.signedPositiveFunctional hδneg hmem n (y * x) := by
  simp only [signedPositiveFunctional_apply, htr.map_mul_comm]

/-- The trace radical of `signedPositiveFunctional` coincides with the unnormalized trace radical
of `tr n`. -/
@[simp]
theorem traceRadical_signedPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδneg : δ < 0) (hmem : -δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.signedPositiveFunctional hδneg hmem n).toLinearMap.traceRadical
        (htr.signedPositiveFunctional_mul_comm hδneg hmem n) =
      (tr n).traceRadical (htr.map_mul_comm n) :=
  LinearMap.traceRadical_smul (tr n) (htr.map_mul_comm n) (isUnit_one.neg.pow n).isRegular.left

/-- For any nonzero real loop parameter with `|δ| ∈ jonesLoopParameters`, the normalized Markov
trace `((δ : ℂ) ^ n)⁻¹ • tr n` bundled as a `TauCeti.StarPositiveFunctional`. -/
noncomputable def normalizedPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδne : δ ≠ 0) (hmem : |δ| ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := ((δ : ℂ) ^ n)⁻¹ • tr n
  square_nonneg x := by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using
      (htr.forall_inv_pow_map_star_mul_self_nonneg_iff hδne).mpr hmem n x

/-- Evaluation of `normalizedPositiveFunctional`. -/
@[simp]
theorem normalizedPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδne : δ ≠ 0) (hmem : |δ| ∈ jonesLoopParameters) (n : ℕ)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.normalizedPositiveFunctional hδne hmem n x = ((δ : ℂ) ^ n)⁻¹ * tr n x := (rfl)

/-- The normalized positive functional is unital (`τ_n(1) = 1`). -/
theorem normalizedPositiveFunctional_one (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδne : δ ≠ 0) (hmem : |δ| ∈ jonesLoopParameters) (n : ℕ) :
    htr.normalizedPositiveFunctional hδne hmem n 1 = 1 := by
  simp only [normalizedPositiveFunctional_apply, htr.map_one]
  exact inv_mul_cancel₀ (pow_ne_zero n (Complex.ofReal_ne_zero.mpr hδne))

/-- `normalizedPositiveFunctional` is tracial. -/
theorem normalizedPositiveFunctional_mul_comm (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδne : δ ≠ 0) (hmem : |δ| ∈ jonesLoopParameters) (n : ℕ)
    (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.normalizedPositiveFunctional hδne hmem n (x * y) =
      htr.normalizedPositiveFunctional hδne hmem n (y * x) := by
  simp only [normalizedPositiveFunctional_apply, htr.map_mul_comm]

/-- The trace radical of `normalizedPositiveFunctional` coincides with the unnormalized trace
radical of `tr n`. -/
@[simp]
theorem traceRadical_normalizedPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδne : δ ≠ 0) (hmem : |δ| ∈ jonesLoopParameters) (n : ℕ) :
    (htr.normalizedPositiveFunctional hδne hmem n).toLinearMap.traceRadical
        (htr.normalizedPositiveFunctional_mul_comm hδne hmem n) =
      (tr n).traceRadical (htr.map_mul_comm n) :=
  LinearMap.traceRadical_smul (tr n) (htr.map_mul_comm n)
    (IsUnit.mk0 _ (inv_ne_zero (pow_ne_zero n (Complex.ofReal_ne_zero.mpr hδne)))).isRegular.left

end IsMarkovTrace

/-- **Positivity at negative loop parameters.** Let `δ < 0` be real and let `q : ℂˣ` satisfy
`δ = -(q + q⁻¹)`. For any family of conjugate-linear star-ring structures on
`TemperleyLieb ℂ (δ : ℂ) n` fixing the generators `e (δ : ℂ) i`, the signed closure forms
`(-1) ^ n * markovTrace q hq (star x * x)` are real and nonnegative for every `n` and `x` if and
only if `-δ` lies in the Jones loop parameters `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`. -/
theorem markovTrace_neg_one_pow_nonneg_iff {δ : ℝ} (hδ : δ < 0) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)))
    [s : ∀ n, StarRing (TemperleyLieb ℂ (δ : ℂ) n)]
    [sm : ∀ n, StarModule ℂ (TemperleyLieb ℂ (δ : ℂ) n)]
    (he : ∀ (n : ℕ) (i : Fin (n - 1)), star (e (δ : ℂ) i) = e (δ : ℂ) i) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1 : ℂ) ^ n * markovTrace q hq (star x * x)) ↔
      (∃ m : ℕ, 3 ≤ m ∧ -δ = 2 * Real.cos (Real.pi / m)) ∨ 2 ≤ -δ := by
  have hself : Fact (IsSelfAdjoint (δ : ℂ)) := ⟨Complex.conj_ofReal δ⟩
  have hstar : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
      (s n).star x = @star _ (@instStarRing ℂ _ _ (δ : ℂ) n hself).toStar x := fun n x ↦
    congrFun (@star_unique ℂ _ _ (δ : ℂ) n hself (s n).star (s n).star_add (s n).star_mul
      (sm n).star_smul (@star_one _ _ (s n).toStarMul) (he n)) x
  have hequiv :
      (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
          0 ≤ (-1 : ℂ) ^ n * markovTrace q hq ((s n).star x * x)) ↔
        ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
          0 ≤ (-1 : ℂ) ^ n * markovTrace q hq
            (@star _ (@instStarRing ℂ _ _ (δ : ℂ) n hself).toStar x * x) := by
    refine forall₂_congr fun n x ↦ ?_
    rw [hstar n x]
  rw [← mem_jonesLoopParameters]
  exact hequiv.trans
    ((isMarkovTrace_markovTrace q hq).forall_neg_one_pow_map_star_mul_self_nonneg_iff
      (hδ := hself) hδ)

end NegativePositivity

section Checks

open scoped ComplexOrder

-- Check `n = 1` and `n = 2, x = e`: trace scaling requires the sign factor `(-1) ^ n`.
example {R : Type*} [CommRing R] {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') :
    tr 1 1 = δ ∧ (-1 : R) * tr' 1 (signEquiv δ 1 1) = δ ∧
      tr 2 (e δ 0) = δ ∧ (-1 : R) ^ 2 * tr' 2 (signEquiv δ 2 (e δ 0)) = δ := by
  refine ⟨by simp [htr.map_one], ?_, by simp [htr.map_e], ?_⟩
  · rw [htr.map_signEquiv htr', htr.map_one]
    ring
  · rw [htr.map_signEquiv htr', htr.map_e]
    ring

-- Check `δ = -2`: admissible (`-(-2) = 2`), signed forms are nonnegative at all `n`,
-- while the unsigned form fails at `n = 1`.
example {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ = -2)
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) ∧
      tr 1 (star (1 : TemperleyLieb ℂ (δ : ℂ) 1) * 1) < 0 := by
  subst hδ
  refine ⟨(htr.forall_neg_one_pow_map_star_mul_self_nonneg_iff (by norm_num)).mpr ?_,
    htr.map_star_one_mul_one_neg (by norm_num)⟩
  rw [mem_jonesLoopParameters]
  exact Or.inr (by norm_num)

-- Check `δ = -1/2`: `1/2 ∉ jonesLoopParameters`, `f_2 = 1 + 2 • e 0`,
-- `signEquiv (-1/2) 2 f_2 = jonesWenzl (1/2) 2`, and `(-1)^2 * tr 2 (f_2⋆ * f_2) = -3/4 < 0`.
example {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ = -(1 / 2))
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    (1 / 2 : ℝ) ∉ jonesLoopParameters ∧
      jonesWenzl (δ : ℂ) 2 = 1 + (2 : ℂ) • e (δ : ℂ) 0 ∧
      signEquiv (δ : ℂ) 2 (jonesWenzl (δ : ℂ) 2) = jonesWenzl (-(δ : ℂ)) 2 ∧
      (-1 : ℂ) ^ 2 * tr 2 (star (jonesWenzl (δ : ℂ) 2) * jonesWenzl (δ : ℂ) 2) = -(3 / 4 : ℂ) := by
  subst hδ
  refine ⟨fun h ↦ by linarith [one_le_of_mem_jonesLoopParameters h], ?_,
    signEquiv_jonesWenzl _ 2, ?_⟩
  · rw [jonesWenzl_two, Ring.inverse_eq_inv']
    push_cast
    norm_num
  · have hunits : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ ((-(1 / 2) : ℝ) : ℂ) k) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      interval_cases k
      · simp
      · simp only [qInt_two, isUnit_iff_ne_zero]
        push_cast
        norm_num
    rw [htr.map_star_jonesWenzl_mul_jonesWenzl hunits, qInt_add_two, qInt_two, qInt_one]
    push_cast
    norm_num

end Checks

end TauCeti.TemperleyLieb
