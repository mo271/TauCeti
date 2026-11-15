/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.ShiftedLaplace

import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.Asymptotics.Sum.StolzCesaro
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Legendre's continued fraction for the upper incomplete Gamma function (DLMF 8.9.2)

For complex parameters `a, z : ℂ`, Legendre's continued fraction for `z ^ (-a) * exp z * Γ(a, z)`
(DLMF 8.9.2), written in unit-partial-denominator form `0 + K_{n=1}^∞ (aₙ / 1)`, has partial
numerators

* `a₁ = z⁻¹`,
* `a₂ₖ = (k - a) * z⁻¹` for `k ≥ 1`,
* `a₂ₖ₊₁ = k * z⁻¹` for `k ≥ 1`.

We construct the generalized continued fraction `Complex.upperIncompleteGammaContFrac a z`, exhibit
its explicit integral recurrence solution `Complex.upperIncompleteGammaContFracSolution a z` built
from the analytic continuation `TauCeti.shiftedLaplaceIntegral` on `Complex.slitPlane`, prove the
terminating evaluations at positive integers `a = m + 1` (in particular `z⁻¹` after one level at
`a = 1`), establish divergence of the Pincherle reduction-of-order series via saddle-point
asymptotics and Stolz--Cesàro summation when `a ∉ {1, 2, 3, ...}`, and deduce eventual
nonvanishing of denominators and convergence of the convergents on `Complex.slitPlane` for every
`a : ℂ` (handling `a = m + 1` via a tail-continuant shift to `-(m : ℂ)`).

## Main definitions

* `Complex.upperIncompleteGammaPartNum`: the partial numerators `aₙ` of Legendre's continued
  fraction (DLMF 8.9.2) in unit-denominator normalization.
* `Complex.upperIncompleteGammaContFrac`: the `GenContFract ℂ` representing
  `0 + K_{n=1}^∞ (aₙ / 1)`.
* `Complex.upperIncompleteGammaContFracSolution`: the minimal solution of the three-term recurrence
  `f (n + 2) = f (n + 1) + a_{n + 1} * f n` expressed via `TauCeti.shiftedLaplaceIntegral`.

## Main results

* `Complex.upperIncompleteGammaContFracSolution_add_two`: `upperIncompleteGammaContFracSolution a z`
  satisfies the three-term recurrence on `Complex.slitPlane`.
* `Complex.upperIncompleteGammaContFrac_convs'_one_left`,
  `Complex.upperIncompleteGammaContFrac_convs_one_left_one`: at `a = 1`, Legendre's continued
  fraction terminates after one level with value `z⁻¹`.
* `Complex.upperIncompleteGammaContFrac_nums_natCast_add_one`: at `a = m + 1`,
  `nums n = shiftedLaplaceIntegral 0 m z * dens n` for all `z : ℂ` and `n ≥ 2 * m + 1`.
* `Complex.tendsto_norm_sum_upperIncompleteGammaContFrac_reductionOfOrder`: for
  `∀ m : ℕ, a ≠ (m : ℂ) + 1` and `z ∈ Complex.slitPlane`, the Pincherle reduction-of-order partial
  sums diverge in norm to `+∞`.
* `Complex.tendsto_upperIncompleteGammaContFrac_convs`: for every `a : ℂ` and
  `z ∈ Complex.slitPlane`, `(upperIncompleteGammaContFrac a z).dens` is eventually nonzero and
  `(upperIncompleteGammaContFrac a z).convs` converges to
  `TauCeti.shiftedLaplaceIntegral 0 (a - 1) z` (DLMF 8.9.2).
* `Complex.tendsto_upperIncompleteGammaContFrac_convs_of_re_pos`: specialization to `{z | 0 < z.re}`
  converging to `∫ t in Ioi 0, exp (-z * t) * (1 + t) ^ (a - 1)`.

## References

* NIST Digital Library of Mathematical Functions, 8.9.2, <https://dlmf.nist.gov/8.9.E2>.
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. **9** (1967),
  24--82.
* L. Lorentzen and H. Waadeland, *Continued Fractions with Applications*, North-Holland, 1992.
-/

public section

noncomputable section

open Filter Polynomial Finset Asymptotics
open scoped Nat Topology

namespace Complex

/-- Partial numerators `aₙ` (`n ≥ 1`) of Legendre's continued fraction for
`z ^ (-a) * exp z * Γ(a, z)` (DLMF 8.9.2) in unit-denominator form `0 + K_{n=1}^∞ (aₙ / 1)`:
`a₁ = z⁻¹`, `a₂ₖ = (k - a) * z⁻¹`, and `a₂ₖ₊₁ = k * z⁻¹` for `k ≥ 1` (with `a₀ = 0`). -/
def upperIncompleteGammaPartNum (a z : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => z⁻¹
  | n + 2 =>
    if (n + 2) % 2 = 0 then (((n + 2) / 2 : ℕ) - a) * z⁻¹
    else (((n + 2) / 2 : ℕ) : ℂ) * z⁻¹

@[simp]
theorem upperIncompleteGammaPartNum_zero (a z : ℂ) :
    upperIncompleteGammaPartNum a z 0 = 0 := by
  rw [upperIncompleteGammaPartNum]

@[simp]
theorem upperIncompleteGammaPartNum_one (a z : ℂ) :
    upperIncompleteGammaPartNum a z 1 = z⁻¹ := by
  rw [upperIncompleteGammaPartNum]

@[simp]
theorem upperIncompleteGammaPartNum_two_mul_succ (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaPartNum a z (2 * (k + 1)) = (((k + 1 : ℕ) : ℂ) - a) * z⁻¹ := by
  change upperIncompleteGammaPartNum a z (2 * k + 2) = _
  rw [upperIncompleteGammaPartNum]
  have hmod : (2 * k + 2) % 2 = 0 := by omega
  have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
  simp only [hmod, ↓reduceIte, hdiv]

@[simp]
theorem upperIncompleteGammaPartNum_two_mul_succ_add_one (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaPartNum a z (2 * (k + 1) + 1) = ((k + 1 : ℕ) : ℂ) * z⁻¹ := by
  change upperIncompleteGammaPartNum a z ((2 * k + 1) + 2) = _
  rw [upperIncompleteGammaPartNum]
  have hmod : (2 * k + 1 + 2) % 2 ≠ 0 := by omega
  have hdiv : (2 * k + 1 + 2) / 2 = k + 1 := by omega
  simp only [hmod, ↓reduceIte, hdiv]

/-- Legendre's generalized continued fraction `0 + K_{n=1}^∞ (aₙ / 1)` for
`z ^ (-a) * exp z * Γ(a, z)` (DLMF 8.9.2), with unit partial denominators and partial numerators
`Complex.upperIncompleteGammaPartNum a z (n + 1)`. -/
def upperIncompleteGammaContFrac (a z : ℂ) : GenContFract ℂ :=
  ⟨0, Stream'.Seq.ofStream fun n ↦ ⟨upperIncompleteGammaPartNum a z (n + 1), 1⟩⟩

@[simp]
theorem upperIncompleteGammaContFrac_h (a z : ℂ) :
    (upperIncompleteGammaContFrac a z).h = 0 := by
  rw [upperIncompleteGammaContFrac]

@[simp]
theorem upperIncompleteGammaContFrac_s_get? (a z : ℂ) (n : ℕ) :
    (upperIncompleteGammaContFrac a z).s.get? n =
      some ⟨upperIncompleteGammaPartNum a z (n + 1), 1⟩ := by
  rw [upperIncompleteGammaContFrac]
  rfl

/-- Explicit integral solution `fₙ` of the three-term recurrence
`f (n + 2) = f (n + 1) + upperIncompleteGammaPartNum a z (n + 1) * f n` associated with Legendre's
continued fraction (DLMF 8.9.2), normalized by `f 0 = 1` and
`f 1 = -TauCeti.shiftedLaplaceIntegral 0 (a - 1) z`. -/
def upperIncompleteGammaContFracSolution (a z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
    let k := (n + 1) / 2
    if (n + 1) % 2 = 0 then
      (ascPochhammer ℂ k).eval (1 - a) * (z⁻¹) ^ k *
        TauCeti.shiftedLaplaceIntegral (k - 1) (a - 1 - (k : ℂ)) z
    else
      -(ascPochhammer ℂ k).eval (1 - a) * (z⁻¹) ^ k *
        TauCeti.shiftedLaplaceIntegral k (a - 1 - (k : ℂ)) z

@[simp]
theorem upperIncompleteGammaContFracSolution_zero (a z : ℂ) :
    upperIncompleteGammaContFracSolution a z 0 = 1 := by
  rw [upperIncompleteGammaContFracSolution]

theorem upperIncompleteGammaContFracSolution_two_mul_succ (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaContFracSolution a z (2 * (k + 1)) =
      (ascPochhammer ℂ (k + 1)).eval (1 - a) * (z⁻¹) ^ (k + 1) *
        TauCeti.shiftedLaplaceIntegral k (a - 2 - (k : ℂ)) z := by
  change upperIncompleteGammaContFracSolution a z ((2 * k + 1) + 1) = _
  rw [upperIncompleteGammaContFracSolution]
  have hmod : (2 * k + 1 + 1) % 2 = 0 := by omega
  have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [hmod, ↓reduceIte, hdiv, Nat.add_sub_cancel]
  congr 2
  push_cast
  ring

theorem upperIncompleteGammaContFracSolution_two_mul_add_one (a z : ℂ) (k : ℕ) :
    upperIncompleteGammaContFracSolution a z (2 * k + 1) =
      -(ascPochhammer ℂ k).eval (1 - a) * (z⁻¹) ^ k *
        TauCeti.shiftedLaplaceIntegral k (a - 1 - (k : ℂ)) z := by
  rw [upperIncompleteGammaContFracSolution]
  have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp only [hmod, ↓reduceIte, hdiv]

@[simp]
theorem upperIncompleteGammaContFracSolution_one (a z : ℂ) :
    upperIncompleteGammaContFracSolution a z 1 =
      -TauCeti.shiftedLaplaceIntegral 0 (a - 1) z := by
  simpa using upperIncompleteGammaContFracSolution_two_mul_add_one a z 0

/-- Initial-ratio identity `-f 1 / f 0 = TauCeti.shiftedLaplaceIntegral 0 (a - 1) z`. -/
theorem neg_div_upperIncompleteGammaContFracSolution (a z : ℂ) :
    -upperIncompleteGammaContFracSolution a z 1 / upperIncompleteGammaContFracSolution a z 0 =
      TauCeti.shiftedLaplaceIntegral 0 (a - 1) z := by
  simp

/-- **Three-term recurrence** for `Complex.upperIncompleteGammaContFracSolution` on
`Complex.slitPlane`. -/
theorem upperIncompleteGammaContFracSolution_add_two (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (n : ℕ) :
    upperIncompleteGammaContFracSolution a z (n + 2) =
      upperIncompleteGammaContFracSolution a z (n + 1) +
        upperIncompleteGammaPartNum a z (n + 1) * upperIncompleteGammaContFracSolution a z n := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases k with _ | c
    · simp only [zero_add, upperIncompleteGammaContFracSolution_zero,
        upperIncompleteGammaContFracSolution_one, upperIncompleteGammaPartNum_one, mul_one]
      rw [show (2 : ℕ) = 2 * (0 + 1) from rfl, upperIncompleteGammaContFracSolution_two_mul_succ,
        ascPochhammer_one, eval_X, pow_one, Nat.cast_zero, sub_zero]
      have hrec := TauCeti.mul_shiftedLaplaceIntegral_zero (a - 1) hz
      rw [show a - 1 - 1 = a - 2 by ring] at hrec
      have hK0 : TauCeti.shiftedLaplaceIntegral 0 (a - 1) z =
          z⁻¹ * (1 + (a - 1) * TauCeti.shiftedLaplaceIntegral 0 (a - 2) z) := by
        rw [← hrec, inv_mul_cancel_left₀ hz0]
      rw [hK0]
      ring
    · rw [show c + 1 + (c + 1) = 2 * (c + 1) by ring,
        show 2 * (c + 1) + 2 = 2 * ((c + 1) + 1) by ring,
        upperIncompleteGammaContFracSolution_two_mul_succ a z (c + 1),
        upperIncompleteGammaContFracSolution_two_mul_add_one a z (c + 1),
        upperIncompleteGammaContFracSolution_two_mul_succ a z c,
        upperIncompleteGammaPartNum_two_mul_succ_add_one a z c, ascPochhammer_succ_eval,
        show a - 1 - ((c + 1 : ℕ) : ℂ) = a - 2 - (c : ℂ) by push_cast; ring]
      have hrec := TauCeti.mul_shiftedLaplaceIntegral_succ c (a - 2 - (c : ℂ)) hz
      rw [show a - 2 - (c : ℂ) - 1 = a - 2 - ((c + 1 : ℕ) : ℂ) by push_cast; ring] at hrec
      have hK1 : TauCeti.shiftedLaplaceIntegral (c + 1) (a - 2 - (c : ℂ)) z =
          z⁻¹ * (((c + 1 : ℕ) : ℂ) * TauCeti.shiftedLaplaceIntegral c (a - 2 - (c : ℂ)) z +
            (a - 2 - (c : ℂ)) *
              TauCeti.shiftedLaplaceIntegral (c + 1) (a - 2 - ((c + 1 : ℕ) : ℂ)) z) := by
        rw [← hrec, inv_mul_cancel_left₀ hz0]
      rw [hK1, pow_succ _ (c + 1)]
      push_cast
      ring
  · rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring,
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
      upperIncompleteGammaContFracSolution_two_mul_add_one a z (k + 1),
      upperIncompleteGammaContFracSolution_two_mul_succ a z k,
      upperIncompleteGammaContFracSolution_two_mul_add_one a z k,
      upperIncompleteGammaPartNum_two_mul_succ a z k, ascPochhammer_succ_eval,
      show a - 1 - ((k + 1 : ℕ) : ℂ) = a - 2 - (k : ℂ) by push_cast; ring]
    have hsub := TauCeti.shiftedLaplaceIntegral_sub k (a - 1 - (k : ℂ)) hz
    rw [show a - 1 - (k : ℂ) - 1 = a - 2 - (k : ℂ) by ring] at hsub
    rw [← hsub, pow_succ]
    push_cast
    ring

/-- Continuant decomposition `f (n + 1) = g.nums n + f 1 * g.dens n` relating the recurrence
solution `upperIncompleteGammaContFracSolution a z` to the numerators and denominators of
`upperIncompleteGammaContFrac a z`. -/
theorem upperIncompleteGammaContFracSolution_succ_eq_nums_add_dens (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (n : ℕ) :
    upperIncompleteGammaContFracSolution a z (n + 1) =
      (upperIncompleteGammaContFrac a z).nums n +
        upperIncompleteGammaContFracSolution a z 1 *
          (upperIncompleteGammaContFrac a z).dens n := by
  refine Nat.strong_induction_on n fun n ih ↦ ?_
  rcases n with _ | _ | m
  · simp
  · have hs0 := upperIncompleteGammaContFrac_s_get? a z 0
    rw [GenContFract.first_num_eq hs0, GenContFract.first_den_eq hs0,
      upperIncompleteGammaContFracSolution_add_two a hz 0]
    simp [add_comm]
  · have hsm := upperIncompleteGammaContFrac_s_get? a z (m + 1)
    rw [GenContFract.nums_recurrence hsm rfl rfl, GenContFract.dens_recurrence hsm rfl rfl,
      one_mul, one_mul, upperIncompleteGammaContFracSolution_add_two a hz (m + 1),
      ih m (by omega), ih (m + 1) (by omega)]
    ring

/-- First convergent `(upperIncompleteGammaContFrac 1 z).convs 1 = z⁻¹` at `a = 1`. -/
@[simp]
theorem upperIncompleteGammaContFrac_convs_one_left_one (z : ℂ) :
    (upperIncompleteGammaContFrac 1 z).convs 1 = z⁻¹ := by
  have hs0 := upperIncompleteGammaContFrac_s_get? 1 z 0
  rw [GenContFract.conv_eq_num_div_den, GenContFract.first_num_eq hs0,
    GenContFract.first_den_eq hs0]
  simp

/-- Second convergent `(upperIncompleteGammaContFrac 1 z).convs 2 = z⁻¹` at `a = 1`. -/
@[simp]
theorem upperIncompleteGammaContFrac_convs_one_left_two (z : ℂ) :
    (upperIncompleteGammaContFrac 1 z).convs 2 = z⁻¹ := by
  have hs0 := upperIncompleteGammaContFrac_s_get? 1 z 0
  have hs1 := upperIncompleteGammaContFrac_s_get? 1 z 1
  rw [GenContFract.conv_eq_num_div_den, GenContFract.nums_recurrence hs1 rfl rfl,
    GenContFract.dens_recurrence hs1 rfl rfl, GenContFract.first_num_eq hs0,
    GenContFract.first_den_eq hs0, show (1 + 1 : ℕ) = 2 * (0 + 1) from rfl,
    upperIncompleteGammaPartNum_two_mul_succ]
  simp

/-- For `a = 1`, every numerator from index `1` onward satisfies `nums n = z⁻¹ * dens n`. -/
theorem upperIncompleteGammaContFrac_nums_one_left (z : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (upperIncompleteGammaContFrac 1 z).nums n =
      z⁻¹ * (upperIncompleteGammaContFrac 1 z).dens n := by
  revert hn
  refine Nat.strong_induction_on n fun n ih hn ↦ ?_
  rcases n with _ | _ | _ | m
  · omega
  · have hs0 := upperIncompleteGammaContFrac_s_get? 1 z 0
    rw [GenContFract.first_num_eq hs0, GenContFract.first_den_eq hs0]; simp
  · have hs0 := upperIncompleteGammaContFrac_s_get? 1 z 0
    have hs1 := upperIncompleteGammaContFrac_s_get? 1 z 1
    rw [GenContFract.nums_recurrence hs1 rfl rfl, GenContFract.dens_recurrence hs1 rfl rfl,
      GenContFract.first_num_eq hs0, GenContFract.first_den_eq hs0,
      show (1 + 1 : ℕ) = 2 * (0 + 1) from rfl, upperIncompleteGammaPartNum_two_mul_succ]
    simp
  · have hsm := upperIncompleteGammaContFrac_s_get? 1 z (m + 2)
    rw [GenContFract.nums_recurrence hsm rfl rfl, GenContFract.dens_recurrence hsm rfl rfl,
      ih (m + 1) (by omega) (by omega), ih (m + 2) (by omega) (by omega)]
    ring

/-- Helper: if the head pair of `s` has partial numerator `0`, `GenContFract.convs'Aux s k = 0`. -/
private theorem convs'Aux_eq_zero_of_head_zero {s : Stream'.Seq (GenContFract.Pair ℂ)} {b : ℂ}
    (hs : s.head = some ⟨0, b⟩) (k : ℕ) : GenContFract.convs'Aux s k = 0 := by
  cases k with
  | zero => rfl
  | succ k => simp [GenContFract.convs'Aux, hs]

/-- **DLMF 8.9.2 at `a = 1` (terminating evaluation)**: direct evaluation of Legendre's continued
fraction at `a = 1` terminates after one level with value `z⁻¹` for all `z : ℂ` and `1 ≤ n`. -/
theorem upperIncompleteGammaContFrac_convs'_one_left (z : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (upperIncompleteGammaContFrac 1 z).convs' n = z⁻¹ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 k, GenContFract.convs', upperIncompleteGammaContFrac_h, zero_add]
  have hhead0 : (upperIncompleteGammaContFrac 1 z).s.head = some ⟨z⁻¹, 1⟩ := rfl
  have hhead1 : (upperIncompleteGammaContFrac 1 z).s.tail.head = some ⟨0, 1⟩ := by
    change (upperIncompleteGammaContFrac 1 z).s.get? 1 = some ⟨0, 1⟩
    rw [upperIncompleteGammaContFrac_s_get?, show (1 + 1 : ℕ) = 2 * (0 + 1) from rfl,
      upperIncompleteGammaPartNum_two_mul_succ]
    simp
  rw [GenContFract.convs'Aux, hhead0, convs'Aux_eq_zero_of_head_zero hhead1 k]
  simp

/-- At every positive integer `a = m + 1`, the `(2 * m + 2)`-nd partial numerator vanishes, so
`GenContFract.convs'` stabilizes at level `2 * m + 1` for all `z : ℂ`. -/
theorem upperIncompleteGammaContFrac_convs'_natCast_add_one_stable (m : ℕ) (z : ℂ) {n : ℕ}
    (hn : 2 * m + 1 ≤ n) :
    (upperIncompleteGammaContFrac ((m : ℂ) + 1) z).convs' n =
      (upperIncompleteGammaContFrac ((m : ℂ) + 1) z).convs' (2 * m + 1) := by
  suffices h : ∀ (j : ℕ) (s : Stream'.Seq (GenContFract.Pair ℂ)),
      s.get? j = some ⟨0, 1⟩ → ∀ k ≥ j, GenContFract.convs'Aux s k = GenContFract.convs'Aux s j by
    rw [GenContFract.convs', GenContFract.convs']
    congr 1
    refine h (2 * m + 1) _ ?_ n hn
    rw [upperIncompleteGammaContFrac_s_get?, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
      upperIncompleteGammaPartNum_two_mul_succ]
    push_cast; ring_nf
  intro j
  induction j with
  | zero =>
    intro s hs0 k _
    have hhead : s.head = some ⟨0, 1⟩ := hs0
    rw [convs'Aux_eq_zero_of_head_zero hhead k, convs'Aux_eq_zero_of_head_zero hhead 0]
  | succ j ih =>
    intro s hsj k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have htail : s.tail.get? j = some ⟨0, 1⟩ := by rwa [Stream'.Seq.get?_tail]
    simp only [GenContFract.convs'Aux]
    cases s.head with
    | none => rfl
    | some gp => rw [ih s.tail htail k' (by omega)]

/-- At `a = m + 1`, the recurrence solution vanishes from index `2 * m + 2` onward. -/
theorem upperIncompleteGammaContFracSolution_natCast_add_one_eq_zero (m : ℕ) (z : ℂ)
    {n : ℕ} (hn : 2 * m + 2 ≤ n) :
    upperIncompleteGammaContFracSolution ((m : ℂ) + 1) z n = 0 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    rw [show c + 1 + (c + 1) = 2 * (c + 1) by ring,
      upperIncompleteGammaContFracSolution_two_mul_succ,
      show (1 : ℂ) - ((m : ℂ) + 1) = -(m : ℂ) by ring,
      ascPochhammer_eval_neg_natCast_of_lt (by omega : m < c + 1), zero_mul, zero_mul]
  · rw [upperIncompleteGammaContFracSolution_two_mul_add_one,
      show (1 : ℂ) - ((m : ℂ) + 1) = -(m : ℂ) by ring,
      ascPochhammer_eval_neg_natCast_of_lt (by omega : m < k), neg_zero, zero_mul, zero_mul]

/-- Entirety of `w ↦ (upperIncompleteGammaContFrac a w⁻¹).nums n` and `.dens n`. -/
private theorem differentiable_nums_dens_inv (a : ℂ) (n : ℕ) :
    Differentiable ℂ (fun w : ℂ ↦ (upperIncompleteGammaContFrac a w⁻¹).nums n) ∧
      Differentiable ℂ (fun w : ℂ ↦ (upperIncompleteGammaContFrac a w⁻¹).dens n) := by
  have hpart : ∀ j : ℕ, Differentiable ℂ (fun w : ℂ ↦ upperIncompleteGammaPartNum a w⁻¹ j) := by
    intro j
    rcases j with _ | _ | k
    · simp
    · simp [upperIncompleteGammaPartNum]
    · simp only [upperIncompleteGammaPartNum, inv_inv]
      split_ifs <;> fun_prop
  refine Nat.strong_induction_on n fun n ih ↦ ?_
  rcases n with _ | _ | k
  · simp [differentiable_const]
  · have hs0 : ∀ w : ℂ, (upperIncompleteGammaContFrac a w⁻¹).s.get? 0 =
        some ⟨upperIncompleteGammaPartNum a w⁻¹ 1, 1⟩ := fun w ↦
      upperIncompleteGammaContFrac_s_get? a w⁻¹ 0
    simp only [fun w ↦ GenContFract.first_num_eq (hs0 w),
      fun w ↦ GenContFract.first_den_eq (hs0 w), upperIncompleteGammaContFrac_h, mul_zero,
      zero_add]
    exact ⟨hpart 1, differentiable_const 1⟩
  · have hsk : ∀ w : ℂ, (upperIncompleteGammaContFrac a w⁻¹).s.get? (k + 1) =
        some ⟨upperIncompleteGammaPartNum a w⁻¹ (k + 2), 1⟩ := fun w ↦
      upperIncompleteGammaContFrac_s_get? a w⁻¹ (k + 1)
    simp only [fun w ↦ GenContFract.nums_recurrence (hsk w) rfl rfl,
      fun w ↦ GenContFract.dens_recurrence (hsk w) rfl rfl, one_mul]
    exact ⟨(ih (k + 1) (by omega)).1.add ((hpart (k + 2)).mul (ih k (by omega)).1),
      (ih (k + 1) (by omega)).2.add ((hpart (k + 2)).mul (ih k (by omega)).2)⟩

/-- At every positive integer `a = m + 1`, all numerators and denominators from level
`2 * m + 1` onward satisfy `nums n = shiftedLaplaceIntegral 0 m z * dens n` for every `z : ℂ`. -/
theorem upperIncompleteGammaContFrac_nums_natCast_add_one (m : ℕ) (z : ℂ) {n : ℕ}
    (hn : 2 * m + 1 ≤ n) :
    (upperIncompleteGammaContFrac ((m : ℂ) + 1) z).nums n =
      TauCeti.shiftedLaplaceIntegral 0 m z *
        (upperIncompleteGammaContFrac ((m : ℂ) + 1) z).dens n := by
  have hslit : ∀ {ζ : ℂ}, ζ ∈ slitPlane →
      (upperIncompleteGammaContFrac ((m : ℂ) + 1) ζ).nums n =
        TauCeti.shiftedLaplaceIntegral 0 m ζ *
          (upperIncompleteGammaContFrac ((m : ℂ) + 1) ζ).dens n := by
    intro ζ hζ
    have hsol := upperIncompleteGammaContFracSolution_succ_eq_nums_add_dens ((m : ℂ) + 1) hζ n
    rw [upperIncompleteGammaContFracSolution_natCast_add_one_eq_zero m ζ (by omega),
      upperIncompleteGammaContFracSolution_one, add_sub_cancel_right] at hsol
    linear_combination -hsol
  set F : ℂ → ℂ := fun w ↦ (upperIncompleteGammaContFrac ((m : ℂ) + 1) w⁻¹).nums n
  set G : ℂ → ℂ := fun w ↦
    (∑ j ∈ Finset.range (m + 1), (m.descFactorial j : ℂ) * w ^ (j + 1)) *
      (upperIncompleteGammaContFrac ((m : ℂ) + 1) w⁻¹).dens n
  have hF : Differentiable ℂ F := (differentiable_nums_dens_inv ((m : ℂ) + 1) n).1
  have hpoly : Differentiable ℂ
      (fun w : ℂ ↦ ∑ j ∈ Finset.range (m + 1), (m.descFactorial j : ℂ) * w ^ (j + 1)) := by
    fun_prop
  have hG : Differentiable ℂ G := hpoly.mul (differentiable_nums_dens_inv ((m : ℂ) + 1) n).2
  have hlin : Differentiable ℂ (fun s : ℂ ↦ (1 : ℂ) + I * s) := by fun_prop
  have heq := Differentiable.eq_of_ofReal_eq (hF.comp hlin) (hG.comp hlin) fun t ↦ by
    have hre : 0 < (((1 : ℂ) + I * (t : ℂ))⁻¹).re := by
      have h1 : 0 < ((1 : ℂ) + I * (t : ℂ)).re := by simp
      rw [inv_re]
      exact div_pos h1 (normSq_pos.mpr fun h0 ↦ by simp [h0] at h1)
    dsimp only [Function.comp_apply, F, G]
    rw [hslit (Or.inl hre), TauCeti.shiftedLaplaceIntegral_zero_natCast]
    simp only [inv_inv]
  have key := congrFun heq (-I * (z⁻¹ - 1))
  have harg : (1 : ℂ) + I * (-I * (z⁻¹ - 1)) = z⁻¹ := by
    calc (1 : ℂ) + I * (-I * (z⁻¹ - 1)) = 1 - (I * I) * (z⁻¹ - 1) := by ring
      _ = z⁻¹ := by rw [I_mul_I]; ring
  dsimp only [Function.comp_apply, F, G] at key
  rw [harg, inv_inv] at key
  rwa [TauCeti.shiftedLaplaceIntegral_zero_natCast]

/-- Closed form of the even product
`∏ j ∈ Icc 1 (2 * (m + 1)), upperIncompleteGammaPartNum a z j`. -/
private theorem prod_upperIncompleteGammaPartNum_two_mul_succ (a z : ℂ) (m : ℕ) :
    (∏ j ∈ Finset.Icc 1 (2 * (m + 1)), upperIncompleteGammaPartNum a z j) =
      (m ! : ℂ) * (ascPochhammer ℂ (m + 1)).eval (1 - a) * (z⁻¹) ^ (2 * (m + 1)) := by
  induction m with
  | zero =>
    rw [show 2 * (0 + 1) = 1 + 1 from rfl, Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 1 + 1),
      Finset.Icc_self, Finset.prod_singleton, upperIncompleteGammaPartNum_one,
      show (1 + 1 : ℕ) = 2 * (0 + 1) from rfl, upperIncompleteGammaPartNum_two_mul_succ]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, ascPochhammer_one, eval_X, zero_add]
    ring
  | succ m ih =>
    have hpch : (ascPochhammer ℂ (m + 1 + 1)).eval (1 - a) =
        (ascPochhammer ℂ (m + 1)).eval (1 - a) * (1 - a + ((m + 1 : ℕ) : ℂ)) :=
      ascPochhammer_succ_eval _ _
    rw [show 2 * (m + 1 + 1) = (2 * (m + 1) + 1) + 1 by ring,
      Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega), ih,
      upperIncompleteGammaPartNum_two_mul_succ_add_one,
      show (2 * (m + 1) + 1) + 1 = 2 * ((m + 1) + 1) by ring,
      upperIncompleteGammaPartNum_two_mul_succ, Nat.factorial_succ, Nat.cast_mul, hpch,
      show 2 * ((m + 1) + 1) = 2 * (m + 1) + 2 by ring, pow_add, sq]
    push_cast
    ring

/-- Nonvanishing of `(ascPochhammer ℂ n).eval (1 - a)` when `∀ m : ℕ, a ≠ (m : ℂ) + 1`. -/
private theorem ascPochhammer_eval_one_sub_ne_zero {a : ℂ} (ha : ∀ m : ℕ, a ≠ (m : ℂ) + 1)
    (n : ℕ) : (ascPochhammer ℂ n).eval (1 - a) ≠ 0 := by
  intro h0
  rw [ascPochhammer_eval_eq_zero_iff] at h0
  obtain ⟨m, _, hm⟩ := h0
  exact ha m (by linear_combination -hm)

/-- Eventual nonvanishing of `Complex.upperIncompleteGammaContFracSolution a z` on
`Complex.slitPlane` when `a ∉ {1, 2, 3, ...}`. -/
theorem eventually_upperIncompleteGammaContFracSolution_ne_zero {a z : ℂ}
    (ha : ∀ m : ℕ, a ≠ (m : ℂ) + 1) (hz : z ∈ slitPlane) :
    ∀ᶠ n : ℕ in atTop, upperIncompleteGammaContFracSolution a z n ≠ 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hne_rhs : ∀ b : ℂ, ∀ᶠ k : ℕ in atTop,
      (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-b / 2 - 1 / 4) *
        (k : ℂ) ^ (b / 2 - 1 / 4) * cexp (-2 * z ^ (1 / 2 : ℂ) * (k : ℂ) ^ (1 / 2 : ℂ)) ≠ 0 := by
    intro b
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne') (Complex.exp_ne_zero _))
      (cpow_ne_zero_iff.mpr (Or.inl hz0))) (cpow_ne_zero_iff.mpr (Or.inl hk0)))
      (Complex.exp_ne_zero _)
  have hK1 : ∀ᶠ k : ℕ in atTop, TauCeti.shiftedLaplaceIntegral k (a - 1 - (k : ℂ)) z ≠ 0 :=
    ((TauCeti.isEquivalent_shiftedLaplaceIntegral_sub a hz).isTheta.eq_zero_iff.and
      (hne_rhs a)).mono fun _ ⟨h0, hne⟩ ↦ mt h0.mp hne
  have hK2 : ∀ᶠ k : ℕ in atTop, TauCeti.shiftedLaplaceIntegral k (a - 2 - (k : ℂ)) z ≠ 0 := by
    have hθ := (TauCeti.isEquivalent_shiftedLaplaceIntegral_sub (a - 1) hz).isTheta.eq_zero_iff
    filter_upwards [hθ.and (hne_rhs (a - 1))] with k ⟨h0, hne⟩
    simpa only [show a - 1 - 1 - (k : ℂ) = a - 2 - (k : ℂ) by ring] using mt h0.mp hne
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp hK1
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp hK2
  rw [eventually_atTop]
  refine ⟨2 * (max K₁ K₂ + 1), fun n hn ↦ ?_⟩
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    rw [show c + 1 + (c + 1) = 2 * (c + 1) by ring,
      upperIncompleteGammaContFracSolution_two_mul_succ]
    exact mul_ne_zero (mul_ne_zero (ascPochhammer_eval_one_sub_ne_zero ha _)
      (pow_ne_zero _ (inv_ne_zero hz0))) (hK₂ c (by omega))
  · rw [upperIncompleteGammaContFracSolution_two_mul_add_one]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (ascPochhammer_eval_one_sub_ne_zero ha _))
      (pow_ne_zero _ (inv_ne_zero hz0))) (hK₁ k (by omega))

/-- Reduction-of-order term `(-1) ^ m * (∏ j ∈ Icc 1 m, a_j) / (f m * f (m + 1))`. -/
private def reductionTerm (a z : ℂ) (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * (∏ j ∈ Finset.Icc 1 m, upperIncompleteGammaPartNum a z j) /
    (upperIncompleteGammaContFracSolution a z m *
      upperIncompleteGammaContFracSolution a z (m + 1))

/-- Exact formula for `reductionTerm a z (2 * (m + 1))` once `f (2 * (m + 1))` and
`f (2 * (m + 1) + 1)` are nonzero. -/
private theorem reductionTerm_two_mul_succ {a z : ℂ} (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1)
    (hz : z ∈ slitPlane) (m : ℕ)
    (hf0 : upperIncompleteGammaContFracSolution a z (2 * (m + 1)) ≠ 0)
    (hf1 : upperIncompleteGammaContFracSolution a z (2 * (m + 1) + 1) ≠ 0) :
    reductionTerm a z (2 * (m + 1)) =
      -(m ! : ℂ) / ((ascPochhammer ℂ (m + 1)).eval (1 - a) *
        TauCeti.shiftedLaplaceIntegral m (a - 2 - (m : ℂ)) z *
        TauCeti.shiftedLaplaceIntegral (m + 1) (a - 2 - (m : ℂ)) z) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hpch : (ascPochhammer ℂ (m + 1)).eval (1 - a) ≠ 0 :=
    ascPochhammer_eval_one_sub_ne_zero ha (m + 1)
  have hpow : (z⁻¹) ^ (m + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hz0)
  rw [upperIncompleteGammaContFracSolution_two_mul_succ] at hf0
  rw [upperIncompleteGammaContFracSolution_two_mul_add_one,
    show a - 1 - ((m + 1 : ℕ) : ℂ) = a - 2 - (m : ℂ) by push_cast; ring] at hf1
  have hKm : TauCeti.shiftedLaplaceIntegral m (a - 2 - (m : ℂ)) z ≠ 0 := right_ne_zero_of_mul hf0
  have hKm1 : TauCeti.shiftedLaplaceIntegral (m + 1) (a - 2 - (m : ℂ)) z ≠ 0 :=
    right_ne_zero_of_mul hf1
  rw [reductionTerm, Even.neg_one_pow ⟨m + 1, by ring⟩, one_mul,
    prod_upperIncompleteGammaPartNum_two_mul_succ,
    upperIncompleteGammaContFracSolution_two_mul_succ,
    upperIncompleteGammaContFracSolution_two_mul_add_one,
    show a - 1 - ((m + 1 : ℕ) : ℂ) = a - 2 - (m : ℂ) by push_cast; ring,
    show 2 * (m + 1) = (m + 1) + (m + 1) by ring, pow_add]
  field_simp [hpch, hpow, hKm, hKm1]

/-- Exact formula for the paired sum `reductionTerm a z (2 * (m + 1)) +
reductionTerm a z (2 * (m + 1) + 1)` using the three-term recurrence. -/
private theorem reductionTerm_pair_eq {a z : ℂ} (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1)
    (hz : z ∈ slitPlane) (m : ℕ)
    (hf0 : upperIncompleteGammaContFracSolution a z (2 * (m + 1)) ≠ 0)
    (hf1 : upperIncompleteGammaContFracSolution a z (2 * (m + 1) + 1) ≠ 0)
    (hf2 : upperIncompleteGammaContFracSolution a z (2 * (m + 2)) ≠ 0) :
    reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1) =
      z * (m ! : ℂ) / ((ascPochhammer ℂ (m + 2)).eval (1 - a) *
        TauCeti.shiftedLaplaceIntegral m (a - 2 - (m : ℂ)) z *
        TauCeti.shiftedLaplaceIntegral (m + 1) (a - 3 - (m : ℂ)) z) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hrec := upperIncompleteGammaContFracSolution_add_two a hz (2 * (m + 1))
  rw [show 2 * (m + 1) + 2 = 2 * (m + 2) by ring] at hrec
  have hpair : reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1) =
      (∏ j ∈ Finset.Icc 1 (2 * (m + 1)), upperIncompleteGammaPartNum a z j) /
        (upperIncompleteGammaContFracSolution a z (2 * (m + 1)) *
          upperIncompleteGammaContFracSolution a z (2 * (m + 2))) := by
    rw [reductionTerm, reductionTerm, show 2 * (m + 1) + 1 + 1 = 2 * (m + 2) by ring,
      Even.neg_one_pow ⟨m + 1, by ring⟩, Odd.neg_one_pow ⟨m + 1, rfl⟩, one_mul,
      Finset.prod_Icc_succ_top (by omega)]
    field_simp [hf0, hf1, hf2]
    linear_combination (∏ x ∈ Finset.Icc 1 (2 * (m + 1)), upperIncompleteGammaPartNum a z x) * hrec
  rw [hpair, prod_upperIncompleteGammaPartNum_two_mul_succ,
    upperIncompleteGammaContFracSolution_two_mul_succ a z m,
    show 2 * (m + 2) = 2 * ((m + 1) + 1) by ring,
    upperIncompleteGammaContFracSolution_two_mul_succ a z (m + 1),
    show a - 2 - ((m + 1 : ℕ) : ℂ) = a - 3 - (m : ℂ) by push_cast; ring]
  have hpch1 : (ascPochhammer ℂ (m + 1)).eval (1 - a) ≠ 0 :=
    ascPochhammer_eval_one_sub_ne_zero ha (m + 1)
  have hpch2 : (ascPochhammer ℂ (m + 2)).eval (1 - a) ≠ 0 :=
    ascPochhammer_eval_one_sub_ne_zero ha (m + 2)
  have hpow1 : (z⁻¹) ^ (m + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hz0)
  rw [upperIncompleteGammaContFracSolution_two_mul_succ] at hf0
  rw [show 2 * (m + 2) = 2 * ((m + 1) + 1) by ring,
    upperIncompleteGammaContFracSolution_two_mul_succ,
    show a - 2 - ((m + 1 : ℕ) : ℂ) = a - 3 - (m : ℂ) by push_cast; ring] at hf2
  have hKm : TauCeti.shiftedLaplaceIntegral m (a - 2 - (m : ℂ)) z ≠ 0 := right_ne_zero_of_mul hf0
  have hKm1 : TauCeti.shiftedLaplaceIntegral (m + 1) (a - 3 - (m : ℂ)) z ≠ 0 :=
    right_ne_zero_of_mul hf2
  rw [show 2 * (m + 1) = (m + 1) + (m + 1) by ring, pow_add, pow_succ (z⁻¹) (m + 1)]
  field_simp [hz0, hpch1, hpch2, hpow1, hKm, hKm1]

/-- Rising factorial product `∏ j ∈ range n, (s + j) = (ascPochhammer ℂ n).eval s`. -/
private theorem prod_range_add_eq_ascPochhammer (s : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (s + (j : ℂ))) = (ascPochhammer ℂ n).eval s := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ih, ascPochhammer_succ_eval]

/-- Euler Gamma-sequence asymptotic `(m ! : ℂ) / (ascPochhammer ℂ (m + 1)).eval (1 - a) ~
Complex.Gamma (1 - a) * (m : ℂ) ^ (a - 1)` when `∀ j : ℕ, a ≠ (j : ℂ) + 1`. -/
private theorem isEquivalent_factorial_div_ascPochhammer {a : ℂ} (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1) :
    (fun m : ℕ ↦ (m ! : ℂ) / (ascPochhammer ℂ (m + 1)).eval (1 - a)) ~[atTop]
      fun m : ℕ ↦ Gamma (1 - a) * (m : ℂ) ^ (a - 1) := by
  have hG_ne : Gamma (1 - a) ≠ 0 :=
    Gamma_ne_zero fun j hj ↦ ha j (by linear_combination -hj)
  have hG_eq : Complex.GammaSeq (1 - a) ~[atTop] fun _ : ℕ ↦ Gamma (1 - a) := by
    have hlim : Tendsto (Complex.GammaSeq (1 - a) / fun _ : ℕ ↦ Gamma (1 - a))
        atTop (𝓝 (Gamma (1 - a) / Gamma (1 - a))) :=
      ((GammaSeq_tendsto_Gamma (1 - a)).div_const (Gamma (1 - a))).congr fun _ ↦ rfl
    rw [div_self hG_ne] at hlim
    exact isEquivalent_of_tendsto_one hlim
  refine ((hG_eq.mul (IsEquivalent.refl (u := fun m : ℕ ↦ (m : ℂ) ^ (a - 1)))).congr_left
    ?_).congr_right (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  dsimp only [Pi.mul_apply]
  rw [GammaSeq, prod_range_add_eq_ascPochhammer]
  calc ((m : ℂ) ^ (1 - a) * (m ! : ℂ) / (ascPochhammer ℂ (m + 1)).eval (1 - a)) *
        (m : ℂ) ^ (a - 1)
      = ((m : ℂ) ^ (1 - a) * (m : ℂ) ^ (a - 1)) * (m ! : ℂ) /
          (ascPochhammer ℂ (m + 1)).eval (1 - a) := by ring
    _ = (m ! : ℂ) / (ascPochhammer ℂ (m + 1)).eval (1 - a) := by
        rw [← cpow_add _ _ hm0, show (1 - a) + (a - 1) = 0 by ring, cpow_zero, one_mul]

/-- Shifted-index Pochhammer asymptotic `(m ! : ℂ) / (ascPochhammer ℂ (m + 2)).eval (1 - a) ~
Complex.Gamma (1 - a) * (m : ℂ) ^ (a - 2)`. -/
private theorem isEquivalent_factorial_div_ascPochhammer_succ {a : ℂ}
    (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1) :
    (fun m : ℕ ↦ (m ! : ℂ) / (ascPochhammer ℂ (m + 2)).eval (1 - a)) ~[atTop]
      fun m : ℕ ↦ Gamma (1 - a) * (m : ℂ) ^ (a - 2) := by
  have hlin : (fun m : ℕ ↦ (1 - a + ((m + 1 : ℕ) : ℂ))⁻¹) ~[atTop]
      fun m : ℕ ↦ (m : ℂ) ^ (-1 : ℂ) := by
    refine isEquivalent_of_tendsto_one ?_
    have hm_inv : Tendsto (fun m : ℕ ↦ (m : ℂ)⁻¹) atTop (𝓝 0) := by
      have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      simpa only [Function.comp_def, ofReal_zero, ofReal_inv, ofReal_natCast] using h
    have h1 : Tendsto (fun m : ℕ ↦ (1 + (2 - a) * (m : ℂ)⁻¹)⁻¹) atTop (𝓝 1) := by
      simpa only [mul_zero, add_zero, inv_one] using
        ((hm_inv.const_mul (2 - a)).const_add 1).inv₀ (by norm_num)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [Pi.div_apply]
    rw [cpow_neg_one]; push_cast; field_simp [hm0]; ring
  refine (((isEquivalent_factorial_div_ascPochhammer ha).mul hlin).congr_left ?_).congr_right ?_
  · filter_upwards with m
    have hp : (ascPochhammer ℂ (m + 2)).eval (1 - a) =
        (ascPochhammer ℂ (m + 1)).eval (1 - a) * (1 - a + ((m + 1 : ℕ) : ℂ)) :=
      ascPochhammer_succ_eval _ _
    dsimp only [Pi.mul_apply]
    rw [hp, ← div_eq_mul_inv, div_div]
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [Pi.mul_apply]
    rw [mul_assoc, ← cpow_add _ _ hm0, show a - 1 + (-1 : ℂ) = a - 2 by ring]

/-- Forward difference of square roots: `√(m + 1) - √m ~ (1 / 2) * m ^ (-1 / 2)`. -/
private theorem isEquivalent_sqrt_succ_sub :
    (fun m : ℕ ↦ Real.sqrt (m + 1 : ℝ) - Real.sqrt m) ~[atTop]
      fun m : ℕ ↦ (1 / 2 : ℝ) * (m : ℝ) ^ (-1 / 2 : ℝ) := by
  refine isEquivalent_of_tendsto_one ?_
  have h1 : Tendsto (fun m : ℕ ↦ Real.sqrt (1 + (m : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_add 1)
    simpa only [Function.comp_def, add_zero, Real.sqrt_one] using h
  have hlim : Tendsto (fun m : ℕ ↦ 2 * (Real.sqrt (1 + (m : ℝ)⁻¹) + 1)⁻¹) atTop (𝓝 1) := by
    have h := ((h1.add_const 1).inv₀ (by norm_num)).const_mul 2
    rwa [show (2 : ℝ) * (1 + 1)⁻¹ = 1 by norm_num] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  have hsum_pos : 0 < Real.sqrt (m + 1 : ℝ) + Real.sqrt m := by positivity
  have hdiff : Real.sqrt (m + 1 : ℝ) - Real.sqrt m = (Real.sqrt (m + 1 : ℝ) + Real.sqrt m)⁻¹ := by
    apply mul_right_cancel₀ hsum_pos.ne'
    rw [inv_mul_cancel₀ hsum_pos.ne']
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m + 1), Real.sq_sqrt hm_pos.le]
  have hmul : Real.sqrt (m + 1 : ℝ) = Real.sqrt m * Real.sqrt (1 + (m : ℝ)⁻¹) := by
    rw [← Real.sqrt_mul hm_pos.le]; congr 1; field_simp [hm_pos.ne']
  have hrpow : (m : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt m)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hm_pos.le]; norm_num
  dsimp only [Pi.div_apply]
  rw [hdiff, hmul, hrpow]
  field_simp [hsqrt_pos.ne', (by positivity : Real.sqrt (1 + (m : ℝ)⁻¹) + 1 ≠ 0)]

/-- Forward difference `√(m + 1) - √m → 0` as `m → ∞`. -/
private theorem tendsto_sqrt_succ_sub_zero :
    Tendsto (fun m : ℕ ↦ Real.sqrt (m + 1 : ℝ) - Real.sqrt m) atTop (𝓝 0) := by
  refine isEquivalent_sqrt_succ_sub.symm.tendsto_nhds ?_
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_natCast_atTop_atTop).const_mul (1 / 2)
  simpa only [Function.comp_def, neg_div, mul_zero] using h

/-- Cast identity `((m : ℂ) ^ (1 / 2 : ℂ)) = ((Real.sqrt m : ℝ) : ℂ)`. -/
private theorem natCast_cpow_half_eq_ofReal_sqrt (m : ℕ) :
    (m : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt m : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow (Nat.cast_nonneg m), ofReal_natCast]
  push_cast; rfl

/-- Shift invariance `((m + 1 : ℕ) : ℂ) ^ γ ~[atTop] (m : ℂ) ^ γ` and
`cexp (c * ((m + 1 : ℕ) : ℂ) ^ (1 / 2)) ~[atTop] cexp (c * (m : ℂ) ^ (1 / 2))`. -/
private theorem isEquivalent_succ_cpow_and_cexp_sqrt (γ c : ℂ) :
    ((fun m : ℕ ↦ ((m + 1 : ℕ) : ℂ) ^ γ) ~[atTop] fun m : ℕ ↦ (m : ℂ) ^ γ) ∧
      ((fun m : ℕ ↦ cexp (c * ((m + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ))) ~[atTop]
        fun m : ℕ ↦ cexp (c * (m : ℂ) ^ (1 / 2 : ℂ))) := by
  constructor
  · refine isEquivalent_of_tendsto_one ?_
    have hbase : Tendsto (fun m : ℕ ↦ ((1 + (m : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 1) := by
      have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_add 1)
      simpa only [Function.comp_def, add_zero, ofReal_one] using h
    have h1 : Tendsto (fun m : ℕ ↦ (((1 + (m : ℝ)⁻¹ : ℝ) : ℂ)) ^ γ) atTop (𝓝 1) := by
      have h := (continuousAt_cpow_const (b := γ)
        (Or.inl (by simp : 0 < (1 : ℂ).re))).tendsto.comp hbase
      simpa only [Function.comp_def, one_cpow] using h
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have hm_c : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm_c0 : (m : ℂ) ^ γ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hm_c)
    have hmul : ((m + 1 : ℕ) : ℂ) = (m : ℂ) * ((1 + (m : ℝ)⁻¹ : ℝ) : ℂ) := by
      push_cast; field_simp [hm_c]
    dsimp only [Pi.div_apply]
    rw [hmul, ← ofReal_natCast, mul_cpow_ofReal_nonneg hm_pos.le (by positivity), ofReal_natCast,
      mul_div_cancel_left₀ _ hm_c0]
  · refine isEquivalent_of_tendsto_one ?_
    have hexp1 : Tendsto
        (fun m : ℕ ↦ cexp (c * ((Real.sqrt (m + 1 : ℝ) - Real.sqrt m : ℝ) : ℂ))) atTop (𝓝 1) := by
      have h := Complex.continuous_exp.continuousAt.tendsto.comp
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp
          tendsto_sqrt_succ_sub_zero).const_mul c)
      simpa only [Function.comp_def, ofReal_zero, mul_zero, Complex.exp_zero] using h
    refine hexp1.congr fun m ↦ ?_
    dsimp only [Pi.div_apply]
    rw [natCast_cpow_half_eq_ofReal_sqrt (m + 1), natCast_cpow_half_eq_ofReal_sqrt m, Nat.cast_add,
      Nat.cast_one, ← Complex.exp_sub]
    congr 1; push_cast; ring

/-- Complex forward difference of stretched exponentials:
`cexp (c * √(m + 1)) - cexp (c * √m) ~ (c / 2) * (m : ℂ) ^ (-1 / 2) * cexp (c * √m)`. -/
private theorem isEquivalent_cexp_sqrt_sub (c : ℂ) :
    (fun m : ℕ ↦ cexp (c * (((m + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ))) -
        cexp (c * ((m : ℂ) ^ (1 / 2 : ℂ)))) ~[atTop]
      fun m : ℕ ↦ (c / 2) * (m : ℂ) ^ (-1 / 2 : ℂ) * cexp (c * ((m : ℂ) ^ (1 / 2 : ℂ))) := by
  have hexp0 : (fun w : ℂ ↦ cexp w - 1) ~[𝓝 0] fun w : ℂ ↦ w := by
    have hd : (fun w : ℂ ↦ cexp w - 1 - w) =o[𝓝 0] fun w : ℂ ↦ w := by
      simpa only [zero_add, Complex.exp_zero, smul_eq_mul, mul_one] using
        hasDerivAt_iff_isLittleO_nhds_zero.mp (Complex.hasDerivAt_exp 0)
    exact hd.isEquivalent
  have hδ0 : Tendsto (fun m : ℕ ↦ c * ((Real.sqrt (m + 1 : ℝ) - Real.sqrt m : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_sqrt_succ_sub_zero).const_mul c
    simpa only [Function.comp_def, ofReal_zero, mul_zero] using h
  have hδ_eq : (fun m : ℕ ↦ c * ((Real.sqrt (m + 1 : ℝ) - Real.sqrt m : ℝ) : ℂ)) ~[atTop]
      fun m : ℕ ↦ (c / 2) * (m : ℂ) ^ (-1 / 2 : ℂ) := by
    have hof : (fun m : ℕ ↦ ((Real.sqrt (m + 1 : ℝ) - Real.sqrt m : ℝ) : ℂ)) ~[atTop]
        fun m : ℕ ↦ (((1 / 2 : ℝ) * (m : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
      have h1 := (isEquivalent_iff_tendsto_one (by
        filter_upwards [eventually_ge_atTop 1] with m hm
        have _hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
        positivity)).mp isEquivalent_sqrt_succ_sub
      have h2 : Tendsto (fun m : ℕ ↦
          (((Real.sqrt (m + 1 : ℝ) - Real.sqrt m) /
            ((1 / 2 : ℝ) * (m : ℝ) ^ (-1 / 2 : ℝ)) : ℝ) : ℂ)) atTop (𝓝 1) := by
        have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h1
        simpa only [Function.comp_def, Pi.div_apply, ofReal_one] using hc
      exact isEquivalent_of_tendsto_one
        (h2.congr fun m ↦ by dsimp only [Pi.div_apply]; rw [ofReal_div])
    refine ((IsEquivalent.refl (u := fun _ : ℕ ↦ c)).mul hof).congr_right ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp only [Pi.mul_apply]
    rw [ofReal_mul, ofReal_cpow hm_pos.le, ofReal_natCast]; push_cast; ring
  refine ((((hexp0.comp_tendsto hδ0).trans hδ_eq).mul
    (IsEquivalent.refl (u := fun m : ℕ ↦ cexp (c * ((m : ℂ) ^ (1 / 2 : ℂ)))))).congr_left
      (Eventually.of_forall fun m ↦ ?_)).congr_right (Eventually.of_forall fun _ ↦ rfl)
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [natCast_cpow_half_eq_ofReal_sqrt (m + 1), natCast_cpow_half_eq_ofReal_sqrt m, Nat.cast_add,
    Nat.cast_one, sub_mul, one_mul, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- Real forward difference of stretched exponentials:
`Real.exp (σ * √(m + 1)) - Real.exp (σ * √m) ~ (σ / 2) * m ^ (-1 / 2) * Real.exp (σ * √m)`. -/
private theorem isEquivalent_real_exp_sqrt_sub (σ : ℝ) :
    (fun m : ℕ ↦ Real.exp (σ * Real.sqrt ((m + 1 : ℕ) : ℝ)) -
        Real.exp (σ * Real.sqrt m)) ~[atTop]
      fun m : ℕ ↦ (σ / 2) * (m : ℝ) ^ (-1 / 2 : ℝ) * Real.exp (σ * Real.sqrt m) := by
  have hexp0 : (fun x : ℝ ↦ Real.exp x - 1) ~[𝓝 0] fun x : ℝ ↦ x := by
    have hd : (fun x : ℝ ↦ Real.exp x - 1 - x) =o[𝓝 0] fun x : ℝ ↦ x := by
      simpa only [zero_add, Real.exp_zero, smul_eq_mul, mul_one] using
        hasDerivAt_iff_isLittleO_nhds_zero.mp (Real.hasDerivAt_exp 0)
    exact hd.isEquivalent
  have hδ0 : Tendsto (fun m : ℕ ↦ σ * (Real.sqrt (m + 1 : ℝ) - Real.sqrt m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_sqrt_succ_sub_zero.const_mul σ
  have hδ_eq : (fun m : ℕ ↦ σ * (Real.sqrt (m + 1 : ℝ) - Real.sqrt m)) ~[atTop]
      fun m : ℕ ↦ (σ / 2) * (m : ℝ) ^ (-1 / 2 : ℝ) :=
    ((IsEquivalent.refl (u := fun _ : ℕ ↦ σ)).mul isEquivalent_sqrt_succ_sub).congr_right
      (Eventually.of_forall fun m ↦ by dsimp only [Pi.mul_apply]; ring)
  refine ((((hexp0.comp_tendsto hδ0).trans hδ_eq).mul
    (IsEquivalent.refl (u := fun m : ℕ ↦ Real.exp (σ * Real.sqrt m)))).congr_left
      (Eventually.of_forall fun m ↦ ?_)).congr_right (Eventually.of_forall fun _ ↦ rfl)
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [Nat.cast_add, Nat.cast_one, sub_mul, one_mul, ← Real.exp_add]
  congr 2; ring

/-- Shifted-index asymptotic for `shiftedLaplaceIntegral (m + 1) (b - 1 - (m + 1)) z` in terms of
`(m : ℂ)`. -/
private theorem isEquivalent_shiftedLaplaceIntegral_succ (b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (fun m : ℕ ↦ TauCeti.shiftedLaplaceIntegral (m + 1) (b - 1 - ((m + 1 : ℕ) : ℂ)) z) ~[atTop]
      fun m : ℕ ↦ (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-b / 2 - 1 / 4) *
        (m : ℂ) ^ (b / 2 - 1 / 4) * cexp (-2 * z ^ (1 / 2 : ℂ) * (m : ℂ) ^ (1 / 2 : ℂ)) := by
  have hcomp := (TauCeti.isEquivalent_shiftedLaplaceIntegral_sub b hz).comp_tendsto
    (tendsto_add_atTop_nat 1)
  obtain ⟨hpow, hexp⟩ := isEquivalent_succ_cpow_and_cexp_sqrt (b / 2 - 1 / 4)
    (-2 * z ^ (1 / 2 : ℂ))
  exact (hcomp.congr_left (Eventually.of_forall fun _ ↦ rfl)).trans
    ((((IsEquivalent.refl.mul hpow).mul hexp).congr_left
      (Eventually.of_forall fun _ ↦ rfl)).congr_right (Eventually.of_forall fun _ ↦ rfl))

/-- Saddle-point asymptotic for `TauCeti.shiftedLaplaceIntegral m (a - 2 - m) z`. -/
private theorem isEquivalent_shiftedLaplaceIntegral_sub_two (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    (fun m : ℕ ↦ TauCeti.shiftedLaplaceIntegral m (a - 2 - (m : ℂ)) z) ~[atTop]
      fun m : ℕ ↦ ((Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) *
          z ^ (1 / 2 : ℂ)) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) *
        cexp (-2 * z ^ (1 / 2 : ℂ) * (m : ℂ) ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  refine ((TauCeti.isEquivalent_shiftedLaplaceIntegral_sub (a - 1) hz).congr_left ?_).congr_right ?_
  · filter_upwards with m
    rw [show a - 1 - 1 - (m : ℂ) = a - 2 - (m : ℂ) by ring]
  · filter_upwards with m
    congr 2
    rw [show (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) * z ^ (1 / 2 : ℂ) =
      (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * (z ^ (-a / 2 - 1 / 4) * z ^ (1 / 2 : ℂ)) by ring,
      ← cpow_add _ _ hz0]
    congr 2; ring

/-- Nonzero leading constant `Γ(1 - a) / (2 * z ^ (1 / 2) * c_a ^ 2)` of the Pincherle
reduction-of-order partial sums. -/
private def reductionLeadConst (a z : ℂ) : ℂ :=
  Gamma (1 - a) / (2 * z ^ (1 / 2 : ℂ) *
    ((Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4)) ^ 2)

private theorem reductionLeadConst_ne_zero {a z : ℂ} (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1)
    (hz : z ∈ slitPlane) : reductionLeadConst a z ≠ 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hG : Gamma (1 - a) ≠ 0 := Gamma_ne_zero fun j hj ↦ ha j (by linear_combination -hj)
  have hca : (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
      (Complex.exp_ne_zero _)) (cpow_ne_zero_iff.mpr (Or.inl hz0))
  exact div_ne_zero hG (mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hz0)))
    (pow_ne_zero 2 hca))

/-- Asymptotic equivalence of the single even term `reductionTerm a z (2 * (m + 1))`. -/
private theorem isEquivalent_reductionTerm_two_mul_succ {a z : ℂ}
    (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1) (hz : z ∈ slitPlane) :
    (fun m : ℕ ↦ reductionTerm a z (2 * (m + 1))) ~[atTop]
      fun m : ℕ ↦ (-2 * reductionLeadConst a z) *
        cexp (4 * z ^ (1 / 2 : ℂ) * (m : ℂ) ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  have hζ0 : ζ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  set ca : ℂ := (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4)
  have hca0 : ca ≠ 0 := mul_ne_zero (mul_ne_zero
    (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne') (Complex.exp_ne_zero _))
    (cpow_ne_zero_iff.mpr (Or.inl hz0))
  have hKm := isEquivalent_shiftedLaplaceIntegral_sub_two a hz
  have hKm1 : (fun m : ℕ ↦ TauCeti.shiftedLaplaceIntegral (m + 1) (a - 2 - (m : ℂ)) z) ~[atTop]
      fun m : ℕ ↦ ca * (m : ℂ) ^ (a / 2 - 1 / 4) * cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)) :=
    (isEquivalent_shiftedLaplaceIntegral_succ a hz).congr_left
      (Eventually.of_forall fun m ↦ by
        dsimp only
        rw [show a - 1 - ((m + 1 : ℕ) : ℂ) = a - 2 - (m : ℂ) by push_cast; ring])
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_upperIncompleteGammaContFracSolution_ne_zero ha hz)
  refine ((((IsEquivalent.refl (u := fun _ : ℕ ↦ (-1 : ℂ))).mul
      (isEquivalent_factorial_div_ascPochhammer ha)).div (hKm.mul hKm1)).congr_left
    ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop N₀] with m hm
    dsimp only [Pi.div_apply, Pi.mul_apply]
    rw [reductionTerm_two_mul_succ ha hz m (hN₀ _ (by omega)) (hN₀ _ (by omega))]
    ring
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    set P : ℂ := (m : ℂ) ^ (a - 1)
    have hP : P ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hm0)
    set E4 : ℂ := cexp (4 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))
    have hE4 : E4 ≠ 0 := Complex.exp_ne_zero _
    have hp : (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) * (m : ℂ) ^ (a / 2 - 1 / 4) = P := by
      dsimp only [P]; rw [← cpow_add _ _ hm0]; congr 1; ring
    have he : cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)) *
        cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)) = E4⁻¹ := by
      dsimp only [E4]; rw [← Complex.exp_add, ← Complex.exp_neg]; congr 1; ring
    change -1 * (Gamma (1 - a) * P) /
        (((ca * ζ) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) * cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) *
          (ca * (m : ℂ) ^ (a / 2 - 1 / 4) * cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)))) =
      (-2 * (Gamma (1 - a) / (2 * ζ * ca ^ 2))) * E4
    rw [show ((ca * ζ) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) *
          cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) *
        (ca * (m : ℂ) ^ (a / 2 - 1 / 4) * cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) =
        ca ^ 2 * ζ * ((m : ℂ) ^ ((a - 1) / 2 - 1 / 4) * (m : ℂ) ^ (a / 2 - 1 / 4)) *
          (cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)) *
            cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) by ring, hp, he]
    field_simp [hca0, hζ0, hP, hE4]

/-- Saddle-point asymptotic for `TauCeti.shiftedLaplaceIntegral (m + 1) (a - 3 - m) z`. -/
private theorem isEquivalent_shiftedLaplaceIntegral_sub_three (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    (fun m : ℕ ↦ TauCeti.shiftedLaplaceIntegral (m + 1) (a - 3 - (m : ℂ)) z) ~[atTop]
      fun m : ℕ ↦ ((Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) *
          z ^ (1 / 2 : ℂ)) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) *
        cexp (-2 * z ^ (1 / 2 : ℂ) * (m : ℂ) ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  refine ((isEquivalent_shiftedLaplaceIntegral_succ (a - 1) hz).congr_left ?_).congr_right ?_
  · filter_upwards with m
    rw [show a - 1 - 1 - ((m + 1 : ℕ) : ℂ) = a - 3 - (m : ℂ) by push_cast; ring]
  · filter_upwards with m
    congr 2
    rw [show (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) * z ^ (1 / 2 : ℂ) =
      (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * (z ^ (-a / 2 - 1 / 4) * z ^ (1 / 2 : ℂ)) by ring,
      ← cpow_add _ _ hz0]
    congr 2; ring

/-- Asymptotic equivalence of the paired sum
`reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1)`. -/
private theorem isEquivalent_reductionTerm_pair {a z : ℂ}
    (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1) (hz : z ∈ slitPlane) :
    (fun m : ℕ ↦ reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1)) ~[atTop]
      fun m : ℕ ↦ (2 * z ^ (1 / 2 : ℂ) * reductionLeadConst a z) *
        (m : ℂ) ^ (-1 / 2 : ℂ) * cexp (4 * z ^ (1 / 2 : ℂ) * (m : ℂ) ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  have hζ0 : ζ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hζ_sq : ζ * ζ = z := by dsimp [ζ]; rw [← cpow_add _ _ hz0]; norm_num
  set ca : ℂ := (Real.sqrt Real.pi : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4)
  have hca0 : ca ≠ 0 := mul_ne_zero (mul_ne_zero
    (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne') (Complex.exp_ne_zero _))
    (cpow_ne_zero_iff.mpr (Or.inl hz0))
  have hKm := isEquivalent_shiftedLaplaceIntegral_sub_two a hz
  have hKm1 := isEquivalent_shiftedLaplaceIntegral_sub_three a hz
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_upperIncompleteGammaContFracSolution_ne_zero ha hz)
  refine ((((IsEquivalent.refl (u := fun _ : ℕ ↦ z)).mul
      (isEquivalent_factorial_div_ascPochhammer_succ ha)).div (hKm.mul hKm1)).congr_left
    ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop N₀] with m hm
    dsimp only [Pi.div_apply, Pi.mul_apply]
    rw [reductionTerm_pair_eq ha hz m (hN₀ _ (by omega)) (hN₀ _ (by omega)) (hN₀ _ (by omega))]
    ring
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    set P : ℂ := (m : ℂ) ^ (a - 3 / 2)
    have hP : P ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hm0)
    set E4 : ℂ := cexp (4 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))
    have hE4 : E4 ≠ 0 := Complex.exp_ne_zero _
    have hp1 : (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) = P := by
      dsimp only [P]; rw [← cpow_add _ _ hm0]; congr 1; ring
    have hp2 : (m : ℂ) ^ (a - 2) = P * (m : ℂ) ^ (-1 / 2 : ℂ) := by
      dsimp only [P]; rw [← cpow_add _ _ hm0]; congr 1; ring
    have he : cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)) *
        cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)) = E4⁻¹ := by
      dsimp only [E4]; rw [← Complex.exp_add, ← Complex.exp_neg]; congr 1; ring
    change z * (Gamma (1 - a) * (m : ℂ) ^ (a - 2)) /
        (((ca * ζ) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) * cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) *
          ((ca * ζ) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) *
            cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)))) =
      (2 * ζ * (Gamma (1 - a) / (2 * ζ * ca ^ 2))) * (m : ℂ) ^ (-1 / 2 : ℂ) * E4
    rw [show ((ca * ζ) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) *
          cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) *
        ((ca * ζ) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4) *
          cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) =
        ca ^ 2 * (ζ * ζ) *
          ((m : ℂ) ^ ((a - 1) / 2 - 1 / 4) * (m : ℂ) ^ ((a - 1) / 2 - 1 / 4)) *
          (cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ)) *
            cexp (-2 * ζ * (m : ℂ) ^ (1 / 2 : ℂ))) by ring, hζ_sq, hp1, hp2, he]
    field_simp [hz0, hca0, hζ0, hP, hE4]

/-- Norm identity
`‖cexp (4 * z ^ (1 / 2) * m ^ (1 / 2))‖ = Real.exp ((4 * (z ^ (1 / 2)).re) * √m)`. -/
private theorem norm_cexp_four_mul_sqrt (z : ℂ) (m : ℕ) :
    ‖cexp (4 * z ^ (1 / 2 : ℂ) * (m : ℂ) ^ (1 / 2 : ℂ))‖ =
      Real.exp ((4 * (z ^ (1 / 2 : ℂ)).re) * Real.sqrt m) := by
  rw [natCast_cpow_half_eq_ofReal_sqrt, Complex.norm_exp]
  congr 1; simp [mul_re]

/-- Divergence `Real.exp ((4 * (z ^ (1 / 2)).re) * √m) → +∞` on `Complex.slitPlane`. -/
private theorem tendsto_exp_four_re_mul_sqrt_atTop {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun m : ℕ ↦ Real.exp ((4 * (z ^ (1 / 2 : ℂ)).re) * Real.sqrt m)) atTop atTop := by
  have hζ : 0 < 4 * (z ^ (1 / 2 : ℂ)).re := mul_pos (by norm_num) (TauCeti.cpow_half_re_pos hz)
  exact Real.tendsto_exp_atTop.comp ((Filter.tendsto_atTop_mono
    (fun m : ℕ ↦ (Real.sqrt_eq_rpow m).ge)
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop hζ)

/-- Stolz--Cesàro asymptotic for the paired partial sums
`∑ m ∈ Ico M₀ M, (reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1))`. -/
private theorem isEquivalent_sum_Ico_reductionTerm_pair {a z : ℂ}
    (ha : ∀ j : ℕ, a ≠ (j : ℂ) + 1) (hz : z ∈ slitPlane) (M₀ : ℕ) :
    (fun M : ℕ ↦ ∑ m ∈ Finset.Ico M₀ M,
      (reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1))) ~[atTop]
      fun M : ℕ ↦ reductionLeadConst a z *
        cexp (4 * z ^ (1 / 2 : ℂ) * (M : ℂ) ^ (1 / 2 : ℂ)) := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  have hζ_re : 0 < ζ.re := TauCeti.cpow_half_re_pos hz
  set L : ℂ := reductionLeadConst a z
  have hL0 : L ≠ 0 := reductionLeadConst_ne_zero ha hz
  set E : ℕ → ℂ := fun M ↦ cexp (4 * ζ * (M : ℂ) ^ (1 / 2 : ℂ))
  set w : ℕ → ℝ := fun M ↦ Real.exp ((4 * ζ.re) * Real.sqrt M)
  have hu_sub : (fun m : ℕ ↦ L * E (m + 1) - L * E m) ~[atTop]
      fun m : ℕ ↦ (2 * ζ * L) * (m : ℂ) ^ (-1 / 2 : ℂ) * E m := by
    refine (((IsEquivalent.refl (u := fun _ : ℕ ↦ L)).mul
      (isEquivalent_cexp_sqrt_sub (4 * ζ))).congr_left ?_).congr_right ?_
    · filter_upwards with m; dsimp only [Pi.mul_apply, E]; rw [mul_sub]
    · filter_upwards with m; dsimp only [Pi.mul_apply, E]; ring
  have hv_u : (fun m : ℕ ↦ (reductionTerm a z (2 * (m + 1)) +
      reductionTerm a z (2 * (m + 1) + 1)) - (L * E (m + 1) - L * E m)) =o[atTop]
      fun m ↦ (2 * ζ * L) * (m : ℂ) ^ (-1 / 2 : ℂ) * E m :=
    ((isEquivalent_reductionTerm_pair ha hz).trans hu_sub.symm).isLittleO.trans_isEquivalent hu_sub
  have hbigO : (fun m : ℕ ↦ (2 * ζ * L) * (m : ℂ) ^ (-1 / 2 : ℂ) * E m) =O[atTop]
      fun m : ℕ ↦ ((4 * ζ.re) / 2) * (m : ℝ) ^ (-1 / 2 : ℝ) * w m := by
    rw [isBigO_iff]
    refine ⟨‖2 * ζ * L‖ / (2 * ζ.re), ?_⟩
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have hm_norm : ‖(m : ℂ) ^ (-1 / 2 : ℂ)‖ = (m : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [← ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hm_pos]; norm_num
    have hEw : ‖E m‖ = w m := norm_cexp_four_mul_sqrt z m
    rw [norm_mul, norm_mul, hm_norm, hEw, Real.norm_of_nonneg (by positivity)]
    exact le_of_eq (by field_simp [hζ_re.ne']; ring)
  have hv_w : (fun m : ℕ ↦ (reductionTerm a z (2 * (m + 1)) +
      reductionTerm a z (2 * (m + 1) + 1)) - (L * E (m + 1) - L * E m)) =o[atTop]
      fun m ↦ w (m + 1) - w m :=
    (hv_u.trans_isBigO hbigO).trans_isEquivalent (isEquivalent_real_exp_sqrt_sub (4 * ζ.re)).symm
  have hw_mono : ∀ᶠ m : ℕ in atTop, w m ≤ w (m + 1) := Eventually.of_forall fun m ↦
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)) (by positivity))
  have hwu : w =O[atTop] fun M ↦ L * E M :=
    isBigO_iff.mpr ⟨‖L‖⁻¹, Eventually.of_forall fun M ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, norm_mul, norm_cexp_four_mul_sqrt z M,
        inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hL0)]⟩
  exact Asymptotics.isEquivalent_sum_Ico_of_sub hv_w hw_mono
    (tendsto_exp_four_re_mul_sqrt_atTop hz) hwu M₀

/-- Pairing identity `∑ j ∈ Ico (2 * (M₀ + 1)) (2 * (M + 1)), u j =
∑ m ∈ Ico M₀ M, (u (2 * (m + 1)) + u (2 * (m + 1) + 1))` for `M₀ ≤ M`. -/
private theorem sum_Ico_two_mul_succ_eq_pair (u : ℕ → ℂ) {M₀ M : ℕ} (hM : M₀ ≤ M) :
    (∑ j ∈ Finset.Ico (2 * (M₀ + 1)) (2 * (M + 1)), u j) =
      ∑ m ∈ Finset.Ico M₀ M, (u (2 * (m + 1)) + u (2 * (m + 1) + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  clear hM
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show 2 * (M₀ + (d + 1) + 1) = (2 * (M₀ + d + 1) + 1) + 1 by ring,
      Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega), ih,
      show M₀ + (d + 1) = (M₀ + d) + 1 by ring, Finset.sum_Ico_succ_top (by omega), add_assoc]

/-- Combining `Tendsto (fun k ↦ g (2 * k)) atTop atTop` and
`Tendsto (fun k ↦ g (2 * k + 1)) atTop atTop` yields `Tendsto g atTop atTop`. -/
private theorem tendsto_atTop_of_even_and_odd {g : ℕ → ℝ}
    (heven : Tendsto (fun k : ℕ ↦ g (2 * k)) atTop atTop)
    (hodd : Tendsto (fun k : ℕ ↦ g (2 * k + 1)) atTop atTop) :
    Tendsto g atTop atTop := by
  rw [Filter.tendsto_atTop] at heven hodd ⊢
  intro B
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp (heven B)
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (hodd B)
  rw [eventually_atTop]
  refine ⟨2 * max K₁ K₂ + 1, fun n hn ↦ ?_⟩
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show k + k = 2 * k by ring]; exact hK₁ k (by omega)
  · exact hK₂ k (by omega)

/-- Sign-flipped asymptotic for the odd partial sum `(∑ m ∈ Ico M₀ M, pair m) + even M`. -/
private theorem isEquivalent_sum_Ico_reductionTerm_odd {a z : ℂ}
    (ha : ∀ m : ℕ, a ≠ (m : ℂ) + 1) (hz : z ∈ slitPlane) (M₀ : ℕ) :
    (fun M : ℕ ↦ (∑ m ∈ Finset.Ico M₀ M,
      (reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1))) +
      reductionTerm a z (2 * (M + 1))) ~[atTop]
      fun M : ℕ ↦ -reductionLeadConst a z *
        cexp (4 * z ^ (1 / 2 : ℂ) * (M : ℂ) ^ (1 / 2 : ℂ)) := by
  set L : ℂ := reductionLeadConst a z
  set E : ℕ → ℂ := fun M ↦ cexp (4 * z ^ (1 / 2 : ℂ) * (M : ℂ) ^ (1 / 2 : ℂ))
  have ho1 : (fun M : ℕ ↦ (∑ m ∈ Finset.Ico M₀ M,
      (reductionTerm a z (2 * (m + 1)) + reductionTerm a z (2 * (m + 1) + 1))) -
        L * E M) =o[atTop] fun M ↦ -L * E M :=
    (isEquivalent_sum_Ico_reductionTerm_pair ha hz M₀).isLittleO.trans_isBigO (isBigO_iff.mpr
      ⟨1, Eventually.of_forall fun M ↦ by dsimp only [L, E]; simp⟩)
  have ho2 : (fun M : ℕ ↦ reductionTerm a z (2 * (M + 1)) - (-2 * L) * E M) =o[atTop]
      fun M ↦ -L * E M :=
    (isEquivalent_reductionTerm_two_mul_succ ha hz).isLittleO.trans_isBigO (isBigO_iff.mpr
      ⟨2, Eventually.of_forall fun M ↦ le_of_eq (by
        dsimp only [L, E]
        rw [show (-2 * reductionLeadConst a z) *
              cexp (4 * z ^ (1 / 2 : ℂ) * (M : ℂ) ^ (1 / 2 : ℂ)) =
            2 * (-reductionLeadConst a z *
              cexp (4 * z ^ (1 / 2 : ℂ) * (M : ℂ) ^ (1 / 2 : ℂ))) by ring,
          norm_mul, Complex.norm_ofNat])⟩)
  exact ((ho1.add ho2).congr_left fun M ↦ by
    dsimp only [Pi.add_apply, Pi.sub_apply, L, E]; ring).isEquivalent

/-- **Pincherle reduction-of-order sum divergence for Legendre's continued fraction (DLMF 8.9.2).**
For `a ∉ {1, 2, 3, ...}` and `z ∈ Complex.slitPlane`, there exists `N` such that
`upperIncompleteGammaContFracSolution a z m ≠ 0` for all `m ≥ N` and the reduction-of-order partial
sums diverge in norm to `+∞`. -/
theorem tendsto_norm_sum_upperIncompleteGammaContFrac_reductionOfOrder {a z : ℂ}
    (ha : ∀ m : ℕ, a ≠ (m : ℂ) + 1) (hz : z ∈ slitPlane) :
    ∃ N : ℕ, (∀ m ≥ N, upperIncompleteGammaContFracSolution a z m ≠ 0) ∧
      Tendsto (fun n : ℕ ↦ ‖∑ m ∈ Finset.Ico N n,
        (-1 : ℂ) ^ m * (∏ j ∈ Finset.Icc 1 m, upperIncompleteGammaPartNum a z j) /
          (upperIncompleteGammaContFracSolution a z m *
            upperIncompleteGammaContFracSolution a z (m + 1))‖)
        atTop atTop := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventually_upperIncompleteGammaContFracSolution_ne_zero ha hz)
  refine ⟨2 * (M₀ + 1), fun m hm ↦ hM₀ m (by omega), ?_⟩
  set L : ℂ := reductionLeadConst a z
  have hL0 : L ≠ 0 := reductionLeadConst_ne_zero ha hz
  set E : ℕ → ℂ := fun M ↦ cexp (4 * z ^ (1 / 2 : ℂ) * (M : ℂ) ^ (1 / 2 : ℂ))
  have hLE_top : Tendsto (norm ∘ fun M : ℕ ↦ L * E M) atTop atTop :=
    ((tendsto_exp_four_re_mul_sqrt_atTop hz).const_mul_atTop (norm_pos_iff.mpr hL0)).congr
      fun M ↦ by dsimp only [Function.comp_apply, E]; rw [norm_mul, norm_cexp_four_mul_sqrt]
  have hS_pair := isEquivalent_sum_Ico_reductionTerm_pair ha hz M₀
  have hS_odd := isEquivalent_sum_Ico_reductionTerm_odd ha hz M₀
  refine tendsto_atTop_of_even_and_odd ?_ ?_
  · have h1 : Tendsto (fun M : ℕ ↦ ‖∑ m ∈ Finset.Ico (2 * (M₀ + 1)) (2 * (M + 1)),
        reductionTerm a z m‖) atTop atTop :=
      (hS_pair.isTheta.tendsto_norm_atTop_iff.mpr hLE_top).congr'
        ((eventually_ge_atTop M₀).mono fun M hM ↦ by
          dsimp only [Function.comp_apply]; rw [← sum_Ico_two_mul_succ_eq_pair _ hM])
    exact (h1.comp (tendsto_sub_atTop_nat 1)).congr'
      ((eventually_ge_atTop 1).mono fun K hK ↦ by
        dsimp only [Function.comp_apply, reductionTerm]; rw [Nat.sub_add_cancel hK])
  · have hneg_top : Tendsto (norm ∘ fun M : ℕ ↦ -L * E M) atTop atTop :=
      hLE_top.congr fun M ↦ by dsimp only [Function.comp_apply]; rw [neg_mul, norm_neg]
    have h1 : Tendsto (fun M : ℕ ↦ ‖∑ m ∈ Finset.Ico (2 * (M₀ + 1)) (2 * (M + 1) + 1),
        reductionTerm a z m‖) atTop atTop :=
      (hS_odd.isTheta.tendsto_norm_atTop_iff.mpr hneg_top).congr'
        ((eventually_ge_atTop M₀).mono fun M hM ↦ by
          dsimp only [Function.comp_apply]
          rw [Finset.sum_Ico_succ_top (by omega), sum_Ico_two_mul_succ_eq_pair _ hM])
    exact (h1.comp (tendsto_sub_atTop_nat 1)).congr'
      ((eventually_ge_atTop 1).mono fun K hK ↦ by
        dsimp only [Function.comp_apply, reductionTerm]; rw [Nat.sub_add_cancel hK])

/-- Shifted denominator sequence `D 0 = 0`,
`D (n + 1) = (upperIncompleteGammaContFrac a z).dens n`. -/
private def shiftedDens (a z : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => (upperIncompleteGammaContFrac a z).dens n

/-- Three-term recurrence for `shiftedDens`. -/
private theorem shiftedDens_add_two (a z : ℂ) (k : ℕ) :
    shiftedDens a z (k + 2) =
      shiftedDens a z (k + 1) + upperIncompleteGammaPartNum a z (k + 1) * shiftedDens a z k := by
  rcases k with _ | k
  · have hs0 := upperIncompleteGammaContFrac_s_get? a z 0
    simp [shiftedDens, GenContFract.first_den_eq hs0]
  · have hsk := upperIncompleteGammaContFrac_s_get? a z (k + 1)
    simp only [shiftedDens, GenContFract.dens_recurrence hsk rfl rfl, one_mul]

/-- Wronskian identity `f m * D (m + 1) - f (m + 1) * D m = (-1) ^ m * ∏ j ∈ Icc 1 m, a_j` for
`upperIncompleteGammaContFracSolution` against the continuant denominators. -/
private theorem wronskian_upperIncompleteGammaContFracSolution (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (m : ℕ) :
    upperIncompleteGammaContFracSolution a z m * shiftedDens a z (m + 1) -
      upperIncompleteGammaContFracSolution a z (m + 1) * shiftedDens a z m =
      (-1 : ℂ) ^ m * ∏ j ∈ Finset.Icc 1 m, upperIncompleteGammaPartNum a z j := by
  induction m with
  | zero => simp [shiftedDens]
  | succ m ih =>
    rw [shiftedDens_add_two a z m, upperIncompleteGammaContFracSolution_add_two a hz m,
      Finset.prod_Icc_succ_top (by omega), pow_succ]
    linear_combination -upperIncompleteGammaPartNum a z (m + 1) * ih

/-- Minimality of `upperIncompleteGammaContFracSolution` against the continuant denominators when
`a ∉ {1, 2, 3, ...}`. -/
private theorem tendsto_upperIncompleteGammaContFracSolution_div_dens {a z : ℂ}
    (ha : ∀ m : ℕ, a ≠ (m : ℂ) + 1) (hz : z ∈ slitPlane) :
    (∀ᶠ n : ℕ in atTop, (upperIncompleteGammaContFrac a z).dens n ≠ 0) ∧
      Tendsto (fun n : ℕ ↦ upperIncompleteGammaContFracSolution a z (n + 1) /
        (upperIncompleteGammaContFrac a z).dens n) atTop (𝓝 0) := by
  obtain ⟨N, hN, hsum_top⟩ :=
    tendsto_norm_sum_upperIncompleteGammaContFrac_reductionOfOrder ha hz
  set f := upperIncompleteGammaContFracSolution a z
  set D := shiftedDens a z
  have htele : ∀ n ≥ N, D n / f n = D N / f N + ∑ m ∈ Finset.Ico N n, reductionTerm a z m := by
    intro n hn
    have hstep : ∀ m ∈ Finset.Ico N n,
        reductionTerm a z m = D (m + 1) / f (m + 1) - D m / f m := by
      intro m hm
      have hfm : f m ≠ 0 := hN m (Finset.mem_Ico.mp hm).1
      have hfm1 : f (m + 1) ≠ 0 := hN (m + 1) (by linarith [(Finset.mem_Ico.mp hm).1])
      rw [div_sub_div _ _ hfm1 hfm, reductionTerm,
        ← wronskian_upperIncompleteGammaContFracSolution a hz m]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_Ico_sub (fun m ↦ D m / f m) hn]
    abel
  have hDf_top : Tendsto (fun n : ℕ ↦ ‖(upperIncompleteGammaContFrac a z).dens n / f (n + 1)‖)
      atTop atTop := by
    have h1 : Tendsto (fun n : ℕ ↦ ‖D N / f N + ∑ m ∈ Finset.Ico N (n + 1), reductionTerm a z m‖)
        atTop atTop := by
      have hsub := hsum_top.comp (tendsto_add_atTop_nat 1)
      rw [Filter.tendsto_atTop] at hsub ⊢
      intro B
      filter_upwards [hsub (B + ‖D N / f N‖)] with n hn
      have hn' : B + ‖D N / f N‖ ≤ ‖∑ m ∈ Finset.Ico N (n + 1), reductionTerm a z m‖ := hn
      have htri := norm_sub_le (D N / f N + ∑ m ∈ Finset.Ico N (n + 1), reductionTerm a z m)
        (D N / f N)
      rw [add_sub_cancel_left] at htri
      linarith
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [← htele (n + 1) (by omega)]
    rfl
  have hdens_ne : ∀ᶠ n : ℕ in atTop, (upperIncompleteGammaContFrac a z).dens n ≠ 0 := by
    filter_upwards [hDf_top.eventually_gt_atTop 0] with n hn h0
    simp [h0] at hn
  refine ⟨hdens_ne, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  refine (tendsto_inv_atTop_zero.comp hDf_top).congr fun n ↦ ?_
  rw [Function.comp_apply, norm_div, norm_div, inv_div]

/-- Nonvanishing of `∏ j ∈ Icc 1 (2 * m + 1), upperIncompleteGammaPartNum ((m : ℂ) + 1) z j` for
`z ≠ 0`. -/
private theorem prod_upperIncompleteGammaPartNum_two_mul_add_one_ne_zero (m : ℕ) {z : ℂ}
    (hz0 : z ≠ 0) :
    (∏ j ∈ Finset.Icc 1 (2 * m + 1), upperIncompleteGammaPartNum ((m : ℂ) + 1) z j) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.mp hj
  rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    rw [show c + 1 + (c + 1) = 2 * (c + 1) by ring, upperIncompleteGammaPartNum_two_mul_succ]
    refine mul_ne_zero (fun h0 ↦ ?_) (inv_ne_zero hz0)
    have hre := congrArg Complex.re h0
    simp only [Nat.cast_add, Nat.cast_one, sub_re, add_re, natCast_re, one_re, zero_re] at hre
    have hcm : (c : ℝ) + 1 ≤ m := by exact_mod_cast (show c + 1 ≤ m by omega)
    linarith
  · rcases k with _ | c
    · simpa using inv_ne_zero hz0
    · rw [upperIncompleteGammaPartNum_two_mul_succ_add_one]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero c)) (inv_ne_zero hz0)

/-- At `a = m + 1`, the tail partial numerators after `a_{2 * m + 2} = 0` coincide with those at
`-(m : ℂ)`, so `shiftedDens ((m : ℂ) + 1) z (2 * m + 2 + r) = c₀ * shiftedDens (-(m : ℂ)) z (r + 1)`
with `c₀ ≠ 0`. -/
private theorem shiftedDens_natCast_add_one_tail (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ r : ℕ,
      shiftedDens ((m : ℂ) + 1) z (2 * m + 2 + r) = c₀ * shiftedDens (-(m : ℂ)) z (r + 1) := by
  have hc₀ : shiftedDens ((m : ℂ) + 1) z (2 * m + 2) ≠ 0 := by
    intro h0
    have hw := wronskian_upperIncompleteGammaContFracSolution ((m : ℂ) + 1) hz (2 * m + 1)
    rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring,
      upperIncompleteGammaContFracSolution_natCast_add_one_eq_zero m z le_rfl, zero_mul, sub_zero,
      h0, mul_zero] at hw
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (prod_upperIncompleteGammaPartNum_two_mul_add_one_ne_zero m (slitPlane_ne_zero hz)) hw.symm
  refine ⟨shiftedDens ((m : ℂ) + 1) z (2 * m + 2), hc₀, fun r ↦ ?_⟩
  refine Nat.strong_induction_on r fun r ih ↦ ?_
  rcases r with _ | _ | k
  · simp [shiftedDens]
  · have h1 : shiftedDens ((m : ℂ) + 1) z (2 * m + 2 + 1) =
        shiftedDens ((m : ℂ) + 1) z (2 * m + 2) := by
      rw [show 2 * m + 2 + 1 = (2 * m + 1) + 2 by ring,
        shiftedDens_add_two ((m : ℂ) + 1) z (2 * m + 1),
        show (2 * m + 1) + 1 = 2 * (m + 1) by ring,
        upperIncompleteGammaPartNum_two_mul_succ]
      push_cast; ring
    have h2 : shiftedDens (-(m : ℂ)) z 2 = 1 := by
      simpa [shiftedDens] using
        GenContFract.first_den_eq (upperIncompleteGammaContFrac_s_get? (-(m : ℂ)) z 0)
    rw [h1, h2, mul_one]
  · have hpart : upperIncompleteGammaPartNum ((m : ℂ) + 1) z (2 * m + 2 + (k + 1)) =
        upperIncompleteGammaPartNum (-(m : ℂ)) z ((k + 1) + 1) := by
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [show 2 * m + 2 + (j + j + 1) = 2 * (m + j + 1) + 1 by ring,
          show (j + j + 1) + 1 = 2 * (j + 1) by ring,
          upperIncompleteGammaPartNum_two_mul_succ_add_one,
          upperIncompleteGammaPartNum_two_mul_succ]
        push_cast; ring
      · rw [show 2 * m + 2 + (2 * j + 1 + 1) = 2 * ((m + j + 1) + 1) by ring,
          show (2 * j + 1 + 1) + 1 = 2 * (j + 1) + 1 by ring,
          upperIncompleteGammaPartNum_two_mul_succ,
          upperIncompleteGammaPartNum_two_mul_succ_add_one]
        push_cast; ring
    rw [show 2 * m + 2 + (k + 2) = (2 * m + 2 + k) + 2 by ring,
      shiftedDens_add_two ((m : ℂ) + 1) z (2 * m + 2 + k),
      show (2 * m + 2 + k) + 1 = 2 * m + 2 + (k + 1) by ring,
      ih (k + 1) (by omega), ih k (by omega), hpart,
      show (k + 2) + 1 = (k + 1) + 2 by ring, shiftedDens_add_two (-(m : ℂ)) z (k + 1)]
    ring

/-- **DLMF 8.9.2 on `Complex.slitPlane` (Legendre's continued fraction).**
For every `a : ℂ` and every `z ∈ Complex.slitPlane`, the continuant denominators of
`Complex.upperIncompleteGammaContFrac a z` are eventually nonzero and its convergents converge to
`TauCeti.shiftedLaplaceIntegral 0 (a - 1) z`. -/
theorem tendsto_upperIncompleteGammaContFrac_convs (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (∀ᶠ n : ℕ in atTop, (upperIncompleteGammaContFrac a z).dens n ≠ 0) ∧
      Tendsto (upperIncompleteGammaContFrac a z).convs atTop
        (𝓝 (TauCeti.shiftedLaplaceIntegral 0 (a - 1) z)) := by
  by_cases ha : ∀ m : ℕ, a ≠ (m : ℂ) + 1
  · obtain ⟨hdens, hmin⟩ := tendsto_upperIncompleteGammaContFracSolution_div_dens ha hz
    have hlim : Tendsto
        (fun n : ℕ ↦ TauCeti.shiftedLaplaceIntegral 0 (a - 1) z +
          upperIncompleteGammaContFracSolution a z (n + 1) /
            (upperIncompleteGammaContFrac a z).dens n)
        atTop (𝓝 (TauCeti.shiftedLaplaceIntegral 0 (a - 1) z)) := by
      simpa using hmin.const_add (TauCeti.shiftedLaplaceIntegral 0 (a - 1) z)
    refine ⟨hdens, hlim.congr' ?_⟩
    filter_upwards [hdens] with n hn
    have hsol := upperIncompleteGammaContFracSolution_succ_eq_nums_add_dens a hz n
    rw [upperIncompleteGammaContFracSolution_one] at hsol
    rw [GenContFract.conv_eq_num_div_den]
    field_simp [hn]
    linear_combination hsol
  · push Not at ha
    obtain ⟨m, rfl⟩ := ha
    have hb : ∀ k : ℕ, -(m : ℂ) ≠ (k : ℂ) + 1 := fun k hk ↦ by
      have hre := congrArg Complex.re hk
      simp only [neg_re, add_re, natCast_re, one_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨hdens_neg, _⟩ := tendsto_upperIncompleteGammaContFracSolution_div_dens hb hz
    obtain ⟨c₀, hc₀, htail⟩ := shiftedDens_natCast_add_one_tail m hz
    have hdens : ∀ᶠ n : ℕ in atTop,
        (upperIncompleteGammaContFrac ((m : ℂ) + 1) z).dens n ≠ 0 := by
      filter_upwards [eventually_ge_atTop (2 * m + 1),
        (tendsto_sub_atTop_nat (2 * m + 1)).eventually hdens_neg] with n hn hneg
      have h1 := htail (n - (2 * m + 1))
      rw [show 2 * m + 2 + (n - (2 * m + 1)) = n + 1 by omega] at h1
      simp only [shiftedDens] at h1
      rw [h1]
      exact mul_ne_zero hc₀ hneg
    refine ⟨hdens, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (2 * m + 1), hdens] with n hn hdn
    rw [GenContFract.conv_eq_num_div_den, upperIncompleteGammaContFrac_nums_natCast_add_one m z hn,
      add_sub_cancel_right, mul_div_cancel_right₀ _ hdn]

/-- **DLMF 8.9.2 on the open right half-plane `{z : ℂ | 0 < z.re}`.**
For every `a : ℂ` and `0 < z.re`, the convergents of Legendre's continued fraction converge to the
Laplace integral `∫ t in Ioi 0, exp (-z * t) * (1 + t) ^ (a - 1)`. -/
theorem tendsto_upperIncompleteGammaContFrac_convs_of_re_pos (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (upperIncompleteGammaContFrac a z).convs atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), cexp (-(z * (t : ℂ))) * (1 + (t : ℂ)) ^ (a - 1))) := by
  have h := (tendsto_upperIncompleteGammaContFrac_convs a (Or.inl hz)).2
  rwa [TauCeti.shiftedLaplaceIntegral_eq_integral_of_re_pos 0 (a - 1) hz,
    show (fun t : ℝ ↦ cexp (-(z * (t : ℂ))) * (t : ℂ) ^ 0 * (1 + (t : ℂ)) ^ (a - 1)) =
      fun t : ℝ ↦ cexp (-(z * (t : ℂ))) * (1 + (t : ℂ)) ^ (a - 1) by ext t; simp] at h

end Complex

end
