/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Finset.Sort
public import TauCeti.Algebra.Order.BigOperators.PowersetCard
public import TauCeti.Analysis.SpecialFunctions.Exp.Factorial
public import TauCeti.NumberTheory.SelbergSieve.Basic
public import TauCeti.NumberTheory.SelbergSieve.Dimension

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Brun's combinatorial sieve and fundamental estimate

Brun's pure combinatorial sieve replaces the full Möbius function `μ` on divisors of a squarefree
modulus `P` by two parity-truncated coefficient systems `λ⁺ = TauCeti.brunUpperWeight` (`ε = 1`) and
`λ⁻ = TauCeti.brunLowerWeight` (`ε = 0`). Writing the prime factors of a divisor `d ∣ P` in
strictly decreasing order `p₁ > ⋯ > p_r`, `TauCeti.brunWeight P y β ε d` equals `(μ d : ℝ)` when
every prefix `1 ≤ m ≤ r` of parity `m ≡ ε (mod 2)` satisfies `p_m < (y / (p₁ ⋯ p_m)) ^ (1 / β)`,
and `0` otherwise.

Expanding the inclusion-exclusion sum by the first failing prefix index yields pointwise Möbius
brackets `∑_{d ∣ r} λ⁻(d) ≤ 1_{r = 1} ≤ ∑_{d ∣ r} λ⁺(d)` on divisors of `P` (with the upper bracket
`BoundingSieve.IsUpperMoebius` holding unconditionally on all `n : ℕ` whenever `P ≠ 0`), modulus
bound `|λ_ε(d)| ≤ 1`, and strict support bound `d < y`. Combining the first-failure decomposition
with an Euler-product sieve dimension bound `s.HasProductDimension κ K` yields two-sided bounds on
`s.mainSum` and Brun's fundamental sieve estimate `BoundingSieve.brun_fundamental_estimate`.

## Main definitions and results

* `TauCeti.brunWeight`, `TauCeti.brunUpperWeight`, and `TauCeti.brunLowerWeight`: Brun's parity
  prefix-truncated combinatorial sieve coefficients `λ_ε`, `λ⁺`, and `λ⁻`.
* `TauCeti.lt_of_brunWeight_ne_zero`: strict divisor cutoff `d < y` for nonzero Brun coefficients
  whenever `1 < y`, `1 ≤ β`, and all prime factors of `P` are below `y`.
* `TauCeti.sum_divisors_brunLowerWeight_le`, `TauCeti.le_sum_divisors_brunUpperWeight`, and
  `TauCeti.isUpperMoebius_brunUpperWeight`: pointwise divisor brackets, together with the weighted
  sieve inequalities `BoundingSieve.sum_brunLowerWeight_mul_multSum_le_siftedSum` and
  `BoundingSieve.siftedSum_le_sum_brunUpperWeight_mul_multSum`.
* `BoundingSieve.brun_mainSum_bounds`: dimension-controlled lower and upper main-term bounds
  `(1 - δ) V ≤ s.mainSum λ⁻ ≤ V ≤ s.mainSum λ⁺ ≤ (1 + δ) V` with `δ = exp (9 κ + 1 - u) K ^ 10`.
* `BoundingSieve.brun_fundamental_estimate`: Brun's fundamental two-sided sifted-sum estimate.

## References

* V. Brun, *La série 1/5 + 1/7 + 1/11 + 1/13 + ⋯ où les dénominateurs sont « nombres premiers
  jumeaux » est convergente ou finie*, Bull. Sci. Math. 43 (1919), 100–104 and 124–128.
* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 12: "Brun's combinatorial sieve",
  Sections 12.2–12.4, Lemma 12.1 and Theorem 12.2 (with the lower main-term factor `1 - δ`
  corrected from the printed `1 + δ`).
-/

public noncomputable section

open Finset Nat ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TauCeti

/-- Brun's combinatorial sieve coefficient `λ_ε(d)` for modulus `P`, real cutoff `y`, parameter `β`,
and parity `ε`: equal to `(μ d : ℝ)` if `d ∈ P.divisors` and the decreasing prime factors
`p₁ > ⋯ > p_r` of `d` satisfy `p_m < (y / (p₁ ⋯ p_m)) ^ (1 / β)` for every `1 ≤ m ≤ r` with
`m % 2 = ε % 2`, and `0` otherwise. -/
def brunWeight (P : ℕ) (y β : ℝ) (ε d : ℕ) : ℝ :=
  open Classical in
  if d ∈ P.divisors ∧
      ∀ i : Fin (d.primeFactors.sort (· ≥ ·)).length,
        (i.1 + 1) % 2 = ε % 2 →
          (((d.primeFactors.sort (· ≥ ·))[i] : ℕ) : ℝ) <
            (y / ((((d.primeFactors.sort (· ≥ ·)).take (i.1 + 1)).prod : ℕ) : ℝ)) ^ (1 / β) then
    (μ d : ℝ)
  else
    0

/-- Brun's upper combinatorial sieve coefficient `λ⁺ = brunWeight P y β 1`. -/
def brunUpperWeight (P : ℕ) (y β : ℝ) : ℕ → ℝ :=
  brunWeight P y β 1

/-- Brun's lower combinatorial sieve coefficient `λ⁻ = brunWeight P y β 0`. -/
def brunLowerWeight (P : ℕ) (y β : ℝ) : ℕ → ℝ :=
  brunWeight P y β 0

/-- Explicit unfolding of `TauCeti.brunWeight`. -/
theorem brunWeight_def (P : ℕ) (y β : ℝ) (ε d : ℕ) :
    brunWeight P y β ε d =
      (open Classical in
        if d ∈ P.divisors ∧
            ∀ i : Fin (d.primeFactors.sort (· ≥ ·)).length,
              (i.1 + 1) % 2 = ε % 2 →
                (((d.primeFactors.sort (· ≥ ·))[i] : ℕ) : ℝ) <
                  (y / ((((d.primeFactors.sort (· ≥ ·)).take (i.1 + 1)).prod : ℕ) : ℝ)) ^
                    (1 / β) then
          (μ d : ℝ)
        else
          0) := (rfl)

/-- Evaluation of `TauCeti.brunUpperWeight` as `TauCeti.brunWeight` at parity `1`. -/
@[simp]
theorem brunUpperWeight_apply (P : ℕ) (y β : ℝ) (d : ℕ) :
    brunUpperWeight P y β d = brunWeight P y β 1 d := (rfl)

/-- Evaluation of `TauCeti.brunLowerWeight` as `TauCeti.brunWeight` at parity `0`. -/
@[simp]
theorem brunLowerWeight_apply (P : ℕ) (y β : ℝ) (d : ℕ) :
    brunLowerWeight P y β d = brunWeight P y β 0 d := (rfl)

/-- Prefix admissibility condition on a decreasing list of primes. -/
private def brunListCond (y β : ℝ) (ε : ℕ) (ps : List ℕ) : Prop :=
  ∀ i : Fin ps.length,
    (i.1 + 1) % 2 = ε % 2 →
      ((ps[i] : ℕ) : ℝ) < (y / (((ps.take (i.1 + 1)).prod : ℕ) : ℝ)) ^ (1 / β)

private lemma brunWeight_eq_ite_brunListCond (P : ℕ) (y β : ℝ) (ε d : ℕ) :
    brunWeight P y β ε d =
      open Classical in
      if d ∈ P.divisors ∧ brunListCond y β ε (d.primeFactors.sort (· ≥ ·)) then
        (μ d : ℝ)
      else 0 := by
  rw [brunWeight_def]
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd h1 h2
  · exact absurd h3 h1
  · rfl

/-- At `d = 1`, the empty prime-factor list is vacuously admissible, so `brunWeight P y β ε 1 = 1`
whenever `P ≠ 0`. -/
theorem brunWeight_one {P : ℕ} (hP : P ≠ 0) (y β : ℝ) (ε : ℕ) :
    brunWeight P y β ε 1 = 1 := by
  rw [brunWeight_eq_ite_brunListCond]
  split_ifs with h
  · simp
  · refine absurd ⟨Nat.one_mem_divisors.mpr hP, fun i ↦ Fin.elim0 (by simpa using i)⟩ h

/-- `brunUpperWeight P y β 1 = 1` whenever `P ≠ 0`. -/
theorem brunUpperWeight_one {P : ℕ} (hP : P ≠ 0) (y β : ℝ) :
    brunUpperWeight P y β 1 = 1 :=
  brunWeight_one hP y β 1

/-- `brunLowerWeight P y β 1 = 1` whenever `P ≠ 0`. -/
theorem brunLowerWeight_one {P : ℕ} (hP : P ≠ 0) (y β : ℝ) :
    brunLowerWeight P y β 1 = 1 :=
  brunWeight_one hP y β 0

/-- Outside the positive divisors of `P`, `brunWeight` vanishes. -/
theorem brunWeight_eq_zero_of_notMem_divisors {P : ℕ} {y β : ℝ} {ε d : ℕ} (hd : d ∉ P.divisors) :
    brunWeight P y β ε d = 0 := by
  rw [brunWeight_eq_ite_brunListCond]
  split_ifs with h
  · exact absurd h.1 hd
  · rfl

/-- `brunWeight` vanishes at `0`. -/
@[simp]
theorem brunWeight_zero (P : ℕ) (y β : ℝ) (ε : ℕ) :
    brunWeight P y β ε 0 = 0 :=
  brunWeight_eq_zero_of_notMem_divisors (by simp)

/-- At modulus `P = 0`, `brunWeight` vanishes identically. -/
@[simp]
theorem brunWeight_zero_left (y β : ℝ) (ε d : ℕ) :
    brunWeight 0 y β ε d = 0 :=
  brunWeight_eq_zero_of_notMem_divisors (by simp)

/-- Every Brun coefficient has absolute value at most `1`. -/
theorem abs_brunWeight_le_one (P : ℕ) (y β : ℝ) (ε d : ℕ) :
    |brunWeight P y β ε d| ≤ 1 := by
  rw [brunWeight_eq_ite_brunListCond]
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- Every upper Brun coefficient has absolute value at most `1`. -/
theorem abs_brunUpperWeight_le_one (P : ℕ) (y β : ℝ) (d : ℕ) :
    |brunUpperWeight P y β d| ≤ 1 :=
  abs_brunWeight_le_one P y β 1 d

/-- Every lower Brun coefficient has absolute value at most `1`. -/
theorem abs_brunLowerWeight_le_one (P : ℕ) (y β : ℝ) (d : ℕ) :
    |brunLowerWeight P y β d| ≤ 1 :=
  abs_brunWeight_le_one P y β 0 d

/-- For a squarefree positive divisor `d ∈ P.divisors`, `brunWeight P y β ε d` equals `(μ d : ℝ)`
if and only if every parity-selected prefix inequality holds. -/
theorem brunWeight_eq_moebius_iff {P : ℕ} {y β : ℝ} {ε d : ℕ}
    (hdP : d ∈ P.divisors) (hd : Squarefree d) :
    brunWeight P y β ε d = (μ d : ℝ) ↔
      ∀ i : Fin (d.primeFactors.sort (· ≥ ·)).length,
        (i.1 + 1) % 2 = ε % 2 →
          (((d.primeFactors.sort (· ≥ ·))[i] : ℕ) : ℝ) <
            (y / ((((d.primeFactors.sort (· ≥ ·)).take (i.1 + 1)).prod : ℕ) : ℝ)) ^ (1 / β) := by
  rw [brunWeight_def]
  have hμ : (μ d : ℝ) ≠ 0 := by
    exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hd
  split_ifs with h
  · exact ⟨fun _ ↦ h.2, fun _ ↦ rfl⟩
  · exact ⟨fun h0 ↦ absurd h0.symm hμ, fun hpref ↦ absurd ⟨hdP, hpref⟩ h⟩

private lemma lt_of_brunListCond_ge_two {ps : List ℕ} {d : ℕ} {y β : ℝ} {ε : ℕ}
    (hy0 : 0 < y) (hβ : 1 ≤ β) (hr : 2 ≤ ps.length) (hd_pos : 0 < d) (hd_prod : ps.prod = d)
    (hsort : ps.SortedGT) (hprime : ∀ p ∈ ps, p.Prime) (hpref : brunListCond y β ε ps) :
    (d : ℝ) < y := by
  have hβ0 : 0 < β := by linarith
  by_cases hpar : ps.length % 2 = ε % 2
  · have hlast := hpref ⟨ps.length - 1, by omega⟩
      (by simp [Nat.sub_add_cancel (by omega : 1 ≤ ps.length), hpar])
    have htake : (ps.take (ps.length - 1 + 1)).prod = d := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ ps.length), List.take_length, hd_prod]
    rw [htake] at hlast
    have hp1 : (1 : ℝ) ≤ (ps[ps.length - 1] : ℝ) := by
      exact_mod_cast (hprime _ (List.getElem_mem _)).one_lt.le
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd_pos
    have hpow : ((ps[ps.length - 1] : ℝ)) ^ β < y / d :=
      (Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hβ0).mp
        (by simpa only [Fin.getElem_fin, one_div] using hlast)
    simpa only [one_mul] using (lt_div_iff₀ hd0).mp ((Real.one_le_rpow hp1 hβ0.le).trans_lt hpow)
  · have hpen := hpref ⟨ps.length - 2, by omega⟩ (by dsimp; omega)
    set P_pen : ℕ := (ps.take (ps.length - 2 + 1)).prod
    have hsplit : d = P_pen * ps[ps.length - 1] := by
      have ht := congrArg List.prod
        (List.take_succ_eq_append_getElem (l := ps) (i := ps.length - 1) (by omega))
      rw [Nat.sub_add_cancel (by omega : 1 ≤ ps.length), List.take_length, hd_prod,
        List.prod_append, List.prod_singleton] at ht
      have h3 : ps.length - 2 + 1 = ps.length - 1 := by omega
      simpa only [P_pen, h3] using ht
    have hPpen_pos : (0 : ℝ) < P_pen := by
      rw [hsplit] at hd_pos; exact_mod_cast Nat.pos_of_mul_pos_right hd_pos
    have hpow : ((ps[ps.length - 2] : ℝ)) ^ β < y / P_pen :=
      (Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hβ0).mp
        (by simpa only [Fin.getElem_fin, one_div] using hpen)
    have hp_le : (ps[ps.length - 1] : ℝ) ≤ (ps[ps.length - 2] : ℝ) := by
      exact_mod_cast hsort.getElem_le_getElem_iff.mpr (by omega)
    have hp1 : (1 : ℝ) ≤ (ps[ps.length - 2] : ℝ) := by
      exact_mod_cast (hprime _ (List.getElem_mem _)).one_lt.le
    have hlast_le : (ps[ps.length - 1] : ℝ) ≤ ((ps[ps.length - 2] : ℝ)) ^ β :=
      hp_le.trans ((Real.rpow_one _).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hp1 hβ))
    have hd_cast : (d : ℝ) = (P_pen : ℝ) * (ps[ps.length - 1] : ℝ) := by exact_mod_cast hsplit
    rw [hd_cast]
    calc (P_pen : ℝ) * (ps[ps.length - 1] : ℝ)
      _ ≤ (P_pen : ℝ) * ((ps[ps.length - 2] : ℝ)) ^ β :=
        mul_le_mul_of_nonneg_left hlast_le hPpen_pos.le
      _ < (P_pen : ℝ) * (y / P_pen) := mul_lt_mul_of_pos_left hpow hPpen_pos
      _ = y := mul_div_cancel₀ y hPpen_pos.ne'

/-- Strict support bound for Brun coefficients: if `1 < y`, `1 ≤ β`, and every prime factor of `P`
is strictly below `y`, then any `d` with `brunWeight P y β ε d ≠ 0` satisfies `(d : ℝ) < y`. -/
theorem lt_of_brunWeight_ne_zero {P : ℕ} {y β : ℝ} {ε d : ℕ} (hy : 1 < y) (hβ : 1 ≤ β)
    (hprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < y) (hne : brunWeight P y β ε d ≠ 0) :
    (d : ℝ) < y := by
  rw [brunWeight_eq_ite_brunListCond] at hne
  split_ifs at hne with hcond
  swap
  · exact absurd rfl hne
  obtain ⟨hdP, hpref⟩ := hcond
  have hsq : Squarefree d :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (by exact_mod_cast hne)
  have hd_dvd : d ∣ P := Nat.dvd_of_mem_divisors hdP
  have hP0 : P ≠ 0 := (Nat.mem_divisors.mp hdP).2
  set ps := d.primeFactors.sort (· ≥ ·)
  have hd_prod : ps.prod = d := by
    rw [(d.primeFactors.sort_perm_toList (· ≥ ·)).prod_eq, Finset.prod_toList,
      Nat.prod_primeFactors_of_squarefree hsq]
  rcases eq_or_ne ps.length 0 with hr0 | hr_pos
  · have hnil : ps = [] := List.eq_nil_of_length_eq_zero hr0
    have hd1 : d = 1 := by simpa [hnil] using hd_prod.symm
    simpa [hd1] using hy
  · rcases eq_or_ne ps.length 1 with hr1 | hr2
    · obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hr1
      have hmem : p ∈ d.primeFactors := (Finset.mem_sort (· ≥ ·)).mp (by simp [ps, hp])
      have hpP : p ∈ P.primeFactors :=
        (Nat.mem_primeFactors_of_ne_zero hP0).mpr
          ⟨Nat.prime_of_mem_primeFactors hmem, (Nat.dvd_of_mem_primeFactors hmem).trans hd_dvd⟩
      have hdp : d = p := by simpa [hp] using hd_prod.symm
      simpa [hdp] using hprimes p hpP
    · exact lt_of_brunListCond_ge_two (by linarith) hβ (by omega) (Nat.pos_of_mem_divisors hdP)
        hd_prod d.primeFactors.sortedGT_sort
        (fun p hp ↦ Nat.prime_of_mem_primeFactors ((Finset.mem_sort (· ≥ ·)).mp hp)) hpref

/-! ### First-failure combinatorial identity (Kedlaya Lemma 12.1) -/

/-- First-failure condition on a decreasing list `ps`: `ps` is nonempty of parity `ε % 2`,
satisfies all parity-selected prefix bounds before the last element, and fails at the last element.
-/
private def brunFirstFailList (y β : ℝ) (ε : ℕ) (ps : List ℕ) : Prop :=
  ∃ hne : 0 < ps.length,
    ps.length % 2 = ε % 2 ∧
    ¬ (((ps[ps.length - 1] : ℕ) : ℝ) < (y / ((ps.prod : ℕ) : ℝ)) ^ (1 / β)) ∧
    ∀ i : Fin ps.length, i.1 < ps.length - 1 → (i.1 + 1) % 2 = ε % 2 →
      ((ps[i] : ℕ) : ℝ) < (y / (((ps.take (i.1 + 1)).prod : ℕ) : ℝ)) ^ (1 / β)

private lemma brunListCond_nil (y β : ℝ) (ε : ℕ) : brunListCond y β ε [] :=
  fun i ↦ Fin.elim0 i

private lemma brunListCond_cons (y β : ℝ) (ε p : ℕ) (ps : List ℕ) :
    brunListCond y β ε (p :: ps) ↔
      (1 % 2 = ε % 2 → (p : ℝ) < (y / p) ^ (1 / β)) ∧ brunListCond (y / p) β (ε + 1) ps := by
  simp only [brunListCond]
  constructor
  · intro h
    refine ⟨fun hpar ↦ by simpa using h ⟨0, Nat.succ_pos _⟩ hpar, fun j hj ↦ ?_⟩
    have hsucc := h ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ (by dsimp; omega)
    simpa [List.take_succ_cons, Nat.cast_mul, div_mul_eq_div_div] using hsucc
  · rintro ⟨h0, htail⟩ ⟨i, hi⟩ hpar
    cases i with
    | zero => simpa using h0 hpar
    | succ j =>
      have hj := htail ⟨j, Nat.lt_of_succ_lt_succ hi⟩ (by dsimp at hpar ⊢; omega)
      simpa [List.take_succ_cons, Nat.cast_mul, div_mul_eq_div_div] using hj

private lemma brunFirstFailList_nil (y β : ℝ) (ε : ℕ) : ¬ brunFirstFailList y β ε [] := by
  rintro ⟨hne, -⟩
  simp at hne

private lemma brunFirstFailList_singleton (y β : ℝ) (ε p : ℕ) :
    brunFirstFailList y β ε [p] ↔ 1 % 2 = ε % 2 ∧ ¬ ((p : ℝ) < (y / p) ^ (1 / β)) := by
  constructor
  · rintro ⟨_, hpar, hfail, _⟩
    exact ⟨hpar, by simpa using hfail⟩
  · rintro ⟨hpar, hfail⟩
    exact ⟨by simp, by simpa using hpar, by simpa using hfail, fun _ hi ↦ by simp at hi⟩

private lemma brunFirstFailList_cons_of_fail (y β : ℝ) (ε p : ℕ) (ps : List ℕ)
    (hpar : 1 % 2 = ε % 2) (hfail : ¬ ((p : ℝ) < (y / p) ^ (1 / β))) :
    brunFirstFailList y β ε (p :: ps) ↔ ps = [] := by
  cases ps with
  | nil =>
    rw [brunFirstFailList_singleton]
    exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨hpar, hfail⟩⟩
  | cons q qs =>
    simp only [reduceCtorEq, iff_false]
    rintro ⟨_, _, _, hprev⟩
    exact hfail (by simpa using hprev ⟨0, by simp⟩ (by simp) hpar)

private lemma brunFirstFailList_cons_of_ok (y β : ℝ) (ε p : ℕ) (ps : List ℕ)
    (hok : 1 % 2 = ε % 2 → (p : ℝ) < (y / p) ^ (1 / β)) :
    brunFirstFailList y β ε (p :: ps) ↔ brunFirstFailList (y / p) β (ε + 1) ps := by
  cases ps with
  | nil =>
    rw [brunFirstFailList_singleton]
    simp only [brunFirstFailList_nil, iff_false]
    rintro ⟨hpar, hfail⟩
    exact hfail (hok hpar)
  | cons q qs =>
    simp only [brunFirstFailList, List.length_cons]
    constructor
    · rintro ⟨_, hpar, hfail, hprev⟩
      refine ⟨Nat.succ_pos _, by omega, ?_, fun j hj hjpar ↦ ?_⟩
      · simpa [Nat.cast_mul, div_mul_eq_div_div] using hfail
      · have hs := hprev ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ (Nat.succ_lt_succ hj)
          (by dsimp at hjpar ⊢; omega)
        simpa [List.take_succ_cons, Nat.cast_mul, div_mul_eq_div_div] using hs
    · rintro ⟨_, hpar, hfail, hprev⟩
      refine ⟨Nat.succ_pos _, by omega, ?_, fun ⟨i, hi⟩ hlt hipar ↦ ?_⟩
      · simpa [Nat.cast_mul, div_mul_eq_div_div] using hfail
      · cases i with
        | zero => simpa using hok hipar
        | succ j =>
          have hj := hprev ⟨j, Nat.lt_of_succ_lt_succ hi⟩ (Nat.lt_of_succ_lt_succ hlt)
            (by dsimp at hipar ⊢; omega)
          simpa [List.take_succ_cons, Nat.cast_mul, div_mul_eq_div_div] using hj

private def brunAdmSum (Q : Finset ℕ) (f : ℕ → ℝ) (y β : ℝ) (ε : ℕ) : ℝ :=
  open Classical in
  ∑ S ∈ Q.powerset,
    if brunListCond y β ε (S.sort (· ≥ ·)) then (-1 : ℝ) ^ S.card * ∏ q ∈ S, f q else 0

private def brunFailSum (Q : Finset ℕ) (f : ℕ → ℝ) (y β : ℝ) (ε : ℕ) : ℝ :=
  open Classical in
  ∑ t ∈ Q.powerset.filter (fun t ↦ brunFirstFailList y β ε (t.sort (· ≥ ·))),
    (∏ q ∈ t, f q) * ∏ q ∈ Q.filter (fun q ↦ ∀ x ∈ t, q < x), (1 - f q)

private lemma filter_lt_insert_max {Q' t : Finset ℕ} {p : ℕ}
    (hgt : ∀ q ∈ Q', q < p) (ht : t ⊆ Q') (hne : t.Nonempty) :
    (insert p Q').filter (fun q ↦ ∀ x ∈ t, q < x) = Q'.filter (fun q ↦ ∀ x ∈ t, q < x) := by
  obtain ⟨x₀, hx₀⟩ := hne
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert]
  refine ⟨fun ⟨hq, hlt⟩ ↦ ⟨hq.resolve_left ?_, hlt⟩, fun ⟨hq, hlt⟩ ↦ ⟨Or.inr hq, hlt⟩⟩
  rintro rfl
  exact absurd (hlt x₀ hx₀) (not_lt_of_gt (hgt x₀ (ht hx₀)))

private lemma brunAdmSum_insert_max {Q' : Finset ℕ} {p : ℕ} (hp_not : p ∉ Q')
    (hgt : ∀ q ∈ Q', q < p) (f : ℕ → ℝ) (y β : ℝ) (ε : ℕ) :
    brunAdmSum (insert p Q') f y β ε = brunAdmSum Q' f y β ε +
      open Classical in
      ∑ S ∈ Q'.powerset,
        if brunListCond y β ε (p :: S.sort (· ≥ ·)) then
          -f p * ((-1 : ℝ) ^ S.card * ∏ q ∈ S, f q) else 0 := by
  classical
  have hpow_disj : Disjoint Q'.powerset (Q'.powerset.image (insert p)) := by
    rw [Finset.disjoint_left]
    intro S hS hins
    rcases Finset.mem_image.mp hins with ⟨T, _, rfl⟩
    exact hp_not (Finset.mem_powerset.mp hS (Finset.mem_insert_self p T))
  rw [brunAdmSum, Finset.powerset_insert, Finset.sum_union hpow_disj, brunAdmSum,
    Finset.sum_image (fun S hS T hT hST ↦ by
      have hpS : p ∉ S := fun h ↦ hp_not (Finset.mem_powerset.mp hS h)
      have hpT : p ∉ T := fun h ↦ hp_not (Finset.mem_powerset.mp hT h)
      simpa [Finset.erase_insert hpS, Finset.erase_insert hpT] using congrArg (·.erase p) hST)]
  refine congrArg (brunAdmSum Q' f y β ε + ·) (Finset.sum_congr rfl fun S hS ↦ ?_)
  have hpS : p ∉ S := fun h ↦ hp_not (Finset.mem_powerset.mp hS h)
  have hsort : (insert p S).sort (· ≥ ·) = p :: S.sort (· ≥ ·) :=
    Finset.sort_insert (· ≥ ·) (fun x hx ↦ (hgt x (Finset.mem_powerset.mp hS hx)).le) hpS
  rw [hsort, Finset.card_insert_of_notMem hpS, Finset.prod_insert hpS, pow_succ]
  split_ifs <;> ring

private lemma brunFailSum_insert_max {Q' : Finset ℕ} {p : ℕ} (hp_not : p ∉ Q')
    (hgt : ∀ q ∈ Q', q < p) (f : ℕ → ℝ) (y β : ℝ) (ε : ℕ) :
    brunFailSum (insert p Q') f y β ε = brunFailSum Q' f y β ε +
      open Classical in
      ∑ S ∈ Q'.powerset,
        if brunFirstFailList y β ε (p :: S.sort (· ≥ ·)) then
          f p * ((∏ q ∈ S, f q) *
            ∏ q ∈ (insert p Q').filter (fun q ↦ ∀ x ∈ insert p S, q < x), (1 - f q))
        else 0 := by
  classical
  have hpow_disj : Disjoint Q'.powerset (Q'.powerset.image (insert p)) := by
    rw [Finset.disjoint_left]
    intro S hS hins
    rcases Finset.mem_image.mp hins with ⟨T, _, rfl⟩
    exact hp_not (Finset.mem_powerset.mp hS (Finset.mem_insert_self p T))
  have hfail_Q' : ∑ t ∈ Q'.powerset,
      (if brunFirstFailList y β ε (t.sort (· ≥ ·)) then
        (∏ q ∈ t, f q) * ∏ q ∈ (insert p Q').filter (fun q ↦ ∀ x ∈ t, q < x), (1 - f q) else 0) =
      brunFailSum Q' f y β ε := by
    rw [brunFailSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    split_ifs with hf
    · obtain ⟨hlen, -⟩ := hf
      have hne_t : t.Nonempty := Finset.card_pos.mp (by simpa using hlen)
      rw [filter_lt_insert_max hgt (Finset.mem_powerset.mp ht) hne_t]
    · rfl
  rw [brunFailSum, Finset.sum_filter, Finset.powerset_insert, Finset.sum_union hpow_disj, hfail_Q',
    Finset.sum_image (fun S hS T hT hST ↦ by
      have hpS : p ∉ S := fun h ↦ hp_not (Finset.mem_powerset.mp hS h)
      have hpT : p ∉ T := fun h ↦ hp_not (Finset.mem_powerset.mp hT h)
      simpa [Finset.erase_insert hpS, Finset.erase_insert hpT] using congrArg (·.erase p) hST)]
  refine congrArg (brunFailSum Q' f y β ε + ·) (Finset.sum_congr rfl fun S hS ↦ ?_)
  have hpS : p ∉ S := fun h ↦ hp_not (Finset.mem_powerset.mp hS h)
  have hsort : (insert p S).sort (· ≥ ·) = p :: S.sort (· ≥ ·) :=
    Finset.sort_insert (· ≥ ·) (fun x hx ↦ (hgt x (Finset.mem_powerset.mp hS hx)).le) hpS
  rw [hsort, Finset.prod_insert hpS, mul_assoc]

private lemma brun_first_failure_step_fail {Q' : Finset ℕ} {p : ℕ} (hp_not : p ∉ Q')
    (hgt : ∀ q ∈ Q', q < p) (f : ℕ → ℝ) (y β : ℝ) (ε : ℕ)
    (hpar1 : 1 % 2 = ε % 2) (hnlt : ¬ ((p : ℝ) < (y / p) ^ (1 / β)))
    (ih1 : brunAdmSum Q' f y β ε - ∏ q ∈ Q', (1 - f q) =
      (-1 : ℝ) ^ (ε + 1) * brunFailSum Q' f y β ε) :
    brunAdmSum (insert p Q') f y β ε - ∏ q ∈ insert p Q', (1 - f q) =
      (-1 : ℝ) ^ (ε + 1) * brunFailSum (insert p Q') f y β ε := by
  classical
  rw [brunAdmSum_insert_max hp_not hgt, brunFailSum_insert_max hp_not hgt,
    Finset.prod_insert hp_not]
  have hadm_zero : ∑ S ∈ Q'.powerset,
      (if brunListCond y β ε (p :: S.sort (· ≥ ·)) then
        -f p * ((-1 : ℝ) ^ S.card * ∏ q ∈ S, f q) else 0) = 0 :=
    Finset.sum_eq_zero fun S _ ↦ by
      split_ifs with h
      · exact absurd (((brunListCond_cons y β ε p _).mp h).1 hpar1) hnlt
      · rfl
  have hfail_single : ∑ S ∈ Q'.powerset,
      (if brunFirstFailList y β ε (p :: S.sort (· ≥ ·)) then
        f p * ((∏ q ∈ S, f q) *
          ∏ q ∈ (insert p Q').filter (fun q ↦ ∀ x ∈ insert p S, q < x), (1 - f q))
      else 0) = f p * ∏ q ∈ Q', (1 - f q) := by
    have hcond_eq : ∀ S ∈ Q'.powerset,
        brunFirstFailList y β ε (p :: S.sort (· ≥ ·)) ↔ S = ∅ := fun S _ ↦ by
      rw [brunFirstFailList_cons_of_fail y β ε p _ hpar1 hnlt,
        ← Finset.card_eq_zero, ← Finset.length_sort (r := (· ≥ ·)), List.length_eq_zero_iff]
    rw [Finset.sum_congr rfl fun S hS ↦ by rw [if_congr (hcond_eq S hS) rfl rfl]]
    rw [Finset.sum_ite_eq' Q'.powerset ∅]
    split_ifs with hemp
    swap
    · exact absurd (Finset.empty_mem_powerset Q') hemp
    have hp_set : insert p (∅ : Finset ℕ) = {p} := rfl
    have hflt : (insert p Q').filter (fun q ↦ ∀ x ∈ ({p} : Finset ℕ), q < x) = Q' := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, forall_eq]
      exact ⟨fun ⟨hq, hqp⟩ ↦ hq.resolve_left hqp.ne, fun hq ↦ ⟨Or.inr hq, hgt q hq⟩⟩
    rw [Finset.prod_empty, one_mul, hp_set, hflt]
  have hsign : (-1 : ℝ) ^ (ε + 1) = 1 := Even.neg_one_pow (Nat.even_iff.mpr (by omega))
  rw [hsign] at ih1 ⊢
  rw [hadm_zero, hfail_single]
  linear_combination ih1

private lemma brun_first_failure_step_ok {Q' : Finset ℕ} {p : ℕ} (hp_not : p ∉ Q')
    (hgt : ∀ q ∈ Q', q < p) (f : ℕ → ℝ) (y β : ℝ) (ε : ℕ)
    (hok : 1 % 2 = ε % 2 → (p : ℝ) < (y / p) ^ (1 / β))
    (ih1 : brunAdmSum Q' f y β ε - ∏ q ∈ Q', (1 - f q) =
      (-1 : ℝ) ^ (ε + 1) * brunFailSum Q' f y β ε)
    (ih2 : brunAdmSum Q' f (y / p) β (ε + 1) - ∏ q ∈ Q', (1 - f q) =
      (-1 : ℝ) ^ (ε + 1 + 1) * brunFailSum Q' f (y / p) β (ε + 1)) :
    brunAdmSum (insert p Q') f y β ε - ∏ q ∈ insert p Q', (1 - f q) =
      (-1 : ℝ) ^ (ε + 1) * brunFailSum (insert p Q') f y β ε := by
  classical
  rw [brunAdmSum_insert_max hp_not hgt, brunFailSum_insert_max hp_not hgt,
    Finset.prod_insert hp_not]
  have hadm_rec : ∑ S ∈ Q'.powerset,
      (if brunListCond y β ε (p :: S.sort (· ≥ ·)) then
        -f p * ((-1 : ℝ) ^ S.card * ∏ q ∈ S, f q) else 0) =
      -f p * brunAdmSum Q' f (y / p) β (ε + 1) := by
    rw [brunAdmSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    have hiff : brunListCond y β ε (p :: S.sort (· ≥ ·)) ↔
        brunListCond (y / p) β (ε + 1) (S.sort (· ≥ ·)) :=
      (brunListCond_cons y β ε p _).trans ⟨And.right, fun h ↦ ⟨hok, h⟩⟩
    rw [if_congr hiff rfl rfl]
    split_ifs <;> ring
  have hfail_rec : ∑ S ∈ Q'.powerset,
      (if brunFirstFailList y β ε (p :: S.sort (· ≥ ·)) then
        f p * ((∏ q ∈ S, f q) *
          ∏ q ∈ (insert p Q').filter (fun q ↦ ∀ x ∈ insert p S, q < x), (1 - f q))
      else 0) = f p * brunFailSum Q' f (y / p) β (ε + 1) := by
    rw [brunFailSum, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS ↦ ?_
    rw [if_congr (brunFirstFailList_cons_of_ok y β ε p _ hok) rfl rfl]
    split_ifs with hf
    · obtain ⟨hlen, -⟩ := hf
      have hne_S : S.Nonempty := Finset.card_pos.mp (by simpa using hlen)
      have hflt : (insert p Q').filter (fun q ↦ ∀ x ∈ insert p S, q < x) =
          Q'.filter (fun q ↦ ∀ x ∈ S, q < x) := by
        rw [← filter_lt_insert_max hgt (Finset.mem_powerset.mp hS) hne_S]
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
        refine ⟨fun ⟨hq, _, hSlt⟩ ↦ ⟨hq, hSlt⟩, fun ⟨hq, hSlt⟩ ↦ ⟨hq, ?_, hSlt⟩⟩
        obtain ⟨x₀, hx₀⟩ := hne_S
        exact (hSlt x₀ hx₀).trans (hgt x₀ (Finset.mem_powerset.mp hS hx₀))
      rw [hflt]
    · simp
  have hpow_sign : (-1 : ℝ) ^ (ε + 1 + 1) = -((-1 : ℝ) ^ (ε + 1)) := by ring
  rw [hpow_sign] at ih2
  rw [hadm_rec, hfail_rec]
  linear_combination ih1 - f p * ih2

/-- Kedlaya's Lemma 12.1: the difference between the parity-truncated inclusion-exclusion sum over
`Q` and the full Euler product `∏_{q ∈ Q} (1 - f q)` equals `(-1) ^ (ε + 1)` times the sum of
first-failure masses. -/
private lemma brun_first_failure_identity (Q : Finset ℕ) (f : ℕ → ℝ) :
    ∀ (y β : ℝ) (ε : ℕ),
      brunAdmSum Q f y β ε - ∏ q ∈ Q, (1 - f q) = (-1 : ℝ) ^ (ε + 1) * brunFailSum Q f y β ε := by
  classical
  induction hcard : Q.card generalizing Q with
  | zero =>
    intro y β ε
    rw [Finset.card_eq_zero.mp hcard]
    simp [brunAdmSum, brunFailSum, Finset.sum_filter, brunListCond_nil, brunFirstFailList_nil]
  | succ k ih =>
    intro y β ε
    have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
    set p := Q.max' hQne
    set Q' := Q.erase p
    have hp_mem : p ∈ Q := Q.max'_mem hQne
    have hp_not : p ∉ Q' := Finset.notMem_erase p Q
    have hQ'_card : Q'.card = k := by
      dsimp only [Q']
      rw [Finset.card_erase_of_mem hp_mem, hcard, Nat.add_sub_cancel]
    have hgt : ∀ q ∈ Q', q < p := fun q hq ↦
      lt_of_le_of_ne (Q.le_max' q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq)
    rw [(Finset.insert_erase hp_mem).symm]
    by_cases hp_fail : 1 % 2 = ε % 2 ∧ ¬ ((p : ℝ) < (y / p) ^ (1 / β))
    · exact brun_first_failure_step_fail hp_not hgt f y β ε hp_fail.1 hp_fail.2
        (ih Q' hQ'_card y β ε)
    · exact brun_first_failure_step_ok hp_not hgt f y β ε (by tauto)
        (ih Q' hQ'_card y β ε) (ih Q' hQ'_card (y / p) β (ε + 1))

private lemma brunFailSum_nonneg {Q : Finset ℕ} {f : ℕ → ℝ}
    (hf0 : ∀ q ∈ Q, 0 ≤ f q) (hf1 : ∀ q ∈ Q, f q ≤ 1) (y β : ℝ) (ε : ℕ) :
    0 ≤ brunFailSum Q f y β ε := by
  classical
  refine Finset.sum_nonneg fun t ht ↦ mul_nonneg ?_ ?_
  · have htQ : t ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    exact Finset.prod_nonneg fun q hq ↦ hf0 q (htQ hq)
  · exact Finset.prod_nonneg fun q hq ↦ sub_nonneg.mpr (hf1 q (Finset.mem_filter.mp hq).1)

/-- Express `∑ d ∈ r.divisors, brunWeight P y β ε d * g d` (for multiplicative `g`, `P ≠ 0`, and
`r ∣ P`) as `brunAdmSum r.primeFactors g y β ε`. -/
private lemma sum_divisors_brunWeight_mul_eq_brunAdmSum {P r : ℕ} (hP0 : P ≠ 0) (hrP : r ∣ P)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) (y β : ℝ) (ε : ℕ) :
    ∑ d ∈ r.divisors, brunWeight P y β ε d * g d = brunAdmSum r.primeFactors g y β ε := by
  classical
  have hr0 : r ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hrP
  have hsub : ∑ d ∈ r.divisors, brunWeight P y β ε d * g d =
      ∑ d ∈ r.divisors.filter Squarefree, brunWeight P y β ε d * g d := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun d hd hnsq ↦ ?_).symm
    have hsq : ¬ Squarefree d := fun hs ↦ hnsq (Finset.mem_filter.mpr ⟨hd, hs⟩)
    rw [brunWeight_eq_ite_brunListCond]
    split_ifs
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    · simp
  rw [hsub, Nat.sum_divisors_filter_squarefree hr0, Nat.factors_eq, brunAdmSum]
  refine Finset.sum_congr rfl fun S hS ↦ ?_
  have hS_sub : S ⊆ r.primeFactors := Finset.mem_powerset.mp hS
  have hS_primes : ∀ p ∈ S, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors (hS_sub hp)
  have hval : S.val.prod = ∏ p ∈ S, p := S.prod_val.trans (Finset.prod_congr rfl fun _ _ ↦ rfl)
  have hd_pf : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hS_primes
  have hd_dvd_r : (∏ p ∈ S, p) ∣ r :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hS_sub).trans r.prod_primeFactors_dvd
  have hdP : (∏ p ∈ S, p) ∈ P.divisors := Nat.mem_divisors.mpr ⟨hd_dvd_r.trans hrP, hP0⟩
  have hμ : (μ (∏ p ∈ S, p) : ℝ) = (-1 : ℝ) ^ S.card := by
    have hm := (isMultiplicative_moebius.intCast :
      (μ : ArithmeticFunction ℝ).IsMultiplicative).map_prod_of_subset_primeFactors r S hS_sub
    rw [intCoe_apply] at hm
    rw [hm, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun p hp ↦ by
      simp [ArithmeticFunction.moebius_apply_prime (hS_primes p hp)]
  have hg_prod : g (∏ p ∈ S, p) = ∏ p ∈ S, g p :=
    hg.map_prod_of_subset_primeFactors r S hS_sub
  rw [hval, brunWeight_eq_ite_brunListCond, hd_pf, hμ, hg_prod]
  split_ifs with h1 hc hc2
  · rfl
  · exact absurd h1.2 hc
  · exact absurd ⟨hdP, hc2⟩ h1
  · exact zero_mul _

private lemma sum_divisors_brunWeight_sub_ite_eq {P r : ℕ} (hP : P ≠ 0) (hr : r ∣ P)
    (y β : ℝ) (ε : ℕ) :
    (∑ d ∈ r.divisors, brunWeight P y β ε d) - (if r = 1 then 1 else 0) =
      (-1 : ℝ) ^ (ε + 1) *
        brunFailSum r.primeFactors (fun q ↦ (ζ : ArithmeticFunction ℝ) q) y β ε := by
  have hr0 : r ≠ 0 := ne_zero_of_dvd_ne_zero hP hr
  have hzeta : ∑ d ∈ r.divisors, brunWeight P y β ε d =
      ∑ d ∈ r.divisors, brunWeight P y β ε d * (ζ : ArithmeticFunction ℝ) d := by
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [natCoe_apply, zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne', Nat.cast_one, mul_one]
  have hprod : (∏ q ∈ r.primeFactors, (1 - (ζ : ArithmeticFunction ℝ) q)) =
      if r = 1 then 1 else 0 := by
    split_ifs with hr1
    · subst hr1; simp
    · obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hr1
      have hp : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hr0⟩
      exact Finset.prod_eq_zero hp
        (by rw [natCoe_apply, zeta_apply_ne hp_prime.ne_zero]; norm_num)
  rw [hzeta, sum_divisors_brunWeight_mul_eq_brunAdmSum hP hr isMultiplicative_zeta.natCast, ← hprod]
  exact brun_first_failure_identity r.primeFactors _ y β ε

private lemma brunFailSum_zeta_nonneg (r : ℕ) (y β : ℝ) (ε : ℕ) :
    0 ≤ brunFailSum r.primeFactors (fun q ↦ (ζ : ArithmeticFunction ℝ) q) y β ε :=
  brunFailSum_nonneg
    (fun q hq ↦ by
      rw [natCoe_apply, zeta_apply_ne (Nat.prime_of_mem_primeFactors hq).ne_zero]; norm_num)
    (fun q hq ↦ by
      rw [natCoe_apply, zeta_apply_ne (Nat.prime_of_mem_primeFactors hq).ne_zero]; norm_num)
    y β ε

/-! ### Pointwise divisor brackets -/

/-- Lower Brun divisor bracket: for every divisor `r ∣ P`,
`∑ d ∈ r.divisors, brunLowerWeight P y β d ≤ if r = 1 then 1 else 0`. -/
theorem sum_divisors_brunLowerWeight_le {P r : ℕ} (hr : r ∣ P) (y β : ℝ) :
    ∑ d ∈ r.divisors, brunLowerWeight P y β d ≤ if r = 1 then 1 else 0 := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp only [brunLowerWeight_apply, brunWeight_zero_left, Finset.sum_const_zero]
    split_ifs <;> norm_num
  · simp only [brunLowerWeight_apply]
    have hid := sum_divisors_brunWeight_sub_ite_eq hP hr y β 0
    have hnn := brunFailSum_zeta_nonneg r y β 0
    rw [_root_.pow_one, neg_one_mul] at hid
    linarith

/-- Upper Brun divisor bracket on divisors `r ∣ P` with `P ≠ 0`. -/
theorem le_sum_divisors_brunUpperWeight {P r : ℕ} (hP : P ≠ 0) (hr : r ∣ P) (y β : ℝ) :
    (if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, brunUpperWeight P y β d := by
  simp only [brunUpperWeight_apply]
  have hid := sum_divisors_brunWeight_sub_ite_eq hP hr y β 1
  have hnn := brunFailSum_zeta_nonneg r y β 1
  have hsign : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
  rw [hsign, one_mul] at hid
  linarith

/-- Whenever `P ≠ 0`, `brunUpperWeight P y β` satisfies `BoundingSieve.IsUpperMoebius` on all
`n : ℕ`. -/
theorem isUpperMoebius_brunUpperWeight {P : ℕ} (hP : P ≠ 0) (y β : ℝ) :
    BoundingSieve.IsUpperMoebius (brunUpperWeight P y β) := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · set r := Nat.gcd P n
    have hrP : r ∣ P := Nat.gcd_dvd_left P n
    have hrn : r ∣ n := Nat.gcd_dvd_right P n
    have hsum_eq : ∑ d ∈ n.divisors, brunUpperWeight P y β d =
        ∑ d ∈ r.divisors, brunUpperWeight P y β d := by
      refine (Finset.sum_subset (Nat.divisors_subset_of_dvd hn0 hrn) fun d hdn hdr ↦ ?_).symm
      refine brunWeight_eq_zero_of_notMem_divisors fun hdP ↦ hdr ?_
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors hdP) (Nat.dvd_of_mem_divisors hdn),
          ne_zero_of_dvd_ne_zero hP hrP⟩
    rw [hsum_eq]
    refine le_trans ?_ (le_sum_divisors_brunUpperWeight hP hrP y β)
    split_ifs with hn1 hr1
    · exact le_rfl
    · subst hn1
      exact absurd (Nat.gcd_one_right P) hr1
    · norm_num
    · exact le_rfl

end TauCeti

namespace BoundingSieve

open TauCeti

/-- Lower weighted sifted-sum inequality for Brun's lower coefficients `brunLowerWeight`. -/
theorem sum_brunLowerWeight_mul_multSum_le_siftedSum (s : BoundingSieve) (y β : ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, brunLowerWeight s.prodPrimes y β d * s.multSum d ≤ s.siftedSum :=
  s.sum_mul_multSum_le_siftedSum_of_dvd_prodPrimes _ fun _ hr ↦
    sum_divisors_brunLowerWeight_le hr y β

/-- Upper weighted sifted-sum inequality for Brun's upper coefficients `brunUpperWeight`. -/
theorem siftedSum_le_sum_brunUpperWeight_mul_multSum (s : BoundingSieve) (y β : ℝ) :
    s.siftedSum ≤ ∑ d ∈ s.prodPrimes.divisors, brunUpperWeight s.prodPrimes y β d * s.multSum d :=
  s.siftedSum_le_sum_of_upperMoebius _ (isUpperMoebius_brunUpperWeight s.prodPrimes_ne_zero y β)

/-! ### Analytic tail and prefix estimates for Brun's main terms -/

private lemma brun_tail_ratio_bounds :
    0 ≤ Real.exp (10 / 9) / 9 ∧
      Real.exp (10 / 9) / 9 < Real.exp (-1) ∧
      (Real.exp (10 / 9) / 9) / (1 - Real.exp (10 / 9) / 9) ≤ 1 := by
  have hexp1 : Real.exp 1 < (272 / 100 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hexp19_pow : (Real.exp (19 / 9)) ^ 9 < (9 : ℝ) ^ 9 := by
    have hpow9 : (Real.exp (19 / 9)) ^ 9 = (Real.exp 1) ^ 19 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      norm_num
    rw [hpow9]
    calc (Real.exp 1) ^ 19
      _ < (272 / 100 : ℝ) ^ 19 := pow_lt_pow_left₀ hexp1 (Real.exp_pos 1).le (by omega)
      _ < (9 : ℝ) ^ 9 := by norm_num
  have hexp19 : Real.exp (19 / 9) < 9 :=
    lt_of_pow_lt_pow_left₀ 9 (by positivity) hexp19_pow
  have ha_lt : Real.exp (10 / 9) / 9 < Real.exp (-1) := by
    have hsplit : Real.exp (10 / 9) = Real.exp (19 / 9) * Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    rw [hsplit, mul_div_right_comm]
    calc (Real.exp (19 / 9) / 9) * Real.exp (-1)
      _ < 1 * Real.exp (-1) :=
        mul_lt_mul_of_pos_right ((div_lt_one (by norm_num)).mpr hexp19) (Real.exp_pos _)
      _ = Real.exp (-1) := one_mul _
  have hexp_neg1_lt : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) (by linarith [Real.exp_one_gt_d9])
  exact ⟨by positivity, ha_lt, (div_le_one (by linarith)).mpr (by linarith)⟩

/-- Every first-failure list of positive primes `< z` with `z ^ u = y` and `1 < z` has length at
least `⌊u - β⌋₊ + 1`. -/
private lemma brun_firstFail_card_ge {ps : List ℕ} {y β u z : ℝ}
    (hy0 : 0 < y) (hβ0 : 0 < β) (hu : β ≤ u) (hz1 : 1 < z) (hzy : z ^ u = y)
    (hpos : ∀ p ∈ ps, 0 < p) (hmem : ∀ p ∈ ps, (p : ℝ) < z)
    {ε : ℕ} (hfail : brunFirstFailList y β ε ps) :
    ⌊u - β⌋₊ + 1 ≤ ps.length := by
  obtain ⟨_, _, hnlt, _⟩ := hfail
  have hprod_pos : (0 : ℝ) < (ps.prod : ℕ) := by exact_mod_cast List.prod_pos hpos
  have hy_div : y / ((ps.prod : ℕ) : ℝ) ≤ ((ps[ps.length - 1] : ℝ)) ^ β :=
    (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) hβ0).mp
      (by simpa only [one_div] using not_lt.mp hnlt)
  have hy_le : y ≤ ((ps[ps.length - 1] : ℝ)) ^ β * (ps.prod : ℕ) :=
    (div_le_iff₀ hprod_pos).mp hy_div
  have hlast_lt : ((ps[ps.length - 1] : ℝ)) ^ β < z ^ β :=
    Real.rpow_lt_rpow (Nat.cast_nonneg _) (hmem _ (List.getElem_mem _)) hβ0
  have hprod_le : ((ps.prod : ℕ) : ℝ) ≤ z ^ ps.length := by
    simpa only [Nat.cast_list_prod, Nat.coe_castRingHom] using
      List.prod_map_le_pow_length₀ (f := Nat.castRingHom ℝ)
        (fun _ _ ↦ by simp) fun p hp ↦ by simpa only [Nat.coe_castRingHom] using (hmem p hp).le
  have hzu_lt : z ^ u < z ^ (β + (ps.length : ℝ)) := by
    calc z ^ u = y := hzy
      _ ≤ ((ps[ps.length - 1] : ℝ)) ^ β * (ps.prod : ℕ) := hy_le
      _ < z ^ β * (ps.prod : ℕ) := mul_lt_mul_of_pos_right hlast_lt hprod_pos
      _ ≤ z ^ β * z ^ ps.length :=
        mul_le_mul_of_nonneg_left hprod_le (Real.rpow_pos_of_pos (by linarith) β).le
      _ = z ^ (β + (ps.length : ℝ)) := by rw [Real.rpow_add (by linarith), Real.rpow_natCast]
  have hu_lt : u - β < (ps.length : ℝ) := by
    linarith [(Real.rpow_lt_rpow_left_iff hz1).mp hzu_lt]
  exact Nat.succ_le_of_lt ((Nat.floor_lt (sub_nonneg.mpr hu)).mpr hu_lt)

private lemma brun_prefix_quot_step {ps : List ℕ} {y β z : ℝ}
    (hβ1 : 1 < β) (hz1 : 1 < z) (hsort : ps.SortedGT) (hpos : ∀ p ∈ ps, 0 < p)
    {r : ℕ} (hr2 : r + 2 < ps.length)
    (ih : z ^ (β * (1 - 1 / β) ^ r) ≤ y / (((ps.take r).prod : ℕ) : ℝ))
    (hstep : (ps[r]'(by omega) : ℝ) < (y / (((ps.take (r + 1)).prod : ℕ) : ℝ)) ^ (1 / β)) :
    z ^ (β * (1 - 1 / β) ^ (r + 2)) ≤ y / (((ps.take (r + 2)).prod : ℕ) : ℝ) := by
  set α : ℝ := 1 - 1 / β
  set Y_r : ℝ := y / (((ps.take r).prod : ℕ) : ℝ)
  have hβ0 : 0 < β := by linarith
  have hα0 : 0 < α := sub_pos.mpr ((div_lt_one hβ0).mpr hβ1)
  have hYr0 : 0 < Y_r :=
    lt_of_lt_of_le zero_lt_one ((Real.one_le_rpow hz1.le (by positivity)).trans ih)
  have htake_r1 : (((ps.take (r + 1)).prod : ℕ) : ℝ) =
      (((ps.take r).prod : ℕ) : ℝ) * (ps[r] : ℝ) := by
    rw [List.take_succ_eq_append_getElem (by omega), List.prod_append, List.prod_singleton,
      Nat.cast_mul]
  rw [htake_r1, div_mul_eq_div_div] at hstep
  have hpr_pos : (0 : ℝ) < (ps[r] : ℝ) := by exact_mod_cast hpos _ (List.getElem_mem _)
  have hpr1_pos : (0 : ℝ) < (ps[r + 1] : ℝ) := by exact_mod_cast hpos _ (List.getElem_mem _)
  have hpr_pow : ((ps[r] : ℝ)) ^ (β + 1) ≤ Y_r := by
    rw [Real.rpow_add hpr_pos, Real.rpow_one]
    exact (le_div_iff₀ hpr_pos).mp (((Real.lt_rpow_inv_iff_of_pos hpr_pos.le (by positivity)
      hβ0).mp (by simpa only [one_div] using hstep)).le)
  have hpr_bound : (ps[r] : ℝ) ≤ Y_r ^ (1 / (β + 1)) := by
    simpa only [← Real.rpow_mul hpr_pos.le, mul_one_div_cancel (by positivity : β + 1 ≠ 0),
      Real.rpow_one] using
      Real.rpow_le_rpow (by positivity) hpr_pow (by positivity : 0 ≤ 1 / (β + 1))
  have hpr1_bound : (ps[r + 1] : ℝ) ≤ Y_r ^ (1 / (β + 1)) :=
    (Nat.cast_le.mpr (hsort.getElem_le_getElem_iff.mpr (by omega))).trans hpr_bound
  have hYr2_ge : Y_r ^ ((β - 1) / (β + 1)) ≤ y / (((ps.take (r + 2)).prod : ℕ) : ℝ) := by
    rw [List.take_succ_eq_append_getElem (l := ps) (i := r + 1) (by omega), List.prod_append,
      List.prod_singleton, Nat.cast_mul, htake_r1, mul_assoc, div_mul_eq_div_div]
    have hprod_pr : (ps[r] : ℝ) * (ps[r + 1] : ℝ) ≤ Y_r ^ (2 / (β + 1)) := by
      simpa only [← Real.rpow_add hYr0, (by ring : 1 / (β + 1) + 1 / (β + 1) = 2 / (β + 1))]
        using mul_le_mul hpr_bound hpr1_bound hpr1_pos.le (by positivity)
    have hexp_diff : Y_r ^ ((β - 1) / (β + 1)) = Y_r / Y_r ^ (2 / (β + 1)) := by
      nth_rw 2 [← Real.rpow_one Y_r]; rw [← Real.rpow_sub hYr0]; congr 1; field_simp; ring
    exact hexp_diff ▸ div_le_div_of_nonneg_left hYr0.le (mul_pos hpr_pos hpr1_pos) hprod_pr
  have hα2 : α ^ 2 ≤ (β - 1) / (β + 1) := by
    have hsq : α ^ 2 = (β - 1) ^ 2 / β ^ 2 := by simp only [α]; field_simp
    rw [hsq, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  calc z ^ (β * α ^ (r + 2))
    _ = z ^ (β * α ^ r * α ^ 2) := by rw [_root_.pow_add, mul_assoc]
    _ ≤ z ^ (β * α ^ r * ((β - 1) / (β + 1))) :=
      Real.rpow_le_rpow_of_exponent_le hz1.le (mul_le_mul_of_nonneg_left hα2 (by positivity))
    _ = (z ^ (β * α ^ r)) ^ ((β - 1) / (β + 1)) := Real.rpow_mul (by linarith) _ _
    _ ≤ Y_r ^ ((β - 1) / (β + 1)) := Real.rpow_le_rpow (by positivity) ih (by positivity)
    _ ≤ y / (((ps.take (r + 2)).prod : ℕ) : ℝ) := hYr2_ge

/-- Two-step inductive lower bound on `y / (ps.take r).prod` along parity-matched prefix indices. -/
private lemma brun_prefix_quot_ge {ps : List ℕ} {y β u z : ℝ}
    (hβ1 : 1 < β) (hu : β ≤ u) (hz1 : 1 < z) (hzy : z ^ u = y)
    (hsort : ps.SortedGT) (hpos : ∀ p ∈ ps, 0 < p) (hmem : ∀ p ∈ ps, (p : ℝ) < z)
    {ε : ℕ} (hfail : brunFirstFailList y β ε ps) :
    ∀ r : ℕ, r < ps.length → (ps.length - 1 - r) % 2 = 0 →
      z ^ (β * (1 - 1 / β) ^ r) ≤ y / (((ps.take r).prod : ℕ) : ℝ) := by
  obtain ⟨_, hpar_n, _, hprev⟩ := hfail
  have hz0 : 0 < z := by linarith
  have hy_ge : z ^ β ≤ y := hzy ▸ Real.rpow_le_rpow_of_exponent_le hz1.le hu
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ihr =>
    intro hr hpar_r
    rcases r with _ | _ | r
    · simp [hy_ge]
    · have htake1 : (ps.take 1).prod = ps[0] := by
        cases ps with
        | nil => simp at hr
        | cons _ _ => simp
      have hp0_pos : (0 : ℝ) < (ps[0] : ℝ) := by exact_mod_cast hpos _ (List.getElem_mem _)
      have hp0_le : (ps[0] : ℝ) ≤ z := (hmem _ (List.getElem_mem _)).le
      have hexp : β * (1 - 1 / β) ^ 1 = β - 1 := by rw [_root_.pow_one]; field_simp
      rw [htake1, hexp, Real.rpow_sub hz0, Real.rpow_one]
      exact (div_le_div_of_nonneg_right hy_ge hz0.le).trans
        (div_le_div_of_nonneg_left (by linarith [Real.rpow_pos_of_pos hz0 β]) hp0_pos hp0_le)
    · have hr0 : r < ps.length := by omega
      have hr_lt : r < ps.length - 1 := by omega
      have hr_par : (r + 1) % 2 = ε % 2 := by omega
      exact brun_prefix_quot_step hβ1 hz1 hsort hpos hr
        (ihr r (by omega) hr0 (by omega)) (hprev ⟨r, hr0⟩ hr_lt hr_par)

/-- Every element of a first-failure list of primes `< z` is at least `z ^ ((1 - 1 / β) ^ n)`. -/
private lemma brun_firstFail_mem_ge {ps : List ℕ} {y β u z : ℝ}
    (hβ : 1 ≤ β) (hu : β ≤ u) (hz1 : 1 < z) (hzy : z ^ u = y)
    (hsort : ps.SortedGT) (hpos : ∀ p ∈ ps, 0 < p) (hmem : ∀ p ∈ ps, (p : ℝ) < z)
    {ε : ℕ} (hfail : brunFirstFailList y β ε ps) :
    ∀ p ∈ ps, z ^ ((1 - 1 / β) ^ ps.length) ≤ (p : ℝ) := by
  have ⟨hne, _, hnlt, _⟩ := hfail
  have hlast_le_mem : ∀ p ∈ ps, ps[ps.length - 1] ≤ p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact hsort.getElem_le_getElem_iff.mpr (by omega)
  suffices hlast : z ^ ((1 - 1 / β) ^ ps.length) ≤ (ps[ps.length - 1] : ℝ) from
    fun p hp ↦ hlast.trans (by exact_mod_cast hlast_le_mem p hp)
  rcases eq_or_lt_of_le hβ with rfl | hβ1
  · rw [div_one, sub_self, zero_pow hne.ne', Real.rpow_zero]
    exact_mod_cast hpos _ (List.getElem_mem _)
  · have hY := brun_prefix_quot_ge hβ1 hu hz1 hzy hsort hpos hmem hfail
      (ps.length - 1) (by omega) (by simp)
    set Y_last : ℝ := y / (((ps.take (ps.length - 1)).prod : ℕ) : ℝ)
    have ht := List.take_succ_eq_append_getElem (l := ps) (i := ps.length - 1) (by omega)
    rw [Nat.sub_add_cancel hne, List.take_length] at ht
    have hsplit : ((ps.prod : ℕ) : ℝ) =
        (((ps.take (ps.length - 1)).prod : ℕ) : ℝ) * (ps[ps.length - 1] : ℝ) := by
      simpa only [List.prod_append, List.prod_singleton, Nat.cast_mul] using
        congrArg (fun l : List ℕ ↦ ((l.prod : ℕ) : ℝ)) ht
    have hplast_pos : (0 : ℝ) < (ps[ps.length - 1] : ℝ) := by
      exact_mod_cast hpos _ (List.getElem_mem _)
    have hβ0 : 0 < β := by linarith
    have hYr_nn : 0 ≤ Y_last := (Real.rpow_pos_of_pos (by linarith) _).le.trans hY
    have hle : (Y_last / (ps[ps.length - 1] : ℝ)) ^ (1 / β) ≤ (ps[ps.length - 1] : ℝ) := by
      simpa [Y_last, hsplit, div_mul_eq_div_div] using not_lt.mp hnlt
    have hY_le_pow : Y_last ≤ ((ps[ps.length - 1] : ℝ)) ^ (β + 1) := by
      rw [Real.rpow_add hplast_pos, Real.rpow_one]
      exact (div_le_iff₀ hplast_pos).mp ((Real.rpow_inv_le_iff_of_pos
        (div_nonneg hYr_nn hplast_pos.le) hplast_pos.le hβ0).mp (by simpa only [one_div] using hle))
    have hz_pow : z ^ ((β / (β + 1)) * (1 - 1 / β) ^ (ps.length - 1)) ≤
        (ps[ps.length - 1] : ℝ) := by
      calc z ^ ((β / (β + 1)) * (1 - 1 / β) ^ (ps.length - 1))
        _ = (z ^ (β * (1 - 1 / β) ^ (ps.length - 1))) ^ (1 / (β + 1)) := by
          rw [← Real.rpow_mul (by linarith)]; congr 1; ring
        _ ≤ Y_last ^ (1 / (β + 1)) := Real.rpow_le_rpow (by positivity) hY (by positivity)
        _ ≤ (((ps[ps.length - 1] : ℝ)) ^ (β + 1)) ^ (1 / (β + 1)) :=
          Real.rpow_le_rpow hYr_nn hY_le_pow (by positivity)
        _ = (ps[ps.length - 1] : ℝ) := by
          rw [← Real.rpow_mul hplast_pos.le, mul_one_div_cancel (by positivity), Real.rpow_one]
    have hα_le : 1 - 1 / β ≤ β / (β + 1) := by
      rw [(by field_simp : 1 - 1 / β = (β - 1) / β), div_le_div_iff₀ hβ0 (by positivity)]; nlinarith
    have hexp_le : (1 - 1 / β) ^ ps.length ≤ (β / (β + 1)) * (1 - 1 / β) ^ (ps.length - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hne, _root_.pow_succ']
      exact mul_le_mul_of_nonneg_right hα_le
        (pow_nonneg (sub_nonneg.mpr ((div_le_one hβ0).mpr hβ1.le)) _)
    exact (Real.rpow_le_rpow_of_exponent_le hz1.le hexp_le).trans hz_pow

private lemma brun_slice_prod_inv_le_of_pos (s : BoundingSieve) {κ K z : ℝ}
    (hz2 : 2 < z) (hκ_pos : 0 < κ) (hdim : s.HasProductDimension κ K) (n : ℕ) :
    (∏ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ ↦ z ^ ((1 - 1 / (9 * κ + 1)) ^ n) ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - s.nu p)⁻¹) ≤ K * Real.exp ((n : ℝ) / 9) := by
  have hK1 : 1 ≤ K := hdim.one_le
  set α : ℝ := 1 - 1 / (9 * κ + 1)
  set z_n : ℝ := z ^ (α ^ n)
  set Q_n := s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ z_n ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hα_eq : α = (9 * κ) / (9 * κ + 1) := by simp only [α]; field_simp; ring
  have hα_pos : 0 < α := by rw [hα_eq]; positivity
  have hinv_nn : 0 ≤ 1 / (9 * κ + 1) := by positivity
  have hα_le1 : α ≤ 1 := by simp only [α]; linarith
  have hz1 : 1 < z := by linarith
  have hz_n1 : 1 < z_n := Real.one_lt_rpow hz1 (pow_pos hα_pos n)
  have hz_nz : z_n ≤ z :=
    (Real.rpow_le_rpow_of_exponent_le hz1.le (pow_le_one₀ hα_pos.le hα_le1)).trans_eq
      (Real.rpow_one z)
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hlog_zn : Real.log z / Real.log z_n = (α⁻¹) ^ n := by
    rw [Real.log_rpow (by linarith : 0 < z), mul_comm (α ^ n), ← div_div,
      div_self hlogz.ne', one_div, inv_pow]
  have hprod_le_α : (∏ p ∈ Q_n, (1 - s.nu p)⁻¹) ≤ K * ((α⁻¹) ^ n) ^ κ := by
    by_cases hzn2 : 2 ≤ z_n
    · simpa [hlog_zn] using hdim.bound hzn2 hz_nz
    · have hzn2' : z_n < 2 := lt_of_not_ge hzn2
      have hQn_eq : Q_n = s.prodPrimes.primeFactors.filter
          (fun p : ℕ ↦ (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
        ext p
        simp only [Q_n, Finset.mem_filter]
        refine ⟨fun ⟨hpP, _, hpz⟩ ↦ ⟨hpP, ?_, hpz⟩,
          fun ⟨hpP, h2p, hpz⟩ ↦ ⟨hpP, hzn2'.le.trans h2p, hpz⟩⟩
        exact_mod_cast (Nat.prime_of_mem_primeFactors hpP).two_le
      rw [hQn_eq]
      have hlog_le : Real.log z / Real.log 2 ≤ Real.log z / Real.log z_n :=
        div_le_div_of_nonneg_left hlogz.le (Real.log_pos hz_n1)
          (Real.log_le_log (by linarith) hzn2'.le)
      exact (hdim.bound le_rfl hz2.le).trans
        (mul_le_mul_of_nonneg_left
          (hlog_zn ▸ Real.rpow_le_rpow (by positivity) hlog_le hκ_pos.le) (by linarith))
  have hα_inv_le : α⁻¹ ≤ Real.exp (1 / (9 * κ)) := by
    have hinv : α⁻¹ = 1 / (9 * κ) + 1 := by rw [hα_eq, inv_div]; field_simp; ring
    exact hinv ▸ Real.add_one_le_exp _
  have hpow_le : ((α⁻¹) ^ n) ^ κ ≤ Real.exp ((n : ℝ) / 9) := by
    calc ((α⁻¹) ^ n) ^ κ
      _ ≤ ((Real.exp (1 / (9 * κ))) ^ n) ^ κ :=
        Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (by positivity) hα_inv_le n) hκ_pos.le
      _ = Real.exp ((n : ℝ) / 9) := by rw [← Real.exp_nat_mul, ← Real.exp_mul]; congr 1; field_simp
  exact hprod_le_α.trans (mul_le_mul_of_nonneg_left hpow_le (by linarith))

/-- Euler-product ratio bound on the active prime slice
`Q_n = s.prodPrimes.primeFactors.filter (fun p ↦ z ^ ((1 - 1 / β) ^ n) ≤ p ∧ p < z)`. -/
private lemma brun_slice_prod_inv_le (s : BoundingSieve) {κ K : ℝ} (z : ℝ)
    (hdim : s.HasProductDimension κ K) (n : ℕ) :
    (∏ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ ↦ z ^ ((1 - 1 / (9 * κ + 1)) ^ n) ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - s.nu p)⁻¹) ≤ K * Real.exp ((n : ℝ) / 9) := by
  have hK1 : 1 ≤ K := hdim.one_le
  have hκ0 : 0 ≤ κ := hdim.nonneg_dim
  set Q_n := s.prodPrimes.primeFactors.filter
    (fun p : ℕ ↦ z ^ ((1 - 1 / (9 * κ + 1)) ^ n) ≤ (p : ℝ) ∧ (p : ℝ) < z)
  by_cases hz2 : z ≤ 2
  · have hemp : Q_n = ∅ := by
      ext p
      simp only [Q_n, Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨hpP, _, hpz⟩
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hpP).two_le
      linarith
    rw [hemp, Finset.prod_empty]
    exact one_mul (1 : ℝ) ▸ mul_le_mul hK1 (Real.one_le_exp (by positivity)) zero_le_one
      (zero_le_one.trans hK1)
  · rcases eq_or_lt_of_le hκ0 with rfl | hκ_pos
    · have hsub : Q_n ⊆ s.prodPrimes.primeFactors.filter
          (fun p : ℕ ↦ (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < z) := fun p hp ↦ by
        obtain ⟨hpP, _, hpz⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr
          ⟨hpP, by exact_mod_cast (Nat.prime_of_mem_primeFactors hpP).two_le, hpz⟩
      have hinv_ge : ∀ p ∈ s.prodPrimes.primeFactors.filter
          (fun p : ℕ ↦ (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < z), 1 ≤ (1 - s.nu p)⁻¹ := fun p hp ↦ by
        have hpP := (Finset.mem_filter.mp hp).1
        have hdvd := Nat.dvd_of_mem_primeFactors hpP
        have hpp := Nat.prime_of_mem_primeFactors hpP
        exact (one_le_inv₀ (by linarith [s.nu_lt_one_of_prime p hpp hdvd])).mpr
          (by linarith [s.nu_pos_of_prime p hpp hdvd])
      have h1 : (∏ p ∈ Q_n, (1 - s.nu p)⁻¹) ≤ K := by
        calc (∏ p ∈ Q_n, (1 - s.nu p)⁻¹)
          _ ≤ ∏ p ∈ s.prodPrimes.primeFactors.filter
                (fun p : ℕ ↦ (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - s.nu p)⁻¹ :=
            Finset.prod_le_prod_of_subset_of_one_le₀ hsub
              (fun p hp ↦ zero_le_one.trans (hinv_ge p (hsub hp))) fun p hp _ ↦ hinv_ge p hp
          _ ≤ K * (Real.log z / Real.log 2) ^ (0 : ℝ) := hdim.bound le_rfl (lt_of_not_ge hz2).le
          _ = K := by simp
      exact h1.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_exp (by positivity)))
    · exact brun_slice_prod_inv_le_of_pos s (lt_of_not_ge hz2) hκ_pos hdim n

private lemma brun_slice_powersetCard_le {Q_n : Finset ℕ} {f : ℕ → ℝ} {K : ℝ} {n : ℕ}
    (hK1 : 1 ≤ K) (hn1 : 1 ≤ n) (hf : ∀ q ∈ Q_n, 0 ≤ f q)
    (hQn_sum : ∑ p ∈ Q_n, f p ≤ (n : ℝ) / 9 + Real.log K) :
    ∑ t ∈ Q_n.powersetCard n, (∏ q ∈ t, f q) ≤
      (K ^ 9 / Real.exp 1) * (Real.exp 1 / 9) ^ n := by
  have hK0 : 0 < K := by linarith
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogK_nn : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hsum_nn : 0 ≤ ∑ p ∈ Q_n, f p := Finset.sum_nonneg hf
  have hnum_le : ((n : ℝ) / 9 + Real.log K) ^ n ≤ ((n : ℝ) / 9) ^ n * K ^ 9 := by
    have hfactor : (n : ℝ) / 9 + Real.log K = ((n : ℝ) / 9) * (1 + (9 * Real.log K) / n) := by
      field_simp [hn_pos.ne']
    have h9 : (9 : ℝ) * Real.log K = (9 : ℕ) * Real.log K := by norm_num
    rw [hfactor, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (Real.one_add_div_pow_le_exp (by linarith)).trans_eq
      (by rw [h9, Real.exp_nat_mul, Real.exp_log hK0])
  calc ∑ t ∈ Q_n.powersetCard n, (∏ q ∈ t, f q)
    _ ≤ (∑ p ∈ Q_n, f p) ^ n / n ! :=
      Finset.sum_powersetCard_prod_le_pow_sum_div_factorial Q_n n hf
    _ ≤ ((n : ℝ) / 9 + Real.log K) ^ n / n ! :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hsum_nn hQn_sum n) (Nat.cast_nonneg _)
    _ ≤ (((n : ℝ) / 9) ^ n * K ^ 9) / n ! :=
      div_le_div_of_nonneg_right hnum_le (Nat.cast_nonneg _)
    _ ≤ (((n : ℝ) / 9) ^ n * K ^ 9) / (Real.exp 1 * ((n : ℝ) / Real.exp 1) ^ n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.exp_one_mul_div_exp_one_pow_le_factorial hn1)
    _ = (K ^ 9 / Real.exp 1) * (Real.exp 1 / 9) ^ n := by
      rw [div_pow (n : ℝ) 9 n, div_pow (n : ℝ) (Real.exp 1) n, div_pow (Real.exp 1) 9 n]
      have hn_ne : ((n : ℝ)) ^ n ≠ 0 := pow_ne_zero n hn_pos.ne'
      have h9_ne : (9 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      have he_ne : (Real.exp 1) ^ n ≠ 0 := pow_ne_zero n (Real.exp_pos 1).ne'
      field_simp [hn_ne, h9_ne, he_ne, (Real.exp_pos 1).ne']

private lemma brun_tail_prod_le (s : BoundingSieve) {z_n z B : ℝ}
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hQn_inv : (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ z_n ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - s.nu p)⁻¹) ≤ B)
    {t : Finset ℕ}
    (htQn : t ⊆ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ z_n ≤ (p : ℝ) ∧ (p : ℝ) < z)) :
    (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q ↦ ∀ x ∈ t, q < x), (1 - s.nu q)) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * B := by
  set Q := s.prodPrimes.primeFactors
  set Q_n := Q.filter (fun p : ℕ ↦ z_n ≤ (p : ℝ) ∧ (p : ℝ) < z)
  set V : ℝ := ∏ p ∈ Q, (1 - s.nu p)
  have hnu_bounds : ∀ p ∈ Q, 0 < s.nu p ∧ s.nu p < 1 := fun p hp ↦
    ⟨s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp),
      s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)⟩
  have hV_pos : 0 < V := Finset.prod_pos fun p hp ↦ sub_pos.mpr (hnu_bounds p hp).2
  set S_lt := Q.filter (fun q ↦ ∀ x ∈ t, q < x)
  set S_ge := Q.filter (fun q ↦ ¬ ∀ x ∈ t, q < x)
  have hV_split : V = (∏ q ∈ S_lt, (1 - s.nu q)) * ∏ q ∈ S_ge, (1 - s.nu q) := by
    simpa [V, S_lt, S_ge] using
      (Finset.prod_filter_mul_prod_filter_not Q (fun q ↦ ∀ x ∈ t, q < x) (1 - s.nu ·)).symm
  have hSge_pos : 0 < ∏ q ∈ S_ge, (1 - s.nu q) :=
    Finset.prod_pos fun q hq ↦ sub_pos.mpr (hnu_bounds q (Finset.mem_filter.mp hq).1).2
  have hSge_sub : S_ge ⊆ Q_n := fun q hq ↦ by
    obtain ⟨hqQ, hnot⟩ := Finset.mem_filter.mp hq
    simp only [not_forall, not_lt] at hnot
    obtain ⟨x, hxt, hxq⟩ := hnot
    have hxQn := (Finset.mem_filter.mp (htQn hxt)).2.1
    exact Finset.mem_filter.mpr ⟨hqQ, hxQn.trans (by exact_mod_cast hxq), hprimes q hqQ⟩
  have hlt_eq : (∏ q ∈ S_lt, (1 - s.nu q)) = V * ∏ q ∈ S_ge, (1 - s.nu q)⁻¹ := by
    rw [hV_split, Finset.prod_inv_distrib, mul_inv_cancel_right₀ hSge_pos.ne']
  have hinv_ge : ∀ q ∈ Q_n, 1 ≤ (1 - s.nu q)⁻¹ := fun q hq ↦ by
    have hqQ := (Finset.mem_filter.mp hq).1
    exact (one_le_inv₀ (sub_pos.mpr (hnu_bounds q hqQ).2)).mpr
      (by linarith [(hnu_bounds q hqQ).1])
  rw [hlt_eq]
  refine mul_le_mul_of_nonneg_left ?_ hV_pos.le
  exact (Finset.prod_le_prod_of_subset_of_one_le₀ hSge_sub
    (fun q hq ↦ zero_le_one.trans (hinv_ge q (hSge_sub hq)))
    fun q hq _ ↦ hinv_ge q hq).trans hQn_inv

/-- Additive density bound on the `n`-th prime slice from `s.HasProductDimension κ K`. -/
private lemma brun_slice_sum_nu_le (s : BoundingSieve) {κ K : ℝ} (z : ℝ)
    (hdim : s.HasProductDimension κ K) (n : ℕ) :
    ∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ ↦ z ^ ((1 - 1 / (9 * κ + 1)) ^ n) ≤ (p : ℝ) ∧ (p : ℝ) < z), s.nu p ≤
      (n : ℝ) / 9 + Real.log K := by
  have hK1 : 1 ≤ K := hdim.one_le
  refine Real.exp_le_exp.mp ?_
  rw [Real.exp_sum, Real.exp_add, Real.exp_log (by linarith : 0 < K), mul_comm _ K]
  refine (Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) fun p hp ↦ ?_).trans
    (brun_slice_prod_inv_le s z hdim n)
  have hpQ := (Finset.mem_filter.mp hp).1
  have hlt1 := s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpQ)
    (Nat.dvd_of_mem_primeFactors hpQ)
  rw [← inv_inv (Real.exp (s.nu p)), ← Real.exp_neg]
  exact inv_anti₀ (sub_pos.mpr hlt1) (Real.one_sub_le_exp_neg _)

/-- Every first-failing prime subset of cardinality `n` is supported in the `n`-th prime slice. -/
private lemma brun_firstFail_subset_powersetCard (s : BoundingSieve) {κ K y u : ℝ}
    (hy : 1 < y) (hu : 9 * κ + 1 ≤ u) (hdim : s.HasProductDimension κ K)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y ^ (1 / u)) (ε n : ℕ) :
    (open Classical in
      (s.prodPrimes.primeFactors.powerset.filter
        (fun t ↦ brunFirstFailList y (9 * κ + 1) ε (t.sort (· ≥ ·)))).filter
        (fun t ↦ t.card = n) ⊆
      (s.prodPrimes.primeFactors.filter
        (fun p : ℕ ↦ (y ^ (1 / u)) ^ ((1 - 1 / (9 * κ + 1)) ^ n) ≤ (p : ℝ) ∧
          (p : ℝ) < y ^ (1 / u))).powersetCard n) := by
  classical
  have hκ0 : 0 ≤ κ := hdim.nonneg_dim
  set β : ℝ := 9 * κ + 1
  have hβ1 : 1 ≤ β := by simp only [β]; linarith
  have hu0 : 0 < u := by linarith
  set z : ℝ := y ^ (1 / u)
  have hz1 : 1 < z := Real.one_lt_rpow hy (by positivity)
  have hzy : z ^ u = y := by
    rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hu0.ne', Real.rpow_one]
  intro t ht
  obtain ⟨ht_fail, ht_card⟩ := Finset.mem_filter.mp ht
  obtain ⟨htQ, hfail⟩ := Finset.mem_filter.mp ht_fail
  have ht_sub := Finset.mem_powerset.mp htQ
  refine Finset.mem_powersetCard.mpr
    ⟨fun p hp ↦ Finset.mem_filter.mpr ⟨ht_sub hp, ?_, hprimes p (ht_sub hp)⟩, ht_card⟩
  have hps_len : (t.sort (· ≥ ·)).length = n := by simp [ht_card]
  simpa [hps_len] using brun_firstFail_mem_ge hβ1 hu hz1 hzy t.sortedGT_sort
    (fun q hq ↦ (Nat.prime_of_mem_primeFactors (ht_sub ((Finset.mem_sort (· ≥ ·)).mp hq))).pos)
    (fun q hq ↦ hprimes q (ht_sub ((Finset.mem_sort (· ≥ ·)).mp hq))) hfail
    p ((Finset.mem_sort (· ≥ ·)).mpr hp)

/-- Bound on the sum of first-failure terms of fixed positive cardinality `n`. -/
private lemma brun_length_fail_le (s : BoundingSieve) {κ K y u : ℝ}
    (hy : 1 < y) (hu : 9 * κ + 1 ≤ u) (hdim : s.HasProductDimension κ K)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y ^ (1 / u)) (ε : ℕ)
    {n : ℕ} (hn1 : 1 ≤ n) :
    (open Classical in
      ∑ t ∈ (s.prodPrimes.primeFactors.powerset.filter
          (fun t ↦ brunFirstFailList y (9 * κ + 1) ε (t.sort (· ≥ ·)))).filter
          (fun t ↦ t.card = n),
        (∏ q ∈ t, s.nu q) *
          ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q ↦ ∀ x ∈ t, q < x), (1 - s.nu q)) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * (K ^ 10 / Real.exp 1) *
        (Real.exp (10 / 9) / 9) ^ n := by
  classical
  have hK1 : 1 ≤ K := hdim.one_le
  set β : ℝ := 9 * κ + 1
  set z : ℝ := y ^ (1 / u)
  set Q := s.prodPrimes.primeFactors
  set V : ℝ := ∏ p ∈ Q, (1 - s.nu p)
  have hnu_bounds : ∀ p ∈ Q, 0 < s.nu p ∧ s.nu p < 1 := fun p hp ↦
    ⟨s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp),
      s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)⟩
  have hV_pos : 0 < V := Finset.prod_pos fun p hp ↦ sub_pos.mpr (hnu_bounds p hp).2
  set Q_n := Q.filter (fun p : ℕ ↦ z ^ ((1 - 1 / β) ^ n) ≤ (p : ℝ) ∧ (p : ℝ) < z)
  set F_n := (Q.powerset.filter
    (fun t ↦ brunFirstFailList y β ε (t.sort (· ≥ ·)))).filter (fun t ↦ t.card = n)
  have hF_sub : F_n ⊆ Q_n.powersetCard n :=
    brun_firstFail_subset_powersetCard s hy hu hdim hprimes ε n
  have hpow_fac := brun_slice_powersetCard_le hK1 hn1
    (fun q hq ↦ (hnu_bounds q (Finset.mem_filter.mp hq).1).1.le) (brun_slice_sum_nu_le s z hdim n)
  have hexp_n : Real.exp ((n : ℝ) / 9) * (Real.exp 1 / 9) ^ n = (Real.exp (10 / 9) / 9) ^ n := by
    rw [(by ring : (n : ℝ) / 9 = (n : ℕ) * (1 / 9 : ℝ)), Real.exp_nat_mul, ← mul_pow,
      ← mul_div_assoc, ← Real.exp_add]
    congr 2; norm_num
  calc ∑ t ∈ F_n, (∏ q ∈ t, s.nu q) * ∏ q ∈ Q.filter (fun q ↦ ∀ x ∈ t, q < x), (1 - s.nu q)
    _ ≤ ∑ t ∈ F_n, (∏ q ∈ t, s.nu q) * (V * (K * Real.exp ((n : ℝ) / 9))) :=
      Finset.sum_le_sum fun t ht ↦
        have htQn := (Finset.mem_powersetCard.mp (hF_sub ht)).1
        mul_le_mul_of_nonneg_left
          (brun_tail_prod_le s hprimes (brun_slice_prod_inv_le s z hdim n) htQn)
          (Finset.prod_nonneg fun q hq ↦ (hnu_bounds q (Finset.mem_filter.mp (htQn hq)).1).1.le)
    _ = (V * (K * Real.exp ((n : ℝ) / 9))) * ∑ t ∈ F_n, ∏ q ∈ t, s.nu q := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ (V * (K * Real.exp ((n : ℝ) / 9))) * ∑ t ∈ Q_n.powersetCard n, ∏ q ∈ t, s.nu q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hF_sub fun t ht _ ↦
        Finset.prod_nonneg fun q hq ↦
          (hnu_bounds q (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp ht).1 hq)).1).1.le)
        (by positivity)
    _ ≤ (V * (K * Real.exp ((n : ℝ) / 9))) * ((K ^ 9 / Real.exp 1) * (Real.exp 1 / 9) ^ n) :=
      mul_le_mul_of_nonneg_left hpow_fac (by positivity)
    _ = V * (K ^ 10 / Real.exp 1) * (Real.exp (10 / 9) / 9) ^ n := by rw [← hexp_n]; ring

private lemma brun_geom_tail_le {β u : ℝ} :
    (1 / Real.exp 1) *
      ((Real.exp (10 / 9) / 9) ^ (⌊u - β⌋₊ + 1) / (1 - Real.exp (10 / 9) / 9)) ≤
        Real.exp (β - u) := by
  set a : ℝ := Real.exp (10 / 9) / 9
  set m : ℕ := ⌊u - β⌋₊
  obtain ⟨ha0, ha_exp, ha_div⟩ := brun_tail_ratio_bounds
  have haN : a ^ (m + 1) / (1 - a) ≤ Real.exp (-(m : ℝ)) := by
    calc a ^ (m + 1) / (1 - a)
      _ = (a / (1 - a)) * a ^ m := by rw [_root_.pow_succ']; ring
      _ ≤ 1 * (Real.exp (-1)) ^ m :=
        mul_le_mul ha_div (pow_le_pow_left₀ ha0 ha_exp.le m) (pow_nonneg ha0 m) zero_le_one
      _ = Real.exp (-(m : ℝ)) := by rw [one_mul, ← Real.exp_nat_mul]; congr 1; ring
  calc (1 / Real.exp 1) * (a ^ (m + 1) / (1 - a))
    _ ≤ Real.exp (-1) * Real.exp (-(m : ℝ)) := by
      rw [Real.exp_neg, ← one_div]
      exact mul_le_mul_of_nonneg_left haN (by positivity)
    _ = Real.exp (-((m : ℝ) + 1)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (β - u) := Real.exp_le_exp.mpr (by linarith [Nat.lt_floor_add_one (u - β)])

/-- Bound on the full first-failure sum `brunFailSum` under `s.HasProductDimension κ K`. -/
private lemma brunFailSum_le_delta_mul (s : BoundingSieve) {κ K y u : ℝ}
    (hy : 1 < y) (hu : 9 * κ + 1 ≤ u) (hdim : s.HasProductDimension κ K)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y ^ (1 / u)) (ε : ℕ) :
    brunFailSum s.prodPrimes.primeFactors s.nu y (9 * κ + 1) ε ≤
      (Real.exp (9 * κ + 1 - u) * K ^ 10) *
        ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  classical
  have hK1 : 1 ≤ K := hdim.one_le
  have hκ0 : 0 ≤ κ := hdim.nonneg_dim
  set β : ℝ := 9 * κ + 1
  have hβ0 : 0 < β := by simp only [β]; linarith
  have hu0 : 0 < u := by linarith
  set z : ℝ := y ^ (1 / u)
  have hz1 : 1 < z := Real.one_lt_rpow hy (by positivity)
  have hzy : z ^ u = y := by
    rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hu0.ne', Real.rpow_one]
  set Q := s.prodPrimes.primeFactors
  set V : ℝ := ∏ p ∈ Q, (1 - s.nu p)
  have hV_nn : 0 ≤ V := Finset.prod_nonneg fun p hp ↦
    sub_nonneg.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)).le
  set N : ℕ := ⌊u - β⌋₊ + 1
  set F := Q.powerset.filter (fun t ↦ brunFirstFailList y β ε (t.sort (· ≥ ·)))
  have hmaps : ∀ t ∈ F, t.card ∈ Finset.Icc N Q.card := fun t ht ↦ by
    obtain ⟨htQ, hfail⟩ := Finset.mem_filter.mp ht
    have ht_sub : t ⊆ Q := Finset.mem_powerset.mp htQ
    have hcard_ge := brun_firstFail_card_ge (by linarith) hβ0 hu hz1 hzy
      (fun q hq ↦ (Nat.prime_of_mem_primeFactors (ht_sub ((Finset.mem_sort (· ≥ ·)).mp hq))).pos)
      (fun q hq ↦ hprimes q (ht_sub ((Finset.mem_sort (· ≥ ·)).mp hq))) hfail
    exact Finset.mem_Icc.mpr ⟨by simpa [N] using hcard_ge, Finset.card_le_card ht_sub⟩
  set a : ℝ := Real.exp (10 / 9) / 9
  obtain ⟨ha0, ha_exp, -⟩ := brun_tail_ratio_bounds
  have ha1 : a < 1 := ha_exp.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hgeom : ∑ n ∈ Finset.Icc N Q.card, a ^ n ≤ a ^ N / (1 - a) := by
    by_cases hNM : N ≤ Q.card + 1
    · have hIcc : Finset.Icc N Q.card = Finset.Ico N (Q.card + 1) := by ext; simp
      rw [hIcc, geom_sum_Ico' ha1.ne hNM]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg ha0 (Q.card + 1)]) (by linarith)
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      exact div_nonneg (pow_nonneg ha0 N) (by linarith)
  calc brunFailSum Q s.nu y β ε
    _ = ∑ n ∈ Finset.Icc N Q.card, ∑ t ∈ F.filter (fun t ↦ t.card = n),
          (∏ q ∈ t, s.nu q) * ∏ q ∈ Q.filter (fun q ↦ ∀ x ∈ t, q < x), (1 - s.nu q) := by
      rw [brunFailSum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ ∑ n ∈ Finset.Icc N Q.card, V * (K ^ 10 / Real.exp 1) * a ^ n :=
      Finset.sum_le_sum fun n hn ↦
        brun_length_fail_le s hy hu hdim hprimes ε (by have := (Finset.mem_Icc.mp hn).1; omega)
    _ = V * (K ^ 10 / Real.exp 1) * ∑ n ∈ Finset.Icc N Q.card, a ^ n := by rw [← Finset.mul_sum]
    _ ≤ V * (K ^ 10 / Real.exp 1) * (a ^ N / (1 - a)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = V * K ^ 10 * ((1 / Real.exp 1) * (a ^ N / (1 - a))) := by ring
    _ ≤ V * K ^ 10 * Real.exp (β - u) := mul_le_mul_of_nonneg_left brun_geom_tail_le (by positivity)
    _ = (Real.exp (β - u) * K ^ 10) * V := by ring

/-! ### Dimension-controlled Brun main terms and fundamental estimate -/

/-- Dimension-controlled bounds on Brun's lower and upper main sums: under
`s.HasProductDimension κ K` (which automatically forces `0 ≤ κ` and `1 ≤ K`), with `β = 9 * κ + 1`,
`V = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)`, and `δ = exp (9 * κ + 1 - u) * K ^ 10`,
`(1 - δ) * V ≤ s.mainSum (brunLowerWeight s.prodPrimes y β) ≤ V ≤`
`s.mainSum (brunUpperWeight s.prodPrimes y β) ≤ (1 + δ) * V`. -/
theorem brun_mainSum_bounds (s : BoundingSieve) (κ K y u : ℝ)
    (hy : 1 < y) (hu : 9 * κ + 1 ≤ u) (hdim : s.HasProductDimension κ K)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y ^ (1 / u)) :
    let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
    let δ := Real.exp (9 * κ + 1 - u) * K ^ 10
    let β := 9 * κ + 1
    (1 - δ) * V ≤ s.mainSum (brunLowerWeight s.prodPrimes y β) ∧
      s.mainSum (brunLowerWeight s.prodPrimes y β) ≤ V ∧
      V ≤ s.mainSum (brunUpperWeight s.prodPrimes y β) ∧
      s.mainSum (brunUpperWeight s.prodPrimes y β) ≤ (1 + δ) * V := by
  intro V δ β
  have hnu_0 : ∀ q ∈ s.prodPrimes.primeFactors, 0 ≤ s.nu q := fun q hq ↦
    (s.nu_pos_of_prime q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)).le
  have hnu_1 : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 := fun q hq ↦
    (s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)).le
  have hmain_low : s.mainSum (brunLowerWeight s.prodPrimes y β) =
      brunAdmSum s.prodPrimes.primeFactors s.nu y β 0 :=
    sum_divisors_brunWeight_mul_eq_brunAdmSum s.prodPrimes_ne_zero dvd_rfl s.nu_mult y β 0
  have hmain_up : s.mainSum (brunUpperWeight s.prodPrimes y β) =
      brunAdmSum s.prodPrimes.primeFactors s.nu y β 1 :=
    sum_divisors_brunWeight_mul_eq_brunAdmSum s.prodPrimes_ne_zero dvd_rfl s.nu_mult y β 1
  have hid_low := brun_first_failure_identity s.prodPrimes.primeFactors s.nu y β 0
  have hid_up := brun_first_failure_identity s.prodPrimes.primeFactors s.nu y β 1
  have hnn_low := brunFailSum_nonneg hnu_0 hnu_1 y β 0
  have hnn_up := brunFailSum_nonneg hnu_0 hnu_1 y β 1
  have hle_low := brunFailSum_le_delta_mul s hy hu hdim hprimes 0
  have hle_up := brunFailSum_le_delta_mul s hy hu hdim hprimes 1
  have hsign0 : (-1 : ℝ) ^ (0 + 1) = -1 := by norm_num
  have hsign1 : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
  rw [hsign0] at hid_low
  rw [hsign1] at hid_up
  rw [hmain_low, hmain_up]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Brun's fundamental sieve estimate (Kedlaya, *Notes on analytic number theory*, Chapter 12,
Theorem 12.2, with the lower main-term factor `1 - δ` corrected): under `0 ≤ s.totalMass`,
`1 < y`, `9 * κ + 1 ≤ u`, `s.HasProductDimension κ K` (which automatically forces `0 ≤ κ` and
`1 ≤ K`), and prime cutoff `p < y ^ (1 / u)` on all prime factors of `s.prodPrimes`,
`(1 - δ) * V * s.totalMass - s.remainderMass y ≤ s.siftedSum` and
`s.siftedSum ≤ (1 + δ) * V * s.totalMass + s.remainderMass y`. -/
theorem brun_fundamental_estimate (s : BoundingSieve) (κ K y u : ℝ)
    (hX : 0 ≤ s.totalMass) (hy : 1 < y) (hu : 9 * κ + 1 ≤ u)
    (hdim : s.HasProductDimension κ K)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y ^ (1 / u)) :
    let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
    let δ := Real.exp (9 * κ + 1 - u) * K ^ 10
    (1 - δ) * V * s.totalMass - s.remainderMass y ≤ s.siftedSum ∧
      s.siftedSum ≤ (1 + δ) * V * s.totalMass + s.remainderMass y := by
  intro V δ
  set β : ℝ := 9 * κ + 1
  have hκ0 : 0 ≤ κ := hdim.nonneg_dim
  have hβ1 : 1 ≤ β := by simp only [β]; linarith
  have hu1 : 1 ≤ u := hβ1.trans hu
  have hprimes_lt_y : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < y := by
    intro p hp
    refine (hprimes p hp).trans_le ?_
    calc y ^ (1 / u)
      _ ≤ y ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy.le ((div_le_one (by linarith)).mpr hu1)
      _ = y := Real.rpow_one y
  obtain ⟨hlow_ge, -, -, hup_le⟩ := s.brun_mainSum_bounds κ K y u hy hu hdim hprimes
  have herr_low : s.errSum (brunLowerWeight s.prodPrimes y β) ≤ s.remainderMass y := by
    simpa only [one_mul] using s.errSum_le_mul_remainderMass (brunLowerWeight s.prodPrimes y β) y
      (fun d _ hdy ↦ by_contra fun hne ↦ not_lt_of_ge hdy
        (lt_of_brunWeight_ne_zero hy hβ1 hprimes_lt_y hne))
      (fun d _ _ ↦ abs_brunLowerWeight_le_one s.prodPrimes y β d)
  have herr_up : s.errSum (brunUpperWeight s.prodPrimes y β) ≤ s.remainderMass y := by
    simpa only [one_mul] using s.errSum_le_mul_remainderMass (brunUpperWeight s.prodPrimes y β) y
      (fun d _ hdy ↦ by_contra fun hne ↦ not_lt_of_ge hdy
        (lt_of_brunWeight_ne_zero hy hβ1 hprimes_lt_y hne))
      (fun d _ _ ↦ abs_brunUpperWeight_le_one s.prodPrimes y β d)
  constructor
  · have hsieve_low := s.totalMass_mul_mainSum_sub_errSum_le_siftedSum_of_dvd_prodPrimes
      (brunLowerWeight s.prodPrimes y β) fun _ hr ↦ sum_divisors_brunLowerWeight_le hr y β
    have hmain_mul : (1 - δ) * V * s.totalMass ≤
        s.totalMass * s.mainSum (brunLowerWeight s.prodPrimes y β) := by
      rw [mul_comm ((1 - δ) * V)]
      exact mul_le_mul_of_nonneg_left hlow_ge hX
    linarith
  · have hsieve_up := s.siftedSum_le_mainSum_errSum_of_upperMoebius
      (brunUpperWeight s.prodPrimes y β)
      (isUpperMoebius_brunUpperWeight s.prodPrimes_ne_zero y β)
    have hmain_mul : s.totalMass * s.mainSum (brunUpperWeight s.prodPrimes y β) ≤
        (1 + δ) * V * s.totalMass := by
      rw [mul_comm ((1 + δ) * V)]
      exact mul_le_mul_of_nonneg_left hup_le hX
    linarith

end BoundingSieve

