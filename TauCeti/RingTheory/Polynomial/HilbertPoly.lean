/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import TauCeti.RingTheory.Polynomial.Binomial.Basis

/-!
# Binomial expansions, degree bounds, and integer shifts of Hilbert polynomials

Mathlib constructs `Polynomial.preHilbertPoly F d k` and `Polynomial.hilbertPoly p e` over any
characteristic-zero field `F`, showing that `(hilbertPoly p e).eval (n : F)` agrees with the `n`-th
coefficient of `p * (1 - X)⁻ᵉ` for `n > p.natDegree`.

This file supplies the properties needed when `Polynomial.hilbertPoly` is applied to integer-graded
modules whose nonzero pieces may begin in negative degrees:

* **Identification with generalized binomial polynomials:** `preHilbertPoly F d k` equals
  `Ring.choose (X + C ((d : ℤ) - (k : ℤ))) d`. Over `ℚ`, every `hilbertPoly` of an integer
  polynomial `h : ℤ[X]`, together with any integer translate `P(X - d₀)`, therefore lies in the
  integral binomial span `TauCeti.ringChooseSpan (X : ℚ[X])` and takes integer values at all
  integers (positive, zero, or negative).
* **Unconditional degree bound:** `(hilbertPoly p e).degree < e` for all `p : F[X]` and `e : ℕ`,
  including `p = 0` and `e = 0`.
* **Shifted series and integer-evaluation uniqueness:** a polynomial in `F[X]` over a
  characteristic-zero integral domain is uniquely determined by its values on `{d : ℤ | N ≤ d}`,
  and if `(∑_{n ≥ 0} f(d₀ + n) Xⁿ) * (1 - X) ^ e = p`, then `(hilbertPoly p e).comp (X - C d₀)`
  has degree `< e` and evaluates to `f d` at every integer `d > d₀ + p.natDegree`.

## Main results

* `Polynomial.preHilbertPoly_eq_ringChoose`: `preHilbertPoly F d k` as a generalized binomial
  polynomial.
* `Polynomial.hilbertPoly_map_intCast_mem_ringChooseSpan`: `hilbertPoly` of an integer polynomial
  lies in `TauCeti.ringChooseSpan (X : ℚ[X])`.
* `TauCeti.comp_X_add_intCast_mem_ringChooseSpan`,
  `TauCeti.comp_X_sub_intCast_mem_ringChooseSpan`, and
  `TauCeti.exists_intCast_eq_eval_of_mem_ringChooseSpan`: stability of `ringChooseSpan (X : ℚ[X])`
  under integer variable shifts and integrality of its values at all integers.
* `Polynomial.degree_hilbertPoly_lt`: `(hilbertPoly p e).degree < e`.
* `Polynomial.degree_comp_X_add_C` and `Polynomial.degree_comp_X_sub_C`: invariance of `degree`
  under linear shifts `X + C a` and `X - C a`.
* `Polynomial.eq_of_forall_ge_eval_intCast_eq`: agreement at all integers `d ≥ N` implies polynomial
  equality in characteristic zero.
* `Polynomial.eval_hilbertPoly_comp_X_sub_intCast`: evaluation of the `d₀`-shifted Hilbert
  polynomial from a denominator-cleared power-series identity.
-/

public section

open scoped PowerSeries

namespace Polynomial

section ShiftDegree

/-- Composing a polynomial with `X + C a` preserves its degree over any semiring. -/
@[simp]
theorem degree_comp_X_add_C {R : Type*} [Semiring R] (p : R[X]) (a : R) :
    (p.comp (X + C a)).degree = p.degree := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp]
  have hmul : p.leadingCoeff * (X + C a).leadingCoeff ^ p.natDegree ≠ 0 := by
    rw [(monic_X_add_C a).leadingCoeff, one_pow, mul_one]
    exact leadingCoeff_ne_zero.2 hp
  have hcomp : p.comp (X + C a) ≠ 0 := fun h ↦ hmul <| by
    rw [← coeff_comp_degree_mul_degree (by rw [natDegree_X_add_C]; exact one_ne_zero), h,
      coeff_zero]
  rw [degree_eq_natDegree hcomp, degree_eq_natDegree hp, Nat.cast_inj,
    natDegree_comp_eq_of_mul_ne_zero hmul, natDegree_X_add_C, mul_one]

/-- Composing a polynomial with `X - C a` preserves its degree over any ring. -/
@[simp]
theorem degree_comp_X_sub_C {R : Type*} [Ring R] (p : R[X]) (a : R) :
    (p.comp (X - C a)).degree = p.degree := by
  rw [sub_eq_add_neg, ← map_neg, degree_comp_X_add_C]

end ShiftDegree

section CharZeroRing

/-- Over a characteristic-zero integral domain, two polynomials that agree at all integers `d ≥ N`
are equal. -/
theorem eq_of_forall_ge_eval_intCast_eq {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {p q : R[X]} (N : ℤ) (h : ∀ d : ℤ, N ≤ d → p.eval (d : R) = q.eval (d : R)) : p = q := by
  refine eq_of_infinite_eval_eq p q <|
    ((Set.Ici_infinite N).image (Int.cast_injective (α := R)).injOn).mono ?_
  rintro _ ⟨d, hd, rfl⟩
  exact h d hd

end CharZeroRing

section CharZeroField

attribute [local instance] BinomialRing.toHasUniqueDiv

variable {F : Type*} [Field F] [CharZero F]

/-- `Polynomial.preHilbertPoly F d k` is the generalized binomial polynomial
`Ring.choose (X + (d - k)) d`. -/
theorem preHilbertPoly_eq_ringChoose (d k : ℕ) :
    preHilbertPoly F d k = Ring.choose (X + ((d : ℤ) - (k : ℤ) : F[X])) d := by
  refine eq_of_forall_ge_eval_intCast_eq (k : ℤ) fun m hm ↦ ?_
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_trans (Int.natCast_nonneg k) hm)
  have hkn : k ≤ n := Int.ofNat_le.1 hm
  rw [Int.cast_natCast, preHilbertPoly_eq_choose_add_sub F d (Nat.le_add_right_of_le hkn)]
  have hφ := Ring.map_choose (evalRingHom (n : F)) (X + ((d : ℤ) - (k : ℤ) : F[X])) d
  rw [coe_evalRingHom] at hφ
  have harg : eval (n : F) (X + ((d : ℤ) - (k : ℤ) : F[X])) = ((n + d - k : ℕ) : F) := by
    simp only [eval_add, eval_X, eval_sub, Int.cast_natCast, eval_natCast]
    rw [Nat.cast_sub (Nat.le_add_right_of_le hkn), Nat.cast_add]
    ring
  rw [hφ, harg, Ring.choose_natCast]

/-- For every polynomial `p : F[X]` and `e : ℕ`, `Polynomial.hilbertPoly p e` has degree strictly
less than `e` (including the zero-polynomial and `e = 0` cases, where `⊥ < (e : WithBot ℕ)`). -/
theorem degree_hilbertPoly_lt (p : F[X]) (e : ℕ) :
    (hilbertPoly p e).degree < (e : WithBot ℕ) := by
  rcases eq_or_ne (hilbertPoly p e) 0 with h0 | hne
  · simp [h0]
  · have he : 0 < e := Nat.pos_of_ne_zero fun h ↦ hne (h ▸ hilbertPoly_zero_right p)
    refine degree_le_natDegree.trans_lt (Nat.cast_lt.2 ?_)
    rw [natDegree_hilbertPoly_of_ne_zero hne]
    omega

/-- If `(∑_{n ≥ 0} f(d₀ + n) Xⁿ) * (1 - X) ^ e = p`, then the shifted Hilbert polynomial
`(hilbertPoly p e).comp (X - C d₀)` evaluates to `f d` at every integer `d > d₀ + p.natDegree`. -/
theorem eval_hilbertPoly_comp_X_sub_intCast {f : ℤ → F} {p : F[X]} {d₀ : ℤ} {e : ℕ}
    (hseries : (PowerSeries.mk fun n : ℕ ↦ f (d₀ + n)) * (1 - PowerSeries.X) ^ e = (p : F⟦X⟧))
    {d : ℤ} (hd : d₀ + p.natDegree < d) :
    ((hilbertPoly p e).comp (X - C (d₀ : F))).eval (d : F) = f d := by
  have heq : PowerSeries.mk (fun n : ℕ ↦ f (d₀ + n)) =
      (p : F⟦X⟧) * (PowerSeries.invOneSubPow F e).val := by
    calc
      PowerSeries.mk (fun n : ℕ ↦ f (d₀ + n)) =
          PowerSeries.mk (fun n : ℕ ↦ f (d₀ + n)) *
            ((PowerSeries.invOneSubPow F e).inv * (PowerSeries.invOneSubPow F e).val) := by
        rw [(PowerSeries.invOneSubPow F e).inv_val, mul_one]
      _ = (PowerSeries.mk (fun n : ℕ ↦ f (d₀ + n)) * (1 - PowerSeries.X) ^ e) *
            (PowerSeries.invOneSubPow F e).val := by
        rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, mul_assoc]
      _ = (p : F⟦X⟧) * (PowerSeries.invOneSubPow F e).val := by rw [hseries]
  set n : ℕ := (d - d₀).toNat
  have hdd₀ : d₀ ≤ d := by omega
  have hn_eq : d₀ + (n : ℤ) = d := by omega
  have hdeg : p.natDegree < n := by omega
  have hcast : (d : F) - (d₀ : F) = (n : F) := by
    rw [← hn_eq, Int.cast_add, Int.cast_natCast, add_sub_cancel_left]
  rw [eval_comp, eval_sub, eval_X, eval_C, hcast,
    ← coeff_mul_invOneSubPow_eq_hilbertPoly_eval e hdeg, ← heq, PowerSeries.coeff_mk, hn_eq]

end CharZeroField

section Rational

attribute [local instance] BinomialRing.toHasUniqueDiv

/-- `Polynomial.preHilbertPoly ℚ d k` belongs to the integral binomial span
`TauCeti.ringChooseSpan (X : ℚ[X])`. -/
theorem preHilbertPoly_mem_ringChooseSpan (d k : ℕ) :
    preHilbertPoly ℚ d k ∈ TauCeti.ringChooseSpan (X : ℚ[X]) := by
  have hcast : ((d : ℤ) - (k : ℤ) : ℚ[X]) = (((d : ℤ) - (k : ℤ) : ℤ) : ℚ[X]) := by
    push_cast
    rfl
  rw [preHilbertPoly_eq_ringChoose, hcast]
  exact TauCeti.ringChoose_add_intCast_mem_ringChooseSpan (X : ℚ[X]) ((d : ℤ) - (k : ℤ)) d

/-- For any integer polynomial `h : ℤ[X]` and `e : ℕ`, `hilbertPoly (h.map (Int.castRingHom ℚ)) e`
belongs to the integral binomial span `TauCeti.ringChooseSpan (X : ℚ[X])`. -/
theorem hilbertPoly_map_intCast_mem_ringChooseSpan (h : ℤ[X]) (e : ℕ) :
    hilbertPoly (h.map (Int.castRingHom ℚ)) e ∈ TauCeti.ringChooseSpan (X : ℚ[X]) := by
  cases e with
  | zero => exact (TauCeti.ringChooseSpan (X : ℚ[X])).zero_mem
  | succ d =>
    rw [hilbertPoly_succ]
    refine (TauCeti.ringChooseSpan (X : ℚ[X])).sum_mem fun i _ ↦ ?_
    rw [coeff_map, eq_intCast, Int.cast_smul_eq_zsmul]
    exact (TauCeti.ringChooseSpan (X : ℚ[X])).zsmul_mem
      (preHilbertPoly_mem_ringChooseSpan d i) (h.coeff i)

end Rational

end Polynomial

namespace TauCeti

open Polynomial

attribute [local instance] BinomialRing.toHasUniqueDiv

/-- Composing a polynomial in `ringChooseSpan (X : ℚ[X])` with `X + C (a : ℚ)` for `a : ℤ` keeps it
inside `ringChooseSpan (X : ℚ[X])`. -/
theorem comp_X_add_intCast_mem_ringChooseSpan {p : ℚ[X]}
    (hp : p ∈ ringChooseSpan (X : ℚ[X])) (a : ℤ) :
    p.comp (X + C (a : ℚ)) ∈ ringChooseSpan (X : ℚ[X]) := by
  rw [ringChooseSpan_def] at hp
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    have hcomp : (Ring.choose (X : ℚ[X]) n).comp (X + C (a : ℚ)) =
        Ring.choose (X + (a : ℚ[X])) n := by
      have h := Ring.map_choose (compRingHom (X + C (a : ℚ))) (X : ℚ[X]) n
      rwa [coe_compRingHom_apply, coe_compRingHom_apply, X_comp, map_intCast] at h
    rw [hcomp]
    exact ringChoose_add_intCast_mem_ringChooseSpan (X : ℚ[X]) a n
  | zero => simp
  | add q₁ q₂ _ _ h₁ h₂ =>
    rw [add_comp]
    exact (ringChooseSpan (X : ℚ[X])).add_mem h₁ h₂
  | neg q _ hq =>
    rw [neg_comp]
    exact (ringChooseSpan (X : ℚ[X])).neg_mem hq

/-- Composing a polynomial in `ringChooseSpan (X : ℚ[X])` with `X - C (a : ℚ)` for `a : ℤ` keeps it
inside `ringChooseSpan (X : ℚ[X])`. -/
theorem comp_X_sub_intCast_mem_ringChooseSpan {p : ℚ[X]}
    (hp : p ∈ ringChooseSpan (X : ℚ[X])) (a : ℤ) :
    p.comp (X - C (a : ℚ)) ∈ ringChooseSpan (X : ℚ[X]) := by
  simpa only [sub_eq_add_neg, Int.cast_neg, map_neg] using
    comp_X_add_intCast_mem_ringChooseSpan hp (-a)

/-- Every polynomial in `ringChooseSpan (X : ℚ[X])` takes integer values at all integers. -/
theorem exists_intCast_eq_eval_of_mem_ringChooseSpan {p : ℚ[X]}
    (hp : p ∈ ringChooseSpan (X : ℚ[X])) (m : ℤ) :
    ∃ z : ℤ, (z : ℚ) = p.eval (m : ℚ) := by
  rw [ringChooseSpan_def] at hp
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    refine ⟨Ring.choose m n, ?_⟩
    have hev := Ring.map_choose (evalRingHom (m : ℚ)) (X : ℚ[X]) n
    simpa only [coe_evalRingHom, eval_X, TauCeti.Ring.choose_intCast] using hev.symm
  | zero => exact ⟨0, by simp⟩
  | add q₁ q₂ _ _ h₁ h₂ =>
    obtain ⟨z₁, hz₁⟩ := h₁
    obtain ⟨z₂, hz₂⟩ := h₂
    exact ⟨z₁ + z₂, by simp [← hz₁, ← hz₂]⟩
  | neg q _ hq =>
    obtain ⟨z, hz⟩ := hq
    exact ⟨-z, by simp [← hz]⟩

end TauCeti
