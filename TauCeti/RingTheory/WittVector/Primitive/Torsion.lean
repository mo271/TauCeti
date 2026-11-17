/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Primitive.Basic
import TauCeti.RingTheory.Perfect.Basic

/-!
# Bounded `p`-torsion in principal Witt-vector quotients

Let `S` be a perfect ring of characteristic `p`, possibly with zero divisors, and let `ξ : 𝕎 S`
be a distinguished Witt vector (its first Witt coordinate `ξ.coeff 1` is a unit). Since
`p ^ 2 ∣ ξ * g` forces `p ∣ g` (`WittVector.IsDistinguished.p_dvd_of_p_sq_dvd_mul`) and `p` is a
nonzerodivisor in `𝕎 S` (`WittVector.eq_zero_of_p_mul_eq_zero`), we have `p ^ 2 * f ∈ (ξ) →
p * f ∈ (ξ)`. By induction, every element of the quotient `𝕎 S ⧸ (ξ)` annihilated by a power of
`p` is already annihilated by `p`: the `p`-primary torsion of `𝕎 S ⧸ (ξ)` has bound one
(Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral `p`-adic Hodge theory*,
Proposition 4.19(3)).

## Main results

* `WittVector.IsDistinguished.p_dvd_of_p_sq_dvd_mul`: if `p ^ 2 ∣ ξ * g` then `p ∣ g`.
* `WittVector.IsDistinguished.p_mul_mem_span_of_p_sq_mul_mem_span`: if `p ^ 2 * f ∈ (ξ)` then
  `p * f ∈ (ξ)`.
* `WittVector.IsDistinguished.p_mul_mem_span_of_p_pow_mul_mem_span`,
  `WittVector.IsDistinguished.p_pow_mul_mem_span_iff`: the same for arbitrary powers `p ^ n`.
* `WittVector.IsDistinguished.p_mul_eq_zero_of_pow_mul_eq_zero`,
  `WittVector.IsDistinguished.p_pow_mul_eq_zero_iff`: in `𝕎 S ⧸ (ξ)`, `p ^ n * x = 0` implies
  `p * x = 0` for every `n : ℕ` (and is equivalent to `p * x = 0` for `n ≠ 0`).

## References

* B. Bhatt, M. Morrow, P. Scholze, *Topological Hochschild homology and integral `p`-adic Hodge
  theory*, Proposition 4.19(3).
-/

public section

namespace WittVector

open Ideal

variable {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]
  {ξ : WittVector p S}

local notation "𝕎" => WittVector p

namespace IsDistinguished

/-- **Divisibility detection for a distinguished Witt vector** (Bhatt–Morrow–Scholze, *Topological
Hochschild homology and integral `p`-adic Hodge theory*, proof of Proposition 4.19(3)). Over a
perfect ring of characteristic `p`, if `ξ` is distinguished and `p ^ 2 ∣ ξ * g`, then `p ∣ g`. -/
theorem p_dvd_of_p_sq_dvd_mul (hξ : ξ.IsDistinguished) {g : 𝕎 S}
    (h : (p : 𝕎 S) ^ 2 ∣ ξ * g) : (p : 𝕎 S) ∣ g := by
  have := TauCeti.isReduced_of_perfectRing S p
  rw [← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]
  obtain ⟨q, hq⟩ := h
  refine hξ.coeff_zero_eq_zero_of_mul ?_ ?_
  · rw [hq, mul_comm, mul_pow_charP_coeff_zero q two_pos]
  · rw [hq, mul_comm, mul_pow_charP_coeff_zero q one_lt_two]

/-- **One-step torsion reduction in `𝕎 S`.** Over a perfect ring `S` of characteristic `p`, if
`ξ : 𝕎 S` is distinguished and `p ^ 2 * f ∈ (ξ)`, then `p * f ∈ (ξ)` (Bhatt–Morrow–Scholze,
*Topological Hochschild homology and integral `p`-adic Hodge theory*, proof of
Proposition 4.19(3)). -/
theorem p_mul_mem_span_of_p_sq_mul_mem_span (hξ : ξ.IsDistinguished) {f : 𝕎 S}
    (hf : (p : 𝕎 S) ^ 2 * f ∈ span {ξ}) : (p : 𝕎 S) * f ∈ span {ξ} := by
  obtain ⟨g, hg⟩ := mem_span_singleton.mp hf
  obtain ⟨g', rfl⟩ := hξ.p_dvd_of_p_sq_dvd_mul ⟨f, hg.symm⟩
  have hdiff : ((p : 𝕎 S) * f - ξ * g') * p = 0 := by linear_combination hg
  have heq : (p : 𝕎 S) * f = ξ * g' := sub_eq_zero.mp (eq_zero_of_p_mul_eq_zero _ hdiff)
  exact mem_span_singleton.mpr ⟨g', heq⟩

/-- Over a perfect ring `S` of characteristic `p`, if `ξ : 𝕎 S` is distinguished and
`p ^ n * f ∈ (ξ)` for some `n : ℕ`, then `p * f ∈ (ξ)`. -/
theorem p_mul_mem_span_of_p_pow_mul_mem_span (hξ : ξ.IsDistinguished) (n : ℕ) {f : 𝕎 S}
    (hf : (p : 𝕎 S) ^ n * f ∈ span {ξ}) : (p : 𝕎 S) * f ∈ span {ξ} := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul] at hf
    exact mul_mem_left _ _ hf
  | succ n ih =>
    cases n with
    | zero => simpa using hf
    | succ n =>
      apply ih
      have hsq : (p : 𝕎 S) ^ 2 * ((p : 𝕎 S) ^ n * f) ∈ span {ξ} := by
        convert hf using 1
        ring
      have h1 := hξ.p_mul_mem_span_of_p_sq_mul_mem_span hsq
      convert h1 using 1
      ring

/-- Over a perfect ring `S` of characteristic `p`, if `ξ : 𝕎 S` is distinguished and `n ≠ 0`, then
`p ^ n * f ∈ (ξ)` if and only if `p * f ∈ (ξ)`. -/
theorem p_pow_mul_mem_span_iff (hξ : ξ.IsDistinguished) {n : ℕ} (hn : n ≠ 0) (f : 𝕎 S) :
    (p : 𝕎 S) ^ n * f ∈ span {ξ} ↔ (p : 𝕎 S) * f ∈ span {ξ} := by
  refine ⟨hξ.p_mul_mem_span_of_p_pow_mul_mem_span n, fun h ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ, mul_assoc]
  exact mul_mem_left _ _ h

/-- **Bound-one `p`-torsion in principal Witt-vector quotients** (Bhatt–Morrow–Scholze,
*Topological Hochschild homology and integral `p`-adic Hodge theory*, Proposition 4.19(3)). Over
an arbitrary perfect ring `S` of characteristic `p`, if `ξ : 𝕎 S` is distinguished, then every
`p`-power torsion element of `𝕎 S ⧸ (ξ)` is annihilated by `p`. -/
theorem p_mul_eq_zero_of_pow_mul_eq_zero (hξ : ξ.IsDistinguished) (n : ℕ)
    {x : 𝕎 S ⧸ span {ξ}} (hx : (p : 𝕎 S ⧸ span {ξ}) ^ n * x = 0) :
    (p : 𝕎 S ⧸ span {ξ}) * x = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_natCast (Ideal.Quotient.mk (span {ξ})), ← map_pow, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [← map_natCast (Ideal.Quotient.mk (span {ξ})), ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact hξ.p_mul_mem_span_of_p_pow_mul_mem_span n hx

/-- Over a perfect ring `S` of characteristic `p`, if `ξ : 𝕎 S` is distinguished and `n ≠ 0`, then
`p ^ n * x = 0` if and only if `p * x = 0` in `𝕎 S ⧸ (ξ)`. -/
theorem p_pow_mul_eq_zero_iff (hξ : ξ.IsDistinguished) {n : ℕ} (hn : n ≠ 0)
    (x : 𝕎 S ⧸ span {ξ}) :
    (p : 𝕎 S ⧸ span {ξ}) ^ n * x = 0 ↔ (p : 𝕎 S ⧸ span {ξ}) * x = 0 := by
  refine ⟨hξ.p_mul_eq_zero_of_pow_mul_eq_zero n, fun h ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ, mul_assoc, h, mul_zero]

end IsDistinguished

end WittVector
