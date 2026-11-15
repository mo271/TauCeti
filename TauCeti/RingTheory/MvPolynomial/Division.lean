/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Descending divisibility of multivariate polynomials via coprime denominator clearing

Suppose `φ : R →+* S` is an injective ring homomorphism and `H * map φ Δ = map φ P` in
`MvPolynomial σ S`. When `R` is not a unique factorization domain, divisibility of `map φ P` by
`map φ Δ` over `S` (for instance `S = FractionRing R`) need not descend to `Δ ∣ P` over `R` in
general. However, if `Δ` contains an isolated pure-power monomial `X_j ^ k` — meaning
`Finsupp.single j k` is the unique exponent in `Δ.support` with `j`-th coordinate at least `k` —
then downward induction on the `j`-degree of `H` shows that `φ (Δ.coeff (Finsupp.single j k))` to
the power `H.degreeOf j + 1` clears every coefficient of `H` into `Set.range φ`.

When `Δ` has two such isolated pure powers whose coefficients generate coprime powers in `R` (or,
more generally, whenever two coprime elements `u₁, u₂ : R` multiply every coefficient of `H` into
`Set.range φ`), a Bézout combination puts every coefficient of `H` into `Set.range φ`, so `H` lies
in `Set.range (map φ)` and injectivity of `φ` descends the divisibility to `Δ ∣ P` in
`MvPolynomial σ R`.

## Main results

* `MvPolynomial.pow_mul_coeff_mem_range_of_mul_map_eq`: clearing coefficients of `H` into
  `Set.range φ` using an isolated pure-power monomial of `Δ`.
* `MvPolynomial.dvd_of_mul_map_eq_of_isCoprime`: descending `H * map φ Δ = map φ P` to `Δ ∣ P`
  along an injective `φ : R →+* S` when two coprime elements of `R` clear the coefficients of `H`.
-/

public section

namespace MvPolynomial

/-- Suppose `H * map φ Δ = map φ P` over commutative rings, and `Finsupp.single j k` is the unique
exponent in the support of `Δ` whose `j`-th coordinate is at least `k`. Then multiplying every
coefficient of `H` by `φ (Δ.coeff (Finsupp.single j k)) ^ (H.degreeOf j + 1)` lands in
`Set.range φ`. -/
theorem pow_mul_coeff_mem_range_of_mul_map_eq {σ R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} {Δ P : MvPolynomial σ R} {H : MvPolynomial σ S}
    (hmul : H * map φ Δ = map φ P) {j : σ} {k : ℕ}
    (huniq : ∀ s ∈ Δ.support, k ≤ s j → s = Finsupp.single j k) (e : σ →₀ ℕ) :
    φ (Δ.coeff (Finsupp.single j k)) ^ (H.degreeOf j + 1) * H.coeff e ∈ Set.range φ := by
  classical
  let u := Δ.coeff (Finsupp.single j k)
  suffices ∀ r : ℕ, ∀ d : σ →₀ ℕ, H.degreeOf j - d j < r → φ u ^ r * H.coeff d ∈ φ.range from
    RingHom.mem_range.mp (this (H.degreeOf j + 1) e (by omega))
  intro r
  induction r with
  | zero => intro d hd; omega
  | succ r ih =>
    intro d hd
    by_cases hd0 : H.coeff d = 0
    · simp [hd0]
    have hc := congrArg (fun p ↦ p.coeff (d + Finsupp.single j k)) hmul
    rw [coeff_mul, coeff_map] at hc
    have hx₀ : (d, Finsupp.single j k) ∈ Finset.antidiagonal (d + Finsupp.single j k) :=
      Finset.mem_antidiagonal.mpr rfl
    rw [← Finset.add_sum_erase _ _ hx₀, coeff_map] at hc
    have hsum : φ u ^ r *
        ∑ x ∈ (Finset.antidiagonal (d + Finsupp.single j k)).erase (d, Finsupp.single j k),
          H.coeff x.1 * (map φ Δ).coeff x.2 ∈ φ.range := by
      rw [Finset.mul_sum]
      refine φ.range.sum_mem fun x hx ↦ ?_
      rw [coeff_map, ← mul_assoc]
      by_cases hx1 : H.coeff x.1 = 0
      · simp [hx1]
      by_cases hx2 : Δ.coeff x.2 = 0
      · simp [hx2]
      obtain ⟨hne, hadd⟩ := Finset.mem_erase.mp hx
      rw [Finset.mem_antidiagonal] at hadd
      have hlt : x.2 j < k := by
        by_contra! hge
        have hs := huniq x.2 (mem_support_iff.mpr hx2) hge
        exact hne (Prod.ext (add_right_cancel (hs ▸ hadd)) hs)
      have hxj : d j < x.1 j := by
        have := DFunLike.congr_fun hadd j
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        omega
      have hdeg := monomial_le_degreeOf j (mem_support_iff.mpr hx1)
      exact φ.range.mul_mem (ih x.1 (by omega)) ⟨Δ.coeff x.2, rfl⟩
    have hrhs : φ u ^ r * φ (P.coeff (d + Finsupp.single j k)) ∈ φ.range :=
      φ.range.mul_mem (φ.range.pow_mem ⟨u, rfl⟩ r) ⟨_, rfl⟩
    have heq : φ u ^ (r + 1) * H.coeff d =
        φ u ^ r * φ (P.coeff (d + Finsupp.single j k)) -
          φ u ^ r *
            ∑ x ∈ (Finset.antidiagonal (d + Finsupp.single j k)).erase (d, Finsupp.single j k),
              H.coeff x.1 * (map φ Δ).coeff x.2 := by
      dsimp only [u]; rw [← hc]; ring
    rw [heq]
    exact φ.range.sub_mem hrhs hsum

/-- If `φ : R →+* S` is injective, `H * map φ Δ = map φ P`, and two coprime elements `u₁, u₂ : R`
each multiply every coefficient of `H` into `Set.range φ`, then `Δ ∣ P` in `MvPolynomial σ R`. -/
theorem dvd_of_mul_map_eq_of_isCoprime {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {φ : R →+* S} (hφ : Function.Injective φ) {Δ P : MvPolynomial σ R} {H : MvPolynomial σ S}
    (hmul : H * map φ Δ = map φ P) {u₁ u₂ : R}
    (h₁ : ∀ e, φ u₁ * H.coeff e ∈ Set.range φ)
    (h₂ : ∀ e, φ u₂ * H.coeff e ∈ Set.range φ)
    (hcop : IsCoprime u₁ u₂) : Δ ∣ P := by
  obtain ⟨a, b, hab⟩ := hcop
  have hmem : H ∈ Set.range (map φ) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨e, -, rfl⟩ := mem_coeffs_iff.mp hc
    obtain ⟨r₁, hr₁⟩ := h₁ e
    obtain ⟨r₂, hr₂⟩ := h₂ e
    refine ⟨a * r₁ + b * r₂, ?_⟩
    calc φ (a * r₁ + b * r₂)
        = φ a * (φ u₁ * H.coeff e) + φ b * (φ u₂ * H.coeff e) := by
          simp only [map_add, map_mul, hr₁, hr₂]
      _ = φ (a * u₁ + b * u₂) * H.coeff e := by simp only [map_add, map_mul]; ring
      _ = H.coeff e := by rw [hab, map_one, one_mul]
  obtain ⟨H₀, rfl⟩ := hmem
  exact ⟨H₀, (map_injective φ hφ (by rw [map_mul, mul_comm, hmul])).symm⟩

end MvPolynomial
