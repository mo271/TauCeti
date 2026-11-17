/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
-- Private: Mathlib's radical-coefficient divisor lemma and monic-factorization lemmas.
import Mathlib.RingTheory.IntegralClosure.GoingDown
import TauCeti.RingTheory.Polynomial.Monic.Basic

/-!
# The polynomial `(1 + X) ^ n - 1` and distinguished polynomials

The polynomial `(1 + X) ^ n - 1` over a ring `R` is monic of degree `n` for `n ≠ 0`,
with constant coefficient `0` and, for `0 < k`, `k`-th coefficient the binomial coefficient
`n.choose k`. Over a commutative ring, when `n = p ^ m` is a power of a prime `p`, every
binomial coefficient `(p ^ m).choose k` with `0 < k < p ^ m` is divisible by `p`, so the
polynomial is *distinguished* at every ideal `I` containing `p`: monic with all non-leading
coefficients in `I`. Over the `p`-adic integers, or any complete local ring of residue
characteristic `p`, this is the shape of divisor for which Mathlib's Weierstrass division is
available.

This is the polynomial cutting out the finite levels of the power-series coordinate on the
completed group algebra `ℤ_p[[Γ]]` of a procyclic pro-`p` group `Γ`: at a level `Γ ⧸ U` of order
`p ^ m`, the class of the topological generator satisfies `σ ^ (p ^ m) = 1`, so
`(1 + X) ^ (p ^ m) - 1` vanishes at `X = σ - 1`.

For a general polynomial `F` distinguished at an ideal `I` with `I ^ e ⊆ (p)`, every root `t` of
`F` in an `O`-algebra satisfies `t ^ deg F ∈ I`, hence `p ∣ t ^ (deg F * e)`. Distinguished
polynomials at `I` are closed under finite products, including the empty product `1`. Conversely,
by `Polynomial.coeff_mem_radical_span_coeff_of_dvd`, any monic divisor of a polynomial
distinguished at `I` is distinguished at `I.radical` (hence at `I` itself when `I` is radical).
Consequently, over a commutative ring without zero divisors, every polynomial distinguished at a
radical ideal factors as a product of irreducible distinguished polynomials, and uniquely so when
the polynomial ring is a unique factorization monoid.

## Main results

* `TauCeti.Polynomial.monic_one_add_X_pow_sub_one`: `(1 + X) ^ n - 1` is monic for `n ≠ 0`.
* `TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one`: `(1 + X) ^ n - 1` has `natDegree` equal
  to `n` (at `n = 0` the polynomial is `0`, whose `natDegree` is `0` by convention).
* `TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one`: `(1 + X) ^ (p ^ m) - 1` is
  distinguished at every ideal containing `p`.
* `Polynomial.IsDistinguishedAt.natCast_dvd_pow_of_aeval_eq_zero`: a root `t` of a polynomial `F`
  distinguished at `I`, with `I ^ e ⊆ (p)`, satisfies `p ∣ t ^ (deg F * e)`.
* `Polynomial.isDistinguishedAt_one`, `Polynomial.IsDistinguishedAt.pow`,
  `Polynomial.isDistinguishedAt_prod`, `Polynomial.isDistinguishedAt_multiset_prod`: `1`, powers,
  finite products and multiset products of distinguished polynomials are distinguished.
* `Polynomial.IsDistinguishedAt.mono`: distinguishedness is monotone in the ideal.
* `Polynomial.IsDistinguishedAt.of_dvd_radical`, `Polynomial.IsDistinguishedAt.of_dvd`,
  `Polynomial.IsDistinguishedAt.mul_iff`: monic divisors of a distinguished polynomial at `I` are
  distinguished at `I.radical` (and at `I` when `I` is radical).
* `Polynomial.IsDistinguishedAt.existsUnique_associated_radical_of_dvd`,
  `Polynomial.IsDistinguishedAt.existsUnique_associated_of_dvd`: over a commutative ring without
  zero divisors, every divisor of a distinguished polynomial is associated to a unique
  distinguished polynomial.
* `Polynomial.IsDistinguishedAt.exists_multiset_irreducible_prod_eq`,
  `Polynomial.IsDistinguishedAt.existsUnique_multiset_irreducible_prod_eq`: factorization of a
  distinguished polynomial into irreducible distinguished polynomials over a radical ideal.
-/

public section

namespace TauCeti

open Polynomial

namespace Polynomial

variable {R : Type*}

section Ring

variable [Ring R]

/-- The polynomial `(1 + X) ^ n - 1` has `natDegree` equal to `n`. For `n ≠ 0` this is its
degree; at `n = 0` the polynomial is `0`, whose `natDegree` is `0` by convention. -/
@[simp]
theorem natDegree_one_add_X_pow_sub_one [Nontrivial R] (n : ℕ) :
    ((1 + X) ^ n - 1 : R[X]).natDegree = n := by
  simpa [add_comm] using
    (natDegree_sub_C (p := (X + C (1 : R)) ^ n) (a := 1)).trans
      (natDegree_pow_X_add_C n 1)

/-- The polynomial `(1 + X) ^ n - 1` is monic for `n ≠ 0`. -/
theorem monic_one_add_X_pow_sub_one {n : ℕ} (hn : n ≠ 0) : ((1 + X) ^ n - 1 : R[X]).Monic := by
  nontriviality R
  rw [Monic, leadingCoeff, natDegree_one_add_X_pow_sub_one]
  simp [coeff_one_add_X_pow, coeff_one, hn]

end Ring

variable [CommRing R]

/-- **`(1 + X) ^ (p ^ m) - 1` is a distinguished polynomial at every ideal containing `p`**, for a
prime `p`: it is monic, its constant coefficient is `0`, and its other non-leading coefficients are
the binomial coefficients `(p ^ m).choose k` with `0 < k < p ^ m`, which `p` divides. -/
theorem isDistinguishedAt_one_add_X_pow_sub_one {p : ℕ} (hp : p.Prime) {I : Ideal R}
    (hI : (p : R) ∈ I) (m : ℕ) : ((1 + X) ^ p ^ m - 1 : R[X]).IsDistinguishedAt I := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨⟨fun hk ↦ by simp [natDegree_of_subsingleton] at hk⟩, monic_of_subsingleton _⟩
  refine ⟨⟨fun {k} hk ↦ ?_⟩, monic_one_add_X_pow_sub_one (pow_ne_zero m hp.ne_zero)⟩
  rw [natDegree_one_add_X_pow_sub_one] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [coeff_one_add_X_pow]
  · rw [coeff_sub, coeff_one_add_X_pow, coeff_one, ite_eq_right hk0.ne', sub_zero]
    exact I.mem_of_dvd (Nat.cast_dvd_cast (hp.dvd_choose_pow hk0.ne' hk.ne)) hI

end Polynomial

end TauCeti

namespace Polynomial

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- The constant polynomial `1` is distinguished at every ideal. -/
theorem isDistinguishedAt_one : (1 : R[X]).IsDistinguishedAt I :=
  ⟨⟨fun hn ↦ by simp at hn⟩, monic_one⟩

/-- A power of a distinguished polynomial is distinguished. -/
theorem IsDistinguishedAt.pow {f : R[X]} (hf : f.IsDistinguishedAt I) (n : ℕ) :
    (f ^ n).IsDistinguishedAt I := by
  induction n with
  | zero => exact pow_zero f ▸ isDistinguishedAt_one
  | succ n ih => exact pow_succ f n ▸ ih.mul hf

/-- A finite product of distinguished polynomials is distinguished. -/
theorem isDistinguishedAt_prod {ι : Type*} {s : Finset ι} {f : ι → R[X]}
    (hf : ∀ i ∈ s, (f i).IsDistinguishedAt I) : (∏ i ∈ s, f i).IsDistinguishedAt I :=
  Finset.prod_induction f (·.IsDistinguishedAt I) (fun _ _ ↦ IsDistinguishedAt.mul)
    isDistinguishedAt_one hf

/-- A multiset product of distinguished polynomials is distinguished. -/
theorem isDistinguishedAt_multiset_prod {s : Multiset R[X]}
    (hf : ∀ f ∈ s, f.IsDistinguishedAt I) : s.prod.IsDistinguishedAt I :=
  Multiset.prod_induction (·.IsDistinguishedAt I) s (fun _ _ ↦ IsDistinguishedAt.mul)
    isDistinguishedAt_one hf

end Polynomial

namespace Polynomial.IsDistinguishedAt

variable {O : Type*} [CommRing O] {I : Ideal O} {F : O[X]} {p e : ℕ}

/-- If `F` is distinguished at `I` and `I ^ e ⊆ (p)`, then every root `t` of `F` in an `O`-algebra
satisfies `p ∣ t ^ (deg F * e)`. -/
theorem natCast_dvd_pow_of_aeval_eq_zero (hF : F.IsDistinguishedAt I)
    (hI : I ^ e ≤ Ideal.span {(p : O)}) {S : Type*} [CommRing S] [Algebra O S] {t : S}
    (ht : aeval t F = 0) : (p : S) ∣ t ^ (F.natDegree * e) := by
  have h := hF.toIsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map ht
    hF.monic F.natDegree natDegree_map_le
  have h' : t ^ (F.natDegree * e) ∈ (Ideal.span {(p : O)}).map (algebraMap O S) := by
    rw [pow_mul]
    exact Ideal.map_mono hI (Ideal.map_pow (algebraMap O S) I e ▸ Ideal.pow_mem_pow h e)
  rwa [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at h'

/-- A polynomial distinguished at `I` is distinguished at every ideal containing `I`. -/
theorem mono {J : Ideal O} (hF : F.IsDistinguishedAt I) (hIJ : I ≤ J) :
    F.IsDistinguishedAt J :=
  ⟨⟨fun hn ↦ hIJ (hF.mem hn)⟩, hF.monic⟩

/-- A monic divisor of a polynomial distinguished at `I` is distinguished at `I.radical`. -/
theorem of_dvd_radical {G : O[X]} (hF : F.IsDistinguishedAt I) (hG : G.Monic) (hdvd : G ∣ F) :
    G.IsDistinguishedAt I.radical :=
  ⟨⟨fun {i} hi ↦ Ideal.radical_mono
    (Ideal.span_le.mpr (by rintro _ ⟨j, hj, rfl⟩; exact hF.mem hj))
    (Polynomial.coeff_mem_radical_span_coeff_of_dvd F G hF.monic hG hdvd i hi.ne)⟩, hG⟩

/-- Over a radical ideal `I`, every monic divisor of a polynomial distinguished at `I` is
distinguished at `I`. -/
theorem of_dvd {G : O[X]} (hF : F.IsDistinguishedAt I) (hI : I.IsRadical) (hG : G.Monic)
    (hdvd : G ∣ F) : G.IsDistinguishedAt I :=
  hI.radical ▸ hF.of_dvd_radical hG hdvd

/-- Over a radical ideal `I`, the product of two monic polynomials is distinguished at `I` if and
only if both factors are. -/
theorem mul_iff {G : O[X]} (hI : I.IsRadical) (hF : F.Monic) (hG : G.Monic) :
    (F * G).IsDistinguishedAt I ↔ F.IsDistinguishedAt I ∧ G.IsDistinguishedAt I :=
  ⟨fun h ↦ ⟨h.of_dvd hI hF (dvd_mul_right F G), h.of_dvd hI hG (dvd_mul_left G F)⟩,
    fun ⟨h₁, h₂⟩ ↦ h₁.mul h₂⟩

/-- Over a commutative ring without zero divisors, every divisor of a polynomial distinguished at
`I` is associated to a unique polynomial distinguished at `I.radical`. -/
theorem existsUnique_associated_radical_of_dvd [NoZeroDivisors O] {d : O[X]}
    (hF : F.IsDistinguishedAt I) (hd : d ∣ F) :
    ∃! G : O[X], G.IsDistinguishedAt I.radical ∧ Associated d G := by
  obtain ⟨G, ⟨hGmon, hassoc⟩, huniq⟩ := hF.monic.existsUnique_associated_of_dvd hd
  refine ⟨G, ⟨hF.of_dvd_radical hGmon (hassoc.symm.dvd.trans hd), hassoc⟩, ?_⟩
  rintro G' ⟨hG', hG'assoc⟩
  exact huniq G' ⟨hG'.monic, hG'assoc⟩

/-- Over a commutative ring without zero divisors, every divisor of a polynomial distinguished at a
radical ideal `I` is associated to a unique polynomial distinguished at `I`. -/
theorem existsUnique_associated_of_dvd [NoZeroDivisors O] {d : O[X]}
    (hF : F.IsDistinguishedAt I) (hI : I.IsRadical) (hd : d ∣ F) :
    ∃! G : O[X], G.IsDistinguishedAt I ∧ Associated d G :=
  hI.radical ▸ hF.existsUnique_associated_radical_of_dvd hd

/-- Over a commutative ring without zero divisors, every polynomial distinguished at a radical
ideal `I` factors as a multiset product of irreducible polynomials distinguished at `I`. -/
theorem exists_multiset_irreducible_prod_eq [NoZeroDivisors O]
    (hF : F.IsDistinguishedAt I) (hI : I.IsRadical) :
    ∃ s : Multiset O[X], (∀ G ∈ s, G.IsDistinguishedAt I ∧ Irreducible G) ∧ s.prod = F := by
  obtain ⟨s, hs, rfl⟩ := hF.monic.exists_multiset_irreducible_prod_eq
  exact ⟨s, fun G hG ↦
    ⟨hF.of_dvd hI (hs G hG).1 (Multiset.dvd_prod hG), (hs G hG).2⟩, rfl⟩

/-- Over a commutative ring without zero divisors, every polynomial distinguished at `I` factors
as a multiset product of irreducible polynomials distinguished at `I.radical`. -/
theorem exists_multiset_irreducible_radical_prod_eq [NoZeroDivisors O]
    (hF : F.IsDistinguishedAt I) :
    ∃ s : Multiset O[X], (∀ G ∈ s, G.IsDistinguishedAt I.radical ∧ Irreducible G) ∧ s.prod = F :=
  (hF.mono Ideal.le_radical).exists_multiset_irreducible_prod_eq (Ideal.radical_isRadical I)

/-- Over a commutative ring without zero divisors whose polynomial ring is a unique factorization
monoid, every polynomial distinguished at a radical ideal `I` factors uniquely as a multiset
product of irreducible polynomials distinguished at `I`. -/
theorem existsUnique_multiset_irreducible_prod_eq [NoZeroDivisors O]
    [UniqueFactorizationMonoid O[X]] (hF : F.IsDistinguishedAt I) (hI : I.IsRadical) :
    ∃! s : Multiset O[X], (∀ G ∈ s, G.IsDistinguishedAt I ∧ Irreducible G) ∧ s.prod = F := by
  obtain ⟨s, ⟨hs, hsprod⟩, huniq⟩ := hF.monic.existsUnique_multiset_irreducible_prod_eq
  refine ⟨s, ⟨fun G hG ↦ ⟨hF.of_dvd hI (hs G hG).1 (hsprod ▸ Multiset.dvd_prod hG), (hs G hG).2⟩,
    hsprod⟩, ?_⟩
  rintro t ⟨ht, htprod⟩
  exact huniq t ⟨fun G hG ↦ ⟨(ht G hG).1.monic, (ht G hG).2⟩, htprod⟩

/-- Over a commutative ring without zero divisors whose polynomial ring is a unique factorization
monoid, every polynomial distinguished at `I` factors uniquely as a multiset product of irreducible
polynomials distinguished at `I.radical`. -/
theorem existsUnique_multiset_irreducible_radical_prod_eq [NoZeroDivisors O]
    [UniqueFactorizationMonoid O[X]] (hF : F.IsDistinguishedAt I) :
    ∃! s : Multiset O[X], (∀ G ∈ s, G.IsDistinguishedAt I.radical ∧ Irreducible G) ∧ s.prod = F :=
  (hF.mono Ideal.le_radical).existsUnique_multiset_irreducible_prod_eq (Ideal.radical_isRadical I)

end Polynomial.IsDistinguishedAt
