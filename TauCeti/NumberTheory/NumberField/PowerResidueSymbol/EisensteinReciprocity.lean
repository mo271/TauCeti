/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.EisensteinPrimary
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Relation
import Mathlib.RingTheory.Ideal.Int
import TauCeti.NumberTheory.DedekindDomain.RelNorm
import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Pointwise
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime and `K = ℚ(ζ_p)` the `p`-th cyclotomic field, with ring of integers
`𝓞 K = ℤ[ζ_p]`. For an element `α ∈ 𝓞 K` that is primary with respect to a primitive `p`-th root
of unity (`TauCeti.IsEisensteinPrimary`), and a rational integer `a` prime to `p`, the
**Eisenstein reciprocity law** asserts that

`(α / a)_p = (a / α)_p`,

the `p`-th power residue symbols (`Ideal.powerResidueSymbolIdeal`) being taken at the principal
ideals `a 𝓞 K` and `α 𝓞 K`. Neither `α` being a nonunit, nor `a ≠ ±1`, nor coprimality of `a` and
`α` need be assumed: if `a` and `α` are not coprime, both symbols vanish.

The proof goes through the Gauss sum power `Φ((α))` and the Stickelberger product
`α ^ γ = ∏_σ (σ⁻¹ α) ^ c(σ)` (`TauCeti.stickelbergerProduct`):

1. **Power residue symbol of the Stickelberger product**
   (`Ideal.powerResidueSymbolIdeal_stickelbergerProduct`): in any cyclotomic field `ℚ(ζ_m)` with
   `m ≥ 2`, `(α ^ γ / B)_m = (α / N(B))_m` for every ideal `B` of `𝓞 K` and every `α ∈ 𝓞 K`. At
   a maximal ideal `P`, Galois equivariance of the power residue symbol turns each factor
   `(σ⁻¹ α / P)_m ^ c(σ) = σ ((σ⁻¹ α / P)_m)` into `(α / σ P)_m`, and `∏_σ σ P = N(P) 𝓞 K`
   (`Ideal.prod_smul_eq_span_absNorm`).
2. **Eisenstein reciprocity at the norm of an ideal**
   (`IsPrimitiveRoot.eisenstein_reciprocity_absNorm`): for `α` primary in `ℚ(ζ_p)` and an ideal `B`
   whose norm is prime to `p`, `(α / N(B))_p = (N(B) / α)_p`. By multiplicativity this reduces to a
   maximal ideal `P` whose norm is prime to `p` and to `N((α))`, where Stickelberger's relation for
   primary integers (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`) gives
   `Φ((α)) = ±α ^ γ`, `(-1 / P)_p = 1` since `p` is odd, and
   `Ideal.powerResidueSymbol_stickelbergerPhi` evaluates `(Φ((α)) / P)_p = (N(P) / α)_p`.
3. **The Eisenstein reciprocity law** (`IsPrimitiveRoot.eisenstein_reciprocity`): negation leaves
   both sides unchanged since `p` is odd, reducing to a natural number `n` prime to `p`
   (`IsPrimitiveRoot.eisenstein_reciprocity_natCast`), and multiplicativity reduces to a rational
   prime `q ≠ p` coprime to `α`. Picking a prime `P` of `𝓞 K` above `q`, its norm is `N(P) = q ^ f`
   where the inertia degree `f` divides `[K : ℚ] = p - 1`, so `f` is prime to `p`; the previous
   step gives `(α / q)_p ^ f = (q / α)_p ^ f` between `p`-th roots of unity, hence
   `(α / q)_p = (q / α)_p`.

## Main results

* `Ideal.powerResidueSymbolIdeal_stickelbergerProduct`: `(α ^ γ / B)_m = (α / N(B))_m` in `ℚ(ζ_m)`
  for `m ≥ 2`, any ideal `B`, and any `α ∈ 𝓞 K`.
* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / N(B))_p = (N(B) / α)_p` for an odd prime
  `p`, a primary `α ∈ 𝓞 K`, and an ideal `B` of norm prime to `p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for an odd prime `p`,
  a primary `α ∈ 𝓞 K`, and a natural number `n` not divisible by `p`.
* `IsPrimitiveRoot.eisenstein_reciprocity`: the Eisenstein reciprocity law `(α / a)_p = (a / α)_p`
  for an odd prime `p`, a primary `α ∈ 𝓞 K`, and a rational integer `a` not divisible by `p`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §§2, 5.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid IsCyclotomicExtension.Rat
open scoped Pointwise

namespace Ideal

variable {m : ℕ} [NeZero m] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]

/-- For `2 ≤ m`, every cyclotomic character representative `c(σ) ∈ [0, m)` is nonzero. -/
private theorem galEquivZMod_val_ne_zero (hm : 2 ≤ m) (σ : Gal(K/ℚ)) :
    (galEquivZMod m K σ : ZMod m).val ≠ 0 := by
  have : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (by omega)
  intro h
  have hz : (galEquivZMod m K σ : ZMod m) = 0 := by
    rw [← ZMod.natCast_zmod_val (galEquivZMod m K σ : ZMod m), h, Nat.cast_zero]
  exact Units.ne_zero (galEquivZMod m K σ) hz

/-- At a maximal ideal `P`, the `m`-th power residue symbol of the Stickelberger product `α ^ γ`
equals `(α / N(P))_m`. -/
private theorem powerResidueSymbolIdeal_stickelbergerProduct_of_isMaximal (hm : 2 ≤ m)
    (P : Ideal (𝓞 K)) [P.IsMaximal] (α : 𝓞 K) :
    powerResidueSymbolIdeal P m (Quotient.mk P (TauCeti.stickelbergerProduct m α)) =
      powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) m (Quotient.mk _ α) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [powerResidueSymbolIdeal_of_isMaximal, TauCeti.stickelbergerProduct_def, map_prod, map_prod]
  -- Evaluate each factor `(σ⁻¹ α / P)_m ^ c(σ)` as `(α / σ P)_m` by Galois equivariance.
  have hterm (σ : Gal(K/ℚ)) :
      powerResidueSymbol P m (Quotient.mk P ((σ⁻¹ • α) ^ (galEquivZMod m K σ : ZMod m).val)) =
        powerResidueSymbolIdeal (σ • P) m (Quotient.mk (σ • P) α) := by
    rw [map_pow, map_pow]
    by_cases hα : Quotient.mk P (σ⁻¹ • α) = 0
    · rw [hα, MulChar.map_zero, zero_pow (galEquivZMod_val_ne_zero hm σ)]
      have hα' : Quotient.mk (σ • P) α = 0 := by
        rw [Quotient.eq_zero_iff_mem] at hα ⊢
        exact mem_pointwise_smul_iff_inv_smul_mem.mpr hα
      rw [hα', MulChar.map_zero]
    · have hpow := powerResidueSymbol_pow_eq_one (P := P) (n := m) hα
      rw [← galEquivZMod_smul_of_pow_eq m K σ hpow]
      have hmap := map_powerResidueSymbolIdeal (n := m) P
        (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ) (σ⁻¹ • α)
      have hPmap : P.map (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ) = σ • P :=
        (Ideal.pointwise_smul_def P).symm
      rw [powerResidueSymbolIdeal_of_isMaximal, hPmap] at hmap
      simpa only [MulSemiringAction.toRingEquiv_apply_apply, smul_inv_smul] using hmap
  rw [Finset.prod_congr rfl fun σ _ ↦ hterm σ, ← powerResidueSymbolIdeal_prod_right,
    prod_smul_eq_span_absNorm P]
  intro σ _
  exact Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField K)

/-- **Power residue symbol of the Stickelberger product.** Let `K` be the `m`-th cyclotomic field,
`m ≥ 2`, `B` an ideal of `𝓞 K`, and `α ∈ 𝓞 K`. Then `(α ^ γ / B)_m = (α / N(B))_m`, where
`α ^ γ = ∏_σ (σ⁻¹ α) ^ c(σ)` is `TauCeti.stickelbergerProduct m α`. No coprimality hypothesis is
needed. -/
theorem powerResidueSymbolIdeal_stickelbergerProduct (hm : 2 ≤ m) (B : Ideal (𝓞 K)) (α : 𝓞 K) :
    powerResidueSymbolIdeal B m (Quotient.mk B (TauCeti.stickelbergerProduct m α)) =
      powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) m (Quotient.mk _ α) := by
  induction B using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.cast_zero, span_singleton_zero, powerResidueSymbolIdeal_bot]
    -- At `⊥`, the trivial character detects whether the element is a unit in `𝓞 K`.
    have hunit : IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) (TauCeti.stickelbergerProduct m α)) ↔
        IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) α) := by
      simp only [Quotient.isUnit_mk_iff, sup_bot_eq, span_singleton_eq_top]
      refine ⟨fun h ↦ isUnit_of_dvd_unit ?_ h, fun h ↦ ?_⟩
      · rw [TauCeti.stickelbergerProduct_def]
        have hdvd := Finset.dvd_prod_of_mem
          (fun σ : Gal(K/ℚ) ↦ (σ⁻¹ • α) ^ (galEquivZMod m K σ : ZMod m).val)
          (Finset.mem_univ (1 : Gal(K/ℚ)))
        have : Fact (1 < m) := ⟨by omega⟩
        simpa [ZMod.val_one] using hdvd
      · rw [TauCeti.stickelbergerProduct_def]
        exact Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun σ _ ↦
          (h.map (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ⁻¹)).pow _
    by_cases hu : IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) α)
    · rw [MulChar.one_apply (hunit.mpr hu), MulChar.one_apply hu]
    · rw [MulChar.map_nonunit _ (hunit.not.mpr hu), MulChar.map_nonunit _ hu]
  | h₂ B hB =>
    rw [isUnit_iff.mp hB, absNorm_top, Nat.cast_one, span_singleton_one,
      powerResidueSymbolIdeal_top, powerResidueSymbolIdeal_top]
  | h₃ B P hB₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    have hNP₀ : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, span_singleton_eq_bot, Nat.cast_eq_zero, absNorm_eq_zero_iff]
      exact hP.ne_zero
    have hNB₀ : span {(absNorm B : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, span_singleton_eq_bot, Nat.cast_eq_zero, absNorm_eq_zero_iff]
      exact hB₀
    rw [powerResidueSymbolIdeal_mul_right hP.ne_zero hB₀, map_mul, Nat.cast_mul,
      ← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hNP₀ hNB₀,
      powerResidueSymbolIdeal_stickelbergerProduct_of_isMaximal hm P α, ih]

end Ideal

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- Eisenstein reciprocity at the norm of a maximal ideal `P` whose norm is prime to `p` and to
`N((α))`. -/
private theorem eisenstein_reciprocity_absNorm_of_isMaximal (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hPp : (absNorm P).Coprime p) (hαP : (absNorm (span {α})).Coprime (absNorm P)) :
    powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm P : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  rw [← powerResidueSymbolIdeal_stickelbergerProduct hp.two_le P α,
    ← powerResidueSymbol_stickelbergerPhi (span {α}) P hPp hαP hp.two_le,
    powerResidueSymbolIdeal_of_isMaximal]
  rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with h | h
  · rw [h]
  · rw [h, map_neg, ← powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_neg hp_odd,
      powerResidueSymbolIdeal_of_isMaximal]

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` primary with respect to a primitive `p`-th root of unity, and `B` an ideal of `𝓞 K`
whose norm is prime to `p`. Then `(α / N(B))_p = (N(B) / α)_p`, the symbols being taken at the
principal ideals `N(B) 𝓞 K` and `α 𝓞 K`. No coprimality between `α` and `N(B)` is assumed: when
they are not coprime, both sides vanish. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {B : Ideal (𝓞 K)}
    (hB : (absNorm B).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm B : 𝓞 K)) := by
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm B : 𝓞 K)})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]
  have hN : (absNorm (span {α})).Coprime (absNorm B) :=
    absNorm_coprime_of_isCoprime_span_natCast hcop
  clear hcop
  induction B using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at hB
    exact absurd hB (Fact.out : p.Prime).ne_one
  | h₂ B hBu =>
    rw [isUnit_iff.mp hBu, absNorm_top, Nat.cast_one, span_singleton_one,
      powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
  | h₃ B P hB₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at hB
    rw [map_mul, Nat.coprime_mul_iff_right] at hN
    have hNP₀ : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, span_singleton_eq_bot, Nat.cast_eq_zero, absNorm_eq_zero_iff]
      exact hP.ne_zero
    have hNB₀ : span {(absNorm B : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, span_singleton_eq_bot, Nat.cast_eq_zero, absNorm_eq_zero_iff]
      exact hB₀
    rw [map_mul, Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hNP₀ hNB₀, map_mul, map_mul,
      hζ.eisenstein_reciprocity_absNorm_of_isMaximal hp2 hα P hB.1 hN.1, ih hB.2 hN.2]

/-- Eisenstein reciprocity between a primary element `α` and a rational prime `q ≠ p` coprime to
`α`. -/
private theorem eisenstein_reciprocity_prime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hqp : ¬ p ∣ q)
    (hcop : IsCoprime (span {α}) (span {(q : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have := Fact.mk hq
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  -- Pick a maximal ideal `P` of `𝓞 K` lying above `(q : ℤ)`, with `N(P) = q ^ f`.
  have : (span {(q : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  obtain ⟨P, hPmax, hPover⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral (span {(q : ℤ)}) (S := 𝓞 K)
  set f := P.inertiaDeg ℤ
  have hNP : q ^ f = absNorm P := pow_inertiaDeg q P
  -- `N(P) = q ^ f` is prime to `p`, so ideal-norm reciprocity gives
  -- `(α / q)_p ^ f = (q / α)_p ^ f`.
  have hPcop : (absNorm P).Coprime p :=
    hNP ▸ ((hp.coprime_iff_not_dvd.mpr hqp).symm).pow_left f
  have hrec := hζ.eisenstein_reciprocity_absNorm hp2 hα hPcop
  rw [← hNP, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right,
    map_pow, map_pow] at hrec
  -- The residue degree `f` divides `[K : ℚ] = p - 1`, hence is coprime to `p`.
  have hfdvd : f ∣ p - 1 := by
    have hcard := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (span {(q : ℤ)}) (𝓞 K) Gal(K/ℚ)
    rw [inertiaDegIn_eq_inertiaDeg (span {(q : ℤ)}) P Gal(K/ℚ),
      IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank p K,
      Nat.totient_prime hp] at hcard
    exact ⟨((span {(q : ℤ)}).primesOver (𝓞 K)).ncard * (span {(q : ℤ)}).ramificationIdxIn (𝓞 K),
      by rw [← hcard]; ring⟩
  have hfp : f.Coprime p := by
    have hfpos : 0 < f := inertiaDeg_pos P ℤ
    have hp2' : 2 ≤ p := hp.two_le
    have hflt : f < p := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hfdvd) (by omega)
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hfpos hflt)).symm
  -- Both symbols are `p`-th roots of unity, so cancelling the `f`-th power yields equality.
  have hx : powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) ^ p = 1 :=
    powerResidueSymbolIdeal_pow_eq_one
      (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop))
  have hy : powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) ^ p = 1 :=
    powerResidueSymbolIdeal_pow_eq_one
      (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop.symm))
  obtain ⟨k, -, hfk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hfp hp.one_lt
  have hpow {z : 𝓞 K} (hz : z ^ p = 1) : (z ^ f) ^ k = z := by
    rw [← pow_mul, ← Nat.div_add_mod (f * k) p, hfk, pow_add, pow_mul, hz, one_pow, one_mul,
      pow_one]
  rw [← hpow hx, hrec, hpow hy]

/-- **The Eisenstein reciprocity law for natural numbers.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` primary with respect to a primitive `p`-th root of unity, and `n : ℕ` not divisible by
`p`. Then `(α / n)_p = (n / α)_p`, the symbols being taken at the principal ideals `n 𝓞 K` and
`α 𝓞 K`. If `n` and `α` are not coprime, both sides vanish. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  by_cases hcop : IsCoprime (span {α}) (span {(n : 𝓞 K)})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]
  induction n using induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hu =>
    rw [Nat.isUnit_iff.mp hu, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ n q hn₀ hq ih =>
    have hqp : q.Prime := Nat.prime_iff.mpr hq
    have hqndvd : ¬ p ∣ q := fun h ↦ hn (dvd_mul_of_dvd_left h n)
    have hnndvd : ¬ p ∣ n := fun h ↦ hn (dvd_mul_of_dvd_right h q)
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton, IsCoprime.mul_right_iff] at hcop
    have hq₀ : span {(q : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, span_singleton_eq_bot, Nat.cast_eq_zero]
      exact hqp.ne_zero
    have hn₀' : span {(n : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, span_singleton_eq_bot, Nat.cast_eq_zero]
      exact hn₀
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hq₀ hn₀', map_mul, map_mul,
      hζ.eisenstein_reciprocity_prime hp2 hα hqp hqndvd hcop.1, ih hnndvd hcop.2]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, `α ∈ 𝓞 K` primary
with respect to a primitive `p`-th root of unity, and `a : ℤ` not divisible by `p`. Then
`(α / a)_p = (a / α)_p`, the `p`-th power residue symbols being taken at the principal ideals
`a 𝓞 K` and `α 𝓞 K`. Neither `α` being a nonunit, nor `a ≠ ±1`, nor coprimality of `a` and `α` is
needed: if `a` and `α` are not coprime, both sides vanish. -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hnat : ¬ p ∣ a.natAbs := fun h ↦ ha (Int.natCast_dvd.mpr h)
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hnat
  · rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg, map_neg,
      powerResidueSymbolIdeal_neg hp_odd]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hnat

end IsPrimitiveRoot

section Examples

variable {K : Type*} [Field K] [NumberField K]

/- For `p = 3` and any primary element `α` of `ℤ[ω]`, ideal-norm reciprocity at the inert ideal
`(2)` (of norm `4`) gives `(α / 4)_3 = (4 / α)_3`. -/
example [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    powerResidueSymbolIdeal (span {(4 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ (4 : 𝓞 K)) := by
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := by
    rw [← Nat.cast_ofNat (R := 𝓞 K), absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.Rat.finrank 3 K]
    decide
  have hrec := hζ.eisenstein_reciprocity_absNorm (by decide) hα (B := span {(2 : 𝓞 K)})
    (by rw [hN2]; decide)
  rw [hN2, Nat.cast_ofNat] at hrec
  exact hrec

/- For `p = 3` and the primary prime `α = -1 - 3ω` of `ℤ[ω]`, Eisenstein reciprocity at `a = 2`
recovers cubic reciprocity `(α / 2)_3 = (2 / α)_3`. -/
example [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    let α : 𝓞 K := -1 - 3 * hζ.toInteger
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  have h3 : (hζ.toInteger - 1) ^ 2 ∣ (3 : 𝓞 K) := by
    simpa using (hζ.toInteger_sub_one_sq_dvd_intCast_iff (by decide)).mpr (dvd_refl (3 : ℤ))
  have hα : TauCeti.IsEisensteinPrimary hζ.toInteger (-1 - 3 * hζ.toInteger) := by
    rw [TauCeti.isEisensteinPrimary_iff, hζ.isCoprime_toInteger_sub_one_iff]
    refine ⟨fun hd ↦ ?_, -4, ?_⟩
    · have h4 : hζ.toInteger - 1 ∣ ((-4 : ℤ) : 𝓞 K) := by
        have h' := dvd_add hd (dvd_mul_left (hζ.toInteger - 1) 3)
        convert h' using 1
        push_cast
        ring
      have := (zeta_sub_one_dvd_intCast_iff' 3 hζ).mp h4
      omega
    · convert h3.mul_right (1 - hζ.toInteger) using 1
      push_cast
      ring
  have hrec := hζ.eisenstein_reciprocity (by decide) hα (a := 2) (by decide)
  rw [Int.cast_ofNat] at hrec
  exact hrec

/- The hypothesis `a ≠ ±1` is not needed: at `a = -1`, Eisenstein reciprocity applies and both
symbols equal `1`. -/
example {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp2 : p ≠ 2) {α : 𝓞 K} (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K)}) p (Ideal.Quotient.mk _ α) = 1 ∧
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ ((-1 : ℤ) : 𝓞 K)) = 1 := by
  have hrec := hζ.eisenstein_reciprocity hp2 hα (a := -1) fun h ↦ by
    have : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) (dvd_neg.mp h)
    exact (Fact.out : p.Prime).ne_one this
  have h1 : powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K)}) p (Ideal.Quotient.mk _ α) = 1 := by
    rw [Int.cast_neg, Int.cast_one, span_singleton_neg, span_singleton_one,
      powerResidueSymbolIdeal_top]
  exact ⟨h1, hrec.symm.trans h1⟩

/- The primary hypothesis cannot be dropped: for `p = 3`, the primitive cube root `ζ` is not
primary (`hζ.not_isEisensteinPrimary_toInteger`), and `(ζ / 2)_3 = ζ ≠ 1 = (2 / ζ)_3`. -/
example [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ hζ.toInteger) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := by
    rw [← Nat.cast_ofNat (R := 𝓞 K), absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.Rat.finrank 3 K]
    decide
  have hu : IsUnit hζ.toInteger := hζ.toInteger_isPrimitiveRoot.isUnit (by decide)
  rw [span_singleton_eq_top.mpr hu, powerResidueSymbolIdeal_top,
    powerResidueSymbolIdeal_mk_of_pow_eq_one (by rw [hN2]; decide)
      hζ.toInteger_isPrimitiveRoot.pow_eq_one, hN2]
  simpa using hζ.toInteger_isPrimitiveRoot.ne_one (by decide)

end Examples
