/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coprime linear shifts inside an ideal of a Dedekind domain

Let `R` be a Dedekind domain and `I` a nonzero ideal of `R`. Given coprime `a, b : R`, we can
shift `b` by a multiple `t * a` with `t ∈ I` so that `b + t * a` is nonzero and avoids
`v ^ (multiplicity v I + 1)` at every prime `v` in a prescribed finite set of height-one primes
containing the prime divisors of `I`.

Consequently, when `b ∈ I`, for any nonzero ideal `J` there exists `t ∈ I` such that
`(b + t * a) = I * K` with `K` coprime to `J`, and whenever `0 ≠ J ≤ I` there exists `t ∈ I` with
`(b + t * a) ⊔ J = I`. Unlike Mathlib's `IsDedekindDomain.exists_sup_span_eq` (which chooses an
unconstrained generator of `I` modulo `J`), these lemmas require the generator to lie in the
prescribed arithmetic progression `b + t * a` (`t ∈ I`).

## Main results

* `Ideal.exists_mem_add_mul_notMem_pow_succ`: for a nonzero ideal `I`, a finite set `S` of
  height-one primes containing all prime divisors of `I`, and coprime `a, b`, there exists
  `t ∈ I` such that `b + t * a ≠ 0` and
  `b + t * a ∉ v.asIdeal ^ (multiplicity v.asIdeal I + 1)` for every `v ∈ S`.
* `Ideal.exists_mem_span_add_mul_eq_mul_and_isCoprime`: factoring `(b + t * a) = I * K` with `K`
  coprime to a prescribed nonzero ideal `J`.
* `Ideal.exists_mem_span_add_mul_sup_eq`: for `0 ≠ J ≤ I`, finding `t ∈ I` with `b + t * a ≠ 0`
  and `(b + t * a) ⊔ J = I`.

## References

* H. Bass, J. Milnor, and J.-P. Serre, *Solution of the congruence subgroup problem for `SL_n`
  (`n ≥ 3`) and `Sp_{2n}` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §2, pp. 65–68.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Local step: at a height-one prime `v`, given coprime `a, b` and a natural number `e`, there
exists `t ∈ v ^ e` such that `b + t * a ∉ v ^ (e + 1)`. -/
private theorem exists_local_shift (v : HeightOneSpectrum R) (e : ℕ) {a b : R}
    (hab : IsCoprime a b) :
    ∃ t ∈ v.asIdeal ^ e, b + t * a ∉ v.asIdeal ^ (e + 1) := by
  by_cases hb : b ∈ v.asIdeal ^ (e + 1)
  · obtain ⟨π, hπ_mem, hπ_not⟩ := IsConcreteLE.exists_of_lt (Ideal.pow_succ_lt_pow v.ne_bot e)
    have ha_not : a ∉ v.asIdeal := by
      intro ha
      have hb_mem : b ∈ v.asIdeal := Ideal.pow_le_self (Nat.succ_ne_zero e) hb
      obtain ⟨x, y, hxy⟩ := hab
      have h1 : (1 : R) ∈ v.asIdeal :=
        hxy ▸ add_mem (mul_mem_left _ x ha) (mul_mem_left _ y hb_mem)
      exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    refine ⟨π, hπ_mem, fun hmem ↦ hπ_not ?_⟩
    have hπa : π * a ∈ v.asIdeal ^ (e + 1) := by
      simpa only [add_sub_cancel_left] using sub_mem hmem hb
    have hcop_v : IsCoprime v.asIdeal (Ideal.span {a}) := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have heq : v.asIdeal = v.asIdeal ⊔ Ideal.span {a} :=
        v.isMaximal.eq_of_le hne le_sup_left
      exact ha_not (heq ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self a))
    have hcop_pow : IsCoprime (v.asIdeal ^ (e + 1)) (Ideal.span {a}) := hcop_v.pow_left
    obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp hcop_pow
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
    have hπ_eq : π = π * x + r * (π * a) := by
      calc
        π = π * (x + a * r) := by rw [hxy, mul_one]
        _ = π * x + r * (π * a) := by ring
    rw [hπ_eq]
    exact add_mem (mul_mem_left _ π hx) (mul_mem_left _ r hπa)
  · exact ⟨0, zero_mem _, by simpa using hb⟩

/-- Empty-prime-set base case for `exists_mem_add_mul_notMem_pow_succ`: if no height-one prime
divides `I`, then `I = ⊤`, and `t = 0` or `t = 1` makes `b + t * a ≠ 0`. -/
private theorem exists_mem_add_mul_of_no_prime_dvd (I : Ideal R) (hI : I ≠ ⊥)
    (hno : ∀ v : HeightOneSpectrum R, ¬ v.asIdeal ∣ I) {a b : R} (hab : IsCoprime a b) :
    ∃ t ∈ I, b + t * a ≠ 0 := by
  have hI_top : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM_max, hIM⟩ := Ideal.exists_le_maximal I hne
    have hM_ne : M ≠ ⊥ := fun hbot ↦ hI (le_bot_iff.mp (hbot ▸ hIM))
    exact hno ⟨M, hM_max.isPrime, hM_ne⟩ (Ideal.dvd_iff_le.mpr hIM)
  by_cases hb0 : b = 0
  · subst hb0
    have ha0 : a ≠ 0 := by
      obtain ⟨x, y, hxy⟩ := hab
      intro ha
      simp [ha] at hxy
    exact ⟨1, hI_top ▸ Submodule.mem_top, by simpa using ha0⟩
  · exact ⟨0, zero_mem I, by simpa using hb0⟩

/-- For a nonzero ideal `I` of a Dedekind domain `R`, a finite set `S` of height-one primes
containing every prime divisor of `I`, and coprime `a, b : R`, there exists `t ∈ I` such that
`b + t * a ≠ 0` and `b + t * a ∉ v ^ (multiplicity v I + 1)` for every `v ∈ S`. -/
theorem exists_mem_add_mul_notMem_pow_succ (I : Ideal R) (hI : I ≠ ⊥)
    (S : Finset (HeightOneSpectrum R))
    (hIS : ∀ v : HeightOneSpectrum R, v.asIdeal ∣ I → v ∈ S)
    {a b : R} (hab : IsCoprime a b) :
    ∃ t ∈ I, b + t * a ≠ 0 ∧ ∀ v ∈ S, b + t * a ∉ v.asIdeal ^ (multiplicity v.asIdeal I + 1) := by
  classical
  by_cases hS : S = ∅
  · subst hS
    obtain ⟨t, htI, hne0⟩ := exists_mem_add_mul_of_no_prime_dvd I hI
      (fun v hv ↦ Finset.notMem_empty v (hIS v hv)) hab
    exact ⟨t, htI, hne0, fun _ hv ↦ (Finset.notMem_empty _ hv).elim⟩
  · choose loc hloc_mem hloc_not using
      fun v : S ↦ exists_local_shift v.1 (multiplicity v.1.asIdeal I) hab
    let J : S → Ideal R := fun v ↦ v.1.asIdeal ^ (multiplicity v.1.asIdeal I + 1)
    have hpair : Pairwise (Function.onFun IsCoprime J) := fun v w hvw ↦
      HeightOneSpectrum.isCoprime_pow_of_ne v.1 w.1 (Subtype.coe_ne_coe.mpr hvw) _ _
    obtain ⟨qt, hqt⟩ := Ideal.quotientInfToPiQuotient_surj hpair
      (fun v : S ↦ Ideal.Quotient.mk (J v) (loc v))
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective qt
    have hcong : ∀ v : S, t - loc v ∈ J v := by
      intro v
      have hv := congr_fun hqt v
      rw [Ideal.quotientInfToPiQuotient_mk'] at hv
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem t (loc v)).mp hv
    have htI : t ∈ I := by
      rw [← Ideal.iInf_maxPowDividing_eq hI, Submodule.mem_iInf]
      intro v
      by_cases hv : v.asIdeal ∣ I
      · have hvS : v ∈ S := hIS v hv
        rw [v.maxPowDividing_eq_pow_multiplicity hI]
        have hsub : t - loc ⟨v, hvS⟩ ∈ v.asIdeal ^ multiplicity v.asIdeal I :=
          Ideal.pow_le_pow_right (Nat.le_succ _) (hcong ⟨v, hvS⟩)
        have hsum := add_mem (hloc_mem ⟨v, hvS⟩) hsub
        rwa [add_sub_cancel] at hsum
      · have hcount : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
          by_contra hc
          exact hv ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc)
        rw [maxPowDividing, hcount, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    have hnot : ∀ v ∈ S, b + t * a ∉ v.asIdeal ^ (multiplicity v.asIdeal I + 1) := by
      intro v hvS hmem
      have hdiff : (t - loc ⟨v, hvS⟩) * a ∈ v.asIdeal ^ (multiplicity v.asIdeal I + 1) :=
        mul_mem_right a _ (hcong ⟨v, hvS⟩)
      apply hloc_not ⟨v, hvS⟩
      have heq : b + loc ⟨v, hvS⟩ * a = (b + t * a) - (t - loc ⟨v, hvS⟩) * a := by ring
      rw [heq]
      exact sub_mem hmem hdiff
    obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact ⟨t, htI, fun h0 ↦ hnot v₀ hv₀ (h0 ▸ zero_mem _), hnot⟩

/-- For nonzero ideals `I` and `J` of a Dedekind domain `R` and coprime `a, b : R` with `b ∈ I`,
there exist `t ∈ I` and an ideal `K` such that `b + t * a ≠ 0`, `Ideal.span {b + t * a} = I * K`,
and `IsCoprime K J`. -/
theorem exists_mem_span_add_mul_eq_mul_and_isCoprime (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    {a b : R} (hb : b ∈ I) (hab : IsCoprime a b) :
    ∃ t ∈ I, ∃ K : Ideal R, b + t * a ≠ 0 ∧ Ideal.span {b + t * a} = I * K ∧ IsCoprime K J := by
  classical
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  let S : Finset (HeightOneSpectrum R) := (Ideal.finite_factors hIJ).toFinset
  have hIS : ∀ v : HeightOneSpectrum R, v.asIdeal ∣ I → v ∈ S := by
    intro v hv
    exact (Ideal.finite_factors hIJ).mem_toFinset.mpr (dvd_mul_of_dvd_left hv J)
  obtain ⟨t, htI, hne0, hnot⟩ := exists_mem_add_mul_notMem_pow_succ I hI S hIS hab
  have hmemI : b + t * a ∈ I := add_mem hb (mul_mem_right a I htI)
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_iff_mem I |>.mpr hmemI)
  refine ⟨t, htI, K, hne0, hK, ?_⟩
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  obtain ⟨M, hM_max, hKM⟩ := Ideal.exists_le_maximal (K ⊔ J) htop
  have hJM : J ≤ M := le_sup_right.trans hKM
  have hKM' : K ≤ M := le_sup_left.trans hKM
  have hM_ne : M ≠ ⊥ := fun hbot ↦ hJ (le_bot_iff.mp (hbot ▸ hJM))
  let v : HeightOneSpectrum R := ⟨M, hM_max.isPrime, hM_ne⟩
  have hvS : v ∈ S := (Ideal.finite_factors hIJ).mem_toFinset.mpr
    (dvd_mul_of_dvd_right (Ideal.dvd_iff_le.mpr hJM) I)
  have hpow : v.asIdeal ^ multiplicity v.asIdeal I ∣ I := by
    rw [← v.maxPowDividing_eq_pow_multiplicity hI]
    exact Ideal.dvd_iff_le.mpr
      ((Ideal.iInf_maxPowDividing_eq hI).ge.trans
        (iInf_le (fun w : HeightOneSpectrum R ↦ w.maxPowDividing I) v))
  have hpow_succ : v.asIdeal ^ (multiplicity v.asIdeal I + 1) ∣ Ideal.span {b + t * a} := by
    rw [pow_succ, hK]
    exact mul_dvd_mul hpow (Ideal.dvd_iff_le.mpr hKM')
  exact hnot v hvS ((Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp hpow_succ))

/-- For nonzero ideals `J ≤ I` of a Dedekind domain `R` and coprime `a, b : R` with `b ∈ I`, there
exists `t ∈ I` such that `b + t * a ≠ 0` and `Ideal.span {b + t * a} ⊔ J = I`. -/
theorem exists_mem_span_add_mul_sup_eq (I J : Ideal R) (hJ : J ≠ ⊥) (hJI : J ≤ I)
    {a b : R} (hb : b ∈ I) (hab : IsCoprime a b) :
    ∃ t ∈ I, b + t * a ≠ 0 ∧ Ideal.span {b + t * a} ⊔ J = I := by
  have hI : I ≠ ⊥ := fun hbot ↦ hJ (le_bot_iff.mp (hbot ▸ hJI))
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr hJI
  have hJ'_ne : J' ≠ ⊥ := fun hbot ↦ hJ (by simp [hJ', hbot])
  obtain ⟨t, htI, K, hne0, hK, hcop⟩ :=
    exists_mem_span_add_mul_eq_mul_and_isCoprime I J' hI hJ'_ne hb hab
  refine ⟨t, htI, hne0, ?_⟩
  rw [hK, hJ', ← Ideal.mul_sup, hcop.sup_eq, Ideal.mul_top]

end Ideal
