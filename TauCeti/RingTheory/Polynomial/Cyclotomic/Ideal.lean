/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Prime-power cyclotomic congruences, two-order ideals, and root separation

For a prime `p`, a positive exponent `e`, and an order `n`, the cyclotomic polynomials `Φ_n` and
`Φ_{p ^ e n}` fail to be coprime over `ℤ`: in characteristic `p` the higher polynomial collapses to
a power of the lower one,
`Φ_{p ^ e n} = Φ_n ^ (φ(p ^ e n) / φ(n))`,
so over any commutative ring `R` the difference `Φ_{p ^ e n} - Φ_n ^ (φ(p ^ e n) / φ(n))` is a
multiple of `p`. Conversely, evaluating `Φ_{p ^ e}(1) = p` along `X ↦ X ^ n` shows that `p` itself
lies in the two-generator ideal `(Φ_n, Φ_{p ^ e n})`. Together these two divisibilities identify the
two-order cyclotomic ideal completely:
`(Φ_n, Φ_{p ^ e n}) = (p, Φ_n)` in `R[X]`.

Contracting this ideal to scalar polynomials gives `(p) ⊆ R` whenever `n ≥ 1` (whereas `(Φ_n)`
alone contracts to `⊥`), and the quotient `R[X] ⧸ (Φ_n, Φ_{p ^ e n})` is canonically `R`-algebra
isomorphic to `AdjoinRoot (cyclotomic n (R ⧸ (p)))` — over `ℤ`, to `(ℤ/pℤ)[X] ⧸ (Φ_n)`. In
Habiro's theory of cyclotomic completions `R⟦X - 1⟧_S`, this identification explains how adjacent
orders `n` and `p ^ e n` paste modulo `p` to force `p`-adic continuity of Taylor expansions at
roots of unity (Habiro 2004, Lemma 4.1).

Complementing the ideal side, evaluating `Φ_d` at `1` separates roots of unity by whether their
order ratio `d` is a prime power:

* when `d` is not a prime power, `Φ_d(1) = 1`, so `1 - ω` is a unit in `R` at every root `ω` of
  `Φ_d`, and in any nontrivial `I`-adically Hausdorff ring no power `(1 - ω) ^ m` can lie in `I`;
* when `d = p ^ (k + 1)` is a prime power, `ω - 1` divides `p` at every root `ω` of `Φ_d`, and
  more generally `p ∣ (ω - 1) ^ p ^ e` whenever `ω ^ p ^ e = 1`, making `ω - 1` topologically
  nilpotent in the `(p)`-adic topology.

## Main results

* `Polynomial.cyclotomic_mul_dvd_expand`: `Φ_{d n}(X) ∣ Φ_d(X ^ n)` for all `d, n : ℕ`.
* `Polynomial.cyclotomic_prime_pow_mul_eq_pow`: in characteristic `p`,
  `Φ_{p ^ e n} = Φ_n ^ (φ(p ^ e n) / φ(n))`.
* `Polynomial.natCast_dvd_cyclotomic_prime_pow_mul_sub_pow`: over any commutative ring,
  `p ∣ Φ_{p ^ e n} - Φ_n ^ (φ(p ^ e n) / φ(n))`.
* `Polynomial.natCast_mem_span_cyclotomic_prime_pow_mul`: `p ∈ (Φ_n, Φ_{p ^ e n})` for `e ≥ 1`.
* `Polynomial.span_cyclotomic_prime_pow_mul`: `(Φ_n, Φ_{p ^ e n}) = (p, Φ_n)` for `e ≥ 1`.
* `Polynomial.comap_C_span_cyclotomic_prime_pow_mul`: `(Φ_n, Φ_{p ^ e n}) ∩ R = (p)` for
  `e ≥ 1` and `n ≥ 1`.
* `Polynomial.quotientSpanCyclotomicPrimePowMulAlgEquiv`,
  `Polynomial.quotientSpanCyclotomicPrimePowMulIntEquiv`:
  `R[X] ⧸ (Φ_n, Φ_{p ^ e n}) ≃ₐ[R] AdjoinRoot (Φ_n (R ⧸ (p)))` and its `ZMod p` specialization
  over `ℤ`.
* `Polynomial.isUnit_one_sub_of_isRoot_cyclotomic_not_prime_pow`,
  `Polynomial.notMem_of_isHausdorff_of_isRoot_cyclotomic_not_prime_pow`: `1 - ω` is a unit at
  every root `ω` of `Φ_d` for non-prime-power `d`, so `(1 - ω) ^ m ∉ I` in any nontrivial
  `I`-adically Hausdorff ring.
* `Polynomial.sub_one_dvd_natCast_of_isRoot_cyclotomic_prime_pow`,
  `Nat.Prime.natCast_dvd_sub_one_pow_of_pow_eq_one`: at prime-power roots of unity, `ω - 1 ∣ p`
  and `p ∣ (ω - 1) ^ p ^ e`.

## References

* [K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. 40 (2004),
  1127–1146], §3 and Lemma 4.1.
* [E. Wagner, *Habiro rings and Bigalois objects*, arXiv:2507.18527 (2025)], Lemma 2.1.
-/

public section

namespace Polynomial

section ExpandDvd

/-- **`Φ_{d n}(X)` divides `Φ_d(X ^ n)`** over any commutative ring and for all `d, n : ℕ`.
At `d = 0` or `n = 0` the left-hand side degenerates to `Φ_0 = 1`. -/
theorem cyclotomic_mul_dvd_expand {R : Type*} [CommRing R] (d n : ℕ) :
    cyclotomic (d * n) R ∣ expand R n (cyclotomic d R) := by
  induction n using Nat.strong_induction_on generalizing d with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rcases eq_or_ne n 1 with rfl | hn1
    · simp
    set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    obtain ⟨m, hm⟩ : p ∣ n := Nat.minFac_dvd n
    have hm_pos : 0 < m := Nat.pos_of_ne_zero fun hm0 ↦ hn0 (by simp [hm, hm0])
    have hm_lt : m < n := by
      rw [hm]
      exact lt_mul_of_one_lt_left hm_pos hp.one_lt
    rw [hm, ← mul_assoc, mul_comm p m, expand_mul]
    have hstep : cyclotomic (d * p) R ∣ expand R p (cyclotomic d R) := by
      by_cases hpd : p ∣ d
      · rw [cyclotomic_expand_eq_cyclotomic hp hpd R]
      · rw [cyclotomic_expand_eq_cyclotomic_mul hp hpd R]
        exact dvd_mul_right _ _
    exact (ih m hm_lt (d * p)).trans (_root_.map_dvd (expand R m) hstep)

/-- Symmetric multiplication-order form of `Polynomial.cyclotomic_mul_dvd_expand`:
`Φ_{n d}(X) ∣ Φ_d(X ^ n)`. -/
theorem cyclotomic_mul_dvd_expand' {R : Type*} [CommRing R] (d n : ℕ) :
    cyclotomic (n * d) R ∣ expand R n (cyclotomic d R) := by
  rw [mul_comm]
  exact cyclotomic_mul_dvd_expand d n

end ExpandDvd

section CharP

/-- In characteristic `p`, if `p ∣ n`, then `Φ_{p ^ e n} = Φ_n ^ p ^ e` for every `e : ℕ`.
This is the `p ∣ n` counterpart of `Polynomial.cyclotomic_mul_prime_pow_eq`. -/
theorem cyclotomic_prime_pow_mul_eq_pow_of_dvd (R : Type*) [Ring R] {p : ℕ} [Fact p.Prime]
    [CharP R p] {n : ℕ} (hn : p ∣ n) (e : ℕ) :
    cyclotomic (p ^ e * n) R = cyclotomic n R ^ p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hdvd : p ∣ p ^ e * n := dvd_mul_of_dvd_right hn (p ^ e)
    rw [pow_succ', mul_assoc, mul_comm p (p ^ e * n), cyclotomic_mul_prime_dvd_eq_pow R hdvd, ih,
      ← pow_mul, mul_comm (p ^ e) p]

private theorem totient_prime_pow_mul_div {p : ℕ} (hp : p.Prime) (e n : ℕ) :
    (p ^ e * n).totient / n.totient =
      if n = 0 then 0 else if e = 0 then 1 else if p ∣ n then p ^ e else p ^ e - p ^ (e - 1) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hφn : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
  rcases eq_or_ne e 0 with rfl | he0
  · simp [hn0, Nat.div_self hφn]
  simp only [hn0, he0, ↓reduceIte]
  by_cases hpn : p ∣ n
  · rw [ite_eq_left hpn]
    have htot : ∀ k : ℕ, (p ^ k * n).totient = p ^ k * n.totient := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_assoc, Nat.totient_mul_of_dvd (dvd_mul_of_dvd_right hpn _), ih,
          ← mul_assoc]
    rw [htot e, Nat.mul_div_cancel _ hφn]
  · rw [ite_eq_right hpn]
    have hcop : (p ^ e).Coprime n := (hp.coprime_iff_not_dvd.mpr hpn).pow_left e
    rw [Nat.totient_mul hcop, Nat.mul_div_cancel _ hφn,
      Nat.totient_prime_pow hp (Nat.pos_of_ne_zero he0), Nat.mul_sub_left_distrib, mul_one,
      ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero he0)]

/-- **Unified characteristic-`p` power law for cyclotomic polynomials.** Over any ring of prime
characteristic `p` and for all `e, n : ℕ`,
`Φ_{p ^ e n} = Φ_n ^ (φ(p ^ e n) / φ(n))`.
This unifies `Polynomial.cyclotomic_mul_prime_pow_eq` (`p ∤ n`, exponent `p ^ e - p ^ (e - 1)`)
and `Polynomial.cyclotomic_prime_pow_mul_eq_pow_of_dvd` (`p ∣ n`, exponent `p ^ e`), while also
covering the degenerate cases `e = 0` and `n = 0`. -/
theorem cyclotomic_prime_pow_mul_eq_pow (R : Type*) [Ring R] {p : ℕ} [hp : Fact p.Prime]
    [CharP R p] (e n : ℕ) :
    cyclotomic (p ^ e * n) R = cyclotomic n R ^ ((p ^ e * n).totient / n.totient) := by
  rw [totient_prime_pow_mul_div hp.out e n]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne e 0 with rfl | he0
  · simp [hn0]
  simp only [hn0, he0, ↓reduceIte]
  by_cases hpn : p ∣ n
  · rw [ite_eq_left hpn, cyclotomic_prime_pow_mul_eq_pow_of_dvd R hpn e]
  · rw [ite_eq_right hpn, cyclotomic_mul_prime_pow_eq R hpn (Nat.pos_of_ne_zero he0)]

end CharP

section CongruenceAndIdeal

variable {R : Type*} [CommRing R]

/-- **Prime-power cyclotomic congruence modulo `p`.** Over any commutative ring `R`, for any prime
`p` and all `e, n : ℕ`, `p` divides `Φ_{p ^ e n} - Φ_n ^ (φ(p ^ e n) / φ(n))` in `R[X]`. -/
theorem natCast_dvd_cyclotomic_prime_pow_mul_sub_pow {p : ℕ} (hp : p.Prime) (e n : ℕ) :
    (p : R[X]) ∣ cyclotomic (p ^ e * n) R - cyclotomic n R ^ ((p ^ e * n).totient / n.totient) := by
  have : Fact p.Prime := ⟨hp⟩
  suffices hZ : (p : ℤ[X]) ∣
      cyclotomic (p ^ e * n) ℤ - cyclotomic n ℤ ^ ((p ^ e * n).totient / n.totient) by
    simpa using _root_.map_dvd (mapRingHom (Int.castRingHom R)) hZ
  rw [← C_eq_natCast, C_dvd_iff_dvd_coeff]
  intro i
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod p))
      ((cyclotomic (p ^ e * n) ℤ -
        cyclotomic n ℤ ^ ((p ^ e * n).totient / n.totient)).coeff i) = 0
  rw [← coeff_map, Polynomial.map_sub, Polynomial.map_pow, map_cyclotomic_int, map_cyclotomic_int,
    cyclotomic_prime_pow_mul_eq_pow (ZMod p) e n, sub_self, coeff_zero]

/-- Explicit-exponent form of `Polynomial.natCast_dvd_cyclotomic_prime_pow_mul_sub_pow` when
`¬ p ∣ n` and `0 < e`: `p` divides `Φ_{p ^ e n} - Φ_n ^ (p ^ e - p ^ (e - 1))`. -/
theorem natCast_dvd_cyclotomic_prime_pow_mul_sub_pow_of_not_dvd {p e n : ℕ} (hp : p.Prime)
    (he : 0 < e) (hpn : ¬ p ∣ n) :
    (p : R[X]) ∣ cyclotomic (p ^ e * n) R - cyclotomic n R ^ (p ^ e - p ^ (e - 1)) := by
  have hn0 : n ≠ 0 := fun h ↦ hpn (h ▸ dvd_zero p)
  have h := natCast_dvd_cyclotomic_prime_pow_mul_sub_pow (R := R) hp e n
  rwa [totient_prime_pow_mul_div hp e n, ite_eq_right hn0, ite_eq_right he.ne',
    ite_eq_right hpn] at h

/-- Explicit-exponent form of `Polynomial.natCast_dvd_cyclotomic_prime_pow_mul_sub_pow` when
`p ∣ n`: `p` divides `Φ_{p ^ e n} - Φ_n ^ p ^ e`. -/
theorem natCast_dvd_cyclotomic_prime_pow_mul_sub_pow_of_dvd {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hpn : p ∣ n) (e : ℕ) :
    (p : R[X]) ∣ cyclotomic (p ^ e * n) R - cyclotomic n R ^ p ^ e := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne e 0 with rfl | he0
  · simp
  have h := natCast_dvd_cyclotomic_prime_pow_mul_sub_pow (R := R) hp e n
  rwa [totient_prime_pow_mul_div hp e n, ite_eq_right hn0, ite_eq_right he0,
    ite_eq_left hpn] at h

/-- **`p` lies in the two-order cyclotomic ideal `(Φ_n, Φ_{p ^ e n})`** whenever `p` is prime and
`0 < e`. The hypothesis `0 < e` is sharp: for `e = 0` and `n ≥ 1`, `(Φ_n)` contracts to `⊥` in `R`
(see `Polynomial.comap_C_span_cyclotomic`). -/
theorem natCast_mem_span_cyclotomic_prime_pow_mul {p e : ℕ} (hp : p.Prime) (he : 0 < e) (n : ℕ) :
    (p : R[X]) ∈ Ideal.span {cyclotomic n R, cyclotomic (p ^ e * n) R} := by
  rcases eq_or_ne n 0 with rfl | _
  · rw [mul_zero, cyclotomic_zero, Ideal.span_insert, Ideal.span_singleton_one, sup_top_eq]
    trivial
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  have : Fact p.Prime := ⟨hp⟩
  have hdvd₁ : X - 1 ∣ cyclotomic (p ^ (k + 1)) R - (p : R[X]) := by
    have hroot : IsRoot (cyclotomic (p ^ (k + 1)) R - (p : R[X])) 1 := by
      rw [IsRoot.def, eval_sub, eval_one_cyclotomic_prime_pow, eval_natCast, sub_self]
    simpa using dvd_iff_isRoot.mpr hroot
  have hdvd₂ : cyclotomic n R ∣ expand R n (cyclotomic (p ^ (k + 1)) R) - (p : R[X]) := by
    refine (cyclotomic.dvd_X_pow_sub_one n R).trans ?_
    simpa [map_sub] using _root_.map_dvd (expand R n) hdvd₁
  have hdvd₃ : cyclotomic (p ^ (k + 1) * n) R ∣ expand R n (cyclotomic (p ^ (k + 1)) R) :=
    cyclotomic_mul_dvd_expand (p ^ (k + 1)) n
  set I := Ideal.span ({cyclotomic n R, cyclotomic (p ^ (k + 1) * n) R} : Set R[X])
  have hmem₂ : expand R n (cyclotomic (p ^ (k + 1)) R) - p ∈ I :=
    Ideal.span_mono (by simp) (Ideal.mem_span_singleton.mpr hdvd₂)
  have hmem₃ : expand R n (cyclotomic (p ^ (k + 1)) R) ∈ I :=
    Ideal.span_mono (by simp) (Ideal.mem_span_singleton.mpr hdvd₃)
  simpa using I.sub_mem hmem₃ hmem₂

/-- **Two-order cyclotomic ideal identity (Habiro 2004, Lemma 4.1).** Over any commutative ring `R`,
for any prime `p`, `0 < e`, and `n : ℕ`,
`(Φ_n, Φ_{p ^ e n}) = (p, Φ_n)` in `R[X]`. -/
theorem span_cyclotomic_prime_pow_mul {p e : ℕ} (hp : p.Prime) (he : 0 < e) (n : ℕ) :
    Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X]) =
      Ideal.span ({(p : R[X]), cyclotomic n R} : Set R[X]) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [Ideal.span_insert, Ideal.span_singleton_one]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · set d := (p ^ e * n).totient / n.totient
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hd_pos : 0 < d := by
        refine Nat.div_pos ?_ (Nat.totient_pos.mpr hn_pos)
        exact Nat.le_of_dvd
          (Nat.totient_pos.mpr (mul_pos (pow_pos hp.pos e) hn_pos))
          (Nat.totient_dvd_of_dvd (dvd_mul_left n (p ^ e)))
      have hsub : cyclotomic (p ^ e * n) R - cyclotomic n R ^ d ∈
          Ideal.span ({(p : R[X]), cyclotomic n R} : Set R[X]) :=
        Ideal.span_mono (by simp)
          (Ideal.mem_span_singleton.mpr (natCast_dvd_cyclotomic_prime_pow_mul_sub_pow hp e n))
      have hpow : cyclotomic n R ^ d ∈
          Ideal.span ({(p : R[X]), cyclotomic n R} : Set R[X]) :=
        Ideal.span_mono (by simp)
          (Ideal.mem_span_singleton.mpr (dvd_pow_self (cyclotomic n R) hd_pos.ne'))
      simpa using add_mem hsub hpow
  · rw [Ideal.span_le]
    rintro f (rfl | rfl)
    · exact natCast_mem_span_cyclotomic_prime_pow_mul hp he n
    · exact Ideal.subset_span (by simp)

/-- For `0 < n`, a single cyclotomic polynomial generates an ideal of `R[X]` intersecting the
constant polynomials `R` in `⊥`. In particular, when `R = ℤ`, no nonzero integer lies in `(Φ_n)`,
showing that `0 < e` is essential in `Polynomial.natCast_mem_span_cyclotomic_prime_pow_mul`. -/
theorem comap_C_span_cyclotomic {n : ℕ} (hn : 0 < n) :
    Ideal.comap (C : R →+* R[X]) (Ideal.span {cyclotomic n R}) = ⊥ := by
  ext r
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton, Submodule.mem_bot]
  refine ⟨fun hdvd ↦ ?_, fun hr ↦ by simp [hr]⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim r 0
  · obtain ⟨q, hq⟩ := hdvd
    by_contra hr
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hr (C_inj.mp (by simpa using hq))
    have hdeg := congr_arg natDegree hq
    rw [natDegree_C, (cyclotomic.monic n R).natDegree_mul' hq0, natDegree_cyclotomic] at hdeg
    have := Nat.totient_pos.mpr hn
    omega

/-- For `0 < e` and `0 < n`, the scalar contraction of `(Φ_n, Φ_{p ^ e n})` along `C : R →+* R[X]`
is `(p)`. The positivity hypothesis `0 < n` is sharp: at `n = 0` the ideal `(Φ_0, Φ_0) = ⊤`
contracts to `⊤` rather than `(p)`. -/
theorem comap_C_span_cyclotomic_prime_pow_mul {p e n : ℕ} (hp : p.Prime) (he : 0 < e) (hn : 0 < n) :
    Ideal.comap (C : R →+* R[X])
        (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) =
      Ideal.span {(p : R)} := by
  rw [span_cyclotomic_prime_pow_mul hp he n]
  ext r
  simp only [Ideal.mem_comap]
  refine ⟨fun hr ↦ ?_, fun hr ↦ ?_⟩
  · set I := Ideal.span {(p : R)}
    set π : R →+* R ⧸ I := Ideal.Quotient.mk I
    have hmap : C (π r) ∈ Ideal.span {cyclotomic n (R ⧸ I)} := by
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hr
      have hπ := congr_arg (Polynomial.map π) hab
      have hp0 : π (p : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      have hpX0 : (p : R[X]).map π = 0 := by
        rw [← C_eq_natCast, map_C, hp0, C_0]
      simp only [Polynomial.map_add, Polynomial.map_mul, hpX0, mul_zero, zero_add,
        map_cyclotomic, map_C] at hπ
      exact Ideal.mem_span_singleton.mpr ⟨b.map π, by rw [← hπ, mul_comm]⟩
    have hπr : π r = 0 := by
      have hmem : π r ∈ Ideal.comap (C : R ⧸ I →+* (R ⧸ I)[X])
          (Ideal.span {cyclotomic n (R ⧸ I)}) := hmap
      rwa [comap_C_span_cyclotomic hn, Submodule.mem_bot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hπr
  · have hmap : C r ∈ Ideal.span ({(p : R[X])} : Set R[X]) := by
      simpa [Ideal.map_span, C_eq_natCast] using Ideal.mem_map_of_mem (C : R →+* R[X]) hr
    exact Ideal.span_mono (by simp) hmap

end CongruenceAndIdeal

section QuotientEquiv

variable {R : Type*} [CommRing R]

private noncomputable def toAdjoinRootModNatAlgHom {p e : ℕ} (hp : p.Prime) (he : 0 < e) (n : ℕ) :
    (R[X] ⧸ Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) →ₐ[R]
      AdjoinRoot (cyclotomic n (R ⧸ Ideal.span {(p : R)})) :=
  Ideal.Quotient.liftₐ
    (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X]))
    (aeval (AdjoinRoot.root (cyclotomic n (R ⧸ Ideal.span {(p : R)}))))
    (fun f hf ↦ by
      set I : Ideal R := Ideal.span {(p : R)}
      set B := AdjoinRoot (cyclotomic n (R ⧸ I))
      rw [span_cyclotomic_prime_pow_mul hp he n] at hf
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hf
      have hp0 : (p : B) = 0 := by
        have hpI : Ideal.Quotient.mk I (p : R) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [← map_natCast (algebraMap R B), AdjoinRoot.algebraMap_eq' R, RingHom.comp_apply,
          Ideal.Quotient.algebraMap_eq, hpI, map_zero]
      have hΦ0 : aeval (AdjoinRoot.root (cyclotomic n (R ⧸ I))) (cyclotomic n R) = 0 := by
        rw [aeval_def, AdjoinRoot.algebraMap_eq' R, ← eval₂_map, Ideal.Quotient.algebraMap_eq,
          map_cyclotomic, AdjoinRoot.eval₂_root]
      simp [hp0, hΦ0])

@[simp]
private theorem toAdjoinRootModNatAlgHom_mk {p e : ℕ} (hp : p.Prime) (he : 0 < e) (n : ℕ)
    (g : R[X]) :
    toAdjoinRootModNatAlgHom hp he n
        (Ideal.Quotient.mk
          (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) g) =
      aeval (AdjoinRoot.root (cyclotomic n (R ⧸ Ideal.span {(p : R)}))) g :=
  rfl

private noncomputable def ofAdjoinRootModNatAlgHom {p e : ℕ} (hp : p.Prime) (he : 0 < e) (n : ℕ) :
    AdjoinRoot (cyclotomic n (R ⧸ Ideal.span {(p : R)})) →ₐ[R]
      (R[X] ⧸ Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) :=
  let I : Ideal R := Ideal.span {(p : R)}
  let J : Ideal R[X] := Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])
  let baseHom : R ⧸ I →ₐ[R] R[X] ⧸ J :=
    Ideal.Quotient.liftₐ I (Algebra.ofId R (R[X] ⧸ J)) fun r hr ↦ by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hr
      rw [map_mul, Algebra.ofId_apply, map_natCast, ← map_natCast (Ideal.Quotient.mk J),
        Ideal.Quotient.eq_zero_iff_mem.mpr (natCast_mem_span_cyclotomic_prime_pow_mul hp he n),
        zero_mul]
  AdjoinRoot.liftAlgHom (cyclotomic n (R ⧸ I)) baseHom (Ideal.Quotient.mk J X) (by
    have hcomp : (baseHom : R ⧸ I →+* R[X] ⧸ J).comp (Ideal.Quotient.mk I) =
        (Ideal.Quotient.mk J).comp C := by
      ext r
      rfl
    rw [← map_cyclotomic n (Ideal.Quotient.mk I), eval₂_map, hcomp, ← hom_eval₂, eval₂_C_X,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp))

@[simp]
private theorem ofAdjoinRootModNatAlgHom_of {p e : ℕ} (hp : p.Prime) (he : 0 < e) (n : ℕ)
    (r : R) :
    ofAdjoinRootModNatAlgHom hp he n
        (AdjoinRoot.of (cyclotomic n (R ⧸ Ideal.span {(p : R)}))
          (Ideal.Quotient.mk (Ideal.span {(p : R)}) r)) =
      Ideal.Quotient.mk
        (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) (C r) := by
  simp only [ofAdjoinRootModNatAlgHom, AdjoinRoot.liftAlgHom_of]
  rfl

@[simp]
private theorem ofAdjoinRootModNatAlgHom_root {p e : ℕ} (hp : p.Prime) (he : 0 < e) (n : ℕ) :
    ofAdjoinRootModNatAlgHom hp he n
        (AdjoinRoot.root (cyclotomic n (R ⧸ Ideal.span {(p : R)}))) =
      Ideal.Quotient.mk
        (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) X := by
  simp [ofAdjoinRootModNatAlgHom]

/-- **Two-order cyclotomic quotient equivalence.** Over any commutative ring `R`, for a prime `p`,
`0 < e`, and `n : ℕ`, the quotient `R[X] ⧸ (Φ_n, Φ_{p ^ e n})` is canonically `R`-algebra
isomorphic to `AdjoinRoot (cyclotomic n (R ⧸ (p)))`. -/
noncomputable def quotientSpanCyclotomicPrimePowMulAlgEquiv {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) :
    (R[X] ⧸ Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) ≃ₐ[R]
      AdjoinRoot (cyclotomic n (R ⧸ Ideal.span {(p : R)})) :=
  AlgEquiv.ofAlgHom
    (toAdjoinRootModNatAlgHom hp he n)
    (ofAdjoinRootModNatAlgHom hp he n)
    (by
      apply AlgHom.toRingHom_injective
      ext x
      · simp [AdjoinRoot.algebraMap_eq' R, Ideal.Quotient.algebraMap_eq]
      · simp)
    (by
      apply Ideal.Quotient.algHom_ext
      ext
      simp [Ideal.Quotient.mkₐ_eq_mk])

/-- `Polynomial.quotientSpanCyclotomicPrimePowMulAlgEquiv` sends the residue class of `g : R[X]`
to the residue class of `g mod p` in `AdjoinRoot (cyclotomic n (R ⧸ (p)))`. -/
@[simp]
theorem quotientSpanCyclotomicPrimePowMulAlgEquiv_mk {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) (g : R[X]) :
    quotientSpanCyclotomicPrimePowMulAlgEquiv hp he n
        (Ideal.Quotient.mk
          (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) g) =
      AdjoinRoot.mk (cyclotomic n (R ⧸ Ideal.span {(p : R)}))
        (g.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))) := by
  have hhom :
      ((quotientSpanCyclotomicPrimePowMulAlgEquiv (R := R) hp he n).toAlgHom.toRingHom).comp
          (Ideal.Quotient.mk
            (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X]))) =
        (AdjoinRoot.mk (cyclotomic n (R ⧸ Ideal.span {(p : R)}))).comp
          (mapRingHom (Ideal.Quotient.mk (Ideal.span {(p : R)}))) := by
    ext r
    · simp [quotientSpanCyclotomicPrimePowMulAlgEquiv, AdjoinRoot.algebraMap_eq' R,
        Ideal.Quotient.algebraMap_eq]
    · simp [quotientSpanCyclotomicPrimePowMulAlgEquiv, AdjoinRoot.mk_X]
  exact RingHom.congr_fun hhom g

/-- `Polynomial.quotientSpanCyclotomicPrimePowMulAlgEquiv` sends the image of `X` to
`AdjoinRoot.root`. -/
theorem quotientSpanCyclotomicPrimePowMulAlgEquiv_mk_X {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) :
    quotientSpanCyclotomicPrimePowMulAlgEquiv (R := R) hp he n
        (Ideal.Quotient.mk
          (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) X) =
      AdjoinRoot.root (cyclotomic n (R ⧸ Ideal.span {(p : R)})) := by
  simp [AdjoinRoot.mk_X]

/-- The inverse of `Polynomial.quotientSpanCyclotomicPrimePowMulAlgEquiv` sends `AdjoinRoot.root`
to the residue class of `X`. -/
@[simp]
theorem quotientSpanCyclotomicPrimePowMulAlgEquiv_symm_root {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) :
    (quotientSpanCyclotomicPrimePowMulAlgEquiv (R := R) hp he n).symm
        (AdjoinRoot.root (cyclotomic n (R ⧸ Ideal.span {(p : R)}))) =
      Ideal.Quotient.mk
        (Ideal.span ({cyclotomic n R, cyclotomic (p ^ e * n) R} : Set R[X])) X := by
  apply (quotientSpanCyclotomicPrimePowMulAlgEquiv (R := R) hp he n).injective
  rw [AlgEquiv.apply_symm_apply, quotientSpanCyclotomicPrimePowMulAlgEquiv_mk_X]

/-- **Integer two-order cyclotomic quotient equivalence (Habiro 2004, Lemma 4.1).** For a prime
`p`, `0 < e`, and `n : ℕ`, `ℤ[X] ⧸ (Φ_n, Φ_{p ^ e n})` is canonically isomorphic to
`AdjoinRoot (cyclotomic n (ZMod p))`, i.e. `(ℤ/pℤ)[X] ⧸ (Φ_n)`. -/
noncomputable def quotientSpanCyclotomicPrimePowMulIntEquiv {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) :
    (ℤ[X] ⧸ Ideal.span ({cyclotomic n ℤ, cyclotomic (p ^ e * n) ℤ} : Set ℤ[X])) ≃+*
      AdjoinRoot (cyclotomic n (ZMod p)) :=
  (quotientSpanCyclotomicPrimePowMulAlgEquiv (R := ℤ) hp he n).toRingEquiv.trans
    (AdjoinRoot.mapRingEquiv (Int.quotientSpanNatEquivZMod p)
      (cyclotomic n (ℤ ⧸ Ideal.span {(p : ℤ)})) (cyclotomic n (ZMod p))
      (Associated.of_eq (map_cyclotomic n (Int.quotientSpanNatEquivZMod p).toRingHom)))

/-- `Polynomial.quotientSpanCyclotomicPrimePowMulIntEquiv` sends the residue class of `g : ℤ[X]`
to the residue class of `g mod p` in `AdjoinRoot (cyclotomic n (ZMod p))`. -/
@[simp]
theorem quotientSpanCyclotomicPrimePowMulIntEquiv_mk {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) (g : ℤ[X]) :
    quotientSpanCyclotomicPrimePowMulIntEquiv hp he n
        (Ideal.Quotient.mk
          (Ideal.span ({cyclotomic n ℤ, cyclotomic (p ^ e * n) ℤ} : Set ℤ[X])) g) =
      AdjoinRoot.mk (cyclotomic n (ZMod p)) (g.map (Int.castRingHom (ZMod p))) := by
  have hhom :
      (quotientSpanCyclotomicPrimePowMulIntEquiv hp he n).toRingHom.comp
          (Ideal.Quotient.mk
            (Ideal.span ({cyclotomic n ℤ, cyclotomic (p ^ e * n) ℤ} : Set ℤ[X]))) =
        (AdjoinRoot.mk (cyclotomic n (ZMod p))).comp (mapRingHom (Int.castRingHom (ZMod p))) := by
    ext k
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        quotientSpanCyclotomicPrimePowMulIntEquiv, RingEquiv.trans_apply,
        AlgEquiv.coe_toRingEquiv, quotientSpanCyclotomicPrimePowMulAlgEquiv_mk,
        map_C, AdjoinRoot.coe_mapRingEquiv, coe_mapRingHom, AdjoinRoot.mk_C, AdjoinRoot.map_of]
      have hcast := RingHom.congr_fun (Int.quotientSpanNatEquivZMod_comp_Quotient_mk p) k
      exact congr_arg (AdjoinRoot.of (cyclotomic n (ZMod p))) hcast
    · simp [quotientSpanCyclotomicPrimePowMulIntEquiv, AdjoinRoot.mk_X]
  exact RingHom.congr_fun hhom g

/-- `Polynomial.quotientSpanCyclotomicPrimePowMulIntEquiv` sends the image of `X` to
`AdjoinRoot.root`. -/
theorem quotientSpanCyclotomicPrimePowMulIntEquiv_mk_X {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) :
    quotientSpanCyclotomicPrimePowMulIntEquiv hp he n
        (Ideal.Quotient.mk
          (Ideal.span ({cyclotomic n ℤ, cyclotomic (p ^ e * n) ℤ} : Set ℤ[X])) X) =
      AdjoinRoot.root (cyclotomic n (ZMod p)) := by
  simp [AdjoinRoot.mk_X]

/-- The inverse of `Polynomial.quotientSpanCyclotomicPrimePowMulIntEquiv` sends `AdjoinRoot.root`
to the residue class of `X`. -/
@[simp]
theorem quotientSpanCyclotomicPrimePowMulIntEquiv_symm_root {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (n : ℕ) :
    (quotientSpanCyclotomicPrimePowMulIntEquiv hp he n).symm
        (AdjoinRoot.root (cyclotomic n (ZMod p))) =
      Ideal.Quotient.mk
        (Ideal.span ({cyclotomic n ℤ, cyclotomic (p ^ e * n) ℤ} : Set ℤ[X])) X := by
  apply (quotientSpanCyclotomicPrimePowMulIntEquiv hp he n).injective
  rw [RingEquiv.apply_symm_apply, quotientSpanCyclotomicPrimePowMulIntEquiv_mk_X]

end QuotientEquiv

section RootSeparation

variable {R : Type*} [CommRing R]

/-- **Non-prime-power cyclotomic roots have unit distance from `1`.** Over any commutative ring `R`,
if `d` is not a prime power (`∀ p, p.Prime → ∀ k, p ^ k ≠ d`, which in particular excludes `d = 1`
since `2 ^ 0 = 1`) and `ω` is a root of `Φ_d`, then `1 - ω` is a unit in `R`. -/
theorem isUnit_one_sub_of_isRoot_cyclotomic_not_prime_pow {d : ℕ}
    (hd : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ d) {ω : R} (hω : (cyclotomic d R).IsRoot ω) :
    IsUnit (1 - ω) := by
  refine isUnit_of_dvd_one ?_
  have hdvd := sub_dvd_eval_sub 1 ω (cyclotomic d R)
  rwa [eval_one_cyclotomic_not_prime_pow hd, hω.eq_zero, sub_zero] at hdvd

/-- Variant of `Polynomial.isUnit_one_sub_of_isRoot_cyclotomic_not_prime_pow` for `ω - 1`. -/
theorem isUnit_sub_one_of_isRoot_cyclotomic_not_prime_pow {d : ℕ}
    (hd : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ d) {ω : R} (hω : (cyclotomic d R).IsRoot ω) :
    IsUnit (ω - 1) := by
  simpa only [neg_sub] using (isUnit_one_sub_of_isRoot_cyclotomic_not_prime_pow hd hω).neg

/-- **Hausdorff adic rings separate `1` from non-prime-power cyclotomic roots.** In a nontrivial
commutative ring `R` that is `I`-adically Hausdorff (for instance `I = (p)` in `ℤ` or `ℤ_p`), if
`d` is not a prime power and `ω` is a root of `Φ_d`, then `(1 - ω) ^ m ∉ I` for every `m : ℕ`.
Thus a Taylor expansion around `1` cannot converge `I`-adically at `ω`. -/
theorem notMem_of_isHausdorff_of_isRoot_cyclotomic_not_prime_pow [Nontrivial R] (I : Ideal R)
    [IsHausdorff I R] {d : ℕ} (hd : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ d) {ω : R}
    (hω : (cyclotomic d R).IsRoot ω) (m : ℕ) :
    (1 - ω) ^ m ∉ I := by
  intro hmem
  have hu : IsUnit ((1 - ω) ^ m) :=
    (isUnit_one_sub_of_isRoot_cyclotomic_not_prime_pow hd hω).pow m
  have htop : I = ⊤ := Ideal.eq_top_of_isUnit_mem I hmem hu
  have : Subsingleton R := IsHausdorff.subsingleton (htop ▸ ‹IsHausdorff I R›)
  exact not_subsingleton R this

/-- Over any commutative ring `R`, if `p` is prime and `ω` is a root of `Φ_{p ^ (k + 1)}`, then
`ω - 1` divides `p`. Unlike `IsPrimitiveRoot.sub_one_dvd_natCast`, no domain assumption on `R` is
needed. -/
theorem sub_one_dvd_natCast_of_isRoot_cyclotomic_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} {ω : R}
    (hω : (cyclotomic (p ^ (k + 1)) R).IsRoot ω) :
    ω - 1 ∣ (p : R) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := sub_dvd_eval_sub 1 ω (cyclotomic (p ^ (k + 1)) R)
  rw [eval_one_cyclotomic_prime_pow, hω.eq_zero, sub_zero] at hdvd
  simpa only [neg_sub] using neg_dvd.mpr hdvd

end RootSeparation

end Polynomial

namespace Nat.Prime

/-- **Prime-power roots of unity are `(p)`-adically close to `1`.** Over any commutative ring `R`,
if `p` is prime and `ω ^ p ^ e = 1`, then `p` divides `(ω - 1) ^ p ^ e`. -/
theorem natCast_dvd_sub_one_pow_of_pow_eq_one {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {e : ℕ} {ω : R} (hω : ω ^ p ^ e = 1) :
    (p : R) ∣ (ω - 1) ^ p ^ e := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp 1 (ω - 1) e
  have h1 : (1 + (ω - 1)) ^ p ^ e = 1 := by simpa using hω
  rw [h1, one_pow] at hr
  exact ⟨-(ω - 1) * r, by linear_combination -hr⟩

/-- Variant of `Nat.Prime.natCast_dvd_sub_one_pow_of_pow_eq_one` for `1 - ω`. -/
theorem natCast_dvd_one_sub_pow_of_pow_eq_one {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {e : ℕ} {ω : R} (hω : ω ^ p ^ e = 1) :
    (p : R) ∣ (1 - ω) ^ p ^ e := by
  have h : (1 - ω) ^ p ^ e = (-1) ^ p ^ e * (ω - 1) ^ p ^ e := by
    rw [← mul_pow]
    congr 1
    ring
  rw [h]
  exact dvd_mul_of_dvd_right (hp.natCast_dvd_sub_one_pow_of_pow_eq_one hω) _

/-- If `p` is prime and `ω ^ p ^ e = 1` in `R`, then `(ω - 1) ^ (p ^ e * m) ∈ (p) ^ m` for every
`m : ℕ`, so `ω - 1` is topologically nilpotent in the `(p)`-adic topology. -/
theorem sub_one_pow_mem_pow_span_of_pow_eq_one {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {e : ℕ} {ω : R} (hω : ω ^ p ^ e = 1) (m : ℕ) :
    (ω - 1) ^ (p ^ e * m) ∈ Ideal.span {(p : R)} ^ m := by
  rw [pow_mul, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact pow_dvd_pow_of_dvd (hp.natCast_dvd_sub_one_pow_of_pow_eq_one hω) m

end Nat.Prime
