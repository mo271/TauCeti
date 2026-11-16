/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Expand

/-!
# Resultants and comaximality of cyclotomic polynomials

For `1 ≤ n < m`, the resultant of the cyclotomic polynomials `Φ_n` and `Φ_m` over `ℤ` (and hence
over any commutative ring `R`) is given by Apostol's / Louboutin's formula:

* if `m / n = p ^ e` for a prime `p` and `e ≥ 1`, then `Res(Φ_n, Φ_m) = p ^ φ(n)`;
* otherwise, `Res(Φ_n, Φ_m) = 1`.

In the opposite order `m > n ≥ 1`, `Res(Φ_m, Φ_n) = Res(Φ_n, Φ_m)` whenever `m > 2` (because
`φ(m)` is even), while for the unique odd-totient pair `(m, n) = (2, 1)` one has
`Res(Φ_2, Φ_1) = Res(X + 1, X - 1) = -2`. In particular, whenever `m ≠ n` do not differ by a
prime-power factor, `Res(Φ_m, Φ_n) = 1` in both orders and even at `0` (`Φ_0 = 1`).

Since `Φ_m` is monic, `IsCoprime (Φ_m) (Φ_n)` in `R[X]` is equivalent to `Res(Φ_m, Φ_n)` being a
unit in `R`. Combining this with the resultant formula characterizes comaximality of cyclotomic
ideals over an arbitrary commutative ring `R`: for positive `m` and `n` over a nontrivial ring `R`,
`Φ_m` and `Φ_n` are coprime in `R[X]` if and only if `m ≠ n` and every prime `p` dividing one order
as `m = p ^ e n` or `n = p ^ e m` (`e ≥ 1`) is a unit in `R`. Over `ℤ`, `(Φ_m, Φ_n) = ⊤` if and
only if `m ≠ n` and neither `m / n` nor `n / m` is a prime power; over `ℚ`, every prime is a unit,
recovering `Polynomial.cyclotomic.isCoprime_rat`.

## Proof strategy

Over an integral domain containing a primitive `n`-th root of unity, splitting `Φ_n` into linear
factors evaluates `Res(Φ_n, f) = ∏_{μ ∈ μ_n^×} f(μ)`. Specializing to `ℂ` shows that for `k`
coprime to `n`, `Res(Φ_n, g(X ^ k)) = Res(Φ_n, g)` because `μ ↦ μ ^ k` permutes `μ_n^×`. Together
with the expansion identity `Res(f(X ^ q), g(X ^ q)) = Res(f, g) ^ q` from
`TauCeti.RingTheory.Polynomial.Resultant.Expand` and the factorization of `Φ_s(X ^ q)` for a prime
`q`, strong induction on `m` determines `Res(Φ_n, Φ_m)` over `ℤ`, and base change along `ℤ → R`
transfers the formula to every commutative ring.

## Main results

* `IsPrimitiveRoot.resultant_cyclotomic_left`, `IsPrimitiveRoot.resultant_cyclotomic_right`:
  root-product formulas for resultants with `Φ_n` over an integral domain.
* `IsPrimitiveRoot.resultant_cyclotomic_expand_of_coprime`: invariance of `Res(Φ_n, f(X ^ k))` when
  `k.Coprime n`.
* `Polynomial.resultant_cyclotomic_of_lt`: Apostol's formula for `Res(Φ_n, Φ_m)` when `0 < n < m`.
* `Polynomial.resultant_cyclotomic_prime_pow_mul`: `Res(Φ_n, Φ_{p ^ e n}) = p ^ φ(n)`.
* `Polynomial.resultant_cyclotomic_comm_of_two_lt`, `Polynomial.resultant_cyclotomic_two_one`:
  behavior under swapping the two cyclotomic polynomials.
* `Polynomial.resultant_cyclotomic_eq_one_of_not_prime_pow_ratio`: `Res(Φ_m, Φ_n) = 1` whenever
  `m ≠ n` do not differ by a prime power.
* `Polynomial.natAbs_resultant_cyclotomic`: symmetric formula for `(Res(Φ_m, Φ_n)).natAbs` over `ℤ`.
* `Polynomial.isCoprime_cyclotomic_prime_pow_mul_iff`, `Polynomial.isCoprime_cyclotomic_iff_of_ne`,
  `Polynomial.isCoprime_cyclotomic_iff`, `Polynomial.isCoprime_cyclotomic_int_iff`: exact
  characterizations of `IsCoprime (cyclotomic m R) (cyclotomic n R)`.

## References

* [T. M. Apostol, *Resultants of cyclotomic polynomials*, Proc. Amer. Math. Soc. **24** (1970),
  457–462].
* [S. Louboutin, *Resultants of cyclotomic polynomials*, Publ. Math. Debrecen **50** (1997),
  75–77].
* [K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146], §5.
-/

public section

namespace IsPrimitiveRoot

open Polynomial

/-- Over an integral domain `K` containing a primitive `n`-th root of unity `ζ`, the resultant of
`Φ_n` with any polynomial `f` is the product of `f(μ)` over `μ ∈ primitiveRoots n K`. -/
theorem resultant_cyclotomic_left {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (f : K[X]) :
    (cyclotomic n K).resultant f = ∏ μ ∈ primitiveRoots n K, f.eval μ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    resultant_prod_left_of_monic _ (fun μ _ ↦ monic_X_sub_C μ)]
  refine Finset.prod_congr rfl fun μ _ ↦ ?_
  rw [natDegree_X_sub_C, resultant_X_sub_C_left (hg := le_rfl)]

/-- Over an integral domain `K` containing a primitive `n`-th root of unity `ζ`, the resultant of
`f` with `Φ_n` is `(-1) ^ (deg f * φ(n))` times the product of `f(μ)` over
`μ ∈ primitiveRoots n K`. -/
theorem resultant_cyclotomic_right {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (f : K[X]) :
    f.resultant (cyclotomic n K) =
      (-1) ^ (f.natDegree * n.totient) * ∏ μ ∈ primitiveRoots n K, f.eval μ := by
  rw [resultant_comm, hζ.resultant_cyclotomic_left, natDegree_cyclotomic, mul_comm f.natDegree]

/-- Over an integral domain `K` containing a primitive `n`-th root of unity, substituting `X ^ k`
with `k` coprime to `n` permutes `primitiveRoots n K` and therefore preserves `Res(Φ_n, ·)`. -/
theorem resultant_cyclotomic_expand_of_coprime {K : Type*} [CommRing K] [IsDomain K] {ζ : K}
    {k n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hcop : k.Coprime n) (f : K[X]) :
    (cyclotomic n K).resultant (expand K k f) = (cyclotomic n K).resultant f := by
  rcases eq_or_ne n 0 with rfl | hn0
  · obtain rfl : k = 1 := by simpa using hcop
    simp
  have : NeZero n := ⟨hn0⟩
  rw [hζ.resultant_cyclotomic_left, hζ.resultant_cyclotomic_left]
  simp only [expand_eval]
  rw [← Finset.prod_coe_sort, ← Finset.prod_coe_sort (primitiveRoots n K)]
  simpa only [primitiveRootsPowEquivOfCoprime_apply_coe] using
    (primitiveRootsPowEquivOfCoprime hcop).prod_comp (fun x : primitiveRoots n K ↦ f.eval (x : K))

end IsPrimitiveRoot

namespace Polynomial

section Helpers

private theorem minFac_prime_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    (p ^ e).minFac = p := by
  have hne1 : p ^ e ≠ 1 := (one_lt_pow₀ hp.one_lt he.ne').ne'
  have hmin_prime : (p ^ e).minFac.Prime := Nat.minFac_prime hne1
  exact (Nat.prime_dvd_prime_iff_eq hmin_prime hp).mp
    (hmin_prime.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ e)))

private theorem resultant_mul_left_of_monic {R : Type*} [CommRing R] {f₁ f₂ : R[X]}
    (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (g : R[X]) :
    (f₁ * f₂).resultant g = f₁.resultant g * f₂.resultant g := by
  nontriviality R
  conv_lhs => rw [hf₁.natDegree_mul hf₂]
  exact resultant_mul_left f₁ f₂ g g.natDegree le_rfl

private theorem resultant_mul_right_of_monic {R : Type*} [CommRing R] (f : R[X]) {g₁ g₂ : R[X]}
    (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) :
    f.resultant (g₁ * g₂) = f.resultant g₁ * f.resultant g₂ := by
  nontriviality R
  conv_lhs => rw [hg₁.natDegree_mul hg₂]
  exact resultant_mul_right f g₁ g₂ f.natDegree le_rfl

private theorem resultant_cyclotomic_int_expand_of_coprime {k n : ℕ} (hcop : k.Coprime n)
    (g : ℤ[X]) :
    (cyclotomic n ℤ).resultant (expand ℤ k g) = (cyclotomic n ℤ).resultant g := by
  rcases eq_or_ne n 0 with rfl | hn0
  · obtain rfl : k = 1 := by simpa using hcop
    simp
  apply Int.cast_injective (α := ℂ)
  change Int.castRingHom ℂ ((cyclotomic n ℤ).resultant (expand ℤ k g)) =
    Int.castRingHom ℂ ((cyclotomic n ℤ).resultant g)
  rw [← resultant_map_of_natDegree_eq (Int.castRingHom ℂ)
      (natDegree_map_eq_of_injective Int.cast_injective _)
      (natDegree_map_eq_of_injective Int.cast_injective _),
    ← resultant_map_of_natDegree_eq (Int.castRingHom ℂ)
      (natDegree_map_eq_of_injective Int.cast_injective _)
      (natDegree_map_eq_of_injective Int.cast_injective _),
    map_cyclotomic_int, map_expand]
  exact (Complex.isPrimitiveRoot_exp n hn0).resultant_cyclotomic_expand_of_coprime hcop _

private theorem resultant_cyclotomic_mul_prime_expand {r q : ℕ} (hr : 0 < r) (hq : q.Prime)
    (g : ℤ[X]) (hg : (cyclotomic r ℤ).resultant g ≠ 0) :
    (cyclotomic (r * q) ℤ).resultant (expand ℤ q g) =
      (cyclotomic r ℤ).resultant g ^ ((r * q).totient / r.totient) := by
  have hφr : 0 < r.totient := Nat.totient_pos.mpr hr
  by_cases hqr : q ∣ r
  · have htot : (r * q).totient / r.totient = q := by
      rw [mul_comm r q, Nat.totient_mul_of_dvd hqr, mul_comm q, Nat.mul_div_cancel_left _ hφr]
    rw [htot, ← cyclotomic_expand_eq_cyclotomic hq hqr ℤ, resultant_expand]
  · have htot : (r * q).totient / r.totient = q - 1 := by
      rw [mul_comm r q, Nat.totient_mul_of_prime_of_not_dvd hq hqr, mul_comm (q - 1),
        Nat.mul_div_cancel_left _ hφr]
    rw [htot]
    have hcop : q.Coprime r := hq.coprime_iff_not_dvd.mpr hqr
    have hR : (cyclotomic r ℤ).resultant (expand ℤ q g) = (cyclotomic r ℤ).resultant g :=
      resultant_cyclotomic_int_expand_of_coprime hcop g
    have hmul :
        (cyclotomic (r * q) ℤ).resultant (expand ℤ q g) * (cyclotomic r ℤ).resultant g =
          (cyclotomic r ℤ).resultant g ^ (q - 1) * (cyclotomic r ℤ).resultant g := by
      calc (cyclotomic (r * q) ℤ).resultant (expand ℤ q g) * (cyclotomic r ℤ).resultant g
          = (cyclotomic (r * q) ℤ).resultant (expand ℤ q g) *
              (cyclotomic r ℤ).resultant (expand ℤ q g) := by rw [hR]
        _ = (cyclotomic (r * q) ℤ * cyclotomic r ℤ).resultant (expand ℤ q g) :=
            (resultant_mul_left_of_monic (cyclotomic.monic (r * q) ℤ) (cyclotomic.monic r ℤ) _).symm
        _ = (expand ℤ q (cyclotomic r ℤ)).resultant (expand ℤ q g) := by
            rw [cyclotomic_expand_eq_cyclotomic_mul hq hqr ℤ]
        _ = (cyclotomic r ℤ).resultant g ^ q := resultant_expand _ _ _
        _ = (cyclotomic r ℤ).resultant g ^ (q - 1) * (cyclotomic r ℤ).resultant g := by
            rw [← pow_succ, Nat.sub_add_cancel hq.pos]
    exact mul_right_cancel₀ hg hmul

private def cyclotomicResultantInt (n m : ℕ) : ℤ :=
  if n ∣ m ∧ IsPrimePow (m / n) then ((m / n).minFac : ℤ) ^ n.totient else 1

private theorem cyclotomicResultantInt_pos (n m : ℕ) : 0 < cyclotomicResultantInt n m := by
  unfold cyclotomicResultantInt
  split_ifs
  · exact pow_pos (Int.natCast_pos.mpr (Nat.minFac_pos _)) _
  · exact zero_lt_one

private theorem cyclotomicResultantInt_mul_right {r s q : ℕ} (hq : 0 < q) :
    cyclotomicResultantInt r s ^ ((r * q).totient / r.totient) =
      cyclotomicResultantInt (r * q) (s * q) := by
  unfold cyclotomicResultantInt
  have hdvd : r * q ∣ s * q ↔ r ∣ s := mul_dvd_mul_iff_right hq.ne'
  have hdiv : s * q / (r * q) = s / r := Nat.mul_div_mul_right s r hq
  simp only [hdvd, hdiv]
  split_ifs
  · rw [← pow_mul, Nat.mul_div_cancel' (Nat.totient_dvd_of_dvd (dvd_mul_right r q))]
  · exact one_pow _

private theorem cyclotomicResultantInt_mul_prime {n q : ℕ} (hn : 0 < n) (hq : q.Prime) :
    cyclotomicResultantInt n (n * q) = (q : ℤ) ^ n.totient := by
  unfold cyclotomicResultantInt
  have hcond : n ∣ n * q ∧ IsPrimePow (n * q / n) := by
    rw [Nat.mul_div_cancel_left q hn]
    exact ⟨dvd_mul_right n q, hq.isPrimePow⟩
  rw [ite_eq_left hcond, Nat.mul_div_cancel_left q hn, hq.minFac_eq]

private theorem cyclotomicResultantInt_mul_prime_of_dvd_of_not_dvd {n s q : ℕ} (hn : 0 < n)
    (hs : 0 < s) (hq : q.Prime) (hqs : q ∣ s) (hqn : ¬ q ∣ n) :
    cyclotomicResultantInt n s = cyclotomicResultantInt n (s * q) := by
  unfold cyclotomicResultantInt
  have hdvd_iff : n ∣ s * q ↔ n ∣ s :=
    ⟨(hq.coprime_iff_not_dvd.mpr hqn).symm.dvd_of_dvd_mul_right, fun h ↦ dvd_mul_of_dvd_left h q⟩
  by_cases hns : n ∣ s
  · have hnsq : n ∣ s * q := hdvd_iff.mpr hns
    set d := s / n
    have hs_eq : s = d * n := (Nat.div_mul_cancel hns).symm
    have hdiv_sq : s * q / n = d * q := by
      rw [hs_eq, mul_right_comm, Nat.mul_div_cancel _ hn]
    have hqd : q ∣ d := (hq.dvd_mul.mp (hs_eq ▸ hqs)).resolve_right hqn
    have hd0 : d ≠ 0 := fun h ↦ hs.ne' (by rw [hs_eq, h, zero_mul])
    have hd1 : d ≠ 1 := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd
      have := hq.two_le
      omega
    have hpp_iff : IsPrimePow d ↔ IsPrimePow (d * q) := by
      refine ⟨fun hd_pp ↦ ?_, fun hdq_pp ↦ hdq_pp.dvd (dvd_mul_right d q) hd1⟩
      obtain ⟨p, k, hp, _, hpk⟩ := (isPrimePow_nat_iff d).mp hd_pp
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hpk ▸ hqd))
      rw [← hpk, hqp, ← pow_succ]
      exact (isPrimePow_nat_iff _).mpr ⟨p, k + 1, hp, Nat.succ_pos k, rfl⟩
    rw [hdiv_sq]
    by_cases hpp : IsPrimePow d
    · obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff d).mp hpp
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hpk ▸ hqd))
      have hmin₁ : d.minFac = p := by rw [← hpk]; exact minFac_prime_pow hp hk
      have hmin₂ : (d * q).minFac = p := by
        rw [← hpk, hqp, ← pow_succ]
        exact minFac_prime_pow hp (Nat.succ_pos k)
      rw [ite_eq_left ⟨hns, hpp⟩, ite_eq_left ⟨hnsq, hpp_iff.mp hpp⟩, hmin₁, hmin₂]
    · have hn1 : ¬ (n ∣ s ∧ IsPrimePow d) := fun h ↦ hpp h.2
      have hn2 : ¬ (n ∣ s * q ∧ IsPrimePow (d * q)) := fun h ↦ hpp (hpp_iff.mpr h.2)
      rw [ite_eq_right hn1, ite_eq_right hn2]
  · have hn1 : ¬ (n ∣ s ∧ IsPrimePow (s / n)) := fun h ↦ hns h.1
    have hn2 : ¬ (n ∣ s * q ∧ IsPrimePow (s * q / n)) := fun h ↦ hns (hdvd_iff.mp h.1)
    rw [ite_eq_right hn1, ite_eq_right hn2]

private theorem resultant_cyclotomic_int_of_lt {n m : ℕ} (hn : 0 < n) (hnm : n < m) :
    (cyclotomic n ℤ).resultant (cyclotomic m ℤ) = cyclotomicResultantInt n m := by
  induction m using Nat.strong_induction_on generalizing n with
  | ind m ih =>
    have ih_ne_zero : ∀ {a b : ℕ}, 0 < a → a < m → 0 < b → b < m → a ≠ b →
        (cyclotomic a ℤ).resultant (cyclotomic b ℤ) ≠ 0 := by
      intro a b ha ham hb hbm hab
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · rw [ih b hbm ha hlt]
        exact (cyclotomicResultantInt_pos a b).ne'
      · exact absurd rfl hab
      · rw [resultant_comm, ih a ham hb hgt]
        exact mul_ne_zero (pow_ne_zero _ (by decide)) (cyclotomicResultantInt_pos b a).ne'
    have ih_eq_one : ∀ {a b : ℕ}, 0 < a → a < m → 0 < b → b < m → a ≠ b →
        2 < max a b → ¬ a ∣ b → ¬ b ∣ a →
        (cyclotomic a ℤ).resultant (cyclotomic b ℤ) = 1 := by
      intro a b ha ham hb hbm hab hmax hab_dvd hba_dvd
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · rw [ih b hbm ha hlt]
        unfold cyclotomicResultantInt
        exact ite_eq_right fun h ↦ hab_dvd h.1
      · exact absurd rfl hab
      · have ha2 : 2 < a := by rwa [max_eq_left hgt.le] at hmax
        have heven : Even ((cyclotomic a ℤ).natDegree * (cyclotomic b ℤ).natDegree) := by
          rw [natDegree_cyclotomic]
          exact (Nat.totient_even ha2).mul_right _
        rw [resultant_comm, Even.neg_one_pow heven, one_mul, ih a ham hb hgt]
        unfold cyclotomicResultantInt
        exact ite_eq_right fun h ↦ hba_dvd h.1
    have hm1 : m ≠ 1 := by omega
    set q := m.minFac
    have hq : q.Prime := Nat.minFac_prime hm1
    obtain ⟨s, hs_eq⟩ : q ∣ m := Nat.minFac_dvd m
    have hm_eq : m = s * q := by rw [hs_eq, mul_comm]
    have hs_pos : 0 < s := Nat.pos_of_ne_zero fun hs0 ↦ by simp [hs0] at hm_eq; omega
    have hs_lt : s < m := by
      rw [hm_eq]
      exact lt_mul_of_one_lt_right hs_pos hq.one_lt
    by_cases hqs : q ∣ s
    · have hΦm : cyclotomic m ℤ = expand ℤ q (cyclotomic s ℤ) := by
        rw [hm_eq, ← cyclotomic_expand_eq_cyclotomic hq hqs ℤ]
      by_cases hqn : q ∣ n
      · obtain ⟨r, hr_eq⟩ : q ∣ n := hqn
        have hn_eq : n = r * q := by rw [hr_eq, mul_comm]
        have hr_pos : 0 < r := Nat.pos_of_ne_zero fun hr0 ↦ by simp [hr0] at hn_eq; omega
        have hrs : r < s := by
          rw [hn_eq, hm_eq] at hnm
          exact Nat.lt_of_mul_lt_mul_right hnm
        have h_rs_ne : (cyclotomic r ℤ).resultant (cyclotomic s ℤ) ≠ 0 := by
          rw [ih s hs_lt hr_pos hrs]
          exact (cyclotomicResultantInt_pos r s).ne'
        rw [hΦm, hn_eq, resultant_cyclotomic_mul_prime_expand hr_pos hq _ h_rs_ne,
          ih s hs_lt hr_pos hrs, cyclotomicResultantInt_mul_right hq.pos, ← hm_eq]
      · rw [hΦm, resultant_cyclotomic_int_expand_of_coprime (hq.coprime_iff_not_dvd.mpr hqn)]
        have hns_ne : n ≠ s := fun h ↦ hqn (h ▸ hqs)
        rcases lt_or_gt_of_ne hns_ne with hns_lt | hsn_lt
        · rw [ih s hs_lt hn hns_lt, hm_eq,
            cyclotomicResultantInt_mul_prime_of_dvd_of_not_dvd hn hs_pos hq hqs hqn]
        · have hs2 : 2 ≤ s := le_trans hq.two_le (Nat.le_of_dvd hs_pos hqs)
          have hmax : 2 < max n s := by omega
          have hnot_ns : ¬ n ∣ s := Nat.not_dvd_of_pos_of_lt hs_pos hsn_lt
          have hnot_sn : ¬ s ∣ n := fun h ↦ hqn (hqs.trans h)
          rw [ih_eq_one hn hnm hs_pos hs_lt hns_ne hmax hnot_ns hnot_sn]
          unfold cyclotomicResultantInt
          symm
          refine ite_eq_right fun ⟨hnm_dvd, hpp⟩ ↦ ?_
          obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff (m / n)).mp hpp
          have hpm : p ∣ m := by
            have hdvd_pk : p ∣ m / n := by rw [← hpk]; exact dvd_pow_self p hk.ne'
            exact hdvd_pk.trans ⟨n, (Nat.div_mul_cancel hnm_dvd).symm⟩
          have hqp : q ≤ p := Nat.minFac_le_of_dvd hp.two_le hpm
          have hp_pow : p ≤ p ^ k := Nat.le_self_pow hk.ne' p
          have hm_ge : q * n ≤ m := by
            calc q * n ≤ p ^ k * n := Nat.mul_le_mul_right n (le_trans hqp hp_pow)
              _ = (m / n) * n := by rw [hpk]
              _ = m := Nat.div_mul_cancel hnm_dvd
          have hm_lt : m < q * n := by
            rw [hm_eq, mul_comm s q]
            exact mul_lt_mul_of_pos_left hsn_lt hq.pos
          omega
    · have hexp : expand ℤ q (cyclotomic s ℤ) = cyclotomic m ℤ * cyclotomic s ℤ := by
        rw [hm_eq, cyclotomic_expand_eq_cyclotomic_mul hq hqs ℤ]
      by_cases hqn : q ∣ n
      · obtain ⟨r, hr_eq⟩ := id hqn
        have hn_eq : n = r * q := by rw [hr_eq, mul_comm]
        have hr_pos : 0 < r := Nat.pos_of_ne_zero fun hr0 ↦ by simp [hr0] at hn_eq; omega
        have hrs : r < s := by
          rw [hn_eq, hm_eq] at hnm
          exact Nat.lt_of_mul_lt_mul_right hnm
        have h_rs_ne : (cyclotomic r ℤ).resultant (cyclotomic s ℤ) ≠ 0 := by
          rw [ih s hs_lt hr_pos hrs]
          exact (cyclotomicResultantInt_pos r s).ne'
        have h_lhs :
            (cyclotomic n ℤ).resultant (expand ℤ q (cyclotomic s ℤ)) =
              cyclotomicResultantInt n m := by
          rw [hn_eq, resultant_cyclotomic_mul_prime_expand hr_pos hq _ h_rs_ne,
            ih s hs_lt hr_pos hrs, cyclotomicResultantInt_mul_right hq.pos, ← hm_eq, ← hn_eq]
        have hns_ne : n ≠ s := fun h ↦ hqs (h ▸ hqn)
        have hn2 : 2 ≤ n := by
          rw [hn_eq]
          exact le_trans hq.two_le (Nat.le_mul_of_pos_left q hr_pos)
        have hs2 : 2 ≤ s := by omega
        have hmax : 2 < max n s := by omega
        have hnot_ns : ¬ n ∣ s := fun h ↦ hqs (hqn.trans h)
        have hnot_sn : ¬ s ∣ n := fun h ↦ by
          rw [hn_eq] at h
          have hsr : s ∣ r := (hq.coprime_iff_not_dvd.mpr hqs).symm.dvd_of_dvd_mul_right h
          exact hrs.not_ge (Nat.le_of_dvd hr_pos hsr)
        have h_ns_one : (cyclotomic n ℤ).resultant (cyclotomic s ℤ) = 1 :=
          ih_eq_one hn hnm hs_pos hs_lt hns_ne hmax hnot_ns hnot_sn
        rw [hexp, resultant_mul_right_of_monic _ (cyclotomic.monic m ℤ) (cyclotomic.monic s ℤ),
          h_ns_one, mul_one] at h_lhs
        exact h_lhs
      · rcases eq_or_ne n s with rfl | hns_ne
        · rw [hm_eq, cyclotomicResultantInt_mul_prime hn hq]
          rcases eq_or_ne n 1 with rfl | hn1
          · have : Fact q.Prime := ⟨hq⟩
            rw [one_mul, cyclotomic_one, ← C_1, natDegree_X_sub_C,
              resultant_X_sub_C_left (hg := le_rfl), eval_one_cyclotomic_prime, Nat.totient_one,
              pow_one]
          · set p₀ := n.minFac
            have hp₀ : p₀.Prime := Nat.minFac_prime hn1
            obtain ⟨r, hr_eq⟩ : p₀ ∣ n := Nat.minFac_dvd n
            have hn_eq : n = r * p₀ := by rw [hr_eq, mul_comm]
            have hr_pos : 0 < r := Nat.pos_of_ne_zero fun hr0 ↦ by simp [hr0] at hn_eq; omega
            have hp₀q : p₀ ≠ q := fun h ↦ hqn (h ▸ Nat.minFac_dvd n)
            have hrq_pos : 0 < r * q := mul_pos hr_pos hq.pos
            have hrq_lt : r * q < m := by
              rw [hm_eq, hn_eq, mul_right_comm r p₀ q]
              exact lt_mul_of_one_lt_right hrq_pos hp₀.one_lt
            have hr_lt_rq : r < r * q := lt_mul_of_one_lt_right hr_pos hq.one_lt
            have h_rq :
                (cyclotomic r ℤ).resultant (cyclotomic (r * q) ℤ) = (q : ℤ) ^ r.totient := by
              rw [ih (r * q) hrq_lt hr_pos hr_lt_rq, cyclotomicResultantInt_mul_prime hr_pos hq]
            have h_rq_ne : (cyclotomic r ℤ).resultant (cyclotomic (r * q) ℤ) ≠ 0 := by
              rw [h_rq]
              exact pow_ne_zero _ (Int.natCast_ne_zero.mpr hq.ne_zero)
            have hm_rq : m = r * q * p₀ := by rw [hm_eq, hn_eq, mul_right_comm r p₀ q]
            by_cases hp₀r : p₀ ∣ r
            · have hp₀rq : p₀ ∣ r * q := dvd_mul_of_dvd_left hp₀r q
              have hΦn : cyclotomic n ℤ = expand ℤ p₀ (cyclotomic r ℤ) := by
                rw [hn_eq, ← cyclotomic_expand_eq_cyclotomic hp₀ hp₀r ℤ]
              have hΦm' : cyclotomic (n * q) ℤ = expand ℤ p₀ (cyclotomic (r * q) ℤ) := by
                rw [← hm_eq, hm_rq, ← cyclotomic_expand_eq_cyclotomic hp₀ hp₀rq ℤ]
              have htot : r.totient * p₀ = n.totient := by
                rw [hn_eq, mul_comm r p₀, Nat.totient_mul_of_dvd hp₀r, mul_comm]
              rw [hΦn, hΦm', resultant_expand, h_rq, ← pow_mul, htot]
            · have hp₀rq : ¬ p₀ ∣ r * q := fun h ↦
                (hp₀.dvd_mul.mp h).elim hp₀r fun h2 ↦
                  hp₀q ((Nat.prime_dvd_prime_iff_eq hp₀ hq).mp h2)
              have hexp_rq :
                  expand ℤ p₀ (cyclotomic (r * q) ℤ) =
                    cyclotomic (n * q) ℤ * cyclotomic (r * q) ℤ := by
                rw [← hm_eq, hm_rq, cyclotomic_expand_eq_cyclotomic_mul hp₀ hp₀rq ℤ]
              have h_exp_val :
                  (cyclotomic n ℤ).resultant (expand ℤ p₀ (cyclotomic (r * q) ℤ)) =
                    (q : ℤ) ^ n.totient := by
                rw [hn_eq, resultant_cyclotomic_mul_prime_expand hr_pos hp₀ _ h_rq_ne, h_rq,
                  ← pow_mul, Nat.mul_div_cancel' (Nat.totient_dvd_of_dvd (dvd_mul_right r p₀)),
                  ← hn_eq]
              have hnrq_ne : n ≠ r * q := fun h ↦ by
                rw [hn_eq] at h
                exact hp₀q (mul_left_cancel₀ hr_pos.ne' h)
              have hn2 : 2 ≤ n := by
                rw [hn_eq]
                exact le_trans hp₀.two_le (Nat.le_mul_of_pos_left p₀ hr_pos)
              have hrq2 : 2 ≤ r * q :=
                le_trans hq.two_le (Nat.le_mul_of_pos_left q hr_pos)
              have hmax : 2 < max n (r * q) := by omega
              have hnot_nrq : ¬ n ∣ r * q := fun h ↦ by
                rw [hn_eq, mul_dvd_mul_iff_left hr_pos.ne'] at h
                exact hp₀q ((Nat.prime_dvd_prime_iff_eq hp₀ hq).mp h)
              have hnot_rqn : ¬ r * q ∣ n := fun h ↦ by
                rw [hn_eq, mul_dvd_mul_iff_left hr_pos.ne'] at h
                exact hp₀q.symm ((Nat.prime_dvd_prime_iff_eq hq hp₀).mp h)
              have h_nrq_one : (cyclotomic n ℤ).resultant (cyclotomic (r * q) ℤ) = 1 :=
                ih_eq_one hn hnm hrq_pos hrq_lt hnrq_ne hmax hnot_nrq hnot_rqn
              rw [hexp_rq, resultant_mul_right_of_monic _ (cyclotomic.monic (n * q) ℤ)
                (cyclotomic.monic (r * q) ℤ), h_nrq_one, mul_one] at h_exp_val
              exact h_exp_val
        · have hmul :
              (cyclotomic n ℤ).resultant (cyclotomic m ℤ) *
                  (cyclotomic n ℤ).resultant (cyclotomic s ℤ) =
                1 * (cyclotomic n ℤ).resultant (cyclotomic s ℤ) := by
            rw [one_mul,
              ← resultant_mul_right_of_monic _ (cyclotomic.monic m ℤ) (cyclotomic.monic s ℤ),
              ← hexp, resultant_cyclotomic_int_expand_of_coprime (hq.coprime_iff_not_dvd.mpr hqn)]
          have h_lhs_one : (cyclotomic n ℤ).resultant (cyclotomic m ℤ) = 1 :=
            mul_right_cancel₀ (ih_ne_zero hn hnm hs_pos hs_lt hns_ne) hmul
          rw [h_lhs_one]
          unfold cyclotomicResultantInt
          symm
          refine ite_eq_right fun ⟨hnm_dvd, hpp⟩ ↦ ?_
          rw [hm_eq] at hnm_dvd hpp
          have hns_dvd : n ∣ s :=
            (hq.coprime_iff_not_dvd.mpr hqn).symm.dvd_of_dvd_mul_right hnm_dvd
          set d := s / n
          have hs_dn : s = d * n := (Nat.div_mul_cancel hns_dvd).symm
          have hdiv_eq : s * q / n = d * q := by
            rw [hs_dn, mul_right_comm, Nat.mul_div_cancel _ hn]
          rw [hdiv_eq] at hpp
          obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff (d * q)).mp hpp
          have hqp : q = p :=
            (Nat.prime_dvd_prime_iff_eq hq hp).mp
              (hq.dvd_of_dvd_pow (hpk ▸ dvd_mul_left q d))
          rw [← hqp] at hpk
          rcases eq_or_ne k 1 with rfl | hk1
          · rw [pow_one] at hpk
            have hd1 : d = 1 := mul_right_cancel₀ hq.ne_zero (by simpa using hpk.symm)
            rw [hd1, one_mul] at hs_dn
            exact hns_ne hs_dn.symm
          · have hk2 : 2 ≤ k := by omega
            have hqd : q ∣ d := by
              refine ⟨q ^ (k - 2), ?_⟩
              apply mul_right_cancel₀ hq.ne_zero
              calc d * q = q ^ k := hpk.symm
                _ = q * q ^ (k - 2) * q := by
                  rw [mul_assoc, mul_comm (q ^ (k - 2)) q, ← mul_assoc, ← sq, ← pow_add,
                    show 2 + (k - 2) = k by omega]
            exact hqs (hs_dn ▸ dvd_mul_of_dvd_left hqd n)

private theorem resultant_cyclotomic_map_int (R : Type*) [CommRing R] [Nontrivial R] (m n : ℕ) :
    (cyclotomic m R).resultant (cyclotomic n R) =
      Int.castRingHom R ((cyclotomic m ℤ).resultant (cyclotomic n ℤ)) := by
  rw [← map_cyclotomic_int m R, ← map_cyclotomic_int n R,
    resultant_map_of_natDegree_eq (Int.castRingHom R)
      ((cyclotomic.monic m ℤ).natDegree_map _)
      ((cyclotomic.monic n ℤ).natDegree_map _)]

end Helpers

section ResultantFormula

variable {R : Type*} [CommRing R]

/-- **Apostol's cyclotomic resultant formula** (`0 < n < m`). Over any commutative ring `R`,
`Res(Φ_n, Φ_m) = p ^ φ(n)` when `m / n = p ^ e` is a prime power (`e ≥ 1`), and `1` otherwise. -/
theorem resultant_cyclotomic_of_lt {n m : ℕ} (hn : 0 < n) (hnm : n < m) :
    (cyclotomic n R).resultant (cyclotomic m R) =
      if n ∣ m ∧ IsPrimePow (m / n) then ((m / n).minFac : R) ^ n.totient else 1 := by
  nontriviality R
  rw [resultant_cyclotomic_map_int, resultant_cyclotomic_int_of_lt hn hnm]
  unfold cyclotomicResultantInt
  split_ifs <;> simp

/-- **Resultant of prime-power-adjacent cyclotomic polynomials.** Over any commutative ring `R`,
for a prime `p`, `0 < e`, and `0 < n`, `Res(Φ_n, Φ_{p ^ e n}) = p ^ φ(n)`. -/
theorem resultant_cyclotomic_prime_pow_mul {p e n : ℕ} (hp : p.Prime) (he : 0 < e) (hn : 0 < n) :
    (cyclotomic n R).resultant (cyclotomic (p ^ e * n) R) = (p : R) ^ n.totient := by
  have hlt : n < p ^ e * n := lt_mul_of_one_lt_left hn (one_lt_pow₀ hp.one_lt he.ne')
  have hdiv : p ^ e * n / n = p ^ e := Nat.mul_div_cancel _ hn
  have hcond : n ∣ p ^ e * n ∧ IsPrimePow (p ^ e * n / n) := by
    rw [hdiv]
    exact ⟨dvd_mul_left n (p ^ e), (isPrimePow_nat_iff _).mpr ⟨p, e, hp, he, rfl⟩⟩
  rw [resultant_cyclotomic_of_lt hn hlt, ite_eq_left hcond, hdiv, minFac_prime_pow hp he]

/-- Explicit `Res(Φ_n, Φ_m) = 1` form of `Polynomial.resultant_cyclotomic_of_lt` when `0 < n < m`
and `m / n` is not a prime power. -/
theorem resultant_cyclotomic_eq_one_of_lt {n m : ℕ} (hn : 0 < n) (hnm : n < m)
    (h : ¬ (n ∣ m ∧ IsPrimePow (m / n))) :
    (cyclotomic n R).resultant (cyclotomic m R) = 1 := by
  rw [resultant_cyclotomic_of_lt hn hnm, ite_eq_right h]

/-- At `(m, n) = (2, 1)`, both `φ(2) = 1` and `φ(1) = 1` are odd, so swapping `Φ_1 = X - 1` and
`Φ_2 = X + 1` introduces a minus sign: `Res(Φ_2, Φ_1) = -2`. -/
theorem resultant_cyclotomic_two_one :
    (cyclotomic 2 R).resultant (cyclotomic 1 R) = -2 := by
  nontriviality R
  have h12 : (cyclotomic 1 R).resultant (cyclotomic 2 R) = 2 := by
    simpa using resultant_cyclotomic_prime_pow_mul (R := R) Nat.prime_two Nat.one_pos Nat.one_pos
  have hdeg : (cyclotomic 2 R).natDegree * (cyclotomic 1 R).natDegree = 1 := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic, Nat.totient_two, Nat.totient_one]
  rw [resultant_comm, hdeg, pow_one, h12]
  ring

/-- Whenever `2 < m`, `φ(m)` is even, so `Res(Φ_m, Φ_n) = Res(Φ_n, Φ_m)` for every `n : ℕ`
(including `n = 0` and `n = m`). -/
theorem resultant_cyclotomic_comm_of_two_lt {m : ℕ} (hm : 2 < m) (n : ℕ) :
    (cyclotomic m R).resultant (cyclotomic n R) =
      (cyclotomic n R).resultant (cyclotomic m R) := by
  nontriviality R
  have heven : Even ((cyclotomic m R).natDegree * (cyclotomic n R).natDegree) := by
    rw [natDegree_cyclotomic]
    exact (Nat.totient_even hm).mul_right _
  rw [resultant_comm, Even.neg_one_pow heven, one_mul]

/-- Swapped-order companion to `Polynomial.resultant_cyclotomic_prime_pow_mul`:
`Res(Φ_{p ^ e n}, Φ_n) = p ^ φ(n)` except at the unique case `p ^ e * n = 2` (`p = 2, e = 1,
n = 1`), where it equals `-2`. -/
theorem resultant_cyclotomic_prime_pow_mul_left {p e n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hn : 0 < n) :
    (cyclotomic (p ^ e * n) R).resultant (cyclotomic n R) =
      if p ^ e * n = 2 then -2 else (p : R) ^ n.totient := by
  have hge2 : 2 ≤ p ^ e * n := by
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ e := Nat.le_self_pow he.ne' p
      _ ≤ p ^ e * n := Nat.le_mul_of_pos_right _ hn
  by_cases h2 : p ^ e * n = 2
  · rw [ite_eq_left h2]
    have hn1 : n = 1 := by
      by_contra hn1
      have hn2 : 2 ≤ n := by omega
      have hpe2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow he.ne' p)
      have : 4 ≤ p ^ e * n := Nat.mul_le_mul hpe2 hn2
      omega
    rw [h2, hn1, resultant_cyclotomic_two_one]
  · rw [ite_eq_right h2, resultant_cyclotomic_comm_of_two_lt (by omega),
      resultant_cyclotomic_prime_pow_mul hp he hn]

/-- **Symmetric unit resultant when orders do not differ by a prime power.** Over any commutative
ring `R` and for all `m, n : ℕ` (including `0`, where `Φ_0 = 1`) with `m ≠ n`, if neither `m / n`
nor `n / m` is a prime power (`m ≠ p ^ e n` and `n ≠ p ^ e m` for every prime `p` and `e > 0`),
then `Res(Φ_m, Φ_n) = 1`. No `-1` sign appears because `{m, n} = {1, 2}` has `2 = 2 ^ 1 * 1`. -/
theorem resultant_cyclotomic_eq_one_of_not_prime_pow_ratio {m n : ℕ} (hmn : m ≠ n)
    (h : ∀ p e : ℕ, p.Prime → 0 < e → m ≠ p ^ e * n ∧ n ≠ p ^ e * m) :
    (cyclotomic m R).resultant (cyclotomic n R) = 1 := by
  nontriviality R
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnot_lt : ∀ {a b : ℕ}, a < b →
      (∀ p e : ℕ, p.Prime → 0 < e → b ≠ p ^ e * a) → ¬ (a ∣ b ∧ IsPrimePow (b / a)) := by
    rintro a b _ hba ⟨hab_dvd, hpp⟩
    obtain ⟨p, e, hp, he, hpe⟩ := (isPrimePow_nat_iff (b / a)).mp hpp
    refine hba p e hp he ?_
    rw [hpe, Nat.div_mul_cancel hab_dvd]
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact resultant_cyclotomic_eq_one_of_lt hm_pos hlt (hnot_lt hlt fun p e hp he ↦ (h p e hp he).2)
  · have hm2 : 2 < m := by
      by_contra hm_le
      have h21 : m = 2 ^ 1 * n := by omega
      exact (h 2 1 Nat.prime_two Nat.one_pos).1 h21
    rw [resultant_cyclotomic_comm_of_two_lt hm2,
      resultant_cyclotomic_eq_one_of_lt hn_pos hgt (hnot_lt hgt fun p e hp he ↦ (h p e hp he).1)]

/-- **Symmetric magnitude of integer cyclotomic resultants.** For all positive `m ≠ n`,
`|Res(Φ_m, Φ_n)|` equals `p ^ φ(min m n)` if `max m n / min m n = p ^ e` is a prime power, and `1`
otherwise. -/
theorem natAbs_resultant_cyclotomic {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    ((cyclotomic m ℤ).resultant (cyclotomic n ℤ)).natAbs =
      if min m n ∣ max m n ∧ IsPrimePow (max m n / min m n) then
        (max m n / min m n).minFac ^ (min m n).totient
      else 1 := by
  have helper : ∀ {a b : ℕ}, 0 < a → a < b →
      ((cyclotomic a ℤ).resultant (cyclotomic b ℤ)).natAbs =
        if a ∣ b ∧ IsPrimePow (b / a) then (b / a).minFac ^ a.totient else 1 := by
    intro a b ha hab
    rw [resultant_cyclotomic_of_lt ha hab]
    split_ifs <;> simp
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    exact helper hm hlt
  · rw [min_eq_right hgt.le, max_eq_left hgt.le, resultant_comm, Int.natAbs_mul,
      Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
    exact helper hn hgt

/-- Magnitude companion to `Polynomial.resultant_cyclotomic_prime_pow_mul` in either order. -/
theorem natAbs_resultant_cyclotomic_prime_pow_mul {p e n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hn : 0 < n) :
    ((cyclotomic n ℤ).resultant (cyclotomic (p ^ e * n) ℤ)).natAbs = p ^ n.totient := by
  rw [resultant_cyclotomic_prime_pow_mul hp he hn]
  simp

end ResultantFormula

section Comaximality

variable {R : Type*} [CommRing R]

/-- **Comaximality of cyclotomic polynomials whose orders do not differ by a prime power.** Over any
commutative ring `R` and for all `m ≠ n : ℕ` (including `0`), if `m ≠ p ^ e * n` and `n ≠ p ^ e * m`
for every prime `p` and `0 < e`, then `Φ_m` and `Φ_n` generate the unit ideal in `R[X]`. -/
theorem isCoprime_cyclotomic_of_not_prime_pow_ratio {m n : ℕ} (hmn : m ≠ n)
    (h : ∀ p e : ℕ, p.Prime → 0 < e → m ≠ p ^ e * n ∧ n ≠ p ^ e * m) :
    IsCoprime (cyclotomic m R) (cyclotomic n R) := by
  rw [← isUnit_resultant_iff_isCoprime (cyclotomic.monic m R),
    resultant_cyclotomic_eq_one_of_not_prime_pow_ratio hmn h]
  exact isUnit_one

/-- **Comaximality criterion for prime-power-adjacent cyclotomic polynomials.** Over any commutative
ring `R`, for a prime `p`, `0 < e`, and `0 < n`, `Φ_n` and `Φ_{p ^ e n}` are coprime in `R[X]` if
and only if `p` is a unit in `R`. -/
theorem isCoprime_cyclotomic_prime_pow_mul_iff {p e n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hn : 0 < n) :
    IsCoprime (cyclotomic n R) (cyclotomic (p ^ e * n) R) ↔ IsUnit (p : R) := by
  rw [← isUnit_resultant_iff_isCoprime (cyclotomic.monic n R),
    resultant_cyclotomic_prime_pow_mul hp he hn,
    isUnit_pow_iff (Nat.totient_pos.mpr hn).ne']

/-- **General comaximality characterization for distinct positive cyclotomic orders.** Over any
commutative ring `R` (without nontriviality or characteristic assumptions), for `0 < m`, `0 < n`,
and `m ≠ n`, `Φ_m` and `Φ_n` are coprime in `R[X]` if and only if every prime `p` relating `m` and
`n` by `m = p ^ e * n` or `n = p ^ e * m` (`0 < e`) is a unit in `R`. -/
theorem isCoprime_cyclotomic_iff_of_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    IsCoprime (cyclotomic m R) (cyclotomic n R) ↔
      ∀ p e : ℕ, p.Prime → 0 < e → m = p ^ e * n ∨ n = p ^ e * m → IsUnit (p : R) := by
  constructor
  · intro hcop p e hp he hrel
    rcases hrel with rfl | rfl
    · exact (isCoprime_cyclotomic_prime_pow_mul_iff hp he hn).mp hcop.symm
    · exact (isCoprime_cyclotomic_prime_pow_mul_iff hp he hm).mp hcop
  · intro hunit
    by_cases hrel : ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ (m = p ^ e * n ∨ n = p ^ e * m)
    · obtain ⟨p, e, hp, he, hpe⟩ := hrel
      have hp_unit : IsUnit (p : R) := hunit p e hp he hpe
      rcases hpe with rfl | rfl
      · exact ((isCoprime_cyclotomic_prime_pow_mul_iff hp he hn).mpr hp_unit).symm
      · exact (isCoprime_cyclotomic_prime_pow_mul_iff hp he hm).mpr hp_unit
    · refine isCoprime_cyclotomic_of_not_prime_pow_ratio hmn fun p e hp he ↦ ?_
      exact ⟨fun h1 ↦ hrel ⟨p, e, hp, he, Or.inl h1⟩, fun h2 ↦ hrel ⟨p, e, hp, he, Or.inr h2⟩⟩

/-- **Full comaximality characterization over any nontrivial commutative ring.** For `0 < m` and
`0 < n` over `[CommRing R] [Nontrivial R]`, `Φ_m` and `Φ_n` are coprime in `R[X]` if and only if
`m ≠ n` and every prime `p` with `m = p ^ e * n` or `n = p ^ e * m` (`0 < e`) is a unit in `R`.
Nontriviality is sharp at `m = n`: in the zero ring `IsCoprime` holds trivially for every pair. -/
theorem isCoprime_cyclotomic_iff [Nontrivial R] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsCoprime (cyclotomic m R) (cyclotomic n R) ↔
      m ≠ n ∧ ∀ p e : ℕ, p.Prime → 0 < e → m = p ^ e * n ∨ n = p ^ e * m → IsUnit (p : R) := by
  rcases eq_or_ne m n with rfl | hmn
  · simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    rw [← isUnit_resultant_iff_isCoprime (cyclotomic.monic m R),
      resultant_self_eq_zero _ (by rw [natDegree_cyclotomic]; exact (Nat.totient_pos.mpr hm).ne')]
    exact not_isUnit_zero
  · exact ⟨fun h ↦ ⟨hmn, (isCoprime_cyclotomic_iff_of_ne hm hn hmn).mp h⟩,
      fun h ↦ (isCoprime_cyclotomic_iff_of_ne hm hn hmn).mpr h.2⟩

/-- **Exact comaximality characterization over `ℤ` (Habiro 2004, §5).** For `0 < m` and `0 < n`,
`Φ_m` and `Φ_n` are coprime in `ℤ[X]` if and only if `m ≠ n` and neither `m / n` nor `n / m` is a
prime power (`m ≠ p ^ e * n` and `n ≠ p ^ e * m` for all primes `p` and `0 < e`). -/
theorem isCoprime_cyclotomic_int_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsCoprime (cyclotomic m ℤ) (cyclotomic n ℤ) ↔
      m ≠ n ∧ ∀ p e : ℕ, p.Prime → 0 < e → m ≠ p ^ e * n ∧ n ≠ p ^ e * m := by
  rw [isCoprime_cyclotomic_iff hm hn]
  refine and_congr_right fun _ ↦ ⟨fun h p e hp he ↦ ?_, fun h p e hp he hrel ↦ ?_⟩
  · have hnot_unit : ¬ IsUnit (p : ℤ) := by
      rw [Int.isUnit_iff]
      have := hp.two_le
      omega
    exact ⟨fun h1 ↦ hnot_unit (h p e hp he (Or.inl h1)),
      fun h2 ↦ hnot_unit (h p e hp he (Or.inr h2))⟩
  · exact False.elim (hrel.elim (h p e hp he).1 (h p e hp he).2)

end Comaximality

end Polynomial
