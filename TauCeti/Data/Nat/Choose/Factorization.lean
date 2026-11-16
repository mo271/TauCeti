/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Prime-power carries and `p`-adic valuations of binomial coefficients

For a modulus `m` and a lower index `k < m` with `k ≤ n`, subtracting `k` from `n` borrows across
`m` — equivalently, adding `k % m` and `(n - k) % m` produces a carry of size `m` — exactly when
`n % m < k`. Specializing Kummer's carry count `Nat.factorization_choose` to prime-power moduli
`m = p ^ j` yields three consequences for a prime `p`:

* If `p ^ r ∣ k₁`, `k₁ ≤ k₂ < p ^ (r + 1)` and `k₂ ≤ n`, every base-`p` carry for `n choose k₁`
  occurs at a position `j ≥ r + 1` and persists for `n choose k₂`, so the `p`-adic valuation of
  `n choose k₁` is at most that of `n choose k₂`.
* If `p ^ w ∣ n` and `0 < k < p ^ w`, position `w` always carries, so `p ∣ n choose k`.
* By Lucas' theorem on `p ^ w`-blocks, `p ∣ (a * p ^ w) choose (p ^ w)` holds if and only if
  `p ∣ a`.

## Main results

* `Nat.Prime.factorization_choose_le_of_dvd_of_lt`: if `p ^ r ∣ k₁`, `k₁ ≤ k₂ < p ^ (r + 1)` and
  `k₂ ≤ n`, then `(n.choose k₁).factorization p ≤ (n.choose k₂).factorization p`.
* `Nat.Prime.factorization_choose_pow_le`: specialization to `k₁ = p ^ r`, bounding the `p`-adic
  valuation of `n choose k` on `[p ^ r, p ^ (r + 1))` below by that of `n choose (p ^ r)`.
* `Nat.Prime.dvd_choose_of_pow_dvd`: if `p ^ w ∣ n` and `0 < k < p ^ w`, then `p ∣ n.choose k`.
* `Nat.Prime.dvd_choose_mul_pow_iff`: `p ∣ (a * p ^ w).choose (p ^ w) ↔ p ∣ a`.

## References

* E. E. Kummer, *Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen*,
  J. Reine Angew. Math. **44** (1852), 93–146.
-/

public section

namespace Nat.Prime

/-- For `k ≤ n` and `k < m`, the addition of `k % m` and `(n - k) % m` reaches `m` if and only if
`n % m < k`. -/
private theorem carry_iff_mod_lt {m n k : ℕ} (hkn : k ≤ n) (hkm : k < m) :
    m ≤ k % m + (n - k) % m ↔ n % m < k := by
  have hm0 : 0 < m := Nat.zero_lt_of_lt hkm
  have hmod : n % m < m := Nat.mod_lt n hm0
  have hdiv : m * (n / m) + n % m = n := Nat.div_add_mod n m
  rw [Nat.mod_eq_of_lt hkm]
  rcases lt_or_ge (n % m) k with hlt | hge
  · have hq : 1 ≤ n / m := by
      by_contra! hq0
      have h0 : n / m = 0 := Nat.lt_one_iff.mp hq0
      rw [h0, mul_zero, zero_add] at hdiv
      omega
    have hmul : m * (n / m) = m * (n / m - 1) + m := by
      conv_lhs => rw [← Nat.sub_add_cancel hq, mul_add, mul_one]
    have hsub : n - k = (m + n % m - k) + m * (n / m - 1) := by omega
    rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    exact iff_of_true (by omega) hlt
  · have hsub : n - k = (n % m - k) + m * (n / m) := by omega
    rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    exact iff_of_false (by omega) (not_lt.mpr hge)

/-- **Carry domination on `[p ^ r, p ^ (r + 1))`.** If `p` is prime, `p ^ r ∣ k₁`,
`k₁ ≤ k₂ < p ^ (r + 1)` and `k₂ ≤ n`, then the `p`-adic valuation of `n choose k₁` is at most that
of `n choose k₂`. -/
theorem factorization_choose_le_of_dvd_of_lt {p r k₁ k₂ n : ℕ} (hp : p.Prime)
    (hdvd : p ^ r ∣ k₁) (hle : k₁ ≤ k₂) (hlt : k₂ < p ^ (r + 1)) (hkn : k₂ ≤ n) :
    (n.choose k₁).factorization p ≤ (n.choose k₂).factorization p := by
  rw [Nat.factorization_choose hp (hle.trans hkn) (Nat.lt_succ_self _),
    Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  refine Finset.card_le_card fun j hj ↦ ?_
  obtain ⟨hjIco, hcarry⟩ := Finset.mem_filter.mp hj
  rcases le_or_gt j r with hjr | hjr
  · have hmod0 : k₁ % p ^ j = 0 :=
      Nat.mod_eq_zero_of_dvd ((Nat.pow_dvd_pow p hjr).trans hdvd)
    have hlt' : (n - k₁) % p ^ j < p ^ j := Nat.mod_lt _ (pow_pos hp.pos _)
    omega
  · have hpj : p ^ (r + 1) ≤ p ^ j := Nat.pow_le_pow_right hp.pos hjr
    refine Finset.mem_filter.mpr ⟨hjIco, (carry_iff_mod_lt hkn (hlt.trans_le hpj)).mpr ?_⟩
    exact ((carry_iff_mod_lt (hle.trans hkn) (hle.trans_lt (hlt.trans_le hpj))).mp hcarry).trans_le
      hle

/-- For `p` prime and `p ^ r ≤ k < p ^ (r + 1)` with `k ≤ n`, the `p`-adic valuation of
`n choose (p ^ r)` is at most that of `n choose k`. -/
theorem factorization_choose_pow_le {p r k n : ℕ} (hp : p.Prime) (hrk : p ^ r ≤ k)
    (hkp : k < p ^ (r + 1)) (hkn : k ≤ n) :
    (n.choose (p ^ r)).factorization p ≤ (n.choose k).factorization p :=
  hp.factorization_choose_le_of_dvd_of_lt dvd_rfl hrk hkp hkn

/-- If `p` is prime, `p ^ w ∣ n` and `0 < k < p ^ w`, then `p` divides `n choose k`. -/
theorem dvd_choose_of_pow_dvd {p w n k : ℕ} (hp : p.Prime) (hn : p ^ w ∣ n) (hk0 : 0 < k)
    (hkp : k < p ^ w) : p ∣ n.choose k := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [Nat.choose_eq_zero_of_lt hnk]
    exact dvd_zero p
  have hw0 : 1 ≤ w := by
    rcases w with _ | w
    · rw [pow_zero] at hkp
      omega
    · exact Nat.succ_pos w
  rw [hp.dvd_iff_one_le_factorization (Nat.choose_pos hkn).ne',
    Nat.factorization_choose hp hkn
      (lt_max_of_lt_left (Nat.lt_succ_self _) : Nat.log p n < max (Nat.log p n + 1) (w + 1))]
  refine Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hw0, ?_⟩, ?_⟩⟩
  · exact lt_max_of_lt_right (Nat.lt_succ_self w)
  · rw [carry_iff_mod_lt hkn hkp, Nat.mod_eq_zero_of_dvd hn]
    exact hk0

/-- For `p` prime, `p` divides `(a * p ^ w) choose (p ^ w)` if and only if `p` divides `a`. -/
theorem dvd_choose_mul_pow_iff {p a w : ℕ} (hp : p.Prime) :
    p ∣ (a * p ^ w).choose (p ^ w) ↔ p ∣ a := by
  have : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := w) (a := a) (b := 1)
  rw [mul_comm (p ^ w) a, mul_one, Nat.choose_one_right] at h
  exact h.dvd_iff dvd_rfl

end Nat.Prime
