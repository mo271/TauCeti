/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Multinomial upper bounds for elementary symmetric sums over `Finset.powersetCard`

For nonnegative weights `f` on a finite set `s`, each `n`-element subset `t ∈ s.powersetCard n`
appears `n!` times in the expansion of `(∑ x ∈ s, f x) ^ n`, while diagonal terms with repeated
indices are nonnegative and may be dropped. This file proves the resulting ordered-semiring bound
`n! • ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n` and its divided form in ordered
semifields.

## Main results

* `Finset.factorial_nsmul_sum_powersetCard_prod_le_pow_sum`: in an ordered commutative semiring,
  `n.factorial • ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n` when `0 ≤ f x` on `s`.
* `Finset.sum_powersetCard_prod_le_pow_sum_div_factorial`: the corresponding quotient bound
  `∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n / n.factorial` in a linearly ordered
  semifield.
-/

public section

namespace Finset

private theorem card_succ_nsmul_sum_powersetCard_prod_le {ι R : Type*}
    [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    (s : Finset ι) (n : ℕ) {f : ι → R} (hf : ∀ x ∈ s, 0 ≤ f x) :
    (n + 1) • ∑ t ∈ s.powersetCard (n + 1), ∏ x ∈ t, f x ≤
      (∑ a ∈ s, f a) * ∑ u ∈ s.powersetCard n, ∏ x ∈ u, f x := by
  classical
  have hstep : (n + 1) • ∑ t ∈ s.powersetCard (n + 1), ∏ x ∈ t, f x =
      ∑ a ∈ s, f a * ∑ t ∈ (s.powersetCard (n + 1)).filter (a ∈ ·), ∏ x ∈ t.erase a, f x := by
    calc
      (n + 1) • ∑ t ∈ s.powersetCard (n + 1), ∏ x ∈ t, f x
        = ∑ t ∈ s.powersetCard (n + 1), (n + 1) • ∏ x ∈ t, f x := by
            simp only [nsmul_eq_mul, mul_sum]
      _ = ∑ t ∈ s.powersetCard (n + 1), ∑ a ∈ t, f a * ∏ x ∈ t.erase a, f x := by
            refine sum_congr rfl fun t ht ↦ ?_
            rw [← (mem_powersetCard.mp ht).2, ← sum_const]
            exact sum_congr rfl fun a ha ↦ (mul_prod_erase t f ha).symm
      _ = ∑ t ∈ s.powersetCard (n + 1),
            ∑ a ∈ s, if a ∈ t then f a * ∏ x ∈ t.erase a, f x else 0 := by
            refine sum_congr rfl fun t ht ↦ ?_
            rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (mem_powersetCard.mp ht).1]
      _ = ∑ a ∈ s, f a * ∑ t ∈ (s.powersetCard (n + 1)).filter (a ∈ ·), ∏ x ∈ t.erase a, f x := by
            rw [sum_comm]
            refine sum_congr rfl fun a _ ↦ ?_
            rw [mul_sum, sum_filter]
  rw [hstep, sum_mul]
  refine sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_left ?_ (hf a ha)
  have himg : (s.powersetCard (n + 1)).filter (a ∈ ·) =
      ((s.erase a).powersetCard n).image (insert a) := by
    ext t
    simp only [mem_filter, mem_powersetCard, mem_image]
    constructor
    · rintro ⟨⟨hts, htc⟩, hat⟩
      exact ⟨t.erase a, ⟨subset_erase.mpr ⟨(erase_subset a t).trans hts, notMem_erase a t⟩,
        by rw [card_erase_of_mem hat, htc, Nat.add_sub_cancel]⟩, insert_erase hat⟩
    · rintro ⟨u, ⟨hus, huc⟩, rfl⟩
      have hau : a ∉ u := fun h ↦ notMem_erase a s (hus h)
      exact ⟨⟨insert_subset ha (hus.trans (erase_subset a s)),
        by rw [card_insert_of_notMem hau, huc]⟩, mem_insert_self a u⟩
  rw [himg, sum_image]
  · calc
      ∑ u ∈ (s.erase a).powersetCard n, ∏ x ∈ (insert a u).erase a, f x
        = ∑ u ∈ (s.erase a).powersetCard n, ∏ x ∈ u, f x := by
            refine sum_congr rfl fun u hu ↦ ?_
            have hau : a ∉ u := fun h ↦ notMem_erase a s ((mem_powersetCard.mp hu).1 h)
            rw [erase_insert hau]
      _ ≤ ∑ u ∈ s.powersetCard n, ∏ x ∈ u, f x :=
            sum_le_sum_of_subset_of_nonneg (powersetCard_mono (erase_subset a s))
              fun u hu _ ↦ prod_nonneg fun x hx ↦ hf x ((mem_powersetCard.mp hu).1 hx)
  · intro u₁ hu₁ u₂ hu₂ hins
    have h₁ : a ∉ u₁ := fun h ↦ notMem_erase a s ((mem_powersetCard.mp hu₁).1 h)
    have h₂ : a ∉ u₂ := fun h ↦ notMem_erase a s ((mem_powersetCard.mp hu₂).1 h)
    simpa only [erase_insert h₁, erase_insert h₂] using congrArg (erase · a) hins

/-- In an ordered commutative semiring, `n!` times the `n`-th elementary symmetric sum of
nonnegative weights on `s` is at most `(∑ x ∈ s, f x) ^ n`. -/
theorem factorial_nsmul_sum_powersetCard_prod_le_pow_sum {ι R : Type*}
    [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    (s : Finset ι) (n : ℕ) {f : ι → R} (hf : ∀ x ∈ s, 0 ≤ f x) :
    n.factorial • ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hS : 0 ≤ ∑ x ∈ s, f x := sum_nonneg hf
      rw [Nat.factorial_succ, mul_comm, mul_nsmul']
      calc
        n.factorial • ((n + 1) • ∑ t ∈ s.powersetCard (n + 1), ∏ x ∈ t, f x)
          ≤ n.factorial • ((∑ a ∈ s, f a) * ∑ u ∈ s.powersetCard n, ∏ x ∈ u, f x) :=
              nsmul_le_nsmul_right (card_succ_nsmul_sum_powersetCard_prod_le s n hf) _
        _ = (∑ a ∈ s, f a) * (n.factorial • ∑ u ∈ s.powersetCard n, ∏ x ∈ u, f x) := by
              simp only [nsmul_eq_mul, mul_left_comm]
        _ ≤ (∑ a ∈ s, f a) * (∑ a ∈ s, f a) ^ n := mul_le_mul_of_nonneg_left ih hS
        _ = (∑ a ∈ s, f a) ^ (n + 1) := (pow_succ' _ _).symm

/-- In a linearly ordered semifield, the `n`-th elementary symmetric sum of nonnegative weights on
`s` is at most `(∑ x ∈ s, f x) ^ n / n!`. -/
theorem sum_powersetCard_prod_le_pow_sum_div_factorial {ι K : Type*}
    [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    (s : Finset ι) (n : ℕ) {f : ι → K} (hf : ∀ x ∈ s, 0 ≤ f x) :
    ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n / n.factorial := by
  have hfac : (0 : K) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
  rw [le_div_iff₀ hfac, mul_comm]
  simpa only [nsmul_eq_mul] using factorial_nsmul_sum_powersetCard_prod_le_pow_sum s n hf

end Finset
