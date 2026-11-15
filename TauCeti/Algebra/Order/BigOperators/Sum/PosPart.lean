/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.MinMax

/-!
# Positive and negative parts of a balanced sum

When a finite sum in a linearly ordered additive commutative group is zero, its total negative
part equals its total positive part, and twice its total positive part equals its total absolute
value. Applied to the difference of two finite families with equal sums, total surplus equals total
deficit and twice the total deficit equals the `ℓ¹` distance. This expresses the balance of supply
and demand without requiring multiplication, an Archimedean property, or order completeness.
-/

public section

namespace Finset

variable {ι K : Type*} [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]

/-- A balanced finite family has equal total negative and positive parts. -/
theorem sum_max_neg_eq_sum_max (s : Finset ι) (b : ι → K) (hb : ∑ v ∈ s, b v = 0) :
    ∑ v ∈ s, max (-b v) 0 = ∑ v ∈ s, max (b v) 0 := by
  have h : (∑ v ∈ s, max (b v) 0) - ∑ v ∈ s, max (-b v) 0 = 0 := by
    rw [← sum_sub_distrib]
    simpa only [max_zero_sub_max_neg_zero_eq_self] using hb
  exact (sub_eq_zero.1 h).symm

/-- Twice the total positive part of a balanced finite family equals its total absolute value. -/
theorem two_nsmul_sum_max_eq_sum_abs (s : Finset ι) (b : ι → K) (hb : ∑ v ∈ s, b v = 0) :
    2 • ∑ v ∈ s, max (b v) 0 = ∑ v ∈ s, |b v| := by
  calc 2 • ∑ v ∈ s, max (b v) 0
      = ∑ v ∈ s, max (b v) 0 + ∑ v ∈ s, max (-b v) 0 := by
          rw [two_nsmul, s.sum_max_neg_eq_sum_max b hb]
    _ = ∑ v ∈ s, |b v| := by
          rw [← sum_add_distrib]
          simp only [max_zero_add_max_neg_zero_eq_abs_self]

/-- Two finite families with equal sums have equal total surplus and total deficit. -/
theorem sum_max_sub_eq_sum_max_sub (s : Finset ι) {f g : ι → K}
    (hfg : ∑ v ∈ s, f v = ∑ v ∈ s, g v) :
    ∑ v ∈ s, max (f v - g v) 0 = ∑ v ∈ s, max (g v - f v) 0 := by
  simpa only [neg_sub] using
    s.sum_max_neg_eq_sum_max (fun v ↦ g v - f v) (by rw [sum_sub_distrib, hfg, sub_self])

/-- Twice the total deficit between two finite families with equal sums equals their `ℓ¹` distance.
-/
theorem two_nsmul_sum_max_sub_eq_sum_abs_sub (s : Finset ι) {f g : ι → K}
    (hfg : ∑ v ∈ s, f v = ∑ v ∈ s, g v) :
    2 • ∑ v ∈ s, max (g v - f v) 0 = ∑ v ∈ s, |f v - g v| := by
  simpa only [abs_sub_comm] using
    s.two_nsmul_sum_max_eq_sum_abs (fun v ↦ g v - f v) (by rw [sum_sub_distrib, hfg, sub_self])

end Finset
