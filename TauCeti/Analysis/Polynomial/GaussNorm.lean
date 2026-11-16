/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Order.Lattice

/-!
# Gauss-norm bounds and convergence for polynomials of bounded degree

For a polynomial `p` of natural degree at most `d` over a seminormed ring `R`, the power-series
Gauss norm `(p : R⟦X⟧).gaussNorm norm c` only sees the finitely many coefficients in degrees at
most `d`. At a nonnegative radius `c ≥ 0` it equals the maximum of `‖p.coeff k‖ * c ^ k` over
`k ∈ range (d + 1)`, and at any real parameter `c` it is bounded by the corresponding maximum at
`|c|`.

Consequently, along any filter, if a family of polynomials `F a` eventually has degree at most `d`
and converges coefficientwise to `f` in degrees at most `d`, then `F a - f` converges to zero in the
power-series Gauss norm at every real parameter, and at nonnegative radii the Gauss norms of `F a`
converge to that of `f`. No completeness, commutativity, or ultrametric hypothesis on `R` is
needed.

## Main results

* `Polynomial.hasGaussNorm_coe`: every polynomial has bounded weighted coefficients as a power
  series at every real parameter.
* `Polynomial.gaussNorm_coe_eq_sup'_range`: for `p.natDegree ≤ d` and `0 ≤ c`, the power-series
  Gauss norm of `p` is the finite maximum over `range (d + 1)`.
* `Polynomial.gaussNorm_coe_le_sup'_range`: for `p.natDegree ≤ d` and arbitrary `c : ℝ`, it is at
  most the finite maximum at `|c|`.
* `Polynomial.tendsto_gaussNorm_coe_zero_of_natDegree_le`,
  `Polynomial.tendsto_gaussNorm_coe_sub_of_natDegree_le`: coefficientwise convergence in bounded
  degree implies Gauss-norm convergence of the difference at every radius.
* `Polynomial.tendsto_gaussNorm_coe_of_natDegree_le`: at nonnegative radii, the Gauss norms
  themselves converge.
-/

public section

open Filter Finset
open scoped PowerSeries Topology

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R]

/-- A polynomial has a finite Gauss norm as a power series for any function `v` with `v 0 = 0` and
any real parameter `c`, since all coefficients above `p.natDegree` vanish. -/
theorem hasGaussNorm_coe {v : R → ℝ} (hv0 : v 0 = 0) (c : ℝ) (p : R[X]) :
    (p : R⟦X⟧).HasGaussNorm v c := by
  let S : Finset ℝ := insert 0 ((range (p.natDegree + 1)).image fun k ↦ v (p.coeff k) * c ^ k)
  refine ⟨S.sup' (insert_nonempty _ _) id, ?_⟩
  rintro _ ⟨k, rfl⟩
  dsimp only
  rw [coeff_coe]
  refine le_sup'_of_le id ?_ le_rfl
  by_cases hk : k ≤ p.natDegree
  · exact mem_insert_of_mem (mem_image_of_mem (fun j ↦ v (p.coeff j) * c ^ j)
      (mem_range_succ_iff.mpr hk))
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hk), hv0, zero_mul]
    exact mem_insert_self _ _

end Semiring

section SeminormedRing

variable {R : Type*} [SeminormedRing R]

/-- At any real parameter `c`, the power-series Gauss norm of a polynomial `p` of degree at most `d`
is bounded by the maximum of `‖p.coeff k‖ * |c| ^ k` over `k ≤ d`. -/
theorem gaussNorm_coe_le_sup'_range {p : R[X]} {d : ℕ} (hp : p.natDegree ≤ d) (c : ℝ) :
    (p : R⟦X⟧).gaussNorm norm c ≤
      (range (d + 1)).sup' nonempty_range_add_one fun k ↦ ‖p.coeff k‖ * |c| ^ k := by
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun k ↦ ?_
  by_cases hk : k ≤ d
  · refine (le_trans ?_ (le_sup' (fun j ↦ ‖p.coeff j‖ * |c| ^ j) (mem_range_succ_iff.mpr hk)))
    rw [coeff_coe, ← abs_pow]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
  · rw [coeff_coe, coeff_eq_zero_of_natDegree_lt (hp.trans_lt (not_le.mp hk)), norm_zero, zero_mul]
    exact le_trans (by positivity)
      (le_sup' (fun j ↦ ‖p.coeff j‖ * |c| ^ j) (mem_range_succ_iff.mpr (Nat.zero_le d)))

/-- At a nonnegative radius `c ≥ 0`, the power-series Gauss norm of a polynomial `p` of degree at
most `d` equals the maximum of `‖p.coeff k‖ * c ^ k` over `k ≤ d`. -/
theorem gaussNorm_coe_eq_sup'_range {p : R[X]} {d : ℕ} (hp : p.natDegree ≤ d) {c : ℝ}
    (hc : 0 ≤ c) :
    (p : R⟦X⟧).gaussNorm norm c =
      (range (d + 1)).sup' nonempty_range_add_one fun k ↦ ‖p.coeff k‖ * c ^ k := by
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun k _ ↦ ?_)
  · simpa only [abs_of_nonneg hc] using gaussNorm_coe_le_sup'_range hp c
  · simpa only [coeff_coe] using PowerSeries.le_gaussNorm norm c (p : R⟦X⟧)
      (hasGaussNorm_coe norm_zero c p) k

/-- At any real parameter `c`, the power-series Gauss norm of a polynomial `p` of degree at most `d`
is bounded by `∑ k ∈ range (d + 1), ‖p.coeff k‖ * |c| ^ k`. -/
theorem gaussNorm_coe_le_sum_range {p : R[X]} {d : ℕ} (hp : p.natDegree ≤ d) (c : ℝ) :
    (p : R⟦X⟧).gaussNorm norm c ≤ ∑ k ∈ range (d + 1), ‖p.coeff k‖ * |c| ^ k :=
  (gaussNorm_coe_le_sup'_range hp c).trans <|
    Finset.sup'_le _ _ fun _ hk ↦
      single_le_sum (fun j _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg c) j)) hk

/-- If a family of polynomials eventually has degree at most `d` along a filter `l` and each of its
coefficients of index at most `d` tends to zero, then its power-series Gauss norm tends to zero at
every real parameter `c`. -/
theorem tendsto_gaussNorm_coe_zero_of_natDegree_le {α : Type*} {l : Filter α} {F : α → R[X]}
    {d : ℕ} (hd : ∀ᶠ a in l, (F a).natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, Tendsto (fun a ↦ (F a).coeff k) l (𝓝 0)) (c : ℝ) :
    Tendsto (fun a ↦ ((F a : R⟦X⟧)).gaussNorm norm c) l (𝓝 0) := by
  have hsum : Tendsto (fun a ↦ ∑ k ∈ range (d + 1), ‖(F a).coeff k‖ * |c| ^ k) l (𝓝 0) := by
    rw [← sum_const_zero (s := range (d + 1))]
    refine tendsto_finsetSum (range (d + 1)) fun k hk ↦ ?_
    simpa using (hcoeff k (mem_range_succ_iff.mp hk)).norm.mul_const (|c| ^ k)
  exact squeeze_zero' (.of_forall fun a ↦ PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
    (hd.mono fun a ha ↦ gaussNorm_coe_le_sum_range ha c) hsum

/-- **Gauss convergence of bounded-degree polynomial limits.** If `F a` eventually has degree at
most `d` along `l`, `f` has degree at most `d`, and `(F a).coeff k → f.coeff k` for every `k ≤ d`,
then `((F a - f : R[X]) : R⟦X⟧).gaussNorm norm c → 0` for every `c : ℝ`. -/
theorem tendsto_gaussNorm_coe_sub_of_natDegree_le {α : Type*} {l : Filter α} {F : α → R[X]}
    {f : R[X]} {d : ℕ} (hd : ∀ᶠ a in l, (F a).natDegree ≤ d) (hf : f.natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, Tendsto (fun a ↦ (F a).coeff k) l (𝓝 (f.coeff k))) (c : ℝ) :
    Tendsto (fun a ↦ (((F a - f : R[X]) : R⟦X⟧)).gaussNorm norm c) l (𝓝 0) := by
  refine tendsto_gaussNorm_coe_zero_of_natDegree_le
    (hd.mono fun a ha ↦ (natDegree_sub_le _ _).trans (max_le ha hf)) (fun k hk ↦ ?_) c
  simpa only [coeff_sub, sub_self] using (hcoeff k hk).sub_const (f.coeff k)

/-- At a nonnegative radius `c ≥ 0`, coefficientwise convergence of polynomials of bounded degree
implies convergence of their power-series Gauss norms. -/
theorem tendsto_gaussNorm_coe_of_natDegree_le {α : Type*} {l : Filter α} {F : α → R[X]}
    {f : R[X]} {d : ℕ} (hd : ∀ᶠ a in l, (F a).natDegree ≤ d) (hf : f.natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, Tendsto (fun a ↦ (F a).coeff k) l (𝓝 (f.coeff k))) {c : ℝ}
    (hc : 0 ≤ c) :
    Tendsto (fun a ↦ ((F a : R⟦X⟧)).gaussNorm norm c) l (𝓝 ((f : R⟦X⟧).gaussNorm norm c)) := by
  rw [gaussNorm_coe_eq_sup'_range hf hc]
  have hlim : Tendsto (fun a ↦ (range (d + 1)).sup' nonempty_range_add_one
      fun k ↦ ‖(F a).coeff k‖ * c ^ k) l
      (𝓝 ((range (d + 1)).sup' nonempty_range_add_one fun k ↦ ‖f.coeff k‖ * c ^ k)) :=
    Tendsto.finset_sup'_nhds_apply nonempty_range_add_one fun k hk ↦
      (hcoeff k (mem_range_succ_iff.mp hk)).norm.mul_const (c ^ k)
  exact hlim.congr' (hd.mono fun a ha ↦ (gaussNorm_coe_eq_sup'_range ha hc).symm)

end SeminormedRing

end Polynomial
