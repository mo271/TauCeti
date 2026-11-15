/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Stolz--Cesàro summation against a telescoping comparison sequence

When a sequence `f : ℕ → E` is `o(w (k + 1) - w k)` for an eventually nondecreasing sequence
`w : ℕ → ℝ` tending to `+∞`, its partial sums `∑ k ∈ Ico N K, f k` are `o(w K)` as `K → ∞`.
Consequently, if `v k` approximates a forward difference `u (k + 1) - u k` up to an error that is
`o(w (k + 1) - w k)` with `w = O(u)`, then the partial sums `∑ k ∈ Ico N K, v k` are
asymptotically equivalent to `u K` as `K → ∞`, independent of the lower cutoff `N`.

Unlike geometric-tail summation lemmas that require `‖u k‖ = o(‖u (k + 1)‖)`, this comparison
applies in the sub-geometric regime where consecutive ratios `u (k + 1) / u k` tend to `1`, such as
stretched-exponential sequences `exp (c * √k)` arising in saddle-point asymptotics of recurrence
solutions and continued fractions.

## Main results

* `Asymptotics.IsLittleO.sum_Ico_of_tendsto_atTop`: Stolz--Cesàro `o`-summation over
  `Finset.Ico N K` against an eventually nondecreasing sequence `w → +∞`.
* `Asymptotics.isEquivalent_sum_Ico_of_sub`: asymptotic equivalence `∑ k ∈ Ico N K, v k ~ u K` from
  a forward-difference approximation `v k - (u (k + 1) - u k) = o(w (k + 1) - w k)` with `w = O(u)`.
* `Asymptotics.isEquivalent_sum_Ico_of_sub_norm`: specialization to `w k = ‖u k‖` when `‖u k‖` is
  eventually nondecreasing and tends to `+∞`.
-/

public section

open Filter Finset
open scoped Topology

namespace Asymptotics

/-- **Stolz--Cesàro `o`-summation against a telescoping sequence.** If `f k = o(w (k + 1) - w k)`
for an eventually nondecreasing real sequence `w` tending to `+∞`, then for every lower cutoff `N`
the partial sums `∑ k ∈ Ico N K, f k` are `o(w K)` as `K → ∞`. -/
theorem IsLittleO.sum_Ico_of_tendsto_atTop {E : Type*} [SeminormedAddCommGroup E]
    {f : ℕ → E} {w : ℕ → ℝ}
    (hf : f =o[atTop] fun k ↦ w (k + 1) - w k)
    (hw_mono : ∀ᶠ k in atTop, w k ≤ w (k + 1))
    (hw_top : Tendsto w atTop atTop) (N : ℕ) :
    (fun K ↦ ∑ k ∈ Ico N K, f k) =o[atTop] w := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hw_mono
  set g : ℕ → ℝ := fun k ↦ max (w (k + 1) - w k) 0
  have hg_nonneg : 0 ≤ g := fun k ↦ le_max_right _ _
  have hg_eq : (fun k ↦ w (k + 1) - w k) =ᶠ[atTop] g := by
    filter_upwards [eventually_ge_atTop M] with k hk
    exact (max_eq_left (sub_nonneg.mpr (hM k hk))).symm
  have hg_sum_eq : ∀ K ≥ M,
      ∑ k ∈ range K, g k = w K + ((∑ k ∈ range M, g k) - w M) := fun K hK ↦ by
    rw [← sum_range_add_sum_Ico g hK]
    have hIco : ∑ k ∈ Ico M K, g k = ∑ k ∈ Ico M K, (w (k + 1) - w k) :=
      Finset.sum_congr rfl fun k hk ↦ max_eq_left (sub_nonneg.mpr (hM k (mem_Ico.mp hk).1))
    rw [hIco, sum_Ico_sub (fun k ↦ w k) hK]
    ring
  have hw_norm_top : Tendsto (fun K ↦ ‖w K‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp hw_top
  have hg_equiv : (fun K ↦ ∑ k ∈ range K, g k) ~[atTop] w :=
    (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hw_norm_top).congr_left
      ((eventually_ge_atTop M).mono fun K hK ↦ (hg_sum_eq K hK).symm)
  have hg_top : Tendsto (fun K ↦ ∑ k ∈ range K, g k) atTop atTop :=
    hg_equiv.symm.tendsto_atTop hw_top
  have hrange : (fun K ↦ ∑ k ∈ range K, ‖f k‖) =o[atTop] w :=
    ((hf.norm_left.congr' EventuallyEq.rfl hg_eq).sum_range hg_nonneg hg_top).trans_isEquivalent
      hg_equiv
  have hconst : (fun _ : ℕ ↦ ∑ k ∈ range N, ‖f k‖) =o[atTop] w :=
    isLittleO_const_left.mpr (Or.inr hw_norm_top)
  have hnorm_sum : (fun K ↦ ∑ k ∈ Ico N K, ‖f k‖) =o[atTop] w :=
    (hrange.sub hconst).congr' ((eventually_ge_atTop N).mono fun K hK ↦ by
      dsimp only [Pi.sub_apply]
      rw [← sum_range_add_sum_Ico (fun k ↦ ‖f k‖) hK, add_sub_cancel_left]) EventuallyEq.rfl
  exact (isBigO_of_le atTop fun K ↦
    (norm_sum_le _ _).trans (Real.le_norm_self _)).trans_isLittleO hnorm_sum

/-- **Telescoping asymptotic equivalence via Stolz--Cesàro.** If `v k` approximates the forward
difference `u (k + 1) - u k` up to an error that is `o(w (k + 1) - w k)` for an eventually
nondecreasing sequence `w → +∞` with `w = O(u)`, then `∑ k ∈ Ico N K, v k ~ u K` as `K → ∞` for
every lower cutoff `N`. -/
theorem isEquivalent_sum_Ico_of_sub {E : Type*} [NormedAddCommGroup E]
    {v u : ℕ → E} {w : ℕ → ℝ}
    (hv : (fun k ↦ v k - (u (k + 1) - u k)) =o[atTop] fun k ↦ w (k + 1) - w k)
    (hw_mono : ∀ᶠ k in atTop, w k ≤ w (k + 1))
    (hw_top : Tendsto w atTop atTop)
    (hwu : w =O[atTop] u) (N : ℕ) :
    (fun K ↦ ∑ k ∈ Ico N K, v k) ~[atTop] u := by
  have herr : (fun K ↦ ∑ k ∈ Ico N K, (v k - (u (k + 1) - u k))) =o[atTop] u :=
    (hv.sum_Ico_of_tendsto_atTop hw_mono hw_top N).trans_isBigO hwu
  have hconst : (fun _ : ℕ ↦ u N) =o[atTop] u :=
    (isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp hw_top))).trans_isBigO hwu
  refine IsLittleO.isEquivalent ((herr.sub hconst).congr' ?_ EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop N] with K hK
  rw [Pi.sub_apply, sum_sub_distrib, sum_Ico_sub u hK]
  abel

/-- Specialization of `Asymptotics.isEquivalent_sum_Ico_of_sub` to `w k = ‖u k‖` when `‖u k‖` is
eventually nondecreasing and tends to `+∞`. -/
theorem isEquivalent_sum_Ico_of_sub_norm {E : Type*} [NormedAddCommGroup E]
    {v u : ℕ → E}
    (hv : (fun k ↦ v k - (u (k + 1) - u k)) =o[atTop] fun k ↦ ‖u (k + 1)‖ - ‖u k‖)
    (hu_mono : ∀ᶠ k in atTop, ‖u k‖ ≤ ‖u (k + 1)‖)
    (hu_top : Tendsto (fun k ↦ ‖u k‖) atTop atTop) (N : ℕ) :
    (fun K ↦ ∑ k ∈ Ico N K, v k) ~[atTop] u :=
  isEquivalent_sum_Ico_of_sub hv hu_mono hu_top (isBigO_norm_left.mpr (isBigO_refl u atTop)) N

end Asymptotics

end
