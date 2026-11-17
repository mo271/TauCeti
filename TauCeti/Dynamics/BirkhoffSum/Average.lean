/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Order.LiminfLimsup

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Recurrence, norm bounds, and shift-invariance of Birkhoff averages

This file establishes algebraic recurrences, pointwise norm bounds, and orbit-shift invariance
properties for `birkhoffAverage`, independent of any measure-theoretic structure.

## Main results

* `TauCeti.birkhoffAverage_succ_apply'` and `TauCeti.birkhoffAverage_comp_eq_sub` — exact one-step
  shift recurrences relating `birkhoffAverage R T f (n + 1) x` and `birkhoffAverage R T f n (T x)`;
* `TauCeti.norm_birkhoffAverage_le` and `TauCeti.norm_birkhoffAverage_le_of_norm_le` — pointwise
  triangle-inequality and uniform norm bounds for Birkhoff averages;
* `TauCeti.tendsto_birkhoffAverage_comp_iff` — shifting the starting point by `T` preserves
  convergence of Birkhoff averages and their limit in any real topological vector space, without
  boundedness assumptions;
* `TauCeti.limsup_birkhoffAverage_comp` and `TauCeti.liminf_birkhoffAverage_comp` — strict
  invariance under `T` of the extended-real `limsup` and `liminf` of real Birkhoff averages.
-/

public section

open Filter Function
open scoped Topology

namespace TauCeti

/-- Exact one-step shift recurrence for Birkhoff averages:
`A_{n+1} f x = (n + 1)⁻¹ • f x + (n / (n + 1)) • A_n f (T x)`. -/
theorem birkhoffAverage_succ_apply' {R α E : Type*} [DivisionSemiring R] [CharZero R]
    [AddCommMonoid E] [Module R E] (T : α → α) (f : α → E) (n : ℕ) (x : α) :
    birkhoffAverage R T f (n + 1) x =
      ((n + 1 : ℕ) : R)⁻¹ • f x +
        ((n : R) / ((n + 1 : ℕ) : R)) • birkhoffAverage R T f n (T x) := by
  rw [birkhoffAverage, birkhoffSum_succ_apply', smul_add, birkhoffAverage, smul_smul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnR : (n : R) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hcomm : Commute ((n + 1 : ℕ) : R)⁻¹ (n : R)⁻¹ :=
      (Nat.commute_cast ((n + 1 : ℕ) : R) n).inv_left₀.inv_right₀
    rw [div_eq_mul_inv, mul_assoc, hcomm.eq, ← mul_assoc, mul_inv_cancel₀ hnR, one_mul]

/-- Rearranged one-step shift recurrence expressing `A_n f (T x)` in terms of `A_{n+1} f x`. -/
theorem birkhoffAverage_comp_eq_sub {R α E : Type*} [DivisionSemiring R] [CharZero R]
    [AddCommGroup E] [Module R E] (T : α → α) (f : α → E) (n : ℕ) (x : α) :
    birkhoffAverage R T f n (T x) =
      (((n + 1 : ℕ) : R) / (n : R)) • birkhoffAverage R T f (n + 1) x -
        (n : R)⁻¹ • f x := by
  have hn1 : ((n + 1 : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hcomm : Commute (n : R)⁻¹ ((n + 1 : ℕ) : R)⁻¹ :=
    (Nat.commute_cast (n : R) (n + 1)).inv_left₀.inv_right₀
  rw [birkhoffAverage, birkhoffAverage, smul_smul, div_eq_mul_inv, mul_assoc, hcomm.eq,
    ← mul_assoc, mul_inv_cancel₀ hn1, one_mul, birkhoffSum_succ_apply', smul_add,
    add_sub_cancel_left]

/-- Pointwise triangle inequality for Birkhoff averages: the norm of the Birkhoff average is at
most the real Birkhoff average of the norms. -/
theorem norm_birkhoffAverage_le {α E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [IsBoundedSMul ℝ E] (T : α → α) (f : α → E) (n : ℕ) (x : α) :
    ‖birkhoffAverage ℝ T f n x‖ ≤ birkhoffAverage ℝ T (fun y ↦ ‖f y‖) n x := by
  rw [birkhoffAverage, birkhoffAverage, smul_eq_mul]
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

/-- Pointwise norm bound on Birkhoff averages of a uniformly bounded observable. -/
theorem norm_birkhoffAverage_le_of_norm_le {α E : Type*} [SeminormedAddCommGroup E]
    [Module ℝ E] [IsBoundedSMul ℝ E] (T : α → α) {f : α → E} {M : ℝ}
    (hM : ∀ y, ‖f y‖ ≤ M) (n : ℕ) (x : α) :
    ‖birkhoffAverage ℝ T f n x‖ ≤ M := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using (norm_nonneg (f x)).trans (hM x)
  · refine (norm_birkhoffAverage_le T f n x).trans ?_
    rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
    calc
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ‖f (T^[i] x)‖
        ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, M :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ ↦ hM _) (by positivity)
      _ = M := by simp [hn]

private theorem tendsto_natCast_div_succ :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  rw [sub_zero] at h1
  refine h1.congr fun n ↦ ?_
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

private theorem tendsto_succ_div_natCast :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) + (n : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast
  field_simp

/-- Shifting the starting point by `T` preserves convergence of Birkhoff averages and their limit,
without requiring boundedness of the observable. -/
theorem tendsto_birkhoffAverage_comp_iff {α E : Type*}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E]
    (T : α → α) (f : α → E) (x : α) (c : E) :
    Tendsto (fun n ↦ birkhoffAverage ℝ T f n (T x)) atTop (𝓝 c) ↔
      Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 c) := by
  constructor
  · intro h
    rw [← tendsto_add_atTop_iff_nat 1]
    have hinv : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹) • f x) atTop (𝓝 (0 : E)) := by
      have h0 : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹) • f x) atTop (𝓝 ((0 : ℝ) • f x)) :=
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).smul_const (f x)
      rwa [zero_smul] at h0
    have hmain : Tendsto (fun n : ℕ ↦ ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) •
        birkhoffAverage ℝ T f n (T x)) atTop (𝓝 c) := by
      have h1 := tendsto_natCast_div_succ.smul h
      rwa [one_smul] at h1
    have hadd := hinv.add hmain
    rw [zero_add] at hadd
    exact hadd.congr fun n ↦ (birkhoffAverage_succ_apply' T f n x).symm
  · intro h
    have hshift : Tendsto (fun n ↦ birkhoffAverage ℝ T f (n + 1) x) atTop (𝓝 c) :=
      (tendsto_add_atTop_iff_nat 1).2 h
    have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • f x) atTop (𝓝 (0 : E)) := by
      have h0 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • f x) atTop (𝓝 ((0 : ℝ) • f x)) :=
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).smul_const (f x)
      rwa [zero_smul] at h0
    have hmain : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) •
        birkhoffAverage ℝ T f (n + 1) x - (n : ℝ)⁻¹ • f x) atTop (𝓝 c) := by
      have h1 := (tendsto_succ_div_natCast.smul hshift).sub hinv
      rwa [one_smul, sub_zero] at h1
    exact hmain.congr fun n ↦ (birkhoffAverage_comp_eq_sub T f n x).symm

private theorem ereal_le_of_forall_real_gt {a b : EReal}
    (H : ∀ r : ℝ, b < (r : EReal) → a ≤ (r : EReal)) : a ≤ b := by
  by_contra! h
  obtain ⟨r, hr1, hr2⟩ := EReal.exists_between_coe_real h
  exact hr2.not_ge (H r hr1)

private theorem limsup_birkhoffAverage_comp_le {α : Type*} (T : α → α) (f : α → ℝ) (x : α) :
    limsup (fun n ↦ ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop ≤
      limsup (fun n ↦ ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop := by
  refine ereal_le_of_forall_real_gt fun r hr ↦ ?_
  obtain ⟨r', hr'1, hr'2⟩ := EReal.exists_between_coe_real hr
  have hev : ∀ᶠ n in atTop, birkhoffAverage ℝ T f (n + 1) x < r' := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (eventually_lt_of_limsup_lt hr'1)]
      with n hn using EReal.coe_lt_coe_iff.mp hn
  have hlim : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) * r' - (n : ℝ)⁻¹ * f x)
      atTop (𝓝 r') := by
    simpa using (tendsto_succ_div_natCast.mul_const r').sub
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (f x))
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ne_atTop 0, hev,
    hlim.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.mp hr'2))] with n hn hlt hbound
  rw [birkhoffAverage_comp_eq_sub T f n x, smul_eq_mul, smul_eq_mul]
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / (n : ℝ) :=
    div_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  exact EReal.coe_le_coe_iff.mpr <|
    ((sub_lt_sub_right (mul_lt_mul_of_pos_left hlt hpos) _).trans hbound).le

private theorem le_limsup_birkhoffAverage_comp {α : Type*} (T : α → α) (f : α → ℝ) (x : α) :
    limsup (fun n ↦ ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop ≤
      limsup (fun n ↦ ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop := by
  refine ereal_le_of_forall_real_gt fun r hr ↦ ?_
  obtain ⟨r', hr'1, hr'2⟩ := EReal.exists_between_coe_real hr
  have hev : ∀ᶠ n in atTop, birkhoffAverage ℝ T f n (T x) < r' := by
    filter_upwards [eventually_lt_of_limsup_lt hr'1] with n hn using EReal.coe_lt_coe_iff.mp hn
  have hlim : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹) * f x +
      ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) * r') atTop (𝓝 r') := by
    simpa using ((tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).mul_const (f x)).add
      (tendsto_natCast_div_succ.mul_const r')
  refine limsup_le_of_le (by isBoundedDefault) ?_
  have hsucc : ∀ᶠ n in atTop, ((birkhoffAverage ℝ T f (n + 1) x : ℝ) : EReal) ≤ (r : EReal) := by
    filter_upwards [hev, hlim.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.mp hr'2))]
      with n hlt hbound
    rw [birkhoffAverage_succ_apply', smul_eq_mul, smul_eq_mul]
    have hnonneg : (0 : ℝ) ≤ (n : ℝ) / ((n + 1 : ℕ) : ℝ) :=
      div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg (n + 1))
    exact EReal.coe_le_coe_iff.mpr <|
      ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hlt.le hnonneg)).trans_lt hbound).le
  rw [eventually_atTop] at hsucc ⊢
  obtain ⟨N, hN⟩ := hsucc
  exact ⟨N + 1, fun m hm ↦ by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_of_lt hm)
    exact hN k (by omega)⟩

/-- The extended-real `limsup` of Birkhoff averages is strictly invariant under `T`. -/
theorem limsup_birkhoffAverage_comp {α : Type*} (T : α → α) (f : α → ℝ) (x : α) :
    limsup (fun n ↦ ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop =
      limsup (fun n ↦ ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop :=
  le_antisymm (limsup_birkhoffAverage_comp_le T f x) (le_limsup_birkhoffAverage_comp T f x)

/-- The extended-real `liminf` of Birkhoff averages is strictly invariant under `T`. -/
theorem liminf_birkhoffAverage_comp {α : Type*} (T : α → α) (f : α → ℝ) (x : α) :
    liminf (fun n ↦ ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop =
      liminf (fun n ↦ ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop := by
  have h := limsup_birkhoffAverage_comp T (-f) x
  have hneg (y : α) : (fun n ↦ ((birkhoffAverage ℝ T (-f) n y : ℝ) : EReal)) =
      -(fun n ↦ ((birkhoffAverage ℝ T f n y : ℝ) : EReal)) := by
    funext n
    simp [birkhoffAverage_neg_apply]
  rw [hneg (T x), hneg x, EReal.limsup_neg, EReal.limsup_neg] at h
  exact neg_inj.mp h

end TauCeti
