/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Open additive maps with bounded lifts

An additive map between seminormed groups is open if every element has a preimage
whose norm is bounded by a fixed multiple of its norm. Neither continuity nor completeness is
required. When the codomain is a normed group and zero lifts to zero, preimages whose norms
approximate the target norm (`‖x‖ < ‖y‖ + ε` for every `ε > 0`) supply such a uniform bound with
any factor `K > 1`. These criteria turn norm-controlled lifts into quotient-topology comparisons.
-/

public section

namespace TauCeti

/-- For a zero-preserving map into a normed group, sharp preimage bounds (`‖x‖ < ‖y‖ + ε` for every
`ε > 0`) imply uniformly bounded lifts with any factor `K > 1`: zero lifts to zero, while a nonzero
`y` has positive norm so `(K - 1) * ‖y‖ > 0` is an admissible slack. -/
theorem exists_norm_le_of_forall_pos_lt_add {E F 𝓕 : Type*}
    [SeminormedAddGroup E] [NormedAddGroup F] [FunLike 𝓕 E F] [ZeroHomClass 𝓕 E F] (f : 𝓕)
    (h : ∀ y, ∀ ε > 0, ∃ x, f x = y ∧ ‖x‖ < ‖y‖ + ε) {K : ℝ} (hK : 1 < K) (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ K * ‖y‖ := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy], by simp [hy]⟩
  · obtain ⟨x, hx, hn⟩ := h y ((K - 1) * ‖y‖)
      (mul_pos (sub_pos.mpr hK) (norm_pos_iff.mpr hy))
    exact ⟨x, hx, hn.le.trans_eq (by ring)⟩

/-- An additive map between seminormed groups with uniformly norm-bounded lifts is open. -/
theorem isOpenMap_of_exists_norm_le {E F 𝓕 : Type*}
    [SeminormedAddGroup E] [SeminormedAddGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ}
    (h : ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ K * ‖y‖) : IsOpenMap f := by
  let L := max K 1
  have hL : 0 < L := lt_max_of_lt_right one_pos
  intro U hU
  rw [Metric.isOpen_iff] at hU ⊢
  rintro _ ⟨x, hxU, rfl⟩
  obtain ⟨r, hr, hrU⟩ := hU x hxU
  refine ⟨r / L, div_pos hr hL, fun y hy => ?_⟩
  obtain ⟨z, hz, hzn⟩ := h (-f x + y)
  refine ⟨x + z, hrU ?_, by rw [map_add, hz, add_neg_cancel_left]⟩
  have hy' : ‖-f x + y‖ < r / L := by
    rw [← dist_eq_norm_neg_add]
    exact Metric.mem_ball'.1 hy
  rw [Metric.mem_ball', dist_eq_norm_neg_add, neg_add_cancel_left]
  calc ‖z‖ ≤ L * ‖-f x + y‖ :=
      hzn.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (norm_nonneg _))
    _ < r := by simpa only [mul_comm] using (lt_div_iff₀ hL).mp hy'

end TauCeti
