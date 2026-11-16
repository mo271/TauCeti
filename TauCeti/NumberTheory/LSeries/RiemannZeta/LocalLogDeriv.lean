/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.LSeries.ZetaZeros
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.NumberTheory.LSeries.RiemannZeta.VerticalGrowth

/-!
# Local logarithmic-derivative expansions and safe heights for the Riemann zeta function

Applying Jensen's zero-count inequality (`AnalyticOnNhd.sum_divisor_half_le`) and Landau's local
logarithmic-derivative lemma (`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le`) to the entire
regularized function `riemannZeta₁(s) = (s - 1) ζ(s)` yields three standard analytic tools for
`ζ′/ζ`:

1. **Nested-disc expansion (`TauCeti.riemannZeta_local_logDeriv`)**: about any centre `s₀` on a
   fixed vertical line `Re s₀ = σ₀ > 1`, `ζ′/ζ(s) + 1 / (s - 1)` agrees on `‖s - s₀‖ ≤ r` (with
   `r < r'`, `s ≠ 1`, `ζ(s) ≠ 0`) with the partial-fraction sum `∑ m(ρ) / (s - ρ)` over all zeros
   of `ζ` in `‖ρ - s₀‖ ≤ r'` (trivial zeros included), up to `O(log (|Im s₀| + 2))`.
2. **Unit-window expansion (`TauCeti.riemannZeta_logDeriv_window`)**: on the strip
   `-1 ≤ Re s ≤ 2` (`s ≠ 1`, `ζ(s) ≠ 0`), specializing to `s₀ = 2 + i Im s`, `r = 3`, `r' = 4`
   absorbs the trivial zeros `-2 (n + 1)` and the distant critical-strip zeros of the disc—each at
   distance at least `1` from `s` and numbering `O(log (|Im s| + 2))`—into the remainder, leaving
   only the nontrivial zeros in the unit window `0 < Re ρ < 1`, `|Im ρ - Im s| ≤ 1`.
3. **Safe horizontal contours (`TauCeti.riemannZeta_safe_height`)**: in every unit interval
   `[T, T + 1]` with `T ≥ 2`, the band `T - 1 ≤ Im ρ ≤ T + 2` contains `O(log (T + 2))` critical
   zeros, so by the pigeonhole principle some height `T' ∈ [T, T + 1]` stays at distance
   `≫ 1 / log (T + 2)` from every ordinate in the band. On both horizontal segments `σ ± i T'`
   (`-1 ≤ σ ≤ 2`), `ζ` is nonvanishing and `‖ζ′/ζ(σ ± i T')‖ ≤ C log² (T + 2)`.

## Main results

* `TauCeti.finite_closedBall_riemannZeta_eq_zero` and
  `TauCeti.exists_finsum_analyticOrderAt_riemannZeta_closedBall_le`: finiteness and
  `O(log (|Im s₀| + 2))` multiplicity count of zeros of `ζ` in `closedBall s₀ r'` for
  `Re s₀ = σ₀ > 1`.
* `TauCeti.riemannZeta_local_logDeriv`: nested-disc partial-fraction expansion of
  `ζ′/ζ(s) + 1 / (s - 1)`.
* `TauCeti.one_le_norm_sub_of_riemannZeta_eq_zero` and `TauCeti.riemannZeta_logDeriv_window`:
  unit-window expansion on `-1 ≤ Re s ≤ 2`.
* `TauCeti.deriv_riemannZeta_conj`: `deriv riemannZeta (conj s) = conj (deriv riemannZeta s)`.
* `TauCeti.exists_mem_Icc_abs_sub_im_riemannZeta_zero_ge` and `TauCeti.riemannZeta_safe_height`:
  safe heights `T' ∈ [T, T + 1]` avoiding critical-zero ordinates by `≫ 1 / log (T + 2)` and
  satisfying `‖ζ′/ζ(σ ± i T')‖ ≤ C log² (T + 2)` across `-1 ≤ σ ≤ 2`.

## References

* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §§3.9, 9.6.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 15 and 17.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemmas 8.5–8.6 and 11.2–11.4.
-/

public section

open Complex Real Set Metric MeromorphicOn Filter Topology
open scoped ComplexConjugate

namespace TauCeti

/-! ### Zeros, multiplicities, and logarithmic derivative of `riemannZeta₁` vs `riemannZeta` -/

/-- `riemannZeta₁` has the exact same zeros as `riemannZeta` on all of `ℂ` (at `s = 1` both
`riemannZeta₁ 1 = 1` and Mathlib's value `riemannZeta 1` are nonzero). -/
@[simp]
theorem riemannZeta₁_eq_zero_iff {z : ℂ} : riemannZeta₁ z = 0 ↔ riemannZeta z = 0 := by
  rcases eq_or_ne z 1 with rfl | hz
  · simp [riemannZeta_one_ne_zero]
  · rw [riemannZeta_eq_inv_sub_mul hz, mul_eq_zero, inv_eq_zero, sub_eq_zero]
    simp [hz]

/-- Away from `z = 1`, `riemannZeta₁` and `riemannZeta` have the same `analyticOrderAt`. -/
theorem analyticOrderAt_riemannZeta₁_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    analyticOrderAt riemannZeta₁ z = analyticOrderAt riemannZeta z := by
  have heq : riemannZeta₁ =ᶠ[𝓝 z] (fun w ↦ w - 1) * riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    exact riemannZeta₁_eq_sub_mul hw
  have hsub : AnalyticAt ℂ (fun w : ℂ ↦ w - 1) z := analyticAt_id.sub analyticAt_const
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hsub (analyticOn_riemannZeta z hz),
    hsub.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]

/-- `riemannZeta₁` has finite analytic order at every point of `ℂ`. -/
theorem analyticOrderAt_riemannZeta₁_ne_top (z : ℂ) : analyticOrderAt riemannZeta₁ z ≠ ⊤ := by
  have hana : AnalyticOnNhd ℂ riemannZeta₁ univ :=
    fun w _ ↦ differentiable_riemannZeta₁.analyticAt w
  refine hana.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 1)
    (mem_univ z) ?_
  rw [(differentiable_riemannZeta₁.analyticAt 1).analyticOrderAt_eq_zero.mpr
    (by simp : riemannZeta₁ 1 ≠ 0)]
  exact ENat.zero_ne_top

/-- Every zero of `riemannZeta` has positive natural analytic multiplicity. -/
theorem one_le_toNat_analyticOrderAt_riemannZeta {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
  have hρ1 : ρ ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ hρ)
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 :=
    (analyticOn_riemannZeta ρ hρ1).analyticOrderAt_ne_zero.mpr hρ
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← analyticOrderAt_riemannZeta₁_of_ne_one hρ1]
    exact analyticOrderAt_riemannZeta₁_ne_top ρ
  exact Nat.one_le_iff_ne_zero.mpr ((ENat.toNat_eq_zero.not.mpr (not_or.mpr ⟨hne0, htop⟩)))

open Classical in
/-- On any set `U`, the meromorphic divisor of `riemannZeta₁` equals
`(analyticOrderAt riemannZeta z).toNat` at zeros of `riemannZeta` in `U`, and `0` elsewhere. -/
theorem divisor_riemannZeta₁_eq (U : Set ℂ) (z : ℂ) :
    divisor riemannZeta₁ U z =
      if z ∈ U ∧ riemannZeta z = 0 then ((analyticOrderAt riemannZeta z).toNat : ℤ) else 0 := by
  have hana : AnalyticAt ℂ riemannZeta₁ z := differentiable_riemannZeta₁.analyticAt z
  have hmero : MeromorphicOn riemannZeta₁ U := fun w _ ↦
    (differentiable_riemannZeta₁.analyticAt w).meromorphicAt
  split_ifs with h
  · have hz1 : z ≠ 1 := fun h1 ↦ riemannZeta_one_ne_zero (h1 ▸ h.2)
    rw [hmero.divisor_eq_analyticOrderNatAt hana h.1, analyticOrderNatAt,
      analyticOrderAt_riemannZeta₁_of_ne_one hz1]
  · rcases not_and_or.mp h with hzU | hζ
    · simp [hzU]
    · exact hana.divisor_apply_eq_zero (mt riemannZeta₁_eq_zero_iff.mp hζ)

/-- Away from `s = 1` and the zeros of `ζ`, `ζ′/ζ(s) + 1 / (s - 1)` is `logDeriv riemannZeta₁ s`. -/
theorem deriv_div_riemannZeta_add_one_div_sub_one {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s + 1 / (s - 1) = logDeriv riemannZeta₁ s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hζ₁ : riemannZeta₁ s ≠ 0 := mt riemannZeta₁_eq_zero_iff.mp hζ
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs, logDeriv_apply]
  field_simp
  ring

/-- The derivative of `riemannZeta` commutes with complex conjugation everywhere on `ℂ`. -/
@[simp]
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have hfun : conj ∘ riemannZeta ∘ conj = riemannZeta := funext fun z ↦ by simp
  have h := congrFun (deriv_conj_conj (f := riemannZeta)) (conj s)
  simpa [hfun] using h

/-! ### Relative circle bounds and local zero counts -/

/-- On a vertical line `Re s₀ = σ₀ > 1`, `‖riemannZeta₁ s₀‖` is bounded below by the positive
constant `(σ₀ - 1) / (riemannZeta σ₀).re`. -/
theorem div_riemannZeta_re_le_norm_riemannZeta₁ {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {s₀ : ℂ}
    (hs₀ : s₀.re = σ₀) :
    (σ₀ - 1) / (riemannZeta σ₀).re ≤ ‖riemannZeta₁ s₀‖ := by
  have hs₀1 : s₀ ≠ 1 := fun h ↦ by have := congrArg re h; simp [hs₀] at this; linarith
  have hsub : σ₀ - 1 ≤ ‖s₀ - 1‖ := by
    have : σ₀ - 1 = (s₀ - 1).re := by simp [hs₀]
    exact this.le.trans ((le_abs_self _).trans (abs_re_le_norm _))
  rw [riemannZeta₁_eq_sub_mul hs₀1, norm_mul, div_eq_mul_inv]
  exact mul_le_mul hsub (inv_riemannZeta_re_le_norm_riemannZeta hσ₀ hs₀.symm.le)
    (inv_nonneg.mpr (riemannZeta_re_pos_of_one_lt hσ₀).le) (norm_nonneg _)

/-- In any closed disc, `riemannZeta` has only finitely many zeros. -/
theorem finite_closedBall_riemannZeta_eq_zero (s₀ : ℂ) (r' : ℝ) :
    {z : ℂ | ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0}.Finite :=
  (isCompact_closedBall s₀ r').inter_riemannZetaZeros_finite.subset
    fun z hz ↦ ⟨by simpa [mem_closedBall, dist_eq_norm] using hz.1, hz.2⟩

private theorem finsum_closedBall_riemannZeta_eq_sum {M : Type*} [AddCommMonoid M]
    (s₀ : ℂ) (r' : ℝ) (g : ℂ → M) :
    (∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0}, g ρ.val) =
      ∑ ρ ∈ (finite_closedBall_riemannZeta_eq_zero s₀ r').toFinset, g ρ := by
  rw [finsum_subtype_eq_finsum_cond (f := g)]
  exact finsum_cond_eq_sum_of_cond_iff g fun _ ↦ by
    simp [(finite_closedBall_riemannZeta_eq_zero s₀ r').mem_toFinset]

/-- Relative circle bound for `riemannZeta₁` on `sphere s₀ R` with `Re s₀ = σ₀ > 1`:
`‖riemannZeta₁ w‖ ≤ M(s₀) * ‖riemannZeta₁ s₀‖` with `log M(s₀) ≤ K * log (|Im s₀| + 2)`. -/
private theorem exists_relative_sphere_bound_riemannZeta₁ {σ₀ R : ℝ} (hσ₀ : 1 < σ₀) :
    ∃ K > 0, ∀ s₀ : ℂ, s₀.re = σ₀ → ∃ M ≥ (1 : ℝ),
      Real.log M ≤ K * Real.log (|s₀.im| + 2) ∧
        ∀ w ∈ sphere s₀ R, ‖riemannZeta₁ w‖ ≤ M * ‖riemannZeta₁ s₀‖ := by
  obtain ⟨C₁, hC₁, B, hB, hball⟩ := exists_norm_riemannZeta₁_closedBall_le_rpow σ₀ R
  have hpos_ζ : 0 < (riemannZeta σ₀).re := riemannZeta_re_pos_of_one_lt hσ₀
  have : 0 < σ₀ - 1 := sub_pos.mpr hσ₀
  set A := max 1 (C₁ * (riemannZeta σ₀).re / (σ₀ - 1))
  have hA1 : 1 ≤ A := le_max_left _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨Real.log A / Real.log 2 + B + 1, by
    have := div_nonneg (Real.log_nonneg hA1) hlog2.le; positivity, fun s₀ hs₀ ↦ ?_⟩
  set M := A * (|s₀.im| + 2) ^ B
  have ht2 : 2 ≤ |s₀.im| + 2 := by linarith [abs_nonneg s₀.im]
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA1
    (Real.one_le_rpow (by linarith) hB)
  refine ⟨M, hM1, ?_, fun w hw ↦ ?_⟩
  · have hlogt : Real.log 2 ≤ Real.log (|s₀.im| + 2) := Real.log_le_log two_pos ht2
    rw [Real.log_mul (zero_lt_one.trans_le hA1).ne' (by positivity),
      Real.log_rpow (by positivity)]
    have hA_bound : Real.log A ≤ (Real.log A / Real.log 2) * Real.log (|s₀.im| + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlogt (Real.log_nonneg hA1)
    linarith [hlog2.le.trans hlogt]
  · have hw_ball : w ∈ closedBall s₀ R := sphere_subset_closedBall hw
    have hlow := div_riemannZeta_re_le_norm_riemannZeta₁ hσ₀ hs₀
    have hCA : C₁ * (riemannZeta σ₀).re / (σ₀ - 1) ≤ A := le_max_right _ _
    calc ‖riemannZeta₁ w‖ ≤ C₁ * (|s₀.im| + 2) ^ B := hball s₀ w hs₀ hw_ball
      _ = (C₁ * (riemannZeta σ₀).re / (σ₀ - 1)) * (|s₀.im| + 2) ^ B *
            ((σ₀ - 1) / (riemannZeta σ₀).re) := by field_simp
      _ ≤ (A * (|s₀.im| + 2) ^ B) * ‖riemannZeta₁ s₀‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCA (by positivity)) hlow
            (by positivity) (by positivity)

/-- **Local disc zero count for `riemannZeta`.** For `σ₀ > 1` and any `r' : ℝ`, the number of zeros
of `riemannZeta` in `‖z - s₀‖ ≤ r'` (counted with analytic multiplicity) is
`O(log (|Im s₀| + 2))` uniformly for `Re s₀ = σ₀`. -/
theorem exists_finsum_analyticOrderAt_riemannZeta_closedBall_le {σ₀ r' : ℝ} (hσ₀ : 1 < σ₀) :
    ∃ C > 0, ∀ s₀ : ℂ, s₀.re = σ₀ →
      ((∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
          (analyticOrderAt riemannZeta ρ.val).toNat : ℕ) : ℝ) ≤
        C * Real.log (|s₀.im| + 2) := by
  set R := max r' 1
  have : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨K, hK, hrel⟩ := exists_relative_sphere_bound_riemannZeta₁ (R := 2 * R) hσ₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨K / Real.log 2, div_pos hK hlog2, fun s₀ hs₀ ↦ ?_⟩
  obtain ⟨M, _, hlogM, hM⟩ := hrel s₀ hs₀
  have hf : AnalyticOnNhd ℂ riemannZeta₁ (closedBall s₀ (2 * R)) :=
    fun w _ ↦ differentiable_riemannZeta₁.analyticAt w
  have hz₀ : riemannZeta₁ s₀ ≠ 0 :=
    mt riemannZeta₁_eq_zero_iff.mp (riemannZeta_ne_zero_of_one_le_re (hs₀ ▸ hσ₀.le))
  have hjensen := hf.sum_divisor_half_le (by positivity) hz₀ hM
  rw [mul_div_cancel_left₀ R two_ne_zero] at hjensen
  have hSR_fin := finite_closedBall_riemannZeta_eq_zero s₀ R
  have hS_fin := finite_closedBall_riemannZeta_eq_zero s₀ r'
  have hdiv_eq : ((∑ᶠ ρ, divisor riemannZeta₁ (closedBall s₀ R) ρ : ℤ) : ℝ) =
      ∑ ρ ∈ hSR_fin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hSR_fin.toFinset) fun z hz ↦ by
      classical
      rw [Finset.mem_coe, hSR_fin.mem_toFinset]; by_contra hnot
      rw [Function.mem_support] at hz
      refine hz ?_
      rw [divisor_riemannZeta₁_eq, ite_eq_right_iff]
      rintro ⟨hz1, hz2⟩
      exact absurd ⟨by simpa [mem_closedBall, dist_eq_norm] using hz1, hz2⟩ hnot]
    push_cast
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hρ' := hSR_fin.mem_toFinset.mp hρ
    have hmem : ρ ∈ closedBall s₀ R ∧ riemannZeta ρ = 0 :=
      ⟨by simpa [mem_closedBall, dist_eq_norm] using hρ'.1, hρ'.2⟩
    simp [divisor_riemannZeta₁_eq, hmem]
  have hsub_sum : ((∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
        (analyticOrderAt riemannZeta ρ.val).toNat : ℕ) : ℝ) ≤
      ∑ ρ ∈ hSR_fin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
    rw [finsum_closedBall_riemannZeta_eq_sum s₀ r' (fun ρ ↦ (analyticOrderAt riemannZeta ρ).toNat)]
    push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun z hz ↦ hSR_fin.mem_toFinset.mpr
        ⟨(hS_fin.mem_toFinset.mp hz).1.trans (le_max_left _ _), (hS_fin.mem_toFinset.mp hz).2⟩)
      fun _ _ _ ↦ Nat.cast_nonneg _
  calc ((∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
          (analyticOrderAt riemannZeta ρ.val).toNat : ℕ) : ℝ)
      ≤ ((∑ᶠ ρ, divisor riemannZeta₁ (closedBall s₀ R) ρ : ℤ) : ℝ) :=
        hsub_sum.trans_eq hdiv_eq.symm
    _ ≤ Real.log M / Real.log 2 := hjensen
    _ ≤ (K * Real.log (|s₀.im| + 2)) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogM hlog2.le
    _ = (K / Real.log 2) * Real.log (|s₀.im| + 2) := by ring

/-! ### Nested-disc expansion, critical-strip window expansion, and safe heights -/

/-- **Nested-disc expansion of `ζ′/ζ`.** About any centre `s₀` with `Re s₀ = σ₀ > 1`, for `r < r'`,
`‖s - s₀‖ ≤ r`, `s ≠ 1` and `riemannZeta s ≠ 0`, `ζ′/ζ(s) + 1 / (s - 1)` differs from the finite
sum `∑ m(ρ) / (s - ρ)` over all zeros of `ζ` in `‖ρ - s₀‖ ≤ r'` (trivial zeros included) by
`O(log (|Im s₀| + 2))`. Note `s ≠ 1` excludes the pole of `ζ`. -/
theorem riemannZeta_local_logDeriv {σ₀ r r' : ℝ} (hσ₀ : 1 < σ₀) (hrr' : r < r') :
    ∃ C : ℝ, ∀ s₀ s : ℂ, s₀.re = σ₀ → ‖s - s₀‖ ≤ r → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s₀.im| + 2) := by
  rcases lt_or_ge r 0 with hr | hr
  · refine ⟨0, fun s₀ s _ hs _ _ ↦ ?_⟩
    exact absurd (hs.trans_lt hr) (not_lt.mpr (norm_nonneg _))
  have : 0 < r' := hr.trans_lt hrr'
  obtain ⟨K, _, hrel⟩ := exists_relative_sphere_bound_riemannZeta₁ (R := 2 * r') hσ₀
  refine ⟨4 * (r' + r) / (r' - r) ^ 2 * K, fun s₀ s hs₀ hs hs1 hζ ↦ ?_⟩
  obtain ⟨M, hM1, hlogM, hM⟩ := hrel s₀ hs₀
  have hf : AnalyticOnNhd ℂ riemannZeta₁ (closedBall s₀ (2 * r')) :=
    fun w _ ↦ differentiable_riemannZeta₁.analyticAt w
  have hz₀ : riemannZeta₁ s₀ ≠ 0 :=
    mt riemannZeta₁_eq_zero_iff.mp (riemannZeta_ne_zero_of_one_le_re (hs₀ ▸ hσ₀.le))
  have hfz : riemannZeta₁ s ≠ 0 := mt riemannZeta₁_eq_zero_iff.mp hζ
  have hlandau := hf.norm_logDeriv_sub_finsum_divisor_le (r := r') le_rfl hz₀ hM
    (hs.trans_lt hrr') hfz
  have hS_fin := finite_closedBall_riemannZeta_eq_zero s₀ r'
  have hsum_eq : (∑ᶠ ρ, (divisor riemannZeta₁ (closedBall s₀ r') ρ : ℂ) / (s - ρ)) =
      ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
        ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val) := by
    rw [finsum_closedBall_riemannZeta_eq_sum s₀ r'
        (fun ρ ↦ ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ)),
      finsum_eq_sum_of_support_subset _ (s := hS_fin.toFinset) fun z hz ↦ by
        classical
        rw [Finset.mem_coe, hS_fin.mem_toFinset]; by_contra hnot
        rw [Function.mem_support] at hz
        have h0 : divisor riemannZeta₁ (closedBall s₀ r') z = 0 := by
          rw [divisor_riemannZeta₁_eq, ite_eq_right_iff]
          rintro ⟨hz1, hz2⟩
          exact absurd ⟨by simpa [mem_closedBall, dist_eq_norm] using hz1, hz2⟩ hnot
        simp [h0] at hz]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hρ' := hS_fin.mem_toFinset.mp hρ
    have hmem : ρ ∈ closedBall s₀ r' ∧ riemannZeta ρ = 0 :=
      ⟨by simpa [mem_closedBall, dist_eq_norm] using hρ'.1, hρ'.2⟩
    simp [divisor_riemannZeta₁_eq, hmem]
  rw [deriv_div_riemannZeta_add_one_div_sub_one hs1 hζ, ← hsum_eq]
  have : 0 < r' - r := sub_pos.mpr hrr'
  have hrad : 4 * (r' + ‖s - s₀‖) / (r' - ‖s - s₀‖) ^ 2 ≤ 4 * (r' + r) / (r' - r) ^ 2 := by
    gcongr
  calc ‖logDeriv riemannZeta₁ s -
          ∑ᶠ ρ, (divisor riemannZeta₁ (closedBall s₀ r') ρ : ℂ) / (s - ρ)‖
      ≤ 4 * (r' + ‖s - s₀‖) / (r' - ‖s - s₀‖) ^ 2 * Real.log M := hlandau
    _ ≤ 4 * (r' + r) / (r' - r) ^ 2 * (K * Real.log (|s₀.im| + 2)) :=
        mul_le_mul hrad hlogM (Real.log_nonneg hM1) (by positivity)
    _ = 4 * (r' + r) / (r' - r) ^ 2 * K * Real.log (|s₀.im| + 2) := by ring

/-- Any zero `ρ` of `riemannZeta` outside the unit critical-strip window
`0 < Re ρ < 1`, `|Im ρ - Im s| ≤ 1` lies at distance at least `1` from every `s` with
`-1 ≤ Re s`. -/
theorem one_le_norm_sub_of_riemannZeta_eq_zero {s ρ : ℂ} (hs : -1 ≤ s.re)
    (hρ : riemannZeta ρ = 0) (hwin : ¬(0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - s.im| ≤ 1)) :
    1 ≤ ‖s - ρ‖ := by
  have hρ_lt1 : ρ.re < 1 := lt_of_not_ge fun hge ↦ riemannZeta_ne_zero_of_one_le_re hge hρ
  rcases lt_or_ge 0 ρ.re with hρ0 | hρ0
  · have him_gt : 1 < |ρ.im - s.im| := lt_of_not_ge fun hle ↦ hwin ⟨hρ0, hρ_lt1, hle⟩
    exact him_gt.le.trans (by rw [abs_sub_comm]; simpa using abs_im_le_norm (s - ρ))
  · obtain ⟨n, rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hρ0).mp hρ
    have hre_triv : ((-2 : ℂ) * (n + 1)).re ≤ -2 := by simp
    have h1 : 1 ≤ (s - (-2 * (n + 1))).re := by simp at hre_triv ⊢; linarith
    exact h1.trans ((le_abs_self _).trans (abs_re_le_norm _))

/-- **Unit-window expansion of `ζ′/ζ` on `-1 ≤ Re s ≤ 2`.** Away from `s = 1` and the zeros of
`riemannZeta`, `ζ′/ζ(s) + 1 / (s - 1)` differs from the partial-fraction sum over the critical
zeros of `ζ` in the unit height window `|Im ρ - Im s| ≤ 1` by `O(log (|Im s| + 2))`. -/
theorem riemannZeta_logDeriv_window :
    ∃ C : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s.im| + 2) := by
  -- Apply `riemannZeta_local_logDeriv` at `s₀ = 2 + i Im s` with `r = 3 < 4 = r'`.
  obtain ⟨C₁, hloc⟩ := riemannZeta_local_logDeriv (σ₀ := 2) (r := 3) (r' := 4)
    one_lt_two (by norm_num)
  obtain ⟨C₂, _, hcnt⟩ :=
    exists_finsum_analyticOrderAt_riemannZeta_closedBall_le (σ₀ := 2) (r' := 4) one_lt_two
  refine ⟨max C₁ 0 + C₂, fun s hs_lo hs_hi hs1 hζ ↦ ?_⟩
  set s₀ : ℂ := 2 + s.im * I
  have hs_dist : ‖s - s₀‖ ≤ 3 := by
    have hsub : s - s₀ = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [s₀]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_le]; exact ⟨by linarith, by linarith⟩
  -- Split the disc zeros `‖ρ - s₀‖ ≤ 4` into the unit window and its complement (`‖s - ρ‖ ≥ 1`).
  have hWD : {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0} ⊆
      {z : ℂ | ‖z - s₀‖ ≤ 4 ∧ riemannZeta z = 0} := fun z ⟨hz0, hz1, hzim, hzζ⟩ ↦ ⟨by
    have hre : |(z - s₀).re| ≤ 2 := by
      have : (z - s₀).re = z.re - 2 := by simp [s₀]
      rw [this, abs_le]; exact ⟨by linarith, by linarith⟩
    have him : |(z - s₀).im| ≤ 1 := by simpa [s₀] using hzim
    exact (norm_le_abs_re_add_abs_im (z - s₀)).trans (by linarith), hzζ⟩
  have hD_fin := finite_closedBall_riemannZeta_eq_zero s₀ 4
  have hW_fin := hD_fin.subset hWD
  set term : ℂ → ℂ := fun ρ ↦ ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ)
  have hW_sum : (∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
        term ρ.val) = ∑ ρ ∈ hW_fin.toFinset, term ρ := by
    rw [finsum_subtype_eq_finsum_cond (f := term)]
    exact finsum_cond_eq_sum_of_cond_iff term fun _ ↦ by simp [hW_fin.mem_toFinset]
  have hsub_sdiff : ∑ ρ ∈ hD_fin.toFinset, term ρ - ∑ ρ ∈ hW_fin.toFinset, term ρ =
      ∑ ρ ∈ hD_fin.toFinset \ hW_fin.toFinset, term ρ :=
    (Finset.sum_sdiff_eq_sub
      (fun z hz ↦ hD_fin.mem_toFinset.mpr (hWD (hW_fin.mem_toFinset.mp hz)))).symm
  have htail : ‖∑ ρ ∈ hD_fin.toFinset \ hW_fin.toFinset, term ρ‖ ≤ C₂ * Real.log (|s.im| + 2) := by
    calc ‖∑ ρ ∈ hD_fin.toFinset \ hW_fin.toFinset, term ρ‖
        ≤ ∑ ρ ∈ hD_fin.toFinset \ hW_fin.toFinset,
            ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
          obtain ⟨hρD, hρW⟩ := Finset.mem_sdiff.mp hρ
          have hρD' := hD_fin.mem_toFinset.mp hρD
          simp only [term, norm_div, Complex.norm_natCast]
          exact div_le_self (Nat.cast_nonneg _)
            (one_le_norm_sub_of_riemannZeta_eq_zero hs_lo hρD'.2 fun h ↦
              hρW (hW_fin.mem_toFinset.mpr ⟨h.1, h.2.1, h.2.2, hρD'.2⟩))
      _ ≤ ∑ ρ ∈ hD_fin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ ↦ Nat.cast_nonneg _
      _ ≤ C₂ * Real.log (|s.im| + 2) := by
          have hc := hcnt s₀ (by simp [s₀])
          rw [finsum_closedBall_riemannZeta_eq_sum s₀ 4
            (fun ρ ↦ (analyticOrderAt riemannZeta ρ).toNat)] at hc
          have hc' : ∑ ρ ∈ hD_fin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
              C₂ * Real.log (|s₀.im| + 2) := by exact_mod_cast hc
          simpa [s₀] using hc'
  have hmain := hloc s₀ s (by simp [s₀]) hs_dist hs1 hζ
  rw [finsum_closedBall_riemannZeta_eq_sum s₀ 4 term] at hmain
  rw [hW_sum]
  have hsplit : deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ ρ ∈ hW_fin.toFinset, term ρ =
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ ρ ∈ hD_fin.toFinset, term ρ) +
        ∑ ρ ∈ hD_fin.toFinset \ hW_fin.toFinset, term ρ := by rw [← hsub_sdiff]; ring
  rw [hsplit]
  have hmain0 : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
      ∑ ρ ∈ hD_fin.toFinset, term ρ‖ ≤ C₁ * Real.log (|s.im| + 2) := by simpa [s₀] using hmain
  have hmain' : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
      ∑ ρ ∈ hD_fin.toFinset, term ρ‖ ≤ max C₁ 0 * Real.log (|s.im| + 2) :=
    hmain0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith [abs_nonneg s.im])))
  exact ((norm_add_le _ _).trans (add_le_add hmain' htail)).trans_eq (by ring)

/-- For `T ≥ 2`, the zeros of `riemannZeta` in the critical-strip band
`0 < Re ρ < 1`, `T - 1 ≤ Im ρ ≤ T + 2` form a finite set whose total analytic multiplicity is
`O(log (T + 2))`. -/
private theorem exists_sum_analyticOrderAt_riemannZeta_band_le :
    ∃ C > 0, ∀ T : ℝ, 2 ≤ T →
      ∃ hB : {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ T - 1 ≤ z.im ∧ z.im ≤ T + 2 ∧
        riemannZeta z = 0}.Finite,
      (∑ ρ ∈ hB.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤
        C * Real.log (T + 2) := by
  obtain ⟨C₂, hC₂, hcnt⟩ :=
    exists_finsum_analyticOrderAt_riemannZeta_closedBall_le (σ₀ := 2) (r' := 4) one_lt_two
  refine ⟨2 * C₂, by positivity, fun T hT ↦ ?_⟩
  set s₀ : ℂ := 2 + ((T + 1 / 2 : ℝ) : ℂ) * I
  have hD_fin := finite_closedBall_riemannZeta_eq_zero s₀ 4
  have hBD : {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ T - 1 ≤ z.im ∧ z.im ≤ T + 2 ∧ riemannZeta z = 0} ⊆
      {z : ℂ | ‖z - s₀‖ ≤ 4 ∧ riemannZeta z = 0} := fun z ⟨hz0, hz1, hzlo, hzhi, hzζ⟩ ↦ ⟨by
    have hre : |(z - s₀).re| ≤ 2 := by
      have : (z - s₀).re = z.re - 2 := by simp [s₀]
      rw [this, abs_le]; exact ⟨by linarith, by linarith⟩
    have him : |(z - s₀).im| ≤ 3 / 2 := by
      have : (z - s₀).im = z.im - (T + 1 / 2) := by simp [s₀]
      rw [this, abs_le]; exact ⟨by linarith, by linarith⟩
    exact (norm_le_abs_re_add_abs_im (z - s₀)).trans (by linarith), hzζ⟩
  have hB_fin := hD_fin.subset hBD
  refine ⟨hB_fin, ?_⟩
  have hc := hcnt s₀ (by simp [s₀])
  rw [finsum_closedBall_riemannZeta_eq_sum s₀ 4
    (fun ρ ↦ (analyticOrderAt riemannZeta ρ).toNat)] at hc
  have hc' : ∑ ρ ∈ hD_fin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
      C₂ * Real.log (|s₀.im| + 2) := by exact_mod_cast hc
  have hlog_s₀ : Real.log (|s₀.im| + 2) ≤ 2 * Real.log (T + 2) := by
    have him : |s₀.im| + 2 ≤ (T + 2) ^ 2 := by
      have hs₀_im : s₀.im = T + 1 / 2 := by simp [s₀]
      rw [hs₀_im, abs_of_pos (by linarith)]; nlinarith
    exact (Real.log_le_log (by positivity) him).trans_eq (by rw [Real.log_pow]; norm_num)
  exact ((Finset.sum_le_sum_of_subset_of_nonneg
    (fun z hz ↦ hD_fin.mem_toFinset.mpr (hBD (hB_fin.mem_toFinset.mp hz)))
    fun _ _ _ ↦ Nat.cast_nonneg _).trans
      (hc'.trans (mul_le_mul_of_nonneg_left hlog_s₀ hC₂.le))).trans_eq (by ring)

/-- **Safe ordinate selection for `riemannZeta`.** Every unit interval `[T, T + 1]` (`T ≥ 2`)
contains a height `T'` separated by at least `(K * log (T + 2))⁻¹` from the ordinates of all
zeros of `riemannZeta` in the band `0 < Re ρ < 1`, `T - 1 ≤ Im ρ ≤ T + 2`. -/
theorem exists_mem_Icc_abs_sub_im_riemannZeta_zero_ge :
    ∃ K > 0, ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Icc T (T + 1),
      ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → T - 1 ≤ ρ.im → ρ.im ≤ T + 2 → riemannZeta ρ = 0 →
        (K * Real.log (T + 2))⁻¹ ≤ |T' - ρ.im| := by
  classical
  obtain ⟨C, hC, hband⟩ := exists_sum_analyticOrderAt_riemannZeta_band_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K := 2 * (C + 1 / Real.log 2)
  refine ⟨K, by positivity, fun T hT ↦ ?_⟩
  obtain ⟨hB_fin, hB_sum⟩ := hband T hT
  set S := hB_fin.toFinset
  have hN_le : 2 * ((S.card : ℝ) + 1) ≤ K * Real.log (T + 2) := by
    have hcard : (S.card : ℝ) ≤ C * Real.log (T + 2) := by
      calc (S.card : ℝ) = ∑ _ρ ∈ S, (1 : ℝ) := by simp
        _ ≤ ∑ ρ ∈ S, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) :=
            Finset.sum_le_sum fun ρ hρ ↦ by
              exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta
                (hB_fin.mem_toFinset.mp hρ).2.2.2.2
        _ ≤ C * Real.log (T + 2) := hB_sum
    have h1_le : 1 ≤ (1 / Real.log 2) * Real.log (T + 2) := by
      rw [one_div_mul_eq_div, one_le_div hlog2]; exact Real.log_le_log two_pos (by linarith)
    have hK_eq : K * Real.log (T + 2) =
        2 * (C * Real.log (T + 2) + (1 / Real.log 2) * Real.log (T + 2)) := by
      simp only [K]; ring
    linarith [hK_eq]
  have hN_pos : 0 < (S.card : ℝ) + 1 := Nat.cast_add_one_pos S.card
  set t : Fin (S.card + 1) → ℝ := fun j ↦ T + (j : ℝ) / (S.card + 1 : ℝ)
  have ht_mem (j : Fin (S.card + 1)) : t j ∈ Icc T (T + 1) :=
    ⟨le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hN_pos.le), by
      linarith [div_le_one_of_le₀ (by exact_mod_cast j.isLt.le : (j : ℝ) ≤ S.card + 1) hN_pos.le]⟩
  by_contra! hbad
  choose f hf0 hf1 hflo hfhi hfζ hflt using fun j ↦ hbad (t j) (ht_mem j)
  let F : Fin (S.card + 1) → S := fun j ↦
    ⟨f j, hB_fin.mem_toFinset.mpr ⟨hf0 j, hf1 j, hflo j, hfhi j, hfζ j⟩⟩
  obtain ⟨i, j, hij, hFij⟩ := Fintype.exists_ne_map_eq_of_card_lt F (by simp)
  have hij_ge : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
    have hij_int : (i : ℤ) ≠ (j : ℤ) := fun h ↦ hij (Fin.ext (Int.ofNat.inj h))
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij_int)
  have hdiff : ((S.card : ℝ) + 1)⁻¹ ≤ |t i - t j| := by
    have hsub : t i - t j = ((i : ℝ) - (j : ℝ)) / (S.card + 1 : ℝ) := by simp only [t]; ring
    rw [hsub, abs_div, abs_of_pos hN_pos, ← one_div]
    exact div_le_div_of_nonneg_right hij_ge hN_pos.le
  have htri : |t i - t j| ≤ |t i - (f i).im| + |t j - (f j).im| := by
    have hfij : f i = f j := congrArg Subtype.val hFij
    rw [hfij]
    simpa [abs_sub_comm ((f j).im) (t j)] using abs_sub_le (t i) (f j).im (t j)
  have hinv_le : (K * Real.log (T + 2))⁻¹ ≤ (2 * ((S.card : ℝ) + 1))⁻¹ :=
    inv_anti₀ (by positivity) hN_le
  linarith [hflt i, hflt j,
    (by field_simp; ring : (2 * ((S.card : ℝ) + 1))⁻¹ + (2 * ((S.card : ℝ) + 1))⁻¹ =
      ((S.card : ℝ) + 1)⁻¹)]

/-- Along a horizontal segment `σ + i T'` (`T' ∈ [T, T + 1]`, `T ≥ 2`) whose ordinate `T'` is
`(K * log (T + 2))⁻¹`-separated from critical-zero ordinates in `[T - 1, T + 2]`, `riemannZeta`
is nonvanishing and the unit-window partial-fraction sum is bounded by
`C * K * log (T + 2) ^ 2`. -/
private theorem riemannZeta_ne_zero_and_norm_window_le {C K T T' σ : ℝ}
    (hC : 0 < C) (hK : 0 < K) (hT : 2 ≤ T) (hT' : T' ∈ Icc T (T + 1))
    {hB : {w : ℂ | 0 < w.re ∧ w.re < 1 ∧ T - 1 ≤ w.im ∧ w.im ≤ T + 2 ∧
      riemannZeta w = 0}.Finite}
    (hB_sum : (∑ ρ ∈ hB.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤
      C * Real.log (T + 2))
    (hgap : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → T - 1 ≤ ρ.im → ρ.im ≤ T + 2 → riemannZeta ρ = 0 →
      (K * Real.log (T + 2))⁻¹ ≤ |T' - ρ.im|) :
    riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0 ∧
      ‖∑ᶠ ρ : {w : ℂ // 0 < w.re ∧ w.re < 1 ∧
          |w.im - ((σ : ℂ) + (T' : ℂ) * I).im| ≤ 1 ∧ riemannZeta w = 0},
          ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) /
            (((σ : ℂ) + (T' : ℂ) * I) - ρ.val)‖ ≤
        C * K * Real.log (T + 2) ^ 2 := by
  set z : ℂ := (σ : ℂ) + (T' : ℂ) * I
  have hlogT_pos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have hz_ne0 : riemannZeta z ≠ 0 := by
    rcases le_or_gt 1 σ with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa [z] using h1)
    rcases le_or_gt σ 0 with h0 | h0
    · intro hζ0
      obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos (by simpa [z] using h0)).mp hζ0
      have := congrArg im hn; simp [z] at this; linarith [hT'.1]
    · intro hζ0
      have h0_lt : 0 < |T' - z.im| := (by positivity : 0 < (K * Real.log (T + 2))⁻¹).trans_le
        (hgap z (by simpa [z] using h0) (by simpa [z] using h1)
          (by simp [z]; linarith [hT'.1]) (by simp [z]; linarith [hT'.2]) hζ0)
      simp [z] at h0_lt
  refine ⟨hz_ne0, ?_⟩
  have hWB : {w : ℂ | 0 < w.re ∧ w.re < 1 ∧ |w.im - z.im| ≤ 1 ∧ riemannZeta w = 0} ⊆
      {w : ℂ | 0 < w.re ∧ w.re < 1 ∧ T - 1 ≤ w.im ∧ w.im ≤ T + 2 ∧ riemannZeta w = 0} := by
    rintro w ⟨hw0, hw1, hwim, hwζ⟩
    simp only [z, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add] at hwim
    exact ⟨hw0, hw1, by linarith [(abs_le.mp hwim).1, hT'.1],
      by linarith [(abs_le.mp hwim).2, hT'.2], hwζ⟩
  have hWz_fin := hB.subset hWB
  set term : ℂ → ℂ := fun ρ ↦ ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)
  have hS_eq : (∑ᶠ ρ : {w : ℂ // 0 < w.re ∧ w.re < 1 ∧ |w.im - z.im| ≤ 1 ∧ riemannZeta w = 0},
        term ρ.val) = ∑ ρ ∈ hWz_fin.toFinset, term ρ := by
    rw [finsum_subtype_eq_finsum_cond (f := term)]
    exact finsum_cond_eq_sum_of_cond_iff term fun _ ↦ by simp [hWz_fin.mem_toFinset]
  rw [hS_eq]
  calc ‖∑ ρ ∈ hWz_fin.toFinset, term ρ‖
      ≤ (∑ ρ ∈ hWz_fin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) *
          (K * Real.log (T + 2)) := by
        rw [Finset.sum_mul]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
        obtain ⟨hρ0, hρ1, hρlo, hρhi, hρζ⟩ := hWB (hWz_fin.mem_toFinset.mp hρ)
        have hinv : (‖z - ρ‖)⁻¹ ≤ K * Real.log (T + 2) := by
          simpa using inv_anti₀ (by positivity)
            ((hgap ρ hρ0 hρ1 hρlo hρhi hρζ).trans (by simpa [z] using abs_im_le_norm (z - ρ)))
        dsimp only [term]
        rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
    _ ≤ (C * Real.log (T + 2)) * (K * Real.log (T + 2)) :=
        mul_le_mul ((Finset.sum_le_sum_of_subset_of_nonneg
          (fun w hw ↦ hB.mem_toFinset.mpr (hWB (hWz_fin.mem_toFinset.mp hw)))
          fun _ _ _ ↦ Nat.cast_nonneg _).trans hB_sum) le_rfl (by positivity) (by positivity)
    _ = C * K * Real.log (T + 2) ^ 2 := by ring

/-- Upper horizontal segment bound for `riemannZeta_safe_height` once `T' ∈ [T, T + 1]` is
`(K * log (T + 2))⁻¹`-separated from critical-zero ordinates in `[T - 1, T + 2]`. -/
private theorem norm_deriv_div_riemannZeta_safe_upper {C₁ C K : ℝ} (hC : 0 < C) (hK : 0 < K)
    (hwin : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C₁ * Real.log (|s.im| + 2))
    {T T' σ : ℝ} (hT : 2 ≤ T) (hT' : T' ∈ Icc T (T + 1)) (hσ_lo : -1 ≤ σ) (hσ_hi : σ ≤ 2)
    {hB : {w : ℂ | 0 < w.re ∧ w.re < 1 ∧ T - 1 ≤ w.im ∧ w.im ≤ T + 2 ∧
      riemannZeta w = 0}.Finite}
    (hB_sum : (∑ ρ ∈ hB.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤
      C * Real.log (T + 2))
    (hgap : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → T - 1 ≤ ρ.im → ρ.im ≤ T + 2 → riemannZeta ρ = 0 →
      (K * Real.log (T + 2))⁻¹ ≤ |T' - ρ.im|) :
    riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0 ∧
      ‖deriv riemannZeta ((σ : ℂ) + (T' : ℂ) * I) / riemannZeta ((σ : ℂ) + (T' : ℂ) * I)‖ ≤
        (C * K + 2 * max C₁ 0 / Real.log 2 + 1 / Real.log 2 ^ 2) *
          Real.log (T + 2) ^ 2 := by
  obtain ⟨hz_ne0, hWz_sum⟩ :=
    riemannZeta_ne_zero_and_norm_window_le hC hK hT hT' hB_sum hgap (σ := σ)
  refine ⟨hz_ne0, ?_⟩
  set z : ℂ := (σ : ℂ) + (T' : ℂ) * I
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogT_ge : Real.log 2 ≤ Real.log (T + 2) := Real.log_le_log two_pos (by linarith)
  have hlogT_pos : 0 < Real.log (T + 2) := hlog2.trans_le hlogT_ge
  have hT'2 : 2 ≤ T' := hT.trans hT'.1
  have hz_ne1 : z ≠ 1 := fun h ↦ by have := congrArg im h; simp [z] at this; linarith
  have hlog_z : Real.log (|z.im| + 2) ≤ 2 * Real.log (T + 2) := by
    have him : |z.im| + 2 ≤ (T + 2) ^ 2 := by
      simp only [z, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add, abs_of_pos (by linarith : 0 < T')]
      nlinarith [hT'.2]
    exact (Real.log_le_log (by positivity) him).trans_eq (by rw [Real.log_pow]; norm_num)
  set S_win := ∑ᶠ ρ : {w : ℂ // 0 < w.re ∧ w.re < 1 ∧ |w.im - z.im| ≤ 1 ∧ riemannZeta w = 0},
    ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (z - ρ.val)
  have hpole : ‖1 / (z - 1)‖ ≤ (1 / Real.log 2 ^ 2) * Real.log (T + 2) ^ 2 := by
    have h1 : ‖1 / (z - 1)‖ ≤ 1 := by
      rw [one_div, norm_inv]
      exact inv_le_one_of_one_le₀ ((by linarith [le_abs_self T'] : 1 ≤ |T'|).trans
        (by simpa [z] using abs_im_le_norm (z - 1)))
    have hsq : 1 ≤ (1 / Real.log 2 ^ 2) * Real.log (T + 2) ^ 2 := by
      rw [one_div_mul_eq_div, one_le_div (sq_pos_of_pos hlog2)]
      exact pow_le_pow_left₀ hlog2.le hlogT_ge 2
    exact h1.trans hsq
  have hrem : ‖deriv riemannZeta z / riemannZeta z + 1 / (z - 1) - S_win‖ ≤
      (2 * max C₁ 0 / Real.log 2) * Real.log (T + 2) ^ 2 := by
    have hw := (hwin z (by simpa [z] using hσ_lo) (by simpa [z] using hσ_hi) hz_ne1 hz_ne0).trans
      ((mul_le_mul_of_nonneg_right (le_max_left C₁ 0)
        (Real.log_nonneg (by linarith [abs_nonneg z.im]))).trans
        (mul_le_mul_of_nonneg_left hlog_z (le_max_right C₁ 0)))
    have hlin : max C₁ 0 * (2 * Real.log (T + 2)) ≤
        (2 * max C₁ 0 / Real.log 2) * Real.log (T + 2) ^ 2 := by
      rw [sq, ← mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hlog2]
      have hmul := mul_le_mul_of_nonneg_left hlogT_ge
        (mul_nonneg (mul_nonneg zero_le_two (le_max_right C₁ 0)) hlogT_pos.le)
      linarith
    exact hw.trans hlin
  have hdecomp : deriv riemannZeta z / riemannZeta z =
      (deriv riemannZeta z / riemannZeta z + 1 / (z - 1) - S_win) + S_win - 1 / (z - 1) := by ring
  rw [hdecomp]
  exact ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hrem hWz_sum)) hpole)).trans_eq (by ring)

/-- **Safe horizontal contours for `ζ′/ζ`.** There exists an absolute constant `C` such that every
`T ≥ 2` admits a height `T' ∈ [T, T + 1]` on which `riemannZeta` is nonvanishing and
`‖ζ′/ζ(s)‖ ≤ C * log (T + 2) ^ 2` across `-1 ≤ Re s ≤ 2` on both horizontal segments `σ ± i T'`. -/
theorem riemannZeta_safe_height :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Icc T (T + 1), ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ∀ s ∈ ({(σ : ℂ) + (T' : ℂ) * I, (σ : ℂ) - (T' : ℂ) * I} : Set ℂ),
        riemannZeta s ≠ 0 ∧
          ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (T + 2) ^ 2 := by
  obtain ⟨C₁, hwin⟩ := riemannZeta_logDeriv_window
  obtain ⟨C₀, hC₀, hband⟩ := exists_sum_analyticOrderAt_riemannZeta_band_le
  obtain ⟨K, hK, hord⟩ := exists_mem_Icc_abs_sub_im_riemannZeta_zero_ge
  refine ⟨C₀ * K + 2 * max C₁ 0 / Real.log 2 + 1 / Real.log 2 ^ 2, fun T hT ↦ ?_⟩
  obtain ⟨hB, hB_sum⟩ := hband T hT
  obtain ⟨T', hT', hgap⟩ := hord T hT
  refine ⟨T', hT', fun σ hσ_lo hσ_hi s hs ↦ ?_⟩
  have hupper := norm_deriv_div_riemannZeta_safe_upper hC₀ hK hwin hT hT' hσ_lo hσ_hi hB_sum hgap
  rcases hs with rfl | hs
  · exact hupper
  · rw [mem_singleton_iff] at hs
    subst hs
    have hconj : (σ : ℂ) - (T' : ℂ) * I = conj ((σ : ℂ) + (T' : ℂ) * I) := by simp [sub_eq_add_neg]
    rw [hconj, riemannZeta_conj, deriv_riemannZeta_conj, ← map_div₀, norm_conj]
    exact ⟨mt (congrArg conj) (by simpa using hupper.1), hupper.2⟩

end TauCeti

/-! ### Example

In `riemannZeta_local_logDeriv` with `s₀ = 2` and `r' = 4`, the trivial zero `ρ = -2` lies in the
disc `‖ρ - 2‖ ≤ 4` and is counted in the partial-fraction sum, whereas `riemannZeta_logDeriv_window`
restricts its sum to nontrivial zeros in `0 < Re ρ < 1` and absorbs `-2` into the remainder. -/

example : ‖(-2 : ℂ) - 2‖ ≤ 4 ∧ riemannZeta (-2) = 0 ∧ ¬(0 < (-2 : ℂ).re) := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  simpa using riemannZeta_neg_two_mul_nat_add_one 0
