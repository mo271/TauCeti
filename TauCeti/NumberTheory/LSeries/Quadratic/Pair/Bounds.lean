/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
public import TauCeti.Data.Nat.GCD
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds

/-!
# Uniform bounds for the two-character L-function product

For characters of positive levels `M` and `N`, the three nonprincipal factors in
`ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` have product bounded by `343 (MN)²` on
`|s - 2| ≤ 3/2`. The constant is independent of both characters and levels. This is the
level-dependent input for Cauchy estimates on the regularized four-factor product, and hence
for the two-character comparison near one. The zeta regularization is a fixed entire function
and can be bounded on this disk independently of the characters.

More generally, on the half-plane `1 / 2 ≤ Re s` away from `s = 1` (`1 / 2 ≤ ‖s - 1‖`), combining
the partial-summation growth bound for `ζ(s)` with the principal and nonprincipal Dirichlet
`L`-function bounds gives the vertical polynomial growth bound
`‖ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)‖ ≤ 256 (MN)² ‖s‖⁴` for arbitrary characters `χ` and `ψ`
(principal or nonprincipal).

The estimates use the continued L-functions, not the junk value of a divergent series.
Quadraticity and primitivity are unnecessary for these estimates; for primitive characters
the levels are their conductors. The product character stays at its actual least-common-multiple
level, retaining all deleted Euler factors.

## Main results

* `DirichletCharacter.norm_LFunction_mul_mul_le_of_mem_closedBall`: uniform `(MN)²` bound on the
  three character `L`-factors over `|s - 2| ≤ 3 / 2`.
* `DirichletCharacter.norm_pair_le_of_one_half_le_re`: vertical polynomial growth bound
  `256 (MN)² ‖s‖⁴` on the full four-factor product for `1 / 2 ≤ Re s` and `1 / 2 ≤ ‖s - 1‖`.

## References

* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
-/

public section

open Complex Metric

namespace DirichletCharacter

variable {M N : ℕ} [NeZero M] [NeZero N]
variable (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)

/-- The three nonprincipal L-factors in the two-character product have a uniform polynomial
level bound on the closed disk used for Cauchy estimates near one. -/
theorem norm_LFunction_mul_mul_le_of_mem_closedBall (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) (3 / 2)) :
    ‖χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      343 * ((M : ℝ) * N) ^ 2 := by
  have hdist : ‖s - 2‖ ≤ 3 / 2 := mem_closedBall_iff_norm.mp hs
  have hre : 1 / 2 ≤ s.re := by
    have hlo := neg_abs_le (s - 2).re
    have habs := abs_re_le_norm (s - 2)
    norm_num [sub_re] at hlo habs
    linarith
  have hnorm : ‖s‖ ≤ 7 / 2 := by
    have := norm_le_insert (2 : ℂ) s
    norm_num [norm_sub_rev (2 : ℂ) s] at this
    linarith
  have hbound {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρ : ρ ≠ 1) :
      ‖ρ.LFunction s‖ ≤ 7 * L := by
    have hb := ρ.norm_LFunction_le_level_mul_norm_div_re hρ (by linarith : 0 < s.re)
    apply hb.trans
    apply (div_le_iff₀ (by linarith : 0 < s.re)).mpr
    nlinarith
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N))
      (Nat.lcm_dvd_mul M N)
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (7 * (M : ℝ)) * (7 * N) * (7 * Nat.lcm M N) :=
      mul_le_mul (mul_le_mul (hbound χ hχ) (hbound ψ hψ) (norm_nonneg _) (by positivity))
        (hbound (χ.mul ψ) hχψ) (norm_nonneg _) (by positivity)
    _ ≤ (7 * M) * (7 * N) * (7 * ((M : ℝ) * N)) := by gcongr
    _ = 343 * ((M : ℝ) * N) ^ 2 := by ring

/-- **Vertical polynomial growth of the four-factor product.** For any Dirichlet characters `χ` mod
`M` and `ψ` mod `N` (principal or nonprincipal) and any `s` with `1 / 2 ≤ Re s` and
`1 / 2 ≤ ‖s - 1‖`,
`‖ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)‖ ≤ 256 (M N)² ‖s‖⁴`. -/
theorem norm_pair_le_of_one_half_le_re {s : ℂ} (hre : 1 / 2 ≤ s.re) (hd : 1 / 2 ≤ ‖s - 1‖) :
    ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      256 * ((M : ℝ) * N) ^ 2 * ‖s‖ ^ 4 := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hd; linarith
  have hζ : ‖riemannZeta s‖ ≤ 4 * ‖s‖ := by
    have hb := TauCeti.norm_riemannZeta_le_of_re_pos hs0
    have h1 : ‖s‖ / ‖s - 1‖ ≤ 2 * ‖s‖ :=
      (div_le_iff₀ (by linarith)).mpr (by nlinarith [norm_nonneg s])
    have h2 : ‖s‖ / s.re ≤ 2 * ‖s‖ := (div_le_iff₀ hs0).mpr (by nlinarith [norm_nonneg s])
    linarith
  have hL {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) :
      ‖ρ.LFunction s‖ ≤ 4 * (L : ℝ) * ‖s‖ := by
    by_cases hρ : ρ = 1
    · subst hρ
      have htriv : ‖LFunctionTrivChar L s‖ ≤ (L : ℝ) * ‖riemannZeta s‖ := by
        have h1 := norm_LFunctionTrivChar₁_le (N := L) hs0.le
        simp only [LFunctionTrivChar₁, Function.update_of_ne hs1, norm_mul, LFunctionTrivChar,
          LFunction_modOne_eq] at h1
        have hs1' : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
        exact le_of_mul_le_mul_left (by simpa [mul_left_comm] using h1) hs1'
      calc ‖(1 : DirichletCharacter ℂ L).LFunction s‖
          ≤ (L : ℝ) * (4 * ‖s‖) := htriv.trans (by gcongr)
        _ = 4 * (L : ℝ) * ‖s‖ := by ring
    · calc ‖ρ.LFunction s‖ ≤ (L : ℝ) * ‖s‖ / s.re :=
            ρ.norm_LFunction_le_level_mul_norm_div_re hρ hs0
        _ ≤ 4 * (L : ℝ) * ‖s‖ := by
            have hLs : 0 ≤ (L : ℝ) * ‖s‖ := by positivity
            exact (div_le_iff₀ hs0).mpr (by nlinarith)
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  have hχψ_le : ‖(χ.mul ψ).LFunction s‖ ≤ 4 * ((M : ℝ) * N) * ‖s‖ :=
    (hL (χ.mul ψ)).trans (by gcongr)
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(χ.mul ψ).LFunction s‖
      ≤ (4 * ‖s‖) * (4 * (M : ℝ) * ‖s‖) * (4 * (N : ℝ) * ‖s‖) * (4 * ((M : ℝ) * N) * ‖s‖) :=
        mul_le_mul (mul_le_mul (mul_le_mul hζ (hL χ) (norm_nonneg _) (by positivity))
          (hL ψ) (norm_nonneg _) (by positivity)) hχψ_le (norm_nonneg _) (by positivity)
    _ = 256 * ((M : ℝ) * N) ^ 2 * ‖s‖ ^ 4 := by ring

end DirichletCharacter
