/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Residue
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.RiemannZeta
import TauCeti.NumberTheory.LSeries.SmoothedSum
import TauCeti.NumberTheory.LSeries.SumCoeff
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Shifted Mellin smoothing of the four-factor L-function product

For nonprincipal Dirichlet characters `χ` and `ψ` of levels `M` and `N`, the four-factor product
`F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` represents the Dirichlet series of
`DirichletCharacter.zetaMulPairCoeffs` on `Re s > 1`. Twisting its coefficients by `n ^ (-β)` for
`0 < β < 1` and smoothing by `e ^ (-n x)` (`x > 0`) writes

`∑ₙ aₙ n ^ (-β) e ^ (-n x) = mellinInv (2 - β) (w ↦ Γ(w) F(w + β)) x`.

Shifting the line of integration across the poles at `s = 1` (of `F`) and `s = β` (of `Γ(s - β)`)
to any vertical line `Re s = σ₁` with `0 < σ₁ < β` expresses this smoothed sum as the sum of the
residue of `F(s) Γ(s - β) x ^ (β - s)` at `s = 1`, the value `F(β)`, and the shifted vertical
integral on `Re s = σ₁`. To pass to the limit on horizontal segments without Stirling or functional
equation estimates for `ζ`, the rectangles are cut at the heights `Tₖ = (2k + 1) π / log 2`, where
`2 ^ (1 - (σ ± i Tₖ)) = -2 ^ (1 - σ)` keeps `|1 - 2 ^ (1 - s)| ≥ 1` uniformly across `σ > 0`, so the
alternating-series continuation of `ζ` gives polynomial growth while `Γ(s - β)` decays faster than
`Tₖ ^ (-6)`.

When `χ` and `ψ` are quadratic with nonprincipal product `χ.mul ψ ≠ 1`, the coefficients `aₙ` are
nonnegative real numbers with `a₁ = 1`, so the smoothed sum is at least `e ^ (-x)`. Specializing to
`σ₁ = 1 / 4` and `1 / 2 ≤ β < 1` whenever `F(β) ≤ 0`, and choosing `x` of size `((M N) ^ 8)⁻¹` so
that the shifted integral is at most `e⁻¹ / 2`, gives Goldfeld's quantitative lower bound

`c (1 - β) (M N) ^ (-8 (1 - β)) ≤ Re (L(1, χ) L(1, ψ) L(1, χ.mul ψ))`

with an absolute constant `c > 0`.

## Main results

* `DirichletCharacter.hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp`: the shifted contour formula
  for `∑ₙ aₙ n ^ (-β) e ^ (-n x)` for arbitrary nonprincipal characters `χ` and `ψ`.
* `DirichletCharacter.hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp_of_mul_ne_one` and
  `DirichletCharacter.hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp_of_mul_eq_one`: explicit
  formulas in the simple-pole (`χ.mul ψ ≠ 1`) and double-pole (`χ.mul ψ = 1`) cases.
* `DirichletCharacter.exists_norm_mellinInv_pair_le`: uniform conductor and `x`-power bound for the
  shifted integral on `Re s = 1 / 4`.
* `DirichletCharacter.exists_le_LFunction_one_mul_mul_of_pair_nonpos`: Goldfeld's lower bound for
  `L(1, χ) L(1, ψ) L(1, χ.mul ψ)` from `F(β) ≤ 0` on `1 / 2 ≤ β < 1`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9.
-/

public section

open Filter MeasureTheory Set
open Complex hiding exp continuous_exp
open scoped ComplexOrder Interval Topology

namespace DirichletCharacter

section Growth

/-- Partial summation of the alternating zeta series bounds `(1 - 2 ^ (1 - s)) ζ(s)` by
`‖s‖ / Re s` across the open right half-plane away from `1`. -/
private theorem norm_one_sub_two_cpow_mul_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖(1 - 2 ^ (1 - s)) * riemannZeta s‖ ≤ ‖s‖ / s.re := by
  rw [TauCeti.one_sub_two_cpow_mul_riemannZeta_eq_mul_integral hs hs1]
  simpa [one_mul] using TauCeti.LSeries.norm_mul_integral_le_of_bound (C := 1) _
    (fun n ↦ by simpa using TauCeti.LSeries.norm_sum_Icc_neg_one_pow_add_one_le (R := ℂ) n) hs

/-- On any vertical line `Re s = σ > 0` with `σ ≠ 1`, the factor `1 - 2 ^ (1 - s)` is bounded away
from zero by `|1 - 2 ^ (1 - σ)|`, giving linear growth of `ζ(s)` in `‖s‖`. -/
private theorem norm_riemannZeta_le_of_re_ne_one {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / (s.re * |1 - (2 : ℝ) ^ (1 - s.re)|) := by
  have hs_ne : s ≠ 1 := fun h ↦ hs1 (by simp [h])
  have hpow_ne : (2 : ℝ) ^ (1 - s.re) ≠ 1 := by
    rcases lt_trichotomy s.re 1 with hlt | h | hgt
    · exact (Real.one_lt_rpow one_lt_two (by linarith)).ne'
    · exact absurd h hs1
    · exact (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)).ne
  have habs_pos : 0 < |1 - (2 : ℝ) ^ (1 - s.re)| := abs_pos.mpr (sub_ne_zero.mpr hpow_ne.symm)
  have hnorm2 : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos two_pos,
      sub_re, one_re]
  have hlo : |1 - (2 : ℝ) ^ (1 - s.re)| ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
    simpa [hnorm2] using abs_norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ (1 - s))
  have hmain := norm_one_sub_two_cpow_mul_riemannZeta_le hs hs_ne
  rw [norm_mul] at hmain
  rw [← div_div, le_div_iff₀ habs_pos, mul_comm]
  exact (mul_le_mul_of_nonneg_right hlo (norm_nonneg _)).trans hmain

/-- Discrete horizontal cut heights `(2k + 1) π / log 2` at which `2 ^ (1 - (σ ± i Tₖ))` is real
and negative, keeping `1 - 2 ^ (1 - s)` of norm at least `1` across `σ = 1`. -/
private noncomputable def zetaCutHeight (k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * Real.pi / Real.log 2

private theorem zetaCutHeight_pos (k : ℕ) : 0 < zetaCutHeight k :=
  div_pos (mul_pos (by positivity) Real.pi_pos) (Real.log_pos one_lt_two)

private theorem tendsto_zetaCutHeight_atTop : Tendsto zetaCutHeight atTop atTop := by
  unfold zetaCutHeight
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlin : Tendsto (fun k : ℕ ↦ (2 * (k : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos).atTop_add tendsto_const_nhds
  exact (hlin.atTop_mul_const Real.pi_pos).atTop_div_const hlog

/-- At any height `y` with `y log 2 = (2m + 1) π`, `2 ^ (1 - (σ + i y)) = -2 ^ (1 - σ)` and hence
`‖ζ(σ + i y)‖ ≤ ‖σ + i y‖ / σ` for every `σ > 0`. -/
private theorem norm_riemannZeta_le_of_mul_log_two_eq {σ y : ℝ} (hσ : 0 < σ) {m : ℤ}
    (hy : y * Real.log 2 = (2 * (m : ℝ) + 1) * Real.pi) :
    ‖riemannZeta ((σ : ℂ) + y * I)‖ ≤ ‖(σ : ℂ) + y * I‖ / σ := by
  set s : ℂ := (σ : ℂ) + y * I
  have hy_ne : y ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hy
    rcases mul_eq_zero.mp hy.symm with hm | hπ
    · have hm' : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast hm
      omega
    · exact Real.pi_ne_zero hπ
  have hs1 : s ≠ 1 := fun h ↦ hy_ne (by simpa [s] using congrArg im h)
  have hexp_odd : Complex.exp (-(((2 * (m : ℝ) + 1) * Real.pi : ℝ) : ℂ) * I) = -1 := by
    have hsplit : -(((2 * (m : ℝ) + 1) * Real.pi : ℝ) : ℂ) * I =
        ((-m - 1 : ℤ) : ℂ) * (2 * Real.pi * I) + Real.pi * I := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_pi_mul_I]
  have hpow : (2 : ℂ) ^ (1 - s) = -(((2 : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      cpow_def_of_ne_zero (by norm_num : ((2 : ℝ) : ℂ) ≠ 0), ← ofReal_log zero_le_two]
    have harg : (Real.log 2 : ℂ) * (1 - s) =
        (((1 - σ) * Real.log 2 : ℝ) : ℂ) + (-(((2 * (m : ℝ) + 1) * Real.pi : ℝ) : ℂ) * I) := by
      rw [← hy]
      simp only [s]
      push_cast
      ring
    rw [harg, Complex.exp_add, hexp_odd, ← ofReal_exp, mul_comm (1 - σ),
      ← Real.rpow_def_of_pos two_pos]
    ring
  have h1sub : 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
    rw [hpow, sub_neg_eq_add, ← ofReal_one, ← ofReal_add, norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith [Real.rpow_pos_of_pos two_pos (1 - σ)]
  have hmain := norm_one_sub_two_cpow_mul_riemannZeta_le (s := s) (by simpa [s] using hσ) hs1
  rw [norm_mul, show s.re = σ by simp [s] ] at hmain
  exact (le_mul_of_one_le_left (norm_nonneg _) h1sub).trans hmain

private theorem norm_riemannZeta_add_zetaCutHeight_le {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    ‖riemannZeta ((σ : ℂ) + zetaCutHeight k * I)‖ ≤ ‖(σ : ℂ) + zetaCutHeight k * I‖ / σ := by
  refine norm_riemannZeta_le_of_mul_log_two_eq hσ (m := k) ?_
  unfold zetaCutHeight
  rw [div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
  norm_cast

private theorem norm_riemannZeta_sub_zetaCutHeight_le {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    ‖riemannZeta ((σ : ℂ) - zetaCutHeight k * I)‖ ≤ ‖(σ : ℂ) - zetaCutHeight k * I‖ / σ := by
  have heq : (σ : ℂ) - zetaCutHeight k * I = (σ : ℂ) + ((-zetaCutHeight k : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [heq]
  exact norm_riemannZeta_le_of_mul_log_two_eq hσ (y := -zetaCutHeight k) (m := -(k : ℤ) - 1) (by
    unfold zetaCutHeight
    rw [neg_mul, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
    push_cast
    ring)

/-- Any Dirichlet L-function (principal or nonprincipal) grows at most linearly in `1 + ‖s‖` on
`Re s ≥ σ₁ > 0` wherever `ζ(s)` satisfies a linear bound in `1 + ‖s‖`. -/
private theorem norm_LFunction_le_of_norm_riemannZeta_le {L : ℕ} [NeZero L]
    (ρ : DirichletCharacter ℂ L) {σ₁ Cζ : ℝ} (hσ₁ : 0 < σ₁) {s : ℂ}
    (hs : σ₁ ≤ s.re) (hs1 : s ≠ 1) (hζ : ‖riemannZeta s‖ ≤ Cζ * (1 + ‖s‖)) :
    ‖ρ.LFunction s‖ ≤ max ((L : ℝ) / σ₁) ((2 : ℝ) ^ L.primeFactors.card * Cζ) * (1 + ‖s‖) := by
  have hs0 : 0 < s.re := hσ₁.trans_le hs
  by_cases hρ : ρ = 1
  · subst hρ
    rw [show (1 : DirichletCharacter ℂ L).LFunction s = LFunctionTrivChar L s from rfl,
      LFunctionTrivChar_eq_mul_riemannZeta hs1, norm_mul]
    have hprod : ‖∏ p ∈ L.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ (2 : ℝ) ^ L.primeFactors.card := by
      rw [norm_prod]
      calc
        ∏ p ∈ L.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖
          ≤ ∏ _p ∈ L.primeFactors, (2 : ℝ) := by
            refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun p hp ↦ ?_
            have hp_prime := Nat.prime_of_mem_primeFactors hp
            have hcpow : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
              rw [norm_natCast_cpow_of_pos hp_prime.pos, neg_re]
              exact Real.rpow_le_one_of_one_le_of_nonpos (mod_cast hp_prime.one_lt.le) (by linarith)
            linarith [norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s)), norm_one (α := ℂ)]
        _ = (2 : ℝ) ^ L.primeFactors.card := by simp
    calc
      ‖∏ p ∈ L.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖
        ≤ (2 : ℝ) ^ L.primeFactors.card * (Cζ * (1 + ‖s‖)) :=
          mul_le_mul hprod hζ (norm_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ L.primeFactors.card * Cζ) * (1 + ‖s‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · calc
      ‖ρ.LFunction s‖ ≤ (L : ℝ) * ‖s‖ / s.re := ρ.norm_LFunction_le_level_mul_norm_div_re hρ hs0
      _ ≤ (L : ℝ) * (1 + ‖s‖) / σ₁ := by
        gcongr
        linarith
      _ = ((L : ℝ) / σ₁) * (1 + ‖s‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- Points on the vertical lines `Re s = σ₁`, `Re s = 2`, or the horizontal segments
`[σ₁, 2] ± i Tₖ`. -/
private def OnShiftedContour (σ₁ : ℝ) (s : ℂ) : Prop :=
  s.re = σ₁ ∨ s.re = 2 ∨
    ∃ k : ℕ, s.re ∈ Set.Icc σ₁ 2 ∧ (s.im = zetaCutHeight k ∨ s.im = -zetaCutHeight k)

private theorem onShiftedContour_re_ge {σ₁ : ℝ} {s : ℂ} (hσ₁ : σ₁ < 1)
    (hs : OnShiftedContour σ₁ s) : σ₁ ≤ s.re := by
  rcases hs with h | h | ⟨_, hI, _⟩
  · linarith
  · linarith
  · exact hI.1

private theorem onShiftedContour_ne_one {σ₁ : ℝ} {s : ℂ} (hσ₁ : σ₁ < 1)
    (hs : OnShiftedContour σ₁ s) : s ≠ 1 := by
  rcases hs with h | h | ⟨k, _, him⟩
  · intro heq; simp [heq] at h; linarith
  · intro heq; simp [heq] at h
  · intro heq
    have hpos := zetaCutHeight_pos k
    rcases him with hi | hi <;> simp [heq] at hi <;> linarith

/-- Uniform linear growth of `ζ(s)` across `OnShiftedContour σ₁`. -/
private theorem exists_norm_riemannZeta_le_onShiftedContour {σ₁ : ℝ} (hσ₁ : 0 < σ₁)
    (hσ₁1 : σ₁ < 1) :
    ∃ Cζ : ℝ, 0 < Cζ ∧ ∀ {s : ℂ}, OnShiftedContour σ₁ s →
      ‖riemannZeta s‖ ≤ Cζ * (1 + ‖s‖) := by
  let Cζ : ℝ := max (1 / (σ₁ * |1 - (2 : ℝ) ^ (1 - σ₁)|))
    (max (1 / (2 * |1 - (2 : ℝ) ^ (1 - (2 : ℝ))|)) (1 / σ₁))
  refine ⟨Cζ, lt_max_of_lt_right (lt_max_of_lt_right (div_pos one_pos hσ₁)), fun {s} hs ↦ ?_⟩
  rcases hs with h | h | ⟨k, hI, him⟩
  · have hb := norm_riemannZeta_le_of_re_ne_one (s := s) (by linarith) (by linarith)
    rw [h] at hb
    refine (hb.trans ?_).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [one_div_mul_eq_div]
    gcongr
    linarith
  · have hb := norm_riemannZeta_le_of_re_ne_one (s := s) (by linarith) (by linarith)
    rw [h] at hb
    refine (hb.trans ?_).trans
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (by positivity))
    rw [one_div_mul_eq_div]
    gcongr
    linarith
  · have hs_eq : s = (s.re : ℂ) + s.im * I := (re_add_im s).symm
    have hb : ‖riemannZeta s‖ ≤ ‖s‖ / s.re := by
      rw [hs_eq]
      rcases him with hi | hi
      · rw [hi]; simpa [← hs_eq] using norm_riemannZeta_add_zetaCutHeight_le (hσ₁.trans_le hI.1) k
      · rw [hi, ofReal_neg, neg_mul, ← sub_eq_add_neg]
        simpa [sub_eq_add_neg, neg_mul, ← hs_eq] using
          norm_riemannZeta_sub_zetaCutHeight_le (hσ₁.trans_le hI.1) k
    calc
      ‖riemannZeta s‖ ≤ ‖s‖ / s.re := hb
      _ ≤ (1 + ‖s‖) / σ₁ := by have := hI.1; gcongr; linarith
      _ = (1 / σ₁) * (1 + ‖s‖) := by ring
      _ ≤ Cζ * (1 + ‖s‖) :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)

/-- Uniform `O((1 + ‖s‖) ^ 4)` growth of the four-factor product along `OnShiftedContour σ₁`. -/
private theorem exists_norm_pair_le_pow_four {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {σ₁ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ {s : ℂ}, OnShiftedContour σ₁ s →
      ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
        B * (1 + ‖s‖) ^ 4 := by
  obtain ⟨Cζ, hCζ_pos, hζ_bound⟩ := exists_norm_riemannZeta_le_onShiftedContour hσ₁ hσ₁1
  let C₁ : ℝ := (M : ℝ) / σ₁
  let C₂ : ℝ := (N : ℝ) / σ₁
  let C₃ : ℝ := max ((Nat.lcm M N : ℝ) / σ₁) ((2 : ℝ) ^ (Nat.lcm M N).primeFactors.card * Cζ)
  refine ⟨Cζ * C₁ * C₂ * C₃ + 1, by positivity, fun {s} hs ↦ ?_⟩
  have hre : σ₁ ≤ s.re := onShiftedContour_re_ge hσ₁1 hs
  have hs_ne : s ≠ 1 := onShiftedContour_ne_one hσ₁1 hs
  have hζ : ‖riemannZeta s‖ ≤ Cζ * (1 + ‖s‖) := hζ_bound hs
  have hL {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρ : ρ ≠ 1) :
      ‖ρ.LFunction s‖ ≤ ((L : ℝ) / σ₁) * (1 + ‖s‖) := by
    calc
      ‖ρ.LFunction s‖ ≤ (L : ℝ) * ‖s‖ / s.re :=
        ρ.norm_LFunction_le_level_mul_norm_div_re hρ (hσ₁.trans_le hre)
      _ ≤ (L : ℝ) * (1 + ‖s‖) / σ₁ := by gcongr; linarith
      _ = ((L : ℝ) / σ₁) * (1 + ‖s‖) := by ring
  have hχψb : ‖(χ.mul ψ).LFunction s‖ ≤ C₃ * (1 + ‖s‖) :=
    norm_LFunction_le_of_norm_riemannZeta_le (χ.mul ψ) hσ₁ hre hs_ne hζ
  rw [norm_mul, norm_mul, norm_mul]
  calc
    ‖riemannZeta s‖ * ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(χ.mul ψ).LFunction s‖
      ≤ (Cζ * (1 + ‖s‖)) * (C₁ * (1 + ‖s‖)) * (C₂ * (1 + ‖s‖)) * (C₃ * (1 + ‖s‖)) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul hζ (hL χ hχ) (norm_nonneg _) (by positivity))
            (hL ψ hψ) (norm_nonneg _) (by positivity))
          hχψb (norm_nonneg _) (by positivity)
    _ = (Cζ * C₁ * C₂ * C₃) * (1 + ‖s‖) ^ 4 := by ring
    _ ≤ (Cζ * C₁ * C₂ * C₃ + 1) * (1 + ‖s‖) ^ 4 := by gcongr; linarith

end Growth

section ContourShift

/-- At `s = β`, `s ↦ x ^ (-(s - β)) (Γ(s - β) F(s))` is meromorphic with residue `F(β)` whenever
`F` is analytic at `β` and `x > 0`, even if `F(β) = 0`. -/
private theorem meromorphicAt_and_residue_at_beta {F : ℂ → ℂ} {β x : ℝ} (hx : 0 < x)
    (hF : AnalyticAt ℂ F β) :
    MeromorphicAt (fun s : ℂ ↦ (x : ℂ) ^ (-(s - β)) * (Gamma (s - β) * F s)) β ∧
      TauCeti.Contour.residue
        (fun s : ℂ ↦ (x : ℂ) ^ (-(s - β)) * (Gamma (s - β) * F s)) β = F β := by
  let h : ℂ → ℂ := fun s ↦ (x : ℂ) ^ (-(s - β)) * Gamma (s - β + 1) * F s
  have hx_slit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hΓ_an : AnalyticAt ℂ (fun s : ℂ ↦ Gamma (s - β + 1)) β := by
    refine (Complex.analyticAt_Gamma fun n hn ↦ ?_).comp (by fun_prop)
    have hre := congrArg re hn
    simp only [sub_self, zero_add, one_re, neg_re, natCast_re] at hre
    linarith [n.cast_nonneg' (α := ℝ)]
  have hh : AnalyticAt ℂ h β :=
    ((analyticAt_const.cpow (by fun_prop) hx_slit).mul hΓ_an).mul hF
  have he : (fun s : ℂ ↦ (x : ℂ) ^ (-(s - β)) * (Gamma (s - β) * F s)) =ᶠ[𝓝[≠] (β : ℂ)]
      fun s ↦ (s - β) ^ (-1 : ℤ) • h s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsub : s - (β : ℂ) ≠ 0 := sub_ne_zero.mpr hs
    simp only [h, smul_eq_mul, zpow_neg_one, Complex.Gamma_add_one (s - β) hsub]
    field_simp
  refine ⟨MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-1, h, hh, he⟩, ?_⟩
  have hres := TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by norm_num : (-1 : ℤ) ≤ -1)
    hh he
  simpa [h, iteratedDeriv_zero, Complex.Gamma_one] using hres

/-- A vertically polynomially bounded function `F(w + β)` (`O((1 + ‖w + β‖) ^ 4)`) multiplied by
`Γ(w)` is vertically integrable on every line `Re w = σ - β` avoiding the poles of `Γ`. -/
private theorem verticalIntegrable_Gamma_mul_of_pow_four {F : ℂ → ℂ} {σ β B : ℝ}
    (hpoles : ∀ n : ℕ, σ - β ≠ -n) (hB : 0 ≤ B)
    (hcont : Continuous fun t : ℝ ↦ F ((σ : ℂ) + t * I))
    (hbound : ∀ t : ℝ, ‖F ((σ : ℂ) + t * I)‖ ≤ B * (1 + ‖(σ : ℂ) + t * I‖) ^ 4) :
    VerticalIntegrable (fun w : ℂ ↦ Gamma w * F (w + β)) (σ - β) := by
  obtain ⟨CΓ, hCΓ⟩ := Complex.exists_norm_Gamma_le_mul_inv_one_add_sq_pow hpoles 3
  have : 0 ≤ CΓ := by
    have := (norm_nonneg _).trans (hCΓ 0)
    simpa using this
  let K : ℝ := (1 + |σ|) ^ 2 + 1
  have hshift (t : ℝ) : ((σ - β : ℝ) : ℂ) + t * I + β = (σ : ℂ) + t * I := by push_cast; ring
  refine (integrable_inv_one_add_sq.const_mul (CΓ * B * K ^ 2)).mono' ?_
    (Eventually.of_forall fun t ↦ ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous fun t : ℝ ↦ Gamma (((σ - β : ℝ) : ℂ) + t * I) :=
      continuous_iff_continuousAt.mpr fun t ↦
        (Complex.differentiableAt_Gamma _ fun m hm ↦ hpoles m (by
          simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    have h2 : Continuous fun t : ℝ ↦ F (((σ - β : ℝ) : ℂ) + t * I + β) := by
      simpa only [hshift] using hcont
    exact h1.mul h2
  · dsimp only
    rw [hshift, norm_mul]
    have hnorm_le : (1 + ‖(σ : ℂ) + t * I‖) ^ 2 ≤ K * (1 + t ^ 2) := by
      have htri : ‖(σ : ℂ) + t * I‖ ≤ |σ| + |t| :=
        (norm_add_le _ _).trans (by simp [Complex.norm_real])
      have hsq : (1 + ‖(σ : ℂ) + t * I‖) ^ 2 ≤ (1 + |σ| + |t|) ^ 2 := by
        nlinarith [norm_nonneg ((σ : ℂ) + t * I), htri]
      have hcauchy : (1 + |σ| + |t|) ^ 2 ≤ ((1 + |σ|) ^ 2 + 1) * (1 + t ^ 2) := by
        nlinarith [sq_nonneg ((1 + |σ|) * |t| - 1), sq_abs t, abs_nonneg σ, abs_nonneg t]
      exact hsq.trans hcauchy
    have hpow4 : (1 + ‖(σ : ℂ) + t * I‖) ^ 4 ≤ K ^ 2 * (1 + t ^ 2) ^ 2 := by
      calc
        (1 + ‖(σ : ℂ) + t * I‖) ^ 4 = ((1 + ‖(σ : ℂ) + t * I‖) ^ 2) ^ 2 := by ring
        _ ≤ (K * (1 + t ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hnorm_le 2
        _ = K ^ 2 * (1 + t ^ 2) ^ 2 := by ring
    have : 0 < 1 + t ^ 2 := by positivity
    calc
      ‖Gamma (((σ - β : ℝ) : ℂ) + t * I)‖ * ‖F ((σ : ℂ) + t * I)‖
        ≤ (CΓ * ((1 + t ^ 2) ^ 3)⁻¹) * (B * (1 + ‖(σ : ℂ) + t * I‖) ^ 4) :=
          mul_le_mul (hCΓ t) (hbound t) (norm_nonneg _) (by positivity)
      _ ≤ (CΓ * ((1 + t ^ 2) ^ 3)⁻¹) * (B * (K ^ 2 * (1 + t ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow4 hB) (by positivity)
      _ = CΓ * B * K ^ 2 * (1 + t ^ 2)⁻¹ := by field_simp

/-- Rapid `O(Tₖ ^ (-6))` decay of `Γ(s - β)` along horizontal cuts `Im s = ± Tₖ`. -/
private theorem norm_Gamma_sub_le_on_zetaCutHeight {σ₁ β σ sgn : ℝ} (hσ₁ : 0 < σ₁)
    (hβ0 : 0 < β) (hβ : β < 1) (hσI : σ ∈ Set.Icc σ₁ 2) (hsgn : sgn = 1 ∨ sgn = -1) (k : ℕ) :
    ‖Gamma (((σ : ℂ) + (sgn * zetaCutHeight k : ℝ) * I) - β)‖ ≤
      8 * Real.Gamma 8 * ((1 + zetaCutHeight k ^ 2) ^ 3)⁻¹ := by
  set y : ℝ := sgn * zetaCutHeight k
  set s : ℂ := (σ : ℂ) + y * I
  have hre6 : 5 ≤ (s - (β : ℂ)).re + 6 ∧ (s - (β : ℂ)).re + 6 ≤ 8 := by
    simp only [s, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    exact ⟨by linarith [hσI.1], by linarith [hσI.2]⟩
  have hΓ_re : Real.Gamma ((s - (β : ℂ)).re + 6) ≤ Real.Gamma 8 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (by linarith [hre6.1] : (2 : ℝ) ≤ _) (by norm_num)
      hre6.2
  have hΓ_prod := (Complex.norm_Gamma_mul_prod_norm_le (s := s - β) (n := 6)
    (by push_cast; linarith [hre6.1])).trans hΓ_re
  have hTk_ge_one : 1 ≤ zetaCutHeight k := by
    unfold zetaCutHeight
    rw [one_le_div (Real.log_pos one_lt_two)]
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hlog2, Real.two_le_pi, k.cast_nonneg (α := ℝ)]
  have hprod_lo : ((1 + zetaCutHeight k ^ 2) / 2) ^ 3 ≤
      ∏ j ∈ Finset.range 6, ‖s - (β : ℂ) + j‖ := by
    have hfac (j : ℕ) : (1 + zetaCutHeight k ^ 2) / 2 ≤ ‖s - (β : ℂ) + j‖ ^ 2 := by
      have habs : zetaCutHeight k ≤ ‖s - (β : ℂ) + j‖ := by
        have := abs_im_le_norm (s - (β : ℂ) + j)
        rw [show (s - (β : ℂ) + j).im = y by simp [s] ] at this
        rcases hsgn with h | h <;> simpa [y, h, abs_of_pos (zetaCutHeight_pos k)] using this
      nlinarith [norm_nonneg (s - (β : ℂ) + j), hTk_ge_one, habs]
    have h6 : (((1 + zetaCutHeight k ^ 2) / 2) ^ 3) ^ 2 ≤
        (∏ j ∈ Finset.range 6, ‖s - (β : ℂ) + j‖) ^ 2 := by
      rw [← Finset.prod_pow, show (((1 + zetaCutHeight k ^ 2) / 2) ^ 3) ^ 2 =
          ∏ _j ∈ Finset.range 6, ((1 + zetaCutHeight k ^ 2) / 2) by simp; ring]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ hfac j
    exact le_of_pow_le_pow_left₀ two_ne_zero
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) h6
  have hpos : 0 < ((1 + zetaCutHeight k ^ 2) / 2) ^ 3 := by positivity
  have hle := (mul_le_mul_of_nonneg_left hprod_lo (norm_nonneg (Gamma (s - β)))).trans hΓ_prod
  rw [← le_div_iff₀ hpos] at hle
  exact hle.trans_eq (by field_simp; ring)

/-- Along horizontal segments `[σ₁, 2] ± i Tₖ`, the `O(Tₖ ^ (-6))` decay of `Γ(s - β)` dominates
the `O((1 + ‖s‖) ^ 4)` growth of `F(s)`, so the horizontal edge integrals tend to zero. -/
private theorem tendsto_horizontal_integral_zero {F : ℂ → ℂ} {σ₁ β x B : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₁β : σ₁ < β) (hβ : β < 1) (hx : 0 < x) (hB : 0 ≤ B) (sgn : ℝ)
    (hsgn : sgn = 1 ∨ sgn = -1)
    (hbound : ∀ k : ℕ, ∀ σ ∈ Set.Icc σ₁ 2,
      ‖F ((σ : ℂ) + (sgn * zetaCutHeight k : ℝ) * I)‖ ≤
        B * (1 + ‖(σ : ℂ) + (sgn * zetaCutHeight k : ℝ) * I‖) ^ 4) :
    Tendsto (fun k : ℕ ↦ ∫ σ : ℝ in σ₁..2,
      (x : ℂ) ^ (-(((σ : ℂ) + (sgn * zetaCutHeight k : ℝ) * I) - β)) *
        (Gamma (((σ : ℂ) + (sgn * zetaCutHeight k : ℝ) * I) - β) *
          F ((σ : ℂ) + (sgn * zetaCutHeight k : ℝ) * I))) atTop (𝓝 0) := by
  let Xmax : ℝ := max (x ^ (β - σ₁)) (x ^ (β - 2))
  let C : ℝ := Xmax * (8 * Real.Gamma 8) * (B * 100)
  have hσ₁2 : σ₁ ≤ 2 := (hσ₁β.trans hβ).le.trans (by norm_num)
  have hXmax0 : 0 ≤ Xmax := le_trans (by positivity) (le_max_left _ _)
  have hlim : Tendsto (fun k : ℕ ↦ C * (1 + zetaCutHeight k ^ 2)⁻¹ * |2 - σ₁|) atTop (𝓝 0) := by
    have hsq : Tendsto (fun k : ℕ ↦ 1 + zetaCutHeight k ^ 2) atTop atTop :=
      tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num) |>.comp
        tendsto_zetaCutHeight_atTop)
    simpa using (tendsto_inv_atTop_zero.comp hsq).const_mul C |>.mul_const |2 - σ₁|
  refine squeeze_zero_norm (fun k ↦ ?_) hlim
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ_mem ↦ ?_
  rw [Set.uIoc_of_le hσ₁2] at hσ_mem
  have hσI : σ ∈ Set.Icc σ₁ 2 := Set.Ioc_subset_Icc_self hσ_mem
  set y : ℝ := sgn * zetaCutHeight k
  set s : ℂ := (σ : ℂ) + y * I
  have hxpow : ‖(x : ℂ) ^ (-(s - β))‖ ≤ Xmax := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, show (-(s - (β : ℂ))).re = β - σ by simp [s] ]
    rcases le_or_gt x 1 with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [hσI.2])).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [hσI.1])).trans (le_max_left _ _)
  have hΓ_bound := norm_Gamma_sub_le_on_zetaCutHeight hσ₁ (hσ₁.trans hσ₁β) hβ hσI hsgn k
  have hF_bound : ‖F s‖ ≤ B * 100 * (1 + zetaCutHeight k ^ 2) ^ 2 := by
    have htri : 1 + ‖s‖ ≤ 3 + zetaCutHeight k := by
      have h1 : ‖s‖ ≤ |σ| + |y| := (norm_add_le _ _).trans (by simp [Complex.norm_real])
      have hσ_abs : |σ| ≤ 2 := abs_le.mpr ⟨by linarith [hσI.1], hσI.2⟩
      have hy_abs : |y| = zetaCutHeight k := by
        rcases hsgn with h | h <;> simp [y, h, abs_of_pos (zetaCutHeight_pos k)]
      linarith [h1, hσ_abs, hy_abs]
    have hsq : (1 + ‖s‖) ^ 2 ≤ 10 * (1 + zetaCutHeight k ^ 2) :=
      (pow_le_pow_left₀ (by positivity) htri 2).trans
        (by nlinarith [sq_nonneg (3 * zetaCutHeight k - 1)])
    have hpow4 : (1 + ‖s‖) ^ 4 ≤ 100 * (1 + zetaCutHeight k ^ 2) ^ 2 := by
      calc
        (1 + ‖s‖) ^ 4 = ((1 + ‖s‖) ^ 2) ^ 2 := by ring
        _ ≤ (10 * (1 + zetaCutHeight k ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
        _ = 100 * (1 + zetaCutHeight k ^ 2) ^ 2 := by ring
    exact (hbound k σ hσI).trans (by nlinarith [hpow4])
  have : 0 ≤ Real.Gamma 8 := (Real.Gamma_pos_of_pos (by norm_num)).le
  have : 0 < 1 + zetaCutHeight k ^ 2 := by positivity
  rw [norm_mul, norm_mul]
  calc
    ‖(x : ℂ) ^ (-(s - β))‖ * (‖Gamma (s - β)‖ * ‖F s‖)
      ≤ Xmax * ((8 * Real.Gamma 8 * ((1 + zetaCutHeight k ^ 2) ^ 3)⁻¹) *
          (B * 100 * (1 + zetaCutHeight k ^ 2) ^ 2)) :=
        mul_le_mul hxpow (mul_le_mul hΓ_bound hF_bound (norm_nonneg _) (by positivity))
          (by positivity) hXmax0
    _ = C * (1 + zetaCutHeight k ^ 2)⁻¹ := by
      dsimp only [C]
      field_simp

/-- Analyticity of the Mellin weight `s ↦ Γ(s - β) x ^ (-(s - β))` at `s = 1` for `β < 1` and
`x > 0`. -/
private theorem analyticAt_Gamma_sub_mul_cpow_one {β x : ℝ} (hβ : β < 1) (hx : 0 < x) :
    AnalyticAt ℂ (fun s : ℂ ↦ Gamma (s - β) * (x : ℂ) ^ (-(s - β))) 1 := by
  refine ((Complex.analyticAt_Gamma fun n hn ↦ ?_).comp (by fun_prop)).mul
    (analyticAt_const.cpow (by fun_prop) (ofReal_mem_slitPlane.mpr hx))
  have hre := congrArg re hn
  simp only [sub_re, one_re, ofReal_re, neg_re, natCast_re] at hre
  linarith [n.cast_nonneg' (α := ℝ)]

/-- Holomorphy of `s ↦ x ^ (-(s - β)) (Γ(s - β) F(s))` on `{Re s > 0} \ {1, β}` when `β < 1` and
`F` is holomorphic on `{Re s > 0} \ {1}`. -/
private theorem differentiableOn_shifted_integrand {F : ℂ → ℂ} {β x : ℝ} (hβ : β < 1) (hx : 0 < x)
    (hF_diff : DifferentiableOn ℂ F ({s : ℂ | 0 < s.re} \ {(1 : ℂ)})) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (x : ℂ) ^ (-(s - β)) * (Gamma (s - β) * F s))
      ({s : ℂ | 0 < s.re} \ (↑({1, (β : ℂ)} : Finset ℂ) : Set ℂ)) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  intro s ⟨hsU, hsS⟩
  have hs1 : s ≠ 1 := fun h ↦ hsS (by simp [h])
  have hsβ : s ≠ (β : ℂ) := fun h ↦ hsS (by simp [h])
  have hpoles : ∀ n : ℕ, s - (β : ℂ) ≠ -n := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · exact sub_ne_zero.mpr hsβ (by simpa using hn)
    · have hre := congrArg re hn
      simp only [sub_re, ofReal_re, neg_re, natCast_re] at hre
      have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn0)
      have : (0 : ℝ) < s.re := hsU
      linarith
  have hF_at : DifferentiableAt ℂ F s :=
    hF_diff.differentiableAt ((hU.sdiff isClosed_singleton).mem_nhds ⟨hsU, hs1⟩)
  have h1 : DifferentiableAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (-(z - (β : ℂ)))) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have h2 : DifferentiableAt ℂ (fun z : ℂ ↦ Gamma (z - (β : ℂ))) s :=
    DifferentiableAt.comp s (Complex.differentiableAt_Gamma _ hpoles) (by fun_prop)
  exact (h1.mul (h2.mul hF_at)).differentiableWithinAt

/-- Rectangle residue identity on `[σ₁, 2] × [-Tₖ, Tₖ]` enclosing the two poles `1` and `β`. -/
private theorem rectBoundary_shifted_eq {g : ℂ → ℂ} {σ₁ β : ℝ} {Rβ : ℂ}
    (hσ₁ : 0 < σ₁) (hσ₁β : σ₁ < β) (hβ : β < 1)
    (hg_diff : DifferentiableOn ℂ g
      ({s : ℂ | 0 < s.re} \ (↑({1, (β : ℂ)} : Finset ℂ) : Set ℂ)))
    (hmero_1 : MeromorphicAt g 1) (hmero_β : MeromorphicAt g β)
    (hres_β : TauCeti.Contour.residue g β = Rβ) (k : ℕ) :
    (∫ σ : ℝ in σ₁..2, g ((σ : ℂ) + (-1 * zetaCutHeight k : ℝ) * I)) -
      (∫ σ : ℝ in σ₁..2, g ((σ : ℂ) + (1 * zetaCutHeight k : ℝ) * I)) +
      I • (∫ y : ℝ in -zetaCutHeight k..zetaCutHeight k, g ((2 : ℂ) + y * I)) -
      I • (∫ y : ℝ in -zetaCutHeight k..zetaCutHeight k, g ((σ₁ : ℂ) + y * I)) =
    2 * (Real.pi : ℂ) * I * (TauCeti.Contour.residue g 1 + Rβ) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  let S : Finset ℂ := {1, (β : ℂ)}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have h1β : (1 : ℂ) ≠ (β : ℂ) := by exact_mod_cast hβ.ne'
  set T : ℝ := zetaCutHeight k
  have : 0 < T := zetaCutHeight_pos k
  set z : ℂ := (σ₁ : ℂ) - T * I
  set w : ℂ := 2 + T * I
  have hz_re : z.re = σ₁ := by simp [z]
  have hz_im : z.im = -T := by simp [z]
  have hw_re : w.re = 2 := by simp [w]
  have hw_im : w.im = T := by simp [w]
  have hrect_sub_U : Rectangle z w ⊆ U := by
    intro p hp
    rw [Rectangle, mem_reProdIm, hz_re, hw_re, uIcc_of_le (by linarith)] at hp
    exact hσ₁.trans_le hp.1.1
  have hfr_disj : ∀ p ∈ frontier (Rectangle z w), p ∉ (↑S : Set ℂ) := by
    intro p hp hpS
    rw [frontier_rectangle, hz_re, hw_re, hz_im, hw_im, uIcc_of_le (by linarith),
      uIcc_of_le (by linarith)] at hp
    have hp_cases : p = 1 ∨ p = (β : ℂ) := by simpa [S] using hpS
    rcases hp with ⟨_, hp_im⟩ | ⟨hp_re, _⟩
    · rcases hp_im with hp_im | hp_im <;> rcases hp_cases with rfl | rfl <;>
        simp at hp_im <;> linarith
    · rcases hp_re with hp_re | hp_re <;> rcases hp_cases with rfl | rfl <;>
        simp at hp_re <;> linarith
  have hcont_fr : ContinuousOn g (frontier (Rectangle z w)) :=
    (hg_diff.continuousOn).mono fun p hp ↦
      ⟨hrect_sub_U ((isClosed_rectangle z w).frontier_subset hp), hfr_disj p hp⟩
  have hres := TauCeti.Contour.classicalResidueTheorem_nullHomologous hU hg_diff
    (fun s hs _ ↦ by
      rcases (by simpa [S] using hs : s = 1 ∨ s = (β : ℂ)) with rfl | rfl
      · exact hmero_1
      · exact hmero_β)
    (isPiecewiseC1On_rectBoundary z w)
    (fun t _ ↦ hrect_sub_U (rectBoundary_mem_rectangle t))
    (by simp)
    (fun t _ ↦ hfr_disj _ (rectBoundary_mem_frontier t))
    (TauCeti.Contour.isNullHomologous_rectBoundary hrect_sub_U)
  rw [integral_rectBoundary hcont_fr, Finset.sum_pair h1β,
    TauCeti.Contour.windingNumber_rectBoundary_eq_one
      ⟨⟨by simp [hz_re]; linarith, by simp [hw_re]⟩,
        by simp [hz_im]; linarith, by simp [hw_im]; linarith⟩,
    TauCeti.Contour.windingNumber_rectBoundary_eq_one
      ⟨⟨by simp [hz_re]; linarith, by simp [hw_re]; linarith⟩,
        by simp [hz_im]; linarith, by simp [hw_im]; linarith⟩,
    one_mul, one_mul, hres_β] at hres
  simpa [hz_re, hw_re, hz_im, hw_im] using hres

/-- Shifting the Mellin inverse of `w ↦ Γ(w) F(w + β)` from `Re s = 2` to `Re s = σ₁` picks up
the residue at `s = 1` and `F(β)` at `s = β`. -/
private theorem mellinInv_two_sub_eq_residue_add_eval_add_mellinInv
    {M N : ℕ} [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) {σ₁ β x : ℝ} (hσ₁ : 0 < σ₁) (hσ₁β : σ₁ < β) (hβ : β < 1)
    (hx : 0 < x) :
    let F : ℂ → ℂ := fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s
    mellinInv (2 - β) (fun w ↦ Gamma w * F (w + β)) x =
      TauCeti.Contour.residue (fun s ↦ F s * (Gamma (s - β) * (x : ℂ) ^ (-(s - β)))) 1 +
        F β + mellinInv (σ₁ - β) (fun w ↦ Gamma w * F (w + β)) x := by
  intro F
  let g : ℂ → ℂ := fun s ↦ (x : ℂ) ^ (-(s - β)) * (Gamma (s - β) * F s)
  have hg_comm : g = fun s ↦ F s * (Gamma (s - β) * (x : ℂ) ^ (-(s - β))) := by
    funext s; dsimp only [g]; ring
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hF_diff : DifferentiableOn ℂ F (U \ {(1 : ℂ)}) := fun s hs ↦
    ((((differentiableAt_riemannZeta hs.2).mul (differentiable_LFunction hχ s)).mul
      (differentiable_LFunction hψ s)).mul
      ((χ.mul ψ).differentiableAt_LFunction s (.inl hs.2))).differentiableWithinAt
  have hg_diff := differentiableOn_shifted_integrand hβ hx hF_diff
  have hF_an_β : AnalyticAt ℂ F β :=
    (hF_diff.analyticOnNhd (hU.sdiff isClosed_singleton)) β
      ⟨by simpa [U] using hσ₁.trans hσ₁β, Set.notMem_singleton_iff.mpr (by exact_mod_cast hβ.ne)⟩
  obtain ⟨hmero_β, hres_β⟩ := meromorphicAt_and_residue_at_beta hx hF_an_β
  have hmero_1 : MeromorphicAt g 1 := by
    have hF_mero : MeromorphicAt F 1 := by
      by_cases hχψ : χ.mul ψ = 1
      · exact meromorphicAt_of_meromorphicOrderAt_ne_zero
          (by rw [meromorphicOrderAt_pair_eq_neg_two χ ψ hχ hψ hχψ]; decide)
      · exact meromorphicAt_of_meromorphicOrderAt_ne_zero
          (by rw [meromorphicOrderAt_pair_eq_neg_one χ ψ hχ hψ hχψ]; decide)
    rw [hg_comm]
    exact hF_mero.mul (analyticAt_Gamma_sub_mul_cpow_one hβ hx).meromorphicAt
  obtain ⟨B, hB, hB_bound⟩ := exists_norm_pair_le_pow_four χ ψ hχ hψ hσ₁ (hσ₁β.trans hβ)
  have hcont_line (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≠ 1) :
      Continuous fun y : ℝ ↦ F ((σ : ℂ) + y * I) :=
    (hF_diff.continuousOn.comp_continuous (by fun_prop) fun y ↦
      ⟨by simpa [U] using hσ0, fun h ↦ hσ1 (by simpa using congrArg re h)⟩)
  have hv2 : VerticalIntegrable (fun w : ℂ ↦ Gamma w * F (w + β)) (2 - β) :=
    verticalIntegrable_Gamma_mul_of_pow_four
      (fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]) hB.le
      (hcont_line 2 two_pos (by norm_num)) (fun y ↦ hB_bound (Or.inr (Or.inl (by simp))))
  have hv1 : VerticalIntegrable (fun w : ℂ ↦ Gamma w * F (w + β)) (σ₁ - β) :=
    verticalIntegrable_Gamma_mul_of_pow_four
      (fun n hn ↦ by
        rcases eq_or_ne n 0 with rfl | hn0
        · simp at hn; linarith
        · linarith [(Nat.one_le_cast (α := ℝ)).mpr (Nat.pos_of_ne_zero hn0)])
      hB.le (hcont_line σ₁ hσ₁ (hσ₁β.trans hβ).ne) (fun y ↦ hB_bound (Or.inl (by simp)))
  have hg_line (σ y : ℝ) :
      (x : ℂ) ^ (-(((σ - β : ℝ) : ℂ) + y * I)) •
        (Gamma (((σ - β : ℝ) : ℂ) + y * I) * F (((σ - β : ℝ) : ℂ) + y * I + β)) =
      g ((σ : ℂ) + y * I) := by
    rw [show (((σ - β : ℝ) : ℂ) + y * I + β) = (σ : ℂ) + y * I by push_cast; ring,
      show (((σ - β : ℝ) : ℂ) + y * I) = ((σ : ℂ) + y * I) - β by push_cast; ring]
    simp only [g, smul_eq_mul]
  have hbot := tendsto_horizontal_integral_zero (F := F) hσ₁ hσ₁β hβ hx hB.le (-1) (Or.inr rfl)
    fun k σ hσI ↦ hB_bound (Or.inr (Or.inr ⟨k, by simpa using hσI, Or.inr (by simp)⟩))
  have htop := tendsto_horizontal_integral_zero (F := F) hσ₁ hσ₁β hβ hx hB.le 1 (Or.inl rfl)
    fun k σ hσI ↦ hB_bound (Or.inr (Or.inr ⟨k, by simpa using hσI, Or.inl (by simp)⟩))
  have hright := intervalIntegral_tendsto_integral
    ((hv2.integrable_cpow_smul hx).congr (Eventually.of_forall (hg_line 2)))
    (tendsto_neg_atTop_atBot.comp tendsto_zetaCutHeight_atTop) tendsto_zetaCutHeight_atTop
  have hleft := intervalIntegral_tendsto_integral
    ((hv1.integrable_cpow_smul hx).congr (Eventually.of_forall (hg_line σ₁)))
    (tendsto_neg_atTop_atBot.comp tendsto_zetaCutHeight_atTop) tendsto_zetaCutHeight_atTop
  have heq_lim : (0 : ℂ) - 0 + I • (∫ y : ℝ, g ((2 : ℂ) + y * I)) -
      I • (∫ y : ℝ, g ((σ₁ : ℂ) + y * I)) =
      2 * (Real.pi : ℂ) * I * (TauCeti.Contour.residue g 1 + F β) :=
    tendsto_nhds_unique (((hbot.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I))
      (tendsto_const_nhds.congr' (Eventually.of_forall fun k ↦
        (rectBoundary_shifted_eq hσ₁ hσ₁β hβ hg_diff hmero_1 hmero_β hres_β k).symm))
  have hmellin (σ : ℝ) : mellinInv (σ - β) (fun w ↦ Gamma w * F (w + β)) x =
      (1 / (2 * Real.pi)) • ∫ y : ℝ, g ((σ : ℂ) + y * I) := by
    rw [mellinInv]; congr 1; exact integral_congr_ae (Eventually.of_forall (hg_line σ))
  rw [hmellin 2, hmellin σ₁, ← hg_comm, real_smul, real_smul]
  simp only [zero_sub, neg_zero, zero_add, smul_eq_mul] at heq_lim
  generalize ∫ y : ℝ, g ((2 : ℂ) + y * I) = I₂, ∫ y : ℝ, g ((σ₁ : ℂ) + y * I) = I₁ at heq_lim ⊢
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hπ]
  apply mul_left_cancel₀ I_ne_zero
  linear_combination heq_lim

/-- **Shifted Mellin formula for the four-factor L-function product.** For nonprincipal Dirichlet
characters `χ` and `ψ`, `0 < σ₁ < β < 1`, and `x > 0`, the exponentially smoothed sum of
`aₙ n ^ (-β)` equals the sum of the residue of `F(s) Γ(s - β) x ^ (β - s)` at `s = 1`, the value
`F(β)`, and the shifted Mellin inverse on `Re s = σ₁`. -/
theorem hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {σ₁ β : ℝ} (hσ₁ : 0 < σ₁) (hσ₁β : σ₁ < β) (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x))
      (TauCeti.Contour.residue
        (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
          (Gamma (s - β) * (x : ℂ) ^ (-(s - β)))) 1 +
        riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        mellinInv (σ₁ - β)
          (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
            ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x) := by
  let f : ℕ → ℂ := fun n ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ))
  have hf0 : f 0 = 0 := by simp [f]
  have hsum_f : LSeriesSummable f (2 - β : ℝ) := by
    rw [TauCeti.LSeries.LSeriesSummable_mul_natCast_cpow_neg_iff]
    have h2 : (((2 - β : ℝ) : ℂ) + β) = 2 := by push_cast; ring
    rw [h2]
    exact (LSeriesHasSum_zetaMulPairCoeffs χ ψ (by norm_num)).LSeriesSummable
  have hsm := TauCeti.LSeries.hasSum_mellinInv_Gamma_mul_LSeries hf0 (by linarith : 0 < 2 - β)
    hsum_f hx
  have hmellin_eq : mellinInv (2 - β) (fun w ↦ Gamma w * LSeries f w) x =
      mellinInv (2 - β) (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
        ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x := by
    rw [mellinInv, mellinInv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    have hre : 1 < ((((2 - β : ℝ) : ℂ) + y * I) + β).re := by simp
    dsimp only [f]
    rw [TauCeti.LSeries.LSeries_mul_natCast_cpow_neg,
      (LSeriesHasSum_zetaMulPairCoeffs χ ψ hre).LSeries_eq]
  rw [← mellinInv_two_sub_eq_residue_add_eval_add_mellinInv χ ψ hχ hψ hσ₁ hσ₁β hβ hx,
    ← hmellin_eq]
  exact hsm

/-- **Shifted Mellin formula in the simple-pole case (`χ.mul ψ ≠ 1`).** The pole at `s = 1`
contributes `L(1, χ) L(1, ψ) L(1, χ.mul ψ) Γ(1 - β) x ^ (β - 1)`. -/
theorem hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp_of_mul_ne_one
    {M N : ℕ} [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) {σ₁ β : ℝ} (hσ₁ : 0 < σ₁) (hσ₁β : σ₁ < β)
    (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x))
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
          (Gamma (1 - β) * (x : ℂ) ^ ((β : ℂ) - 1)) +
        riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        mellinInv (σ₁ - β)
          (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
            ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x) := by
  have hres := residue_pair_mul_of_mul_ne_one χ ψ hχ hψ hχψ
    (analyticAt_Gamma_sub_mul_cpow_one hβ hx)
  rw [show -((1 : ℂ) - β) = (β : ℂ) - 1 by ring] at hres
  rw [← hres]
  exact hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp χ ψ hχ hψ hσ₁ hσ₁β hβ hx

/-- **Shifted Mellin formula in the double-pole case (`χ.mul ψ = 1`).** The pole at `s = 1`
contributes the derivative at `1` of the regularized product times `Γ(s - β) x ^ (β - s)`. -/
theorem hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp_of_mul_eq_one
    {M N : ℕ} [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ = 1) {σ₁ β : ℝ} (hσ₁ : 0 < σ₁) (hσ₁β : σ₁ < β)
    (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x))
      (deriv (fun s ↦ LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
          LFunctionTrivChar₁ (Nat.lcm M N) s * (Gamma (s - β) * (x : ℂ) ^ (-(s - β)))) 1 +
        riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        mellinInv (σ₁ - β)
          (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
            ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x) := by
  rw [← residue_pair_mul_of_mul_eq_one χ ψ hχ hψ hχψ
    (analyticAt_Gamma_sub_mul_cpow_one hβ hx)]
  exact hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp χ ψ hχ hψ hσ₁ hσ₁β hβ hx

end ContourShift

section GoldfeldBound

/-- Uniform `O((1 + t ^ 2) ^ (-3))` bound on `Γ(1 / 4 - β + i t)` across `β ∈ [1 / 2, 1)`. -/
private theorem norm_Gamma_quarter_sub_le {β : ℝ} (hβ0 : 1 / 2 ≤ β) (hβ1 : β < 1) (t : ℝ) :
    ‖Gamma (((1 / 4 - β : ℝ) : ℂ) + t * I)‖ ≤
      4 ^ 6 * Real.Gamma 6 * ((1 + t ^ 2) ^ 3)⁻¹ := by
  set w : ℂ := ((1 / 4 - β : ℝ) : ℂ) + t * I
  have hw6 : 2 ≤ w.re + 6 ∧ w.re + 6 ≤ 6 := by
    simp only [w, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    exact ⟨by linarith, by linarith⟩
  have hΓ_re : Real.Gamma (w.re + 6) ≤ Real.Gamma 6 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn hw6.1 (by norm_num) hw6.2
  have hΓ_prod := (Complex.norm_Gamma_mul_prod_norm_le (s := w) (n := 6)
    (by push_cast; linarith [hw6.1])).trans hΓ_re
  have hprod_lo : ((1 / 16 : ℝ) * (1 + t ^ 2)) ^ 3 ≤ ∏ j ∈ Finset.range 6, ‖w + j‖ := by
    have hfac (j : ℕ) : (1 / 16 : ℝ) * (1 + t ^ 2) ≤ ‖w + j‖ ^ 2 := by
      have hsq : ‖w + j‖ ^ 2 = (1 / 4 - β + j) ^ 2 + t ^ 2 := by
        rw [← normSq_eq_norm_sq, normSq_apply]; simp [w]; ring
      rw [hsq]
      rcases eq_or_ne j 0 with rfl | hj0
      · have : 1 / 4 - β ≤ -1 / 4 := by linarith
        nlinarith [sq_nonneg t]
      · have hj1 : (1 : ℝ) ≤ j := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hj0)
        have : 1 / 4 ≤ 1 / 4 - β + j := by linarith [hj1]
        nlinarith [sq_nonneg t]
    have h6 : (((1 / 16 : ℝ) * (1 + t ^ 2)) ^ 3) ^ 2 ≤
        (∏ j ∈ Finset.range 6, ‖w + j‖) ^ 2 := by
      rw [← Finset.prod_pow, show (((1 / 16 : ℝ) * (1 + t ^ 2)) ^ 3) ^ 2 =
          ∏ _j ∈ Finset.range 6, ((1 / 16 : ℝ) * (1 + t ^ 2)) by simp; ring]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ hfac j
    exact le_of_pow_le_pow_left₀ two_ne_zero
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) h6
  have hpos : 0 < ((1 / 16 : ℝ) * (1 + t ^ 2)) ^ 3 := by positivity
  have hle := (mul_le_mul_of_nonneg_left hprod_lo (norm_nonneg (Gamma w))).trans hΓ_prod
  rw [← le_div_iff₀ hpos] at hle
  refine hle.trans_eq ?_
  field_simp
  norm_num

/-- Explicit `(M N) ^ 2 (1 + t ^ 2) ^ 2` bound for the four-factor product on `Re s = 1 / 4`. -/
private theorem norm_pair_quarter_add_le {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) (t : ℝ) :
    let s : ℂ := (1 / 4 : ℂ) + t * I
    let cζ : ℝ := 1 / ((1 / 4 : ℝ) * |1 - (2 : ℝ) ^ (3 / 4 : ℝ)|)
    ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      64 * cζ * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by
  intro s cζ
  have hcζ : 0 < cζ := by
    have h2 : 1 < (2 : ℝ) ^ (3 / 4 : ℝ) := Real.one_lt_rpow one_lt_two (by norm_num)
    have : 0 < |1 - (2 : ℝ) ^ (3 / 4 : ℝ)| := abs_pos.mpr (by linarith [h2])
    positivity
  have hs_re : s.re = 1 / 4 := by simp [s]
  have hζ : ‖riemannZeta s‖ ≤ cζ * ‖s‖ := by
    have hb := norm_riemannZeta_le_of_re_ne_one (s := s) (by rw [hs_re]; norm_num)
      (by rw [hs_re]; norm_num)
    rw [hs_re, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at hb
    exact hb.trans_eq (by dsimp only [cζ]; ring)
  have hL {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρ : ρ ≠ 1) :
      ‖ρ.LFunction s‖ ≤ 4 * (L : ℝ) * ‖s‖ := by
    have hb := ρ.norm_LFunction_le_level_mul_norm_div_re hρ (by rw [hs_re]; norm_num)
    rw [hs_re] at hb
    exact hb.trans_eq (by ring)
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  have hs_pow4 : ‖s‖ ^ 4 ≤ (1 + t ^ 2) ^ 2 := by
    have hs2 : ‖s‖ ^ 2 ≤ 1 + t ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp [s]; linarith
    calc
      ‖s‖ ^ 4 = (‖s‖ ^ 2) ^ 2 := by ring
      _ ≤ (1 + t ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hs2 2
  rw [norm_mul, norm_mul, norm_mul]
  calc
    ‖riemannZeta s‖ * ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(χ.mul ψ).LFunction s‖
      ≤ (cζ * ‖s‖) * (4 * (M : ℝ) * ‖s‖) * (4 * (N : ℝ) * ‖s‖) *
          (4 * (Nat.lcm M N : ℝ) * ‖s‖) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul hζ (hL χ hχ) (norm_nonneg _) (by positivity))
            (hL ψ hψ) (norm_nonneg _) (by positivity))
          (hL (χ.mul ψ) hχψ) (norm_nonneg _) (by positivity)
    _ ≤ (cζ * ‖s‖) * (4 * (M : ℝ) * ‖s‖) * (4 * (N : ℝ) * ‖s‖) *
          (4 * ((M : ℝ) * N) * ‖s‖) := by gcongr
    _ = 64 * cζ * ((M : ℝ) * N) ^ 2 * ‖s‖ ^ 4 := by ring
    _ ≤ 64 * cζ * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by gcongr

/-- **Uniform conductor and `x`-power bound for the shifted Mellin integral.** On the line
`Re s = 1 / 4`, for any nonprincipal characters `χ` and `ψ` of levels `M` and `N` with
`χ.mul ψ ≠ 1`, any `1 / 2 ≤ β < 1`, and any `x > 0`, the shifted Mellin integral is bounded by
`C (M N) ^ 2 x ^ (β - 1 / 4)` with an absolute constant `C > 0` independent of `β`, `M`, `N`, and
`x`. -/
theorem exists_norm_mellinInv_pair_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 → ∀ {β : ℝ}, 1 / 2 ≤ β → β < 1 → ∀ {x : ℝ}, 0 < x →
      ‖mellinInv (1 / 4 - β)
        (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
          ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x‖ ≤
        C * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 4) := by
  let cζ : ℝ := 1 / ((1 / 4 : ℝ) * |1 - (2 : ℝ) ^ (3 / 4 : ℝ)|)
  have hcζ : 0 < cζ := by
    have h2 : 1 < (2 : ℝ) ^ (3 / 4 : ℝ) := Real.one_lt_rpow one_lt_two (by norm_num)
    have : 0 < |1 - (2 : ℝ) ^ (3 / 4 : ℝ)| := abs_pos.mpr (by linarith [h2])
    positivity
  have : 0 < Real.Gamma 6 := Real.Gamma_pos_of_pos (by norm_num)
  let C : ℝ := (1 / 2) * (4 ^ 6 * Real.Gamma 6 * (64 * cζ))
  refine ⟨C, by positivity, fun {M N} _ _ χ ψ hχ hψ hχψ {β} hβ0 hβ1 {x} hx ↦ ?_⟩
  let F : ℂ → ℂ := fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s
  let f : ℝ → ℂ := fun t ↦
    (x : ℂ) ^ (-(((1 / 4 - β : ℝ) : ℂ) + t * I)) •
      (Gamma (((1 / 4 - β : ℝ) : ℂ) + t * I) * F (((1 / 4 - β : ℝ) : ℂ) + t * I + β))
  have hpoint (t : ℝ) :
      ‖f t‖ ≤ (4 ^ 6 * Real.Gamma 6 * (64 * cζ)) * ((M : ℝ) * N) ^ 2 *
        x ^ (β - 1 / 4) * (1 + t ^ 2)⁻¹ := by
    set w : ℂ := ((1 / 4 - β : ℝ) : ℂ) + t * I
    set s : ℂ := (1 / 4 : ℂ) + t * I
    have hws : w + β = s := by simp only [w, s]; push_cast; ring
    have hxpow : ‖(x : ℂ) ^ (-w)‖ = x ^ (β - 1 / 4) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]; congr 1; simp [w]
    have hΓ_bound := norm_Gamma_quarter_sub_le hβ0 hβ1 t
    have hF_bound := norm_pair_quarter_add_le χ ψ hχ hψ hχψ t
    have : 0 < 1 + t ^ 2 := by positivity
    dsimp only [f]
    rw [norm_smul, norm_mul, hws, hxpow]
    calc
      x ^ (β - 1 / 4) * (‖Gamma w‖ * ‖F s‖)
        ≤ x ^ (β - 1 / 4) * ((4 ^ 6 * Real.Gamma 6 * ((1 + t ^ 2) ^ 3)⁻¹) *
            (64 * cζ * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hΓ_bound hF_bound (norm_nonneg _) (by positivity)) (by positivity)
      _ = (4 ^ 6 * Real.Gamma 6 * (64 * cζ)) * ((M : ℝ) * N) ^ 2 *
            x ^ (β - 1 / 4) * (1 + t ^ 2)⁻¹ := by field_simp
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    1 / (2 * Real.pi) * ‖∫ t : ℝ, f t‖
      ≤ 1 / (2 * Real.pi) * ∫ t : ℝ, ‖f t‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ 1 / (2 * Real.pi) * ∫ t : ℝ,
          ((4 ^ 6 * Real.Gamma 6 * (64 * cζ)) * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 4)) *
            (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (integrable_inv_one_add_sq.const_mul _) (Eventually.of_forall hpoint))
          (by positivity)
    _ = C * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 4) := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
        have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
        dsimp only [C]
        field_simp

/-- On `(0, 1)`, `Γ(u) ≤ 1 / u` because `u Γ(u) = Γ(u + 1) ≤ 1` by convexity of `Γ` on `[1, 2]`. -/
private theorem Gamma_le_inv_of_mem_Ioo {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    Real.Gamma u ≤ 1 / u := by
  have hconv := Real.convexOn_Gamma.2 (by simp : (1 : ℝ) ∈ Set.Ioi 0)
    (by simp : (2 : ℝ) ∈ Set.Ioi 0) (by linarith : 0 ≤ 1 - u) (by linarith : 0 ≤ u)
    (by ring : (1 - u) + u = 1)
  have hu_eq : (1 - u) • (1 : ℝ) + u • (2 : ℝ) = u + 1 := by simp [smul_eq_mul]; ring
  rw [hu_eq, smul_eq_mul, smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at hconv
  have hadd : u * Real.Gamma u ≤ 1 := by
    rw [← Real.Gamma_add_one hu0.ne']
    linarith
  rwa [le_div_iff₀ hu0, mul_comm]

/-- Nonnegativity of `zetaMulPairCoeffs` and `a₁ = 1` lower bound the real part of the shifted
contour decomposition by `e ^ (-1)` whenever `0 < x ≤ 1`. -/
private theorem exp_neg_one_le_smoothed_pair_re {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1)
    {β x : ℝ} (hβ0 : 1 / 2 ≤ β) (hβ1 : β < 1) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.exp (-1) ≤
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
          (Gamma (1 - β) * (x : ℂ) ^ ((β : ℂ) - 1)) +
        riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        mellinInv (1 / 4 - β)
          (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
            ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x).re := by
  have hhas_re := Complex.reCLM.hasSum
    (hasSum_zetaMulPairCoeffs_mul_cpow_neg_mul_exp_of_mul_ne_one χ ψ hχ hψ hχψ
      (σ₁ := 1 / 4) (by norm_num) (by linarith) hβ1 hx0)
  have hterm_nonneg (n : ℕ) :
      0 ≤ (χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x)).re := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have ha : 0 ≤ χ.zetaMulPairCoeffs ψ n := zetaMulPairCoeffs_nonneg hχq hψq n
      have hpow : 0 ≤ (n : ℂ) ^ (-(β : ℂ)) := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, ← ofReal_neg, ← ofReal_cpow n.cast_nonneg]
        exact Complex.zero_le_real.mpr (by positivity)
      have hexp : 0 ≤ (Real.exp (-n * x) : ℂ) := Complex.zero_le_real.mpr (Real.exp_pos _).le
      exact (Complex.nonneg_iff.mp (mul_nonneg (mul_nonneg ha hpow) hexp)).1
  calc
    Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    _ = (χ.zetaMulPairCoeffs ψ 1 * ((1 : ℕ) : ℂ) ^ (-(β : ℂ)) * Real.exp (-(1 : ℕ) * x)).re := by
      rw [zetaMulPairCoeffs_one, Nat.cast_one, Nat.cast_one, one_cpow, one_mul, one_mul,
        neg_one_mul, ofReal_re]
    _ ≤ _ := le_hasSum hhas_re 1 (fun n _ ↦ hterm_nonneg n)

/-- Choosing `x = ((2 C e + 1) ^ 4 (M N) ^ 8)⁻¹` scales `C (M N) ^ 2 x ^ (β - 1 / 4)` below
`e ^ (-1) / 2` for every `β ≥ 1 / 2`. -/
private theorem mul_sq_mul_rpow_sub_quarter_le_half_exp_neg_one {C β : ℝ} (hC : 0 < C)
    (hβ0 : 1 / 2 ≤ β) (M N : ℕ) [NeZero M] [NeZero N] :
    let B : ℝ := 2 * C * Real.exp 1 + 1
    let x : ℝ := (B ^ 4 * ((M : ℝ) * N) ^ 8)⁻¹
    C * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 4) ≤ Real.exp (-1) / 2 := by
  intro B x
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    linarith [mul_pos (mul_pos two_pos hC) (Real.exp_pos 1)]
  have hMN1 : 1 ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.mul_pos (NeZero.pos M) (NeZero.pos N)
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := inv_le_one_of_one_le₀
    (by nlinarith [one_le_pow₀ hB1 (n := 4), pow_le_pow_right₀ hMN1 (by omega : 0 ≤ 8)])
  have hx_rpow_quarter : x ^ (1 / 4 : ℝ) = (B * ((M : ℝ) * N) ^ 2)⁻¹ := by
    have hx_eq : x = ((B * ((M : ℝ) * N) ^ 2)⁻¹) ^ (4 : ℝ) := by
      dsimp only [x]
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
      congr 1; ring
    rw [hx_eq, ← Real.rpow_mul (by positivity)]
    norm_num
  calc
    C * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 4)
      ≤ C * ((M : ℝ) * N) ^ 2 * x ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)) (by positivity)
    _ = C / B := by
        have : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
        have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
        have : B ≠ 0 := by positivity
        rw [hx_rpow_quarter]; field_simp
    _ ≤ C / (2 * C * Real.exp 1) := by gcongr; dsimp only [B]; linarith
    _ = Real.exp (-1) / 2 := by rw [Real.exp_neg]; field_simp

/-- **Goldfeld's lower bound for the three-factor L-value product at `1`.** There is an absolute
constant `c > 0` such that for any nonprincipal quadratic characters `χ` and `ψ` of levels `M` and
`N` with `χ.mul ψ ≠ 1` and any real `1 / 2 ≤ β < 1` at which
`ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ) ≤ 0`, one has

`c (1 - β) (M N) ^ (-8 (1 - β)) ≤ Re (L(1, χ) L(1, ψ) L(1, χ.mul ψ))`. -/
theorem exists_le_LFunction_one_mul_mul_of_pair_nonpos :
    ∃ c : ℝ, 0 < c ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      ∀ {β : ℝ}, 1 / 2 ≤ β → β < 1 →
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β ≤ 0 →
      c * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) ≤
        (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re := by
  obtain ⟨C, hC, hInt⟩ := exists_norm_mellinInv_pair_le
  let B : ℝ := 2 * C * Real.exp 1 + 1
  have hB1 : 1 ≤ B := by
    dsimp only [B]; linarith [mul_pos (mul_pos two_pos hC) (Real.exp_pos 1)]
  let A : ℝ := B ^ 4
  have hA1 : 1 ≤ A := one_le_pow₀ hB1
  refine ⟨Real.exp (-1) / (2 * A), by positivity,
    fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ0 hβ1 hFβ ↦ ?_⟩
  have hMN1 : 1 ≤ (M : ℝ) * N := by exact_mod_cast Nat.mul_pos (NeZero.pos M) (NeZero.pos N)
  set x : ℝ := (A * ((M : ℝ) * N) ^ 8)⁻¹
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [pow_le_pow_right₀ hMN1 (by omega : 0 ≤ 8)])
  have hsum_ge := exp_neg_one_le_smoothed_pair_re χ ψ hχq hψq hχ hψ hχψ hβ0 hβ1 hx0 hx1
  have herr : (mellinInv (1 / 4 - β)
      (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
        ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x).re ≤ Real.exp (-1) / 2 :=
    (re_le_norm _).trans ((hInt χ ψ hχ hψ hχψ hβ0 hβ1 hx0).trans
      (mul_sq_mul_rpow_sub_quarter_le_half_exp_neg_one hC hβ0 M N))
  set P : ℂ := χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1
  have hP_pos : 0 < P :=
    mul_pos (mul_pos (LFunction_apply_one_pos hχq hχ) (LFunction_apply_one_pos hψq hψ))
      (LFunction_apply_one_pos (isQuadratic_mul hχq hψq) hχψ)
  obtain ⟨hPre_pos, hPim⟩ := Complex.pos_iff.mp hP_pos
  have hpole_re : (P * (Gamma (1 - β) * (x : ℂ) ^ ((β : ℂ) - 1))).re =
      P.re * Real.Gamma (1 - β) * x ^ (β - 1) := by
    have h1β : (1 : ℂ) - (β : ℂ) = ((1 - β : ℝ) : ℂ) := by push_cast; ring
    have hβ1_c : (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
    have hP_eq : P = (P.re : ℂ) := Complex.ext rfl (by simp [← hPim])
    conv_lhs => rw [hP_eq]
    rw [h1β, hβ1_c, Complex.Gamma_ofReal, ← ofReal_cpow hx0.le, ← ofReal_mul, ← ofReal_mul,
      ofReal_re, ← mul_assoc]
  have hFβ_re : (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0 := by
    simpa using (Complex.le_def.mp hFβ).1
  simp only [add_re] at hsum_ge
  rw [hpole_re] at hsum_ge
  have hmain : Real.exp (-1) / 2 ≤ P.re * Real.Gamma (1 - β) * x ^ (β - 1) := by linarith
  have hΓ_ub : Real.Gamma (1 - β) ≤ 1 / (1 - β) :=
    Gamma_le_inv_of_mem_Ioo (by linarith) (by linarith)
  have hx_ub : x ^ (β - 1) ≤ A * ((M : ℝ) * N) ^ (8 * (1 - β)) := by
    have hx_inv : x ^ (β - 1) = (A * ((M : ℝ) * N) ^ 8) ^ (1 - β) := by
      dsimp only [x]
      rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub]
    rw [hx_inv, Real.mul_rpow (by positivity) (by positivity),
      show (((M : ℝ) * N) ^ 8) ^ (1 - β) = ((M : ℝ) * N) ^ (8 * (1 - β)) by
        rw [← Real.rpow_natCast ((M : ℝ) * N) 8, ← Real.rpow_mul (by positivity)]; ring_nf]
    gcongr
    exact Real.rpow_le_self_of_one_le hA1 (by linarith)
  have : 0 ≤ Real.Gamma (1 - β) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hprod_ub : P.re * Real.Gamma (1 - β) * x ^ (β - 1) ≤
      P.re * (1 / (1 - β)) * (A * ((M : ℝ) * N) ^ (8 * (1 - β))) :=
    (by gcongr : P.re * Real.Gamma (1 - β) * x ^ (β - 1) ≤ P.re * (1 / (1 - β)) * x ^ (β - 1)).trans
      (by gcongr)
  have hineq := hmain.trans hprod_ub
  have h1β_pos : 0 < 1 - β := by linarith
  have hA_pos : 0 < A := by positivity
  have hpow_pos : 0 < ((M : ℝ) * N) ^ (8 * (1 - β)) := by positivity
  rw [show -8 * (1 - β) = -(8 * (1 - β)) by ring, Real.rpow_neg (by positivity),
    ← div_eq_mul_inv, div_le_iff₀ hpow_pos]
  calc
    Real.exp (-1) / (2 * A) * (1 - β)
      = (Real.exp (-1) / 2) * ((1 - β) / A) := by
          have : A ≠ 0 := hA_pos.ne'; field_simp
    _ ≤ (P.re * (1 / (1 - β)) * (A * ((M : ℝ) * N) ^ (8 * (1 - β)))) * ((1 - β) / A) :=
          mul_le_mul_of_nonneg_right hineq (by positivity)
    _ = P.re * ((M : ℝ) * N) ^ (8 * (1 - β)) := by
          have : 1 - β ≠ 0 := h1β_pos.ne'; have : A ≠ 0 := hA_pos.ne'; field_simp

end GoldfeldBound

end DirichletCharacter
