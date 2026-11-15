/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Residue
public import TauCeti.NumberTheory.LSeries.SmoothedSum
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Bounds
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Goldfeld's shifted Mellin contour for a pair of Dirichlet characters

For nonprincipal characters `χ` mod `M` and `ψ` mod `N`, Goldfeld's proof of Siegel's theorem (in
the `Γ(s)` exponential-smoothing exposition of Iwaniec–Kowalski, §5.9, and Montgomery–Vaughan,
§11.4) smooths the Dirichlet series of `F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` shifted by a
real parameter `1 / 2 < β < 1`:

`(1 / 2π) ∫ Γ(2 + i t) F(2 + β + i t) x^{-(2 + i t)} dt = ∑_{n ≥ 1} c_n n^{-β} e^{-n x}`

for `x > 0`. Shifting the vertical line of integration left from `Re s = 2` to
`Re s = 1 / 2 - β` crosses only the simple pole of `Γ(s)` at `s = 0` (with residue `F(β)`) and the
pole of `F(s + β)` at `s = 1 - β`.

When `3 / 4 ≤ β < 1`, the shifted line `Re s = 1 / 2 - β ∈ (-1 / 2, -1 / 4]` stays uniformly
bounded away from the poles `0` and `-1` of `Γ`, while `s + β` lies on the critical line
`Re w = 1 / 2`, where `DirichletCharacter.norm_pair_le_of_one_half_le_re` bounds `F(w)`
polynomially in `(M N)² ‖w‖⁴`. This gives an explicit uniform `O((M N)² x^{β - 1/2})` bound on the
shifted integral. For quadratic characters with nonprincipal product and `Re F(β) ≤ 0`, choosing
`x asymp ((M N)²)^{-4}` yields Goldfeld's fundamental lower bound
`c (1 - β) (M N)^{-8(1 - β)}` for `L(1, χ) L(1, ψ) L(1, χ.mul ψ)`.

## Main results

* `DirichletCharacter.hasSum_zetaMulPairCoeffs_cpow_mul_exp`: smoothed Dirichlet series identity on
  `Re s = 2` for `-1 < β` and `x > 0`.
* `DirichletCharacter.exp_neg_le_re_mellinInv_Gamma_mul_pair`: `e^{-x}` lower bound for the
  smoothed sum when `χ` and `ψ` are quadratic.
* `DirichletCharacter.mellinInv_Gamma_mul_pair_of_mul_ne_one` and
  `DirichletCharacter.mellinInv_Gamma_mul_pair_of_mul_eq_one`: the shifted Mellin contour identities
  in the simple-pole and double-pole cases.
* `DirichletCharacter.exists_pos_mul_rpow_le_re_LFunction_one_mul`: Goldfeld's residue lower bound
  under `Re F(β) ≤ 0`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9 (exponential `Γ(s)` smoothing of
  Goldfeld's contour shift).
* H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, §11.4.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Filter MeasureTheory Set
open Complex hiding exp continuous_exp
open scoped Topology ComplexOrder Interval

namespace DirichletCharacter

private lemma gamma_one_sub_le_two_div {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β < 1) :
    Real.Gamma (1 - β) ≤ 2 / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith
  have h2 : 1 ≤ 2 - β := by linarith
  have ha1 : (1 - β) + 1 = 2 - β := by ring
  have ha2 : (2 - β) + 1 = 3 - β := by ring
  have hstep1 : Real.Gamma (2 - β) = (1 - β) * Real.Gamma (1 - β) := by
    simpa [ha1] using Real.Gamma_add_one h1.ne'
  have hstep2 : Real.Gamma (3 - β) = (2 - β) * Real.Gamma (2 - β) := by
    simpa [ha2] using Real.Gamma_add_one (by linarith : 2 - β ≠ 0)
  have hmono : Real.Gamma (3 - β) ≤ 2 := by
    calc Real.Gamma (3 - β) ≤ Real.Gamma 3 :=
          Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith) (by norm_num) (by linarith)
      _ = 2 := by simp
  rw [le_div_iff₀ h1, mul_comm]
  calc (1 - β) * Real.Gamma (1 - β)
      ≤ (2 - β) * ((1 - β) * Real.Gamma (1 - β)) :=
        le_mul_of_one_le_left (mul_nonneg h1.le (Real.Gamma_pos_of_pos h1).le) h2
    _ = Real.Gamma (3 - β) := by rw [← hstep1, hstep2]
    _ ≤ 2 := hmono

private lemma analyticAt_cpow_mul_Gamma_sub_one {β x : ℝ} (hβ₁ : β < 1) (hx : 0 < x) :
    AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-(w - β)) * Gamma (w - β)) 1 := by
  refine (analyticAt_const.cpow (by fun_prop) (ofReal_mem_slitPlane.mpr hx)).mul ?_
  refine (analyticAt_Gamma fun m hm ↦ ?_).comp_of_eq (by fun_prop) rfl
  have hre : ((1 : ℂ) - β).re = -(m : ℝ) := by simpa using congrArg Complex.re hm
  simp only [sub_re, one_re, ofReal_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) m]

variable {M N : ℕ} [NeZero M] [NeZero N]

private noncomputable abbrev pairProd (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (s : ℂ) : ℂ :=
  riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s

private lemma analyticAt_pairProd (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ (pairProd χ ψ) w :=
  (((analyticOn_riemannZeta w hw).mul (χ.analyticAt_LFunction (Or.inl hw))).mul
    (ψ.analyticAt_LFunction (Or.inl hw))).mul
    ((χ.mul ψ).analyticAt_LFunction (Or.inl hw))

/-- **Smoothed Dirichlet series of the shifted four-factor product.** For `-1 < β` and `x > 0`,
`∑_{n ≥ 0} c_n n^{-β} e^{-n x}` converges to the Mellin inverse on `Re s = 2` of
`s ↦ Γ(s) ζ(s + β) L(s + β, χ) L(s + β, ψ) L(s + β, χ.mul ψ)`. -/
theorem hasSum_zetaMulPairCoeffs_cpow_mul_exp (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ : -1 < β) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x))
      (mellinInv 2 (fun s ↦ Gamma s *
        (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
          (χ.mul ψ).LFunction (s + β))) x) := by
  have hs : LSeriesSummable (fun n ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ))) 2 :=
    (LSeriesHasSum_zetaMulPairCoeffs χ ψ (s := (2 : ℂ) + β) (by simp; linarith)).summable.congr
      fun n ↦ (TauCeti.LSeries.term_mul_natCast_cpow_neg _ _ _ n).symm
  have hmain := TauCeti.LSeries.hasSum_mellinInv_Gamma_mul_LSeries (by simp) two_pos hs hx
  have heq : mellinInv 2
        (fun s ↦ Gamma s * LSeries (fun n ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ))) s) x =
      mellinInv 2 (fun s ↦ Gamma s * pairProd χ ψ (s + β)) x := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [TauCeti.LSeries.LSeries_mul_natCast_cpow_neg,
      (LSeriesHasSum_zetaMulPairCoeffs χ ψ (by simp; linarith)).LSeries_eq]
  rwa [heq] at hmain

/-- For quadratic characters `χ` and `ψ`, `-1 < β`, and `x > 0`, `e ^ (-x)` bounds below the real
part of the Mellin inverse at `σ = 2` of
`s ↦ Γ(s) ζ(s + β) L(s + β, χ) L(s + β, ψ) L(s + β, χ.mul ψ)`. -/
theorem exp_neg_le_re_mellinInv_Gamma_mul_pair {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic)
    {β : ℝ} (hβ : -1 < β) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ (mellinInv 2 (fun s ↦ Gamma s *
      (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
        (χ.mul ψ).LFunction (s + β))) x).re := by
  set g : ℕ → ℝ := fun n ↦
    Complex.reCLM (χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x))
  have hsum : HasSum g (Complex.reCLM (mellinInv 2 (fun s ↦ Gamma s *
      (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
        (χ.mul ψ).LFunction (s + β))) x)) :=
    Complex.reCLM.hasSum (hasSum_zetaMulPairCoeffs_cpow_mul_exp χ ψ hβ hx)
  have hnn (n : ℕ) : 0 ≤ g n := by
    dsimp only [g]
    rw [Complex.reCLM_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hc : χ.zetaMulPairCoeffs ψ n = ((χ.zetaMulPairCoeffs ψ n).re : ℂ) :=
        Complex.eq_re_of_ofReal_le (r := 0) (by simpa using zetaMulPairCoeffs_nonneg hχ hψ n)
      have hre : 0 ≤ (χ.zetaMulPairCoeffs ψ n).re :=
        Complex.zero_le_real.mp (by rw [← hc]; exact zetaMulPairCoeffs_nonneg hχ hψ n)
      have hpow : (n : ℂ) ^ (-(β : ℂ)) = (((n : ℝ) ^ (-β) : ℝ) : ℂ) := by
        rw [← ofReal_natCast, ofReal_cpow (Nat.cast_nonneg n), ofReal_neg]
      rw [hc, hpow, ← ofReal_mul, ← ofReal_mul, ofReal_re]
      positivity
  have h1 : g 1 = Real.exp (-x) := by simp [g, -ofReal_exp]
  rw [← Complex.reCLM_apply, ← h1, ← hsum.tsum_eq]
  exact Summable.le_tsum hsum.summable 1 fun n _ ↦ hnn n

private lemma norm_Gamma_mul_pair_horizontal_le (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1)
    {u y : ℝ} (hu : u ∈ [[1 / 2 - β, (2 : ℝ)]]) (hy : 4 ≤ |y|) :
    ‖Gamma (u + y * I) * pairProd χ ψ (u + y * I + β)‖ ≤
      4096 * Real.Gamma 8 * ((M : ℝ) * N) ^ 2 * |y|⁻¹ ^ 2 := by
  have hu' : 1 / 2 - β ≤ u ∧ u ≤ 2 := by
    rwa [Set.uIcc_of_le (by linarith)] at hu
  set z : ℂ := (u : ℂ) + y * I
  have hy0 : 0 < |y| := by linarith
  have hwre : 1 / 2 ≤ (z + β).re := by simp [z]; linarith [hu'.1]
  have hwd : 1 / 2 ≤ ‖z + β - 1‖ := by
    have him : |(z + β - 1).im| = |y| := by simp [z]
    linarith [abs_im_le_norm (z + β - 1)]
  have hwnorm : ‖z + β‖ ≤ 2 * |y| := by
    have h1 : ‖z + β‖ = ‖((u + β : ℝ) : ℂ) + y * I‖ := by congr 1; push_cast [z]; ring
    have habs : |u + β| ≤ 3 := abs_le.mpr ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    rw [h1]
    calc ‖((u + β : ℝ) : ℂ) + y * I‖ ≤ ‖((u + β : ℝ) : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |u + β| + |y| := by rw [norm_real, Real.norm_eq_abs, norm_mul, norm_real,
          Real.norm_eq_abs, norm_I, mul_one]
      _ ≤ 2 * |y| := by linarith
  have hF : ‖pairProd χ ψ (z + β)‖ ≤ 4096 * ((M : ℝ) * N) ^ 2 * |y| ^ 4 := by
    calc ‖pairProd χ ψ (z + β)‖ ≤ 256 * ((M : ℝ) * N) ^ 2 * ‖z + β‖ ^ 4 :=
          norm_pair_le_of_one_half_le_re χ ψ hwre hwd
      _ ≤ 256 * ((M : ℝ) * N) ^ 2 * (2 * |y|) ^ 4 := by gcongr
      _ = 4096 * ((M : ℝ) * N) ^ 2 * |y| ^ 4 := by ring
  have hΓprod := norm_Gamma_mul_prod_norm_le (s := z) (n := 6) (by simp [z]; linarith [hu'.1])
  have hp6 : |y| ^ 6 ≤ ∏ k ∈ Finset.range 6, ‖z + k‖ := by
    calc |y| ^ 6 = ∏ _k ∈ Finset.range 6, |y| := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ k ∈ Finset.range 6, ‖z + k‖ := by
        gcongr with k _
        calc |y| = |(z + k).im| := by simp [z]
          _ ≤ ‖z + k‖ := abs_im_le_norm _
  have hΓ8 : Real.Gamma (z.re + 6) ≤ Real.Gamma 8 := by
    have hzre : z.re = u := by simp [z]
    rw [hzre]
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith [hu'.1]) (by norm_num)
      (by linarith [hu'.2])
  have hΓ : ‖Gamma z‖ ≤ Real.Gamma 8 / |y| ^ 6 := by
    rw [le_div_iff₀ (pow_pos hy0 6)]
    exact (mul_le_mul_of_nonneg_left hp6 (norm_nonneg _)).trans (hΓprod.trans hΓ8)
  rw [norm_mul]
  calc ‖Gamma z‖ * ‖pairProd χ ψ (z + β)‖
      ≤ (Real.Gamma 8 / |y| ^ 6) * (4096 * ((M : ℝ) * N) ^ 2 * |y| ^ 4) :=
        mul_le_mul hΓ hF (norm_nonneg _) (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le
          (pow_nonneg hy0.le 6))
    _ = 4096 * Real.Gamma 8 * ((M : ℝ) * N) ^ 2 * |y|⁻¹ ^ 2 := by field_simp [hy0.ne']

private lemma continuous_pairProd_vertical (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {σ β : ℝ} (hne : σ + β ≠ 1) :
    Continuous fun t : ℝ ↦ pairProd χ ψ ((σ : ℂ) + t * I + β) :=
  continuous_iff_continuousAt.mpr fun t ↦
    (analyticAt_pairProd χ ψ fun h ↦
      hne (by simpa using congrArg Complex.re h)).continuousAt.comp (by fun_prop)

private lemma verticalIntegrable_Gamma_mul_pair (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {σ β : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ -n) (hσβ : 1 / 2 ≤ σ + β) (hne : σ + β ≠ 1) :
    VerticalIntegrable (fun s ↦ Gamma s * pairProd χ ψ (s + β)) σ := by
  obtain ⟨CΓ, hCΓ⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hσ 3
  have hcontF := continuous_pairProd_vertical χ ψ hne
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc.image (continuous_norm.comp hcontF)).bddAbove
  set C₁ : ℝ := max (max B₀ 0) (256 * ((M : ℝ) * N) ^ 2 * (1 + (σ + β) ^ 2) ^ 2)
  have hC₁0 : 0 ≤ C₁ := le_max_of_le_left (le_max_right _ _)
  have hF (t : ℝ) : ‖pairProd χ ψ ((σ : ℂ) + t * I + β)‖ ≤ C₁ * (1 + t ^ 2) ^ 2 := by
    rcases le_or_gt |t| 1 with ht | ht
    · calc ‖pairProd χ ψ ((σ : ℂ) + t * I + β)‖
          ≤ B₀ := hB₀ ⟨t, abs_le.mp ht, rfl⟩
        _ ≤ C₁ := (le_max_left _ _).trans (le_max_left _ _)
        _ ≤ C₁ * (1 + t ^ 2) ^ 2 := le_mul_of_one_le_right hC₁0 (by nlinarith [sq_nonneg t])
    · set w : ℂ := (σ : ℂ) + t * I + β
      have hwd : 1 / 2 ≤ ‖w - 1‖ := by
        have him : |(w - 1).im| = |t| := by simp [w]
        linarith [abs_im_le_norm (w - 1)]
      have hwn : ‖w‖ ^ 4 ≤ (1 + (σ + β) ^ 2) ^ 2 * (1 + t ^ 2) ^ 2 := by
        have hsq : ‖w‖ ^ 2 = (σ + β) ^ 2 + t ^ 2 := by
          rw [← normSq_eq_norm_sq, normSq_apply]; simp [w]; ring
        have hle : ‖w‖ ^ 2 ≤ (1 + (σ + β) ^ 2) * (1 + t ^ 2) := by
          rw [hsq]; nlinarith [sq_nonneg (σ + β), sq_nonneg t]
        calc ‖w‖ ^ 4 = (‖w‖ ^ 2) ^ 2 := by ring
          _ ≤ ((1 + (σ + β) ^ 2) * (1 + t ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
          _ = (1 + (σ + β) ^ 2) ^ 2 * (1 + t ^ 2) ^ 2 := by ring
      calc ‖pairProd χ ψ w‖ ≤ 256 * ((M : ℝ) * N) ^ 2 * ‖w‖ ^ 4 :=
            norm_pair_le_of_one_half_le_re χ ψ (by simp [w]; linarith) hwd
        _ ≤ (256 * ((M : ℝ) * N) ^ 2 * (1 + (σ + β) ^ 2) ^ 2) * (1 + t ^ 2) ^ 2 := by
            nlinarith [hwn]
        _ ≤ C₁ * (1 + t ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hcontΓ : Continuous fun t : ℝ ↦ Gamma ((σ : ℂ) + t * I) :=
    continuous_iff_continuousAt.mpr fun t ↦
      (analyticAt_Gamma fun m hm ↦
        hσ m (by simpa using congrArg Complex.re hm)).continuousAt.comp (by fun_prop)
  refine (integrable_inv_one_add_sq.const_mul (max CΓ 0 * C₁)).mono'
    (hcontΓ.mul hcontF).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
  rw [norm_mul]
  have hΓt : ‖Gamma ((σ : ℂ) + t * I)‖ ≤ max CΓ 0 * ((1 + t ^ 2) ^ 3)⁻¹ :=
    (hCΓ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have ht2 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  calc ‖Gamma ((σ : ℂ) + t * I)‖ * ‖pairProd χ ψ ((σ : ℂ) + t * I + β)‖
      ≤ (max CΓ 0 * ((1 + t ^ 2) ^ 3)⁻¹) * (C₁ * (1 + t ^ 2) ^ 2) :=
        mul_le_mul hΓt (hF t) (norm_nonneg _) (by positivity)
    _ = max CΓ 0 * C₁ * (1 + t ^ 2)⁻¹ := by field_simp [ht2]

private lemma residue_cpow_mul_Gamma_mul_pair_zero (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ₁ : β ≠ 1) {x : ℝ} (hx : 0 < x) :
    TauCeti.Contour.residue
      (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β))) 0 = pairProd χ ψ β := by
  have hb1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ₁
  have hF_an : AnalyticAt ℂ (fun z : ℂ ↦ pairProd χ ψ (z + β)) 0 :=
    (analyticAt_pairProd χ ψ hb1).comp_of_eq (by fun_prop) (by simp)
  have hx_an : AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (-z)) 0 :=
    analyticAt_const.cpow (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
  have hmero : MeromorphicAt (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β))) 0 :=
    hx_an.meromorphicAt.mul ((Meromorphic.Gamma 0).mul hF_an.meromorphicAt)
  have hlim : Tendsto (fun z : ℂ ↦ (z - 0) *
      ((x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β)))) (𝓝[≠] 0) (𝓝 (pairProd χ ψ β)) := by
    have ht := tendsto_self_mul_Gamma_nhds_zero.mul
      ((hx_an.continuousAt.mul hF_an.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
    simpa [mul_assoc, mul_left_comm, mul_comm] using ht
  exact TauCeti.Contour.residue_eq_of_tendsto_sub_mul hmero hlim

open scoped Classical in
private lemma analyticAt_Gamma_mul_pair (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ₁ : β < 1) {z : ℂ}
    (hz : z.re ∈ Icc (1 / 2 - β) 2) (hzS : z ∉ ({0, 1 - (β : ℂ)} : Finset ℂ)) :
    AnalyticAt ℂ (fun s ↦ Gamma s * pairProd χ ψ (s + β)) z := by
  have hz0 : z ≠ 0 := fun h ↦ hzS (by simp [h])
  have hz1 : z + β ≠ 1 := fun h ↦ by
    have hzeq : z = 1 - (β : ℂ) := by linear_combination h
    exact hzS (by simp [hzeq])
  have hΓ : AnalyticAt ℂ Gamma z := analyticAt_Gamma fun m hm ↦ by
    rcases eq_or_ne m 0 with rfl | hm0
    · exact hz0 (by simpa using hm)
    · have hre : z.re = -(m : ℝ) := by simpa using congrArg Complex.re hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
      linarith [hz.1]
  exact hΓ.mul ((analyticAt_pairProd χ ψ hz1).comp_of_eq (by fun_prop) rfl)

private lemma tendsto_horizontal_Gamma_mul_pair (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ ↦ ∫ u : ℝ in (1 / 2 - β)..2,
      (x : ℂ) ^ (-((u : ℂ) + T * I)) *
        (Gamma (u + T * I) * pairProd χ ψ ((u + T * I) + β))) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ ↦ ∫ u : ℝ in (1 / 2 - β)..2,
      (x : ℂ) ^ (-((u : ℂ) - T * I)) *
        (Gamma (u - T * I) * pairProd χ ψ ((u - T * I) + β))) atTop (𝓝 0) := by
  set f : ℂ → ℂ := fun s ↦ Gamma s * pairProd χ ψ (s + β)
  have hzero : (0 : ℝ) = 4096 * Real.Gamma 8 * ((M : ℝ) * N) ^ 2 * 0 ^ 2 := by ring
  have hb0 : Tendsto (fun T : ℝ ↦ 4096 * Real.Gamma 8 * ((M : ℝ) * N) ^ 2 * T⁻¹ ^ 2)
      atTop (𝓝 0) := hzero ▸ ((tendsto_inv_atTop_zero.pow 2).const_mul _)
  refine ⟨tendsto_integral_cpow_smul_zero_of_norm_le (f := f) (y := id)
    (σ₁ := 1 / 2 - β) (σ₂ := 2) hx hb0 ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT u hu
    have hTabs : |T| = T := abs_of_nonneg (by linarith)
    have hb := norm_Gamma_mul_pair_horizontal_le χ ψ hβ₀ hβ₁ hu (hTabs.symm ▸ hT)
    rwa [hTabs] at hb
  · have hbot' := tendsto_integral_cpow_smul_zero_of_norm_le (f := f) (y := fun T ↦ -T)
      (σ₁ := 1 / 2 - β) (σ₂ := 2) hx hb0 <| by
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT u hu
      have hTabs : |-T| = T := by rw [abs_neg, abs_of_nonneg (by linarith)]
      have hb := norm_Gamma_mul_pair_horizontal_le χ ψ hβ₀ hβ₁ hu (hTabs.symm ▸ hT)
      rwa [hTabs] at hb
    refine hbot'.congr fun T ↦ intervalIntegral.integral_congr fun u _ ↦ ?_
    rw [smul_eq_mul, ofReal_neg, neg_mul, ← sub_eq_add_neg]

open scoped Classical in
private theorem mellinInv_Gamma_mul_pair_eq_add_residue (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s ↦ Gamma s * pairProd χ ψ (s + β)) x =
      mellinInv (1 / 2 - β) (fun s ↦ Gamma s * pairProd χ ψ (s + β)) x +
        pairProd χ ψ β +
        TauCeti.Contour.residue
          (fun w ↦ pairProd χ ψ w * ((x : ℂ) ^ (-(w - β)) * Gamma (w - β))) 1 := by
  set f : ℂ → ℂ := fun s ↦ Gamma s * pairProd χ ψ (s + β)
  set S : Finset ℂ := {0, 1 - (β : ℂ)}
  have hf_mero : ∀ s ∈ S, s.re ∈ Ioo (1 / 2 - β) 2 → MeromorphicAt f s := fun s _ _ ↦ by
    have htrans : AnalyticAt ℂ (fun z : ℂ ↦ z + (β : ℂ)) s := by fun_prop
    exact (Meromorphic.Gamma s).mul
      (((((TauCeti.meromorphic_riemannZeta _).comp_analyticAt htrans).mul
        ((χ.meromorphic_LFunction _).comp_analyticAt htrans)).mul
        ((ψ.meromorphic_LFunction _).comp_analyticAt htrans)).mul
        (((χ.mul ψ).meromorphic_LFunction _).comp_analyticAt htrans))
  have hS_re : ∀ s ∈ S, s.re ≠ 1 / 2 - β ∧ s.re ≠ 2 := fun s hs ↦ by
    rcases Finset.mem_insert.mp hs with rfl | hs'
    · refine ⟨by simp; linarith, by simp⟩
    · rw [Finset.mem_singleton.mp hs']
      refine ⟨by simp, by simp; linarith⟩
  have hint₁ : VerticalIntegrable f (1 / 2 - β) :=
    verticalIntegrable_Gamma_mul_pair χ ψ (σ := 1 / 2 - β) (β := β)
      (fun n h ↦ by
        rcases eq_or_ne n 0 with rfl | hn
        · simp only [Nat.cast_zero, neg_zero] at h
          linarith
        · have hm : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          linarith) (by linarith) (by linarith)
  have hint₂ : VerticalIntegrable f 2 :=
    verticalIntegrable_Gamma_mul_pair χ ψ (σ := 2) (β := β)
      (fun n h ↦ by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith) (by linarith)
  obtain ⟨htop, hbot⟩ := tendsto_horizontal_Gamma_mul_pair χ ψ hβ₀ hβ₁ hx
  have hshift := mellinInv_eq_mellinInv_add_sum_residue (by linarith : 1 / 2 - β ≤ 2) hx
    (fun _ hz hzS ↦ analyticAt_Gamma_mul_pair χ ψ hβ₁ hz hzS) hf_mero hS_re hint₁ hint₂ htop hbot
  have hfilt : S.filter (fun s ↦ s.re ∈ Ioo (1 / 2 - β) 2) = S :=
    Finset.filter_true_of_mem fun s hs ↦ by
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · simp only [mem_Ioo, zero_re]; refine ⟨by linarith, by norm_num⟩
      · rw [Finset.mem_singleton.mp hs']
        simp only [mem_Ioo, sub_re, one_re, ofReal_re]; refine ⟨by linarith, by linarith⟩
  have hne01 : (0 : ℂ) ≠ 1 - (β : ℂ) := fun h ↦ by
    have hre := congrArg Complex.re h; simp at hre; linarith [hβ₁]
  rw [hfilt, Finset.sum_pair hne01, residue_cpow_mul_Gamma_mul_pair_zero χ ψ hβ₁.ne hx]
    at hshift
  have hr1 : TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) (1 - (β : ℂ)) =
      TauCeti.Contour.residue
        (fun w ↦ pairProd χ ψ w * ((x : ℂ) ^ (-(w - β)) * Gamma (w - β))) 1 := by
    have hcomp := TauCeti.Contour.residue_comp_add_const
      (fun w ↦ pairProd χ ψ w * ((x : ℂ) ^ (-(w - β)) * Gamma (w - β))) (β : ℂ) (1 - (β : ℂ))
    rw [sub_add_cancel] at hcomp; rw [← hcomp]
    congr 1 with z; dsimp only [f]; rw [add_sub_cancel_right]; ring
  rw [hr1] at hshift
  linear_combination hshift

/-- **Shifted Mellin identity in the simple-pole case.** For nonprincipal characters `χ` mod `M`
and `ψ` mod `N` (`χ ≠ 1`, `ψ ≠ 1`) with `χ.mul ψ ≠ 1`, `1 / 2 < β < 1`, and `x > 0`, shifting from
`Re s = 2` to `Re s = 1 / 2 - β` extracts `ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)` and
`L(1, χ) L(1, ψ) L(1, χ.mul ψ) x^{-(1 - β)} Γ(1 - β)`. -/
theorem mellinInv_Gamma_mul_pair_of_mul_ne_one (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1)
    {β : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s ↦ Gamma s *
      (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
        (χ.mul ψ).LFunction (s + β))) x =
      mellinInv (1 / 2 - β) (fun s ↦ Gamma s *
        (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
          (χ.mul ψ).LFunction (s + β))) x +
        (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β) +
        χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
          ((x : ℂ) ^ (-((1 : ℂ) - β)) * Gamma ((1 : ℂ) - β)) := by
  rw [mellinInv_Gamma_mul_pair_eq_add_residue χ ψ hβ₀ hβ₁ hx,
    residue_pair_mul_of_mul_ne_one χ ψ hχ hψ hχψ (analyticAt_cpow_mul_Gamma_sub_one hβ₁ hx)]

/-- **Shifted Mellin identity in the double-pole case.** For nonprincipal characters `χ` mod `M`
and `ψ` mod `N` (`χ ≠ 1`, `ψ ≠ 1`) with `χ.mul ψ = 1`, `1 / 2 < β < 1`, and `x > 0`, the pole at
`s = 1 - β` is double and contributes the derivative of the regularized product at `1`. -/
theorem mellinInv_Gamma_mul_pair_of_mul_eq_one (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ = 1)
    {β : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s ↦ Gamma s *
      (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
        (χ.mul ψ).LFunction (s + β))) x =
      mellinInv (1 / 2 - β) (fun s ↦ Gamma s *
        (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
          (χ.mul ψ).LFunction (s + β))) x +
        (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β) +
        deriv (fun w ↦ LFunctionTrivChar₁ 1 w * χ.LFunction w * ψ.LFunction w *
          LFunctionTrivChar₁ (Nat.lcm M N) w *
          ((x : ℂ) ^ (-(w - β)) * Gamma (w - β))) 1 := by
  rw [mellinInv_Gamma_mul_pair_eq_add_residue χ ψ hβ₀ hβ₁ hx,
    residue_pair_mul_of_mul_eq_one χ ψ hχ hψ hχψ (analyticAt_cpow_mul_Gamma_sub_one hβ₁ hx)]

private lemma norm_Gamma_shifted_le {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β ≤ 1) (t : ℝ) :
    ‖Gamma ((1 / 2 - β : ℝ) + t * I)‖ ≤ 960 * ((1 + t ^ 2) ^ 3)⁻¹ := by
  set σ : ℝ := 1 / 2 - β
  set z : ℂ := (σ : ℂ) + t * I
  have hfac (k : ℕ) : ‖z + k‖ ^ 2 = (σ + k) ^ 2 + t ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]; simp [z]; ring
  have hf0 : (1 / 16) * (1 + t ^ 2) ≤ ‖z + (0 : ℕ)‖ ^ 2 := by
    rw [hfac 0]; simp only [Nat.cast_zero, add_zero]
    have hσ4 : σ ≤ -(1 / 4) := by dsimp [σ]; linarith
    nlinarith [sq_nonneg t]
  have hf1 : (1 / 4) * (1 + t ^ 2) ≤ ‖z + (1 : ℕ)‖ ^ 2 := by
    rw [hfac 1]; simp only [Nat.cast_one]
    have hσ1 : 1 / 2 ≤ σ + 1 := by dsimp [σ]; linarith
    nlinarith [sq_nonneg t]
  have hfk {k : ℕ} (hk : 2 ≤ k) : 1 + t ^ 2 ≤ ‖z + k‖ ^ 2 := by
    rw [hfac k]
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hσk : 1 ≤ σ + k := by dsimp [σ]; linarith
    nlinarith
  have hp_sq : ((1 / 8) * (1 + t ^ 2) ^ 3) ^ 2 ≤ (∏ k ∈ Finset.range 6, ‖z + k‖) ^ 2 := by
    rw [← Finset.prod_pow]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    have h2 := hfk (by decide : 2 ≤ 2); have h3 := hfk (by decide : 2 ≤ 3)
    have h4 := hfk (by decide : 2 ≤ 4); have h5 := hfk (by decide : 2 ≤ 5)
    calc ((1 / 8) * (1 + t ^ 2) ^ 3) ^ 2
        = ((1 / 16) * (1 + t ^ 2)) * ((1 / 4) * (1 + t ^ 2)) *
            (1 + t ^ 2) * (1 + t ^ 2) * (1 + t ^ 2) * (1 + t ^ 2) := by ring
      _ ≤ ‖z + (0 : ℕ)‖ ^ 2 * ‖z + (1 : ℕ)‖ ^ 2 * ‖z + (2 : ℕ)‖ ^ 2 *
            ‖z + (3 : ℕ)‖ ^ 2 * ‖z + (4 : ℕ)‖ ^ 2 * ‖z + (5 : ℕ)‖ ^ 2 := by gcongr
  have hp : (1 / 8) * (1 + t ^ 2) ^ 3 ≤ ∏ k ∈ Finset.range 6, ‖z + k‖ :=
    le_of_pow_le_pow_left₀ two_ne_zero (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hp_sq
  have hΓprod := norm_Gamma_mul_prod_norm_le (s := z) (n := 6) (by simp [z, σ]; linarith)
  have hΓ6 : Real.Gamma (z.re + 6) ≤ 120 := by
    have hzre : z.re = σ := by simp [z]
    rw [hzre]
    calc Real.Gamma (σ + 6) ≤ Real.Gamma 6 :=
          Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp [σ]; linarith) (by norm_num)
            (by dsimp [σ]; linarith)
      _ = 120 := by simp [Nat.factorial]
  have h1 := (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (hΓprod.trans hΓ6)
  have hrew : (960 : ℝ) * ((1 + t ^ 2) ^ 3)⁻¹ = 120 / ((1 / 8) * (1 + t ^ 2) ^ 3) := by
    field_simp; ring
  rw [hrew, le_div_iff₀ (by positivity)]
  exact h1

private lemma norm_Gamma_mul_pair_shifted_le (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β ≤ 1) (t : ℝ) :
    ‖Gamma ((1 / 2 - β : ℝ) + t * I) * pairProd χ ψ (((1 / 2 - β : ℝ) + t * I) + β)‖ ≤
      245760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹ := by
  set z : ℂ := ((1 / 2 - β : ℝ) : ℂ) + t * I
  have hT : 0 < 1 + t ^ 2 := by positivity
  have hw : z + β = (1 / 2 : ℂ) + t * I := by push_cast [z]; ring
  have hwd : 1 / 2 ≤ ‖(1 / 2 : ℂ) + t * I - 1‖ := by
    have hre : ((1 / 2 : ℂ) + t * I - 1).re = -(1 / 2) := by simp; ring
    have habs := abs_re_le_norm ((1 / 2 : ℂ) + t * I - 1)
    rw [hre] at habs; norm_num at habs; exact habs
  have hwn4 : ‖(1 / 2 : ℂ) + t * I‖ ^ 4 ≤ (1 + t ^ 2) ^ 2 := by
    have hsq : ‖(1 / 2 : ℂ) + t * I‖ ^ 2 ≤ 1 + t ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp; linarith
    calc ‖(1 / 2 : ℂ) + t * I‖ ^ 4 = (‖(1 / 2 : ℂ) + t * I‖ ^ 2) ^ 2 := by ring
      _ ≤ (1 + t ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
  have hF : ‖pairProd χ ψ (z + β)‖ ≤ 256 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by
    rw [hw]
    exact (norm_pair_le_of_one_half_le_re χ ψ (by simp) hwd).trans (by gcongr)
  rw [norm_mul]
  calc ‖Gamma z‖ * ‖pairProd χ ψ (z + β)‖
      ≤ (960 * ((1 + t ^ 2) ^ 3)⁻¹) * (256 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2) :=
        mul_le_mul (norm_Gamma_shifted_le hβ₀ hβ₁ t) hF (norm_nonneg _) (by positivity)
    _ = 245760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹ := by field_simp [hT.ne']; ring

private lemma norm_mellinInv_Gamma_mul_pair_le (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖mellinInv (1 / 2 - β) (fun s ↦ Gamma s *
      (riemannZeta (s + β) * χ.LFunction (s + β) * ψ.LFunction (s + β) *
        (χ.mul ψ).LFunction (s + β))) x‖ ≤
      122880 * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2) := by
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hint : Integrable fun t : ℝ ↦
      x ^ (β - 1 / 2) * (245760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.const_mul _).const_mul _
  have hle : ‖∫ t : ℝ, (x : ℂ) ^ (-(((1 / 2 - β : ℝ) : ℂ) + t * I)) •
      (Gamma ((1 / 2 - β : ℝ) + t * I) *
        pairProd χ ψ (((1 / 2 - β : ℝ) + t * I) + β))‖ ≤
      ∫ t : ℝ, x ^ (β - 1 / 2) * (245760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹) := by
    refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun t ↦ ?_)
    rw [smul_eq_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-(((1 / 2 - β : ℝ) : ℂ) + t * I)).re = β - 1 / 2 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left (norm_Gamma_mul_pair_shifted_le χ ψ hβ₀ hβ₁ t)
      (Real.rpow_nonneg hx.le _)
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, (x : ℂ) ^ (-(((1 / 2 - β : ℝ) : ℂ) + t * I)) •
        (Gamma ((1 / 2 - β : ℝ) + t * I) *
           pairProd χ ψ (((1 / 2 - β : ℝ) + t * I) + β))‖
      ≤ 1 / (2 * Real.pi) *
          ∫ t : ℝ, x ^ (β - 1 / 2) * (245760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 122880 * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2) := by
        rw [integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq]
        field_simp [Real.pi_ne_zero]; ring

private lemma one_quarter_le_norm_residue_term {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β < 1)
    (hFβ : (pairProd χ ψ β).re ≤ 0) :
    1 / 4 ≤ ‖χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
      ((((491520 * ((M : ℝ) * N) ^ 2) ^ (-4 : ℝ) : ℝ) : ℂ) ^ (-((1 : ℂ) - β)) *
        Gamma ((1 : ℂ) - β))‖ := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hMN1 : 1 ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.mul_pos (NeZero.pos M) (NeZero.pos N)
  set Q : ℝ := 491520 * ((M : ℝ) * N) ^ 2
  have hQ2 : 2 ≤ Q := by dsimp [Q]; nlinarith
  have hQ0 : 0 < Q := by linarith
  set x : ℝ := Q ^ (-4 : ℝ)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hQ0 _
  have hx_half : x ≤ 1 / 2 :=
    (Real.rpow_le_rpow_of_nonpos zero_lt_two hQ2 (by norm_num)).trans (by norm_num)
  have hexp : 1 / 2 ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have hx_err : x ^ (β - 1 / 2) ≤ Q⁻¹ := by
    have he1 : (-4 : ℝ) * (1 / 4) = -1 := by norm_num
    calc x ^ (β - 1 / 2) ≤ x ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith) (by linarith)
      _ = Q⁻¹ := by
          dsimp [x]
          rw [← Real.rpow_mul hQ0.le, he1, Real.rpow_neg_one]
  have herr : ‖mellinInv (1 / 2 - β) (fun s ↦ Gamma s * pairProd χ ψ (s + β)) x‖ ≤ 1 / 4 := by
    calc ‖mellinInv (1 / 2 - β) (fun s ↦ Gamma s * pairProd χ ψ (s + β)) x‖
        ≤ 122880 * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2) :=
          norm_mellinInv_Gamma_mul_pair_le χ ψ hβ₀ hβ₁.le hx0
      _ ≤ 122880 * ((M : ℝ) * N) ^ 2 * Q⁻¹ := by gcongr
      _ = 1 / 4 := by dsimp [Q]; field_simp [hM0, hN0]; ring
  set R₁ : ℂ := χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
    ((x : ℂ) ^ (-((1 : ℂ) - β)) * Gamma ((1 : ℂ) - β))
  have hshift := congrArg Complex.re
    (mellinInv_Gamma_mul_pair_of_mul_ne_one χ ψ hχ hψ hχψ (by linarith) hβ₁ hx0)
  simp only [add_re] at hshift
  have hlow := hexp.trans
    (exp_neg_le_re_mellinInv_Gamma_mul_pair hχq hψq (by linarith : -1 < β) hx0)
  have herr_re := (le_abs_self _).trans (abs_re_le_norm
    (mellinInv (1 / 2 - β) (fun s ↦ Gamma s * pairProd χ ψ (s + β)) x)) |>.trans herr
  have hreR : 1 / 4 ≤ R₁.re := by dsimp [pairProd] at hlow herr_re hFβ; linarith
  exact hreR.trans (Complex.re_le_norm R₁)

/-- **Goldfeld's fundamental residue lower bound.** There is an absolute constant `c > 0` such that
for any nonprincipal quadratic characters `χ` mod `M` and `ψ` mod `N` with `χ.mul ψ ≠ 1` and any
`3 / 4 ≤ β < 1` where `Re (ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)) ≤ 0`,
`c (1 - β) (M N)^{-8(1 - β)} ≤ Re L(1, χ) · Re L(1, ψ) · Re L(1, χ.mul ψ)`. -/
theorem exists_pos_mul_rpow_le_re_LFunction_one_mul :
    ∃ c : ℝ, 0 < c ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      ∀ {β : ℝ}, 3 / 4 ≤ β → β < 1 →
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0 →
      c * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) ≤
        (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := by
  refine ⟨1 / 3932160, by norm_num, fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ₀ hβ₁ hFβ ↦ ?_⟩
  set Q : ℝ := 491520 * ((M : ℝ) * N) ^ 2
  have hMN1 : 1 ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.mul_pos (NeZero.pos M) (NeZero.pos N)
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  set x : ℝ := Q ^ (-4 : ℝ)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hQ0 _
  have hR₁_ge := one_quarter_le_norm_residue_term hχq hψq hχ hψ hχψ hβ₀ hβ₁ hFβ
  set P : ℝ := (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg
    (Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ)).1.le
    (Complex.pos_iff.mp (LFunction_apply_one_pos hψq hψ)).1.le)
    (Complex.pos_iff.mp (LFunction_apply_one_pos (isQuadratic_mul hχq hψq) hχψ)).1.le
  have hx_pow : ‖(x : ℂ) ^ (-((1 : ℂ) - β))‖ ≤ 491520 * ((M : ℝ) * N) ^ (8 * (1 - β)) := by
    have hre_exp : (-((1 : ℂ) - β)).re = -(1 - β) := by simp
    have hm1 : (-4 : ℝ) * -(1 - β) = 4 * (1 - β) := by ring
    have hm2 : (2 : ℕ) * (4 * (1 - β)) = 8 * (1 - β) := by push_cast; ring
    rw [norm_cpow_eq_rpow_re_of_pos hx0, hre_exp]
    dsimp [x, Q]
    rw [← Real.rpow_mul hQ0.le, hm1, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast ((M : ℝ) * N) 2, ← Real.rpow_mul (by positivity), hm2]
    exact mul_le_mul_of_nonneg_right
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : 4 * (1 - β) ≤ 1)).trans
        (by norm_num)) (by positivity)
  have hΓ_le : ‖Gamma ((1 : ℂ) - β)‖ ≤ 2 / (1 - β) :=
    (norm_Gamma_le_Gamma_re (by simp; linarith)).trans (gamma_one_sub_le_two_div hβ₀ hβ₁)
  have hR₁_le : ‖χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
      ((x : ℂ) ^ (-((1 : ℂ) - β)) * Gamma ((1 : ℂ) - β))‖ ≤
      P * (491520 * ((M : ℝ) * N) ^ (8 * (1 - β)) * (2 / (1 - β))) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_LFunction_one_eq_re hχq hχ,
      norm_LFunction_one_eq_re hψq hψ,
      norm_LFunction_one_eq_re (isQuadratic_mul hχq hψq) hχψ]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hx_pow hΓ_le (norm_nonneg _) (by positivity)) hP0
  have hcomb := hR₁_ge.trans hR₁_le
  have h1β : 0 < 1 - β := by linarith
  have hcomb' : (1 - β) / 4 ≤ P * (983040 * ((M : ℝ) * N) ^ (8 * (1 - β))) := by
    calc (1 - β) / 4 = 1 / 4 * (1 - β) := by ring
      _ ≤ P * (491520 * ((M : ℝ) * N) ^ (8 * (1 - β)) * (2 / (1 - β))) * (1 - β) :=
            mul_le_mul_of_nonneg_right hcomb h1β.le
      _ = P * (983040 * ((M : ℝ) * N) ^ (8 * (1 - β))) := by field_simp [h1β.ne']; ring
  have hneg : (-8 : ℝ) * (1 - β) = -(8 * (1 - β)) := by ring
  have hdiv : 1 / 3932160 * (1 - β) * (((M : ℝ) * N) ^ (8 * (1 - β)))⁻¹ =
      (1 - β) / (3932160 * ((M : ℝ) * N) ^ (8 * (1 - β))) := by ring
  rw [hneg, Real.rpow_neg (by positivity), hdiv, div_le_iff₀ (by positivity)]
  linarith

end DirichletCharacter
