/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# The Mellin–Barnes integral of `(1 + u)^{-a}` and Barnes's first lemma

For `0 < Re s < Re a` the Mellin transform of `t ↦ (1 + t)^{-a}` is Euler's Beta integral of the
second kind ([DLMF 5.12.3](https://dlmf.nist.gov/5.12.E3)),

`∫₀^∞ t^{s - 1} (1 + t)^{-a} dt = Γ(s) Γ(a - s) / Γ(a)`,

obtained from the Beta integral over `[0, 1]` by the substitution `t = u / (1 - u)`. This adapts
the real-variable proof of `TauCeti.integral_rpow_mul_one_add_rpow` to complex parameters. On
every vertical line `Re s = σ` avoiding the poles of both factors the product `Γ(s) Γ(a - s)` is
integrable, since `Γ(σ + i y)` decays faster than every power of `|y|` while `Γ(a - σ - i y)` is
bounded. For `0 < σ < Re a`, Mellin inversion then gives the Mellin–Barnes integral of the
binomial,

`Γ(a) (1 + u)^{-a} = (1 / 2π) ∫ Γ(σ + i y) Γ(a - σ - i y) u^{-σ - i y} dy`   for `u > 0`.

Integrating `u^{a + i y - 1} (1 + u)^{-(a + c)} Γ(b + i y) Γ(d - i y)` over `(0, ∞) × ℝ` in both
orders via Fubini's theorem yields **Barnes's first lemma**
([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)): for `a, b, c, d : ℂ` with positive real parts,

`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`,

together with its shifted form on any vertical line `Re s = σ` separating `-a, -b` from `c, d`.

## Main results

* `Complex.hasMellin_one_add_cpow_neg`: the Mellin transform of `(1 + t)^{-a}` converges at every
  `s` with `0 < Re s < Re a` and equals `Γ(s) Γ(a - s) / Γ(a)` there.
* `Complex.verticalIntegrable_Gamma_mul_Gamma_sub` and `Complex.integrable_Gamma_add_mul_Gamma_sub`:
  integrability of two-Gamma Mellin–Barnes kernels on pole-free vertical lines.
* `Complex.mellinInv_Gamma_mul_Gamma_sub`, `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`,
  and `Complex.integral_cpow_mul_I_mul_Gamma_add_mul_Gamma_sub`: Mellin–Barnes integral
  evaluations of `(1 + u)^{-a}`.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: integrability of the four-Gamma kernel
  `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` whenever `Re a, Re b, Re c, Re d` avoid the
  nonpositive integers.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: Barnes's first lemma (DLMF 5.13.3).
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_line`: Barnes's first lemma along a
  separating vertical line `Re s = σ`.

## References

* NIST Digital Library of Mathematical Functions, equations 5.12.3 and 5.13.3, and §15.6 (the
  Mellin–Barnes integrals 15.6.6–15.6.7).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§12.41 and 14.5–14.52.
* G. E. Andrews, R. Askey, and R. Roy, *Special Functions*, Theorem 2.4.2.
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp log

namespace Complex

/-- Under the chart `u ↦ u / (1 - u)` of `(0, 1)` onto `(0, ∞)`, the Mellin integrand of
`(1 + t)^{-a}` at `s` becomes the integrand of the Beta integral with parameters `s` and
`a - s`. -/
private lemma abs_deriv_smul_cpow_mul_one_add_cpow (s a : ℂ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    |((1 - u) ^ 2)⁻¹| • (((u / (1 - u) : ℝ) : ℂ) ^ (s - 1) • (1 + ((u / (1 - u) : ℝ) : ℂ)) ^ (-a)) =
      (u : ℂ) ^ (s - 1) * (1 - (u : ℂ)) ^ (a - s - 1) := by
  obtain ⟨hu0, hu1⟩ := hu
  have h1u : 0 < 1 - u := by linarith
  -- every power below has a positive real base, so it is `exp (Real.log x * w)`
  have hexp {x : ℝ} (hx : 0 < x) (w : ℂ) : (x : ℂ) ^ w = cexp (Real.log x * w) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hbase : 1 + ((u / (1 - u) : ℝ) : ℂ) = (((1 - u)⁻¹ : ℝ) : ℂ) := by
    have hr : 1 + u / (1 - u) = (1 - u)⁻¹ := by field_simp; ring
    rw [← hr]
    push_cast
    ring
  have hsub : (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  have hfac : ((|((1 - u) ^ 2)⁻¹| : ℝ) : ℂ) = cexp (-(2 * Real.log (1 - u))) := by
    have hr : |((1 - u) ^ 2)⁻¹| = Real.exp (-(2 * Real.log (1 - u))) := by
      rw [abs_of_nonneg (by positivity), Real.exp_neg,
        show 2 * Real.log (1 - u) = Real.log ((1 - u) ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [hr, ofReal_exp]
    push_cast
    ring_nf
  rw [real_smul, smul_eq_mul, hbase, hsub, hfac,
    hexp (div_pos hu0 h1u), hexp (inv_pos.mpr h1u), hexp hu0, hexp h1u,
    Real.log_div hu0.ne' h1u.ne',
    Real.log_inv, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Euler's Beta integral of the second kind** (DLMF 5.12.3). For `0 < Re s < Re a` the Mellin
transform of `t ↦ (1 + t)^{-a}` converges at `s` and equals `Γ(s) Γ(a - s) / Γ(a)`. -/
theorem hasMellin_one_add_cpow_neg {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    HasMellin (fun t : ℝ ↦ (1 + (t : ℂ)) ^ (-a)) s (Gamma s * Gamma (a - s) / Gamma a) := by
  have has : 0 < (a - s).re := by simpa using hsa
  have hchart : (fun u : ℝ ↦ u / (1 - u)) '' Ioo 0 1 = Ioi 0 := by
    rw [TauCeti.image_div_one_sub_Ioo (u0 := 0) zero_lt_one]
    norm_num
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ ↦ u / (1 - u)) ((1 - u) ^ 2)⁻¹ (Ioo 0 1) u :=
    fun u hu ↦ (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ ↦ u / (1 - u)) (Ioo 0 1) :=
    TauCeti.strictMonoOn_div_one_sub.injOn.mono Ioo_subset_Iio_self
  -- the Beta integrand on `(0, 1)`, as an integrable function on `Ioo 0 1`
  have hbeta : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * (1 - (u : ℂ)) ^ (a - s - 1))
      (Ioo 0 1) := by
    have h := betaIntegral_convergent hs has
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    exact h.mono_set Ioo_subset_Ioc_self
  refine ⟨?_, ?_⟩
  · rw [MellinConvergent, ← hchart,
      integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    exact hbeta.congr_fun (fun u hu ↦ (abs_deriv_smul_cpow_mul_one_add_cpow s a hu).symm)
      measurableSet_Ioo
  · rw [mellin, ← hchart,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
      setIntegral_congr_fun measurableSet_Ioo
        fun u hu ↦ abs_deriv_smul_cpow_mul_one_add_cpow s a hu,
      setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      ← betaIntegral, betaIntegral_eq_Gamma_mul_div _ _ hs has, add_sub_cancel]

/-- On every vertical line `Re s = σ` with neither `σ` nor `Re a - σ` a nonpositive integer, the
product `Γ(s) Γ(a - s)` is integrable. -/
theorem verticalIntegrable_Gamma_mul_Gamma_sub {a : ℂ} {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n)
    (haσ : ∀ n : ℕ, a.re - σ ≠ -n) :
    VerticalIntegrable (fun s ↦ Gamma s * Gamma (a - s)) σ := by
  have hsub (y : ℝ) : a - (σ + y * I) = ↑(a.re - σ) + ↑(a.im - y) * I := by
    apply Complex.ext <;> simp
  obtain ⟨C, hC⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow haσ 0
  refine (verticalIntegrable_Gamma hσ).mul_bdd (c := C) ?_
    (Eventually.of_forall fun y ↦ by simpa [hsub] using hC (a.im - y))
  refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y ↦ ?_)
  refine (differentiableAt_Gamma _ fun m h ↦ haσ m ?_).continuousAt.comp (by fun_prop)
  simpa using congrArg re h

/-- **The Mellin–Barnes integral of `(1 + u)^{-a}`.** On every vertical line `Re s = σ` with
`0 < σ < Re a`, Mellin inversion of `Γ(s) Γ(a - s)` gives `Γ(a) (1 + u)^{-a}` for `u > 0`:
`(1 / 2π) ∫ u^{-(σ + i y)} Γ(σ + i y) Γ(a - σ - i y) dy = Γ(a) (1 + u)^{-a}`. -/
theorem mellinInv_Gamma_mul_Gamma_sub {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re) {u : ℝ}
    (hu : 0 < u) :
    mellinInv σ (fun s ↦ Gamma s * Gamma (a - s)) u = Gamma a * (1 + (u : ℂ)) ^ (-a) := by
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (hσ.trans hσa)
  have hline : ∀ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) =
      mellin (fun t : ℝ ↦ Gamma a • (1 + (t : ℂ)) ^ (-a)) (σ + y * I) := by
    intro y
    rw [mellin_const_smul, (hasMellin_one_add_cpow_neg (by simpa using hσ)
      (by simpa using hσa)).2, smul_eq_mul, mul_div_cancel₀ _ hΓa]
  have hint : VerticalIntegrable (mellin fun t : ℝ ↦ Gamma a • (1 + (t : ℂ)) ^ (-a)) σ :=
    (verticalIntegrable_Gamma_mul_Gamma_sub (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).congr (Eventually.of_forall hline)
  have hconv := (hasMellin_one_add_cpow_neg (s := σ) (a := a) (by simpa using hσ)
    (by simpa using hσa)).1.const_smul (Gamma a)
  have hcont : ContinuousAt (fun t : ℝ ↦ Gamma a • (1 + (t : ℂ)) ^ (-a)) u := by
    refine ((continuousAt_cpow_const ?_).comp (f := fun t : ℝ ↦ 1 + (t : ℂ))
      (by fun_prop)).const_smul (Gamma a)
    rw [← ofReal_one, ← ofReal_add]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  rw [mellinInv]
  simp_rw [hline]
  rw [← mellinInv, mellinInv_mellin_eq σ _ hu hconv hint hcont]
  exact smul_eq_mul _ _

/-- **The Mellin–Barnes integral of `(1 + u)^{-a}`**, as an unnormalised vertical integral: on
every line `Re s = σ` with `0 < σ < Re a`,
`∫ u^{-(σ + i y)} Γ(σ + i y) Γ(a - σ - i y) dy = 2π Γ(a) (1 + u)^{-a}` for `u > 0`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_sub {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (a - (σ + y * I))) =
      2 * π * (Gamma a * (1 + (u : ℂ)) ^ (-a)) := by
  have h := mellinInv_Gamma_mul_Gamma_sub hσ hσa hu
  rw [mellinInv, real_smul] at h
  simp only [smul_eq_mul] at h
  rw [← h, ← mul_assoc,
    show (2 * π : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]

/-- If neither `Re b` nor `Re d` is a nonpositive integer, `y ↦ Γ(b + i y) Γ(d - i y)` is
integrable on `ℝ`. -/
theorem integrable_Gamma_add_mul_Gamma_sub {b d : ℂ} (hb : ∀ n : ℕ, b.re ≠ -n)
    (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦ Gamma (b + y * I) * Gamma (d - y * I) := by
  have h := (verticalIntegrable_Gamma_mul_Gamma_sub (a := b + d) (σ := d.re) hd
    (by simpa using hb)).comp_sub_left d.im
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  have hd_eq : (d.re : ℂ) + ((d.im - y : ℝ) : ℂ) * I = d - y * I := by
    apply Complex.ext <;> simp
  have hb_eq : b + d - (d - y * I) = b + y * I := by ring
  dsimp only
  rw [hd_eq, hb_eq, mul_comm]

/-- Shifted Mellin–Barnes integral of the binomial: for `Re b > 0`, `Re d > 0`, and `u > 0`,
`∫ u^{i y} Γ(b + i y) Γ(d - i y) dy = 2π Γ(b + d) u^d (1 + u)^{-(b + d)}`. -/
theorem integral_cpow_mul_I_mul_Gamma_add_mul_Gamma_sub {b d : ℂ} (hb : 0 < b.re) (hd : 0 < d.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (y * I) * (Gamma (b + y * I) * Gamma (d - y * I)) =
      2 * π * Gamma (b + d) * (u : ℂ) ^ d * (1 + (u : ℂ)) ^ (-(b + d)) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  rw [← integral_sub_left_eq_self _ volume d.im]
  have hcongr : (fun y : ℝ ↦ (u : ℂ) ^ (((d.im - y : ℝ) : ℂ) * I) *
        (Gamma (b + ((d.im - y : ℝ) : ℂ) * I) * Gamma (d - ((d.im - y : ℝ) : ℂ) * I))) =
      fun y : ℝ ↦ (u : ℂ) ^ d * ((u : ℂ) ^ (-((d.re : ℂ) + y * I)) *
        (Gamma ((d.re : ℂ) + y * I) * Gamma (b + d - ((d.re : ℂ) + y * I)))) := by
    ext y
    have hd_eq : (d.re : ℂ) + y * I = d - ((d.im - y : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hexp : ((d.im - y : ℝ) : ℂ) * I = d + -((d.re : ℂ) + y * I) := by
      rw [hd_eq]; ring
    rw [hexp, cpow_add _ _ hu0]
    ring_nf
  rw [hcongr, integral_const_mul,
    integral_cpow_neg_mul_Gamma_mul_Gamma_sub hd (by simpa using hb) hu]
  ring

/-- If none of `Re a, Re b, Re c, Re d` is a nonpositive integer, the four-Gamma Barnes integrand
`y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` is integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n) (hc : ∀ n : ℕ, c.re ≠ -n)
    (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨Ca, hCa⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow ha 0
  obtain ⟨Cc, hCc⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hc 0
  have ha_eq (y : ℝ) : a + y * I = (a.re : ℂ) + ((a.im + y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hc_eq (y : ℝ) : c - y * I = (c.re : ℂ) + ((c.im - y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hcont : Continuous fun y : ℝ ↦ Gamma (a + y * I) * Gamma (c - y * I) := by
    refine (continuous_iff_continuousAt.2 fun y ↦ ?_).mul
      (continuous_iff_continuousAt.2 fun y ↦ ?_)
    · exact (differentiableAt_Gamma _ fun m h ↦
        ha m (by simpa using congrArg re h)).continuousAt.comp (by fun_prop)
    · exact (differentiableAt_Gamma _ fun m h ↦
        hc m (by simpa using congrArg re h)).continuousAt.comp (by fun_prop)
  have hbdd : ∀ y : ℝ, ‖Gamma (a + y * I) * Gamma (c - y * I)‖ ≤ Ca * Cc := fun y ↦ by
    have h1 : ‖Gamma (a + y * I)‖ ≤ Ca := by simpa [ha_eq y] using hCa (a.im + y)
    have h2 : ‖Gamma (c - y * I)‖ ≤ Cc := by simpa [hc_eq y] using hCc (c.im - y)
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hint := (integrable_Gamma_add_mul_Gamma_sub hb hd).bdd_mul hcont.aestronglyMeasurable
    (Eventually.of_forall hbdd)
  exact hint.congr (Eventually.of_forall fun y ↦ by dsimp only; ring)

/-- Product integrability of the two-variable kernel in the proof of Barnes's first lemma. -/
private theorem integrable_barnesKernel {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable
      (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ (a - 1) * (1 + (p.1 : ℂ)) ^ (-(a + c))) *
        ((p.1 : ℂ) ^ (p.2 * I) * (Gamma (b + p.2 * I) * Gamma (d - p.2 * I))))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hg₁ : Integrable (fun u : ℝ ↦ ‖(u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (-(a + c))‖)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [MellinConvergent, IntegrableOn, smul_eq_mul] using
      (hasMellin_one_add_cpow_neg (s := a) (a := a + c) ha (by simpa using hc)).1.norm
  have hg₂ : Integrable (fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖) volume :=
    (integrable_Gamma_add_mul_Gamma_sub
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).norm
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ (a - 1) * (1 + (p.1 : ℂ)) ^ (-(a + c))) *
        ((p.1 : ℂ) ^ (p.2 * I) * (Gamma (b + p.2 * I) * Gamma (d - p.2 * I))))
      (Ioi (0 : ℝ) ×ˢ univ) := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hu_slit : (p.1 : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hp1
    have h1u_slit : 1 + (p.1 : ℂ) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_mem_slitPlane.2 (by linarith)
    have hc1 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (a - 1)) p :=
      (continuous_ofReal.comp continuous_fst).continuousAt.cpow continuousAt_const hu_slit
    have hc2 : ContinuousAt (fun q : ℝ × ℝ ↦ (1 + (q.1 : ℂ)) ^ (-(a + c))) p :=
      (continuous_const.add (continuous_ofReal.comp continuous_fst)).continuousAt.cpow
        continuousAt_const h1u_slit
    have hc3 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (q.2 * I)) p :=
      (continuous_ofReal.comp continuous_fst).continuousAt.cpow (by fun_prop) hu_slit
    have hc4 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (b + q.2 * I)) p :=
      (differentiableAt_Gamma _ fun m h ↦ by
        have := congrArg re h; simp at this; linarith [m.cast_nonneg' (α := ℝ)]).continuousAt.comp
        (by fun_prop)
    have hc5 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (d - q.2 * I)) p :=
      (differentiableAt_Gamma _ fun m h ↦ by
        have := congrArg re h; simp at this; linarith [m.cast_nonneg' (α := ℝ)]).continuousAt.comp
        (by fun_prop)
    exact ((hc1.mul hc2).mul (hc3.mul (hc4.mul hc5))).continuousWithinAt
  have hprod_eq : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ (a - 1) * (1 + (p.1 : ℂ)) ^ (-(a + c))) *
        ((p.1 : ℂ) ^ (p.2 * I) * (Gamma (b + p.2 * I) * Gamma (d - p.2 * I))))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [hprod_eq]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
  refine (hg₁.smul_prod hg₂).mono' hmeas ?_
  have hae : ∀ᶠ p : ℝ × ℝ in ae ((volume.restrict (Ioi (0 : ℝ))).prod volume),
      p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := by
    rw [hprod_eq]
    exact ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)
  filter_upwards [hae] with p hp
  have hp1 : 0 < p.1 := hp.1
  have hnorm_I : ‖(p.1 : ℂ) ^ (p.2 * I)‖ = 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos hp1]
    simp
  simp [smul_eq_mul, hnorm_I]

/-- The `y`-first iterated integral in the Fubini proof of Barnes's first lemma. -/
private theorem integral_barnesKernel_right {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    ∫ u in Ioi (0 : ℝ), ∫ y : ℝ,
      ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
        ((u : ℂ) ^ (y * I) * (Gamma (b + y * I) * Gamma (d - y * I))) =
      2 * π * Gamma (b + d) * (Gamma (a + d) * Gamma (b + c) / Gamma (a + b + c + d)) := by
  have hinner : ∀ u ∈ Ioi (0 : ℝ),
      ∫ y : ℝ, ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
          ((u : ℂ) ^ (y * I) * (Gamma (b + y * I) * Gamma (d - y * I))) =
        (2 * π * Gamma (b + d)) *
          ((u : ℂ) ^ (a + d - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := fun u (hu : 0 < u) ↦ by
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
    have h1u0 : 1 + (u : ℂ) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_ne_zero.2 (by linarith)
    rw [integral_const_mul, integral_cpow_mul_I_mul_Gamma_add_mul_Gamma_sub hb hd hu]
    have hp1 : (u : ℂ) ^ (a - 1) * (u : ℂ) ^ d = (u : ℂ) ^ (a + d - 1) := by
      rw [← cpow_add _ _ hu0]; ring_nf
    have hp2 : (1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)) =
        (1 + (u : ℂ)) ^ (-(a + b + c + d)) := by
      rw [← cpow_add _ _ h1u0]; ring_nf
    linear_combination (2 * π * Gamma (b + d) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) * hp1 +
      (2 * π * Gamma (b + d) * (u : ℂ) ^ (a - 1) * (u : ℂ) ^ d) * hp2
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul]
  have hm := (hasMellin_one_add_cpow_neg (s := a + d) (a := a + b + c + d)
    (by simp; linarith) (by simp; linarith)).2
  have hsub : a + b + c + d - (a + d) = b + c := by ring
  rw [mellin] at hm
  simpa only [smul_eq_mul, hsub] using congrArg ((2 * π * Gamma (b + d)) * ·) hm

/-- The `u`-first iterated integral in the Fubini proof of Barnes's first lemma. -/
private theorem integral_barnesKernel_left {a b c d : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) :
    ∫ y : ℝ, ∫ u in Ioi (0 : ℝ),
      ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
        ((u : ℂ) ^ (y * I) * (Gamma (b + y * I) * Gamma (d - y * I))) =
      (Gamma (a + c))⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  have hinner : ∀ y : ℝ,
      ∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
          ((u : ℂ) ^ (y * I) * (Gamma (b + y * I) * Gamma (d - y * I))) =
        (Gamma (a + c))⁻¹ * (Gamma (a + y * I) * Gamma (b + y * I) *
          Gamma (c - y * I) * Gamma (d - y * I)) := fun y ↦ by
    have hcongr : ∀ u ∈ Ioi (0 : ℝ),
        ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
          ((u : ℂ) ^ (y * I) * (Gamma (b + y * I) * Gamma (d - y * I))) =
        ((u : ℂ) ^ (a + y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
          (Gamma (b + y * I) * Gamma (d - y * I)) := fun u (hu : 0 < u) ↦ by
      have hp : (u : ℂ) ^ (a - 1) * (u : ℂ) ^ (y * I) = (u : ℂ) ^ (a + y * I - 1) := by
        rw [← cpow_add _ _ (ofReal_ne_zero.2 hu.ne')]; ring_nf
      linear_combination ((1 + (u : ℂ)) ^ (-(a + c)) *
        (Gamma (b + y * I) * Gamma (d - y * I))) * hp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_mul_const]
    have hm := (hasMellin_one_add_cpow_neg (s := a + y * I) (a := a + c)
      (by simpa using ha) (by simpa using hc)).2
    have hsub : a + c - (a + y * I) = c - y * I := by ring
    rw [mellin] at hm
    simp only [smul_eq_mul, hsub] at hm
    rw [hm]
    ring
  simp_rw [hinner, integral_const_mul]

/-- **Barnes's first lemma** ([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)). For `a, b, c, d : ℂ`
with positive real parts,
`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have hswap := integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume)
    (f := fun (u : ℝ) (y : ℝ) ↦ ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
      ((u : ℂ) ^ (y * I) * (Gamma (b + y * I) * Gamma (d - y * I))))
    (integrable_barnesKernel ha hb hc hd)
  rw [integral_barnesKernel_right ha hb hc hd, integral_barnesKernel_left ha hc] at hswap
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using add_pos ha hc)
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  calc (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)
      = (2 * π : ℂ)⁻¹ * (Gamma (a + c) * ((Gamma (a + c))⁻¹ * ∫ y : ℝ,
          Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I))) := by
        rw [mul_inv_cancel_left₀ hΓac]
    _ = (2 * π : ℂ)⁻¹ * (Gamma (a + c) *
          (2 * π * Gamma (b + d) * (Gamma (a + d) * Gamma (b + c) / Gamma (a + b + c + d)))) := by
        rw [← hswap]
    _ = Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
        field_simp [h2pi]

/-- **Barnes's first lemma along a separating vertical line**: for any real `σ` with
`-Re a < σ`, `-Re b < σ`, `σ < Re c`, and `σ < Re d`,
`(1 / 2π) ∫ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - σ - i y) Γ(d - σ - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_line {a b c d : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hc : σ < c.re) (hd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma (a := a + σ) (b := b + σ) (c := c - σ)
    (d := d - σ) (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hcongr : (fun y : ℝ ↦ Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I))) =
      fun y : ℝ ↦ Gamma (a + σ + y * I) * Gamma (b + σ + y * I) *
        Gamma (c - σ - y * I) * Gamma (d - σ - y * I) := by
    ext y
    ring_nf
  rw [hcongr, h]
  ring_nf

end Complex
