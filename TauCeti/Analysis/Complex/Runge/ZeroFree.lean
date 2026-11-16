/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import TauCeti.Topology.FilledIn
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Contour.Primitive
import TauCeti.Analysis.Contour.Winding.LocallyConstant
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# Zero-free Runge approximation on filled compact sets

Ordinary Runge approximation approximates a function `u` holomorphic near a compact set `K ⊆ Ω`
uniformly on `K` by functions holomorphic on all of `Ω` when `K` is filled in `Ω`
(`TauCeti.IsFilledIn K Ω`). Uniform proximity on `K` keeps the approximants nonvanishing near `K`
when `u` has no zeros on `K`, yet says nothing about zeros far from `K`: on the punctured plane
`Ω = ℂ \ {0}` with `K = {z | 1 ≤ ‖z‖ ≤ 2}`, the function `u z = z - 1 / 2` is already holomorphic
on `Ω` and nowhere zero on `K`, while vanishing at `1 / 2 ∈ Ω`.

This file proves the **zero-free Runge approximation theorem**
(`TauCeti.IsFilledIn.exists_differentiableOn_ne_zero_norm_sub_lt`): if `K ⊆ Ω` is compact and
filled in the open set `Ω ⊆ ℂ`, and `u` is holomorphic on an open neighborhood `U` of `K` without
zeros on `K`, then `u` can be approximated uniformly on `K` by functions that are holomorphic and
*nowhere zero throughout `Ω`*. Neither `K` nor `Ω` is required to be connected or nonempty.

The proof follows Rainer's pole-pairing factorization:

1. **Holomorphic logarithms of Borsuk quotients**
   (`TauCeti.exists_isOpen_differentiableOn_eqOn_exp_comp_sub_div_sub`): if `b ∉ K` and
   `a ∈ connectedComponentIn Kᶜ b`, a path in `Kᶜ` from `b` to `a` has compact image `P` disjoint
   from `K`, so every closed piecewise-`C¹` curve in the open neighborhood `W = Pᶜ` of `K` winds
   equally around `a` and `b`. Thus `logDeriv (fun z ↦ (z - b) / (z - a))` has vanishing periods
   on `W`, giving a holomorphic logarithm of `(z - b) / (z - a)` on `W`.
2. **Unbounded-component linear factors**
   (`TauCeti.exists_isOpen_differentiableOn_eqOn_exp_comp_sub_of_notMem_filledHull`): if
   `b ∉ filledHull K`, it lies in the unique unbounded component of `Kᶜ`, which also contains a
   positive real `r` outside a disc `ball 0 r ⊇ filledHull K`. Combining the Borsuk quotient for
   `(b, r)` with a holomorphic logarithm of `z - r` on the convex disc `ball 0 r` yields a
   holomorphic logarithm of `z - b` near `K`.
3. **Global zero-free factorization**: discretizing the Cauchy–Pompeiu representation approximates
   `u` on `K` by a rational sum `r(z) = ∑ i, d i * (z - ζ i)⁻¹` without zeros on `K`. Writing
   `r = P / Q` and splitting `P` over `ℂ`, each root or pole in a bounded component of `Kᶜ` is
   paired with a point of that component outside `Ω` (supplied by `IsFilledIn K Ω`), while factors
   in the unbounded component are absorbed into an exponential. Hence `r = H * exp ℓ` near `K` with
   `H` holomorphic and zero-free on `Ω`; approximating `ℓ` on `K` by `L` holomorphic on `Ω` produces
   the nowhere-zero approximant `G = H * exp L`.

## Main results

* `TauCeti.exists_isOpen_differentiableOn_eqOn_exp_comp_sub_div_sub`: when `K` is closed and `a`
  lies in the connected component of `b` in `Kᶜ`, `(z - b) / (z - a)` admits a holomorphic
  logarithm on an open neighborhood of `K`.
* `TauCeti.exists_isOpen_differentiableOn_eqOn_exp_comp_sub_of_notMem_filledHull`: when
  `b ∉ filledHull K` for compact `K`, `z - b` admits a holomorphic logarithm on an open
  neighborhood of `K`.
* `TauCeti.IsFilledIn.exists_differentiableOn_ne_zero_norm_sub_lt`: zero-free Runge approximation
  on compact sets filled in an open plane set `Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 15.1 and Proposition 15.2.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.9.
-/

public section

open Bornology Complex Filter Function Metric Polynomial Set
open scoped Real Topology

namespace TauCeti

/-- **Logarithmic derivative of a Borsuk quotient.** Off `{a, b}`, the logarithmic derivative of
`z ↦ (z - b) / (z - a)` is `(z - b)⁻¹ - (z - a)⁻¹`. -/
private theorem logDeriv_sub_div_sub {a b z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    logDeriv (fun w ↦ (w - b) / (w - a)) z = (z - b)⁻¹ - (z - a)⁻¹ := by
  have hda : DifferentiableAt ℂ (fun w ↦ w - a) z := differentiableAt_id.sub_const a
  have hdb : DifferentiableAt ℂ (fun w ↦ w - b) z := differentiableAt_id.sub_const b
  have hdiv := logDeriv_div (f := fun w ↦ w - b) (g := fun w ↦ w - a) z
    (sub_ne_zero.mpr hzb) (sub_ne_zero.mpr hza) hdb hda
  simpa [Pi.div_def, logDeriv_apply] using hdiv

/-- Period vanishing of `logDeriv (fun z ↦ (z - b) / (z - a))` outside a preconnected set `P`
containing `a` and `b`. -/
private theorem isExactOn_logDeriv_sub_div_sub_of_isPreconnected {P : Set ℂ}
    (hPopen : IsOpen Pᶜ) (hPconn : IsPreconnected P) {a b : ℂ} (haP : a ∈ P) (hbP : b ∈ P) :
    Complex.IsExactOn (logDeriv fun z ↦ (z - b) / (z - a)) Pᶜ := by
  have hnot_a : ∀ z ∈ Pᶜ, z ≠ a := fun z (hz : z ∉ P) h ↦ hz (h ▸ haP)
  have hnot_b : ∀ z ∈ Pᶜ, z ≠ b := fun z (hz : z ∉ P) h ↦ hz (h ▸ hbP)
  have hcont : ContinuousOn (logDeriv fun z ↦ (z - b) / (z - a)) Pᶜ := by
    have hc₁ : ContinuousOn (fun z ↦ (z - b)⁻¹) Pᶜ :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun z hz ↦ sub_ne_zero.mpr (hnot_b z hz)
    have hc₂ : ContinuousOn (fun z ↦ (z - a)⁻¹) Pᶜ :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun z hz ↦ sub_ne_zero.mpr (hnot_a z hz)
    exact (hc₁.sub hc₂).congr fun z hz ↦ logDeriv_sub_div_sub (hnot_a z hz) (hnot_b z hz)
  refine Contour.isExactOn_of_forall_closed_integral_eq_zero hPopen hcont
    fun γ s t hγ hγW hclosed ↦ ?_
  have hP_avoid : P ⊆ (γ '' uIcc s t)ᶜ := fun w hwP ⟨u, hu, hγu⟩ ↦ hγW hu (hγu ▸ hwP)
  have ha_comp : a ∈ connectedComponentIn (γ '' uIcc s t)ᶜ b :=
    hPconn.subset_connectedComponentIn hbP hP_avoid haP
  have hwind := hγ.windingNumber_eq_of_mem_connectedComponentIn hclosed ha_comp
  have havoid_a : ∀ u ∈ uIcc s t, γ u ≠ a := fun u hu ↦ hnot_a (γ u) (hγW hu)
  have havoid_b : ∀ u ∈ uIcc s t, γ u ≠ b := fun u hu ↦ hnot_b (γ u) (hγW hu)
  have hint_a := Contour.intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn havoid_a
    hγ.intervalIntegrable_deriv
  have hint_b := Contour.intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn havoid_b
    hγ.intervalIntegrable_deriv
  rw [Contour.windingNumber_eq_integral_of_avoidance hγ.continuousOn havoid_a hint_a,
    Contour.windingNumber_eq_integral_of_avoidance hγ.continuousOn havoid_b hint_b,
    mul_right_inj' (inv_ne_zero two_pi_I_ne_zero)] at hwind
  have hcongr : EqOn (fun u ↦ deriv γ u • logDeriv (fun z ↦ (z - b) / (z - a)) (γ u))
      (fun u ↦ (γ u - b)⁻¹ * deriv γ u - (γ u - a)⁻¹ * deriv γ u) (uIcc s t) := fun u hu ↦ by
    dsimp only
    rw [smul_eq_mul, logDeriv_sub_div_sub (havoid_a u hu) (havoid_b u hu)]
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hint_b hint_a,
    hwind, sub_self]

/-- **Holomorphic logarithm of a Borsuk quotient near a closed set** (Rainer, Lemma 15.1). If
`K ⊆ ℂ` is closed and `a` lies in the connected component of `b` in `Kᶜ`, then there is an open
neighborhood `W` of `K` avoiding `a` and `b` on which `z ↦ (z - b) / (z - a)` admits a holomorphic
logarithm. -/
theorem exists_isOpen_differentiableOn_eqOn_exp_comp_sub_div_sub {K : Set ℂ} (hK : IsClosed K)
    {a b : ℂ} (ha : a ∈ connectedComponentIn Kᶜ b) :
    ∃ (W : Set ℂ) (ℓ : ℂ → ℂ), IsOpen W ∧ K ⊆ W ∧ a ∉ W ∧ b ∉ W ∧
      DifferentiableOn ℂ ℓ W ∧ EqOn (Complex.exp ∘ ℓ) (fun z ↦ (z - b) / (z - a)) W := by
  obtain ⟨p, hp⟩ := hK.isOpen_compl.joinedIn_of_mem_connectedComponentIn ha
  have hWopen : IsOpen (range p)ᶜ := (isCompact_range p.continuous).isClosed.isOpen_compl
  have hbP : b ∈ range p := ⟨0, p.source⟩
  have haP : a ∈ range p := ⟨1, p.target⟩
  have hKW : K ⊆ (range p)ᶜ := by
    rintro z hz ⟨t, rfl⟩
    exact connectedComponentIn_subset Kᶜ b (hp t) hz
  have hg_diff : DifferentiableOn ℂ (fun z ↦ (z - b) / (z - a)) (range p)ᶜ :=
    (differentiableOn_id.sub (differentiableOn_const b)).div
      (differentiableOn_id.sub (differentiableOn_const a)) fun z (hz : z ∉ range p) ↦
        sub_ne_zero.mpr fun h ↦ hz (h ▸ haP)
  have hg_ne : (0 : ℂ) ∉ (fun z ↦ (z - b) / (z - a)) '' (range p)ᶜ := by
    rintro ⟨z, hz : z ∉ range p, hz0⟩
    exact div_ne_zero (sub_ne_zero.mpr fun h : z = b ↦ hz (h ▸ hbP))
      (sub_ne_zero.mpr fun h : z = a ↦ hz (h ▸ haP)) hz0
  have hexact := isExactOn_logDeriv_sub_div_sub_of_isPreconnected hWopen
    (isPreconnected_range p.continuous) haP hbP
  obtain ⟨ℓ, hℓ, heq⟩ :=
    Contour.exists_differentiableOn_eqOn_exp_comp_of_isExactOn hWopen hg_diff hg_ne hexact
  exact ⟨(range p)ᶜ, ℓ, hWopen, hKW, fun h ↦ h haP, fun h ↦ h hbP, hℓ, heq⟩

/-- **Holomorphic logarithm of an unbounded-component linear factor.** If `K ⊆ ℂ` is compact and
`b ∉ filledHull K`, then `z ↦ z - b` admits a holomorphic logarithm on an open neighborhood of
`K`. -/
theorem exists_isOpen_differentiableOn_eqOn_exp_comp_sub_of_notMem_filledHull {K : Set ℂ}
    (hK : IsCompact K) {b : ℂ} (hb : b ∉ filledHull K) :
    ∃ (W : Set ℂ) (ℓ : ℂ → ℂ), IsOpen W ∧ K ⊆ W ∧
      DifferentiableOn ℂ ℓ W ∧ EqOn (Complex.exp ∘ ℓ) (fun z ↦ z - b) W := by
  obtain ⟨R₀, hR₀⟩ := (isBounded_filledHull.mpr hK.isBounded).subset_ball (0 : ℂ)
  set r : ℝ := max R₀ 1
  have hr : 0 < r := lt_max_of_lt_right zero_lt_one
  have hball : filledHull K ⊆ ball (0 : ℂ) r := hR₀.trans (ball_subset_ball (le_max_left R₀ 1))
  have hr_notMem : (r : ℂ) ∉ filledHull K := fun h ↦ by
    have hlt := mem_ball_zero_iff.mp (hball h)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hlt
    exact lt_irrefl r hlt
  have hrank : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  have hr_comp : (r : ℂ) ∈ connectedComponentIn Kᶜ b := by
    rw [← compl_filledHull_eq_connectedComponentIn hrank hK.isBounded hb]
    exact hr_notMem
  obtain ⟨W₁, ℓ₁, hW₁, hKW₁, -, -, hℓ₁, heq₁⟩ :=
    exists_isOpen_differentiableOn_eqOn_exp_comp_sub_div_sub hK.isClosed hr_comp
  have hg₂_diff : DifferentiableOn ℂ (fun z : ℂ ↦ z - r) (ball 0 r) :=
    differentiableOn_id.sub (differentiableOn_const (r : ℂ))
  have hg₂_ne : (0 : ℂ) ∉ (fun z : ℂ ↦ z - r) '' ball 0 r := by
    rintro ⟨z, hz, hz0⟩
    have hlt := mem_ball_zero_iff.mp hz
    rw [sub_eq_zero.mp hz0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hlt
    exact lt_irrefl r hlt
  have hlog₂_diff : DifferentiableOn ℂ (logDeriv fun z : ℂ ↦ z - r) (ball 0 r) :=
    ((differentiableOn_id.sub (differentiableOn_const (r : ℂ))).inv fun z hz h0 ↦
      hg₂_ne ⟨z, hz, h0⟩).congr fun _ _ ↦ by simp [logDeriv_apply]
  have hex₂ : Complex.IsExactOn (logDeriv fun z : ℂ ↦ z - r) (ball 0 r) :=
    Contour.isExactOn_of_starConvex isOpen_ball ((convex_ball (0 : ℂ) r).starConvex
      (mem_ball_self hr)) hlog₂_diff
  obtain ⟨ℓ₂, hℓ₂, heq₂⟩ :=
    Contour.exists_differentiableOn_eqOn_exp_comp_of_isExactOn isOpen_ball hg₂_diff hg₂_ne hex₂
  refine ⟨W₁ ∩ ball 0 r, fun z ↦ ℓ₁ z + ℓ₂ z, hW₁.inter isOpen_ball,
    subset_inter hKW₁ (subset_filledHull.trans hball),
    (hℓ₁.mono inter_subset_left).add (hℓ₂.mono inter_subset_right), fun z hz ↦ ?_⟩
  have hzr : z - (r : ℂ) ≠ 0 := fun h0 ↦ hg₂_ne ⟨z, hz.2, h0⟩
  have h1 : Complex.exp (ℓ₁ z) = (z - b) / (z - r) := heq₁ hz.1
  have h2 : Complex.exp (ℓ₂ z) = z - r := heq₂ hz.2
  change Complex.exp (ℓ₁ z + ℓ₂ z) = z - b
  rw [Complex.exp_add, h1, h2, div_mul_cancel₀ _ hzr]

/-- Scalar Runge approximation on a compact set `K` filled in `Ω`, assembled from discretized
Cauchy–Pompeiu on a thickening inside `V` and simple-fraction Runge approximation. -/
private theorem exists_differentiableOn_norm_sub_lt_of_isFilledIn {K Ω V : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hV : IsOpen V) (hKV : K ⊆ V) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨M, hM⟩ := hK.cthickening.exists_bound_of_continuousOn (hf.mono hδV).continuousOn
  set B : ℝ := max M 0 + 1
  have hB_pos : 0 < B := by positivity
  have hfB : ∀ z ∈ thickening δ K, ‖f z‖ ≤ B := fun z hz ↦
    (hM z (thickening_subset_cthickening δ K hz)).trans
      ((le_max_left M 0).trans (lt_add_one _).le)
  obtain ⟨N, ζ, c, hζ, hdisc⟩ := hK.exists_norm_sub_sum_mul_sub_inv_smul_le
    isOpen_thickening (self_subset_thickening hδ K) (div_pos (half_pos hε) hB_pos)
  let a : Fin N → ℂ := fun i ↦ c i * f (ζ i)
  have ha_pos : ∀ i, 0 < ε / 2 / ((N : ℝ) + 1) / (‖a i‖ + 1) := fun i ↦ by positivity
  choose g hg hg_approx using fun i : Fin N ↦
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ i).2 (ha_pos i)
  refine ⟨fun z ↦ ∑ i, a i * g i z,
    DifferentiableOn.fun_sum fun i _ ↦ (hg i).const_mul (a i), fun z hz ↦ ?_⟩
  have h1 : ‖f z - ∑ i, a i * (z - ζ i)⁻¹‖ ≤ ε / 2 := by
    have hd := hdisc f B (hf.mono ((thickening_subset_cthickening δ K).trans hδV)) hfB z hz
    rw [div_mul_cancel₀ _ hB_pos.ne'] at hd
    have heq : (∑ i, a i * (z - ζ i)⁻¹) = ∑ i, (c i * (z - ζ i)⁻¹) • f (ζ i) :=
      Finset.sum_congr rfl fun i _ ↦ by simp [a, smul_eq_mul, mul_right_comm]
    rwa [heq]
  have h2 : ‖(∑ i, a i * (z - ζ i)⁻¹) - ∑ i, a i * g i z‖ < ε / 2 := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i, (a i * (z - ζ i)⁻¹ - a i * g i z)‖
        ≤ ∑ i : Fin N, ‖a i * ((z - ζ i)⁻¹ - g i z)‖ := by
          simpa [mul_sub] using norm_sum_le Finset.univ
            (fun i ↦ a i * (z - ζ i)⁻¹ - a i * g i z)
      _ ≤ ∑ _i : Fin N, ε / 2 / ((N : ℝ) + 1) := Finset.sum_le_sum fun i _ ↦ by
          rw [norm_mul]
          exact (mul_le_mul (lt_add_one ‖a i‖).le (hg_approx i z hz).le (norm_nonneg _)
            (by positivity)).trans_eq (mul_div_cancel₀ _ (by positivity))
      _ = (N : ℝ) * (ε / 2 / ((N : ℝ) + 1)) := by simp
      _ < ((N : ℝ) + 1) * (ε / 2 / ((N : ℝ) + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one (N : ℝ)) (by positivity)
      _ = ε / 2 := mul_div_cancel₀ _ (by positivity)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt
    ((add_lt_add_of_le_of_lt h1 h2).trans_eq (add_halves ε))

/-- One linear factor `z ↦ z - b` with `b ∉ K` splits near `K` into a factor holomorphic and
nowhere zero on `Ω` times an exponential of a function holomorphic near `K`. -/
private theorem exists_linear_factor_decomposition {K Ω : Set ℂ} (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {b : ℂ} (hb : b ∉ K) :
    ∃ (h : ℂ → ℂ) (W : Set ℂ) (ℓ : ℂ → ℂ),
      DifferentiableOn ℂ h Ω ∧ (∀ z ∈ Ω, h z ≠ 0) ∧
      IsOpen W ∧ K ⊆ W ∧ DifferentiableOn ℂ ℓ W ∧
      ∀ z ∈ W, z - b = h z * Complex.exp (ℓ z) := by
  by_cases hbH : b ∈ filledHull K
  · have hnot := (isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
      hK.isClosed hΩ hKΩ).mp hfill b ⟨hbH, hb⟩
    obtain ⟨a, ha_comp, haΩ⟩ := not_subset.mp hnot
    obtain ⟨W₁, ℓ, hW₁, hKW₁, haW₁, -, hℓ, heq⟩ :=
      exists_isOpen_differentiableOn_eqOn_exp_comp_sub_div_sub hK.isClosed ha_comp
    refine ⟨fun z ↦ z - a, W₁, ℓ,
      differentiableOn_id.sub (differentiableOn_const a),
      fun z hz ↦ sub_ne_zero.mpr fun h ↦ haΩ (h ▸ hz),
      hW₁, hKW₁, hℓ, fun z hz ↦ ?_⟩
    have hza : z - a ≠ 0 := sub_ne_zero.mpr fun h ↦ haW₁ (h ▸ hz)
    have hexp : Complex.exp (ℓ z) = (z - b) / (z - a) := heq hz
    rw [hexp, mul_div_cancel₀ _ hza]
  · obtain ⟨W, ℓ, hW, hKW, hℓ, heq⟩ :=
      exists_isOpen_differentiableOn_eqOn_exp_comp_sub_of_notMem_filledHull hK hbH
    refine ⟨fun _ ↦ 1, W, ℓ, differentiableOn_const 1, fun _ _ ↦ one_ne_zero,
      hW, hKW, hℓ, fun z hz ↦ ?_⟩
    have hexp : Complex.exp (ℓ z) = z - b := heq hz
    rw [one_mul, hexp]

/-- A finite list of linear factors `∏_{b ∈ bs} (z - b)` with every `b ∉ K` splits near `K` into a
factor holomorphic and nowhere zero on `Ω` times an exponential of a function holomorphic near
`K`. -/
private theorem exists_list_linear_factor_decomposition {K Ω : Set ℂ} (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∀ (bs : List ℂ), (∀ b ∈ bs, b ∉ K) →
      ∃ (h : ℂ → ℂ) (W : Set ℂ) (ℓ : ℂ → ℂ),
        DifferentiableOn ℂ h Ω ∧ (∀ z ∈ Ω, h z ≠ 0) ∧
        IsOpen W ∧ K ⊆ W ∧ DifferentiableOn ℂ ℓ W ∧
        ∀ z ∈ W, (bs.map fun b ↦ z - b).prod = h z * Complex.exp (ℓ z)
  | [], _ =>
    ⟨fun _ ↦ 1, univ, fun _ ↦ 0, differentiableOn_const 1, fun _ _ ↦ one_ne_zero,
      isOpen_univ, subset_univ K, differentiableOn_const 0, fun _ _ ↦ by simp⟩
  | b :: bs, hbs => by
    obtain ⟨h₁, W₁, ℓ₁, hh₁, hne₁, hW₁, hKW₁, hℓ₁, heq₁⟩ :=
      exists_linear_factor_decomposition hfill hΩ hK hKΩ (hbs b List.mem_cons_self)
    obtain ⟨h₂, W₂, ℓ₂, hh₂, hne₂, hW₂, hKW₂, hℓ₂, heq₂⟩ :=
      exists_list_linear_factor_decomposition hfill hΩ hK hKΩ bs
        (fun x hx ↦ hbs x (List.mem_cons_of_mem b hx))
    refine ⟨fun z ↦ h₁ z * h₂ z, W₁ ∩ W₂, fun z ↦ ℓ₁ z + ℓ₂ z,
      hh₁.mul hh₂, fun z hz ↦ mul_ne_zero (hne₁ z hz) (hne₂ z hz),
      hW₁.inter hW₂, subset_inter hKW₁ hKW₂,
      (hℓ₁.mono inter_subset_left).add (hℓ₂.mono inter_subset_right), fun z hz ↦ ?_⟩
    simp only [List.map_cons, List.prod_cons, heq₁ z hz.1, heq₂ z hz.2, Complex.exp_add]
    ring

/-- **Rational sum as a polynomial quotient.** Away from the poles `ζ i`, the simple-fraction sum
`∑ i, d i * (z - ζ i)⁻¹` equals `P.eval z / Q.eval z` for explicit polynomials `P, Q : ℂ[X]`. -/
private theorem sum_mul_sub_inv_eq_eval_div {N : ℕ} (ζ d : Fin N → ℂ) {z : ℂ}
    (hz : ∀ i, z ≠ ζ i) :
    let Q : ℂ[X] := ∏ i : Fin N, (X - C (ζ i))
    let P : ℂ[X] := ∑ i : Fin N, C (d i) * ∏ j ∈ Finset.univ.erase i, (X - C (ζ j))
    (∑ i, d i * (z - ζ i)⁻¹) = P.eval z / Q.eval z := by
  intro Q P
  have hzi : ∀ i, z - ζ i ≠ 0 := fun i ↦ sub_ne_zero.mpr (hz i)
  have hQ : Q.eval z = ∏ i : Fin N, (z - ζ i) := by simp [Q, Polynomial.eval_prod]
  have hP : P.eval z = ∑ i : Fin N, d i * ∏ j ∈ Finset.univ.erase i, (z - ζ j) := by
    trans ∑ i : Fin N, (C (d i) * ∏ j ∈ Finset.univ.erase i, (X - C (ζ j))).eval z
    · exact map_sum (Polynomial.evalRingHom z) _ _
    · simp [Polynomial.eval_prod]
  rw [hP, hQ, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have herase : (∏ j : Fin N, (z - ζ j)) =
      (z - ζ i) * ∏ j ∈ Finset.univ.erase i, (z - ζ j) :=
    (Finset.mul_prod_erase Finset.univ (fun j ↦ z - ζ j) (Finset.mem_univ i)).symm
  have hprod_ne : (∏ j ∈ Finset.univ.erase i, (z - ζ j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ hzi j
  rw [herase, mul_div_mul_right _ _ hprod_ne, div_eq_mul_inv]

/-- Any nonvanishing simple-fraction sum on a nonempty compact `K` factors on an open neighborhood
of `K` as `H * exp ℓ`, where `H` is holomorphic and nowhere zero on `Ω`. -/
private theorem exists_sum_inv_factorization {K Ω : Set ℂ} (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hKne : K.Nonempty)
    {N : ℕ} (ζ d : Fin N → ℂ) (hζ : ∀ i, ζ i ∉ K)
    (hr_ne : ∀ z ∈ K, (∑ i, d i * (z - ζ i)⁻¹) ≠ 0) :
    ∃ (H : ℂ → ℂ) (W : Set ℂ) (ℓ : ℂ → ℂ),
      DifferentiableOn ℂ H Ω ∧ (∀ z ∈ Ω, H z ≠ 0) ∧
      IsOpen W ∧ K ⊆ W ∧ DifferentiableOn ℂ ℓ W ∧
      ∀ z ∈ W, (∑ i, d i * (z - ζ i)⁻¹) = H z * Complex.exp (ℓ z) := by
  set Q : ℂ[X] := ∏ i : Fin N, (X - C (ζ i))
  set P : ℂ[X] := ∑ i : Fin N, C (d i) * ∏ j ∈ Finset.univ.erase i, (X - C (ζ j))
  obtain ⟨z₀, hz₀⟩ := hKne
  have hP0 : P ≠ 0 := fun h ↦ hr_ne z₀ hz₀ <| by
    rw [sum_mul_sub_inv_eq_eval_div ζ d fun i hi ↦ hζ i (hi ▸ hz₀)]
    simp [P, h]
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hroots_notMem : ∀ b ∈ P.roots.toList, b ∉ K := fun b hb hbK ↦ hr_ne b hbK <| by
    have hb_root : P.eval b = 0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toList.mp hb)
    rw [sum_mul_sub_inv_eq_eval_div ζ d fun i hi ↦ hζ i (hi ▸ hbK)]
    simp [P, hb_root]
  have hpoles_notMem : ∀ b ∈ List.ofFn ζ, b ∉ K := fun b hb ↦ by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact hζ i
  obtain ⟨h₁, W₁, ℓ₁, hh₁, hne₁, hW₁, hKW₁, hℓ₁, heq₁⟩ :=
    exists_list_linear_factor_decomposition hfill hΩ hK hKΩ P.roots.toList hroots_notMem
  obtain ⟨h₂, W₂, ℓ₂, hh₂, hne₂, hW₂, hKW₂, hℓ₂, heq₂⟩ :=
    exists_list_linear_factor_decomposition hfill hΩ hK hKΩ (List.ofFn ζ) hpoles_notMem
  refine ⟨fun z ↦ h₁ z / h₂ z, W₁ ∩ (W₂ ∩ (range ζ)ᶜ),
    fun z ↦ Complex.log P.leadingCoeff + ℓ₁ z - ℓ₂ z,
    hh₁.div hh₂ hne₂, fun z hz ↦ div_ne_zero (hne₁ z hz) (hne₂ z hz),
    hW₁.inter (hW₂.inter (finite_range ζ).isClosed.isOpen_compl),
    subset_inter hKW₁ (subset_inter hKW₂ fun z hz ⟨i, hi⟩ ↦ hζ i (hi ▸ hz)),
    ((differentiableOn_const _).add (hℓ₁.mono inter_subset_left)).sub
      (hℓ₂.mono (inter_subset_right.trans inter_subset_left)),
    fun z ⟨hz₁, hz₂, hzS⟩ ↦ ?_⟩
  have hzi : ∀ i, z ≠ ζ i := fun i h ↦ hzS ⟨i, h.symm⟩
  have hP_eval : P.eval z = P.leadingCoeff * h₁ z * Complex.exp (ℓ₁ z) := by
    rw [(IsAlgClosed.splits P).eval_eq_prod_roots, ← Multiset.coe_toList P.roots,
      Multiset.map_coe, Multiset.prod_coe, heq₁ z hz₁, mul_assoc]
  have hQ_eval : Q.eval z = h₂ z * Complex.exp (ℓ₂ z) := by
    rw [show Q.eval z = ((List.ofFn ζ).map fun b ↦ z - b).prod by
      simp [Q, Polynomial.eval_prod, List.prod_ofFn], heq₂ z hz₂]
  have hQ_ne : Q.eval z ≠ 0 := by
    rw [show Q.eval z = ∏ i : Fin N, (z - ζ i) by simp [Q, Polynomial.eval_prod]]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ sub_ne_zero.mpr (hzi i)
  have hh₂_ne : h₂ z ≠ 0 := left_ne_zero_of_mul (hQ_eval ▸ hQ_ne)
  rw [sum_mul_sub_inv_eq_eval_div ζ d hzi]
  dsimp only
  rw [hP_eval, hQ_eval, sub_eq_add_neg, Complex.exp_add, Complex.exp_add,
    Complex.exp_log hlc, Complex.exp_neg]
  field_simp [hh₂_ne, Complex.exp_ne_zero (ℓ₂ z)]

/-- Discretizing Cauchy–Pompeiu approximates a function `u` holomorphic near nonempty compact `K`
and nonvanishing on `K` by a simple-fraction sum without poles or zeros on `K`. -/
private theorem exists_sum_mul_sub_inv_ne_zero_norm_sub_lt {K U : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : K ⊆ U)
    {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u U) (hne : ∀ z ∈ K, u z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ d : Fin N → ℂ), (∀ i, ζ i ∉ K) ∧
      (∀ z ∈ K, (∑ i, d i * (z - ζ i)⁻¹) ≠ 0) ∧
      ∀ z ∈ K, ‖u z - ∑ i, d i * (z - ζ i)⁻¹‖ < ε := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨M₀, hM₀⟩ := hK.cthickening.exists_bound_of_continuousOn (hu.mono hδ₀U).continuousOn
  set B : ℝ := max M₀ 0 + 1
  have hB_pos : 0 < B := by positivity
  have huB : ∀ z ∈ thickening δ₀ K, ‖u z‖ ≤ B := fun z hz ↦
    (hM₀ z (thickening_subset_cthickening δ₀ K hz)).trans
      ((le_max_left M₀ 0).trans (lt_add_one _).le)
  obtain ⟨z_min, hz_min, hmin⟩ := hK.exists_isMinOn hKne (hu.continuousOn.mono hKU).norm
  set η : ℝ := ‖u z_min‖
  have hη_pos : 0 < η := norm_pos_iff.mpr (hne z_min hz_min)
  set τ : ℝ := min ε (η / 2)
  have hτ_pos : 0 < τ := lt_min hε (half_pos hη_pos)
  obtain ⟨N, ζ, c, hζ, hdisc⟩ := hK.exists_norm_sub_sum_mul_sub_inv_smul_le
    isOpen_thickening (self_subset_thickening hδ₀ K) (div_pos (half_pos hτ_pos) hB_pos)
  let d : Fin N → ℂ := fun i ↦ c i * u (ζ i)
  have hur_lt : ∀ z ∈ K, ‖u z - ∑ i, d i * (z - ζ i)⁻¹‖ < τ := fun z hz ↦ by
    have hd := hdisc u B (hu.mono ((thickening_subset_cthickening δ₀ K).trans hδ₀U)) huB z hz
    rw [div_mul_cancel₀ _ hB_pos.ne'] at hd
    have heq : (∑ i, (c i * (z - ζ i)⁻¹) • u (ζ i)) = ∑ i, d i * (z - ζ i)⁻¹ :=
      Finset.sum_congr rfl fun i _ ↦ by simp [d, smul_eq_mul, mul_right_comm]
    rw [heq] at hd
    exact hd.trans_lt (half_lt_self hτ_pos)
  refine ⟨N, ζ, d, fun i ↦ (hζ i).2, fun z hz hr0 ↦ ?_,
    fun z hz ↦ (hur_lt z hz).trans_le (min_le_left _ _)⟩
  have hle : η ≤ ‖u z‖ := isMinOn_iff.mp hmin z hz
  have hlt : ‖u z‖ < η / 2 := by
    have h1 := hur_lt z hz
    rw [hr0, sub_zero] at h1
    exact h1.trans_le (min_le_right _ _)
  linarith

/-- **Zero-free Runge approximation** (Rainer, Proposition 15.2). If a compact set `K ⊆ Ω` is
filled in an open set `Ω ⊆ ℂ`, and `u` is holomorphic on an open neighborhood `U` of `K` and
nonvanishing on `K`, then for every `ε > 0` there exists `g` holomorphic and nowhere zero on `Ω`
satisfying `‖u z - g z‖ < ε` for all `z ∈ K`. -/
theorem IsFilledIn.exists_differentiableOn_ne_zero_norm_sub_lt {K Ω U : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hU : IsOpen U) (hKU : K ⊆ U) {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u U)
    (hne : ∀ z ∈ K, u z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ Ω, g z ≠ 0) ∧
      ∀ z ∈ K, ‖u z - g z‖ < ε := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ _ ↦ one_ne_zero, by simp⟩
  obtain ⟨N, ζ, d, hζ, hr_ne, hur_lt⟩ :=
    exists_sum_mul_sub_inv_ne_zero_norm_sub_lt hK hKne hU hKU hu hne (half_pos hε)
  obtain ⟨H, W, ℓ, hH, hH_ne, hW, hKW, hℓ, hr_fac⟩ :=
    exists_sum_inv_factorization hfill hΩ hK hKΩ hKne ζ d hζ hr_ne
  set r : ℂ → ℂ := fun z ↦ ∑ i, d i * (z - ζ i)⁻¹
  have hur : ∀ z ∈ K, ‖u z - r z‖ < ε / 2 := hur_lt
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hu.continuousOn.mono hKU)
  set C : ℝ := max M₀ 0 + ε / 2 + 1
  have hC_pos : 0 < C := by positivity
  have hr_le : ∀ z ∈ K, ‖r z‖ ≤ C := fun z hz ↦ by
    have hu_le : ‖u z‖ ≤ max M₀ 0 := (hM₀ z hz).trans (le_max_left M₀ 0)
    have hr_u : ‖r z‖ ≤ ‖u z‖ + ‖u z - r z‖ := by
      simpa [sub_sub_cancel] using norm_sub_le (u z) (u z - r z)
    exact (hr_u.trans (add_le_add hu_le (hur z hz).le)).trans (lt_add_one _).le
  set δ : ℝ := min 1 ((ε / 2) / (2 * C))
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨L, hL, hL_approx⟩ :=
    exists_differentiableOn_norm_sub_lt_of_isFilledIn hfill hΩ hK hKΩ hW hKW hℓ hδ_pos
  refine ⟨fun z ↦ H z * Complex.exp (L z),
    hH.mul hL.cexp, fun z hz ↦ mul_ne_zero (hH_ne z hz) (Complex.exp_ne_zero (L z)), fun z hz ↦ ?_⟩
  have hdiff_lt : ‖L z - ℓ z‖ < δ := by
    rw [norm_sub_rev]
    exact hL_approx z hz
  have hexp_bound : ‖Complex.exp (L z - ℓ z) - 1‖ ≤ 2 * ‖L z - ℓ z‖ :=
    Complex.norm_exp_sub_one_le (hdiff_lt.le.trans (min_le_left _ _))
  have hrG : ‖r z - H z * Complex.exp (L z)‖ < ε / 2 := by
    have hr_z : r z = H z * Complex.exp (ℓ z) := hr_fac z (hKW hz)
    have hrew : r z - H z * Complex.exp (L z) = r z * (1 - Complex.exp (L z - ℓ z)) := by
      rw [hr_z, mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
      ring_nf
    rw [hrew, norm_mul, norm_sub_rev (1 : ℂ)]
    calc ‖r z‖ * ‖Complex.exp (L z - ℓ z) - 1‖
        ≤ C * (2 * ‖L z - ℓ z‖) :=
          mul_le_mul (hr_le z hz) hexp_bound (norm_nonneg _) hC_pos.le
      _ < C * (2 * δ) := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hdiff_lt two_pos) hC_pos
      _ ≤ C * (2 * ((ε / 2) / (2 * C))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le_two) hC_pos.le
      _ = ε / 2 := by field_simp
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt
    ((add_lt_add (hur z hz) hrG).trans_eq (add_halves ε))

end TauCeti
