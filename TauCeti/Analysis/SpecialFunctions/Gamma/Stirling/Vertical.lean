/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Stirling's formula on vertical strips

For every compact interval `[a, b]`,
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`, that is along `cocompact ℝ`
([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9), with the remainder of
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)). The statement is additive in `log ‖Γ‖`, so it adds
up over finite products of shifted Gamma factors.

The proof is the sector form `TauCeti.abs_log_norm_Gamma_sub_stirling_le`
(`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Basic.lean`) at the angle `π / 4`.
Once `|σ| ≤ |t|` the point `σ + i t` has `|arg| ≤ 3π/4`, and the sector main term
`(σ - 1/2) log ‖s‖ - t arg s - σ` differs from the vertical one by two terms of size `O(1 / |t|)`:

* `0 ≤ log ‖s‖ - log |t| ≤ |σ| / |t|`, since `|t| ≤ ‖s‖ ≤ |t| + |σ|`;
* for `t > 0`, `π / 2 - arg s = arctan (σ / t)` (`Complex.arg_eq_pi_div_two_sub_arctan_of_im_pos`)
  and `|arctan x - x| ≤ |x| ^ 3` (`Real.abs_arctan_sub_self_le`), so `t (π / 2 - arg s) - σ` is at
  most `σ ^ 2 / t` in absolute value.

Negative `t` reduces to positive `t` by `Γ(conj s) = conj (Γ s)`. Exponentiating the asymptotic and
combining with compactness on bounded-height rectangles yields global exponential upper bounds for
`‖Γ(s)‖` away from the real axis, for `‖Γ(z + i t)‖` along pole-free vertical lines, and for the
entire reciprocal `‖(Γ s)⁻¹‖` across the whole strip `a ≤ Re s ≤ b`.

## Main declarations

* `TauCeti.abs_log_norm_Gamma_vertical_sub_le`: the explicit bound
  `(2 / (1 - cos (π / 4)) ^ 3 + |σ - 1/2| |σ| + σ ^ 2) / |t|` at every `s = σ + i t` with `t ≠ 0`
  and `|σ| ≤ |t|`.
* `TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le`: one constant and one threshold for all `s`
  with `Re s ∈ [a, b]`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_sub`: the uniform `O(1 / |t|)` form in `(σ, t)` along
  `𝓟 (Icc a b) ×ˢ cocompact ℝ`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_strip_sub`: the same as a function of `s : ℂ`, along
  `cocompact ℂ` restricted to the strip `Re s ∈ [a, b]`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_line_sub`: the same on a single vertical line, along
  `cocompact ℝ`.
* `TauCeti.exists_norm_Gamma_vertical_strip_le`:
  `‖Γ(s)‖ ≤ C |Im s| ^ (Re s - 1/2) exp(-π |Im s| / 2)` for `Re s ∈ [a, b]` and `1 ≤ |Im s|`.
* `TauCeti.exists_norm_inv_Gamma_vertical_strip_le`:
  `‖(Γ s)⁻¹‖ ≤ C (1 + |Im s|) ^ (1/2 - Re s) exp(π |Im s| / 2)` for all `s` with `Re s ∈ [a, b]`.
* `TauCeti.exists_norm_Gamma_add_mul_I_le` and `TauCeti.exists_norm_Gamma_vertical_line_le`:
  `‖Γ(z + i t)‖ ≤ C (1 + |t|) ^ (Re z - 1/2) exp(-π |t| / 2)` for all `t : ℝ` when `Re z` avoids
  the nonpositive integers.
-/

public section

open Complex Real Filter Set Asymptotics

namespace TauCeti

/-- The modulus term: `0 ≤ log ‖σ + i t‖ - log t ≤ |σ| / t` for `t > 0`, since
`t ≤ ‖σ + i t‖ ≤ t + |σ|`. -/
private theorem abs_log_norm_sub_log_im_le {σ t : ℝ} (ht : 0 < t) :
    |Real.log ‖(σ : ℂ) + t * I‖ - Real.log t| ≤ |σ| / t := by
  set s : ℂ := σ + t * I
  have hts : t ≤ ‖s‖ := by simpa [s, abs_of_pos ht] using abs_im_le_norm s
  have hst : ‖s‖ ≤ |σ| + t := by simpa [s, abs_of_pos ht] using norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log ht hts)),
    ← Real.log_div (ht.trans_le hts).ne' ht.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos (ht.trans_le hts) ht)).trans ?_
  rw [div_sub_one ht.ne']
  exact div_le_div_of_nonneg_right (by linarith) ht.le

/-- The angle term: `|t (arctan (σ / t) - σ / t)| ≤ σ ^ 2 / t` for `|σ| ≤ t`, from the cubic
bound `|arctan x - x| ≤ |x| ^ 3` at `|x| ≤ 1`. -/
private theorem abs_mul_arctan_div_sub_div_le {σ t : ℝ} (ht : 0 < t) (hσt : |σ| ≤ t) :
    |t * (Real.arctan (σ / t) - σ / t)| ≤ σ ^ 2 / t := by
  have hx1 : |σ / t| ≤ 1 := by
    rw [abs_div, abs_of_pos ht]
    exact div_le_one_of_le₀ hσt ht.le
  rw [abs_mul, abs_of_pos ht]
  calc t * |Real.arctan (σ / t) - σ / t| ≤ t * |σ / t| ^ 2 :=
        mul_le_mul_of_nonneg_left ((Real.abs_arctan_sub_self_le _).trans
          (pow_le_pow_of_le_one (abs_nonneg _) hx1 (by norm_num))) ht.le
    _ = σ ^ 2 / t := by
      rw [sq_abs]
      field_simp

/-- The explicit vertical bound in the upper half-plane. -/
private theorem abs_log_norm_Gamma_vertical_sub_le_of_pos {σ t : ℝ} (ht : 0 < t)
    (hσt : |σ| ≤ t) :
    |Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2)| ≤
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |σ - 1 / 2| * |σ| + σ ^ 2) / |t| := by
  set s : ℂ := σ + t * I
  set K : ℝ := 2 / (1 - Real.cos (π / 4)) ^ 3
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  rw [abs_of_pos ht]
  have hs0 : s ≠ 0 := fun h ↦ ht.ne' (by rw [← him, h, zero_im])
  have hts : t ≤ ‖s‖ := by simpa [him, abs_of_pos ht] using abs_im_le_norm s
  have hK : 0 ≤ K := div_nonneg zero_le_two (pow_nonneg (sub_nonneg.2 (Real.cos_le_one _)) 3)
  -- the angle: `arg s = π / 2 - arctan (σ / t)` with `|arctan (σ / t)| ≤ π / 4`
  have harg := arg_eq_pi_div_two_sub_arctan_of_im_pos (w := s) (by rwa [him])
  rw [hre, him] at harg
  have hatan_le : |Real.arctan (σ / t)| ≤ π / 4 := by
    have hx1 : |σ / t| ≤ 1 := by
      rw [abs_div, abs_of_pos ht]
      exact div_le_one_of_le₀ hσt ht.le
    rw [← Real.arctan_one, abs_le, ← Real.arctan_neg]
    exact ⟨Real.arctan_mono (abs_le.1 hx1).1, Real.arctan_mono (abs_le.1 hx1).2⟩
  have hsector : |s.arg| ≤ π - π / 4 := by
    rw [harg, abs_le]
    obtain ⟨h1, h2⟩ := abs_le.1 hatan_le
    constructor <;> linarith [Real.pi_pos]
  -- Stirling on the sector `|arg s| ≤ 3π/4`
  have hS := abs_log_norm_Gamma_sub_stirling_le (by positivity) (by linarith [Real.pi_pos])
    hsector hs0
  rw [hre, him, ← div_div] at hS
  have hS' : K / ‖s‖ ≤ K / t := div_le_div_of_nonneg_left hK ht hts
  -- the modulus term
  have hA : |(σ - 1 / 2) * (Real.log ‖s‖ - Real.log t)| ≤ |σ - 1 / 2| * |σ| / t := by
    rw [abs_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_log_norm_sub_log_im_le ht) (abs_nonneg _)
  have hsplit : Real.log ‖Complex.Gamma s‖ -
      ((σ - 1 / 2) * Real.log t - π * t / 2 + Real.log (2 * π) / 2) =
      (Real.log ‖Complex.Gamma s‖ - ((σ - 1 / 2) * Real.log ‖s‖ - t * s.arg - σ +
        Real.log (2 * π) / 2)) + (σ - 1 / 2) * (Real.log ‖s‖ - Real.log t) +
      t * (Real.arctan (σ / t) - σ / t) := by
    have hσ : t * (σ / t) = σ := by field_simp
    rw [harg]
    linear_combination hσ
  rw [hsplit, add_div, add_div]
  refine (abs_add_three _ _ _).trans ?_
  linarith [hS.trans hS', abs_mul_arctan_div_sub_div_le ht hσt]

/-- The explicit vertical bound in the coordinates `s = σ + i t`. -/
private theorem abs_log_norm_Gamma_vertical_sub_le_of_ne_zero {σ t : ℝ} (ht : t ≠ 0)
    (hσt : |σ| ≤ |t|) :
    |Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2)| ≤
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |σ - 1 / 2| * |σ| + σ ^ 2) / |t| := by
  rcases ht.lt_or_gt with ht | ht
  · have hpos := abs_log_norm_Gamma_vertical_sub_le_of_pos (σ := σ) (neg_pos.2 ht)
      (by rwa [abs_of_neg ht] at hσt)
    have hconj : (σ : ℂ) + t * I = (starRingEnd ℂ) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [abs_neg] at hpos
    rwa [hconj, Complex.Gamma_conj, Complex.norm_conj]
  · exact abs_log_norm_Gamma_vertical_sub_le_of_pos ht (by rwa [abs_of_pos ht] at hσt)

/-- **Stirling's formula on vertical strips**, explicit form: for `s = σ + i t` with `t ≠ 0` and
`|σ| ≤ |t|`,
`|log ‖Γ(s)‖ - ((σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2)| ≤
(2 / (1 - cos (π / 4)) ^ 3 + |σ - 1/2| |σ| + σ ^ 2) / |t|`. -/
theorem abs_log_norm_Gamma_vertical_sub_le {s : ℂ} (hs : s.im ≠ 0) (hre : |s.re| ≤ |s.im|) :
    |Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2)| ≤
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |s.re - 1 / 2| * |s.re| + s.re ^ 2) / |s.im| := by
  simpa only [re_add_im] using abs_log_norm_Gamma_vertical_sub_le_of_ne_zero hs hre

/-- Stirling's formula on vertical strips, with one constant and one threshold for the whole
strip `a ≤ Re s ≤ b`: for `s = σ + i t` with `σ ∈ [a, b]` and `T ≤ |t|`,
`|log ‖Γ(s)‖ - ((σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2)| ≤ C / |t|`. -/
theorem exists_abs_log_norm_Gamma_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gamma s‖ -
          ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2)| ≤
        C / |s.im| := by
  set M := max |a| |b|
  refine ⟨2 / (1 - Real.cos (π / 4)) ^ 3 + (M + 1 / 2) * M + M ^ 2, M + 1,
    fun s hs ht ↦ ?_⟩
  have hσM : |s.re| ≤ M := abs_le_max_abs_abs hs.1 hs.2
  have hM : 0 ≤ M := (abs_nonneg _).trans hσM
  have ht0 : 0 < |s.im| := by linarith
  refine (abs_log_norm_Gamma_vertical_sub_le (abs_pos.1 ht0) (by linarith)).trans ?_
  refine div_le_div_of_nonneg_right ?_ ht0.le
  have h1 : |s.re - 1 / 2| ≤ M + 1 / 2 := by
    obtain ⟨hl, hu⟩ := abs_le.1 hσM
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |s.re - 1 / 2| * |s.re| ≤ (M + 1 / 2) * M :=
    mul_le_mul h1 hσM (abs_nonneg _) (by linarith)
  have h3 : s.re ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hσM 2
  linarith

/-- **Stirling's formula on vertical strips** ([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9)):
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` uniformly for
`σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Complex.Gamma (p.1 + p.2 * I)‖ -
        ((p.1 - 1 / 2) * Real.log |p.2| - π * |p.2| / 2 + Real.log (2 * π) / 2))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ t : ℝ in cocompact ℝ, T ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hT] with p hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  simpa using h (p.1 + p.2 * I) (by simpa using hp.1) (by simpa using hp.2)

/-- **Stirling's formula on vertical strips** as a function of `s = σ + i t`:
`log ‖Γ(s)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` as `s → ∞` in the strip
`a ≤ Re s ≤ b`. -/
theorem isBigO_log_norm_Gamma_vertical_strip_sub (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ s : ℂ in cocompact ℂ, T + max |a| |b| ≤ ‖s‖ :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop _
  filter_upwards [hT.filter_mono inf_le_left,
    (eventually_principal.2 fun _ hs ↦ hs).filter_mono inf_le_right] with s hs hre
  have hM : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs hre.1 hre.2
  have hnorm := norm_le_abs_re_add_abs_im s
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  exact h s hre (by linarith)

/-- Stirling's formula on a single vertical line `Re s = σ`:
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical_line_sub (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  (isBigO_log_norm_Gamma_vertical_sub σ σ).comp_tendsto
    ((tendsto_principal.2 (Eventually.of_forall fun _ ↦ left_mem_Icc.2 le_rfl)).prodMk tendsto_id)

/-- For `1 ≤ u` and any real exponent `r`, `u ^ r ≤ 2 ^ |r| * (1 + u) ^ r`. -/
private theorem rpow_le_two_rpow_abs_mul_one_add_rpow {u : ℝ} (hu : 1 ≤ u) (r : ℝ) :
    u ^ r ≤ 2 ^ |r| * (1 + u) ^ r := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have h1u : 0 < 1 + u := by linarith
  have hrat : (u / (1 + u)) ^ r ≤ 2 ^ |r| :=
    Real.rpow_le_rpow_abs (div_pos hu0 h1u) ((div_le_one h1u).2 (by linarith) |>.trans one_le_two)
      (by rw [inv_div, div_le_iff₀ hu0]; linarith) r
  calc u ^ r = (u / (1 + u)) ^ r * (1 + u) ^ r := by
        rw [Real.div_rpow hu0.le h1u.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos h1u r).ne']
    _ ≤ 2 ^ |r| * (1 + u) ^ r := mul_le_mul_of_nonneg_right hrat (Real.rpow_nonneg h1u.le r)

/-- Shifting `t` by `c` changes `(1 + |t|) ^ r` by at most `(1 + |c|) ^ |r|`. -/
private theorem one_add_abs_add_rpow_le (c t r : ℝ) :
    (1 + |c + t|) ^ r ≤ (1 + |c|) ^ |r| * (1 + |t|) ^ r := by
  have hct : 0 < 1 + |c + t| := by positivity
  have ht : 0 < 1 + |t| := by positivity
  have hup : (1 + |c + t|) / (1 + |t|) ≤ 1 + |c| := by
    rw [div_le_iff₀ ht]
    simpa [Real.norm_eq_abs] using one_add_norm_add_le c t
  have hlow : ((1 + |c + t|) / (1 + |t|))⁻¹ ≤ 1 + |c| := by
    rw [inv_div, div_le_iff₀ hct]
    simpa [Real.norm_eq_abs] using one_add_norm_add_le (-c) (c + t)
  have hrat := Real.rpow_le_rpow_abs (div_pos hct ht) hup hlow r
  calc (1 + |c + t|) ^ r = ((1 + |c + t|) / (1 + |t|)) ^ r * (1 + |t|) ^ r := by
        rw [Real.div_rpow hct.le ht.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos ht r).ne']
    _ ≤ (1 + |c|) ^ |r| * (1 + |t|) ^ r :=
      mul_le_mul_of_nonneg_right hrat (Real.rpow_nonneg ht.le r)

/-- Exponential upper bound for the Gamma function on a vertical strip away from the real axis:
for every `a, b : ℝ`, there is `C > 0` such that
`‖Γ(s)‖ ≤ C * |Im s| ^ (Re s - 1/2) * exp (-π |Im s| / 2)` whenever `Re s ∈ [a, b]` and
`1 ≤ |Im s|`. -/
theorem exists_norm_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b → 1 ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C * |s.im| ^ (s.re - 1 / 2) * Real.exp (-π * |s.im| / 2) := by
  obtain ⟨C₀, T₀, hS⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set T : ℝ := max T₀ 1
  set C₁ : ℝ := max C₀ 0
  set K : Set ℂ := Icc a b ×ℂ (Icc (-T) (-1) ∪ Icc 1 T)
  have hK : IsCompact K := isCompact_Icc.reProdIm (isCompact_Icc.union isCompact_Icc)
  have hK_im : ∀ z ∈ K, 1 ≤ |z.im| := by
    rintro z ⟨-, hz | hz⟩
    · rw [abs_of_neg (by linarith [hz.2] : z.im < 0)]; linarith [hz.2]
    · exact hz.1.trans (le_abs_self _)
  set f : ℂ → ℝ := fun z ↦
    ‖Complex.Gamma z‖ / (|z.im| ^ (z.re - 1 / 2) * Real.exp (-π * |z.im| / 2))
  have hf : ContinuousOn f K := fun z hz ↦ by
    have him1 : 1 ≤ |z.im| := hK_im z hz
    have him_pos : 0 < |z.im| := zero_lt_one.trans_le him1
    have him0 : z.im ≠ 0 := abs_pos.1 him_pos
    have hzne : ∀ m : ℕ, z ≠ -m := fun m hm ↦ him0 (by simp [hm])
    have hΓ : ContinuousAt (fun w : ℂ ↦ ‖Complex.Gamma w‖) z :=
      (Complex.differentiableAt_Gamma z hzne).continuousAt.norm
    have hrpow : ContinuousAt (fun w : ℂ ↦ |w.im| ^ (w.re - 1 / 2)) z :=
      (continuous_im.abs.continuousAt).rpow (by fun_prop) (Or.inl him_pos.ne')
    have hexp : ContinuousAt (fun w : ℂ ↦ Real.exp (-π * |w.im| / 2)) z := by fun_prop
    exact (hΓ.div (hrpow.mul hexp)
      (mul_ne_zero (Real.rpow_pos_of_pos him_pos _).ne' (Real.exp_pos _).ne')).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf
  set C_tail : ℝ := Real.exp (Real.log (2 * π) / 2 + C₁)
  refine ⟨max (max M 1) C_tail, by positivity, fun s hs him ↦ ?_⟩
  have him_pos : 0 < |s.im| := zero_lt_one.trans_le him
  have hden : 0 < |s.im| ^ (s.re - 1 / 2) * Real.exp (-π * |s.im| / 2) := by positivity
  rcases le_or_gt |s.im| T with hle | hgt
  · have hsK : s ∈ K := by
      refine ⟨hs, ?_⟩
      rcases le_or_gt 0 s.im with h0 | h0
      · rw [abs_of_nonneg h0] at him hle
        exact Or.inr ⟨him, hle⟩
      · rw [abs_of_neg h0] at him hle
        exact Or.inl ⟨by linarith, by linarith⟩
    have hfs : f s ≤ max (max M 1) C_tail :=
      ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM s hsK)).trans
        ((le_max_left M 1).trans (le_max_left _ _))
    rw [mul_assoc]
    exact (div_le_iff₀ hden).1 hfs
  · have hs_ne : ∀ m : ℕ, s ≠ -m := fun m hm ↦ (abs_pos.1 him_pos) (by simp [hm])
    have hΓpos : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero hs_ne)
    have hlog := (abs_le.1 (hS s hs ((le_max_left _ _).trans hgt.le))).2
    have herr : C₀ / |s.im| ≤ C₁ :=
      (div_le_div_of_nonneg_right (le_max_left _ _) him_pos.le).trans
        (div_le_self (le_max_right _ _) him)
    have hlog' : Real.log ‖Complex.Gamma s‖ ≤
        (Real.log (2 * π) / 2 + C₁) + (s.re - 1 / 2) * Real.log |s.im| + (-π * |s.im| / 2) := by
      linarith
    have hexp := Real.exp_le_exp.2 hlog'
    rw [Real.exp_log hΓpos, Real.exp_add, Real.exp_add, mul_comm (s.re - 1 / 2),
      ← Real.rpow_def_of_pos him_pos] at hexp
    exact hexp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity))

/-- Exponential upper bound for the entire function `s ↦ (Γ s)⁻¹` on any vertical strip
`a ≤ Re s ≤ b`, valid across all imaginary parts without pole restrictions:
`‖(Γ s)⁻¹‖ ≤ C * (1 + |Im s|) ^ (1/2 - Re s) * exp (π |Im s| / 2)`. -/
theorem exists_norm_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, T₀, hS⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set T : ℝ := max T₀ 1
  set C₁ : ℝ := max C₀ 0
  set B : ℝ := max |a| |b| + 1 / 2 with hB_def
  set K : Set ℂ := Icc a b ×ℂ Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  set g : ℂ → ℝ := fun z ↦
    ‖(Complex.Gamma z)⁻¹‖ / ((1 + |z.im|) ^ (1 / 2 - z.re) * Real.exp (π * |z.im| / 2))
  have hg : Continuous g := by
    have hnum : Continuous fun z : ℂ ↦ ‖(Complex.Gamma z)⁻¹‖ :=
      Complex.differentiable_one_div_Gamma.continuous.norm
    have hrpow : Continuous fun z : ℂ ↦ (1 + |z.im|) ^ (1 / 2 - z.re) :=
      (continuous_const.add continuous_im.abs).rpow (by fun_prop)
        fun z ↦ Or.inl (by positivity : 1 + |z.im| ≠ 0)
    exact hnum.div (hrpow.mul (by fun_prop)) fun z ↦ by positivity
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  set C_tail : ℝ := Real.exp (C₁ - Real.log (2 * π) / 2) * 2 ^ B
  refine ⟨max (max M 1) C_tail, by positivity, fun s hs ↦ ?_⟩
  have hden : 0 < (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by positivity
  rcases le_or_gt |s.im| T with hle | hgt
  · have hsK : s ∈ K := ⟨hs, abs_le.1 hle⟩
    have hgs : g s ≤ max (max M 1) C_tail :=
      ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM s hsK)).trans
        ((le_max_left M 1).trans (le_max_left _ _))
    rw [mul_assoc]
    exact (div_le_iff₀ hden).1 hgs
  · have him1 : 1 ≤ |s.im| := (le_max_right _ _).trans hgt.le
    have him_pos : 0 < |s.im| := zero_lt_one.trans_le him1
    have hs_ne : ∀ m : ℕ, s ≠ -m := fun m hm ↦ (abs_pos.1 him_pos) (by simp [hm])
    have hlog := (abs_le.1 (hS s hs ((le_max_left _ _).trans hgt.le))).1
    have herr : C₀ / |s.im| ≤ C₁ :=
      (div_le_div_of_nonneg_right (le_max_left _ _) him_pos.le).trans
        (div_le_self (le_max_right _ _) him1)
    have hlog_inv : Real.log ‖(Complex.Gamma s)⁻¹‖ ≤
        (C₁ - Real.log (2 * π) / 2) + (1 / 2 - s.re) * Real.log |s.im| + π * |s.im| / 2 := by
      rw [norm_inv, Real.log_inv]
      linarith
    have hexp := Real.exp_le_exp.2 hlog_inv
    rw [Real.exp_log (norm_pos_iff.2 (inv_ne_zero (Complex.Gamma_ne_zero hs_ne))),
      Real.exp_add, Real.exp_add, mul_comm (1 / 2 - s.re),
      ← Real.rpow_def_of_pos him_pos] at hexp
    have hB : |1 / 2 - s.re| ≤ B := by
      obtain ⟨hl, hu⟩ := abs_le.1 (abs_le_max_abs_abs hs.1 hs.2)
      exact abs_le.2 ⟨by linarith [hB_def], by linarith [hB_def]⟩
    have hrpow : |s.im| ^ (1 / 2 - s.re) ≤ 2 ^ B * (1 + |s.im|) ^ (1 / 2 - s.re) :=
      (rpow_le_two_rpow_abs_mul_one_add_rpow him1 _).trans
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two hB)
          (by positivity))
    calc ‖(Complex.Gamma s)⁻¹‖
        ≤ Real.exp (C₁ - Real.log (2 * π) / 2) * (2 ^ B * (1 + |s.im|) ^ (1 / 2 - s.re)) *
            Real.exp (π * |s.im| / 2) :=
          hexp.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow (by positivity)) (by positivity))
      _ = C_tail * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by ring
      _ ≤ max (max M 1) C_tail * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)

/-- Exponential upper bound for `t ↦ Γ(z + i t)` along a vertical line avoiding the poles of `Γ`:
`‖Γ(z + i t)‖ ≤ C * (1 + |t|) ^ (Re z - 1/2) * exp (-π |t| / 2)` for all `t : ℝ`. -/
theorem exists_norm_Gamma_add_mul_I_le {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) :
    ∃ C > 0, ∀ t : ℝ,
      ‖Complex.Gamma (z + t * I)‖ ≤ C * (1 + |t|) ^ (z.re - 1 / 2) * Real.exp (-π * |t| / 2) := by
  obtain ⟨C₁, hC₁, hstrip⟩ := exists_norm_Gamma_vertical_strip_le z.re z.re
  set K : Set ℝ := Icc (-z.im - 1) (-z.im + 1)
  set f : ℝ → ℝ := fun t ↦
    ‖Complex.Gamma (z + t * I)‖ / ((1 + |t|) ^ (z.re - 1 / 2) * Real.exp (-π * |t| / 2))
  have hf : Continuous f := by
    have hΓ : Continuous fun t : ℝ ↦ ‖Complex.Gamma (z + t * I)‖ :=
      (continuous_iff_continuousAt.2 fun t ↦
        (Complex.differentiableAt_Gamma _ fun m hm ↦
          hz m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)).norm
    have hrpow : Continuous fun t : ℝ ↦ (1 + |t|) ^ (z.re - 1 / 2) :=
      (continuous_const.add continuous_abs).rpow continuous_const
        fun t ↦ Or.inl (by positivity : 1 + |t| ≠ 0)
    exact hΓ.div (hrpow.mul (by fun_prop)) fun t ↦ by positivity
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := K) hf.continuousOn
  set C_tail : ℝ :=
    C₁ * 2 ^ |z.re - 1 / 2| * (1 + |z.im|) ^ |z.re - 1 / 2| * Real.exp (π * |z.im| / 2)
  refine ⟨max (max M 1) C_tail, by positivity, fun t ↦ ?_⟩
  have hden : 0 < (1 + |t|) ^ (z.re - 1 / 2) * Real.exp (-π * |t| / 2) := by positivity
  rcases le_or_gt |z.im + t| 1 with hle | hgt
  · have htK : t ∈ K := by
      obtain ⟨hl, hu⟩ := abs_le.1 hle
      exact ⟨by linarith, by linarith⟩
    have hft : f t ≤ max (max M 1) C_tail :=
      ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM t htK)).trans
        ((le_max_left M 1).trans (le_max_left _ _))
    rw [mul_assoc]
    exact (div_le_iff₀ hden).1 hft
  · have hs : ‖Complex.Gamma (z + t * I)‖ ≤
        C₁ * |z.im + t| ^ (z.re - 1 / 2) * Real.exp (-π * |z.im + t| / 2) := by
      simpa using hstrip (z + t * I) (by simp) (by simpa using hgt.le)
    have hrpow : |z.im + t| ^ (z.re - 1 / 2) ≤
        2 ^ |z.re - 1 / 2| * ((1 + |z.im|) ^ |z.re - 1 / 2| * (1 + |t|) ^ (z.re - 1 / 2)) :=
      (rpow_le_two_rpow_abs_mul_one_add_rpow hgt.le _).trans
        (mul_le_mul_of_nonneg_left (one_add_abs_add_rpow_le z.im t _) (by positivity))
    have hexp : Real.exp (-π * |z.im + t| / 2) ≤
        Real.exp (π * |z.im| / 2) * Real.exp (-π * |t| / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have htri : |t| - |z.im| ≤ |z.im + t| := by
        have := abs_add_le (-z.im) (z.im + t)
        rw [abs_neg, neg_add_cancel_left] at this
        linarith
      nlinarith [Real.pi_pos]
    calc ‖Complex.Gamma (z + t * I)‖
        ≤ C₁ * (2 ^ |z.re - 1 / 2| *
            ((1 + |z.im|) ^ |z.re - 1 / 2| * (1 + |t|) ^ (z.re - 1 / 2))) *
            (Real.exp (π * |z.im| / 2) * Real.exp (-π * |t| / 2)) :=
          hs.trans (mul_le_mul
            (mul_le_mul_of_nonneg_left hrpow hC₁.le) hexp (by positivity) (by positivity))
      _ = C_tail * (1 + |t|) ^ (z.re - 1 / 2) * Real.exp (-π * |t| / 2) := by ring
      _ ≤ max (max M 1) C_tail * (1 + |t|) ^ (z.re - 1 / 2) * Real.exp (-π * |t| / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)

/-- Exponential upper bound for `t ↦ Γ(σ + i t)` along a vertical line `Re s = σ` avoiding the
poles of `Γ`. -/
theorem exists_norm_Gamma_vertical_line_le {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    ∃ C > 0, ∀ t : ℝ,
      ‖Complex.Gamma (σ + t * I)‖ ≤ C * (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2) := by
  simpa using exists_norm_Gamma_add_mul_I_le (z := σ) (by simpa using hσ)

end TauCeti
