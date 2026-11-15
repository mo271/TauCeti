/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Data.Nat.GCD
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Shift
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Sign

/-!
# Siegel's theorem for quadratic Dirichlet characters

For every `ε > 0`, there exists a constant `c > 0` such that every nonprincipal quadratic Dirichlet
character `χ` modulo `q` satisfies `c * q ^ (-ε) ≤ Re L(1, χ)`.

Writing `F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` for the four-factor product attached to two
characters `χ` mod `M` and `ψ` mod `N`, the proof follows Goldfeld's contour-shifting method for
primitive characters, combined with the zero-free versus exceptional-zero dichotomy on `(1 - δ, 1)`
for `δ = min (1 / 4) (ε / 20)` and the deleted-Euler-factor comparison
`DirichletCharacter.exists_norm_LFunction_changeLevel_le_rpow`:

1. Dividing Goldfeld's three-factor residue bound
   (`DirichletCharacter.exists_pos_mul_rpow_le_re_LFunction_one_mul`) by the elementary upper bound
   `Re L(1, ρ) ≤ 1 + log L ≤ 2 (1 - β)⁻¹ L ^ (1 - β)` for `ρ = ψ` and `ρ = χ.mul ψ` yields the
   two-character lower bound `c (1 - β)³ (M N)^{-10(1 - β)} ≤ Re L(1, χ)` whenever `Re F(β) ≤ 0` on
   `[3 / 4, 1)`.
2. In particular, if `L(β, ψ) = 0` for `β ∈ [3 / 4, 1)` and `χ.mul ψ ≠ 1`, then `F(β) = 0` gives
   `c (1 - β)³ (M N)^{-10(1 - β)} ≤ Re L(1, χ)`.
3. If `L(·, ρ)` has no zero on `(1 - δ, 1)` for any primitive nonprincipal quadratic character `ρ`,
   pairing any primitive `χ` of conductor `q` with the Legendre character modulo `3` (or modulo `5`
   when `q = 3`) produces a nonprincipal product whose primitive character also has nonvanishing
   `L`-function on `(1 - δ, 1)`, so `F(1 - δ) ≤ 0`
   (`DirichletCharacter.pair_nonpos_of_forall_ne_zero`) and `Re L(1, χ) ≫ δ³ q^{-10 δ}`.
4. Otherwise, fixing one primitive nonprincipal quadratic character `ψ` with a real zero
   `L(β, ψ) = 0` for `β ∈ (1 - δ, 1)` bounds `Re L(1, χ)` for every primitive `χ ≠ ψ` via step 2,
   while `χ = ψ` is a single positive value `Re L(1, ψ) > 0`. Passing from an arbitrary nonprincipal
   quadratic character modulo `q` to its primitive character costs at most `O_ε(q ^ (ε / 2))`,
   giving the general theorem across all moduli. The resulting constant `c` depends on the
   hypothetical zero `β` and is therefore ineffective.

## Main results

* `DirichletCharacter.exists_pos_mul_rpow_le_re_LFunction_one_of_re_nonpos`: two-character `L(1, χ)`
  lower bound from `Re (ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)) ≤ 0`.
* `DirichletCharacter.exists_pos_mul_rpow_le_re_LFunction_one_of_eq_zero`: two-character `L(1, χ)`
  lower bound from a real zero `L(β, ψ) = 0` in `[3 / 4, 1)`.
* `DirichletCharacter.exists_pos_mul_rpow_le_re_LFunction_one_of_forall_ne_zero`: effective uniform
  `c δ³ q^{-10 δ} ≤ Re L(1, χ)` bound assuming a real zero-free interval `(1 - δ, 1)`.
* `DirichletCharacter.quadratic_LFunction_siegel`: Siegel's theorem `c * q ^ (-ε) ≤ Re L(1, χ)`
  across all nonprincipal quadratic characters modulo `q`.

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Complex
open scoped ComplexOrder

namespace DirichletCharacter

private lemma re_LFunction_one_le_two_mul_inv_mul_rpow {L : ℕ} [NeZero L]
    {ρ : DirichletCharacter ℂ L} (hρ : ρ ≠ 1) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (ρ.LFunction 1).re ≤ 2 * δ⁻¹ * (L : ℝ) ^ δ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hL0 : 0 ≤ (L : ℝ) := by linarith
  have hrpow1 : 1 ≤ (L : ℝ) ^ δ := Real.one_le_rpow hL1 hδ₀.le
  have h1 : 1 ≤ δ⁻¹ * (L : ℝ) ^ δ := by
    rw [inv_mul_eq_div, one_le_div hδ₀]
    exact hδ₁.trans hrpow1
  have hlog : Real.log L ≤ δ⁻¹ * (L : ℝ) ^ δ := by
    rw [inv_mul_eq_div]
    exact Real.log_le_rpow_div hL0 hδ₀
  exact (Complex.re_le_norm _).trans <|
    (ρ.norm_LFunction_one_le_one_add_log hρ).trans (by linarith)

/-- **Two-character lower bound for `Re L(1, χ)` from nonpositivity at `β`.** There exists an
absolute constant `c > 0` such that for nonprincipal quadratic characters `χ` mod `M` and `ψ` mod
`N` with `χ.mul ψ ≠ 1` and `3 / 4 ≤ β < 1`, if
`Re (ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)) ≤ 0`, then
`c (1 - β)³ (M N)^{-10(1 - β)} ≤ Re L(1, χ)`. -/
theorem exists_pos_mul_rpow_le_re_LFunction_one_of_re_nonpos :
    ∃ c : ℝ, 0 < c ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      ∀ {β : ℝ}, 3 / 4 ≤ β → β < 1 →
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0 →
      c * (1 - β) ^ 3 * ((M : ℝ) * N) ^ (-10 * (1 - β)) ≤ (χ.LFunction 1).re := by
  obtain ⟨c, hc, hgold⟩ := exists_pos_mul_rpow_le_re_LFunction_one_mul
  refine ⟨c / 4, by positivity, fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ₀ hβ₁ hFβ ↦ ?_⟩
  set δ : ℝ := 1 - β
  have hδ₀ : 0 < δ := by dsimp [δ]; linarith
  have hδ₁ : δ ≤ 1 := by dsimp [δ]; linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hMN0 : 0 < (M : ℝ) * N :=
    mul_pos (Nat.cast_pos.mpr (NeZero.pos M)) (Nat.cast_pos.mpr (NeZero.pos N))
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  have hψ_up : (ψ.LFunction 1).re ≤ 2 * δ⁻¹ * ((M : ℝ) * N) ^ δ :=
    (re_LFunction_one_le_two_mul_inv_mul_rpow hψ hδ₀ hδ₁).trans <| mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (le_mul_of_one_le_left (by positivity) hM1) hδ₀.le)
      (by positivity)
  have hχψ_up : ((χ.mul ψ).LFunction 1).re ≤ 2 * δ⁻¹ * ((M : ℝ) * N) ^ δ :=
    (re_LFunction_one_le_two_mul_inv_mul_rpow hχψ hδ₀ hδ₁).trans <| mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hlcm hδ₀.le) (by positivity)
  have hχ_pos : 0 < (χ.LFunction 1).re := (Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ)).1
  have hχψ_pos : 0 < ((χ.mul ψ).LFunction 1).re :=
    (Complex.pos_iff.mp (LFunction_apply_one_pos (isQuadratic_mul hχq hψq) hχψ)).1
  have hprod_le : (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re ≤
      (χ.LFunction 1).re * (4 * δ⁻¹ ^ 2 * ((M : ℝ) * N) ^ (2 * δ)) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hχ_pos.le
    calc (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re
        ≤ (2 * δ⁻¹ * ((M : ℝ) * N) ^ δ) * (2 * δ⁻¹ * ((M : ℝ) * N) ^ δ) :=
          mul_le_mul hψ_up hχψ_up hχψ_pos.le (by positivity)
      _ = 4 * δ⁻¹ ^ 2 * (((M : ℝ) * N) ^ δ * ((M : ℝ) * N) ^ δ) := by ring
      _ = 4 * δ⁻¹ ^ 2 * ((M : ℝ) * N) ^ (2 * δ) := by rw [← Real.rpow_add hMN0, two_mul]
  have hbase := (hgold χ ψ hχq hψq hχ hψ hχψ hβ₀ hβ₁ hFβ).trans hprod_le
  have hfac_nn : 0 ≤ (1 / 4) * δ ^ 2 * ((M : ℝ) * N) ^ (-2 * δ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbase hfac_nn
  have hzero_exp : 2 * δ + -2 * δ = 0 := by ring
  calc c / 4 * δ ^ 3 * ((M : ℝ) * N) ^ (-10 * δ)
      = c * δ * (((M : ℝ) * N) ^ (-8 * δ) * ((M : ℝ) * N) ^ (-2 * δ)) * ((1 / 4) * δ ^ 2) := by
        rw [← Real.rpow_add hMN0]; ring_nf
    _ = c * δ * ((M : ℝ) * N) ^ (-8 * δ) * ((1 / 4) * δ ^ 2 * ((M : ℝ) * N) ^ (-2 * δ)) := by ring
    _ ≤ (χ.LFunction 1).re * (4 * δ⁻¹ ^ 2 * ((M : ℝ) * N) ^ (2 * δ)) *
          ((1 / 4) * δ ^ 2 * ((M : ℝ) * N) ^ (-2 * δ)) := hmul
    _ = (χ.LFunction 1).re * ((δ⁻¹ * δ) ^ 2 *
          (((M : ℝ) * N) ^ (2 * δ) * ((M : ℝ) * N) ^ (-2 * δ))) := by ring
    _ = (χ.LFunction 1).re := by
        rw [inv_mul_cancel₀ hδ₀.ne', ← Real.rpow_add hMN0, hzero_exp, Real.rpow_zero]
        ring

/-- **Two-character lower bound from an exceptional real zero.** If the `L`-function `L(·, ψ)` of a
nonprincipal quadratic character `ψ` mod `N` vanishes at `β ∈ [3 / 4, 1)`, then every nonprincipal
quadratic character `χ` mod `M` with `χ.mul ψ ≠ 1` satisfies
`c (1 - β)³ (M N)^{-10(1 - β)} ≤ Re L(1, χ)`. -/
theorem exists_pos_mul_rpow_le_re_LFunction_one_of_eq_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      ∀ {β : ℝ}, 3 / 4 ≤ β → β < 1 → ψ.LFunction β = 0 →
      c * (1 - β) ^ 3 * ((M : ℝ) * N) ^ (-10 * (1 - β)) ≤ (χ.LFunction 1).re := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_rpow_le_re_LFunction_one_of_re_nonpos
  exact ⟨c, hc, fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ₀ hβ₁ hβ0 ↦
    hbound χ ψ hχq hψq hχ hψ hχψ hβ₀ hβ₁ (by simp [hβ0])⟩

private lemma mul_LFunction_ne_zero_of_forall_primitive {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic) (hχψ : χ.mul ψ ≠ 1) {β : ℝ} (hβ₀ : 0 < β)
    (hzero : ∀ (q : ℕ) [NeZero q] (ρ : DirichletCharacter ℂ q),
      ρ.IsPrimitive → ρ.IsQuadratic → ρ ≠ 1 → ∀ σ ∈ Set.Ioo β 1, ρ.LFunction σ ≠ 0) :
    ∀ σ ∈ Set.Ioo β 1, (χ.mul ψ).LFunction σ ≠ 0 := by
  have : NeZero (χ.mul ψ).conductor := ⟨(χ.mul ψ).conductor_ne_zero⟩
  have hρp : (χ.mul ψ).primitiveCharacter.IsPrimitive := (χ.mul ψ).primitiveCharacter_isPrimitive
  have hρq : (χ.mul ψ).primitiveCharacter.IsQuadratic :=
    (isQuadratic_primitiveCharacter_iff (χ.mul ψ)).mpr (isQuadratic_mul hχq hψq)
  have hρ1 : (χ.mul ψ).primitiveCharacter ≠ 1 :=
    (primitiveCharacter_eq_one_iff (χ.mul ψ)).not.mpr hχψ
  intro σ hσ
  have hσ0 : 0 < (σ : ℂ).re := by simp; linarith [hσ.1]
  have hσ1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.2.ne
  rw [← changeLevel_primitiveCharacter (χ.mul ψ), Ne,
    LFunction_changeLevel_eq_zero_iff (χ.mul ψ).primitiveCharacter
      (χ.mul ψ).conductor_dvd_level hσ0 (Or.inr hσ1)]
  exact hzero (χ.mul ψ).conductor (χ.mul ψ).primitiveCharacter hρp hρq hρ1 σ hσ

/-- **Effective uniform `L(1, χ)` lower bound under a real zero-free interval.** There is an
absolute constant `c > 0` such that whenever `0 < δ ≤ 1 / 4` and `L(·, ρ)` has no zero on
`(1 - δ, 1)` for any primitive nonprincipal quadratic character `ρ`, every primitive nonprincipal
quadratic character `χ` modulo `q` satisfies `c * δ ^ 3 * q ^ (-10 * δ) ≤ Re L(1, χ)`. -/
theorem exists_pos_mul_rpow_le_re_LFunction_one_of_forall_ne_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 4 →
      (∀ (q : ℕ) [NeZero q] (ρ : DirichletCharacter ℂ q),
        ρ.IsPrimitive → ρ.IsQuadratic → ρ ≠ 1 →
        ∀ σ ∈ Set.Ioo (1 - δ) 1, ρ.LFunction σ ≠ 0) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
        c * δ ^ 3 * (q : ℝ) ^ (-10 * δ) ≤ (χ.LFunction 1).re := by
  obtain ⟨c₀, hc₀, hbound⟩ := exists_pos_mul_rpow_le_re_LFunction_one_of_re_nonpos
  refine ⟨c₀ * (5 : ℝ) ^ (-(5 / 2 : ℝ)), by positivity,
    fun {δ} hδ₀ hδ₁ hzero q _ χ hχp hχq hχ1 ↦ ?_⟩
  have hpair (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≤ 5) (hqp : q ≠ p) :
      c₀ * (5 : ℝ) ^ (-(5 / 2 : ℝ)) * δ ^ 3 * (q : ℝ) ^ (-10 * δ) ≤ (χ.LFunction 1).re := by
    have hp : p.Prime := Fact.out
    have : NeZero p := ⟨hp.ne_zero⟩
    set ψ : DirichletCharacter ℂ p := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
    have hψp : ψ.IsPrimitive := isPrimitive_quadraticChar_ringHomComp (by simp) hp2
    have hψq : ψ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
    have hψ1 : ψ ≠ 1 := quadraticChar_ringHomComp_ne_one (by simp) hp2
    have hχψ : χ.mul ψ ≠ 1 := fun h1 ↦ by
      rcases (hχp.mul_eq_one_iff hψp hψq).mp h1 with ⟨heq, -⟩
      exact hqp heq
    have hβ₀ : 0 < 1 - δ := by linarith
    have hsign := pair_nonpos_of_forall_ne_zero hχq hψq hχ1 hψ1 hχψ hβ₀ (by linarith) fun σ hσ ↦
      ⟨hzero q χ hχp hχq hχ1 σ hσ, hzero p ψ hψp hψq hψ1 σ hσ,
        mul_LFunction_ne_zero_of_forall_primitive hχq hψq hχψ hβ₀ hzero σ hσ⟩
    have hre0 := (Complex.nonpos_iff.mp hsign).1
    have hmain := hbound χ ψ hχq hψq hχ1 hψ1 hχψ (β := 1 - δ) (by linarith) (by linarith) hre0
    have hsub : 1 - (1 - δ) = δ := by ring
    rw [hsub] at hmain
    have hp_rpow : (5 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (p : ℝ) ^ (-10 * δ) :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)).trans <|
        Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hp.pos) (by exact_mod_cast hp5) (by linarith)
    calc c₀ * (5 : ℝ) ^ (-(5 / 2 : ℝ)) * δ ^ 3 * (q : ℝ) ^ (-10 * δ)
        ≤ c₀ * (p : ℝ) ^ (-10 * δ) * δ ^ 3 * (q : ℝ) ^ (-10 * δ) := by gcongr
      _ = c₀ * δ ^ 3 * ((q : ℝ) * p) ^ (-10 * δ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ (χ.LFunction 1).re := hmain
  by_cases hq3 : q = 3
  · have : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact hpair 5 (by decide) (by decide) (by omega)
  · have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact hpair 3 (by decide) (by decide) hq3

private theorem quadratic_LFunction_siegel_primitive {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
        c * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  set δ : ℝ := min (1 / 4) (ε / 10)
  have hδ₀ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ ≤ 1 / 4 := min_le_left _ _
  have hδε : 10 * δ ≤ ε := by have := min_le_right (1 / 4) (ε / 10); linarith
  by_cases hzero : ∀ (M : ℕ) [NeZero M] (ρ : DirichletCharacter ℂ M),
      ρ.IsPrimitive → ρ.IsQuadratic → ρ ≠ 1 → ∀ σ ∈ Set.Ioo (1 - δ) 1, ρ.LFunction σ ≠ 0
  · obtain ⟨c₀, hc₀, hbound⟩ := exists_pos_mul_rpow_le_re_LFunction_one_of_forall_ne_zero
    refine ⟨c₀ * δ ^ 3, by positivity, fun q _ χ hχp hχq hχ1 ↦ ?_⟩
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
      (by positivity)).trans (hbound hδ₀ hδ₁ hzero q χ hχp hχq hχ1)
  · push Not at hzero
    obtain ⟨M, hM, ψ, hψp, hψq, hψ1, β, hβ, hψβ⟩ := hzero
    have : NeZero M := hM
    obtain ⟨c₀, hc₀, hex⟩ := exists_pos_mul_rpow_le_re_LFunction_one_of_eq_zero
    have h1β : 0 < 1 - β := by linarith [hβ.2]
    have hM0 : 0 < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
    set c₁ : ℝ := c₀ * (1 - β) ^ 3 * (M : ℝ) ^ (-10 * (1 - β))
    have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
    have hψ1_pos : 0 < (ψ.LFunction 1).re :=
      (Complex.pos_iff.mp (LFunction_apply_one_pos hψq hψ1)).1
    set c : ℝ := min c₁ ((ψ.LFunction 1).re * (M : ℝ) ^ ε)
    refine ⟨c, lt_min hc₁ (by positivity), fun q _ χ hχp hχq hχ1 ↦ ?_⟩
    by_cases hmul : χ.mul ψ = 1
    · rcases (hχp.mul_eq_one_iff hψp hψq).mp hmul with ⟨rfl, rfl⟩
      calc c * (q : ℝ) ^ (-ε)
          ≤ ((χ.LFunction 1).re * (q : ℝ) ^ ε) * (q : ℝ) ^ (-ε) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = (χ.LFunction 1).re * ((q : ℝ) ^ ε * (q : ℝ) ^ (-ε)) := by ring
        _ = (χ.LFunction 1).re := by
            rw [← Real.rpow_add hM0, add_neg_cancel, Real.rpow_zero, mul_one]
    · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      calc c * (q : ℝ) ^ (-ε)
          ≤ c₁ * (q : ℝ) ^ (-10 * (1 - β)) :=
            mul_le_mul (min_le_left _ _)
              (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith [hβ.1])) (by positivity) hc₁.le
        _ = c₀ * (1 - β) ^ 3 * ((q : ℝ) * M) ^ (-10 * (1 - β)) := by
            dsimp [c₁]; rw [Real.mul_rpow (by positivity) hM0.le]; ring
        _ ≤ (χ.LFunction 1).re :=
            hex χ ψ hχq hψq hχ1 hψ1 hmul (by linarith [hβ.1]) hβ.2 hψβ

/-- **Siegel's theorem.** For every `ε > 0`, there is an (ineffective) constant `c > 0` such that
`c * q ^ (-ε) ≤ Re L(1, χ)` for every nonprincipal quadratic Dirichlet character `χ` modulo `q`. -/
theorem quadratic_LFunction_siegel {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsQuadratic → χ ≠ 1 →
        c * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  obtain ⟨c₁, hc₁, hprim⟩ := quadratic_LFunction_siegel_primitive (half_pos hε)
  obtain ⟨A, hA, hchg⟩ := exists_norm_LFunction_changeLevel_le_rpow (δ := 1) (ε := ε / 2)
    one_pos (half_pos hε)
  refine ⟨c₁ / A, div_pos hc₁ hA, fun q _ χ hχq hχ1 ↦ ?_⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ₀q : χ.primitiveCharacter.IsQuadratic :=
    (isQuadratic_primitiveCharacter_iff χ).mpr hχq
  have hχ₀1 : χ.primitiveCharacter ≠ 1 :=
    (primitiveCharacter_eq_one_iff χ).not.mpr hχ1
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hcond_le : (χ.conductor : ℝ) ≤ q :=
    Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
  have hlow₀ : c₁ * (q : ℝ) ^ (-(ε / 2)) ≤ ‖χ.primitiveCharacter.LFunction 1‖ :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr (NeZero.pos χ.conductor)) hcond_le
        (by linarith))
      hc₁.le).trans <|
      (hprim χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hχ₀q hχ₀1).trans
        (Complex.re_le_norm _)
  have hcmp : ‖χ.primitiveCharacter.LFunction 1‖ ≤ A * (q : ℝ) ^ (ε / 2) * ‖χ.LFunction 1‖ := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      (hchg χ.conductor q χ.primitiveCharacter χ.conductor_dvd_level 1 (by simp) (Or.inl hχ₀1)).2
  rw [norm_LFunction_one_eq_re hχq hχ1] at hcmp
  have hexp : -ε = -(ε / 2) - ε / 2 := by ring
  rw [hexp, sub_eq_add_neg, Real.rpow_add hq0]
  have hdiv : c₁ / A * ((q : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2))) =
      (c₁ * (q : ℝ) ^ (-(ε / 2))) / (A * (q : ℝ) ^ (ε / 2)) := by
    rw [Real.rpow_neg hq0.le]
    field_simp [hA.ne']
  rw [hdiv, div_le_iff₀ (by positivity)]
  linarith [hlow₀, hcmp]

end DirichletCharacter
