/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.Data.Nat.GCD
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.ShiftedSum
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Sign

/-!
# Siegel's theorem for primitive quadratic Dirichlet L-functions

For any `ε > 0`, Siegel's theorem provides a single constant `c_ε > 0` such that every
nonprincipal primitive quadratic Dirichlet character `χ` modulo `q` satisfies
`c_ε q ^ (-ε) ≤ Re L(1, χ)`.

The proof follows Goldfeld's contour-shift method applied to the four-factor product
`F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)`
(`DirichletCharacter.exists_le_LFunction_one_mul_mul_of_pair_nonpos`):
whenever `χ` and `ψ` are nonprincipal quadratic characters of levels `M` and `q` with
`χ.mul ψ ≠ 1` and `F(β) ≤ 0` at `β ∈ [1 / 2, 1)` satisfying `1 - β ≤ ε / 16`, Goldfeld's lower
bound on `L(1, χ) L(1, ψ) L(1, χ.mul ψ)` combined with the logarithmic upper bound
`‖L(1, ρ)‖ ≤ 1 + log L` (`DirichletCharacter.norm_LFunction_one_le_one_add_log`) on the auxiliary
factors `χ` and `χ.mul ψ` yields `c(ε, β, M) q ^ (-ε) ≤ Re L(1, ψ)`.

Setting `β₀ = 1 - min (ε / 16) (1 / 2)`, a classical case split completes the proof:
* If no nonprincipal primitive quadratic L-function vanishes on `(β₀, 1)`, then `F(β₀) ≤ 0` for
  every pair with `χ.mul ψ ≠ 1` (`DirichletCharacter.pair_nonpos_of_forall_ne_zero`); pairing `ψ`
  with the Legendre character modulo `3` (or modulo `5` when `q = 3`) yields an explicit uniform
  bound (`DirichletCharacter.exists_le_LFunction_one_re_of_forall_ne_zero`).
* If some nonprincipal primitive quadratic character `χ` modulo `M` has a real zero
  `β ∈ (β₀, 1)`, then `F(β) = 0` identically for every other primitive quadratic character `ψ`,
  giving a lower bound for all `ψ` distinct from `χ`
  (`DirichletCharacter.exists_le_LFunction_one_re_of_LFunction_eq_zero_of_ne`), and absorbing the
  single positive value `L(1, χ)` covers the whole family
  (`DirichletCharacter.exists_le_LFunction_one_re_of_LFunction_eq_zero`).

Because the choice between these two cases is nonconstructive, the resulting constant `c_ε` in
`TauCeti.quadratic_LFunction_siegel` is ineffective.

## Main results

* `DirichletCharacter.exists_le_LFunction_one_re_of_forall_ne_zero`: uniform `q ^ (-ε)` lower bound
  under a common real zero-free interval `(β, 1)`.
* `DirichletCharacter.exists_le_LFunction_one_re_of_LFunction_eq_zero_of_ne` and
  `DirichletCharacter.exists_le_LFunction_one_re_of_LFunction_eq_zero`: two-character comparison
  from a real zero `L(β, χ) = 0` close to `1`.
* `TauCeti.quadratic_LFunction_siegel`: Siegel's theorem for all nonprincipal primitive quadratic
  Dirichlet characters.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Complex
open scoped ComplexOrder

namespace DirichletCharacter

/-- Power-saving upper bound on `Re L(1, ρ)` from `‖L(1, ρ)‖ ≤ 1 + log L`, valid for imprimitive
characters as well as primitive ones. -/
private theorem LFunction_one_re_le_mul_rpow {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L)
    (hρ : ρ ≠ 1) {η : ℝ} (hη : 0 < η) :
    (ρ.LFunction 1).re ≤ (1 + 1 / η) * (L : ℝ) ^ η := by
  have hL1 : 1 ≤ (L : ℝ) := Nat.one_le_cast.mpr NeZero.one_le
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ η := Real.one_le_rpow hL1 hη.le
  have hlog : Real.log L ≤ (L : ℝ) ^ η / η := Real.log_natCast_le_rpow_div L hη
  calc
    (ρ.LFunction 1).re ≤ ‖ρ.LFunction 1‖ := Complex.re_le_norm _
    _ ≤ 1 + Real.log L := ρ.norm_LFunction_one_le_one_add_log hρ
    _ ≤ (L : ℝ) ^ η + (L : ℝ) ^ η / η := add_le_add h1 hlog
    _ = (1 + 1 / η) * (L : ℝ) ^ η := by ring

private theorem re_mul_eq_mul_re_of_pos {a b : ℂ} (ha : 0 < a) (hb : 0 < b) :
    (a * b).re = a.re * b.re := by
  obtain ⟨_, haim⟩ := Complex.pos_iff.mp ha
  obtain ⟨_, hbim⟩ := Complex.pos_iff.mp hb
  simp [Complex.mul_re, ← haim, ← hbim]

/-- Dividing Goldfeld's three-factor lower bound by upper bounds on `L(1, χ)` and `L(1, χ.mul ψ)`
gives a lower bound on `Re L(1, ψ)` depending only on `ε`, `β`, and the auxiliary level `M`. -/
private theorem exists_pair_aux_constant (ε β : ℝ) (hε : 0 < ε) (hβ0 : 1 / 2 ≤ β) (hβ1 : β < 1)
    (hβε : 1 - β ≤ ε / 16) (M : ℕ) [NeZero M] :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ M)
      (ψ : DirichletCharacter ℂ q),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β ≤ 0 →
      c * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  obtain ⟨c₀, hc₀, hGoldfeld⟩ := exists_le_LFunction_one_mul_mul_of_pair_nonpos
  let η : ℝ := ε / 2
  have hη : 0 < η := half_pos hε
  let K : ℝ := (1 + 1 / η) ^ 2 * (M : ℝ) ^ ε
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hK_pos : 0 < K := by positivity
  have : 0 < 1 - β := sub_pos.mpr hβ1
  let c : ℝ := c₀ * (1 - β) * (M : ℝ) ^ (-η) / K
  refine ⟨c, by positivity, fun q _ χ ψ hχq hψq hχ hψ hχψ hFβ ↦ ?_⟩
  have hq_pos : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hMq1 : 1 ≤ (M : ℝ) * q := by
    exact_mod_cast Nat.mul_pos (NeZero.pos M) (NeZero.pos q)
  -- Positive real L-values at `1` factor out of `Complex.re`.
  have hLχ_pos := LFunction_apply_one_pos hχq hχ
  have hLψ_pos := LFunction_apply_one_pos hψq hψ
  have hLχψ_pos := LFunction_apply_one_pos (isQuadratic_mul hχq hψq) hχψ
  have hre_prod : (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re =
      (ψ.LFunction 1).re * ((χ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re) := by
    rw [re_mul_eq_mul_re_of_pos (mul_pos hLχ_pos hLψ_pos) hLχψ_pos,
      re_mul_eq_mul_re_of_pos hLχ_pos hLψ_pos]
    ring
  -- Upper bound the two auxiliary factors by `K * q ^ (ε / 2)`.
  have hlcm_le : (Nat.lcm M q : ℝ) ≤ (M : ℝ) * q := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos q)) (Nat.lcm_dvd_mul M q)
  have hχ_ub := LFunction_one_re_le_mul_rpow χ hχ hη
  have hχψ_ub : ((χ.mul ψ).LFunction 1).re ≤ (1 + 1 / η) * ((M : ℝ) * q) ^ η :=
    (LFunction_one_re_le_mul_rpow (χ.mul ψ) hχψ hη).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hlcm_le hη.le)
        (by positivity))
  have haux_ub : (χ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re ≤ K * (q : ℝ) ^ η := by
    calc
      (χ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re
        ≤ ((1 + 1 / η) * (M : ℝ) ^ η) * ((1 + 1 / η) * ((M : ℝ) * q) ^ η) :=
          mul_le_mul hχ_ub hχψ_ub (Complex.pos_iff.mp hLχψ_pos).1.le (by positivity)
      _ = (1 + 1 / η) ^ 2 * ((M : ℝ) ^ η * (M : ℝ) ^ η) * (q : ℝ) ^ η := by
          rw [Real.mul_rpow hM_pos.le hq_pos.le]
          ring
      _ = K * (q : ℝ) ^ η := by
          dsimp only [K, η]
          rw [← Real.rpow_add hM_pos, add_halves]
  -- Lower bound the three-factor product by `c₀ (1 - β) (M q) ^ (-ε / 2)`.
  have hprod_lb : c₀ * (1 - β) * ((M : ℝ) * q) ^ (-η) ≤
      (ψ.LFunction 1).re * (K * (q : ℝ) ^ η) := by
    calc
      c₀ * (1 - β) * ((M : ℝ) * q) ^ (-η)
        ≤ c₀ * (1 - β) * ((M : ℝ) * q) ^ (-8 * (1 - β)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hMq1 (by dsimp only [η]; linarith))
            (by positivity)
      _ ≤ (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re :=
          hGoldfeld χ ψ hχq hψq hχ hψ hχψ hβ0 hβ1 hFβ
      _ = (ψ.LFunction 1).re * ((χ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re) := hre_prod
      _ ≤ (ψ.LFunction 1).re * (K * (q : ℝ) ^ η) :=
          mul_le_mul_of_nonneg_left haux_ub (Complex.pos_iff.mp hLψ_pos).1.le
  -- Cancel `K * q ^ (ε / 2)` from both sides.
  have hKq_pos : 0 < K * (q : ℝ) ^ η := by positivity
  rw [← mul_le_mul_iff_left₀ hKq_pos]
  refine (le_of_eq ?_).trans hprod_lb
  calc
    c * (q : ℝ) ^ (-ε) * (K * (q : ℝ) ^ η)
      = c₀ * (1 - β) * (M : ℝ) ^ (-η) * ((q : ℝ) ^ (-ε) * (q : ℝ) ^ η) := by
          have : K ≠ 0 := hK_pos.ne'
          dsimp only [c]
          field_simp
    _ = c₀ * (1 - β) * ((M : ℝ) * q) ^ (-η) := by
          rw [← Real.rpow_add hq_pos, show -ε + η = -η by dsimp only [η]; ring,
            Real.mul_rpow hM_pos.le hq_pos.le]
          ring

/-- For an odd prime `p`, the complex Legendre character modulo `p` is primitive, quadratic, and
nonprincipal. -/
private theorem isPrimitive_and_isQuadratic_quadraticChar (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    let χ : DirichletCharacter ℂ p := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
    χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ ≠ 1 := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  dsimp only
  refine ⟨?_, (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ),
    quadraticChar_ringHomComp_ne_one hR hp2⟩
  rw [isPrimitive_def]
  have hc := conductor_changeLevel_quadraticChar (R := ℂ) hR hp2 (dvd_refl p)
  rwa [changeLevel_self] at hc

/-- **Zero-free branch of Siegel's theorem.** If `0 < ε` and no nonprincipal primitive quadratic
L-function vanishes on `(β, 1)` for some `β ∈ [1 / 2, 1)` with `1 - β ≤ ε / 16`, then there is a
uniform constant `c > 0` with `c q ^ (-ε) ≤ Re L(1, ψ)` for every nonprincipal primitive quadratic
character `ψ` modulo `q`. -/
theorem exists_le_LFunction_one_re_of_forall_ne_zero {ε β : ℝ} (hε : 0 < ε)
    (hβ0 : 1 / 2 ≤ β) (hβ1 : β < 1) (hβε : 1 - β ≤ ε / 16)
    (hzero : ∀ (q : ℕ) [NeZero q] (ρ : DirichletCharacter ℂ q),
      ρ.IsPrimitive → ρ.IsQuadratic → ρ ≠ 1 → ∀ σ ∈ Set.Ioo β 1, ρ.LFunction σ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
      ψ.IsPrimitive → ψ.IsQuadratic → ψ ≠ 1 →
      c * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨c₃, hc₃, hb₃⟩ := exists_pair_aux_constant ε β hε hβ0 hβ1 hβε 3
  obtain ⟨c₅, hc₅, hb₅⟩ := exists_pair_aux_constant ε β hε hβ0 hβ1 hβε 5
  refine ⟨min c₃ c₅, lt_min hc₃ hc₅, fun q _ ψ hψp hψq hψ1 ↦ ?_⟩
  -- Helper applying `pair_nonpos_of_forall_ne_zero` to a fixed odd-prime Legendre character.
  have happly (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hpq : p ≠ q) {c : ℝ}
      (hb : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q),
        χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
        riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β ≤ 0 →
        c * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re) :
      c * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
    set χ : DirichletCharacter ℂ p := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
    obtain ⟨hχp, hχq, hχ1⟩ := isPrimitive_and_isQuadratic_quadraticChar p hp2
    have hχψ1 : χ.mul ψ ≠ 1 :=
      mt (hχp.mul_eq_one_iff hψp hψq).mp fun ⟨heq, _⟩ ↦ hpq heq
    have : NeZero (χ.mul ψ).conductor := ⟨(χ.mul ψ).conductor_ne_zero⟩
    have hχ'p : (χ.mul ψ).primitiveCharacter.IsPrimitive :=
      (χ.mul ψ).primitiveCharacter_isPrimitive
    have hχ'q : (χ.mul ψ).primitiveCharacter.IsQuadratic :=
      (isQuadratic_mul hχq hψq).primitiveCharacter
    have hχ'1 : (χ.mul ψ).primitiveCharacter ≠ 1 := fun h1 ↦ hχψ1 <| by
      rw [← changeLevel_primitiveCharacter (χ.mul ψ), h1, map_one]
    have hnonpos : riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β ≤ 0 := by
      refine pair_nonpos_of_forall_ne_zero hχq hψq hχ1 hψ1 hχψ1 (by linarith) hβ1 fun σ hσ ↦
        ⟨hzero p χ hχp hχq hχ1 σ hσ, hzero q ψ hψp hψq hψ1 σ hσ, ?_⟩
      rw [← changeLevel_primitiveCharacter (χ.mul ψ)]
      exact mt (LFunction_changeLevel_eq_zero_iff (χ.mul ψ).primitiveCharacter
        (χ.mul ψ).conductor_dvd_level (s := (σ : ℂ))
        (by simpa using (by linarith : 0 < β).trans hσ.1) (.inl hχ'1)).mp
        (hzero _ (χ.mul ψ).primitiveCharacter hχ'p hχ'q hχ'1 σ hσ)
    exact hb q χ ψ hχq hψq hχ1 hψ1 hχψ1 hnonpos
  by_cases hq3 : q = 3
  · have h5 : c₅ * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re :=
      happly 5 (by decide) (by omega) hb₅
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans h5
  · have h3 : c₃ * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re :=
      happly 3 (by decide) (Ne.symm hq3) hb₃
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans h3

/-- **Two-character comparison from a real zero.** If a nonprincipal primitive quadratic character
`χ` modulo `M` vanishes at `β ∈ [1 / 2, 1)` with `1 - β ≤ ε / 16`, then there is a constant
`c > 0` (depending on `ε`, `β`, and `M`) such that `c q ^ (-ε) ≤ Re L(1, ψ)` for every other
nonprincipal primitive quadratic character `ψ` modulo `q`. -/
theorem exists_le_LFunction_one_re_of_LFunction_eq_zero_of_ne {ε β : ℝ} (hε : 0 < ε)
    (hβ0 : 1 / 2 ≤ β) (hβ1 : β < 1) (hβε : 1 - β ≤ ε / 16) {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (hχp : χ.IsPrimitive) (hχq : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    (hzero : χ.LFunction β = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
      ψ.IsPrimitive → ψ.IsQuadratic → ψ ≠ 1 → (¬∃ h : M = q, h ▸ χ = ψ) →
      c * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  obtain ⟨c, hc, hb⟩ := exists_pair_aux_constant ε β hε hβ0 hβ1 hβε M
  refine ⟨c, hc, fun q _ ψ hψp hψq hψ1 hne ↦ ?_⟩
  have hχψ1 : χ.mul ψ ≠ 1 := mt (hχp.mul_eq_one_iff hψp hψq).mp hne
  exact hb q χ ψ hχq hψq hχ1 hψ1 hχψ1 (by simp [hzero])

/-- **Exceptional-zero branch of Siegel's theorem.** Under the hypotheses of
`exists_le_LFunction_one_re_of_LFunction_eq_zero_of_ne`, absorbing the positive value `L(1, χ)`
into the constant extends the lower bound `c q ^ (-ε) ≤ Re L(1, ψ)` to *every* nonprincipal
primitive quadratic character `ψ`, including `χ` itself. -/
theorem exists_le_LFunction_one_re_of_LFunction_eq_zero {ε β : ℝ} (hε : 0 < ε)
    (hβ0 : 1 / 2 ≤ β) (hβ1 : β < 1) (hβε : 1 - β ≤ ε / 16) {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (hχp : χ.IsPrimitive) (hχq : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    (hzero : χ.LFunction β = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
      ψ.IsPrimitive → ψ.IsQuadratic → ψ ≠ 1 →
      c * (q : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  obtain ⟨c₁, hc₁, hb⟩ :=
    exists_le_LFunction_one_re_of_LFunction_eq_zero_of_ne hε hβ0 hβ1 hβε χ hχp hχq hχ1 hzero
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hLχ_re : 0 < (χ.LFunction 1).re := (Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ1)).1
  let c₀ : ℝ := (χ.LFunction 1).re * (M : ℝ) ^ ε
  refine ⟨min c₁ c₀, lt_min hc₁ (by positivity), fun q _ ψ hψp hψq hψ1 ↦ ?_⟩
  by_cases heq : ∃ h : M = q, h ▸ χ = ψ
  · rcases heq with ⟨rfl, rfl⟩
    calc
      min c₁ c₀ * (M : ℝ) ^ (-ε)
        ≤ c₀ * (M : ℝ) ^ (-ε) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (χ.LFunction 1).re * ((M : ℝ) ^ ε * (M : ℝ) ^ (-ε)) := by dsimp only [c₀]; ring
      _ = (χ.LFunction 1).re := by
        rw [← Real.rpow_add hM_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (hb q ψ hψp hψq hψ1 heq)

end DirichletCharacter

namespace TauCeti

/-- **Siegel's theorem.** For every `ε > 0`, there exists a constant `c > 0` such that
`c q ^ (-ε) ≤ Re L(1, χ)` for every nonprincipal primitive quadratic Dirichlet character `χ`
modulo `q`. The constant is uniform over all conductors `q`, and is ineffective because the proof
splits classically on whether some primitive quadratic L-function has a real zero close to `1`. -/
theorem quadratic_LFunction_siegel (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
        c * Real.rpow (q : ℝ) (-ε) ≤ (DirichletCharacter.LFunction χ 1).re := by
  let δ : ℝ := min (ε / 16) (1 / 2)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ_le_ε : δ ≤ ε / 16 := min_le_left _ _
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  let β₀ : ℝ := 1 - δ
  by_cases hex : ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter ℂ M) (β : ℝ),
      χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧ β ∈ Set.Ioo β₀ 1 ∧ χ.LFunction β = 0
  · rcases hex with ⟨M, hM, χ, β, hχp, hχq, hχ1, hβ, hzero⟩
    exact DirichletCharacter.exists_le_LFunction_one_re_of_LFunction_eq_zero hε
      (by linarith [hβ.1]) hβ.2 (by linarith [hβ.1]) χ hχp hχq hχ1 hzero
  · refine DirichletCharacter.exists_le_LFunction_one_re_of_forall_ne_zero (β := β₀) hε
      (by linarith) (by linarith) (by linarith) fun q hq ρ hρp hρq hρ1 σ hσ h0 ↦ ?_
    exact hex ⟨q, hq, ρ, σ, hρp, hρq, hρ1, hσ, h0⟩

end TauCeti
