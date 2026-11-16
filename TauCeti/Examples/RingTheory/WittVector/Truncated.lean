/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.FieldDivision
public import TauCeti.RingTheory.WittVector.Reduced
public import TauCeti.RingTheory.WittVector.Truncated

/-!
# Checks for finite-length Witt operators and reduced-ring Witt vectors

Concrete computations and sharpness checks for `TruncatedWittVector` and `WittVector`:

* Degenerate lengths: `W_0(R)` is trivial (`F : W_1(ℤ) → W_0(ℤ)` vanishes) and `W_1(R) ≃+* R`.
* Direction and mixed-characteristic behaviour of finite Frobenius: at `p = 2`,
  `F(1, 1) = 1^2 + 2 * 1 = 3` in `W_2(ℤ)` whereas restriction gives `1`; over `𝔽_2`, `F(0, 1) = 0`.
* Ghost map at length two: on `W_2(ℤ)` it sends `(a, b)` to `(a, a ^ p + p * b)` and is injective
  even though `p` is not a unit in `ℤ`; over `𝔽_p`, `(0, 1) ≠ 0` has vanishing ghost components, so
  `p`-torsion-freeness cannot be omitted.
* Finite Verschiebung: remains injective in the presence of `p`-torsion, agrees with multiplication
  by `p` under `W_r(𝔽_p) ≃+* ℤ / p^r ℤ`, and disagrees with `p` over `ℤ / 4ℤ` at `p = 2`.
* Imperfect reduced rings: for `R = 𝔽_p[X]`, Frobenius on `R` is injective but not surjective, yet
  Witt Frobenius on `𝕎 (𝔽_p[X])` is injective and `p` is a nonzerodivisor in `𝕎 (𝔽_p[X])`.
-/

public section

noncomputable section

namespace TauCeti.Examples.WittVectorTruncated

open scoped Polynomial nonZeroDivisors
open TruncatedWittVector

section GeneralPrime

variable (p : ℕ) [hp : Fact p.Prime]

-- Length zero has a subsingleton carrier, and `F : W_1(ℤ) → W_0(ℤ)` is identically zero.
example (x : TruncatedWittVector p 1 ℤ) : TruncatedWittVector.frobenius x = 0 :=
  Subsingleton.elim _ _

-- `W_0(R)` is trivial and `W_1(R) ≃+* R`.
example {R : Type*} [CommRing R] (x : TruncatedWittVector p 0 R) : x = 0 :=
  Subsingleton.elim _ _

example (R : Type*) [CommRing R] : TruncatedWittVector p 1 R ≃+* R :=
  constantCoeffEquiv p R

-- For `R = ℤ` and `r = 2`, the ghost map is `(a, b) ↦ (a, a ^ p + p * b)` and is injective even
-- though `p` is not a unit in `ℤ`.
example (a b : ℤ) :
    ghostMap (mk p ![a, b] : TruncatedWittVector p 2 ℤ) 0 = a ∧
      ghostMap (mk p ![a, b] : TruncatedWittVector p 2 ℤ) 1 = a ^ p + p * b := by
  refine ⟨?_, ?_⟩
  · simp [ghostComponent_zero]
  · simp [ghostComponent_one]

example :
    Function.Injective
      (fun (x : TruncatedWittVector p 2 ℤ) (i : Fin 2) ↦ WittVector.ghostComponent i x.out) ∧
      ¬ IsUnit (p : ℤ) := by
  refine ⟨ghostComponent_out_injective (mul_right_injective₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)),
    fun h ↦ ?_⟩
  have habs : Int.natAbs (p : ℤ) = 1 := Int.isUnit_iff_natAbs_eq.mp h
  exact hp.out.ne_one (by simpa using habs)

-- Over `𝔽_p` at length two, `(0, 1)` and `0` are distinct yet have identical ghost components, so
-- `p`-torsion-freeness cannot be dropped from ghost injectivity.
example :
    (mk p ![0, 1] : TruncatedWittVector p 2 (ZMod p)) ≠ 0 ∧
      ghostMap (mk p ![0, 1] : TruncatedWittVector p 2 (ZMod p)) =
        ghostMap (0 : TruncatedWittVector p 2 (ZMod p)) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h1 := congrArg (coeff 1) h
    simp only [coeff_mk, Matrix.cons_val_one, coeff_zero] at h1
    exact one_ne_zero h1
  · ext i
    fin_cases i
    · simp [ghostComponent_zero]
    · simp [ghostComponent_one, zero_pow hp.out.ne_zero]

-- Finite Verschiebung stays injective when `R` has nontrivial `p`-torsion.
example (r : ℕ) :
    Function.Injective
      (verschiebung :
        TruncatedWittVector p r (ZMod (p ^ 2)) → TruncatedWittVector p (r + 1) (ZMod (p ^ 2))) :=
  verschiebung_injective

-- Over `𝔽_p`, finite Verschiebung corresponds to multiplication by `p` under
-- `W_r(𝔽_p) ≃+* ℤ / p^r ℤ`.
example (r : ℕ) (x : ZMod (p ^ (r + 1))) :
    (zmodEquivTrunc p (r + 1)).symm
      (verschiebung (zmodEquivTrunc p r (ZMod.castHom (pow_dvd_pow p (Nat.le_succ r)) _ x))) =
      p * x :=
  zmodEquivTrunc_symm_verschiebung x

-- For the imperfect reduced ring `R = 𝔽_p[X]`, Frobenius on `R` is injective and not surjective,
-- while Witt Frobenius on `𝕎 (𝔽_p[X])` is injective and `𝕎 (𝔽_p[X])` is `p`-torsion-free.
example :
    Function.Injective (_root_.frobenius (ZMod p)[X] p) ∧
      ¬ Function.Surjective (_root_.frobenius (ZMod p)[X] p) ∧
      Function.Injective (WittVector.frobenius : WittVector p (ZMod p)[X] → _) ∧
      (p : WittVector p (ZMod p)[X]) ∈ (WittVector p (ZMod p)[X])⁰ := by
  refine ⟨frobenius_inj (ZMod p)[X] p, fun hsurj ↦ ?_,
    WittVector.frobenius_injective p (ZMod p)[X],
    WittVector.p_mem_nonZeroDivisors p (ZMod p)[X]⟩
  obtain ⟨f, hf⟩ := hsurj Polynomial.X
  rw [frobenius_def] at hf
  have hdeg := congrArg Polynomial.natDegree hf
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdeg
  exact hp.out.ne_one (Nat.eq_one_of_mul_eq_one_right hdeg)

end GeneralPrime

section PrimeTwo

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- At `p = 2`, `(1, 1) ∈ W_2(ℤ)` maps under `F` to `1^2 + 2 * 1 = 3`, whereas restriction gives `1`.
example :
    constantCoeffEquiv 2 ℤ
        (TruncatedWittVector.frobenius (mk 2 ![1, 1] : TruncatedWittVector 2 2 ℤ)) = 3 ∧
      constantCoeffEquiv 2 ℤ
        (truncate (Nat.le_succ 1) (mk 2 ![1, 1] : TruncatedWittVector 2 2 ℤ)) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [constantCoeffEquiv_apply, coeff_frobenius_zero]
    norm_num [coeff_mk]
  · simp

-- Over `𝔽_2`, `F(0, 1) = 0`: the second coordinate vanishes modulo `2`.
example :
    TruncatedWittVector.frobenius (mk 2 ![0, 1] : TruncatedWittVector 2 2 (ZMod 2)) = 0 := by
  ext i
  rw [Fin.eq_zero i, coeff_frobenius_charP]
  simp

-- Over `ℤ / 4ℤ` (a `ℤ_(2)`-algebra with `2 ≠ 0`), `V(1) ≠ 2` in `W_2(ℤ / 4ℤ)`.
example :
    verschiebung (1 : TruncatedWittVector 2 1 (ZMod 4)) ≠
      (2 : TruncatedWittVector 2 2 (ZMod 4)) := by
  intro h
  have h0 := congrArg (coeff 0) h
  rw [verschiebung_coeff_zero, coeff_ofNat_zero] at h0
  exact absurd h0 (by decide)

end PrimeTwo

end TauCeti.Examples.WittVectorTruncated

end
