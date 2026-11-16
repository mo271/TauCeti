/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.MulOpposite
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Opposite-algebra invariance and regularized quotients for `CFC.nnrpow`

In a non-unital topological star algebra with a real continuous functional calculus, nonnegative
real powers `a ^ y` (`CFC.nnrpow`) commute with passing between `A` and its multiplicative opposite
`Aᵐᵒᵖ`. This translates power identities between left and right Hilbert C⋆-modules.

In an isometric non-unital continuous functional calculus, for `0 < p ≤ q` and `0 < ε`, the
regularized quotient `c = cfcₙ (fun t : ℝ≥0 ↦ t ^ p / (t ^ q + ε)) a` of a positive element `a`
satisfies `c * a ^ q + ε • c = a ^ p` and `‖a ^ p - c * a ^ q‖ ≤ ε ^ (p / q)`. Specializing to
`q = 1 / 2` and `p = 1 / 2 - r` yields the norm-convergent approximations behind Lance's
fractional-power factorization in Hilbert C⋆-modules.

## Main declarations

* `CFC.unop_nnrpow`, `CFC.op_nnrpow`: nonnegative real powers commute with `MulOpposite.unop` and
  `MulOpposite.op`.
* `CFC.commute_cfcₙ_nnrpow_div_add_nnrpow`: the regularized quotient commutes with every power
  `a ^ r`.
* `CFC.cfcₙ_nnrpow_div_add_mul_nnrpow_add`: `c * a ^ q + ε • c = a ^ p`.
* `CFC.nnNorm_nnrpow_sub_cfcₙ_nnrpow_div_add_mul_nnrpow_le`,
  `CFC.norm_nnrpow_sub_cfcₙ_nnrpow_div_add_mul_nnrpow_le`:
  `‖a ^ p - c * a ^ q‖ ≤ (ε : ℝ) ^ ((p : ℝ) / (q : ℝ))`.
* `CFC.tendsto_cfcₙ_nnrpow_div_add_mul_nnrpow`: `c * a ^ q → a ^ p` as `ε → 0⁺`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.4.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 2.31.
-/

public section

open Filter MulOpposite Topology
open scoped NNReal

namespace CFC

section MulOpposite

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [NonnegSpectrumClass ℝ Aᵐᵒᵖ] [IsSemitopologicalRing A] [T2Space A]

/-- Nonnegative real powers in the opposite algebra `Aᵐᵒᵖ` agree with those in `A`. -/
@[simp]
theorem unop_nnrpow (a : Aᵐᵒᵖ) (y : ℝ≥0) : unop (a ^ y) = (unop a) ^ y :=
  MulOpposite.unop_cfcₙ_nonneg (NNReal.nnrpow · y) a

/-- Nonnegative real powers in `A` agree with those in the opposite algebra `Aᵐᵒᵖ`. -/
@[simp]
theorem op_nnrpow (a : A) (y : ℝ≥0) : op (a ^ y) = (op a) ^ y :=
  MulOpposite.op_cfcₙ_nonneg (NNReal.nnrpow · y) a

end MulOpposite

section RegularizedQuotient

section Algebraic

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

private lemma continuous_nnrpow_div_add (p q : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) :
    Continuous fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε) :=
  (NNReal.continuous_nnrpow_const p).div
    ((NNReal.continuous_nnrpow_const q).add continuous_const)
    fun _ ↦ (add_pos_of_nonneg_of_pos zero_le hε).ne'

private lemma continuousOn_nnrpow_div_add (p q : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) (s : Set ℝ≥0) :
    ContinuousOn (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) s :=
  (continuous_nnrpow_div_add p q hε).continuousOn

private lemma nnrpow_div_add_zero {p : ℝ≥0} (hp : 0 < p) (q ε : ℝ≥0) :
    NNReal.nnrpow 0 p / (NNReal.nnrpow 0 q + ε) = 0 := by
  simp [hp.ne']

/-- The regularized power quotient `cfcₙ (fun t ↦ t ^ p / (t ^ q + ε)) a` commutes with every
nonnegative power `a ^ r`. -/
theorem commute_cfcₙ_nnrpow_div_add_nnrpow (a : A) {p : ℝ≥0} (hp : 0 < p) (q : ℝ≥0)
    {ε : ℝ≥0} (hε : 0 < ε) (r : ℝ≥0) :
    Commute (cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a) (a ^ r) := by
  by_cases ha : 0 ≤ a
  · obtain rfl | hr := eq_zero_or_pos r
    · simp
    rw [commute_iff_eq, nnrpow_def]
    have hc := continuousOn_nnrpow_div_add p q hε (quasispectrum ℝ≥0 a)
    have hc0 := nnrpow_div_add_zero hp q ε
    have hr0 : NNReal.nnrpow 0 r = 0 := by simp [hr.ne']
    rw [← cfcₙ_mul _ _ a hc hc0 (by fun_prop) hr0,
      ← cfcₙ_mul _ _ a (by fun_prop) hr0 hc hc0]
    exact cfcₙ_congr fun t _ ↦ mul_comm _ _
  · simp [nnrpow_def, cfcₙ_apply_of_not_predicate a ha]

/-- Algebraic decomposition of `a ^ p` via the regularized quotient
`c = cfcₙ (fun t ↦ t ^ p / (t ^ q + ε)) a`: one has `c * a ^ q + ε • c = a ^ p`. -/
theorem cfcₙ_nnrpow_div_add_mul_nnrpow_add (a : A) {p q ε : ℝ≥0} (hp : 0 < p) (hq : 0 < q)
    (hε : 0 < ε) :
    cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a * a ^ q +
        ε • cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a =
      a ^ p := by
  have hc := continuousOn_nnrpow_div_add p q hε (quasispectrum ℝ≥0 a)
  have hc0 := nnrpow_div_add_zero hp q ε
  have hq0 : NNReal.nnrpow 0 q = 0 := by simp [hq.ne']
  calc
    cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a * a ^ q +
        ε • cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a
      = cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε) * NNReal.nnrpow t q +
          ε • (NNReal.nnrpow t p / (NNReal.nnrpow t q + ε))) a := by
        rw [nnrpow_def, cfcₙ_add _ _ a (by exact hc.mul (by fun_prop)) (by simp [hc0])
          (by exact hc.const_smul ε) (by simp [hc0]), cfcₙ_mul _ _ a hc hc0 (by fun_prop) hq0,
          cfcₙ_smul ε _ a hc hc0]
    _ = a ^ p := by
        rw [nnrpow_def]
        refine cfcₙ_congr fun t _ ↦ ?_
        dsimp only [smul_eq_mul]
        rw [mul_comm ε _, ← mul_add, div_mul_cancel₀ _ (add_pos_of_nonneg_of_pos zero_le hε).ne']

end Algebraic

section Isometric

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- Uniform `ℝ≥0`-norm estimate for the regularized power quotient: for `0 < p ≤ q` and `0 < ε`,
`‖a ^ p - cfcₙ (fun t ↦ t ^ p / (t ^ q + ε)) a * a ^ q‖₊ ≤ ε ^ (p / q)`. -/
theorem nnNorm_nnrpow_sub_cfcₙ_nnrpow_div_add_mul_nnrpow_le (a : A) {p q ε : ℝ≥0}
    (hp : 0 < p) (hpq : p ≤ q) (hε : 0 < ε) :
    ‖a ^ p - cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a * a ^ q‖₊ ≤
      ε ^ ((p : ℝ) / (q : ℝ)) := by
  have hq : 0 < q := hp.trans_le hpq
  have hsub :
      a ^ p - cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a * a ^ q =
        cfcₙ (fun t : ℝ≥0 ↦ ε • (NNReal.nnrpow t p / (NNReal.nnrpow t q + ε))) a := by
    rw [sub_eq_iff_eq_add', ← cfcₙ_nnrpow_div_add_mul_nnrpow_add a hp hq hε,
      cfcₙ_smul ε _ a (continuousOn_nnrpow_div_add p q hε _) (nnrpow_div_add_zero hp q ε)]
  rw [hsub]
  refine nnNorm_cfcₙ_nnreal_le fun t _ ↦ ?_
  have hθ₀ : 0 ≤ (p : ℝ) / (q : ℝ) := by positivity
  have hθ₁ : (p : ℝ) / (q : ℝ) ≤ 1 := (div_le_one (NNReal.coe_pos.2 hq)).2 (NNReal.coe_le_coe.2 hpq)
  have ht : NNReal.nnrpow t p = (NNReal.nnrpow t q) ^ ((p : ℝ) / (q : ℝ)) := by
    rw [NNReal.nnrpow_def, NNReal.nnrpow_def, ← NNReal.rpow_mul,
      mul_div_cancel₀ _ (NNReal.coe_pos.2 hq).ne']
  rw [smul_eq_mul, ht]
  exact NNReal.mul_rpow_div_add_le (NNReal.nnrpow t q) ε hθ₀ hθ₁

/-- Uniform norm estimate for the regularized power quotient: for `0 < p ≤ q` and `0 < ε`,
`‖a ^ p - cfcₙ (fun t ↦ t ^ p / (t ^ q + ε)) a * a ^ q‖ ≤ ε ^ (p / q)`. -/
theorem norm_nnrpow_sub_cfcₙ_nnrpow_div_add_mul_nnrpow_le (a : A) {p q ε : ℝ≥0}
    (hp : 0 < p) (hpq : p ≤ q) (hε : 0 < ε) :
    ‖a ^ p - cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a * a ^ q‖ ≤
      (ε : ℝ) ^ ((p : ℝ) / (q : ℝ)) := by
  simpa only [coe_nnNorm, NNReal.coe_rpow] using
    NNReal.coe_le_coe.2 (nnNorm_nnrpow_sub_cfcₙ_nnrpow_div_add_mul_nnrpow_le a hp hpq hε)

/-- As `ε → 0⁺` in `ℝ≥0`, `cfcₙ (fun t ↦ t ^ p / (t ^ q + ε)) a * a ^ q` converges in norm to
`a ^ p` whenever `0 < p ≤ q`. -/
theorem tendsto_cfcₙ_nnrpow_div_add_mul_nnrpow (a : A) {p q : ℝ≥0} (hp : 0 < p) (hpq : p ≤ q) :
    Tendsto
      (fun ε : ℝ≥0 ↦ cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t p / (NNReal.nnrpow t q + ε)) a * a ^ q)
      (𝓝[>] 0) (𝓝 (a ^ p)) := by
  have hq : 0 < q := hp.trans_le hpq
  have hθ : 0 < (p : ℝ) / (q : ℝ) := by positivity
  have hcont : Continuous fun ε : ℝ≥0 ↦ (ε : ℝ) ^ ((p : ℝ) / (q : ℝ)) :=
    NNReal.continuous_coe.rpow_const fun _ ↦ Or.inr hθ.le
  have hg : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ) ^ ((p : ℝ) / (q : ℝ))) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow hθ.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _)
    (eventually_nhdsWithin_iff.2 <| .of_forall fun ε (hε : 0 < ε) ↦ ?_) hg
  rw [norm_sub_rev]
  exact norm_nnrpow_sub_cfcₙ_nnrpow_div_add_mul_nnrpow_le a hp hpq hε

end Isometric

end RegularizedQuotient

end CFC
