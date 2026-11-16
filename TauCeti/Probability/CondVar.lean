/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional law of total variance

Mathlib proves the second-moment formula `Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2` for a
square-integrable random variable `X` under `m ≤ m₀` and `[IsFiniteMeasure μ]`, and derives the
unconditional law of total variance `μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ]` on a
probability space.

Because Mathlib's `condExp` and `condVar` both vanish when `m` is not a sub-σ-algebra of `m₀`,
when `μ.trim` is not σ-finite, or when `X` is not integrable (leaving `μ[X | m] = 0`), the
second-moment formula holds for *every* measure `μ` and *every* `m` assuming only `MemLp X 2 μ`.
Combining it with the tower property of conditional expectation yields the conditional law of
total variance for nested sub-σ-algebras `m₁ ≤ m₂ ≤ m₀`:

`Var[Θ; μ | m₁] =ᵐ[μ] μ[Var[Θ; μ | m₂] | m₁] + Var[μ[Θ | m₂]; μ | m₁]`.

In Bayesian missing-data analysis, taking `m₁ = σ(Y_obs)` and `m₂ = σ(Y_obs, Y_mis)` decomposes
the observed-data posterior variance into the posterior predictive expectation of the
complete-data posterior variance plus the posterior predictive variance of the complete-data
posterior mean.

## Main statements

* `ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp_of_memLp`: the second-moment formula
  `Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2` for any `MemLp X 2 μ`, without finiteness or
  sub-σ-algebra hypotheses on `μ` and `m`.
* `ProbabilityTheory.condVar_ae_eq_condExp_condVar_add_condVar_condExp`: the conditional law of
  total variance for `m₁ ≤ m₂ ≤ m₀` and `MemLp Θ 2 μ`.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley,
  2020, §10.2, (10.9)–(10.10), p. 233.
-/

public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {Ω : Type*} {m₁ m₂ m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}

/-- The conditional variance of a square-integrable real random variable equals the conditional
second moment minus the square of the conditional expectation, for any measure `μ` and any
measurable space `m`. When `¬ m ≤ m₀` or `μ.trim` fails to be σ-finite both sides vanish, and when
`X` is square-integrable without being integrable `μ[X | m] = 0` reduces both sides to
`μ[X ^ 2 | m]`. -/
theorem condVar_ae_eq_condExp_sq_sub_sq_condExp_of_memLp {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 := by
  by_cases hm : m ≤ m₀
  swap
  · simp [condVar_of_not_le hm, condExp_of_not_le hm]
  by_cases hσ : SigmaFinite (μ.trim hm)
  swap
  · simp [condVar_of_not_sigmaFinite hσ, condExp_of_not_sigmaFinite hm hσ]
  by_cases hX₁ : Integrable X μ
  swap
  · simp [condVar, condExp_of_not_integrable hX₁]
  have aux₀ : Integrable (X ^ 2) μ := hX.integrable_sq
  have aux₁ : Integrable (2 * X * μ[X | m]) μ := by
    rw [mul_assoc]
    exact (memLp_one_iff_integrable.1 <| hX.mul (hX.condExp one_le_two)).const_mul _
  have aux₂ : Integrable (μ[X | m] ^ 2) μ := (hX.condExp one_le_two).integrable_sq
  calc
    Var[X; μ | m]
    _ = μ[X ^ 2 - 2 * X * μ[X | m] + μ[X | m] ^ 2 | m] := by rw [condVar, sub_sq]
    _ =ᵐ[μ] μ[X ^ 2 | m] - 2 * μ[X | m] ^ 2 + μ[X | m] ^ 2 := by
      filter_upwards [condExp_add (m := m) (aux₀.sub aux₁) aux₂, condExp_sub (m := m) aux₀ aux₁,
        condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp aux₁ (hX₁.const_mul _),
        condExp_ofNat (m := m) 2 X] with ω hω₀ hω₁ hω₂ hω₃
      simp [hω₀, hω₁, hω₂, hω₃,
        condExp_of_stronglyMeasurable hm (stronglyMeasurable_condExp.pow _) aux₂]
      simp [mul_assoc, sq]
    _ = μ[X ^ 2 | m] - μ[X | m] ^ 2 := by ring

/-- **Conditional law of total variance.** For nested sub-σ-algebras `m₁ ≤ m₂ ≤ m₀` and a
square-integrable random variable `Θ`, the `m₁`-conditional variance of `Θ` splits into the
`m₁`-conditional expectation of its `m₂`-conditional variance and the `m₁`-conditional variance
of its `m₂`-conditional expectation. -/
theorem condVar_ae_eq_condExp_condVar_add_condVar_condExp (h₁₂ : m₁ ≤ m₂) (h₂₀ : m₂ ≤ m₀)
    {Θ : Ω → ℝ} (hΘ : MemLp Θ 2 μ) :
    Var[Θ; μ | m₁] =ᵐ[μ] μ[Var[Θ; μ | m₂] | m₁] + Var[μ[Θ | m₂]; μ | m₁] := by
  have h₁₀ : m₁ ≤ m₀ := h₁₂.trans h₂₀
  by_cases hσ₂ : SigmaFinite (μ.trim h₂₀)
  swap
  · have hσ₁ : ¬ SigmaFinite (μ.trim h₁₀) := fun h ↦ hσ₂ (sigmaFiniteTrim_mono h₂₀ h₁₂)
    simp [condVar_of_not_sigmaFinite hσ₁, condExp_of_not_sigmaFinite h₁₀ hσ₁]
  have hY : MemLp (μ[Θ | m₂]) 2 μ := hΘ.condExp one_le_two
  have h₁ := condVar_ae_eq_condExp_sq_sub_sq_condExp_of_memLp (m := m₁) hΘ
  have h₂ := condExp_congr_ae (m := m₁)
    (condVar_ae_eq_condExp_sq_sub_sq_condExp_of_memLp (m := m₂) hΘ)
  have hYsq : Integrable (μ[Θ | m₂] ^ 2) μ := hY.integrable_sq
  have h₃ := condExp_sub (μ := μ) (m := m₁)
    (integrable_condExp (f := Θ ^ 2) (m := m₂)) hYsq
  have h₄ := condVar_ae_eq_condExp_sq_sub_sq_condExp_of_memLp (m := m₁) hY
  have h_tower_sq : μ[μ[Θ ^ 2 | m₂] | m₁] =ᵐ[μ] μ[Θ ^ 2 | m₁] :=
    condExp_condExp_of_le h₁₂ h₂₀
  have h_tower : μ[μ[Θ | m₂] | m₁] =ᵐ[μ] μ[Θ | m₁] :=
    condExp_condExp_of_le h₁₂ h₂₀
  filter_upwards [h₁, h₂, h₃, h₄, h_tower_sq, h_tower] with ω hω₁ hω₂ hω₃ hω₄ htsq ht
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] at hω₁ hω₂ hω₃ hω₄ ⊢
  rw [hω₁, hω₂, hω₃, htsq, hω₄, ht]
  ring

end ProbabilityTheory
