/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Stopping

/-!
# Indistinguishability of continuous versions and stopped processes

Two stochastic processes indexed by a separable topological space and taking values in a
Hausdorff space are indistinguishable whenever almost every path of each process is continuous
and the two processes agree almost everywhere at each fixed index. Countable dense sampling turns
separate-time almost-everywhere agreement into simultaneous agreement outside one common null set.

Indistinguishability is also preserved by stopping at any random time, without measurability or
regularity assumptions on the time or the paths.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §1.
-/

public section

open Filter MeasureTheory Set TopologicalSpace

namespace ProbabilityTheory.Indistinguishable

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}

/-- Almost surely continuous modifications over a separable index space with Hausdorff target
are indistinguishable. Neither measurability of the processes nor finiteness of the measure is
required. -/
theorem of_ae_eq_eval_of_ae_continuous [TopologicalSpace ι] [SeparableSpace ι]
    [TopologicalSpace E] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (heq : ∀ t, X t =ᵐ[P] Y t) : X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ι
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ t : D, X t ω = Y t ω := ae_all_iff.2 fun t ↦ heq t
  filter_upwards [hX, hY, hD] with ω hXω hYω hDω
  exact congrFun (hXω.ext_on hDd hYω fun t ht ↦ hDω ⟨t, ht⟩)

/-- Stopping two indistinguishable processes at the same random time yields indistinguishable
processes. -/
@[gcongr]
protected theorem stoppedProcess [LinearOrder ι] [Nonempty ι]
    (h : X ≡ᵐ[P] Y) (τ : Ω → WithTop ι) :
    stoppedProcess X τ ≡ᵐ[P] stoppedProcess Y τ := by
  filter_upwards [h] with ω hω t
  simp only [MeasureTheory.stoppedProcess, hω]

end ProbabilityTheory.Indistinguishable
