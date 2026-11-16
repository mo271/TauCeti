/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
import TauCeti.Probability.Kernel.Composition.CompProd

/-!
# Mixture decomposition of regular conditional distributions

Given three random variables `θ : Ω → E`, `Yo : Ω → O`, and `Ym : Ω → M` on a finite measure space
`(Ω, J)` with `E` and `M` nonempty standard Borel spaces, the regular conditional distribution of
`θ` given `Yo` disintegrates through `(Yo, Ym)`:

`condDistrib θ Yo J =ᵐ[J.map Yo]
  (condDistrib θ (fun ω ↦ (Yo ω, Ym ω)) J) ∘ₖ (Kernel.id ×ₖ condDistrib Ym Yo J)`.

In Bayesian inference with missing data, `Yo` is the observed data, `Ym` is the missing data, and
`θ` is the estimand: the observed-data posterior `P(θ | Y_obs)` equals the complete-data posterior
`P(θ | Y_obs, Y_mis)` averaged over the posterior predictive distribution `P(Y_mis | Y_obs)` of
the missing data.

## Main statements

* `ProbabilityTheory.condDistrib_ae_eq_comp`: `condDistrib θ Yo J` agrees `J.map Yo`-almost
  everywhere with `(condDistrib θ (fun ω ↦ (Yo ω, Ym ω)) J) ∘ₖ (Kernel.id ×ₖ condDistrib Ym Yo J)`
  whenever `θ`, `Yo`, and `Ym` are `J`-a.e. measurable.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley,
  2020, §10.2, (10.8), p. 233.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

/-- **Tower mixture law for regular conditional distributions.** For `J`-a.e. measurable maps `θ`,
`Yo`, and `Ym` on a finite measure space with `E` and `M` nonempty standard Borel spaces, the
conditional distribution of `θ` given `Yo` agrees `J.map Yo`-almost everywhere with the composition
of the conditional distribution of `θ` given `(Yo, Ym)` and `Kernel.id ×ₖ condDistrib Ym Yo J`. -/
theorem condDistrib_ae_eq_comp {Ω O M E : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    {J : Measure Ω} [IsFiniteMeasure J] {θ : Ω → E} {Yo : Ω → O} {Ym : Ω → M}
    (hθ : AEMeasurable θ J) (hYo : AEMeasurable Yo J) (hYm : AEMeasurable Ym J) :
    condDistrib θ Yo J =ᵐ[J.map Yo]
      (condDistrib θ (fun ω ↦ (Yo ω, Ym ω)) J) ∘ₖ (Kernel.id ×ₖ condDistrib Ym Yo J) := by
  set η := condDistrib Ym Yo J
  set κ := condDistrib θ (fun ω ↦ (Yo ω, Ym ω)) J
  refine condDistrib_ae_eq_of_measure_eq_compProd hYo hθ ?_
  calc
    J.map (fun ω ↦ (Yo ω, θ ω))
    _ = (J.map (fun ω ↦ ((Yo ω, Ym ω), θ ω))).map
        ((Prod.map id Prod.snd) ∘ MeasurableEquiv.prodAssoc) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      rfl
    _ = ((J.map Yo ⊗ₘ η ⊗ₘ κ).map MeasurableEquiv.prodAssoc).map (Prod.map id Prod.snd) := by
      rw [← compProd_map_condDistrib (hYo.prodMk hYm) hθ, ← compProd_map_condDistrib hYo hYm,
        Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (J.map Yo ⊗ₘ (η ⊗ₖ κ)).map (Prod.map id Prod.snd) := by rw [Measure.compProd_assoc']
    _ = J.map Yo ⊗ₘ (η ⊗ₖ κ).snd := by rw [← Measure.compProd_map measurable_snd, ← Kernel.snd_eq]
    _ = J.map Yo ⊗ₘ (κ ∘ₖ (Kernel.id ×ₖ η)) := by rw [Kernel.snd_compProd]

end ProbabilityTheory
