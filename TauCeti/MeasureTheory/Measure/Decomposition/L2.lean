/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# `L²` integrability of square-root Radon–Nikodym derivatives

For any finite measure `P` and any measure `μ` on a measurable space `X`, the Radon–Nikodym
derivative `P.rnDeriv μ` satisfies `∫ (P.rnDeriv μ x).toReal ∂μ ≤ P.real Set.univ < ∞`, so its
square root `fun x ↦ √(P.rnDeriv μ x).toReal` belongs to `L²(μ)`. By Cauchy–Schwarz in `L²(μ)`, the
geometric mean `fun x ↦ √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)` is `μ`-integrable for
any two finite measures `P` and `Q`.

## Main results

* `MeasureTheory.Measure.memLp_two_sqrt_toReal_rnDeriv`: `√(P.rnDeriv μ).toReal` lies in `L²(μ)`
  for every finite measure `P`.
* `MeasureTheory.Measure.integrable_sqrt_toReal_rnDeriv_mul`: the geometric mean
  `√((P.rnDeriv μ).toReal * (Q.rnDeriv μ).toReal)` is `μ`-integrable for finite measures `P`, `Q`.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The square root of the Radon–Nikodym derivative of a finite measure belongs to `L²`. -/
theorem memLp_two_sqrt_toReal_rnDeriv (P μ : Measure X) [IsFiniteMeasure P] :
    MemLp (fun x ↦ √(P.rnDeriv μ x).toReal) 2 μ := by
  refine (memLp_two_iff_integrable_sq
    ((Measure.measurable_rnDeriv P μ).ennreal_toReal.sqrt.aestronglyMeasurable)).2 ?_
  simpa [Real.sq_sqrt ENNReal.toReal_nonneg] using
    Measure.integrable_toReal_rnDeriv (μ := P) (ν := μ)

/-- The geometric mean `√(dP/dμ · dQ/dμ)` of the Radon–Nikodym derivatives of two finite measures
is integrable. -/
theorem integrable_sqrt_toReal_rnDeriv_mul (P Q μ : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] :
    Integrable (fun x ↦ √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)) μ :=
  ((P.memLp_two_sqrt_toReal_rnDeriv μ).integrable_mul
    (Q.memLp_two_sqrt_toReal_rnDeriv μ)).congr <|
      ae_of_all _ fun _ ↦ (Real.sqrt_mul ENNReal.toReal_nonneg _).symm

end MeasureTheory.Measure
