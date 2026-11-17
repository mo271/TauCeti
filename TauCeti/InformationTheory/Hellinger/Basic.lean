/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.CompNotation

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.Probability.Kernel.Composition.MeasureComp
import TauCeti.MeasureTheory.Measure.Decomposition.L2
import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Hellinger affinity and squared Hellinger distance

For two measures `P` and `Q` on a measurable space `X`, the **Hellinger affinity** is
`hellingerAffinity P Q = ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal)`
integrated against `P + Q`, and the **squared Hellinger distance** is
`sqHellinger P Q = 2 * (1 - hellingerAffinity P Q)`.

With this unhalved normalization (matching Tsybakov and Samworth–Shah), for probability measures
`P` and `Q` dominated by any σ-finite measure `μ`,
`sqHellinger P Q = ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ`
takes values in `[0, 2]`, vanishes if and only if `P = Q`, attains `2` if and only if `P ⟂ₘ Q`,
and its square root `√(sqHellinger P Q)` is a metric on probability measures (the `L²` distance of
the square-root densities). Several affinity identities (`hellingerAffinity_eq_integral`,
`hellingerAffinity_withDensity`, `hellingerAffinity_self`, `hellingerAffinity_dirac_left`, and
invariance under measurable embeddings) hold more generally for σ-finite measures.

The Hellinger affinity is nondecreasing (and the squared Hellinger distance is nonincreasing) under
composition with any Markov kernel `κ` (`hellingerAffinity_le_comp`, `sqHellinger_comp_le`) and in
particular under pushforward along any almost-everywhere measurable map; measurable embeddings
preserve both with equality.

## Main definitions

* `TauCeti.hellingerAffinity`: the Hellinger affinity `∫ √(dP/d(P+Q) · dQ/d(P+Q)) d(P + Q)`.
* `TauCeti.sqHellinger`: the squared Hellinger distance `2 * (1 - hellingerAffinity P Q)`.

## Main results

* `TauCeti.hellingerAffinity_eq_integral`, `TauCeti.sqHellinger_eq_integral`: independence of the
  σ-finite dominating measure `μ`.
* `TauCeti.hellingerAffinity_eq_integral_of_ac`, `TauCeti.sqHellinger_eq_integral_of_ac`:
  `f`-divergence integral formulas when `P ≪ Q`.
* `TauCeti.hellingerAffinity_withDensity`, `TauCeti.sqHellinger_withDensity`: evaluation for
  measures given by densities with respect to a σ-finite measure.
* `TauCeti.hellingerAffinity_eq_tsum_singleton`, `TauCeti.sqHellinger_eq_tsum_singleton`:
  series formulas on countable measurable spaces with measurable singletons.
* `TauCeti.hellingerAffinity_mem_Icc`, `TauCeti.sqHellinger_mem_Icc`: bounds `[0, 1]` and `[0, 2]`
  for probability measures.
* `TauCeti.sqHellinger_eq_zero_iff`, `TauCeti.hellingerAffinity_eq_zero_iff`,
  `TauCeti.sqHellinger_eq_two_iff`: characterization of the extreme values `P = Q` and `P ⟂ₘ Q`.
* `TauCeti.sqrt_sqHellinger_triangle`: triangle inequality for `√(sqHellinger P Q)`.
* `TauCeti.hellingerAffinity_dirac_left`, `TauCeti.hellingerAffinity_dirac_right`,
  `TauCeti.sqHellinger_dirac_left`, `TauCeti.sqHellinger_dirac_right`: affinity and squared
  Hellinger distance with a Dirac mass (without assuming measurable singletons).
* `TauCeti.hellingerAffinity_le_comp`, `TauCeti.sqHellinger_comp_le`: data processing inequality
  under Markov kernels.
* `MeasurableEmbedding.hellingerAffinity_map`, `MeasurableEquiv.hellingerAffinity_map`: invariance
  under measurable embeddings and measurable equivalences.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Definition 2.3 and
  properties (i)–(iii), p. 83.
* R. J. Samworth and R. D. Shah, *Modern Statistical Methods and Theory*, Cambridge University
  Press, 2026, Lemma 8.10, p. 233 (data processing for `f`-divergences).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The **Hellinger affinity** of two measures `P` and `Q`, defined via their Radon–Nikodym
derivatives with respect to `P + Q`. For finite measures dominated by a σ-finite measure `μ`,
it equals `∫ x, √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ`. -/
def hellingerAffinity (P Q : Measure X) : ℝ :=
  ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q)

/-- Definitional unfolding of `hellingerAffinity`. -/
theorem hellingerAffinity_def (P Q : Measure X) :
    hellingerAffinity P Q =
      ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q) := (rfl)

/-- The **squared Hellinger distance** of two measures `P` and `Q`, using the unhalved
normalization `2 * (1 - hellingerAffinity P Q)`, which takes values in `[0, 2]` on probability
measures. -/
def sqHellinger (P Q : Measure X) : ℝ :=
  2 * (1 - hellingerAffinity P Q)

/-- Definitional unfolding of `sqHellinger`. -/
theorem sqHellinger_def (P Q : Measure X) :
    sqHellinger P Q = 2 * (1 - hellingerAffinity P Q) := (rfl)

/-- The Hellinger affinity is symmetric in its two measures. -/
theorem hellingerAffinity_comm (P Q : Measure X) :
    hellingerAffinity P Q = hellingerAffinity Q P := by
  simp only [hellingerAffinity_def, add_comm P Q, mul_comm]

/-- The squared Hellinger distance is symmetric in its two measures. -/
theorem sqHellinger_comm (P Q : Measure X) :
    sqHellinger P Q = sqHellinger Q P := by
  rw [sqHellinger_def, sqHellinger_def, hellingerAffinity_comm]

/-- The Hellinger affinity is always nonnegative. -/
theorem hellingerAffinity_nonneg (P Q : Measure X) : 0 ≤ hellingerAffinity P Q :=
  integral_nonneg fun _ ↦ Real.sqrt_nonneg _

/-- The squared Hellinger distance is always at most `2`. -/
theorem sqHellinger_le_two (P Q : Measure X) : sqHellinger P Q ≤ 2 := by
  rw [sqHellinger_def]
  linarith [hellingerAffinity_nonneg P Q]

/-- The Hellinger affinity with the zero measure on the left is `0`. -/
@[simp]
theorem hellingerAffinity_zero_left (Q : Measure X) : hellingerAffinity 0 Q = 0 := by
  rw [hellingerAffinity_def, zero_add]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [Measure.rnDeriv_zero Q] with x hx
  simp [hx]

/-- The Hellinger affinity with the zero measure on the right is `0`. -/
@[simp]
theorem hellingerAffinity_zero_right (P : Measure X) : hellingerAffinity P 0 = 0 := by
  rw [hellingerAffinity_comm, hellingerAffinity_zero_left]

/-- The squared Hellinger distance with the zero measure on the left is `2`. -/
@[simp]
theorem sqHellinger_zero_left (Q : Measure X) : sqHellinger 0 Q = 2 := by
  simp [sqHellinger_def]

/-- The squared Hellinger distance with the zero measure on the right is `2`. -/
@[simp]
theorem sqHellinger_zero_right (P : Measure X) : sqHellinger P 0 = 2 := by
  simp [sqHellinger_def]

section DominatingMeasure

/-- **Independence of the dominating measure for the Hellinger affinity.** For σ-finite measures
`P` and `Q` dominated by a σ-finite measure `μ`, the Hellinger affinity is computed by integrating
`√((P.rnDeriv μ).toReal * (Q.rnDeriv μ).toReal)` against `μ`. -/
theorem hellingerAffinity_eq_integral (P Q μ : Measure X) [SigmaFinite P] [SigmaFinite Q]
    [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    hellingerAffinity P Q =
      ∫ x, √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ := by
  rw [hellingerAffinity_def]
  set ν := P + Q
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hνμ : ν ≪ μ := hP.add_left hQ
  rw [← integral_toReal_rnDeriv_mul hνμ]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_mul_rnDeriv hPν (κ := μ),
    Measure.rnDeriv_mul_rnDeriv hQν (κ := μ)] with x hPx hQx
  rw [← hPx, ← hQx, Pi.mul_apply, Pi.mul_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hnonneg : 0 ≤ (ν.rnDeriv μ x).toReal := ENNReal.toReal_nonneg
  calc
    (ν.rnDeriv μ x).toReal * √((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal)
        = √((ν.rnDeriv μ x).toReal ^ 2) *
            √((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal) := by
          rw [Real.sqrt_sq hnonneg]
    _ = √((ν.rnDeriv μ x).toReal ^ 2 * ((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal)) := by
          rw [← Real.sqrt_mul (sq_nonneg _)]
    _ = √((P.rnDeriv ν x).toReal * (ν.rnDeriv μ x).toReal *
          ((Q.rnDeriv ν x).toReal * (ν.rnDeriv μ x).toReal)) := by ring_nf

/-- When `P ≪ Q`, the Hellinger affinity of σ-finite measures `P` and `Q` equals
`∫ x, √(P.rnDeriv Q x).toReal ∂Q`. -/
theorem hellingerAffinity_eq_integral_of_ac (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q]
    (hPQ : P ≪ Q) :
    hellingerAffinity P Q = ∫ x, √(P.rnDeriv Q x).toReal ∂Q := by
  rw [hellingerAffinity_eq_integral P Q Q hPQ Measure.AbsolutelyContinuous.rfl]
  refine integral_congr_ae ?_
  filter_upwards [Q.rnDeriv_self] with x hx
  simp [hx]

/-- The Hellinger affinity of two σ-finite measures given by densities with respect to a σ-finite
measure `μ`. -/
theorem hellingerAffinity_withDensity (μ : Measure X) [SigmaFinite μ] {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    [SigmaFinite (μ.withDensity f)] [SigmaFinite (μ.withDensity g)] :
    hellingerAffinity (μ.withDensity f) (μ.withDensity g) =
      ∫ x, √((f x).toReal * (g x).toReal) ∂μ := by
  rw [hellingerAffinity_eq_integral _ _ μ (withDensity_absolutelyContinuous μ f)
    (withDensity_absolutelyContinuous μ g)]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity₀ μ hf, Measure.rnDeriv_withDensity₀ μ hg] with
    x hfx hgx
  rw [hfx, hgx]

/-- The Hellinger affinity of a σ-finite measure with itself equals its real total mass
(`0` if `P Set.univ = ∞`). -/
@[simp]
theorem hellingerAffinity_self (P : Measure X) [SigmaFinite P] :
    hellingerAffinity P P = P.real Set.univ := by
  rw [hellingerAffinity_eq_integral_of_ac P P Measure.AbsolutelyContinuous.rfl]
  have h1 : ∀ᵐ x ∂P, √(P.rnDeriv P x).toReal = 1 := by
    filter_upwards [P.rnDeriv_self] with x hx
    simp [hx]
  rw [integral_congr_ae h1, integral_const, smul_eq_mul, mul_one]

/-- The squared Hellinger distance from a probability measure to itself is `0`. -/
@[simp]
theorem sqHellinger_self (P : Measure X) [IsProbabilityMeasure P] :
    sqHellinger P P = 0 := by
  simp [sqHellinger_def]

/-- **Independence of the dominating measure for the squared Hellinger distance.** For probability
measures `P` and `Q` dominated by a σ-finite measure `μ`, the squared Hellinger distance is the
`L²(μ)` squared distance between the square roots of their Radon–Nikodym derivatives. -/
theorem sqHellinger_eq_integral (P Q μ : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    sqHellinger P Q =
      ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ := by
  have hp : Integrable (fun x ↦ (P.rnDeriv μ x).toReal) μ := Measure.integrable_toReal_rnDeriv
  have hq : Integrable (fun x ↦ (Q.rnDeriv μ x).toReal) μ := Measure.integrable_toReal_rnDeriv
  have hpq : Integrable (fun x ↦ √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)) μ :=
    P.integrable_sqrt_toReal_rnDeriv_mul Q μ
  have hexpand : ∀ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 =
      (P.rnDeriv μ x).toReal + (Q.rnDeriv μ x).toReal -
        2 * √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) := fun x ↦ by
    rw [sub_sq, Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg,
      Real.sqrt_mul ENNReal.toReal_nonneg]
    ring
  simp_rw [hexpand]
  rw [integral_sub (hp.fun_add hq) (hpq.const_mul 2), integral_add hp hq, integral_const_mul,
    Measure.integral_toReal_rnDeriv hP, Measure.integral_toReal_rnDeriv hQ,
    ← hellingerAffinity_eq_integral P Q μ hP hQ, sqHellinger_def]
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one]
  ring

/-- When `P ≪ Q`, the squared Hellinger distance of two probability measures is the `f`-divergence
integral `∫ x, (√(P.rnDeriv Q x).toReal - 1) ^ 2 ∂Q`. -/
theorem sqHellinger_eq_integral_of_ac (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    sqHellinger P Q = ∫ x, (√(P.rnDeriv Q x).toReal - 1) ^ 2 ∂Q := by
  rw [sqHellinger_eq_integral P Q Q hPQ Measure.AbsolutelyContinuous.rfl]
  refine integral_congr_ae ?_
  filter_upwards [Q.rnDeriv_self] with x hx
  simp [hx]

/-- The squared Hellinger distance of two probability measures given by densities with respect to
a σ-finite measure `μ`. -/
theorem sqHellinger_withDensity (μ : Measure X) [SigmaFinite μ] {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    [IsProbabilityMeasure (μ.withDensity f)] [IsProbabilityMeasure (μ.withDensity g)] :
    sqHellinger (μ.withDensity f) (μ.withDensity g) =
      ∫ x, (√(f x).toReal - √(g x).toReal) ^ 2 ∂μ := by
  rw [sqHellinger_eq_integral _ _ μ (withDensity_absolutelyContinuous μ f)
    (withDensity_absolutelyContinuous μ g)]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity₀ μ hf, Measure.rnDeriv_withDensity₀ μ hg] with
    x hfx hgx
  rw [hfx, hgx]

/-- On a countable space with measurable singletons, the Hellinger affinity of two finite measures
equals the series `∑' x, √(P.real {x} * Q.real {x})`. -/
theorem hellingerAffinity_eq_tsum_singleton (P Q : Measure X) [Countable X]
    [MeasurableSingletonClass X] [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q = ∑' x, √(P.real {x} * Q.real {x}) := by
  rw [hellingerAffinity_def]
  set ν := P + Q
  rw [integral_countable (P.integrable_sqrt_toReal_rnDeriv_mul Q ν)]
  refine tsum_congr fun x ↦ ?_
  by_cases hν : ν {x} = 0
  · have hP : P {x} = 0 := by
      have : P {x} + Q {x} = 0 := by simpa [ν] using hν
      exact (add_eq_zero.1 this).1
    simp [Measure.real_def, hν, hP]
  · have hν_fin : ν {x} ≠ ∞ := measure_ne_top ν {x}
    have hν_pos : 0 < ν.real {x} := ENNReal.toReal_pos hν hν_fin
    rw [Measure.rnDeriv_eq_measure_singleton_div hν hν_fin,
      Measure.rnDeriv_eq_measure_singleton_div hν hν_fin,
      ENNReal.toReal_div, ENNReal.toReal_div, smul_eq_mul,
      ← Measure.real_def, ← Measure.real_def, ← Measure.real_def]
    have hfrac : P.real {x} / ν.real {x} * (Q.real {x} / ν.real {x}) =
        P.real {x} * Q.real {x} / (ν.real {x}) ^ 2 := by ring
    rw [hfrac, Real.sqrt_div (mul_nonneg measureReal_nonneg measureReal_nonneg),
      Real.sqrt_sq hν_pos.le, mul_div_cancel₀ _ hν_pos.ne']

/-- On a countable space with measurable singletons, the squared Hellinger distance of two
probability measures equals the series `∑' x, (√(P.real {x}) - √(Q.real {x})) ^ 2`. -/
theorem sqHellinger_eq_tsum_singleton (P Q : Measure X) [Countable X]
    [MeasurableSingletonClass X] [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    sqHellinger P Q = ∑' x, (√(P.real {x}) - √(Q.real {x})) ^ 2 := by
  set ν := P + Q
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hint : Integrable (fun x ↦ (√(P.rnDeriv ν x).toReal - √(Q.rnDeriv ν x).toReal) ^ 2) ν :=
    ((P.memLp_two_sqrt_toReal_rnDeriv ν).sub (Q.memLp_two_sqrt_toReal_rnDeriv ν)).integrable_sq
  rw [sqHellinger_eq_integral P Q ν hPν hQν, integral_countable hint]
  refine tsum_congr fun x ↦ ?_
  by_cases hν : ν {x} = 0
  · have hPQ : P {x} = 0 ∧ Q {x} = 0 := by
      have : P {x} + Q {x} = 0 := by simpa [ν] using hν
      exact add_eq_zero.1 this
    simp [Measure.real_def, hν, hPQ.1, hPQ.2]
  · have hν_fin : ν {x} ≠ ∞ := measure_ne_top ν {x}
    have hν_pos : 0 < ν.real {x} := ENNReal.toReal_pos hν hν_fin
    rw [Measure.rnDeriv_eq_measure_singleton_div hν hν_fin,
      Measure.rnDeriv_eq_measure_singleton_div hν hν_fin,
      ENNReal.toReal_div, ENNReal.toReal_div, smul_eq_mul,
      ← Measure.real_def, ← Measure.real_def, ← Measure.real_def,
      Real.sqrt_div measureReal_nonneg, Real.sqrt_div measureReal_nonneg,
      ← sub_div, div_pow, Real.sq_sqrt hν_pos.le, mul_div_cancel₀ _ hν_pos.ne']

end DominatingMeasure

section BoundsAndMetric

/-- Cauchy–Schwarz bound for the Hellinger affinity of two finite measures. -/
theorem hellingerAffinity_le_sqrt_mul (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q ≤ √(P.real Set.univ * Q.real Set.univ) := by
  set ν := P + Q
  have hP : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) Real.HolderConjugate.two_two
    (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _) (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _)
    (by simpa using P.memLp_two_sqrt_toReal_rnDeriv ν)
    (by simpa using Q.memLp_two_sqrt_toReal_rnDeriv ν)
  have hLHS : hellingerAffinity P Q =
      ∫ x, √(P.rnDeriv ν x).toReal * √(Q.rnDeriv ν x).toReal ∂ν := by
    rw [hellingerAffinity_def]
    simp_rw [Real.sqrt_mul ENNReal.toReal_nonneg]
    rfl
  rw [hLHS]
  refine hcs.trans_eq ?_
  have hsq : ∀ (R : Measure X) [IsFiniteMeasure R], R ≪ ν →
      ∫ x, √(R.rnDeriv ν x).toReal ^ (2 : ℝ) ∂ν = R.real Set.univ := fun R _ hR ↦ by
    simp_rw [Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg]
    exact Measure.integral_toReal_rnDeriv hR
  rw [hsq P hP, hsq Q hQ, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul measureReal_nonneg]

/-- The Hellinger affinity of two probability measures is at most `1`. -/
theorem hellingerAffinity_le_one (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    hellingerAffinity P Q ≤ 1 := by
  simpa using hellingerAffinity_le_sqrt_mul P Q

/-- The Hellinger affinity of two probability measures lies in `[0, 1]`. -/
theorem hellingerAffinity_mem_Icc (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    hellingerAffinity P Q ∈ Icc 0 1 :=
  ⟨hellingerAffinity_nonneg P Q, hellingerAffinity_le_one P Q⟩

/-- The squared Hellinger distance of two probability measures is nonnegative. -/
theorem sqHellinger_nonneg (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ sqHellinger P Q := by
  rw [sqHellinger_def]
  linarith [hellingerAffinity_le_one P Q]

/-- The squared Hellinger distance of two probability measures lies in `[0, 2]`. -/
theorem sqHellinger_mem_Icc (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    sqHellinger P Q ∈ Icc 0 2 :=
  ⟨sqHellinger_nonneg P Q, sqHellinger_le_two P Q⟩

/-- The squared Hellinger distance of two probability measures vanishes if and only if they are
equal. -/
@[simp]
theorem sqHellinger_eq_zero_iff (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    sqHellinger P Q = 0 ↔ P = Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact sqHellinger_self P⟩
  set ν := P + Q
  have hP : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [sqHellinger_eq_integral P Q ν hP hQ] at h
  have hint : Integrable (fun x ↦ (√(P.rnDeriv ν x).toReal - √(Q.rnDeriv ν x).toReal) ^ 2) ν :=
    ((P.memLp_two_sqrt_toReal_rnDeriv ν).sub (Q.memLp_two_sqrt_toReal_rnDeriv ν)).integrable_sq
  have hae : (fun x ↦ (√(P.rnDeriv ν x).toReal - √(Q.rnDeriv ν x).toReal) ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _) hint).1 h
  have hrn : P.rnDeriv ν =ᵐ[ν] Q.rnDeriv ν := by
    filter_upwards [hae, Measure.rnDeriv_lt_top P ν, Measure.rnDeriv_lt_top Q ν] with x hx hPx hQx
    have hsqrt : √(P.rnDeriv ν x).toReal = √(Q.rnDeriv ν x).toReal :=
      sub_eq_zero.1 (sq_eq_zero_iff.1 hx)
    have htoReal : (P.rnDeriv ν x).toReal = (Q.rnDeriv ν x).toReal := by
      have := congrArg (· ^ 2) hsqrt
      simpa [Real.sq_sqrt ENNReal.toReal_nonneg] using this
    exact (ENNReal.toReal_eq_toReal_iff' hPx.ne hQx.ne).1 htoReal
  calc
    P = ν.withDensity (P.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq P ν hP).symm
    _ = ν.withDensity (Q.rnDeriv ν) := withDensity_congr_ae hrn
    _ = Q := Measure.withDensity_rnDeriv_eq Q ν hQ

/-- The Hellinger affinity of two probability measures equals `1` if and only if they are equal. -/
@[simp]
theorem hellingerAffinity_eq_one_iff (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    hellingerAffinity P Q = 1 ↔ P = Q := by
  rw [← sqHellinger_eq_zero_iff, sqHellinger_def]
  constructor <;> intro h <;> linarith

/-- The Hellinger affinity of two finite measures vanishes if and only if they are mutually
singular. -/
@[simp]
theorem hellingerAffinity_eq_zero_iff (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q = 0 ↔ P ⟂ₘ Q := by
  set ν := P + Q
  have hP : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [hellingerAffinity_def, integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _) (P.integrable_sqrt_toReal_rnDeriv_mul Q ν)]
  constructor
  · intro hae
    refine ⟨P.rnDeriv ν ⁻¹' {0},
      (Measure.measurable_rnDeriv P ν) (measurableSet_singleton 0), ?_, ?_⟩
    · rw [← Measure.setLIntegral_rnDeriv hP]
      exact setLIntegral_eq_zero ((Measure.measurable_rnDeriv P ν) (measurableSet_singleton 0))
        fun x hx ↦ hx
    · rw [← Measure.setLIntegral_rnDeriv hQ,
        setLIntegral_eq_zero_iff
          ((Measure.measurable_rnDeriv P ν) (measurableSet_singleton 0)).compl
          (Measure.measurable_rnDeriv Q ν)]
      filter_upwards [hae, Measure.rnDeriv_lt_top P ν, Measure.rnDeriv_lt_top Q ν] with
        x hx hPx hQx hxP
      have hmul : (P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal = 0 :=
        (Real.sqrt_eq_zero (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).1 hx
      rcases mul_eq_zero.1 hmul with h0 | h0
      · exact absurd (((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right hPx.ne) hxP
      · exact ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right hQx.ne
  · intro hsing
    filter_upwards [Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := ν) hsing.measure_nullSet,
      Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := ν) hsing.measure_compl_nullSet] with
      x hxP hxQ
    by_cases hx : x ∈ hsing.nullSet
    · simp [hxP hx]
    · simp [hxQ hx]

/-- The squared Hellinger distance of two finite measures equals `2` if and only if they are
mutually singular. -/
@[simp]
theorem sqHellinger_eq_two_iff (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    sqHellinger P Q = 2 ↔ P ⟂ₘ Q := by
  rw [← hellingerAffinity_eq_zero_iff, sqHellinger_def]
  constructor <;> intro h <;> linarith

/-- **Triangle inequality for the Hellinger distance.** For probability measures `P`, `Q`, and `R`,
`√(sqHellinger P R) ≤ √(sqHellinger P Q) + √(sqHellinger Q R)`. -/
theorem sqrt_sqHellinger_triangle (P Q R : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    √(sqHellinger P R) ≤ √(sqHellinger P Q) + √(sqHellinger Q R) := by
  set μ := P + Q + R
  have hP : P ≪ μ := (Measure.AbsolutelyContinuous.rfl.add_right Q).add_right R
  have hQ : Q ≪ μ := (Measure.AbsolutelyContinuous.rfl.add_right' P).add_right R
  have hR : R ≪ μ := Measure.AbsolutelyContinuous.rfl.add_right' (P + Q)
  let fp : X → ℝ := fun x ↦ √(P.rnDeriv μ x).toReal
  let fq : X → ℝ := fun x ↦ √(Q.rnDeriv μ x).toReal
  let fr : X → ℝ := fun x ↦ √(R.rnDeriv μ x).toReal
  have hfp : MemLp fp 2 μ := P.memLp_two_sqrt_toReal_rnDeriv μ
  have hfq : MemLp fq 2 μ := Q.memLp_two_sqrt_toReal_rnDeriv μ
  have hfr : MemLp fr 2 μ := R.memLp_two_sqrt_toReal_rnDeriv μ
  have heq : ∀ (A B : Measure X) [IsProbabilityMeasure A] [IsProbabilityMeasure B],
      A ≪ μ → B ≪ μ →
      √(sqHellinger A B) =
        (eLpNorm (fun x ↦ √(A.rnDeriv μ x).toReal - √(B.rnDeriv μ x).toReal) 2 μ).toReal := by
    intro A B _ _ hA hB
    have hmeas : AEStronglyMeasurable
        (fun x ↦ √(A.rnDeriv μ x).toReal - √(B.rnDeriv μ x).toReal) μ :=
      ((A.memLp_two_sqrt_toReal_rnDeriv μ).sub
        (B.memLp_two_sqrt_toReal_rnDeriv μ)).aestronglyMeasurable
    rw [sqHellinger_eq_integral A B μ hA hB,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) ENNReal.ofNat_ne_top hmeas]
    have hint : Integrable (fun x ↦ (√(A.rnDeriv μ x).toReal - √(B.rnDeriv μ x).toReal) ^ 2) μ :=
      ((A.memLp_two_sqrt_toReal_rnDeriv μ).sub (B.memLp_two_sqrt_toReal_rnDeriv μ)).integrable_sq
    have hlin : ∫⁻ x, ‖√(A.rnDeriv μ x).toReal - √(B.rnDeriv μ x).toReal‖ₑ ^ (2 : ℝ) ∂μ =
        ENNReal.ofReal (∫ x, (√(A.rnDeriv μ x).toReal - √(B.rnDeriv μ x).toReal) ^ 2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _)]
      refine lintegral_congr fun x ↦ ?_
      rw [Real.eNorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    simp only [ENNReal.toReal_ofNat]
    rw [hlin, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _),
      ← Real.sqrt_eq_rpow]
  rw [heq P R hP hR, heq P Q hP hQ, heq Q R hQ hR]
  have hsub : (fun x ↦ fp x - fr x) = (fun x ↦ fp x - fq x) + (fun x ↦ fq x - fr x) := by
    ext x; simp [Pi.add_apply]
  rw [hsub]
  have htri : eLpNorm ((fun x ↦ fp x - fq x) + (fun x ↦ fq x - fr x)) 2 μ ≤
      eLpNorm (fun x ↦ fp x - fq x) 2 μ + eLpNorm (fun x ↦ fq x - fr x) 2 μ :=
    eLpNorm_add_le (by norm_num)
  have hfin1 : eLpNorm (fun x ↦ fp x - fq x) 2 μ ≠ ∞ := (hfp.sub hfq).eLpNorm_ne_top
  have hfin2 : eLpNorm (fun x ↦ fq x - fr x) 2 μ ≠ ∞ := (hfq.sub hfr).eLpNorm_ne_top
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) htri).trans_eq
    (ENNReal.toReal_add hfin1 hfin2)

/-- The Hellinger affinity of a Dirac mass at `a` with any σ-finite measure `Q` is `√(Q.real {a})`.
No `MeasurableSingletonClass` assumption is required; `Q.real {a}` is the outer-measure mass of
the singleton `{a}`. -/
@[simp]
theorem hellingerAffinity_dirac_left (a : X) (Q : Measure X) [SigmaFinite Q] :
    hellingerAffinity (Measure.dirac a) Q = √(Q.real {a}) := by
  set P := Measure.dirac a
  set ν := P + Q
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  let g : X → ℝ := fun x ↦ √((Q.rnDeriv ν x).toReal / (P.rnDeriv ν x).toReal)
  have hgm : Measurable g :=
    ((Measure.measurable_rnDeriv Q ν).ennreal_toReal.div
      (Measure.measurable_rnDeriv P ν).ennreal_toReal).sqrt
  have hpt : ∀ x, √((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal) =
      (P.rnDeriv ν x).toReal * g x := fun x ↦ by
    by_cases hp : (P.rnDeriv ν x).toReal = 0
    · simp [hp]
    · have hp_pos : 0 < (P.rnDeriv ν x).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp)
      dsimp only [g]
      calc
        √((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal)
            = √((P.rnDeriv ν x).toReal ^ 2 * ((Q.rnDeriv ν x).toReal / (P.rnDeriv ν x).toReal)) :=
              by field_simp
        _ = (P.rnDeriv ν x).toReal * √((Q.rnDeriv ν x).toReal / (P.rnDeriv ν x).toReal) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp_pos.le]
  have hνa_pos : ν {a} ≠ 0 := by simp [ν, P]
  have hνa_fin : ν {a} ≠ ∞ := measure_singleton_lt_top.ne
  have hνreal_pos : 0 < ν.real {a} := ENNReal.toReal_pos hνa_pos hνa_fin
  calc
    hellingerAffinity P Q
        = ∫ x, (P.rnDeriv ν x).toReal * g x ∂ν := by
          rw [hellingerAffinity_def]
          exact integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ x, g x ∂P := integral_toReal_rnDeriv_mul hPν
    _ = g a := integral_dirac' g a hgm.stronglyMeasurable
    _ = √(Q.real {a}) := by
          dsimp only [g]
          rw [Measure.rnDeriv_eq_measure_singleton_div hνa_pos hνa_fin,
            Measure.rnDeriv_eq_measure_singleton_div hνa_pos hνa_fin,
            ENNReal.toReal_div, ENNReal.toReal_div]
          have hPa : (P {a}).toReal = 1 := by simp [P]
          rw [hPa, ← Measure.real_def, ← Measure.real_def,
            div_div_div_cancel_right₀ hνreal_pos.ne', div_one]

/-- The Hellinger affinity of any σ-finite measure `P` with a Dirac mass at `a` is `√(P.real {a})`.
-/
@[simp]
theorem hellingerAffinity_dirac_right (P : Measure X) [SigmaFinite P] (a : X) :
    hellingerAffinity P (Measure.dirac a) = √(P.real {a}) := by
  rw [hellingerAffinity_comm, hellingerAffinity_dirac_left]

/-- The squared Hellinger distance between a Dirac mass at `a` and any σ-finite measure `Q` is
`2 * (1 - √(Q.real {a}))`. -/
@[simp]
theorem sqHellinger_dirac_left (a : X) (Q : Measure X) [SigmaFinite Q] :
    sqHellinger (Measure.dirac a) Q = 2 * (1 - √(Q.real {a})) := by
  rw [sqHellinger_def, hellingerAffinity_dirac_left]

/-- The squared Hellinger distance between any σ-finite measure `P` and a Dirac mass at `a` is
`2 * (1 - √(P.real {a}))`. -/
@[simp]
theorem sqHellinger_dirac_right (P : Measure X) [SigmaFinite P] (a : X) :
    sqHellinger P (Measure.dirac a) = 2 * (1 - √(P.real {a})) := by
  rw [sqHellinger_def, hellingerAffinity_dirac_right]

end BoundsAndMetric

section DataProcessing

/-- Pointwise regularization bound for the balanced AM–GM weight used in data processing. -/
private theorem regularized_amgm_bound {p q ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hε : 0 < ε) :
    √((q + ε) / (p + ε)) * p + (√((q + ε) / (p + ε)))⁻¹ * q ≤
      2 * (√(p * q) + √(2 * ε) + ε) := by
  have hp_pos : 0 < p + ε := by linarith
  have hq_pos : 0 < q + ε := by linarith
  set t := √((q + ε) / (p + ε))
  have ht_pos : 0 < t := Real.sqrt_pos.2 (div_pos hq_pos hp_pos)
  have ht_eq : t = √(q + ε) / √(p + ε) := Real.sqrt_div hq_pos.le _
  have hterm1 : t * p ≤ √((p + ε) * (q + ε)) := by
    have : t * (p + ε) = √((p + ε) * (q + ε)) := by
      rw [ht_eq, Real.sqrt_mul hp_pos.le, div_mul_eq_mul_div,
        div_eq_iff (Real.sqrt_pos.2 hp_pos).ne']
      calc √(q + ε) * (p + ε)
          = √(q + ε) * (√(p + ε) * √(p + ε)) := by rw [Real.mul_self_sqrt hp_pos.le]
        _ = √(p + ε) * √(q + ε) * √(p + ε) := by ring
    nlinarith
  have hterm2 : t⁻¹ * q ≤ √((p + ε) * (q + ε)) := by
    have : t⁻¹ * (q + ε) = √((p + ε) * (q + ε)) := by
      rw [ht_eq, inv_div, Real.sqrt_mul hp_pos.le, div_mul_eq_mul_div,
        div_eq_iff (Real.sqrt_pos.2 hq_pos).ne']
      calc √(p + ε) * (q + ε)
          = √(p + ε) * (√(q + ε) * √(q + ε)) := by rw [Real.mul_self_sqrt hq_pos.le]
        _ = √(p + ε) * √(q + ε) * √(q + ε) := by ring
    nlinarith [inv_pos.2 ht_pos]
  have hreg : √((p + ε) * (q + ε)) ≤ √(p * q) + √(2 * ε) + ε := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h1 : (p + q) * ε ≤ 2 * ε := by nlinarith
    have h2 : 0 ≤ 2 * √(p * q) * (√(2 * ε) + ε) + 2 * √(2 * ε) * ε := by positivity
    have hsq2 : √(2 * ε) ^ 2 = 2 * ε := Real.sq_sqrt (by positivity)
    have hsqpq : √(p * q) ^ 2 = p * q := Real.sq_sqrt (mul_nonneg hp0 hq0)
    nlinarith
  linarith

/-- Fiberwise AM–GM upper bound for `2 * hellingerAffinity P Q` integrated against the Markov
kernel `κ`. -/
private theorem two_mul_hellingerAffinity_le_lintegral_kernel (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] {t : Y → ℝ}
    (ht_meas : Measurable t) (ht_pos : ∀ y, 0 < t y) :
    2 * ENNReal.ofReal (hellingerAffinity P Q) ≤
      ∫⁻ x, P.rnDeriv (P + Q) x * ∫⁻ y, ENNReal.ofReal (t y) ∂(κ x) ∂(P + Q) +
        ∫⁻ x, Q.rnDeriv (P + Q) x * ∫⁻ y, ENNReal.ofReal ((t y)⁻¹) ∂(κ x) ∂(P + Q) := by
  set ν := P + Q
  have ht_inv : Measurable fun y ↦ (t y)⁻¹ := ht_meas.inv
  have hPmeas : Measurable fun x ↦ P.rnDeriv ν x * ∫⁻ y, ENNReal.ofReal (t y) ∂(κ x) :=
    (Measure.measurable_rnDeriv P ν).mul
      (Measurable.lintegral_kernel_prod_right' (ht_meas.ennreal_ofReal.comp measurable_snd))
  have hsqrt_meas : Measurable fun x ↦
      ENNReal.ofReal (√((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal)) :=
    (((Measure.measurable_rnDeriv P ν).ennreal_toReal.mul
      (Measure.measurable_rnDeriv Q ν).ennreal_toReal).sqrt).ennreal_ofReal
  rw [hellingerAffinity_def,
    ofReal_integral_eq_lintegral_ofReal (P.integrable_sqrt_toReal_rnDeriv_mul Q ν)
      (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _),
    ← lintegral_const_mul _ hsqrt_meas, ← lintegral_add_left hPmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top P ν, Measure.rnDeriv_lt_top Q ν] with x hPx hQx
  have hconst : 2 * ENNReal.ofReal (√((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal)) =
      ∫⁻ _ : Y, 2 * ENNReal.ofReal
        (√((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal)) ∂(κ x) := by simp
  have htP_meas : Measurable fun y ↦ P.rnDeriv ν x * ENNReal.ofReal (t y) :=
    ht_meas.ennreal_ofReal.const_mul _
  rw [hconst, ← lintegral_const_mul _ ht_meas.ennreal_ofReal,
    ← lintegral_const_mul _ ht_inv.ennreal_ofReal, ← lintegral_add_left htP_meas]
  refine lintegral_mono fun y ↦ ?_
  rw [← ENNReal.ofReal_toReal hPx.ne, ← ENNReal.ofReal_toReal hQx.ne,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg (ht_pos y).le)
      (mul_nonneg ENNReal.toReal_nonneg (inv_nonneg.2 (ht_pos y).le)),
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  have ham := two_mul_le_add_sq (√(t y * (P.rnDeriv ν x).toReal))
    (√((t y)⁻¹ * (Q.rnDeriv ν x).toReal))
  have hmul : √(t y * (P.rnDeriv ν x).toReal) * √((t y)⁻¹ * (Q.rnDeriv ν x).toReal) =
      √((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal) := by
    rw [← Real.sqrt_mul (mul_nonneg (ht_pos y).le ENNReal.toReal_nonneg)]
    congr 1; field_simp [(ht_pos y).ne']
  rw [mul_assoc 2, hmul, Real.sq_sqrt (mul_nonneg (ht_pos y).le ENNReal.toReal_nonneg),
    Real.sq_sqrt (mul_nonneg (inv_nonneg.2 (ht_pos y).le) ENNReal.toReal_nonneg)] at ham
  linarith

/-- One-step AM–GM upper bound for `2 * hellingerAffinity P Q` using an arbitrary positive
measurable weight `t` on the target space `Y`. -/
private theorem two_mul_hellingerAffinity_le_lintegral (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] {t : Y → ℝ}
    (ht_meas : Measurable t) (ht_pos : ∀ y, 0 < t y) :
    2 * ENNReal.ofReal (hellingerAffinity P Q) ≤
      ∫⁻ y, ENNReal.ofReal (t y) * (κ ∘ₘ P).rnDeriv (κ ∘ₘ P + κ ∘ₘ Q) y ∂(κ ∘ₘ P + κ ∘ₘ Q) +
        ∫⁻ y, ENNReal.ofReal ((t y)⁻¹) *
          (κ ∘ₘ Q).rnDeriv (κ ∘ₘ P + κ ∘ₘ Q) y ∂(κ ∘ₘ P + κ ∘ₘ Q) := by
  set ν := P + Q
  have ht_inv : Measurable fun y ↦ (t y)⁻¹ := ht_meas.inv
  have htransfer : ∀ (R : Measure X) [IsFiniteMeasure R] (_ : R ≪ ν) {g : Y → ℝ≥0∞},
      Measurable g →
      ∫⁻ x, R.rnDeriv ν x * ∫⁻ y, g y ∂(κ x) ∂ν =
        ∫⁻ y, (κ ∘ₘ R).rnDeriv (κ ∘ₘ P + κ ∘ₘ Q) y * g y ∂(κ ∘ₘ P + κ ∘ₘ Q) := by
    intro R _ hR g hg
    rw [← Measure.comp_add]
    calc
      ∫⁻ x, R.rnDeriv ν x * ∫⁻ y, g y ∂(κ x) ∂ν
          = ∫⁻ x, ∫⁻ y, g y ∂(κ x) ∂R :=
            lintegral_rnDeriv_mul hR
              (Measurable.lintegral_kernel_prod_right' (hg.comp measurable_snd)).aemeasurable
      _ = ∫⁻ y, g y ∂(κ ∘ₘ R) := (Measure.lintegral_bind κ.aemeasurable hg.aemeasurable).symm
      _ = ∫⁻ y, (κ ∘ₘ R).rnDeriv (κ ∘ₘ ν) y * g y ∂(κ ∘ₘ ν) :=
          (lintegral_rnDeriv_mul (hR.comp_right κ) hg.aemeasurable).symm
  refine (two_mul_hellingerAffinity_le_lintegral_kernel P Q κ ht_meas ht_pos).trans_eq ?_
  rw [htransfer P (Measure.AbsolutelyContinuous.rfl.add_right Q) ht_meas.ennreal_ofReal,
    htransfer Q (Measure.AbsolutelyContinuous.rfl.add_right' P) ht_inv.ennreal_ofReal]
  simp_rw [mul_comm]

/-- Integral bound for the regularized AM–GM weight `√((dQ'/dν' + ε) / (dP'/dν' + ε))`. -/
private theorem lintegral_regularized_weight_le (P' Q' : Measure Y) [IsFiniteMeasure P']
    [IsFiniteMeasure Q'] {ε : ℝ} (hε : 0 < ε) :
    let ν' := P' + Q'
    let t : Y → ℝ := fun y ↦ √(((Q'.rnDeriv ν' y).toReal + ε) / ((P'.rnDeriv ν' y).toReal + ε))
    ∫⁻ y, ENNReal.ofReal (t y) * P'.rnDeriv ν' y ∂ν' +
        ∫⁻ y, ENNReal.ofReal ((t y)⁻¹) * Q'.rnDeriv ν' y ∂ν' ≤
      2 * ENNReal.ofReal (hellingerAffinity P' Q') +
        ENNReal.ofReal (2 * (√(2 * ε) + ε)) * ν' Set.univ := by
  intro ν' t
  have ht_pos (y : Y) : 0 < t y :=
    Real.sqrt_pos.2 (div_pos (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε)
      (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε))
  have ht_meas : Measurable t :=
    ((((Measure.measurable_rnDeriv Q' ν').ennreal_toReal.add measurable_const).div
      ((Measure.measurable_rnDeriv P' ν').ennreal_toReal.add measurable_const)).sqrt)
  have hRHS_meas : Measurable fun y ↦
      ENNReal.ofReal (√((P'.rnDeriv ν' y).toReal * (Q'.rnDeriv ν' y).toReal)) :=
    (((Measure.measurable_rnDeriv P' ν').ennreal_toReal.mul
      (Measure.measurable_rnDeriv Q' ν').ennreal_toReal).sqrt).ennreal_ofReal
  have hLHS_meas : Measurable fun y ↦ ENNReal.ofReal (t y) * P'.rnDeriv ν' y :=
    ht_meas.ennreal_ofReal.mul (Measure.measurable_rnDeriv P' ν')
  have h2RHS_meas : Measurable fun y ↦
      2 * ENNReal.ofReal (√((P'.rnDeriv ν' y).toReal * (Q'.rnDeriv ν' y).toReal)) :=
    hRHS_meas.const_mul 2
  rw [← lintegral_add_left hLHS_meas, hellingerAffinity_def,
    ofReal_integral_eq_lintegral_ofReal (P'.integrable_sqrt_toReal_rnDeriv_mul Q' ν')
      (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _),
    ← lintegral_const_mul _ hRHS_meas, ← lintegral_const (ENNReal.ofReal (2 * (√(2 * ε) + ε))),
    ← lintegral_add_left h2RHS_meas]
  refine lintegral_mono_ae ?_
  filter_upwards [Measure.rnDeriv_le_one_of_le (Measure.le_add_right le_rfl : P' ≤ ν'),
    Measure.rnDeriv_le_one_of_le (Measure.le_add_left le_rfl : Q' ≤ ν'),
    Measure.rnDeriv_lt_top P' ν', Measure.rnDeriv_lt_top Q' ν'] with y hP1 hQ1 hPfin hQfin
  have hp1 : (P'.rnDeriv ν' y).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hP1
  have hq1 : (Q'.rnDeriv ν' y).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hQ1
  rw [← ENNReal.ofReal_toReal hPfin.ne, ← ENNReal.ofReal_toReal hQfin.ne,
    ← ENNReal.ofReal_mul (ht_pos y).le, ← ENNReal.ofReal_mul (inv_nonneg.2 (ht_pos y).le),
    ← ENNReal.ofReal_add (mul_nonneg (ht_pos y).le ENNReal.toReal_nonneg)
      (mul_nonneg (inv_nonneg.2 (ht_pos y).le) ENNReal.toReal_nonneg),
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  linarith [regularized_amgm_bound ENNReal.toReal_nonneg hp1 ENNReal.toReal_nonneg hq1 hε]

/-- **Data processing inequality for the Hellinger affinity.** Composing two finite measures with a
Markov kernel does not decrease their Hellinger affinity. -/
theorem hellingerAffinity_le_comp (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    hellingerAffinity P Q ≤ hellingerAffinity (κ ∘ₘ P) (κ ∘ₘ Q) := by
  set P' := κ ∘ₘ P
  set Q' := κ ∘ₘ Q
  set ν' := P' + Q'
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set M := ν'.real Set.univ + 1
  have hM : 0 < M := by positivity
  set ε := min (δ / (2 * M)) ((δ / (2 * M)) ^ 2 / 2)
  have hε : 0 < ε := by positivity
  let t : Y → ℝ := fun y ↦ √(((Q'.rnDeriv ν' y).toReal + ε) / ((P'.rnDeriv ν' y).toReal + ε))
  have ht_pos (y : Y) : 0 < t y :=
    Real.sqrt_pos.2 (div_pos (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε)
      (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε))
  have ht_meas : Measurable t :=
    ((((Measure.measurable_rnDeriv Q' ν').ennreal_toReal.add measurable_const).div
      ((Measure.measurable_rnDeriv P' ν').ennreal_toReal.add measurable_const)).sqrt)
  have hcombined := (two_mul_hellingerAffinity_le_lintegral P Q κ ht_meas ht_pos).trans
    (lintegral_regularized_weight_le P' Q' hε)
  have hreal : 2 * hellingerAffinity P Q ≤
      2 * hellingerAffinity P' Q' + 2 * (√(2 * ε) + ε) * ν'.real Set.univ := by
    have hRHS_nonneg : 0 ≤ 2 * hellingerAffinity P' Q' + 2 * (√(2 * ε) + ε) * ν'.real Set.univ :=
      add_nonneg (mul_nonneg (by norm_num) (hellingerAffinity_nonneg P' Q')) (by positivity)
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν' Set.univ), ← Measure.real_def,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (hellingerAffinity_nonneg P' Q'))
        (by positivity)] at hcombined
    exact (ENNReal.ofReal_le_ofReal_iff hRHS_nonneg).1 hcombined
  have hε1 : ε ≤ δ / (2 * M) := min_le_left _ _
  have hε2 : √(2 * ε) ≤ δ / (2 * M) :=
    Real.sqrt_le_iff.2 ⟨by positivity,
      by linarith [min_le_right (δ / (2 * M)) ((δ / (2 * M)) ^ 2 / 2)]⟩
  have hsum : √(2 * ε) + ε ≤ δ / M := by
    have hhalf : δ / (2 * M) + δ / (2 * M) = δ / M := by field_simp; ring
    linarith
  have herror : (√(2 * ε) + ε) * ν'.real Set.univ ≤ δ :=
    (mul_le_mul hsum (by linarith : ν'.real Set.univ ≤ M)
      measureReal_nonneg (by positivity)).trans_eq (div_mul_cancel₀ δ hM.ne')
  linarith

/-- **Data processing inequality for the squared Hellinger distance.** Composing two finite
measures with a Markov kernel does not increase their squared Hellinger distance. -/
theorem sqHellinger_comp_le (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    sqHellinger (κ ∘ₘ P) (κ ∘ₘ Q) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_comp P Q κ]

/-- Pushing two finite measures forward along a map that is almost everywhere measurable for both
measures does not decrease their Hellinger affinity. -/
theorem hellingerAffinity_le_map_of_aemeasurable (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] {f : X → Y} (hP : AEMeasurable f P) (hQ : AEMeasurable f Q) :
    hellingerAffinity P Q ≤ hellingerAffinity (P.map f) (Q.map f) := by
  have hPQ : AEMeasurable f (P + Q) := hP.add_measure hQ
  have hfp : f =ᵐ[P] hPQ.mk f := (ae_add_measure_iff.1 hPQ.ae_eq_mk).1
  have hfq : f =ᵐ[Q] hPQ.mk f := (ae_add_measure_iff.1 hPQ.ae_eq_mk).2
  rw [Measure.map_congr hfp, Measure.map_congr hfq]
  simpa [Measure.deterministic_comp_eq_map] using
    hellingerAffinity_le_comp P Q (Kernel.deterministic (hPQ.mk f) hPQ.measurable_mk)

/-- Pushing two finite measures forward along a measurable map does not decrease their Hellinger
affinity. -/
theorem hellingerAffinity_le_map (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f : X → Y} (hf : Measurable f) :
    hellingerAffinity P Q ≤ hellingerAffinity (P.map f) (Q.map f) :=
  hellingerAffinity_le_map_of_aemeasurable P Q hf.aemeasurable hf.aemeasurable

/-- Pushing two finite measures forward along a map that is almost everywhere measurable for both
measures does not increase their squared Hellinger distance. -/
theorem sqHellinger_map_le_of_aemeasurable (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] {f : X → Y} (hP : AEMeasurable f P) (hQ : AEMeasurable f Q) :
    sqHellinger (P.map f) (Q.map f) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_map_of_aemeasurable P Q hP hQ]

/-- Pushing two finite measures forward along a measurable map does not increase their squared
Hellinger distance. -/
theorem sqHellinger_map_le (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f : X → Y} (hf : Measurable f) :
    sqHellinger (P.map f) (Q.map f) ≤ sqHellinger P Q :=
  sqHellinger_map_le_of_aemeasurable P Q hf.aemeasurable hf.aemeasurable

end DataProcessing

end TauCeti

namespace MeasurableEmbedding

open TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable embedding preserves the Hellinger affinity of two σ-finite measures. -/
theorem hellingerAffinity_map {f : X → Y} (hf : MeasurableEmbedding f) (P Q : Measure X)
    [SigmaFinite P] [SigmaFinite Q] :
    hellingerAffinity (P.map f) (Q.map f) = hellingerAffinity P Q := by
  rw [hellingerAffinity_def, hellingerAffinity_def, ← Measure.map_add _ _ hf.measurable,
    hf.integral_map]
  refine integral_congr_ae ?_
  filter_upwards [hf.rnDeriv_map P (P + Q), hf.rnDeriv_map Q (P + Q)] with x hPx hQx
  rw [hPx, hQx]

/-- A measurable embedding preserves the squared Hellinger distance of two σ-finite measures. -/
theorem sqHellinger_map {f : X → Y} (hf : MeasurableEmbedding f) (P Q : Measure X)
    [SigmaFinite P] [SigmaFinite Q] :
    sqHellinger (P.map f) (Q.map f) = sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def, hf.hellingerAffinity_map]

end MeasurableEmbedding

namespace MeasurableEquiv

open TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable equivalence preserves the Hellinger affinity of two σ-finite measures. -/
@[simp]
theorem hellingerAffinity_map (e : X ≃ᵐ Y) (P Q : Measure X)
    [SigmaFinite P] [SigmaFinite Q] :
    hellingerAffinity (P.map e) (Q.map e) = hellingerAffinity P Q :=
  e.measurableEmbedding.hellingerAffinity_map P Q

/-- A measurable equivalence preserves the squared Hellinger distance of two σ-finite measures. -/
@[simp]
theorem sqHellinger_map (e : X ≃ᵐ Y) (P Q : Measure X)
    [SigmaFinite P] [SigmaFinite Q] :
    sqHellinger (P.map e) (Q.map e) = sqHellinger P Q :=
  e.measurableEmbedding.sqHellinger_map P Q

end MeasurableEquiv
