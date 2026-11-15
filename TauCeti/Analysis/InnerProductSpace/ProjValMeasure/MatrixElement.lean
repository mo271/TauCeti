/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Variation
public import TauCeti.MeasureTheory.VectorMeasure.WithDensity

/-!
# Matrix elements of the integral against a projection-valued measure

Let `P` be a projection-valued measure on `X` acting on a complex Hilbert space `H`. For vectors
`ψ ξ : H`, the polarized complex measure `μ_(ψ,ξ) = P.polarizedComplexMeasure ψ ξ` takes the value
`⟪ψ, P(B) ξ⟫` on a measurable set `B`, and has finite variation. This file identifies the matrix
elements of the operator integral `P.integral f = ∫ f dP` of a bounded Borel symbol `f` with
Mathlib's integral against this complex measure, through the multiplication pairing `ℂ × ℂ → ℂ`:

`⟪ψ, (∫ f dP) ξ⟫ = ∫ᵛ x, f x ∂[mul ℝ ℂ; μ_(ψ,ξ)]`.

So the operator integral is determined by scalar integration against the polarized measures, and
the scalar integration theory of complex measures applies to its matrix elements.

On the diagonal, the variation of the polarized measure `μ_(ξ,ξ)` is the finite positive measure
`P.diag ξ` (`variation_polarizedComplexMeasure_self`), and integrating any complex function
against `μ_(ξ,ξ)` gives the Bochner integral against `P.diag ξ`.

## Main declarations

* `ProjValMeasure.integral_polarizedComplexMeasure_eq_inner_integral`: the matrix element
  `⟪ψ, (∫ f dP) ξ⟫` is the integral of `f` against `μ_(ψ,ξ)`.
* `ProjValMeasure.integral_polarizedComplexMeasure_self`: integration of any `f : X → ℂ` against
  `μ_(ξ,ξ)` is the Bochner integral against `P.diag ξ`.
* `ProjValMeasure.polarizedComplexMeasure_integral_right`,
  `ProjValMeasure.polarizedComplexMeasure_integral_left`, and `ProjValMeasure.diag_integral`:
  applying `P.integral f` multiplies the polarized complex measure by density `f` (or `star f` in
  the first slot) and multiplies `P.diag ξ` by density `‖f ·‖ₑ ^ 2`.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill, 1991, Theorem 12.21.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The matrix element of the integral of a simple symbol is its integral against the polarized
measure. -/
private theorem integral_polarizedComplexMeasure_ofSimpleFunc (P : ProjValMeasure X H)
    (s : SimpleFunc X ℂ) (ψ ξ : H) :
    ∫ᵛ x, s x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ] =
      ⟪ψ, P.integral (BoundedBorelFunction.ofSimpleFunc s) ξ⟫_ℂ := by
  induction s using SimpleFunc.induction with
  | @const c B hB =>
    have hs : ⇑(SimpleFunc.piecewise B hB (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
        B.indicator fun _ => c := by
      ext x
      by_cases hx : x ∈ B <;> simp [SimpleFunc.piecewise_apply, hx]
    have h : BoundedBorelFunction.ofSimpleFunc
        (SimpleFunc.piecewise B hB (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
          c • BoundedBorelFunction.indicator B hB 1 := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [hs, VectorMeasure.integral_indicator_const _ hB, h]
    simp [integral_indicator, inner_smul_right, polarizedComplexMeasure_apply _ _ _ _ hB]
  | @add s t _ hs ht =>
    rw [FunLike.coe_add, VectorMeasure.integral_add (SimpleFunc.integrable_of_isFiniteMeasure s)
      (SimpleFunc.integrable_of_isFiniteMeasure t), hs, ht]
    simp [inner_add_right]

/-- **Matrix elements of the integral against a projection-valued measure.** For a bounded Borel
symbol `f`, `⟪ψ, (∫ f dP) ξ⟫` is the integral of `f` against the polarized complex measure
`μ_(ψ,ξ)`, whose value on a measurable set `B` is `⟪ψ, P(B) ξ⟫`, through the multiplication
pairing. -/
theorem integral_polarizedComplexMeasure_eq_inner_integral (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) (ψ ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ] =
      ⟪ψ, P.integral f ξ⟫_ℂ := by
  obtain ⟨s, hs_le, hs⟩ := BoundedBorelFunction.exists_seq_tendsto_ofSimpleFunc f
  have hcont : Continuous fun g => ⟪ψ, P.integral g ξ⟫_ℂ :=
    continuous_const.inner ((ContinuousLinearMap.apply ℂ H ξ).continuous.comp
      P.continuous_integral)
  refine tendsto_nhds_unique (l := atTop)
    (f := fun n => ∫ᵛ x, s n x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ])
    ?_ (((hcont.tendsto f).comp hs).congr fun n => ?_)
  · -- Dominated convergence, with the constant bound `‖f‖` and pointwise convergence.
    refine VectorMeasure.tendsto_integral_filter_of_norm_le_const
      (Eventually.of_forall fun n => (s n).aestronglyMeasurable)
      ⟨‖f‖, Eventually.of_forall fun n => Eventually.of_forall (hs_le n)⟩
      (Eventually.of_forall fun x => ?_)
    rw [BoundedBorelFunction.tendsto_iff_tendstoUniformly] at hs
    simpa using hs.tendsto_at x
  · exact (P.integral_polarizedComplexMeasure_ofSimpleFunc (s n) ψ ξ).symm

/-- Integration of a complex function against the diagonal polarized measure through the
multiplication pairing is the Bochner integral against the diagonal measure. Both sides vanish
when `f` is not integrable, since the variation of the polarized measure is the diagonal
measure. -/
@[simp]
theorem integral_polarizedComplexMeasure_self (P : ProjValMeasure X H) (f : X → ℂ) (ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ξ ξ] =
      ∫ x, f x ∂(P.diag ξ) := by
  rw [polarizedComplexMeasure_self_eq_withDensityᵥ, VectorMeasure.integral_mul_withDensityᵥ_one]

/-- Applying `P.integral f` in the second argument multiplies the polarized complex measure by the
density `f`. -/
theorem polarizedComplexMeasure_integral_right (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure ψ (P.integral f ξ) =
      (P.polarizedComplexMeasure ψ ξ).withDensity f (ContinuousLinearMap.mul ℝ ℂ) := by
  ext B hB
  have hcomm := (P.forall_commute_integral_iff (P.proj B hB)).2
    (fun C hC => P.proj_mul_comm B C hB hC) f
  rw [polarizedComplexMeasure_apply _ _ _ _ hB,
    ← mul_apply_eq_comp, hcomm.eq, mul_apply_eq_comp,
    ← integral_polarizedComplexMeasure_eq_inner_integral,
    polarizedComplexMeasure_proj_right _ hB,
    VectorMeasure.withDensity_apply (f.integrable _)]

/-- Applying `P.integral f` in the first argument multiplies the polarized complex measure by the
conjugate density `star ⇑f`. -/
theorem polarizedComplexMeasure_integral_left (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure (P.integral f ψ) ξ =
      (P.polarizedComplexMeasure ψ ξ).withDensity (star ⇑f) (ContinuousLinearMap.mul ℝ ℂ) := by
  ext B hB
  rw [polarizedComplexMeasure_apply _ _ _ _ hB,
    ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    ← integral_polarizedComplexMeasure_eq_inner_integral,
    polarizedComplexMeasure_proj_right _ hB, ← BoundedBorelFunction.coe_star,
    VectorMeasure.withDensity_apply ((star f).integrable _)]

/-- Applying `P.integral f` multiplies the diagonal spectral measure `P.diag ξ` by the density
`x ↦ ‖f x‖ₑ ^ 2`. -/
theorem diag_integral (P : ProjValMeasure X H) (f : BoundedBorelFunction X) (ξ : H) :
    P.diag (P.integral f ξ) = (P.diag ξ).withDensity fun x => ‖f x‖ₑ ^ 2 := by
  have hpol : P.polarizedComplexMeasure (P.integral f ξ) (P.integral f ξ) =
      (P.polarizedComplexMeasure ξ ξ).withDensity (fun x => f x * star (f x))
        (ContinuousLinearMap.mul ℝ ℂ) := by
    rw [polarizedComplexMeasure_integral_right, polarizedComplexMeasure_integral_left,
      ← BoundedBorelFunction.coe_star,
      VectorMeasure.withDensity_withDensity_mul ((star f).integrable _)]
    rfl
  have hvar := congrArg VectorMeasure.variation hpol
  have hint : (P.polarizedComplexMeasure ξ ξ).Integrable (fun x => f x * star (f x)) :=
    (f * star f).integrable _
  rw [variation_polarizedComplexMeasure_self,
    VectorMeasure.variation_withDensity_mul hint,
    variation_polarizedComplexMeasure_self] at hvar
  refine hvar.trans (withDensity_congr_ae <| Filter.Eventually.of_forall fun x => ?_)
  simp [sq, eNorm_mul]

end ProjValMeasure
end TauCeti
