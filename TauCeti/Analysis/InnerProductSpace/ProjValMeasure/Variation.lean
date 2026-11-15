/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Polarization

/-!
# The sharp variation estimate for polarized spectral measures

For the complex measure `P.polarizedComplexMeasure ψ ξ` associated with a normalized
projection-valued measure, we prove

`(P.polarizedComplexMeasure ψ ξ).variation univ ≤ ofReal (‖ψ‖ * ‖ξ‖)`,

and more generally on every measurable set `B`:

`(P.polarizedComplexMeasure ψ ξ).variation B ≤ ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖)`.

This sharp bound makes the polarized complex measure a finite-variation measure, symmetric in its
two vector arguments up to variation and absolutely continuous with respect to both `P.diag ψ` and
`P.diag ξ`, and yields Cauchy–Schwarz `L²` domination for integration against its variation:

`∫⁻ x, g x ∂(P.polarizedComplexMeasure ψ ξ).variation`
`  ≤ ‖ψ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2)`,

along with its symmetric left-hand counterpart against `P.diag ψ` and the two-function bound for
almost-everywhere measurable nonnegative integrands.

In particular, every measurable symbol with finite second moment against `P.diag ξ` (or `P.diag ψ`)
is integrable against `P.polarizedComplexMeasure ψ ξ`, with `L¹` norm bounded by
`‖ψ‖ * √(∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ))`.

On the diagonal, the variation of `P.polarizedComplexMeasure ξ ξ` is exactly `P.diag ξ`.

The underlying PVM and polarized-measure constructions are adapted from the
AIQ-Kitware DKPS formalization (Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, Section 3.1.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sharp variation bound for nonzero vectors. -/
private theorem polarizedComplexMeasure_variation_univ_le_of_ne_zero
    (P : ProjValMeasure X H) {ψ ξ : H} (hψz : ψ ≠ 0) (hξz : ξ ≠ 0) :
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
  have hψ : 0 < ‖ψ‖ := norm_pos_iff.mpr hψz
  have hξ : 0 < ‖ξ‖ := norm_pos_iff.mpr hξz
  let a : ℝ≥0 := ⟨‖ξ‖ / (2 * ‖ψ‖), by positivity⟩
  let b : ℝ≥0 := ⟨‖ψ‖ / (2 * ‖ξ‖), by positivity⟩
  have ha : (a : ℝ) = ‖ξ‖ / (2 * ‖ψ‖) := rfl
  have hb : (b : ℝ) = ‖ψ‖ / (2 * ‖ξ‖) := rfl
  let m : Measure X := a • P.diag ψ + b • P.diag ξ
  have hm (B : Set X) :
      m.real B = (a : ℝ) * (P.diag ψ).real B + (b : ℝ) * (P.diag ξ).real B := by
    simp only [m]
    rw [measureReal_add_apply, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
  have hmajor : (P.polarizedComplexMeasure ψ ξ).variation ≤ m := by
    apply VectorMeasure.variation_le_of_forall_eNorm_le
    intro B hB
    have hbound : ‖P.polarizedComplexMeasure ψ ξ B‖ ≤ m.real B := by
      rw [hm B, ha, hb]
      exact P.norm_polarizedComplexMeasure_apply_le B hB
    simpa only [measureReal_def, ofReal_norm] using
      (ENNReal.ofReal_le_of_le_toReal hbound)
  have hmass : m.real Set.univ = ‖ψ‖ * ‖ξ‖ := by
    rw [hm Set.univ, P.diag_real_univ, P.diag_real_univ, ha, hb]
    field_simp [ne_of_gt hψ, ne_of_gt hξ]
    ring
  calc
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤ m Set.univ := hmajor Set.univ
    _ = ENNReal.ofReal (m.real Set.univ) :=
        (ofReal_measureReal (μ := m) (s := Set.univ)).symm
    _ = ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by rw [hmass]

/-- The variation of a polarized spectral measure has the sharp mass bound. -/
theorem polarizedComplexMeasure_variation_univ_le (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
  by_cases hψz : ψ = 0
  · subst ψ
    rw [P.polarizedComplexMeasure_zero_left, VectorMeasure.variation_zero]
    simp
  by_cases hξz : ξ = 0
  · subst ξ
    rw [P.polarizedComplexMeasure_zero_right, VectorMeasure.variation_zero]
    simp
  exact P.polarizedComplexMeasure_variation_univ_le_of_ne_zero hψz hξz

/-- The variation of a polarized complex measure is finite. -/
instance instIsFiniteMeasurePolarizedVariation (P : ProjValMeasure X H) (ψ ξ : H) :
    IsFiniteMeasure (P.polarizedComplexMeasure ψ ξ).variation := by
  refine ⟨?_⟩
  exact (P.polarizedComplexMeasure_variation_univ_le ψ ξ).trans_lt
    ENNReal.ofReal_lt_top

/-- The variation of the diagonal polarized measure is the diagonal measure. -/
@[simp]
theorem variation_polarizedComplexMeasure_self (P : ProjValMeasure X H) (ξ : H) :
    (P.polarizedComplexMeasure ξ ξ).variation = P.diag ξ := by
  rw [polarizedComplexMeasure_self_eq_withDensityᵥ,
    Measure.variation_withDensityᵥ (integrable_const _)]
  simp

private theorem variation_polarizedComplexMeasure_le_comm
    (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≤ (P.polarizedComplexMeasure ξ ψ).variation := by
  refine VectorMeasure.variation_le_of_forall_eNorm_le fun B hB => ?_
  have hconj : P.polarizedComplexMeasure ψ ξ B = star (P.polarizedComplexMeasure ξ ψ B) := by
    rw [P.polarizedComplexMeasure_apply _ _ _ hB, P.polarizedComplexMeasure_apply _ _ _ hB,
      RCLike.star_def, inner_conj_symm]
    exact ((P.isSelfAdjoint_proj B hB).isSymmetric ψ ξ).symm
  rw [hconj, ← ofReal_norm, norm_star, ofReal_norm]
  exact VectorMeasure.eNorm_measure_le_variation _ B

/-- Swapping the two vectors leaves the variation of `P.polarizedComplexMeasure` unchanged, since
`P.polarizedComplexMeasure ψ ξ` and `P.polarizedComplexMeasure ξ ψ` are complex conjugates on every
measurable set. -/
theorem variation_polarizedComplexMeasure_comm (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation = (P.polarizedComplexMeasure ξ ψ).variation :=
  le_antisymm (variation_polarizedComplexMeasure_le_comm P ψ ξ)
    (variation_polarizedComplexMeasure_le_comm P ξ ψ)

/-- **Setwise sharp variation estimate** for a polarized spectral measure: on every measurable set
`B`, the variation is bounded by `‖P(B) ψ‖ * ‖P(B) ξ‖`. -/
theorem variation_polarizedComplexMeasure_apply_le (P : ProjValMeasure X H) (ψ ξ : H)
    {B : Set X} (hB : MeasurableSet B) :
    (P.polarizedComplexMeasure ψ ξ).variation B ≤
      ENNReal.ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖) := by
  have hrestrict :
      P.polarizedComplexMeasure (P.proj B hB ψ) (P.proj B hB ξ) =
        (P.polarizedComplexMeasure ψ ξ).restrict B := by
    rw [P.polarizedComplexMeasure_proj_right hB, P.polarizedComplexMeasure_proj_left hB,
      (P.polarizedComplexMeasure ψ ξ).restrict_restrict hB hB, Set.inter_self]
  calc (P.polarizedComplexMeasure ψ ξ).variation B
      = (P.polarizedComplexMeasure ψ ξ).variation.restrict B Set.univ := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ = ((P.polarizedComplexMeasure ψ ξ).restrict B).variation Set.univ := by
          rw [VectorMeasure.variation_restrict hB]
    _ = (P.polarizedComplexMeasure (P.proj B hB ψ) (P.proj B hB ξ)).variation Set.univ := by
          rw [hrestrict]
    _ ≤ ENNReal.ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖) :=
          P.polarizedComplexMeasure_variation_univ_le _ _

/-- The variation of `P.polarizedComplexMeasure ψ ξ` is absolutely continuous with respect to
`P.diag ξ`. -/
theorem variation_polarizedComplexMeasure_absolutelyContinuous_right
    (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≪ P.diag ξ := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hB₀ => ?_
  have hsq : ‖P.proj B hB ξ‖ₑ ^ 2 = 0 := (P.enorm_sq_proj_apply B hB ξ).trans hB₀
  rw [sq_eq_zero_iff, eNorm_eq_zero] at hsq
  exact nonpos_iff_eq_zero.1 <|
    (P.variation_polarizedComplexMeasure_apply_le ψ ξ hB).trans (by simp [hsq])

/-- The variation of `P.polarizedComplexMeasure ψ ξ` is absolutely continuous with respect to
`P.diag ψ`. -/
theorem variation_polarizedComplexMeasure_absolutelyContinuous_left
    (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≪ P.diag ψ :=
  P.variation_polarizedComplexMeasure_comm ψ ξ ▸
    P.variation_polarizedComplexMeasure_absolutelyContinuous_right ξ ψ

private theorem simpleFunc_lintegral_mul_variation_polarizedComplexMeasure_le
    (P : ProjValMeasure X H) (ψ ξ : H) (φ₁ φ₂ : SimpleFunc X ℝ≥0∞) :
    (φ₁ * φ₂).lintegral (P.polarizedComplexMeasure ψ ξ).variation ≤
      (∫⁻ x, φ₁ x ^ 2 ∂(P.diag ψ)) ^ (1 / 2 : ℝ) *
        (∫⁻ x, φ₂ x ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  let Φ : SimpleFunc X (ℝ≥0∞ × ℝ≥0∞) := φ₁.pair φ₂
  have hmul : Φ.map (fun p => p.1 * p.2) = φ₁ * φ₂ := by
    ext x
    simp [Φ, SimpleFunc.map_apply]
  have hstep :
      (φ₁ * φ₂).lintegral (P.polarizedComplexMeasure ψ ξ).variation ≤
        ∑ p ∈ Φ.range,
          (p.1 * ‖P.proj (Φ ⁻¹' {p}) (Φ.measurableSet_fiber p) ψ‖ₑ) *
            (p.2 * ‖P.proj (Φ ⁻¹' {p}) (Φ.measurableSet_fiber p) ξ‖ₑ) := by
    rw [← hmul, SimpleFunc.map_lintegral]
    refine Finset.sum_le_sum fun p _ => ?_
    have hB := Φ.measurableSet_fiber p
    have hvar : (P.polarizedComplexMeasure ψ ξ).variation (Φ ⁻¹' {p}) ≤
        ‖P.proj (Φ ⁻¹' {p}) hB ψ‖ₑ * ‖P.proj (Φ ⁻¹' {p}) hB ξ‖ₑ := by
      refine (P.variation_polarizedComplexMeasure_apply_le ψ ξ hB).trans_eq ?_
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    calc p.1 * p.2 * (P.polarizedComplexMeasure ψ ξ).variation (Φ ⁻¹' {p})
        ≤ p.1 * p.2 * (‖P.proj (Φ ⁻¹' {p}) hB ψ‖ₑ * ‖P.proj (Φ ⁻¹' {p}) hB ξ‖ₑ) := by gcongr
      _ = (p.1 * ‖P.proj (Φ ⁻¹' {p}) hB ψ‖ₑ) * (p.2 * ‖P.proj (Φ ⁻¹' {p}) hB ξ‖ₑ) := by ac_rfl
  have hcs := ENNReal.inner_le_Lp_mul_Lq Φ.range
    (fun p => p.1 * ‖P.proj (Φ ⁻¹' {p}) (Φ.measurableSet_fiber p) ψ‖ₑ)
    (fun p => p.2 * ‖P.proj (Φ ⁻¹' {p}) (Φ.measurableSet_fiber p) ξ‖ₑ)
    Real.HolderConjugate.two_two
  have hfactor (η : H) (π : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞) (φ : SimpleFunc X ℝ≥0∞)
      (hπ : ∀ x, π (Φ x) = φ x) :
      ∑ p ∈ Φ.range, (π p * ‖P.proj (Φ ⁻¹' {p}) (Φ.measurableSet_fiber p) η‖ₑ) ^ (2 : ℝ) =
        ∫⁻ x, φ x ^ 2 ∂(P.diag η) := by
    calc ∑ p ∈ Φ.range, (π p * ‖P.proj (Φ ⁻¹' {p}) (Φ.measurableSet_fiber p) η‖ₑ) ^ (2 : ℝ)
        = (Φ.map fun p => π p ^ 2).lintegral (P.diag η) := by
            rw [SimpleFunc.map_lintegral]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [ENNReal.rpow_ofNat, mul_pow, P.enorm_sq_proj_apply]
      _ = ∫⁻ x, φ x ^ 2 ∂(P.diag η) := by
            rw [← SimpleFunc.lintegral_eq_lintegral]
            exact lintegral_congr fun x => by simp [SimpleFunc.map_apply, hπ x]
  rw [hfactor ψ Prod.fst φ₁ (fun _ => rfl), hfactor ξ Prod.snd φ₂ (fun _ => rfl)] at hcs
  exact hstep.trans hcs

/-- **Two-function Cauchy–Schwarz bound** for integration against the variation of a polarized
spectral measure: for `P.diag ψ`-a.e. measurable `f` and `P.diag ξ`-a.e. measurable `g`,
`∫⁻ x, f x * g x ∂(P.polarizedComplexMeasure ψ ξ).variation` is bounded by
`(∫⁻ x, f x ^ 2 ∂(P.diag ψ)) ^ (1 / 2) * (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2)`. -/
theorem lintegral_mul_variation_polarizedComplexMeasure_le
    (P : ProjValMeasure X H) (ψ ξ : H) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f (P.diag ψ)) (hg : AEMeasurable g (P.diag ξ)) :
    ∫⁻ x, f x * g x ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      (∫⁻ x, f x ^ 2 ∂(P.diag ψ)) ^ (1 / 2 : ℝ) *
        (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  set f' := hf.mk f
  set g' := hg.mk g
  have hf' : Measurable f' := hf.measurable_mk
  have hg' : Measurable g' := hg.measurable_mk
  have hfg_ae : (fun x => f x * g x) =ᵐ[(P.polarizedComplexMeasure ψ ξ).variation]
      fun x => f' x * g' x := by
    filter_upwards [P.variation_polarizedComplexMeasure_absolutelyContinuous_left ψ ξ hf.ae_eq_mk,
      P.variation_polarizedComplexMeasure_absolutelyContinuous_right ψ ξ hg.ae_eq_mk] with x hfx hgx
    rw [hfx, hgx]
  rw [lintegral_congr_ae hfg_ae,
    lintegral_congr_ae (hf.ae_eq_mk.mono fun x hx => congrArg (· ^ 2) hx),
    lintegral_congr_ae (hg.ae_eq_mk.mono fun x hx => congrArg (· ^ 2) hx)]
  have hle_sup (x : X) :
      f' x * g' x ≤ ⨆ n, (SimpleFunc.eapprox f' n * SimpleFunc.eapprox g' n) x := by
    rw [← SimpleFunc.iSup_eapprox_apply hf' x,
      ← SimpleFunc.iSup_eapprox_apply hg' x, ENNReal.iSup_mul]
    refine iSup_le fun i => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun j => le_iSup_of_le (max i j) ?_
    rw [FunLike.coe_mul, Pi.mul_apply]
    exact mul_le_mul' (SimpleFunc.monotone_eapprox f' (le_max_left i j) x)
      (SimpleFunc.monotone_eapprox g' (le_max_right i j) x)
  refine (lintegral_mono hle_sup).trans ?_
  rw [lintegral_iSup (fun n => (SimpleFunc.eapprox f' n * SimpleFunc.eapprox g' n).measurable)
    (fun m n hmn x => mul_le_mul' (SimpleFunc.monotone_eapprox f' hmn x)
      (SimpleFunc.monotone_eapprox g' hmn x))]
  refine iSup_le fun n => ?_
  rw [SimpleFunc.lintegral_eq_lintegral]
  refine (simpleFunc_lintegral_mul_variation_polarizedComplexMeasure_le P ψ ξ _ _).trans ?_
  gcongr with x x
  · exact (le_iSup (fun k => SimpleFunc.eapprox f' k x) n).trans_eq
      (SimpleFunc.iSup_eapprox_apply hf' x)
  · exact (le_iSup (fun k => SimpleFunc.eapprox g' k x) n).trans_eq
      (SimpleFunc.iSup_eapprox_apply hg' x)

/-- **Cauchy–Schwarz domination** for integration against the variation of a polarized spectral
measure: for every `g : X → ℝ≥0∞`, the lower Lebesgue integral of `g` against
`(P.polarizedComplexMeasure ψ ξ).variation` is bounded by
`‖ψ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2)`. -/
theorem lintegral_variation_polarizedComplexMeasure_le
    (P : ProjValMeasure X H) (ψ ξ : H) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  rw [lintegral_def]
  refine iSup₂_le fun φ hφ => ?_
  have h1 : (∫⁻ x, (1 : SimpleFunc X ℝ≥0∞) x ^ 2 ∂(P.diag ψ)) ^ (1 / 2 : ℝ) = ‖ψ‖ₑ := by
    have hconst : (∫⁻ x, (1 : SimpleFunc X ℝ≥0∞) x ^ 2 ∂(P.diag ψ)) = ‖ψ‖ₑ ^ (2 : ℝ) := by
      simp [P.diag_univ]
    rw [hconst, ← ENNReal.rpow_mul, mul_one_div_cancel (by positivity), ENNReal.rpow_one]
  have hstep := simpleFunc_lintegral_mul_variation_polarizedComplexMeasure_le P ψ ξ 1 φ
  rw [one_mul, h1] at hstep
  refine hstep.trans ?_
  gcongr with x
  exact hφ x

/-- Left-hand **Cauchy–Schwarz domination** for integration against the variation of a polarized
spectral measure: for every `g : X → ℝ≥0∞`, the lower Lebesgue integral of `g` against
`(P.polarizedComplexMeasure ψ ξ).variation` is bounded by
`‖ξ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ψ)) ^ (1 / 2)`. -/
theorem lintegral_variation_polarizedComplexMeasure_le_left
    (P : ProjValMeasure X H) (ψ ξ : H) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ξ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ψ)) ^ (1 / 2 : ℝ) := by
  rw [P.variation_polarizedComplexMeasure_comm]
  exact P.lintegral_variation_polarizedComplexMeasure_le ξ ψ g

/-- A function that is almost everywhere strongly measurable for the variation of
`P.polarizedComplexMeasure ψ ξ` and has finite second extended-norm moment against `P.diag ξ` is
integrable against `(P.polarizedComplexMeasure ψ ξ).variation`. -/
theorem integrable_variation_polarizedComplexMeasure_of_lintegral_enorm_sq_lt_top
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (P : ProjValMeasure X H) (ψ ξ : H)
    {f : X → E} (hf : AEStronglyMeasurable f (P.polarizedComplexMeasure ψ ξ).variation)
    (hξ : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(P.diag ξ) < ∞) :
    Integrable f (P.polarizedComplexMeasure ψ ξ).variation := by
  refine ⟨hf, (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun x => ‖f x‖ₑ).trans_lt ?_⟩
  exact ENNReal.mul_lt_top eNorm_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hξ.ne)

/-- Left-hand counterpart of
`integrable_variation_polarizedComplexMeasure_of_lintegral_enorm_sq_lt_top`, assuming finite second
extended-norm moment against `P.diag ψ`. -/
theorem integrable_variation_polarizedComplexMeasure_of_lintegral_enorm_sq_lt_top_left
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (P : ProjValMeasure X H) (ψ ξ : H)
    {f : X → E} (hf : AEStronglyMeasurable f (P.polarizedComplexMeasure ψ ξ).variation)
    (hψ : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(P.diag ψ) < ∞) :
    Integrable f (P.polarizedComplexMeasure ψ ξ).variation := by
  rw [Integrable, P.variation_polarizedComplexMeasure_comm] at *
  exact P.integrable_variation_polarizedComplexMeasure_of_lintegral_enorm_sq_lt_top ξ ψ hf hψ

/-- **Cauchy–Schwarz `L¹`–`L²` bound** for the variation of a polarized spectral measure: whenever
`x ↦ ‖f x‖ ^ 2` is integrable against `P.diag ξ`,
`∫ x, ‖f x‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤ ‖ψ‖ * √(∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le
    {E : Type*} [SeminormedAddCommGroup E] (P : ProjValMeasure X H) (ψ ξ : H) {f : X → E}
    (hξ : Integrable (fun x => ‖f x‖ ^ 2) (P.diag ξ)) :
    ∫ x, ‖f x‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ * Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ)) := by
  by_cases hint : Integrable (fun x => ‖f x‖) (P.polarizedComplexMeasure ψ ξ).variation
  · have hlin : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(P.diag ξ) = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hξ (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have hle := P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun x => ‖f x‖ₑ
    have hpow : ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ))) := by
      rw [Real.sqrt_eq_rpow,
        ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity)]
    rw [hlin, hpow, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at hle
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hint.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (lintegral_congr fun x => ?_).trans_le hle
    rw [ofReal_norm]
  · rw [integral_undef hint]
    positivity

/-- Left-hand **Cauchy–Schwarz `L¹`–`L²` bound** for the variation of a polarized spectral measure:
whenever `x ↦ ‖f x‖ ^ 2` is integrable against `P.diag ψ`,
`∫ x, ‖f x‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤ ‖ξ‖ * √(∫ x, ‖f x‖ ^ 2 ∂(P.diag ψ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le_left
    {E : Type*} [SeminormedAddCommGroup E] (P : ProjValMeasure X H) (ψ ξ : H) {f : X → E}
    (hψ : Integrable (fun x => ‖f x‖ ^ 2) (P.diag ψ)) :
    ∫ x, ‖f x‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ξ‖ * Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(P.diag ψ)) := by
  rw [P.variation_polarizedComplexMeasure_comm]
  exact P.integral_norm_variation_polarizedComplexMeasure_le ξ ψ hψ

end TauCeti.ProjValMeasure
