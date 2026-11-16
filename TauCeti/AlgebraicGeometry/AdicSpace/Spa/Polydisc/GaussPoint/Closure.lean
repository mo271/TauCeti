/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint.Topology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Basic
public import TauCeti.RingTheory.Huber.Reduction.Normed

import Mathlib.FieldTheory.Finite.Basic
import TauCeti.Algebra.MvPolynomial.Funext
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basis
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

/-!
# The unit Gauss point of a closed polydisc and its closure in rational points

Let `R` be a normed commutative ring with multiplicative ultrametric norm (`[NormMulClass R]`,
`[NormOneClass R]`). Pulling back the multiplicative ultrametric Gauss norm on
`MvPowerSeries.IsRestricted.subring (fun _ : Fin n ↦ 1)` across the continuous ring equivalence
`TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv` equips the restricted power-series ring
`R⟨T₁, …, Tₙ⟩` with the *unit-radius Gauss valuation* `unitGaussValuation n R` with values in
`ℝ≥0`. Over an ultrametric normed field `K` (including trivially normed fields),
`unitGaussValuation n K` is bounded by `1` on power-bounded elements and defines the *unit Gauss
point* `unitGaussPoint n K : closedPolydisc n K`, characterized uniquely by comparing restricted
series via their unit Gauss norms (`eq_unitGaussPoint_iff`) and agreeing at `n = 1` with
`gaussPoint zero_lt_one le_rfl` (`unitGaussPoint_one_eq_gaussPoint`).

When `K` is complete and its canonical reduction `CanonicalReduction K = K° ⧸ K°°` is infinite,
`unitGaussPoint n K` lies in the topological closure of the classical evaluation points
`(K°)ⁿ → closedPolydisc n K` (`unitGaussPoint_mem_closure_range_classicalPoint`, Howe–Klevdal II,
proof of Lemma 9.3.5). Concretely, any open neighbourhood of `unitGaussPoint n K` contains the trace
of a basic open `Spv(K⟨T⟩)(F/s)` for a finite set `F` and denominator `s` with `‖s‖ > 0` and
`‖t‖ ≤ ‖s‖` for all `t ∈ F`. Rescaling `F` and `s` by the inverse of a dominant coefficient of `s`
reduces to `‖s'‖ = 1` and `‖t'‖ ≤ 1`; truncating `s'` modulo `K°°` produces a nonzero polynomial in
`n` variables over the infinite residue field `CanonicalReduction K`, which takes a nonzero value at
some residue tuple (`MvPolynomial.exists_eval_ne_zero`). Lifting that tuple to `(K°)ⁿ` gives a
classical point in `Spv(K⟨T⟩)(F/s)`.

Two boundary phenomena complete the picture:
* For `n = 0`, `unitGaussPoint 0 K` already belongs to the classical-point locus unconditionally
  (`unitGaussPoint_zero_mem_range_classicalPoint`), even when the residue field is finite.
* For `n ≥ 1`, the infinite-residue-field hypothesis is both sufficient and necessary
  (`unitGaussPoint_mem_closure_range_classicalPoint_iff_infinite`): when `CanonicalReduction K` is
  finite of cardinality `q`, the rational open `{v | 1 ≤ v(T₀^q - T₀)}` contains
  `unitGaussPoint n K` (since `‖T₀^q - T₀‖ = 1`) yet misses every classical point because
  `a₀^q - a₀ ∈ K°°` for all `a₀ ∈ K°`
  (`unitGaussPoint_notMem_closure_range_classicalPoint_of_finite`).
  When `CanonicalReduction K` is infinite and `n ≥ 1`, the classical-point locus is therefore not
  closed in `closedPolydisc n K` (`not_isClosed_range_classicalPoint`), since `unitGaussPoint n K`
  lies in its closure but has trivial support (`unitGaussPoint_ne_classicalPoint`).

## Main definitions

* `TauCeti.ValuationSpectrum.unitGaussValuation`: the unit-radius Gauss valuation on
  `R⟨T₁, …, Tₙ⟩` with values in `ℝ≥0`.
* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point of `closedPolydisc n K`.

## Main results

* `TauCeti.ValuationSpectrum.unitGaussValuation_apply` and
  `TauCeti.ValuationSpectrum.coe_unitGaussValuation`: comparison with the Gauss norm across
  `restrictedMvPowerSeriesGaussEquiv`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_vle_iff` and
  `TauCeti.ValuationSpectrum.eq_unitGaussPoint_iff`: characterization of `unitGaussPoint n K` by
  unit Gauss norm comparison.
* `TauCeti.ValuationSpectrum.unitGaussPoint_one_eq_gaussPoint`: agreement with
  `gaussPoint zero_lt_one le_rfl` in one variable.
* `TauCeti.ValuationSpectrum.exists_classicalPoint_mem_of_unitGaussPoint_mem_isOpen` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint`: every open
  neighbourhood of `unitGaussPoint n K` meets the classical points when `CanonicalReduction K` is
  infinite, placing `unitGaussPoint n K` in their closure.
* `TauCeti.ValuationSpectrum.not_isClosed_range_classicalPoint`: for `n ≥ 1` and infinite residue
  field, the classical-point locus is not closed in `closedPolydisc n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_range_classicalPoint_of_finite` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint_iff_infinite`:
  finite-residue-field obstruction and exact characterization for `n ≥ 1`.

## References

* S. Howe and C. Klevdal, *Admissible modules and normality of classical affinoid varieties*,
  Adv. Math. 442 (2024), 109563, proof of Lemma 9.3.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

/-! ### The unit-radius Gauss valuation on `R⟨T₁, …, Tₙ⟩` -/

section UnitGaussValuation

variable {n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NonarchimedeanRing R]
  [NormMulClass R] [NormOneClass R]

/-- **The unit-radius Gauss valuation on `R⟨T₁, …, Tₙ⟩`**, sending a restricted series
`f = ∑_ν a_ν T^ν` to `‖restrictedMvPowerSeriesGaussEquiv f‖₊ = max_ν ‖a_ν‖₊ : ℝ≥0`. -/
noncomputable def unitGaussValuation (n : ℕ) (R : Type*) [NormedCommRing R]
    [IsUltrametricDist R] [NonarchimedeanRing R] [NormMulClass R] [NormOneClass R] :
    Valuation
      (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight)
      ℝ≥0 where
  toFun f := ‖restrictedMvPowerSeriesGaussEquiv f‖₊
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by rw [map_mul, nnNorm_mul]
  map_add_le_max' f g := by
    rw [← NNReal.coe_le_coe, map_add]
    exact IsUltrametricDist.norm_add_le_max _ _

/-- `unitGaussValuation n R` agrees with the `nnNorm` of `restrictedMvPowerSeriesGaussEquiv f`. -/
theorem unitGaussValuation_apply
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    unitGaussValuation n R f = ‖restrictedMvPowerSeriesGaussEquiv f‖₊ :=
  (rfl)

/-- Coerced to `ℝ`, `unitGaussValuation n R f` is the Gauss norm of
`restrictedMvPowerSeriesGaussEquiv f`. -/
@[simp]
theorem coe_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (unitGaussValuation n R f : ℝ) = ‖restrictedMvPowerSeriesGaussEquiv f‖ :=
  coe_nnNorm _

/-- `unitGaussValuation n R` is continuous on `R⟨T₁, …, Tₙ⟩`. -/
theorem isContinuous_unitGaussValuation :
    (unitGaussValuation n R).IsContinuous := by
  refine Valuation.isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  have heq : {f | unitGaussValuation n R f < γ} =
      restrictedMvPowerSeriesGaussEquiv ⁻¹' Metric.ball 0 (γ : ℝ) := by
    ext f
    simp [unitGaussValuation_apply, ← NNReal.coe_lt_coe]
  rw [heq]
  exact Metric.isOpen_ball.preimage continuous_restrictedMvPowerSeriesGaussEquiv

/-- Every coefficient norm `‖coeff ν f‖₊` is bounded by `unitGaussValuation n R f`. -/
theorem nnNorm_coeff_le_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (ν : Fin n →₀ ℕ) :
    ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) R)‖₊ ≤ unitGaussValuation n R f := by
  rw [unitGaussValuation_apply, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
  simpa [coe_restrictedMvPowerSeriesGaussEquiv] using
    MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv f) ν

/-- Every restricted series attains its unit-radius Gauss valuation at some multi-index. -/
theorem exists_nnNorm_coeff_eq_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    ∃ ν : Fin n →₀ ℕ,
      ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) R)‖₊ = unitGaussValuation n R f := by
  obtain ⟨ν, hν⟩ := MvPowerSeries.exists_norm_coeff_eq_norm (restrictedMvPowerSeriesGaussEquiv f)
  exact ⟨ν, NNReal.eq <| by
    simpa [unitGaussValuation_apply, coe_restrictedMvPowerSeriesGaussEquiv] using hν⟩

/-- `unitGaussValuation n R f ≤ γ` holds if and only if every coefficient has `nnNorm` at most
`γ`. -/
theorem unitGaussValuation_le_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight}
    {γ : ℝ≥0} :
    unitGaussValuation n R f ≤ γ ↔
      ∀ ν, ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) R)‖₊ ≤ γ := by
  rw [unitGaussValuation_apply, ← NNReal.coe_le_coe, coe_nnNorm, MvPowerSeries.norm_le_iff]
  refine forall_congr' fun ν ↦ ?_
  simp [coe_restrictedMvPowerSeriesGaussEquiv, Finsupp.prod, ← NNReal.coe_le_coe]

/-- `unitGaussValuation n R` vanishes only at `0`. -/
@[simp]
theorem unitGaussValuation_eq_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight} :
    unitGaussValuation n R f = 0 ↔ f = 0 := by
  rw [unitGaussValuation_apply, nnNorm_eq_zero,
    map_eq_zero_iff _ restrictedMvPowerSeriesGaussEquiv.injective]

/-- On constants, `unitGaussValuation n R` is `nnNorm`. -/
@[simp]
theorem unitGaussValuation_weightedC (a : R) :
    unitGaussValuation n R (weightedC (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight a) = ‖a‖₊ :=
  NNReal.eq <| by simp [unitGaussValuation_apply, restrictedMvPowerSeriesGaussEquiv_weightedC]

/-- On each coordinate variable `Tᵢ`, `unitGaussValuation n R` takes the value `1`. -/
@[simp]
theorem unitGaussValuation_weightedX (i : Fin n) :
    unitGaussValuation n R (weightedX (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight i) = 1 :=
  NNReal.eq <| by simp [unitGaussValuation_apply, restrictedMvPowerSeriesGaussEquiv_weightedX]

end UnitGaussValuation

/-! ### The unit Gauss point of `closedPolydisc n K` -/

section UnitGaussPoint

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

/-- Over any ultrametric normed field `K` (including trivially normed fields), every power-bounded
element of `K⟨T₁, …, Tₙ⟩` has unit-radius Gauss valuation at most `1`. -/
theorem unitGaussValuation_le_one_of_isPowerBounded
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : IsPowerBounded f) : unitGaussValuation n K f ≤ 1 := by
  rw [unitGaussValuation_apply, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]
  by_contra! hgt
  have hex : ∃ ν, 1 < ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) K)‖ := by
    by_contra! hle
    refine hgt.not_ge (MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_)
    simpa [coe_restrictedMvPowerSeriesGaussEquiv, Finsupp.prod] using hle ν
  obtain ⟨ν, hν⟩ := hex
  let c : K := MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) K)
  let _ : NontriviallyNormedField K :=
    NontriviallyNormedField.ofNormNeOne ⟨c, norm_pos_iff.mp (zero_lt_one.trans hν), hν.ne'⟩
  have hpb : restrictedMvPowerSeriesGaussEquiv f ∈ powerBoundedSubring _ :=
    mem_powerBoundedSubring.mpr <|
      (isPowerBounded_ringEquiv_iff restrictedMvPowerSeriesGaussEquiv
        continuous_restrictedMvPowerSeriesGaussEquiv
        continuous_restrictedMvPowerSeriesGaussEquiv_symm).mpr hf
  rw [TauCeti.MvPowerSeries.powerBoundedSubring_eq_unitClosedBall,
    Subring.mem_unitClosedBall] at hpb
  exact hgt.not_ge hpb

/-- **The unit Gauss point `η` of `closedPolydisc n K`**, defined by `unitGaussValuation n K` over
any ultrametric normed field `K`. -/
noncomputable def unitGaussPoint (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K]
    [NonarchimedeanRing K] : closedPolydisc n K :=
  ⟨ofValuation (unitGaussValuation n K), (mem_closedPolydisc_iff _ _ _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr isContinuous_unitGaussValuation,
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact unitGaussValuation_le_one_of_isPowerBounded (mem_powerBoundedSubring.mp hf)⟩⟩

/-- The underlying point of `unitGaussPoint n K` in `Spv K⟨T₁, …, Tₙ⟩` is
`ofValuation (unitGaussValuation n K)`. -/
theorem unitGaussPoint_val :
    (unitGaussPoint n K).1 = ofValuation (unitGaussValuation n K) :=
  (rfl)

/-- `unitGaussPoint n K` compares two restricted series by their unit Gauss norms. -/
@[simp]
theorem unitGaussPoint_vle_iff
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).1.toValuativeRel.vle f g ↔
      ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
  rw [unitGaussPoint_val, vle_ofValuation, ← NNReal.coe_le_coe, coe_unitGaussValuation,
    coe_unitGaussValuation]

/-- A point of `closedPolydisc n K` equals `unitGaussPoint n K` if and only if it compares all
pairs of restricted series by their unit Gauss norms. -/
theorem eq_unitGaussPoint_iff {η : closedPolydisc n K} :
    η = unitGaussPoint n K ↔
      ∀ f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
        η.1.toValuativeRel.vle f g ↔
          ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
  refine ⟨fun h ↦ h ▸ unitGaussPoint_vle_iff, fun h ↦ Subtype.ext <| ext' fun f g ↦ ?_⟩
  rw [h f g, unitGaussPoint_vle_iff]

/-- `unitGaussPoint n K` dominates `f` by `0` if and only if `f = 0`. -/
theorem unitGaussPoint_vle_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    (unitGaussPoint n K).1.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [unitGaussPoint_vle_iff, map_zero, norm_zero, norm_le_zero_iff,
    map_eq_zero_iff _ restrictedMvPowerSeriesGaussEquiv.injective]

/-- **The support of `unitGaussPoint n K` is trivial.** -/
@[simp]
theorem supp_unitGaussPoint : (unitGaussPoint n K).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by rw [mem_supp_iff, unitGaussPoint_vle_zero_iff, Ideal.mem_bot]

/-- **For `n ≥ 1`, `unitGaussPoint n K` is never a classical evaluation point.** -/
theorem unitGaussPoint_ne_classicalPoint [NeZero n] [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint n K ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot (unitGaussPoint n K) (supp_unitGaussPoint (n := n) (K := K))
    x a ha

/-- In dimension `1` over a nontrivially normed field, `unitGaussPoint 1 K` agrees with the
radius-`1` Gauss point `gaussPoint zero_lt_one le_rfl`. -/
theorem unitGaussPoint_one_eq_gaussPoint {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [NonarchimedeanRing K] :
    unitGaussPoint 1 K = gaussPoint (K := K) zero_lt_one le_rfl := by
  refine ((eq_unitGaussPoint_iff (n := 1) (K := K)
    (η := gaussPoint (K := K) zero_lt_one le_rfl)).mpr fun f g ↦ ?_).symm
  rw [gaussPoint_vle_iff, ← NNReal.coe_le_coe]
  have hnorm (h : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight) :
      (closedDiscGaussValuation (R := K) zero_lt_one le_rfl h : ℝ) =
        ‖restrictedMvPowerSeriesGaussEquiv h‖ := by
    refine le_antisymm ?_ (MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_)
    · rw [coe_closedDiscGaussValuation]
      refine ciSup_le fun m ↦ ?_
      simpa [coe_restrictedMvPowerSeriesGaussEquiv, Finsupp.prod] using
        MvPowerSeries.norm_coeff_mul_prod_le (restrictedMvPowerSeriesGaussEquiv h)
          (Finsupp.single 0 m)
    · have hν : ν = Finsupp.single 0 (ν 0) :=
        Finsupp.ext fun i ↦ by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
      rw [hν]
      simpa [coe_restrictedMvPowerSeriesGaussEquiv, Finsupp.prod] using
        norm_coeff_mul_pow_le_closedDiscGaussValuation zero_lt_one le_rfl h (ν 0)
  rw [hnorm f, hnorm g]

end UnitGaussPoint

/-! ### Closure of classical points and Howe–Klevdal Lemma 9.3.5 -/

section Closure

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K]

/-- Evaluating the Huber image of a polynomial at a power-bounded tuple agrees with
`MvPolynomial.eval`. -/
private theorem evalAtHom_weightedPolynomialHom (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (p : MvPolynomial (Fin n) K) :
    evalAtHom a ha
        (weightedPolynomialHom (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight p) =
      MvPolynomial.eval a p := by
  rw [evalAtHom_eq_restrictedEval₂, restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom,
    TauCeti.MvPowerSeries.polynomialToRestricted_apply, MvPowerSeries.restrictedEval₂_polynomial,
    MvPolynomial.eval₂_id]

/-- Key reduction lemma for Gauss-point closure: over an infinite canonical residue field
`CanonicalReduction K`, if `g ∈ K⟨T₁, …, Tₙ⟩` has unit Gauss norm `1`, there exists a tuple
`a ∈ (K°)ⁿ` at which `‖g(a)‖ = 1`. -/
private theorem exists_norm_evalAtHom_eq_one_of_norm_eq_one [Infinite (CanonicalReduction K)]
    {g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hg : ‖restrictedMvPowerSeriesGaussEquiv g‖ = 1) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)}, ‖evalAtHom a.1 a.2 g‖ = 1 := by
  classical
  -- Extract a multi-index `ν₀` attaining the Gauss norm `1`.
  obtain ⟨ν₀, hν₀⟩ := exists_nnNorm_coeff_eq_unitGaussValuation g
  have hν₀_norm : ‖MvPowerSeries.coeff ν₀ (g : MvPowerSeries (Fin n) K)‖ = 1 := by
    rw [← coe_nnNorm, hν₀, coe_unitGaussValuation, hg]
  have hcoeff_le (ν : Fin n →₀ ℕ) :
      ‖MvPowerSeries.coeff ν (g : MvPowerSeries (Fin n) K)‖ ≤ 1 := by
    rw [← coe_nnNorm, ← hg, ← coe_unitGaussValuation]
    exact NNReal.coe_le_coe.mpr (nnNorm_coeff_le_unitGaussValuation g ν)
  -- Only finitely many coefficients of `g` have norm at least `1 / 2`.
  have hfin : {ν : Fin n →₀ ℕ |
      (1 / 2 : ℝ) ≤ ‖MvPowerSeries.coeff ν (g : MvPowerSeries (Fin n) K)‖}.Finite := by
    let U := IsUltrametricDist.ball_openAddSubgroup K (by positivity : (0 : ℝ) < 1 / 2)
    refine ((mem_weightedRestrictedSubring.mp g.2).finite_coeff_notMem U).subset
      fun ν hν hmem ↦ ?_
    rw [weightMul_one_weight] at hmem
    exact not_lt_of_ge hν (mem_ball_zero_iff.mp hmem)
  let F : Finset (Fin n →₀ ℕ) := hfin.toFinset
  -- Build the integral polynomial truncation `P_int` on `F` and its residue polynomial `P_bar`.
  let cInt (ν : Fin n →₀ ℕ) : powerBoundedSubring K :=
    ⟨MvPowerSeries.coeff ν (g : MvPowerSeries (Fin n) K),
      mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr (hcoeff_le ν))⟩
  let PInt : MvPolynomial (Fin n) (powerBoundedSubring K) :=
    ∑ ν ∈ F, MvPolynomial.monomial ν (cInt ν)
  let mkRed : powerBoundedSubring K →+* CanonicalReduction K :=
    Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
  let PBar : MvPolynomial (Fin n) (CanonicalReduction K) := PInt.map mkRed
  have hPBar_ne : PBar ≠ 0 := by
    intro h0
    have hc0 : PBar.coeff ν₀ = 0 := by simp [h0]
    have hν₀F : ν₀ ∈ F := by
      rw [hfin.mem_toFinset, Set.mem_ofPred_eq, hν₀_norm]
      norm_num
    simp only [PBar, PInt, MvPolynomial.coeff_map, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hν₀F, ↓reduceIte] at hc0
    have hmem : cInt ν₀ ∈ topologicallyNilpotentIdeal K :=
      Ideal.Quotient.eq_zero_iff_mem.mp hc0
    rw [mem_topologicallyNilpotentIdeal_iff_norm_lt_one] at hmem
    exact hmem.ne hν₀_norm
  -- Since `CanonicalReduction K` is an infinite field, `PBar` does not vanish identically.
  obtain ⟨barA, hbarA⟩ := MvPolynomial.exists_eval_ne_zero hPBar_ne
  choose aInt haInt using fun i ↦ Ideal.Quotient.mk_surjective (barA i)
  let a : Fin n → K := fun i ↦ (aInt i : K)
  have ha : ∀ i, IsPowerBounded (a i) := fun i ↦ mem_powerBoundedSubring.mp (aInt i).2
  refine ⟨⟨a, ha⟩, ?_⟩
  -- Compare `g(a)` with the polynomial truncation `PK(a)` using ultrametricity.
  let PK : MvPolynomial (Fin n) K := PInt.map (powerBoundedSubring K).subtype
  let PT : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedPolynomialHom _ isWeightFamily_one_weight PK
  have hPK_eval : evalAtHom a ha PT = (MvPolynomial.eval aInt PInt : K) := by
    rw [evalAtHom_weightedPolynomialHom, ← Subring.coe_subtype, MvPolynomial.eval₂_comp]
    simp [PK, a, Function.comp_def]
  have hPK_norm : ‖evalAtHom a ha PT‖ = 1 := by
    have hmk : mkRed (MvPolynomial.eval aInt PInt) = MvPolynomial.eval barA PBar := by
      have hcomp : mkRed ∘ aInt = barA := funext haInt
      rw [MvPolynomial.eval₂_comp, hcomp]
      simp [PBar]
    have hnot_lt : ¬ ‖(MvPolynomial.eval aInt PInt : K)‖ < 1 := by
      rw [← mem_topologicallyNilpotentIdeal_iff_norm_lt_one, ← Ideal.Quotient.eq_zero_iff_mem, hmk]
      exact hbarA
    have hle_one : ‖(MvPolynomial.eval aInt PInt : K)‖ ≤ 1 :=
      isPowerBounded_iff_norm_le_one.mp
        (mem_powerBoundedSubring.mp (MvPolynomial.eval aInt PInt).2)
    rw [hPK_eval]
    exact le_antisymm hle_one (not_lt.mp hnot_lt)
  have hdiff_le : ‖restrictedMvPowerSeriesGaussEquiv (g - PT)‖ ≤ 1 / 2 := by
    refine MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_
    simp only [Finsupp.prod, one_pow, Finset.prod_const_one, mul_one,
      coe_restrictedMvPowerSeriesGaussEquiv, AddSubgroupClass.coe_sub, PT,
      coe_weightedPolynomialHom, MvPolynomial.coeff_coe, map_sub]
    by_cases hνF : ν ∈ F
    · simp only [PK, PInt, MvPolynomial.coeff_map, MvPolynomial.coeff_sum,
        MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hνF, ↓reduceIte, Subring.coe_subtype,
        cInt, sub_self, norm_zero]
      positivity
    · have hlt : ‖MvPowerSeries.coeff ν (g : MvPowerSeries (Fin n) K)‖ < 1 / 2 :=
        lt_of_not_ge fun hge ↦ hνF (hfin.mem_toFinset.mpr hge)
      simp only [PK, PInt, MvPolynomial.coeff_map, MvPolynomial.coeff_sum,
        MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hνF, ↓reduceIte, map_zero, sub_zero]
      exact hlt.le
  have hdiff_eval : ‖evalAtHom a ha g - evalAtHom a ha PT‖ < ‖evalAtHom a ha PT‖ := by
    rw [← map_sub, hPK_norm]
    exact (norm_evalAtHom_le a ha (g - PT)).trans_lt (hdiff_le.trans_lt (by norm_num))
  have heq : ‖evalAtHom a ha g‖ = ‖evalAtHom a ha PT‖ := by
    have hadd : evalAtHom a ha g = evalAtHom a ha PT + (evalAtHom a ha g - evalAtHom a ha PT) :=
      (add_sub_cancel _ _).symm
    rw [hadd, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hdiff_eval)]
    exact max_eq_left hdiff_eval.le
  exact heq.trans hPK_norm

/-- Over a complete ultrametric normed field with infinite canonical residue field, every
finite-numerator basic open containing `unitGaussPoint n K` contains a classical point. -/
theorem exists_classicalPoint_mem_basicOpenFinset_of_unitGaussPoint_mem
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K))
    {T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    {s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hη : (unitGaussPoint n K).1 ∈ basicOpenFinset T s) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)},
      (classicalPoint x a.1 a.2).1 ∈ basicOpenFinset T s := by
  rw [mem_basicOpenFinset_iff] at hη
  obtain ⟨hTs, hs0⟩ := hη
  rw [unitGaussPoint_vle_zero_iff] at hs0
  -- Choose a dominant coefficient `c` of `s` and rescale `s` and `T` by `c⁻¹`.
  obtain ⟨ν₀, hν₀⟩ := exists_nnNorm_coeff_eq_unitGaussValuation s
  let c : K := MvPowerSeries.coeff ν₀ (s : MvPowerSeries (Fin n) K)
  have hc_norm : ‖c‖ = ‖restrictedMvPowerSeriesGaussEquiv s‖ := by
    rw [← coe_nnNorm, hν₀, coe_unitGaussValuation]
  have hs_pos : 0 < ‖restrictedMvPowerSeriesGaussEquiv s‖ :=
    norm_pos_iff.mpr ((map_eq_zero_iff _ restrictedMvPowerSeriesGaussEquiv.injective).not.mpr hs0)
  have hc_ne : c ≠ 0 := norm_pos_iff.mp (hc_norm.symm ▸ hs_pos)
  let u : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedC _ isWeightFamily_one_weight c⁻¹
  have hu_norm : ‖restrictedMvPowerSeriesGaussEquiv u‖ = ‖c‖⁻¹ := by
    rw [← coe_unitGaussValuation, unitGaussValuation_weightedC, coe_nnNorm, norm_inv]
  have hs'_norm : ‖restrictedMvPowerSeriesGaussEquiv (u * s)‖ = 1 := by
    rw [← coe_unitGaussValuation, map_mul, NNReal.coe_mul, coe_unitGaussValuation,
      coe_unitGaussValuation, hu_norm, ← hc_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc_ne)]
  obtain ⟨a, ha_s'⟩ := exists_norm_evalAtHom_eq_one_of_norm_eq_one (K := K) hs'_norm
  refine ⟨a, ?_⟩
  have hsa_norm : ‖evalAtHom a.1 a.2 s‖ = ‖c‖ := by
    have hmul : evalAtHom a.1 a.2 (u * s) = c⁻¹ * evalAtHom a.1 a.2 s := by
      rw [map_mul, evalAtHom_weightedC]
    have h1 : ‖c‖⁻¹ * ‖evalAtHom a.1 a.2 s‖ = 1 := by
      rwa [hmul, norm_mul, norm_inv] at ha_s'
    exact ((inv_mul_eq_one₀ (norm_ne_zero_iff.mpr hc_ne)).mp h1).symm
  rw [mem_basicOpenFinset_iff]
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · rw [classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.2, hsa_norm]
    have ht_le : ‖restrictedMvPowerSeriesGaussEquiv t‖ ≤ ‖c‖ := by
      rw [hc_norm, ← unitGaussPoint_vle_iff]
      exact hTs t ht
    have ht'_le : ‖restrictedMvPowerSeriesGaussEquiv (u * t)‖ ≤ 1 := by
      rw [← coe_unitGaussValuation, map_mul, NNReal.coe_mul, coe_unitGaussValuation,
        coe_unitGaussValuation, hu_norm]
      exact (mul_le_mul_of_nonneg_left ht_le (inv_nonneg.mpr (norm_nonneg c))).trans_eq
        (inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc_ne))
    have hta_le : ‖c‖⁻¹ * ‖evalAtHom a.1 a.2 t‖ ≤ 1 := by
      have := (norm_evalAtHom_le a.1 a.2 (u * t)).trans ht'_le
      rwa [map_mul, evalAtHom_weightedC, norm_mul, norm_inv] at this
    have := mul_le_mul_of_nonneg_left hta_le (norm_nonneg c)
    rwa [mul_inv_cancel_left₀ (norm_ne_zero_iff.mpr hc_ne), mul_one] at this
  · rw [classicalPoint_vle, map_zero, vle_iff_norm_le_of_mem_spa x.2, norm_zero, hsa_norm, not_le]
    exact norm_pos_iff.mpr hc_ne

/-- Every open neighbourhood of `unitGaussPoint n K` in `closedPolydisc n K` contains a classical
evaluation point when `CanonicalReduction K` is infinite. -/
theorem exists_classicalPoint_mem_of_unitGaussPoint_mem_isOpen
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K))
    {U : Set (closedPolydisc n K)} (hU : IsOpen U) (hη : unitGaussPoint n K ∈ U) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)}, classicalPoint x a.1 a.2 ∈ U := by
  rw [isOpen_induced_iff] at hU
  obtain ⟨V, hV, rfl⟩ := hU
  obtain ⟨_, ⟨T, s, rfl⟩, hηB, hBV⟩ :=
    (isTopologicalBasis_basicOpenFinset _).mem_nhds_iff.mp (hV.mem_nhds hη)
  obtain ⟨a, haB⟩ := exists_classicalPoint_mem_basicOpenFinset_of_unitGaussPoint_mem x hηB
  exact ⟨a, hBV haB⟩

/-- **Howe–Klevdal II, Lemma 9.3.5 (Gauss-point closure).** Over a complete ultrametric normed
field `K` with infinite canonical residue field `CanonicalReduction K = K° ⧸ K°°`, the unit Gauss
point `unitGaussPoint n K` lies in the closure of the classical evaluation points on
`closedPolydisc n K`. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  rw [mem_closure_iff]
  intro U hU hη
  obtain ⟨a, haU⟩ := exists_classicalPoint_mem_of_unitGaussPoint_mem_isOpen x hU hη
  exact ⟨classicalPoint x a.1 a.2, haU, a, rfl⟩

/-- **For `n ≥ 1` and infinite canonical residue field, the classical-point locus is not closed in
`closedPolydisc n K`**: `unitGaussPoint n K` lies in its closure (`Howe–Klevdal II, Lemma 9.3.5`)
but has trivial support, hence is not classical. -/
theorem not_isClosed_range_classicalPoint [NeZero n] [Infinite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K)) :
    ¬ IsClosed (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  intro hclosed
  have hmem : unitGaussPoint n K ∈
      Set.range (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) := by
    rw [← hclosed.closure_eq]
    exact unitGaussPoint_mem_closure_range_classicalPoint x
  obtain ⟨a, ha⟩ := hmem
  exact unitGaussPoint_ne_classicalPoint x a.1 a.2 ha.symm

/-! ### Boundary cases: `n = 0` and finite residue field -/

/-- For `n = 0`, `unitGaussPoint 0 K` already lies in the range of `classicalPoint` unconditionally
(without any infiniteness assumption on the residue field). -/
theorem unitGaussPoint_zero_mem_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K ∈ Set.range (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  rw [range_classicalPoint_zero]
  exact Set.mem_univ _

/-- **Finite-residue-field obstruction.** When `n ≥ 1` and `CanonicalReduction K` is finite of
cardinality `q`, the rational open `{v | 1 ≤ v(T₀^q - T₀)}` contains `unitGaussPoint n K` and
misses every classical point, so `unitGaussPoint n K` is not in the closure of the classical
points. -/
theorem unitGaussPoint_notMem_closure_range_classicalPoint_of_finite
    [NeZero n] [Finite (CanonicalReduction K)] (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∉ closure (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  let _ : Fintype (CanonicalReduction K) := Fintype.ofFinite (CanonicalReduction K)
  let q : ℕ := Fintype.card (CanonicalReduction K)
  have hq : 1 < q := Fintype.one_lt_card
  let X₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX _ isWeightFamily_one_weight 0
  let P : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    X₀ ^ q - X₀
  -- Show `‖P‖ = 1` using its degree-`1` coefficient `-1` (since `q > 1`) and the ultrametric bound.
  have hP_norm : ‖restrictedMvPowerSeriesGaussEquiv P‖ = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← coe_unitGaussValuation]
      refine NNReal.coe_le_one.mpr (((unitGaussValuation n K).map_sub (X₀ ^ q) X₀).trans ?_)
      refine max_le ?_ ?_
      · rw [map_pow, unitGaussValuation_weightedX, one_pow]
      · rw [unitGaussValuation_weightedX]
    · have hle := nnNorm_coeff_le_unitGaussValuation P (Finsupp.single 0 1)
      rw [← NNReal.coe_le_coe, coe_nnNorm, coe_unitGaussValuation] at hle
      have hpow : MvPowerSeries.coeff (Finsupp.single (0 : Fin n) 1)
          ((X₀ : MvPowerSeries (Fin n) K) ^ q) = 0 := by
        have hXpow : ((X₀ : MvPowerSeries (Fin n) K) ^ q) =
            ((MvPolynomial.X (0 : Fin n) ^ q : MvPolynomial (Fin n) K) :
              MvPowerSeries (Fin n) K) := by
          simp [X₀, coe_weightedX]
        rw [hXpow, MvPolynomial.coeff_coe, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.coeff_monomial]
        have hne : Finsupp.single (0 : Fin n) q ≠ Finsupp.single (0 : Fin n) 1 := fun h ↦ by
          have := Finsupp.ext_iff.mp h 0
          simp only [Finsupp.single_eq_same] at this
          exact hq.ne' this
        simp [hne]
      have hX1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin n) 1)
          (X₀ : MvPowerSeries (Fin n) K) = 1 := by
        simp [X₀, coe_weightedX, MvPowerSeries.coeff_X]
      have hP1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin n) 1)
          (P : MvPowerSeries (Fin n) K) = -1 := by
        simp [P, AddSubgroupClass.coe_sub, hpow, hX1]
      simpa [hP1] using hle
  -- Separate `unitGaussPoint n K` from all classical points by `Subtype.val ⁻¹' basicOpen 1 P`.
  let U : Set (closedPolydisc n K) := Subtype.val ⁻¹' basicOpen 1 P
  have hU_open : IsOpen U := (isOpen_basicOpen 1 P).preimage continuous_subtype_val
  have hηU : unitGaussPoint n K ∈ U := by
    rw [Set.mem_preimage, mem_basicOpen_iff, unitGaussPoint_vle_iff, unitGaussPoint_vle_zero_iff]
    refine ⟨by simp [hP_norm], fun hP0 ↦ by simp [hP0] at hP_norm⟩
  rw [mem_closure_iff]
  intro hcl
  obtain ⟨_, ⟨hU_mem, ⟨a, rfl⟩⟩⟩ := hcl U hU_open hηU
  rw [Set.mem_preimage, mem_basicOpen_iff, classicalPoint_vle, map_one,
    vle_iff_norm_le_of_mem_spa x.2, norm_one] at hU_mem
  -- For any `a₀ ∈ K°`, its residue in `CanonicalReduction K` satisfies `ā₀^q = ā₀`, so
  -- `‖a₀^q - a₀‖ < 1`.
  let a₀ : powerBoundedSubring K := ⟨a.1 0, mem_powerBoundedSubring.mpr (a.2 0)⟩
  let mkRed : powerBoundedSubring K →+* CanonicalReduction K :=
    Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
  have hres : mkRed (a₀ ^ q - a₀) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hlt : ‖((a₀ ^ q - a₀ : powerBoundedSubring K) : K)‖ < 1 :=
    mem_topologicallyNilpotentIdeal_iff_norm_lt_one.mp (Ideal.Quotient.eq_zero_iff_mem.mp hres)
  have heval : evalAtHom a.1 a.2 P = ((a₀ ^ q - a₀ : powerBoundedSubring K) : K) := by
    simp [P, X₀, a₀, map_sub, map_pow, evalAtHom_weightedX]
  rw [← heval] at hlt
  exact hU_mem.1.not_gt hlt

/-- **Exact characterization for `n ≥ 1`.** Over a complete ultrametric normed field `K`, the unit
Gauss point `unitGaussPoint n K` lies in the closure of the classical evaluation points if and only
if the canonical residue field `CanonicalReduction K = K° ⧸ K°°` is infinite. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint_iff_infinite
    [NeZero n] (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) ↔ Infinite (CanonicalReduction K) := by
  refine ⟨fun h ↦ ?_, fun _ ↦ unitGaussPoint_mem_closure_range_classicalPoint x⟩
  rw [← not_finite_iff_infinite]
  intro hfin
  exact unitGaussPoint_notMem_closure_range_classicalPoint_of_finite x h

end Closure

end TauCeti.ValuationSpectrum
