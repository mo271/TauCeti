/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.EvaluationTopology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.ValuedReduction

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
import TauCeti.Topology.Homeomorph.SetCongr
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic

/-!
# The unit Gauss point of the closed polydisc and its rational-point closure

Let `K` be a nontrivially normed ultrametric field and `D^n = closedPolydisc n K` the `n`-variable
closed unit polydisc `Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)`. The unit-radius Gauss norm
`f ↦ sup_ν ‖f_ν‖` on `K⟨T₁, …, Tₙ⟩` is multiplicative, ultrametric, continuous for the Huber
restricted-series topology, and bounded by `1` on `(K⟨T₁, …, Tₙ⟩)°`, so it defines the canonical
*unit Gauss point* `unitGaussPoint n K : D^n`. It is the unique point of `D^n` satisfying
`IsUnitGaussPoint`, has trivial support, is invariant under translations `Tᵢ ↦ Tᵢ + aᵢ` by
power-bounded tuples, and agrees at `n = 1` with `gaussPoint zero_lt_one le_rfl`.

Over a complete nontrivially normed ultrametric field `K`, this file characterizes when
`unitGaussPoint n K` lies in the closure of the classical `K`-rational evaluation points
`{classicalPoint x a.1 a.2 | a ∈ (K°)ⁿ}`:

* **Infinite residue field (`Infinite (CanonicalReduction K)`).** Every nonzero series
  `s ∈ K⟨T₁, …, Tₙ⟩` attains its Gauss norm at some tuple `a ∈ (K°)ⁿ`: scaling `s` by the inverse
  of a coefficient of maximal norm produces a series `s'` of Gauss norm `1` whose canonical
  reduction in `𝓀[K][X₁, …, Xₙ]` is a nonzero polynomial; since `𝓀[K]` is infinite,
  `MvPolynomial.funext_iff` provides a residue tuple where this polynomial does not vanish, and any
  lift `a ∈ (𝒪[K])ⁿ` gives `‖s(a)‖ = ‖s‖`. Consequently every rational open neighbourhood of
  `unitGaussPoint n K` meets the `K`-rational evaluation points, so `unitGaussPoint n K` lies in
  their closure (`unitGaussPoint_mem_closure_range_classicalPoint` and
  `gaussPoint_mem_closure_rationalPoints`). Every closed subset of `D^n` containing all `K`-rational
  points therefore contains `unitGaussPoint n K`, and for `n ≥ 1` the `K`-rational points are not
  closed in `D^n`.
* **Dimension zero (`n = 0`).** Every series in zero variables is constant, so `unitGaussPoint 0 K`
  equals `classicalPoint x 0 _` unconditionally, without any cardinality hypothesis on the residue
  field.
* **Finite residue field (`Finite (CanonicalReduction K)`, `n ≥ 1`).** Writing `q = |𝓀[K]|`, the
  polynomial `P = T₀ ^ q - T₀` has Gauss norm `1` while `‖a₀ ^ q - a₀‖ < 1` for every `a₀ ∈ K°`, so
  the basic open `|1| ≤ |P| ≠ 0` contains `unitGaussPoint n K` and is disjoint from the `K`-rational
  points. Thus for `n ≥ 1`, `unitGaussPoint n K` lies in the closure of the `K`-rational points if
  and only if `CanonicalReduction K` is infinite (`unitGaussPoint_mem_closure_iff_infinite`).

## Main definitions

* `TauCeti.ValuationSpectrum.closedPolydiscUnitGaussValuation`: the unit-radius Gauss norm on
  `R⟨T₁, …, Tₙ⟩` as an `ℝ≥0`-valued valuation, for a normed commutative ring `R` with multiplicative
  ultrametric norm.
* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point of `closedPolydisc n K`.
* `TauCeti.ValuationSpectrum.IsUnitGaussPoint`: predicate characterizing a point of
  `closedPolydisc n K` that compares series by their unit-radius Gauss norms.

## Main results

* `TauCeti.ValuationSpectrum.isUnitGaussPoint_unitGaussPoint` and
  `TauCeti.ValuationSpectrum.isUnitGaussPoint_iff_eq_unitGaussPoint`: existence and uniqueness of
  the point satisfying `IsUnitGaussPoint`.
* `TauCeti.ValuationSpectrum.supp_unitGaussPoint`,
  `TauCeti.ValuationSpectrum.unitGaussPoint_ne_classicalPoint`,
  `TauCeti.ValuationSpectrum.comap_taylorHom_unitGaussPoint`, and
  `TauCeti.ValuationSpectrum.unitGaussPoint_one_eq_gaussPoint`: basic properties and compatibility
  with translation and the one-variable `gaussPoint`.
* `TauCeti.ValuationSpectrum.exists_norm_evalAtHom_eq_norm`: over complete `K` with infinite
  canonical reduction, every `s ∈ K⟨T₁, …, Tₙ⟩` attains its Gauss norm at some `a ∈ (K°)ⁿ`.
* `TauCeti.ValuationSpectrum.exists_classicalPoint_mem_rationalSubset`: every rational open
  containing `unitGaussPoint n K` contains a classical `K`-rational point when
  `CanonicalReduction K` is infinite.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: the unit Gauss point lies in
  the closure of the classical `K`-rational evaluation points when `CanonicalReduction K` is
  infinite.
* `TauCeti.ValuationSpectrum.not_unitGaussPoint_mem_closure_of_finite` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_iff_infinite`: for `n ≥ 1`, closure
  membership holds if and only if `CanonicalReduction K` is infinite.

## References

* S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures II: The bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer, 1984,
  §§5.1.3–5.1.4.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 7.57.
-/

public section

open Filter Topology
open scoped NNReal NormedField

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section NormedRing

variable {n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]
  [NormOneClass R]

variable (n R) in
/-- **The unit-radius Gauss valuation on `R⟨T₁, …, Tₙ⟩`** with values in `ℝ≥0`, sending a restricted
power series `f` to its unit-radius Gauss norm `sup_ν ‖f_ν‖`. -/
noncomputable def closedPolydiscUnitGaussValuation :
    Valuation (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight) ℝ≥0 where
  toFun f := ‖restrictedMvPowerSeriesGaussEquiv f‖₊
  map_zero' := by simp
  map_one' := by
    rw [← NNReal.coe_inj, coe_nnNorm, NNReal.coe_one]
    simp
  map_mul' f g := by simp [nnNorm_mul]
  map_add_le_max' f g := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_max, coe_nnNorm, coe_nnNorm, map_add]
    exact IsUltrametricDist.norm_add_le_max _ _

/-- `closedPolydiscUnitGaussValuation` is the `ℝ≥0`-valued Gauss norm transported along
`restrictedMvPowerSeriesGaussEquiv`. -/
theorem closedPolydiscUnitGaussValuation_apply
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    closedPolydiscUnitGaussValuation n R f = ‖restrictedMvPowerSeriesGaussEquiv f‖₊ :=
  (rfl)

/-- Coerced to `ℝ`, `closedPolydiscUnitGaussValuation` is `MvPowerSeries.gaussNorm` at unit
polyradius. -/
theorem coe_closedPolydiscUnitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (closedPolydiscUnitGaussValuation n R f : ℝ) =
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) R) := by
  rw [closedPolydiscUnitGaussValuation_apply, coe_nnNorm, MvPowerSeries.norm_eq_gaussNorm,
    coe_restrictedMvPowerSeriesGaussEquiv]

@[simp]
theorem closedPolydiscUnitGaussValuation_eq_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight} :
    closedPolydiscUnitGaussValuation n R f = 0 ↔ f = 0 := by
  rw [closedPolydiscUnitGaussValuation_apply, nnNorm_eq_zero, RingEquiv.map_eq_zero_iff]

@[simp]
theorem closedPolydiscUnitGaussValuation_weightedC (a : R) :
    closedPolydiscUnitGaussValuation n R (weightedC _ isWeightFamily_one_weight a) = ‖a‖₊ := by
  rw [← NNReal.coe_inj, closedPolydiscUnitGaussValuation_apply, coe_nnNorm, coe_nnNorm,
    restrictedMvPowerSeriesGaussEquiv_weightedC, MvPowerSeries.norm_algebraMap_isRestrictedSubring]

@[simp]
theorem closedPolydiscUnitGaussValuation_weightedX (i : Fin n) :
    closedPolydiscUnitGaussValuation n R (weightedX _ isWeightFamily_one_weight i) = 1 := by
  rw [← NNReal.coe_inj, closedPolydiscUnitGaussValuation_apply, coe_nnNorm, NNReal.coe_one,
    restrictedMvPowerSeriesGaussEquiv_weightedX, MvPowerSeries.norm_X]

/-- Every monomial `f_ν T^ν` of `f` has unit Gauss valuation at most that of `f`. -/
theorem closedPolydiscUnitGaussValuation_monomial_le
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (ν : Fin n →₀ ℕ) :
    closedPolydiscUnitGaussValuation n R
        (weightedC _ isWeightFamily_one_weight
            (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) R)) *
          ∏ i, weightedX _ isWeightFamily_one_weight i ^ ν i) ≤
      closedPolydiscUnitGaussValuation n R f := by
  rw [map_mul, map_prod, closedPolydiscUnitGaussValuation_weightedC]
  simp only [map_pow, closedPolydiscUnitGaussValuation_weightedX, one_pow, Finset.prod_const_one,
    mul_one]
  rw [closedPolydiscUnitGaussValuation_apply, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
  simpa [Finsupp.prod] using
    MvPowerSeries.norm_coeff_mul_prod_le (restrictedMvPowerSeriesGaussEquiv f) ν

/-- **The unit Gauss valuation is continuous** for the Huber restricted-series topology. -/
theorem isContinuous_closedPolydiscUnitGaussValuation :
    (closedPolydiscUnitGaussValuation n R).IsContinuous := by
  refine Valuation.isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  rcases eq_or_ne γ 0 with rfl | _
  · simp
  have heq : {f | closedPolydiscUnitGaussValuation n R f < γ} =
      restrictedMvPowerSeriesGaussEquiv ⁻¹' Metric.ball 0 (γ : ℝ) := by
    ext f
    simp [closedPolydiscUnitGaussValuation_apply, ← NNReal.coe_lt_coe]
  rw [heq]
  exact Metric.isOpen_ball.preimage continuous_restrictedMvPowerSeriesGaussEquiv

end NormedRing

section UnitGaussPoint

variable {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Over a nontrivially normed ultrametric field `K`, the unit Gauss valuation is at most `1` on
power-bounded elements of `K⟨T₁, …, Tₙ⟩`. -/
theorem closedPolydiscUnitGaussValuation_le_one_of_isPowerBounded
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : IsPowerBounded f) : closedPolydiscUnitGaussValuation n K f ≤ 1 := by
  have hf' : restrictedMvPowerSeriesGaussEquiv f ∈
      powerBoundedSubring (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) := by
    rw [mem_powerBoundedSubring]
    exact (isPowerBounded_ringEquiv_iff restrictedMvPowerSeriesGaussEquiv
      continuous_restrictedMvPowerSeriesGaussEquiv
      continuous_restrictedMvPowerSeriesGaussEquiv_symm).mpr hf
  rw [TauCeti.MvPowerSeries.powerBoundedSubring_eq_unitClosedBall,
    Subring.mem_unitClosedBall] at hf'
  rw [closedPolydiscUnitGaussValuation_apply]
  exact NNReal.coe_le_one.mp (by simpa using hf')

variable (n K) in
/-- **The unit Gauss point of `closedPolydisc n K`**, defined by the unit-radius Gauss norm on
`K⟨T₁, …, Tₙ⟩`. -/
noncomputable def unitGaussPoint : closedPolydisc n K :=
  ⟨ofValuation (closedPolydiscUnitGaussValuation n K), (mem_closedPolydisc_iff n K _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr isContinuous_closedPolydiscUnitGaussValuation,
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact closedPolydiscUnitGaussValuation_le_one_of_isPowerBounded
          (mem_powerBoundedSubring.mp hf)⟩⟩

theorem unitGaussPoint_val :
    (unitGaussPoint n K).1 = ofValuation (closedPolydiscUnitGaussValuation n K) :=
  (rfl)

@[simp]
theorem unitGaussPoint_vle_iff
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).1.toValuativeRel.vle f g ↔
      closedPolydiscUnitGaussValuation n K f ≤ closedPolydiscUnitGaussValuation n K g := by
  rw [unitGaussPoint_val, vle_ofValuation]

/-- **Predicate for the unit Gauss point** on `closedPolydisc n K`: `η` compares restricted power
series by their unit-radius Gauss norms. -/
def IsUnitGaussPoint (η : closedPolydisc n K) : Prop :=
  ∀ f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
    η.1.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
        MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K)

/-- `unitGaussPoint n K` satisfies `IsUnitGaussPoint`. -/
theorem isUnitGaussPoint_unitGaussPoint : IsUnitGaussPoint (unitGaussPoint n K) := by
  intro f g
  rw [unitGaussPoint_vle_iff, ← NNReal.coe_le_coe, coe_closedPolydiscUnitGaussValuation,
    coe_closedPolydiscUnitGaussValuation]

/-- **Uniqueness of the unit Gauss point**: a point of `closedPolydisc n K` satisfies
`IsUnitGaussPoint` if and only if it equals `unitGaussPoint n K`. -/
theorem isUnitGaussPoint_iff_eq_unitGaussPoint {η : closedPolydisc n K} :
    IsUnitGaussPoint η ↔ η = unitGaussPoint n K := by
  refine ⟨fun h ↦ Subtype.ext (ext' fun f g ↦ ?_), fun h ↦ h ▸ isUnitGaussPoint_unitGaussPoint⟩
  rw [h f g, ← isUnitGaussPoint_unitGaussPoint f g]

/-- The support of `unitGaussPoint n K` is trivial. -/
@[simp]
theorem supp_unitGaussPoint : (unitGaussPoint n K).1.supp = ⊥ := by
  ext f
  rw [mem_supp_iff, unitGaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero,
    closedPolydiscUnitGaussValuation_eq_zero_iff, Ideal.mem_bot]

/-- Over a complete field in positive dimension, `unitGaussPoint n K` is not a classical point. -/
theorem unitGaussPoint_ne_classicalPoint [NeZero n] [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint n K ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot (unitGaussPoint n K) supp_unitGaussPoint x a ha

/-- In dimension `1`, `unitGaussPoint 1 K` agrees with the radius-`1` Gauss point `gaussPoint`. -/
theorem unitGaussPoint_one_eq_gaussPoint :
    unitGaussPoint 1 K = gaussPoint (K := K) zero_lt_one le_rfl := by
  refine Subtype.ext (ext' fun f g ↦ ?_)
  rw [unitGaussPoint_vle_iff, gaussPoint_vle_iff, ← NNReal.coe_le_coe, ← NNReal.coe_le_coe,
    coe_closedPolydiscUnitGaussValuation, coe_closedPolydiscUnitGaussValuation,
    coe_closedDiscGaussValuation, coe_closedDiscGaussValuation]
  have hnorm (h : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight) :
      MvPowerSeries.gaussNorm norm (fun _ : Fin 1 ↦ (1 : ℝ)) (h : MvPowerSeries (Fin 1) K) =
        ⨆ m : ℕ,
          ‖MvPowerSeries.coeff (Finsupp.single 0 m) (h : MvPowerSeries (Fin 1) K)‖ *
            (1 : ℝ) ^ m := by
    rw [← coe_restrictedMvPowerSeriesGaussEquiv h, ← MvPowerSeries.norm_eq_gaussNorm]
    refine le_antisymm (MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_)
      (ciSup_le fun m ↦ by
        simpa [Finsupp.prod] using
          MvPowerSeries.norm_coeff_mul_prod_le (restrictedMvPowerSeriesGaussEquiv h)
            (Finsupp.single 0 m))
    have hν : ν = Finsupp.single 0 (ν 0) :=
      Finsupp.ext fun i ↦ by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
    have hle := le_ciSup
      ⟨‖restrictedMvPowerSeriesGaussEquiv h‖, Set.forall_mem_range.mpr fun m ↦ by
        simpa [Finsupp.prod] using
          MvPowerSeries.norm_coeff_mul_prod_le (restrictedMvPowerSeriesGaussEquiv h)
            (Finsupp.single 0 m)⟩ (ν 0)
    simpa [← hν, Finsupp.prod] using hle
  rw [hnorm f, hnorm g]

/-- **Translation invariance of the unit Gauss point** over a complete field: pulling back along
`Tᵢ ↦ Tᵢ + aᵢ` for `a ∈ (K°)ⁿ` fixes `unitGaussPoint n K`. -/
theorem comap_taylorHom_unitGaussPoint [CompleteSpace K] (a : Fin n → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    comap (taylorHom a ha) (unitGaussPoint n K).1 = (unitGaussPoint n K).1 := by
  have hval (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight) :
      closedPolydiscUnitGaussValuation n K (taylorHom a ha f) =
        closedPolydiscUnitGaussValuation n K f := by
    refine valuation_taylorHom_eq a ha isContinuous_closedPolydiscUnitGaussValuation
      (fun i ↦ ?_) closedPolydiscUnitGaussValuation_monomial_le f
    refine (Valuation.map_add _ _ _).trans (max_le le_rfl ?_)
    rw [closedPolydiscUnitGaussValuation_weightedC, closedPolydiscUnitGaussValuation_weightedX,
      ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]
    exact isPowerBounded_iff_norm_le_one.mp (ha i)
  refine ext' fun f g ↦ ?_
  rw [comap_vle, unitGaussPoint_vle_iff, unitGaussPoint_vle_iff, hval f, hval g]

end UnitGaussPoint

section Closure

variable {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Rational maximum-modulus attainment over infinite residue fields.** When
`CanonicalReduction K` is infinite, every restricted series `s ∈ K⟨T₁, …, Tₙ⟩` attains its
unit-radius Gauss norm at some tuple `a ∈ (K°)ⁿ`. -/
theorem exists_norm_evalAtHom_eq_norm [Infinite (CanonicalReduction K)]
    (s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)},
      ‖evalAtHom a.1 a.2 s‖ = ‖restrictedMvPowerSeriesGaussEquiv s‖ := by
  have : Infinite (Valued.ResidueField K) := (infinite_canonicalReduction_iff K).mp inferInstance
  let G := MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ (1 : ℝ))
  set S : G := restrictedMvPowerSeriesGaussEquiv s
  rcases eq_or_ne S 0 with hS0 | hS0
  · refine ⟨⟨0, fun _ ↦ isPowerBounded_zero⟩, ?_⟩
    have hs0 : s = 0 := restrictedMvPowerSeriesGaussEquiv.injective (by simpa [S] using hS0)
    simp [hs0, S, hS0]
  obtain ⟨ν₀, hν₀⟩ := MvPowerSeries.exists_norm_coeff_eq_norm S
  set c : K := MvPowerSeries.coeff ν₀ (S : MvPowerSeries (Fin n) K)
  have hc_pos : 0 < ‖c‖ := hν₀.symm ▸ norm_pos_iff.mpr hS0
  have hS'_norm : ‖algebraMap K G c⁻¹ * S‖ = 1 := by
    rw [norm_mul, MvPowerSeries.norm_algebraMap_isRestrictedSubring, norm_inv, ← hν₀,
      inv_mul_cancel₀ hc_pos.ne']
  let s' : Subring.unitClosedBall G :=
    ⟨algebraMap K G c⁻¹ * S, Subring.mem_unitClosedBall.mpr hS'_norm.le⟩
  have hred_ne : TauCeti.MvPowerSeries.restrictedReduction s' ≠ 0 :=
    TauCeti.MvPowerSeries.restrictedReduction_ne_zero_iff.mpr hS'_norm
  have hex_bar : ∃ bar_a : Fin n → Valued.ResidueField K,
      MvPolynomial.eval bar_a (TauCeti.MvPowerSeries.restrictedReduction s') ≠ 0 := by
    by_contra! hall
    exact hred_ne (MvPolynomial.funext fun bar_a ↦ by simpa using hall bar_a)
  obtain ⟨bar_a, hbar_a⟩ := hex_bar
  choose a₀ ha₀ using fun i ↦ IsLocalRing.residue_surjective (R := Valued.integer K) (bar_a i)
  have ha_pb : ∀ i : Fin n, IsPowerBounded ((a₀ i : Valued.integer K) : K) :=
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.mem_iff.mp (a₀ i).2)
  refine ⟨⟨fun i ↦ (a₀ i : K), ha_pb⟩, ?_⟩
  have hmap_id : IsLocalRing.ResidueField.map
      ((RingHom.id K).integerRestrict (fun _ ↦ le_rfl)) =
        RingHom.id (Valued.ResidueField K) := by
    ext x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.map_residue]
    exact congrArg _ (Subtype.ext (by simp))
  have hnot_lt : ¬ ‖MvPowerSeries.restrictedEval₂ (RingHom.id K) (fun i ↦ (a₀ i : K))
      (fun _ ↦ le_rfl) (fun i ↦ Valued.integer.mem_iff.mp (a₀ i).2) (s' : G)‖ < 1 := by
    rw [TauCeti.MvPowerSeries.norm_restrictedEval₂_lt_one_iff, hmap_id, MvPolynomial.eval₂_id]
    simpa only [ha₀] using hbar_a
  have hs'_ev_eq : ‖MvPowerSeries.restrictedEval₂ (RingHom.id K) (fun i ↦ (a₀ i : K))
      (fun _ ↦ le_rfl) (fun i ↦ Valued.integer.mem_iff.mp (a₀ i).2) (s' : G)‖ = 1 :=
    le_antisymm
      ((MvPowerSeries.norm_restrictedEval₂_le _ _ _ _ (s' : G)).trans hS'_norm.le)
      (not_lt.mp hnot_lt)
  have hmul_ev : MvPowerSeries.restrictedEval₂ (RingHom.id K) (fun i ↦ (a₀ i : K))
      (fun _ ↦ le_rfl) (fun i ↦ Valued.integer.mem_iff.mp (a₀ i).2) (s' : G) =
      c⁻¹ * evalAtHom (fun i ↦ (a₀ i : K)) ha_pb s := by
    have hs'_coe : (s' : G) = algebraMap K G c⁻¹ * S := rfl
    rw [hs'_coe, map_mul, MvPowerSeries.restrictedEval₂_algebraMap, RingHom.id_apply,
      evalAtHom_eq_restrictedEval₂]
  rw [hmul_ev, norm_mul, norm_inv] at hs'_ev_eq
  calc ‖evalAtHom (fun i ↦ (a₀ i : K)) ha_pb s‖
      = ‖c‖ * (‖c‖⁻¹ * ‖evalAtHom (fun i ↦ (a₀ i : K)) ha_pb s‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc_pos.ne', one_mul]
    _ = ‖c‖ * 1 := by rw [hs'_ev_eq]
    _ = ‖S‖ := by rw [mul_one, hν₀]

/-- Every `basicOpenFinset T s` containing `unitGaussPoint n K` contains a classical `K`-rational
point when `CanonicalReduction K` is infinite. -/
theorem exists_classicalPoint_mem_basicOpenFinset [Infinite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hη : (unitGaussPoint n K).1 ∈ basicOpenFinset T s) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)},
      (classicalPoint x a.1 a.2).1 ∈ basicOpenFinset T s := by
  rw [mem_basicOpenFinset_iff] at hη
  obtain ⟨a, ha_eq⟩ := exists_norm_evalAtHom_eq_norm s
  refine ⟨a, ?_⟩
  rw [mem_basicOpenFinset_iff]
  have hs_pos : 0 < ‖restrictedMvPowerSeriesGaussEquiv s‖ := by
    refine norm_pos_iff.mpr fun hs0 ↦ hη.2 ?_
    rw [unitGaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero,
      closedPolydiscUnitGaussValuation_eq_zero_iff]
    exact restrictedMvPowerSeriesGaussEquiv.injective (by simpa using hs0)
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · rw [classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.2, ha_eq]
    have hts := (unitGaussPoint_vle_iff t s).mp (hη.1 t ht)
    rw [closedPolydiscUnitGaussValuation_apply, closedPolydiscUnitGaussValuation_apply,
      ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm] at hts
    exact (norm_evalAtHom_le a.1 a.2 t).trans hts
  · rw [classicalPoint_vle, map_zero, vle_iff_norm_le_of_mem_spa x.2, norm_zero, norm_le_zero_iff]
    exact norm_pos_iff.mp (ha_eq ▸ hs_pos)

/-- **Every rational subset of `closedPolydisc n K` containing `unitGaussPoint n K` contains a
classical `K`-rational point** when `CanonicalReduction K` is infinite. -/
theorem exists_classicalPoint_mem_rationalSubset [Infinite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hη : (unitGaussPoint n K).1 ∈ rationalSubset (powerBoundedSubring _) T s) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)},
      (classicalPoint x a.1 a.2).1 ∈ rationalSubset (powerBoundedSubring _) T s := by
  rw [mem_rationalSubset_iff] at hη
  have hbo : (unitGaussPoint n K).1 ∈ basicOpenFinset T s :=
    (mem_basicOpenFinset_iff T s _).mpr ⟨hη.2.1, hη.2.2⟩
  obtain ⟨a, ha⟩ := exists_classicalPoint_mem_basicOpenFinset x T s hbo
  rw [mem_basicOpenFinset_iff] at ha
  refine ⟨a, (mem_rationalSubset_iff _ T s _).mpr ?_⟩
  exact ⟨closedPolydisc_def n K ▸ (classicalPoint x a.1 a.2).2, ha.1, ha.2⟩

/-- **The unit Gauss point lies in the closure of the classical `K`-rational points** on
`closedPolydisc n K` over every complete nontrivially normed ultrametric field `K` with infinite
residue field `CanonicalReduction K`. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint [Infinite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈
      closure (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) := by
  have : IsHuberRing K := (IsTateRing.of_nontriviallyNormedField K).toIsHuberRing
  let e := Homeomorph.setCongr (closedPolydisc_def n K)
  rw [mem_closure_iff]
  intro U hU hηU
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hηU' : e (unitGaussPoint n K) ∈ e.symm ⁻¹' U := by simpa using hηU
  obtain ⟨W, hW, hηW, hWU⟩ :=
    (isTopologicalBasis_spaRationalFamily _).isOpen_iff.mp hU' (e (unitGaussPoint n K)) hηU'
  obtain ⟨T, s, -, rfl⟩ := mem_spaRationalFamily_iff.mp hW
  obtain ⟨a, ha⟩ := exists_classicalPoint_mem_rationalSubset x T s
    (by simpa only [e, Set.mem_preimage, Homeomorph.setCongr_apply] using hηW)
  have haW :
      e (classicalPoint x a.1 a.2) ∈
        Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s := by
    simpa only [e, Set.mem_preimage, Homeomorph.setCongr_apply] using ha
  exact ⟨classicalPoint x a.1 a.2, by simpa using hWU haW, a, rfl⟩

/-- **Gauss-point closure.** Over a complete nontrivially normed ultrametric field `K` whose
canonical reduction `K° ⧸ K°°` is infinite, the unit Gauss point exists on `closedPolydisc n K` in
every dimension `n` and lies in the closure of the evaluation points at tuples of power-bounded
elements of `K` (Howe–Klevdal II, proof of Lemma 9.3.5). -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (n : ℕ) (x : spa (powerBoundedSubring K)) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint η ∧ η ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.1 a.2)) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint,
    unitGaussPoint_mem_closure_range_classicalPoint x⟩

/-- Every closed subset of `closedPolydisc n K` containing all classical `K`-rational evaluation
points also contains `unitGaussPoint n K` when `CanonicalReduction K` is infinite. -/
theorem unitGaussPoint_mem_of_isClosed_of_range_classicalPoint_subset
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K))
    {F : Set (closedPolydisc n K)} (hF : IsClosed F)
    (hsub : Set.range (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) ⊆ F) :
    unitGaussPoint n K ∈ F :=
  (closure_minimal hsub hF) (unitGaussPoint_mem_closure_range_classicalPoint x)

/-- In positive dimension over a complete nontrivially normed ultrametric field with infinite
residue field, the set of classical `K`-rational points is not closed in `closedPolydisc n K`. -/
theorem not_isClosed_range_classicalPoint [NeZero n] [Infinite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K)) :
    ¬ IsClosed (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  intro hclosed
  obtain ⟨a, ha⟩ := unitGaussPoint_mem_of_isClosed_of_range_classicalPoint_subset x hclosed
    Set.Subset.rfl
  exact unitGaussPoint_ne_classicalPoint x a.1 a.2 ha.symm

/-! ### Dimension zero and the finite-residue obstruction -/

/-- In dimension `0`, `unitGaussPoint 0 K` equals the unique classical point `classicalPoint x 0 _`,
with no hypothesis on the residue field of `K`. -/
theorem unitGaussPoint_zero_eq_classicalPoint (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K =
      classicalPoint x (0 : Fin 0 → K) (fun i ↦ Fin.elim0 i) := by
  refine Subtype.ext (ext' fun f g ↦ ?_)
  obtain ⟨c, hc⟩ := MvPowerSeries.C_surjective (f : MvPowerSeries (Fin 0) K)
  obtain ⟨d, hd⟩ := MvPowerSeries.C_surjective (g : MvPowerSeries (Fin 0) K)
  have hf : f = weightedC _ isWeightFamily_one_weight c :=
    Subtype.ext (hc.symm.trans (coe_weightedC c).symm)
  have hg : g = weightedC _ isWeightFamily_one_weight d :=
    Subtype.ext (hd.symm.trans (coe_weightedC d).symm)
  rw [hf, hg, unitGaussPoint_vle_iff, classicalPoint_vle, evalAtHom_weightedC, evalAtHom_weightedC,
    vle_iff_norm_le_of_mem_spa x.2, closedPolydiscUnitGaussValuation_weightedC,
    closedPolydiscUnitGaussValuation_weightedC, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]

/-- Unconditionally in dimension `0`, `unitGaussPoint 0 K` lies in the closure of the classical
`K`-rational points over every complete nontrivially normed ultrametric field `K`. -/
theorem unitGaussPoint_zero_mem_closure_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K ∈
      closure (Set.range fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) :=
  subset_closure ⟨⟨0, fun i ↦ Fin.elim0 i⟩, (unitGaussPoint_zero_eq_classicalPoint x).symm⟩

/-- **Finite-residue obstruction in positive dimension.** If `n ≥ 1` and `CanonicalReduction K` is
finite of cardinality `q`, then `P = T₀ ^ q - T₀` has Gauss norm `1` while `‖P(a)‖ < 1` at every
`a ∈ (K°)ⁿ`, so the basic open `|1| ≤ |P| ≠ 0` separates `unitGaussPoint n K` from the classical
`K`-rational points. -/
theorem not_unitGaussPoint_mem_closure_of_finite [NeZero n] [Finite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∉
      closure (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) := by
  have : Finite (Valued.ResidueField K) := (finite_canonicalReduction_iff K).mp inferInstance
  let _ : Fintype (Valued.ResidueField K) := Fintype.ofFinite (Valued.ResidueField K)
  set q := Fintype.card (Valued.ResidueField K)
  have hq : 1 < q := Fintype.one_lt_card
  set T₀ := weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight 0
  set P := T₀ ^ q - T₀
  have hP_val : closedPolydiscUnitGaussValuation n K P = 1 := by
    refine le_antisymm ?_ ?_
    · refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · rw [map_pow, closedPolydiscUnitGaussValuation_weightedX, one_pow]
      · rw [closedPolydiscUnitGaussValuation_weightedX]
    · rw [closedPolydiscUnitGaussValuation_apply, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnNorm]
      have hsingle_ne : Finsupp.single (0 : Fin n) q ≠ Finsupp.single (0 : Fin n) 1 := by
        intro h
        have h' := Finsupp.ext_iff.mp h 0
        simp only [Finsupp.single_eq_same] at h'
        omega
      have hcoeff : MvPowerSeries.coeff (Finsupp.single (0 : Fin n) 1)
          (P : MvPowerSeries (Fin n) K) = -1 := by
        rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_weightedX,
          MvPowerSeries.X_pow_eq, map_sub, MvPowerSeries.coeff_monomial_ne hsingle_ne.symm,
          MvPowerSeries.coeff_X]
        simp only [↓reduceIte, zero_sub]
      have hle := MvPowerSeries.norm_coeff_mul_prod_le (restrictedMvPowerSeriesGaussEquiv P)
        (Finsupp.single (0 : Fin n) 1)
      simpa [Finsupp.prod, hcoeff] using hle
  let U : Set (closedPolydisc n K) := Subtype.val ⁻¹' basicOpen 1 P
  have hUopen : IsOpen U := (isOpen_basicOpen 1 P).preimage continuous_subtype_val
  have hηU : unitGaussPoint n K ∈ U := by
    simp [U, mem_basicOpen_iff, unitGaussPoint_vle_iff, hP_val]
  intro hcl
  obtain ⟨_, hUmem, a, rfl⟩ := (mem_closure_iff.mp hcl) U hUopen hηU
  simp only [U, P, T₀, Set.mem_preimage, mem_basicOpen_iff, classicalPoint_vle, map_one, map_sub,
    map_pow, evalAtHom_weightedX, vle_iff_norm_le_of_mem_spa x.2, norm_one] at hUmem
  let a₀ : Valued.integer K :=
    ⟨a.1 0, Valued.integer.mem_iff.mpr (isPowerBounded_iff_norm_le_one.mp (a.2 0))⟩
  have hres : IsLocalRing.residue (Valued.integer K) (a₀ ^ q - a₀) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hlt : ‖a.1 0 ^ q - a.1 0‖ < 1 := by
    simpa [a₀] using (Valued.integer.residue_eq_zero_iff_norm_lt_one (x := a₀ ^ q - a₀)).mp hres
  exact hUmem.1.not_gt hlt

/-- **Sharp residue-field criterion in positive dimension.** Over a complete nontrivially normed
ultrametric field `K` and for `n ≥ 1`, `unitGaussPoint n K` lies in the closure of the classical
`K`-rational evaluation points if and only if `CanonicalReduction K` is infinite. -/
theorem unitGaussPoint_mem_closure_iff_infinite [NeZero n] (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈
        closure (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.1 a.2) ↔
      Infinite (CanonicalReduction K) := by
  refine ⟨fun h ↦ ?_, fun h ↦ unitGaussPoint_mem_closure_range_classicalPoint x⟩
  by_contra hinf
  have : Finite (CanonicalReduction K) := not_infinite_iff_finite.mp hinf
  exact not_unitGaussPoint_mem_closure_of_finite x h

end Closure

end TauCeti.ValuationSpectrum
