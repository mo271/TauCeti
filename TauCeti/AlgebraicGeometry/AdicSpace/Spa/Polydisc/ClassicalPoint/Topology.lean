/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import Mathlib.Topology.Baire.CompleteMetrizable

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Lipschitz

/-!
# Subspace topology and Baire property of rational points on the closed polydisc

Let `K` be a complete ultrametric normed field and `D = closedPolydisc k K` the closed unit
polydisc `Spa(K⟨T₁, …, Tₖ⟩, K⟨T₁, …, Tₖ⟩°)` of dimension `k`. Every tuple `a ∈ (K°)ᵏ` of
power-bounded elements gives a classical evaluation point `classicalPoint x a ha : D`, which is
independent of the base point `x : Spa(K, K°)` because `Spa(K, K°)` compares scalars by their norms.

This file identifies the subspace topology on the rational locus `D(K)` induced from `D`:

* **Lipschitz evaluation (`norm_evalAtHom_sub_le`, `continuous_evalAtHom_point`):** via the
  continuous Gauss comparison `K⟨T⟩ ≃+* K{T}`, evaluating a restricted series `f` is Lipschitz in
  the tuple `a ∈ (K°)ᵏ` with constant equal to the unit Gauss norm of `f`.
* **Continuity of the classical-point map (`continuous_classicalPoint`):** for every basic open
  `Spv(K⟨T⟩)(f/s)`, ultrametric norm stability makes `‖s(b)‖ = ‖s(a)‖ ≠ 0` and
  `‖f(b)‖ ≤ ‖s(b)‖` on a norm ball around any `a` in the preimage, so `(K°)ᵏ → D` is continuous
  even when the norm on `K` is trivial.
* **Subpolydiscs and homeomorphism onto the image (`closedSubpolydisc`,
  `isEmbedding_classicalPoint`, `classicalPointHomeomorph`):** the rational locus
  `closedSubpolydisc a c` cut out by `|Tᵢ - aᵢ| ≤ |c| ≠ 0` pulls back along `classicalPoint` to
  the clopen metric ball of radius `‖c‖` around `a`. When `K` is nontrivially normed, small nonzero
  scalars exist, so `(K°)ᵏ → D` is a topological embedding onto `D(K)`.
* **Completeness and Baire property (`instCompleteSpaceSubtypeForallIsPowerBounded`,
  `baireSpace_range_classicalPoint`):** `(K°)ᵏ` is the closed unit ball of `Kᵏ`, hence a complete
  metric space and a Baire space, and when `K` is nontrivially normed its homeomorphic image `D(K)`
  in `D` is also a Baire space.
* **Zero-dimensional case (`eq_classicalPoint_zero`, `range_classicalPoint_zero`):** for `k = 0`,
  `closedPolydisc 0 K` consists of the single classical point at the empty tuple.

## Main definitions

* `TauCeti.ValuationSpectrum.closedSubpolydisc`: the rational locus `D(a, |c|)` inside
  `closedPolydisc k K` cut out by `v(Tᵢ - aᵢ) ≤ v(c) ≠ 0`.
* `TauCeti.ValuationSpectrum.classicalPointHomeomorph`: the homeomorphism between `(K°)ᵏ` and its
  image in `closedPolydisc k K` over a nontrivially normed complete ultrametric field `K`.

## Main results

* `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_le` and
  `TauCeti.ValuationSpectrum.continuous_evalAtHom_point`: Lipschitz and continuity properties of
  restricted power-series evaluation in the tuple `a ∈ (K°)ᵏ`.
* `TauCeti.ValuationSpectrum.continuous_classicalPoint`: continuity of `(K°)ᵏ → closedPolydisc k K`
  over any complete ultrametric normed field.
* `TauCeti.ValuationSpectrum.isEmbedding_classicalPoint`: `(K°)ᵏ → closedPolydisc k K` is a
  topological embedding when `K` is nontrivially normed.
* `TauCeti.ValuationSpectrum.baireSpace_range_classicalPoint`: the rational-point locus inside
  `closedPolydisc k K` is a Baire space when `K` is nontrivially normed.
* `TauCeti.ValuationSpectrum.eq_classicalPoint_zero` and
  `TauCeti.ValuationSpectrum.range_classicalPoint_zero`: in dimension `0`, the classical points fill
  `closedPolydisc 0 K`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50, Theorem 7.35,
  and Example 7.57.
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.1.4.
-/

public section

open Filter Set Topology

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

/-! ### Multivariable closed subpolydiscs -/

section Subpolydisc

variable {k : ℕ} {K : Type*} [CommRing K] [TopologicalSpace K] [NonarchimedeanRing K]

/-- **The closed subpolydisc `D(a, |c|)`** of `closedPolydisc k K` cut out by the valuation
conditions `v(Tᵢ - aᵢ) ≤ v(c) ≠ 0` for every coordinate `i : Fin k`. -/
def closedSubpolydisc (a : Fin k → K) (c : K) : Set (closedPolydisc k K) :=
  {v | (∀ i : Fin k, v.1.toValuativeRel.vle
      (weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
        weightedC _ isWeightFamily_one_weight (a i))
      (weightedC _ isWeightFamily_one_weight c)) ∧
    ¬ v.1.toValuativeRel.vle (weightedC _ isWeightFamily_one_weight c) 0}

/-- Membership in `closedSubpolydisc a c` is the coordinatewise valuation bound against `c` and
nonvanishing of `c`. -/
@[simp]
theorem mem_closedSubpolydisc (a : Fin k → K) (c : K) (v : closedPolydisc k K) :
    v ∈ closedSubpolydisc a c ↔
      (∀ i : Fin k, v.1.toValuativeRel.vle
        (weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
          weightedC _ isWeightFamily_one_weight (a i))
        (weightedC _ isWeightFamily_one_weight c)) ∧
      ¬ v.1.toValuativeRel.vle (weightedC _ isWeightFamily_one_weight c) 0 :=
  Iff.rfl

open scoped Classical in
/-- `closedSubpolydisc a c` is the trace of the rational subset with numerators
`{Tᵢ - aᵢ | i} ∪ {c}` and denominator `c`. -/
theorem closedSubpolydisc_eq_rationalSubset (a : Fin k → K) (c : K) :
    closedSubpolydisc a c = Subtype.val ⁻¹'
      rationalSubset (powerBoundedSubring
          (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight))
        ((Finset.univ.image fun i : Fin k ↦
            weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
              weightedC _ isWeightFamily_one_weight (a i)) ∪
          {weightedC _ isWeightFamily_one_weight c})
        (weightedC _ isWeightFamily_one_weight c) := by
  ext v
  have hv : v.1 ∈ spa (powerBoundedSubring
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight)) :=
    closedPolydisc_def k K ▸ v.2
  simp [mem_closedSubpolydisc, mem_rationalSubset_iff, hv]

/-- Every `closedSubpolydisc a c` is open in `closedPolydisc k K`. -/
theorem isOpen_closedSubpolydisc (a : Fin k → K) (c : K) : IsOpen (closedSubpolydisc a c) := by
  classical
  have h := isOpen_val_preimage_rationalSubset
    (Aplus := powerBoundedSubring
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight))
    ((Finset.univ.image fun i : Fin k ↦
        weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
          weightedC _ isWeightFamily_one_weight (a i)) ∪
      {weightedC _ isWeightFamily_one_weight c})
    (weightedC _ isWeightFamily_one_weight c)
  have h' : IsOpen ((Homeomorph.setCongr (closedPolydisc_def k K)) ⁻¹' _) :=
    h.preimage (Homeomorph.setCongr (closedPolydisc_def k K)).continuous
  convert h' using 1
  rw [closedSubpolydisc_eq_rationalSubset]
  rfl

/-- When `c` is a unit of `K`, `closedSubpolydisc a c` belongs to `spaRationalFamily`. -/
theorem closedSubpolydisc_mem_spaRationalFamily_of_isUnit (a : Fin k → K) {c : K}
    (hc : IsUnit c) :
    (Homeomorph.setCongr (closedPolydisc_def k K)).symm ⁻¹' closedSubpolydisc a c ∈
      spaRationalFamily (powerBoundedSubring
        (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight)) := by
  classical
  rw [closedSubpolydisc_eq_rationalSubset]
  exact val_preimage_rationalSubset_mem_spaRationalFamily_of_isUnit _ _
    (hc.map (weightedC _ isWeightFamily_one_weight))

end Subpolydisc

/-! ### Completeness of `(K°)ᵏ`, Lipschitz evaluation, and continuity of `classicalPoint` -/

section PowerBoundedTuples

variable {k : ℕ} {K : Type*} [NormedField K]

/-- The set `(K°)ᵏ` of tuples with power-bounded coordinates is the closed unit ball of `Kᵏ`. -/
theorem setOf_forall_isPowerBounded_eq_closedBall :
    {a : Fin k → K | ∀ i, IsPowerBounded (a i)} = Metric.closedBall 0 1 := by
  ext a
  simp only [Set.mem_ofPred_eq, isPowerBounded_iff_norm_le_one, Metric.mem_closedBall,
    dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).symm

/-- The set `(K°)ᵏ` is closed in `Kᵏ`. -/
theorem isClosed_setOf_forall_isPowerBounded :
    IsClosed {a : Fin k → K | ∀ i, IsPowerBounded (a i)} := by
  rw [setOf_forall_isPowerBounded_eq_closedBall]
  exact Metric.isClosed_closedBall

/-- When `K` is complete, `(K°)ᵏ` is a complete metric space for the sup norm. -/
instance instCompleteSpaceSubtypeForallIsPowerBounded [CompleteSpace K] :
    CompleteSpace {a : Fin k → K // ∀ i, IsPowerBounded (a i)} :=
  @IsClosed.completeSpace_coe _ _ _ {a : Fin k → K | ∀ i, IsPowerBounded (a i)}
    isClosed_setOf_forall_isPowerBounded

end PowerBoundedTuples

section NormedField

variable {k : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K]

/-- Over an ultrametric normed field, `evalAtHom` agrees with `restrictedEval₂` across
`restrictedMvPowerSeriesGaussEquiv`. -/
theorem evalAtHom_eq_restrictedEval₂ (a : Fin k → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    evalAtHom a ha f =
      MvPowerSeries.restrictedEval₂ (RingHom.id K) a (fun _ ↦ le_rfl)
        (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i))
        (restrictedMvPowerSeriesGaussEquiv f) := by
  have h : evalAtHom a ha =
      (MvPowerSeries.restrictedEval₂ (RingHom.id K) a (fun _ ↦ le_rfl)
        (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i))).comp
        restrictedMvPowerSeriesGaussEquiv.toRingHom :=
    weightedRestrictedSubring_ringHom_ext_of_continuous _
      (continuous_evalAtHom a ha)
      ((MvPowerSeries.continuous_restrictedEval₂ _ _ _ _).comp
        continuous_restrictedMvPowerSeriesGaussEquiv)
      (fun c ↦ by simp)
      (fun i ↦ by
        simp only [evalAtHom_weightedX, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, restrictedMvPowerSeriesGaussEquiv_weightedX]
        exact (MvPowerSeries.restrictedEval₂_X _ _ _ _ i).symm)
  exact RingHom.congr_fun h f

/-- Evaluation at a power-bounded tuple does not exceed the unit Gauss norm. -/
theorem norm_evalAtHom_le (a : Fin k → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [evalAtHom_eq_restrictedEval₂]
  exact MvPowerSeries.norm_restrictedEval₂_le _ _ _ _ _

/-- **Lipschitz bound for `evalAtHom` in the evaluation tuple.** -/
theorem norm_evalAtHom_sub_le {b a : Fin k → K} (hb : ∀ i, IsPowerBounded (b i))
    (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    ‖evalAtHom b hb f - evalAtHom a ha f‖ ≤
      ‖restrictedMvPowerSeriesGaussEquiv f‖ * ‖b - a‖ := by
  rw [evalAtHom_eq_restrictedEval₂, evalAtHom_eq_restrictedEval₂]
  exact TauCeti.MvPowerSeries.norm_restrictedEval₂_sub_le _ _ _ _ _

/-- For a fixed series `f ∈ K⟨T₁, …, Tₖ⟩`, `a ↦ evalAtHom a.1 a.2 f` is Lipschitz on `(K°)ᵏ` with
constant `‖restrictedMvPowerSeriesGaussEquiv f‖₊`. -/
theorem lipschitzWith_evalAtHom_point
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    LipschitzWith ‖restrictedMvPowerSeriesGaussEquiv f‖₊
      (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.1 a.2 f) :=
  LipschitzWith.of_dist_le_mul fun b a ↦ by
    simpa [Subtype.dist_eq, dist_eq_norm] using norm_evalAtHom_sub_le b.2 a.2 f

/-- For a fixed series `f ∈ K⟨T₁, …, Tₖ⟩`, the evaluation map `a ↦ f(a)` is continuous on
`(K°)ᵏ`. -/
@[continuity, fun_prop]
theorem continuous_evalAtHom_point
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.1 a.2 f) :=
  (lipschitzWith_evalAtHom_point f).continuous

/-- Over an ultrametric normed field, `classicalPoint x a ha` is independent of the auxiliary point
`x : Spa(K, K°)`. -/
theorem classicalPoint_congr_spa (x y : spa (powerBoundedSubring K)) (a : Fin k → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    classicalPoint x a ha = classicalPoint y a ha :=
  Subtype.ext <| ext' fun f g ↦ by
    rw [classicalPoint_vle, classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.2,
      vle_iff_norm_le_of_mem_spa y.2]

/-- A classical point lies in `basicOpen f s` if and only if `‖f(a)‖ ≤ ‖s(a)‖` and `s(a) ≠ 0`. -/
theorem classicalPoint_mem_basicOpen_iff (x : spa (powerBoundedSubring K)) (a : Fin k → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (f s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (classicalPoint x a ha).1 ∈ basicOpen f s ↔
      ‖evalAtHom a ha f‖ ≤ ‖evalAtHom a ha s‖ ∧ evalAtHom a ha s ≠ 0 := by
  rw [mem_basicOpen_iff, classicalPoint_vle, classicalPoint_vle, map_zero,
    vle_iff_norm_le_of_mem_spa x.2, vle_iff_norm_le_of_mem_spa x.2, norm_zero, norm_le_zero_iff]

/-- A classical point lies in `rationalSubset _ T s` if and only if `‖t(a)‖ ≤ ‖s(a)‖` for every
`t ∈ T` and `s(a) ≠ 0`. -/
theorem classicalPoint_mem_rationalSubset_iff (x : spa (powerBoundedSubring K)) (a : Fin k → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (classicalPoint x a ha).1 ∈ rationalSubset (powerBoundedSubring _) T s ↔
      (∀ t ∈ T, ‖evalAtHom a ha t‖ ≤ ‖evalAtHom a ha s‖) ∧ evalAtHom a ha s ≠ 0 := by
  have hv : (classicalPoint x a ha).1 ∈ spa (powerBoundedSubring _) :=
    closedPolydisc_def k K ▸ (classicalPoint x a ha).2
  simp only [mem_rationalSubset_iff, hv, true_and, classicalPoint_vle, map_zero,
    vle_iff_norm_le_of_mem_spa x.2, norm_zero, norm_le_zero_iff]

/-- The preimage of any `basicOpen f s` under the classical-point map is open in `(K°)ᵏ`. -/
theorem isOpen_preimage_classicalPoint_basicOpen (x : spa (powerBoundedSubring K))
    (f s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    IsOpen ((fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ (classicalPoint x a.1 a.2).1)
      ⁻¹' basicOpen f s) := by
  rw [Metric.isOpen_iff]
  intro a ha
  rw [Set.mem_preimage, classicalPoint_mem_basicOpen_iff] at ha
  have hsa : 0 < ‖evalAtHom a.1 a.2 s‖ := norm_pos_iff.mpr ha.2
  obtain ⟨δ₁, hδ₁, hfδ⟩ :=
    Metric.continuous_iff.mp (continuous_evalAtHom_point f) a ‖evalAtHom a.1 a.2 s‖ hsa
  obtain ⟨δ₂, hδ₂, hsδ⟩ :=
    Metric.continuous_iff.mp (continuous_evalAtHom_point s) a ‖evalAtHom a.1 a.2 s‖ hsa
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun b hb ↦ ?_⟩
  rw [Metric.mem_ball] at hb
  rw [Set.mem_preimage, classicalPoint_mem_basicOpen_iff]
  have hfb : ‖evalAtHom b.1 b.2 f - evalAtHom a.1 a.2 f‖ < ‖evalAtHom a.1 a.2 s‖ := by
    simpa [dist_eq_norm] using hfδ b (lt_min_iff.mp hb).1
  have hsb : ‖evalAtHom b.1 b.2 s - evalAtHom a.1 a.2 s‖ < ‖evalAtHom a.1 a.2 s‖ := by
    simpa [dist_eq_norm] using hsδ b (lt_min_iff.mp hb).2
  have hnorm_s : ‖evalAtHom b.1 b.2 s‖ = ‖evalAtHom a.1 a.2 s‖ := by
    have hadd : evalAtHom b.1 b.2 s =
        evalAtHom a.1 a.2 s + (evalAtHom b.1 b.2 s - evalAtHom a.1 a.2 s) :=
      (add_sub_cancel _ _).symm
    rw [hadd, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hsb)]
    exact max_eq_left hsb.le
  refine ⟨?_, norm_pos_iff.mp (hnorm_s ▸ hsa)⟩
  rw [hnorm_s]
  calc ‖evalAtHom b.1 b.2 f‖ =
        ‖evalAtHom b.1 b.2 f - evalAtHom a.1 a.2 f + evalAtHom a.1 a.2 f‖ := by
          rw [sub_add_cancel]
    _ ≤ max ‖evalAtHom b.1 b.2 f - evalAtHom a.1 a.2 f‖ ‖evalAtHom a.1 a.2 f‖ :=
        IsUltrametricDist.norm_add_le_max _ _
    _ ≤ ‖evalAtHom a.1 a.2 s‖ := max_le hfb.le ha.1

/-- **The classical-point map `(K°)ᵏ → closedPolydisc k K` is continuous**, for every complete
ultrametric normed field `K` (including trivially normed fields). -/
@[continuity, fun_prop]
theorem continuous_classicalPoint (x : spa (powerBoundedSubring K)) :
    Continuous (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  refine Continuous.subtype_mk ?_ fun (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) ↦
    (classicalPoint x a.1 a.2).2
  rw [instTopologicalSpace_eq_generateFrom, continuous_generateFrom_iff]
  rintro _ ⟨f, s, rfl⟩
  exact isOpen_preimage_classicalPoint_basicOpen x f s

/-- A classical point `x_b` lies in `closedSubpolydisc a c` if and only if `‖b - a‖ ≤ ‖c‖` and
`c ≠ 0`. -/
theorem classicalPoint_mem_closedSubpolydisc_iff (x : spa (powerBoundedSubring K))
    (b : Fin k → K) (hb : ∀ i, IsPowerBounded (b i)) (a : Fin k → K) (c : K) :
    classicalPoint x b hb ∈ closedSubpolydisc a c ↔ ‖b - a‖ ≤ ‖c‖ ∧ c ≠ 0 := by
  simp only [mem_closedSubpolydisc, classicalPoint_vle, map_sub, evalAtHom_weightedX,
    evalAtHom_weightedC, map_zero, vle_iff_norm_le_of_mem_spa x.2, norm_zero, norm_le_zero_iff,
    ← Pi.sub_apply]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg c)]

/-- For `c ≠ 0`, the preimage of `closedSubpolydisc a.1 c` under `classicalPoint` is the closed
metric ball of radius `‖c‖` around `a` in `(K°)ᵏ`. -/
theorem preimage_classicalPoint_closedSubpolydisc (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) {c : K} (hc : c ≠ 0) :
    (fun b : {b : Fin k → K // ∀ i, IsPowerBounded (b i)} ↦ classicalPoint x b.1 b.2) ⁻¹'
      closedSubpolydisc a.1 c = Metric.closedBall a ‖c‖ := by
  ext b
  rw [Set.mem_preimage, classicalPoint_mem_closedSubpolydisc_iff, Metric.mem_closedBall,
    Subtype.dist_eq, dist_eq_norm]
  simp [hc]

/-- The preimage of `closedSubpolydisc a c` under `classicalPoint` is clopen in `(K°)ᵏ` for every
`a : Fin k → K` and `c : K`. -/
theorem isClopen_preimage_classicalPoint_closedSubpolydisc (x : spa (powerBoundedSubring K))
    (a : Fin k → K) (c : K) :
    IsClopen ((fun b : {b : Fin k → K // ∀ i, IsPowerBounded (b i)} ↦ classicalPoint x b.1 b.2) ⁻¹'
      closedSubpolydisc a c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · convert isClopen_empty
    ext b
    rw [Set.mem_preimage, classicalPoint_mem_closedSubpolydisc_iff]
    simp
  · have hset : (fun b : {b : Fin k → K // ∀ i, IsPowerBounded (b i)} ↦
        classicalPoint x b.1 b.2) ⁻¹' closedSubpolydisc a c =
          ⋂ i : Fin k, (fun b : {b : Fin k → K // ∀ i, IsPowerBounded (b i)} ↦ b.1 i) ⁻¹'
            Metric.closedBall (a i) ‖c‖ := by
      ext b
      rw [Set.mem_preimage, classicalPoint_mem_closedSubpolydisc_iff,
        pi_norm_le_iff_of_nonneg (norm_nonneg c), Set.mem_iInter]
      simp [hc, dist_eq_norm]
    rw [hset]
    exact isClopen_iInter_of_finite fun i ↦
      (IsUltrametricDist.isClopen_closedBall (x := a i) (norm_pos_iff.mpr hc).ne').preimage
        ((continuous_apply i).comp continuous_subtype_val)

end NormedField

/-! ### Zero-dimensional closed polydisc -/

section ZeroDim

/-- Every restricted series in zero variables is the constant `constantCoeff f`. -/
private theorem eq_weightedC_zero {R : Type*} [SeminormedCommRing R] [NonarchimedeanRing R]
    (f : weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    f = weightedC (fun _ : Fin 0 ↦ ({1} : Set R)) isWeightFamily_one_weight
      (MvPowerSeries.constantCoeff (f : MvPowerSeries (Fin 0) R)) := by
  apply Subtype.ext
  ext ν
  have hν : ν = 0 := Finsupp.ext fun i ↦ i.elim0
  subst hν
  simp [coe_weightedC]

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K] [CompleteSpace K]

/-- **Every point of `closedPolydisc 0 K` is the classical point at the empty tuple.** -/
theorem eq_classicalPoint_zero (v : closedPolydisc 0 K) (x : spa (powerBoundedSubring K)) :
    v = classicalPoint x Fin.elim0 (fun i ↦ i.elim0) := by
  refine Subtype.ext <| ext' fun f g ↦ ?_
  rw [eq_weightedC_zero f, eq_weightedC_zero g, closedPolydisc_vle_weightedC_iff,
    classicalPoint_vle, evalAtHom_weightedC, evalAtHom_weightedC, vle_iff_norm_le_of_mem_spa x.2]

/-- `closedPolydisc 0 K` is a subsingleton over every complete ultrametric normed field. -/
instance instSubsingletonClosedPolydiscZero : Subsingleton (closedPolydisc 0 K) :=
  ⟨fun v w ↦ by
    let x : spa (powerBoundedSubring K) := ⟨_, comap_weightedC_mem_spa v⟩
    rw [eq_classicalPoint_zero v x, eq_classicalPoint_zero w x]⟩

/-- For `k = 0`, the classical points fill the entire `closedPolydisc 0 K` unconditionally
(regardless of whether the residue field of `K` is finite or infinite). -/
theorem range_classicalPoint_zero (x : spa (powerBoundedSubring K)) :
    Set.range (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) = Set.univ := by
  refine Set.eq_univ_of_forall fun v ↦ ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩, ?_⟩
  exact (eq_classicalPoint_zero v x).symm

end ZeroDim

/-! ### Topological embedding, homeomorphism onto `D(K)`, and Baire property -/

section NontriviallyNormedField

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K] [CompleteSpace K]

/-- **Over a nontrivially normed complete nonarchimedean field, `classicalPoint` induces the
sup-norm topology on `(K°)ᵏ`.** -/
theorem isInducing_classicalPoint (x : spa (powerBoundedSubring K)) :
    Topology.IsInducing (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  rw [Topology.isInducing_iff_nhds]
  intro a
  refine le_antisymm (continuous_classicalPoint x).continuousAt.tendsto.le_comap ?_
  rw [((nhds_basis_opens _).comap _).le_basis_iff (Metric.nhds_basis_ball (x := a))]
  intro ε hε
  -- Choose a small nonzero scalar `c` with `0 < ‖c‖ < ε` via `NormedField.exists_norm_lt`
  obtain ⟨c, hc0, hcε⟩ := NormedField.exists_norm_lt K hε
  refine ⟨closedSubpolydisc a.1 c, ⟨?_, isOpen_closedSubpolydisc a.1 c⟩, ?_⟩
  · rw [classicalPoint_mem_closedSubpolydisc_iff]
    exact ⟨by simp [norm_nonneg c], norm_pos_iff.mp hc0⟩
  · rw [preimage_classicalPoint_closedSubpolydisc x a (norm_pos_iff.mp hc0)]
    exact Metric.closedBall_subset_ball hcε

/-- **The classical-point map `(K°)ᵏ → closedPolydisc k K` is a topological embedding.** -/
theorem isEmbedding_classicalPoint (x : spa (powerBoundedSubring K)) :
    Topology.IsEmbedding (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) :=
  ⟨isInducing_classicalPoint x, classicalPoint_injective_of_isField (Field.toIsField K) x⟩

/-- **Homeomorphism between `(K°)ᵏ` (with the sup-norm metric topology) and the rational-point
locus `D(K)` inside `closedPolydisc k K`.** -/
noncomputable def classicalPointHomeomorph (x : spa (powerBoundedSubring K)) :
    {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ≃ₜ
      Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) :=
  (isEmbedding_classicalPoint x).toHomeomorph

/-- Applying `classicalPointHomeomorph x` gives `classicalPoint x a.1 a.2` in the range subtype. -/
@[simp]
theorem coe_classicalPointHomeomorph_apply (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointHomeomorph x a : closedPolydisc k K) = classicalPoint x a.1 a.2 :=
  (rfl)

/-- **The rational-point locus `D(K)` inside `closedPolydisc k K` is a Baire space** for the
subspace topology induced from `Spa(K⟨T₁, …, Tₖ⟩, K⟨T₁, …, Tₖ⟩°)`. -/
theorem baireSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    BaireSpace (Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2)) :=
  (classicalPointHomeomorph x).symm.isOpenEmbedding.baireSpace

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
