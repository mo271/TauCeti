/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Covering numbers, packing numbers, and separated sets

Metric facts about `ε`-separated sets and covering numbers in pseudo-emetric spaces.

## Main results

* `TauCeti.packingNumber_le_of_forall_finset_card_le`: a finite bound on the sizes of the finite
  `ε`-separated subsets of a set bounds its packing number.
* `TauCeti.coveringNumber_univ_subtype`: the covering number of `univ : Set S` in the subtype `S`
  equals `coveringNumber ε S`.
* `TauCeti.separableSpace_of_coveringNumber_ne_top`: finite dyadic covering numbers imply
  `SeparableSpace`.
* `TauCeti.nonneg_of_coveringNumber_le`: a polynomial small-scale covering-number bound
  `coveringNumber ε S ≤ C * ε ^ (-d)` on a nonempty set forces `0 ≤ d`.
* `Metric.IsSeparated.pairwiseDisjoint_closedBall`: the closed balls of radius `ε / 2` around
  the points of an `ε`-separated set are pairwise disjoint.
-/

public section

open Filter Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- If every finite `ε`-separated subset of `A` has at most `B ≠ ∞` elements, then the packing
number of `A` at scale `ε` is at most `B`. -/
theorem packingNumber_le_of_forall_finset_card_le {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0}
    {A : Set X} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (h : ∀ s : Finset X, (s : Set X) ⊆ A → IsSeparated ε (s : Set X) → (s.card : ℝ≥0∞) ≤ B) :
    (packingNumber ε A : ℝ≥0∞) ≤ B := by
  rw [packingNumber]
  simp only [ENat.toENNReal_iSup]
  refine iSup₂_le fun C hCA ↦ iSup_le fun hC ↦ ?_
  rcases C.finite_or_infinite with hCf | hCi
  · rw [hCf.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact h hCf.toFinset (by simpa using hCA) (by simpa using hC)
  · -- An infinite separated subset would contain finite separated subsets of every size.
    exfalso
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hB
    obtain ⟨s, hsC, rfl⟩ := hCi.exists_subset_card_eq n
    exact (h s (hsC.trans hCA) (hC.subset hsC)).not_gt hn

/-- The internal covering number of `univ` in the subtype of `S ⊆ X` equals the covering number of
`S` in `X`. -/
@[simp]
theorem coveringNumber_univ_subtype {X : Type*} [PseudoEMetricSpace X] (ε : ℝ≥0) (S : Set X) :
    coveringNumber ε (univ : Set S) = coveringNumber ε S := by
  have h := (isometry_subtype_coe (s := S)).coveringNumber_image'
    Subtype.val_injective.injOn (ε := ε) (A := univ)
  rw [Subtype.coe_image_univ] at h
  exact h.symm

/-- A pseudo-emetric space whose dyadic covering numbers `coveringNumber ((1 / 2) ^ n) univ` are all
finite is separable. -/
theorem separableSpace_of_coveringNumber_ne_top {X : Type*} [PseudoEMetricSpace X]
    (h : ∀ n : ℕ, coveringNumber ((1 / 2 : ℝ≥0) ^ n) (univ : Set X) ≠ ⊤) :
    SeparableSpace X := by
  have : SecondCountableTopology X := EMetric.secondCountable_of_almost_dense_set fun ε hε ↦ by
    obtain ⟨n, hn⟩ := ((tendsto_order.1
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((1 / 2 : ℝ≥0) : ℝ≥0∞))
        (by norm_num))).2 ε hε).exists
    refine ⟨minimalCover ((1 / 2 : ℝ≥0) ^ n) (univ : Set X), finite_minimalCover.countable,
      eq_univ_of_forall fun y ↦ ?_⟩
    obtain ⟨x, hx, hyx⟩ := isCover_minimalCover (h n) (mem_univ y)
    exact mem_biUnion hx (mem_closedEBall.2 (hyx.trans (ENNReal.coe_pow (1 / 2 : ℝ≥0) n ▸ hn.le)))
  infer_instance

/-- A nonempty set whose small-scale covering numbers satisfy `coveringNumber ε S ≤ C * ε ^ (-d)`
for `0 < ε ≤ 1` necessarily has `0 ≤ d`. -/
theorem nonneg_of_coveringNumber_le {X : Type*} [PseudoEMetricSpace X]
    {S : Set X} (hS : S.Nonempty) {C : ℝ≥0} {d : ℝ}
    (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε S : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d)) :
    0 ≤ d := by
  by_contra! hd
  have hq : ((1 / 2 : ℝ≥0) ^ (-d) : ℝ≥0) < 1 := NNReal.rpow_lt_one (by norm_num) (by linarith)
  have htend : Tendsto
      (fun n : ℕ ↦ (C : ℝ≥0∞) * (((1 / 2 : ℝ≥0) ^ (-d) : ℝ≥0) : ℝ≥0∞) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.coe_lt_one_iff.2 hq))
      (Or.inr ENNReal.coe_ne_top)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htend).2 1 zero_lt_one).exists
  have hpos : 0 < coveringNumber ((1 / 2 : ℝ≥0) ^ n) S := coveringNumber_pos_iff.2 hS
  have h1 : (1 : ℝ≥0∞) ≤ coveringNumber ((1 / 2 : ℝ≥0) ^ n) S := by
    exact_mod_cast Order.one_le_iff_pos.2 hpos
  have hle := h1.trans (hcov ((1 / 2) ^ n) (pow_pos (by norm_num) n)
    (pow_le_one₀ zero_le (by norm_num)))
  rw [ENNReal.coe_pow, ENNReal.pow_rpow_comm,
    ← ENNReal.coe_rpow_of_ne_zero (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)] at hle
  exact (hle.trans_lt hn).false

end TauCeti

namespace Metric

/-- The closed balls of radius `ε / 2` around the points of an `ε`-separated set are pairwise
disjoint. -/
theorem IsSeparated.pairwiseDisjoint_closedBall {X : Type*} [PseudoMetricSpace X] {ε : ℝ≥0}
    {C : Set X} (hC : IsSeparated ε C) : C.PairwiseDisjoint fun x ↦ closedBall x (ε / 2) := by
  intro x hx y hy hxy
  refine closedBall_disjoint_closedBall ?_
  have h : (ε : ℝ≥0∞) < edist x y := hC hx hy hxy
  rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at h
  linarith

end Metric
