/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.UnitBall
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Reduction
public import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Canonical reduction of an ultrametric normed field

For an ultrametric normed field `K`, the topological power-bounded subring `K°`
(`TauCeti.Huber.powerBoundedSubring K`) is the closed unit ball `Subring.unitClosedBall K` and the
valuation ring `𝒪[K]` (`Valued.integer K`), while the ideal of topologically nilpotent elements
`K°°` (`TauCeti.Huber.topologicallyNilpotentIdeal K`) is the open-ball ideal `unitBallIdeal K` and
the maximal ideal of `K°`. Consequently `K°` is a local ring with maximal ideal `K°°`, and the
Huber canonical reduction `CanonicalReduction K = K° ⧸ K°°` is canonically isomorphic to the valued
residue field `𝓀[K]`.

Rank-one norm control is essential for this identification: in a general valued field of rank
greater than one whose topology is induced by the valuation, every valuation subring properly
containing `𝒪[K]` is bounded, so `K°` can strictly contain `𝒪[K]`. Neither nontriviality of the
norm nor completeness of `K` is needed for the ring isomorphism `CanonicalReduction K ≃+* 𝓀[K]`.
When `K` is nontrivially normed and `K°` is compact (in particular when `K` is a proper space such
as `ℚ_[p]` or a finite extension thereof), `CanonicalReduction K` is finite.

## Main definitions

* `TauCeti.Huber.powerBoundedSubringEquivInteger`: the ring isomorphism `K° ≃+* 𝒪[K]` given by the
  identity on underlying elements of `K`.
* `TauCeti.Huber.canonicalReductionEquivResidueField`: the ring isomorphism
  `CanonicalReduction K ≃+* 𝓀[K]` identifying `K° ⧸ K°°` with the valued residue field of `K`.

## Main results

* `TauCeti.Huber.powerBoundedSubring_eq_unitClosedBall` and
  `TauCeti.Huber.powerBoundedSubring_eq_integer`: `K°` equals `Subring.unitClosedBall K` and
  `𝒪[K]` as subrings of `K`.
* `TauCeti.Huber.mem_topologicallyNilpotentIdeal_iff_norm_lt_one`: an element of `K°` lies in
  `K°°` if and only if its norm is strictly less than `1`.
* `TauCeti.Huber.isLocalRing_powerBoundedSubring`,
  `TauCeti.Huber.maximalIdeal_powerBoundedSubring`, and
  `TauCeti.Huber.isMaximal_topologicallyNilpotentIdeal`: `K°` is a local ring with maximal ideal
  `K°°`.
* `TauCeti.Huber.infinite_canonicalReduction_iff`, `TauCeti.Huber.finite_canonicalReduction_iff`,
  and `TauCeti.Huber.card_canonicalReduction`: transfer of finiteness and cardinality between
  `CanonicalReduction K` and `𝓀[K]`.
* `TauCeti.Huber.finite_canonicalReduction_of_compactSpace`: over a nontrivially normed ultrametric
  field with compact `K°`, the canonical reduction `K° ⧸ K°°` is finite.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer, 1984,
  §§1.2 and 6.3.1.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 5.27 and Example 6.39.
-/

public section

namespace TauCeti.Huber

open scoped NormedField Valued

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

variable (K) in
/-- **The power-bounded subring of an ultrametric normed field is its closed unit ball.** -/
theorem powerBoundedSubring_eq_unitClosedBall :
    powerBoundedSubring K = Subring.unitClosedBall K :=
  SetLike.coe_injective <|
    (coe_powerBoundedSubring_eq_closedBall K).trans (Subring.coe_unitClosedBall K).symm

/-- An element of `K°` is topologically nilpotent if and only if its norm is less than `1`. -/
theorem mem_topologicallyNilpotentIdeal_iff_norm_lt_one {x : powerBoundedSubring K} :
    x ∈ topologicallyNilpotentIdeal K ↔ ‖(x : K)‖ < 1 := by
  rw [mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]

/-- An element of `K°` is a unit of `K°` if and only if its norm is `1`. -/
theorem isUnit_powerBoundedSubring_iff_norm_eq_one {x : powerBoundedSubring K} :
    IsUnit x ↔ ‖(x : K)‖ = 1 := by
  let e := RingEquiv.subringCongr (powerBoundedSubring_eq_unitClosedBall K)
  rw [← isUnit_map_iff e, isUnit_unitClosedBall_iff_norm_eq_one]
  rfl

/-- **The power-bounded subring `K°` of an ultrametric normed field is a local ring.** -/
instance isLocalRing_powerBoundedSubring : IsLocalRing (powerBoundedSubring K) :=
  (RingEquiv.subringCongr (powerBoundedSubring_eq_unitClosedBall K)).symm.isLocalRing

variable (K) in
/-- **The maximal ideal of `K°` is the ideal `K°°` of topologically nilpotent elements.** -/
theorem maximalIdeal_powerBoundedSubring :
    IsLocalRing.maximalIdeal (powerBoundedSubring K) = topologicallyNilpotentIdeal K := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_powerBoundedSubring_iff_norm_eq_one,
    mem_topologicallyNilpotentIdeal_iff_norm_lt_one,
    (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.2)).lt_iff_ne]

/-- Over an ultrametric normed field, `K°°` is a maximal ideal of `K°`, so `CanonicalReduction K`
is a field via `Ideal.Quotient.field`. -/
instance isMaximal_topologicallyNilpotentIdeal : (topologicallyNilpotentIdeal K).IsMaximal :=
  maximalIdeal_powerBoundedSubring K ▸ IsLocalRing.maximalIdeal.isMaximal _

variable (K) in
/-- **The power-bounded subring `K°` coincides with the valued integer ring `𝒪[K]`.** -/
theorem powerBoundedSubring_eq_integer : powerBoundedSubring K = 𝒪[K] := by
  ext x
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, Valuation.mem_integer_iff]
  exact (NNReal.coe_le_coe (r₁ := ‖x‖₊) (r₂ := 1)).symm

variable (K) in
/-- The identity on `K` identifies the power-bounded subring `K°` with the valuation ring `𝒪[K]`. -/
noncomputable def powerBoundedSubringEquivInteger : powerBoundedSubring K ≃+* 𝒪[K] :=
  RingEquiv.subringCongr (powerBoundedSubring_eq_integer K)

@[simp]
theorem coe_powerBoundedSubringEquivInteger_apply (x : powerBoundedSubring K) :
    (powerBoundedSubringEquivInteger K x : K) = x :=
  (rfl)

@[simp]
theorem coe_powerBoundedSubringEquivInteger_symm_apply (x : 𝒪[K]) :
    ((powerBoundedSubringEquivInteger K).symm x : K) = x :=
  (rfl)

variable (K) in
/-- Under `powerBoundedSubringEquivInteger`, the maximal ideal `𝓂[K]` of `𝒪[K]` pulls back to
`topologicallyNilpotentIdeal K`. -/
theorem comap_powerBoundedSubringEquivInteger_maximalIdeal :
    (IsLocalRing.maximalIdeal 𝒪[K]).comap (powerBoundedSubringEquivInteger K : _ →+* _) =
      topologicallyNilpotentIdeal K := by
  rw [← maximalIdeal_powerBoundedSubring K]
  ext x
  simp only [Ideal.mem_comap, RingEquiv.coe_toRingHom,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_map_iff (powerBoundedSubringEquivInteger K)]

variable (K) in
/-- Under `powerBoundedSubringEquivInteger`, `topologicallyNilpotentIdeal K` maps to the maximal
ideal `𝓂[K]` of `𝒪[K]`. -/
theorem map_powerBoundedSubringEquivInteger_topologicallyNilpotentIdeal :
    (topologicallyNilpotentIdeal K).map (powerBoundedSubringEquivInteger K : _ →+* _) =
      IsLocalRing.maximalIdeal 𝒪[K] := by
  rw [← comap_powerBoundedSubringEquivInteger_maximalIdeal]
  exact Ideal.map_comap_of_surjective _ (powerBoundedSubringEquivInteger K).surjective _

variable (K) in
/-- **Canonical reduction equals the valued residue field**: for an ultrametric normed field `K`,
`CanonicalReduction K = K° ⧸ K°°` is canonically isomorphic to `𝓀[K] = 𝒪[K] ⧸ 𝓂[K]`. -/
noncomputable def canonicalReductionEquivResidueField : CanonicalReduction K ≃+* 𝓀[K] :=
  Ideal.quotientEquiv (topologicallyNilpotentIdeal K) (IsLocalRing.maximalIdeal 𝒪[K])
    (powerBoundedSubringEquivInteger K)
    (map_powerBoundedSubringEquivInteger_topologicallyNilpotentIdeal K).symm

@[simp]
theorem canonicalReductionEquivResidueField_mk (x : powerBoundedSubring K) :
    canonicalReductionEquivResidueField K (Ideal.Quotient.mk (topologicallyNilpotentIdeal K) x) =
      IsLocalRing.residue 𝒪[K] (powerBoundedSubringEquivInteger K x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

@[simp]
theorem canonicalReductionEquivResidueField_symm_residue (x : 𝒪[K]) :
    (canonicalReductionEquivResidueField K).symm (IsLocalRing.residue 𝒪[K] x) =
      Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
        ((powerBoundedSubringEquivInteger K).symm x) := by
  apply (canonicalReductionEquivResidueField K).injective
  rw [RingEquiv.apply_symm_apply, canonicalReductionEquivResidueField_mk,
    RingEquiv.apply_symm_apply]

variable (K) in
/-- The canonical reduction `K° ⧸ K°°` is infinite if and only if the residue field `𝓀[K]` is
infinite. -/
theorem infinite_canonicalReduction_iff : Infinite (CanonicalReduction K) ↔ Infinite 𝓀[K] :=
  (canonicalReductionEquivResidueField K).toEquiv.infinite_iff

variable (K) in
/-- The canonical reduction `K° ⧸ K°°` is finite if and only if the residue field `𝓀[K]` is
finite. -/
theorem finite_canonicalReduction_iff : Finite (CanonicalReduction K) ↔ Finite 𝓀[K] :=
  (canonicalReductionEquivResidueField K).toEquiv.finite_iff

variable (K) in
/-- The cardinality of `CanonicalReduction K` agrees with that of the residue field `𝓀[K]`. -/
theorem card_canonicalReduction : Nat.card (CanonicalReduction K) = Nat.card 𝓀[K] :=
  Nat.card_congr (canonicalReductionEquivResidueField K).toEquiv

variable (K) in
/-- `K°` is compact if and only if `𝒪[K]` is compact. -/
theorem compactSpace_powerBoundedSubring_iff_compactSpace_integer :
    CompactSpace (powerBoundedSubring K) ↔ CompactSpace 𝒪[K] := by
  let e := Homeomorph.setCongr (congrArg SetLike.coe (powerBoundedSubring_eq_integer K))
  exact ⟨fun _ ↦ e.compactSpace, fun _ ↦ e.symm.compactSpace⟩

/-- Over a proper ultrametric normed field (in particular over `ℚ_[p]` or any finite extension),
the power-bounded subring `K°` is compact because it coincides with `Metric.closedBall 0 1`. -/
instance compactSpace_powerBoundedSubring_of_properSpace [ProperSpace K] :
    CompactSpace (powerBoundedSubring K) :=
  isCompact_iff_compactSpace.mp
    (coe_powerBoundedSubring_eq_closedBall K ▸ isCompact_closedBall 0 1)

end NormedField

section LocallyCompact

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

open Valued.integer in
/-- Over a nontrivially normed ultrametric field whose power-bounded subring `K°` is compact, the
canonical reduction `K° ⧸ K°°` is finite. -/
instance finite_canonicalReduction_of_compactSpace [CompactSpace (powerBoundedSubring K)] :
    Finite (CanonicalReduction K) := by
  have : (Valued.v : Valuation K NNReal).RankOne :=
    inferInstanceAs (NormedField.valuation (K := K)).RankOne
  have hcomp : CompactSpace 𝒪[K] :=
    (compactSpace_powerBoundedSubring_iff_compactSpace_integer K).mp inferInstance
  exact (finite_canonicalReduction_iff K).mpr
    (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
      hcomp).2.2

end LocallyCompact

end TauCeti.Huber
