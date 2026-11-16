/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Reduction.Basic
public import TauCeti.Topology.Algebra.Valued.Integer
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Canonical reduction of an ultrametric normed field

For an ultrametric normed field `K`, the power-bounded subring `K°` is the closed unit ball
`𝒪[K]`, and the ideal `K°°` of topologically nilpotent elements consists of the elements of norm
strictly less than `1`. Every element of `K° \ K°°` has norm `1`, so its inverse in `K` also has
norm `1` and already lies in `K°`. Hence `K°°` is a maximal ideal of `K°` and the canonical
reduction `K° ⧸ K°°` is a field, including when the norm on `K` is trivial (in which case `K° = K`
and `K°° = 0`).

When `K` is nontrivially normed, the open unit ball is also the maximal ideal of the valuation
ring `𝒪[K]`, so the equality of subrings `K° = 𝒪[K]` identifies `CanonicalReduction K` with the
residue field `𝓀[K] = IsLocalRing.ResidueField 𝒪[K]`.

## Main definitions

* `TauCeti.Huber.canonicalReductionEquivResidueField`: the ring isomorphism
  `CanonicalReduction K ≃+* IsLocalRing.ResidueField (Valued.integer K)` for a nontrivially normed
  ultrametric field `K`.

## Main results

* `TauCeti.Huber.mem_topologicallyNilpotentIdeal_iff_norm_lt_one`: an element of `K°` lies in
  `K°°` if and only if its norm is strictly less than `1`.
* `TauCeti.Huber.powerBoundedSubring_eq_integer`: `K° = 𝒪[K]` as subrings of `K`.
* `TauCeti.Huber.isMaximal_topologicallyNilpotentIdeal` and `Field (CanonicalReduction K)`:
  `K°°` is maximal in `K°`, making the canonical reduction a field.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.3.1.
-/

public section

open IsLocalRing
open scoped NormedField

namespace TauCeti.Huber

section NormedField

/-- In an ultrametric normed field, an element of `K°` lies in `K°°` if and only if its norm is
strictly less than `1`. -/
theorem mem_topologicallyNilpotentIdeal_iff_norm_lt_one {K : Type*} [NormedField K]
    [IsUltrametricDist K] {a : powerBoundedSubring K} :
    a ∈ topologicallyNilpotentIdeal K ↔ ‖(a : K)‖ < 1 :=
  mem_topologicallyNilpotentIdeal.trans tendsto_pow_atTop_nhds_zero_iff_norm_lt_one

/-- Two elements of `K°` have equal images in `CanonicalReduction K` if and only if their
difference has norm strictly less than `1`. -/
theorem canonicalReduction_mk_eq_iff {K : Type*} [NormedField K] [IsUltrametricDist K]
    {a b : powerBoundedSubring K} :
    Ideal.Quotient.mk (topologicallyNilpotentIdeal K) a =
        Ideal.Quotient.mk (topologicallyNilpotentIdeal K) b ↔
      ‖(a : K) - (b : K)‖ < 1 := by
  rw [Ideal.Quotient.eq, mem_topologicallyNilpotentIdeal_iff_norm_lt_one, AddSubgroupClass.coe_sub]

/-- **The power-bounded subring `K°` equals the valuation ring `𝒪[K]`.** -/
theorem powerBoundedSubring_eq_integer (K : Type*) [NormedField K] [IsUltrametricDist K] :
    powerBoundedSubring K = Valued.integer K := by
  ext x
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, Valuation.mem_integer_iff]
  exact (NNReal.coe_le_one (r := ‖x‖₊)).symm

/-- In an ultrametric normed field, every element of `K° \ K°°` has norm `1` and is therefore a
unit of `K°`; hence `K°°` is a maximal ideal of `K°`. This includes trivially normed fields, where
`K°° = ⊥` and `K° = ⊤`. -/
instance isMaximal_topologicallyNilpotentIdeal (K : Type*) [NormedField K] [IsUltrametricDist K] :
    (topologicallyNilpotentIdeal K).IsMaximal := by
  refine Ideal.Quotient.maximal_of_isField _ ⟨⟨0, 1, fun h ↦ ?_⟩, mul_comm, fun {x} hx ↦ ?_⟩
  · have h1 : (1 : powerBoundedSubring K) ∈ topologicallyNilpotentIdeal K :=
      Ideal.Quotient.eq_zero_iff_mem.mp h.symm
    exact lt_irrefl (1 : ℝ) (by simpa using mem_topologicallyNilpotentIdeal_iff_norm_lt_one.mp h1)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha_not : ¬ ‖(a : K)‖ < 1 := fun hlt ↦
      hx (Ideal.Quotient.eq_zero_iff_mem.mpr
        (mem_topologicallyNilpotentIdeal_iff_norm_lt_one.mpr hlt))
    have ha_le : ‖(a : K)‖ ≤ 1 := isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp a.2)
    have ha_norm : ‖(a : K)‖ = 1 := le_antisymm ha_le (not_lt.mp ha_not)
    have ha_ne : (a : K) ≠ 0 := norm_ne_zero_iff.mp (by rw [ha_norm]; exact one_ne_zero)
    refine ⟨Ideal.Quotient.mk _ ⟨(a : K)⁻¹, mem_powerBoundedSubring.mpr
      (isPowerBounded_iff_norm_le_one.mpr (by rw [norm_inv, ha_norm, inv_one]))⟩, ?_⟩
    rw [← map_mul]
    exact congrArg (Ideal.Quotient.mk _) (Subtype.ext (mul_inv_cancel₀ ha_ne))

/-- The canonical reduction `K° ⧸ K°°` of an ultrametric normed field is a field. -/
noncomputable instance instFieldCanonicalReduction (K : Type*) [NormedField K]
    [IsUltrametricDist K] : Field (CanonicalReduction K) :=
  Ideal.Quotient.field (topologicallyNilpotentIdeal K)

end NormedField

section NontriviallyNormedField

/-- **The canonical reduction `K° ⧸ K°°` is canonically isomorphic to the residue field `𝓀[K]`**
of the valuation ring `𝒪[K]`, for a nontrivially normed ultrametric field `K`. -/
noncomputable def canonicalReductionEquivResidueField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    CanonicalReduction K ≃+* IsLocalRing.ResidueField (Valued.integer K) :=
  let e := RingEquiv.subringCongr (powerBoundedSubring_eq_integer K)
  Ideal.quotientEquiv (topologicallyNilpotentIdeal K) (maximalIdeal (Valued.integer K)) e <|
    le_antisymm
      (fun x hx ↦ by
        rw [← e.apply_symm_apply x, ← RingEquiv.coe_toRingHom]
        exact Ideal.mem_map_of_mem _ (mem_topologicallyNilpotentIdeal_iff_norm_lt_one.mpr
          (by simpa [e, AddSubgroupClass.coe_norm] using
            Valued.integer.mem_maximalIdeal_iff.mp hx)))
      (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
        rw [Ideal.mem_comap, RingEquiv.coe_toRingHom, Valued.integer.mem_maximalIdeal_iff]
        simpa [e, AddSubgroupClass.coe_norm] using
          mem_topologicallyNilpotentIdeal_iff_norm_lt_one.mp ha)

/-- `canonicalReductionEquivResidueField` sends the class of `a ∈ K°` to the residue of
`a ∈ 𝒪[K]`. -/
@[simp]
theorem canonicalReductionEquivResidueField_mk {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] (a : powerBoundedSubring K) :
    canonicalReductionEquivResidueField K (Ideal.Quotient.mk (topologicallyNilpotentIdeal K) a) =
      residue (Valued.integer K)
        (RingEquiv.subringCongr (powerBoundedSubring_eq_integer K) a) :=
  (rfl)

/-- The inverse of `canonicalReductionEquivResidueField` sends the residue of `a ∈ 𝒪[K]` to the
class of `a ∈ K°`. -/
@[simp]
theorem canonicalReductionEquivResidueField_symm_residue {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] (a : Valued.integer K) :
    (canonicalReductionEquivResidueField K).symm (residue (Valued.integer K) a) =
      Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
        ((RingEquiv.subringCongr (powerBoundedSubring_eq_integer K)).symm a) := by
  apply (canonicalReductionEquivResidueField K).injective
  simp only [RingEquiv.apply_symm_apply, canonicalReductionEquivResidueField_mk,
    RingEquiv.apply_symm_apply]

end NontriviallyNormedField

end TauCeti.Huber
