/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic

/-!
# Topological basis of `Spv A` by finite-numerator basic opens

For any commutative ring `A`, the sets `basicOpenFinset T s = {v ∈ Spv A | (∀ t ∈ T, v(t) ≤ v(s)) ∧
v(s) ≠ 0}` generate the topology of `Spv A` and are closed under finite intersections
(`basicOpenFinset_inter`), so they form a topological basis of `Spv A`
(`TauCeti.ValuationSpectrum.isTopologicalBasis_basicOpenFinset`).

## Main results

* `TauCeti.ValuationSpectrum.isTopologicalBasis_basicOpenFinset`: the family of all
  `basicOpenFinset T s` (`T : Finset A`, `s : A`) is a topological basis of `Spv A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 4.1 and Lemma 7.5.
-/

public section

namespace TauCeti.ValuationSpectrum

open scoped Pointwise

/-- For any commutative ring `A`, the finite-numerator basic opens `basicOpenFinset T s` form a
topological basis of `Spv A`. -/
theorem isTopologicalBasis_basicOpenFinset (A : Type*) [CommRing A] :
    TopologicalSpace.IsTopologicalBasis
      {U : Set (Spv A) | ∃ (T : Finset A) (s : A), U = basicOpenFinset T s} := by
  classical
  refine TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter ?_ ?_
  · refine le_antisymm (le_generateFrom ?_) ?_
    · rintro U ⟨T, s, rfl⟩
      exact isOpen_basicOpenFinset T s
    · rw [instTopologicalSpace_eq_generateFrom]
      refine TopologicalSpace.generateFrom_anti ?_
      rintro U ⟨f, s, rfl⟩
      exact ⟨{f}, s, by ext v; simp⟩
  · refine ⟨⟨∅, 1, ?_⟩, ?_⟩
    · ext v
      simp [v.toValuativeRel.not_vle_one_zero]
    · rintro U ⟨T₁, s₁, rfl⟩ V ⟨T₂, s₂, rfl⟩
      exact ⟨insert s₁ T₁ * insert s₂ T₂, s₁ * s₂, basicOpenFinset_inter T₁ T₂ s₁ s₂⟩

end TauCeti.ValuationSpectrum
