/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.Geometry.Manifold.DifferentialForm.Monodromy

/-!
# Closed `1`-forms on simply connected manifolds are exact

On a simply connected manifold every closed `1`-form is the differential of a function
(`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`), so the first de Rham cohomology vanishes
(`TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`).

By the Poincaré lemma (`TauCeti.exists_contMDiff_isPrimitiveOn`) a closed `C^r` `1`-form (`1 ≤ r`)
admits a `C^r` primitive near every point. Applying
`TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace` produces a global differentiable
primitive `f`, and since `f` agrees near each point with a translate of a `C^r` local primitive
(`TauCeti.IsPrimitiveOn.eventuallyEq_add_const`), `f` is itself `C^r`.

The Poincaré lemma is where finite dimensionality, the Hausdorff property and completeness of the
coefficient space are used. Manifolds with boundary or corners are included.

## Main declarations

* `TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`: a closed `C^r` `1`-form (`1 ≤ r`) with
  values in a complete space on a simply connected manifold has a `C^r` primitive.
* `TauCeti.exactForms_one_eq_closedForms_of_simplyConnectedSpace`: on a simply connected manifold
  every closed smooth real `1`-form is exact.
* `TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`: `H¹_dR(M) = 0` for simply
  connected `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields* (closed covector fields on simply connected manifolds are exact), and
  Chapter 17.
* Allen Hatcher, *Algebraic Topology*, Proposition 1.33 (the lifting criterion).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]

/-! ### Exactness on simply connected manifolds -/

/-- **Closed `1`-forms on simply connected manifolds are exact.** A closed `C^r` `1`-form
(`1 ≤ r`) with values in a complete space on a simply connected manifold is the exterior
derivative of a `C^r` function. -/
theorem exists_mextDeriv_eq_of_simplyConnectedSpace [SimplyConnectedSpace M] {r : ℕ∞}
    (hr : 1 ≤ r) {φ : RoughForm I M F 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) :
    ∃ ψ : RoughForm I M F 0, IsSmoothForm I r ψ ∧ mextDeriv ψ = φ := by
  obtain ⟨f, hf⟩ :=
    exists_isPrimitiveOn_univ_of_simplyConnectedSpace (hφ.exists_isPrimitiveOn hr hclosed)
  refine exists_mextDeriv_eq_of_forall_eventuallyEq_add_const (f := f) fun x ↦ ?_
  obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
  exact ⟨g, f x - g x, hg x, hf.eventuallyEq_add_const hgU (mem_univ x) hxU,
    hgU.mextDeriv_eq x hxU⟩

variable (I M) in
/-- On a simply connected manifold every closed smooth real `1`-form is exact. -/
theorem exactForms_one_eq_closedForms_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    exactForms I M 1 = closedForms I M 1 := by
  refine le_antisymm (exactForms_le_closedForms I 1) fun φ hφ ↦ ?_
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_simplyConnectedSpace (r := ⊤) le_top
    φ.isSmoothForm ((mem_closedForms I φ).mp hφ)
  rw [exactForms_succ]
  exact ⟨⟨ψ, hψ.mem_smoothBundleForms⟩, Subtype.ext ((mextDerivₗ_apply I 0 _).trans hdψ)⟩

variable (I M) in
/-- **The first de Rham cohomology of a simply connected manifold vanishes.** -/
theorem subsingleton_deRhamCohomology_one_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    Subsingleton (deRhamCohomology I M 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective _ _ c
  rw [deRhamCohomology.mk_eq_zero_iff, exactForms_one_eq_closedForms_of_simplyConnectedSpace]
  exact φ.2

end TauCeti
