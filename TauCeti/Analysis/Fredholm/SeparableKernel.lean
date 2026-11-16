/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Analysis.Fredholm.Compatibility
public import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.Star
import TauCeti.Analysis.Fredholm.CompactPerturbation

/-!
# Separable finite-rank operators and second-kind Fredholm integral equations

This file develops the finite matrix reduction, index-zero Fredholm alternative, and exact
solvability conditions for second-kind equations `(1 + K) u = h` where `K` is a finite-rank
separable operator, first for an abstract pairing `K u = ∑ j, β j u • a j` on a normed or Banach
space, then for Hilbert-space rank-one sums `K u = ∑ j, ⟪g j, u⟫_𝕜 • f j`, and finally for
continuous separable integral kernels on `C(X, 𝕜)` over a compact finite-measure space `(X, μ)` in
both the bilinear (`k(x, y) = ∑ j, a j x * b j y`) and conjugate-first sesquilinear
(`k(x, y) = ∑ j, a j x * conj (g j y)`) slot conventions.

## Main declarations

* `TauCeti.separableOperator`, `TauCeti.separableMatrix`: the operator
  `u ↦ ∑ j, β j u • a j` on a normed space `E` and its finite interaction matrix
  `M i j = β i (a j)`.
* `TauCeti.one_add_separableOperator_eq_iff`: `(1 + K) u = h` holds if and only if there exists
  `c : ι → 𝕜` solving `c i + ∑ j, β i (a j) * c j = β i h` with `u = h - ∑ j, c j • a j` (and in
  fact `c i = β i u`).
* `TauCeti.kerOneAddSeparableOperatorEquiv`,
  `TauCeti.bijective_one_add_separableOperator_iff_det_ne_zero`,
  `TauCeti.alternative_one_add_separableOperator`,
  `TauCeti.exists_one_add_separableOperator_eq_iff`: kernel isomorphism, determinant invertibility
  criterion, index-zero Fredholm alternative, and exact left-nullspace solvability condition.
* `TauCeti.hilbertSeparableOperator`, `TauCeti.hilbertSeparableMatrix`: the Hilbert-space
  separable operator `∑ j, InnerProductSpace.rankOne 𝕜 (f j) (g j)` with its adjoint formula
  `(hilbertSeparableOperator 𝕜 f g)† = hilbertSeparableOperator 𝕜 g f` and adjoint-kernel
  compatibility condition.
* `TauCeti.continuousSeparableOperator`, `TauCeti.continuousSesqSeparableOperator`: continuous
  finite-rank separable integral operators on `C(X, 𝕜)` under the bilinear and conjugate-first
  sesquilinear conventions, their agreement over `ℝ`, and the `[0, 1]` constant-`i` contrast
  (`TauCeti.unitInterval_const_I_sesq_vs_bilinear`).

## References

* R. Kress, *Linear Integral Equations*, 3rd ed., Chapter 3 and §4.2.
* F. Riesz and B. Sz.-Nagy, *Functional Analysis*, §§70–77.
-/

public section

open Module MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix

namespace Matrix

variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι]

/-- **Left-nullspace solvability criterion for finite matrices.** Over a field, a vector
`b : ι → 𝕜` lies in the column space `range (A.mulVecLin)` if and only if `∑ i, d i * b i = 0` for
every left nullvector `d` satisfying `∀ j, ∑ i, d i * A i j = 0`. -/
theorem mem_range_mulVecLin_iff (A : Matrix ι ι 𝕜) (b : ι → 𝕜) :
    b ∈ LinearMap.range A.mulVecLin ↔
      ∀ d : ι → 𝕜, (∀ j, ∑ i, d i * A i j = 0) → ∑ i, d i * b i = 0 := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ d hd
    calc ∑ i, d i * A.mulVecLin c i
        = ∑ i, d i * ∑ j, A i j * c j := rfl
      _ = ∑ j, (∑ i, d i * A i j) * c j := by
          simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun j _ ↦ by rw [hd j, zero_mul]
  · intro hb
    by_contra hnot
    obtain ⟨φ, hφb, hφ0⟩ :=
      (LinearMap.range A.mulVecLin).exists_dual_map_eq_bot_of_notMem hnot inferInstance
    let d : ι → 𝕜 := fun i ↦ φ (Pi.single i 1)
    have hφ_eq (x : ι → 𝕜) : φ x = ∑ i, d i * x i := by
      conv_lhs => rw [← (Pi.basisFun 𝕜 ι).sum_repr x, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Pi.basisFun_repr, Pi.basisFun_apply, map_smul, smul_eq_mul, mul_comm]
    have hd (j : ι) : ∑ i, d i * A i j = 0 := by
      have hmem : φ (A.mulVecLin (Pi.single j 1)) ∈ (LinearMap.range A.mulVecLin).map φ :=
        ⟨_, ⟨Pi.single j 1, rfl⟩, rfl⟩
      rw [hφ0, Submodule.mem_bot, hφ_eq] at hmem
      have hcol (i : ι) : A.mulVecLin (Pi.single j 1) i = A i j := by
        simp [mulVec, dotProduct, Pi.single_apply]
      simpa only [hcol] using hmem
    exact hφb ((hφ_eq b).trans (hb d hd))

end Matrix

namespace TauCeti

section AbstractSeparable

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The `ι × ι` interaction matrix `M i j = β i (a j)` associated to functionals
`β : ι → StrongDual 𝕜 E` and vectors `a : ι → E`. -/
def separableMatrix (β : ι → StrongDual 𝕜 E) (a : ι → E) : Matrix ι ι 𝕜 :=
  Matrix.of fun i j ↦ β i (a j)

/-- Entrywise formula for `TauCeti.separableMatrix`. -/
@[simp]
theorem separableMatrix_apply (β : ι → StrongDual 𝕜 E) (a : ι → E) (i j : ι) :
    separableMatrix β a i j = β i (a j) :=
  (rfl)

variable [Fintype ι]

/-- The finite-rank **separable operator** `u ↦ ∑ j, β j u • a j` associated to bounded linear
functionals `β : ι → StrongDual 𝕜 E` and vectors `a : ι → E`. -/
noncomputable def separableOperator (β : ι → StrongDual 𝕜 E) (a : ι → E) : E →L[𝕜] E :=
  ∑ j, (β j).smulRight (a j)

/-- Pointwise action of `TauCeti.separableOperator`. -/
@[simp]
theorem separableOperator_apply (β : ι → StrongDual 𝕜 E) (a : ι → E) (u : E) :
    separableOperator β a u = ∑ j, β j u • a j := by
  simp [separableOperator]

/-- Operator-norm bound `‖separableOperator β a‖ ≤ ∑ j, ‖a j‖ * ‖β j‖`. -/
theorem norm_separableOperator_le (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    ‖separableOperator β a‖ ≤ ∑ j, ‖a j‖ * ‖β j‖ :=
  (norm_sum_le _ _).trans <| Finset.sum_le_sum fun j _ ↦ by
    rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm]

/-- Every `TauCeti.separableOperator` has finite-dimensional range (spanned by `Set.range a`). -/
theorem hasFiniteRange_separableOperator (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    (separableOperator β a : E →ₗ[𝕜] E).HasFiniteRange := by
  have hle : LinearMap.range (separableOperator β a : E →ₗ[𝕜] E) ≤
      Submodule.span 𝕜 (Set.range a) := by
    rintro _ ⟨u, rfl⟩
    simpa only [ContinuousLinearMap.coe_coe, separableOperator_apply] using
      sum_mem fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range a)) :=
    Module.Finite.span_of_finite 𝕜 (Set.finite_range a)
  have : FiniteDimensional 𝕜 (LinearMap.range (separableOperator β a : E →ₗ[𝕜] E)) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact Submodule.FG.of_finite

/-- Over an `IsRCLikeNormedField`, every `TauCeti.separableOperator` is compact. -/
theorem isCompactOperator_separableOperator [IsRCLikeNormedField 𝕜]
    (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    IsCompactOperator (separableOperator β a) := by
  have : LocallyCompactSpace 𝕜 := by
    let _ := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  exact (hasFiniteRange_separableOperator β a).isCompactOperator

/-- On a Banach space over a complete `IsRCLikeNormedField`, `1 + separableOperator β a` is
Fredholm. -/
theorem isFredholm_one_add_separableOperator [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
    [CompleteSpace E] (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    ContinuousLinearMap.IsFredholm (1 + separableOperator β a) :=
  isFredholm_one_add (isCompactOperator_separableOperator β a)

/-- On a Banach space over a complete `IsRCLikeNormedField`, `1 + separableOperator β a` has
Fredholm index zero. -/
@[simp]
theorem index_one_add_separableOperator [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
    [CompleteSpace E] (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    ContinuousLinearMap.index (1 + separableOperator β a) = 0 :=
  ContinuousLinearMap.index_one_add_eq_zero (isCompactOperator_separableOperator β a)

/-- **Forward reduction.** Any solution `u` of `(1 + separableOperator β a) u = h` has moments
`c i = β i u` satisfying `c i + ∑ j, β i (a j) * c j = β i h` and is reconstructed by
`u = h - ∑ j, c j • a j`. -/
theorem apply_eq_of_one_add_separableOperator_eq {β : ι → StrongDual 𝕜 E} {a : ι → E} {u h : E}
    (hu : (1 + separableOperator β a) u = h) :
    (∀ i, β i u + ∑ j, β i (a j) * β j u = β i h) ∧ u = h - ∑ j, β j u • a j := by
  have hu' : u + ∑ j, β j u • a j = h := by
    simpa only [add_apply, one_apply_eq_self, separableOperator_apply] using hu
  refine ⟨fun i ↦ ?_, eq_sub_of_add_eq hu'⟩
  have hi := congrArg (β i) hu'
  rw [map_add, map_sum] at hi
  refine Eq.trans ?_ hi
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]

/-- **Backward reconstruction.** If `c : ι → 𝕜` solves `c i + ∑ j, β i (a j) * c j = β i h`, then
`u = h - ∑ j, c j • a j` has moments `β i u = c i` and solves `(1 + separableOperator β a) u = h`.
-/
theorem one_add_separableOperator_sub_eq {β : ι → StrongDual 𝕜 E} {a : ι → E} {h : E} {c : ι → 𝕜}
    (hc : ∀ i, c i + ∑ j, β i (a j) * c j = β i h) :
    (∀ i, β i (h - ∑ j, c j • a j) = c i) ∧
      (1 + separableOperator β a) (h - ∑ j, c j • a j) = h := by
  have hβ (i : ι) : β i (h - ∑ j, c j • a j) = c i := by
    rw [map_sub, map_sum, ← hc i]
    have hsum : ∑ j, (β i) (c j • a j) = ∑ j, β i (a j) * c j :=
      Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
    rw [hsum, add_sub_cancel_right]
  refine ⟨hβ, ?_⟩
  simp only [add_apply, one_apply_eq_self, separableOperator_apply, hβ, sub_add_cancel]

/-- **Finite matrix equivalence.** The equation `(1 + separableOperator β a) u = h` holds if and
only if there exists `c : ι → 𝕜` solving `c i + ∑ j, β i (a j) * c j = β i h` with
`u = h - ∑ j, c j • a j`. -/
theorem one_add_separableOperator_eq_iff (β : ι → StrongDual 𝕜 E) (a : ι → E) (u h : E) :
    (1 + separableOperator β a) u = h ↔
      ∃ c : ι → 𝕜, (∀ i, c i + ∑ j, β i (a j) * c j = β i h) ∧ u = h - ∑ j, c j • a j :=
  ⟨fun hu ↦ ⟨fun i ↦ β i u, apply_eq_of_one_add_separableOperator_eq hu⟩,
    fun ⟨_, hc, hu⟩ ↦ hu ▸ (one_add_separableOperator_sub_eq hc).2⟩

section DecidableEq

variable [DecidableEq ι]

/-- Coordinatewise expansion of `(1 + separableMatrix β a).mulVecLin c`. -/
theorem one_add_separableMatrix_mulVecLin_apply (β : ι → StrongDual 𝕜 E) (a : ι → E)
    (c : ι → 𝕜) (i : ι) :
    (1 + separableMatrix β a).mulVecLin c i = c i + ∑ j, β i (a j) * c j := by
  simp [Matrix.mulVec, dotProduct]

/-- Canonical linear isomorphism between `ker (1 + separableOperator β a)` and the finite matrix
kernel `ker (1 + separableMatrix β a).mulVecLin`, given by `u ↦ fun i ↦ β i u` and
`c ↦ -∑ j, c j • a j`. -/
noncomputable def kerOneAddSeparableOperatorEquiv (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    LinearMap.ker ((1 + separableOperator β a : E →L[𝕜] E) : E →ₗ[𝕜] E) ≃ₗ[𝕜]
      LinearMap.ker (1 + separableMatrix β a).mulVecLin where
  toFun u := ⟨fun i ↦ β i u.1, by
    ext i
    rw [one_add_separableMatrix_mulVecLin_apply, Pi.zero_apply]
    simpa only [map_zero] using (apply_eq_of_one_add_separableOperator_eq u.2).1 i⟩
  map_add' u v := by ext i; exact map_add (β i) u.1 v.1
  map_smul' r u := by ext i; exact map_smul (β i) r u.1
  invFun c := ⟨-∑ j, c.1 j • a j, by
    have hc (i : ι) : c.1 i + ∑ j, β i (a j) * c.1 j = β i 0 := by
      simpa only [one_add_separableMatrix_mulVecLin_apply, Pi.zero_apply, map_zero] using
        congrFun c.2 i
    simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, zero_sub] using
      (one_add_separableOperator_sub_eq (h := 0) hc).2⟩
  left_inv u := by
    ext1
    have hu := (apply_eq_of_one_add_separableOperator_eq u.2).2
    simpa only [zero_sub] using hu.symm
  right_inv c := by
    ext i
    have hc (k : ι) : c.1 k + ∑ j, β k (a j) * c.1 j = β k 0 := by
      simpa only [one_add_separableMatrix_mulVecLin_apply, Pi.zero_apply, map_zero] using
        congrFun c.2 k
    simpa only [zero_sub] using (one_add_separableOperator_sub_eq (h := 0) hc).1 i

/-- The kernel of `1 + separableOperator β a` has the same `finrank` as the finite matrix kernel
`ker (1 + separableMatrix β a).mulVecLin`. -/
theorem finrank_ker_one_add_separableOperator (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    finrank 𝕜 (LinearMap.ker ((1 + separableOperator β a : E →L[𝕜] E) : E →ₗ[𝕜] E)) =
      finrank 𝕜 (LinearMap.ker (1 + separableMatrix β a).mulVecLin) :=
  (kerOneAddSeparableOperatorEquiv β a).finrank_eq

/-- The kernel of `1 + separableOperator β a` is trivial if and only if
`det (1 + separableMatrix β a) ≠ 0`. -/
theorem ker_one_add_separableOperator_eq_bot_iff_det_ne_zero (β : ι → StrongDual 𝕜 E)
    (a : ι → E) :
    LinearMap.ker ((1 + separableOperator β a : E →L[𝕜] E) : E →ₗ[𝕜] E) = ⊥ ↔
      (1 + separableMatrix β a).det ≠ 0 := by
  let e := kerOneAddSeparableOperatorEquiv β a
  have hker : LinearMap.ker ((1 + separableOperator β a : E →L[𝕜] E) : E →ₗ[𝕜] E) = ⊥ ↔
      LinearMap.ker (1 + separableMatrix β a).mulVecLin = ⊥ := by
    simp only [Submodule.eq_bot_iff]
    refine ⟨fun h c hc ↦ ?_, fun h u hu ↦ ?_⟩
    · have h0 : (e.symm ⟨c, hc⟩ : E) = 0 := h _ (e.symm ⟨c, hc⟩).2
      have he0 : e.symm ⟨c, hc⟩ = 0 := Subtype.ext h0
      exact congrArg Subtype.val (e.symm.injective (he0.trans (map_zero _).symm))
    · have h0 : (e ⟨u, hu⟩ : ι → 𝕜) = 0 := h _ (e ⟨u, hu⟩).2
      have he0 : e ⟨u, hu⟩ = 0 := Subtype.ext h0
      exact congrArg Subtype.val (e.injective (he0.trans (map_zero _).symm))
  rw [hker, ← not_iff_not, not_ne_iff, ← Matrix.exists_mulVec_eq_zero_iff]
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply, not_forall,
    exists_prop]
  tauto

/-- **Determinant bijectivity criterion.** On a Banach space over a complete `IsRCLikeNormedField`,
`1 + separableOperator β a` is bijective if and only if `det (1 + separableMatrix β a) ≠ 0`. -/
theorem bijective_one_add_separableOperator_iff_det_ne_zero [IsRCLikeNormedField 𝕜]
    [CompleteSpace 𝕜] [CompleteSpace E] (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    Function.Bijective (1 + separableOperator β a : E →L[𝕜] E) ↔
      (1 + separableMatrix β a).det ≠ 0 := by
  have hFred := isFredholm_one_add_separableOperator β a
  have := hFred.finite_coker
  rw [(1 + separableOperator β a).bijective_iff_ker_eq_bot_of_index_eq_zero
    (index_one_add_separableOperator β a), ker_one_add_separableOperator_eq_bot_iff_det_ne_zero]

/-- **Fredholm alternative for `1 + separableOperator β a`.** Either
`det (1 + separableMatrix β a) ≠ 0` and `1 + separableOperator β a` is invertible and bijective, or
`det (1 + separableMatrix β a) = 0` and `1 + separableOperator β a` has nontrivial kernel and
proper range of equal `finrank` matching `finrank 𝕜 (ker (1 + separableMatrix β a).mulVecLin)`. -/
theorem alternative_one_add_separableOperator [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
    [CompleteSpace E] (β : ι → StrongDual 𝕜 E) (a : ι → E) :
    ((1 + separableMatrix β a).det ≠ 0 ∧
        (1 + separableOperator β a).IsInvertible ∧
        Function.Bijective (1 + separableOperator β a : E →L[𝕜] E)) ∨
      ((1 + separableMatrix β a).det = 0 ∧
        LinearMap.ker ((1 + separableOperator β a : E →L[𝕜] E) : E →ₗ[𝕜] E) ≠ ⊥ ∧
        LinearMap.range ((1 + separableOperator β a : E →L[𝕜] E) : E →ₗ[𝕜] E) ≠ ⊤ ∧
        finrank 𝕜 (E ⧸ LinearMap.range ((1 + separableOperator β a : E →L[𝕜] E) : E →ₗ[𝕜] E)) =
          finrank 𝕜 (LinearMap.ker (1 + separableMatrix β a).mulVecLin)) := by
  have hFred := isFredholm_one_add_separableOperator β a
  rcases hFred.alternative_of_index_eq_zero (index_one_add_separableOperator β a) with
    ⟨hinv, hbij⟩ | ⟨hker, hrange, hdim⟩
  · exact Or.inl ⟨(bijective_one_add_separableOperator_iff_det_ne_zero β a).mp hbij, hinv, hbij⟩
  · refine Or.inr ⟨?_, hker, hrange, hdim.trans (finrank_ker_one_add_separableOperator β a)⟩
    exact not_ne_iff.mp
      ((ker_one_add_separableOperator_eq_bot_iff_det_ne_zero β a).not.mp hker)

end DecidableEq

/-- **Exact solvability condition for `1 + separableOperator β a`.** The equation
`(1 + separableOperator β a) u = h` has a solution `u : E` if and only if every left nullvector
`d : ι → 𝕜` satisfying `∀ j, d j + ∑ i, d i * β i (a j) = 0` also satisfies
`∑ i, d i * β i h = 0`. -/
theorem exists_one_add_separableOperator_eq_iff (β : ι → StrongDual 𝕜 E) (a : ι → E) (h : E) :
    (∃ u, (1 + separableOperator β a) u = h) ↔
      ∀ d : ι → 𝕜, (∀ j, d j + ∑ i, d i * β i (a j) = 0) → ∑ i, d i * β i h = 0 := by
  classical
  have hex : (∃ u, (1 + separableOperator β a) u = h) ↔
      (fun i ↦ β i h) ∈ LinearMap.range (1 + separableMatrix β a).mulVecLin := by
    simp only [one_add_separableOperator_eq_iff, LinearMap.mem_range, funext_iff,
      one_add_separableMatrix_mulVecLin_apply]
    exact ⟨fun ⟨_, c, hc, _⟩ ↦ ⟨c, hc⟩, fun ⟨c, hc⟩ ↦ ⟨h - ∑ j, c j • a j, c, hc, rfl⟩⟩
  rw [hex, Matrix.mem_range_mulVecLin_iff]
  refine forall_congr' fun d ↦ imp_congr_left (forall_congr' fun j ↦ ?_)
  have hexp : (∑ i, d i * (1 + separableMatrix β a) i j) = d j + ∑ i, d i * β i (a j) := by
    simp [Matrix.add_apply, Matrix.one_apply, mul_add, Finset.sum_add_distrib]
  rw [hexp]

end AbstractSeparable

section HilbertSeparable

variable (𝕜 : Type*) {H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The Gram interaction matrix `M i j = ⟪g i, f j⟫_𝕜` of `TauCeti.hilbertSeparableOperator 𝕜 f g`.
-/
noncomputable def hilbertSeparableMatrix (f g : ι → H) : Matrix ι ι 𝕜 :=
  separableMatrix (fun j ↦ innerSL 𝕜 (g j)) f

/-- Entrywise formula for `TauCeti.hilbertSeparableMatrix`. -/
@[simp]
theorem hilbertSeparableMatrix_apply (f g : ι → H) (i j : ι) :
    hilbertSeparableMatrix 𝕜 f g i j = ⟪g i, f j⟫_𝕜 :=
  (rfl)

/-- Swapping `f` and `g` takes the conjugate transpose of `TauCeti.hilbertSeparableMatrix`. -/
@[simp]
theorem conjTranspose_hilbertSeparableMatrix (f g : ι → H) :
    (hilbertSeparableMatrix 𝕜 f g)ᴴ = hilbertSeparableMatrix 𝕜 g f := by
  ext i j
  simp [Matrix.conjTranspose_apply, inner_conj_symm]

variable [Fintype ι]

/-- The Hilbert-space **separable operator** `u ↦ ∑ j, ⟪g j, u⟫_𝕜 • f j` built from Mathlib's
`InnerProductSpace.rankOne`, with the conjugate-first inner product. -/
noncomputable def hilbertSeparableOperator (f g : ι → H) : H →L[𝕜] H :=
  ∑ j, InnerProductSpace.rankOne 𝕜 (f j) (g j)

/-- `TauCeti.hilbertSeparableOperator` is definitionally `TauCeti.separableOperator` with the Riesz
functionals `j ↦ innerSL 𝕜 (g j)`. -/
theorem hilbertSeparableOperator_eq_separableOperator (f g : ι → H) :
    hilbertSeparableOperator 𝕜 f g = separableOperator (fun j ↦ innerSL 𝕜 (g j)) f :=
  (rfl)

/-- Pointwise action `hilbertSeparableOperator 𝕜 f g u = ∑ j, ⟪g j, u⟫_𝕜 • f j`. -/
@[simp]
theorem hilbertSeparableOperator_apply (f g : ι → H) (u : H) :
    hilbertSeparableOperator 𝕜 f g u = ∑ j, ⟪g j, u⟫_𝕜 • f j := by
  simp [hilbertSeparableOperator]

/-- Operator-norm bound `‖hilbertSeparableOperator 𝕜 f g‖ ≤ ∑ j, ‖f j‖ * ‖g j‖`. -/
theorem norm_hilbertSeparableOperator_le (f g : ι → H) :
    ‖hilbertSeparableOperator 𝕜 f g‖ ≤ ∑ j, ‖f j‖ * ‖g j‖ :=
  (norm_sum_le _ _).trans <| Finset.sum_le_sum fun j _ ↦
    (InnerProductSpace.norm_rankOne (𝕜 := 𝕜) (f j) (g j)).le

/-- Every `TauCeti.hilbertSeparableOperator` has finite rank. -/
theorem hasFiniteRange_hilbertSeparableOperator (f g : ι → H) :
    (hilbertSeparableOperator 𝕜 f g : H →ₗ[𝕜] H).HasFiniteRange :=
  hasFiniteRange_separableOperator (fun j ↦ innerSL 𝕜 (g j)) f

/-- Every `TauCeti.hilbertSeparableOperator` is compact. -/
theorem isCompactOperator_hilbertSeparableOperator (f g : ι → H) :
    IsCompactOperator (hilbertSeparableOperator 𝕜 f g) :=
  isCompactOperator_separableOperator (fun j ↦ innerSL 𝕜 (g j)) f

/-- **Hilbert finite matrix equivalence.** For `u, h : H`, `u + hilbertSeparableOperator 𝕜 f g u =
h` holds if and only if there exists `c : ι → 𝕜` (namely `c i = ⟪g i, u⟫_𝕜`) solving
`c i + ∑ j, ⟪g i, f j⟫_𝕜 * c j = ⟪g i, h⟫_𝕜` with `u = h - ∑ j, c j • f j`. -/
theorem one_add_hilbertSeparableOperator_eq_iff (f g : ι → H) (u h : H) :
    (1 + hilbertSeparableOperator 𝕜 f g) u = h ↔
      ∃ c : ι → 𝕜, (∀ i, c i + ∑ j, ⟪g i, f j⟫_𝕜 * c j = ⟪g i, h⟫_𝕜) ∧ u = h - ∑ j, c j • f j :=
  one_add_separableOperator_eq_iff (fun j ↦ innerSL 𝕜 (g j)) f u h

/-- Forward moment formula `c i = ⟪g i, u⟫_𝕜` for `(1 + hilbertSeparableOperator 𝕜 f g) u = h`. -/
theorem inner_eq_of_one_add_hilbertSeparableOperator_eq {𝕜 : Type*} [RCLike 𝕜]
    [InnerProductSpace 𝕜 H] {f g : ι → H} {u h : H}
    (hu : (1 + hilbertSeparableOperator 𝕜 f g) u = h) :
    (∀ i, ⟪g i, u⟫_𝕜 + ∑ j, ⟪g i, f j⟫_𝕜 * ⟪g j, u⟫_𝕜 = ⟪g i, h⟫_𝕜) ∧
      u = h - ∑ j, ⟪g j, u⟫_𝕜 • f j :=
  apply_eq_of_one_add_separableOperator_eq hu

/-- **Matrix compatibility condition on a pre-Hilbert space.** `(1 + hilbertSeparableOperator 𝕜 f g)
u = h` is solvable if and only if `∑ i, d i * ⟪g i, h⟫_𝕜 = 0` whenever
`∀ j, d j + ∑ i, d i * ⟪g i, f j⟫_𝕜 = 0`. -/
theorem exists_one_add_hilbertSeparableOperator_eq_iff_matrix (f g : ι → H) (h : H) :
    (∃ u, (1 + hilbertSeparableOperator 𝕜 f g) u = h) ↔
      ∀ d : ι → 𝕜, (∀ j, d j + ∑ i, d i * ⟪g i, f j⟫_𝕜 = 0) → ∑ i, d i * ⟪g i, h⟫_𝕜 = 0 :=
  exists_one_add_separableOperator_eq_iff (fun j ↦ innerSL 𝕜 (g j)) f h

section CompleteHilbert

variable [CompleteSpace H]

/-- Taking the Hilbert adjoint of `TauCeti.hilbertSeparableOperator 𝕜 f g` swaps `f` and `g`. -/
@[simp]
theorem adjoint_hilbertSeparableOperator (f g : ι → H) :
    (hilbertSeparableOperator 𝕜 f g)† = hilbertSeparableOperator 𝕜 g f := by
  simp [hilbertSeparableOperator, map_sum]

/-- On a Hilbert space, `1 + hilbertSeparableOperator 𝕜 f g` is Fredholm. -/
theorem isFredholm_one_add_hilbertSeparableOperator (f g : ι → H) :
    ContinuousLinearMap.IsFredholm (1 + hilbertSeparableOperator 𝕜 f g) :=
  isFredholm_one_add_separableOperator (fun j ↦ innerSL 𝕜 (g j)) f

/-- On a Hilbert space, `1 + hilbertSeparableOperator 𝕜 f g` has index zero. -/
@[simp]
theorem index_one_add_hilbertSeparableOperator (f g : ι → H) :
    ContinuousLinearMap.index (1 + hilbertSeparableOperator 𝕜 f g) = 0 :=
  index_one_add_separableOperator (fun j ↦ innerSL 𝕜 (g j)) f

/-- **Adjoint-kernel compatibility condition for `1 + hilbertSeparableOperator 𝕜 f g`.** On a
Hilbert space, `(1 + hilbertSeparableOperator 𝕜 f g) u = h` is solvable if and only if
`⟪z, h⟫_𝕜 = 0` for every `z ∈ ker (1 + hilbertSeparableOperator 𝕜 g f)`. -/
theorem exists_one_add_hilbertSeparableOperator_eq_iff_ker_adjoint (f g : ι → H) (h : H) :
    (∃ u, (1 + hilbertSeparableOperator 𝕜 f g) u = h) ↔
      ∀ z ∈ LinearMap.ker ((1 + hilbertSeparableOperator 𝕜 g f : H →L[𝕜] H) : H →ₗ[𝕜] H),
        ⟪z, h⟫_𝕜 = 0 := by
  have hadj : ((1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H)†) =
      1 + hilbertSeparableOperator 𝕜 g f := by
    rw [map_add, adjoint_hilbertSeparableOperator, ContinuousLinearMap.one_def,
      ContinuousLinearMap.adjoint_id]
  have hFred := isFredholm_one_add_hilbertSeparableOperator 𝕜 f g
  simpa only [hadj] using
    hFred.exists_apply_eq_iff_forall_inner_ker_adjoint_eq_zero (y := h)

/-- **Determinant bijectivity criterion for `1 + hilbertSeparableOperator 𝕜 f g`.** -/
theorem bijective_one_add_hilbertSeparableOperator_iff_det_ne_zero [DecidableEq ι]
    (f g : ι → H) :
    Function.Bijective (1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H) ↔
      (1 + hilbertSeparableMatrix 𝕜 f g).det ≠ 0 :=
  bijective_one_add_separableOperator_iff_det_ne_zero (fun j ↦ innerSL 𝕜 (g j)) f

/-- **Hilbert Fredholm alternative for `1 + hilbertSeparableOperator 𝕜 f g`.** Either
`det (1 + hilbertSeparableMatrix 𝕜 f g) ≠ 0` and `1 + hilbertSeparableOperator 𝕜 f g` is invertible
and bijective, or `det (1 + hilbertSeparableMatrix 𝕜 f g) = 0` and `1 + K` has nontrivial kernel,
proper range, and equal `finrank` of `ker (1 + K)`, `ker (1 + hilbertSeparableOperator 𝕜 g f)`,
`H ⧸ range (1 + K)`, and `ker (1 + hilbertSeparableMatrix 𝕜 f g).mulVecLin`. -/
theorem alternative_one_add_hilbertSeparableOperator [DecidableEq ι] (f g : ι → H) :
    ((1 + hilbertSeparableMatrix 𝕜 f g).det ≠ 0 ∧
        (1 + hilbertSeparableOperator 𝕜 f g).IsInvertible ∧
        Function.Bijective (1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H)) ∨
      ((1 + hilbertSeparableMatrix 𝕜 f g).det = 0 ∧
        LinearMap.ker ((1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H) : H →ₗ[𝕜] H) ≠ ⊥ ∧
        LinearMap.range ((1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H) : H →ₗ[𝕜] H) ≠ ⊤ ∧
        finrank 𝕜
            (LinearMap.ker ((1 + hilbertSeparableOperator 𝕜 g f : H →L[𝕜] H) : H →ₗ[𝕜] H)) =
          finrank 𝕜
            (LinearMap.ker ((1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H) : H →ₗ[𝕜] H)) ∧
        finrank 𝕜
            (H ⧸ LinearMap.range ((1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H) : H →ₗ[𝕜] H)) =
          finrank 𝕜 (LinearMap.ker (1 + hilbertSeparableMatrix 𝕜 f g).mulVecLin)) := by
  have hadj : ((1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H)†) =
      1 + hilbertSeparableOperator 𝕜 g f := by
    rw [map_add, adjoint_hilbertSeparableOperator, ContinuousLinearMap.one_def,
      ContinuousLinearMap.adjoint_id]
  have hFred := isFredholm_one_add_hilbertSeparableOperator 𝕜 f g
  have hadj_dim : finrank 𝕜
      (LinearMap.ker ((1 + hilbertSeparableOperator 𝕜 g f : H →L[𝕜] H) : H →ₗ[𝕜] H)) =
      finrank 𝕜
        (LinearMap.ker ((1 + hilbertSeparableOperator 𝕜 f g : H →L[𝕜] H) : H →ₗ[𝕜] H)) := by
    rw [← hadj, hFred.finrank_ker_adjoint_eq_finrank_ker_iff_index_eq_zero,
      ← ContinuousLinearMap.index_def]
    exact index_one_add_hilbertSeparableOperator 𝕜 f g
  rcases alternative_one_add_separableOperator (fun j ↦ innerSL 𝕜 (g j)) f with
    hreg | ⟨hdet, hker, hrange, hcoker⟩
  · exact Or.inl hreg
  · exact Or.inr ⟨hdet, hker, hrange, hadj_dim, hcoker⟩

end CompleteHilbert

end HilbertSeparable

section ContinuousSeparable

variable {𝕜 X ι : Type*} [RCLike 𝕜]
  [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]

/-- Continuous linear functional `u ↦ ∫ y, b y * u y ∂μ` on `C(X, 𝕜)` defined by an integrable
weight `b : X → 𝕜` on a compact space `X` with `[OpensMeasurableSpace X]`. -/
noncomputable def continuousIntegralDual [OpensMeasurableSpace X] (μ : Measure X) (b : X → 𝕜)
    (hb : Integrable b μ) : StrongDual 𝕜 C(X, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ ∫ y, b y * u y ∂μ
      map_add' := fun u v ↦ by
        simp_rw [ContinuousMap.add_apply, mul_add]
        exact integral_add
          (hb.mul_bdd u.continuous.aestronglyMeasurable
            (Filter.Eventually.of_forall u.norm_coe_le_norm))
          (hb.mul_bdd v.continuous.aestronglyMeasurable
            (Filter.Eventually.of_forall v.norm_coe_le_norm))
      map_smul' := fun c u ↦ by
        calc ∫ y, b y * (c • u) y ∂μ
            = ∫ y, c * (b y * u y) ∂μ :=
              integral_congr_ae (Filter.Eventually.of_forall fun y ↦ by
                simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring)
          _ = c • ∫ y, b y * u y ∂μ := by rw [integral_const_mul, smul_eq_mul] }
    (∫ y, ‖b y‖ ∂μ) fun u ↦ by
      refine (norm_integral_le_of_norm_le (hb.norm.mul_const ‖u‖) ?_).trans_eq
        (integral_mul_const _ _)
      exact Filter.Eventually.of_forall fun y ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm y) (norm_nonneg _)

/-- Evaluation formula for `TauCeti.continuousIntegralDual`. -/
@[simp]
theorem continuousIntegralDual_apply [OpensMeasurableSpace X] (μ : Measure X) (b : X → 𝕜)
    (hb : Integrable b μ) (u : C(X, 𝕜)) :
    continuousIntegralDual μ b hb u = ∫ y, b y * u y ∂μ :=
  (rfl)

/-- Norm bound `‖continuousIntegralDual μ b hb‖ ≤ ∫ y, ‖b y‖ ∂μ`. -/
theorem norm_continuousIntegralDual_le [OpensMeasurableSpace X] (μ : Measure X) (b : X → 𝕜)
    (hb : Integrable b μ) :
    ‖continuousIntegralDual μ b hb‖ ≤ ∫ y, ‖b y‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _

variable [OpensMeasurableSpace X]

/-- Every continuous scalar-valued function on a compact space is integrable with respect to any
finite measure (assuming open sets are measurable). -/
theorem ContinuousMap.integrable (μ : Measure X) [IsFiniteMeasure μ] (u : C(X, 𝕜)) :
    Integrable u μ := by
  simpa only [mul_one] using
    (integrable_const (1 : 𝕜)).bdd_mul u.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall u.norm_coe_le_norm)

/-- Multiplying an integrable weight `b : X → 𝕜` by `u : C(X, 𝕜)` on a compact space produces an
integrable function. -/
theorem ContinuousMap.integrable_mul_of_integrable {μ : Measure X} {b : X → 𝕜}
    (hb : Integrable b μ) (u : C(X, 𝕜)) :
    Integrable (fun y ↦ b y * u y) μ :=
  hb.mul_bdd u.continuous.aestronglyMeasurable (Filter.Eventually.of_forall u.norm_coe_le_norm)

section FiniteMeasure

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- Continuous linear functional `u ↦ ∫ y, b y * u y ∂μ` on `C(X, 𝕜)` associated to a continuous
weight `b : C(X, 𝕜)` on a compact finite-measure space. -/
noncomputable def continuousMapIntegralDual (b : C(X, 𝕜)) : StrongDual 𝕜 C(X, 𝕜) :=
  continuousIntegralDual μ b (ContinuousMap.integrable μ b)

/-- Evaluation formula for `TauCeti.continuousMapIntegralDual`. -/
@[simp]
theorem continuousMapIntegralDual_apply (b u : C(X, 𝕜)) :
    continuousMapIntegralDual μ b u = ∫ y, b y * u y ∂μ :=
  (rfl)

/-- Norm bound `‖continuousMapIntegralDual μ b‖ ≤ μ.real Set.univ * ‖b‖`. -/
theorem norm_continuousMapIntegralDual_le (b : C(X, 𝕜)) :
    ‖continuousMapIntegralDual μ b‖ ≤ μ.real Set.univ * ‖b‖ := by
  refine (norm_continuousIntegralDual_le μ b _).trans ?_
  simpa only [integral_const, smul_eq_mul] using
    integral_mono (ContinuousMap.integrable μ b).norm (integrable_const ‖b‖) b.norm_coe_le_norm

/-- Interaction matrix `M i j = ∫ y, b i y * a j y ∂μ` of `TauCeti.continuousSeparableOperator`. -/
noncomputable def continuousSeparableMatrix (a b : ι → C(X, 𝕜)) : Matrix ι ι 𝕜 :=
  separableMatrix (fun j ↦ continuousMapIntegralDual μ (b j)) a

/-- Entrywise formula for `TauCeti.continuousSeparableMatrix`. -/
@[simp]
theorem continuousSeparableMatrix_apply (a b : ι → C(X, 𝕜)) (i j : ι) :
    continuousSeparableMatrix μ a b i j = ∫ y, b i y * a j y ∂μ :=
  (rfl)

/-- Interaction matrix `M i j = ∫ y, conj (g i y) * a j y ∂μ` of
`TauCeti.continuousSesqSeparableOperator`. -/
noncomputable def continuousSesqSeparableMatrix (a g : ι → C(X, 𝕜)) : Matrix ι ι 𝕜 :=
  continuousSeparableMatrix μ a (fun j ↦ star (g j))

variable [Fintype ι]

/-- **Bilinear continuous separable integral operator** on `C(X, 𝕜)` with kernel
`k(x, y) = ∑ j, a j x * b j y`, sending `u` to `x ↦ ∫ y, (∑ j, a j x * b j y) * u y ∂μ`. -/
noncomputable def continuousSeparableOperator (a b : ι → C(X, 𝕜)) : C(X, 𝕜) →L[𝕜] C(X, 𝕜) :=
  separableOperator (fun j ↦ continuousMapIntegralDual μ (b j)) a

/-- Expansion of `continuousSeparableOperator μ a b u` as a finite linear combination of `a j`. -/
@[simp]
theorem continuousSeparableOperator_apply (a b : ι → C(X, 𝕜)) (u : C(X, 𝕜)) :
    continuousSeparableOperator μ a b u = ∑ j, (∫ y, b j y * u y ∂μ) • a j := by
  simp [continuousSeparableOperator]

/-- Pointwise integral formula `(continuousSeparableOperator μ a b u) x =
∫ y, (∑ j, a j x * b j y) * u y ∂μ`. -/
theorem continuousSeparableOperator_apply_apply (a b : ι → C(X, 𝕜)) (u : C(X, 𝕜)) (x : X) :
    continuousSeparableOperator μ a b u x = ∫ y, (∑ j, a j x * b j y) * u y ∂μ := by
  have hint (j : ι) : Integrable (fun y ↦ a j x * (b j y * u y)) μ :=
    (ContinuousMap.integrable_mul_of_integrable (ContinuousMap.integrable μ (b j)) u).const_mul
      (a j x)
  calc continuousSeparableOperator μ a b u x
      = ∑ j, (∫ y, b j y * u y ∂μ) * a j x := by
        simp [ContinuousMap.coe_sum, mul_comm]
    _ = ∑ j, ∫ y, a j x * (b j y * u y) ∂μ :=
        Finset.sum_congr rfl fun j _ ↦ by rw [integral_const_mul, mul_comm]
    _ = ∫ y, ∑ j, a j x * (b j y * u y) ∂μ := (integral_finsetSum _ fun j _ ↦ hint j).symm
    _ = ∫ y, (∑ j, a j x * b j y) * u y ∂μ := by
        congr 1 with y
        simp_rw [Finset.sum_mul, mul_assoc]

/-- Norm bound `‖continuousSeparableOperator μ a b‖ ≤ μ.real Set.univ * ∑ j, ‖a j‖ * ‖b j‖`. -/
theorem norm_continuousSeparableOperator_le (a b : ι → C(X, 𝕜)) :
    ‖continuousSeparableOperator μ a b‖ ≤ μ.real Set.univ * ∑ j, ‖a j‖ * ‖b j‖ := by
  refine (norm_separableOperator_le _ a).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  calc ‖a j‖ * ‖continuousMapIntegralDual μ (b j)‖
      ≤ ‖a j‖ * (μ.real Set.univ * ‖b j‖) :=
        mul_le_mul_of_nonneg_left (norm_continuousMapIntegralDual_le μ (b j)) (norm_nonneg _)
    _ = μ.real Set.univ * (‖a j‖ * ‖b j‖) := by ring

/-- `TauCeti.continuousSeparableOperator` has finite rank. -/
theorem hasFiniteRange_continuousSeparableOperator (a b : ι → C(X, 𝕜)) :
    (continuousSeparableOperator μ a b : C(X, 𝕜) →ₗ[𝕜] C(X, 𝕜)).HasFiniteRange :=
  hasFiniteRange_separableOperator _ a

/-- `1 + continuousSeparableOperator μ a b` is Fredholm on `C(X, 𝕜)`. -/
theorem isFredholm_one_add_continuousSeparableOperator (a b : ι → C(X, 𝕜)) :
    ContinuousLinearMap.IsFredholm (1 + continuousSeparableOperator μ a b) :=
  isFredholm_one_add_separableOperator _ a

/-- `1 + continuousSeparableOperator μ a b` has Fredholm index zero on `C(X, 𝕜)`. -/
@[simp]
theorem index_one_add_continuousSeparableOperator (a b : ι → C(X, 𝕜)) :
    ContinuousLinearMap.index (1 + continuousSeparableOperator μ a b) = 0 :=
  index_one_add_separableOperator _ a

/-- **Finite matrix reduction for `(1 + continuousSeparableOperator μ a b) u = f`.** -/
theorem one_add_continuousSeparableOperator_eq_iff (a b : ι → C(X, 𝕜)) (u f : C(X, 𝕜)) :
    (1 + continuousSeparableOperator μ a b) u = f ↔
      ∃ c : ι → 𝕜, (∀ i, c i + ∑ j, (∫ y, b i y * a j y ∂μ) * c j = ∫ y, b i y * f y ∂μ) ∧
        u = f - ∑ j, c j • a j :=
  one_add_separableOperator_eq_iff _ a u f

/-- **Exact solvability condition for `(1 + continuousSeparableOperator μ a b) u = f`.** -/
theorem exists_one_add_continuousSeparableOperator_eq_iff (a b : ι → C(X, 𝕜)) (f : C(X, 𝕜)) :
    (∃ u, (1 + continuousSeparableOperator μ a b) u = f) ↔
      ∀ d : ι → 𝕜, (∀ j, d j + ∑ i, d i * (∫ y, b i y * a j y ∂μ) = 0) →
        ∑ i, d i * (∫ y, b i y * f y ∂μ) = 0 :=
  exists_one_add_separableOperator_eq_iff _ a f

/-- **Conjugate-first sesquilinear continuous separable integral operator** on `C(X, 𝕜)` with
kernel `k(x, y) = ∑ j, a j x * conj (g j y)`, defined as
`continuousSeparableOperator μ a (fun j ↦ star (g j))`. -/
noncomputable def continuousSesqSeparableOperator (a g : ι → C(X, 𝕜)) : C(X, 𝕜) →L[𝕜] C(X, 𝕜) :=
  continuousSeparableOperator μ a (fun j ↦ star (g j))

/-- Expansion of `continuousSesqSeparableOperator μ a g u` as a finite linear combination of
`a j`. -/
@[simp]
theorem continuousSesqSeparableOperator_apply (a g : ι → C(X, 𝕜)) (u : C(X, 𝕜)) :
    continuousSesqSeparableOperator μ a g u =
      ∑ j, (∫ y, starRingEnd 𝕜 (g j y) * u y ∂μ) • a j := by
  rw [continuousSesqSeparableOperator, continuousSeparableOperator_apply]
  simp_rw [ContinuousMap.star_apply, RCLike.star_def]

/-- Over `ℝ`, the sesquilinear and bilinear continuous separable operators coincide. -/
@[simp]
theorem continuousSesqSeparableOperator_real (μ : Measure X) [IsFiniteMeasure μ]
    (a g : ι → C(X, ℝ)) :
    continuousSesqSeparableOperator μ a g = continuousSeparableOperator μ a g := by
  simp [continuousSesqSeparableOperator]

/-- Pointwise integral formula `(continuousSesqSeparableOperator μ a g u) x =
∫ y, (∑ j, a j x * conj (g j y)) * u y ∂μ`. -/
theorem continuousSesqSeparableOperator_apply_apply (a g : ι → C(X, 𝕜)) (u : C(X, 𝕜)) (x : X) :
    continuousSesqSeparableOperator μ a g u x =
      ∫ y, (∑ j, a j x * starRingEnd 𝕜 (g j y)) * u y ∂μ := by
  rw [continuousSesqSeparableOperator]
  simpa only [ContinuousMap.star_apply, RCLike.star_def] using
    continuousSeparableOperator_apply_apply μ a (fun j ↦ star (g j)) u x

/-- Norm bound `‖continuousSesqSeparableOperator μ a g‖ ≤ μ.real Set.univ * ∑ j, ‖a j‖ * ‖g j‖`. -/
theorem norm_continuousSesqSeparableOperator_le (a g : ι → C(X, 𝕜)) :
    ‖continuousSesqSeparableOperator μ a g‖ ≤ μ.real Set.univ * ∑ j, ‖a j‖ * ‖g j‖ := by
  rw [continuousSesqSeparableOperator]
  simpa only [norm_star] using norm_continuousSeparableOperator_le μ a (fun j ↦ star (g j))

/-- **Finite matrix reduction for `(1 + continuousSesqSeparableOperator μ a g) u = f`.** -/
theorem one_add_continuousSesqSeparableOperator_eq_iff (a g : ι → C(X, 𝕜)) (u f : C(X, 𝕜)) :
    (1 + continuousSesqSeparableOperator μ a g) u = f ↔
      ∃ c : ι → 𝕜,
        (∀ i, c i + ∑ j, (∫ y, starRingEnd 𝕜 (g i y) * a j y ∂μ) * c j =
          ∫ y, starRingEnd 𝕜 (g i y) * f y ∂μ) ∧
        u = f - ∑ j, c j • a j := by
  rw [continuousSesqSeparableOperator]
  simpa only [ContinuousMap.star_apply, RCLike.star_def] using
    one_add_continuousSeparableOperator_eq_iff μ a (fun j ↦ star (g j)) u f

/-- **Exact solvability condition for `(1 + continuousSesqSeparableOperator μ a g) u = f`.** -/
theorem exists_one_add_continuousSesqSeparableOperator_eq_iff (a g : ι → C(X, 𝕜)) (f : C(X, 𝕜)) :
    (∃ u, (1 + continuousSesqSeparableOperator μ a g) u = f) ↔
      ∀ d : ι → 𝕜,
        (∀ j, d j + ∑ i, d i * (∫ y, starRingEnd 𝕜 (g i y) * a j y ∂μ) = 0) →
        ∑ i, d i * (∫ y, starRingEnd 𝕜 (g i y) * f y ∂μ) = 0 := by
  rw [continuousSesqSeparableOperator]
  simpa only [ContinuousMap.star_apply, RCLike.star_def] using
    exists_one_add_continuousSeparableOperator_eq_iff μ a (fun j ↦ star (g j)) f

/-- **Determinant bijectivity criterion for `1 + continuousSeparableOperator μ a b`.** -/
theorem bijective_one_add_continuousSeparableOperator_iff_det_ne_zero [DecidableEq ι]
    (a b : ι → C(X, 𝕜)) :
    Function.Bijective (1 + continuousSeparableOperator μ a b : C(X, 𝕜) →L[𝕜] C(X, 𝕜)) ↔
      (1 + continuousSeparableMatrix μ a b).det ≠ 0 := by
  rw [continuousSeparableOperator, continuousSeparableMatrix]
  exact bijective_one_add_separableOperator_iff_det_ne_zero _ a

/-- **Determinant bijectivity criterion for `1 + continuousSesqSeparableOperator μ a g`.** -/
theorem bijective_one_add_continuousSesqSeparableOperator_iff_det_ne_zero [DecidableEq ι]
    (a g : ι → C(X, 𝕜)) :
    Function.Bijective (1 + continuousSesqSeparableOperator μ a g : C(X, 𝕜) →L[𝕜] C(X, 𝕜)) ↔
      (1 + continuousSesqSeparableMatrix μ a g).det ≠ 0 := by
  rw [continuousSesqSeparableOperator, continuousSesqSeparableMatrix]
  exact bijective_one_add_continuousSeparableOperator_iff_det_ne_zero μ a (fun j ↦ star (g j))

end FiniteMeasure

/-- **Slot-convention check on `C([0, 1], ℂ)`.** For the constant factor `f = g = i` on
`unitInterval`, the conjugate-first sesquilinear operator sends `const c` to `const c` so
`1 + K_sesq` sends `const c` to `const (2 * c)` and is bijective, whereas the bilinear operator
sends `const c` to `const (-c)` so `1 + K_bilin` annihilates `1` and has nontrivial kernel. -/
theorem unitInterval_const_I_sesq_vs_bilinear :
    let a : Fin 1 → C(unitInterval, ℂ) := fun _ ↦ ContinuousMap.const unitInterval Complex.I
    (∀ c : ℂ, (1 + continuousSesqSeparableOperator volume a a) (ContinuousMap.const _ c) =
      ContinuousMap.const _ (2 * c)) ∧
      Function.Bijective
        (1 + continuousSesqSeparableOperator volume a a :
          C(unitInterval, ℂ) →L[ℂ] C(unitInterval, ℂ)) ∧
      (1 + continuousSeparableOperator volume a a) 1 = 0 ∧
      LinearMap.ker
        ((1 + continuousSeparableOperator volume a a : C(unitInterval, ℂ) →L[ℂ] C(unitInterval, ℂ))
          : C(unitInterval, ℂ) →ₗ[ℂ] C(unitInterval, ℂ)) ≠ ⊥ := by
  intro a
  have hsesq (c : ℂ) : (1 + continuousSesqSeparableOperator volume a a) (ContinuousMap.const _ c) =
      ContinuousMap.const _ (2 * c) := by
    ext x
    simp only [add_apply, one_apply_eq_self, ContinuousMap.add_apply, ContinuousMap.const_apply,
      continuousSesqSeparableOperator_apply_apply, a, Finset.univ_unique, Finset.sum_singleton,
      Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg, one_mul, integral_const, probReal_univ,
      Complex.real_smul, Complex.ofReal_one]
    ring
  have hdet_sesq : (1 + continuousSesqSeparableMatrix volume a a).det ≠ 0 := by
    rw [Matrix.det_unique]
    simp [continuousSesqSeparableMatrix, continuousSeparableMatrix, a, probReal_univ]
  have hbilin : (1 + continuousSeparableOperator volume a a) 1 = 0 := by
    ext x
    simp [a, probReal_univ]
  refine ⟨hsesq,
    (bijective_one_add_continuousSesqSeparableOperator_iff_det_ne_zero volume a a).mpr hdet_sesq,
    hbilin, fun hbot ↦ ?_⟩
  have h1mem : (1 : C(unitInterval, ℂ)) ∈
      LinearMap.ker
        ((1 + continuousSeparableOperator volume a a : C(unitInterval, ℂ) →L[ℂ] C(unitInterval, ℂ))
          : C(unitInterval, ℂ) →ₗ[ℂ] C(unitInterval, ℂ)) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact hbilin
  rw [hbot, Submodule.mem_bot] at h1mem
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (congrArg (fun u : C(unitInterval, ℂ) ↦ u ⟨0, by simp⟩) h1mem)

end ContinuousSeparable

end TauCeti

end
