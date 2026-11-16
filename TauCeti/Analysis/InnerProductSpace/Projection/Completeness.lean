/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Closedness and completeness of projected subspaces

A subspace that admits an orthogonal projection is the range of a continuous idempotent and is
therefore closed. Consequently the sum of two orthogonal subspaces admitting orthogonal
projections also admits an orthogonal projection, is closed, and its orthogonal projection is the
sum of theirs, with no completeness assumption on the ambient space. In a complete ambient
inner-product space, a projected subspace is itself complete, and closedness, completeness and
existence of an orthogonal projection are equivalent.

The completeness observation also appears in
`ForTauCeti/Analysis/InnerProductSpace/ReducingSubspace.lean` of the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0).
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace admitting an orthogonal projection is closed. -/
theorem isClosed_of_hasOrthogonalProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsClosed (U : Set E) := by
  rw [← U.range_starProjection]
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range U.isIdempotentElem_starProjection

private theorem IsOrtho.sub_starProjection_add_mem_orthogonal_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) (v : E) :
    v - (U.starProjection v + V.starProjection v) ∈ (U ⊔ V)ᗮ := by
  rw [← Submodule.inf_orthogonal, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [sub_add_eq_sub_sub]
    exact Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal v)
      (h.symm (V.starProjection_apply_mem v))
  · rw [sub_add_eq_sub_sub_swap]
    exact Vᗮ.sub_mem (V.sub_starProjection_mem_orthogonal v)
      (h (U.starProjection_apply_mem v))

/-- The sum of two orthogonal subspaces admitting orthogonal projections admits an orthogonal
projection, without assuming completeness of the ambient space. -/
theorem IsOrtho.hasOrthogonalProjection_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    (U ⊔ V).HasOrthogonalProjection where
  exists_orthogonal v :=
    ⟨U.starProjection v + V.starProjection v,
      Submodule.add_mem_sup (U.starProjection_apply_mem v) (V.starProjection_apply_mem v),
      h.sub_starProjection_add_mem_orthogonal_sup v⟩

/-- The sum of two orthogonal subspaces admitting orthogonal projections is closed, without
assuming completeness of the ambient space. -/
theorem IsOrtho.isClosed_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    IsClosed ((U ⊔ V : Submodule 𝕜 E) : Set E) := by
  have := h.hasOrthogonalProjection_sup
  exact (U ⊔ V).isClosed_of_hasOrthogonalProjection

/-- The orthogonal projection onto the sum of two orthogonal subspaces is the sum of their
orthogonal projections. -/
theorem IsOrtho.starProjection_sup {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [(U ⊔ V).HasOrthogonalProjection]
    (h : U ⟂ V) :
    (U ⊔ V).starProjection = U.starProjection + V.starProjection := by
  ext v
  rw [_root_.add_apply]
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (Submodule.add_mem_sup (U.starProjection_apply_mem v) (V.starProjection_apply_mem v))
    (h.sub_starProjection_add_mem_orthogonal_sup v)

/-- A subspace admitting an orthogonal projection is complete when the ambient space is. -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsComplete (U : Set E) :=
  (U.isClosed_of_hasOrthogonalProjection).isComplete

variable [CompleteSpace E]

/-- In a complete space, a subspace admitting an orthogonal projection is a complete space.

This is not an instance, since `HasOrthogonalProjection.ofCompleteSpace` goes the other way. -/
theorem completeSpace_coe_of_hasOrthogonalProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : CompleteSpace U :=
  U.isComplete_coe_of_hasOrthogonalProjection.completeSpace_coe

/-- In a complete space, a subspace has an orthogonal projection exactly when it is closed. -/
theorem hasOrthogonalProjection_iff_isClosed {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ IsClosed (U : Set E) :=
  ⟨fun _ ↦ U.isClosed_of_hasOrthogonalProjection, fun h ↦
    have := h.isComplete.completeSpace_coe
    .ofCompleteSpace U⟩

/-- In a complete space, a subspace has an orthogonal projection exactly when it is complete. -/
theorem hasOrthogonalProjection_iff_completeSpace {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ CompleteSpace U :=
  ⟨fun _ ↦ U.completeSpace_coe_of_hasOrthogonalProjection, fun _ ↦ .ofCompleteSpace U⟩

end Submodule
