/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal decomposition and monotonicity of Gram matrices under projections

For a subspace `U` of an inner product space admitting an orthogonal projection and an arbitrary
indexed family `v : n → E`, the Gram matrix `(i, j) ↦ ⟪v i, v j⟫` splits as the sum of the Gram
matrices of `P_U ∘ v` and `P_{Uᗮ} ∘ v`. Consequently `gram v - gram (P_{Uᗮ} ∘ v)` is positive
semidefinite, and vanishes if and only if every `v i` already lies in `Uᗮ`. More generally, for
nested projected subspaces `U ≤ V`, the difference `gram (P_{Uᗮ} ∘ v) - gram (P_{Vᗮ} ∘ v)` is the
Gram matrix of `(P_V - P_U) ∘ v` and is therefore positive semidefinite. Neither completeness of
the ambient space nor finiteness of the index type is needed.

In semiparametric statistics these identities are the matrix information-loss inequalities for
projecting a vector of scores onto a nuisance tangent space.

## Main results

* `Submodule.gram_starProjection_add_gram_starProjection_orthogonal`:
  `gram (P_U ∘ v) + gram (P_{Uᗮ} ∘ v) = gram v`.
* `Submodule.posSemidef_gram_sub_gram_starProjection_orthogonal`:
  `gram v - gram (P_{Uᗮ} ∘ v)` is positive semidefinite.
* `Submodule.gram_starProjection_orthogonal_eq_gram_iff`:
  `gram (P_{Uᗮ} ∘ v) = gram v` if and only if every `v i` lies in `Uᗮ`.
* `Submodule.gram_starProjection_orthogonal_sub_of_le` and
  `Submodule.posSemidef_gram_starProjection_orthogonal_sub_of_le`: for `U ≤ V`,
  `gram (P_{Uᗮ} ∘ v) - gram (P_{Vᗮ} ∘ v)` equals `gram ((P_V - P_U) ∘ v)` and is positive
  semidefinite.
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace Submodule

variable {𝕜 E n : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Gram matrix of a family splits into the Gram matrices of its projections onto `U` and
onto `Uᗮ`. -/
theorem gram_starProjection_add_gram_starProjection_orthogonal (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (v : n → E) :
    gram 𝕜 (U.starProjection ∘ v) + gram 𝕜 (Uᗮ.starProjection ∘ v) = gram 𝕜 v := by
  have hproj (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x y : E) :
      ⟪K.starProjection x, K.starProjection y⟫_𝕜 = ⟪K.starProjection x, y⟫_𝕜 := by
    rw [← K.inner_starProjection_left_eq_right,
      K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)]
  ext i j
  simp only [Matrix.add_apply, gram_apply, Function.comp_apply, hproj,
    ← inner_add_left, U.starProjection_add_starProjection_orthogonal]

/-- Subtracting the Gram matrix of the orthogonal-complement projections leaves the Gram matrix
of the projections onto `U`. -/
theorem gram_sub_gram_starProjection_orthogonal (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (v : n → E) :
    gram 𝕜 v - gram 𝕜 (Uᗮ.starProjection ∘ v) = gram 𝕜 (U.starProjection ∘ v) :=
  sub_eq_of_eq_add (U.gram_starProjection_add_gram_starProjection_orthogonal v).symm

/-- Projecting a family onto `Uᗮ` lowers its Gram matrix in the positive-semidefinite order. -/
theorem posSemidef_gram_sub_gram_starProjection_orthogonal (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (v : n → E) :
    (gram 𝕜 v - gram 𝕜 (Uᗮ.starProjection ∘ v)).PosSemidef := by
  rw [U.gram_sub_gram_starProjection_orthogonal v]
  exact Matrix.posSemidef_gram 𝕜 _

/-- Projecting onto `Uᗮ` leaves the Gram matrix of `v` unchanged if and only if every vector in `v`
already lies in `Uᗮ`. -/
theorem gram_starProjection_orthogonal_eq_gram_iff (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (v : n → E) :
    gram 𝕜 (Uᗮ.starProjection ∘ v) = gram 𝕜 v ↔ ∀ i, v i ∈ Uᗮ := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have hsub : gram 𝕜 (U.starProjection ∘ v) = 0 := by
      rw [← U.gram_sub_gram_starProjection_orthogonal v, h, sub_self]
    have hii := congr_fun (congr_fun hsub i) i
    simp only [gram_apply, Function.comp_apply, Matrix.zero_apply, inner_self_eq_zero] at hii
    exact U.starProjection_apply_eq_zero_iff.mp hii
  · have heq : Uᗮ.starProjection ∘ v = v :=
      funext fun i ↦ Uᗮ.starProjection_eq_self_iff.mpr (h i)
    rw [heq]

/-- For `U ≤ V`, the loss in the Gram matrix of residuals from enlarging `U` to `V` is the Gram
matrix of `(P_V - P_U) ∘ v`. -/
theorem gram_starProjection_orthogonal_sub_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) (v : n → E) :
    gram 𝕜 (Uᗮ.starProjection ∘ v) - gram 𝕜 (Vᗮ.starProjection ∘ v) =
      gram 𝕜 (⇑(V.starProjection - U.starProjection) ∘ v) := by
  ext i j
  simp only [Matrix.sub_apply, gram_apply, Function.comp_apply, FunLike.coe_sub,
    Pi.sub_apply]
  -- Decompose `P_{Uᗮ} x = P_{Vᗮ} x + (P_V x - P_U x)` with the two summands in `Vᗮ` and `V`.
  have hsplit (x : E) :
      Uᗮ.starProjection x = Vᗮ.starProjection x + (V.starProjection x - U.starProjection x) := by
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_orthogonal_val]
    abel
  have hmem (x : E) : V.starProjection x - U.starProjection x ∈ V :=
    V.sub_mem (V.starProjection_apply_mem x) (h (U.starProjection_apply_mem x))
  rw [hsplit (v i), hsplit (v j), inner_add_left, inner_add_right, inner_add_right,
    V.inner_right_of_mem_orthogonal (hmem (v i)) (Vᗮ.starProjection_apply_mem (v j)),
    V.inner_left_of_mem_orthogonal (hmem (v j)) (Vᗮ.starProjection_apply_mem (v i)),
    add_zero, zero_add, add_sub_cancel_left]

/-- Enlarging the subspace `U` to `V` lowers the Gram matrix of the orthogonal-complement
projections in the positive-semidefinite order. -/
theorem posSemidef_gram_starProjection_orthogonal_sub_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) (v : n → E) :
    (gram 𝕜 (Uᗮ.starProjection ∘ v) - gram 𝕜 (Vᗮ.starProjection ∘ v)).PosSemidef := by
  rw [gram_starProjection_orthogonal_sub_of_le h v]
  exact Matrix.posSemidef_gram 𝕜 _

end Submodule
