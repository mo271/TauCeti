/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Compatible additive group norms

Two additive group norms bounded by constant multiples of one another induce the same
uniformity (`AddGroupNorm.uniformity_eq_of_le`), as does any additive group norm on a uniform
additive group whose open balls form a neighbourhood basis of zero
(`AddGroupNorm.uniformity_eq_of_hasBasis_nhds_zero`). On any uniform additive commutative group,
`AddGroupNorm.toNormedAddCommGroupOfUniformity` installs such a norm while retaining the original
uniformity and topology definitionally. In particular, existing completeness and continuity proofs
remain usable. This construction is shared by adapted, rounded, and completed tensor product norms.
-/

public section

open Filter Topology
open scoped NNReal Uniformity

namespace AddGroupNorm

section NormedAddCommGroup

variable {M : Type*} [NormedAddCommGroup M]

/-- An additive group norm bounded-equivalent to the original norm induces its uniformity. -/
theorem uniformity_eq_of_le (N : AddGroupNorm M) {C D : ℝ≥0}
    (h₁ : ∀ x, N x ≤ C * ‖x‖) (h₂ : ∀ x, ‖x‖ ≤ D * N x) :
    𝓤 M = @uniformity M N.toNormedAddCommGroup.toUniformSpace := by
  let g := ‹NormedAddCommGroup M›
  let n := N.toNormedAddCommGroup
  -- Keep the original norm implicit and name the second metric explicitly.
  let := g
  have hd (x y : M) : @dist M n.toDist x y = N (-x + y) := rfl
  have hf : @UniformContinuous M M g.toUniformSpace n.toUniformSpace id := by
    apply @LipschitzWith.uniformContinuous M M g.toPseudoEMetricSpace n.toPseudoEMetricSpace C id
    apply @LipschitzWith.of_dist_le_mul M M g.toPseudoMetricSpace n.toPseudoMetricSpace C id
    intro x y
    simpa only [id_eq, hd, dist_eq_norm_neg_add] using h₁ (-x + y)
  have hg : @UniformContinuous M M n.toUniformSpace g.toUniformSpace id := by
    apply @LipschitzWith.uniformContinuous M M n.toPseudoEMetricSpace g.toPseudoEMetricSpace D id
    apply @LipschitzWith.of_dist_le_mul M M n.toPseudoMetricSpace g.toPseudoMetricSpace D id
    intro x y
    simpa only [id_eq, hd, dist_eq_norm_neg_add] using h₂ (-x + y)
  apply le_antisymm
  · intro s hs
    exact @uniformContinuous_def M M g.toUniformSpace n.toUniformSpace id |>.mp hf s hs
  · intro s hs
    exact @uniformContinuous_def M M n.toUniformSpace g.toUniformSpace id |>.mp hg s hs

end NormedAddCommGroup

section UniformSpace

variable {M : Type*} [AddCommGroup M] [UniformSpace M]

/-- An additive group norm whose positive open balls form a neighbourhood basis of zero in a
uniform additive group induces its uniformity. -/
theorem uniformity_eq_of_hasBasis_nhds_zero [IsUniformAddGroup M] (N : AddGroupNorm M)
    (h : (𝓝 (0 : M)).HasBasis (0 < ·) fun r ↦ {x | N x < r}) :
    𝓤 M = @uniformity M N.toNormedAddCommGroup.toUniformSpace := by
  let g := N.toNormedAddCommGroup
  have hd (x y : M) : @dist M g.toDist x y = N (y - x) :=
    @dist_eq_norm' M g.toSeminormedAddCommGroup x y
  refine h.uniformity_of_nhds_zero.eq_of_same_basis
    ((@Metric.uniformity_basis_dist M g.toPseudoMetricSpace).congr (fun _ ↦ Iff.rfl) ?_)
  intro ε _
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, hd]

/-- Install an additive group norm with the original uniformity and topology retained
definitionally. Thus completeness and continuity are unchanged. -/
noncomputable abbrev toNormedAddCommGroupOfUniformity (N : AddGroupNorm M)
    (h : 𝓤 M = @uniformity M N.toNormedAddCommGroup.toUniformSpace) : NormedAddCommGroup M :=
  { N.toNormedAddCommGroup with
    toMetricSpace := N.toNormedAddCommGroup.toMetricSpace.replaceUniformity h }

/-- The compatible structure has the specified additive group norm. -/
theorem norm_toNormedAddCommGroupOfUniformity (N : AddGroupNorm M)
    (h : 𝓤 M = @uniformity M N.toNormedAddCommGroup.toUniformSpace) (x : M) :
    @norm M (N.toNormedAddCommGroupOfUniformity h).toNorm x = N x := (rfl)

end UniformSpace

end AddGroupNorm
