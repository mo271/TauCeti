/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Sequence
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Removing the closure from the Banach–Schauder / Henkel approximation

The Baire step of the open mapping theorem produces a point of `closure (f '' U)`, not of
`f '' U`, and every step after it inherits that closure. This file removes it in two settings:

* When the source has a basis of open subgroups at zero (`mem_image_of_mem_closure_image`), a
  point of `closure (f '' V 0)` really is the image of a point of `V 0`: the approximating errors
  tend to zero along the basis, so in a complete nonarchimedean group they are summable, and the
  sum stays inside the closed subgroup `V 0`.
* In any complete first-countable uniform commutative group
  (`isOpenMap_of_closure_image_mem_nhds`), no nonarchimedean hypothesis is needed: Mathlib's
  `IsTopologicalAddGroup.exists_antitone_basis_nhds_zero` supplies an antitone neighbourhood basis
  `V` with `V (n + 1) + V (n + 1) ⊆ V n`, so the partial sums of the approximating sequence are
  Cauchy and stay inside a prescribed closed neighbourhood `U`.

In both cases, regularity of the target sends the residuals to zero (`hasBasis_nhds_closure`),
and separation identifies the image of the limit with the target point.

## Main results

* `TauCeti.mem_image_of_mem_closure_image`: `closure (f '' V 0) ⊆ f '' V 0`, in the presence of
  a basis of subgroups, completeness, and the neighbourhood hypothesis the Baire step supplies.
* `TauCeti.isOpenMap_of_closure_image_mem_nhds`: an additive map out of a complete
  first-countable uniform commutative group is open once the closures of the images of
  neighbourhoods of zero are neighbourhoods of zero.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter IX, §1.7.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology
open scoped Pointwise Uniformity

namespace TauCeti

private theorem tendsto_of_sub_mem_closure_image {M N F : Type*} [AddZeroClass M]
    [TopologicalSpace M] [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [FunLike F M N] [AddMonoidHomClass F M N] (f : F) (hf : ContinuousAt (f : M → N) 0)
    {V : ℕ → Set M} (hV : (𝓝 (0 : M)).HasAntitoneBasis V) {s : ℕ → M} {y : N}
    (hres : ∀ n, y - (f : M → N) (s n) ∈ closure ((f : M → N) '' V (n + 1))) :
    Tendsto (fun n ↦ (f : M → N) (s n)) atTop (𝓝 y) := by
  have hsub : Tendsto (fun n ↦ y - (f : M → N) (s n)) atTop (𝓝 (0 : N)) := by
    refine (hasBasis_nhds_closure (0 : N)).tendsto_right_iff.mpr fun U hU ↦ ?_
    have hpre : (f : M → N) ⁻¹' U ∈ 𝓝 (0 : M) := hf (by rw [map_zero]; exact hU)
    obtain ⟨n₀, -, hn₀⟩ := hV.toHasBasis.mem_iff.mp hpre
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact closure_mono ((Set.image_mono
      ((hV.antitone (hn.trans (Nat.le_succ n))).trans hn₀)).trans
      (Set.image_preimage_subset _ _)) (hres n)
  -- `-(y - f s) + y = f s` reassociates without commuting anything in `N`.
  simpa using hsub.neg.add_const y

private theorem sum_Ico_mem_of_add_subset {M : Type*} [AddCommMonoid M] {V : ℕ → Set M}
    (h0 : ∀ n, (0 : M) ∈ V n) (hadd : ∀ n, V (n + 1) + V (n + 1) ⊆ V n) {x : ℕ → M}
    (hx : ∀ n, x n ∈ V n) :
    ∀ k m, ∑ i ∈ Finset.Ico (m + 1) (m + 1 + k), x i ∈ V m
  | 0, m => by simpa using h0 m
  | k + 1, m => by
    have hsplit : ∑ i ∈ Finset.Ico (m + 1) (m + 1 + (k + 1)), x i =
        x (m + 1) + ∑ i ∈ Finset.Ico (m + 2) (m + 2 + k), x i := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m + 1 < m + 1 + (k + 1))]
      grind
    rw [hsplit]
    exact hadd m (Set.add_mem_add (hx (m + 1)) (sum_Ico_mem_of_add_subset h0 hadd hx k (m + 1)))

variable {M N : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [T0Space N]

/-- **Henkel's approximation converges.** Let `V` be an antitone basis of subgroups at zero in a
complete group `M`, let `f : M → N` be an additive map continuous at zero, and suppose each
`closure (f '' V (n + 1))` is a neighbourhood of zero — which is what the Baire step of Henkel's
theorem provides. Then every point of `closure (f '' V 0)` is already the image of a point of
`V 0`.

`M` is not assumed nonarchimedean: a basis of subgroups at zero is exactly that condition, and
the proof reconstructs the instance from `hV`. `N` need not be commutative, and separation of it
is used only to identify the two limits of the partial sums. -/
theorem mem_image_of_mem_closure_image {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : ContinuousAt (f : M → N) 0) {V : ℕ → AddSubgroup M}
    (hV : (𝓝 (0 : M)).HasAntitoneBasis fun n ↦ (V n : Set M))
    (hVN : ∀ n, closure ((f : M → N) '' (V (n + 1) : Set M)) ∈ 𝓝 (0 : N))
    {y : N} (hy : y ∈ closure ((f : M → N) '' (V 0 : Set M))) :
    y ∈ (f : M → N) '' (V 0 : Set M) := by
  have hf' : Continuous (f : M → N) := continuous_of_continuousAt_zero f hf
  obtain ⟨x, hxV, hxres⟩ :=
    exists_seq_mem_and_sub_sum_mem f (fun n ↦ (V n : Set M)) hVN hy
  -- A basis of subgroups at zero *is* nonarchimedean, so the instance need not be assumed.
  have : NonarchimedeanAddGroup M :=
    ⟨fun U hU ↦ by
      obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp hU
      exact ⟨⟨V n, (V n).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)⟩, hn⟩⟩
  -- The errors tend to zero along the basis, so in a complete group they are summable.
  have hsummable : Summable x :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (by rw [Nat.cofinite_eq_atTop]; exact hV.tendsto hxV)
  -- Their sum stays in `V 0`: an open subgroup is closed, and every error lies in it.
  refine ⟨∑' n, x n, tsum_mem ((V 0).isClosed_of_isOpen
    ((V 0).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)))
    (fun n ↦ hV.antitone (Nat.zero_le n) (hxV n)), ?_⟩
  -- The partial sums have two limits under `f`: its value at the sum, and `y`.
  have hpart : Tendsto (fun n ↦ (f : M → N) (∑ i ∈ Finset.range (n + 1), x i)) atTop
      (𝓝 ((f : M → N) (∑' n, x n))) :=
    ((hf'.tendsto _).comp hsummable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hpart (tendsto_of_sub_mem_closure_image f hf hV hxres)

/-- **Openness from the closure step.** Let `f : M → N` be an additive map, continuous at zero,
out of a complete first-countable uniform commutative group. If the closure of the image of every
neighbourhood of zero is a neighbourhood of zero, then `f` is open.

The hypothesis is what the Baire step of the Banach–Schauder and Henkel theorems provides, and
it can also be checked directly by approximating a dense subset of a neighbourhood of zero in `N`
with control. -/
theorem isOpenMap_of_closure_image_mem_nhds [(𝓝 (0 : M)).IsCountablyGenerated]
    {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (f : F)
    (hfc : ContinuousAt (f : M → N) 0)
    (h : ∀ U ∈ 𝓝 (0 : M), closure ((f : M → N) '' U) ∈ 𝓝 (0 : N)) :
    IsOpenMap (f : M → N) := by
  have hf' : Continuous (f : M → N) := continuous_of_continuousAt_zero f hfc
  have : (𝓤 M).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨u, hu, hu_add⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero M
  refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr fun S hS ↦ ?_
  rw [Filter.mem_map] at hS
  obtain ⟨U, ⟨hU, hU_closed⟩, hUS⟩ := (closed_nhds_basis (0 : M)).mem_iff.mp hS
  obtain ⟨n₀, -, hn₀⟩ := hu.toHasBasis.mem_iff.mp hU
  let V : ℕ → Set M := fun n ↦ u (n + (n₀ + 1))
  have hV : (𝓝 (0 : M)).HasAntitoneBasis V :=
    hu.comp_mono (fun _ _ hab ↦ Nat.add_le_add_right hab _) (tendsto_add_atTop_nat (n₀ + 1))
  have hV_add : ∀ n, V (n + 1) + V (n + 1) ⊆ V n := fun n ↦ by
    simpa [V, Nat.add_right_comm] using hu_add (n + (n₀ + 1))
  have hV0 : ∀ n, (0 : M) ∈ V n := fun n ↦ mem_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)
  have hnhds : ∀ n, closure ((f : M → N) '' V n) ∈ 𝓝 (0 : N) := fun n ↦
    h _ (hV.toHasBasis.mem_of_mem (i := n) trivial)
  refine Filter.mem_of_superset (hnhds 0) fun y hy ↦ ?_
  obtain ⟨x, hxV, hxres⟩ := exists_seq_mem_and_sub_sum_mem f V (fun n ↦ hnhds (n + 1)) hy
  have hcauchy : CauchySeq fun n ↦ ∑ i ∈ Finset.range n, x i := by
    have h𝓤M : (𝓤 M).HasBasis (fun _ ↦ True) fun i ↦ (fun p : M × M ↦ p.1 - p.2) ⁻¹' V i :=
      uniformity_eq_comap_nhds_zero_swapped M ▸ hV.toHasBasis.comap _
    rw [h𝓤M.cauchySeq_iff']
    refine fun m _ ↦ ⟨m + 1, fun n hn ↦ ?_⟩
    simp only [Set.mem_preimage]
    rw [← Finset.sum_Ico_eq_sub _ hn]
    simpa [Nat.add_sub_cancel' hn] using sum_Ico_mem_of_add_subset hV0 hV_add hxV (n - (m + 1)) m
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hzU : z ∈ U := hU_closed.mem_of_tendsto hz <| by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsum : ∑ i ∈ Finset.range n, x i = x 0 + ∑ i ∈ Finset.Ico 1 n, x i := by
      rw [← Finset.sum_range_add_sum_Ico x hn, Finset.sum_range_one]
    rw [hsum]
    exact ((hu_add n₀).trans hn₀) <| Set.add_mem_add (by simpa [V] using hxV 0) <| by
      simpa [V, Nat.add_sub_cancel' hn] using sum_Ico_mem_of_add_subset hV0 hV_add hxV (n - 1) 0
  have hfz : (f : M → N) z = y := tendsto_nhds_unique
    (((hf'.tendsto z).comp hz).comp (tendsto_add_atTop_nat 1))
    (tendsto_of_sub_mem_closure_image f hfc hV hxres)
  exact hfz ▸ hUS hzU

end TauCeti

end
