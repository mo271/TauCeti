/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Extending local identities from locally dense sets

Two maps into a Hausdorff space that agree near a point `x` within a set `s` whose closure is a
neighbourhood of `x`, and that are continuous within `s` at every point near `x`, agree on a full
neighbourhood of `x`. This is a germ-level analogue of `Set.EqOn.of_subset_closure`. For
example, it extends identities across a coordinate hyperplane whose complement is dense.

Similarly, agreement near `x` within a subset `w ⊆ s` that is locally dense in `s` extends to
agreement within `s` when `f` is continuous within `s` and `g` is continuous within `w` along `s`
near `x`, and any continuous local extension `g` of `f` across a locally dense set `s` agrees near
`x` with `z ↦ limUnder (𝓝[s] z) f`.
-/

public section

open Filter Topology

/-- Maps into a Hausdorff space that agree near `x` within a set `s` whose closure is a
neighbourhood of `x`, and that are continuous within `s` at every point near `x`, agree on a full
neighbourhood of `x`. -/
theorem Filter.EventuallyEq.eventuallyEq_nhds_of_closure_mem_nhds {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {s : Set X} {x : X} {f g : X → Y}
    (hfg : f =ᶠ[𝓝[s] x] g) (hs : closure s ∈ 𝓝 x)
    (hf : ∀ᶠ z in 𝓝 x, ContinuousWithinAt f s z) (hg : ∀ᶠ z in 𝓝 x, ContinuousWithinAt g s z) :
    f =ᶠ[𝓝 x] g := by
  filter_upwards [hs, hf, hg, (eventually_nhdsWithin_iff.mp hfg).eventually_nhds]
    with z hzs hfz hgz hz
  have := mem_closure_iff_nhdsWithin_neBot.mp hzs
  exact tendsto_nhds_unique_of_eventuallyEq hfz hgz (eventually_nhdsWithin_iff.mpr hz)

/-- If `f` agrees with `g` near `x` within a subset `w ⊆ s` such that `closure w ∈ 𝓝[s] x`,
`f` is continuous within `s` along `𝓝[s] x`, and `g` is continuous within `w` along `𝓝[s] x`, then
`f` and `g` agree near `x` within `s`. -/
theorem Filter.EventuallyEq.nhdsWithin_of_subset_of_closure_mem_nhdsWithin {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {w s : Set X} {x : X} {f g : X → Y}
    (hws : w ⊆ s) (hfg : f =ᶠ[𝓝[w] x] g) (hw : closure w ∈ 𝓝[s] x)
    (hf : ∀ᶠ z in 𝓝[s] x, ContinuousWithinAt f s z)
    (hg : ∀ᶠ z in 𝓝[s] x, ContinuousWithinAt g w z) :
    f =ᶠ[𝓝[s] x] g := by
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [eventually_nhdsWithin_iff.mp hf, eventually_nhdsWithin_iff.mp hw,
    eventually_nhdsWithin_iff.mp hg, (eventually_nhdsWithin_iff.mp hfg).eventually_nhds]
    with z hfz hzw hgz hz hzs
  have := mem_closure_iff_nhdsWithin_neBot.mp (hzw hzs)
  exact tendsto_nhds_unique_of_eventuallyEq ((hfz hzs).mono hws) (hgz hzs)
    (eventually_nhdsWithin_iff.mpr hz)

/-- If `g` is continuous within `s` at every point near `x`, agrees with `f` near `x` within `s`,
and `closure s ∈ 𝓝 x`, then `z ↦ limUnder (𝓝[s] z) f` agrees with `g` near `x`. -/
theorem Filter.EventuallyEq.eventuallyEq_limUnder_nhdsWithin_of_closure_mem_nhds {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [Nonempty Y] {s : Set X} {x : X}
    {f g : X → Y} (hfg : f =ᶠ[𝓝[s] x] g) (hs : closure s ∈ 𝓝 x)
    (hg : ∀ᶠ z in 𝓝 x, ContinuousWithinAt g s z) :
    (fun z ↦ limUnder (𝓝[s] z) f) =ᶠ[𝓝 x] g := by
  filter_upwards [hs, hg, (eventually_nhdsWithin_iff.mp hfg.symm).eventually_nhds]
    with z hzs hgz hz
  have := mem_closure_iff_nhdsWithin_neBot.mp hzs
  exact (hgz.congr' (eventually_nhdsWithin_iff.mpr hz)).limUnder_eq
