/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Minimizing sequences for infima of functions

For a function `f : X → β` bounded below on a nonempty set `S`, we lift Mathlib's
`exists_seq_tendsto_sInf` to an admissible minimizing sequence in `S` whose values decrease
monotonically to `sInf (f '' S)`. For an ordered additive codomain (in particular `ℝ`), we also
construct a minimizing sequence controlled by any prescribed sequence of positive tolerances
tending to zero, including the explicit rate `1 / (n + 1)`.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- Every function bounded below on a nonempty set admits an admissible minimizing sequence
whose values decrease monotonically to `sInf (f '' S)`. -/
theorem exists_seq_tendsto_sInf_image {X β : Type*} [ConditionallyCompleteLinearOrder β]
    [TopologicalSpace β] [OrderTopology β] [FirstCountableTopology β] {f : X → β} {S : Set X}
    (hne : S.Nonempty) (hb : BddBelow (f '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ Antitone (f ∘ u) ∧
      Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' S))) := by
  obtain ⟨y, hy_anti, hy_lim, hy_mem⟩ := exists_seq_tendsto_sInf (hne.image f) hb
  choose u hu hfu using hy_mem
  have hcomp : f ∘ u = y := funext hfu
  exact ⟨u, hu, hcomp.symm ▸ hy_anti, hcomp.symm ▸ hy_lim⟩

/-- Given positive tolerances `ε n → 0`, every function bounded below on a nonempty set admits an
admissible minimizing sequence with `f (u n) < sInf (f '' S) + ε n`. -/
theorem exists_seq_lt_sInf_add {X β : Type*} [ConditionallyCompleteLinearOrder β]
    [AddZeroClass β] [AddLeftStrictMono β] [TopologicalSpace β] [OrderTopology β]
    [SeparatelyContinuousAdd β] {f : X → β} {S : Set X} (hne : S.Nonempty)
    (hb : BddBelow (f '' S)) {ε : ℕ → β} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ (∀ n, f (u n) < sInf (f '' S) + ε n) ∧
      Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' S))) := by
  have hchoose (n : ℕ) : ∃ x ∈ S, f x < sInf (f '' S) + ε n := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne.image f) (lt_add_of_pos_right _ (hε n))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hchoose
  refine ⟨u, hu, hlt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hε0.const_add (sInf (f '' S)))
    (fun n ↦ csInf_le hb (mem_image_of_mem f (hu n)))
    (fun n ↦ (hlt n).le)⟩

/-- Every real-valued function bounded below on a nonempty set admits an admissible minimizing
sequence with `f (u n) < sInf (f '' S) + 1 / (n + 1)`. -/
theorem exists_seq_lt_sInf_add_one_div {X : Type*} {f : X → ℝ} {S : Set X}
    (hne : S.Nonempty) (hb : BddBelow (f '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ (∀ n, f (u n) < sInf (f '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' S))) :=
  exists_seq_lt_sInf_add hne hb (fun n ↦ by positivity) tendsto_one_div_add_atTop_nhds_zero_nat

end TauCeti
