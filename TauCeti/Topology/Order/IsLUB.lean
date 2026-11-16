/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Minimizing sequences approaching an infimum

Given a function `f : X → β` bounded below on a nonempty set `s : Set X`, this file constructs
sequences `u : ℕ → X` in `s` whose values `f (u n)` converge to `sInf (f '' s)`:

* `TauCeti.exists_antitone_minimizing_seq`: in a first-countable conditionally complete linear
  order topology, `u` can be chosen so that `f ∘ u` is antitone, lifting Mathlib's
  `exists_seq_tendsto_sInf` from `f '' s` back to `s`.
* `TauCeti.exists_seq_mem_lt_csInf_add_one_div`: for real-valued `f : X → ℝ`, `u` can be chosen
  with the quantitative bound `f (u n) < sInf (f '' s) + 1 / (n + 1)` for every `n`.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- In a first-countable conditionally complete linear order topology, any function bounded below
on a nonempty set `s` admits a sequence in `s` with antitone values converging to
`sInf (f '' s)`. -/
theorem exists_antitone_minimizing_seq {X β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {f : X → β} {s : Set X}
    (hne : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Antitone (f ∘ u) ∧
      Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' s))) := by
  obtain ⟨y, hanti, hlim, hmem⟩ := exists_seq_tendsto_sInf (hne.image f) hbdd
  choose u hu hfu using hmem
  have hcomp : f ∘ u = y := funext hfu
  exact ⟨u, hu, hcomp ▸ hanti, hcomp ▸ hlim⟩

/-- For any real-valued function bounded below on a nonempty set `s`, there exists a sequence `u`
in `s` satisfying `f (u n) < sInf (f '' s) + 1 / (n + 1)` and `f (u n) → sInf (f '' s)`. -/
theorem exists_seq_mem_lt_csInf_add_one_div {X : Type*} {f : X → ℝ} {s : Set X}
    (hne : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧
      (∀ n, f (u n) < sInf (f '' s) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' s))) := by
  have hex (n : ℕ) : ∃ x ∈ s, f x < sInf (f '' s) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image f)
      (lt_add_of_pos_right _ (one_div_pos.2 (Nat.cast_add_one_pos n)))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hex
  refine ⟨u, hu, hlt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbdd (mem_image_of_mem f (hu n))) (fun n ↦ (hlt n).le)⟩
  simpa only [add_zero] using
    (tendsto_const_nhds (x := sInf (f '' s))).add tendsto_one_div_add_atTop_nhds_zero_nat

end TauCeti
