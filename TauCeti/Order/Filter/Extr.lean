/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels and infimum attainment

A minimum on a sublevel transfers to the full admissible set, and any nonempty sublevel of a
function bounded below shares the infimum of the full set. At a minimizer, the sublevel at the
minimum value is exactly the set of all minimizers, and the value attained equals `sInf (f '' s)`.
-/

public section

open Set

namespace TauCeti

/-- A minimum on a sublevel is a minimum on the whole set, provided its value is
below the sublevel threshold. -/
theorem isMinOn_sublevel_iff {X β : Type*} [LinearOrder β] {f : X → β}
    {S : Set X} {u : X} {b : β} (hu : f u ≤ b) :
    IsMinOn f {x ∈ S | f x ≤ b} u ↔ IsMinOn f S u := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h hx.1⟩
  by_cases hb : f x ≤ b
  · exact h ⟨hx, hb⟩
  · exact hu.trans (le_of_not_ge hb)

/-- Passing to a nonempty sublevel does not change the infimum of a function bounded below. -/
theorem sInf_image_sublevel_eq {X β : Type*} [ConditionallyCompleteLinearOrder β] {f : X → β}
    {S : Set X} {b : β} (hb : BddBelow (f '' S)) (hne : {x ∈ S | f x ≤ b}.Nonempty) :
    sInf (f '' {x ∈ S | f x ≤ b}) = sInf (f '' S) := by
  have hsub : {x ∈ S | f x ≤ b} ⊆ S := fun _ hx ↦ hx.1
  refine le_antisymm ?_ (csInf_le_csInf hb (hne.image f) (image_mono hsub))
  refine le_csInf ((hne.mono hsub).image f) ?_
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxb : f x ≤ b
  · exact csInf_le (hb.mono (image_mono hsub)) (mem_image_of_mem f ⟨hx, hxb⟩)
  · obtain ⟨y, hy⟩ := hne
    exact (csInf_le (hb.mono (image_mono hsub)) (mem_image_of_mem f hy)).trans
      (hy.2.trans (le_of_not_ge hxb))

end TauCeti

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (h hy)⟩⟩

/-- An admissible minimizer realizes `sInf (f '' S)`. -/
theorem IsMinOn.sInf_image_eq {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) : sInf (f '' S) = f u :=
  (h.isGLB hu).csInf_eq ⟨f u, u, hu, rfl⟩

namespace TauCeti

/-- For a function bounded below on `S`, an admissible point is a minimizer if and only if its
value equals `sInf (f '' S)`. -/
theorem isMinOn_iff_eq_sInf_image {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (hu : u ∈ S) (hb : BddBelow (f '' S)) :
    IsMinOn f S u ↔ f u = sInf (f '' S) :=
  ⟨fun h ↦ (h.sInf_image_eq hu).symm,
    fun h _ hx ↦ h.le.trans (csInf_le hb (mem_image_of_mem f hx))⟩

end TauCeti
