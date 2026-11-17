/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Upper semicontinuity along order extensions with locally finitely many values

Let `f : X → α` take values in a preorder `α` and suppose `e : α → β` is a monotone map to another
preorder `β` (for instance, passing from the pointwise order on `∀ i, γ i` to the total
lexicographic order `Lex (∀ i, γ i)`). If `f` locally takes only finitely many values and every
upper set `{y | f z ≤ f y}` of an attained value is closed in `X`, then every upper set
`{x | w ≤ e (f x)}` in the target order is also closed: on any neighbourhood `U` where `f` takes
finitely many values, `U ∩ {x | w ≤ e (f x)}` is the finite union of `U ∩ {x | v ≤ f x}` over the
values `v ∈ f '' U` with `w ≤ e v`. When `β` is linearly ordered, `e ∘ f` is upper semicontinuous.

## Main results

* `TauCeti.inter_setOf_le_comp_eq_biUnion`: on any set `U`, the `e`-upper set
  `U ∩ {x | w ≤ e (f x)}` is the union of `U ∩ {x | v ≤ f x}` over attained values
  `v ∈ f '' U` with `w ≤ e v`.
* `TauCeti.isClosed_setOf_le_comp_of_locally_finite_range`: closedness of `{x | w ≤ e (f x)}`
  from closedness of attained `α`-upper sets and local finiteness of values of `f`.
* `TauCeti.upperSemicontinuous_comp_of_isClosed_le`: `UpperSemicontinuous (e ∘ f)` when `β` is
  linearly ordered.
* `TauCeti.upperSemicontinuous_toLex_of_isClosed_le` and
  `TauCeti.upperSemicontinuous_toLex_of_forall_upperSemicontinuous`: specialization to the
  lexicographic order `Lex (∀ i, γ i)`.

## References

* E. Bierstone, P. D. Milman, and M. Temkin, *Q-universal desingularization* (2009), §6.1.
-/

public section

open scoped Topology

namespace TauCeti

section Preorder

variable {X α β : Type*} [Preorder α] [Preorder β]

/-- On any set `U`, the upper level set `{x ∈ U | w ≤ e (f x)}` for a monotone map `e : α → β`
is the union of the `α`-upper level sets `{x ∈ U | v ≤ f x}` over all attained values
`v ∈ f '' U` satisfying `w ≤ e v`. -/
theorem inter_setOf_le_comp_eq_biUnion {f : X → α} {e : α → β} (he : Monotone e) (U : Set X)
    (w : β) :
    U ∩ {x | w ≤ e (f x)} = ⋃ v ∈ f '' U ∩ {v | w ≤ e v}, U ∩ {x | v ≤ f x} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
  refine ⟨fun ⟨hxU, hwx⟩ ↦ ⟨f x, ⟨⟨x, hxU, rfl⟩, hwx⟩, hxU, le_rfl⟩, ?_⟩
  rintro ⟨v, ⟨-, hwv⟩, hxU, hvf⟩
  exact ⟨hxU, hwv.trans (he hvf)⟩

/-- If `f : X → α` locally takes finitely many values and every upper set `{y | f z ≤ f y}` of an
attained value is closed, then `{x | w ≤ e (f x)}` is closed for every monotone `e : α → β` and
every `w : β`. -/
theorem isClosed_setOf_le_comp_of_locally_finite_range [TopologicalSpace X] {f : X → α}
    {e : α → β} (he : Monotone e) (hclosed : ∀ z : X, IsClosed {y : X | f z ≤ f y})
    (hfin : ∀ x : X, ∃ U ∈ 𝓝 x, (f '' U).Finite) (w : β) :
    IsClosed {x : X | w ≤ e (f x)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU_nhds, hU_fin⟩ := hfin x
  obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU_nhds
  have hV_fin : (f '' V).Finite := hU_fin.subset (Set.image_mono hVU)
  let F : Set X := ⋃ v ∈ f '' V ∩ {v | w ≤ e v}, {y : X | v ≤ f y}
  have hF_closed : IsClosed F :=
    (hV_fin.subset Set.inter_subset_left).isClosed_biUnion fun v hv ↦ by
      obtain ⟨z, -, rfl⟩ := hv.1
      exact hclosed z
  have hVF : V ∩ {y : X | w ≤ e (f y)} = V ∩ F := by
    rw [inter_setOf_le_comp_eq_biUnion he V w, Set.inter_iUnion₂]
  have hxF : x ∉ F := fun hxF ↦ hx (by
    have : x ∈ V ∩ {y : X | w ≤ e (f y)} := hVF ▸ ⟨hxV, hxF⟩
    exact this.2)
  refine Filter.mem_of_superset ((hV_open.inter hF_closed.isOpen_compl).mem_nhds ⟨hxV, hxF⟩) ?_
  intro y ⟨hyV, hyF⟩ hyw
  exact hyF (hVF ▸ ⟨hyV, hyw⟩ : y ∈ V ∩ F).2

end Preorder

section LinearOrder

variable {X α β : Type*} [TopologicalSpace X] [Preorder α] [LinearOrder β]

/-- If `f : X → α` locally takes finitely many values and every upper set `{y | f z ≤ f y}` of an
attained value is closed, then `e ∘ f` is upper semicontinuous for any monotone map `e : α → β`
into a linear order. -/
theorem upperSemicontinuous_comp_of_isClosed_le {f : X → α} {e : α → β} (he : Monotone e)
    (hclosed : ∀ z : X, IsClosed {y : X | f z ≤ f y})
    (hfin : ∀ x : X, ∃ U ∈ 𝓝 x, (f '' U).Finite) :
    UpperSemicontinuous (e ∘ f) :=
  upperSemicontinuous_iff_isClosed_preimage.mpr fun w ↦
    isClosed_setOf_le_comp_of_locally_finite_range he hclosed hfin w

end LinearOrder

section PiLex

variable {X ι : Type*} {γ : ι → Type*} [TopologicalSpace X] [LinearOrder ι] [WellFoundedLT ι]
  [∀ i, LinearOrder (γ i)]

/-- **Lexicographic upper semicontinuity from pointwise upper semicontinuity.** If a function
`f : X → ∀ i, γ i` locally takes finitely many values and its pointwise upper sets
`{y | f z ≤ f y}` are closed, then `x ↦ toLex (f x)` is upper semicontinuous for the
lexicographic order. -/
theorem upperSemicontinuous_toLex_of_isClosed_le {f : X → ∀ i, γ i}
    (hclosed : ∀ z : X, IsClosed {y : X | f z ≤ f y})
    (hfin : ∀ x : X, ∃ U ∈ 𝓝 x, (f '' U).Finite) :
    UpperSemicontinuous fun x ↦ toLex (f x) :=
  upperSemicontinuous_comp_of_isClosed_le Pi.toLex_monotone hclosed hfin

/-- If every coordinate `x ↦ f x i` is upper semicontinuous and `f` locally takes finitely many
values, then `x ↦ toLex (f x)` is upper semicontinuous for the lexicographic order. -/
theorem upperSemicontinuous_toLex_of_forall_upperSemicontinuous {f : X → ∀ i, γ i}
    (husc : ∀ i, UpperSemicontinuous fun x ↦ f x i)
    (hfin : ∀ x : X, ∃ U ∈ 𝓝 x, (f '' U).Finite) :
    UpperSemicontinuous fun x ↦ toLex (f x) :=
  upperSemicontinuous_toLex_of_isClosed_le (fun z ↦ by
    have hset : {y : X | f z ≤ f y} = ⋂ i, (fun y ↦ f y i) ⁻¹' Set.Ici (f z i) := by
      ext y
      simp [Pi.le_def]
    rw [hset]
    exact isClosed_iInter fun i ↦ (husc i).isClosed_preimage (f z i)) hfin

end PiLex

end TauCeti
