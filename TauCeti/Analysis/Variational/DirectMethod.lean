/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Extr
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Topology.Semicontinuity.Sequential
public import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# The direct method in the weak topology

This file proves the direct method of the calculus of variations in both its topological and
sequential forms.

In the topological form, a weakly lower semicontinuous energy taking values in a linear order on a
nonempty weakly closed admissible set attains its minimum if its sublevels are norm bounded and the
canonical bidual map is surjective. No lower bound on the energy is assumed: compactness of one
nonempty sublevel provides it, and every sublevel and the set of minimizers are weakly compact.

In the sequential form, over `ℝ` or `ℂ`, the angelic (Fréchet–Urysohn) consequence of
Eberlein–Šmulian shows that on any relatively weakly compact set, sequential weak lower
semicontinuity agrees with weak lower semicontinuity, and sequential weak closedness agrees with
weak closedness. Consequently:
* bounded sublevels of a sequentially weakly lower semicontinuous energy on a sequentially weakly
  closed set are weakly compact, yielding minimum attainment and weak compactness of minimizers
  without assuming a prior lower bound;
* a single nonempty bounded sublevel on which sequential closedness and sequential weak lower
  semicontinuity hold suffices;
* for an energy bounded below on a sequentially weakly closed set, the existence of a single
  norm-bounded minimizing sequence yields a minimizer
  (`exists_isMinOn_of_bounded_minimizing_sequence`) and subsequential weak convergence to a
  minimizer (`exists_subseq_tendsto_toWeakSpace_isMinOn`).

The reflexivity hypothesis is surjectivity of the continuous bidual inclusion, not algebraic
reflexivity. Completeness is not needed as a separate hypothesis. The topological results work over
any proper nontrivially normed field and in seminormed spaces; the sequential results work over any
`RCLike` scalar field in normed spaces.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Set Bornology NormedSpace Filter Topology

namespace TauCeti

private theorem image_toWeakSpace_sublevel {𝕜 V β : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
    [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]
    [Preorder β] (E : V → β) (S : Set V) (b : β) :
    toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      (toWeakSpace 𝕜 V '' S) ∩
        (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)) ⁻¹' Iic b := by
  ext u
  simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage,
    mem_ofPred_eq, mem_inter_iff, mem_Iic]

section Topological

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a weakly closed set in a reflexive space, a bounded sublevel of a weakly lower
semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  obtain ⟨C, hC, hEC⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hE b
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    rw [image_toWeakSpace_sublevel, hEC]
    exact hS.inter hC
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace_of_isBounded hV hb

/-- A single nonempty bounded sublevel suffices for the direct method on a weakly
closed admissible set. -/
theorem exists_isMinOn_of_weak_closed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hcompact := isCompact_toWeakSpace_sublevel hV hS hE b hb
  have hsubset : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} ⊆ toWeakSpace 𝕜 V '' S :=
    image_mono fun _ hx ↦ hx.1
  obtain ⟨w, hw, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact (hE.mono hsubset)
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The direct method.** A weakly lower semicontinuous energy with bounded sublevels on
a nonempty weakly closed set in a reflexive space attains its minimum. -/
theorem exists_isMinOn_of_weak_closed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_weak_closed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the full set of minimizers of a weakly lower semicontinuous energy on a weakly
closed set in a reflexive space is bounded, then that set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel hV hS hE (E u) hb

/-- For a weakly lower semicontinuous energy with bounded sublevels on a weakly closed set
in a reflexive space, the set of minimizers is weakly compact, including when the admissible
set is empty. -/
theorem isCompact_toWeakSpace_minimizers
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isBounded hV hS hE hb.isBounded_minimizers

end Topological

section Sequential

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- On a relatively weakly compact subset of a real or complex normed space, sequential weak lower
semicontinuity and weak lower semicontinuity agree. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn_of_isCompact_closure
    {β : Type*} [LinearOrder β] {s : Set (WeakSpace 𝕜 V)} (hs : IsCompact (closure s))
    {f : WeakSpace 𝕜 V → β} :
    SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s :=
  letI : FrechetUrysohnSpace s := frechetUrysohnSpace_of_isCompact_closure hs
  seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

/-- On a sequentially weakly closed set in a reflexive space, a bounded sublevel of a sequentially
weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hseq : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    rw [image_toWeakSpace_sublevel]
    exact hE.isSeqClosed_inter_preimage_Iic hS b
  have hcpt : IsCompact (closure (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :=
    isCompact_closure_toWeakSpace_of_isBounded hV hb
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_iff_isSeqClosed_of_isCompact_closure hcpt).2 hseq
  simpa only [hclosed.closure_eq] using hcpt

/-- **Single-sublevel sequential direct method.** If a single nonempty bounded sublevel of `E` on
`S` is sequentially weakly closed and `E` is sequentially weakly lower semicontinuous on that
sublevel, then `E` attains its minimum on `S`. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty) (hb : IsBounded {u ∈ S | E u ≤ b})
    (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :
    ∃ u ∈ S, IsMinOn E S u := by
  have hcpt : IsCompact (closure (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :=
    isCompact_closure_toWeakSpace_of_isBounded hV hb
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_iff_isSeqClosed_of_isCompact_closure hcpt).2 hsub
  have hcompact : IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    simpa only [hclosed.closure_eq] using hcpt
  have hElsc : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn_of_isCompact_closure hcpt).1 hE
  obtain ⟨w, hw, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact hElsc
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The direct method (sequential sublevel form).** A sequentially weakly lower semicontinuous
energy with bounded sublevels on a nonempty sequentially weakly closed set in a reflexive space
attains its minimum, without assuming a prior lower bound. -/
theorem exists_isMinOn_of_isSeqClosed
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  refine exists_isMinOn_of_isSeqClosed_sublevel hV ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v)) ?_
    (hE.mono (image_mono fun _ hx ↦ hx.1))
  rw [image_toWeakSpace_sublevel]
  exact hE.isSeqClosed_inter_preimage_Iic hS (E v)

/-- If the full set of minimizers of a sequentially weakly lower semicontinuous energy on a
sequentially weakly closed set in a reflexive space is bounded, then that set of minimizers is
weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE (E u) hb

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a sequentially
weakly closed set in a reflexive space, the set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

/-- **The sequential direct method.** In a reflexive space, an energy bounded below on a
sequentially weakly closed set attains its infimum as soon as a norm-bounded minimizing sequence
exists and the energy satisfies the lower-semicontinuity inequality along weakly convergent
sequences with convergent values. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : ∀ (w : ℕ → V) (v : V) (r : β), (∀ n, w n ∈ S) → v ∈ S →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (E ∘ w) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  have hK : IsCompact (closure (toWeakSpace 𝕜 V '' range u)) :=
    isCompact_closure_toWeakSpace_of_isBounded hV hb
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure hK mem_range_self
  have hvS : v ∈ S := isSeqClosed_toWeakSpace_iff.1 hS (u ∘ φ) v (fun n ↦ hu (φ n)) hlim
  have hEv : E v ≤ sInf (E '' S) :=
    hE (u ∘ φ) v (sInf (E '' S)) (fun n ↦ hu (φ n)) hvS hlim (hmin.comp hφ.tendsto_atTop)
  exact ⟨v, hvS, fun x hx ↦ hEv.trans (csInf_le hbelow (mem_image_of_mem E hx))⟩

/-- Single-sublevel variant of the sequential direct method: sequential weak closedness and
sequential weak lower semicontinuity need only hold within a sublevel containing the norm-bounded
minimizing sequence. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence_of_sublevel
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S)) {b : β}
    (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : ∀ (w : ℕ → V) (v : V) (r : β), (∀ n, w n ∈ S ∧ E (w n) ≤ b) → v ∈ S → E v ≤ b →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (E ∘ w) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hub : ∀ n, E (u n) ≤ b) (hb : IsBounded (range u))
    (hmin : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  have hinf : sInf (E '' {x ∈ S | E x ≤ b}) = sInf (E '' S) :=
    sInf_image_sublevel_eq hbelow ⟨u 0, hu 0, hub 0⟩
  obtain ⟨v, hv, hvmin⟩ :=
    exists_isMinOn_of_bounded_minimizing_sequence (S := {u ∈ S | E u ≤ b}) hV
      (hbelow.mono (image_mono fun _ hx ↦ hx.1)) hsub
      (fun w v r hw hv hlim hr ↦ hE w v r hw hv.1 hv.2 hlim hr)
      (fun n ↦ ⟨hu n, hub n⟩) hb (hinf.symm ▸ hmin)
  exact ⟨v, hv.1, (isMinOn_sublevel_iff hv.2).1 hvmin⟩

/-- Every norm-bounded minimizing sequence in a sequentially weakly closed set in a reflexive space
has a subsequence converging weakly to a minimizer. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  have hK : IsCompact (closure (toWeakSpace 𝕜 V '' range u)) :=
    isCompact_closure_toWeakSpace_of_isBounded hV hb
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure hK mem_range_self
  have hvS : v ∈ S := isSeqClosed_toWeakSpace_iff.1 hS (u ∘ φ) v (fun n ↦ hu (φ n)) hlim
  have hmin' : IsMinOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) (toWeakSpace 𝕜 V v) := by
    have hEq : (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) '' (toWeakSpace 𝕜 V '' S) =
        E '' S := by
      ext y
      simp only [mem_image, exists_exists_and_eq_and, LinearEquiv.symm_apply_apply]
    refine hE.isMinOn_of_tendsto (hEq ▸ hbelow)
      (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 V) (hu (φ n)))
      (mem_image_of_mem (toWeakSpace 𝕜 V) hvS) hlim ?_
    simpa only [hEq, Function.comp_def, LinearEquiv.symm_apply_apply] using
      hmin.comp hφ.tendsto_atTop
  refine ⟨v, hvS, fun x hx ↦ ?_, φ, hφ, hlim⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin' (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

end Sequential

end TauCeti
