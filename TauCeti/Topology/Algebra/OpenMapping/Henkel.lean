/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Complete
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Maps.Strict.Module
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import TauCeti.Topology.Algebra.Module.Submodule

/-!
# The Banach–Schauder / Henkel open mapping theorem

A surjective equivariant additive map out of a complete first-countable uniform commutative group
is open, provided the scalars carry a zero sequence of units and the target is a `T0` Baire space.
This file assembles that statement from the pieces built around it.

Each hypothesis pays for one step and no other.

* The zero sequence of units and the Baire property give
  `TauCeti.HasZeroSequenceOfUnits.closure_image_mem_nhds_zero`: the *closure* of the image of a
  neighbourhood of zero is a neighbourhood of zero. Supplying that closure step is the only use
  the Baire hypothesis is put to here; whether a weaker hypothesis would do is not addressed.
* Completeness and countable generation of `𝓝 0` remove the closure in
  `TauCeti.isOpenMap_of_closure_image_mem_nhds`.

No nonarchimedean or local convexity assumption is needed on either space; in particular, over a
nontrivially normed field (such as `ℝ`, `ℂ`, or `ℚ_[p]`, each of which carries a zero sequence of
units), this yields the Banach–Schauder / Fréchet open mapping theorem.

## Main results

* `TauCeti.HasZeroSequenceOfUnits.isOpenMap`: Henkel's / Banach–Schauder open mapping theorem.
* `TauCeti.HasZeroSequenceOfUnits.isQuotientMap`: the surjective map in `isOpenMap` induces the
  quotient topology on its target, so the target's topology is determined by the source's.
* `LinearMap.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits`: over a ring with a zero
  sequence of units, closed-range linear maps from a complete first-countable uniform module into
  a completely metrisable module are strict, assuming continuity at zero for the map and for the
  scalar action on the source, and continuity of constant scalar actions on the target.
* `ContinuousLinearMap.isOpenMap_of_surjective`,
  `ContinuousLinearMap.isQuotientMap_of_surjective`, and
  `ContinuousLinearMap.isStrictMap_of_isClosed_range`: the dot-notation forms for continuous
  linear maps.
* `ContinuousLinearMap.isOpenMap_coprod_of_left` and
  `ContinuousLinearMap.isOpenMap_coprod_of_right`: openness of a coprod map when either factor is
  open.

For a completely metrisable uniform target `F` carrying `[UniformSpace F] [IsUniformAddGroup F]
[MetrizableSpace F] [CompleteSpace F]`, Mathlib's `IsUniformAddGroup.uniformity_countably_generated`
supplies `(𝓤 F).IsCountablyGenerated` so that `BaireSpace F` synthesizes automatically via the
public import `Mathlib.Topology.Baire.CompleteMetrizable`.

The other two implications of Wedhorn's Theorem 6.16, that an open linear map is surjective and that
a continuous one has a complete target, are in `TauCeti.Topology.Algebra.OpenMapping.Converse`.

Mathlib's `MonoidHom.isOpenMap_of_sigmaCompact` proves openness for a continuous surjection from
a σ-compact source onto a T2 Baire target group (locally compact groups being the standard
example of such a target). Neither theorem implies the other: both ask the target to be Baire,
but this one asks the *source* to be complete and first countable where that one asks it to be
σ-compact, and neither of those conditions implies the other.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter IX, §§1.7–1.10.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
* T. Wedhorn, *Adic Spaces*, Theorem 6.16.
-/

public section

open Filter Topology

namespace TauCeti

variable {A M N : Type*} [MonoidWithZero A] [TopologicalSpace A] [HasZeroSequenceOfUnits A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓝 (0 : M)).IsCountablyGenerated] [MulActionWithZero A M]
  [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [T0Space N] [BaireSpace N]
  [MulAction A N] [ContinuousConstSMul A N]

/-- **Banach–Schauder / Henkel open mapping theorem.** A surjective `A`-equivariant additive map
from a complete first-countable uniform commutative group to a `T0` Baire space is open, when `A`
has a zero sequence of units.

Only continuity at zero is asked of `f`, and only continuity in the scalar at zero is asked of
the action, in the form `hc` that the Baire step already uses. -/
theorem HasZeroSequenceOfUnits.isOpenMap {F : Type*} [FunLike F M N] [MulActionHomClass F A M N]
    [AddMonoidHomClass F M N] (f : F) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsOpenMap (f : M → N) :=
  isOpenMap_of_closure_image_mem_nhds f hfc fun _ hU ↦
    HasZeroSequenceOfUnits.closure_image_mem_nhds_zero f hf hc hU

/-- **Open mapping theorem in quotient form.** Under exactly the hypotheses of
`TauCeti.HasZeroSequenceOfUnits.isOpenMap`, the map does not merely carry open sets to open sets:
the topology of `N` is the one coinduced from `M`, so a map out of `N` is continuous exactly when
its composite with `f` is.

The quotient conclusion needs `f` continuous everywhere, but that is not an extra hypothesis: an
additive homomorphism out of a topological group is continuous as soon as it is continuous at `0`
(`continuous_of_continuousAt_zero`), so `hfc` is the same assumption the open-mapping theorem
makes. This is the form behind `TauCeti.Huber.IsTateRing.isModuleTopology`, which pins down the
topology of a finite module over a Tate ring. -/
theorem HasZeroSequenceOfUnits.isQuotientMap {F : Type*} [FunLike F M N]
    [MulActionHomClass F A M N] [AddMonoidHomClass F M N] (f : F) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsQuotientMap (f : M → N) :=
  have hcont : Continuous (f : M → N) := continuous_of_continuousAt_zero f hfc
  (HasZeroSequenceOfUnits.isOpenMap f hf hfc hc).isQuotientMap hcont hf

end TauCeti

namespace LinearMap

open TopologicalSpace

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [IsCompletelyMetrizableSpace F] [Module R F] [ContinuousConstSMul R F]

/-- A linear map with closed range is strict when the scalar ring has a zero sequence of units,
the source is complete and first countable, and the target is completely metrisable. Only
continuity at zero is needed for the map and for scalar multiplication.

The target's additive operations need only be continuous: no uniform structure on the target
or uniform continuity of its operations is assumed. -/
theorem isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits (f : E →ₗ[R] F)
    (hfc : ContinuousAt (f : E → F) 0)
    (hc : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hr : IsClosed (f.range : Set F)) : Topology.IsStrictMap (f : E → F) := by
  have : IsCompletelyMetrizableSpace f.range :=
    hr.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace
  have hcont : Continuous (f.rangeRestrict : E → f.range) :=
    (continuous_of_continuousAt_zero f hfc).subtype_mk _
  exact LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mpr
    ⟨f.surjective_rangeRestrict, hcont,
      TauCeti.HasZeroSequenceOfUnits.isOpenMap f.rangeRestrict f.surjective_rangeRestrict
        hcont.continuousAt hc⟩

end LinearMap

namespace ContinuousLinearMap

open TopologicalSpace

section Semiring

variable {R E F : Type*} [Semiring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module R F]
  [ContinuousConstSMul R F]

/-- **Open mapping theorem for continuous linear maps.** A surjective continuous linear map from a
complete first-countable uniform module to a `T0` Baire topological module over a topological
semiring with a zero sequence of units (in particular, any nontrivially normed field or Tate ring)
is open. -/
theorem isOpenMap_of_surjective [T0Space F] [BaireSpace F] (f : E →L[R] F)
    (hf : Function.Surjective f) : IsOpenMap f :=
  TauCeti.HasZeroSequenceOfUnits.isOpenMap f hf f.continuous.continuousAt
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **Quotient form of the open mapping theorem for continuous linear maps.** Under the hypotheses
of `ContinuousLinearMap.isOpenMap_of_surjective`, `f` is a quotient map. -/
theorem isQuotientMap_of_surjective [T0Space F] [BaireSpace F] (f : E →L[R] F)
    (hf : Function.Surjective f) : IsQuotientMap f :=
  (f.isOpenMap_of_surjective hf).isQuotientMap f.continuous hf

end Semiring

section Ring

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module R F]
  [ContinuousConstSMul R F] [IsCompletelyMetrizableSpace F]

/-- A continuous linear map with closed range from a complete first-countable uniform module into a
completely metrisable module over a topological ring with a zero sequence of units is strict. -/
theorem isStrictMap_of_isClosed_range (f : E →L[R] F) (hr : IsClosed (f.range : Set F)) :
    Topology.IsStrictMap f :=
  f.toLinearMap.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits f.continuous.continuousAt
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt) hr

end Ring

section Coprod

variable {R E G F : Type*} [Semiring R]
  [AddCommMonoid E] [TopologicalSpace E] [Module R E]
  [AddCommMonoid G] [TopologicalSpace G] [Module R G]
  [AddCommGroup F] [TopologicalSpace F] [ContinuousAdd F] [Module R F]

/-- If `f : E →L[R] F` is an open map, then `f.coprod g : E × G →L[R] F` is open for any
`g : G →L[R] F`. -/
theorem isOpenMap_coprod_of_left (f : E →L[R] F) (g : G →L[R] F) (hf : IsOpenMap f) :
    IsOpenMap (f.coprod g) := by
  intro U hU
  have heq : (f.coprod g) '' U = ⋃ b : G, (· + g b) '' (f '' ((fun a ↦ (a, b)) ⁻¹' U)) := by
    ext y
    simp only [Set.mem_image, Prod.exists, coprod_apply, Set.mem_iUnion, Set.mem_preimage]
    exact ⟨fun ⟨a, b, hab, h⟩ ↦ ⟨b, f a, ⟨a, hab, rfl⟩, h⟩,
      fun ⟨b, _, ⟨a, hab, rfl⟩, h⟩ ↦ ⟨a, b, hab, h⟩⟩
  rw [heq]
  exact isOpen_iUnion fun b ↦
    isOpenMap_add_right (g b) _ (hf _ (hU.preimage (continuous_id.prodMk continuous_const)))

/-- If `g : G →L[R] F` is an open map, then `f.coprod g : E × G →L[R] F` is open for any
`f : E →L[R] F`. -/
theorem isOpenMap_coprod_of_right (f : E →L[R] F) (g : G →L[R] F) (hg : IsOpenMap g) :
    IsOpenMap (f.coprod g) := by
  intro U hU
  have heq : (f.coprod g) '' U = ⋃ a : E, (f a + ·) '' (g '' ((fun b ↦ (a, b)) ⁻¹' U)) := by
    ext y
    simp only [Set.mem_image, Prod.exists, coprod_apply, Set.mem_iUnion, Set.mem_preimage]
    exact ⟨fun ⟨a, b, hab, h⟩ ↦ ⟨a, g b, ⟨b, hab, rfl⟩, h⟩,
      fun ⟨a, _, ⟨b, hab, rfl⟩, h⟩ ↦ ⟨a, b, hab, h⟩⟩
  rw [heq]
  exact isOpen_iUnion fun a ↦
    isOpenMap_add_left (f a) _ (hg _ (hU.preimage (continuous_const.prodMk continuous_id)))

end Coprod

end ContinuousLinearMap

end
