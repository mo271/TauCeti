/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.DifferentialForm.Monodromy

/-!
# Primitives of holomorphic functions on simply connected domains

Mathlib's `Complex.IsConservativeOn.isExactOn_ball` and `DifferentiableOn.isExactOn_ball` construct
primitives on discs for Banach-space-valued functions on `ℂ`. This file extends both results to
arbitrary simply connected open subsets `U ⊆ ℂ` via the covering-space exactness theorem
`IsOpen.exists_isPrimitiveOn_of_simplyConnectedSpace` for `1`-forms with local primitives.

For `f : ℂ → E`, associating to each `z : ℂ` the real-linear map `v ↦ v • f z` defines a real
`1`-form on `ℂ` whose primitives on any open subset are precisely the complex primitives of `f` on
that subset. On every open disc inside `U`, Morera's theorem produces a local primitive, so when `U`
is simply connected the `1`-form admits a global primitive on `U`, giving `Complex.IsExactOn f U`.

## Main declarations

* `Complex.IsConservativeOn.isExactOn_of_simplyConnectedSpace`: **Morera's theorem on simply
  connected domains**—a continuous conservative function on a simply connected open subset of `ℂ`
  with values in a complete complex normed space has a primitive.
* `DifferentiableOn.isExactOn_of_simplyConnectedSpace`: every holomorphic function on a simply
  connected open subset of `ℂ` with values in a complete complex normed space has a primitive.
* `Complex.isExactOn_iff_differentiableOn`: on a simply connected open subset of `ℂ`, having a
  primitive is equivalent to holomorphicity.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, Section 4.2, Corollary 2 to Theorem 16
  (analytic functions on simply connected regions have primitives).
-/

public section

open Metric Set
open scoped Manifold

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E}

/-- A function `g : ℂ → E` has complex derivative `f z` at every point of an open set `V ⊆ ℂ`
precisely when it is a real primitive on `V` of the `1`-form `z ↦ (v ↦ v • f z)`. -/
private theorem isPrimitiveOn_toSpanSingleton_iff {g : ℂ → E} {V : Set ℂ} (hV : IsOpen V) :
    TauCeti.IsPrimitiveOn (I := 𝓘(ℝ, ℂ))
        (fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ E (0 : Fin 1)
          ((ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ) :
          TauCeti.RoughForm 𝓘(ℝ, ℂ) ℂ E 1) g V ↔
      ∀ z ∈ V, HasDerivAt g (f z) z := by
  rw [TauCeti.isPrimitiveOn_ofSubsingleton_iff]
  refine ⟨fun ⟨_, hg⟩ z hz ↦ ?_, fun hg ↦ ⟨hV, fun z hz ↦ ?_⟩⟩
  · rw [hasDerivAt_iff_hasFDerivAt]
    exact hasFDerivAt_of_restrictScalars ℝ (hg z hz) rfl
  · exact (hasDerivAt_iff_hasFDerivAt.mp (hg z hz)).restrictScalars ℝ

variable [CompleteSpace E]

/-- **Morera's theorem on simply connected domains.** On a simply connected open subset `U` of `ℂ`,
a continuous function into a complete complex normed space whose integrals around rectangles vanish
has a holomorphic primitive on `U`. -/
theorem IsConservativeOn.isExactOn_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    [SimplyConnectedSpace U] (hf' : ContinuousOn f U) (hf : IsConservativeOn f U) :
    IsExactOn f U := by
  let φ : TauCeti.RoughForm 𝓘(ℝ, ℂ) ℂ E 1 := fun z ↦
    ContinuousAlternatingMap.ofSubsingleton ℝ ℂ E (0 : Fin 1)
      ((ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ)
  obtain ⟨g, hg⟩ := hU.exists_isPrimitiveOn_of_simplyConnectedSpace (φ := φ) fun z hz ↦ by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
    obtain ⟨h, hh⟩ := (hf.mono hball).isExactOn_ball (hf'.mono hball)
    exact ⟨h, ball z r, mem_ball_self hr,
      (isPrimitiveOn_toSpanSingleton_iff isOpen_ball).mpr hh⟩
  exact ⟨g, (isPrimitiveOn_toSpanSingleton_iff hU).mp hg⟩

/-- Every holomorphic function on a simply connected open subset `U` of `ℂ` with values in a
complete complex normed space has a holomorphic primitive on `U`. -/
theorem _root_.DifferentiableOn.isExactOn_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    [SimplyConnectedSpace U] (hf : DifferentiableOn ℂ f U) : IsExactOn f U :=
  hf.isConservativeOn.isExactOn_of_simplyConnectedSpace hU hf.continuousOn

/-- On a simply connected open subset `U` of `ℂ`, a function into a complete complex normed space
has a primitive on `U` if and only if it is holomorphic on `U`. -/
theorem isExactOn_iff_differentiableOn {U : Set ℂ} (hU : IsOpen U) [SimplyConnectedSpace U] :
    IsExactOn f U ↔ DifferentiableOn ℂ f U :=
  ⟨fun hf ↦ hf.differentiableOn hU, fun hf ↦ hf.isExactOn_of_simplyConnectedSpace hU⟩

end Complex
