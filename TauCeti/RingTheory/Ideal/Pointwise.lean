/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Ideals under a pointwise action

A monoid acting on a semiring by ring endomorphisms carries principal ideals to principal ideals
(`Ideal.smul_span_singleton`). When a group acts by ring automorphisms, its pointwise action on
ideals preserves maximal ideals (`Ideal.IsMaximal.smul`, complementing Mathlib's
`Ideal.IsPrime.smul`) and, over a commutative semiring, preserves coprimality of ideals
(`Ideal.isCoprime_pointwise_smul_iff`).

## Main results

* `Ideal.smul_span_singleton`: `g • span {x} = span {g • x}`.
* `Ideal.IsMaximal.smul`: the translate of a maximal ideal is maximal.
* `Ideal.isCoprime_pointwise_smul_iff`, `Ideal.isCoprime_pointwise_smul_left_iff`,
  `Ideal.isCoprime_pointwise_smul_right_iff`: coprimality of ideals under a pointwise group action.
-/

public section

open scoped Pointwise

namespace Ideal

section Monoid

variable {M R : Type*} [Monoid M] [Semiring R] [MulSemiringAction M R]

/-- The pointwise action on a principal ideal acts on its generator. -/
@[simp]
theorem smul_span_singleton (g : M) (x : R) : g • span {x} = span {g • x} := by
  rw [smul_closure, Set.smul_set_singleton]

end Monoid

section Group

variable {M R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]

/-- **Translates of maximal ideals are maximal.** The translate `g • I` is the preimage of `I`
under a ring automorphism, so it is maximal whenever `I` is. -/
instance IsMaximal.smul {I : Ideal R} [I.IsMaximal] (g : M) : (g • I).IsMaximal := by
  rw [I.pointwise_smul_eq_comap]
  infer_instance

end Group

section CommSemiring

variable {M R : Type*} [Group M] [CommSemiring R] [MulSemiringAction M R]

private theorem isCoprime_of_smul {g : M} {I J : Ideal R} (h : IsCoprime I J) :
    IsCoprime (g • I) (g • J) := by
  rw [isCoprime_iff_sup_eq, ← smul_sup, isCoprime_iff_sup_eq.mp h, pointwise_smul_def, map_top]

/-- A pointwise group action by ring automorphisms preserves coprimality of ideals. -/
@[simp]
theorem isCoprime_pointwise_smul_iff {g : M} {I J : Ideal R} :
    IsCoprime (g • I) (g • J) ↔ IsCoprime I J :=
  ⟨fun h ↦ by simpa using isCoprime_of_smul (g := g⁻¹) h, isCoprime_of_smul⟩

/-- Moving a pointwise group action from the left ideal to the right ideal in `IsCoprime`. -/
theorem isCoprime_pointwise_smul_left_iff {g : M} {I J : Ideal R} :
    IsCoprime (g • I) J ↔ IsCoprime I (g⁻¹ • J) := by
  rw [← isCoprime_pointwise_smul_iff (g := g⁻¹), inv_smul_smul]

/-- Moving a pointwise group action from the right ideal to the left ideal in `IsCoprime`. -/
theorem isCoprime_pointwise_smul_right_iff {g : M} {I J : Ideal R} :
    IsCoprime I (g • J) ↔ IsCoprime (g⁻¹ • I) J := by
  rw [← isCoprime_pointwise_smul_iff (g := g⁻¹), inv_smul_smul]

end CommSemiring

end Ideal
