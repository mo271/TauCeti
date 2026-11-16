/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic

/-!
# Periodicity and antiperiodicity under algebraic operations and composition

A function periodic under `c₁` and `c₂` is periodic under every integer combination
`m c₁ + n c₂` (`Function.Periodic.int_mul_add_int_mul`). For the periods `1` and `i` of a
function on `ℂ` these are the vectors of the lattice `ℤ + ℤ i`; for the periods `τ` and `1` of a
function on `ℂ` they are the vectors of the lattice `ℤ τ + ℤ`.

A function with period `c` composed with the reflection `x ↦ -x` still has period `c`
(`Function.Periodic.comp_neg`).

The family which is a `c`-periodic function `g` at one index and zero at the others is
`c`-periodic at every index (`Function.Periodic.piSingle_apply`).

Pointwise algebraic operations preserve `c`-antiperiodicity: `0`, `-f`, `f + g`, `f - g`, and
pointwise products or scalar multiples of a `c`-periodic function with a `c`-antiperiodic function
are `c`-antiperiodic (`Function.antiperiodic_zero`, `Function.Antiperiodic.fun_neg`,
`Function.Antiperiodic.fun_add`, `Function.Antiperiodic.fun_sub`,
`Function.Periodic.smul_antiperiodic`, `Function.Periodic.mul_antiperiodic`,
`Function.Antiperiodic.mul_periodic`). Postcomposing a `c`-antiperiodic function with an even map
produces a `c`-periodic function (`Function.Antiperiodic.comp_even`), while postcomposing with an
odd map preserves `c`-antiperiodicity (`Function.Antiperiodic.comp_odd`).
-/

public section

namespace Function

section Periodic

variable {α β : Type*} [NonAssocRing α] {f : α → β} {c₁ c₂ : α}

/-- A function periodic under `c₁` and `c₂` is periodic under every integer combination
`m c₁ + n c₂`. -/
theorem Periodic.int_mul_add_int_mul (h₁ : Periodic f c₁) (h₂ : Periodic f c₂) (m n : ℤ) :
    Periodic f (m * c₁ + n * c₂) :=
  (h₁.int_mul m).add_period (h₂.int_mul n)

/-- A function with period `c`, composed with the reflection `x ↦ -x`, has period `c`. -/
theorem Periodic.comp_neg {γ : Type*} [AddCommGroup γ] {f : γ → β} {c : γ} (h : Periodic f c) :
    Periodic (fun x ↦ f (-x)) c := by
  simpa only [zero_sub] using h.const_sub 0

/-- The family which is a `c`-periodic function `g` at the index `i` and zero at the other indices
is `c`-periodic at every index. -/
theorem Periodic.piSingle_apply {ι γ δ : Type*} [DecidableEq ι] [Add γ] [Zero δ] {g : γ → δ} {c : γ}
    (hg : Periodic g c) (i j : ι) : Periodic ((Pi.single i g : ι → γ → δ) j) c := by
  rcases eq_or_ne j i with rfl | h
  · simpa using hg
  · rw [Pi.single_eq_of_ne h]
    exact fun _ ↦ rfl

end Periodic

section Antiperiodic

variable {α β γ : Type*} [Add α] {c : α}

/-- The zero function is `c`-antiperiodic for every `c`. -/
theorem antiperiodic_zero [NegZeroClass β] (c : α) : Antiperiodic (0 : α → β) c :=
  fun _ ↦ neg_zero.symm

/-- Pointwise negation preserves `c`-antiperiodicity (`Function.Antiperiodic.neg` negates the
antiperiod `c` instead). -/
theorem Antiperiodic.fun_neg [Neg β] {f : α → β} (hf : Antiperiodic f c) :
    Antiperiodic (-f) c :=
  fun x ↦ congrArg Neg.neg (hf x)

/-- Pointwise addition of two `c`-antiperiodic functions is `c`-antiperiodic
(`Function.Antiperiodic.add` adds two antiperiods of the same function instead). -/
theorem Antiperiodic.fun_add [SubtractionCommMonoid β] {f g : α → β}
    (hf : Antiperiodic f c) (hg : Antiperiodic g c) : Antiperiodic (f + g) c := fun x ↦ by
  simp only [Pi.add_apply, hf x, hg x, neg_add_rev, add_comm]

/-- Pointwise subtraction of two `c`-antiperiodic functions is `c`-antiperiodic
(`Function.Antiperiodic.sub` subtracts two antiperiods of the same function instead). -/
theorem Antiperiodic.fun_sub [SubtractionCommMonoid β] {f g : α → β}
    (hf : Antiperiodic f c) (hg : Antiperiodic g c) : Antiperiodic (f - g) c :=
  sub_eq_add_neg f g ▸ hf.fun_add hg.fun_neg

/-- Pointwise scalar multiplication of a `c`-periodic scalar function on a `c`-antiperiodic
function is `c`-antiperiodic. -/
theorem Periodic.smul_antiperiodic [Monoid γ] [AddGroup β] [DistribMulAction γ β]
    {f : α → γ} {g : α → β} (hf : Periodic f c) (hg : Antiperiodic g c) :
    Antiperiodic (fun x ↦ f x • g x) c := fun x ↦ by
  simp only [hf x, hg x, smul_neg]

/-- Pointwise multiplication of a `c`-periodic function on the left with a `c`-antiperiodic
function on the right is `c`-antiperiodic. -/
theorem Periodic.mul_antiperiodic [Mul β] [HasDistribNeg β] {f g : α → β}
    (hf : Periodic f c) (hg : Antiperiodic g c) : Antiperiodic (f * g) c := fun x ↦ by
  simp only [Pi.mul_apply, hf x, hg x, mul_neg]

/-- Pointwise multiplication of a `c`-antiperiodic function on the left with a `c`-periodic
function on the right is `c`-antiperiodic. -/
theorem Antiperiodic.mul_periodic [Mul β] [HasDistribNeg β] {f g : α → β}
    (hf : Antiperiodic f c) (hg : Periodic g c) : Antiperiodic (f * g) c := fun x ↦ by
  simp only [Pi.mul_apply, hf x, hg x, neg_mul]

/-- Postcomposing a `c`-antiperiodic function with an even map `g` (`∀ y, g (-y) = g y`) gives a
`c`-periodic function. -/
theorem Antiperiodic.comp_even [Neg β] {f : α → β} (hf : Antiperiodic f c)
    {g : β → γ} (hg : ∀ y, g (-y) = g y) : Periodic (g ∘ f) c := fun x ↦ by
  simp only [comp_apply, hf x, hg]

/-- Postcomposing a `c`-antiperiodic function with an odd map `g` (`∀ y, g (-y) = -g y`) gives a
`c`-antiperiodic function. -/
theorem Antiperiodic.comp_odd [Neg β] [Neg γ] {f : α → β} (hf : Antiperiodic f c)
    {g : β → γ} (hg : ∀ y, g (-y) = -g y) : Antiperiodic (g ∘ f) c := fun x ↦ by
  simp only [comp_apply, hf x, hg]

end Antiperiodic

end Function
