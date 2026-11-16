/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Witt vectors over reduced rings of characteristic `p`

Let `R` be a commutative ring of characteristic `p`. On `𝕎 R`, the Witt Frobenius operator acts
coordinatewise by `p`-th powers (`WittVector.frobenius_eq_map_frobenius`). When `R` is reduced, its
Frobenius endomorphism is injective (`frobenius_inj`), so Witt Frobenius on `𝕎 R` is injective as
well (`WittVector.frobenius_injective`), without assuming that `R` is perfect.

Combining injectivity of Witt Frobenius with `F(V x) = x * p` (`WittVector.frobenius_verschiebung`)
and injectivity of Verschiebung (`WittVector.verschiebung_injective`) shows that `p` is a
nonzerodivisor in `𝕎 R` (`WittVector.p_mem_nonZeroDivisors`). This extends Mathlib's perfect-ring
`p`-torsion-freeness theorem `WittVector.eq_zero_of_p_mul_eq_zero` to arbitrary reduced
`𝔽_p`-algebras, and in fact `IsReduced R` is both necessary and sufficient in characteristic `p`
(`WittVector.frobenius_injective_iff`, `WittVector.p_mem_nonZeroDivisors_iff`). These properties
provide the `p`-torsion-freeness of `𝕎 R` needed for crystalline cohomology and Witt-vector
comparison arguments over reduced (not necessarily perfect) `𝔽_p`-algebras.

## Main results

* `WittVector.frobenius_injective`: Witt Frobenius on `𝕎 R` is injective when `R` is reduced of
  characteristic `p`.
* `WittVector.frobenius_injective_iff`: in characteristic `p`, Witt Frobenius on `𝕎 R` is injective
  if and only if `R` is reduced.
* `WittVector.p_mem_nonZeroDivisors`: `(p : 𝕎 R)` is a nonzerodivisor when `R` is reduced of
  characteristic `p`.
* `WittVector.p_mem_nonZeroDivisors_iff`: in characteristic `p`, `(p : 𝕎 R)` is a nonzerodivisor if
  and only if `R` is reduced.
* `WittVector.p_mul_injective`, `WittVector.mul_p_injective`, `WittVector.p_mul_eq_zero`,
  `WittVector.mul_p_eq_zero`: `p`-torsion-freeness of `𝕎 R` for reduced `R` of characteristic `p`.

## References

* B. Bhatt, J. Lurie, and A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  §3.6, Proposition 3.6.2.
* A. Langer and T. Zink, *De Rham–Witt cohomology for a proper and smooth morphism*, J. Inst. Math.
  Jussieu 3 (2004), §1.2.
-/

public section

namespace WittVector

open scoped nonZeroDivisors

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

local notation "𝕎" => WittVector p

section InjectiveFrobenius

/-- Over any commutative ring `R`, if Witt Frobenius on `𝕎 R` is injective then `(p : 𝕎 R)` is a
nonzerodivisor. -/
theorem p_mem_nonZeroDivisors_of_frobenius_injective
    (hf : Function.Injective (frobenius : 𝕎 R → 𝕎 R)) :
    (p : 𝕎 R) ∈ (𝕎 R)⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  rw [← frobenius_verschiebung, ← map_zero frobenius] at hx
  exact verschiebung_injective p R (by simpa using hf hx)

end InjectiveFrobenius

section CharP

variable [CharP R p]

variable (p R) in
/-- If `R` is a reduced ring of characteristic `p`, then Witt Frobenius on `𝕎 R` is injective. -/
theorem frobenius_injective [IsReduced R] :
    Function.Injective (frobenius : 𝕎 R → 𝕎 R) := by
  rw [frobenius_eq_map_frobenius]
  exact map_injective (_root_.frobenius R p) (frobenius_inj R p)

variable (p R) in
/-- Over a commutative ring `R` of characteristic `p`, Witt Frobenius on `𝕎 R` is injective if and
only if `R` is reduced. -/
theorem frobenius_injective_iff :
    Function.Injective (frobenius : 𝕎 R → 𝕎 R) ↔ IsReduced R := by
  refine ⟨fun hf ↦ (isReduced_iff_pow_one_lt p hp.out.one_lt).mpr fun r hr ↦ ?_,
    fun _ ↦ frobenius_injective p R⟩
  have h0 : frobenius (teichmuller p r) = frobenius 0 := by
    rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, hr, teichmuller_zero, map_zero]
  simpa using congrArg (fun w : 𝕎 R ↦ w.coeff 0) (hf h0)

variable (p R) in
/-- If `R` is a reduced ring of characteristic `p`, then `(p : 𝕎 R)` is a nonzerodivisor: the ring
of Witt vectors `𝕎 R` is `p`-torsion-free. -/
theorem p_mem_nonZeroDivisors [IsReduced R] : (p : 𝕎 R) ∈ (𝕎 R)⁰ :=
  p_mem_nonZeroDivisors_of_frobenius_injective (frobenius_injective p R)

variable (p R) in
/-- Over a commutative ring `R` of characteristic `p`, `(p : 𝕎 R)` is a nonzerodivisor if and only
if `R` is reduced. -/
theorem p_mem_nonZeroDivisors_iff : (p : 𝕎 R) ∈ (𝕎 R)⁰ ↔ IsReduced R := by
  refine ⟨fun hp0 ↦ (isReduced_iff_pow_one_lt p hp.out.one_lt).mpr fun r hr ↦ ?_,
    fun _ ↦ p_mem_nonZeroDivisors p R⟩
  have hmul : teichmuller p r * (p : 𝕎 R) = 0 := by
    rw [← verschiebung_frobenius, frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, hr,
      teichmuller_zero, map_zero]
  have hteich : teichmuller p r = 0 :=
    (mul_right_mem_nonZeroDivisors_eq_zero_iff hp0).mp hmul
  simpa using congrArg (fun w : 𝕎 R ↦ w.coeff 0) hteich

section IsReduced

variable [IsReduced R]

variable (p R) in
/-- Multiplication on the left by `p` on `𝕎 R` is injective when `R` is reduced of characteristic
`p`. -/
theorem p_mul_injective : Function.Injective (fun x : 𝕎 R ↦ (p : 𝕎 R) * x) := by
  intro x y h
  rw [← sub_eq_zero, ← mul_sub] at h
  exact sub_eq_zero.mp ((mul_left_mem_nonZeroDivisors_eq_zero_iff (p_mem_nonZeroDivisors p R)).mp h)

variable (p R) in
/-- Multiplication on the right by `p` on `𝕎 R` is injective when `R` is reduced of characteristic
`p`. -/
theorem mul_p_injective : Function.Injective (fun x : 𝕎 R ↦ x * (p : 𝕎 R)) := by
  simpa only [mul_comm _ (p : 𝕎 R)] using p_mul_injective p R

/-- In `𝕎 R` for reduced `R` of characteristic `p`, `(p : 𝕎 R) * x = 0` holds iff `x = 0`. -/
@[simp]
theorem p_mul_eq_zero {x : 𝕎 R} : (p : 𝕎 R) * x = 0 ↔ x = 0 :=
  mul_left_mem_nonZeroDivisors_eq_zero_iff (p_mem_nonZeroDivisors p R)

/-- In `𝕎 R` for reduced `R` of characteristic `p`, `x * (p : 𝕎 R) = 0` holds iff `x = 0`. -/
@[simp]
theorem mul_p_eq_zero {x : 𝕎 R} : x * (p : 𝕎 R) = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisors_eq_zero_iff (p_mem_nonZeroDivisors p R)

end IsReduced

end CharP

end WittVector
