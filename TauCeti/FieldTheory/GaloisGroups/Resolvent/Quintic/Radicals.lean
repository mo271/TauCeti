/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.AbelRuffini.Basic
public import TauCeti.FieldTheory.GaloisGroups.Label
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Separation

import TauCeti.FieldTheory.GaloisGroups.Certificate.Dihedral
import TauCeti.FieldTheory.GaloisGroups.Certificate.Examples
import TauCeti.FieldTheory.GaloisGroups.Certificate.Frobenius

/-!
# Solvability by radicals of quintics and labelled polynomials in characteristic zero

Combining the characteristic-zero radical criterion for polynomials
(`TauCeti.isSolvable_gal_iff_forall_rootSet_mem_solvableByRad`) with Chapman's separation theorem
and Dummit's `F₂₀` resolvent criterion (`TauCeti.isSolvable_gal_iff_exists_isRoot_quinticF20`)
yields **Dummit's Theorem 1 in radical form**: over any field `F` of characteristic zero and any
algebraically closed extension `Ω / F`, a monic irreducible quintic `f : F[X]` has its roots in
`solvableByRad F Ω` if and only if Dummit's `F₂₀` resolvent sextic `quinticF20Spec.specialize F f`
has a root in `F` (`TauCeti.forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20`). No
separability hypothesis on `f` or on the specialized sextic is required.

This file also connects transitive-group labels (`TauCeti.HasGaloisLabel`) to `solvableByRad` in
characteristic zero (`TauCeti.HasGaloisLabel.forall_rootSet_mem_solvableByRad_iff`) and records four
benchmark rational examples:
* `X⁵ - 2` (`5T3 = F₂₀`): all complex/algebraic roots lie in `solvableByRad ℚ Ω`;
* `X⁵ - 5X - 12` (`5T2 = D₅`): all roots lie in `solvableByRad ℚ Ω`;
* `X⁵ - X - 1` (`5T5 = S₅`): no root in any extension `E / ℚ` lies in `solvableByRad ℚ E`;
* `(X⁵ - X - 1)(X - 1)`: reducible degree-six polynomial over `ℚ` having one root (`1`) in
  `solvableByRad ℚ Ω` while not all of its roots lie in `solvableByRad ℚ Ω`, showing that the
  irreducibility hypothesis in `TauCeti.forall_rootSet_mem_solvableByRad_iff_exists` cannot be
  dropped.

## Main results

* `TauCeti.forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20`,
  `TauCeti.exists_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20`: **Dummit's criterion for
  quintics** in radical form.
* `TauCeti.HasGaloisLabel.forall_rootSet_mem_solvableByRad_iff`: a polynomial with a transitive
  Galois label in characteristic zero has radical roots unless its label is `5T4` or `5T5`.
* `TauCeti.forall_rootSet_mem_solvableByRad_X_pow_five_sub_two`,
  `TauCeti.forall_rootSet_mem_solvableByRad_X_pow_five_sub_five_mul_X_sub_twelve`: radical
  solvability of `X⁵ - 2` and `X⁵ - 5X - 12` over `ℚ`.
* `TauCeti.not_mem_solvableByRad_of_mem_rootSet_X_pow_five_sub_X_sub_one`: no root of `X⁵ - X - 1`
  over `ℚ` lies in `solvableByRad`.
* `TauCeti.exists_and_not_forall_rootSet_mem_solvableByRad_mul_X_sub_one`: `(X⁵ - X - 1)(X - 1)`
  has a root in `solvableByRad ℚ Ω` without having all roots in `solvableByRad ℚ Ω`.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), 387–401,
  Theorem 1.
* R. Chapman, *A note on Dummit's "Solving solvable quintics"* (1995).
-/

public section

open Polynomial

namespace TauCeti

section DummitCriterion

/-- **Dummit's criterion for quintics, radical form** (Dummit, *Solving solvable quintics*,
Theorem 1, with Chapman's separation theorem). Over a field `F` of characteristic zero and any
algebraically closed extension `Ω / F` (such as `AlgebraicClosure F` or `ℂ`), all roots in `Ω` of a
monic irreducible quintic `f : F[X]` lie in `solvableByRad F Ω` if and only if Dummit's `F₂₀`
resolvent sextic `quinticF20Spec.specialize F f` has a root in `F`. -/
theorem forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20 {F : Type*} (Ω : Type*)
    [Field F] [CharZero F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] {f : F[X]} (hf : f.Monic)
    (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (∀ x ∈ f.rootSet Ω, x ∈ solvableByRad F Ω) ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  have : NeZero (5 : F) := ⟨OfNat.ofNat_ne_zero 5⟩
  rw [← isSolvable_gal_iff_forall_rootSet_mem_solvableByRad Ω f,
    isSolvable_gal_iff_exists_isRoot_quinticF20 hf hirr.separable hirr hdeg]

/-- Single-root form of Dummit's radical criterion: for a monic irreducible quintic `f : F[X]` in
characteristic zero and an algebraically closed extension `Ω / F`, some root of `f` in `Ω` lies in
`solvableByRad F Ω` if and only if `quinticF20Spec.specialize F f` has a root in `F`. -/
theorem exists_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20 {F : Type*} (Ω : Type*)
    [Field F] [CharZero F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] {f : F[X]} (hf : f.Monic)
    (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (∃ x ∈ f.rootSet Ω, x ∈ solvableByRad F Ω) ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  rw [← forall_rootSet_mem_solvableByRad_iff_exists hirr,
    forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20 Ω hf hirr hdeg]

/-- **Radical solvability from a transitive Galois label.** In characteristic zero, for any
algebraically closed extension `Ω / F`, a polynomial `f : F[X]` carrying the label `j` of degree
`n` (`n ≤ 5`) has all of its roots in `solvableByRad F Ω` if and only if the label is neither `5T4`
nor `5T5`. -/
theorem HasGaloisLabel.forall_rootSet_mem_solvableByRad_iff {F : Type*} (Ω : Type*) [Field F]
    [CharZero F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] {f : F[X]} {n : ℕ}
    {j : TransitiveGroupIndex n} (h : HasGaloisLabel f j) :
    (∀ x ∈ f.rootSet Ω, x ∈ solvableByRad F Ω) ↔ n ≠ 5 ∨ (j : ℕ) < 3 := by
  rw [← isSolvable_gal_iff_forall_rootSet_mem_solvableByRad Ω f,
    h.isSolvable_iff_ne_five_or_lt_three]

end DummitCriterion

section Examples

/-- All roots of the Kummer quintic `X⁵ - 2 : ℚ[X]` (label `5T3 = F₂₀`) in any algebraically closed
`ℚ`-extension `Ω` are solvable by radicals over `ℚ`. -/
theorem forall_rootSet_mem_solvableByRad_X_pow_five_sub_two (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] :
    ∀ x ∈ (X ^ 5 - 2 : ℚ[X]).rootSet Ω, x ∈ solvableByRad ℚ Ω := by
  have hlabel : HasGaloisLabel (X ^ 5 - 2 : ℚ[X]) (⟨2, by simp⟩ : TransitiveGroupIndex 5) := by
    simpa using hasGaloisLabel_X_pow_five_sub_two
  exact (hlabel.forall_rootSet_mem_solvableByRad_iff Ω).mpr (Or.inr (by decide))

/-- All roots of Dummit's dihedral quintic `X⁵ - 5X - 12 : ℚ[X]` (label `5T2 = D₅`) in any
algebraically closed `ℚ`-extension `Ω` are solvable by radicals over `ℚ`. -/
theorem forall_rootSet_mem_solvableByRad_X_pow_five_sub_five_mul_X_sub_twelve (Ω : Type*)
    [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] :
    ∀ x ∈ (X ^ 5 - 5 * X - 12 : ℚ[X]).rootSet Ω, x ∈ solvableByRad ℚ Ω := by
  have hlabel :
      HasGaloisLabel (X ^ 5 - 5 * X - 12 : ℚ[X]) (⟨1, by simp⟩ : TransitiveGroupIndex 5) := by
    simpa using hasGaloisLabel_X_pow_five_sub_five_mul_X_sub_twelve
  exact (hlabel.forall_rootSet_mem_solvableByRad_iff Ω).mpr (Or.inr (by decide))

/-- The quintic `X⁵ - X - 1 : ℚ[X]` (label `5T5 = S₅`) has nonsolvable Galois group. -/
theorem not_isSolvable_gal_X_pow_five_sub_X_sub_one :
    ¬ Group.IsSolvable (X ^ 5 - X - 1 : ℚ[X]).Gal := by
  have hlabel : HasGaloisLabel (X ^ 5 - X - 1 : ℚ[X]) (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
    simpa using hasGaloisLabel_X_pow_five_sub_X_sub_one
  rw [hlabel.isSolvable_iff_ne_five_or_lt_three]
  decide

/-- No root of `X⁵ - X - 1 : ℚ[X]` in any field extension `E / ℚ` lies in `solvableByRad ℚ E`. -/
theorem not_mem_solvableByRad_of_mem_rootSet_X_pow_five_sub_X_sub_one {E : Type*} [Field E]
    [Algebra ℚ E] {x : E} (hx : x ∈ (X ^ 5 - X - 1 : ℚ[X]).rootSet E) :
    x ∉ solvableByRad ℚ E := by
  have hlabel : HasGaloisLabel (X ^ 5 - X - 1 : ℚ[X]) (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
    simpa using hasGaloisLabel_X_pow_five_sub_X_sub_one
  exact fun hrad ↦ not_isSolvable_gal_X_pow_five_sub_X_sub_one
    (isSolvable_gal_of_irreducible hrad hlabel.irreducible (aeval_eq_zero_of_mem_rootSet hx))

/-- **Sharpness of irreducibility in `TauCeti.forall_rootSet_mem_solvableByRad_iff_exists`.**
Over `ℚ`, the reducible degree-six polynomial `(X⁵ - X - 1)(X - 1)` has a root (`1`) in
`solvableByRad ℚ Ω` for every algebraically closed extension `Ω / ℚ`, yet not all of its roots in
`Ω` lie in `solvableByRad ℚ Ω`. -/
theorem exists_and_not_forall_rootSet_mem_solvableByRad_mul_X_sub_one (Ω : Type*) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosed Ω] :
    (∃ x ∈ ((X ^ 5 - X - 1) * (X - 1) : ℚ[X]).rootSet Ω, x ∈ solvableByRad ℚ Ω) ∧
      ¬ (∀ x ∈ ((X ^ 5 - X - 1) * (X - 1) : ℚ[X]).rootSet Ω, x ∈ solvableByRad ℚ Ω) := by
  have hlabel : HasGaloisLabel (X ^ 5 - X - 1 : ℚ[X]) (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
    simpa using hasGaloisLabel_X_pow_five_sub_X_sub_one
  have hf_ne : (X ^ 5 - X - 1 : ℚ[X]) ≠ 0 := hlabel.irreducible.ne_zero
  have hlin_ne : (X - 1 : ℚ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hprod_ne : ((X ^ 5 - X - 1) * (X - 1) : ℚ[X]) ≠ 0 := mul_ne_zero hf_ne hlin_ne
  refine ⟨⟨1, ?_, one_mem _⟩, fun hall ↦ ?_⟩
  · rw [mem_rootSet_of_ne hprod_ne]
    simp
  · refine not_isSolvable_gal_X_pow_five_sub_X_sub_one
      ((isSolvable_gal_iff_forall_rootSet_mem_solvableByRad Ω _).mpr fun x hx ↦ hall x ?_)
    rw [mem_rootSet_of_ne hprod_ne, map_mul, aeval_eq_zero_of_mem_rootSet hx, zero_mul]

end Examples

end TauCeti
