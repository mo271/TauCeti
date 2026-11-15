/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Cointegral.Finite
public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.Module.Injective.Frobenius
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite-dimensional Hopf algebras are Frobenius

A nonzero right invariant functional on a finite-dimensional Hopf algebra is a Frobenius
functional. Here right invariance means `(φ ⊗ id) Δ(x) = φ(x) 1`, so this is the right-cointegral
convention (`TauCeti.isRightCointegral_iff_isRightInvariantIntegral`). Left invariant functionals
give Frobenius functionals as well.

A Frobenius functional on a finite-dimensional bialgebra pairs nontrivially with both integral
spaces: each has a unique element on which the functional is one, so both `leftIntegral k H` and
`rightIntegral k H` are one-dimensional. For a right invariant functional, strong invariance gives
both halves of the dual-basis reconstruction formula from the coproduct of its normalized left
integral, and in particular makes the antipode bijective.

Combining these conditional statements with the existence of a nonzero left cointegral from the
Fundamental Theorem of Hopf Modules (`TauCeti.exists_isLeftCointegral_ne_zero` in
`TauCeti.Algebra.HopfAlgebra.Cointegral.Finite`) establishes the unconditional Larson–Sweedler
theorems for every finite-dimensional Hopf algebra `H` over a field `k`:

* `H` carries a Frobenius functional (`TauCeti.HopfAlgebra.exists_isFrobeniusFunctional`), hence is
  left and right self-injective (`TauCeti.HopfAlgebra.moduleInjective_self`,
  `TauCeti.HopfAlgebra.moduleInjective_op_self`) and its projective and injective left modules
  coincide (`TauCeti.HopfAlgebra.moduleProjective_iff_moduleInjective`);
* `leftIntegral k H`, `rightIntegral k H`, `leftCointegrals k H`, and `rightCointegrals k H` are
  all one-dimensional over `k`;
* the antipode `S : H →ₗ[k] H` is bijective
  (`TauCeti.HopfAlgebra.antipode_bijective_of_finiteDimensional`).

## Main results

* `LinearMap.IsRightInvariantIntegral.sum_apply_antipode_mul_smul`: opposite-side dual-basis
  reconstruction from a normalized left integral.
* `TauCeti.isRightCointegral_iff_isRightInvariantIntegral` and
  `TauCeti.isLeftCointegral_iff_isLeftInvariantIntegral`: equivalence of the cointegral and
  invariant-integral predicates on a bialgebra.
* `TauCeti.HopfAlgebra.exists_isFrobeniusFunctional`: every finite-dimensional Hopf algebra over a
  field admits a Frobenius functional.
* `TauCeti.finrank_leftIntegral`, `TauCeti.finrank_rightIntegral`,
  `TauCeti.finrank_rightCointegrals`: one-dimensionality of left/right integrals and right
  cointegrals.
* `TauCeti.HopfAlgebra.antipode_bijective_of_finiteDimensional`: bijectivity of the antipode in
  finite dimension.
* `TauCeti.HopfAlgebra.moduleProjective_iff_moduleInjective`: projective and injective left modules
  coincide without finiteness assumptions on the module.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. **91** (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, Section 2.1.

The nondegeneracy input is the algebraic faithfulness theorem in
`TauCeti.Algebra.HopfAlgebra.Integral`.
-/

public section

open Coalgebra HopfAlgebra TauCeti
open scoped Coalgebra

namespace LinearMap

variable {k H : Type*} [Field k] [Ring H]

section Bialgebra

variable [Bialgebra k H] [FiniteDimensional k H] {φ : H →ₗ[k] k}

/-- The left integral pairing to one against a Frobenius functional exists uniquely.
No normalization of its counit is required. -/
theorem IsFrobeniusFunctional.existsUnique_leftIntegral_apply_eq_one
    (hφ : φ.IsFrobeniusFunctional) :
    ∃! t : leftIntegral k H, φ t = 1 := by
  obtain ⟨t, ht⟩ := hφ.isPerfPair.bijective_right.surjective (counit (R := k))
  have ht' (x : H) : φ (x * t) = counit (R := k) x :=
    DFunLike.congr_fun ht x
  have hmem : t ∈ leftIntegral k H := by
    rw [mem_leftIntegral_iff]
    intro x
    apply hφ.eq_of_forall_apply_mul_eq
    intro y
    simp [← mul_assoc, ht', mul_comm]
  have hone : φ t = 1 := by simpa using ht' 1
  refine ⟨⟨t, hmem⟩, hone, ?_⟩
  intro u hu
  apply Subtype.ext
  apply hφ.eq_of_forall_apply_mul_eq
  intro x
  simp [(mem_leftIntegral_iff.mp u.property) x, hu, ht']

/-- The right integral pairing to one against a Frobenius functional exists uniquely. -/
theorem IsFrobeniusFunctional.existsUnique_rightIntegral_apply_eq_one
    (hφ : φ.IsFrobeniusFunctional) :
    ∃! t : rightIntegral k H, φ t = 1 := by
  obtain ⟨t, ht⟩ := hφ.toDualEquiv.surjective (counit (R := k))
  have ht' (x : H) : φ (t * x) = counit (R := k) x := by
    simpa using DFunLike.congr_fun ht x
  have hmem : t ∈ rightIntegral k H := by
    rw [mem_rightIntegral_iff]
    intro x
    apply sub_eq_zero.mp
    apply hφ.eq_zero_of_forall_left
    intro y
    simp [sub_mul, mul_assoc, ht']
  have hone : φ t = 1 := by simpa using ht' 1
  refine ⟨⟨t, hmem⟩, hone, ?_⟩
  intro u hu
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hφ.eq_zero_of_forall_left
  intro x
  simp [sub_mul, (mem_rightIntegral_iff.mp u.property) x, hu, ht']

/-- A Frobenius functional identifies the left integral space with a line. -/
theorem IsFrobeniusFunctional.finrank_leftIntegral
    (hφ : φ.IsFrobeniusFunctional) : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨t, ht, _⟩ := hφ.existsUnique_leftIntegral_apply_eq_one
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  apply (finrank_eq_one_iff_of_ne_zero' t ht0).mpr
  intro u
  refine ⟨φ u, ?_⟩
  apply Subtype.ext
  apply hφ.eq_of_forall_apply_mul_eq
  intro x
  simp [(mem_leftIntegral_iff.mp t.property) x,
    (mem_leftIntegral_iff.mp u.property) x, ht, mul_comm]

/-- A Frobenius functional identifies the right integral space with a line. -/
theorem IsFrobeniusFunctional.finrank_rightIntegral
    (hφ : φ.IsFrobeniusFunctional) : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨t, ht, _⟩ := hφ.existsUnique_rightIntegral_apply_eq_one
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  apply (finrank_eq_one_iff_of_ne_zero' t ht0).mpr
  intro u
  refine ⟨φ u, ?_⟩
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hφ.eq_zero_of_forall_left
  intro x
  simp [sub_mul, (mem_rightIntegral_iff.mp t.property) x,
    (mem_rightIntegral_iff.mp u.property) x, ht, mul_comm]

end Bialgebra

section Hopf

variable [HopfAlgebra k H] {φ : H →ₗ[k] k}

/-- A nonzero right invariant functional on a finite-dimensional Hopf algebra
is a Frobenius functional. -/
theorem IsRightInvariantIntegral.isFrobeniusFunctional [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  .of_left fun _ hx => hφ.eq_zero_of_forall_mul_eq_zero h0 hx

/-- A nonzero left invariant functional on a finite-dimensional Hopf algebra
is a Frobenius functional. -/
theorem IsLeftInvariantIntegral.isFrobeniusFunctional [FiniteDimensional k H]
    (hφ : φ.IsLeftInvariantIntegral) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  .of_right fun _ hx => hφ.eq_zero_of_forall_mul_eq_zero h0 hx

/-- A nonzero right invariant functional makes the antipode surjective in finite
dimension, via the normalized left integral's reconstruction formula. -/
theorem IsRightInvariantIntegral.antipode_surjective [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) :
    Function.Surjective (antipode k : H → H) := by
  classical
  obtain ⟨t, ht, _⟩ :=
    (hφ.isFrobeniusFunctional h0).existsUnique_leftIntegral_apply_eq_one
  let r := ℛ k (t : H)
  intro x
  refine ⟨∑ i ∈ r.index, φ (x * r.left i) • r.right i, ?_⟩
  simpa only [map_sum, map_smul] using
    hφ.sum_apply_mul_smul_antipode t.property ht r x

/-- The antipode is bijective whenever a finite-dimensional Hopf algebra admits
a nonzero right invariant functional. -/
theorem IsRightInvariantIntegral.antipode_bijective [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) :
    Function.Bijective (antipode k : H → H) :=
  ⟨LinearMap.injective_iff_surjective.mpr (hφ.antipode_surjective h0),
    hφ.antipode_surjective h0⟩

/-- **Dual-basis reconstruction on the opposite side**: for a right invariant functional `φ` on a
finite-dimensional Hopf algebra and a left integral `t` normalized by `φ t = 1`, the family
`(S t₂, t₁)` from any coproduct representation of `t` also reconstructs `x` by pairing `S t₂` on the
left, complementing `LinearMap.IsRightInvariantIntegral.sum_apply_mul_smul_antipode`. -/
theorem IsRightInvariantIntegral.sum_apply_antipode_mul_smul [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) {t : H} (ht : t ∈ leftIntegral k H)
    (htφ : φ t = 1) {ι : Type*} (r : Coalgebra.Repr k t ι) (x : H) :
    ∑ i ∈ r.index, φ (antipode k (r.right i) * x) • r.left i = x := by
  have h0 : φ ≠ 0 := by
    rintro rfl
    simp at htφ
  apply (hφ.isFrobeniusFunctional h0).eq_of_forall_apply_mul_eq
  intro y
  calc φ (y * ∑ i ∈ r.index, φ (antipode k (r.right i) * x) • r.left i)
      = ∑ i ∈ r.index, φ (y * r.left i) * φ (antipode k (r.right i) * x) := by
        simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = φ ((∑ i ∈ r.index, φ (y * r.left i) • antipode k (r.right i)) * x) := by
        simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
    _ = φ (y * x) := by
        rw [hφ.sum_apply_mul_smul_antipode ht htφ r y]

end Hopf

end LinearMap

namespace TauCeti

section Bridge

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- Right cointegrals on a bialgebra have the same defining contraction equation as right
invariant integrals. -/
theorem isRightCointegral_iff_isRightInvariantIntegral (φ : Module.Dual R H) :
    IsRightCointegral φ ↔ φ.IsRightInvariantIntegral := by
  rw [isRightCointegral_def, LinearMap.isRightInvariantIntegral_iff]

/-- Left cointegrals on a bialgebra have the same defining contraction equation as left
invariant integrals. -/
theorem isLeftCointegral_iff_isLeftInvariantIntegral (φ : Module.Dual R H) :
    IsLeftCointegral φ ↔ φ.IsLeftInvariantIntegral := by
  rw [isLeftCointegral_def, LinearMap.isLeftInvariantIntegral_iff]

alias ⟨IsRightCointegral.isRightInvariantIntegral,
  _root_.LinearMap.IsRightInvariantIntegral.isRightCointegral⟩ :=
  isRightCointegral_iff_isRightInvariantIntegral

alias ⟨IsLeftCointegral.isLeftInvariantIntegral,
  _root_.LinearMap.IsLeftInvariantIntegral.isLeftCointegral⟩ :=
  isLeftCointegral_iff_isLeftInvariantIntegral

end Bridge

section LarsonSweedler

variable {k H : Type*} [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- Every nonzero right cointegral on a finite-dimensional Hopf algebra over a field is a
Frobenius functional. -/
theorem IsRightCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsRightCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  hφ.isRightInvariantIntegral.isFrobeniusFunctional h0

/-- Every nonzero left cointegral on a finite-dimensional Hopf algebra over a field is a
Frobenius functional. -/
theorem IsLeftCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsLeftCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  hφ.isLeftInvariantIntegral.isFrobeniusFunctional h0

variable (k H)

/-- **Larson–Sweedler Frobenius theorem**: every finite-dimensional Hopf algebra over a field
admits a Frobenius functional. -/
theorem HopfAlgebra.exists_isFrobeniusFunctional :
    ∃ φ : H →ₗ[k] k, φ.IsFrobeniusFunctional := by
  obtain ⟨φ, hφ, h0⟩ := exists_isLeftCointegral_ne_zero k H
  exact ⟨φ, hφ.isFrobeniusFunctional h0⟩

/-- **Larson–Sweedler theorem (left integrals)**: the space of left integrals of a
finite-dimensional Hopf algebra over a field has dimension `1`. -/
@[simp]
theorem finrank_leftIntegral : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.finrank_leftIntegral

/-- **Larson–Sweedler theorem (right integrals)**: the space of right integrals of a
finite-dimensional Hopf algebra over a field has dimension `1`. -/
@[simp]
theorem finrank_rightIntegral : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.finrank_rightIntegral

/-- **Larson–Sweedler theorem (right cointegrals)**: the space of right cointegrals of a
finite-dimensional Hopf algebra over a field has dimension `1`. -/
@[simp]
theorem finrank_rightCointegrals : Module.finrank k (rightCointegrals k H) = 1 := by
  rw [(rightCointegralsEquivRightIntegral k H).finrank_eq, finrank_rightIntegral]

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left integral. -/
theorem exists_leftIntegral_ne_zero : ∃ t : H, t ∈ leftIntegral k H ∧ t ≠ 0 := by
  have : Nontrivial (leftIntegral k H) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_leftIntegral]; exact Nat.zero_lt_one)
  obtain ⟨⟨t, ht⟩, hne⟩ := exists_ne (0 : leftIntegral k H)
  exact ⟨t, ht, fun h0 ↦ hne (Subtype.ext h0)⟩

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero right integral. -/
theorem exists_rightIntegral_ne_zero : ∃ t : H, t ∈ rightIntegral k H ∧ t ≠ 0 := by
  have : Nontrivial (rightIntegral k H) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_rightIntegral]; exact Nat.zero_lt_one)
  obtain ⟨⟨t, ht⟩, hne⟩ := exists_ne (0 : rightIntegral k H)
  exact ⟨t, ht, fun h0 ↦ hne (Subtype.ext h0)⟩

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero right cointegral. -/
theorem exists_isRightCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsRightCointegral φ ∧ φ ≠ 0 := by
  have : Nontrivial (rightCointegrals k H) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_rightCointegrals]; exact Nat.zero_lt_one)
  obtain ⟨⟨φ, hφ⟩, hne⟩ := exists_ne (0 : rightCointegrals k H)
  exact ⟨φ, (mem_rightCointegrals φ).mp hφ, fun h0 ↦ hne (Subtype.ext h0)⟩

/-- **Larson–Sweedler antipode theorem**: the antipode of any finite-dimensional Hopf algebra over
a field is bijective. -/
theorem HopfAlgebra.antipode_bijective_of_finiteDimensional :
    Function.Bijective (antipode k : H →ₗ[k] H) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact hφ.isRightInvariantIntegral.antipode_bijective h0

include k in
/-- Every finite-dimensional Hopf algebra over a field is left self-injective. -/
theorem HopfAlgebra.moduleInjective_self : Module.Injective H H := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_self

include k in
/-- Every finite-dimensional Hopf algebra over a field is right self-injective. -/
theorem HopfAlgebra.moduleInjective_op_self : Module.Injective Hᵐᵒᵖ H := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_op_self

variable {H}

include k in
/-- **Projective modules over a finite-dimensional Hopf algebra are injective.** No finiteness is
assumed on the module. -/
theorem HopfAlgebra.moduleInjective_of_projective (P : Type*) [AddCommGroup P] [Module H P]
    [Module.Projective H P] : Module.Injective H P := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_of_projective P

include k in
/-- **Injective modules over a finite-dimensional Hopf algebra are projective.** No finiteness is
assumed on the module. -/
theorem HopfAlgebra.moduleProjective_of_injective.{w} [Small.{w} H] (M : Type w) [AddCommGroup M]
    [Module H M] [Module.Injective H M] : Module.Projective H M := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleProjective_of_injective M

include k in
/-- **Projective and injective modules over a finite-dimensional Hopf algebra coincide**: a left
module over a finite-dimensional Hopf algebra over a field, not necessarily finitely generated, is
projective if and only if it is injective. -/
theorem HopfAlgebra.moduleProjective_iff_moduleInjective.{w} [Small.{w} H] (M : Type w)
    [AddCommGroup M] [Module H M] : Module.Projective H M ↔ Module.Injective H M := by
  obtain ⟨_, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleProjective_iff_moduleInjective M

end LarsonSweedler

end TauCeti
