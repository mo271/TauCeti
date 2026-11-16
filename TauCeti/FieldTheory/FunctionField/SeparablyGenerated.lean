/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.FieldTheory.Separable.TranscendenceDegreeOne

/-!
# Separably generated algebraic function fields

An algebraic function field over a perfect field admits a separating element: a transcendental
element `x` over which the function field is finite and separable.  This supplies the parameter
needed for the differential calculus of an algebraic function field in arbitrary characteristic,
while keeping the more general results over imperfect fields stated with an explicit separating
element.

Over an imperfect field a separating element still exists when `F` is geometrically reduced over
`k`, for instance when `L ⊗[k] F` is reduced for an algebraically closed field `L` over `k`
(`Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct`). Combining this with
`TauCeti.isGeometricallyReduced_of_separating` equates geometric reducedness of a function field
with the existence of a separating element. If `F ⊗[k] L` is even a domain, then `k` is moreover
algebraically closed in `F` (`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`), so `F`
is separably generated with exact constants, that is, a regular extension of `k`.

In general a separating element need not exist. An element of `F` outside `k` with a
`p`-power in `k`, such as `t^{1/p}` in `𝔽_p(t^{1/p})(X)` over `𝔽_p(t)`, would be both separable
and purely inseparable over `k(x)` for a separating `x`, hence a constant of `k(x)`, which it is
not.

## Main results

* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_perfectField`: a
  function field over a perfect field has a separating element.
* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced`:
  a geometrically reduced function field has a separating element.
* `TauCeti.IsFunctionField.isGeometricallyReduced_iff_exists_separating`: a function field is
  geometrically reduced iff it admits a separating element.
* `TauCeti.IsFunctionField.isDomain_tensorProduct_iff_exists_separating_and_isIntegrallyClosedIn`,
  `TauCeti.IsFunctionField.forall_isDomain_tensorProduct_field_iff`: regular-extension
  equivalences for function fields over an algebraically closed test field and across all field
  extensions.
* `TauCeti.not_isSeparable_adjoin_of_pow_mem`: an element outside `k` with a power
  `α ^ q ^ n` in `k` rules out every separating element.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2 and
  Section IV.1.
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
-/

public section

noncomputable section

open scoped IntermediateField TensorProduct

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace IsFunctionField

/-- **A function field over a perfect field is separably generated** (Stichtenoth,
Proposition 3.10.2): it has a transcendental element `x` such that `F / k(x)` is separable.
Finiteness over `k(x)` follows separately from
`TauCeti.IsFunctionField.finiteDimensional_adjoin`. -/
theorem exists_transcendental_and_isSeparable_adjoin_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  exact TauCeti.exists_transcendental_and_isSeparable_adjoin_of_perfectField hF.trdeg_eq_one

/-- **A geometrically reduced function field is separably generated**: if `F` is geometrically
reduced over `k`, then it has a transcendental element `x` such that `F / k(x)` is separable,
whether or not `k` is perfect. Finiteness over `k(x)` follows separately from
`TauCeti.IsFunctionField.finiteDimensional_adjoin`. -/
theorem exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced
    [Algebra.IsGeometricallyReduced k F] (hF : IsFunctionField k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  exact TauCeti.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced
    hF.trdeg_eq_one

/-- A one-variable function field is geometrically reduced over its base field if and
only if it admits a separating element. -/
theorem isGeometricallyReduced_iff_exists_separating (hF : IsFunctionField k F) :
    Algebra.IsGeometricallyReduced k F ↔
      ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F :=
  ⟨fun _ ↦ hF.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced,
    fun ⟨_, hx, _⟩ ↦ isGeometricallyReduced_of_separating hx⟩

/-- **Regular-extension equivalence for one-variable function fields.** For an
algebraically closed field `Ω` over `k`, `F ⊗[k] Ω` is a domain if and only if `F/k`
admits a separating element and `k` is integrally closed in `F`. -/
theorem isDomain_tensorProduct_iff_exists_separating_and_isIntegrallyClosedIn
    (hF : IsFunctionField k F) (Ω : Type*) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    IsDomain (F ⊗[k] Ω) ↔
      (∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F) ∧
        IsIntegrallyClosedIn k F := by
  rw [isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn Ω,
    hF.isGeometricallyReduced_iff_exists_separating]

/-- A one-variable function field `F/k` stays a domain after tensoring with every field
extension `K/k` if and only if `F/k` admits a separating element and `k` is integrally
closed in `F`. -/
theorem forall_isDomain_tensorProduct_field_iff (hF : IsFunctionField k F) :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔
      (∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F) ∧
        IsIntegrallyClosedIn k F := by
  rw [TauCeti.forall_isDomain_tensorProduct_field_iff,
    hF.isGeometricallyReduced_iff_exists_separating]

end IsFunctionField

end TauCeti
