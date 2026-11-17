/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.NumberTheory.Padics.Complex
import TauCeti.Analysis.Normed.Field.AxSenTate
import TauCeti.Analysis.Normed.Field.GaloisAction

/-!
# The continuous Galois action and Ax–Sen–Tate theorem for `ℂ_[p]`

This file specializes the general normed-field Galois action
(`TauCeti.Analysis.Normed.Field.GaloisAction`) and Ax–Sen–Tate theorem
(`TauCeti.Analysis.Normed.Field.AxSenTate`) to the field `ℂ_[p] = PadicComplex p` of `p`-adic
complex numbers.

Every `ℚ_[p]`-automorphism of `PadicAlgCl p` preserves the spectral norm and extends uniquely by
continuity to an isometric `ℚ_[p]`-algebra automorphism of `ℂ_[p]` (`AlgEquiv.completion`), giving
a jointly continuous action `(PadicAlgCl p ≃ₐ[K] PadicAlgCl p) × ℂ_[p] → ℂ_[p]` for every
intermediate field `K` of `PadicAlgCl p / ℚ_[p]`.

Since `‖(p : ℚ_[p])‖ = p⁻¹ < 1`, the Ax–Sen lemma gives the explicit constant
`p ^ (p / (p - 1)²)` on `PadicAlgCl p`, and the Ax–Sen–Tate theorem identifies the fixed points of
any closed subgroup `H ≤ Gal(PadicAlgCl p / ℚ_[p])` in `ℂ_[p]` with the closure of the algebraic
fixed field `PadicAlgCl p ^ H`, and hence identifies the `Gal(PadicAlgCl p / K)`-fixed points of
`ℂ_[p]` with `K` whenever `K / ℚ_[p]` is finite.

## Main results

* `PadicComplex.continuous_completion_map`: joint continuity of
  `(PadicAlgCl p ≃ₐ[K] PadicAlgCl p) × ℂ_[p] → ℂ_[p]` for any intermediate field
  `K` of `PadicAlgCl p / ℚ_[p]`.
* `PadicComplex.exists_norm_sub_le_of_forall_norm_sub_le`: the Ax–Sen lemma on `PadicAlgCl p` with
  constant `(p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2)`.
* `PadicComplex.forall_completion_map_eq_iff_mem_closure_fixedField`: for any closed subgroup `H`
  of `PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p`, `ℂ_[p] ^ H = closure (PadicAlgCl p ^ H)`.
* `PadicComplex.forall_completion_map_eq_iff_exists_of_finiteDimensional`: for any finite
  intermediate field `K` of `PadicAlgCl p / ℚ_[p]`, `ℂ_[p] ^ G_K = K`.
* `PadicComplex.forall_completion_map_eq_iff_exists_algebraMap`: `ℂ_[p] ^ G_{ℚ_[p]} = ℚ_[p]`.

## References

* J. Ax, *Zeros of polynomials over local fields — the Galois action*, J. Algebra 15 (1970),
  417–428.
* O. Brinon and B. Conrad, *CMI Summer School Notes on `p`-adic Hodge Theory*, §2.1,
  Proposition 2.1.2, p. 12.
* J.-M. Fontaine and Y. Ouyang, *Theory of `p`-adic Galois Representations*, §4.1.2,
  Propositions 4.3 and 4.9, pp. 89–91.
-/

public section

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

private theorem norm_p_padicAlgCl : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap', Padic.norm_p]

private theorem norm_p_padicAlgCl_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap']
  exact Padic.norm_p_lt_one

/-- **Joint continuity of the Galois action on `ℂ_[p]`.** For any intermediate field `K` of
`PadicAlgCl p / ℚ_[p]` (not necessarily finite-dimensional), the extended Galois action
`(PadicAlgCl p ≃ₐ[K] PadicAlgCl p) × ℂ_[p] → ℂ_[p]` via `UniformSpace.Completion.map` is jointly
continuous for the Krull topology on `PadicAlgCl p ≃ₐ[K] PadicAlgCl p` and the norm topology on
`ℂ_[p]`. -/
theorem continuous_completion_map (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Continuous fun z : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) × ℂ_[p] ↦
      UniformSpace.Completion.map z.1 z.2 :=
  TauCeti.continuous_completion_map_of_isScalarTower ℚ_[p]

/-- **The Ax–Sen lemma in `PadicAlgCl p`.** For any intermediate field `K` of
`PadicAlgCl p / ℚ_[p]` and any `α : PadicAlgCl p`, if `‖σ α - α‖ ≤ M` for every
`σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p`, then there exists `a : K` such that
`‖α - (a : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2) * M`. -/
theorem exists_norm_sub_le_of_forall_norm_sub_le
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) {M : ℝ}
    (hα : ∀ σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p, ‖σ α - α‖ ≤ M) :
    ∃ a : K, ‖α - (a : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2) * M := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K
  have h := TauCeti.exists_norm_sub_algebraMap_le_of_forall_norm_sub_le hp hp0
    (norm_p_padicAlgCl_lt_one p)
    (fun σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p ↦ (σ.restrictScalars ℚ_[p]).isometry) α hα
  rw [norm_p_padicAlgCl, inv_inv] at h
  exact h

/-- **Ax–Sen–Tate for closed subgroups of `Gal(PadicAlgCl p / ℚ_[p])`.** For any closed subgroup
`H` of `PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p`, the `H`-fixed points of `ℂ_[p]` equal the closure of
the image of the algebraic fixed field `IntermediateField.fixedField H.toSubgroup`. -/
theorem forall_completion_map_eq_iff_mem_closure_fixedField
    (H : ClosedSubgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (x : ℂ_[p]) :
    (∀ σ ∈ H, UniformSpace.Completion.map σ x = x) ↔
      x ∈ closure (((↑) : PadicAlgCl p → ℂ_[p]) ''
        (IntermediateField.fixedField H.toSubgroup : Set (PadicAlgCl p))) :=
  TauCeti.forall_completion_map_eq_iff_mem_closure_fixedField (Fact.out : p.Prime)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (norm_p_padicAlgCl_lt_one p)
    (fun σ ↦ σ.isometry) H x

/-- **Ax–Sen–Tate for finite extensions of `ℚ_[p]`.** For any finite-dimensional intermediate field
`K` of `PadicAlgCl p / ℚ_[p]`, the `(PadicAlgCl p ≃ₐ[K] PadicAlgCl p)`-fixed points of `ℂ_[p]`
are precisely `K`. -/
theorem forall_completion_map_eq_iff_exists_of_finiteDimensional
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p, UniformSpace.Completion.map σ x = x) ↔
      ∃ k : K, x = ((k : PadicAlgCl p) : ℂ_[p]) :=
  TauCeti.forall_completion_map_eq_iff_exists_of_finiteDimensional
    (Fact.out : p.Prime) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    Padic.norm_p_lt_one K x

/-- **Ax–Sen–Tate over `ℚ_[p]`.** The `(PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)`-fixed points of
`ℂ_[p]` are precisely the image of `ℚ_[p]`. -/
theorem forall_completion_map_eq_iff_exists_algebraMap (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, UniformSpace.Completion.map σ x = x) ↔
      ∃ k : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] k :=
  TauCeti.forall_completion_map_eq_iff_exists_algebraMap
    (Fact.out : p.Prime) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    Padic.norm_p_lt_one x

end PadicComplex
