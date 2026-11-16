/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Base change of homogeneous polynomial pieces

Let `S` be an `R`-algebra. Tensoring the degree-`n` homogeneous piece `homogeneousSubmodule σ R n`
of `MvPolynomial σ R` on the left by `S` gives `homogeneousSubmodule σ S n`, compatibly with both:

* the monomial bases `(homogeneousMonomialBasis n).baseChange S` and `homogeneousMonomialBasis n`,
  indexed by `{e : σ →₀ ℕ // e.degree = n}`; and
* the ambient polynomial base-change equivalence `MvPolynomial.algebraTensorAlgEquiv R S`.

No finiteness assumption on `σ` or Noetherian assumption on `R` or `S` is needed.

## Main definitions

* `TauCeti.homogeneousSubmoduleBaseChangeEquiv`: the `S`-linear equivalence
  `S ⊗[R] homogeneousSubmodule σ R n ≃ₗ[S] homogeneousSubmodule σ S n`.

## Main results

* `TauCeti.homogeneousSubmoduleBaseChangeEquiv_tmul` and
  `TauCeti.coe_homogeneousSubmoduleBaseChangeEquiv_tmul`: action on pure tensors.
* `TauCeti.homogeneousSubmoduleBaseChangeEquiv_basis`: the equivalence carries the base-changed
  monomial basis to the monomial basis over `S`.
* `TauCeti.coe_homogeneousSubmoduleBaseChangeEquiv_eq_algebraTensorAlgEquiv`: compatibility with
  `MvPolynomial.algebraTensorAlgEquiv R S` along
  `(homogeneousSubmodule σ R n).subtype.baseChange S`.
* `MvPolynomial.map_algebraTensorAlgEquiv_baseChange_homogeneousSubmodule`: the image of
  `(homogeneousSubmodule σ R n).baseChange S` under `algebraTensorAlgEquiv R S` is
  `homogeneousSubmodule σ S n`.
-/

public section

open scoped TensorProduct
open MvPolynomial

namespace TauCeti

section Equiv

variable (σ R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] (n : ℕ) in
/-- Base change of the degree-`n` homogeneous polynomials along an arbitrary `R`-algebra `S`. -/
noncomputable def homogeneousSubmoduleBaseChangeEquiv :
    S ⊗[R] homogeneousSubmodule σ R n ≃ₗ[S] homogeneousSubmodule σ S n :=
  ((homogeneousMonomialBasis (σ := σ) (R := R) n).baseChange S).equiv
    (homogeneousMonomialBasis (σ := σ) (R := S) n) (Equiv.refl _)

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Base change sends the base-changed monomial basis over `R` to the monomial basis over `S`. -/
theorem homogeneousSubmoduleBaseChangeEquiv_basis (n : ℕ) (i : {e : σ →₀ ℕ // e.degree = n}) :
    homogeneousSubmoduleBaseChangeEquiv σ R S n
        (((homogeneousMonomialBasis (σ := σ) (R := R) n).baseChange S) i) =
      homogeneousMonomialBasis (σ := σ) (R := S) n i := by
  rw [homogeneousSubmoduleBaseChangeEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

@[simp]
theorem homogeneousSubmoduleBaseChangeEquiv_symm_basis (n : ℕ)
    (i : {e : σ →₀ ℕ // e.degree = n}) :
    (homogeneousSubmoduleBaseChangeEquiv σ R S n).symm
        (homogeneousMonomialBasis (σ := σ) (R := S) n i) =
      ((homogeneousMonomialBasis (σ := σ) (R := R) n).baseChange S) i := by
  rw [LinearEquiv.symm_apply_eq, homogeneousSubmoduleBaseChangeEquiv_basis]

@[simp]
theorem homogeneousSubmoduleBaseChangeEquiv_tmul (n : ℕ) (s : S)
    (p : homogeneousSubmodule σ R n) :
    homogeneousSubmoduleBaseChangeEquiv σ R S n (s ⊗ₜ p) =
      s • mapHomogeneousSubmodule (algebraMap R S) n p := by
  have h1 : homogeneousSubmoduleBaseChangeEquiv σ R S n (1 ⊗ₜ p) =
      mapHomogeneousSubmodule (algebraMap R S) n p := by
    have hp : p ∈ Submodule.span R (Set.range (homogeneousMonomialBasis (σ := σ) (R := R) n)) := by
      rw [(homogeneousMonomialBasis (σ := σ) (R := R) n).span_eq]
      trivial
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← Module.Basis.baseChange_apply, homogeneousSubmoduleBaseChangeEquiv_basis,
        mapHomogeneousSubmodule_homogeneousMonomialBasis]
    | zero => simp
    | add x y _ _ hx hy => simp [TensorProduct.tmul_add, hx, hy]
    | smul r x _ hx =>
      have hsmul : (1 : S) ⊗ₜ[R] (r • x) = algebraMap R S r • ((1 : S) ⊗ₜ[R] x) := by
        rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul]
      rw [hsmul, map_smul, hx, LinearMap.map_smulₛₗ]
  have hs : s ⊗ₜ[R] p = s • ((1 : S) ⊗ₜ[R] p) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, map_smul, h1]

theorem coe_homogeneousSubmoduleBaseChangeEquiv_tmul (n : ℕ) (s : S)
    (p : homogeneousSubmodule σ R n) :
    (homogeneousSubmoduleBaseChangeEquiv σ R S n (s ⊗ₜ p) : MvPolynomial σ S) =
      s • MvPolynomial.map (algebraMap R S) p := by
  simp

/-- `homogeneousSubmoduleBaseChangeEquiv` intertwines the base-changed submodule inclusion with
`MvPolynomial.algebraTensorAlgEquiv R S`. -/
theorem coe_homogeneousSubmoduleBaseChangeEquiv_eq_algebraTensorAlgEquiv (n : ℕ)
    (x : S ⊗[R] homogeneousSubmodule σ R n) :
    (homogeneousSubmoduleBaseChangeEquiv σ R S n x : MvPolynomial σ S) =
      algebraTensorAlgEquiv R S ((homogeneousSubmodule σ R n).subtype.baseChange S x) :=
  TensorProduct.inductionOn x (fun s p ↦ by simp) (fun x y hx hy ↦ by simp [hx, hy])

end Equiv

end TauCeti

namespace MvPolynomial

/-- Under `MvPolynomial.algebraTensorAlgEquiv R S`, the `S`-submodule
`(homogeneousSubmodule σ R n).baseChange S` of `S ⊗[R] MvPolynomial σ R` maps onto
`homogeneousSubmodule σ S n`. -/
@[simp]
theorem map_algebraTensorAlgEquiv_baseChange_homogeneousSubmodule
    (σ R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] (n : ℕ) :
    ((homogeneousSubmodule σ R n).baseChange S).map
        (algebraTensorAlgEquiv R S).toLinearMap =
      homogeneousSubmodule σ S n := by
  refine le_antisymm ?_ fun q hq ↦ ?_
  · rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule, TensorProduct.mk_apply,
      AlgEquiv.toLinearMap_apply, algebraTensorAlgEquiv_tmul, one_smul]
    exact hp.map (algebraMap R S)
  · let x := (TauCeti.homogeneousSubmoduleBaseChangeEquiv σ R S n).symm ⟨q, hq⟩
    refine ⟨(homogeneousSubmodule σ R n).subtype.baseChange S x, ⟨x, rfl⟩, ?_⟩
    have hx := TauCeti.coe_homogeneousSubmoduleBaseChangeEquiv_eq_algebraTensorAlgEquiv n x
    simpa [x] using hx.symm

end MvPolynomial
