/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Hom

/-!
# Scalar extension of alternating maps

For a commutative `R`-algebra `A` and `R`-modules `M` and `N`, an alternating map
`ω : M [⋀^Fin n]→ₗ[R] N` extends uniquely to an `A`-alternating map
`ω.baseChange A : (A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N)` evaluating on pure tensors by
`(a₀ ⊗ x₀, …, aₙ₋₁ ⊗ xₙ₋₁) ↦ (∏ i, aᵢ) ⊗ ω(x₀, …, xₙ₋₁)`.

The construction passes through the exterior power via `exteriorPower.alternatingMapLinearEquiv`
and `TauCeti.exteriorPower.equivBaseChange`, which requires no flatness, freeness, or
invertibility of factorials. When `M` is finitely generated and projective over `R`, its exterior
power `⋀[R]^n M` is again finitely generated and projective, so the comparison map
`A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) → ((A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N))` is an `A`-linear
equivalence (`AlternatingMap.baseChangeEquiv`).

## Main definitions

* `AlternatingMap.baseChange`: scalar extension of a single alternating map.
* `AlternatingMap.baseChangeHom`: the canonical `A`-linear comparison map
  `A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) →ₗ[A] ((A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N))`.
* `AlternatingMap.baseChangeEquiv`: the comparison as an `A`-linear equivalence when `M` is
  finitely generated and projective.

## Main results

* `AlternatingMap.ext_tmul`: an `A`-alternating map on `A ⊗[R] M` is determined by its values on
  tuples of pure tensors `i ↦ 1 ⊗ xᵢ`.
* `AlternatingMap.baseChange_apply_tmul`: evaluation of `ω.baseChange A` on pure tensors.
* `AlternatingMap.curryLeft_baseChange`: compatibility of scalar extension with interior product.
-/

public section

open scoped TensorProduct

namespace AlternatingMap

instance instIsScalarTower {R M N ι S T : Type*}
    [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Monoid S] [Monoid T] [DistribMulAction S N] [DistribMulAction T N]
    [SMulCommClass R S N] [SMulCommClass R T N] [SMul S T] [IsScalarTower S T N] :
    IsScalarTower S T (M [⋀^ι]→ₗ[R] N) :=
  FunLike.isScalarTower

variable {R : Type*} (A : Type*) {M N : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Two `A`-alternating maps out of `A ⊗[R] M` are equal if they agree on all tuples of pure
tensors `i ↦ 1 ⊗ xᵢ`. -/
theorem ext_tmul {A : Type*} [CommRing A] [Algebra R A] {P : Type*} [AddCommGroup P] [Module A P]
    {n : ℕ} {f g : (A ⊗[R] M) [⋀^Fin n]→ₗ[A] P}
    (h : ∀ v : Fin n → M, f (fun i ↦ (1 : A) ⊗ₜ[R] v i) = g (fun i ↦ (1 : A) ⊗ₜ[R] v i)) :
    f = g := by
  let _ : Module R P := Module.compHom P (algebraMap R A)
  have _ : IsScalarTower R A P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply exteriorPower.alternatingMapLinearEquiv.injective
  refine LinearMap.ext fun y ↦ ?_
  set e := TauCeti.exteriorPower.equivBaseChange (R := R) (M := M) A n
  obtain ⟨z, rfl⟩ := e.symm.surjective y
  suffices hcomp :
      (exteriorPower.alternatingMapLinearEquiv f).comp e.symm.toLinearMap =
      (exteriorPower.alternatingMapLinearEquiv g).comp e.symm.toLinearMap from
    LinearMap.congr_fun hcomp z
  refine TensorProduct.AlgebraTensorModule.ext fun a x ↦ ?_
  suffices hmk :
      (((exteriorPower.alternatingMapLinearEquiv f).comp e.symm.toLinearMap).restrictScalars R).comp
        (TensorProduct.mk R A (⋀[R]^n M) a) =
      (((exteriorPower.alternatingMapLinearEquiv g).comp e.symm.toLinearMap).restrictScalars R).comp
        (TensorProduct.mk R A (⋀[R]^n M) a) from
    LinearMap.congr_fun hmk x
  refine exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ ?_
  simp [e, TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti, h v]

/-- Scalar extension of an alternating map `ω : M [⋀^Fin n]→ₗ[R] N` to an `A`-alternating map
`(A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N)`. -/
noncomputable def baseChange {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) :
    (A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N) :=
  exteriorPower.alternatingMapLinearEquiv.symm
    (((exteriorPower.alternatingMapLinearEquiv ω).baseChange A).comp
      (TauCeti.exteriorPower.equivBaseChange A n).toLinearMap)

/-- Evaluating `ω.baseChange A` on a tuple of pure tensors multiplies the scalar coefficients and
tensors with the value of `ω`. -/
@[simp]
theorem baseChange_apply_tmul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) (a : Fin n → A) (v : Fin n → M) :
    ω.baseChange A (fun i ↦ a i ⊗ₜ[R] v i) = (∏ i, a i) ⊗ₜ[R] ω v := by
  simp [baseChange, exteriorPower.alternatingMapLinearEquiv_symm_apply]

/-- Evaluating `ω.baseChange A` on `i ↦ 1 ⊗ vᵢ` gives `1 ⊗ ω v`. -/
theorem baseChange_apply_one_tmul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) :
    ω.baseChange A (fun i ↦ (1 : A) ⊗ₜ[R] v i) = (1 : A) ⊗ₜ[R] ω v := by
  simp [baseChange_apply_tmul]

@[simp]
theorem baseChange_zero {n : ℕ} :
    (0 : M [⋀^Fin n]→ₗ[R] N).baseChange A = 0 := by
  refine ext_tmul (R := R) fun v ↦ ?_
  simp

@[simp]
theorem baseChange_add {n : ℕ} (ω₁ ω₂ : M [⋀^Fin n]→ₗ[R] N) :
    (ω₁ + ω₂).baseChange A = ω₁.baseChange A + ω₂.baseChange A := by
  refine ext_tmul (R := R) fun v ↦ ?_
  simp [TensorProduct.tmul_add]

@[simp]
theorem baseChange_smul {n : ℕ} (r : R) (ω : M [⋀^Fin n]→ₗ[R] N) :
    (r • ω).baseChange A = r • ω.baseChange A := by
  refine ext_tmul (R := R) fun v ↦ ?_
  simp [TensorProduct.tmul_smul]

@[simp]
theorem baseChange_neg {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) :
    (-ω).baseChange A = -(ω.baseChange A) := by
  refine ext_tmul (R := R) fun v ↦ ?_
  simp [TensorProduct.tmul_neg]

@[simp]
theorem baseChange_sub {n : ℕ} (ω₁ ω₂ : M [⋀^Fin n]→ₗ[R] N) :
    (ω₁ - ω₂).baseChange A = ω₁.baseChange A - ω₂.baseChange A := by
  refine ext_tmul (R := R) fun v ↦ ?_
  simp [TensorProduct.tmul_sub]

/-- Scalar extension commutes with interior product on pure tensors:
`ι_{a ⊗ x} (ω_A) = a • (ι_x ω)_A`. -/
theorem curryLeft_baseChange {n : ℕ} (ω : M [⋀^Fin (n + 1)]→ₗ[R] N) (a : A) (x : M) :
    (ω.baseChange A).curryLeft (a ⊗ₜ[R] x) = a • (ω.curryLeft x).baseChange A := by
  refine ext_tmul (R := R) fun v ↦ ?_
  have hcons :
      Matrix.vecCons (a ⊗ₜ[R] x) (fun i ↦ (1 : A) ⊗ₜ[R] v i) =
        fun i : Fin (n + 1) ↦ Matrix.vecCons a (fun _ ↦ (1 : A)) i ⊗ₜ[R] Matrix.vecCons x v i := by
    ext i
    refine Fin.cases rfl (fun j ↦ rfl) i
  rw [curryLeft_apply_apply, hcons, baseChange_apply_tmul, Fin.prod_univ_succ]
  simp [TensorProduct.smul_tmul', curryLeft_apply_apply]

variable (R M N)

/-- The canonical `A`-linear comparison map
`A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) → ((A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N))`,
sending `a ⊗ ω` to `a • ω.baseChange A`. -/
noncomputable def baseChangeHom (n : ℕ) :
    A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) →ₗ[A] ((A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N)) :=
  LinearMap.liftBaseChange A
    { toFun := fun ω ↦ ω.baseChange A
      map_add' := baseChange_add A
      map_smul' := fun r ω ↦ by
        rw [RingHom.id_apply, baseChange_smul] }

/-- On pure tensors, `baseChangeHom` sends `a ⊗ ω` to `a • ω.baseChange A`. -/
@[simp]
theorem baseChangeHom_tmul (n : ℕ) (a : A) (ω : M [⋀^Fin n]→ₗ[R] N) :
    baseChangeHom R A M N n (a ⊗ₜ[R] ω) = a • ω.baseChange A := by
  simp [baseChangeHom]

/-- Evaluating `baseChangeHom (a ⊗ ω)` on a tuple of pure tensors. -/
theorem baseChangeHom_tmul_apply (n : ℕ) (a : A) (ω : M [⋀^Fin n]→ₗ[R] N)
    (b : Fin n → A) (v : Fin n → M) :
    baseChangeHom R A M N n (a ⊗ₜ[R] ω) (fun i ↦ b i ⊗ₜ[R] v i) =
      (a * ∏ i, b i) ⊗ₜ[R] ω v := by
  simp [TensorProduct.smul_tmul']

/-- **Scalar extension of alternating maps out of a finite projective module.** When `M` is
finitely generated and projective over `R`, the canonical comparison map
`A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) → ((A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N))` is an `A`-linear
equivalence. -/
noncomputable def baseChangeEquiv (n : ℕ) [Module.Finite R M] [Module.Projective R M] :
    A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[A] ((A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N)) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := N) (n := n)) ≪≫ₗ
    (LinearMap.isBaseChange_baseChangeHom R A (⋀[R]^n M) N).equiv ≪≫ₗ
    LinearEquiv.arrowCongr (TauCeti.exteriorPower.equivBaseChange A n).symm
      (LinearEquiv.refl A (A ⊗[R] N)) ≪≫ₗ
    (exteriorPower.alternatingMapLinearEquiv (R := A) (M := A ⊗[R] M) (N := A ⊗[R] N)
      (n := n)).symm

/-- The underlying linear map of `baseChangeEquiv` is `baseChangeHom`. -/
@[simp]
theorem baseChangeEquiv_toLinearMap (n : ℕ) [Module.Finite R M] [Module.Projective R M] :
    (baseChangeEquiv R A M N n).toLinearMap = baseChangeHom R A M N n := by
  refine TensorProduct.AlgebraTensorModule.ext fun a ω ↦ ?_
  refine ext_tmul (R := R) fun v ↦ ?_
  simp [baseChangeEquiv, IsBaseChange.equiv_tmul, LinearMap.baseChangeHom,
    exteriorPower.alternatingMapLinearEquiv_symm_apply, TensorProduct.smul_tmul']

/-- Evaluating `baseChangeEquiv` on a pure tensor. -/
@[simp]
theorem baseChangeEquiv_tmul (n : ℕ) [Module.Finite R M] [Module.Projective R M]
    (a : A) (ω : M [⋀^Fin n]→ₗ[R] N) :
    baseChangeEquiv R A M N n (a ⊗ₜ[R] ω) = a • ω.baseChange A := by
  rw [← LinearEquiv.coe_toLinearMap, baseChangeEquiv_toLinearMap, baseChangeHom_tmul]

end AlternatingMap
