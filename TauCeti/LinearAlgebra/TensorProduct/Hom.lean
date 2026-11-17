/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Projective
import Mathlib.RingTheory.Finiteness.Projective
import TauCeti.LinearAlgebra.LinearMap.Comp
import TauCeti.LinearAlgebra.TensorProduct.Tower
import TauCeti.Logic.Function.Basic

/-!
# Scalar extension of linear-map spaces

For a finite projective source module, extending the scalars of the space of linear maps is the
same as taking linear maps between the scalar-extended modules: if `P` and `Q` are base changes
of `M` and `N` to `S`, then `P →ₗ[S] Q` is the base change of `M →ₗ[R] N`
(`IsBaseChange.linearMapLeftRight_of_projective`). Mathlib proves this for a finite free source
(`IsBaseChange.linearMapLeftRight`); a finite projective module is a retract of a finite free one,
and the comparison map is natural in the source, so the free case passes to retracts.

Similarly, for a finitely presented source module and a flat algebra `S`, `P →ₗ[S] Q` is the base
change of `M →ₗ[R] N` (`IsBaseChange.linearMapLeftRight_of_flat`), transporting Mathlib's
`Module.FinitePresentation.isBaseChange_map` along the base-change equivalences for `M` and `N`.

Combining both stages along a tower `R → S → T` where `S` is flat over `R` and the base-changed
modules over `S` are finite projective yields `IsBaseChange.linearMapLeftRight_of_flat_projective`,
together with the natural dual-evaluation isomorphism
`(P' →ₗ[T] Q') ≃ₗ[T] (Module.Dual R (M →ₗ[R] N) →ₗ[R] T)`
(`IsBaseChange.bijective_homDualEval_of_flat_projective`, `IsBaseChange.homDualEval_natural`) and
the associated coordinate embedding from a finite presentation of `Module.Dual R (M →ₗ[R] N)`
(`IsBaseChange.homCoords`, `IsBaseChange.homCoords_exact`).

This file also records compatibility of `IsBaseChange.linearMapLeftRightHom` with iterated base
change (`IsBaseChange.linearMapLeftRightHom_comp_comp`) and identifies Mathlib's
`LinearMap.baseChangeHom` as the scalar-extension map, so `IsBaseChange.equiv` supplies the
comparison equivalence and `IsBaseChange.equiv_tmul` evaluates it on pure tensors.
-/

public section

open TensorProduct

namespace IsBaseChange

variable {R S M N P Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]
  [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]

/-- **Linear maps out of a finite projective module commute with base change.** If `α : M → P`
and `β : N → Q` exhibit `P` and `Q` as the base changes of `M` and `N` to `S`, and `M` is finite
projective, then `P →ₗ[S] Q` is the base change of `M →ₗ[R] N`, through the map sending `g` to the
unique `S`-linear map `P → Q` extending `β ∘ g`. -/
theorem linearMapLeftRight_of_projective [Module.Finite R M] [Module.Projective R M]
    {α : M →ₗ[R] P} (j : IsBaseChange S α) {β : N →ₗ[R] Q} (k : IsBaseChange S β) :
    IsBaseChange S (linearMapLeftRightHom j β) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  set F := Fin n → R
  have jF := TensorProduct.isBaseChange R F S
  -- `M` is a retract of the free module `F`, and `P` of its base change `S ⊗[R] F`.
  let pS : S ⊗[R] F →ₗ[S] P := LinearMap.liftBaseChange S (α ∘ₗ p)
  let iS : P →ₗ[S] S ⊗[R] F := j.lift (TensorProduct.mk R S F 1 ∘ₗ i)
  have hpiS (x : P) : pS (iS x) = x := by
    induction x using j.inductionOn with
    | tmul m => simp [pS, iS, j.lift_eq, ← LinearMap.comp_apply p i, hpi]
    | smul s x h => simp [h]
    | add x y hx hy => simp [hx, hy]
  -- The comparison maps for `M` and for `F`; the second is bijective since `F` is free.
  let ΦM := LinearMap.liftBaseChange S (linearMapLeftRightHom j β)
  let ΦF := LinearMap.liftBaseChange S (linearMapLeftRightHom jF β)
  have hΦF : Function.Bijective ΦF := by
    convert (jF.linearMapLeftRight k).equiv.bijective using 1
    exact congr_arg DFunLike.coe (AlgebraTensorModule.ext fun s y ↦ by simp [ΦF])
  -- The comparison maps commute with composition with the retraction and the section.
  have hp (x : M →ₗ[R] N) : linearMapLeftRightHom jF β (x ∘ₗ p) =
      linearMapLeftRightHom j β x ∘ₗ pS := by
    refine jF.algHom_ext _ _ fun v ↦ ?_
    rw [linearMapLeftRightHom_comp_apply]
    simp [pS]
  have hi (y : F →ₗ[R] N) : linearMapLeftRightHom j β (y ∘ₗ i) =
      linearMapLeftRightHom jF β y ∘ₗ iS := by
    refine j.algHom_ext _ _ fun m ↦ ?_
    simp [iS, j.lift_eq, -mk_apply]
  have ha (z : S ⊗[R] (M →ₗ[R] N)) :
      ΦF ((LinearMap.lcomp R N p).baseChange S z) = ΦM z ∘ₗ pS := by
    induction z with
    | tmul s x => simp [ΦF, ΦM, ← hp, LinearMap.smul_comp, LinearMap.lcomp_apply']
    | add x y hx hy => simp [hx, hy, LinearMap.add_comp]
  have hb (z : S ⊗[R] (F →ₗ[R] N)) :
      ΦM ((LinearMap.lcomp R N i).baseChange S z) = ΦF z ∘ₗ iS := by
    induction z with
    | tmul s y => simp [ΦF, ΦM, ← hi, LinearMap.smul_comp, LinearMap.lcomp_apply']
    | add x y hx hy => simp [hx, hy, LinearMap.add_comp]
  have hd (g : P →ₗ[S] Q) : (g ∘ₗ pS) ∘ₗ iS = g := by
    ext x
    simp [hpiS]
  -- Hence `ΦM` is a retract of the bijection `ΦF`, so it is bijective.
  exact of_equiv (LinearEquiv.ofBijective ΦM (Function.bijective_of_retract (a := fun z ↦
    (LinearMap.lcomp R N p).baseChange S z) (b := (· ∘ₗ pS)) (d := (· ∘ₗ iS)) hΦF ha hb
    (LinearMap.baseChange_leftInverse (LinearMap.lcomp_comp_lcomp_eq_id hpi)) hd)) fun x ↦
    (LinearMap.liftBaseChange_tmul _ _ _ _).trans (one_smul S _)

/-- **Linear maps out of a finitely presented module commute with flat base change.** If `α : M → P`
and `β : N → Q` exhibit `P` and `Q` as the base changes of `M` and `N` to a flat `R`-algebra `S`,
and `M` is finitely presented over `R`, then `P →ₗ[S] Q` is the base change of `M →ₗ[R] N`. -/
theorem linearMapLeftRight_of_flat {R S M N P Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    {α : M →ₗ[R] P} (j : IsBaseChange S α) {β : N →ₗ[R] Q} (k : IsBaseChange S β) :
    IsBaseChange S (linearMapLeftRightHom j β) := by
  have hbc := Module.FinitePresentation.isBaseChange_map R M N S
  refine of_equiv (hbc.equiv ≪≫ₗ LinearEquiv.arrowCongr j.equiv k.equiv) fun f ↦ ?_
  refine j.algHom_ext _ _ fun m ↦ ?_
  simp [hbc.equiv_tmul]

/-- Extending linear maps in two stages along a tower `R → S → T` agrees with extending them in one
stage along `R → T`. -/
theorem linearMapLeftRightHom_comp_comp {T P' Q' : Type*} [CommSemiring T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommMonoid P'] [Module R P'] [Module S P'] [Module T P']
    [IsScalarTower R S P'] [IsScalarTower S T P'] [IsScalarTower R T P']
    [AddCommMonoid Q'] [Module R Q'] [Module S Q'] [Module T Q']
    [IsScalarTower R S Q'] [IsScalarTower S T Q'] [IsScalarTower R T Q']
    {α₁ : M →ₗ[R] P} (j₁ : IsBaseChange S α₁) {α₂ : P →ₗ[S] P'} (j₂ : IsBaseChange T α₂)
    (β₁ : N →ₗ[R] Q) (β₂ : Q →ₗ[S] Q') :
    (linearMapLeftRightHom j₂ β₂).restrictScalars R ∘ₗ linearMapLeftRightHom j₁ β₁ =
      linearMapLeftRightHom (j₁.comp j₂) (β₂.restrictScalars R ∘ₗ β₁) := by
  refine LinearMap.ext fun f ↦ (j₁.comp j₂).algHom_ext _ _ fun m ↦ ?_
  rw [linearMapLeftRightHom_comp_apply (j₁.comp j₂)]
  simp

section DualEval

variable {A T C B C_T B_T : Type*} [CommRing A] [CommRing T] [Algebra A T]
  [AddCommGroup C] [Module A C] [AddCommGroup B] [Module A B]
  [AddCommGroup C_T] [Module A C_T] [Module T C_T] [IsScalarTower A T C_T]
  [AddCommGroup B_T] [Module A B_T] [Module T B_T] [IsScalarTower A T B_T]

/-- Evaluation of an `A`-module `E` into `Hom_A(Dual A E, T)`, sending `ψ` to
`ℓ ↦ algebraMap A T (ℓ ψ)`. -/
private def evalToDualHom (A T E : Type*) [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup E] [Module A E] :
    E →ₗ[A] (Module.Dual A E →ₗ[A] T) where
  toFun ψ := (Algebra.linearMap A T).comp (Module.Dual.eval A E ψ)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp [Algebra.smul_def]

/-- The canonical `T`-linear evaluation map `(C_T →ₗ[T] B_T) →ₗ[T] (Dual A (C →ₗ[A] B) →ₗ[A] T)`
when `C_T →ₗ[T] B_T` is the base change of `C →ₗ[A] B`. -/
noncomputable def homDualEval {c_T : C →ₗ[A] C_T} (hcT : IsBaseChange T c_T) (b_T : B →ₗ[A] B_T)
    (heT : IsBaseChange T (linearMapLeftRightHom hcT b_T)) :
    (C_T →ₗ[T] B_T) →ₗ[T] (Module.Dual A (C →ₗ[A] B) →ₗ[A] T) :=
  heT.lift (evalToDualHom A T (C →ₗ[A] B))

/-- On a base-changed linear map `ψ`, `homDualEval` evaluates `ℓ` at `ψ` and maps to `T`. -/
@[simp]
theorem homDualEval_baseChange {c_T : C →ₗ[A] C_T} (hcT : IsBaseChange T c_T) (b_T : B →ₗ[A] B_T)
    (heT : IsBaseChange T (linearMapLeftRightHom hcT b_T))
    (ψ : C →ₗ[A] B) (ℓ : Module.Dual A (C →ₗ[A] B)) :
    homDualEval hcT b_T heT (linearMapLeftRightHom hcT b_T ψ) ℓ = algebraMap A T (ℓ ψ) := by
  simp [homDualEval, evalToDualHom, heT.lift_eq]

section FlatProjective

variable {Q C_Q B_Q : Type*} [CommRing Q]
  [Algebra A Q] [Algebra Q T] [IsScalarTower A Q T]
  [AddCommGroup C_Q] [Module A C_Q] [Module Q C_Q] [IsScalarTower A Q C_Q]
  [AddCommGroup B_Q] [Module A B_Q] [Module Q B_Q] [IsScalarTower A Q B_Q]
  [Module Q C_T] [IsScalarTower A Q C_T] [IsScalarTower Q T C_T]
  [Module Q B_T] [IsScalarTower A Q B_T] [IsScalarTower Q T B_T]

/-- Along a tower `A → Q → T` with `Q` flat over `A`, `C` finitely presented over `A`, and `C_Q`
finite projective over `Q`, `C_T →ₗ[T] B_T` is the base change of `C →ₗ[A] B`. -/
theorem linearMapLeftRight_of_flat_projective [Module.Flat A Q] [Module.FinitePresentation A C]
    [Module.Finite Q C_Q] [Module.Projective Q C_Q]
    {c_Q : C →ₗ[A] C_Q} (hcQ : IsBaseChange Q c_Q)
    {b_Q : B →ₗ[A] B_Q} (hbQ : IsBaseChange Q b_Q)
    {c_QT : C_Q →ₗ[Q] C_T} (hcQT : IsBaseChange T c_QT)
    {b_QT : B_Q →ₗ[Q] B_T} (hbQT : IsBaseChange T b_QT) :
    IsBaseChange T
      (linearMapLeftRightHom (hcQ.comp hcQT) (b_QT.restrictScalars A ∘ₗ b_Q)) := by
  have heQ := hcQ.linearMapLeftRight_of_flat hbQ
  have heQT := hcQT.linearMapLeftRight_of_projective hbQT
  have hcomp := heQ.comp heQT
  rwa [linearMapLeftRightHom_comp_comp] at hcomp

/-- When `C_T` and `B_T` factor through finite projective modules over a flat `A`-algebra `Q`,
`homDualEval` is bijective, identifying `C_T →ₗ[T] B_T` with `Module.Dual A (C →ₗ[A] B) →ₗ[A] T`. -/
theorem bijective_homDualEval_of_flat_projective [Module.Flat A Q]
    [Module.FinitePresentation A C] [Module.FinitePresentation A (C →ₗ[A] B)]
    [Module.Finite Q C_Q] [Module.Projective Q C_Q]
    [Module.Finite Q B_Q] [Module.Projective Q B_Q]
    {c_Q : C →ₗ[A] C_Q} (hcQ : IsBaseChange Q c_Q)
    {b_Q : B →ₗ[A] B_Q} (hbQ : IsBaseChange Q b_Q)
    {c_QT : C_Q →ₗ[Q] C_T} (hcQT : IsBaseChange T c_QT)
    {b_QT : B_Q →ₗ[Q] B_T} (hbQT : IsBaseChange T b_QT)
    (heT : IsBaseChange T
      (linearMapLeftRightHom (hcQ.comp hcQT) (b_QT.restrictScalars A ∘ₗ b_Q))) :
    Function.Bijective
      (homDualEval (hcQ.comp hcQT) (b_QT.restrictScalars A ∘ₗ b_Q) heT) := by
  let E := C →ₗ[A] B
  let E_Q := C_Q →ₗ[Q] B_Q
  let E_T := C_T →ₗ[T] B_T
  have : Module.Finite Q E_Q := Module.Finite.equiv (dualTensorHomEquiv Q C_Q B_Q)
  have : Module.Projective Q E_Q := Module.Projective.of_equiv (dualTensorHomEquiv Q C_Q B_Q)
  have heQ : IsBaseChange Q (linearMapLeftRightHom hcQ b_Q) :=
    hcQ.linearMapLeftRight_of_flat hbQ
  have heQT : IsBaseChange T (linearMapLeftRightHom hcQT b_QT) :=
    hcQT.linearMapLeftRight_of_projective hbQT
  have hAQ : IsBaseChange Q (Algebra.linearMap A Q) :=
    of_equiv (AlgebraTensorModule.rid A Q Q) fun a ↦ by
      simp [Algebra.algebraMap_eq_smul_one]
  let n_Q : Module.Dual A E →ₗ[A] Module.Dual Q E_Q :=
    linearMapLeftRightHom heQ (Algebra.linearMap A Q)
  have hnQ : IsBaseChange Q n_Q := heQ.linearMapLeftRight_of_flat hAQ
  let e₅ : (Module.Dual Q E_Q →ₗ[Q] T) ≃ₗ[Q] (Module.Dual A E →ₗ[A] T) :=
    { toFun := fun g ↦ g.restrictScalars A ∘ₗ n_Q
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp
      invFun := fun f ↦ hnQ.lift f
      left_inv := fun g ↦ hnQ.algHom_ext _ _ fun ℓ ↦ by simp [hnQ.lift_eq]
      right_inv := fun f ↦ by ext ℓ; simp [hnQ.lift_eq] }
  let Ψ : E_T ≃ₗ[Q] (Module.Dual A E →ₗ[A] T) :=
    heQT.equiv.symm.restrictScalars Q ≪≫ₗ TensorProduct.comm Q T E_Q ≪≫ₗ
      TensorProduct.congr (Module.evalEquiv Q E_Q) (.refl Q T) ≪≫ₗ
      dualTensorHomEquiv Q (Module.Dual Q E_Q) T ≪≫ₗ e₅
  have hkey (u : E_Q) (ℓ : Module.Dual A E) :
      algebraMap Q T (n_Q ℓ u) =
        homDualEval (hcQ.comp hcQT) (b_QT.restrictScalars A ∘ₗ b_Q) heT
          (linearMapLeftRightHom hcQT b_QT u) ℓ := by
    induction u using heQ.inductionOn with
    | tmul ψ =>
      have hcomp : linearMapLeftRightHom hcQT b_QT (linearMapLeftRightHom hcQ b_Q ψ) =
          linearMapLeftRightHom (hcQ.comp hcQT) (b_QT.restrictScalars A ∘ₗ b_Q) ψ := by
        simpa using LinearMap.congr_fun
          (linearMapLeftRightHom_comp_comp hcQ hcQT b_Q b_QT) ψ
      rw [hcomp, homDualEval_baseChange]
      simp [n_Q, ← IsScalarTower.algebraMap_apply A Q T]
    | smul q u hu =>
      rw [map_smul, smul_eq_mul, map_mul, hu, map_smul, ← algebraMap_smul T q, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
    | add u₁ u₂ h₁ h₂ =>
      simp [map_add, h₁, h₂]
  have hEq : (homDualEval (hcQ.comp hcQT) (b_QT.restrictScalars A ∘ₗ b_Q) heT : E_T → _) = Ψ := by
    funext x
    obtain ⟨z, rfl⟩ := heQT.equiv.surjective x
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => simp [map_add, h₁, h₂]
    | tmul t u =>
      ext ℓ
      simp only [Ψ, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
        LinearEquiv.symm_apply_apply, TensorProduct.comm_tmul, TensorProduct.congr_tmul,
        Module.evalEquiv_apply, LinearEquiv.refl_apply, dualTensorHomEquiv_tmul, e₅,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, Module.Dual.eval_apply, Algebra.smul_def]
      rw [heQT.equiv_tmul, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm, hkey]
  rw [hEq]
  exact Ψ.bijective

end FlatProjective

/-- Naturality of `homDualEval` along an `A`-algebra map `τ : T →ₐ[A] T'` and a compatible
semilinear map on targets `B_T → B_T'`. -/
theorem homDualEval_natural {T' C_T' B_T' : Type*} [CommRing T'] [Algebra A T']
    [AddCommGroup C_T'] [Module A C_T'] [Module T' C_T'] [IsScalarTower A T' C_T']
    [AddCommGroup B_T'] [Module A B_T'] [Module T' B_T'] [IsScalarTower A T' B_T']
    {c_T : C →ₗ[A] C_T} (hcT : IsBaseChange T c_T) (b_T : B →ₗ[A] B_T)
    (heT : IsBaseChange T (linearMapLeftRightHom hcT b_T))
    {c_T' : C →ₗ[A] C_T'} (hcT' : IsBaseChange T' c_T') (b_T' : B →ₗ[A] B_T')
    (heT' : IsBaseChange T' (linearMapLeftRightHom hcT' b_T'))
    (τ : T →ₐ[A] T') (tB : B_T → B_T')
    (htB_add : ∀ x y, tB (x + y) = tB x + tB y)
    (htB_smul : ∀ (t : T) (x : B_T), tB (t • x) = τ t • tB x)
    (htB_b : ∀ y : B, tB (b_T y) = b_T' y)
    (u : C_T →ₗ[T] B_T) :
    ∃ u' : C_T' →ₗ[T'] B_T',
      (∀ m : C, u' (c_T' m) = tB (u (c_T m))) ∧
      ∀ ℓ : Module.Dual A (C →ₗ[A] B),
        homDualEval hcT' b_T' heT' u' ℓ = τ (homDualEval hcT b_T heT u ℓ) := by
  let : Algebra T T' := τ.toRingHom.toAlgebra
  have : IsScalarTower A T T' := IsScalarTower.of_algebraMap_eq fun a ↦ (τ.commutes a).symm
  let : Module T (C_T' →ₗ[T'] B_T') := Module.compHom (C_T' →ₗ[T'] B_T') τ.toRingHom
  have : IsScalarTower A T (C_T' →ₗ[T'] B_T') :=
    { smul_assoc := fun a t v ↦ by
        ext x
        change τ (a • t) • v x = a • (τ t • v x)
        rw [Algebra.smul_def, map_mul, τ.commutes, mul_smul, algebraMap_smul] }
  let push : (C_T →ₗ[T] B_T) →ₗ[T] (C_T' →ₗ[T'] B_T') :=
    heT.lift (linearMapLeftRightHom hcT' b_T')
  refine ⟨push u, ?_, ?_⟩
  · intro m
    induction u using heT.inductionOn with
    | tmul ψ =>
      simp [push, heT.lift_eq, htB_b]
    | smul t u hu =>
      rw [map_smul]
      change (τ t • push u) (c_T' m) = tB ((t • u) (c_T m))
      simp [hu, htB_smul]
    | add u₁ u₂ h₁ h₂ =>
      simp [map_add, h₁, h₂, htB_add]
  · intro ℓ
    induction u using heT.inductionOn with
    | tmul ψ =>
      simp [push, heT.lift_eq, τ.commutes]
    | smul t u hu =>
      rw [map_smul]
      change homDualEval hcT' b_T' heT' (τ t • push u) ℓ =
        τ (homDualEval hcT b_T heT (t • u) ℓ)
      simp [hu, map_mul]
    | add u₁ u₂ h₁ h₂ =>
      simp [map_add, h₁, h₂]

/-- The coordinate map `(C_T →ₗ[T] B_T) →ₗ[T] (Fin r → T)` associated to a linear map
`π : (Fin r → A) →ₗ[A] Module.Dual A (C →ₗ[A] B)`. -/
noncomputable def homCoords {r : ℕ} (π : (Fin r → A) →ₗ[A] Module.Dual A (C →ₗ[A] B))
    {c_T : C →ₗ[A] C_T} (hcT : IsBaseChange T c_T) (b_T : B →ₗ[A] B_T)
    (heT : IsBaseChange T (linearMapLeftRightHom hcT b_T)) :
    (C_T →ₗ[T] B_T) →ₗ[T] (Fin r → T) where
  toFun u i := homDualEval hcT b_T heT u (π (Pi.single i 1))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The `i`-th coordinate of `u` under `homCoords π` is `homDualEval u (π (Pi.single i 1))`. -/
@[simp]
theorem homCoords_apply {r : ℕ} (π : (Fin r → A) →ₗ[A] Module.Dual A (C →ₗ[A] B))
    {c_T : C →ₗ[A] C_T} (hcT : IsBaseChange T c_T) (b_T : B →ₗ[A] B_T)
    (heT : IsBaseChange T (linearMapLeftRightHom hcT b_T))
    (u : C_T →ₗ[T] B_T) (i : Fin r) :
    homCoords π hcT b_T heT u i = homDualEval hcT b_T heT u (π (Pi.single i 1)) := by
  rfl

/-- Exactness of `homCoords`: when `homDualEval` is bijective and
`(Fin s → A) —φ→ (Fin r → A) —π→ Module.Dual A (C →ₗ[A] B) → 0` is exact, `homCoords` is
injective and its image consists of the vectors in `Fin r → T` satisfying the transposed linear
relations of `φ`. -/
theorem homCoords_exact {r s : ℕ} {π : (Fin r → A) →ₗ[A] Module.Dual A (C →ₗ[A] B)}
    {φ : (Fin s → A) →ₗ[A] (Fin r → A)}
    (hπ : Function.Surjective π) (hφπ : Function.Exact φ π)
    {c_T : C →ₗ[A] C_T} (hcT : IsBaseChange T c_T) (b_T : B →ₗ[A] B_T)
    (heT : IsBaseChange T (linearMapLeftRightHom hcT b_T))
    (hbij : Function.Bijective (homDualEval hcT b_T heT)) :
    Function.Injective (homCoords π hcT b_T heT) ∧
      ∀ v : Fin r → T,
        (∃ u, homCoords π hcT b_T heT u = v) ↔
          ∀ j : Fin s, ∑ i : Fin r, algebraMap A T (φ (Pi.single j 1) i) * v i = 0 := by
  let evalFin (n : ℕ) : ((Fin n → A) →ₗ[A] T) ≃ₗ[T] (Fin n → T) :=
    { toFun := fun f i ↦ f (Pi.single i 1)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun v ↦
        { toFun := fun w ↦ ∑ i : Fin n, algebraMap A T (w i) * v i
          map_add' := fun w₁ w₂ ↦ by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun a w ↦ by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            ring }
      left_inv := fun f ↦ by
        refine LinearMap.pi_ext' fun i ↦ LinearMap.ext fun a ↦ ?_
        have h1 : (Pi.single i a : Fin n → A) = a • Pi.single i (1 : A) := by
          ext k
          simp [Pi.single_apply]
        simp only [LinearMap.comp_apply, LinearMap.single_apply, LinearMap.coe_mk, AddHom.coe_mk,
          Pi.single_apply, apply_ite (algebraMap A T), map_zero, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [h1, map_smul, Algebra.smul_def]
      right_inv := fun v ↦ by
        ext i
        simp [Pi.single_apply] }
  have hinj : Function.Injective (homCoords π hcT b_T heT) := by
    have hfac : (homCoords π hcT b_T heT : (C_T →ₗ[T] B_T) → (Fin r → T)) =
        (evalFin r) ∘ (LinearMap.lcomp A T π) ∘ (homDualEval hcT b_T heT) := rfl
    rw [hfac]
    exact (evalFin r).injective.comp
      ((LinearMap.lcomp_injective_of_surjective π hπ).comp hbij.1)
  refine ⟨hinj, fun v ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨u, rfl⟩ j
    have hπφ : π (φ (Pi.single j 1)) = 0 := by
      have hmem : φ (Pi.single j 1) ∈ LinearMap.ker π := by
        rw [LinearMap.exact_iff.mp hφπ]
        exact LinearMap.mem_range_self φ (Pi.single j 1)
      exact hmem
    have hj : homDualEval hcT b_T heT u (π (φ (Pi.single j 1))) = 0 := by
      rw [hπφ, map_zero]
    have hdecomp : φ (Pi.single j 1) = ∑ i : Fin r, (φ (Pi.single j 1) i) • Pi.single i 1 := by
      ext k
      simp [Pi.single_apply]
    rw [hdecomp, map_sum, map_sum] at hj
    simp_rw [map_smul, Algebra.smul_def] at hj
    exact hj
  · intro hv
    let F : (Fin r → A) →ₗ[A] T := (evalFin r).symm v
    have hFφ : F ∘ₗ φ = 0 := by
      refine LinearMap.pi_ext' fun j ↦ LinearMap.ext fun a ↦ ?_
      have hFj : F (φ (Pi.single j 1)) = 0 := by
        simpa [F, evalFin] using hv j
      have ha : Pi.single j a = a • Pi.single j (1 : A) := by
        ext k
        simp [Pi.single_apply]
      simp [ha, hFj]
    have hker : F ∈ LinearMap.ker (LinearMap.lcomp A T φ) := hFφ
    have hex : Function.Exact (LinearMap.lcomp A T π) (LinearMap.lcomp A T φ) :=
      LinearMap.exact_lcomp_of_exact_of_surjective T hφπ hπ
    rw [LinearMap.exact_iff.mp hex] at hker
    obtain ⟨g, hg⟩ := hker
    obtain ⟨u, hu⟩ := hbij.2 g
    refine ⟨u, ?_⟩
    ext i
    have h1 : g (π (Pi.single i 1)) = v i := by
      change (evalFin r) (LinearMap.lcomp A T π g) i = v i
      rw [hg]
      exact congr_fun ((evalFin r).apply_symm_apply v) i
    simpa [hu] using h1

end DualEval

end IsBaseChange

namespace LinearMap

/-- Linear maps out of a finite projective module commute with scalar extension of both
modules. -/
theorem isBaseChange_baseChangeHom (R A M N : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    [AddCommMonoid N] [Module R N] :
    IsBaseChange A (baseChangeHom R A M N) := by
  convert! (TensorProduct.isBaseChange R M A).linearMapLeftRight_of_projective
    (TensorProduct.isBaseChange R N A) using 1
  ext f m
  exact (IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange R M A)
    ((TensorProduct.mk R A N) 1) f m).symm

end LinearMap
