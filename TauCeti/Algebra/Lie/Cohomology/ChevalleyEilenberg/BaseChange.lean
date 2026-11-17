/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.Basic
public import TauCeti.LinearAlgebra.Alternating.BaseChange

/-!
# Base change for the Chevalley–Eilenberg complex

For a commutative `R`-algebra `A`, a Lie algebra `L` over `R`, and an `L`-module `M`, this file
establishes compatibility of the Chevalley–Eilenberg cochain complex with extension of scalars
`A ⊗[R] -`.

At the level of cochains, `AlternatingMap.baseChange` extends an `n`-cochain
`ω : L [⋀^Fin n]→ₗ[R] M` to `(A ⊗[R] L) [⋀^Fin n]→ₗ[A] (A ⊗[R] M)`. It commutes with the Lie
derivative (`lie_baseChange`) and, by induction via Cartan's formula, with the
Chevalley–Eilenberg differential (`d_baseChange`). These maps assemble into a morphism of
cochain complexes
`cochainComplexBaseChange : (A ⊗_R C^•(L, M)) ⟶ C^•(A ⊗_R L, A ⊗_R M)`
without any finiteness, projectivity, or flatness hypotheses.

When `L` is finitely generated and projective over `R`, `AlternatingMap.baseChangeEquiv` shows that
this morphism is an isomorphism of cochain complexes (`cochainComplexBaseChangeIso`). When in
addition `A` is flat over `R` (for instance, any field extension `E'/E`), extension of scalars
preserves homology, yielding the flat base-change isomorphism in every cohomology degree:
`A ⊗[R] H^n(L, M) ≃ₗ[A] H^n(A ⊗[R] L, A ⊗[R] M)` (`cohomologyBaseChangeEquiv`).

## Main definitions

* `TauCeti.LieModule.Cohomology.cochainComplexBaseChange`: the comparison morphism of cochain
  complexes `(extendScalars (algebraMap R A)).mapHomologicalComplex _ (cochainComplex R L M) ⟶
  cochainComplex A (A ⊗[R] L) (A ⊗[R] M)`.
* `TauCeti.LieModule.Cohomology.cochainComplexBaseChangeIso`: the comparison isomorphism of
  cochain complexes when `L` is finitely generated and projective over `R`.
* `TauCeti.LieModule.Cohomology.cohomologyBaseChangeIso` / `cohomologyBaseChangeEquiv`: the
  universal-coefficient base-change isomorphism in cohomology when `L` is finitely generated and
  projective and `A` is flat over `R`.

## Main results

* `TauCeti.LieModule.Cohomology.lie_baseChange`: `⁅a ⊗ x, ω_A⁆ = a • ⁅x, ω⁆_A`.
* `TauCeti.LieModule.Cohomology.d_baseChange`: `d (ω_A) = (d ω)_A`.
* `TauCeti.LieModule.Cohomology.d_comp_baseChangeHom`: compatibility of `d` with
  `AlternatingMap.baseChangeHom`.
-/

public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace TauCeti.LieModule.Cohomology

section Cochains

variable {R A L M : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The Lie derivative on extended cochains satisfies `⁅a ⊗ x, ω_A⁆ = a • ⁅x, ω⁆_A`. -/
@[simp]
theorem lie_baseChange {n : ℕ} (a : A) (x : L) (ω : L [⋀^Fin n]→ₗ[R] M) :
    ⁅a ⊗ₜ[R] x, ω.baseChange A⁆ = a • (⁅x, ω⁆.baseChange A) := by
  refine AlternatingMap.ext_tmul (R := R) fun v ↦ ?_
  rw [AlternatingMap.lie_apply, AlternatingMap.baseChange_apply_one_tmul,
    LieAlgebra.ExtendScalars.bracket_tmul, mul_one, smul_apply,
    AlternatingMap.baseChange_apply_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    AlternatingMap.lie_apply, TensorProduct.tmul_sub, TensorProduct.tmul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hupd :
      Function.update (fun j : Fin n ↦ (1 : A) ⊗ₜ[R] v j) i
          ⁅a ⊗ₜ[R] x, (1 : A) ⊗ₜ[R] v i⁆ =
        fun j : Fin n ↦
          (Function.update (fun _ : Fin n ↦ (1 : A)) i a j) ⊗ₜ[R]
            (Function.update v i ⁅x, v i⁆ j) := by
    ext j
    by_cases hij : j = i
    · subst hij
      simp [LieAlgebra.ExtendScalars.bracket_tmul]
    · simp [hij]
  rw [hupd, AlternatingMap.baseChange_apply_tmul]
  have hprod : (∏ j : Fin n, Function.update (fun _ : Fin n ↦ (1 : A)) i a j) = a := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hprod]

/-- The Chevalley–Eilenberg differential commutes with scalar extension of alternating maps. -/
@[simp]
theorem d_baseChange (n : ℕ) (ω : L [⋀^Fin n]→ₗ[R] M) :
    d A (A ⊗[R] L) (A ⊗[R] M) n (ω.baseChange A) = (d R L M n ω).baseChange A := by
  induction n with
  | zero =>
    refine AlternatingMap.curryLeft_injective (TensorProduct.AlgebraTensorModule.ext fun a x ↦ ?_)
    change (d A (A ⊗[R] L) (A ⊗[R] M) 0 (ω.baseChange A)).curryLeft (a ⊗ₜ[R] x) =
      ((d R L M 0 ω).baseChange A).curryLeft (a ⊗ₜ[R] x)
    rw [curryLeft_d_zero, lie_baseChange, AlternatingMap.curryLeft_baseChange, curryLeft_d_zero]
  | succ n ih =>
    refine AlternatingMap.curryLeft_injective (TensorProduct.AlgebraTensorModule.ext fun a x ↦ ?_)
    change (d A (A ⊗[R] L) (A ⊗[R] M) (n + 1) (ω.baseChange A)).curryLeft (a ⊗ₜ[R] x) =
      ((d R L M (n + 1) ω).baseChange A).curryLeft (a ⊗ₜ[R] x)
    rw [curryLeft_d_succ, lie_baseChange, AlternatingMap.curryLeft_baseChange,
      LinearMap.map_smul, ih, AlternatingMap.curryLeft_baseChange, curryLeft_d_succ,
      AlternatingMap.baseChange_sub]
    ext v
    simp [smul_sub]

variable (R A L M)

/-- Compatibility of the Chevalley–Eilenberg differential with `AlternatingMap.baseChangeHom`. -/
theorem d_comp_baseChangeHom (n : ℕ) :
    (d A (A ⊗[R] L) (A ⊗[R] M) n).comp (AlternatingMap.baseChangeHom R A L M n) =
      (AlternatingMap.baseChangeHom R A L M (n + 1)).comp ((d R L M n).baseChange A) := by
  refine TensorProduct.AlgebraTensorModule.ext fun a ω ↦ ?_
  simp [d_baseChange]

end Cochains

section Complex

universe u₁ u₂ u₃ u₄

variable (R : Type u₁) (A : Type u₂) (L : Type u₃) (M : Type u₄)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The degree-`n` component of the base-change morphism of Chevalley–Eilenberg cochain complexes.
-/
noncomputable def cochainComplexBaseChangeComponent (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)) ⟶
      ModuleCat.of A ((A ⊗[R] L) [⋀^Fin n]→ₗ[A] (A ⊗[R] M)) :=
  (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M))).hom ≫
    ModuleCat.ofHom (AlternatingMap.baseChangeHom R A L M n)

private theorem cochainComplexBaseChangeComponent_comm (i : ℕ) :
    cochainComplexBaseChangeComponent R A L M i ≫
        ModuleCat.ofHom (d A (A ⊗[R] L) (A ⊗[R] M) i) =
      (ModuleCat.extendScalars (algebraMap R A)).map (ModuleCat.ofHom (d R L M i)) ≫
        cochainComplexBaseChangeComponent R A L M (i + 1) := by
  unfold cochainComplexBaseChangeComponent
  rw [← cancel_epi
    (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin i]→ₗ[R] M))).inv]
  apply ModuleCat.hom_ext
  refine TensorProduct.AlgebraTensorModule.ext fun a ω ↦ ?_
  change
    d A (A ⊗[R] L) (A ⊗[R] M) i
        (AlternatingMap.baseChangeHom R A L M i
          ((ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin i]→ₗ[R] M))).hom
            ((ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin i]→ₗ[R] M))).inv
              (a ⊗ₜ[R] ω)))) =
      AlternatingMap.baseChangeHom R A L M (i + 1)
        ((ModuleCat.extendScalarsAlgebraMapIso
            (ModuleCat.of R (L [⋀^Fin (i + 1)]→ₗ[R] M))).hom
          (((ModuleCat.extendScalars (algebraMap R A)).map (ModuleCat.ofHom (d R L M i)))
            ((ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin i]→ₗ[R] M))).inv
              (a ⊗ₜ[R] ω))))
  rw [ModuleCat.extendScalarsAlgebraMapIso_inv_tmul,
    ModuleCat.extendScalarsAlgebraMapIso_hom_tmul]
  change d A (A ⊗[R] L) (A ⊗[R] M) i (AlternatingMap.baseChangeHom R A L M i (a ⊗ₜ[R] ω)) =
    AlternatingMap.baseChangeHom R A L M (i + 1)
      ((ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin (i + 1)]→ₗ[R] M))).hom
        (a ⊗ₜ[R, algebraMap R A] (d R L M i ω : L [⋀^Fin (i + 1)]→ₗ[R] M)))
  have hhom :
      (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin (i + 1)]→ₗ[R] M))).hom
          (a ⊗ₜ[R, algebraMap R A] (d R L M i ω : L [⋀^Fin (i + 1)]→ₗ[R] M)) =
        a ⊗ₜ[R] (d R L M i ω) :=
    ModuleCat.extendScalarsAlgebraMapIso_hom_tmul _ a _
  refine Eq.trans ?_ (congrArg (AlternatingMap.baseChangeHom R A L M (i + 1)) hhom.symm)
  simp

/-- The canonical base-change morphism of Chevalley–Eilenberg cochain complexes
`A ⊗_R C^•(L, M) ⟶ C^•(A ⊗_R L, A ⊗_R M)`. -/
noncomputable def cochainComplexBaseChange :
    ((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex _).obj
        (cochainComplex R L M) ⟶
      cochainComplex A (A ⊗[R] L) (A ⊗[R] M) where
  f n := cochainComplexBaseChangeComponent R A L M n
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst hj
    change cochainComplexBaseChangeComponent R A L M i ≫
        (cochainComplex A (A ⊗[R] L) (A ⊗[R] M)).d i (i + 1) =
      (ModuleCat.extendScalars (algebraMap R A)).map ((cochainComplex R L M).d i (i + 1)) ≫
        cochainComplexBaseChangeComponent R A L M (i + 1)
    rw [cochainComplex_d_succ, cochainComplex_d_succ]
    exact cochainComplexBaseChangeComponent_comm R A L M i

@[simp]
theorem cochainComplexBaseChange_f (n : ℕ) :
    (cochainComplexBaseChange R A L M).f n =
      cochainComplexBaseChangeComponent R A L M n := (rfl)

private instance isIso_cochainComplexBaseChangeComponent [Module.Finite R L]
    [Module.Projective R L] (n : ℕ) :
    IsIso (cochainComplexBaseChangeComponent R A L M n) := by
  let e := AlternatingMap.baseChangeEquiv R A L M n
  let iso := ModuleCat.extendScalarsAlgebraMapIso (S := A) (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M))
  let invM : ModuleCat.of A ((A ⊗[R] L) [⋀^Fin n]→ₗ[A] (A ⊗[R] M)) ⟶
      (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)) :=
    ModuleCat.ofHom e.symm.toLinearMap ≫ iso.inv
  refine ⟨⟨invM, ?_, ?_⟩⟩
  · rw [← cancel_epi iso.inv]
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x ↦ ?_
    change iso.inv (e.symm (AlternatingMap.baseChangeHom R A L M n
        (iso.hom (iso.inv x)))) = iso.inv x
    have hinv : iso.hom (iso.inv x) = x := congrArg (fun f ↦ f x) iso.inv_hom_id
    rw [hinv, ← AlternatingMap.baseChangeEquiv_toLinearMap]
    exact congrArg (fun y ↦ iso.inv y) (e.symm_apply_apply x)
  · apply ModuleCat.hom_ext
    refine LinearMap.ext fun x ↦ ?_
    change AlternatingMap.baseChangeHom R A L M n (iso.hom (iso.inv (e.symm x))) = x
    have hinv : iso.hom (iso.inv (e.symm x)) = e.symm x :=
      congrArg (fun f ↦ f (e.symm x)) iso.inv_hom_id
    rw [hinv, ← AlternatingMap.baseChangeEquiv_toLinearMap]
    exact e.apply_symm_apply x

/-- When `L` is finitely generated and projective over `R`, each degree component of
`cochainComplexBaseChange` is an isomorphism. -/
instance isIso_cochainComplexBaseChange_f [Module.Finite R L] [Module.Projective R L] (n : ℕ) :
    IsIso ((cochainComplexBaseChange R A L M).f n) :=
  isIso_cochainComplexBaseChangeComponent R A L M n

/-- **Base change for the Chevalley–Eilenberg cochain complex.** When `L` is finitely generated
and projective over `R`, `A ⊗_R C^•(L, M) ≅ C^•(A ⊗_R L, A ⊗_R M)` as cochain complexes of
`A`-modules. -/
noncomputable def cochainComplexBaseChangeIso [Module.Finite R L] [Module.Projective R L] :
    ((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex _).obj
        (cochainComplex R L M) ≅
      cochainComplex A (A ⊗[R] L) (A ⊗[R] M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso ((cochainComplexBaseChange R A L M).f n))
    (fun i j hij ↦ (cochainComplexBaseChange R A L M).comm' i j hij)

@[simp]
theorem cochainComplexBaseChangeIso_hom [Module.Finite R L] [Module.Projective R L] :
    (cochainComplexBaseChangeIso R A L M).hom = cochainComplexBaseChange R A L M := by
  ext n
  rfl

end Complex

section FlatCohomology

-- Mathlib's `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` relates rings and modules in
-- a single universe.
universe u

variable (R A L M : Type u)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **Flat base change for Chevalley–Eilenberg cohomology.** When `L` is finitely generated and
projective over `R` and `A` is flat over `R`, extension of scalars commutes with Lie algebra
cohomology in every degree:
`extendScalars (H^n(L, M)) ≅ H^n(A ⊗_R L, A ⊗_R M)`. -/
noncomputable def cohomologyBaseChangeIso [Module.Finite R L] [Module.Projective R L]
    [Module.Flat R A] (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R A)).obj (cohomology R L M n) ≅
      cohomology A (A ⊗[R] L) (A ⊗[R] M) n := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R A)
  have hf : (algebraMap R A).Flat := RingHom.flat_algebraMap_iff.mpr ‹Module.Flat R A›
  have _ : Limits.PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have _ : F.PreservesHomology := inferInstance
  exact (((cochainComplex R L M).sc n).mapHomologyIso F).symm.trans
    (HomologicalComplex.homologyMapIso (cochainComplexBaseChangeIso R A L M) n)

/-- **Flat base change for Chevalley–Eilenberg cohomology as an `A`-linear equivalence.** When `L`
is finitely generated and projective over `R` and `A` is flat over `R`,
`A ⊗[R] H^n(L, M) ≃ₗ[A] H^n(A ⊗[R] L, A ⊗[R] M)`. -/
noncomputable def cohomologyBaseChangeEquiv [Module.Finite R L] [Module.Projective R L]
    [Module.Flat R A] (n : ℕ) :
    A ⊗[R] cohomology R L M n ≃ₗ[A] cohomology A (A ⊗[R] L) (A ⊗[R] M) n :=
  ((ModuleCat.extendScalarsAlgebraMapIso (cohomology R L M n)).symm.trans
    (cohomologyBaseChangeIso R A L M n)).toLinearEquiv

end FlatCohomology

end TauCeti.LieModule.Cohomology
