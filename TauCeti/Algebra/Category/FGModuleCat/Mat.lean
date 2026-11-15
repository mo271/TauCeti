/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Linear.Mat

/-!
# The matrix category and finitely generated modules

For any ring `R : Type u`, right multiplication of row vectors by matrices defines a fully faithful
additive functor `CategoryTheory.Mat.toFGModuleCat R : Mat R ⥤ FGModuleCat.{u} R` sending a finite
index type `M` to the finite free left `R`-module `M → R` and a matrix `f : M ⟶ N` to
`Matrix.vecMulLinear f`. Because `(v ᵥ* f) ᵥ* g = v ᵥ* (f * g)` holds over an arbitrary ring
without transposing, no commutativity assumption on `R` is needed; when `R` is an algebra over a
commutative semiring `S`, the functor is `S`-linear.

Over a division ring `K`, every finite-dimensional left `K`-vector space admits a finite basis, so
`toFGModuleCat K` is essentially surjective and therefore an equivalence of categories
`CategoryTheory.Mat.fgModuleCatEquivalence K : Mat K ≌ FGModuleCat.{u} K`. Transferring the abelian
structure along this equivalence equips `Mat K` with `Abelian (Mat K)` while reusing its existing
`Preadditive (Mat K)` instance.

## Main definitions

* `CategoryTheory.Mat.toFGModuleCat`: the fully faithful additive functor
  `Mat R ⥤ FGModuleCat.{u} R` sending `M` to `M → R` and `f` to `Matrix.vecMulLinear f`.
* `CategoryTheory.Mat.toFGModuleCatFullyFaithful`: witness that `toFGModuleCat R` is fully faithful,
  with preimage given by `LinearMap.toMatrixRight'`.
* `CategoryTheory.Mat.toFGModuleCatUnitIso`: `(toFGModuleCat R).obj (unit R) ≅ FGModuleCat.of R R`.
* `CategoryTheory.Mat.fgModuleCatEquivalence`: the equivalence `Mat K ≌ FGModuleCat.{u} K` over a
  division ring `K`.
* `CategoryTheory.Mat.instAbelian`: the `Abelian (Mat K)` instance over a division ring `K`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Matrix

namespace CategoryTheory.Mat

universe u

section Ring

variable (R : Type u) [Ring R]

-- `@[expose]` is forced by dependent typing of concrete module morphisms: without
-- `(toFGModuleCat R).obj M` unfolding definitionally to `FGModuleCat.of R (M → R)`, evaluating
-- `((toFGModuleCat R).map f).hom.hom` on `v : M → R` would not typecheck without `eqToHom`.
/-- The fully faithful additive functor `Mat R ⥤ FGModuleCat.{u} R` sending a finite index type `M`
to the finite free left `R`-module `M → R` and a matrix `f : M ⟶ N` to right matrix multiplication
`Matrix.vecMulLinear f` on row vectors. -/
@[expose] noncomputable def toFGModuleCat : Mat R ⥤ FGModuleCat.{u} R where
  obj M := FGModuleCat.of R (M → R)
  map {M N} f :=
    let _ : Fintype M := @FintypeCat.fintype M
    FGModuleCat.ofHom (Matrix.vecMulLinear f)
  map_id M := by
    let _ : Fintype M := @FintypeCat.fintype M
    let _ : DecidableEq M := Classical.decEq M
    exact FGModuleCat.hom_ext (LinearMap.ext fun v ↦ Matrix.vecMul_one v)
  map_comp {M N P} f g := by
    let _ : Fintype M := @FintypeCat.fintype M
    let _ : Fintype N := @FintypeCat.fintype N
    exact FGModuleCat.hom_ext (LinearMap.ext fun v ↦ (Matrix.vecMul_vecMul v f g).symm)

/-- Object formula for `toFGModuleCat R`. Not `@[simp]` so `simp` does not rewrite the implicit
endpoints of `((toFGModuleCat R).map f).hom.hom` and `toFGModuleCatUnitIso`. -/
theorem toFGModuleCat_obj (M : Mat R) :
    (toFGModuleCat R).obj M = FGModuleCat.of R (M → R) :=
  rfl

@[simp]
theorem toFGModuleCat_map_apply {M N : Mat R} [Fintype M] (f : M ⟶ N) (v : M → R) :
    ((toFGModuleCat R).map f).hom.hom v = v ᵥ* f := by
  funext j
  simp only [toFGModuleCat, FGModuleCat.hom_hom_ofHom, Matrix.vecMul, dotProduct]
  exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun _ _ ↦ rfl

instance instAdditiveToFGModuleCat : (toFGModuleCat R).Additive where
  map_add {M N} f g := by
    let _ : Fintype M := @FintypeCat.fintype M
    exact FGModuleCat.hom_ext ((Matrix.vecMulBilin R Rᵐᵒᵖ).flip.map_add f g)

open scoped ModuleCat.Algebra in
instance instLinearToFGModuleCat (S : Type*) [CommSemiring S] [Algebra S R] :
    (toFGModuleCat R).Linear S where
  map_smul {M N} f s := by
    let _ : Fintype M := @FintypeCat.fintype M
    refine FGModuleCat.hom_ext (LinearMap.ext fun v ↦ funext fun j ↦ ?_)
    change (∑ i : M, v i * (s • f) i j) = algebraMap S R s * ∑ i : M, v i * f i j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_apply, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes, mul_assoc]

instance instLinearToFGModuleCatOverField (k : Type*) [Field k] [Algebra k R] :
    (toFGModuleCat R).Linear k where
  map_smul {M N} f c := by
    let _ : Fintype M := @FintypeCat.fintype M
    refine FGModuleCat.hom_ext (LinearMap.ext fun v ↦ funext fun j ↦ ?_)
    change (∑ i : M, v i * (c • f) i j) = algebraMap k R c * ∑ i : M, v i * f i j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_apply, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes, mul_assoc]

/-- `toFGModuleCat R` is fully faithful, with preimage given by `LinearMap.toMatrixRight'`. -/
noncomputable def toFGModuleCatFullyFaithful : (toFGModuleCat R).FullyFaithful where
  preimage {M N} φ :=
    let _ : Fintype M := @FintypeCat.fintype M
    let _ : DecidableEq M := Classical.decEq M
    LinearMap.toMatrixRight' φ.hom.hom
  map_preimage {M N} φ := by
    let _ : Fintype M := @FintypeCat.fintype M
    let _ : DecidableEq M := Classical.decEq M
    exact FGModuleCat.hom_ext (LinearMap.toMatrixRight'.left_inv φ.hom.hom)
  preimage_map {M N} f := by
    let _ : Fintype M := @FintypeCat.fintype M
    let _ : DecidableEq M := Classical.decEq M
    exact LinearMap.toMatrixRight'.right_inv f

instance instFullToFGModuleCat : (toFGModuleCat R).Full :=
  (toFGModuleCatFullyFaithful R).full

instance instFaithfulToFGModuleCat : (toFGModuleCat R).Faithful :=
  (toFGModuleCatFullyFaithful R).faithful

/-- `(toFGModuleCat R).obj (unit R)` identifies with the regular left `R`-module `R` by evaluation
at the unique index. -/
noncomputable def toFGModuleCatUnitIso :
    (toFGModuleCat R).obj (unit R) ≅ FGModuleCat.of R R :=
  (LinearEquiv.funUnique (unit R) R R).toFGModuleCatIso

@[simp]
theorem toFGModuleCatUnitIso_hom_apply (v : unit R → R) :
    (toFGModuleCatUnitIso R).hom.hom.hom v = v default :=
  (rfl)

@[simp]
theorem toFGModuleCatUnitIso_inv_apply (r : R) (i : unit R) :
    (toFGModuleCatUnitIso R).inv.hom.hom r i = r :=
  (rfl)

/-- Under `StrongRankCondition R`, the `R`-rank of `(toFGModuleCat R).obj M` is `Nat.card M`. -/
theorem finrank_toFGModuleCat_obj [StrongRankCondition R] (M : Mat R) :
    Module.finrank R ((toFGModuleCat R).obj M) = Nat.card M := by
  let _ : Fintype M := @FintypeCat.fintype M
  exact (Module.finrank_pi R).trans Nat.card_eq_fintype_card.symm

end Ring

section DivisionRing

variable (K : Type u) [DivisionRing K]

/-- Over a division ring `K`, every finite-dimensional `K`-vector space has a finite basis, so
`toFGModuleCat K` is essentially surjective. -/
instance instEssSurjToFGModuleCat : (toFGModuleCat K).EssSurj where
  mem_essImage V := by
    let ι : Type u := ULift.{u} (Fin (Module.finrank K V))
    let e : (ι → K) ≃ₗ[K] V :=
      ((Module.finBasis K V).equivFun.trans (LinearEquiv.funCongrLeft K K Equiv.ulift)).symm
    exact ⟨of K ι, ⟨e.toFGModuleCatIso⟩⟩

instance instIsEquivalenceToFGModuleCat : (toFGModuleCat K).IsEquivalence where

/-- Over a division ring `K`, `Mat K` is equivalent to `FGModuleCat.{u} K`. -/
noncomputable def fgModuleCatEquivalence : Mat K ≌ FGModuleCat.{u} K :=
  (toFGModuleCat K).asEquivalence

@[simp]
theorem fgModuleCatEquivalence_functor :
    (fgModuleCatEquivalence K).functor = toFGModuleCat K :=
  (rfl)

instance instAdditiveFGModuleCatEquivalenceFunctor :
    (fgModuleCatEquivalence K).functor.Additive := by
  rw [fgModuleCatEquivalence_functor]
  infer_instance

open scoped ModuleCat.Algebra in
instance instLinearFGModuleCatEquivalenceFunctor (S : Type*) [CommSemiring S] [Algebra S K] :
    (fgModuleCatEquivalence K).functor.Linear S := by
  rw [fgModuleCatEquivalence_functor]
  infer_instance

instance instLinearFGModuleCatEquivalenceFunctorOverField (k : Type*) [Field k] [Algebra k K] :
    (fgModuleCatEquivalence K).functor.Linear k := by
  rw [fgModuleCatEquivalence_functor]
  infer_instance

/-- Over a division ring `K`, `Mat K` is an abelian category via `toFGModuleCat K`, reusing the
existing `Preadditive (Mat K)` and `HasFiniteBiproducts (Mat K)` instances. -/
noncomputable instance instAbelian : Abelian (Mat K) :=
  abelianOfEquivalence (toFGModuleCat K)

end DivisionRing

end CategoryTheory.Mat
