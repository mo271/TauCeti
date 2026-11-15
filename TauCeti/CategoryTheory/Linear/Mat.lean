/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import TauCeti.CategoryTheory.Linear.Biproduct
public import TauCeti.CategoryTheory.Preadditive.Mat

/-!
# Linear structure and standard bases on matrix categories

Mathlib equips the additive envelope `Mat_ C` of a preadditive category `C`, whose objects are
finite families of objects of `C` and whose morphisms are matrices of morphisms of `C`, with its
preadditive structure only, and leaves `Mat R` unequipped with scalar multiplication or standard
bases.

In the first half of this file, we show that an `R`-linear structure on `C` passes to `Mat_ C`,
with scalars acting entrywise on matrices, so that `Mat_.embedding C`, `F.mapMat_`, and
`Mat_.lift F` are `R`-linear.

In the second half of this file, we equip `Mat R` with:

* Entrywise `S`-module structure on `M ⟶ N` (`Mat.homLinearEquiv`) over any semiring `R`, together
  with the `S`-linear category instance `Linear S (Mat R)` over any ring `R` and scalar semiring `S`
  satisfying `[IsScalarTower S R R]` and `[SMulCommClass S R R]`.
* The standard `R`-basis `Mat.basisHom M N : Module.Basis (M × N) R (M ⟶ N)` of matrix units, its
  coordinates (`Mat.basisHom_repr_apply`), and the matrix-unit composition law
  `Mat.basisHom_comp_basisHom`.
* The endomorphism ring and algebra isomorphisms `Mat.endUnitRingEquiv : End (Mat.unit R) ≃+* Rᵐᵒᵖ`
  and `Mat.endUnitAlgEquiv : End (Mat.unit R) ≃ₐ[R] R`.
* `S`-linearity of scalar extension `(Mat.mapRingHom φ.toRingHom).Linear S` along an `S`-algebra
  homomorphism `φ : R₁ →ₐ[S] R₂`.

## Main declarations

* `CategoryTheory.Linear R (Mat_ C)` and linearity of `Mat_.embedding C`, `F.mapMat_`, and
  `Mat_.lift F`.
* `CategoryTheory.Mat.instLinear`: `Linear S (Mat R)` across arbitrary universes.
* `CategoryTheory.Mat.basisHom`, `CategoryTheory.Mat.basisHom_comp_basisHom`: standard matrix-unit
  basis of `M ⟶ N` and its composition formula.
* `CategoryTheory.Mat.endUnitRingEquiv`, `CategoryTheory.Mat.endUnitAlgEquiv`: endomorphisms of
  `Mat.unit R`.
* `CategoryTheory.Mat.instLinearMapRingHomAlgHom`: linearity of `Mat.mapRingHom` for `AlgHom`s.
-/

public section

namespace CategoryTheory

open Limits

section Mat_

universe w v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {R : Type w} [Semiring R] [Linear R C]

namespace Mat_

/-- The `R`-module of matrices of morphisms between two objects of `Mat_ C`, with scalars acting
entrywise. -/
instance instModuleHom (M N : Mat_ C) : Module R (M ⟶ N) :=
  inferInstanceAs <| Module R (∀ i j, M.X i ⟶ N.X j)

/-- Scalars act entrywise on matrices of morphisms. -/
@[simp]
theorem smul_apply {M N : Mat_ C} (r : R) (f : M ⟶ N) (i : M.ι) (j : N.ι) :
    (r • f) i j = r • f i j :=
  (rfl)

/-- The matrix category of an `R`-linear category is `R`-linear. -/
instance : Linear R (Mat_ C) where
  smul_comp _ _ _ r f g := by
    ext
    simp [Finset.smul_sum]
  comp_smul _ _ _ f r g := by
    ext
    simp [Finset.smul_sum]

/-- The embedding of `C` into `Mat_ C` as one-by-one matrices is `R`-linear. -/
instance : (embedding C).Linear R where

variable {D : Type u₂} [Category.{v₁} D] [Preadditive D] [Linear R D]

/-- The functor induced on matrix categories by an `R`-linear functor is `R`-linear. -/
instance (F : C ⥤ D) [F.Additive] [F.Linear R] : F.mapMat_.Linear R where
  map_smul f r := by
    ext i j
    -- `F.mapMat_` applies `F.map` entrywise (`Functor.mapMat__map`), and scalars act entrywise
    -- (`Mat_.smul_apply`). Neither lemma rewrites here, since the types of `i` and `j` mention
    -- `F.mapMat_.obj`, so the goal is closed up to these two definitional unfoldings.
    exact (F.map_smul r (f i j) :)

variable {E : Type u₁} [Category.{v₁} E] [Preadditive E] [Linear R E]

/-- The extension `Mat_.lift F : Mat_ C ⥤ E` of an `R`-linear functor `F : C ⥤ E` is
`R`-linear. -/
instance lift_linear [HasFiniteBiproducts E] (F : C ⥤ E) [F.Additive] [F.Linear R] :
    (lift F).Linear R where
  map_smul f r := by
    simp only [lift_map, smul_apply, F.map_smul]
    exact biproduct.matrix_smul r _

end Mat_

end Mat_

namespace Mat

universe w u

section Semiring

variable {R : Type u} [Semiring R] {S : Type w} [Semiring S] [Module S R]

/-- Morphisms in `Mat R` carry an entrywise `S`-module structure whenever `R` is an `S`-module. -/
instance instModuleHom (M N : Mat R) : Module S (M ⟶ N) :=
  inferInstanceAs <| Module S (Matrix M N R)

@[simp]
theorem smul_apply {M N : Mat R} (s : S) (f : M ⟶ N) (i : M) (j : N) :
    (s • f) i j = s • f i j :=
  (rfl)

/-- The tautological `S`-linear equivalence `(M ⟶ N) ≃ₗ[S] Matrix M N R`. -/
def homLinearEquiv (S : Type w) [Semiring S] [Module S R] (M N : Mat R) :
    (M ⟶ N) ≃ₗ[S] Matrix M N R :=
  LinearEquiv.refl S (Matrix M N R)

@[simp]
theorem homLinearEquiv_apply (S : Type w) [Semiring S] [Module S R] {M N : Mat R}
    (f : M ⟶ N) (i : M) (j : N) :
    homLinearEquiv S M N f i j = f i j :=
  (rfl)

@[simp]
theorem homLinearEquiv_symm_apply (S : Type w) [Semiring S] [Module S R] {M N : Mat R}
    (A : Matrix M N R) (i : M) (j : N) :
    (homLinearEquiv S M N).symm A i j = A i j :=
  (rfl)

/-- The standard `R`-basis of matrix units on `M ⟶ N` in `Mat R`, indexed by `M × N`. -/
noncomputable def basisHom (M N : Mat R) : Module.Basis (M × N) R (M ⟶ N) :=
  let _ : Fintype M := @FintypeCat.fintype M
  (Matrix.stdBasis R M N).map (homLinearEquiv R M N).symm

/-- The `(i, j)` matrix unit in `Mat.basisHom M N` is `Matrix.single i j 1`. -/
theorem basisHom_apply (M N : Mat R) [DecidableEq M] [DecidableEq N] (p : M × N) :
    (basisHom M N p : Matrix M N R) = Matrix.single p.1 p.2 1 := by
  let _ : Fintype M := @FintypeCat.fintype M
  unfold basisHom homLinearEquiv
  exact (Module.Basis.map_apply _ _ p).trans (Matrix.stdBasis_eq_single R p.1 p.2)

/-- Coordinates in the standard basis `Mat.basisHom M N` are the matrix entries. -/
@[simp]
theorem basisHom_repr_apply {M N : Mat R} (f : M ⟶ N) (p : M × N) :
    (basisHom M N).repr f p = f p.1 p.2 := by
  let _ : Fintype M := @FintypeCat.fintype M
  unfold basisHom homLinearEquiv Matrix.stdBasis
  simp
  rfl

/-- Composition of standard matrix units in `Mat R`: `E_{i, j} ≫ E_{k, l} = δ_{j, k} E_{i, l}`. -/
@[simp]
theorem basisHom_comp_basisHom (M N P : Mat R) [DecidableEq N] (p : M × N) (q : N × P) :
    basisHom M N p ≫ basisHom N P q =
      if p.2 = q.1 then basisHom M P (p.1, q.2) else 0 := by
  classical
  let _ : Fintype N := @FintypeCat.fintype N
  have hp : (basisHom M N p : Matrix M N R) = Matrix.single p.1 p.2 1 := basisHom_apply M N p
  have hq : (basisHom N P q : Matrix N P R) = Matrix.single q.1 q.2 1 := basisHom_apply N P q
  have hmul :
      (basisHom M N p ≫ basisHom N P q : Matrix M P R) =
        Matrix.single p.1 p.2 (1 : R) * Matrix.single q.1 q.2 (1 : R) :=
    Matrix.ext fun i k ↦
      (comp_apply R (basisHom M N p) (basisHom N P q) i k).trans
        ((Finset.sum_congr rfl fun j _ ↦
          congrArg₂ (· * ·)
            (congrArg (fun m : Matrix M N R ↦ m i j) hp)
            (congrArg (fun m : Matrix N P R ↦ m j k) hq)).trans
          (Matrix.mul_apply (M := Matrix.single p.1 p.2 (1 : R))
            (N := Matrix.single q.1 q.2 (1 : R)) (i := i) (k := k)).symm)
  by_cases h : p.2 = q.1
  · refine hmul.trans ?_
    have hsame :
        Matrix.single p.1 p.2 (1 : R) * Matrix.single q.1 q.2 (1 : R) =
          Matrix.single p.1 q.2 (1 : R) := by
      rw [← h, Matrix.single_mul_single_same, one_mul]
    exact hsame.trans ((basisHom_apply M P (p.1, q.2)).symm.trans (ite_eq_left h).symm)
  · have hzero : Matrix.single p.1 p.2 (1 : R) * Matrix.single q.1 q.2 (1 : R) = 0 := by simp [h]
    exact hmul.trans (hzero.trans (ite_eq_right h).symm)

end Semiring

section Ring

attribute [local instance] FintypeCat.fintype in
/-- `Mat R` is an `S`-linear category whenever `R` is a ring and `S` acts centrally on `R`. -/
instance instLinear (S : Type w) (R : Type u) [Semiring S] [Ring R] [Module S R]
    [IsScalarTower S R R] [SMulCommClass S R R] : Linear S (Mat R) where
  homModule M N := instModuleHom M N
  smul_comp _ _ _ s f g := Matrix.ext fun i k ↦
    (comp_apply R (s • f) g i k).trans
      ((Finset.sum_congr rfl fun j _ ↦ smul_mul_assoc s (f i j) (g j k)).trans
        ((Finset.smul_sum (r := s)).symm.trans (congrArg (s • ·) (comp_apply R f g i k)).symm))
  comp_smul _ _ _ f s g := Matrix.ext fun i k ↦
    (comp_apply R f (s • g) i k).trans
      ((Finset.sum_congr rfl fun j _ ↦ mul_smul_comm s (f i j) (g j k)).trans
        ((Finset.smul_sum (r := s)).symm.trans (congrArg (s • ·) (comp_apply R f g i k)).symm))

/-- Endomorphisms of `Mat.unit R` form a ring isomorphic to `Rᵐᵒᵖ`, since multiplication in
`End X` reverses categorical composition (`(f * g).asHom = g.asHom ≫ f.asHom`). -/
def endUnitRingEquiv (R : Type u) [Ring R] : End (unit R) ≃+* Rᵐᵒᵖ where
  toFun f := MulOpposite.op (f.asHom PUnit.unit PUnit.unit)
  invFun r := End.of (Matrix.of fun _ _ ↦ r.unop)
  left_inv _ := End.ext (Matrix.ext fun ⟨⟩ ⟨⟩ ↦ rfl)
  right_inv _ := rfl
  map_mul' f g :=
    (congrArg MulOpposite.op
      (comp_apply_eq_single g.asHom f.asHom PUnit.unit PUnit.unit PUnit.unit
        fun ⟨⟩ h ↦ absurd rfl h)).trans
      (MulOpposite.op_mul _ _)
  map_add' _ _ := rfl

@[simp]
theorem endUnitRingEquiv_apply {R : Type u} [Ring R] (f : End (unit R)) :
    endUnitRingEquiv R f = MulOpposite.op (f.asHom PUnit.unit PUnit.unit) :=
  (rfl)

@[simp]
theorem endUnitRingEquiv_symm_asHom_apply {R : Type u} [Ring R] (r : Rᵐᵒᵖ) (x y : unit R) :
    ((endUnitRingEquiv R).symm r).asHom x y = r.unop :=
  (rfl)

/-- Over a commutative ring `R`, `End (Mat.unit R)` is canonically `R`-algebra isomorphic to `R`. -/
def endUnitAlgEquiv (R : Type u) [CommRing R] : End (unit R) ≃ₐ[R] R where
  toFun f := f.asHom PUnit.unit PUnit.unit
  invFun r := End.of (Matrix.of fun _ _ ↦ r)
  left_inv _ := End.ext (Matrix.ext fun ⟨⟩ ⟨⟩ ↦ rfl)
  right_inv _ := rfl
  map_mul' f g :=
    (comp_apply_eq_single g.asHom f.asHom PUnit.unit PUnit.unit PUnit.unit
      fun ⟨⟩ h ↦ absurd rfl h).trans (mul_comm _ _)
  map_add' _ _ := rfl
  commutes' r := by
    change (r • (𝟙 (unit R) : unit R ⟶ unit R)) PUnit.unit PUnit.unit = r
    exact (congrArg (r * ·) (id_apply_self R (unit R) PUnit.unit)).trans (mul_one r)

@[simp]
theorem endUnitAlgEquiv_apply {R : Type u} [CommRing R] (f : End (unit R)) :
    endUnitAlgEquiv R f = f.asHom PUnit.unit PUnit.unit :=
  (rfl)

@[simp]
theorem endUnitAlgEquiv_symm_asHom_apply {R : Type u} [CommRing R] (r : R) (x y : unit R) :
    ((endUnitAlgEquiv R).symm r).asHom x y = r :=
  (rfl)

/-- Base change along an `S`-algebra homomorphism `φ : R₁ →ₐ[S] R₂` is an `S`-linear functor
`Mat R₁ ⥤ Mat R₂`. -/
instance instLinearMapRingHomAlgHom {S : Type w} {R₁ R₂ : Type u} [CommSemiring S]
    [Ring R₁] [Ring R₂] [Algebra S R₁] [Algebra S R₂] (φ : R₁ →ₐ[S] R₂) :
    (mapRingHom φ.toRingHom).Linear S where
  map_smul f s := Matrix.ext fun i j ↦ map_smul φ s (f i j)

end Ring

end Mat

end CategoryTheory

