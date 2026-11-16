/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action
import Mathlib.Data.Fintype.EquivFin
import TauCeti.LinearAlgebra.SymplecticGroup
import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TwoStrands

/-!
# The Brauer algebra acts by intertwiners of the symplectic group

The action `TauCeti.brauerActionSymp` of the Brauer algebra `B_k(-2n)` on the tensor power
`(R^{2n})^{⊗k}` commutes with the diagonal action `g ↦ g^{⊗k}` of every matrix `g` preserving the
standard alternating form, `gᵀ * J * g = J`. Equivalently, the image of `B_k(-2n)` lies in the
commutant of the symplectic group acting on the tensor power
(`TauCeti.range_brauerActionSymp_le_centralizer`). On two strands, combining the generator
description of `TauCeti.brauerActionSymp` with the two-strand commutant calculation of
`TauCeti.adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer` upgrades this inclusion to an
equality (`TauCeti.range_brauerActionSymp_two_eq_centralizer`, and
`TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero` in characteristic zero).

Unlike the orthogonal proof, which contracts constant arc labellings directly, equivariance here
reduces along the loop-free cap-cup presentation of `BrauerDiagram`
(`TauCeti.BrauerDiagram.capCup_induction_on`): permutation diagrams act by the sign-twisted
reindexing representation, which commutes with every diagonal linear map, and cap-cup generators act
by `TauCeti.symplecticCupCapAt`, which commutes with every symplectic matrix
(`TauCeti.commute_symplecticCupCapAt_piTensorProductMap`). Transporting to matrices via
`TauCeti.symplecticTensorPowerBasis` and reindexing along `Fintype.equivFin` then gives the matrix
commutation `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower` over any finite
label type.

## Main results

* `TauCeti.commute_brauerActionSymp_piTensorProductMap`: every element of `B_k(-2n)` acts by an
  operator commuting with `A^{⊗k}` when `Aᵀ * J * A = J`.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_comp_sumCongr` and
  `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`: reindexing invariance of
  `symplecticActionMatrix`, and its commutation with `A.kroneckerPower (Fin k)` whenever
  `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_tensorPower` and
  `TauCeti.range_brauerActionSymp_le_centralizer`: the image of `B_k(-2n)` lies in the commutant of
  the symplectic group on `(R^{2n})^{⊗k}`.
* `TauCeti.range_brauerActionSymp_two_eq_adjoin`,
  `TauCeti.range_brauerActionSymp_two_eq_centralizer` and
  `TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`: on two strands the image of
  `B₂(-2n)` equals the commutant of the symplectic group.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
* S. Dipper, S. Doty and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl duality*,
  Transactions of the American Mathematical Society 360 (2008), 189-213.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

universe u

section Equivariance

variable (R : Type u) [CommRing R] (n k : ℕ)

private theorem commute_brauerActionSymp_of_piTensorProductMap (D : BrauerDiagram k)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hA : Aᵀ * Matrix.J (Fin n) R * A = Matrix.J (Fin n) R) :
    Commute (brauerActionSymp R n k (BrauerAlgebra.of D))
      (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  induction D using BrauerDiagram.capCup_induction_on with
  | permToBrauer σ =>
    rw [brauerActionSymp_of_permToBrauer, symplecticPermTensorAction_def]
    exact PiTensorProduct.commute_signReindexRepresentation_map σ _
  | capCup_compose a b X hab hloop ih =>
    rw [← BrauerAlgebra.of_mul_of_of_middleLoopCount_eq_zero hloop, map_mul,
      brauerActionSymp_of_capCup R n k hab]
    exact (commute_symplecticCupCapAt_piTensorProductMap hA hab).mul_left ih

/-- **The Brauer algebra commutes with symplectic matrices.** Every element of `B_k(-2n)` acts on
`((Fin n ⊕ Fin n) → R)^{⊗k}` by an operator commuting with the diagonal action of each matrix `A`
satisfying `Aᵀ * J * A = J`. -/
theorem commute_brauerActionSymp_piTensorProductMap (x : BrauerAlgebra R (-(2 * n : R)) k)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hA : Aᵀ * Matrix.J (Fin n) R * A = Matrix.J (Fin n) R) :
    Commute (brauerActionSymp R n k x)
      (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  set T := PiTensorProduct.map fun _ : Fin k => A.mulVecLin
  have hlin : (LinearMap.mulRight R T).comp (brauerActionSymp R n k).toLinearMap =
      (LinearMap.mulLeft R T).comp (brauerActionSymp R n k).toLinearMap :=
    (BrauerAlgebra.basis R (-(2 * n : R)) k).ext fun D => by
      simp only [LinearMap.comp_apply, BrauerAlgebra.basis_apply, AlgHom.toLinearMap_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
      exact (commute_brauerActionSymp_of_piTensorProductMap R n k D hA).eq
  exact LinearMap.congr_fun hlin x

/-- **The Brauer algebra acts by intertwiners of the symplectic group.** Every element of `B_k(-2n)`
acts on `((Fin n ⊕ Fin n) → R)^{⊗k}` by an operator commuting with the tensor power of the standard
representation of the symplectic group. -/
theorem commute_brauerActionSymp_tensorPower (x : BrauerAlgebra R (-(2 * n : R)) k)
    (g : Matrix.symplecticGroup (Fin n) R) :
    Commute (brauerActionSymp R n k x) ((stdSymplecticRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_brauerActionSymp_piTensorProductMap R n k x
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := R)).mp g.prop)

/-- **The image of `B_k(-2n)` lies in the commutant of the symplectic group** acting on the tensor
power `((Fin n ⊕ Fin n) → R)^{⊗k}`. -/
theorem range_brauerActionSymp_le_centralizer :
    (brauerActionSymp R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdSymplecticRep R n).tensorPower k)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionSymp_tensorPower R n k x g).symm.eq

end Equivariance

namespace BrauerDiagram

section MatrixEquivariance

variable {R : Type u} [CommRing R] {l : Type*} [DecidableEq l] {k : ℕ}

/-- Reindexing the halves of `l ⊕ l` along a bijection `e : l ≃ l'` leaves the entries of
`symplecticActionMatrix` unchanged. -/
theorem symplecticActionMatrix_comp_sumCongr {l' : Type*} [DecidableEq l'] (e : l ≃ l')
    (D : BrauerDiagram k) (v u : Fin k → l ⊕ l) :
    D.symplecticActionMatrix R l' (e.sumCongr e ∘ v) (e.sumCongr e ∘ u) =
      D.symplecticActionMatrix R l v u := by
  rw [symplecticActionMatrix_apply, symplecticActionMatrix_apply]
  congr 1
  ext x y
  have hsum (z : Fin k ⊕ Fin k) :
      Sum.elim (e.sumCongr e ∘ u) (e.sumCongr e ∘ v) z = e.sumCongr e (Sum.elim u v z) := by
    cases z <;> rfl
  rcases x with i | i <;> rcases y with j | j <;>
    simp only [symplecticArcWeight_inl_inl, symplecticArcWeight_inl_inr,
      symplecticArcWeight_inr_inl, symplecticArcWeight_inr_inr, hsum,
      (e.sumCongr e).injective.eq_iff]
  · rcases Sum.elim u v (Sum.inl i) with a | a <;>
      rcases Sum.elim u v (Sum.inl j) with b | b <;>
      simp [Matrix.J, Matrix.one_apply, e.injective.eq_iff]
  · rcases Sum.elim u v (Sum.inr i) with a | a <;>
      rcases Sum.elim u v (Sum.inr j) with b | b <;>
      simp [Matrix.J, Matrix.one_apply, e.injective.eq_iff]

private theorem commute_symplecticActionMatrix_kroneckerPower_fin {n : ℕ} (D : BrauerDiagram k)
    {B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hB : Bᵀ * Matrix.J (Fin n) R * B = Matrix.J (Fin n) R) :
    Commute (D.symplecticActionMatrix R (Fin n)) (B.kroneckerPower (Fin k)) := by
  have h := congrArg (LinearMap.toMatrix (symplecticTensorPowerBasis R n k)
    (symplecticTensorPowerBasis R n k))
    (commute_brauerActionSymp_piTensorProductMap R n k (BrauerAlgebra.of D) hB).eq
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, brauerActionSymp_of, LinearMap.toMatrix_toLin,
    Matrix.toMatrix_piTensorProductMap_symplecticTensorPowerBasis] at h
  exact h

/-- **The symplectic matrix of a Brauer diagram commutes with symplectic matrices.** For a matrix
`A` satisfying `Aᵀ * J * A = J`, the matrix `TauCeti.BrauerDiagram.symplecticActionMatrix` of `D`
commutes with the Kronecker power `A.kroneckerPower (Fin k)`. -/
theorem commute_symplecticActionMatrix_kroneckerPower [Fintype l] (D : BrauerDiagram k)
    {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : Aᵀ * Matrix.J l R * A = Matrix.J l R) :
    Commute (D.symplecticActionMatrix R l) (A.kroneckerPower (Fin k)) := by
  set m := Fintype.card l
  let e : l ≃ Fin m := Fintype.equivFin l
  let e' : Fin m ⊕ Fin m ≃ l ⊕ l := e.symm.sumCongr e.symm
  let fk : (Fin k → Fin m ⊕ Fin m) ≃ (Fin k → l ⊕ l) := Equiv.arrowCongr (Equiv.refl (Fin k)) e'
  let B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R := A.submatrix e' e'
  have hJ : (Matrix.J l R).submatrix e' e' = Matrix.J (Fin m) R := by
    ext x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp [Matrix.J, Matrix.one_apply, e', e.symm.injective.eq_iff]
  have hB : Bᵀ * Matrix.J (Fin m) R * B = Matrix.J (Fin m) R := by
    have h := congrArg (fun M => M.submatrix e' e') hA
    rwa [← Matrix.submatrix_mul_equiv _ _ _ e', ← Matrix.submatrix_mul_equiv _ _ _ e',
      ← Matrix.transpose_submatrix, hJ] at h
  have hM : (D.symplecticActionMatrix R l).submatrix fk fk =
      D.symplecticActionMatrix R (Fin m) := by
    ext v u
    rw [Matrix.submatrix_apply]
    exact symplecticActionMatrix_comp_sumCongr (R := R) e.symm D v u
  have hK : (A.kroneckerPower (Fin k)).submatrix fk fk = B.kroneckerPower (Fin k) := by
    ext v u
    simp [Matrix.kroneckerPower_apply, B, fk]
  have hcomm := (commute_symplecticActionMatrix_kroneckerPower_fin D hB).eq
  rw [← hM, ← hK, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv] at hcomm
  rw [commute_iff_eq]
  ext v u
  have h := congrFun (congrFun hcomm (fk.symm v)) (fk.symm u)
  simpa only [Matrix.submatrix_apply, fk.apply_symm_apply] using h

end MatrixEquivariance

end BrauerDiagram

/-! ### Two strands -/

section TwoStrands

/-- **On two strands, the image of `B₂(-2n)` is generated by the symplectic crossing and cap-cup.**
Over every commutative ring, `brauerActionSymp` maps the identity, crossing, and cap-cup diagrams
onto `1`, `TauCeti.symplecticCrossing`, and `TauCeti.symplecticCupCap`. -/
theorem range_brauerActionSymp_two_eq_adjoin (R : Type u) [CommRing R] (n : ℕ) :
    (brauerActionSymp R n 2).range =
      Algebra.adjoin R {symplecticCrossing R n, symplecticCupCap R n} := by
  rw [range_brauerActionSymp_eq_adjoin R n 2 (a := 0) (b := 1) (by decide),
    symplecticCupCapAt_zero_one]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ (rfl | ⟨σ, rfl⟩)
    · exact Algebra.subset_adjoin (by simp)
    · rcases (by decide : ∀ τ : Equiv.Perm (Fin 2), τ = 1 ∨ τ = Equiv.swap 0 1) σ with rfl | rfl
      · rw [map_one]
        exact Subalgebra.one_mem _
      · rw [symplecticPermTensorAction_swap_zero_one]
        exact Algebra.subset_adjoin (by simp)
  · rintro _ (rfl | rfl)
    · rw [← symplecticPermTensorAction_swap_zero_one]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨Equiv.swap 0 1, rfl⟩)
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)

/-- **Brauer duality for the symplectic group on two strands.** Over an integral domain containing a
unit `t` with `t ^ m ≠ 1` for `0 < m ≤ 4`, the image of `B₂(-2n)` under `brauerActionSymp` is the
full commutant of the symplectic group on `((Fin n ⊕ Fin n) → K)^{⊗2}`. -/
theorem range_brauerActionSymp_two_eq_centralizer {K : Type u} [CommRing K] [IsDomain K] (n : ℕ)
    (ht : ∃ t : Kˣ, ∀ m : ℕ, 0 < m → m ≤ 4 → t ^ m ≠ 1) :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) := by
  rw [range_brauerActionSymp_two_eq_adjoin,
    adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer ht]

/-- **Brauer duality for the symplectic group on two strands in characteristic zero**: the image of
`B₂(-2n)` under `brauerActionSymp` is the full commutant of the symplectic group on
`((Fin n ⊕ Fin n) → K)^{⊗2}`. -/
theorem range_brauerActionSymp_two_eq_centralizer_of_charZero {K : Type u} [Field K] [CharZero K]
    (n : ℕ) :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) := by
  rw [range_brauerActionSymp_two_eq_adjoin,
    adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer_of_charZero]

end TwoStrands

end TauCeti
