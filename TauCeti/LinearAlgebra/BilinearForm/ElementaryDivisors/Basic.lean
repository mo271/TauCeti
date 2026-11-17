/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Matrix.Alternating
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Alternating block matrices and structural properties of normal forms

This file develops the basic algebra of alternating block matrices
`Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0` and the structural invariants of
a bilinear form admitting such a Gram matrix in a basis `b`: determinant, unimodularity, rescaling
to `Matrix.J`, cokernel decomposition, kernel rank, and even rank over integral domains.

## Main results

* `Matrix.J_mul_fromBlocks_diagonal`: left-multiplying `[[0, D], [-D, 0]]` by `Matrix.J` produces
  `Matrix.diagonal (Sum.elim d d)`.
* `Matrix.det_fromBlocks_zero_diagonal_neg_diagonal`: the determinant of `[[0, D], [-D, 0]]` is
  `(∏ i, d i) ^ 2` over any commutative ring.
* `Matrix.isUnit_det_fromBlocks_zero_diagonal_neg_diagonal_iff`: `[[0, D], [-D, 0]]` has unit
  determinant iff every `d i` is a unit.
* `Matrix.isAlt_toBilin'_fromBlocks_zero_diagonal_neg_diagonal`: `[[0, D], [-D, 0]]` defines an
  alternating bilinear form in every characteristic.
* `LinearMap.BilinForm.exists_det_toMatrix_eq_unit_sq_mul_prod_sq`: determinant in any finite basis
  differs from `(∏ i, d i) ^ 2` by the square of a unit.
* `LinearMap.BilinForm.isPerfPair_iff_forall_isUnit_of_toMatrix_eq_fromBlocks_diagonal`:
  unimodularity criterion.
* `LinearMap.BilinForm.exists_basis_toMatrix_eq_J_of_toMatrix_eq_fromBlocks_diagonal`: rescaling a
  unit diagonal `d` gives a symplectic basis with Gram matrix `Matrix.J`.
* `LinearMap.BilinForm.mem_range_iff_dvd_of_toMatrix_eq_fromBlocks_diagonal` and
  `LinearMap.BilinForm.quotientRangeEquivPiSpan`: cokernel decomposition
  `Module.Dual R M ⧸ LinearMap.range B ≃ₗ[R] (∀ i, R ⧸ (d i)) × (∀ i, R ⧸ (d i))`.
* `LinearMap.BilinForm.ker_eq_span_inr_of_toMatrix_eq_fromBlocks_zero` and
  `LinearMap.BilinForm.finrank_ker_eq_card_of_toMatrix_eq_fromBlocks_zero`: kernel and nullity of
  a singular alternating normal form.
* `LinearMap.BilinForm.IsAlt.even_finrank_of_isDomain`: a finite free module over an integral
  domain carrying a nondegenerate alternating form has even rank.
-/

public section

open Module Submodule

/-! ### Block alternating matrix identities -/

namespace Matrix

section CommRing

variable {l R : Type*} [Fintype l] [DecidableEq l] [CommRing R]

/-- Left-multiplying the alternating block matrix `[[0, D], [-D, 0]]` by the canonical skew matrix
`Matrix.J` produces the diagonal matrix `diagonal (Sum.elim d d)`. -/
theorem J_mul_fromBlocks_diagonal (d : l → R) :
    Matrix.J l R * fromBlocks 0 (diagonal d) (-diagonal d) 0 = diagonal (Sum.elim d d) := by
  rw [Matrix.J, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, neg_mul, mul_neg, neg_neg,
    neg_zero, Matrix.one_mul]
  exact fromBlocks_diagonal d d

/-- **Determinant of the alternating block matrix `[[0, D], [-D, 0]]`** is `(∏ i, d i) ^ 2` over
every commutative ring. -/
theorem det_fromBlocks_zero_diagonal_neg_diagonal (d : l → R) :
    (fromBlocks (0 : Matrix l l R) (diagonal d) (-diagonal d) 0).det = (∏ i, d i) ^ 2 := by
  have h := congrArg Matrix.det (J_mul_fromBlocks_diagonal d)
  rw [det_mul, det_J, one_mul, det_diagonal, Fintype.prod_sum_type] at h
  simpa only [Sum.elim_inl, Sum.elim_inr, sq] using h

/-- The alternating block matrix `[[0, D], [-D, 0]]` has unit determinant iff every entry of `d`
is a unit. -/
theorem isUnit_det_fromBlocks_zero_diagonal_neg_diagonal_iff (d : l → R) :
    IsUnit (fromBlocks (0 : Matrix l l R) (diagonal d) (-diagonal d) 0).det ↔
      ∀ i, IsUnit (d i) := by
  rw [det_fromBlocks_zero_diagonal_neg_diagonal, isUnit_pow_iff (by decide : 2 ≠ 0),
    IsUnit.prod_univ_iff]

/-- The bilinear form attached to `[[0, D], [-D, 0]]` is alternating in every characteristic. -/
theorem isAlt_toBilin'_fromBlocks_zero_diagonal_neg_diagonal (d : l → R) :
    (fromBlocks (0 : Matrix l l R) (diagonal d) (-diagonal d) 0).toBilin'.IsAlt := by
  rw [isAlt_toBilin'_iff]
  refine ⟨?_, fun i ↦ by rcases i with i | i <;> simp⟩
  rw [fromBlocks_transpose, transpose_zero, diagonal_transpose, transpose_neg, diagonal_transpose,
    fromBlocks_neg, neg_zero, neg_neg]

end CommRing

end Matrix

/-! ### Structural properties of alternating block bases -/

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

section BlockBasis

variable {R M l : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype l] [DecidableEq l]

/-- If `B` has Gram matrix `[[0, D], [-D, 0]]` in a basis `b`, then in every finite basis `c` of
`M` (over a ring with the strong rank condition), `det (B.toMatrix c)` equals `(∏ i, d i) ^ 2`
times the square of a unit. -/
theorem exists_det_toMatrix_eq_unit_sq_mul_prod_sq [StrongRankCondition R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : BilinForm R M}
    {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (c : Basis ι R M) :
    ∃ u : Rˣ, (B.toMatrix c).det = (u : R) ^ 2 * (∏ i, d i) ^ 2 := by
  let e : l ⊕ l ≃ ι := b.indexEquiv c
  have hu : IsUnit ((b.reindex e).toMatrix c).det :=
    Matrix.isUnit_det_of_right_inverse ((b.reindex e).toMatrix_mul_toMatrix_flip c)
  refine ⟨hu.unit, ?_⟩
  rw [det_toMatrix_eq_det_sq_mul_det (b.reindex e) c B, det_toMatrix_reindex, hb,
    Matrix.det_fromBlocks_zero_diagonal_neg_diagonal, IsUnit.unit_spec]

/-- A bilinear form with Gram matrix `[[0, D], [-D, 0]]` in a finite basis is a perfect pairing iff
every diagonal entry `d i` is a unit. -/
theorem isPerfPair_iff_forall_isUnit_of_toMatrix_eq_fromBlocks_diagonal
    {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) :
    B.IsPerfPair ↔ ∀ i, IsUnit (d i) := by
  rw [← Matrix.isUnit_det_fromBlocks_zero_diagonal_neg_diagonal_iff d, ← hb]
  exact ⟨fun h ↦ b.isUnit_det_of_isPerfPair b B h, fun h ↦ b.isPerfPair_of_isUnit_det b B h⟩

/-- If `B` has Gram matrix `[[0, D], [-D, 0]]` with every `d i` a unit, rescaling the second half
of the basis gives a symplectic basis with Gram matrix `Matrix.J l R`. -/
theorem exists_basis_toMatrix_eq_J_of_toMatrix_eq_fromBlocks_diagonal
    {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (hunit : ∀ i, IsUnit (d i)) :
    ∃ b' : Basis (l ⊕ l) R M, B.toMatrix b' = Matrix.J l R := by
  choose u hu using hunit
  let w : l ⊕ l → R := Sum.elim (fun _ ↦ 1) (fun i ↦ -(((u i)⁻¹ : Rˣ) : R))
  have hw : ∀ x, IsUnit (w x) := fun x ↦ by
    rcases x with _ | i
    · exact isUnit_one
    · exact (u i)⁻¹.isUnit.neg
  refine ⟨b.isUnitSMul hw, ?_⟩
  ext x y
  have hxy : B (b x) (b y) =
      Matrix.fromBlocks (0 : Matrix l l R) (Matrix.diagonal d) (-Matrix.diagonal d) 0 x y := by
    rw [← toMatrix_apply, hb]
  simp only [toMatrix_apply, Basis.isUnitSMul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hxy]
  rcases x with i | i <;> rcases y with j | j <;>
    simp only [w, Sum.elim_inl, Sum.elim_inr, Matrix.J, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, Matrix.diagonal_apply, Matrix.one_apply,
      one_mul, mul_zero, neg_mul, mul_neg]
  · split_ifs with hij
    · subst hij; rw [← hu i]; simp
    · simp
  · split_ifs with hij
    · subst hij; rw [← hu i]; simp
    · simp

/-- Evaluation of `B v (b (inl i))` in a basis with alternating block Gram matrix
`[[0, D], [-D, 0]]`. -/
private lemma apply_basis_inl_of_toMatrix_eq_fromBlocks_diagonal
    {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (v : M) (i : l) :
    B v (b (Sum.inl i)) = -b.repr v (Sum.inr i) * d i := by
  rw [apply_eq_dotProduct_toMatrix_mulVec b B v (b (Sum.inl i)), hb, b.repr_self]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finsupp.single_apply,
    Matrix.diagonal_apply]

/-- Evaluation of `B v (b (inr i))` in a basis with alternating block Gram matrix
`[[0, D], [-D, 0]]`. -/
private lemma apply_basis_inr_of_toMatrix_eq_fromBlocks_diagonal
    {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (v : M) (i : l) :
    B v (b (Sum.inr i)) = b.repr v (Sum.inl i) * d i := by
  rw [apply_eq_dotProduct_toMatrix_mulVec b B v (b (Sum.inr i)), hb, b.repr_self]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finsupp.single_apply,
    Matrix.diagonal_apply]

/-- Along a basis with Gram matrix `[[0, D], [-D, 0]]`, a linear functional `φ : Module.Dual R M`
lies in `LinearMap.range B` iff `d i` divides both `φ (b (inl i))` and `φ (b (inr i))` for every
`i`. Holds over any commutative ring, including when some `d i = 0`. -/
theorem mem_range_iff_dvd_of_toMatrix_eq_fromBlocks_diagonal
    {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (φ : Module.Dual R M) :
    φ ∈ LinearMap.range B ↔
      ∀ i, d i ∣ φ (b (Sum.inl i)) ∧ d i ∣ φ (b (Sum.inr i)) := by
  constructor
  · rintro ⟨v, rfl⟩ i
    exact ⟨⟨-b.repr v (Sum.inr i),
        by rw [apply_basis_inl_of_toMatrix_eq_fromBlocks_diagonal hb, mul_comm]⟩,
      ⟨b.repr v (Sum.inl i),
        by rw [apply_basis_inr_of_toMatrix_eq_fromBlocks_diagonal hb, mul_comm]⟩⟩
  · intro hdiv
    choose c₁ hc₁ using fun i ↦ (hdiv i).1
    choose c₂ hc₂ using fun i ↦ (hdiv i).2
    refine ⟨∑ i, c₂ i • b (Sum.inl i) + ∑ i, (-c₁ i) • b (Sum.inr i),
      b.ext fun x ↦ ?_⟩
    rcases x with i | i
    · rw [apply_basis_inl_of_toMatrix_eq_fromBlocks_diagonal hb]
      simp [Finsupp.single_apply, hc₁ i, mul_comm]
    · rw [apply_basis_inr_of_toMatrix_eq_fromBlocks_diagonal hb]
      simp [Finsupp.single_apply, hc₂ i, mul_comm]

/-- Any common multiple `c` of the diagonal entries `d i` carries every dual functional into
`LinearMap.range B`. -/
theorem smul_mem_range_of_toMatrix_eq_fromBlocks_diagonal
    {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    {c : R} (hc : ∀ i, d i ∣ c) (φ : Module.Dual R M) :
    c • φ ∈ LinearMap.range B := by
  rw [mem_range_iff_dvd_of_toMatrix_eq_fromBlocks_diagonal hb]
  intro i
  exact ⟨(hc i).mul_right _, (hc i).mul_right _⟩

/-- The dual coordinate isomorphism sends `LinearMap.range B` to the product of principal ideals
`Ideal.span {Sum.elim d d x}`. -/
private lemma map_dualBasis_equivFun_range_eq_pi {B : BilinForm R M} {b : Basis (l ⊕ l) R M}
    {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) :
    Submodule.map (b.dualBasis.equivFun : Module.Dual R M →ₗ[R] l ⊕ l → R)
        (LinearMap.range B) =
      Submodule.pi Set.univ fun x : l ⊕ l ↦ Ideal.span ({Sum.elim d d x} : Set R) := by
  ext f
  simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    Ideal.mem_span_singleton, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨φ, hφ, rfl⟩ x
    have h := (mem_range_iff_dvd_of_toMatrix_eq_fromBlocks_diagonal hb φ).mp hφ
    rcases x with i | i
    · simpa [Basis.dualBasis_repr] using (h i).1
    · simpa [Basis.dualBasis_repr] using (h i).2
  · intro hf
    refine ⟨b.dualBasis.equivFun.symm f, ?_, b.dualBasis.equivFun.apply_symm_apply f⟩
    rw [mem_range_iff_dvd_of_toMatrix_eq_fromBlocks_diagonal hb]
    intro i
    have hsymm : ∀ x, (b.dualBasis.equivFun.symm f) (b x) = f x := fun x ↦ by
      have h := congrFun (b.dualBasis.equivFun.apply_symm_apply f) x
      rwa [Basis.equivFun_apply, Basis.dualBasis_repr] at h
    exact ⟨by rw [hsymm]; exact hf (Sum.inl i), by rw [hsymm]; exact hf (Sum.inr i)⟩

/-- Splits a dependent family indexed by `l ⊕ l` over `Sum.elim d d` into a pair of families
indexed by `l`. -/
private def sumQuotientEquivProd (d : l → R) :
    ((x : l ⊕ l) → R ⧸ Ideal.span ({Sum.elim d d x} : Set R)) ≃ₗ[R]
      ((i : l) → R ⧸ Ideal.span ({d i} : Set R)) ×
        ((i : l) → R ⧸ Ideal.span ({d i} : Set R)) where
  toFun f := (fun i ↦ f (Sum.inl i), fun i ↦ f (Sum.inr i))
  invFun p x := match x with | Sum.inl i => p.1 i | Sum.inr i => p.2 i
  left_inv f := funext fun x ↦ by rcases x with i | i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype l] [DecidableEq l] in
private lemma sumQuotientEquivProd_fst (d : l → R)
    (f : (x : l ⊕ l) → R ⧸ Ideal.span ({Sum.elim d d x} : Set R)) (i : l) :
    (sumQuotientEquivProd d f).1 i = f (Sum.inl i) := rfl

omit [Fintype l] [DecidableEq l] in
private lemma sumQuotientEquivProd_snd (d : l → R)
    (f : (x : l ⊕ l) → R ⧸ Ideal.span ({Sum.elim d d x} : Set R)) (i : l) :
    (sumQuotientEquivProd d f).2 i = f (Sum.inr i) := rfl

/-- **Cokernel decomposition of an alternating form.** Given a basis `b` in which `B` has Gram
matrix `[[0, D], [-D, 0]]`, the quotient `Module.Dual R M ⧸ LinearMap.range B` splits as the
product of two copies of `∀ i, R ⧸ Ideal.span {d i}`. Holds over any commutative ring, even when
some `d i = 0`. -/
noncomputable def quotientRangeEquivPiSpan {B : BilinForm R M} {b : Basis (l ⊕ l) R M}
    {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) :
    (Module.Dual R M ⧸ LinearMap.range B) ≃ₗ[R]
      ((i : l) → R ⧸ Ideal.span ({d i} : Set R)) ×
        ((i : l) → R ⧸ Ideal.span ({d i} : Set R)) :=
  ((Submodule.Quotient.equiv (LinearMap.range B) _ b.dualBasis.equivFun
    (map_dualBasis_equivFun_range_eq_pi hb)).trans
    (Submodule.quotientPi fun x : l ⊕ l ↦ Ideal.span ({Sum.elim d d x} : Set R))).trans
    (sumQuotientEquivProd d)

/-- The first component of `quotientRangeEquivPiSpan` evaluates a dual functional on the first half
of the symplectic basis modulo `d i`. -/
@[simp]
theorem quotientRangeEquivPiSpan_mk_fst {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (φ : Module.Dual R M) (i : l) :
    (quotientRangeEquivPiSpan hb (Submodule.Quotient.mk φ)).1 i =
      Ideal.Quotient.mk (Ideal.span {d i}) (φ (b (Sum.inl i))) := by
  rw [quotientRangeEquivPiSpan, LinearEquiv.trans_apply, sumQuotientEquivProd_fst,
    LinearEquiv.trans_apply]
  simp [Basis.dualBasis_repr]
  rfl

/-- The second component of `quotientRangeEquivPiSpan` evaluates a dual functional on the second
half of the symplectic basis modulo `d i`. -/
@[simp]
theorem quotientRangeEquivPiSpan_mk_snd {B : BilinForm R M} {b : Basis (l ⊕ l) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (φ : Module.Dual R M) (i : l) :
    (quotientRangeEquivPiSpan hb (Submodule.Quotient.mk φ)).2 i =
      Ideal.Quotient.mk (Ideal.span {d i}) (φ (b (Sum.inr i))) := by
  rw [quotientRangeEquivPiSpan, LinearEquiv.trans_apply, sumQuotientEquivProd_snd,
    LinearEquiv.trans_apply]
  simp [Basis.dualBasis_repr]
  rfl

/-- Evaluation of `B v (b (inl (inl i)))` in a singular alternating block basis. -/
private lemma apply_basis_inl_inl_of_toMatrix_eq_fromBlocks_zero
    {m : Type*} [Fintype m] [DecidableEq m]
    {B : BilinForm R M} {b : Basis ((l ⊕ l) ⊕ m) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0)
    (v : M) (i : l) :
    B v (b (Sum.inl (Sum.inl i))) = -b.repr v (Sum.inl (Sum.inr i)) * d i := by
  rw [apply_eq_dotProduct_toMatrix_mulVec b B v (b (Sum.inl (Sum.inl i))), hb, b.repr_self]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finsupp.single_apply,
    Matrix.diagonal_apply]

/-- Evaluation of `B v (b (inl (inr i)))` in a singular alternating block basis. -/
private lemma apply_basis_inl_inr_of_toMatrix_eq_fromBlocks_zero
    {m : Type*} [Fintype m] [DecidableEq m]
    {B : BilinForm R M} {b : Basis ((l ⊕ l) ⊕ m) R M} {d : l → R}
    (hb : B.toMatrix b = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0)
    (v : M) (i : l) :
    B v (b (Sum.inl (Sum.inr i))) = b.repr v (Sum.inl (Sum.inl i)) * d i := by
  rw [apply_eq_dotProduct_toMatrix_mulVec b B v (b (Sum.inl (Sum.inr i))), hb, b.repr_self]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finsupp.single_apply,
    Matrix.diagonal_apply]

/-- **Kernel of a singular alternating form in normal form.** When `B` has Gram matrix
`fromBlocks [[0, D], [-D, 0]] 0 0 0` in `b : Basis ((l ⊕ l) ⊕ m) R M` and every `d i` is a
non-zero-divisor, the kernel of `B` is spanned by the right-summand basis vectors `b (inr j)`. -/
theorem ker_eq_span_inr_of_toMatrix_eq_fromBlocks_zero {m : Type*} [Fintype m] [DecidableEq m]
    {B : BilinForm R M} {b : Basis ((l ⊕ l) ⊕ m) R M} {d : l → R}
    (hd : ∀ i, d i ∈ nonZeroDivisors R)
    (hb : B.toMatrix b = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0) :
    LinearMap.ker B = Submodule.span R (Set.range fun j : m ↦ b (Sum.inr j)) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have hv_zero : ∀ y, B v (b y) = 0 := fun y ↦ LinearMap.congr_fun hv (b y)
    have hval_inl : ∀ i : l, b.repr v (Sum.inl (Sum.inr i)) = 0 := fun i ↦ by
      have h := hv_zero (Sum.inl (Sum.inl i))
      rw [apply_basis_inl_inl_of_toMatrix_eq_fromBlocks_zero hb] at h
      exact (hd i).2 _ (neg_eq_zero.mp (by rwa [neg_mul] at h))
    have hval_inr : ∀ i : l, b.repr v (Sum.inl (Sum.inl i)) = 0 := fun i ↦ by
      have h := hv_zero (Sum.inl (Sum.inr i))
      rw [apply_basis_inl_inr_of_toMatrix_eq_fromBlocks_zero hb] at h
      exact (hd i).2 _ h
    rw [← b.sum_repr v, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [hval_inl, hval_inr, zero_smul, Finset.sum_const_zero, zero_add]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact b.ext fun y ↦ by
      rw [LinearMap.zero_apply, ← toMatrix_apply, hb]
      rcases y with (i | i) | k <;> simp

/-- The rank of the kernel of a singular alternating form in normal form is the size of its zero
block. -/
theorem finrank_ker_eq_card_of_toMatrix_eq_fromBlocks_zero [StrongRankCondition R]
    {m : Type*} [Fintype m] [DecidableEq m]
    {B : BilinForm R M} {b : Basis ((l ⊕ l) ⊕ m) R M} {d : l → R}
    (hd : ∀ i, d i ∈ nonZeroDivisors R)
    (hb : B.toMatrix b = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0) :
    Module.finrank R (LinearMap.ker B) = Fintype.card m := by
  have hli : LinearIndependent R (fun j : m ↦ b (Sum.inr j)) :=
    b.linearIndependent.comp Sum.inr Sum.inr_injective
  have hker := ker_eq_span_inr_of_toMatrix_eq_fromBlocks_zero hd hb
  let bker : Basis m R (LinearMap.ker B) :=
    (Basis.span hli).map (LinearEquiv.ofEq _ _ hker.symm)
  exact Module.finrank_eq_card_basis bker

end BlockBasis

section EvenRank

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Even rank over an integral domain.** A finite free module over an integral domain carrying a
nondegenerate alternating bilinear form has even rank. Proof by passing to the fraction field and
invoking `LinearMap.BilinForm.IsAlt.even_finrank`. -/
theorem IsAlt.even_finrank_of_isDomain [IsDomain R] [Module.Free R M] [Module.Finite R M]
    {B : BilinForm R M} (hB : B.IsAlt) (hnd : B.Nondegenerate) : Even (Module.finrank R M) := by
  classical
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  let b := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  let A : Matrix ι ι R := B.toMatrix b
  have hdet : A.det ≠ 0 := (nondegenerate_iff_det_ne_zero b).mp hnd
  have hAK_det : (A.map f).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← f.map_det]
    exact fun h ↦ hdet (IsFractionRing.injective R K (h.trans (map_zero f).symm))
  have hA_alt : A.toBilin'.IsAlt := by
    rw [Matrix.isAlt_toBilin'_iff]
    exact ⟨by ext i j; simpa [A, toMatrix_apply] using (hB.neg_eq (b i) (b j)).symm,
      fun i ↦ by simpa [A, toMatrix_apply] using hB.self_eq_zero (b i)⟩
  have hAK_alt : (A.map f).toBilin'.IsAlt := by
    rw [Matrix.isAlt_toBilin'_iff] at hA_alt ⊢
    exact ⟨Matrix.transpose_map_of_transpose_eq_neg f hA_alt.1,
      fun i ↦ by simp [hA_alt.2 i]⟩
  have heven := hAK_alt.even_finrank
    (nondegenerate_toBilin'_iff_det_ne_zero.mpr hAK_det)
  rwa [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_basis b] at heven

end EvenRank

end LinearMap.BilinForm
