/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Generalized Cartan matrices

A **generalized Cartan matrix** on an index type `I` is an integral matrix `A : Matrix I I ℤ` such
that:
* `A i i = 2` for every `i`;
* `A i j ≤ 0` whenever `i ≠ j`;
* `A i j = 0 ↔ A j i = 0` for all `i` and `j`.

Unlike `Matrix.IsFiniteCartan`, no positive-definiteness, symmetrizability, finiteness, or
decidable-equality assumption on `I` is imposed, so affine, hyperbolic, and non-symmetrizable
generalized Cartan matrices are included on equal footing. In particular, `CartanMatrix.E n` is a
generalized Cartan matrix for every `n : ℕ`, including affine `E 9` (`E₈⁽¹⁾`) and hyperbolic
`E 10`.

## Main definitions

* `Matrix.IsGeneralizedCartan`: predicate that `A : Matrix I I ℤ` is a generalized Cartan matrix.

## Main results

* `Matrix.IsGeneralizedCartan.transpose`, `Matrix.IsGeneralizedCartan.submatrix`,
  `Matrix.IsGeneralizedCartan.reindex`, `Matrix.IsGeneralizedCartan.fromBlocks`: closure under
  transposition, injective restriction of the index set, reindexing, and block-diagonal direct sums.
* `Matrix.IsFiniteCartan.isGeneralizedCartan`: every finite-type Cartan matrix is a generalized
  Cartan matrix.
* `CartanMatrix.isGeneralizedCartan_A`, `CartanMatrix.isGeneralizedCartan_B`,
  `CartanMatrix.isGeneralizedCartan_C`, `CartanMatrix.isGeneralizedCartan_D`,
  `CartanMatrix.isGeneralizedCartan_E`, `CartanMatrix.isGeneralizedCartan_F₄`,
  `CartanMatrix.isGeneralizedCartan_G₂`: the classical, exceptional, and extended `Eₙ` families are
  generalized Cartan matrices.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press,
  1990, §1.1.
-/

public section

namespace Matrix

/-- A **generalized Cartan matrix** on an index type `I` is an integral matrix `A` with diagonal
entries `2`, nonpositive off-diagonal entries, and symmetric zero pattern (`A i j = 0 ↔ A j i = 0`).
No finiteness, decidability, or symmetrizability assumption is imposed. -/
structure IsGeneralizedCartan {I : Type*} (A : Matrix I I ℤ) : Prop where
  /-- Every diagonal entry is `2`. -/
  diag : ∀ i, A i i = 2
  /-- Off-diagonal entries are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- An entry vanishes if and only if the symmetrically placed entry vanishes. -/
  zero_comm : ∀ i j, A i j = 0 ↔ A j i = 0

/-- Every matrix on an empty index type is vacuously a generalized Cartan matrix. -/
theorem isGeneralizedCartan_of_isEmpty {I : Type*} [IsEmpty I] (A : Matrix I I ℤ) :
    A.IsGeneralizedCartan where
  diag := isEmptyElim
  offDiag_nonpos := isEmptyElim
  zero_comm := isEmptyElim

namespace IsGeneralizedCartan

variable {I J : Type*} {A : Matrix I I ℤ}

/-- A nonzero off-diagonal entry of a generalized Cartan matrix is strictly negative. -/
theorem offDiag_neg_of_ne_zero (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j)
    (h0 : A i j ≠ 0) : A i j < 0 :=
  lt_of_le_of_ne (hA.offDiag_nonpos i j hij) h0

/-- Nonvanishing of entries of a generalized Cartan matrix is symmetric across the diagonal. -/
theorem ne_zero_comm (hA : A.IsGeneralizedCartan) (i j : I) :
    A i j ≠ 0 ↔ A j i ≠ 0 :=
  not_congr (hA.zero_comm i j)

/-- Symmetrically placed entries of a generalized Cartan matrix have nonnegative product. -/
theorem mul_nonneg_of_symm (hA : A.IsGeneralizedCartan) (i j : I) :
    0 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

/-- At a diagonal position, the truncated Serre exponent `(-A i i).toNat` vanishes. -/
@[simp]
theorem toNat_neg_self (hA : A.IsGeneralizedCartan) (i : I) :
    (-A i i).toNat = 0 := by
  simp [hA.diag]

/-- At distinct nodes, `(-A i j).toNat` casts back to `-A i j` because `A i j ≤ 0`. -/
theorem natCast_toNat_neg_of_ne (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j) :
    ((-A i j).toNat : ℤ) = -A i j :=
  Int.toNat_of_nonneg (neg_nonneg.mpr (hA.offDiag_nonpos i j hij))

/-- At distinct nodes with a nonzero entry, the Serre exponent `(-A i j).toNat` is positive. -/
theorem toNat_neg_pos_of_ne_of_ne_zero (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j)
    (h0 : A i j ≠ 0) : 0 < (-A i j).toNat :=
  Int.pos_iff_toNat_pos.mp (neg_pos.mpr (hA.offDiag_neg_of_ne_zero hij h0))

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose (hA : A.IsGeneralizedCartan) : Aᵀ.IsGeneralizedCartan where
  diag i := hA.diag i
  offDiag_nonpos i j hij := hA.offDiag_nonpos j i hij.symm
  zero_comm i j := hA.zero_comm j i

/-- Transposition preserves the generalized Cartan matrix predicate. -/
@[simp]
protected theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h => h.transpose, IsGeneralizedCartan.transpose⟩

/-- Restricting a generalized Cartan matrix along an injective map of indices gives a generalized
Cartan matrix. For a subset inclusion this is the Cartan matrix of a Levi subdiagram. -/
protected theorem submatrix (hA : A.IsGeneralizedCartan) {f : J → I} (hf : Function.Injective f) :
    (A.submatrix f f).IsGeneralizedCartan where
  diag i := hA.diag (f i)
  offDiag_nonpos i j hij := hA.offDiag_nonpos (f i) (f j) (hf.ne hij)
  zero_comm i j := hA.zero_comm (f i) (f j)

/-- Reindexing a generalized Cartan matrix along a bijection gives a generalized Cartan matrix. -/
protected theorem reindex (hA : A.IsGeneralizedCartan) (e : I ≃ J) :
    (A.reindex e e).IsGeneralizedCartan :=
  hA.submatrix e.symm.injective

/-- Reindexing along a bijection preserves the generalized Cartan matrix predicate. -/
protected theorem reindex_iff (e : I ≃ J) :
    (A.reindex e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h => by simpa using h.reindex e.symm, fun h => h.reindex e⟩

/-- The block-diagonal direct sum of two generalized Cartan matrices is a generalized Cartan
matrix. -/
protected theorem fromBlocks {B : Matrix J J ℤ} (hA : A.IsGeneralizedCartan)
    (hB : B.IsGeneralizedCartan) :
    (Matrix.fromBlocks A 0 0 B).IsGeneralizedCartan where
  diag := by rintro (i | i) <;> simp [hA.diag, hB.diag]
  offDiag_nonpos := by
    rintro (i | i) (j | j) hij
    · exact hA.offDiag_nonpos i j fun h => hij (congrArg Sum.inl h)
    · simp
    · simp
    · exact hB.offDiag_nonpos i j fun h => hij (congrArg Sum.inr h)
  zero_comm := by rintro (i | i) (j | j) <;> simp [hA.zero_comm, hB.zero_comm]

/-- A block-diagonal matrix `fromBlocks A 0 0 B` is a generalized Cartan matrix if and only if both
diagonal blocks are. -/
@[simp]
protected theorem fromBlocks_zero_iff {B : Matrix J J ℤ} :
    (Matrix.fromBlocks A 0 0 B).IsGeneralizedCartan ↔
      A.IsGeneralizedCartan ∧ B.IsGeneralizedCartan :=
  ⟨fun h => ⟨h.submatrix Sum.inl_injective, h.submatrix Sum.inr_injective⟩,
    fun ⟨hA, hB⟩ => hA.fromBlocks hB⟩

/-- Every symmetric integer matrix with diagonal `2` and nonpositive off-diagonal entries is a
generalized Cartan matrix. -/
theorem of_isSymm (hA : A.IsSymm) (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : A.IsGeneralizedCartan where
  diag := hdiag
  offDiag_nonpos := hoff
  zero_comm i j := by rw [hA.apply i j]

end IsGeneralizedCartan

/-- Every finite-type Cartan matrix is a generalized Cartan matrix. -/
theorem IsFiniteCartan.isGeneralizedCartan {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan) : M.IsGeneralizedCartan where
  diag := hM.diag
  offDiag_nonpos := hM.offDiag_nonpos
  zero_comm := hM.zero_comm

end Matrix

namespace CartanMatrix

/-- `CartanMatrix.A n` is a generalized Cartan matrix for every `n`. -/
theorem isGeneralizedCartan_A (n : ℕ) : (A n).IsGeneralizedCartan :=
  Matrix.IsGeneralizedCartan.of_isSymm (A_isSymm n)
    (fun i => congrFun (A_diag n) i) (A_apply_le_zero_of_ne n)

/-- `CartanMatrix.B n` is a generalized Cartan matrix for every `n`. -/
theorem isGeneralizedCartan_B (n : ℕ) : (B n).IsGeneralizedCartan where
  diag := B_diag n
  offDiag_nonpos := B_off_diag_nonpos n
  zero_comm i j := by
    simp only [B, Matrix.of_apply, Fin.ext_iff]
    grind

/-- `CartanMatrix.C n` is a generalized Cartan matrix for every `n`. -/
theorem isGeneralizedCartan_C (n : ℕ) : (C n).IsGeneralizedCartan := by
  rw [← B_transpose]
  exact (isGeneralizedCartan_B n).transpose

/-- `CartanMatrix.D n` is a generalized Cartan matrix for every `n`. -/
theorem isGeneralizedCartan_D (n : ℕ) : (D n).IsGeneralizedCartan :=
  Matrix.IsGeneralizedCartan.of_isSymm (D_isSymm n) (D_diag n) (D_off_diag_nonpos n)

/-- The extended family `CartanMatrix.E n` is a generalized Cartan matrix for every `n`, including
affine `E 9` and hyperbolic `E 10`. -/
theorem isGeneralizedCartan_E (n : ℕ) : (E n).IsGeneralizedCartan :=
  Matrix.IsGeneralizedCartan.of_isSymm
    (Matrix.IsSymm.ext fun i j => by simp only [E, Matrix.of_apply, Fin.ext_iff]; grind)
    (fun i => by simp [E])
    (fun i j hij => by simp only [E, Matrix.of_apply, hij, ↓reduceIte]; split_ifs <;> omega)

/-- `CartanMatrix.F₄` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_F₄ : F₄.IsGeneralizedCartan where
  diag i := by fin_cases i <;> decide
  offDiag_nonpos i j := by fin_cases i <;> fin_cases j <;> decide
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

/-- `CartanMatrix.G₂` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_G₂ : G₂.IsGeneralizedCartan where
  diag i := by fin_cases i <;> decide
  offDiag_nonpos i j := by fin_cases i <;> fin_cases j <;> decide
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

end CartanMatrix
