/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors.Basic
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Unique
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Uniqueness of alternating elementary divisors

This file proves uniqueness up to associates of the alternating elementary divisors of an
alternating block matrix `[[0, D], [-D, 0]]` (both fixed-size and padded with a zero block) over
any commutative cancellative ring `R`, by interleaving `Sum.elim (Sum.elim d d) 0` into a
divisibility chain `[d₀, d₀, d₁, d₁, ..., d_{r-1}, d_{r-1}, 0, ...]` and reducing to Smith
normal form uniqueness (`Matrix.associated_of_mul_diagonal_mul_eq_diagonal`).

## Main results

* `Matrix.associated_of_mul_fromBlocks_diagonal_mul_eq`: uniqueness of elementary divisors for
  equivalent alternating block matrices of fixed size `2g` (zeros allowed in `d₁, d₂`).
* `Matrix.exists_eq_and_associated_of_mul_fromBlocks_zero_mul_eq`: uniqueness of rank `r`, nullity
  `k`, and nonzero elementary divisors for equivalent padded singular alternating block matrices.
* `LinearMap.BilinForm.associated_of_toMatrix_eq_fromBlocks_diagonal`: bilinear-form uniqueness for
  two bases of the same size `Fin g ⊕ Fin g` over any `[CommRing R] [IsCancelMulZero R]`.
* `LinearMap.BilinForm.exists_eq_and_associated_of_toMatrix_eq_fromBlocks_zero`: bilinear-form
  uniqueness for singular normal forms over any `[CommRing R] [IsDomain R]`.
-/

public section

namespace Matrix

section Interleave

/-- Interleaves `Fin r ⊕ Fin r` into the first `2 * r` entries of `Fin (2 * r + k)` as consecutive
pairs `(2 * i, 2 * i + 1)`, followed by `Fin k` at positions `2 * r + j`. Under this reindexing,
`Sum.elim (Sum.elim d d) 0` becomes a divisibility chain whenever `d` is one. -/
private def interleaveEquiv (r k : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin k ≃ Fin (2 * r + k) where
  toFun
    | Sum.inl (Sum.inl i) => ⟨2 * i.val, by omega⟩
    | Sum.inl (Sum.inr i) => ⟨2 * i.val + 1, by omega⟩
    | Sum.inr j => ⟨2 * r + j.val, by omega⟩
  invFun m :=
    if h : m.val < 2 * r then
      if m.val % 2 = 0 then Sum.inl (Sum.inl ⟨m.val / 2, by omega⟩)
      else Sum.inl (Sum.inr ⟨m.val / 2, by omega⟩)
    else Sum.inr ⟨m.val - 2 * r, by omega⟩
  left_inv x := by
    rcases x with (i | i) | j
    · have hlt : 2 * i.val < 2 * r := by omega
      simp only [hlt, ↓reduceDIte, Nat.mul_mod_right, ↓reduceIte]
      have h : (2 * i.val) / 2 = i.val := by omega
      exact congrArg (Sum.inl ∘ Sum.inl) (Fin.ext h)
    · have hlt : 2 * i.val + 1 < 2 * r := by omega
      have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
      simp only [hlt, ↓reduceDIte, hmod, ↓reduceIte]
      have h : (2 * i.val + 1) / 2 = i.val := by omega
      exact congrArg (Sum.inl ∘ Sum.inr) (Fin.ext h)
    · have hge : ¬(2 * r + j.val < 2 * r) := by omega
      simp only [hge, ↓reduceDIte]
      have h : 2 * r + j.val - 2 * r = j.val := by omega
      exact congrArg Sum.inr (Fin.ext h)
  right_inv m := by
    by_cases h : m.val < 2 * r
    · by_cases hp : m.val % 2 = 0
      · simp only [h, hp, ↓reduceDIte, ↓reduceIte]
        exact Fin.ext (by dsimp; omega)
      · simp only [h, hp, ↓reduceDIte, ↓reduceIte]
        exact Fin.ext (by dsimp; omega)
    · simp only [h, ↓reduceDIte]
      exact Fin.ext (by dsimp; omega)

/-- The interleaved divisibility chain `[d 0, d 0, d 1, d 1, ..., d (r - 1), d (r - 1), 0, ...]`
attached to `d : Fin r → R` and nullity `k`. -/
private def interleavedChain {R : Type*} [Zero R] {r : ℕ} (k : ℕ) (d : Fin r → R) :
    Fin (2 * r + k) → R :=
  fun m ↦ if h : m.val < 2 * r then d ⟨m.val / 2, by omega⟩ else 0

private lemma interleavedChain_comp_interleaveEquiv {R : Type*} [Zero R] {r : ℕ} (k : ℕ)
    (d : Fin r → R) (x : (Fin r ⊕ Fin r) ⊕ Fin k) :
    interleavedChain k d (interleaveEquiv r k x) = Sum.elim (Sum.elim d d) 0 x := by
  rcases x with (i | i) | j <;> simp only [interleavedChain, interleaveEquiv, Equiv.coe_fn_mk,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
  · have hlt : 2 * i.val < 2 * r := by omega
    simp only [hlt, ↓reduceDIte]
    have h : (2 * i.val) / 2 = i.val := by omega
    exact congrArg d (Fin.ext h)
  · have hlt : 2 * i.val + 1 < 2 * r := by omega
    simp only [hlt, ↓reduceDIte]
    have h : (2 * i.val + 1) / 2 = i.val := by omega
    exact congrArg d (Fin.ext h)
  · have hge : ¬(2 * r + j.val < 2 * r) := by omega
    simp only [hge, ↓reduceDIte]

private lemma interleavedChain_dvd {R : Type*} [CommRing R] {r : ℕ} (k : ℕ) {d : Fin r → R}
    (hd : ∀ ⦃i j : Fin r⦄, i ≤ j → d i ∣ d j)
    ⦃i j : Fin (2 * r + k)⦄ (hij : i ≤ j) :
    interleavedChain k d i ∣ interleavedChain k d j := by
  by_cases hj : j.val < 2 * r
  · have hi : i.val < 2 * r := lt_of_le_of_lt hij hj
    simp only [interleavedChain, hi, hj, ↓reduceDIte]
    exact hd (Fin.le_def.mpr (Nat.div_le_div_right (Fin.val_le_of_le hij)))
  · simp only [interleavedChain, hj, ↓reduceDIte, dvd_zero]

private lemma reindex_mul_eq {m n R : Type*} [Fintype m] [Fintype n] [CommRing R] (e : m ≃ n)
    (A B : Matrix m m R) :
    reindex e e (A * B) = reindex e e A * reindex e e B := by
  classical
  exact (reindexRingEquiv R e).map_mul A B

private lemma reindex_one_eq {m n R : Type*} [DecidableEq m] [DecidableEq n] [CommRing R]
    (e : m ≃ n) :
    reindex e e (1 : Matrix m m R) = 1 := by
  ext i j
  simp [reindex_apply, submatrix_apply, Matrix.one_apply]

private lemma leftMul_fromBlocks_zero_eq_diagonal {R : Type*} [CommRing R] (r k : ℕ)
    (d : Fin r → R) :
    fromBlocks (Matrix.J (Fin r) R) 0 0 (1 : Matrix (Fin k) (Fin k) R) *
        fromBlocks (fromBlocks 0 (diagonal d) (-diagonal d) 0) 0 0 0 =
      diagonal (Sum.elim (Sum.elim d d) 0) := by
  rw [fromBlocks_multiply, J_mul_fromBlocks_diagonal]
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul]
  rw [← diagonal_zero']
  exact fromBlocks_diagonal (Sum.elim d d) (0 : Fin k → R)

private lemma reindex_leftMul_fromBlocks_zero {R : Type*} [CommRing R] {r k n : ℕ}
    (hdim : 2 * r + k = n) (d : Fin r → R) :
    let e : (Fin r ⊕ Fin r) ⊕ Fin k ≃ Fin n :=
      (interleaveEquiv r k).trans (Fin.castOrderIso hdim).toEquiv
    reindex e e (fromBlocks (Matrix.J (Fin r) R) 0 0 (1 : Matrix (Fin k) (Fin k) R)) *
        reindex e e (fromBlocks (fromBlocks 0 (diagonal d) (-diagonal d) 0) 0 0 0) =
      diagonal (interleavedChain k d ∘ (Fin.castOrderIso hdim).symm) := by
  intro e
  rw [← reindex_mul_eq, leftMul_fromBlocks_zero_eq_diagonal]
  ext i j
  rw [reindex_apply, submatrix_apply]
  obtain ⟨x, rfl⟩ := e.surjective i
  obtain ⟨y, rfl⟩ := e.surjective j
  simp only [Equiv.symm_apply_apply, diagonal_apply, EmbeddingLike.apply_eq_iff_eq]
  split_ifs with hxy
  · subst hxy
    have hx := interleavedChain_comp_interleaveEquiv k d x
    simp only [Function.comp_apply, e, Equiv.trans_apply, RelIso.coe_fn_toEquiv,
      OrderIso.symm_apply_apply]
    exact hx.symm
  · rfl

/-- Value of `(Fin.castOrderIso h).symm m` equals `m.val`. -/
private lemma val_castOrderIso_symm {a b : ℕ} (h : a = b) (m : Fin b) :
    ((Fin.castOrderIso h).symm m).val = m.val :=
  rfl

/-- Permutation matrix `P i j = (1 : Matrix n n R) (σ i) j` built without `CStarAlgebra`
imports. -/
private def permMat {n R : Type*} [DecidableEq n] [CommRing R] (σ : Equiv.Perm n) :
    Matrix n n R :=
  (1 : Matrix n n R).submatrix σ id

private lemma permMat_mul_transpose {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (σ : Equiv.Perm n) :
    permMat (R := R) σ * (permMat (R := R) σ)ᵀ = 1 := by
  ext i j
  simp [permMat, Matrix.mul_apply, Matrix.one_apply]

private lemma isUnit_det_permMat {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (σ : Equiv.Perm n) : IsUnit (permMat (R := R) σ).det :=
  isUnit_det_of_right_inverse (permMat_mul_transpose σ)

private lemma permMat_mul_reindex_mul_transpose {ι n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (e f : ι ≃ n) (M : Matrix ι ι R) :
    permMat (R := R) (e.symm.trans f) * reindex f f M *
        (permMat (R := R) (e.symm.trans f))ᵀ = reindex e e M := by
  ext i j
  simp [permMat, Matrix.mul_apply, Matrix.one_apply, reindex_apply, submatrix_apply]

private lemma reindex_J_diagonal {R : Type*} [CommRing R] {g : ℕ} (d : Fin g → R) :
    let e : Fin g ⊕ Fin g ≃ Fin (2 * g) :=
      (Equiv.sumEmpty (Fin g ⊕ Fin g) (Fin 0)).symm.trans (interleaveEquiv g 0)
    reindex e e (Matrix.J (Fin g) R) *
        reindex e e (fromBlocks 0 (diagonal d) (-diagonal d) 0) =
      diagonal (interleavedChain 0 d) := by
  intro e
  rw [← reindex_mul_eq, J_mul_fromBlocks_diagonal]
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, diagonal_apply,
    EmbeddingLike.apply_eq_iff_eq]
  split_ifs with hxy
  · subst hxy
    simpa [e, Equiv.sumEmpty] using (interleavedChain_comp_interleaveEquiv 0 d (Sum.inl x)).symm
  · rfl

end Interleave

section BlockUniqueness

variable {R : Type*} [CommRing R] [IsCancelMulZero R]

/-- **Uniqueness of alternating elementary divisors for equivalent block matrices (fixed size).**
If `L * [[0, D₁], [-D₁, 0]] * Q = [[0, D₂], [-D₂, 0]]` with `det L` and `det Q` units and
divisibility chains `d₁`, `d₂` (zeros allowed), then `d₁ i` and `d₂ i` are associated for
every `i`. -/
theorem associated_of_mul_fromBlocks_diagonal_mul_eq {g : ℕ} {d₁ d₂ : Fin g → R}
    (hd₁ : ∀ ⦃i j : Fin g⦄, i ≤ j → d₁ i ∣ d₁ j)
    (hd₂ : ∀ ⦃i j : Fin g⦄, i ≤ j → d₂ i ∣ d₂ j)
    {L Q : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R} (hL : IsUnit L.det) (hQ : IsUnit Q.det)
    (h : L * fromBlocks 0 (diagonal d₁) (-diagonal d₁) 0 * Q =
      fromBlocks 0 (diagonal d₂) (-diagonal d₂) 0) (i : Fin g) :
    Associated (d₁ i) (d₂ i) := by
  let e : Fin g ⊕ Fin g ≃ Fin (2 * g) :=
    (Equiv.sumEmpty (Fin g ⊕ Fin g) (Fin 0)).symm.trans (interleaveEquiv g 0)
  let L' : Matrix (Fin (2 * g)) (Fin (2 * g)) R :=
    reindex e e (Matrix.J (Fin g) R) * reindex e e L * reindex e e (-Matrix.J (Fin g) R)
  have hL' : IsUnit L'.det := by
    simp only [L', det_mul, det_reindex_self, det_J, det_neg, Fintype.card_sum, Fintype.card_fin]
    have hpow : (-1 : R) ^ (g + g) = 1 := by
      rw [← two_mul, pow_mul, neg_one_sq, one_pow]
    rwa [hpow, one_mul, one_mul, mul_one]
  have hQ' : IsUnit (reindex e e Q).det := by rwa [det_reindex_self]
  have hmul : L' * diagonal (interleavedChain 0 d₁) * reindex e e Q =
      diagonal (interleavedChain 0 d₂) := by
    rw [← reindex_J_diagonal d₁, ← reindex_J_diagonal d₂]
    calc
      L' * (reindex e e (Matrix.J (Fin g) R) *
          reindex e e (fromBlocks 0 (diagonal d₁) (-diagonal d₁) 0)) * reindex e e Q
        = reindex e e (Matrix.J (Fin g) R) * reindex e e L *
            (reindex e e (-Matrix.J (Fin g) R) * reindex e e (Matrix.J (Fin g) R)) *
            reindex e e (fromBlocks 0 (diagonal d₁) (-diagonal d₁) 0) * reindex e e Q := by
          simp only [L', Matrix.mul_assoc]
      _ = reindex e e (Matrix.J (Fin g) R) *
            reindex e e (L * fromBlocks 0 (diagonal d₁) (-diagonal d₁) 0 * Q) := by
          rw [← reindex_mul_eq e (-Matrix.J (Fin g) R) (Matrix.J (Fin g) R), neg_J_mul_J,
            reindex_one_eq, Matrix.mul_one]
          simp only [reindex_mul_eq, Matrix.mul_assoc]
      _ = reindex e e (Matrix.J (Fin g) R) *
            reindex e e (fromBlocks 0 (diagonal d₂) (-diagonal d₂) 0) := by rw [h]
  have hassoc := associated_of_mul_diagonal_mul_eq_diagonal
    (interleavedChain_dvd 0 hd₁) (interleavedChain_dvd 0 hd₂) hL' hQ' hmul
    ⟨2 * i.val, by omega⟩
  have hlt : 2 * i.val < 2 * g := by omega
  have hdiv : (2 * i.val) / 2 = i.val := by omega
  simpa [interleavedChain, hlt, Fin.mk_eq_mk, hdiv] using hassoc

omit [IsCancelMulZero R] in
/-- Reduction of two equivalent padded singular alternating block matrices to equivalent interleaved
diagonal matrices. -/
private lemma exists_unit_mul_interleaved_eq {r₁ k₁ r₂ k₂ n : ℕ}
    (hn₁ : 2 * r₁ + k₁ = n) (hn₂ : 2 * r₂ + k₂ = n)
    {d₁ : Fin r₁ → R} {d₂ : Fin r₂ → R}
    (e₁ : (Fin r₁ ⊕ Fin r₁) ⊕ Fin k₁ ≃ Fin n)
    (e₂ : (Fin r₂ ⊕ Fin r₂) ⊕ Fin k₂ ≃ Fin n)
    {L Q : Matrix (Fin n) (Fin n) R} (hL : IsUnit L.det) (hQ : IsUnit Q.det)
    (h : L * reindex e₁ e₁
          (fromBlocks (fromBlocks 0 (diagonal d₁) (-diagonal d₁) 0) 0 0 0) * Q =
        reindex e₂ e₂
          (fromBlocks (fromBlocks 0 (diagonal d₂) (-diagonal d₂) 0) 0 0 0)) :
    ∃ L' Q' : Matrix (Fin n) (Fin n) R, IsUnit L'.det ∧ IsUnit Q'.det ∧
      L' * diagonal (interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) * Q' =
        diagonal (interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) := by
  let f₁ := (interleaveEquiv r₁ k₁).trans (Fin.castOrderIso hn₁).toEquiv
  let f₂ := (interleaveEquiv r₂ k₂).trans (Fin.castOrderIso hn₂).toEquiv
  let A₁ := fromBlocks (fromBlocks (0 : Matrix (Fin r₁) (Fin r₁) R)
    (diagonal d₁) (-diagonal d₁) 0) 0 0 (0 : Matrix (Fin k₁) (Fin k₁) R)
  let A₂ := fromBlocks (fromBlocks (0 : Matrix (Fin r₂) (Fin r₂) R)
    (diagonal d₂) (-diagonal d₂) 0) 0 0 (0 : Matrix (Fin k₂) (Fin k₂) R)
  let J₁ := reindex f₁ f₁
    (fromBlocks (Matrix.J (Fin r₁) R) 0 0 (1 : Matrix (Fin k₁) (Fin k₁) R))
  let J₁' := reindex f₁ f₁
    (fromBlocks (-Matrix.J (Fin r₁) R) 0 0 (1 : Matrix (Fin k₁) (Fin k₁) R))
  let J₂ := reindex f₂ f₂
    (fromBlocks (Matrix.J (Fin r₂) R) 0 0 (1 : Matrix (Fin k₂) (Fin k₂) R))
  let P₁ : Matrix (Fin n) (Fin n) R := permMat (e₁.symm.trans f₁)
  let P₂ : Matrix (Fin n) (Fin n) R := permMat (e₂.symm.trans f₂)
  have hJ₁J₁' : J₁' * J₁ = 1 := by
    rw [← reindex_mul_eq, fromBlocks_multiply]
    simp only [neg_J_mul_J, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, fromBlocks_one]
    exact reindex_one_eq f₁
  have hJ₂_det : IsUnit J₂.det := by simp [J₂, det_fromBlocks_zero₂₁]
  have hP₂inv : P₂ᵀ * P₂ = 1 :=
    mul_eq_one_comm.mp (permMat_mul_transpose (R := R) (e₂.symm.trans f₂))
  refine ⟨J₂ * P₂ᵀ * L * P₁ * J₁', P₁ᵀ * Q * P₂, ?_, ?_, ?_⟩
  · simp only [det_mul, det_transpose]
    exact (((hJ₂_det.mul (isUnit_det_permMat _)).mul hL).mul
      (isUnit_det_permMat _)).mul (isUnit_det_of_right_inverse hJ₁J₁')
  · simp only [det_mul, det_transpose]
    exact ((isUnit_det_permMat _).mul hQ).mul (isUnit_det_permMat _)
  · have hM₁ : J₁ * reindex f₁ f₁ A₁ =
        diagonal (interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) :=
      reindex_leftMul_fromBlocks_zero hn₁ d₁
    have hM₂ : J₂ * reindex f₂ f₂ A₂ =
        diagonal (interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) :=
      reindex_leftMul_fromBlocks_zero hn₂ d₂
    have h1 : P₁ * reindex f₁ f₁ A₁ * P₁ᵀ = reindex e₁ e₁ A₁ :=
      permMat_mul_reindex_mul_transpose (R := R) e₁ f₁ A₁
    have h2 : P₂ * reindex f₂ f₂ A₂ * P₂ᵀ = reindex e₂ e₂ A₂ :=
      permMat_mul_reindex_mul_transpose (R := R) e₂ f₂ A₂
    rw [← hM₁, ← hM₂]
    calc
      (J₂ * P₂ᵀ * L * P₁ * J₁') * (J₁ * reindex f₁ f₁ A₁) * (P₁ᵀ * Q * P₂)
        = J₂ * P₂ᵀ * L * P₁ * (J₁' * J₁) * reindex f₁ f₁ A₁ * P₁ᵀ * Q * P₂ := by
          simp only [Matrix.mul_assoc]
      _ = J₂ * P₂ᵀ * (L * (P₁ * reindex f₁ f₁ A₁ * P₁ᵀ) * Q) * P₂ := by
          rw [hJ₁J₁']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = J₂ * P₂ᵀ * (P₂ * reindex f₂ f₂ A₂ * P₂ᵀ) * P₂ := by rw [h1, h, ← h2]
      _ = J₂ * ((P₂ᵀ * P₂) * reindex f₂ f₂ A₂ * (P₂ᵀ * P₂)) := by
          simp only [Matrix.mul_assoc]
      _ = J₂ * reindex f₂ f₂ A₂ := by rw [hP₂inv, Matrix.one_mul, Matrix.mul_one]

omit [IsCancelMulZero R] in
/-- Extract equality of ranks `r₁ = r₂` from pointwise association of two interleaved nonzero
chains. -/
private lemma rank_eq_of_associated_interleavedChain {r₁ k₁ r₂ k₂ n : ℕ}
    (hn₁ : 2 * r₁ + k₁ = n) (hn₂ : 2 * r₂ + k₂ = n)
    {d₁ : Fin r₁ → R} {d₂ : Fin r₂ → R}
    (hd₁₀ : ∀ i, d₁ i ≠ 0) (hd₂₀ : ∀ i, d₂ i ≠ 0)
    (hassoc : ∀ m : Fin n,
      Associated ((interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) m)
        ((interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) m)) :
    r₁ = r₂ := by
  have hzero : ∀ m : Fin n,
      ((interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) m = 0 ↔
        (interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) m = 0) := fun m ↦ by
    obtain ⟨u, hu⟩ := hassoc m
    constructor <;> intro hm
    · rw [hm, zero_mul] at hu; exact hu.symm
    · exact u.isUnit.mul_left_eq_zero.mp (hu.trans hm)
  have hne₁ : ∀ m : Fin n,
      (interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) m ≠ 0 ↔ m.val < 2 * r₁ :=
    fun m ↦ by
      simp only [Function.comp_apply, interleavedChain, val_castOrderIso_symm]
      by_cases hm : m.val < 2 * r₁ <;> simp [hm, hd₁₀]
  have hne₂ : ∀ m : Fin n,
      (interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) m ≠ 0 ↔ m.val < 2 * r₂ :=
    fun m ↦ by
      simp only [Function.comp_apply, interleavedChain, val_castOrderIso_symm]
      by_cases hm : m.val < 2 * r₂ <;> simp [hm, hd₂₀]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm : 2 * r₁ < n := by omega
    have h1 := (hne₁ ⟨2 * r₁, hm⟩).not.mpr (by dsimp; omega)
    have h2 := (hne₂ ⟨2 * r₁, hm⟩).mpr (by dsimp; omega)
    exact h2 ((hzero ⟨2 * r₁, hm⟩).mp (not_not.mp h1))
  · have hm : 2 * r₂ < n := by omega
    have h1 := (hne₁ ⟨2 * r₂, hm⟩).mpr (by dsimp; omega)
    have h2 := (hne₂ ⟨2 * r₂, hm⟩).not.mpr (by dsimp; omega)
    exact h1 ((hzero ⟨2 * r₂, hm⟩).mpr (not_not.mp h2))

/-- **Uniqueness of alternating elementary divisors for equivalent singular block matrices.**
Given two nonzero divisibility chains `d₁ : Fin r₁ → R` and `d₂ : Fin r₂ → R` padded by `k₁`
and `k₂` zero rows and columns to the same size `n`, if the resulting reindexed block matrices
are related by unimodular row and column transformations, then `r₁ = r₂`, `k₁ = k₂`, and
`d₁ i` is associated to `d₂ (i.cast hr)` for every `i`. -/
theorem exists_eq_and_associated_of_mul_fromBlocks_zero_mul_eq {r₁ k₁ r₂ k₂ n : ℕ}
    {d₁ : Fin r₁ → R} {d₂ : Fin r₂ → R}
    (hd₁₀ : ∀ i, d₁ i ≠ 0) (hd₂₀ : ∀ i, d₂ i ≠ 0)
    (hd₁ : ∀ ⦃i j : Fin r₁⦄, i ≤ j → d₁ i ∣ d₁ j)
    (hd₂ : ∀ ⦃i j : Fin r₂⦄, i ≤ j → d₂ i ∣ d₂ j)
    (e₁ : (Fin r₁ ⊕ Fin r₁) ⊕ Fin k₁ ≃ Fin n)
    (e₂ : (Fin r₂ ⊕ Fin r₂) ⊕ Fin k₂ ≃ Fin n)
    {L Q : Matrix (Fin n) (Fin n) R} (hL : IsUnit L.det) (hQ : IsUnit Q.det)
    (h : L * reindex e₁ e₁
          (fromBlocks (fromBlocks 0 (diagonal d₁) (-diagonal d₁) 0) 0 0 0) * Q =
        reindex e₂ e₂
          (fromBlocks (fromBlocks 0 (diagonal d₂) (-diagonal d₂) 0) 0 0 0)) :
    ∃ (hr : r₁ = r₂), k₁ = k₂ ∧
      ∀ i : Fin r₁, Associated (d₁ i) (d₂ (Fin.cast hr i)) := by
  have hn₁ : 2 * r₁ + k₁ = n := by
    have := Fintype.card_congr e₁
    simp only [Fintype.card_sum, Fintype.card_fin] at this; omega
  have hn₂ : 2 * r₂ + k₂ = n := by
    have := Fintype.card_congr e₂
    simp only [Fintype.card_sum, Fintype.card_fin] at this; omega
  obtain ⟨L', Q', hL', hQ', hmul⟩ :=
    exists_unit_mul_interleaved_eq hn₁ hn₂ e₁ e₂ hL hQ h
  have hs₁ : ∀ ⦃i j : Fin n⦄, i ≤ j →
      (interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) i ∣
        (interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) j := fun _ _ hij ↦
    interleavedChain_dvd k₁ hd₁ ((Fin.castOrderIso hn₁).symm.monotone hij)
  have hs₂ : ∀ ⦃i j : Fin n⦄, i ≤ j →
      (interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) i ∣
        (interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) j := fun _ _ hij ↦
    interleavedChain_dvd k₂ hd₂ ((Fin.castOrderIso hn₂).symm.monotone hij)
  have hassoc := associated_of_mul_diagonal_mul_eq_diagonal hs₁ hs₂ hL' hQ' hmul
  have hr : r₁ = r₂ :=
    rank_eq_of_associated_interleavedChain hn₁ hn₂ hd₁₀ hd₂₀ hassoc
  refine ⟨hr, by omega, fun i ↦ ?_⟩
  have hmem := hassoc ⟨2 * i.val, by omega⟩
  have hlt₁ : 2 * i.val < 2 * r₁ := by omega
  have hlt₂ : 2 * i.val < 2 * r₂ := by omega
  have heq₁ :
      (interleavedChain k₁ d₁ ∘ (Fin.castOrderIso hn₁).symm) ⟨2 * i.val, by omega⟩ =
        d₁ i := by
    simp only [Function.comp_apply, interleavedChain, val_castOrderIso_symm, hlt₁, ↓reduceDIte]
    exact congrArg d₁ (Fin.ext (by dsimp; omega))
  have heq₂ :
      (interleavedChain k₂ d₂ ∘ (Fin.castOrderIso hn₂).symm) ⟨2 * i.val, by omega⟩ =
        d₂ (Fin.cast hr i) := by
    simp only [Function.comp_apply, interleavedChain, val_castOrderIso_symm, hlt₂, ↓reduceDIte]
    exact congrArg d₂ (Fin.ext (by dsimp; omega))
  rwa [heq₁, heq₂] at hmem

end BlockUniqueness

end Matrix

namespace LinearMap.BilinForm

open Module
open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Uniqueness of alternating elementary divisors (same size, possibly singular).** Over any
commutative cancellative ring, if two bases indexed by `Fin g ⊕ Fin g` put `B` in alternating
block form with divisibility chains `d₁` and `d₂`, then `d₁ i` and `d₂ i` are associated for
every `i`. Zeros are allowed in `d₁` and `d₂`. -/
theorem associated_of_toMatrix_eq_fromBlocks_diagonal [IsCancelMulZero R]
    {B : BilinForm R M} {g : ℕ} {d₁ d₂ : Fin g → R}
    {b₁ b₂ : Basis (Fin g ⊕ Fin g) R M}
    (hd₁ : ∀ ⦃i j : Fin g⦄, i ≤ j → d₁ i ∣ d₁ j)
    (hd₂ : ∀ ⦃i j : Fin g⦄, i ≤ j → d₂ i ∣ d₂ j)
    (hb₁ : B.toMatrix b₁ = Matrix.fromBlocks 0 (Matrix.diagonal d₁) (-Matrix.diagonal d₁) 0)
    (hb₂ : B.toMatrix b₂ = Matrix.fromBlocks 0 (Matrix.diagonal d₂) (-Matrix.diagonal d₂) 0)
    (i : Fin g) : Associated (d₁ i) (d₂ i) := by
  have hchg := toMatrix_mul_basis_toMatrix b₁ b₂ B
  rw [hb₁, hb₂] at hchg
  have hP : IsUnit (b₁.toMatrix b₂).det :=
    Matrix.isUnit_det_of_right_inverse (b₁.toMatrix_mul_toMatrix_flip b₂)
  exact Matrix.associated_of_mul_fromBlocks_diagonal_mul_eq hd₁ hd₂
    (by rwa [Matrix.det_transpose]) hP hchg i

/-- **Uniqueness of alternating elementary divisors for singular forms.** Over an integral domain,
two alternating block bases of the same bilinear form `B` with nonzero divisibility chains
`d₁ : Fin r₁ → R` and `d₂ : Fin r₂ → R` have equal rank parameter `r₁ = r₂`, equal nullity
`k₁ = k₂`, and associated elementary divisors. -/
theorem exists_eq_and_associated_of_toMatrix_eq_fromBlocks_zero [IsDomain R]
    {B : BilinForm R M} {r₁ k₁ r₂ k₂ : ℕ} {d₁ : Fin r₁ → R} {d₂ : Fin r₂ → R}
    {b₁ : Basis ((Fin r₁ ⊕ Fin r₁) ⊕ Fin k₁) R M}
    {b₂ : Basis ((Fin r₂ ⊕ Fin r₂) ⊕ Fin k₂) R M}
    (hd₁₀ : ∀ i, d₁ i ≠ 0) (hd₂₀ : ∀ i, d₂ i ≠ 0)
    (hd₁ : ∀ ⦃i j : Fin r₁⦄, i ≤ j → d₁ i ∣ d₁ j)
    (hd₂ : ∀ ⦃i j : Fin r₂⦄, i ≤ j → d₂ i ∣ d₂ j)
    (hb₁ : B.toMatrix b₁ = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d₁) (-Matrix.diagonal d₁) 0) 0 0 0)
    (hb₂ : B.toMatrix b₂ = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d₂) (-Matrix.diagonal d₂) 0) 0 0 0) :
    ∃ (hr : r₁ = r₂), k₁ = k₂ ∧
      ∀ i : Fin r₁, Associated (d₁ i) (d₂ (Fin.cast hr i)) := by
  let n := Module.finrank R M
  have hcard₁ : Fintype.card ((Fin r₁ ⊕ Fin r₁) ⊕ Fin k₁) = n :=
    (Module.finrank_eq_card_basis b₁).symm
  have hcard₂ : Fintype.card ((Fin r₂ ⊕ Fin r₂) ⊕ Fin k₂) = n :=
    (Module.finrank_eq_card_basis b₂).symm
  let e₁ : (Fin r₁ ⊕ Fin r₁) ⊕ Fin k₁ ≃ Fin n := Fintype.equivFinOfCardEq hcard₁
  let e₂ : (Fin r₂ ⊕ Fin r₂) ⊕ Fin k₂ ≃ Fin n := Fintype.equivFinOfCardEq hcard₂
  let c₁ := b₁.reindex e₁
  let c₂ := b₂.reindex e₂
  have hchg := toMatrix_mul_basis_toMatrix c₁ c₂ B
  rw [toMatrix_reindex, toMatrix_reindex, hb₁, hb₂] at hchg
  have hP : IsUnit (c₁.toMatrix c₂).det :=
    Matrix.isUnit_det_of_right_inverse (c₁.toMatrix_mul_toMatrix_flip c₂)
  exact Matrix.exists_eq_and_associated_of_mul_fromBlocks_zero_mul_eq
    hd₁₀ hd₂₀ hd₁ hd₂ e₁ e₂ (by rwa [Matrix.det_transpose]) hP hchg

end LinearMap.BilinForm
