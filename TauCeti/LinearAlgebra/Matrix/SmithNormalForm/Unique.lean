/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.LinearAlgebra.Matrix.Divisibility
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

/-!
# Uniqueness of Smith normal form over cancellative rings

Two diagonal matrices `diagonal c` and `diagonal d` whose entries form divisibility chains
`c₀ ∣ c₁ ∣ ⋯` and `d₀ ∣ d₁ ∣ ⋯`, related by unimodular row and column operations
`L * diagonal c * Q = diagonal d` (with `det L` and `det Q` units), have associated diagonal
entries `Associated (c i) (d i)` over any commutative ring with cancellative multiplication
(`IsCancelMulZero`), including singular matrices with trailing zeros.

For each `k ≤ n`, the leading `k`-fold product divides that of the other chain by the minor
divisibility bound
`Matrix.prod_castLE_mul_prod_castLE_dvd_of_mul_diagonal_mul_diagonal_mul_eq` applied once in each
direction, so the partial products are associated. Below the first zero, cancellation via
`Associated.of_mul_left` identifies the individual entries up to units; from the first zero
onward, the divisibility chains force both entries to vanish.

This generalizes the integer uniqueness proof `Matrix.smith_normal_form_unique` in
`TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Int` (originally ported from Chris Birkbeck's
AINTLIB `LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`, Apache-2.0, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`).

## Main results

* `Matrix.prod_castLE_dvd_of_mul_diagonal_mul_eq_diagonal`: over any commutative ring, if
  `P * diagonal c * Q = diagonal d` with `c` a divisibility chain, then the product of the first
  `k` entries of `c` divides that of `d`.
* `Matrix.associated_prod_castLE_of_mul_diagonal_mul_eq_diagonal`: if `L`, `Q` have unit
  determinants and both `c` and `d` are divisibility chains, their leading `k`-fold products are
  associated.
* `Matrix.associated_of_mul_diagonal_mul_eq_diagonal`: **uniqueness of Smith normal form up to
  associates** for two equivalent chained diagonals, including singular matrices.
* `Matrix.associated_of_mul_mul_eq_diagonal`: two Smith normal forms of the same matrix `A` have
  associated invariant factors.

## References

* N. Jacobson, *Basic Algebra I*, second edition, W. H. Freeman, 1985, §3.9.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Leading products of a divisibility chain survive two-sided multiplication.** If
`P * diagonal c * Q = diagonal d` where `c` is a divisibility chain, then for every `k ≤ n` the
product of the first `k` entries of `c` divides the product of the first `k` entries of `d`.
No invertibility or cancellation hypothesis is required. -/
theorem prod_castLE_dvd_of_mul_diagonal_mul_eq_diagonal {c d : Fin n → R}
    (hc : ∀ ⦃i j : Fin n⦄, i ≤ j → c i ∣ c j) (P Q : Matrix (Fin n) (Fin n) R)
    (h : P * diagonal c * Q = diagonal d) {k : ℕ} (hk : k ≤ n) :
    (∏ j : Fin k, c (Fin.castLE hk j)) ∣ ∏ j : Fin k, d (Fin.castLE hk j) := by
  have hdiv := prod_castLE_mul_prod_castLE_dvd_of_mul_diagonal_mul_diagonal_mul_eq hc
    (c₂ := fun _ ↦ 1) (d := d) (fun _ _ _ ↦ dvd_rfl) P 1 Q
    (by rw [diagonal_one, mul_one, mul_one, h]) hk
  simpa only [Finset.prod_const_one, mul_one] using hdiv

section Cancel

variable [IsCancelMulZero R]

/-- **Leading partial products of equivalent divisibility chains are associated.** If
`L * diagonal c * Q = diagonal d` with `det L` and `det Q` units and both `c` and `d` divisibility
chains, then the products of their first `k` entries are associated for every `k ≤ n`. -/
theorem associated_prod_castLE_of_mul_diagonal_mul_eq_diagonal {c d : Fin n → R}
    (hc : ∀ ⦃i j : Fin n⦄, i ≤ j → c i ∣ c j)
    (hd : ∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j)
    {L Q : Matrix (Fin n) (Fin n) R} (hL : IsUnit L.det) (hQ : IsUnit Q.det)
    (h : L * diagonal c * Q = diagonal d) {k : ℕ} (hk : k ≤ n) :
    Associated (∏ j : Fin k, c (Fin.castLE hk j)) (∏ j : Fin k, d (Fin.castLE hk j)) := by
  have hinv : (↑(nonsingInvUnit L hL)⁻¹ : Matrix (Fin n) (Fin n) R) * diagonal d *
      (↑(nonsingInvUnit Q hQ)⁻¹ : Matrix (Fin n) (Fin n) R) = diagonal c :=
    (GeneralLinearGroup.inv_mul_mul_inv_eq_iff_mul_mul_eq
      (nonsingInvUnit L hL) (nonsingInvUnit Q hQ)).2 h
  exact associated_of_dvd_dvd
    (prod_castLE_dvd_of_mul_diagonal_mul_eq_diagonal hc L Q h hk)
    (prod_castLE_dvd_of_mul_diagonal_mul_eq_diagonal hd _ _ hinv hk)

/-- A divisibility chain vanishes at index `i` whenever its strict prefix product vanishes. -/
private lemma eq_zero_of_prod_castLE_eq_zero {a : Fin n → R}
    (ha : ∀ ⦃i j : Fin n⦄, i ≤ j → a i ∣ a j) {i : Fin n}
    (hpre : ∏ j : Fin i.val, a (Fin.castLE i.isLt.le j) = 0) : a i = 0 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hpre
    have hdvd : a (Fin.castLE i.isLt.le l) ∣ a i := ha (Fin.le_def.mpr l.isLt.le)
    rw [hl] at hdvd
    exact zero_dvd_iff.mp hdvd

/-- **Uniqueness of Smith normal form up to associates.** Over a commutative cancellative ring, two
diagonal matrices whose entries form divisibility chains and which differ by unimodular row and
column operations (`L * diagonal c * Q = diagonal d` with `det L` and `det Q` units) have
associated diagonal entries, including singular matrices with trailing zeros. -/
theorem associated_of_mul_diagonal_mul_eq_diagonal {c d : Fin n → R}
    (hc : ∀ ⦃i j : Fin n⦄, i ≤ j → c i ∣ c j)
    (hd : ∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j)
    {L Q : Matrix (Fin n) (Fin n) R} (hL : IsUnit L.det) (hQ : IsUnit Q.det)
    (h : L * diagonal c * Q = diagonal d) (i : Fin n) : Associated (c i) (d i) := by
  have hsplit : ∀ a : Fin n → R,
      ∏ j : Fin (i.val + 1), a (Fin.castLE i.isLt j) =
        (∏ j : Fin i.val, a (Fin.castLE i.isLt.le j)) * a i := fun a ↦ by
    rw [Fin.prod_univ_castSucc]
    rfl
  have hpre : Associated (∏ j : Fin i.val, c (Fin.castLE i.isLt.le j))
      (∏ j : Fin i.val, d (Fin.castLE i.isLt.le j)) :=
    associated_prod_castLE_of_mul_diagonal_mul_eq_diagonal hc hd hL hQ h i.isLt.le
  have hnext : Associated (∏ j : Fin (i.val + 1), c (Fin.castLE i.isLt j))
      (∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j)) :=
    associated_prod_castLE_of_mul_diagonal_mul_eq_diagonal hc hd hL hQ h i.isLt
  rw [hsplit c, hsplit d] at hnext
  by_cases h0 : (∏ j : Fin i.val, c (Fin.castLE i.isLt.le j)) = 0
  · obtain ⟨u, hu⟩ := hpre
    have hd0 : (∏ j : Fin i.val, d (Fin.castLE i.isLt.le j)) = 0 := by
      simpa [h0] using hu.symm
    rw [eq_zero_of_prod_castLE_eq_zero hc h0, eq_zero_of_prod_castLE_eq_zero hd hd0]
  · exact hnext.of_mul_left hpre h0

/-- **Two Smith normal forms of the same matrix have associated invariant factors.** If
`L₁ * A * Q₁ = diagonal c` and `L₂ * A * Q₂ = diagonal d` with unit determinants and
divisibility chains `c` and `d`, then `c i` and `d i` are associated for every `i`. -/
theorem associated_of_mul_mul_eq_diagonal {A : Matrix (Fin n) (Fin n) R} {c d : Fin n → R}
    (hc : ∀ ⦃i j : Fin n⦄, i ≤ j → c i ∣ c j)
    (hd : ∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j)
    {L₁ Q₁ L₂ Q₂ : Matrix (Fin n) (Fin n) R}
    (hL₁ : IsUnit L₁.det) (hQ₁ : IsUnit Q₁.det)
    (hL₂ : IsUnit L₂.det) (hQ₂ : IsUnit Q₂.det)
    (h₁ : L₁ * A * Q₁ = diagonal c) (h₂ : L₂ * A * Q₂ = diagonal d) (i : Fin n) :
    Associated (c i) (d i) := by
  let uL₁ := nonsingInvUnit L₁ hL₁
  let uQ₁ := nonsingInvUnit Q₁ hQ₁
  have hA : (↑uL₁⁻¹ : Matrix (Fin n) (Fin n) R) * diagonal c *
      (↑uQ₁⁻¹ : Matrix (Fin n) (Fin n) R) = A :=
    (GeneralLinearGroup.inv_mul_mul_inv_eq_iff_mul_mul_eq uL₁ uQ₁).2 h₁
  have hL : IsUnit (L₂ * (↑uL₁⁻¹ : Matrix (Fin n) (Fin n) R)).det := by
    rw [det_mul]
    exact hL₂.mul (isUnit_det_of_right_inverse uL₁.inv_mul)
  have hQ : IsUnit ((↑uQ₁⁻¹ : Matrix (Fin n) (Fin n) R) * Q₂).det := by
    rw [det_mul]
    exact (isUnit_det_of_right_inverse uQ₁.inv_mul).mul hQ₂
  refine associated_of_mul_diagonal_mul_eq_diagonal hc hd hL hQ ?_ i
  calc
    L₂ * (↑uL₁⁻¹ : Matrix (Fin n) (Fin n) R) * diagonal c *
        ((↑uQ₁⁻¹ : Matrix (Fin n) (Fin n) R) * Q₂)
      = L₂ * ((↑uL₁⁻¹ : Matrix (Fin n) (Fin n) R) * diagonal c *
          (↑uQ₁⁻¹ : Matrix (Fin n) (Fin n) R)) * Q₂ := by simp only [Matrix.mul_assoc]
    _ = L₂ * A * Q₂ := by rw [hA]
    _ = diagonal d := h₂

end Cancel

end Matrix
