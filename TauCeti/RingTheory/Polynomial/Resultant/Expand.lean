/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultants of expanded polynomials

Replacing `X` by `X ^ k` in two polynomials `f` and `g` raises their resultant to the `k`-th power:
`resultant (expand R k f) (expand R k g) (k * m) (k * n) = resultant f g m n ^ k`.

Over any commutative ring `R`, without monicity, positivity, or degree hypotheses, grouping the
`k * m + k * n` rows and columns of `sylvester (expand R k f) (expand R k g) (k * m) (k * n)` by
their residue class modulo `k` conjugates the matrix (using the same index bijection on rows and
columns, hence with sign `+1`) into the block-diagonal matrix repeating `sylvester f g m n` `k`
times. Since `(expand R k f).natDegree = f.natDegree * k` unconditionally, the same identity holds
for `Polynomial.resultant` at the actual degrees.

## Main results

* `Polynomial.resultant_expand_deg`: `Res_(k m, k n)(f(X ^ k), g(X ^ k)) = Res_(m, n)(f, g) ^ k`.
* `Polynomial.resultant_expand`: `Res(f(X ^ k), g(X ^ k)) = Res(f, g) ^ k`.
-/

public section

namespace Polynomial

section SylvesterExpand

variable {S : Type*} [CommSemiring S]

/-- Reindexing `Fin (m + n) × Fin k` to `Fin (k * m + k * n)` via `(i, r) ↦ r + k * i`. -/
private def expandSylvesterEquiv (k m n : ℕ) :
    Fin (m + n) × Fin k ≃ Fin (k * m + k * n) :=
  finProdFinEquiv.trans (finCongr (by ring))

private theorem not_dvd_add_mul_sub {k i x : ℕ} {r₁ r₂ : Fin k} (hr : r₁ ≠ r₂)
    (hle : r₂.1 + k * x ≤ r₁.1 + k * i) :
    ¬ k ∣ (r₁.1 + k * i) - (r₂.1 + k * x) := by
  intro hdvd
  have hmod := congr_arg (· % k) (Nat.add_sub_of_le hle)
  rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hdvd, add_zero, Nat.mod_mod,
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt r₁.isLt, Nat.mod_eq_of_lt r₂.isLt] at hmod
  exact hr (Fin.ext hmod.symm)

/-- Grouping indices by residue modulo `k` conjugates the Sylvester matrix of `expand S k f` and
`expand S k g` at bounds `(k * m, k * n)` into `k` diagonal copies of `sylvester f g m n`. -/
private theorem sylvester_expand_submatrix (f g : S[X]) (k m n : ℕ) :
    (sylvester (expand S k f) (expand S k g) (k * m) (k * n)).submatrix
        (expandSylvesterEquiv k m n) (expandSylvesterEquiv k m n) =
      Matrix.blockDiagonal fun _ : Fin k ↦ sylvester f g m n := by
  ext ⟨i, r₁⟩ ⟨x, r₂⟩
  have hk : 0 < k := r₁.pos
  have hi_val : (expandSylvesterEquiv k m n (i, r₁) : ℕ) = r₁.1 + k * i.1 := rfl
  have hx_val : (expandSylvesterEquiv k m n (x, r₂) : ℕ) = r₂.1 + k * x.1 := rfl
  simp only [Matrix.submatrix_apply]
  rcases lt_or_ge (x : ℕ) m with hxm | hxm
  · have hxkm : (expandSylvesterEquiv k m n (x, r₂) : ℕ) < k * m := by
      rw [hx_val]
      calc r₂.1 + k * x.1 < k + k * x.1 := Nat.add_lt_add_right r₂.isLt _
        _ = k * (x.1 + 1) := by ring
        _ ≤ k * m := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hxm)
    rw [sylvester_apply_of_lt _ _ _ _ hxkm, hi_val, hx_val]
    by_cases hr : r₁ = r₂
    · subst hr
      rw [Matrix.blockDiagonal_apply_eq, sylvester_apply_of_lt _ _ _ _ hxm]
      have hcond : (r₁.1 + k * x.1 ≤ r₁.1 + k * i.1 ∧
          r₁.1 + k * i.1 ≤ r₁.1 + k * x.1 + k * n) ↔
          (x : ℕ) ≤ i ∧ (i : ℕ) ≤ x + n := by
        rw [add_assoc r₁.1 (k * x.1) (k * n), ← mul_add, add_le_add_iff_left,
          add_le_add_iff_left, mul_le_mul_iff_of_pos_left hk, mul_le_mul_iff_of_pos_left hk]
      rw [if_congr hcond rfl rfl]
      split_ifs with h
      · rw [Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib, coeff_expand_mul' hk]
      · rfl
    · rw [Matrix.blockDiagonal_apply_ne _ _ _ hr]
      split_ifs with h
      · rw [coeff_expand hk, ite_eq_right (not_dvd_add_mul_sub hr h.1)]
      · rfl
  · have hxkm : k * m ≤ (expandSylvesterEquiv k m n (x, r₂) : ℕ) := by
      rw [hx_val]
      exact (Nat.mul_le_mul_left k hxm).trans (Nat.le_add_left _ _)
    rw [sylvester_apply_of_le _ _ _ _ hxkm, hi_val, hx_val]
    by_cases hr : r₁ = r₂
    · subst hr
      rw [Matrix.blockDiagonal_apply_eq, sylvester_apply_of_le _ _ _ _ hxm]
      have hcond : (r₁.1 + k * x.1 ≤ r₁.1 + k * i.1 + k * m ∧
          r₁.1 + k * i.1 ≤ r₁.1 + k * x.1) ↔
          (x : ℕ) ≤ i + m ∧ (i : ℕ) ≤ x := by
        rw [add_assoc r₁.1 (k * i.1) (k * m), ← mul_add, add_le_add_iff_left,
          add_le_add_iff_left, mul_le_mul_iff_of_pos_left hk, mul_le_mul_iff_of_pos_left hk]
      rw [if_congr hcond rfl rfl]
      split_ifs with h
      · rw [add_assoc r₁.1 (k * i.1) (k * m), ← mul_add, Nat.add_sub_add_left,
          ← Nat.mul_sub_left_distrib, coeff_expand_mul' hk]
      · rfl
    · rw [Matrix.blockDiagonal_apply_ne _ _ _ hr]
      split_ifs with h
      · have hrew : r₁.1 + k * i.1 + k * m = r₁.1 + k * (i.1 + m) := by ring
        rw [hrew] at h ⊢
        rw [coeff_expand hk, ite_eq_right (not_dvd_add_mul_sub hr h.1)]
      · rfl

end SylvesterExpand

variable {R : Type*} [CommRing R]

/-- **Resultant of expanded polynomials at explicit degree bounds.** Replacing `X` by `X ^ k` in
both arguments and scaling both degree bounds by `k` raises the resultant to the `k`-th power. No
positivity, monicity, or degree hypothesis is required. -/
theorem resultant_expand_deg (f g : R[X]) (k m n : ℕ) :
    resultant (expand R k f) (expand R k g) (k * m) (k * n) = resultant f g m n ^ k := by
  rw [resultant, ← Matrix.det_submatrix_equiv_self (expandSylvesterEquiv k m n),
    sylvester_expand_submatrix, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, resultant]

/-- **Resultant of expanded polynomials.** Over any commutative ring, `Res(f(X ^ k), g(X ^ k)) =
Res(f, g) ^ k` for every `k : ℕ` and all `f, g : R[X]`. -/
theorem resultant_expand (f g : R[X]) (k : ℕ) :
    (expand R k f).resultant (expand R k g) = f.resultant g ^ k := by
  rw [natDegree_expand, natDegree_expand, mul_comm f.natDegree k, mul_comm g.natDegree k,
    resultant_expand_deg]

end Polynomial
