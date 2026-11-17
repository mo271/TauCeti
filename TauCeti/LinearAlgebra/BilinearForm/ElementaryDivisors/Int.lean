/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors.Basic
import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors.PID
import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors.Unique
import TauCeti.LinearAlgebra.Matrix.Alternating
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# Alternating elementary divisors over the integers

This file specializes the alternating elementary divisor theorem to `R = ℤ`. Flipping the signs
of the second half of the basis vectors makes every elementary divisor `d i` strictly positive, so
the divisibility chain `d₀ ∣ d₁ ∣ ⋯ ∣ d_{g-1}` is literally unique (`d₁ = d₂`). Moreover, every
unit in `ℤ` has square `1`, so `(B.toMatrix c).det = (∏ i, d i) ^ 2` in every finite basis `c`
of `M`, and `B.IsPerfPair ↔ (B.toMatrix c).det = 1`.

In addition, the dual quotient (cokernel) splits as

```text
  Module.Dual ℤ M ⧸ LinearMap.range B ≃+
    ((i : l) → ZMod (d i).natAbs) × ((i : l) → ZMod (d i).natAbs)
```

of cardinality `(∏ i, (d i).natAbs) ^ 2` (or `0` if infinite, when some `d i = 0`).

## Main results

* `LinearMap.BilinForm.det_toMatrix_eq_prod_sq_of_toMatrix_eq_fromBlocks_diagonal`: exact
  determinant formula `(B.toMatrix c).det = (∏ i, d i) ^ 2` in every finite basis `c`.
* `LinearMap.BilinForm.quotientRangeEquivPiZMod` and
  `LinearMap.BilinForm.natCard_dual_quotient_range_eq_prod_sq`: cyclic decomposition of the dual
  quotient and its cardinality `(∏ i, (d i).natAbs) ^ 2`.
* `LinearMap.BilinForm.eq_of_toMatrix_eq_fromBlocks_diagonal` and
  `LinearMap.BilinForm.exists_eq_of_toMatrix_eq_fromBlocks_zero`: literal uniqueness over `ℤ`.
* `LinearMap.BilinForm.isPerfPair_iff_forall_eq_one_of_toMatrix_eq_fromBlocks_diagonal`:
  unimodularity iff `∀ i, d i = 1`.
* `LinearMap.BilinForm.IsAlt.det_toMatrix_pos` and
  `LinearMap.BilinForm.IsAlt.isPerfPair_iff_det_toMatrix_eq_one`: positivity of the Gram
  determinant and unimodularity criterion `det = 1`.
* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_fromBlocks_zero_pos`,
  `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_fromBlocks_diagonal_pos`, and
  `LinearMap.BilinForm.IsAlt.existsUnique_toMatrix_eq_fromBlocks_diagonal_of_finrank_eq`:
  existence and uniqueness of strictly positive elementary divisors over `ℤ`.
* `Matrix.exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_zero_pos` and
  `Matrix.exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_diagonal_pos`: matrix congruence forms
  for skew-symmetric integer matrices with strictly positive elementary divisors.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Lemma 3.1.4.
* Stanford VIGRE seminar notes, *Complex theory of abelian varieties*, §1, Definitions 1.13–1.14.
-/

public section

open Module Submodule

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

section Int

variable {M : Type*} [AddCommGroup M]

/-- **Exact determinant equality over `ℤ`.** If an alternating form `B` on a free abelian group
has Gram matrix `[[0, D], [-D, 0]]` in some basis `b`, then in EVERY finite basis `c` of `M`,
`(B.toMatrix c).det = (∏ i, d i) ^ 2`. -/
theorem det_toMatrix_eq_prod_sq_of_toMatrix_eq_fromBlocks_diagonal
    {l ι : Type*} [Fintype l] [DecidableEq l] [Fintype ι] [DecidableEq ι]
    {B : BilinForm ℤ M} {b : Basis (l ⊕ l) ℤ M} {d : l → ℤ}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (c : Basis ι ℤ M) :
    (B.toMatrix c).det = (∏ i, d i) ^ 2 := by
  obtain ⟨u, hu⟩ := exists_det_toMatrix_eq_unit_sq_mul_prod_sq hb c
  have hu2 : (u : ℤ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  rw [hu, hu2, one_mul]

/-- **Cyclic decomposition of the dual quotient over `ℤ`.** For a basis in which `B` has Gram
matrix `[[0, D], [-D, 0]]`, the cokernel `Module.Dual ℤ M ⧸ LinearMap.range B` is additively
isomorphic to `(∀ i, ZMod (d i).natAbs) × (∀ i, ZMod (d i).natAbs)`. -/
noncomputable def quotientRangeEquivPiZMod {l : Type*} [Fintype l] [DecidableEq l]
    {B : BilinForm ℤ M} {b : Basis (l ⊕ l) ℤ M} {d : l → ℤ}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) :
    Module.Dual ℤ M ⧸ LinearMap.range B ≃+
      ((i : l) → ZMod (d i).natAbs) × ((i : l) → ZMod (d i).natAbs) :=
  (quotientRangeEquivPiSpan hb).toAddEquiv.trans
    (AddEquiv.prodCongr
      (AddEquiv.piCongrRight fun i ↦ (Int.quotientSpanEquivZMod (d i)).toAddEquiv)
      (AddEquiv.piCongrRight fun i ↦ (Int.quotientSpanEquivZMod (d i)).toAddEquiv))

/-- The first component of `quotientRangeEquivPiZMod` evaluates a dual functional on `b (inl i)`
modulo `|d i|`. -/
@[simp]
theorem quotientRangeEquivPiZMod_mk_fst {l : Type*} [Fintype l] [DecidableEq l]
    {B : BilinForm ℤ M} {b : Basis (l ⊕ l) ℤ M} {d : l → ℤ}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (φ : Module.Dual ℤ M) (i : l) :
    (quotientRangeEquivPiZMod hb (Submodule.Quotient.mk φ)).1 i =
      (φ (b (Sum.inl i)) : ZMod (d i).natAbs) :=
  congrArg (d i).quotientSpanEquivZMod (quotientRangeEquivPiSpan_mk_fst hb φ i)

/-- The second component of `quotientRangeEquivPiZMod` evaluates a dual functional on `b (inr i)`
modulo `|d i|`. -/
@[simp]
theorem quotientRangeEquivPiZMod_mk_snd {l : Type*} [Fintype l] [DecidableEq l]
    {B : BilinForm ℤ M} {b : Basis (l ⊕ l) ℤ M} {d : l → ℤ}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
    (φ : Module.Dual ℤ M) (i : l) :
    (quotientRangeEquivPiZMod hb (Submodule.Quotient.mk φ)).2 i =
      (φ (b (Sum.inr i)) : ZMod (d i).natAbs) :=
  congrArg (d i).quotientSpanEquivZMod (quotientRangeEquivPiSpan_mk_snd hb φ i)

/-- **Cardinality of the dual quotient over `ℤ`.** For a basis in which `B` has Gram matrix
`[[0, D], [-D, 0]]`, the cokernel `Module.Dual ℤ M ⧸ LinearMap.range B` has cardinality
`(∏ i, (d i).natAbs) ^ 2` (and `0` when infinite, i.e. when some `d i = 0`). -/
theorem natCard_dual_quotient_range_eq_prod_sq {l : Type*} [Fintype l] [DecidableEq l]
    {B : BilinForm ℤ M} {b : Basis (l ⊕ l) ℤ M} {d : l → ℤ}
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) :
    Nat.card (Module.Dual ℤ M ⧸ LinearMap.range B) = (∏ i, (d i).natAbs) ^ 2 := by
  rw [Nat.card_congr (quotientRangeEquivPiZMod hb).toEquiv, Nat.card_prod, Nat.card_pi]
  simp only [Nat.card_zmod, sq]

/-- Over `ℤ`, a nonnegative divisibility chain `d` in `[[0, D], [-D, 0]]` is uniquely determined
by the bilinear form `B`. -/
theorem eq_of_toMatrix_eq_fromBlocks_diagonal {B : BilinForm ℤ M} {g : ℕ}
    {d₁ d₂ : Fin g → ℤ} {b₁ b₂ : Basis (Fin g ⊕ Fin g) ℤ M}
    (hd₁₀ : ∀ i, 0 ≤ d₁ i) (hd₂₀ : ∀ i, 0 ≤ d₂ i)
    (hd₁ : ∀ ⦃i j : Fin g⦄, i ≤ j → d₁ i ∣ d₁ j)
    (hd₂ : ∀ ⦃i j : Fin g⦄, i ≤ j → d₂ i ∣ d₂ j)
    (hb₁ : B.toMatrix b₁ =
      Matrix.fromBlocks 0 (Matrix.diagonal d₁) (-Matrix.diagonal d₁) 0)
    (hb₂ : B.toMatrix b₂ =
      Matrix.fromBlocks 0 (Matrix.diagonal d₂) (-Matrix.diagonal d₂) 0) :
    d₁ = d₂ := by
  funext i
  have h := associated_of_toMatrix_eq_fromBlocks_diagonal hd₁ hd₂ hb₁ hb₂ i
  exact Int.dvd_antisymm (hd₁₀ i) (hd₂₀ i) h.dvd h.symm.dvd

/-- Over `ℤ`, two singular alternating normal forms with strictly positive divisibility chains
have the same rank parameter, the same nullity, and equal elementary divisors. -/
theorem exists_eq_of_toMatrix_eq_fromBlocks_zero {B : BilinForm ℤ M}
    {r₁ k₁ r₂ k₂ : ℕ} {d₁ : Fin r₁ → ℤ} {d₂ : Fin r₂ → ℤ}
    {b₁ : Basis ((Fin r₁ ⊕ Fin r₁) ⊕ Fin k₁) ℤ M}
    {b₂ : Basis ((Fin r₂ ⊕ Fin r₂) ⊕ Fin k₂) ℤ M}
    (hd₁₀ : ∀ i, 0 < d₁ i) (hd₂₀ : ∀ i, 0 < d₂ i)
    (hd₁ : ∀ ⦃i j : Fin r₁⦄, i ≤ j → d₁ i ∣ d₁ j)
    (hd₂ : ∀ ⦃i j : Fin r₂⦄, i ≤ j → d₂ i ∣ d₂ j)
    (hb₁ : B.toMatrix b₁ = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d₁) (-Matrix.diagonal d₁) 0) 0 0 0)
    (hb₂ : B.toMatrix b₂ = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d₂) (-Matrix.diagonal d₂) 0) 0 0 0) :
    ∃ (hr : r₁ = r₂), k₁ = k₂ ∧ ∀ i : Fin r₁, d₁ i = d₂ (Fin.cast hr i) := by
  obtain ⟨hr, hk, hassoc⟩ := exists_eq_and_associated_of_toMatrix_eq_fromBlocks_zero
    (fun i ↦ (hd₁₀ i).ne') (fun i ↦ (hd₂₀ i).ne') hd₁ hd₂ hb₁ hb₂
  exact ⟨hr, hk, fun i ↦
    Int.dvd_antisymm (hd₁₀ i).le (hd₂₀ _).le (hassoc i).dvd (hassoc i).symm.dvd⟩

/-- Flipping signs on the second half of a basis in singular normal form replaces `d` by `|d|`. -/
private lemma exists_basis_abs_of_toMatrix_eq_fromBlocks_zero {r k : ℕ} {B : BilinForm ℤ M}
    {d : Fin r → ℤ} {b : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) ℤ M}
    (hb : B.toMatrix b = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0) :
    ∃ b' : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) ℤ M,
      B.toMatrix b' = Matrix.fromBlocks
        (Matrix.fromBlocks 0 (Matrix.diagonal (fun i ↦ |d i|))
          (-Matrix.diagonal (fun i ↦ |d i|)) 0) 0 0 0 := by
  let sgn : Fin r → ℤ := fun i ↦ if 0 ≤ d i then 1 else -1
  let w : (Fin r ⊕ Fin r) ⊕ Fin k → ℤ :=
    Sum.elim (Sum.elim (fun _ ↦ 1) sgn) (fun _ ↦ 1)
  have hw : ∀ x, IsUnit (w x) := fun x ↦ by
    rcases x with (_ | i) | _
    · exact isUnit_one
    · simp only [w, Sum.elim_inl, Sum.elim_inr, sgn]
      split_ifs <;> simp
    · exact isUnit_one
  refine ⟨b.isUnitSMul hw, ?_⟩
  ext x y
  have hxy : B (b x) (b y) = Matrix.fromBlocks
      (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℤ)
        (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0 x y := by
    rw [← toMatrix_apply, hb]
  simp only [toMatrix_apply, Basis.isUnitSMul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hxy]
  rcases x with (i | i) | j <;> rcases y with (i' | i') | j' <;>
    simp only [w, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, Matrix.diagonal_apply, one_mul, mul_zero]
  · split_ifs with h
    · subst h; simp only [sgn]; split_ifs with hd <;> [simp [abs_of_nonneg hd];
        simp [abs_of_neg (not_le.mp hd)]]
    · simp
  · split_ifs with h
    · subst h; simp only [sgn]; split_ifs with hd <;> [simp [abs_of_nonneg hd];
        simp [abs_of_neg (not_le.mp hd)]]
    · simp

/-- **Over `ℤ`, a basis in positive alternating block form is unimodular iff every `d i = 1`.** -/
theorem isPerfPair_iff_forall_eq_one_of_toMatrix_eq_fromBlocks_diagonal
    {l : Type*} [Fintype l] [DecidableEq l] {B : BilinForm ℤ M} {b : Basis (l ⊕ l) ℤ M}
    {d : l → ℤ} (hd : ∀ i, 0 < d i)
    (hb : B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) :
    B.IsPerfPair ↔ ∀ i, d i = 1 := by
  rw [isPerfPair_iff_forall_isUnit_of_toMatrix_eq_fromBlocks_diagonal hb]
  exact forall_congr' fun i ↦ by
    rw [Int.isUnit_iff]
    exact ⟨fun h ↦ h.resolve_right (by linarith [hd i]), fun h ↦ Or.inl h⟩

/-- **A nondegenerate alternating form on a finite free `ℤ`-module has strictly positive Gram
determinant** in every finite basis. -/
theorem IsAlt.det_toMatrix_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : BilinForm ℤ M} (hB : B.IsAlt) (hnd : B.Nondegenerate) (c : Basis ι ℤ M) :
    0 < (B.toMatrix c).det := by
  obtain ⟨r, hr⟩ := hB.isSquare_det_toMatrix c
  have hne : (B.toMatrix c).det ≠ 0 := (nondegenerate_iff_det_ne_zero c).mp hnd
  have hr0 : r ≠ 0 := fun h ↦ hne (by simp [hr, h])
  rw [hr]
  exact mul_self_pos.mpr hr0

/-- **Unimodularity criterion for alternating forms over `ℤ`.** An alternating bilinear form on a
finite free `ℤ`-module is a perfect pairing (unimodular) iff its Gram determinant in a basis is
`1`. -/
theorem IsAlt.isPerfPair_iff_det_toMatrix_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : BilinForm ℤ M} (hB : B.IsAlt) (c : Basis ι ℤ M) :
    B.IsPerfPair ↔ (B.toMatrix c).det = 1 := by
  constructor
  · intro hperf
    have hunit : IsUnit (B.toMatrix c).det := c.isUnit_det_of_isPerfPair c B hperf
    have hnd : B.Nondegenerate := (nondegenerate_iff_det_ne_zero c).mpr hunit.ne_zero
    have hpos := hB.det_toMatrix_pos hnd c
    exact (Int.isUnit_iff.mp hunit).resolve_right (by linarith)
  · intro hdet
    exact c.isPerfPair_of_isUnit_det c B (hdet ▸ isUnit_one)

variable [Module.Free ℤ M] [Module.Finite ℤ M]

/-- **Alternating elementary divisor theorem over `ℤ` (general, possibly singular case).** Every
alternating bilinear form on a finite free abelian group has a basis in which its Gram matrix is
`fromBlocks [[0, D], [-D, 0]] 0 0 0` with strictly positive `d : Fin r → ℤ` satisfying
`d₀ ∣ d₁ ∣ ⋯ ∣ d_{r-1}`. -/
theorem IsAlt.exists_basis_toMatrix_eq_fromBlocks_zero_pos {B : BilinForm ℤ M} (hB : B.IsAlt) :
    ∃ (r k : ℕ) (d : Fin r → ℤ) (b : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) ℤ M),
      (∀ i, 0 < d i) ∧ (∀ ⦃i j : Fin r⦄, i ≤ j → d i ∣ d j) ∧
      B.toMatrix b = Matrix.fromBlocks
        (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0 := by
  obtain ⟨r, k, d, b, hd₀, hdchain, hb⟩ := hB.exists_basis_toMatrix_eq_fromBlocks_zero
  obtain ⟨b', hb'⟩ := exists_basis_abs_of_toMatrix_eq_fromBlocks_zero hb
  refine ⟨r, k, fun i ↦ |d i|, b', fun i ↦ abs_pos.mpr (hd₀ i), fun i j hij ↦ ?_, hb'⟩
  exact (abs_dvd_abs _ _).mpr (hdchain hij)

/-- **Alternating elementary divisor theorem over `ℤ` (nondegenerate case).** Every nondegenerate
alternating bilinear form `B` on a finite free `ℤ`-module has a symplectic basis indexed by
`Fin g ⊕ Fin g` in which its Gram matrix is `[[0, D], [-D, 0]]` with `D = Matrix.diagonal d`,
`0 < d i`, and `d₀ ∣ d₁ ∣ ⋯ ∣ d_{g-1}`. -/
theorem IsAlt.exists_basis_toMatrix_eq_fromBlocks_diagonal_pos {B : BilinForm ℤ M}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ (g : ℕ) (d : Fin g → ℤ) (b : Basis (Fin g ⊕ Fin g) ℤ M),
      (∀ i, 0 < d i) ∧ (∀ ⦃i j : Fin g⦄, i ≤ j → d i ∣ d j) ∧
      B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0 := by
  obtain ⟨r, k, d, b, hdpos, hdchain, hb⟩ := hB.exists_basis_toMatrix_eq_fromBlocks_zero_pos
  have hk : k = 0 := by
    have hker := finrank_ker_eq_card_of_toMatrix_eq_fromBlocks_zero
      (fun i ↦ mem_nonZeroDivisors_of_ne_zero (hdpos i).ne') hb
    rw [hnd.ker_eq_bot, finrank_bot, Fintype.card_fin] at hker
    exact hker.symm
  subst hk
  let e : (Fin r ⊕ Fin r) ⊕ Fin 0 ≃ Fin r ⊕ Fin r := Equiv.sumEmpty _ _
  refine ⟨r, d, b.reindex e, hdpos, hdchain, ?_⟩
  ext x y
  rw [toMatrix_reindex, Matrix.reindex_apply, Matrix.submatrix_apply, hb]
  rcases x with i | i <;> rcases y with j | j <;> simp [e]

/-- **Existence and uniqueness of the elementary divisors over `ℤ` (fixed rank `2 * g`).**
For a nondegenerate alternating bilinear form `B` on a free `ℤ`-module of rank `2 * g`, there is a
unique tuple `d : Fin g → ℤ` with `0 < d i` and `d i ∣ d j` for `i ≤ j` such that `B` has Gram
matrix `Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0` in some basis indexed by
`Fin g ⊕ Fin g`. Moreover, by `det_toMatrix_eq_prod_sq_of_toMatrix_eq_fromBlocks_diagonal`,
`(B.toMatrix c).det = (∏ i, d i) ^ 2` in every finite basis `c` of `M`. -/
theorem IsAlt.existsUnique_toMatrix_eq_fromBlocks_diagonal_of_finrank_eq
    {B : BilinForm ℤ M} (hB : B.IsAlt) (hnd : B.Nondegenerate) {g : ℕ}
    (hdim : Module.finrank ℤ M = 2 * g) :
    ∃! d : Fin g → ℤ, (∀ i, 0 < d i) ∧
      (∀ ⦃i j : Fin g⦄, i ≤ j → d i ∣ d j) ∧
      ∃ b : Basis (Fin g ⊕ Fin g) ℤ M,
        B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0 := by
  obtain ⟨r, d, b, hdpos, hdchain, hb⟩ :=
    hB.exists_basis_toMatrix_eq_fromBlocks_diagonal_pos hnd
  have hr : r = g := by
    have := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hr
  refine ⟨d, ⟨hdpos, hdchain, b, hb⟩, ?_⟩
  rintro d' ⟨hd'pos, hd'chain, b', hb'⟩
  exact eq_of_toMatrix_eq_fromBlocks_diagonal (fun i ↦ (hd'pos i).le) (fun i ↦ (hdpos i).le)
    hd'chain hdchain hb' hb

end Int

end LinearMap.BilinForm

namespace Matrix

/-- **Congruence normal form for skew-symmetric integer matrices.** Over `ℤ`, `Aᵀ = -A`
automatically implies vanishing diagonal, and the nonzero elementary divisors can be chosen
strictly positive. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_zero_pos {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ} (hA : Aᵀ = -A) :
    ∃ (r k : ℕ) (e : (Fin r ⊕ Fin r) ⊕ Fin k ≃ ι) (d : Fin r → ℤ) (P : Matrix ι ι ℤ),
      IsUnit P.det ∧ (∀ i, 0 < d i) ∧ (∀ ⦃i j : Fin r⦄, i ≤ j → d i ∣ d j) ∧
      Pᵀ * A * P = reindex e e
        (fromBlocks (fromBlocks 0 (diagonal d) (-diagonal d) 0) 0 0 0) := by
  have hd : ∀ i, A i i = 0 := diag_eq_zero_of_transpose_eq_neg hA fun x hx ↦ by omega
  have halt : A.toBilin'.IsAlt := (isAlt_toBilin'_iff A).mpr ⟨hA, hd⟩
  obtain ⟨r, k, d, b, hdpos, hdchain, hb⟩ := halt.exists_basis_toMatrix_eq_fromBlocks_zero_pos
  let e : (Fin r ⊕ Fin r) ⊕ Fin k ≃ ι := b.indexEquiv (Pi.basisFun ℤ ι)
  let c := b.reindex e
  have hkey := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun ℤ ι) c A.toBilin'
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin',
    LinearMap.BilinForm.toMatrix_reindex, hb] at hkey
  refine ⟨r, k, e, d, (Pi.basisFun ℤ ι).toMatrix c,
    isUnit_det_of_right_inverse ((Pi.basisFun ℤ ι).toMatrix_mul_toMatrix_flip c),
    hdpos, hdchain, hkey⟩

/-- **Congruence normal form for nonsingular skew-symmetric integer matrices.** Over `ℤ`,
`Aᵀ = -A` automatically implies vanishing diagonal, the elementary divisors can be chosen strictly
positive, and `A.det = (∏ i, d i) ^ 2`. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_diagonal_pos {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ} (hA : Aᵀ = -A) (hdet : A.det ≠ 0) :
    ∃ (g : ℕ) (e : Fin g ⊕ Fin g ≃ ι) (d : Fin g → ℤ) (P : Matrix ι ι ℤ),
      IsUnit P.det ∧ (∀ i, 0 < d i) ∧ (∀ ⦃i j : Fin g⦄, i ≤ j → d i ∣ d j) ∧
      Pᵀ * A * P = reindex e e (fromBlocks 0 (diagonal d) (-diagonal d) 0) ∧
      A.det = (∏ i, d i) ^ 2 := by
  have hd : ∀ i, A i i = 0 := diag_eq_zero_of_transpose_eq_neg hA fun x hx ↦ by omega
  have halt : A.toBilin'.IsAlt := (isAlt_toBilin'_iff A).mpr ⟨hA, hd⟩
  have hnd : A.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  obtain ⟨g, d, b, hdpos, hdchain, hb⟩ :=
    halt.exists_basis_toMatrix_eq_fromBlocks_diagonal_pos hnd
  let e : Fin g ⊕ Fin g ≃ ι := b.indexEquiv (Pi.basisFun ℤ ι)
  let c := b.reindex e
  have hkey := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun ℤ ι) c A.toBilin'
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin',
    LinearMap.BilinForm.toMatrix_reindex, hb] at hkey
  have hdet_eq : A.det = (∏ i, d i) ^ 2 := by
    have h := LinearMap.BilinForm.det_toMatrix_eq_prod_sq_of_toMatrix_eq_fromBlocks_diagonal hb
      (Pi.basisFun ℤ ι)
    rwa [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h
  refine ⟨g, e, d, (Pi.basisFun ℤ ι).toMatrix c,
    isUnit_det_of_right_inverse ((Pi.basisFun ℤ ι).toMatrix_mul_toMatrix_flip c),
    hdpos, hdchain, hkey, hdet_eq⟩

end Matrix
