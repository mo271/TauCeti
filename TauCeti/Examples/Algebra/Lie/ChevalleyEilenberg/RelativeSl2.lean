/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.Equivariant
public import TauCeti.Examples.Algebra.Lie.ChevalleyEilenberg.Basic

/-!
# Relative Chevalley–Eilenberg cohomology of `(sl₂(ℝ), so(2), SO(2))`

This file computes both the purely Lie-algebraic relative cohomology
`H^•(sl₂(ℝ), so(2); ℂ)` and the group-enhanced relative cohomology
`H^•(sl₂(ℝ), so(2), SO(2); ℂ)` with trivial coefficients `ℂ`, matching the cohomology of the
compact dual `S²`:

* `so2 ⊂ sl (Fin 2) ℝ` is the one-dimensional skew-symmetric subalgebra `ℝ · J`
  (`J = !![0, -1; 1, 0]`), and `SO(2) = Matrix.specialOrthogonalGroup (Fin 2) ℝ` acts on
  `sl (Fin 2) ℝ` by conjugation (`so2ConjRep`).
* The quotient `sl₂(ℝ) ⧸ so2` is two-dimensional with basis `p₀ = [H]`, `p₁ = [S]`
  (`H = !![1, 0; 0, -1]`, `S = !![0, 1; 1, 0]`).
* An element `g = !![c, -s; s, c] ∈ SO(2)` (`c² + s² = 1`) acts on `sl₂(ℝ) ⧸ so2` by rotation
  with matrix `!![c² - s², -2cs; 2cs, c² - s²]` of determinant `(c² + s²)² = 1`. On the
  complexification `ℂ ⊗[ℝ] (sl₂(ℝ) ⧸ so2)`, the vectors `1 ⊗ p₀ ∓ i ⊗ p₁` are eigenvectors with
  `SO(2)`-weights `(c ± i s)²` (weights `±2`: `so2_weight_plus_two` and `so2_weight_minus_two`).
* In degree `1`, `C¹ = 0` already under `so2`-invariance (`subsingleton_relativeCochain_sl2_one`),
  and also under `SO(2)`-equivariance via the `π/2` rotation `rotQuarter` acting as `-1`
  (`eq_zero_of_horizontal_equivariant_one`).
* In degree `2`, every horizontal `2`-cochain is automatically both `so2`-invariant and
  `SO(2)`-equivariant (`lie_eq_zero_of_mem_horizontalCochain_two`,
  `mem_equivariantCochain_of_mem_horizontalCochain_two`).
* In every degree `n`, `SO(2)`-equivariance on horizontal cochains implies `so2`-invariance
  (`so2_equivariant_implies_invariance`), so `sl2SO2CochainEquivIntertwiningMap` identifies
  `C^n(sl₂(ℝ), so(2), SO(2); ℂ)` with `Hom_{SO(2)}(⋀^n(sl₂(ℝ) ⧸ so(2)), ℂ)`.
* Cohomology of both complexes: `H⁰ ≃ₗ[ℝ] ℂ`, `H¹ = 0`, `H² ≃ₗ[ℝ] ℂ`, and `H^q = 0` for `q ≥ 3`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), §22–§28.
* A. Borel and N. Wallach, *Continuous Cohomology, Discrete Subgroups, and Representations of
  Reductive Groups*, 2nd ed., AMS, 2000, Ch. I, §1.
-/

public section

open scoped TensorProduct
open CategoryTheory LieAlgebra Matrix Module

namespace TauCeti.Examples.ChevalleyEilenberg

open TauCeti.LieModule.Cohomology

/-! ### Cartan basis `(J, H, S)` and `so(2) ⊂ sl₂(ℝ)` -/

/-- Shorthand for the real Lie algebra `sl (Fin 2) ℝ`. -/
abbrev sl2R : Type := SpecialLinear.sl (Fin 2) ℝ

/-- Shorthand for the compact rotation group `SO(2) = Matrix.specialOrthogonalGroup (Fin 2) ℝ`. -/
abbrev SO2 : Type := Matrix.specialOrthogonalGroup (Fin 2) ℝ

/-- The standard generator `J = !![0, -1; 1, 0]` of `so(2) ⊂ sl₂(ℝ)`. -/
def matJ : sl2R := ⟨!![0, -1; 1, 0], by simp⟩

/-- The diagonal Cartan element `H = !![1, 0; 0, -1]` of `sl₂(ℝ)`. -/
def matH : sl2R := ⟨!![1, 0; 0, -1], by simp⟩

/-- The off-diagonal symmetric element `S = !![0, 1; 1, 0]` of `sl₂(ℝ)`. -/
def matS : sl2R := ⟨!![0, 1; 1, 0], by simp⟩

/-- Bracket relation `⁅J, H⁆ = 2 • S` in `sl₂(ℝ)`. -/
theorem lie_matJ_matH : ⁅matJ, matH⁆ = (2 : ℝ) • matS := by
  apply Subtype.ext
  ext i j
  rw [SpecialLinear.sl_bracket]
  fin_cases i <;> fin_cases j <;> simp [matJ, matH, matS] <;> ring

/-- Bracket relation `⁅J, S⁆ = -(2 • H)` in `sl₂(ℝ)`. -/
theorem lie_matJ_matS : ⁅matJ, matS⁆ = -((2 : ℝ) • matH) := by
  apply Subtype.ext
  ext i j
  rw [SpecialLinear.sl_bracket]
  fin_cases i <;> fin_cases j <;> simp [matJ, matH, matS] <;> ring

/-- Bracket relation `⁅H, S⁆ = -(2 • J)` in `sl₂(ℝ)`. -/
theorem lie_matH_matS : ⁅matH, matS⁆ = -((2 : ℝ) • matJ) := by
  apply Subtype.ext
  ext i j
  rw [SpecialLinear.sl_bracket]
  fin_cases i <;> fin_cases j <;> simp [matJ, matH, matS] <;> ring

/-- Decomposition of any trace-zero real `2 × 2` matrix in the Cartan basis `(J, H, S)`. -/
theorem eq_cartan_decomp (A : sl2R) :
    A = ((A.1 1 0 - A.1 0 1) / 2) • matJ + (A.1 0 0) • matH +
      ((A.1 0 1 + A.1 1 0) / 2) • matS := by
  apply Subtype.ext
  ext i j
  have h11 : A.1 1 1 = -A.1 0 0 := val_one_one_eq_neg_val_zero_zero A
  fin_cases i <;> fin_cases j <;> simp [matJ, matH, matS, h11] <;> ring

/-- The Lie subalgebra `so(2) ⊂ sl₂(ℝ)` of skew-symmetric trace-zero `2 × 2` real matrices. -/
def so2 : LieSubalgebra ℝ sl2R where
  carrier := {A | A.1 + A.1ᵀ = 0}
  add_mem' {A B} hA hB := by
    change (A.1 + B.1) + (A.1 + B.1)ᵀ = 0
    rw [Matrix.transpose_add]
    calc A.1 + B.1 + (A.1ᵀ + B.1ᵀ) = (A.1 + A.1ᵀ) + (B.1 + B.1ᵀ) := by abel
      _ = 0 + 0 := by rw [hA, hB]
      _ = 0 := add_zero 0
  zero_mem' := by simp
  smul_mem' c {A} hA := by
    change c • A.1 + (c • A.1)ᵀ = 0
    rw [Matrix.transpose_smul, ← smul_add, hA, smul_zero]
  lie_mem' {A B} hA hB := by
    change (A.1 * B.1 - B.1 * A.1) + (A.1 * B.1 - B.1 * A.1)ᵀ = 0
    have hAt : A.1ᵀ = -A.1 := eq_neg_of_add_eq_zero_right hA
    have hBt : B.1ᵀ = -B.1 := eq_neg_of_add_eq_zero_right hB
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hAt, hBt]
    simp only [neg_mul, mul_neg, neg_neg]
    abel

/-- Characterization of membership in `so(2)` by matrix entries. -/
theorem mem_so2_iff {A : sl2R} :
    A ∈ so2 ↔ A.1 0 0 = 0 ∧ A.1 0 1 + A.1 1 0 = 0 := by
  change A.1 + A.1ᵀ = 0 ↔ _
  have h11 : A.1 1 1 = -A.1 0 0 := val_one_one_eq_neg_val_zero_zero A
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) h
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at h00 h01
    exact ⟨by linarith, h01⟩
  · rintro ⟨h00, h01⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11, h00] <;> linarith

/-- The generator `matJ` belongs to `so2`. -/
theorem matJ_mem_so2 : matJ ∈ so2 :=
  mem_so2_iff.mpr ⟨by simp [matJ], by simp [matJ]⟩

/-- Every element of `so2` is a real scalar multiple of `matJ`. -/
theorem mem_so2_eq_smul_matJ {A : sl2R} (hA : A ∈ so2) : A = (A.1 1 0) • matJ := by
  obtain ⟨h00, h01⟩ := mem_so2_iff.mp hA
  apply Subtype.ext
  ext i j
  have h11 : A.1 1 1 = -A.1 0 0 := val_one_one_eq_neg_val_zero_zero A
  fin_cases i <;> fin_cases j <;> simp [matJ, h11, h00]
  linarith

/-! ### The quotient `sl₂(ℝ) ⧸ so(2)` and its basis `([H], [S])` -/

/-- Coordinate isomorphism `sl₂(ℝ) ⧸ so(2) ≃ₗ[ℝ] (Fin 2 → ℝ)` sending `[A]` to
`(A 0 0, (A 0 1 + A 1 0) / 2)`. -/
noncomputable def sl2QuotSo2EquivFun :
    (sl2R ⧸ so2.toLieSubmodule) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  let φ : sl2R →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun A ↦ ![A.1 0 0, (A.1 0 1 + A.1 1 0) / 2]
      map_add' := fun A B ↦ by ext k; fin_cases k <;> simp; ring
      map_smul' := fun r A ↦ by ext k; fin_cases k <;> simp; ring }
  let toF : (sl2R ⧸ so2.toLieSubmodule) →ₗ[ℝ] (Fin 2 → ℝ) :=
    Submodule.liftQ so2.toLieSubmodule.toSubmodule φ (by
      intro A hA
      rw [LinearMap.mem_ker]
      obtain ⟨h00, h01⟩ := mem_so2_iff.mp hA
      ext k
      fin_cases k
      · exact h00
      · simp [φ, h01])
  { toFun := toF
    map_add' := toF.map_add
    map_smul' := toF.map_smul
    invFun := fun v ↦ LieSubmodule.Quotient.mk (v 0 • matH + v 1 • matS)
    left_inv := fun q ↦ Quotient.inductionOn' q fun A ↦ by
      have hsub : A - (A.1 0 0 • matH + ((A.1 0 1 + A.1 1 0) / 2) • matS) ∈ so2 := by
        rw [mem_so2_iff]
        constructor <;> simp [matH, matS]; ring
      change LieSubmodule.Quotient.mk (A.1 0 0 • matH + ((A.1 0 1 + A.1 1 0) / 2) • matS) =
        LieSubmodule.Quotient.mk A
      symm
      exact (Submodule.Quotient.eq so2.toLieSubmodule.toSubmodule).mpr hsub
    right_inv := fun v ↦ by
      ext k
      change φ (v 0 • matH + v 1 • matS) k = v k
      fin_cases k <;> simp [φ, matH, matS] }

/-- The standard basis `(p₀, p₁) = ([H], [S])` of `sl₂(ℝ) ⧸ so(2)`. -/
noncomputable def sl2QuotSo2Basis : Basis (Fin 2) ℝ (sl2R ⧸ so2.toLieSubmodule) :=
  Basis.ofEquivFun sl2QuotSo2EquivFun

/-- The zeroth basis vector of `sl2QuotSo2Basis` is the coset `[H]`. -/
theorem sl2QuotSo2Basis_zero :
    sl2QuotSo2Basis 0 = LieSubmodule.Quotient.mk matH := by
  rw [sl2QuotSo2Basis, Basis.coe_ofEquivFun]
  change LieSubmodule.Quotient.mk ((1 : ℝ) • matH + (0 : ℝ) • matS) = _
  simp

/-- The first basis vector of `sl2QuotSo2Basis` is the coset `[S]`. -/
theorem sl2QuotSo2Basis_one :
    sl2QuotSo2Basis 1 = LieSubmodule.Quotient.mk matS := by
  rw [sl2QuotSo2Basis, Basis.coe_ofEquivFun]
  change LieSubmodule.Quotient.mk ((0 : ℝ) • matH + (1 : ℝ) • matS) = _
  simp

/-- The real dimension of `sl₂(ℝ) ⧸ so(2)` is `2`. -/
theorem finrank_sl2QuotSo2 : Module.finrank ℝ (sl2R ⧸ so2.toLieSubmodule) = 2 := by
  rw [Module.finrank_eq_card_basis sl2QuotSo2Basis, Fintype.card_fin]

/-! ### Conjugation action of `SO(2)` and weights `±2` -/

/-- The inverse of an orthogonal matrix `g ∈ SO(2)` is its transpose. -/
theorem so2_val_inv (g : SO2) : (g⁻¹).1 = g.1ᵀ := by
  have h1 : g.1 * g.1ᵀ = 1 := by
    have horth := (Matrix.mem_specialOrthogonalGroup_iff.mp g.2).1
    rwa [Matrix.mem_orthogonalGroup_iff] at horth
  have h2 : (g⁻¹).1 * g.1 = 1 := congrArg Subtype.val (inv_mul_cancel g)
  calc (g⁻¹).1 = (g⁻¹).1 * 1 := (Matrix.mul_one _).symm
    _ = (g⁻¹).1 * (g.1 * g.1ᵀ) := by rw [h1]
    _ = ((g⁻¹).1 * g.1) * g.1ᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = 1 * g.1ᵀ := by rw [h2]
    _ = g.1ᵀ := Matrix.one_mul _

/-- Standard parameterization entries of `g = !![c, -s; s, c] ∈ SO(2)` with `c² + s² = 1`. -/
theorem so2_entries (g : SO2) :
    g.1 1 1 = g.1 0 0 ∧ g.1 0 1 = -(g.1 1 0) ∧ (g.1 0 0) ^ 2 + (g.1 1 0) ^ 2 = 1 := by
  obtain ⟨h00, h01, hsq⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp g.2
  refine ⟨h00.symm, h01, ?_⟩
  rw [h01, neg_sq] at hsq
  exact hsq

/-- The conjugation representation of `SO(2)` on `sl₂(ℝ)`: `g · A = g A g⁻¹`. -/
def so2ConjRep : Representation ℝ SO2 sl2R where
  toFun g :=
    { toFun := fun A ↦ ⟨g.1 * A.1 * (g⁻¹).1, by
        have hmul : (g⁻¹).1 * g.1 = 1 := congrArg Subtype.val (inv_mul_cancel g)
        change Matrix.trace (g.1 * A.1 * (g⁻¹).1) = 0
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hmul, Matrix.one_mul]
        exact A.2⟩
      map_add' := fun A B ↦ Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun r A ↦ Subtype.ext (by simp) }
  map_one' := by
    apply LinearMap.ext
    intro A
    apply Subtype.ext
    change (1 : SO2).1 * A.1 * ((1 : SO2)⁻¹).1 = A.1
    simp
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro A
    apply Subtype.ext
    change (g₁ * g₂).1 * A.1 * ((g₁ * g₂)⁻¹).1 =
      g₁.1 * (g₂.1 * A.1 * (g₂⁻¹).1) * (g₁⁻¹).1
    rw [_root_.mul_inv_rev]
    change (g₁.1 * g₂.1) * A.1 * ((g₂⁻¹).1 * (g₁⁻¹).1) =
      g₁.1 * (g₂.1 * A.1 * (g₂⁻¹).1) * (g₁⁻¹).1
    simp [Matrix.mul_assoc]

/-- Conjugation by `g ∈ SO(2)` is a Lie algebra automorphism of `sl₂(ℝ)`. -/
theorem so2ConjRep_map_lie (g : SO2) (A B : sl2R) :
    so2ConjRep g ⁅A, B⁆ = ⁅so2ConjRep g A, so2ConjRep g B⁆ := by
  apply Subtype.ext
  have hmul : (g⁻¹).1 * g.1 = 1 := congrArg Subtype.val (inv_mul_cancel g)
  change g.1 * (A.1 * B.1 - B.1 * A.1) * (g⁻¹).1 =
    (g.1 * A.1 * (g⁻¹).1) * (g.1 * B.1 * (g⁻¹).1) -
    (g.1 * B.1 * (g⁻¹).1) * (g.1 * A.1 * (g⁻¹).1)
  have h1 : (g.1 * A.1 * (g⁻¹).1) * (g.1 * B.1 * (g⁻¹).1) = g.1 * (A.1 * B.1) * (g⁻¹).1 := by
    calc (g.1 * A.1 * (g⁻¹).1) * (g.1 * B.1 * (g⁻¹).1)
        = g.1 * A.1 * ((g⁻¹).1 * g.1) * B.1 * (g⁻¹).1 := by simp [Matrix.mul_assoc]
      _ = g.1 * A.1 * 1 * B.1 * (g⁻¹).1 := by rw [hmul]
      _ = g.1 * (A.1 * B.1) * (g⁻¹).1 := by simp [Matrix.mul_assoc]
  have h2 : (g.1 * B.1 * (g⁻¹).1) * (g.1 * A.1 * (g⁻¹).1) = g.1 * (B.1 * A.1) * (g⁻¹).1 := by
    calc (g.1 * B.1 * (g⁻¹).1) * (g.1 * A.1 * (g⁻¹).1)
        = g.1 * B.1 * ((g⁻¹).1 * g.1) * A.1 * (g⁻¹).1 := by simp [Matrix.mul_assoc]
      _ = g.1 * B.1 * 1 * A.1 * (g⁻¹).1 := by rw [hmul]
      _ = g.1 * (B.1 * A.1) * (g⁻¹).1 := by simp [Matrix.mul_assoc]
  rw [h1, h2, mul_sub, sub_mul]

/-- Conjugation by `SO(2)` preserves the subalgebra `so(2) ⊂ sl₂(ℝ)`. -/
theorem so2ConjRep_mem_so2 (g : SO2) {A : sl2R} (hA : A ∈ so2) :
    so2ConjRep g A ∈ so2 := by
  change (g.1 * A.1 * (g⁻¹).1) + (g.1 * A.1 * (g⁻¹).1)ᵀ = 0
  have hAt : A.1ᵀ = -A.1 := eq_neg_of_add_eq_zero_right hA
  have hginv : (g⁻¹).1 = g.1ᵀ := so2_val_inv g
  rw [hginv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hAt]
  simp [Matrix.mul_assoc]

/-- `g = !![c, -s; s, c] ∈ SO(2)` acts on `H` by `(c² - s²) H + (2cs) S`. -/
theorem so2ConjRep_matH (g : SO2) :
    so2ConjRep g matH =
      ((g.1 0 0) ^ 2 - (g.1 1 0) ^ 2) • matH + (2 * g.1 0 0 * g.1 1 0) • matS := by
  obtain ⟨h11, h01, _⟩ := so2_entries g
  have hginv : (g⁻¹).1 = g.1ᵀ := so2_val_inv g
  apply Subtype.ext
  ext i j
  change (g.1 * matH.1 * (g⁻¹).1) i j = _
  rw [hginv]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, matH, matS, h11, h01] <;> ring

/-- `g = !![c, -s; s, c] ∈ SO(2)` acts on `S` by `-(2cs) H + (c² - s²) S`. -/
theorem so2ConjRep_matS (g : SO2) :
    so2ConjRep g matS =
      (-(2 * g.1 0 0 * g.1 1 0)) • matH + ((g.1 0 0) ^ 2 - (g.1 1 0) ^ 2) • matS := by
  obtain ⟨h11, h01, _⟩ := so2_entries g
  have hginv : (g⁻¹).1 = g.1ᵀ := so2_val_inv g
  apply Subtype.ext
  ext i j
  change (g.1 * matS.1 * (g⁻¹).1) i j = _
  rw [hginv]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, matH, matS, h11, h01] <;> ring

private theorem quotientRep_basis_zero (g : SO2) :
    quotientRepresentation so2 so2ConjRep (fun g _ h ↦ so2ConjRep_mem_so2 g h) g
        (sl2QuotSo2Basis 0) =
      ((g.1 0 0) ^ 2 - (g.1 1 0) ^ 2) • sl2QuotSo2Basis 0 +
        (2 * g.1 0 0 * g.1 1 0) • sl2QuotSo2Basis 1 := by
  rw [sl2QuotSo2Basis_zero, sl2QuotSo2Basis_one, quotientRepresentation_apply_mk, so2ConjRep_matH]
  rfl

private theorem quotientRep_basis_one (g : SO2) :
    quotientRepresentation so2 so2ConjRep (fun g _ h ↦ so2ConjRep_mem_so2 g h) g
        (sl2QuotSo2Basis 1) =
      (-(2 * g.1 0 0 * g.1 1 0)) • sl2QuotSo2Basis 0 +
        ((g.1 0 0) ^ 2 - (g.1 1 0) ^ 2) • sl2QuotSo2Basis 1 := by
  rw [sl2QuotSo2Basis_zero, sl2QuotSo2Basis_one, quotientRepresentation_apply_mk, so2ConjRep_matS]
  rfl

/-- On the complexification `ℂ ⊗[ℝ] (sl₂(ℝ) ⧸ so(2))`, `SO(2)` acts on `1 ⊗ [H] - i ⊗ [S]`
with weight `+2`: `g · (1 ⊗ [H] - i ⊗ [S]) = (c + s i)² • (1 ⊗ [H] - i ⊗ [S])`. -/
theorem so2_weight_plus_two (g : SO2) :
    LinearMap.baseChange ℂ
        (quotientRepresentation so2 so2ConjRep (fun g _ h ↦ so2ConjRep_mem_so2 g h) g)
        ((1 : ℂ) ⊗ₜ[ℝ] sl2QuotSo2Basis 0 - Complex.I ⊗ₜ[ℝ] sl2QuotSo2Basis 1) =
      (((g.1 0 0 : ℂ) + (g.1 1 0 : ℂ) * Complex.I) ^ 2) •
        ((1 : ℂ) ⊗ₜ[ℝ] sl2QuotSo2Basis 0 - Complex.I ⊗ₜ[ℝ] sl2QuotSo2Basis 1) := by
  set c : ℝ := g.1 0 0
  set s : ℝ := g.1 1 0
  set p₀ : sl2R ⧸ so2.toLieSubmodule := sl2QuotSo2Basis 0
  set p₁ : sl2R ⧸ so2.toLieSubmodule := sl2QuotSo2Basis 1
  rw [map_sub, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
    quotientRep_basis_zero g, quotientRep_basis_one g,
    TensorProduct.tmul_add, TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
  have hre : (c ^ 2 - s ^ 2 : ℝ) • (1 : ℂ) - (-(2 * c * s) : ℝ) • Complex.I =
      ((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 * 1 := by
    simp only [Complex.real_smul]; push_cast
    linear_combination -(s : ℂ) ^ 2 * Complex.I_sq
  have him : (2 * c * s : ℝ) • (1 : ℂ) - (c ^ 2 - s ^ 2 : ℝ) • Complex.I =
      -(((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 * Complex.I) := by
    simp only [Complex.real_smul]; push_cast
    linear_combination ((s : ℂ) ^ 2 * Complex.I + 2 * (c : ℂ) * (s : ℂ)) * Complex.I_sq
  calc ((c ^ 2 - s ^ 2 : ℝ) • (1 : ℂ) ⊗ₜ[ℝ] p₀ + (2 * c * s : ℝ) • (1 : ℂ) ⊗ₜ[ℝ] p₁) -
        ((-(2 * c * s) : ℝ) • Complex.I ⊗ₜ[ℝ] p₀ + (c ^ 2 - s ^ 2 : ℝ) • Complex.I ⊗ₜ[ℝ] p₁)
      = ((c ^ 2 - s ^ 2 : ℝ) • (1 : ℂ) - (-(2 * c * s) : ℝ) • Complex.I) ⊗ₜ[ℝ] p₀ +
        ((2 * c * s : ℝ) • (1 : ℂ) - (c ^ 2 - s ^ 2 : ℝ) • Complex.I) ⊗ₜ[ℝ] p₁ := by
          rw [TensorProduct.sub_tmul, TensorProduct.sub_tmul]
          simp only [← TensorProduct.smul_tmul']
          abel
    _ = (((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 * 1) ⊗ₜ[ℝ] p₀ +
        (-(((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 * Complex.I)) ⊗ₜ[ℝ] p₁ := by rw [hre, him]
    _ = (((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 • (1 : ℂ)) ⊗ₜ[ℝ] p₀ -
        (((c : ℂ) + (s : ℂ) * Complex.I) ^ 2 • Complex.I) ⊗ₜ[ℝ] p₁ := by
          rw [TensorProduct.neg_tmul, sub_eq_add_neg]; rfl
    _ = (((c : ℂ) + (s : ℂ) * Complex.I) ^ 2) • ((1 : ℂ) ⊗ₜ[ℝ] p₀ - Complex.I ⊗ₜ[ℝ] p₁) := by
          rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul']

/-- On the complexification `ℂ ⊗[ℝ] (sl₂(ℝ) ⧸ so(2))`, `SO(2)` acts on `1 ⊗ [H] + i ⊗ [S]`
with weight `-2`: `g · (1 ⊗ [H] + i ⊗ [S]) = (c - s i)² • (1 ⊗ [H] + i ⊗ [S])`. -/
theorem so2_weight_minus_two (g : SO2) :
    LinearMap.baseChange ℂ
        (quotientRepresentation so2 so2ConjRep (fun g _ h ↦ so2ConjRep_mem_so2 g h) g)
        ((1 : ℂ) ⊗ₜ[ℝ] sl2QuotSo2Basis 0 + Complex.I ⊗ₜ[ℝ] sl2QuotSo2Basis 1) =
      (((g.1 0 0 : ℂ) - (g.1 1 0 : ℂ) * Complex.I) ^ 2) •
        ((1 : ℂ) ⊗ₜ[ℝ] sl2QuotSo2Basis 0 + Complex.I ⊗ₜ[ℝ] sl2QuotSo2Basis 1) := by
  set c : ℝ := g.1 0 0
  set s : ℝ := g.1 1 0
  set p₀ : sl2R ⧸ so2.toLieSubmodule := sl2QuotSo2Basis 0
  set p₁ : sl2R ⧸ so2.toLieSubmodule := sl2QuotSo2Basis 1
  rw [map_add, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
    quotientRep_basis_zero g, quotientRep_basis_one g,
    TensorProduct.tmul_add, TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
  have hre : (c ^ 2 - s ^ 2 : ℝ) • (1 : ℂ) + (-(2 * c * s) : ℝ) • Complex.I =
      ((c : ℂ) - (s : ℂ) * Complex.I) ^ 2 * 1 := by
    simp only [Complex.real_smul]; push_cast
    linear_combination -(s : ℂ) ^ 2 * Complex.I_sq
  have him : (2 * c * s : ℝ) • (1 : ℂ) + (c ^ 2 - s ^ 2 : ℝ) • Complex.I =
      ((c : ℂ) - (s : ℂ) * Complex.I) ^ 2 * Complex.I := by
    simp only [Complex.real_smul]; push_cast
    linear_combination (-(s : ℂ) ^ 2 * Complex.I + 2 * (c : ℂ) * (s : ℂ)) * Complex.I_sq
  calc ((c ^ 2 - s ^ 2 : ℝ) • (1 : ℂ) ⊗ₜ[ℝ] p₀ + (2 * c * s : ℝ) • (1 : ℂ) ⊗ₜ[ℝ] p₁) +
        ((-(2 * c * s) : ℝ) • Complex.I ⊗ₜ[ℝ] p₀ + (c ^ 2 - s ^ 2 : ℝ) • Complex.I ⊗ₜ[ℝ] p₁)
      = ((c ^ 2 - s ^ 2 : ℝ) • (1 : ℂ) + (-(2 * c * s) : ℝ) • Complex.I) ⊗ₜ[ℝ] p₀ +
        ((2 * c * s : ℝ) • (1 : ℂ) + (c ^ 2 - s ^ 2 : ℝ) • Complex.I) ⊗ₜ[ℝ] p₁ := by
          rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
          simp only [← TensorProduct.smul_tmul']
          abel
    _ = (((c : ℂ) - (s : ℂ) * Complex.I) ^ 2 * 1) ⊗ₜ[ℝ] p₀ +
        (((c : ℂ) - (s : ℂ) * Complex.I) ^ 2 * Complex.I) ⊗ₜ[ℝ] p₁ := by rw [hre, him]
    _ = (((c : ℂ) - (s : ℂ) * Complex.I) ^ 2) • ((1 : ℂ) ⊗ₜ[ℝ] p₀ + Complex.I ⊗ₜ[ℝ] p₁) := by
          rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul']; rfl

/-- The `π/2` rotation `!![0, -1; 1, 0]` in `SO(2)`, which acts as `-1` on `sl₂(ℝ) ⧸ so(2)`. -/
def rotQuarter : SO2 :=
  ⟨!![0, -1; 1, 0], Matrix.of_mem_specialOrthogonalGroup_fin_two_iff.mpr (by norm_num)⟩

/-- The `π/2` rotation `rotQuarter` negates `matH`. -/
theorem so2ConjRep_rotQuarter_matH : so2ConjRep rotQuarter matH = -matH := by
  rw [so2ConjRep_matH]
  simp [rotQuarter]

/-- The `π/2` rotation `rotQuarter` negates `matS`. -/
theorem so2ConjRep_rotQuarter_matS : so2ConjRep rotQuarter matS = -matS := by
  rw [so2ConjRep_matS]
  simp [rotQuarter]

/-! ### Relative cochains and cohomology with coefficients `ℂ` -/

/-- Trivial `sl₂(ℝ)`-module on `ℂ` (viewed as an `ℝ`-vector space). -/
abbrev trivialC : Type := TrivialLieModule ℝ sl2R ℂ

/-- Trivial `SO(2)`-representation on `trivialC`. -/
noncomputable def trivialCRep : Representation ℝ SO2 trivialC :=
  Representation.trivial ℝ SO2 trivialC

theorem trivialCRep_map_lie (g : SO2) (x : sl2R) (m : trivialC) :
    trivialCRep g ⁅x, m⁆ = ⁅so2ConjRep g x, trivialCRep g m⁆ := by
  simp [LieModule.IsTrivial.trivial]

private theorem one_cochain_linear_decomp (ω : sl2R [⋀^Fin 1]→ₗ[ℝ] trivialC)
    (a b c : ℝ) :
    ω ![a • matJ + b • matH + c • matS] =
      a • ω ![matJ] + b • ω ![matH] + c • ω ![matS] := by
  have hadd (x y : sl2R) : ω ![x + y] = ω ![x] + ω ![y] := by
    have hu (z : sl2R) : Function.update ![x] 0 z = ![z] := by ext k; fin_cases k; rfl
    have h := ω.map_update_add ![x] 0 x y
    rwa [hu (x + y), hu x, hu y] at h
  have hsmul (r : ℝ) (x : sl2R) : ω ![r • x] = r • ω ![x] := by
    have hu (z : sl2R) : Function.update ![x] 0 z = ![z] := by ext k; fin_cases k; rfl
    have h := ω.map_update_smul ![x] 0 r x
    rwa [hu (r • x), hu x] at h
  rw [hadd, hadd, hsmul, hsmul, hsmul]

/-- In degree `1`, every `so2`-horizontal and `SO(2)`-equivariant `1`-cochain vanishes
(witnessed already by the `π/2` rotation `rotQuarter` acting as `-1` on `sl₂(ℝ) ⧸ so(2)`). -/
theorem eq_zero_of_horizontal_equivariant_one {ω : sl2R [⋀^Fin 1]→ₗ[ℝ] trivialC}
    (hhor : ω ∈ horizontalCochain ℝ sl2R so2 trivialC 1)
    (heq : ω ∈ equivariantCochain so2ConjRep trivialCRep 1) : ω = 0 := by
  have hsmul (r : ℝ) (x : sl2R) : ω ![r • x] = r • ω ![x] := by
    have hu (z : sl2R) : Function.update ![x] 0 z = ![z] := by ext k; fin_cases k; rfl
    have h := ω.map_update_smul ![x] 0 r x
    rwa [hu (r • x), hu x] at h
  have hJ : ω ![matJ] = 0 := (mem_horizontalCochain_iff.mp hhor) ![matJ] 0 matJ_mem_so2
  have hH : ω ![matH] = 0 := by
    have h := (mem_equivariantCochain_iff.mp heq) rotQuarter ![matH]
    have hcomp : so2ConjRep rotQuarter ∘ ![matH] = ![-matH] := by
      funext k; fin_cases k; exact so2ConjRep_rotQuarter_matH
    rw [hcomp] at h
    have hneg : ω ![-matH] = -ω ![matH] := by
      rw [show -matH = (-1 : ℝ) • matH by simp, hsmul, neg_one_smul]
    rw [hneg] at h
    change ω ![matH] = -ω ![matH] at h
    have h2 : (2 : ℝ) • ω ![matH] = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hS : ω ![matS] = 0 := by
    have h := (mem_equivariantCochain_iff.mp heq) rotQuarter ![matS]
    have hcomp : so2ConjRep rotQuarter ∘ ![matS] = ![-matS] := by
      funext k; fin_cases k; exact so2ConjRep_rotQuarter_matS
    rw [hcomp] at h
    have hneg : ω ![-matS] = -ω ![matS] := by
      rw [show -matS = (-1 : ℝ) • matS by simp, hsmul, neg_one_smul]
    rw [hneg] at h
    change ω ![matS] = -ω ![matS] at h
    have h2 : (2 : ℝ) • ω ![matS] = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv, eq_cartan_decomp (v 0), one_cochain_linear_decomp, hJ, hH, hS]
  simp

/-- In degree `1`, every `so2`-relative `1`-cochain vanishes (`H¹ = 0` already
Lie-algebraically). -/
theorem subsingleton_relativeCochain_sl2_one :
    Subsingleton (relativeCochain ℝ sl2R so2 trivialC 1) := by
  refine ⟨fun ω₁ ω₂ ↦ Subtype.ext ?_⟩
  rw [← sub_eq_zero]
  set ω := ω₁.1 - ω₂.1
  have hω : ω ∈ relativeCochain ℝ sl2R so2 trivialC 1 := Submodule.sub_mem _ ω₁.2 ω₂.2
  have hhor : ∀ (v : Fin 1 → sl2R) (i : Fin 1), v i ∈ so2 → ω v = 0 :=
    (mem_relativeCochain_iff.mp hω).1
  have hinv : ⁅matJ, ω⁆ = 0 := (mem_relativeCochain_iff.mp hω).2 matJ matJ_mem_so2
  have hsmul (r : ℝ) (x : sl2R) : ω ![r • x] = r • ω ![x] := by
    have hu (z : sl2R) : Function.update ![x] 0 z = ![z] := by ext k; fin_cases k; rfl
    have h := ω.map_update_smul ![x] 0 r x
    rwa [hu (r • x), hu x] at h
  have hJ : ω ![matJ] = 0 := hhor ![matJ] 0 matJ_mem_so2
  have hS : ω ![matS] = 0 := by
    have h := congrArg (fun f : sl2R [⋀^Fin 1]→ₗ[ℝ] trivialC ↦ f ![matH]) hinv
    rw [AlternatingMap.lie_apply, zero_apply, LieModule.IsTrivial.trivial,
      zero_sub, neg_eq_zero, Fin.sum_univ_one] at h
    have hupd : Function.update ![matH] 0 ⁅matJ, ![matH] 0⁆ = ![(2 : ℝ) • matS] := by
      funext k; fin_cases k; simp [lie_matJ_matH]
    rw [hupd, hsmul] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hH : ω ![matH] = 0 := by
    have h := congrArg (fun f : sl2R [⋀^Fin 1]→ₗ[ℝ] trivialC ↦ f ![matS]) hinv
    rw [AlternatingMap.lie_apply, zero_apply, LieModule.IsTrivial.trivial,
      zero_sub, neg_eq_zero, Fin.sum_univ_one] at h
    have hupd : Function.update ![matS] 0 ⁅matJ, ![matS] 0⁆ = ![(-2 : ℝ) • matH] := by
      funext k; fin_cases k; simp [lie_matJ_matS, neg_smul]
    rw [hupd, hsmul] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv, eq_cartan_decomp (v 0), one_cochain_linear_decomp, hJ, hH, hS]
  simp

/-- In degree `2`, every `so2`-horizontal `2`-cochain is automatically `so2`-invariant
(because `ad(J)` is traceless on `sl₂(ℝ) ⧸ so(2)`). -/
theorem lie_eq_zero_of_mem_horizontalCochain_two {ω : sl2R [⋀^Fin 2]→ₗ[ℝ] trivialC}
    (hω : ω ∈ horizontalCochain ℝ sl2R so2 trivialC 2) {x : sl2R} (hx : x ∈ so2) :
    ⁅x, ω⁆ = 0 := by
  rw [mem_so2_eq_smul_matJ hx, smul_lie]
  suffices hJ : ⁅matJ, ω⁆ = 0 by rw [hJ, smul_zero]
  set η : (sl2R ⧸ so2.toLieSubmodule) [⋀^Fin 2]→ₗ[ℝ] trivialC :=
    (horizontalCochainEquiv ℝ sl2R so2 trivialC 2).symm ⟨ω, hω⟩
  have hη : η.compLinearMap so2.toLieSubmodule.toSubmodule.mkQ = ω := by
    have h := congrArg Subtype.val
      ((horizontalCochainEquiv ℝ sl2R so2 trivialC 2).apply_symm_apply ⟨ω, hω⟩)
    rwa [horizontalCochainEquiv_apply_val] at h
  rw [← hη, lie_compLinearMap_mkQ (⟨matJ, matJ_mem_so2⟩ : so2) η]
  suffices hzero : ⁅(⟨matJ, matJ_mem_so2⟩ : so2), η⁆ = 0 by
    rw [hzero, AlternatingMap.zero_compLinearMap]
  refine (alternatingMapTopEquiv sl2QuotSo2Basis).injective ?_
  rw [map_zero, alternatingMapTopEquiv_apply, AlternatingMap.lie_apply]
  have htriv : ⁅(⟨matJ, matJ_mem_so2⟩ : so2), η sl2QuotSo2Basis⁆ = 0 :=
    LieModule.IsTrivial.trivial matJ (η sl2QuotSo2Basis)
  rw [htriv, zero_sub, neg_eq_zero, Fin.sum_univ_two]
  have h0 : ⁅(⟨matJ, matJ_mem_so2⟩ : so2), sl2QuotSo2Basis 0⁆ = (2 : ℝ) • sl2QuotSo2Basis 1 := by
    rw [sl2QuotSo2Basis_zero, sl2QuotSo2Basis_one]
    change LieSubmodule.Quotient.mk ⁅matJ, matH⁆ = _
    rw [lie_matJ_matH]
    rfl
  have h1 : ⁅(⟨matJ, matJ_mem_so2⟩ : so2), sl2QuotSo2Basis 1⁆ =
      -((2 : ℝ) • sl2QuotSo2Basis 0) := by
    rw [sl2QuotSo2Basis_zero, sl2QuotSo2Basis_one]
    change LieSubmodule.Quotient.mk ⁅matJ, matS⁆ = _
    rw [lie_matJ_matS]
    rfl
  have ht0 : η (Function.update sl2QuotSo2Basis 0 ((2 : ℝ) • sl2QuotSo2Basis 1)) = 0 := by
    rw [η.map_update_smul, η.map_eq_zero_of_eq _ (i := 0) (j := 1) (by simp) (by decide),
      smul_zero]
  have ht1 : η (Function.update sl2QuotSo2Basis 1 (-((2 : ℝ) • sl2QuotSo2Basis 0))) = 0 := by
    have : Function.update sl2QuotSo2Basis 1 (-((2 : ℝ) • sl2QuotSo2Basis 0)) =
        Function.update sl2QuotSo2Basis 1 ((-2 : ℝ) • sl2QuotSo2Basis 0) := by
      ext k; fin_cases k <;> simp
    rw [this, η.map_update_smul, η.map_eq_zero_of_eq _ (i := 0) (j := 1) (by simp) (by decide),
      smul_zero]
  rw [h0, h1, ht0, ht1, add_zero]

/-- In degree `2`, every `so2`-horizontal `2`-cochain is automatically `SO(2)`-equivariant
(because `g ∈ SO(2)` acts on `sl₂(ℝ) ⧸ so(2)` with determinant `(c² - s²)² + (2cs)² = 1`). -/
theorem mem_equivariantCochain_of_mem_horizontalCochain_two {ω : sl2R [⋀^Fin 2]→ₗ[ℝ] trivialC}
    (hω : ω ∈ horizontalCochain ℝ sl2R so2 trivialC 2) :
    ω ∈ equivariantCochain so2ConjRep trivialCRep 2 := by
  rw [mem_equivariantCochain_iff]
  intro g v
  set η : (sl2R ⧸ so2.toLieSubmodule) [⋀^Fin 2]→ₗ[ℝ] trivialC :=
    (horizontalCochainEquiv ℝ sl2R so2 trivialC 2).symm ⟨ω, hω⟩
  have hη : ∀ w : Fin 2 → sl2R,
      ω w = η (fun i ↦ LieSubmodule.Quotient.mk (w i)) := fun w ↦
    (horizontalCochainEquiv_symm_apply_mk ℝ sl2R so2 trivialC 2 ⟨ω, hω⟩ w).symm
  change ω v = ω (so2ConjRep g ∘ v)
  rw [hη v, hη (so2ConjRep g ∘ v)]
  let qg := quotientRepresentation so2 so2ConjRep (fun g _ h ↦ so2ConjRep_mem_so2 g h) g
  have hcomp : (fun i ↦ LieSubmodule.Quotient.mk (so2ConjRep g (v i))) =
      qg ∘ (fun i ↦ LieSubmodule.Quotient.mk (v i)) := by
    funext i
    exact (quotientRepresentation_apply_mk so2 so2ConjRep _ g (v i)).symm
  change η _ = η (fun i ↦ LieSubmodule.Quotient.mk (so2ConjRep g (v i)))
  rw [hcomp]
  suffices hmap : η.compLinearMap qg = η by
    exact (AlternatingMap.congr_fun hmap (fun i ↦ LieSubmodule.Quotient.mk (v i))).symm
  refine (alternatingMapTopEquiv sl2QuotSo2Basis).injective ?_
  rw [alternatingMapTopEquiv_apply, alternatingMapTopEquiv_apply,
    AlternatingMap.compLinearMap_apply]
  set c : ℝ := g.1 0 0
  set s : ℝ := g.1 1 0
  have hcs : c ^ 2 + s ^ 2 = 1 := (so2_entries g).2.2
  have hvec : (fun i ↦ qg (sl2QuotSo2Basis i)) =
      ![qg (sl2QuotSo2Basis 0), qg (sl2QuotSo2Basis 1)] := by
    ext k; fin_cases k <;> rfl
  have hbasis_vec : sl2QuotSo2Basis = ![sl2QuotSo2Basis 0, sl2QuotSo2Basis 1] := by
    ext k; fin_cases k <;> rfl
  have hswap : η ![sl2QuotSo2Basis 1, sl2QuotSo2Basis 0] = -η sl2QuotSo2Basis := by
    have hs := η.map_swap sl2QuotSo2Basis (show (0 : Fin 2) ≠ 1 by decide)
    have : sl2QuotSo2Basis ∘ Equiv.swap (0 : Fin 2) 1 =
        ![sl2QuotSo2Basis 1, sl2QuotSo2Basis 0] := by
      ext k; fin_cases k <;> rfl
    rwa [this] at hs
  rw [hvec, quotientRep_basis_zero g, quotientRep_basis_one g]
  have hlin : ∀ (a b d e : ℝ),
      η ![a • sl2QuotSo2Basis 0 + b • sl2QuotSo2Basis 1,
          d • sl2QuotSo2Basis 0 + e • sl2QuotSo2Basis 1] =
        (a * e - b * d) • η sl2QuotSo2Basis := by
    intro a b d e
    have h00 : η ![sl2QuotSo2Basis 0, sl2QuotSo2Basis 0] = 0 :=
      η.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
    have h11 : η ![sl2QuotSo2Basis 1, sl2QuotSo2Basis 1] = 0 :=
      η.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
    have hup0 (x y z : sl2R ⧸ so2.toLieSubmodule) :
        η ![x + y, z] = η ![x, z] + η ![y, z] := by
      have hu (w : sl2R ⧸ so2.toLieSubmodule) : Function.update ![x, z] 0 w = ![w, z] := by
        ext k; fin_cases k <;> rfl
      have h := η.map_update_add ![x, z] 0 x y
      rwa [hu (x + y), hu x, hu y] at h
    have hup1 (x y z : sl2R ⧸ so2.toLieSubmodule) :
        η ![x, y + z] = η ![x, y] + η ![x, z] := by
      have hu (w : sl2R ⧸ so2.toLieSubmodule) : Function.update ![x, y] 1 w = ![x, w] := by
        ext k; fin_cases k <;> rfl
      have h := η.map_update_add ![x, y] 1 y z
      rwa [hu (y + z), hu y, hu z] at h
    have hsm0 (r : ℝ) (x y : sl2R ⧸ so2.toLieSubmodule) :
        η ![r • x, y] = r • η ![x, y] := by
      have hu (w : sl2R ⧸ so2.toLieSubmodule) : Function.update ![x, y] 0 w = ![w, y] := by
        ext k; fin_cases k <;> rfl
      have h := η.map_update_smul ![x, y] 0 r x
      rwa [hu (r • x), hu x] at h
    have hsm1 (r : ℝ) (x y : sl2R ⧸ so2.toLieSubmodule) :
        η ![x, r • y] = r • η ![x, y] := by
      have hu (w : sl2R ⧸ so2.toLieSubmodule) : Function.update ![x, y] 1 w = ![x, w] := by
        ext k; fin_cases k <;> rfl
      have h := η.map_update_smul ![x, y] 1 r y
      rwa [hu (r • y), hu y] at h
    rw [hup0, hup1, hup1, hsm0, hsm0, hsm0, hsm0, hsm1, hsm1, hsm1, hsm1, h00, h11, hswap,
      ← hbasis_vec]
    simp only [smul_zero, zero_add, add_zero, smul_neg, smul_smul, sub_smul]
    abel
  rw [hlin]
  have hdet : (c ^ 2 - s ^ 2) * (c ^ 2 - s ^ 2) - 2 * c * s * -(2 * c * s) = 1 := by
    calc (c ^ 2 - s ^ 2) * (c ^ 2 - s ^ 2) - 2 * c * s * -(2 * c * s)
        = (c ^ 2 + s ^ 2) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [hcs]
      _ = 1 := one_pow 2
  rw [hdet, one_smul]

/-- In every degree `n`, `SO(2)`-equivariance on horizontal cochains implies `so2`-invariance,
so `C^n(sl₂(ℝ), so2, SO(2); ℂ) ≃ₗ[ℝ] Hom_{SO(2)}(⋀^n(sl₂(ℝ) ⧸ so2), ℂ)`. -/
theorem so2_equivariant_implies_invariance (n : ℕ) (ω : sl2R [⋀^Fin n]→ₗ[ℝ] trivialC)
    (hhor : ω ∈ horizontalCochain ℝ sl2R so2 trivialC n)
    (heq : ω ∈ equivariantCochain so2ConjRep trivialCRep n) :
    ∀ x ∈ so2, ⁅x, ω⁆ = 0 := by
  match n with
  | 0 =>
    intro x _
    ext v
    simp [AlternatingMap.lie_apply, LieModule.IsTrivial.trivial]
  | 1 =>
    rw [eq_zero_of_horizontal_equivariant_one hhor heq]
    intro x _
    exact lie_zero x
  | 2 =>
    intro x hx
    exact lie_eq_zero_of_mem_horizontalCochain_two hhor hx
  | k + 3 =>
    have hsub : Subsingleton ((sl2R ⧸ so2.toLieSubmodule) [⋀^Fin (k + 3)]→ₗ[ℝ] trivialC) :=
      subsingleton_alternatingMap_of_basis_lt sl2QuotSo2Basis (by omega)
    have hω0 : ω = 0 := by
      have hz : (horizontalCochainEquiv ℝ sl2R so2 trivialC (k + 3)).symm ⟨ω, hhor⟩ = 0 :=
        Subsingleton.elim _ _
      have h1 := congrArg (horizontalCochainEquiv ℝ sl2R so2 trivialC (k + 3)) hz
      rw [LinearEquiv.apply_symm_apply, map_zero] at h1
      exact congrArg Subtype.val h1
    rw [hω0]
    intro x _
    exact lie_zero x

/-- Identification of `(sl₂(ℝ), so(2), SO(2))`-relative `n`-cochains with
`Hom_{SO(2)}(⋀^n(sl₂(ℝ) ⧸ so(2)), ℂ)`. -/
noncomputable def sl2SO2CochainEquivIntertwiningMap (n : ℕ) :
    groupRelativeCochain so2 so2ConjRep trivialCRep n ≃ₗ[ℝ]
      Representation.IntertwiningMap
        ((quotientRepresentation so2 so2ConjRep
          (fun g _ h ↦ so2ConjRep_mem_so2 g h)).exteriorPower n) trivialCRep :=
  groupRelativeCochainEquivIntertwiningMap so2 so2ConjRep trivialCRep
    (fun g _ h ↦ so2ConjRep_mem_so2 g h) n (so2_equivariant_implies_invariance n)

/-- `H⁰(sl₂(ℝ), so(2); ℂ) ≃ₗ[ℝ] ℂ`. -/
noncomputable def sl2RelativeCohomologyZeroEquiv :
    relativeCohomology ℝ sl2R so2 trivialC 0 ≃ₗ[ℝ] ℂ :=
  relativeCohomologyZeroEquivOfIsTrivial ℝ sl2R so2 trivialC ≪≫ₗ
    TrivialLieModule.equiv ℝ sl2R ℂ

/-- `H¹(sl₂(ℝ), so(2); ℂ) = 0` (`Subsingleton`). -/
theorem sl2_subsingleton_relativeCohomology_one :
    Subsingleton (relativeCohomology ℝ sl2R so2 trivialC 1) := by
  have := subsingleton_relativeCochain_sl2_one
  exact subsingleton_relativeCohomology_of_subsingleton

/-- `H^q(sl₂(ℝ), so(2); ℂ) = 0` (`Subsingleton`) for all `q ≥ 3`. -/
theorem sl2_subsingleton_relativeCohomology_ge_three {q : ℕ} (hq : 3 ≤ q) :
    Subsingleton (relativeCohomology ℝ sl2R so2 trivialC q) := by
  have : Module.Free ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Free.of_basis sl2QuotSo2Basis
  have : Module.Finite ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Finite.of_basis sl2QuotSo2Basis
  exact subsingleton_relativeCohomology_of_finrank_lt (by rw [finrank_sl2QuotSo2]; omega)

/-- `H²(sl₂(ℝ), so(2); ℂ) ≃ₗ[ℝ] ℂ`. -/
noncomputable def sl2RelativeCohomologyTwoEquiv :
    relativeCohomology ℝ sl2R so2 trivialC 2 ≃ₗ[ℝ] ℂ := by
  have : Module.Free ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Free.of_basis sl2QuotSo2Basis
  have : Module.Finite ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Finite.of_basis sl2QuotSo2Basis
  have hsub1 : Subsingleton (relativeCochain ℝ sl2R so2 trivialC 1) :=
    subsingleton_relativeCochain_sl2_one
  have hsub3 : Subsingleton (relativeCochain ℝ sl2R so2 trivialC 3) :=
    subsingleton_relativeCochain_of_finrank_lt (by rw [finrank_sl2QuotSo2]; decide)
  have hrange : LinearMap.range (relativeDToCycles ℝ sl2R so2 trivialC 1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨ω, rfl⟩
    rw [Submodule.mem_bot, Subsingleton.elim ω 0, map_zero]
  have hcocycle : relativeCocycle ℝ sl2R so2 trivialC 2 =
      horizontalCochain ℝ sl2R so2 trivialC 2 := by
    ext ω
    rw [mem_relativeCocycle_iff]
    refine ⟨fun h ↦ relativeCochain_le_horizontalCochain 2 h.1, fun h ↦ ?_⟩
    have hrel : ω ∈ relativeCochain ℝ sl2R so2 trivialC 2 :=
      mem_relativeCochain_iff.mpr
        ⟨mem_horizontalCochain_iff.mp h, fun x hx ↦ lie_eq_zero_of_mem_horizontalCochain_two h hx⟩
    have hd : d ℝ sl2R trivialC 2 ω = 0 := by
      have hmem : d ℝ sl2R trivialC 2 ω ∈ relativeCochain ℝ sl2R so2 trivialC 3 :=
        d_mem_relativeCochain hrel
      exact congrArg (fun z : relativeCochain ℝ sl2R so2 trivialC 3 ↦ z.1)
        (Subsingleton.elim (⟨d ℝ sl2R trivialC 2 ω, hmem⟩ :
          relativeCochain ℝ sl2R so2 trivialC 3) 0)
    exact ⟨hrel, hd⟩
  exact (relativeCohomologySuccEquiv ℝ sl2R so2 trivialC 1) ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ hrange) ≪≫ₗ
    (LinearEquiv.ofEq _ _ hcocycle) ≪≫ₗ
    (horizontalCochainEquiv ℝ sl2R so2 trivialC 2).symm ≪≫ₗ
    alternatingMapTopEquiv sl2QuotSo2Basis ≪≫ₗ
    TrivialLieModule.equiv ℝ sl2R ℂ

/-- `H⁰(sl₂(ℝ), so(2), SO(2); ℂ) ≃ₗ[ℝ] ℂ`. -/
noncomputable def sl2SO2CohomologyZeroEquiv :
    groupRelativeCohomology so2 so2ConjRep trivialCRep
      so2ConjRep_map_lie trivialCRep_map_lie 0 ≃ₗ[ℝ] ℂ :=
  have htop :
      ((LieModule.maxTrivSubmodule ℝ sl2R trivialC).toSubmodule ⊓ trivialCRep.invariants :
        Submodule ℝ trivialC) = ⊤ := by
    rw [eq_top_iff]
    intro m _
    exact ⟨fun x ↦ LieModule.IsTrivial.trivial x m, fun _ ↦ rfl⟩
  groupRelativeCohomologyZeroEquiv so2 so2ConjRep trivialCRep
      so2ConjRep_map_lie trivialCRep_map_lie ≪≫ₗ
    (LinearEquiv.ofTop _ htop) ≪≫ₗ
    TrivialLieModule.equiv ℝ sl2R ℂ

private theorem subsingleton_groupRelativeCochain_sl2_one :
    Subsingleton (groupRelativeCochain so2 so2ConjRep trivialCRep 1) := by
  have h1 : Subsingleton (relativeCochain ℝ sl2R so2 trivialC 1) :=
    subsingleton_relativeCochain_sl2_one
  refine ⟨fun ω₁ ω₂ ↦ Subtype.ext ?_⟩
  have hEq : (⟨ω₁.1, (mem_groupRelativeCochain_iff.mp ω₁.2).1⟩ :
      relativeCochain ℝ sl2R so2 trivialC 1) =
    ⟨ω₂.1, (mem_groupRelativeCochain_iff.mp ω₂.2).1⟩ := Subsingleton.elim _ _
  exact congrArg (fun z : relativeCochain ℝ sl2R so2 trivialC 1 ↦ z.1) hEq

/-- `H¹(sl₂(ℝ), so(2), SO(2); ℂ) = 0` (`Subsingleton`). -/
theorem sl2SO2_subsingleton_cohomology_one :
    Subsingleton (groupRelativeCohomology so2 so2ConjRep trivialCRep
      so2ConjRep_map_lie trivialCRep_map_lie 1) := by
  have := subsingleton_groupRelativeCochain_sl2_one
  exact subsingleton_groupRelativeCohomology_of_subsingleton

/-- `H^q(sl₂(ℝ), so(2), SO(2); ℂ) = 0` (`Subsingleton`) for all `q ≥ 3`. -/
theorem sl2SO2_subsingleton_cohomology_ge_three {q : ℕ} (hq : 3 ≤ q) :
    Subsingleton (groupRelativeCohomology so2 so2ConjRep trivialCRep
      so2ConjRep_map_lie trivialCRep_map_lie q) := by
  have : Module.Free ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Free.of_basis sl2QuotSo2Basis
  have : Module.Finite ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Finite.of_basis sl2QuotSo2Basis
  exact subsingleton_groupRelativeCohomology_of_finrank_lt (by rw [finrank_sl2QuotSo2]; omega)

/-- `H²(sl₂(ℝ), so(2), SO(2); ℂ) ≃ₗ[ℝ] ℂ`, matching `H²(S²; ℂ) ≅ ℂ`. -/
noncomputable def sl2SO2CohomologyTwoEquiv :
    groupRelativeCohomology so2 so2ConjRep trivialCRep
      so2ConjRep_map_lie trivialCRep_map_lie 2 ≃ₗ[ℝ] ℂ := by
  have : Module.Free ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Free.of_basis sl2QuotSo2Basis
  have : Module.Finite ℝ (sl2R ⧸ so2.toLieSubmodule) :=
    Module.Finite.of_basis sl2QuotSo2Basis
  have hsub1 : Subsingleton (groupRelativeCochain so2 so2ConjRep trivialCRep 1) :=
    subsingleton_groupRelativeCochain_sl2_one
  have hsub3 : Subsingleton (groupRelativeCochain so2 so2ConjRep trivialCRep 3) :=
    subsingleton_groupRelativeCochain_of_finrank_lt (by rw [finrank_sl2QuotSo2]; decide)
  have hrange : LinearMap.range
      (groupRelativeDToCycles so2 so2ConjRep trivialCRep
        so2ConjRep_map_lie trivialCRep_map_lie 1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨ω, rfl⟩
    rw [Submodule.mem_bot, Subsingleton.elim ω 0, map_zero]
  have hcocycle : groupRelativeCocycle so2 so2ConjRep trivialCRep 2 =
      horizontalCochain ℝ sl2R so2 trivialC 2 := by
    ext ω
    rw [mem_groupRelativeCocycle_iff]
    refine ⟨fun h ↦ relativeCochain_le_horizontalCochain 2
      (mem_groupRelativeCochain_iff.mp h.1).1, fun h ↦ ?_⟩
    have hrel : ω ∈ relativeCochain ℝ sl2R so2 trivialC 2 :=
      mem_relativeCochain_iff.mpr
        ⟨mem_horizontalCochain_iff.mp h, fun x hx ↦ lie_eq_zero_of_mem_horizontalCochain_two h hx⟩
    have heq : ω ∈ equivariantCochain so2ConjRep trivialCRep 2 :=
      mem_equivariantCochain_of_mem_horizontalCochain_two h
    have hgrel : ω ∈ groupRelativeCochain so2 so2ConjRep trivialCRep 2 :=
      mem_groupRelativeCochain_iff.mpr ⟨hrel, heq⟩
    have hd : d ℝ sl2R trivialC 2 ω = 0 := by
      have hmem : d ℝ sl2R trivialC 2 ω ∈ groupRelativeCochain so2 so2ConjRep trivialCRep 3 :=
        d_mem_groupRelativeCochain so2ConjRep_map_lie trivialCRep_map_lie hgrel
      exact congrArg (fun z : groupRelativeCochain so2 so2ConjRep trivialCRep 3 ↦ z.1)
        (Subsingleton.elim (⟨d ℝ sl2R trivialC 2 ω, hmem⟩ :
          groupRelativeCochain so2 so2ConjRep trivialCRep 3) 0)
    exact ⟨hgrel, hd⟩
  exact (groupRelativeCohomologySuccEquiv so2 so2ConjRep trivialCRep
      so2ConjRep_map_lie trivialCRep_map_lie 1) ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ hrange) ≪≫ₗ
    (LinearEquiv.ofEq _ _ hcocycle) ≪≫ₗ
    (horizontalCochainEquiv ℝ sl2R so2 trivialC 2).symm ≪≫ₗ
    alternatingMapTopEquiv sl2QuotSo2Basis ≪≫ₗ
    TrivialLieModule.equiv ℝ sl2R ℂ

end TauCeti.Examples.ChevalleyEilenberg
