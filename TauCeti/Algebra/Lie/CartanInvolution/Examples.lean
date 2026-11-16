/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
public import TauCeti.Algebra.Lie.SpecialLinear.Cartan
public import TauCeti.Algebra.Lie.Symplectic.Cartan
public import TauCeti.Algebra.Lie.Sl2.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.Sl2.Killing
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# Classical witnesses and non-examples for Cartan involutions

This module verifies `LieEquiv.IsCartanInvolution` and `LieEquiv.IsReductiveCartanInvolution` on
concrete matrix Lie algebras over ordered fields (including `ℝ`):

1. **Symplectic Lie algebra `sp l K`:** `X ↦ -Xᵀ` (`LieAlgebra.Symplectic.cartanInvolution`) is a
   Cartan involution.
2. **Special linear Lie algebra `sl (Fin 2) K`:** `X ↦ -Xᵀ`
   (`LieAlgebra.SpecialLinear.cartanInvolution`) has fixed subalgebra `𝔨 = 𝔰𝔬(2)` (skew-symmetric
   trace-zero matrices), `-1`-eigenspace `𝔭` consisting of symmetric trace-zero matrices, twisted
   Killing form `B_θ (X, Y) = 4 tr (X Yᵀ)`, and satisfies `IsCartanInvolution`.
3. **Non-example (`θ = id` on `sl (Fin 2) K`):** the identity automorphism is involutive, yet
   `B_id (H, H) = -8 < 0` on `H = diag (1, -1)`, so `LieEquiv.refl` is neither a Cartan involution
   nor a reductive Cartan involution.
4. **Abelian `1 × 1` matrices `Matrix (Fin 1) (Fin 1) K`:** every involutive automorphism is a
   reductive Cartan involution, and none is a semisimple Cartan involution.
5. **General linear Lie algebra `Matrix (Fin 2) (Fin 2) K = 𝔤𝔩₂(K)`:** `X ↦ -Xᵀ`
   (`TauCeti.negTransposeLieEquiv`) is a reductive Cartan involution on an algebra with both
   nontrivial centre and nontrivial derived ideal, and is not a semisimple Cartan involution.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–§2 and Chapter VII, §2.
-/

public section

open LieAlgebra Matrix

/-! ### Symplectic Lie algebra `sp l K` -/

namespace LieAlgebra.Symplectic

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Negative transpose `X ↦ -Xᵀ` is a Cartan involution of `sp l K`** over any ordered field. -/
theorem isCartanInvolution_cartanInvolution (l K : Type*) [Fintype l] [DecidableEq l]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (cartanInvolution l K).IsCartanInvolution :=
  (LieEquiv.isCartanInvolution_def _).mpr
    ⟨cartanInvolution_cartanInvolution,
      fun _ hX ↦ Left.neg_pos_iff.mpr (killingForm_cartanInvolution_self_neg hX)⟩

/-- Negative transpose on `sp l K` is also a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_cartanInvolution (l K : Type*) [Fintype l] [DecidableEq l]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (cartanInvolution l K).IsReductiveCartanInvolution :=
  (isCartanInvolution_cartanInvolution l K).isReductiveCartanInvolution

end LieAlgebra.Symplectic

/-! ### Special linear Lie algebra `sl n` and `sl (Fin 2)` -/

namespace LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The fixed subalgebra `𝔨` of `cartanInvolution n R` on `sl n R` consists of the skew-symmetric
trace-zero matrices (`𝔰𝔬(n)`). -/
theorem mem_fixedSubalgebra_cartanInvolution_iff {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] {X : sl n R} :
    X ∈ (cartanInvolution n R).toLieHom.fixedSubalgebra ↔
      (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, cartanInvolution_eq_self_iff]

/-- The `-1`-eigenspace `𝔭` of `cartanInvolution n R` on `sl n R` consists of the symmetric
trace-zero matrices. -/
theorem mem_cartanP_cartanInvolution_iff {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] {X : sl n R} :
    X ∈ (cartanInvolution n R).cartanP ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) := by
  rw [LieEquiv.mem_cartanP_iff, cartanInvolution_eq_neg_iff]

/-- On `sl (Fin 2) R`, the twisted Killing form of `X ↦ -Xᵀ` is `4 tr (X Yᵀ)`. -/
theorem cartanBilinForm_cartanInvolution_fin_two {R : Type*} [CommRing R]
    (X Y : sl (Fin 2) R) :
    (cartanInvolution (Fin 2) R).cartanBilinForm X Y = 4 * (X.val * Y.valᵀ).trace := by
  rw [LieEquiv.cartanBilinForm_apply, TauCeti.killingForm_slFinTwo_apply, coe_cartanInvolution,
    mul_neg, trace_neg, mul_neg, neg_neg]

/-- **Negative transpose `X ↦ -Xᵀ` is a Cartan involution of `sl (Fin 2) K`** over any ordered
field. -/
theorem isCartanInvolution_cartanInvolution_fin_two (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] :
    (cartanInvolution (Fin 2) K).IsCartanInvolution := by
  refine (LieEquiv.isCartanInvolution_def _).mpr ⟨involutive_cartanInvolution, fun X hX ↦ ?_⟩
  rw [← LieEquiv.cartanBilinForm_apply, cartanBilinForm_cartanInvolution_fin_two]
  obtain ⟨i, j, hij⟩ : ∃ i j, X.val i j ≠ 0 := by
    by_contra! h
    exact hX (Subtype.ext (Matrix.ext h))
  have htr : 0 < (X.val * X.valᵀ).trace := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
        ⟨j, Finset.mem_univ _, mul_self_pos.mpr hij⟩⟩
  positivity

/-- For the identity automorphism on `sl (Fin 2) R`, the twisted Killing form evaluates to `-8` on
the standard Cartan generator `H = diag (1, -1)`. -/
theorem cartanBilinForm_refl_slFinTwoBasis_two (R : Type*) [CommRing R] :
    (LieEquiv.refl : sl (Fin 2) R ≃ₗ⁅R⁆ sl (Fin 2) R).cartanBilinForm
      (TauCeti.slFinTwoBasis R 2) (TauCeti.slFinTwoBasis R 2) = -8 := by
  rw [LieEquiv.cartanBilinForm_apply, LieEquiv.refl_apply, TauCeti.killingForm_slFinTwoBasis 2 2]
  rfl

/-- **Non-example:** the identity automorphism of `sl (Fin 2) K` is not a Cartan involution over any
ordered field. -/
theorem not_isCartanInvolution_refl_sl_fin_two (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] :
    ¬ (LieEquiv.refl : sl (Fin 2) K ≃ₗ⁅K⁆ sl (Fin 2) K).IsCartanInvolution := by
  intro h
  have hH : TauCeti.slFinTwoBasis K 2 ≠ 0 := (TauCeti.slFinTwoBasis K).ne_zero 2
  have hpos := h.cartanBilinForm_self_pos hH
  rw [cartanBilinForm_refl_slFinTwoBasis_two K] at hpos
  linarith

/-- The identity automorphism of `sl (Fin 2) K` is not a reductive Cartan involution either. -/
theorem not_isReductiveCartanInvolution_refl_sl_fin_two (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] :
    ¬ (LieEquiv.refl : sl (Fin 2) K ≃ₗ⁅K⁆ sl (Fin 2) K).IsReductiveCartanInvolution := by
  rw [LieEquiv.isReductiveCartanInvolution_iff_isCartanInvolution]
  exact not_isCartanInvolution_refl_sl_fin_two K

end LieAlgebra.SpecialLinear

/-! ### Abelian `1 × 1` matrices and reductive `𝔤𝔩₂` -/

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-- `negTransposeLieEquiv n R` is involutive. -/
theorem involutive_negTransposeLieEquiv (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] :
    Function.Involutive (negTransposeLieEquiv n R) := fun X ↦ by
  simp

/-- On the abelian Lie algebra `Matrix (Fin 1) (Fin 1) R`, every involutive automorphism is a
reductive Cartan involution, and over a nontrivial preordered ring none is a semisimple Cartan
involution. -/
theorem isReductiveCartanInvolution_iff_matrix_fin_one {R : Type*} [CommRing R] [Preorder R]
    {θ : Matrix (Fin 1) (Fin 1) R ≃ₗ⁅R⁆ Matrix (Fin 1) (Fin 1) R} :
    θ.IsReductiveCartanInvolution ↔ Function.Involutive θ := by
  have habel : IsLieAbelian (Matrix (Fin 1) (Fin 1) R) :=
    (LieAlgebra.isLieAbelian_iff_center_eq_top R _).mpr center_matrix_eq_top
  exact θ.isReductiveCartanInvolution_iff_involutive

/-- No automorphism of `Matrix (Fin 1) (Fin 1) R` over a nontrivial preordered ring is a semisimple
Cartan involution. -/
theorem not_isCartanInvolution_matrix_fin_one {R : Type*} [CommRing R] [Preorder R] [Nontrivial R]
    {θ : Matrix (Fin 1) (Fin 1) R ≃ₗ⁅R⁆ Matrix (Fin 1) (Fin 1) R} :
    ¬ θ.IsCartanInvolution := by
  have habel : IsLieAbelian (Matrix (Fin 1) (Fin 1) R) :=
    (LieAlgebra.isLieAbelian_iff_center_eq_top R _).mpr center_matrix_eq_top
  exact θ.not_isCartanInvolution_of_isLieAbelian

/-- **Mixed reductive witness:** negative transpose `X ↦ -Xᵀ` is a reductive Cartan involution of
`Matrix (Fin 2) (Fin 2) K = 𝔤𝔩₂(K)` over any ordered field. -/
theorem isReductiveCartanInvolution_negTransposeLieEquiv_fin_two (K : Type*) [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] :
    (negTransposeLieEquiv (Fin 2) K).IsReductiveCartanInvolution := by
  refine (LieEquiv.isReductiveCartanInvolution_def _).mpr
    ⟨involutive_negTransposeLieEquiv (Fin 2) K, ?_⟩
  have hmem (A : Matrix (Fin 2) (Fin 2) K) :
      A ∈ derivedSeries K (Matrix (Fin 2) (Fin 2) K) 1 ↔ A ∈ SpecialLinear.sl (Fin 2) K := by
    rw [derivedSeries_one_eq_slIdeal, mem_slIdeal_iff, SpecialLinear.mem_sl_iff]
  let e : derivedSeries K (Matrix (Fin 2) (Fin 2) K) 1 ≃ₗ⁅K⁆ SpecialLinear.sl (Fin 2) K :=
    { toFun := fun X ↦ ⟨X.1, (hmem X.1).mp X.2⟩
      invFun := fun Y ↦ ⟨Y.1, (hmem Y.1).mpr Y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := Subtype.ext (by
        simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket,
          LieSubalgebra.coe_bracket]) }
  have he : (SpecialLinear.cartanInvolution (Fin 2) K).toLieHom.comp e.toLieHom =
      e.toLieHom.comp ((negTransposeLieEquiv (Fin 2) K).restrictDerivedSeries 1).toLieHom :=
    LieHom.ext fun X ↦ Subtype.ext <| by
      simp [e]
  exact (LieEquiv.isCartanInvolution_iff_of_intertwines e he).mpr
    (SpecialLinear.isCartanInvolution_cartanInvolution_fin_two K)

/-- Negative transpose on `Matrix (Fin 2) (Fin 2) K = 𝔤𝔩₂(K)` is **not** a semisimple Cartan
involution, because `𝔤𝔩₂(K)` has nontrivial centre. -/
theorem not_isCartanInvolution_negTransposeLieEquiv_fin_two (K : Type*) [Field K]
    [LinearOrder K] :
    ¬ (negTransposeLieEquiv (Fin 2) K).IsCartanInvolution :=
  fun hθ ↦ center_matrix_ne_bot K (Fin 2) hθ.center_eq_bot

end TauCeti
