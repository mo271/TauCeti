/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.BarTensorProduct.Basic
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Cohomology

/-!
# Explicit Taylor map and operations of the bar tensor product

This module exposes the explicit operations of the bar tensor product `MM.barTensorProduct NN`
on `(M ⊗ Tᶜ(sB)) ⊗ N`:

* `TauCeti.AInfinityBimodule.barTensorProduct_taylor_tmul`: the exact three-term formula for the
  Taylor map on arbitrary words `((w_A ⊗ ((m ⊗ w_B) ⊗ n)) ⊗ w_C)`.
* `TauCeti.AInfinityBimodule.barTensorProduct_taylor_tmul_one`: specialization to the empty middle
  word `w_B = 1`.
* `TauCeti.AInfinityBimodule.barTensorProduct_b_eq_zero_of_pos` and
  `barTensorProduct_m_eq_zero_of_pos`: vanishing of all mixed operations `b_{i,j}` and `m_{i,j}`
  with `0 < i` and `0 < j`.
* `TauCeti.AInfinityBimodule.barTensorProduct_differential_tmul_one` and
  `barTensorProduct_differential_tmul_of_one`: the unary differential on empty and single-letter
  middle words (recovering the standard two-term tensor differential and five-term bar complex
  formula).
* `TauCeti.AInfinityBimodule.barTensorProduct_m_pos_zero_tmul_one`,
  `barTensorProduct_m_zero_pos_tmul_one`, and `barTensorProduct_m_zero_one_tmul_one`:
  the left and right outer actions on `(m ⊗ 1) ⊗ n`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped BigOperators TensorProduct

namespace TauCeti.AInfinityBimodule

universe uR uA uB uC uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- The counit of `TensorWords` is invariant under every letterwise map. -/
private theorem counit_tensorWords_map {X : Type*} [AddCommGroup X] [Module R X]
    (f : X →ₗ[R] X) (w : TensorWords R X) :
    Coalgebra.counit (R := R) (TensorWords.map f w) = Coalgebra.counit (R := R) w := by
  simpa only [TensorWords.counit_eq_counit, LinearMap.comp_apply] using
    LinearMap.congr_fun (TensorWords.counit_comp_map f) w

/-- The counit of `TensorWords` is invariant under the suspended Koszul twist. -/
private theorem counit_koszulTwist {X : Type*} [AddCommGroup X] [Module R X]
    (G : InternalGrading R X ℤ) (w : TensorWords R X) :
    Coalgebra.counit (R := R) ((TensorWords.grading (G.shift 1)).koszulTwist 1 w) =
      Coalgebra.counit (R := R) w := by
  rw [TensorWords.koszulTwist_grading]
  exact counit_tensorWords_map _ w

/-- Applying `taylorProj` after `barTensorSignTwist` leaves the middle factor untouched and applies
the unsuspended twist `GN.koszulTwist 1` to `N`. -/
private theorem taylorProj_comp_barTensorSignTwist (GC : InternalGrading R C ℤ)
    (GN : InternalGrading R N ℤ) :
    taylorProj R A C ((M ⊗[R] TensorWords R B) ⊗[R] N) ∘ₗ
      barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN =
      (GN.koszulTwist 1).lTensor (M ⊗[R] TensorWords R B) ∘ₗ
        taylorProj R A C ((M ⊗[R] TensorWords R B) ⊗[R] N) := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.comp_apply, barTensorSignTwist_tmul, taylorProj_tmul, counit_koszulTwist,
    map_smul, LinearMap.lTensor_tmul]

/-- Conjugating `NN.taylor` by the unsuspended twists on `N` and `Tᶜ(sC)` negates it and transfers
the twist to `Tᶜ(sB)`. -/
private theorem koszulTwist_comp_taylor_right (NN : AInfinityBimodule BB CC N)
    (wB : TensorWords R B) (n : N) (wC : TensorWords R C) :
    NN.grading.koszulTwist 1
        (NN.taylor ((wB ⊗ₜ NN.grading.koszulTwist 1 n) ⊗ₜ
          (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC)) =
      -NN.taylor (((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 wB ⊗ₜ n) ⊗ₜ wC) := by
  have h := LinearMap.congr_fun (NN.isHomogeneous_taylor.koszulTwist_comp_eq_smul 1)
    ((wB ⊗ₜ NN.grading.koszulTwist 1 n) ⊗ₜ
      (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC)
  simp only [one_mul, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
    LinearMap.comp_apply, neg_one_smul, LinearMap.neg_apply, barGrading_def,
    InternalGrading.koszulTwist_tensorProduct, TensorProduct.map_tmul,
    InternalGrading.koszulTwist_koszulTwist, InternalGrading.koszulTwist_one_shift_one] at h
  rw [← neg_one_smul R n, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul,
    neg_one_smul R, neg_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Contribution of `barTensorLeftDiff` to the Taylor map of `MM.barTensorProduct NN`. -/
private theorem taylorProj_barTensorLeftDiff (MM : AInfinityBimodule AA BB M)
    (GN : InternalGrading R N ℤ) (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    (GN.koszulTwist 1).lTensor (M ⊗[R] TensorWords R B)
      (taylorProj R A C ((M ⊗[R] TensorWords R B) ⊗[R] N)
        (barTensorLeftDiff MM C N
          ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ GN.koszulTwist 1 n)) ⊗ₜ
            (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC))) =
      Coalgebra.counit (R := R) wC •
        (((MM.taylor.rTensor (TensorWords R B) ∘ₗ
          Comodule.cofreeCoact R (TensorWords R B) (TensorWords R A ⊗[R] M))
            ((wA ⊗ₜ m) ⊗ₜ wB)) ⊗ₜ n) -
      Coalgebra.counit (R := R) wA • Coalgebra.counit (R := R) wC •
        ((MM.grading.koszulTwist 1 m ⊗ₜ BB.coaugmentedBarDifferential wB) ⊗ₜ n) := by
  have hcA : ∀ z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B,
      (GN.koszulTwist 1).lTensor (M ⊗[R] TensorWords R B)
        (taylorProj R A C ((M ⊗[R] TensorWords R B) ⊗[R] N)
          ((barTensorAssocLeft R A B C M N).symm
            (z ⊗ₜ (GN.koszulTwist 1 n ⊗ₜ
              (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC)))) =
      Coalgebra.counit (R := R) wC •
        (((Comodule.leftCofreeCounit R (TensorWords R A) M).rTensor (TensorWords R B) z) ⊗ₜ n) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, smul_add, hx, hy]
    | tmul u v =>
      induction u using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, smul_add, hx, hy]
      | tmul a b =>
        simp only [barTensorAssocLeft_symm_tmul, taylorProj_tmul, counit_koszulTwist,
          LinearMap.lTensor_tmul, InternalGrading.koszulTwist_koszulTwist, LinearMap.rTensor_tmul,
          Comodule.leftCofreeCounit_tmul, TensorProduct.smul_tmul']
  simp only [barTensorLeftDiff_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    barTensorAssocLeft_tmul, LinearMap.rTensor_tmul]
  rw [hcA, MM.barDifferential_eq, gradedCoderiv_def]
  simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.add_tmul,
    smul_add, ← LinearMap.rTensor_comp_apply, leftCofreeCounit_comp_leftTaylor,
    ← Comodule.cofreeCoact_def, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    TensorProduct.map_tmul, Comodule.leftCofreeCounit_tmul, counit_tensorWords_map,
    InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply,
    ← TensorProduct.smul_tmul', TensorProduct.neg_tmul, smul_neg]
  rw [smul_comm (Coalgebra.counit (R := R) wC) (Coalgebra.counit (R := R) wA)]
  abel

/-- Contribution of `barTensorMidDiff` to the Taylor map of `MM.barTensorProduct NN`. -/
private theorem taylorProj_barTensorMidDiff (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    (GN.koszulTwist 1).lTensor (M ⊗[R] TensorWords R B)
      (taylorProj R A C ((M ⊗[R] TensorWords R B) ⊗[R] N)
        (barTensorMidDiff AA.grading BB GM C N
          ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ GN.koszulTwist 1 n)) ⊗ₜ
            (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC))) =
      -(Coalgebra.counit (R := R) wA • Coalgebra.counit (R := R) wC •
        ((GM.koszulTwist 1 m ⊗ₜ BB.coaugmentedBarDifferential wB) ⊗ₜ n)) := by
  simp only [barTensorMidDiff_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    barTensorAssocMid_tmul, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    InternalGrading.koszulTwist_tensorProduct, barTensorAssocMid_symm_tmul, taylorProj_tmul,
    counit_koszulTwist, map_neg, map_smul, LinearMap.lTensor_tmul,
    InternalGrading.koszulTwist_koszulTwist, InternalGrading.koszulTwist_one_shift_one,
    LinearMap.neg_apply, TensorProduct.neg_tmul, smul_neg]
  rw [smul_comm]

/-- Helper pushing the two-sided counit projection past `barTensorAssocRight.symm`. -/
private theorem taylorProj_assocRight_symm (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) (wA : TensorWords R A) (m : M)
    (z : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C) :
    (GN.koszulTwist 1).lTensor (M ⊗[R] TensorWords R B)
      (taylorProj R A C ((M ⊗[R] TensorWords R B) ⊗[R] N)
        ((barTensorAssocRight R A B C M N).symm
          (((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1 wA ⊗ₜ
            (GM.shift 1).koszulTwist 1 m) ⊗ₜ z))) =
      -(Coalgebra.counit (R := R) wA •
        ((TensorProduct.assoc R M (TensorWords R B) N).symm
          (GM.koszulTwist 1 m ⊗ₜ
            ((GN.koszulTwist 1).lTensor (TensorWords R B)
              (((TensorProduct.rid R (TensorWords R B ⊗[R] N)).toLinearMap ∘ₗ
                (Coalgebra.counit (R := R) (A := TensorWords R C)).lTensor
                  (TensorWords R B ⊗[R] N)) z))))) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, neg_add, hx, hy]
  | tmul bn c =>
    induction bn using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add, neg_add,
        hx, hy]
    | tmul b n' =>
      rw [InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply,
        ← neg_one_smul R (GM.koszulTwist 1 m), TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul]
      simp only [barTensorAssocRight_symm_tmul, taylorProj_tmul, counit_koszulTwist,
        LinearMap.lTensor_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
        TensorProduct.assoc_symm_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      rw [smul_comm (Coalgebra.counit (R := R) wA), neg_one_smul R,
        TensorProduct.neg_tmul, TensorProduct.neg_tmul]

/-- Sign transformation on the `NN.taylor` summand of `leftTaylor BB NN.taylor`. -/
private theorem koszulTwist_lTensor_leftTaylor_fst (NN : AInfinityBimodule BB CC N)
    (wB : TensorWords R B) (n : N) (wC : TensorWords R C) :
    (NN.grading.koszulTwist 1).lTensor (TensorWords R B)
      (TensorProduct.map (TensorWords.map ((BB.grading.shift 1).koszulTwist 1)) NN.taylor
        (Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R B) N)
          ((wB ⊗ₜ NN.grading.koszulTwist 1 n) ⊗ₜ
            (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC))) =
      (-1 : R) • NN.taylor.lTensor (TensorWords R B)
        (Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R B) N)
          (((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 wB ⊗ₜ n) ⊗ₜ wC)) := by
  have hτB : Coalgebra.comul ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 wB) =
      TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1)
        ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1) (Coalgebra.comul wB) := by
    have h := LinearMap.congr_fun
      (TensorWords.deconcatenation_natural ((BB.grading.shift 1).koszulTwist 1)) wB
    simpa only [TensorWords.koszulTwist_grading, TensorWords.comul_eq_deconcatenation,
      LinearMap.comp_apply] using h
  simp only [Comodule.leftCoactRTensor_tmul, Comodule.leftCofreeCoact_tmul, hτB]
  induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.add_tmul, map_add, smul_add, hu, hv]
  | tmul u v =>
    simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      ← TensorWords.koszulTwist_grading, koszulTwist_comp_taylor_right]
    rw [← neg_one_smul R (NN.taylor _), TensorProduct.tmul_smul]

/-- Applying the right counit to `NN.barDifferential` recovers `leftTaylor BB NN.taylor`. -/
private theorem rid_comp_lTensor_counit_comp_barDifferential (NN : AInfinityBimodule BB CC N) :
    ((TensorProduct.rid R (TensorWords R B ⊗[R] N)).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R C)).lTensor (TensorWords R B ⊗[R] N)) ∘ₗ
      NN.barDifferential = leftTaylor BB NN.taylor := by
  refine TensorProduct.ext' fun bn wC ↦ ?_
  have hεbC : Coalgebra.counit (R := R) (CC.coaugmentedBarDifferential wC) = 0 := by
    simpa only [TensorWords.counit_eq_counit, LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun CC.isGradedCoderivation_coaugmentedBarDifferential.counit_comp wC
  have h1 : ∀ z : TensorWords R C ⊗[R] TensorWords R C,
      ((TensorProduct.rid R (TensorWords R B ⊗[R] N)).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R C)).lTensor (TensorWords R B ⊗[R] N))
        ((leftTaylor BB NN.taylor).rTensor (TensorWords R C)
          ((TensorProduct.assoc R (TensorWords R B ⊗[R] N) (TensorWords R C)
            (TensorWords R C)).symm (bn ⊗ₜ z))) =
        leftTaylor BB NN.taylor
          (bn ⊗ₜ TensorProduct.rid R (TensorWords R C)
            ((Coalgebra.counit (R := R) (A := TensorWords R C)).lTensor (TensorWords R C) z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul a b =>
      simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
        LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
        TensorProduct.tmul_smul, map_smul]
  have hcu : (Coalgebra.counit (R := R) (A := TensorWords R C)).lTensor (TensorWords R C)
      (Coalgebra.comul wC) = wC ⊗ₜ (1 : R) := by
    have hc := LinearMap.congr_fun
      (Coalgebra.lTensor_counit_comp_comul (R := R) (A := TensorWords R C)) wC
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply] using hc
  rw [LinearMap.comp_apply, NN.barDifferential_eq, gradedCoderiv_def, LinearMap.add_apply, map_add]
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, h1, hcu, TensorProduct.rid_tmul, one_smul, hεbC,
    TensorProduct.tmul_zero, map_zero, add_zero]

/-- Contribution of `barTensorRightDiff` to the Taylor map of `MM.barTensorProduct NN`. -/
private theorem taylorProj_barTensorRightDiff (GM : InternalGrading R M ℤ)
    (NN : AInfinityBimodule BB CC N) (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    (NN.grading.koszulTwist 1).lTensor (M ⊗[R] TensorWords R B)
      (taylorProj R A C ((M ⊗[R] TensorWords R B) ⊗[R] N)
        (barTensorRightDiff AA.grading GM NN
          ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ NN.grading.koszulTwist 1 n)) ⊗ₜ
            (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC))) =
      -(Coalgebra.counit (R := R) wA • Coalgebra.counit (R := R) wC •
        ((GM.koszulTwist 1 m ⊗ₜ BB.coaugmentedBarDifferential wB) ⊗ₜ n)) +
      Coalgebra.counit (R := R) wA •
        ((TensorProduct.assoc R M (TensorWords R B) N).symm
          (GM.koszulTwist 1 m ⊗ₜ
            (NN.taylor.lTensor (TensorWords R B)
              (Comodule.leftCoactRTensor (TensorWords R C)
                (Comodule.leftCofreeCoact R (TensorWords R B) N)
                ((((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 wB) ⊗ₜ n) ⊗ₜ
                  wC))))) := by
  have hneg : ∀ z : (M ⊗[R] TensorWords R B) ⊗[R] N, -((-1 : R) • z) = z := fun z ↦ by
    rw [neg_eq_iff_add_eq_zero]
    calc
      (-1 : R) • z + z = (-1 : R) • z + (1 : R) • z := by rw [one_smul]
      _ = ((-1 : R) + 1) • z := (add_smul _ _ _).symm
      _ = 0 := by rw [neg_add_cancel, zero_smul]
  simp only [barTensorRightDiff_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    barTensorAssocRight_tmul, TensorProduct.map_tmul, InternalGrading.koszulTwist_tensorProduct]
  rw [taylorProj_assocRight_symm (AA := AA) GM NN.grading wA m]
  have hval := LinearMap.congr_fun (rid_comp_lTensor_counit_comp_barDifferential NN)
    ((wB ⊗ₜ NN.grading.koszulTwist 1 n) ⊗ₜ
      (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 wC)
  rw [LinearMap.comp_apply] at hval
  rw [hval, leftTaylor_def]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, TensorProduct.tmul_add,
    smul_add, neg_add, koszulTwist_lTensor_leftTaylor_fst, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul, counit_koszulTwist, LinearMap.rTensor_tmul,
    TensorProduct.tmul_smul, map_smul, InternalGrading.koszulTwist_koszulTwist,
    TensorProduct.assoc_symm_tmul]
  rw [add_comm, smul_comm (Coalgebra.counit (R := R) wA) (-1 : R), hneg]

/-- Explicit three-term formula for the Taylor map of `MM.barTensorProduct NN`:
a left action term from `MM.taylor`, a subtracted middle coalgebra differential term from
`BB.coaugmentedBarDifferential`, and a twisted right action term from `NN.taylor`. -/
theorem barTensorProduct_taylor_tmul (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N)
    (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N) (wC : TensorWords R C) :
    (MM.barTensorProduct NN).taylor ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) =
      Coalgebra.counit (R := R) wC •
        (((MM.taylor.rTensor (TensorWords R B) ∘ₗ
          Comodule.cofreeCoact R (TensorWords R B) (TensorWords R A ⊗[R] M))
            ((wA ⊗ₜ m) ⊗ₜ wB)) ⊗ₜ n) -
      Coalgebra.counit (R := R) wA • Coalgebra.counit (R := R) wC •
        ((MM.grading.koszulTwist 1 m ⊗ₜ BB.coaugmentedBarDifferential wB) ⊗ₜ n) +
      Coalgebra.counit (R := R) wA •
        ((TensorProduct.assoc R M (TensorWords R B) N).symm
          (MM.grading.koszulTwist 1 m ⊗ₜ
            (NN.taylor.lTensor (TensorWords R B)
              (Comodule.leftCoactRTensor (TensorWords R C)
                (Comodule.leftCofreeCoact R (TensorWords R B) N)
                ((((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 wB) ⊗ₜ n) ⊗ₜ
                  wC))))) := by
  have hproj := LinearMap.congr_fun
    (taylorProj_comp_barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading)
  simp only [LinearMap.comp_apply] at hproj
  rw [AInfinityBimodule.taylor_def, barTensorProduct_barDifferential, barTensorDifferential_def,
    LinearMap.comp_apply, LinearMap.comp_apply, hproj]
  simp only [barTensorRawDifferential_def, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.add_apply, map_sub, map_add, barTensorSignTwist_tmul,
    taylorProj_barTensorLeftDiff (CC := CC), taylorProj_barTensorMidDiff (AA := AA) (BB := BB)
      (CC := CC), taylorProj_barTensorRightDiff (AA := AA)]
  abel

/-- On empty middle words, the Taylor map splits into the left Taylor map of `MM` and the
Koszul-twisted right Taylor map of `NN`. -/
theorem barTensorProduct_taylor_tmul_one (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N)
    (wA : TensorWords R A) (m : M) (n : N) (wC : TensorWords R C) :
    (MM.barTensorProduct NN).taylor ((wA ⊗ₜ ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n)) ⊗ₜ wC) =
      Coalgebra.counit (R := R) wC • ((MM.taylor ((wA ⊗ₜ m) ⊗ₜ 1) ⊗ₜ 1) ⊗ₜ n) +
      Coalgebra.counit (R := R) wA •
        ((MM.grading.koszulTwist 1 m ⊗ₜ 1) ⊗ₜ NN.taylor ((1 ⊗ₜ n) ⊗ₜ wC)) := by
  rw [barTensorProduct_taylor_tmul]
  simp [BB.coaugmentedBarDifferential_one, Comodule.cofreeCoact_tmul,
    Comodule.leftCoactRTensor_tmul, Comodule.leftCofreeCoact_tmul,
    TensorWords.comul_eq_deconcatenation, TensorWords.deconcatenation_one]

/-- Every mixed suspended operation `b_{i,j}` with `0 < i` and `0 < j` vanishes identically on
`MM.barTensorProduct NN`. -/
@[simp]
theorem barTensorProduct_b_eq_zero_of_pos (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    (MM.barTensorProduct NN).b i j = 0 := by
  refine TensorProduct.ext' fun x c ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [TensorProduct.add_tmul, map_add, hx₁, hx₂]
  | tmul a p =>
    induction p using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hy₁, hy₂]
    | tmul mb n =>
      induction mb using TensorProduct.inductionOn with
      | add z₁ z₂ hz₁ hz₂ =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hz₁, hz₂]
      | tmul m wB =>
        rw [LinearMap.zero_apply, ← taylor_tmul_of, barTensorProduct_taylor_tmul]
        simp [TensorWords.counit_eq_counit, TensorWords.counit_of_of_ne_zero R A hi.ne',
          TensorWords.counit_of_of_ne_zero R C hj.ne']

/-- Every mixed unsuspended operation `m_{i,j}` with `0 < i` and `0 < j` vanishes identically on
`MM.barTensorProduct NN`. -/
@[simp]
theorem barTensorProduct_m_eq_zero_of_pos (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    (MM.barTensorProduct NN).m i j = 0 := by
  ext x a c
  simp [m_apply, barTensorProduct_b_eq_zero_of_pos MM NN hi hj]

/-- On an empty middle word, the unary differential is `d_M ⊗ 1 + (-1)^{|m|} 1 ⊗ d_N`. -/
theorem barTensorProduct_differential_tmul_one (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) (m : M) (n : N) :
    (MM.barTensorProduct NN).differential ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) =
      (MM.differential m ⊗ₜ 1) ⊗ₜ n +
      (MM.grading.koszulTwist 1 m ⊗ₜ 1) ⊗ₜ NN.differential n := by
  rw [differential_apply, barTensorProduct_taylor_tmul_one]
  simp only [TensorWords.counit_eq_counit, TensorWords.counit_one, one_smul, ← differential_apply]

/-- Homogeneous form of `barTensorProduct_differential_tmul_one`. -/
theorem barTensorProduct_differential_tmul_one_of_mem (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) {p : ℤ} {m : M} (hm : m ∈ MM.grading.piece p) (n : N) :
    (MM.barTensorProduct NN).differential ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) =
      (MM.differential m ⊗ₜ 1) ⊗ₜ n +
      ((p.negOnePow : ℤ) : R) • ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ NN.differential n) := by
  rw [barTensorProduct_differential_tmul_one, MM.grading.koszulTwist_apply_of_mem hm]
  simp [TensorProduct.smul_tmul']

/-- On a single middle letter `[b]`, the unary differential recovers the five-term bar complex
formula. -/
theorem barTensorProduct_differential_tmul_of_one (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) (m : M) (b : TensorPower R 1 B) (n : N) :
    (MM.barTensorProduct NN).differential ((m ⊗ₜ TensorWords.of R B 1 b) ⊗ₜ n) =
      (MM.differential m ⊗ₜ TensorWords.of R B 1 b) ⊗ₜ n +
      (MM.taylor ((1 ⊗ₜ m) ⊗ₜ TensorWords.of R B 1 b) ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n -
      (MM.grading.koszulTwist 1 m ⊗ₜ BB.coaugmentedBarDifferential (TensorWords.of R B 1 b)) ⊗ₜ n +
      (MM.grading.koszulTwist 1 m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ
        NN.taylor (((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
          (TensorWords.of R B 1 b) ⊗ₜ n) ⊗ₜ 1) +
      (MM.grading.koszulTwist 1 m ⊗ₜ
        (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 (TensorWords.of R B 1 b)) ⊗ₜ
        NN.differential n := by
  rw [differential_apply, barTensorProduct_taylor_tmul]
  have hτ : (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 (TensorWords.of R B 1 b) =
      TensorWords.of R B 1
        (PiTensorProduct.map (fun _ : Fin 1 ↦ (BB.grading.shift 1).koszulTwist 1) b) := by
    rw [TensorWords.koszulTwist_grading, TensorWords.map_of]
  simp only [TensorWords.counit_eq_counit, TensorWords.counit_one, one_smul,
    Comodule.cofreeCoact_tmul, LinearMap.comp_apply, Comodule.leftCoactRTensor_tmul,
    Comodule.leftCofreeCoact_tmul, TensorWords.comul_eq_deconcatenation,
    TensorWords.deconcatenation_of_length_one, hτ, TensorProduct.tmul_add,
    TensorProduct.add_tmul, map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, ← differential_apply]
  rw [← hτ]
  abel

/-- On `(m ⊗ 1) ⊗ n`, a pure left outer action (`i > 0`, `j = 0`) acts directly on `m`. -/
theorem barTensorProduct_m_pos_zero_tmul_one (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) {i : ℕ} (hi : 0 < i) (m : M) (n : N)
    (a : Fin i → A) (c : Fin 0 → C) :
    (MM.barTensorProduct NN).m i 0 ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) a c =
      (MM.m i 0 m a (fun k ↦ k.elim0) ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n := by
  rw [m_apply, m_apply, ← taylor_tmul_of, ← taylor_tmul_of,
    show TensorWords.of R C 0 _ = (1 : TensorWords R C) from by
      rw [TensorWords.one_eq_of_zero]; exact TensorWords.of_tprod_congr R C fun k ↦ k.elim0,
    show TensorWords.of R B 0 _ = (1 : TensorWords R B) from by
      rw [TensorWords.one_eq_of_zero]; exact TensorWords.of_tprod_congr R B fun k ↦ k.elim0]
  simp only [Nat.cast_zero, InternalGrading.koszulTwist_zero, LinearMap.id_apply]
  rw [barTensorProduct_taylor_tmul_one]
  simp [TensorWords.counit_eq_counit, TensorWords.counit_of_of_ne_zero R A hi.ne']

/-- On `(m ⊗ 1) ⊗ n`, a pure right outer action (`i = 0`, `j > 0`) acts on `n` with the Koszul
twist `j + 1` on `m`. -/
theorem barTensorProduct_m_zero_pos_tmul_one (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) {j : ℕ} (hj : 0 < j) (m : M) (n : N)
    (a : Fin 0 → A) (c : Fin j → C) :
    (MM.barTensorProduct NN).m 0 j ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) a c =
      (MM.grading.koszulTwist ((j : ℤ) + 1) m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ
        NN.m 0 j n (fun k ↦ k.elim0) c := by
  have htwist : (barTensorGrading BB.grading MM.grading NN.grading).koszulTwist j
      ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) =
      (MM.grading.koszulTwist j m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ NN.grading.koszulTwist j n := by
    simp [barTensorGrading_def, InternalGrading.koszulTwist_tensorProduct]
  have hcomp : MM.grading.koszulTwist 1 (MM.grading.koszulTwist j m) =
      MM.grading.koszulTwist ((j : ℤ) + 1) m := by
    rw [← LinearMap.comp_apply, InternalGrading.koszulTwist_comp, add_comm]
  rw [m_apply, m_apply, barTensorProduct_grading, htwist, ← taylor_tmul_of, ← taylor_tmul_of,
    show TensorWords.of R A 0 _ = (1 : TensorWords R A) from by
      rw [TensorWords.one_eq_of_zero]; exact TensorWords.of_tprod_congr R A fun k ↦ k.elim0,
    show TensorWords.of R B 0 _ = (1 : TensorWords R B) from by
      rw [TensorWords.one_eq_of_zero]; exact TensorWords.of_tprod_congr R B fun k ↦ k.elim0,
    barTensorProduct_taylor_tmul_one, hcomp]
  simp [TensorWords.counit_eq_counit, TensorWords.counit_of_of_ne_zero R C hj.ne']

/-- On `(m ⊗ 1) ⊗ n`, the binary right action (`m_{0,1}`) is untwisted. -/
theorem barTensorProduct_m_zero_one_tmul_one (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) (m : M) (n : N)
    (a : Fin 0 → A) (c : Fin 1 → C) :
    (MM.barTensorProduct NN).m 0 1 ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) a c =
      (m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ NN.m 0 1 n (fun k ↦ k.elim0) c := by
  rw [barTensorProduct_m_zero_pos_tmul_one MM NN Nat.one_pos]
  norm_num [InternalGrading.koszulTwist_two]

end TauCeti.AInfinityBimodule
