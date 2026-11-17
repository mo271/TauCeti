/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.BarTensorProduct.Grading
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Taylor

/-!
# Bar tensor product of A-infinity bimodules

Given an `(A, B)` `A∞` bimodule `M` and a `(B, C)` `A∞` bimodule `N`, their two-sided bar tensor
product `M ⊗_{B∞} N` is an `(A, C)` `A∞` bimodule on the carrier

`(M ⊗ Tᶜ(sB)) ⊗ N`,

equipped with `barTensorGrading BB.grading MM.grading NN.grading`. No local finiteness,
boundedness, flatness, or completion assumption is needed: `TensorWords R B` is the direct sum of
finite-length tensor powers, so every deconcatenation sum is finite over any commutative ring `R`.

On the bar bicomodule carrier `W = (Tᶜ(sA) ⊗ ((M ⊗ Tᶜ(sB)) ⊗ N)) ⊗ Tᶜ(sC)`, the structure
differential is constructed in two steps. First, the raw operator

`D_raw = bM_ext + bN_ext - bB_ext`

combines the bar differential of `M` on `Tᶜ(sA) ⊗ sM ⊗ Tᶜ(sB)`, the bar differential of `N` on
`Tᶜ(sB) ⊗ sN ⊗ Tᶜ(sC)` twisted by the suspended left factor `Tᶜ(sA) ⊗ sM`, and subtracts the
doubly counted bar differential `b_B` on `Tᶜ(sB)`. Because `bM_ext - bB_ext` uses the right
coaction of `Tᶜ(sB)` while `bN_ext - bB_ext` uses its left coaction and passes a degree-one map
under the Koszul twist, coassociativity makes their anticommutator vanish, yielding
`D_raw ∘ D_raw = 0`. Second, conjugating `D_raw` by `barTensorSignTwist` corrects the right
co-Leibniz sign and matches the standard DG bar complex signs while preserving `D² = 0` and the
left co-Leibniz law.

## Main definitions

* `TauCeti.AInfinityBimodule.barTensorLeftDiff`, `barTensorMidDiff`, `barTensorRightDiff`:
  the three summands of the raw bar tensor differential.
* `TauCeti.AInfinityBimodule.barTensorRightCore`: the non-coalgebra core of `NN.barDifferential`
  after separating `b_B`.
* `TauCeti.AInfinityBimodule.barTensorRawDifferential`: `bM_ext + bN_ext - bB_ext`.
* `TauCeti.AInfinityBimodule.barTensorDifferential`: the conjugated bar differential
  `Φ ∘ D_raw ∘ Φ`.
* `TauCeti.AInfinityBimodule.barTensorProduct`: the `(A, C)` `A∞` bimodule `M ⊗_{B∞} N`.

## Main results

* `TauCeti.AInfinityBimodule.barTensorRawDifferential_sq` and `barTensorDifferential_sq`:
  the raw and conjugated bar differentials square to zero.
* `TauCeti.AInfinityBimodule.isHomogeneous_barTensorDifferential`: degree-one homogeneity.
* `TauCeti.AInfinityBimodule.isLeftGradedCoderivation_barTensorDifferential` and
  `isGradedCoderivation_barTensorDifferential`: left and right graded co-Leibniz laws.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped BigOperators TensorProduct

namespace TauCeti.AInfinityBimodule

universe uR uA uB uC uM uN

/-! ### Components of the bar tensor differential -/

section BarTensorPieces

attribute [local instance] Comodule.cofree

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  {M : Type uM} {N : Type uN}
  [CommRing R]

/-- The left bimodule bar differential extended across the right factors `N ⊗ Tᶜ(sC)`. -/
noncomputable def barTensorLeftDiff [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
    (MM : AInfinityBimodule AA BB M) (C : Type uC) (N : Type uN)
    [AddCommMonoid C] [Module R C] [AddCommMonoid N] [Module R N] :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C :=
  (barTensorAssocLeft R A B C M N).symm.toLinearMap ∘ₗ
    MM.barDifferential.rTensor (N ⊗[R] TensorWords R C) ∘ₗ
    (barTensorAssocLeft R A B C M N).toLinearMap

/-- Defining formula for `barTensorLeftDiff`. -/
theorem barTensorLeftDiff_def [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
    (MM : AInfinityBimodule AA BB M) (C : Type uC) (N : Type uN)
    [AddCommMonoid C] [Module R C] [AddCommMonoid N] [Module R N] :
    barTensorLeftDiff MM C N =
      (barTensorAssocLeft R A B C M N).symm.toLinearMap ∘ₗ
        MM.barDifferential.rTensor (N ⊗[R] TensorWords R C) ∘ₗ
        (barTensorAssocLeft R A B C M N).toLinearMap := (rfl)

/-- The middle coalgebra bar differential `b_B` twisted by the suspended left factor
`Tᶜ(sA) ⊗ sM`. -/
noncomputable def barTensorMidDiff [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommMonoid M] [Module R M] (GA : InternalGrading R A ℤ) (BB : AInfinityAlgebra R B)
    (GM : InternalGrading R M ℤ) (C : Type uC) (N : Type uN)
    [AddCommMonoid C] [Module R C] [AddCommMonoid N] [Module R N] :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C :=
  (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
    TensorProduct.map
      (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
      (BB.coaugmentedBarDifferential.rTensor (N ⊗[R] TensorWords R C)) ∘ₗ
    (barTensorAssocMid R A B C M N).toLinearMap

/-- Defining formula for `barTensorMidDiff`. -/
theorem barTensorMidDiff_def [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommMonoid M] [Module R M] (GA : InternalGrading R A ℤ) (BB : AInfinityAlgebra R B)
    (GM : InternalGrading R M ℤ) (C : Type uC) (N : Type uN)
    [AddCommMonoid C] [Module R C] [AddCommMonoid N] [Module R N] :
    barTensorMidDiff GA BB GM C N =
      (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
        TensorProduct.map
          (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
          (BB.coaugmentedBarDifferential.rTensor (N ⊗[R] TensorWords R C)) ∘ₗ
        (barTensorAssocMid R A B C M N).toLinearMap := (rfl)

/-- The right bimodule bar differential twisted by the suspended left factor `Tᶜ(sA) ⊗ sM`. -/
noncomputable def barTensorRightDiff [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]
    {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}
    (GA : InternalGrading R A ℤ) (GM : InternalGrading R M ℤ) (NN : AInfinityBimodule BB CC N) :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C :=
  (barTensorAssocRight R A B C M N).symm.toLinearMap ∘ₗ
    TensorProduct.map
      (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
      NN.barDifferential ∘ₗ
    (barTensorAssocRight R A B C M N).toLinearMap

/-- Defining formula for `barTensorRightDiff`. -/
theorem barTensorRightDiff_def [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]
    {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}
    (GA : InternalGrading R A ℤ) (GM : InternalGrading R M ℤ) (NN : AInfinityBimodule BB CC N) :
    barTensorRightDiff GA GM NN =
      (barTensorAssocRight R A B C M N).symm.toLinearMap ∘ₗ
        TensorProduct.map
          (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
          NN.barDifferential ∘ₗ
        (barTensorAssocRight R A B C M N).toLinearMap := (rfl)

/-- The core of `NN.barDifferential` after separating `b_B` on the left word: on `w_B ⊗ (n ⊗ w_C)`
it applies `NN.taylor` to prefixes of `w_C` and adds `ε(w_B) • (τ_{sN}(n) ⊗ b_C(w_C))`. -/
noncomputable def barTensorRightCore [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup N] [Module R N] {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}
    (NN : AInfinityBimodule BB CC N) :
    TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C) →ₗ[R] N ⊗[R] TensorWords R C :=
  NN.taylor.rTensor (TensorWords R C) ∘ₗ
      Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N) ∘ₗ
      (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap +
    TensorProduct.map ((NN.grading.shift 1).koszulTwist 1) CC.coaugmentedBarDifferential ∘ₗ
      Comodule.leftCofreeCounit R (TensorWords R B) (N ⊗[R] TensorWords R C)

/-- Defining formula for `barTensorRightCore`. -/
theorem barTensorRightCore_def [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup N] [Module R N] {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}
    (NN : AInfinityBimodule BB CC N) :
    barTensorRightCore NN =
      NN.taylor.rTensor (TensorWords R C) ∘ₗ
          Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N) ∘ₗ
          (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap +
        TensorProduct.map ((NN.grading.shift 1).koszulTwist 1) CC.coaugmentedBarDifferential ∘ₗ
          Comodule.leftCofreeCounit R (TensorWords R B) (N ⊗[R] TensorWords R C) := (rfl)

end BarTensorPieces

/-! ### The bar tensor differential and square-zero proof -/

section BarTensorProduct

attribute [local instance] Comodule.cofree

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- The raw (unconjugated) bar tensor differential `bM_ext + bN_ext - bB_ext`. -/
noncomputable def barTensorRawDifferential (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C :=
  barTensorLeftDiff MM C N + barTensorRightDiff AA.grading MM.grading NN -
    barTensorMidDiff AA.grading BB MM.grading C N

/-- Defining formula for `barTensorRawDifferential`. -/
theorem barTensorRawDifferential_def (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    barTensorRawDifferential MM NN =
      barTensorLeftDiff MM C N + barTensorRightDiff AA.grading MM.grading NN -
        barTensorMidDiff AA.grading BB MM.grading C N := (rfl)

/-- The suspended bar differential of the bar tensor product `M ⊗_{B∞} N`, obtained by
conjugating the raw differential by `barTensorSignTwist`. -/
noncomputable def barTensorDifferential (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C :=
  barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading ∘ₗ
    barTensorRawDifferential MM NN ∘ₗ
    barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading

/-- Defining formula for `barTensorDifferential`. -/
theorem barTensorDifferential_def (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    barTensorDifferential MM NN =
      barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading ∘ₗ
        barTensorRawDifferential MM NN ∘ₗ
        barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading := (rfl)

/-- The left bimodule bar differential splits into the `leftTaylor` part acting on prefixes of
`w_B` plus the middle bar differential `b_B`. -/
theorem barTensorLeftDiff_eq_add_mid (MM : AInfinityBimodule AA BB M) :
    barTensorLeftDiff MM C N =
      (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
        ((leftTaylor AA MM.taylor).rTensor
            (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) ∘ₗ
          (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B)
            (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C))).symm.toLinearMap ∘ₗ
          (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor
            (TensorWords R A ⊗[R] M)) ∘ₗ
        (barTensorAssocMid R A B C M N).toLinearMap +
      barTensorMidDiff AA.grading BB MM.grading C N := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    barTensorLeftDiff, barTensorMidDiff, barTensorAssocLeft_tmul, barTensorAssocMid_tmul,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  rw [MM.barDifferential_eq, gradedCoderiv_def]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul, TensorProduct.add_tmul, map_add,
    InternalGrading.koszulTwist_tensorProduct, TensorWords.koszulTwist_grading,
    Comodule.leftCofreeCoact_tmul]
  congr 1
  · induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
    | add u v hu hv =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hu, hv]
    | tmul u v =>
      simp only [LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul,
        TensorProduct.assoc_tmul]
      induction leftTaylor AA MM.taylor ((wA ⊗ₜ m) ⊗ₜ u) using TensorProduct.inductionOn with
      | add p q hp hq =>
        simp only [TensorProduct.add_tmul, map_add]
        rw [hp, hq]
      | tmul wA' m' =>
        simp only [barTensorAssocLeft_symm_tmul, barTensorAssocMid_symm_tmul]
  · simp only [barTensorAssocLeft_symm_tmul, barTensorAssocMid_symm_tmul]

/-- The left difference `bM_ext - bB_ext` in `barTensorAssocMid` coordinates. -/
theorem barTensorLeftDiff_sub_barTensorMidDiff (MM : AInfinityBimodule AA BB M) :
    barTensorLeftDiff MM C N - barTensorMidDiff AA.grading BB MM.grading C N =
      (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
        ((leftTaylor AA MM.taylor).rTensor
            (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) ∘ₗ
          (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B)
            (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C))).symm.toLinearMap ∘ₗ
          (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor
            (TensorWords R A ⊗[R] M)) ∘ₗ
        (barTensorAssocMid R A B C M N).toLinearMap := by
  rw [barTensorLeftDiff_eq_add_mid MM, add_sub_cancel_right]

/-- The `NN.taylor` summand of `NN.barDifferential`, reassociated into `Tᶜ(sB) ⊗ (N ⊗ Tᶜ(sC))`. -/
private theorem assoc_taylor_summand (NN : AInfinityBimodule BB CC N)
    (wB : TensorWords R B) (n : N) (wC : TensorWords R C) :
    let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
    let K₁ : TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C) →ₗ[R] N ⊗[R] TensorWords R C :=
      NN.taylor.rTensor (TensorWords R C) ∘ₗ
        Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N) ∘ₗ
        (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap
    (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C))
      (((TensorProduct.map τB NN.taylor ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R B) N)).rTensor (TensorWords R C))
        (Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N)
          ((wB ⊗ₜ n) ⊗ₜ wC))) =
      TensorProduct.map τB K₁
        (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)
          (wB ⊗ₜ (n ⊗ₜ wC))) := by
  intro τB K₁
  have hcomm := LinearMap.congr_fun
    (Comodule.assoc_comp_rTensor_comp_cofreeCoact (R := R) (E := TensorWords R C)
      (Comodule.leftCofreeCoact R (TensorWords R B) N) τB NN.taylor) ((wB ⊗ₜ n) ⊗ₜ wC)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomm
  rw [hcomm]
  simp only [Comodule.leftCoactRTensor_tmul, Comodule.leftCofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
  | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
  | tmul u v => simp [K₁, τB]

/-- Split the left-cofree extension of `barTensorRightCore NN` into its Taylor summand and
the `CC.coaugmentedBarDifferential` summand. -/
private theorem map_barTensorRightCore_comp_leftCofreeCoact
    (NN : AInfinityBimodule BB CC N) :
    let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
    TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C) =
      TensorProduct.map τB
          (NN.taylor.rTensor (TensorWords R C) ∘ₗ
            Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N) ∘ₗ
            (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap) ∘ₗ
          Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C) +
        TensorProduct.map τB
          (TensorProduct.map ((NN.grading.shift 1).koszulTwist 1)
            CC.coaugmentedBarDifferential) := by
  intro τB
  let K₂ : N ⊗[R] TensorWords R C →ₗ[R] N ⊗[R] TensorWords R C :=
    TensorProduct.map ((NN.grading.shift 1).koszulTwist 1) CC.coaugmentedBarDifferential
  rw [barTensorRightCore, TensorProduct.map_add_right, LinearMap.add_comp]
  congr 1
  calc
    TensorProduct.map τB (K₂ ∘ₗ Comodule.leftCofreeCounit R (TensorWords R B)
          (N ⊗[R] TensorWords R C)) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)
      = (TensorProduct.map τB K₂ ∘ₗ
          (Comodule.leftCofreeCounit R (TensorWords R B)
            (N ⊗[R] TensorWords R C)).lTensor (TensorWords R B)) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C) := by
        rw [LinearMap.lTensor_def, ← TensorProduct.map_comp, LinearMap.comp_id]
    _ = TensorProduct.map τB K₂ := by
        rw [LinearMap.comp_assoc, Comodule.lTensor_leftCofreeCounit_comp_leftCofreeCoact,
          LinearMap.comp_id]

/-- After reassociation, `NN.barDifferential` splits as the left-cofree extension of
`barTensorRightCore NN` twisted by `Tᶜ(sB)` plus `b_B` on the left word. -/
private theorem assoc_barDifferential_eq_add_coaugmentedBarDifferential
    (NN : AInfinityBimodule BB CC N) :
    (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).toLinearMap ∘ₗ
        NN.barDifferential ∘ₗ
        (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap =
      TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1)
          (barTensorRightCore NN) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C) +
      BB.coaugmentedBarDifferential.rTensor (N ⊗[R] TensorWords R C) := by
  let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
  let K₁ : TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C) →ₗ[R] N ⊗[R] TensorWords R C :=
    NN.taylor.rTensor (TensorWords R C) ∘ₗ
      Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N) ∘ₗ
      (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap
  let K₂ : N ⊗[R] TensorWords R C →ₗ[R] N ⊗[R] TensorWords R C :=
    TensorProduct.map ((NN.grading.shift 1).koszulTwist 1) CC.coaugmentedBarDifferential
  rw [map_barTensorRightCore_comp_leftCofreeCoact NN]
  refine TensorProduct.ext' fun wB y ↦ ?_
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ hy₁ hy₂ => simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
  | tmul n wC =>
    have hcC := LinearMap.congr_fun
      (Comodule.rTensor_rid_comp_lTensor_counit_comp_cofreeCoact
        (R := R) (C := TensorWords R C) (M := TensorWords R B ⊗[R] N)) ((wB ⊗ₜ n) ⊗ₜ wC)
    simp only [LinearMap.comp_apply] at hcC
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul]
    rw [NN.barDifferential_eq, gradedCoderiv_def, leftTaylor_def, ← Comodule.cofreeCoact_def,
      LinearMap.rTensor_add, LinearMap.add_comp, LinearMap.add_apply, LinearMap.add_apply,
      map_add, map_add]
    simp only [← TensorWords.koszulTwist_grading]
    have hmid : (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C))
        (((BB.coaugmentedBarDifferential.rTensor N ∘ₗ
            (TensorProduct.rid R (TensorWords R B ⊗[R] N)).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := TensorWords R C)).lTensor
              (TensorWords R B ⊗[R] N)).rTensor (TensorWords R C) ∘ₗ
          Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N))
          ((wB ⊗ₜ n) ⊗ₜ wC)) =
        BB.coaugmentedBarDifferential wB ⊗ₜ (n ⊗ₜ wC) := by
      rw [LinearMap.comp_apply, LinearMap.rTensor_comp, LinearMap.comp_apply, hcC]
      simp
    have h1 := assoc_taylor_summand NN wB n wC
    have h2 : (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C))
        ((CC.coaugmentedBarDifferential.lTensor (TensorWords R B ⊗[R] N) ∘ₗ
          (TensorProduct.map τB ((NN.grading.shift 1).koszulTwist 1)).rTensor (TensorWords R C))
            ((wB ⊗ₜ n) ⊗ₜ wC)) =
        TensorProduct.map τB K₂ (wB ⊗ₜ (n ⊗ₜ wC)) := by
      simp [K₂, τB]
    have h1' : (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C))
        ((((TensorProduct.map τB NN.taylor ∘ₗ
          Comodule.leftCoactRTensor (TensorWords R C)
            (Comodule.leftCofreeCoact R (TensorWords R B) N)).rTensor (TensorWords R C) ∘ₗ
          Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N)))
          ((wB ⊗ₜ n) ⊗ₜ wC)) =
        TensorProduct.map τB K₁
          (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)
            (wB ⊗ₜ (n ⊗ₜ wC))) := h1
    rw [h1', hmid, h2]
    ac_rfl

/-- The right bimodule bar differential splits into the left-cofree extension of
`barTensorRightCore NN` plus the middle bar differential `b_B`. -/
theorem barTensorRightDiff_eq_add_mid (GA : InternalGrading R A ℤ) (GM : InternalGrading R M ℤ)
    (NN : AInfinityBimodule BB CC N) :
    barTensorRightDiff GA GM NN =
      (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
        TensorProduct.map
          (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
          (TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1)
            (barTensorRightCore NN) ∘ₗ
            Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)) ∘ₗ
        (barTensorAssocMid R A B C M N).toLinearMap +
      barTensorMidDiff GA BB GM C N := by
  have hN := assoc_barDifferential_eq_add_coaugmentedBarDifferential NN
  have hmap : TensorProduct.map
        (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
        ((TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).toLinearMap ∘ₗ
          NN.barDifferential ∘ₗ
          (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap) =
      TensorProduct.map
        (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
        (TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1)
          (barTensorRightCore NN) ∘ₗ
          Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)) +
      TensorProduct.map
        (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
        (BB.coaugmentedBarDifferential.rTensor (N ⊗[R] TensorWords R C)) := by
    rw [hN, TensorProduct.map_add_right]
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have heval := LinearMap.congr_fun hmap ((wA ⊗ₜ m) ⊗ₜ (wB ⊗ₜ (n ⊗ₜ wC)))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul] at heval
  have heval' := congrArg (barTensorAssocMid R A B C M N).symm heval
  rw [map_add] at heval'
  rw [LinearMap.add_apply, barTensorMidDiff, barTensorRightDiff]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, barTensorAssocRight_tmul,
    barTensorAssocMid_tmul, TensorProduct.map_tmul]
  rw [← heval']
  induction ((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1
      (wA ⊗ₜ m) using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [TensorProduct.add_tmul, map_add, hu₁, hu₂]
  | tmul wA' m' =>
    induction NN.barDifferential ((wB ⊗ₜ n) ⊗ₜ wC) using TensorProduct.inductionOn with
    | add v₁ v₂ hv₁ hv₂ => simp only [TensorProduct.tmul_add, map_add, hv₁, hv₂]
    | tmul bn wC' =>
      induction bn using TensorProduct.inductionOn with
      | add p q hp hq =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hp, hq]
      | tmul wB' n' => simp

/-- The right difference `bN_ext - bB_ext` in `barTensorAssocMid` coordinates. -/
theorem barTensorRightDiff_sub_barTensorMidDiff (GA : InternalGrading R A ℤ)
    (GM : InternalGrading R M ℤ) (NN : AInfinityBimodule BB CC N) :
    barTensorRightDiff GA GM NN - barTensorMidDiff GA BB GM C N =
      (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
        TensorProduct.map
          (((TensorWords.grading (GA.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
          (TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1)
            (barTensorRightCore NN) ∘ₗ
            Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)) ∘ₗ
        (barTensorAssocMid R A B C M N).toLinearMap := by
  rw [barTensorRightDiff_eq_add_mid GA GM NN, add_sub_cancel_right]

/-- The left cofree part of a bimodule Taylor map has degree one. -/
theorem isHomogeneous_leftTaylor_taylor (MM : AInfinityBimodule AA BB M) :
    LinearMap.IsHomogeneous (leftTaylor AA MM.taylor)
      (barGrading AA BB MM.grading).piece
      ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (MM.grading.shift 1)).piece 1 := by
  let W := TensorWords.grading (AA.grading.shift 1)
  let Y := W.tensorProduct (MM.grading.shift 1)
  have hτ : LinearMap.IsHomogeneous (TensorWords.map ((AA.grading.shift 1).koszulTwist 1))
      W.piece W.piece 0 := by
    rw [← TensorWords.koszulTwist_grading]
    exact LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using W.koszulTwist_mem_piece hx 1
  have hb : LinearMap.IsHomogeneous AA.coaugmentedBarDifferential W.piece W.piece 1 := by
    simpa only [W, TensorWords.grading_piece] using AA.isHomogeneous_coaugmentedBarDifferential
  have h1 := (hτ.tensorProduct MM.isHomogeneous_taylor).comp
    (isHomogeneous_leftCoact AA BB MM.grading)
  have h2 := (hb.tensorProduct (LinearMap.isHomogeneous_id (MM.grading.shift 1).piece)).comp
    (TensorWords.isHomogeneous_rid_comp_lTensor_counit Y (BB.grading.shift 1))
  simp only [zero_add, add_zero] at h1 h2
  rw [barGrading_def] at h1
  rw [leftTaylor_def, LinearMap.rTensor_def, barGrading_def]
  exact h1.add h2

/-- Trilinear pairing used to identify both compositions of the left and right middle operators via
coassociativity of `TensorWords R B`. -/
private noncomputable def barTensorTripleEval (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) (x : TensorWords R A ⊗[R] M)
    (y : N ⊗[R] TensorWords R C) :
    TensorWords R B ⊗[R] (TensorWords R B ⊗[R] TensorWords R B) →ₗ[R]
      (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :=
  let τAM := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
    (MM.grading.shift 1)).koszulTwist 1
  let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
  TensorProduct.lift
    { toFun := fun w₁ ↦
        TensorProduct.lift
          { toFun := fun w₂ ↦
              { toFun := fun w₃ ↦
                  leftTaylor AA MM.taylor (τAM x ⊗ₜ τB w₁) ⊗ₜ
                    (τB w₂ ⊗ₜ barTensorRightCore NN (w₃ ⊗ₜ y))
                map_add' := fun a b ↦ by
                  simp only [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add]
                map_smul' := fun r a ↦ by
                  simp only [← TensorProduct.smul_tmul', map_smul, TensorProduct.tmul_smul,
                    RingHom.id_apply] }
            map_add' := fun a b ↦ LinearMap.ext fun c ↦ by
              simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add,
                TensorProduct.add_tmul, TensorProduct.tmul_add]
            map_smul' := fun r a ↦ LinearMap.ext fun c ↦ by
              simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
                ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, RingHom.id_apply] }
      map_add' := fun a b ↦ TensorProduct.ext' fun w₂ w₃ ↦ by
        simp only [LinearMap.add_apply, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
          map_add, TensorProduct.tmul_add, TensorProduct.add_tmul]
      map_smul' := fun r a ↦ TensorProduct.ext' fun w₂ w₃ ↦ by
        simp only [LinearMap.smul_apply, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
          map_smul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', RingHom.id_apply] }

@[simp]
private theorem barTensorTripleEval_tmul (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) (x : TensorWords R A ⊗[R] M)
    (y : N ⊗[R] TensorWords R C) (w₁ w₂ w₃ : TensorWords R B) :
    barTensorTripleEval MM NN x y (w₁ ⊗ₜ (w₂ ⊗ₜ w₃)) =
      leftTaylor AA MM.taylor
          (((TensorWords.grading (AA.grading.shift 1)).tensorProduct
            (MM.grading.shift 1)).koszulTwist 1 x ⊗ₜ
            (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 w₁) ⊗ₜ
        ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 w₂ ⊗ₜ
          barTensorRightCore NN (w₃ ⊗ₜ y)) :=
  (rfl)

/-- Evaluating `N₀ (M₀ _)` via `barTensorTripleEval` on the right-associated comultiplication. -/
private theorem barTensorMid_eval_NM (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) (x : TensorWords R A ⊗[R] M) (wB : TensorWords R B)
    (y : N ⊗[R] TensorWords R C) :
    let τAM := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
      (MM.grading.shift 1)).koszulTwist 1
    let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
    (TensorProduct.map τAM (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)))
      (((leftTaylor AA MM.taylor).rTensor _ ∘ₗ
        (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B) _).symm.toLinearMap ∘ₗ
        (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor _)
          (x ⊗ₜ (wB ⊗ₜ y))) =
      (-1 : R) • barTensorTripleEval MM NN x y
        (Coalgebra.comul.lTensor (TensorWords R B) (Coalgebra.comul wB)) := by
  intro τAM τB
  have hτL : τAM ∘ₗ leftTaylor AA MM.taylor =
      (-1 : R) • (leftTaylor AA MM.taylor ∘ₗ TensorProduct.map τAM τB) := by
    simpa only [τAM, τB, one_mul, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one, barGrading_def, InternalGrading.koszulTwist_tensorProduct] using
      (isHomogeneous_leftTaylor_taylor MM).koszulTwist_comp_eq_smul 1
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, Comodule.leftCofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add, hu, hv]
  | tmul u v =>
    simp only [LinearEquiv.coe_coe, TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
      Comodule.leftCofreeCoact_tmul, LinearMap.lTensor_tmul]
    have hτLx := LinearMap.congr_fun hτL (x ⊗ₜ u)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, TensorProduct.map_tmul] at hτLx
    rw [hτLx, ← TensorProduct.smul_tmul']
    congr 1
    induction Coalgebra.comul (R := R) v using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]
    | tmul a b => simp [τAM, τB]

/-- Evaluating `M₀ (N₀ _)` via `barTensorTripleEval` on the left-associated comultiplication. -/
private theorem barTensorMid_eval_MN (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) (x : TensorWords R A ⊗[R] M) (wB : TensorWords R B)
    (y : N ⊗[R] TensorWords R C) :
    let τAM := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
      (MM.grading.shift 1)).koszulTwist 1
    let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
    ((leftTaylor AA MM.taylor).rTensor _ ∘ₗ
        (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B) _).symm.toLinearMap ∘ₗ
        (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor _)
      ((TensorProduct.map τAM (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)))
          (x ⊗ₜ (wB ⊗ₜ y))) =
      barTensorTripleEval MM NN x y
        ((TensorProduct.assoc R (TensorWords R B) (TensorWords R B) (TensorWords R B))
          (Coalgebra.comul.rTensor (TensorWords R B) (Coalgebra.comul wB))) := by
  intro τAM τB
  have hτB : Coalgebra.comul ∘ₗ τB = TensorProduct.map τB τB ∘ₗ
      (Coalgebra.comul : TensorWords R B →ₗ[R] TensorWords R B ⊗[R] TensorWords R B) := by
    simp only [τB, TensorWords.koszulTwist_grading, TensorWords.comul_eq_deconcatenation,
      TensorWords.deconcatenation_natural]
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Comodule.leftCofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hu, hv]
  | tmul u v =>
    have hcu := LinearMap.congr_fun hτB u
    simp only [LinearMap.comp_apply] at hcu
    simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      Comodule.leftCofreeCoact_tmul, hcu, LinearMap.rTensor_tmul]
    induction Coalgebra.comul (R := R) u using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]
    | tmul a b => simp [τAM, τB]

/-- In `barTensorAssocMid` coordinates, the left and right non-coalgebra operators anticommute. -/
private theorem barTensorMid_anticomm (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    let τAM := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
      (MM.grading.shift 1)).koszulTwist 1
    let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
    let M₀ : (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) →ₗ[R]
        (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :=
      (leftTaylor AA MM.taylor).rTensor _ ∘ₗ
        (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B) _).symm.toLinearMap ∘ₗ
        (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor _
    let N₀ : (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) →ₗ[R]
        (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :=
      TensorProduct.map τAM (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C))
    N₀ ∘ₗ M₀ = (-1 : R) • (M₀ ∘ₗ N₀) := by
  intro τAM τB M₀ N₀
  refine TensorProduct.ext' fun x z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
  | tmul wB y =>
    have hcoassoc := LinearMap.congr_fun
      (Coalgebra.coassoc (R := R) (A := TensorWords R B)) wB
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcoassoc
    calc
      (N₀ ∘ₗ M₀) (x ⊗ₜ (wB ⊗ₜ y))
        = N₀ (M₀ (x ⊗ₜ (wB ⊗ₜ y))) := rfl
      _ = (-1 : R) • barTensorTripleEval MM NN x y
            (Coalgebra.comul.lTensor (TensorWords R B) (Coalgebra.comul wB)) :=
          barTensorMid_eval_NM MM NN x wB y
      _ = (-1 : R) • barTensorTripleEval MM NN x y
            ((TensorProduct.assoc R (TensorWords R B) (TensorWords R B) (TensorWords R B))
              (Coalgebra.comul.rTensor (TensorWords R B) (Coalgebra.comul wB))) := by
          rw [hcoassoc]
      _ = (-1 : R) • M₀ (N₀ (x ⊗ₜ (wB ⊗ₜ y))) := by
          rw [← barTensorMid_eval_MN MM NN x wB y]
      _ = ((-1 : R) • (M₀ ∘ₗ N₀)) (x ⊗ₜ (wB ⊗ₜ y)) := rfl

/-- The left and right non-coalgebra parts of `barTensorRawDifferential` anticommute. -/
private theorem barTensor_cross_anticomm (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    (barTensorLeftDiff MM C N - barTensorMidDiff AA.grading BB MM.grading C N) ∘ₗ
        (barTensorRightDiff AA.grading MM.grading NN -
          barTensorMidDiff AA.grading BB MM.grading C N) +
      (barTensorRightDiff AA.grading MM.grading NN -
          barTensorMidDiff AA.grading BB MM.grading C N) ∘ₗ
        (barTensorLeftDiff MM C N - barTensorMidDiff AA.grading BB MM.grading C N) = 0 := by
  let e := barTensorAssocMid R A B C M N
  let τAM := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
    (MM.grading.shift 1)).koszulTwist 1
  let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
  let M₀ : (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) →ₗ[R]
      (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :=
    (leftTaylor AA MM.taylor).rTensor _ ∘ₗ
      (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B) _).symm.toLinearMap ∘ₗ
      (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor _
  let N₀ : (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) →ₗ[R]
      (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :=
    TensorProduct.map τAM (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
      Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C))
  rw [barTensorLeftDiff_sub_barTensorMidDiff MM, barTensorRightDiff_sub_barTensorMidDiff]
  have hcomp :
      (e.symm.toLinearMap ∘ₗ M₀ ∘ₗ e.toLinearMap) ∘ₗ
          (e.symm.toLinearMap ∘ₗ N₀ ∘ₗ e.toLinearMap) +
        (e.symm.toLinearMap ∘ₗ N₀ ∘ₗ e.toLinearMap) ∘ₗ
          (e.symm.toLinearMap ∘ₗ M₀ ∘ₗ e.toLinearMap) =
      e.symm.toLinearMap ∘ₗ (M₀ ∘ₗ N₀ + N₀ ∘ₗ M₀) ∘ₗ e.toLinearMap := by
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    simp [e]
  have hsum : M₀ ∘ₗ N₀ + N₀ ∘ₗ M₀ = 0 := by
    rw [barTensorMid_anticomm MM NN]
    module
  exact (hcomp.trans (by rw [hsum, LinearMap.zero_comp, LinearMap.comp_zero]))

/-- The raw bar tensor differential squares to zero. -/
theorem barTensorRawDifferential_sq (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    barTensorRawDifferential MM NN ∘ₗ barTensorRawDifferential MM NN = 0 := by
  have hLsq : barTensorLeftDiff MM C N ∘ₗ barTensorLeftDiff MM C N = 0 := by
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    simp only [barTensorLeftDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, ← LinearMap.rTensor_comp_apply, MM.barDifferential_sq,
      LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero]
  have hRsq : barTensorRightDiff AA.grading MM.grading NN ∘ₗ
      barTensorRightDiff AA.grading MM.grading NN = 0 := by
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    simp only [barTensorRightDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, barTensorAssocRight_tmul, TensorProduct.map_tmul,
      ← LinearMap.comp_apply NN.barDifferential NN.barDifferential, NN.barDifferential_sq,
      LinearMap.zero_apply, TensorProduct.tmul_zero, map_zero]
  have hMsq : barTensorMidDiff AA.grading BB MM.grading C N ∘ₗ
      barTensorMidDiff AA.grading BB MM.grading C N = 0 := by
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    simp only [barTensorMidDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, barTensorAssocMid_tmul, TensorProduct.map_tmul,
      LinearMap.rTensor_tmul,
      ← LinearMap.comp_apply BB.coaugmentedBarDifferential BB.coaugmentedBarDifferential,
      BB.coaugmentedBarDifferential_sq, LinearMap.zero_apply, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, map_zero]
  have hsplit : barTensorRawDifferential MM NN ∘ₗ barTensorRawDifferential MM NN =
      barTensorLeftDiff MM C N ∘ₗ barTensorLeftDiff MM C N +
      barTensorRightDiff AA.grading MM.grading NN ∘ₗ
        barTensorRightDiff AA.grading MM.grading NN -
      barTensorMidDiff AA.grading BB MM.grading C N ∘ₗ
        barTensorMidDiff AA.grading BB MM.grading C N +
      ((barTensorLeftDiff MM C N - barTensorMidDiff AA.grading BB MM.grading C N) ∘ₗ
        (barTensorRightDiff AA.grading MM.grading NN -
          barTensorMidDiff AA.grading BB MM.grading C N) +
       (barTensorRightDiff AA.grading MM.grading NN -
          barTensorMidDiff AA.grading BB MM.grading C N) ∘ₗ
        (barTensorLeftDiff MM C N - barTensorMidDiff AA.grading BB MM.grading C N)) := by
    simp only [barTensorRawDifferential, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.sub_comp, LinearMap.comp_sub]
    abel
  rw [hsplit, hLsq, hRsq, hMsq, barTensor_cross_anticomm]
  simp

/-- The bar tensor differential squares to zero. -/
@[simp]
theorem barTensorDifferential_sq (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    barTensorDifferential MM NN ∘ₗ barTensorDifferential MM NN = 0 := by
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  calc
    barTensorDifferential MM NN ∘ₗ barTensorDifferential MM NN =
        Φ ∘ₗ barTensorRawDifferential MM NN ∘ₗ (Φ ∘ₗ Φ) ∘ₗ
          barTensorRawDifferential MM NN ∘ₗ Φ := by
      simp only [barTensorDifferential, Φ, LinearMap.comp_assoc]
    _ = Φ ∘ₗ (barTensorRawDifferential MM NN ∘ₗ barTensorRawDifferential MM NN) ∘ₗ Φ := by
      rw [barTensorSignTwist_comp_self, LinearMap.id_comp, LinearMap.comp_assoc]
    _ = 0 := by
      rw [barTensorRawDifferential_sq, LinearMap.zero_comp, LinearMap.comp_zero]

/-! ### Homogeneity and bicomodule coderivation laws -/

/-- The left piece of the bar tensor differential has degree one. -/
private theorem isHomogeneous_barTensorLeftDiff (MM : AInfinityBimodule AA BB M)
    (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorLeftDiff MM C N)
      (barGrading AA CC (barTensorGrading BB.grading MM.grading GN)).piece
      (barGrading AA CC (barTensorGrading BB.grading MM.grading GN)).piece 1 := by
  let GC := TensorWords.grading (CC.grading.shift 1)
  have h := (isHomogeneous_barTensorAssocLeft_symm AA BB CC MM.grading GN).comp
    ((MM.isHomogeneous_barDifferential.rTensor (GN.tensorProduct GC)).comp
      (isHomogeneous_barTensorAssocLeft AA BB CC MM.grading GN))
  simpa only [barTensorLeftDiff, zero_add, add_zero] using h

/-- The middle piece of the bar tensor differential has degree one. -/
private theorem isHomogeneous_barTensorMidDiff (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorMidDiff AA.grading BB GM C N)
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece 1 := by
  let GA := TensorWords.grading (AA.grading.shift 1)
  let GB := TensorWords.grading (BB.grading.shift 1)
  let GC := TensorWords.grading (CC.grading.shift 1)
  have hτAM : LinearMap.IsHomogeneous ((GA.tensorProduct (GM.shift 1)).koszulTwist 1)
      (GA.tensorProduct (GM.shift 1)).piece (GA.tensorProduct (GM.shift 1)).piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using (GA.tensorProduct (GM.shift 1)).koszulTwist_mem_piece hx 1
  have hbB : LinearMap.IsHomogeneous BB.coaugmentedBarDifferential GB.piece GB.piece 1 := by
    simpa only [GB, TensorWords.grading_piece] using BB.isHomogeneous_coaugmentedBarDifferential
  have h := (isHomogeneous_barTensorAssocMid_symm AA BB CC GM GN).comp
    ((hτAM.tensorProduct (hbB.rTensor (GN.tensorProduct GC))).comp
      (isHomogeneous_barTensorAssocMid AA BB CC GM GN))
  simpa only [barTensorMidDiff, zero_add, add_zero] using h

/-- The right piece of the bar tensor differential has degree one. -/
private theorem isHomogeneous_barTensorRightDiff (GM : InternalGrading R M ℤ)
    (NN : AInfinityBimodule BB CC N) :
    LinearMap.IsHomogeneous (barTensorRightDiff AA.grading GM NN)
      (barGrading AA CC (barTensorGrading BB.grading GM NN.grading)).piece
      (barGrading AA CC (barTensorGrading BB.grading GM NN.grading)).piece 1 := by
  let GA := TensorWords.grading (AA.grading.shift 1)
  have hshift : GA.tensorProduct (GM.shift 1) = (GA.tensorProduct GM).shift 1 := by
    refine InternalGrading.ext fun n ↦ ?_
    rw [InternalGrading.shift_piece, InternalGrading.tensorProduct_piece_eq_iSup,
      InternalGrading.tensorProduct_piece_eq_iSup]
    refine iSup_congr fun p ↦ ?_
    have h : n - p + 1 = n + 1 - p := by omega
    rw [InternalGrading.shift_piece, h]
  have hτAM : LinearMap.IsHomogeneous ((GA.tensorProduct (GM.shift 1)).koszulTwist 1)
      (GA.tensorProduct GM).piece (GA.tensorProduct GM).piece 0 := by
    refine (LinearMap.isHomogeneous_shift_piece_iff (G := GA.tensorProduct GM)
      (H := GA.tensorProduct GM) (c := 1)).1 ?_
    rw [← hshift]
    exact LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using (GA.tensorProduct (GM.shift 1)).koszulTwist_mem_piece hx 1
  have h := (isHomogeneous_barTensorAssocRight_symm AA BB CC GM NN.grading).comp
    ((hτAM.tensorProduct NN.isHomogeneous_barDifferential).comp
      (isHomogeneous_barTensorAssocRight AA BB CC GM NN.grading))
  simpa only [barTensorRightDiff, zero_add, add_zero] using h

/-- The bar tensor differential raises total suspended degree by one. -/
theorem isHomogeneous_barTensorDifferential (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    LinearMap.IsHomogeneous (barTensorDifferential MM NN)
      (barGrading AA CC (barTensorGrading BB.grading MM.grading NN.grading)).piece
      (barGrading AA CC (barTensorGrading BB.grading MM.grading NN.grading)).piece 1 := by
  have hraw : LinearMap.IsHomogeneous (barTensorRawDifferential MM NN)
      (barGrading AA CC (barTensorGrading BB.grading MM.grading NN.grading)).piece
      (barGrading AA CC (barTensorGrading BB.grading MM.grading NN.grading)).piece 1 :=
    ((isHomogeneous_barTensorLeftDiff MM NN.grading).add
      (isHomogeneous_barTensorRightDiff MM.grading NN)).sub
      (isHomogeneous_barTensorMidDiff MM.grading NN.grading)
  have hΦ := isHomogeneous_barTensorSignTwist AA BB.grading CC MM.grading NN.grading
  simpa only [barTensorDifferential, zero_add, add_zero] using hΦ.comp (hraw.comp hΦ)

/-- The left piece `barTensorLeftDiff` is a left graded coderivation over
`AA.coaugmentedBarDifferential`. -/
private theorem leftCoactRTensor_comp_barTensorLeftDiff (MM : AInfinityBimodule AA BB M) :
    let δ := Comodule.leftCoactRTensor (TensorWords R C)
      (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N))
    δ ∘ₗ barTensorLeftDiff MM C N =
      AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
        TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          (barTensorLeftDiff MM C N) ∘ₗ δ := by
  intro δ
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hMM := MM.isLeftGradedCoderivation_barDifferential.coact_apply ((wA ⊗ₜ m) ⊗ₜ wB)
  have hpull : ∀ z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B,
      δ ((barTensorAssocLeft R A B C M N).symm (z ⊗ₜ (n ⊗ₜ wC))) =
        ((barTensorAssocLeft R A B C M N).symm.toLinearMap ∘ₗ
          ((TensorProduct.mk R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
            (N ⊗[R] TensorWords R C)).flip (n ⊗ₜ wC))).lTensor (TensorWords R A)
          (Comodule.leftCoactRTensor (TensorWords R B)
            (Comodule.leftCofreeCoact R (TensorWords R A) M) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul u v =>
      induction u using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul wA' m' =>
        simp only [barTensorAssocLeft_symm_tmul, Comodule.leftCoactRTensor_tmul,
          Comodule.leftCofreeCoact_tmul, δ]
        induction Coalgebra.comul (R := R) wA' using TensorProduct.inductionOn with
        | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
        | tmul a b => simp
  simp only [LinearMap.comp_apply, LinearMap.add_apply, barTensorLeftDiff, LinearEquiv.coe_coe,
    barTensorAssocLeft_tmul, LinearMap.rTensor_tmul]
  rw [hpull, hMM, map_add]
  simp only [Comodule.leftCoactRTensor_tmul, Comodule.leftCofreeCoact_tmul, δ]
  congr 1
  · induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | tmul a b => simp
  · induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | tmul a b => simp

/-- Pull the left coaction of `Tᶜ(sA)` through `barTensorAssocMid.symm`. -/
private theorem leftCoactRTensor_barTensorAssocMid_symm
    (wA : TensorWords R A) (m : M) (z : TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :
    Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N))
        ((barTensorAssocMid R A B C M N).symm ((wA ⊗ₜ m) ⊗ₜ z)) =
      ((barTensorAssocMid R A B C M N).symm.toLinearMap.lTensor (TensorWords R A))
        ((TensorProduct.assoc R (TensorWords R A) (TensorWords R A ⊗[R] M)
            (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)))
          ((Comodule.leftCofreeCoact R (TensorWords R A) M (wA ⊗ₜ m)) ⊗ₜ z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul wB y =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
    | tmul n wC =>
      simp only [barTensorAssocMid_symm_tmul, Comodule.leftCoactRTensor_tmul,
        Comodule.leftCofreeCoact_tmul]
      induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
      | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
      | tmul a b => simp

/-- Any map of the form `barTensorAssocMid.symm ∘ (τ_AM ⊗ G) ∘ barTensorAssocMid` intertwines the
left coaction of `Tᶜ(sA)` with a Koszul twist on the split-off `Tᶜ(sA)` factor. -/
private theorem leftCoactRTensor_comp_assocMid_twist (GM : InternalGrading R M ℤ)
    (G : TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C) →ₗ[R]
      TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :
    let δ := Comodule.leftCoactRTensor (TensorWords R C)
      (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N))
    let τA := (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1
    let F := (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
      TensorProduct.map
        (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1) G ∘ₗ
      (barTensorAssocMid R A B C M N).toLinearMap
    δ ∘ₗ F = TensorProduct.map τA F ∘ₗ δ := by
  intro δ τA F
  have hτA : Coalgebra.comul ∘ₗ τA = TensorProduct.map τA τA ∘ₗ
      (Coalgebra.comul : TensorWords R A →ₗ[R] TensorWords R A ⊗[R] TensorWords R A) := by
    simp only [τA, TensorWords.koszulTwist_grading, TensorWords.comul_eq_deconcatenation,
      TensorWords.deconcatenation_natural]
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hc := LinearMap.congr_fun hτA wA
  simp only [LinearMap.comp_apply] at hc
  simp only [F, δ, LinearMap.comp_apply, LinearEquiv.coe_coe, barTensorAssocMid_tmul,
    TensorProduct.map_tmul, InternalGrading.koszulTwist_tensorProduct]
  rw [leftCoactRTensor_barTensorAssocMid_symm, Comodule.leftCoactRTensor_tmul,
    Comodule.leftCofreeCoact_tmul, Comodule.leftCofreeCoact_tmul, hc]
  induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | tmul a b => simp [τA]

/-- Rewrite `barTensorRightDiff` in `barTensorAssocMid` coordinates. -/
private theorem barTensorRightDiff_eq_assocMid (GM : InternalGrading R M ℤ)
    (NN : AInfinityBimodule BB CC N) :
    barTensorRightDiff AA.grading GM NN =
      (barTensorAssocMid R A B C M N).symm.toLinearMap ∘ₗ
        TensorProduct.map
          (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
          ((TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).toLinearMap ∘ₗ
            NN.barDifferential ∘ₗ
            (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap) ∘ₗ
        (barTensorAssocMid R A B C M N).toLinearMap := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [barTensorRightDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
    barTensorAssocRight_tmul, barTensorAssocMid_tmul, TensorProduct.map_tmul,
    TensorProduct.assoc_symm_tmul]
  induction ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1
      (wA ⊗ₜ m) using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [TensorProduct.add_tmul, map_add, hu₁, hu₂]
  | tmul wA' m' =>
    induction NN.barDifferential ((wB ⊗ₜ n) ⊗ₜ wC) using TensorProduct.inductionOn with
    | add v₁ v₂ hv₁ hv₂ => simp only [TensorProduct.tmul_add, map_add, hv₁, hv₂]
    | tmul bn wC' =>
      induction bn using TensorProduct.inductionOn with
      | add p q hp hq =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hp, hq]
      | tmul wB' n' => simp

/-- The raw bar tensor differential satisfies the left co-Leibniz law over
`AA.coaugmentedBarDifferential`. -/
private theorem leftCoactRTensor_comp_barTensorRawDifferential (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    let δ := Comodule.leftCoactRTensor (TensorWords R C)
      (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N))
    let τA := (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1
    δ ∘ₗ barTensorRawDifferential MM NN =
      AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
        TensorProduct.map τA (barTensorRawDifferential MM NN) ∘ₗ δ := by
  intro δ τA
  have hL : δ ∘ₗ barTensorLeftDiff MM C N =
      AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
        TensorProduct.map τA (barTensorLeftDiff MM C N) ∘ₗ δ :=
    leftCoactRTensor_comp_barTensorLeftDiff (C := C) (N := N) MM
  have hM : δ ∘ₗ barTensorMidDiff AA.grading BB MM.grading C N =
      TensorProduct.map τA (barTensorMidDiff AA.grading BB MM.grading C N) ∘ₗ δ :=
    leftCoactRTensor_comp_assocMid_twist MM.grading
      (BB.coaugmentedBarDifferential.rTensor (N ⊗[R] TensorWords R C))
  have hR : δ ∘ₗ barTensorRightDiff AA.grading MM.grading NN =
      TensorProduct.map τA (barTensorRightDiff AA.grading MM.grading NN) ∘ₗ δ := by
    rw [barTensorRightDiff_eq_assocMid]
    exact leftCoactRTensor_comp_assocMid_twist MM.grading _
  have hadd : barTensorRawDifferential MM NN + barTensorMidDiff AA.grading BB MM.grading C N =
      barTensorLeftDiff MM C N + barTensorRightDiff AA.grading MM.grading NN :=
    sub_add_cancel _ _
  have hsum : δ ∘ₗ barTensorRawDifferential MM NN +
        δ ∘ₗ barTensorMidDiff AA.grading BB MM.grading C N =
      (AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
        TensorProduct.map τA (barTensorRawDifferential MM NN) ∘ₗ δ) +
        δ ∘ₗ barTensorMidDiff AA.grading BB MM.grading C N :=
    calc
      δ ∘ₗ barTensorRawDifferential MM NN + δ ∘ₗ barTensorMidDiff AA.grading BB MM.grading C N
        = δ ∘ₗ (barTensorRawDifferential MM NN +
            barTensorMidDiff AA.grading BB MM.grading C N) := (LinearMap.comp_add _ _ _).symm
      _ = δ ∘ₗ barTensorLeftDiff MM C N + δ ∘ₗ barTensorRightDiff AA.grading MM.grading NN := by
          rw [hadd, LinearMap.comp_add]
      _ = AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
            TensorProduct.map τA
              (barTensorLeftDiff MM C N + barTensorRightDiff AA.grading MM.grading NN) ∘ₗ δ := by
          rw [hL, hR, TensorProduct.map_add_right, LinearMap.add_comp, add_assoc]
      _ = (AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
            TensorProduct.map τA (barTensorRawDifferential MM NN) ∘ₗ δ) +
            δ ∘ₗ barTensorMidDiff AA.grading BB MM.grading C N := by
          rw [← hadd, TensorProduct.map_add_right, LinearMap.add_comp, hM, add_assoc]
  set c := δ ∘ₗ barTensorMidDiff AA.grading BB MM.grading C N
  calc
    δ ∘ₗ barTensorRawDifferential MM NN
      = δ ∘ₗ barTensorRawDifferential MM NN + ((1 : R) + (-1 : R)) • c := by simp
    _ = (δ ∘ₗ barTensorRawDifferential MM NN + c) + (-1 : R) • c := by
        rw [add_smul, one_smul, add_assoc]
    _ = ((AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
          TensorProduct.map τA (barTensorRawDifferential MM NN) ∘ₗ δ) + c) + (-1 : R) • c := by
        rw [hsum]
    _ = (AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
          TensorProduct.map τA (barTensorRawDifferential MM NN) ∘ₗ δ) +
          ((1 : R) + (-1 : R)) • c := by rw [add_smul, one_smul, add_assoc]
    _ = AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
          TensorProduct.map τA (barTensorRawDifferential MM NN) ∘ₗ δ := by simp

/-- The bar tensor differential is a left graded coderivation over
`AA.coaugmentedBarDifferential`. -/
theorem isLeftGradedCoderivation_barTensorDifferential (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    Comodule.IsLeftGradedCoderivationOver
      (Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N)))
      (TensorWords.grading (AA.grading.shift 1)) 1 AA.coaugmentedBarDifferential
      (barTensorDifferential MM NN) := by
  let δ := Comodule.leftCoactRTensor (TensorWords R C)
    (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N))
  let τA := (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  have hraw : δ ∘ₗ barTensorRawDifferential MM NN =
      AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
        TensorProduct.map τA (barTensorRawDifferential MM NN) ∘ₗ δ :=
    leftCoactRTensor_comp_barTensorRawDifferential MM NN
  have hΦ : δ ∘ₗ Φ = Φ.lTensor (TensorWords R A) ∘ₗ δ :=
    leftCoactRTensor_comp_barTensorSignTwist (R := R) (A := A) (B := B) (M := M)
      CC.grading NN.grading
  have heq : δ ∘ₗ barTensorDifferential MM NN =
      AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
        TensorProduct.map τA (barTensorDifferential MM NN) ∘ₗ δ :=
    calc
      δ ∘ₗ (Φ ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ)
        = Φ.lTensor (TensorWords R A) ∘ₗ (δ ∘ₗ barTensorRawDifferential MM NN) ∘ₗ Φ := by
          simp only [← LinearMap.comp_assoc]
          rw [hΦ]
      _ = Φ.lTensor (TensorWords R A) ∘ₗ
            (AA.coaugmentedBarDifferential.rTensor _ +
              TensorProduct.map τA (barTensorRawDifferential MM NN)) ∘ₗ
            (Φ.lTensor (TensorWords R A) ∘ₗ δ) := by
          rw [hraw, ← LinearMap.add_comp, LinearMap.comp_assoc, hΦ]
      _ = (AA.coaugmentedBarDifferential.rTensor _ ∘ₗ (Φ ∘ₗ Φ).lTensor (TensorWords R A) +
            TensorProduct.map τA (Φ ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ)) ∘ₗ δ := by
          simp only [LinearMap.lTensor_def, LinearMap.rTensor_def, LinearMap.comp_add,
            LinearMap.add_comp, ← LinearMap.comp_assoc, ← TensorProduct.map_comp,
            LinearMap.id_comp, LinearMap.comp_id]
      _ = AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δ +
            TensorProduct.map τA (barTensorDifferential MM NN) ∘ₗ δ := by
          rw [barTensorSignTwist_comp_self, LinearMap.lTensor_id, LinearMap.comp_id,
            LinearMap.add_comp]
          rfl
  exact Comodule.isLeftGradedCoderivationOver_iff_coact_apply.2 fun x ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.add_apply] using LinearMap.congr_fun heq x

/-- `barTensorLeftDiff` commutes strictly with the right cofree coaction of `Tᶜ(sC)`. -/
private theorem cofreeCoact_comp_barTensorLeftDiff (MM : AInfinityBimodule AA BB M) :
    Comodule.cofreeCoact R (TensorWords R C)
        (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ∘ₗ
      barTensorLeftDiff MM C N =
      (barTensorLeftDiff MM C N).rTensor (TensorWords R C) ∘ₗ
        Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  have hpull : ∀ (z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) (n : N)
      (wC : TensorWords R C),
      Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N))
          ((barTensorAssocLeft R A B C M N).symm (z ⊗ₜ (n ⊗ₜ wC))) =
        ((barTensorAssocLeft R A B C M N).symm.toLinearMap.rTensor (TensorWords R C))
          ((TensorProduct.assoc R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
              (N ⊗[R] TensorWords R C) (TensorWords R C)).symm
            (z ⊗ₜ (TensorProduct.assoc R N (TensorWords R C) (TensorWords R C)).symm
              (n ⊗ₜ Coalgebra.comul wC))) := by
    intro z n wC
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul u v =>
      induction u using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul wA' m' =>
        simp only [barTensorAssocLeft_symm_tmul, Comodule.cofreeCoact_tmul]
        induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
        | tmul a b => simp
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.comp_apply, barTensorLeftDiff, LinearEquiv.coe_coe,
    barTensorAssocLeft_tmul, LinearMap.rTensor_tmul]
  rw [hpull, Comodule.cofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | tmul a b => simp

/-- `barTensorMidDiff` commutes strictly with the right cofree coaction of `Tᶜ(sC)`. -/
private theorem cofreeCoact_comp_barTensorMidDiff (GM : InternalGrading R M ℤ) :
    Comodule.cofreeCoact R (TensorWords R C)
        (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ∘ₗ
      barTensorMidDiff AA.grading BB GM C N =
      (barTensorMidDiff AA.grading BB GM C N).rTensor (TensorWords R C) ∘ₗ
        Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.comp_apply, barTensorMidDiff, LinearEquiv.coe_coe,
    barTensorAssocMid_tmul, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    InternalGrading.koszulTwist_tensorProduct, barTensorAssocMid_symm_tmul,
    Comodule.cofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | tmul a b => simp

/-- Comparing the double suspension `(sM, sN)` twist with the single suspension twist of the bar
tensor product introduces a minus sign. -/
private theorem barTensorAssocRight_koszulTwist (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) :
    (barTensorAssocRight R A B C M N).symm.toLinearMap ∘ₗ
      TensorProduct.map
        (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
        ((barGrading BB CC GN).koszulTwist 1) ∘ₗ
      (barTensorAssocRight R A B C M N).toLinearMap =
      -((barGrading AA CC (barTensorGrading BB.grading GM GN)).koszulTwist 1) := by
  have hP := shift_barTensorGrading_left BB.grading GM GN 1
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, barTensorAssocRight_tmul,
    TensorProduct.map_tmul, LinearMap.neg_apply, barGrading_def]
  rw [hP]
  simp only [barTensorGrading_def, InternalGrading.koszulTwist_tensorProduct,
    TensorProduct.map_tmul, InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply]
  rw [← neg_one_smul R (GM.koszulTwist 1 m), ← neg_one_smul R (GN.koszulTwist 1 n)]
  conv_rhs => rw [← neg_one_smul R]
  simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, smul_smul,
    barTensorAssocRight_symm_tmul]

/-- Pushing the right cofree coaction of `Tᶜ(sC)` past `(barTensorAssocRight ...).symm`. -/
theorem cofreeCoact_barTensorAssocRight_symm (u : TensorWords R A ⊗[R] M)
    (z : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C) :
    Comodule.cofreeCoact R (TensorWords R C)
        (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N))
        ((barTensorAssocRight R A B C M N).symm (u ⊗ₜ z)) =
      ((barTensorAssocRight R A B C M N).symm.toLinearMap.rTensor (TensorWords R C) ∘ₗ
        (TensorProduct.assoc R (TensorWords R A ⊗[R] M)
          ((TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C) (TensorWords R C)).symm.toLinearMap)
        (u ⊗ₜ Comodule.cofreeCoact R (TensorWords R C) (TensorWords R B ⊗[R] N) z) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [TensorProduct.add_tmul, map_add, hu₁, hu₂]
  | tmul wA' m' =>
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
    | tmul bn wC' =>
      induction bn using TensorProduct.inductionOn with
      | add p q hp hq =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hp, hq]
      | tmul wB' n' =>
        simp only [barTensorAssocRight_symm_tmul, Comodule.cofreeCoact_tmul]
        induction Coalgebra.comul (R := R) wC' using TensorProduct.inductionOn with
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
        | tmul a b => simp

/-- The right piece satisfies the right co-Leibniz law with the opposite sign on `b_C`, before
conjugation by `barTensorSignTwist`. -/
private theorem cofreeCoact_comp_barTensorRightDiff (GM : InternalGrading R M ℤ)
    (NN : AInfinityBimodule BB CC N) :
    let ρ := Comodule.cofreeCoact R (TensorWords R C)
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N))
    let τW := (barGrading AA CC (barTensorGrading BB.grading GM NN.grading)).koszulTwist 1
    ρ ∘ₗ barTensorRightDiff AA.grading GM NN =
      (barTensorRightDiff AA.grading GM NN).rTensor (TensorWords R C) ∘ₗ ρ -
        TensorProduct.map τW CC.coaugmentedBarDifferential ∘ₗ ρ := by
  intro ρ τW
  have hsign := barTensorAssocRight_koszulTwist (AA := AA) (BB := BB) (CC := CC) GM NN.grading
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hNN := NN.isGradedCoderivation_barDifferential.coact_apply ((wB ⊗ₜ n) ⊗ₜ wC)
  rw [Comodule.cofree_coact, ← Comodule.cofreeCoact_def] at hNN
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, barTensorRightDiff, LinearEquiv.coe_coe,
    barTensorAssocRight_tmul, TensorProduct.map_tmul]
  rw [cofreeCoact_barTensorAssocRight_symm, hNN, TensorProduct.tmul_add, map_add, sub_eq_add_neg]
  congr 1
  · simp only [Comodule.cofreeCoact_tmul, ρ]
    induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | tmul a b => simp
  · simp only [Comodule.cofreeCoact_tmul, ρ]
    induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, neg_add, ha, hb]
    | tmul a b =>
      have hs := LinearMap.congr_fun hsign ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ a)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, barTensorAssocRight_tmul,
        TensorProduct.map_tmul, LinearMap.neg_apply] at hs
      simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.assoc_symm_tmul,
        LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul]
      rw [hs]
      calc
        (-τW ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ a)) ⊗ₜ CC.coaugmentedBarDifferential b
          = ((-1 : R) • τW ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ a)) ⊗ₜ
              CC.coaugmentedBarDifferential b := by rw [neg_one_smul R]
        _ = (-1 : R) • (τW ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ a) ⊗ₜ
              CC.coaugmentedBarDifferential b) := (TensorProduct.smul_tmul' _ _ _).symm
        _ = -(τW ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ a) ⊗ₜ CC.coaugmentedBarDifferential b) :=
            eq_neg_of_add_eq_zero_left <| by
              set z := τW ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ a) ⊗ₜ[R] CC.coaugmentedBarDifferential b
              calc
                (-1 : R) • z + z = (-1 : R) • z + (1 : R) • z := by rw [one_smul]
                _ = ((-1 : R) + (1 : R)) • z := (add_smul _ _ _).symm
                _ = 0 := by rw [neg_add_cancel, zero_smul]

/-- Conjugating the total Koszul twist by `barTensorSignTwist` leaves it unchanged. -/
private theorem barTensorSignTwist_conj_koszulTwist (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) :
    let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN
    let τW := (barGrading AA CC (barTensorGrading BB.grading GM GN)).koszulTwist 1
    Φ ∘ₗ τW ∘ₗ Φ = τW := by
  intro Φ τW
  have hP := shift_barTensorGrading_left BB.grading GM GN 1
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [Φ, τW, LinearMap.comp_apply, barTensorSignTwist_tmul, barGrading_def]
  rw [hP]
  simp only [barTensorGrading_def, InternalGrading.koszulTwist_tensorProduct,
    TensorProduct.map_tmul, barTensorSignTwist_tmul, InternalGrading.koszulTwist_koszulTwist]

/-- Conjugating `CC.coaugmentedBarDifferential` by its own Koszul twist negates it. -/
private theorem koszulTwist_conj_coaugmentedBarDifferential :
    let τC := (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1
    τC ∘ₗ CC.coaugmentedBarDifferential ∘ₗ τC = -CC.coaugmentedBarDifferential := by
  intro τC
  have hb : LinearMap.IsHomogeneous CC.coaugmentedBarDifferential
      (TensorWords.grading (CC.grading.shift 1)).piece
      (TensorWords.grading (CC.grading.shift 1)).piece 1 := by
    simpa only [TensorWords.grading_piece] using CC.isHomogeneous_coaugmentedBarDifferential
  have h : τC ∘ₗ CC.coaugmentedBarDifferential = -(CC.coaugmentedBarDifferential ∘ₗ τC) := by
    have h1 := hb.koszulTwist_comp_eq_smul 1
    simp only [one_mul, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one] at h1
    refine LinearMap.ext fun x ↦ ?_
    have hx := LinearMap.congr_fun h1 x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hx
    simp only [LinearMap.comp_apply, LinearMap.neg_apply]
    rw [hx, neg_one_smul R]
  calc
    τC ∘ₗ CC.coaugmentedBarDifferential ∘ₗ τC
      = (τC ∘ₗ CC.coaugmentedBarDifferential) ∘ₗ τC := (LinearMap.comp_assoc _ _ _).symm
    _ = -(CC.coaugmentedBarDifferential ∘ₗ (τC ∘ₗ τC)) := by
      rw [h, LinearMap.neg_comp, LinearMap.comp_assoc]
    _ = -CC.coaugmentedBarDifferential := by
      rw [InternalGrading.koszulTwist_comp_self, LinearMap.comp_id]

/-- Subtracting a tensor map with a negated right factor adds the unnegated tensor map. -/
private theorem tensorProduct_map_sub_neg_right {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f g : X →ₗ[R] X) (h : Y →ₗ[R] Y) :
    TensorProduct.map f (LinearMap.id : Y →ₗ[R] Y) - TensorProduct.map g (-h) =
      f.rTensor Y + TensorProduct.map g h := by
  refine TensorProduct.ext' fun x y ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.neg_apply, LinearMap.rTensor_tmul]
  rw [← neg_one_smul R (h y), TensorProduct.tmul_smul, sub_eq_iff_eq_add]
  set z := g x ⊗ₜ[R] h y
  calc
    f x ⊗ₜ[R] y = f x ⊗ₜ[R] y + ((1 : R) + (-1 : R)) • z := by
      rw [add_neg_cancel, zero_smul, add_zero]
    _ = (f x ⊗ₜ[R] y + z) + (-1 : R) • z := by rw [add_smul, one_smul, add_assoc]

/-- The bar tensor differential is a right graded coderivation over
`CC.coaugmentedBarDifferential`. -/
theorem isGradedCoderivation_barTensorDifferential (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    Comodule.IsGradedCoderivationOver
      (barGrading AA CC (barTensorGrading BB.grading MM.grading NN.grading)) 1
      CC.coaugmentedBarDifferential (barTensorDifferential MM NN) := by
  let ρ := Comodule.cofreeCoact R (TensorWords R C)
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N))
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  let τC := (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1
  let τW := (barGrading AA CC (barTensorGrading BB.grading MM.grading NN.grading)).koszulTwist 1
  have hraw : ρ ∘ₗ barTensorRawDifferential MM NN =
      (barTensorRawDifferential MM NN).rTensor (TensorWords R C) ∘ₗ ρ -
        TensorProduct.map τW CC.coaugmentedBarDifferential ∘ₗ ρ := by
    simp only [barTensorRawDifferential, LinearMap.comp_add, LinearMap.comp_sub,
      LinearMap.rTensor_add, LinearMap.rTensor_sub, LinearMap.add_comp, LinearMap.sub_comp,
      cofreeCoact_comp_barTensorLeftDiff, cofreeCoact_comp_barTensorMidDiff,
      cofreeCoact_comp_barTensorRightDiff, ρ, τW]
    abel
  have hΦ : ρ ∘ₗ Φ = TensorProduct.map Φ τC ∘ₗ ρ :=
    cofreeCoact_comp_barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  have hτC2 : τC ∘ₗ τC = LinearMap.id := InternalGrading.koszulTwist_comp_self _ 1
  have hconjW : Φ ∘ₗ τW ∘ₗ Φ = τW :=
    barTensorSignTwist_conj_koszulTwist (AA := AA) (BB := BB) (CC := CC) MM.grading NN.grading
  have hconjC : τC ∘ₗ CC.coaugmentedBarDifferential ∘ₗ τC = -CC.coaugmentedBarDifferential :=
    koszulTwist_conj_coaugmentedBarDifferential (CC := CC)
  have heq : ρ ∘ₗ barTensorDifferential MM NN =
      (barTensorDifferential MM NN).rTensor (TensorWords R C) ∘ₗ ρ +
        TensorProduct.map τW CC.coaugmentedBarDifferential ∘ₗ ρ :=
    calc
      ρ ∘ₗ (Φ ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ)
        = TensorProduct.map Φ τC ∘ₗ (ρ ∘ₗ barTensorRawDifferential MM NN) ∘ₗ Φ := by
          simp only [← LinearMap.comp_assoc]
          rw [hΦ]
      _ = TensorProduct.map Φ τC ∘ₗ
            ((barTensorRawDifferential MM NN).rTensor (TensorWords R C) -
              TensorProduct.map τW CC.coaugmentedBarDifferential) ∘ₗ
            (TensorProduct.map Φ τC ∘ₗ ρ) := by
          rw [hraw, ← LinearMap.sub_comp, LinearMap.comp_assoc, hΦ]
      _ = (TensorProduct.map (Φ ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ) (τC ∘ₗ τC) -
            TensorProduct.map (Φ ∘ₗ τW ∘ₗ Φ) (τC ∘ₗ CC.coaugmentedBarDifferential ∘ₗ τC)) ∘ₗ ρ := by
          simp only [LinearMap.rTensor_def, LinearMap.comp_sub, LinearMap.sub_comp,
            ← LinearMap.comp_assoc, ← TensorProduct.map_comp, LinearMap.id_comp]
      _ = (barTensorDifferential MM NN).rTensor (TensorWords R C) ∘ₗ ρ +
            TensorProduct.map τW CC.coaugmentedBarDifferential ∘ₗ ρ := by
          rw [hτC2, hconjW, hconjC, tensorProduct_map_sub_neg_right, LinearMap.add_comp]
          rfl
  exact Comodule.isGradedCoderivationOver_iff_coact_apply.2 fun x ↦ by
    rw [Comodule.cofree_coact, ← Comodule.cofreeCoact_def]
    have hx := LinearMap.congr_fun heq x
    rw [← LinearMap.lTensor_comp_rTensor] at hx
    simpa only [LinearMap.comp_apply, LinearMap.add_apply] using hx

/-- The bar tensor product `M ⊗_{B∞} N` of an `(A, B)` `A∞` bimodule `M` and a `(B, C)` `A∞`
bimodule `N`. -/
noncomputable def barTensorProduct (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    AInfinityBimodule AA CC ((M ⊗[R] TensorWords R B) ⊗[R] N) where
  grading := barTensorGrading BB.grading MM.grading NN.grading
  barDifferential := barTensorDifferential MM NN
  isHomogeneous_barDifferential := isHomogeneous_barTensorDifferential MM NN
  isLeftGradedCoderivation_barDifferential := isLeftGradedCoderivation_barTensorDifferential MM NN
  isGradedCoderivation_barDifferential := isGradedCoderivation_barTensorDifferential MM NN
  bar_square_zero := barTensorDifferential_sq MM NN

@[simp]
theorem barTensorProduct_grading (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    (MM.barTensorProduct NN).grading = barTensorGrading BB.grading MM.grading NN.grading :=
  (rfl)

@[simp]
theorem barTensorProduct_barDifferential (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule BB CC N) :
    (MM.barTensorProduct NN).barDifferential = barTensorDifferential MM NN :=
  (rfl)

end BarTensorProduct

end TauCeti.AInfinityBimodule
