/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.BarTensorProduct.Components
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Homotopy

/-!
# Functoriality and homotopy invariance of the bar tensor product

This module constructs functoriality of `MM.barTensorProduct NN` in both arguments for
`A∞` bimodule morphisms and homotopies:

* `TauCeti.AInfinityBimoduleHom.barTensorLeft`: functorial action in the left bimodule argument.
* `TauCeti.AInfinityBimoduleHom.barTensorRight`: functorial action in the right bimodule argument.
* `TauCeti.AInfinityBimoduleHom.barTensorMap`: bifunctorial action on a pair of morphisms,
  satisfying the strict interchange law `barTensorLeft_comp_barTensorRight`.
* Identity and composition laws for `barTensorLeft`, `barTensorRight`, and `barTensorMap`.
* `linearPart` formulas on empty middle words `(m ⊗ 1) ⊗ n` and vanishing of opposite-side higher
  suspended components (`suspendedComponent_barTensorLeft_eq_zero_of_pos`,
  `suspendedComponent_barTensorRight_eq_zero_of_pos`).
* `TauCeti.AInfinityBimoduleHom.Homotopy.barTensorLeft`, `Homotopy.barTensorRight`, and
  `Homotopy.barTensorMap`: homotopy functoriality, yielding cohomology invariance and
  quasi-isomorphism stability under homotopy.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped TensorProduct

namespace TauCeti.AInfinityBimoduleHom

open AInfinityBimodule

universe uR uA uB uC uM uM' uM'' uN uN' uN''

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

attribute [local instance] Comodule.cofree

/-! ### Left-argument extension helpers -/

section LeftHelpers

variable {M : Type uM} {M' : Type uM'} {N : Type uN}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup N] [Module R N]

/-- Extend a linear map on the left bar bicomodule across `N ⊗ Tᶜ(sC)`. -/
private noncomputable def barTensorLeftRaw
    (G : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B) :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M' ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C :=
  (barTensorAssocLeft R A B C M' N).symm.toLinearMap ∘ₗ
    G.rTensor (N ⊗[R] TensorWords R C) ∘ₗ
    (barTensorAssocLeft R A B C M N).toLinearMap

/-- `barTensorLeftRaw` preserves the right cofree coaction of `Tᶜ(sC)`. -/
private theorem cofreeCoact_comp_barTensorLeftRaw
    (G : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B) :
    Comodule.cofreeCoact R (TensorWords R C)
        (TensorWords R A ⊗[R] ((M' ⊗[R] TensorWords R B) ⊗[R] N)) ∘ₗ
        barTensorLeftRaw (C := C) (N := N) G =
      (barTensorLeftRaw (C := C) (N := N) G).rTensor (TensorWords R C) ∘ₗ
        Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  have hpull : ∀ (z : (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B) (n : N)
      (wC : TensorWords R C),
      Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M' ⊗[R] TensorWords R B) ⊗[R] N))
          ((barTensorAssocLeft R A B C M' N).symm (z ⊗ₜ (n ⊗ₜ wC))) =
        ((barTensorAssocLeft R A B C M' N).symm.toLinearMap.rTensor (TensorWords R C))
          ((TensorProduct.assoc R ((TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B)
            (N ⊗[R] TensorWords R C) (TensorWords R C)).symm
            (z ⊗ₜ Comodule.cofreeCoact R (TensorWords R C) N (n ⊗ₜ wC))) := by
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
  simp only [LinearMap.comp_apply, barTensorLeftRaw, LinearEquiv.coe_coe, barTensorAssocLeft_tmul,
    LinearMap.rTensor_tmul, hpull, Comodule.cofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | tmul a b => simp

/-- Build a right `Tᶜ(sC)`-comodule homomorphism from `barTensorLeftRaw`. -/
private noncomputable def barTensorLeftComoduleHom
    (G : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B) :
    Comodule.Hom R (TensorWords R C)
      ((TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C)
      ((TensorWords R A ⊗[R] ((M' ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C) where
  toLinearMap := barTensorLeftRaw (C := C) (N := N) G
  map_coact := by
    rw [Comodule.cofree_coact, Comodule.cofree_coact, ← Comodule.cofreeCoact_def,
      ← Comodule.cofreeCoact_def, ← LinearMap.rTensor_def]
    exact (cofreeCoact_comp_barTensorLeftRaw (C := C) (N := N) G).symm

/-- `barTensorSignTwist` commutes past `barTensorLeftRaw`. -/
private theorem barTensorSignTwist_comm_leftRaw (GN : InternalGrading R N ℤ)
    (G : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B) :
    barTensorSignTwist (R := R) (A := A) (B := B) (M := M') CC.grading GN ∘ₗ
        barTensorLeftRaw (C := C) (N := N) G =
      barTensorLeftRaw (C := C) (N := N) G ∘ₗ
        barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN := by
  let F := barTensorLeftRaw (C := C) (N := N) G
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M') CC.grading GN
  have hc := barTensorSignTwist_conj_assocLeft (R := R) (A := A) (B := B) (M := M) (M' := M')
    CC.grading GN G
  calc
    Φ' ∘ₗ F = (Φ' ∘ₗ F ∘ₗ Φ) ∘ₗ Φ := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, barTensorSignTwist_comp_self,
        LinearMap.comp_id]
    _ = F ∘ₗ Φ := by
      simpa only [F, Φ, Φ', barTensorLeftRaw, LinearMap.comp_assoc] using congrArg (· ∘ₗ Φ) hc

/-- Pushing `barTensorAssocLeft.symm` past `leftCoactRTensor`. -/
private theorem leftCoactRTensor_barTensorAssocLeft_symm (z : (TensorWords R A ⊗[R] M') ⊗[R]
    TensorWords R B) (y : N ⊗[R] TensorWords R C) :
    Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R A) ((M' ⊗[R] TensorWords R B) ⊗[R] N))
        ((barTensorAssocLeft R A B C M' N).symm (z ⊗ₜ y)) =
      ((barTensorAssocLeft R A B C M' N).symm.toLinearMap.lTensor (TensorWords R A) ∘ₗ
        (TensorProduct.assoc R (TensorWords R A)
          ((TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B) (N ⊗[R] TensorWords R C)).toLinearMap)
        ((Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M') z) ⊗ₜ y) := by
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ hy₁ hy₂ => simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
  | tmul n wC =>
    induction z using TensorProduct.inductionOn with
    | add x₁ x₂ hx₁ hx₂ => simp only [TensorProduct.add_tmul, map_add, hx₁, hx₂]
    | tmul u wB =>
      induction u using TensorProduct.inductionOn with
      | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
      | tmul wA m' =>
        simp only [barTensorAssocLeft_symm_tmul, Comodule.leftCoactRTensor_tmul,
          Comodule.leftCofreeCoact_tmul]
        induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
        | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
        | tmul a b => simp

/-- Twisted left-coaction compatibility of `barTensorLeftRaw`. -/
private theorem leftCoactRTensor_comp_barTensorLeftRaw
    (τ : TensorWords R A →ₗ[R] TensorWords R A)
    (G : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B)
    (hG : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M') ∘ₗ G =
      TensorProduct.map τ G ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M)) :
    Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R A) ((M' ⊗[R] TensorWords R B) ⊗[R] N)) ∘ₗ
        barTensorLeftRaw (C := C) (N := N) G =
      TensorProduct.map τ (barTensorLeftRaw (C := C) (N := N) G) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hGx := LinearMap.congr_fun hG ((wA ⊗ₜ m) ⊗ₜ wB)
  simp only [LinearMap.comp_apply] at hGx
  simp only [LinearMap.comp_apply, barTensorLeftRaw, LinearEquiv.coe_coe,
    barTensorAssocLeft_tmul, LinearMap.rTensor_tmul, leftCoactRTensor_barTensorAssocLeft_symm,
    hGx, Comodule.leftCoactRTensor_tmul, Comodule.leftCofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | tmul a b => simp

/-- Homogeneity of `barTensorLeftRaw` for any degree `p`. -/
private theorem isHomogeneous_barTensorLeftRaw (GM : InternalGrading R M ℤ)
    (GM' : InternalGrading R M' ℤ) (GN : InternalGrading R N ℤ) {p : ℤ}
    {G : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B}
    (hG : LinearMap.IsHomogeneous G (barGrading AA BB GM).piece
      (barGrading AA BB GM').piece p) :
    LinearMap.IsHomogeneous (barTensorLeftRaw (C := C) (N := N) G)
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece
      (barGrading AA CC (barTensorGrading BB.grading GM' GN)).piece p := by
  let GC := TensorWords.grading (CC.grading.shift 1)
  have h := (isHomogeneous_barTensorAssocLeft_symm AA BB CC GM' GN).comp
    ((hG.rTensor (GN.tensorProduct GC)).comp
      (isHomogeneous_barTensorAssocLeft AA BB CC GM GN))
  simpa only [barTensorLeftRaw, zero_add, add_zero] using h

/-- Rewrite `barTensorLeftRaw G` in `barTensorAssocMid` coordinates using the counit component
`G₀` of a right `Tᶜ(sB)`-comodule morphism `G`. -/
private theorem barTensorLeftRaw_eq_assocMid
    (G : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B)) :
    let G₀ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] TensorWords R A ⊗[R] M' :=
      (TensorProduct.rid R (TensorWords R A ⊗[R] M')).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor (TensorWords R A ⊗[R] M') ∘ₗ
        G.toLinearMap
    barTensorLeftRaw (C := C) (N := N) G.toLinearMap =
      (barTensorAssocMid R A B C M' N).symm.toLinearMap ∘ₗ
        (G₀.rTensor (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) ∘ₗ
          (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B)
            (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C))).symm.toLinearMap ∘ₗ
          (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor
            (TensorWords R A ⊗[R] M)) ∘ₗ
        (barTensorAssocMid R A B C M N).toLinearMap := by
  intro G₀
  have hlift : G.toLinearMap = G₀.rTensor (TensorWords R B) ∘ₗ
      Comodule.cofreeCoact R (TensorWords R B) (TensorWords R A ⊗[R] M) := by
    have h := congrArg Comodule.Hom.toLinearMap
      (Comodule.Hom.cofreeLift_rid_comp_lTensor_counit_comp G)
    simpa only [Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact,
      ← Comodule.cofreeCoact_def, G₀] using h.symm
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [barTensorLeftRaw, LinearMap.comp_apply, LinearEquiv.coe_coe,
    barTensorAssocLeft_tmul, barTensorAssocMid_tmul, LinearMap.rTensor_tmul, hlift,
    Comodule.cofreeCoact_tmul, Comodule.leftCofreeCoact_tmul, LinearMap.lTensor_tmul]
  induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hu, hv]
  | tmul u v =>
    simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.assoc_tmul]
    induction G₀ ((wA ⊗ₜ m) ⊗ₜ u) using TensorProduct.inductionOn with
    | add p q hp hq => simp only [TensorProduct.add_tmul, map_add]; rw [hp, hq]
    | tmul wA' m' => simp only [barTensorAssocLeft_symm_tmul, barTensorAssocMid_symm_tmul]

/-- Trilinear pairing used to commute `G₀` past `barTensorRightCore NN` via coassociativity. -/
private noncomputable def leftMapTripleEval (GM' : InternalGrading R M' ℤ)
    (NN : AInfinityBimodule BB CC N)
    (G₀ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] TensorWords R A ⊗[R] M')
    (x : TensorWords R A ⊗[R] M) (y : N ⊗[R] TensorWords R C) :
    TensorWords R B ⊗[R] (TensorWords R B ⊗[R] TensorWords R B) →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :=
  let τAM' := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
    (GM'.shift 1)).koszulTwist 1
  let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
  TensorProduct.lift
    { toFun := fun w₁ ↦
        TensorProduct.lift
          { toFun := fun w₂ ↦
              { toFun := fun w₃ ↦
                  τAM' (G₀ (x ⊗ₜ w₁)) ⊗ₜ (τB w₂ ⊗ₜ barTensorRightCore NN (w₃ ⊗ₜ y))
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
          TensorProduct.tmul_add, map_add, TensorProduct.add_tmul]
      map_smul' := fun r a ↦ TensorProduct.ext' fun w₂ w₃ ↦ by
        simp only [LinearMap.smul_apply, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
          TensorProduct.tmul_smul, map_smul, ← TensorProduct.smul_tmul', RingHom.id_apply] }

@[simp]
private theorem leftMapTripleEval_tmul (GM' : InternalGrading R M' ℤ)
    (NN : AInfinityBimodule BB CC N)
    (G₀ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] TensorWords R A ⊗[R] M')
    (x : TensorWords R A ⊗[R] M) (y : N ⊗[R] TensorWords R C)
    (w₁ w₂ w₃ : TensorWords R B) :
    leftMapTripleEval (AA := AA) (BB := BB) GM' NN G₀ x y (w₁ ⊗ₜ (w₂ ⊗ₜ w₃)) =
      ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM'.shift 1)).koszulTwist 1
          (G₀ (x ⊗ₜ w₁)) ⊗ₜ
        ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1 w₂ ⊗ₜ
          barTensorRightCore NN (w₃ ⊗ₜ y)) := (rfl)

/-- Evaluate the left-hand side of the mid-coordinate commutation against `leftMapTripleEval`. -/
private theorem leftMapTripleEval_lhs (GM' : InternalGrading R M' ℤ)
    (NN : AInfinityBimodule BB CC N)
    (G₀ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] TensorWords R A ⊗[R] M')
    (x : TensorWords R A ⊗[R] M) (wB : TensorWords R B) (y : N ⊗[R] TensorWords R C) :
    let τAM' := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
      (GM'.shift 1)).koszulTwist 1
    let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
    let Gm := G₀.rTensor (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) ∘ₗ
      (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B)
        (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C))).symm.toLinearMap ∘ₗ
      (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor
        (TensorWords R A ⊗[R] M)
    let N₀' := TensorProduct.map τAM' (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
      Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C))
    N₀' (Gm (x ⊗ₜ (wB ⊗ₜ y))) =
      leftMapTripleEval (AA := AA) (BB := BB) GM' NN G₀ x y
        (Coalgebra.comul.lTensor (TensorWords R B) (Coalgebra.comul wB)) := by
  intro τAM' τB Gm N₀'
  simp only [Gm, N₀', LinearMap.comp_apply, LinearMap.lTensor_tmul,
    Comodule.leftCofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hu, hv]
  | tmul u v =>
    simp only [TensorProduct.assoc_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
      Comodule.leftCofreeCoact_tmul, LinearMap.lTensor_tmul]
    induction Coalgebra.comul (R := R) v using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]
    | tmul a b =>
      simp [τAM', τB]

/-- Evaluate the right-hand side of the mid-coordinate commutation against `leftMapTripleEval`. -/
private theorem leftMapTripleEval_rhs (GM : InternalGrading R M ℤ) (GM' : InternalGrading R M' ℤ)
    (NN : AInfinityBimodule BB CC N) {p : ℤ}
    (G₀ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] TensorWords R A ⊗[R] M')
    (hτG₀ : ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM'.shift 1)).koszulTwist 1
        ∘ₗ G₀ =
      ((p.negOnePow : ℤ) : R) • (G₀ ∘ₗ TensorProduct.map
        (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist 1)
        ((TensorWords.grading (BB.grading.shift 1)).koszulTwist 1)))
    (x : TensorWords R A ⊗[R] M) (wB : TensorWords R B) (y : N ⊗[R] TensorWords R C) :
    let τAM := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct
      (GM.shift 1)).koszulTwist 1
    let τB := (TensorWords.grading (BB.grading.shift 1)).koszulTwist 1
    let Gm := G₀.rTensor (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) ∘ₗ
      (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B)
        (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C))).symm.toLinearMap ∘ₗ
      (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor
        (TensorWords R A ⊗[R] M)
    let N₀ := TensorProduct.map τAM (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
      Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C))
    ((p.negOnePow : ℤ) : R) • Gm (N₀ (x ⊗ₜ (wB ⊗ₜ y))) =
      leftMapTripleEval (AA := AA) (BB := BB) GM' NN G₀ x y
        ((TensorProduct.assoc R (TensorWords R B) (TensorWords R B) (TensorWords R B))
          (Coalgebra.comul.rTensor (TensorWords R B) (Coalgebra.comul wB))) := by
  intro τAM τB Gm N₀
  have hτB : Coalgebra.comul ∘ₗ τB = TensorProduct.map τB τB ∘ₗ
      (Coalgebra.comul : TensorWords R B →ₗ[R] TensorWords R B ⊗[R] TensorWords R B) := by
    simp only [τB, TensorWords.koszulTwist_grading, TensorWords.comul_eq_deconcatenation,
      TensorWords.deconcatenation_natural]
  simp only [Gm, N₀, LinearMap.comp_apply, TensorProduct.map_tmul,
    Comodule.leftCofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add, hu, hv]
  | tmul u v =>
    have hcu := LinearMap.congr_fun hτB u
    simp only [LinearMap.comp_apply] at hcu
    simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      Comodule.leftCofreeCoact_tmul, hcu, LinearMap.rTensor_tmul]
    induction Coalgebra.comul (R := R) u using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add, ha, hb]
    | tmul a b =>
      have hstep := LinearMap.congr_fun hτG₀ (x ⊗ₜ a)
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, TensorProduct.map_tmul] at hstep
      simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
        TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, leftMapTripleEval_tmul,
        τAM, τB]
      rw [TensorProduct.smul_tmul', ← hstep]

/-- Graded commutation between `barTensorRightDiff - barTensorMidDiff` and `barTensorLeftRaw`
for any degree-`p` right `Tᶜ(sB)`-comodule map `G`. -/
private theorem barTensorRightSubMid_comp_barTensorLeftRaw
    (GM : InternalGrading R M ℤ) (GM' : InternalGrading R M' ℤ)
    (NN : AInfinityBimodule BB CC N) {p : ℤ}
    (G : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B))
    (hG : LinearMap.IsHomogeneous G.toLinearMap (barGrading AA BB GM).piece
      (barGrading AA BB GM').piece p) :
    (barTensorRightDiff AA.grading GM' NN - barTensorMidDiff AA.grading BB GM' C N) ∘ₗ
        barTensorLeftRaw (C := C) (N := N) G.toLinearMap =
      ((p.negOnePow : ℤ) : R) •
        (barTensorLeftRaw (C := C) (N := N) G.toLinearMap ∘ₗ
          (barTensorRightDiff AA.grading GM NN - barTensorMidDiff AA.grading BB GM C N)) := by
  let GA := TensorWords.grading (AA.grading.shift 1)
  let GB := TensorWords.grading (BB.grading.shift 1)
  let τAM := (GA.tensorProduct (GM.shift 1)).koszulTwist 1
  let τAM' := (GA.tensorProduct (GM'.shift 1)).koszulTwist 1
  let τB := GB.koszulTwist 1
  let G₀ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] TensorWords R A ⊗[R] M' :=
    (TensorProduct.rid R (TensorWords R A ⊗[R] M')).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor (TensorWords R A ⊗[R] M') ∘ₗ
      G.toLinearMap
  have hG₀ : LinearMap.IsHomogeneous G₀ (barGrading AA BB GM).piece
      (GA.tensorProduct (GM'.shift 1)).piece p := by
    have hcu := TensorWords.isHomogeneous_rid_comp_lTensor_counit
      (GA.tensorProduct (GM'.shift 1)) (BB.grading.shift 1)
    simp only [barGrading_def] at hG
    have hc := hcu.comp hG
    simpa only [add_zero, G₀, LinearMap.comp_assoc, barGrading_def] using hc
  have hτG₀ : τAM' ∘ₗ G₀ = ((p.negOnePow : ℤ) : R) • (G₀ ∘ₗ TensorProduct.map τAM τB) := by
    simpa only [τAM, τAM', τB, one_mul, barGrading_def,
      InternalGrading.koszulTwist_tensorProduct] using hG₀.koszulTwist_comp_eq_smul 1
  let Gm := G₀.rTensor (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) ∘ₗ
    (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B)
      (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C))).symm.toLinearMap ∘ₗ
    (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor
      (TensorWords R A ⊗[R] M)
  let N₀ := TensorProduct.map τAM (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
    Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C))
  let N₀' := TensorProduct.map τAM' (TensorProduct.map τB (barTensorRightCore NN) ∘ₗ
    Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C))
  have hmid : N₀' ∘ₗ Gm = ((p.negOnePow : ℤ) : R) • (Gm ∘ₗ N₀) := by
    refine TensorProduct.ext' fun x z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
    | tmul wB y =>
      have hLHS := leftMapTripleEval_lhs (AA := AA) (BB := BB) GM' NN G₀ x wB y
      have hRHS := leftMapTripleEval_rhs (AA := AA) (BB := BB) GM GM' NN G₀ hτG₀ x wB y
      have hcoassoc := LinearMap.congr_fun
        (Coalgebra.coassoc (R := R) (A := TensorWords R B)) wB
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcoassoc
      change N₀' (Gm (x ⊗ₜ (wB ⊗ₜ y))) = ((p.negOnePow : ℤ) : R) • Gm (N₀ (x ⊗ₜ (wB ⊗ₜ y)))
      rw [hLHS, hRHS, hcoassoc]
  rw [barTensorRightDiff_sub_barTensorMidDiff AA.grading GM' NN,
    barTensorRightDiff_sub_barTensorMidDiff AA.grading GM NN,
    barTensorLeftRaw_eq_assocMid (C := C) (N := N) G]
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hstep := LinearMap.congr_fun hmid
    ((barTensorAssocMid R A B C M N) ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    Gm, N₀, N₀', τAM, τAM', τB, GA, GB, G₀] at hstep
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← map_smul, hstep]

end LeftHelpers

/-! ### Functoriality in the left bimodule argument -/

section BarTensorLeft

variable {M : Type uM} {M' : Type uM'} {M'' : Type uM''} {N : Type uN}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup M''] [Module R M''] [AddCommGroup N] [Module R N]
  {MM : AInfinityBimodule AA BB M} {MM' : AInfinityBimodule AA BB M'}
  {MM'' : AInfinityBimodule AA BB M''}

private theorem barDifferential_comp_barTensorLeft (NN : AInfinityBimodule BB CC N)
    (f : AInfinityBimoduleHom MM MM') :
    (MM'.barTensorProduct NN).barDifferential ∘ₗ
        (barTensorLeftComoduleHom (C := C) (N := N) f.barMap).toLinearMap =
      (barTensorLeftComoduleHom (C := C) (N := N) f.barMap).toLinearMap ∘ₗ
        (MM.barTensorProduct NN).barDifferential := by
  let F := barTensorLeftRaw (C := C) (N := N) f.barMap
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M') CC.grading NN.grading
  have hL : barTensorLeftDiff MM' C N ∘ₗ F = F ∘ₗ barTensorLeftDiff MM C N := by
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    simp only [F, barTensorLeftRaw, barTensorLeftDiff_def, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ← LinearMap.rTensor_comp_apply,
      f.barDifferential_comp_barMap]
  have hRM := barTensorRightSubMid_comp_barTensorLeftRaw (AA := AA) (BB := BB) (CC := CC)
    MM.grading MM'.grading NN f.barHom f.isHomogeneous_barMap
  simp only [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at hRM
  have hraw : barTensorRawDifferential MM' NN ∘ₗ F = F ∘ₗ barTensorRawDifferential MM NN := by
    rw [barTensorRawDifferential_def, barTensorRawDifferential_def, add_sub_assoc, add_sub_assoc,
      LinearMap.add_comp, LinearMap.comp_add, hL, hRM]
  have hΦ : Φ' ∘ₗ F = F ∘ₗ Φ :=
    barTensorSignTwist_comm_leftRaw (CC := CC) NN.grading f.barMap
  rw [barTensorProduct_barDifferential, barTensorProduct_barDifferential]
  change barTensorDifferential MM' NN ∘ₗ F = F ∘ₗ barTensorDifferential MM NN
  calc
    barTensorDifferential MM' NN ∘ₗ F
      = Φ' ∘ₗ barTensorRawDifferential MM' NN ∘ₗ (Φ' ∘ₗ F) := by
        simp only [barTensorDifferential_def, Φ', LinearMap.comp_assoc]
    _ = Φ' ∘ₗ (barTensorRawDifferential MM' NN ∘ₗ F) ∘ₗ Φ := by
        rw [hΦ]; simp only [LinearMap.comp_assoc]
    _ = (Φ' ∘ₗ F) ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ := by
        rw [hraw]; simp only [LinearMap.comp_assoc]
    _ = F ∘ₗ barTensorDifferential MM NN := by
        rw [hΦ]; simp only [barTensorDifferential_def, Φ, LinearMap.comp_assoc]

/-- Functorial action of `MM ↦ MM.barTensorProduct NN` on a morphism `f : MM → MM'`. -/
noncomputable def barTensorLeft (NN : AInfinityBimodule BB CC N)
    (f : AInfinityBimoduleHom MM MM') :
    AInfinityBimoduleHom (MM.barTensorProduct NN) (MM'.barTensorProduct NN) where
  barHom := barTensorLeftComoduleHom (C := C) (N := N) f.barMap
  leftCoact_comp_barMap := by
    have hl : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M') ∘ₗ f.barMap =
      TensorProduct.map LinearMap.id f.barMap ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
      simpa only [← LinearMap.lTensor_def] using f.leftCoact_comp_barMap
    dsimp only [barTensorLeftComoduleHom]
    simpa only [← LinearMap.lTensor_def] using
      leftCoactRTensor_comp_barTensorLeftRaw (C := C) (N := N) LinearMap.id f.barMap hl
  isHomogeneous_barMap := by
    rw [barTensorProduct_grading, barTensorProduct_grading]
    exact isHomogeneous_barTensorLeftRaw (AA := AA) (BB := BB) (CC := CC)
      MM.grading MM'.grading NN.grading f.isHomogeneous_barMap
  barDifferential_comp_barMap := barDifferential_comp_barTensorLeft NN f

@[simp]
theorem barMap_barTensorLeft (NN : AInfinityBimodule BB CC N)
    (f : AInfinityBimoduleHom MM MM') :
    (barTensorLeft NN f).barMap =
      (barTensorAssocLeft R A B C M' N).symm.toLinearMap ∘ₗ
        f.barMap.rTensor (N ⊗[R] TensorWords R C) ∘ₗ
        (barTensorAssocLeft R A B C M N).toLinearMap := (rfl)

@[simp]
theorem barTensorLeft_id (NN : AInfinityBimodule BB CC N) (MM : AInfinityBimodule AA BB M) :
    barTensorLeft NN (AInfinityBimoduleHom.id MM) =
      AInfinityBimoduleHom.id (MM.barTensorProduct NN) := by
  apply barMap_injective
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp

@[simp]
theorem barTensorLeft_comp (NN : AInfinityBimodule BB CC N)
    (g : AInfinityBimoduleHom MM' MM'') (f : AInfinityBimoduleHom MM MM') :
    barTensorLeft NN (g.comp f) = (barTensorLeft NN g).comp (barTensorLeft NN f) := by
  apply barMap_injective
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [barMap_comp, barMap_barTensorLeft, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, ← LinearMap.rTensor_comp_apply]

/-- On empty middle words, the linear part of `barTensorLeft NN f` acts on `m` by `f.linearPart`. -/
@[simp]
theorem linearPart_barTensorLeft_tmul_one (NN : AInfinityBimodule BB CC N)
    (f : AInfinityBimoduleHom MM MM') (m : M) (n : N) :
    (barTensorLeft NN f).linearPart ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) =
      (f.linearPart m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n := by
  rw [linearPart_apply, taylor_def, LinearMap.comp_apply, barMap_barTensorLeft]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, barTensorAssocLeft_tmul,
    LinearMap.rTensor_tmul, barMap_one_tmul_tmul_one, barTensorAssocLeft_symm_tmul,
    taylorProj_tmul, TensorWords.counit_eq_counit, TensorWords.counit_one, one_smul]

/-- Higher suspended components of `barTensorLeft NN f` with any right algebra inputs vanish. -/
@[simp]
theorem suspendedComponent_barTensorLeft_eq_zero_of_pos (NN : AInfinityBimodule BB CC N)
    (f : AInfinityBimoduleHom MM MM') {i j : ℕ} (hj : 0 < j) :
    (barTensorLeft NN f).suspendedComponent i j = 0 := by
  apply TensorProduct.ext_threefold
  intro a x c
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hx₁, hx₂]
  | tmul mb n =>
    induction mb using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hy₁, hy₂]
    | tmul m wB =>
      simp only [suspendedComponent_tmul, taylor_def, barMap_barTensorLeft, LinearMap.comp_apply,
        LinearEquiv.coe_coe, barTensorAssocLeft_tmul, LinearMap.rTensor_tmul, LinearMap.zero_apply]
      induction f.barMap ((TensorWords.of R A i a ⊗ₜ m) ⊗ₜ wB) using
          TensorProduct.inductionOn with
      | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq, add_zero]
      | tmul u v =>
        induction u using TensorProduct.inductionOn with
        | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq, add_zero]
        | tmul wA' m' =>
          simp [barTensorAssocLeft_symm_tmul, taylorProj_tmul, TensorWords.counit_eq_counit,
            TensorWords.counit_of_of_ne_zero R C hj.ne']

end BarTensorLeft

/-! ### Right-argument extension helpers -/

section RightHelpers

variable {M : Type uM} {N : Type uN} {N' : Type uN'}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/-- Unconjugated extension of a degree-`p` map on the right bar bicomodule across `Tᶜ(sA) ⊗ sM`. -/
private noncomputable def barTensorRightRaw (GM : InternalGrading R M ℤ) (p : ℤ)
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C) :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N')) ⊗[R] TensorWords R C :=
  (barTensorAssocRight R A B C M N').symm.toLinearMap ∘ₗ
    TensorProduct.map
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist p) G ∘ₗ
    (barTensorAssocRight R A B C M N).toLinearMap

/-- Conjugated extension of a degree-`p` map on the right bar bicomodule. -/
private noncomputable def barTensorRightMap (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) (GN' : InternalGrading R N' ℤ) (p : ℤ)
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C) :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N')) ⊗[R] TensorWords R C :=
  barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN' ∘ₗ
    barTensorRightRaw (AA := AA) GM p G ∘ₗ
    barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN

/-- `barTensorRightRaw` commutes with the right cofree coaction of `Tᶜ(sC)`. -/
private theorem cofreeCoact_comp_barTensorRightRaw (GM : InternalGrading R M ℤ) (p : ℤ)
    (G : Comodule.Hom R (TensorWords R C)
      ((TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C)
      ((TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C)) :
    Comodule.cofreeCoact R (TensorWords R C)
        (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N')) ∘ₗ
        barTensorRightRaw (AA := AA) GM p G.toLinearMap =
      (barTensorRightRaw (AA := AA) GM p G.toLinearMap).rTensor (TensorWords R C) ∘ₗ
        Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  have hco := G.map_coact
  rw [Comodule.cofree_coact, Comodule.cofree_coact, ← Comodule.cofreeCoact_def,
    ← Comodule.cofreeCoact_def, ← LinearMap.rTensor_def] at hco
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hGx := LinearMap.congr_fun hco ((wB ⊗ₜ n) ⊗ₜ wC)
  simp only [LinearMap.comp_apply] at hGx
  simp only [LinearMap.comp_apply, barTensorRightRaw, LinearEquiv.coe_coe,
    barTensorAssocRight_tmul, TensorProduct.map_tmul]
  rw [cofreeCoact_barTensorAssocRight_symm, ← hGx, Comodule.cofreeCoact_tmul,
    Comodule.cofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | tmul a b => simp

/-- Conjugating `barTensorRightRaw` by `barTensorSignTwist` preserves the right cofree coaction. -/
private theorem cofreeCoact_comp_barTensorRightMap (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) (GN' : InternalGrading R N' ℤ) (p : ℤ)
    (G : Comodule.Hom R (TensorWords R C)
      ((TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C)
      ((TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C)) :
    Comodule.cofreeCoact R (TensorWords R C)
        (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N')) ∘ₗ
        barTensorRightMap (AA := AA) (CC := CC) GM GN GN' p G.toLinearMap =
      (barTensorRightMap (AA := AA) (CC := CC) GM GN GN' p G.toLinearMap).rTensor
          (TensorWords R C) ∘ₗ
        Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  let ρ := Comodule.cofreeCoact R (TensorWords R C)
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N))
  let ρ' := Comodule.cofreeCoact R (TensorWords R C)
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N'))
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN'
  let τC := (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1
  let Gr := barTensorRightRaw (AA := AA) GM p G.toLinearMap
  have hΦ : ρ ∘ₗ Φ = TensorProduct.map Φ τC ∘ₗ ρ :=
    cofreeCoact_comp_barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN
  have hΦ' : ρ' ∘ₗ Φ' = TensorProduct.map Φ' τC ∘ₗ ρ' :=
    cofreeCoact_comp_barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN'
  have hraw := cofreeCoact_comp_barTensorRightRaw (AA := AA) GM p G
  change ρ' ∘ₗ (Φ' ∘ₗ Gr ∘ₗ Φ) = (Φ' ∘ₗ Gr ∘ₗ Φ).rTensor (TensorWords R C) ∘ₗ ρ
  calc
    ρ' ∘ₗ (Φ' ∘ₗ Gr ∘ₗ Φ)
      = TensorProduct.map Φ' τC ∘ₗ (ρ' ∘ₗ Gr) ∘ₗ Φ := by
        simp only [← LinearMap.comp_assoc]; rw [hΦ']
    _ = TensorProduct.map Φ' τC ∘ₗ Gr.rTensor (TensorWords R C) ∘ₗ
          (TensorProduct.map Φ τC ∘ₗ ρ) := by
        rw [hraw, LinearMap.comp_assoc, hΦ]
    _ = TensorProduct.map (Φ' ∘ₗ Gr ∘ₗ Φ) (τC ∘ₗ τC) ∘ₗ ρ := by
        simp only [LinearMap.rTensor_def, ← LinearMap.comp_assoc, ← TensorProduct.map_comp,
          LinearMap.id_comp]
    _ = (Φ' ∘ₗ Gr ∘ₗ Φ).rTensor (TensorWords R C) ∘ₗ ρ := by
        rw [InternalGrading.koszulTwist_comp_self, ← LinearMap.rTensor_def]

/-- Build a right `Tᶜ(sC)`-comodule homomorphism from `barTensorRightMap`. -/
private noncomputable def barTensorRightComoduleHom (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) (GN' : InternalGrading R N' ℤ) (p : ℤ)
    (G : Comodule.Hom R (TensorWords R C)
      ((TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C)
      ((TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C)) :
    Comodule.Hom R (TensorWords R C)
      ((TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C)
      ((TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N')) ⊗[R] TensorWords R C) where
  toLinearMap := barTensorRightMap (AA := AA) (CC := CC) GM GN GN' p G.toLinearMap
  map_coact := by
    rw [Comodule.cofree_coact, Comodule.cofree_coact, ← Comodule.cofreeCoact_def,
      ← Comodule.cofreeCoact_def, ← LinearMap.rTensor_def]
    exact (cofreeCoact_comp_barTensorRightMap (AA := AA) (CC := CC) GM GN GN' p G).symm

/-- Twisted left-coaction compatibility of `barTensorRightRaw`. -/
private theorem leftCoactRTensor_comp_barTensorRightRaw (GM : InternalGrading R M ℤ) (p : ℤ)
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C) :
    Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N')) ∘ₗ
        barTensorRightRaw (AA := AA) GM p G =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p)
          (barTensorRightRaw (AA := AA) GM p G) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  have hτA : Coalgebra.comul ∘ₗ (TensorWords.grading (AA.grading.shift 1)).koszulTwist p =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p)
        ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p) ∘ₗ
        (Coalgebra.comul : TensorWords R A →ₗ[R] TensorWords R A ⊗[R] TensorWords R A) := by
    simp only [TensorWords.koszulTwist_grading, TensorWords.comul_eq_deconcatenation,
      TensorWords.deconcatenation_natural]
  have hpull : ∀ (wA : TensorWords R A) (m : M)
      (z : (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C),
      Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N'))
          ((barTensorAssocRight R A B C M N').symm ((wA ⊗ₜ m) ⊗ₜ z)) =
        (((barTensorAssocRight R A B C M N').symm.toLinearMap.lTensor (TensorWords R A) ∘ₗ
          (TensorProduct.assoc R (TensorWords R A) (TensorWords R A ⊗[R] M) _).toLinearMap)
          (Comodule.leftCofreeCoact R (TensorWords R A) M (wA ⊗ₜ m) ⊗ₜ z)) := by
    intro wA m z
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
    | tmul bn wC' =>
      induction bn using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hy]
      | tmul wB' n' =>
        simp only [barTensorAssocRight_symm_tmul, Comodule.leftCoactRTensor_tmul,
          Comodule.leftCofreeCoact_tmul]
        induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
        | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
        | tmul a b => simp
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hc := LinearMap.congr_fun hτA wA
  simp only [LinearMap.comp_apply] at hc
  simp only [LinearMap.comp_apply, barTensorRightRaw, LinearEquiv.coe_coe,
    barTensorAssocRight_tmul, TensorProduct.map_tmul, InternalGrading.koszulTwist_tensorProduct,
    hpull, Comodule.leftCoactRTensor_tmul, Comodule.leftCofreeCoact_tmul, hc]
  induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | tmul a b => simp [TensorProduct.map_tmul]

/-- Twisted left-coaction compatibility of `barTensorRightMap`. -/
private theorem leftCoactRTensor_comp_barTensorRightMap (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) (GN' : InternalGrading R N' ℤ) (p : ℤ)
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C) :
    Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N')) ∘ₗ
        barTensorRightMap (AA := AA) (CC := CC) GM GN GN' p G =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p)
          (barTensorRightMap (AA := AA) (CC := CC) GM GN GN' p G) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  let δ := Comodule.leftCoactRTensor (TensorWords R C)
    (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N))
  let δ' := Comodule.leftCoactRTensor (TensorWords R C)
    (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N'))
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN'
  let τA := (TensorWords.grading (AA.grading.shift 1)).koszulTwist p
  have hΦ : δ ∘ₗ Φ = Φ.lTensor (TensorWords R A) ∘ₗ δ :=
    leftCoactRTensor_comp_barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN
  have hΦ' : δ' ∘ₗ Φ' = Φ'.lTensor (TensorWords R A) ∘ₗ δ' :=
    leftCoactRTensor_comp_barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN'
  have hraw := leftCoactRTensor_comp_barTensorRightRaw (AA := AA) GM p G
  change δ' ∘ₗ (Φ' ∘ₗ barTensorRightRaw (AA := AA) GM p G ∘ₗ Φ) =
    TensorProduct.map τA (Φ' ∘ₗ barTensorRightRaw (AA := AA) GM p G ∘ₗ Φ) ∘ₗ δ
  calc
    δ' ∘ₗ (Φ' ∘ₗ barTensorRightRaw (AA := AA) GM p G ∘ₗ Φ)
      = Φ'.lTensor (TensorWords R A) ∘ₗ (δ' ∘ₗ barTensorRightRaw (AA := AA) GM p G) ∘ₗ Φ := by
        simp only [← LinearMap.comp_assoc]; rw [hΦ']
    _ = Φ'.lTensor (TensorWords R A) ∘ₗ
          TensorProduct.map τA (barTensorRightRaw (AA := AA) GM p G) ∘ₗ
          (Φ.lTensor (TensorWords R A) ∘ₗ δ) := by
        rw [hraw, LinearMap.comp_assoc, hΦ]
    _ = TensorProduct.map τA (Φ' ∘ₗ barTensorRightRaw (AA := AA) GM p G ∘ₗ Φ) ∘ₗ δ := by
        simp only [LinearMap.lTensor_def, ← LinearMap.comp_assoc, ← TensorProduct.map_comp,
          LinearMap.id_comp, LinearMap.comp_id]

/-- Homogeneity of `barTensorRightMap` for any degree `p`. -/
private theorem isHomogeneous_barTensorRightMap (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) (GN' : InternalGrading R N' ℤ) {p : ℤ}
    {G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C}
    (hG : LinearMap.IsHomogeneous G (barGrading BB CC GN).piece
      (barGrading BB CC GN').piece p) :
    LinearMap.IsHomogeneous (barTensorRightMap (AA := AA) (CC := CC) GM GN GN' p G)
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece
      (barGrading AA CC (barTensorGrading BB.grading GM GN')).piece p := by
  let GA := TensorWords.grading (AA.grading.shift 1)
  have hshift : GA.tensorProduct (GM.shift 1) = (GA.tensorProduct GM).shift 1 := by
    refine InternalGrading.ext fun n ↦ ?_
    rw [InternalGrading.shift_piece, InternalGrading.tensorProduct_piece_eq_iSup,
      InternalGrading.tensorProduct_piece_eq_iSup]
    refine iSup_congr fun q ↦ ?_
    have h : n - q + 1 = n + 1 - q := by omega
    rw [InternalGrading.shift_piece, h]
  have hτAM : LinearMap.IsHomogeneous ((GA.tensorProduct (GM.shift 1)).koszulTwist p)
      (GA.tensorProduct GM).piece (GA.tensorProduct GM).piece 0 := by
    refine (LinearMap.isHomogeneous_shift_piece_iff (G := GA.tensorProduct GM)
      (H := GA.tensorProduct GM) (c := 1)).1 ?_
    rw [← hshift]
    exact LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using (GA.tensorProduct (GM.shift 1)).koszulTwist_mem_piece hx p
  have hraw : LinearMap.IsHomogeneous (barTensorRightRaw (AA := AA) GM p G)
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece
      (barGrading AA CC (barTensorGrading BB.grading GM GN')).piece p := by
    have h := (isHomogeneous_barTensorAssocRight_symm AA BB CC GM GN').comp
      ((hτAM.tensorProduct hG).comp (isHomogeneous_barTensorAssocRight AA BB CC GM GN))
    simpa only [barTensorRightRaw, zero_add, add_zero] using h
  have hΦ := isHomogeneous_barTensorSignTwist AA BB.grading CC GM GN
  have hΦ' := isHomogeneous_barTensorSignTwist AA BB.grading CC GM GN'
  simpa only [barTensorRightMap, zero_add, add_zero] using (hΦ'.comp (hraw.comp hΦ))

/-- Reassociate a map on `(Tᶜ(sB) ⊗ N) ⊗ Tᶜ(sC)` to `Tᶜ(sB) ⊗ (N ⊗ Tᶜ(sC))`. -/
private noncomputable def assocRightMap
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C) :
    TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C) →ₗ[R]
      TensorWords R B ⊗[R] (N' ⊗[R] TensorWords R C) :=
  (TensorProduct.assoc R (TensorWords R B) N' (TensorWords R C)).toLinearMap ∘ₗ
    G ∘ₗ (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap

/-- Pulling `leftCofreeCoact` through `assocRightMap` matches the twisted `leftCoactRTensor`. -/
private theorem leftCofreeCoact_comp_assocRightMap (p : ℤ)
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C)
    (hG : Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R B) N') ∘ₗ G =
      TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist p) G ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R B) N)) :
    Comodule.leftCofreeCoact R (TensorWords R B) (N' ⊗[R] TensorWords R C) ∘ₗ assocRightMap G =
      TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist p)
          (assocRightMap G) ∘ₗ
        Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C) := by
  have hpull : ∀ z : (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C,
      Comodule.leftCofreeCoact R (TensorWords R B) (N' ⊗[R] TensorWords R C)
        ((TensorProduct.assoc R (TensorWords R B) N' (TensorWords R C)) z) =
      (TensorProduct.assoc R (TensorWords R B) N' (TensorWords R C)).toLinearMap.lTensor
          (TensorWords R B)
        (Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R B) N') z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul bn c =>
      induction bn using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul b n' =>
        simp only [TensorProduct.assoc_tmul, Comodule.leftCofreeCoact_tmul,
          Comodule.leftCoactRTensor_tmul]
        induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
        | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
        | tmul u v => simp
  refine TensorProduct.ext' fun wB y ↦ ?_
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ hy₁ hy₂ => simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
  | tmul n wC =>
    have hGx := LinearMap.congr_fun hG ((wB ⊗ₜ n) ⊗ₜ wC)
    simp only [LinearMap.comp_apply] at hGx
    simp only [assocRightMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_symm_tmul, hpull, hGx, Comodule.leftCoactRTensor_tmul,
      Comodule.leftCofreeCoact_tmul]
    induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | tmul u v => simp

/-- Express `barTensorRightRaw` in `barTensorAssocMid` coordinates. -/
private theorem barTensorRightRaw_assocMid_symm (GM : InternalGrading R M ℤ) (p : ℤ)
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C)
    (z : (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C))) :
    barTensorRightRaw (AA := AA) GM p G ((barTensorAssocMid R A B C M N).symm z) =
      (barTensorAssocMid R A B C M N').symm
        (TensorProduct.map
          (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist p)
          (assocRightMap G) z) := by
  let τAM := ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).koszulTwist p
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
  | tmul x y =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
    | tmul b nc =>
      induction nc using TensorProduct.inductionOn with
      | add q r hq hr => simp only [TensorProduct.tmul_add, map_add, hq, hr]
      | tmul n₀ c =>
        induction x using TensorProduct.inductionOn with
        | add x₁ x₂ hx₁ hx₂ => simp only [TensorProduct.add_tmul, map_add, hx₁, hx₂]
        | tmul a m₀ =>
          simp only [barTensorRightRaw, LinearMap.comp_apply, LinearEquiv.coe_coe,
            barTensorAssocMid_symm_tmul, barTensorAssocRight_tmul, TensorProduct.map_tmul,
            assocRightMap, TensorProduct.assoc_symm_tmul]
          induction G ((b ⊗ₜ n₀) ⊗ₜ c) using TensorProduct.inductionOn with
          | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
          | tmul bn c' =>
            induction bn using TensorProduct.inductionOn with
            | add q r hq hr =>
              simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hq, hr]
            | tmul b' n' =>
              induction τAM (a ⊗ₜ m₀) using TensorProduct.inductionOn with
              | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
              | tmul a' m' =>
                simp [barTensorAssocRight_symm_tmul, barTensorAssocMid_symm_tmul]

/-- Graded commutation between `barTensorLeftDiff - barTensorMidDiff` and `barTensorRightRaw`
for any `G` intertwining the left `Tᶜ(sB)`-coactions with twist `p`. -/
private theorem barTensorLeftSubMid_comp_barTensorRightRaw (MM : AInfinityBimodule AA BB M) (p : ℤ)
    (G : (TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R B ⊗[R] N') ⊗[R] TensorWords R C)
    (hG : Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R B) N') ∘ₗ G =
      TensorProduct.map ((TensorWords.grading (BB.grading.shift 1)).koszulTwist p) G ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R B) N)) :
    (barTensorLeftDiff MM C N' - barTensorMidDiff AA.grading BB MM.grading C N') ∘ₗ
        barTensorRightRaw (AA := AA) MM.grading p G =
      ((p.negOnePow : ℤ) : R) •
        (barTensorRightRaw (AA := AA) MM.grading p G ∘ₗ
          (barTensorLeftDiff MM C N - barTensorMidDiff AA.grading BB MM.grading C N)) := by
  let GA := TensorWords.grading (AA.grading.shift 1)
  let GB := TensorWords.grading (BB.grading.shift 1)
  let τAM := (GA.tensorProduct (MM.grading.shift 1)).koszulTwist p
  let τB := GB.koszulTwist p
  let Ga := assocRightMap G
  have hGa_coact := leftCofreeCoact_comp_assocRightMap (BB := BB) p G hG
  have hτL : τAM ∘ₗ leftTaylor AA MM.taylor =
      ((p.negOnePow : ℤ) : R) • (leftTaylor AA MM.taylor ∘ₗ TensorProduct.map τAM τB) := by
    simpa only [τAM, τB, GA, GB, mul_one, barGrading_def,
      InternalGrading.koszulTwist_tensorProduct] using
      (isHomogeneous_leftTaylor_taylor MM).koszulTwist_comp_eq_smul p
  have hsq : ((p.negOnePow : ℤ) : R) * ((p.negOnePow : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, ← two_mul,
      Int.negOnePow_two_mul, Units.val_one, Int.cast_one]
  rw [barTensorLeftDiff_sub_barTensorMidDiff MM, barTensorLeftDiff_sub_barTensorMidDiff MM]
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hmid :
      (((leftTaylor AA MM.taylor).rTensor _ ∘ₗ
          (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B) _).symm.toLinearMap ∘ₗ
          (Comodule.leftCofreeCoact R (TensorWords R B) (N' ⊗[R] TensorWords R C)).lTensor _)
        (τAM (wA ⊗ₜ m) ⊗ₜ Ga (wB ⊗ₜ (n ⊗ₜ wC)))) =
      ((p.negOnePow : ℤ) : R) •
        (TensorProduct.map τAM Ga
          (((leftTaylor AA MM.taylor).rTensor _ ∘ₗ
            (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B) _).symm.toLinearMap ∘ₗ
            (Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C)).lTensor _)
          ((wA ⊗ₜ m) ⊗ₜ (wB ⊗ₜ (n ⊗ₜ wC))))) := by
    have hcx := LinearMap.congr_fun hGa_coact (wB ⊗ₜ (n ⊗ₜ wC))
    simp only [LinearMap.comp_apply] at hcx
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, Ga]
    rw [hcx]
    simp only [Comodule.leftCofreeCoact_tmul]
    induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
    | add u v hu hv =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add, hu, hv]
    | tmul u v =>
      have hstep := LinearMap.congr_fun hτL ((wA ⊗ₜ m) ⊗ₜ u)
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
        τB, GB] at hstep
      simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe,
        TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul]
      rw [hstep, ← TensorProduct.smul_tmul', smul_smul, hsq, one_smul]
  have h1 : barTensorRightRaw (AA := AA) MM.grading p G ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) =
      (barTensorAssocMid R A B C M N').symm (τAM (wA ⊗ₜ m) ⊗ₜ Ga (wB ⊗ₜ (n ⊗ₜ wC))) := by
    simpa only [barTensorAssocMid_symm_tmul, TensorProduct.map_tmul] using
      barTensorRightRaw_assocMid_symm (AA := AA) MM.grading p G
        ((wA ⊗ₜ m) ⊗ₜ (wB ⊗ₜ (n ⊗ₜ wC)))
  have h2 := barTensorRightRaw_assocMid_symm (AA := AA) MM.grading p G
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, h1, h2,
    LinearEquiv.apply_symm_apply, barTensorAssocMid_tmul, ← map_smul, hmid]
  rfl

end RightHelpers

/-! ### Functoriality in the right bimodule argument -/

section BarTensorRight

variable {M : Type uM} {N : Type uN} {N' : Type uN'} {N'' : Type uN''}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N'] [AddCommGroup N''] [Module R N'']
  {NN : AInfinityBimodule BB CC N} {NN' : AInfinityBimodule BB CC N'}
  {NN'' : AInfinityBimodule BB CC N''}

private theorem barDifferential_comp_barTensorRight (MM : AInfinityBimodule AA BB M)
    (g : AInfinityBimoduleHom NN NN') :
    (MM.barTensorProduct NN').barDifferential ∘ₗ
        (barTensorRightComoduleHom (AA := AA) (CC := CC)
          MM.grading NN.grading NN'.grading 0 g.barHom).toLinearMap =
      (barTensorRightComoduleHom (AA := AA) (CC := CC)
        MM.grading NN.grading NN'.grading 0 g.barHom).toLinearMap ∘ₗ
        (MM.barTensorProduct NN).barDifferential := by
  let G_raw := barTensorRightRaw (AA := AA) MM.grading 0 g.barMap
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN'.grading
  have hR : barTensorRightDiff AA.grading MM.grading NN' ∘ₗ G_raw =
      G_raw ∘ₗ barTensorRightDiff AA.grading MM.grading NN := by
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    simp only [G_raw, barTensorRightRaw, barTensorRightDiff_def, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, barTensorAssocRight_tmul,
      InternalGrading.koszulTwist_zero, TensorProduct.map_tmul, LinearMap.id_apply]
    congr 2
    exact LinearMap.congr_fun g.barDifferential_comp_barMap ((wB ⊗ₜ n) ⊗ₜ wC)
  have hLM := barTensorLeftSubMid_comp_barTensorRightRaw (AA := AA) (BB := BB) (C := C)
    MM 0 g.barMap (by simpa only [InternalGrading.koszulTwist_zero,
      ← LinearMap.lTensor_def] using g.leftCoact_comp_barMap)
  simp only [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul, LinearMap.sub_comp,
    LinearMap.comp_sub] at hLM
  have hraw : barTensorRawDifferential MM NN' ∘ₗ G_raw =
      G_raw ∘ₗ barTensorRawDifferential MM NN := by
    rw [barTensorRawDifferential_def, barTensorRawDifferential_def, LinearMap.sub_comp,
      LinearMap.add_comp, LinearMap.comp_sub, LinearMap.comp_add]
    calc
      barTensorLeftDiff MM C N' ∘ₗ G_raw +
          barTensorRightDiff AA.grading MM.grading NN' ∘ₗ G_raw -
          barTensorMidDiff AA.grading BB MM.grading C N' ∘ₗ G_raw
        = (barTensorLeftDiff MM C N' ∘ₗ G_raw -
            barTensorMidDiff AA.grading BB MM.grading C N' ∘ₗ G_raw) +
            barTensorRightDiff AA.grading MM.grading NN' ∘ₗ G_raw := by abel
      _ = (G_raw ∘ₗ barTensorLeftDiff MM C N -
            G_raw ∘ₗ barTensorMidDiff AA.grading BB MM.grading C N) +
            G_raw ∘ₗ barTensorRightDiff AA.grading MM.grading NN := by rw [hLM, hR]
      _ = _ := by abel
  rw [barTensorProduct_barDifferential, barTensorProduct_barDifferential]
  change barTensorDifferential MM NN' ∘ₗ (Φ' ∘ₗ G_raw ∘ₗ Φ) =
    (Φ' ∘ₗ G_raw ∘ₗ Φ) ∘ₗ barTensorDifferential MM NN
  calc
    barTensorDifferential MM NN' ∘ₗ (Φ' ∘ₗ G_raw ∘ₗ Φ)
      = Φ' ∘ₗ barTensorRawDifferential MM NN' ∘ₗ (Φ' ∘ₗ Φ') ∘ₗ G_raw ∘ₗ Φ := by
        simp only [barTensorDifferential_def, Φ', LinearMap.comp_assoc]
    _ = Φ' ∘ₗ (barTensorRawDifferential MM NN' ∘ₗ G_raw) ∘ₗ Φ := by
        rw [barTensorSignTwist_comp_self, LinearMap.id_comp, LinearMap.comp_assoc]
    _ = Φ' ∘ₗ G_raw ∘ₗ (Φ ∘ₗ Φ) ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ := by
        rw [hraw, barTensorSignTwist_comp_self, LinearMap.id_comp]
        simp only [LinearMap.comp_assoc]
    _ = (Φ' ∘ₗ G_raw ∘ₗ Φ) ∘ₗ barTensorDifferential MM NN := by
        simp only [barTensorDifferential_def, Φ, LinearMap.comp_assoc]

/-- Functorial action of `NN ↦ MM.barTensorProduct NN` on a morphism `g : NN → NN'`. -/
noncomputable def barTensorRight (MM : AInfinityBimodule AA BB M)
    (g : AInfinityBimoduleHom NN NN') :
    AInfinityBimoduleHom (MM.barTensorProduct NN) (MM.barTensorProduct NN') where
  barHom := barTensorRightComoduleHom (AA := AA) (CC := CC)
    MM.grading NN.grading NN'.grading 0 g.barHom
  leftCoact_comp_barMap := by
    dsimp only [barTensorRightComoduleHom]
    simpa only [InternalGrading.koszulTwist_zero, ← LinearMap.lTensor_def] using
      leftCoactRTensor_comp_barTensorRightMap (AA := AA) (CC := CC)
        MM.grading NN.grading NN'.grading 0 g.barMap
  isHomogeneous_barMap := by
    rw [barTensorProduct_grading, barTensorProduct_grading]
    exact isHomogeneous_barTensorRightMap (AA := AA) (BB := BB) (CC := CC)
      MM.grading NN.grading NN'.grading g.isHomogeneous_barMap
  barDifferential_comp_barMap := barDifferential_comp_barTensorRight MM g

@[simp]
theorem barMap_barTensorRight (MM : AInfinityBimodule AA BB M)
    (g : AInfinityBimoduleHom NN NN') :
    (barTensorRight MM g).barMap =
      barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN'.grading ∘ₗ
        ((barTensorAssocRight R A B C M N').symm.toLinearMap ∘ₗ
          g.barMap.lTensor (TensorWords R A ⊗[R] M) ∘ₗ
          (barTensorAssocRight R A B C M N).toLinearMap) ∘ₗ
        barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading := by
  change barTensorRightMap (AA := AA) (CC := CC) MM.grading NN.grading NN'.grading 0 g.barMap = _
  simp only [barTensorRightMap, barTensorRightRaw, InternalGrading.koszulTwist_zero,
    ← LinearMap.lTensor_def]

@[simp]
theorem barTensorRight_id (MM : AInfinityBimodule AA BB M) (NN : AInfinityBimodule BB CC N) :
    barTensorRight MM (AInfinityBimoduleHom.id NN) =
      AInfinityBimoduleHom.id (MM.barTensorProduct NN) := by
  apply barMap_injective
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp

@[simp]
theorem barTensorRight_comp (MM : AInfinityBimodule AA BB M)
    (h : AInfinityBimoduleHom NN' NN'') (g : AInfinityBimoduleHom NN NN') :
    barTensorRight MM (h.comp g) = (barTensorRight MM h).comp (barTensorRight MM g) := by
  apply barMap_injective
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [barMap_comp, barMap_barTensorRight, LinearMap.comp_apply,
    barTensorSignTwist_tmul, LinearEquiv.coe_coe, barTensorAssocRight_tmul, LinearMap.lTensor_tmul]
  have hΦ2 := LinearMap.congr_fun
    (barTensorSignTwist_comp_self (R := R) (A := A) (B := B) (M := M) CC.grading NN'.grading)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hΦ2
  rw [hΦ2]
  simp only [LinearEquiv.apply_symm_apply, LinearMap.lTensor_tmul]

/-- On empty middle words, the linear part of `barTensorRight MM g` acts on `n` by
`g.linearPart`. -/
@[simp]
theorem linearPart_barTensorRight_tmul_one (MM : AInfinityBimodule AA BB M)
    (g : AInfinityBimoduleHom NN NN') (m : M) (n : N) :
    (barTensorRight MM g).linearPart ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) =
      (m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ g.linearPart n := by
  have htw : NN'.grading.koszulTwist 1 (g.linearPart (NN.grading.koszulTwist 1 n)) =
      g.linearPart n := by
    have h := LinearMap.congr_fun (g.isHomogeneous_linearPart.koszulTwist_comp_eq_smul 1)
      (NN.grading.koszulTwist 1 n)
    simpa only [LinearMap.comp_apply, mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one,
      one_smul, InternalGrading.koszulTwist_koszulTwist] using h
  rw [linearPart_apply, taylor_def, LinearMap.comp_apply, barMap_barTensorRight]
  simp only [LinearMap.comp_apply, barTensorSignTwist_tmul, TensorWords.koszulTwist_grading,
    TensorWords.map_one, LinearEquiv.coe_coe, barTensorAssocRight_tmul, LinearMap.lTensor_tmul,
    barMap_one_tmul_tmul_one, barTensorAssocRight_symm_tmul, taylorProj_tmul,
    TensorWords.counit_eq_counit, TensorWords.counit_one, one_smul, htw]

/-- Higher suspended components of `barTensorRight MM g` with any left algebra inputs vanish. -/
@[simp]
theorem suspendedComponent_barTensorRight_eq_zero_of_pos (MM : AInfinityBimodule AA BB M)
    (g : AInfinityBimoduleHom NN NN') {i j : ℕ} (hi : 0 < i) :
    (barTensorRight MM g).suspendedComponent i j = 0 := by
  apply TensorProduct.ext_threefold
  intro a x c
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hx₁, hx₂]
  | tmul mb n =>
    induction mb using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hy₁, hy₂]
    | tmul m wB =>
      simp only [suspendedComponent_tmul, taylor_def, barMap_barTensorRight, LinearMap.comp_apply,
        barTensorSignTwist_tmul, LinearEquiv.coe_coe, barTensorAssocRight_tmul,
        LinearMap.lTensor_tmul, LinearMap.zero_apply]
      induction g.barMap ((wB ⊗ₜ NN.grading.koszulTwist 1 n) ⊗ₜ
          (TensorWords.grading (CC.grading.shift 1)).koszulTwist 1 (TensorWords.of R C j c)) using
          TensorProduct.inductionOn with
      | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq, add_zero]
      | tmul u v =>
        induction u using TensorProduct.inductionOn with
        | add p q hp hq =>
          simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hp, hq, add_zero]
        | tmul wB' n' =>
          simp [barTensorAssocRight_symm_tmul, barTensorSignTwist_tmul, taylorProj_tmul,
            TensorWords.counit_eq_counit, TensorWords.counit_of_of_ne_zero R A hi.ne']

end BarTensorRight

/-! ### Bifunctoriality and strict interchange law -/

section Bifunctor

variable {M : Type uM} {M' : Type uM'} {M'' : Type uM''}
  {N : Type uN} {N' : Type uN'} {N'' : Type uN''}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
  [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] [AddCommGroup N''] [Module R N'']
  {MM : AInfinityBimodule AA BB M} {MM' : AInfinityBimodule AA BB M'}
  {MM'' : AInfinityBimodule AA BB M''}
  {NN : AInfinityBimodule BB CC N} {NN' : AInfinityBimodule BB CC N'}
  {NN'' : AInfinityBimodule BB CC N''}

/-- The left and right functorial actions strictly commute (the interchange law). -/
theorem barTensorLeft_comp_barTensorRight (f : AInfinityBimoduleHom MM MM')
    (g : AInfinityBimoduleHom NN NN') :
    (barTensorLeft NN' f).comp (barTensorRight MM g) =
      (barTensorRight MM' g).comp (barTensorLeft NN f) := by
  apply barMap_injective
  let F := barTensorLeftRaw (C := C) (N := N) f.barMap
  let F' := barTensorLeftRaw (C := C) (N := N') f.barMap
  let G := barTensorRightRaw (AA := AA) MM.grading 0 g.barMap
  let G' := barTensorRightRaw (AA := AA) MM'.grading 0 g.barMap
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN'.grading
  let Ψ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M') CC.grading NN.grading
  let Ψ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M') CC.grading NN'.grading
  have hFΦ : Ψ ∘ₗ F = F ∘ₗ Φ :=
    barTensorSignTwist_comm_leftRaw (CC := CC) NN.grading f.barMap
  have hF'Φ' : Ψ' ∘ₗ F' = F' ∘ₗ Φ' :=
    barTensorSignTwist_comm_leftRaw (CC := CC) NN'.grading f.barMap
  have hraw : F' ∘ₗ G = G' ∘ₗ F := by
    let Ga := assocRightMap g.barMap
    have hGa : Comodule.leftCofreeCoact R (TensorWords R B) (N' ⊗[R] TensorWords R C) ∘ₗ Ga =
        Ga.lTensor (TensorWords R B) ∘ₗ
          Comodule.leftCofreeCoact R (TensorWords R B) (N ⊗[R] TensorWords R C) := by
      simpa only [← LinearMap.lTensor_def, InternalGrading.koszulTwist_zero] using
        leftCofreeCoact_comp_assocRightMap (BB := BB) 0 g.barMap
          (by simpa only [InternalGrading.koszulTwist_zero, ← LinearMap.lTensor_def] using
            g.leftCoact_comp_barMap)
    have hGe := barTensorRightRaw_assocMid_symm (AA := AA) MM.grading 0 g.barMap
    have hGe' := barTensorRightRaw_assocMid_symm (AA := AA) MM'.grading 0 g.barMap
    simp only [InternalGrading.koszulTwist_zero, ← LinearMap.lTensor_def] at hGe hGe'
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    have hF_mid := barTensorLeftRaw_eq_assocMid (C := C) (N := N) f.barHom
    have hF'_mid := barTensorLeftRaw_eq_assocMid (C := C) (N := N') f.barHom
    have hG_pt : G ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) =
        (barTensorAssocMid R A B C M N').symm ((wA ⊗ₜ m) ⊗ₜ Ga (wB ⊗ₜ (n ⊗ₜ wC))) := by
      simpa only [barTensorAssocMid_symm_tmul, LinearMap.lTensor_tmul] using
        hGe ((wA ⊗ₜ m) ⊗ₜ (wB ⊗ₜ (n ⊗ₜ wC)))
    simp only [LinearMap.comp_apply, hG_pt]
    dsimp only [F, F', G']
    rw [hF_mid, hF'_mid]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hGe',
      barTensorAssocMid_tmul, LinearMap.lTensor_tmul]
    congr 1
    have hcx := LinearMap.congr_fun hGa (wB ⊗ₜ (n ⊗ₜ wC))
    simp only [LinearMap.comp_apply] at hcx
    rw [hcx]
    simp only [Comodule.leftCofreeCoact_tmul]
    induction Coalgebra.comul (R := R) wB using TensorProduct.inductionOn with
    | add u v hu hv =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hu, hv]
    | tmul u v => simp [Ga]
  rw [barMap_comp, barMap_comp]
  change F' ∘ₗ (Φ' ∘ₗ G ∘ₗ Φ) = (Ψ' ∘ₗ G' ∘ₗ Ψ) ∘ₗ F
  calc
    F' ∘ₗ (Φ' ∘ₗ G ∘ₗ Φ)
      = (F' ∘ₗ Φ') ∘ₗ G ∘ₗ Φ := by simp only [LinearMap.comp_assoc]
    _ = Ψ' ∘ₗ (F' ∘ₗ G) ∘ₗ Φ := by rw [← hF'Φ']; simp only [LinearMap.comp_assoc]
    _ = Ψ' ∘ₗ G' ∘ₗ (F ∘ₗ Φ) := by rw [hraw]; simp only [LinearMap.comp_assoc]
    _ = (Ψ' ∘ₗ G' ∘ₗ Ψ) ∘ₗ F := by rw [← hFΦ]; simp only [LinearMap.comp_assoc]

/-- Bifunctorial action of the bar tensor product on a pair of bimodule morphisms. -/
noncomputable def barTensorMap (f : AInfinityBimoduleHom MM MM')
    (g : AInfinityBimoduleHom NN NN') :
    AInfinityBimoduleHom (MM.barTensorProduct NN) (MM'.barTensorProduct NN') :=
  (barTensorLeft NN' f).comp (barTensorRight MM g)

/-- The bifunctorial map can equivalently be factored with `barTensorLeft` first. -/
theorem barTensorMap_eq_barTensorRight_comp_barTensorLeft
    (f : AInfinityBimoduleHom MM MM') (g : AInfinityBimoduleHom NN NN') :
    barTensorMap f g = (barTensorRight MM' g).comp (barTensorLeft NN f) :=
  barTensorLeft_comp_barTensorRight f g

@[simp]
theorem barTensorMap_id (MM : AInfinityBimodule AA BB M) (NN : AInfinityBimodule BB CC N) :
    barTensorMap (AInfinityBimoduleHom.id MM) (AInfinityBimoduleHom.id NN) =
      AInfinityBimoduleHom.id (MM.barTensorProduct NN) := by
  simp [barTensorMap]

@[simp]
theorem barTensorMap_comp (f₂ : AInfinityBimoduleHom MM' MM'') (f₁ : AInfinityBimoduleHom MM MM')
    (g₂ : AInfinityBimoduleHom NN' NN'') (g₁ : AInfinityBimoduleHom NN NN') :
    barTensorMap (f₂.comp f₁) (g₂.comp g₁) =
      (barTensorMap f₂ g₂).comp (barTensorMap f₁ g₁) := by
  simp only [barTensorMap, barTensorLeft_comp, barTensorRight_comp, comp_assoc]
  rw [← comp_assoc (barTensorLeft NN'' f₁) (barTensorRight MM g₂),
    barTensorLeft_comp_barTensorRight f₁ g₂, comp_assoc]

/-- On empty middle words, the linear part of `barTensorMap f g` applies `f.linearPart` and
`g.linearPart` independently. -/
@[simp]
theorem linearPart_barTensorMap_tmul_one (f : AInfinityBimoduleHom MM MM')
    (g : AInfinityBimoduleHom NN NN') (m : M) (n : N) :
    (barTensorMap f g).linearPart ((m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ n) =
      (f.linearPart m ⊗ₜ (1 : TensorWords R B)) ⊗ₜ g.linearPart n := by
  simp [barTensorMap]

end Bifunctor

/-! ### Homotopy functoriality and cohomology invariance -/

section HomotopyFunctor

variable {M : Type uM} {M' : Type uM'} {N : Type uN} {N' : Type uN'}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
  {MM : AInfinityBimodule AA BB M} {MM' : AInfinityBimodule AA BB M'}
  {NN : AInfinityBimodule BB CC N} {NN' : AInfinityBimodule BB CC N'}

private theorem barMap_sub_barMap_barTensorLeft (NN : AInfinityBimodule BB CC N)
    {f g : AInfinityBimoduleHom MM MM'} (h : Homotopy f g) :
    (AInfinityBimoduleHom.barTensorLeft NN f).barMap -
        (AInfinityBimoduleHom.barTensorLeft NN g).barMap =
      (MM'.barTensorProduct NN).barDifferential ∘ₗ
          (barTensorLeftComoduleHom (C := C) (N := N) h.barMap).toLinearMap +
        (barTensorLeftComoduleHom (C := C) (N := N) h.barMap).toLinearMap ∘ₗ
          (MM.barTensorProduct NN).barDifferential := by
  let H := barTensorLeftRaw (C := C) (N := N) h.barMap
  let F := barTensorLeftRaw (C := C) (N := N) f.barMap
  let G := barTensorLeftRaw (C := C) (N := N) g.barMap
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M') CC.grading NN.grading
  have hL : F - G = barTensorLeftDiff MM' C N ∘ₗ H + H ∘ₗ barTensorLeftDiff MM C N := by
    refine barTensor_ext fun wA m wB n wC ↦ ?_
    have he := LinearMap.congr_fun h.barMap_sub_barMap ((wA ⊗ₜ m) ⊗ₜ wB)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at he
    have he' := sub_eq_iff_eq_add.mp he
    simp only [F, G, H, barTensorLeftRaw, barTensorLeftDiff_def, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, barTensorAssocLeft_tmul, LinearMap.rTensor_tmul]
    refine sub_eq_iff_eq_add.mpr ?_
    rw [he', TensorProduct.add_tmul, TensorProduct.add_tmul, map_add, map_add]
  have hRM := barTensorRightSubMid_comp_barTensorLeftRaw (AA := AA) (BB := BB) (CC := CC)
    MM.grading MM'.grading NN h.barHomotopy h.isHomogeneous_barHomotopy
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one] at hRM
  have hRM0 : (barTensorRightDiff AA.grading MM'.grading NN -
        barTensorMidDiff AA.grading BB MM'.grading C N) ∘ₗ H +
      H ∘ₗ (barTensorRightDiff AA.grading MM.grading NN -
        barTensorMidDiff AA.grading BB MM.grading C N) = 0 := by
    rw [hRM]; module
  have hraw : F - G =
      barTensorRawDifferential MM' NN ∘ₗ H + H ∘ₗ barTensorRawDifferential MM NN := by
    rw [barTensorRawDifferential_def, barTensorRawDifferential_def, add_sub_assoc, add_sub_assoc,
      LinearMap.add_comp, LinearMap.comp_add]
    calc
      F - G = (barTensorLeftDiff MM' C N ∘ₗ H + H ∘ₗ barTensorLeftDiff MM C N) + 0 := by
        rw [hL, add_zero]
      _ = _ := by rw [← hRM0]; abel
  have hΦH : Φ' ∘ₗ H = H ∘ₗ Φ :=
    barTensorSignTwist_comm_leftRaw (CC := CC) NN.grading h.barMap
  have hΦFG : Φ' ∘ₗ (F - G) ∘ₗ Φ = F - G := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub]
    dsimp only [F, G, Φ, Φ', barTensorLeftRaw]
    rw [barTensorSignTwist_conj_assocLeft CC.grading NN.grading f.barMap,
      barTensorSignTwist_conj_assocLeft CC.grading NN.grading g.barMap]
  rw [barTensorProduct_barDifferential, barTensorProduct_barDifferential]
  change F - G = barTensorDifferential MM' NN ∘ₗ H + H ∘ₗ barTensorDifferential MM NN
  calc
    F - G = Φ' ∘ₗ (F - G) ∘ₗ Φ := hΦFG.symm
    _ = Φ' ∘ₗ (barTensorRawDifferential MM' NN ∘ₗ H + H ∘ₗ barTensorRawDifferential MM NN) ∘ₗ
          Φ := by rw [hraw]
    _ = Φ' ∘ₗ barTensorRawDifferential MM' NN ∘ₗ (H ∘ₗ Φ) +
          (Φ' ∘ₗ H) ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ := by
        simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_assoc]
    _ = Φ' ∘ₗ barTensorRawDifferential MM' NN ∘ₗ (Φ' ∘ₗ H) +
          (H ∘ₗ Φ) ∘ₗ barTensorRawDifferential MM NN ∘ₗ Φ := by
        congr 1
        · rw [hΦH]
        · rw [hΦH]
    _ = barTensorDifferential MM' NN ∘ₗ H + H ∘ₗ barTensorDifferential MM NN := by
        simp only [barTensorDifferential_def, Φ, Φ', LinearMap.comp_assoc]

/-- Extend a bimodule homotopy in the left argument of `barTensorProduct`. -/
noncomputable def Homotopy.barTensorLeft (NN : AInfinityBimodule BB CC N)
    {f g : AInfinityBimoduleHom MM MM'} (h : Homotopy f g) :
    Homotopy (AInfinityBimoduleHom.barTensorLeft NN f)
      (AInfinityBimoduleHom.barTensorLeft NN g) where
  barHomotopy := barTensorLeftComoduleHom (C := C) (N := N) h.barMap
  leftCoact_comp_barMap :=
    leftCoactRTensor_comp_barTensorLeftRaw (C := C) (N := N)
      ((TensorWords.grading (AA.grading.shift 1)).koszulTwist (-1)) h.barMap
      h.leftCoact_comp_barMap
  isHomogeneous_barHomotopy := by
    rw [barTensorProduct_grading, barTensorProduct_grading]
    exact isHomogeneous_barTensorLeftRaw (AA := AA) (BB := BB) (CC := CC)
      MM.grading MM'.grading NN.grading h.isHomogeneous_barHomotopy
  barMap_sub_barMap := barMap_sub_barMap_barTensorLeft NN h

private theorem barMap_sub_barMap_barTensorRight_raw (MM : AInfinityBimodule AA BB M)
    {g₁ g₂ : AInfinityBimoduleHom NN NN'} (h : Homotopy g₁ g₂) :
    barTensorRightRaw (AA := AA) MM.grading 0 g₁.barMap -
        barTensorRightRaw (AA := AA) MM.grading 0 g₂.barMap =
      barTensorRightDiff AA.grading MM.grading NN' ∘ₗ
          barTensorRightRaw (AA := AA) MM.grading (-1) h.barMap +
        barTensorRightRaw (AA := AA) MM.grading (-1) h.barMap ∘ₗ
          barTensorRightDiff AA.grading MM.grading NN := by
  have hτ2 : (((TensorWords.grading (AA.grading.shift 1)).tensorProduct
      (MM.grading.shift 1)).koszulTwist 1) ∘ₗ
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct
        (MM.grading.shift 1)).koszulTwist (-1)) = LinearMap.id := by
    rw [InternalGrading.koszulTwist_comp, add_neg_cancel, InternalGrading.koszulTwist_zero]
  have hτ2' : (((TensorWords.grading (AA.grading.shift 1)).tensorProduct
      (MM.grading.shift 1)).koszulTwist (-1)) ∘ₗ
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct
        (MM.grading.shift 1)).koszulTwist 1) = LinearMap.id := by
    rw [InternalGrading.koszulTwist_comp, neg_add_cancel, InternalGrading.koszulTwist_zero]
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have he := LinearMap.congr_fun h.barMap_sub_barMap ((wB ⊗ₜ n) ⊗ₜ wC)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at he
  have he' := sub_eq_iff_eq_add.mp he
  have ht1 := LinearMap.congr_fun hτ2 (wA ⊗ₜ m)
  have ht2 := LinearMap.congr_fun hτ2' (wA ⊗ₜ m)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at ht1 ht2
  simp only [barTensorRightRaw, barTensorRightDiff_def, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, barTensorAssocRight_tmul, InternalGrading.koszulTwist_zero,
    TensorProduct.map_tmul, LinearMap.id_apply, ht1, ht2]
  refine sub_eq_iff_eq_add.mpr ?_
  rw [he', TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add]

private theorem barMap_sub_barMap_barTensorRight (MM : AInfinityBimodule AA BB M)
    {g₁ g₂ : AInfinityBimoduleHom NN NN'} (h : Homotopy g₁ g₂) :
    (AInfinityBimoduleHom.barTensorRight MM g₁).barMap -
        (AInfinityBimoduleHom.barTensorRight MM g₂).barMap =
      (MM.barTensorProduct NN').barDifferential ∘ₗ
          (barTensorRightComoduleHom (AA := AA) (CC := CC)
            MM.grading NN.grading NN'.grading (-1) h.barHomotopy).toLinearMap +
        (barTensorRightComoduleHom (AA := AA) (CC := CC)
          MM.grading NN.grading NN'.grading (-1) h.barHomotopy).toLinearMap ∘ₗ
          (MM.barTensorProduct NN).barDifferential := by
  let H_raw := barTensorRightRaw (AA := AA) MM.grading (-1) h.barMap
  let G₁_raw := barTensorRightRaw (AA := AA) MM.grading 0 g₁.barMap
  let G₂_raw := barTensorRightRaw (AA := AA) MM.grading 0 g₂.barMap
  let Φ := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  let Φ' := barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading NN'.grading
  have hR := barMap_sub_barMap_barTensorRight_raw MM h
  have hLM := barTensorLeftSubMid_comp_barTensorRightRaw (AA := AA) (BB := BB) (C := C)
    MM (-1) h.barMap h.leftCoact_comp_barMap
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one] at hLM
  have hLM0 : (barTensorLeftDiff MM C N' - barTensorMidDiff AA.grading BB MM.grading C N') ∘ₗ
        H_raw +
      H_raw ∘ₗ (barTensorLeftDiff MM C N - barTensorMidDiff AA.grading BB MM.grading C N) = 0 := by
    rw [hLM]; module
  simp only [LinearMap.sub_comp, LinearMap.comp_sub] at hLM0
  have hraw : G₁_raw - G₂_raw =
      barTensorRawDifferential MM NN' ∘ₗ H_raw + H_raw ∘ₗ barTensorRawDifferential MM NN := by
    rw [barTensorRawDifferential_def, barTensorRawDifferential_def, LinearMap.sub_comp,
      LinearMap.add_comp, LinearMap.comp_sub, LinearMap.comp_add]
    calc
      G₁_raw - G₂_raw = 0 + (barTensorRightDiff AA.grading MM.grading NN' ∘ₗ H_raw +
          H_raw ∘ₗ barTensorRightDiff AA.grading MM.grading NN) := by rw [zero_add, hR]
      _ = _ := by rw [← hLM0]; abel
  rw [barTensorProduct_barDifferential, barTensorProduct_barDifferential]
  have hΦ2 : Φ ∘ₗ Φ = LinearMap.id :=
    barTensorSignTwist_comp_self (R := R) (A := A) (B := B) (M := M) CC.grading NN.grading
  have hΦ'2 : Φ' ∘ₗ Φ' = LinearMap.id :=
    barTensorSignTwist_comp_self (R := R) (A := A) (B := B) (M := M) CC.grading NN'.grading
  change Φ' ∘ₗ G₁_raw ∘ₗ Φ - Φ' ∘ₗ G₂_raw ∘ₗ Φ =
    barTensorDifferential MM NN' ∘ₗ (Φ' ∘ₗ H_raw ∘ₗ Φ) +
      (Φ' ∘ₗ H_raw ∘ₗ Φ) ∘ₗ barTensorDifferential MM NN
  calc
    Φ' ∘ₗ G₁_raw ∘ₗ Φ - Φ' ∘ₗ G₂_raw ∘ₗ Φ
      = Φ' ∘ₗ (G₁_raw - G₂_raw) ∘ₗ Φ := by
        simp only [LinearMap.sub_comp, LinearMap.comp_sub]
    _ = Φ' ∘ₗ (barTensorRawDifferential MM NN' ∘ₗ H_raw +
          H_raw ∘ₗ barTensorRawDifferential MM NN) ∘ₗ Φ := by rw [hraw]
    _ = Φ' ∘ₗ (barTensorRawDifferential MM NN' ∘ₗ (Φ' ∘ₗ Φ') ∘ₗ H_raw) ∘ₗ Φ +
          Φ' ∘ₗ (H_raw ∘ₗ (Φ ∘ₗ Φ) ∘ₗ barTensorRawDifferential MM NN) ∘ₗ Φ := by
        rw [hΦ'2, hΦ2]
        simp only [LinearMap.id_comp, LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_assoc]
    _ = barTensorDifferential MM NN' ∘ₗ (Φ' ∘ₗ H_raw ∘ₗ Φ) +
          (Φ' ∘ₗ H_raw ∘ₗ Φ) ∘ₗ barTensorDifferential MM NN := by
        simp only [barTensorDifferential_def, Φ, Φ', LinearMap.comp_assoc]

/-- Extend a bimodule homotopy in the right argument of `barTensorProduct`. -/
noncomputable def Homotopy.barTensorRight (MM : AInfinityBimodule AA BB M)
    {g₁ g₂ : AInfinityBimoduleHom NN NN'} (h : Homotopy g₁ g₂) :
    Homotopy (AInfinityBimoduleHom.barTensorRight MM g₁)
      (AInfinityBimoduleHom.barTensorRight MM g₂) where
  barHomotopy := barTensorRightComoduleHom (AA := AA) (CC := CC)
    MM.grading NN.grading NN'.grading (-1) h.barHomotopy
  leftCoact_comp_barMap :=
    leftCoactRTensor_comp_barTensorRightMap (AA := AA) (CC := CC)
      MM.grading NN.grading NN'.grading (-1) h.barMap
  isHomogeneous_barHomotopy := by
    rw [barTensorProduct_grading, barTensorProduct_grading]
    exact isHomogeneous_barTensorRightMap (AA := AA) (BB := BB) (CC := CC)
      MM.grading NN.grading NN'.grading h.isHomogeneous_barHomotopy
  barMap_sub_barMap := barMap_sub_barMap_barTensorRight MM h

/-- Combine homotopies in both arguments of `barTensorProduct`. -/
noncomputable def Homotopy.barTensorMap {f₁ f₂ : AInfinityBimoduleHom MM MM'}
    {g₁ g₂ : AInfinityBimoduleHom NN NN'} (hf : Homotopy f₁ f₂) (hg : Homotopy g₁ g₂) :
    Homotopy (AInfinityBimoduleHom.barTensorMap f₁ g₁)
      (AInfinityBimoduleHom.barTensorMap f₂ g₂) :=
  ((hf.barTensorLeft NN').compLeft (AInfinityBimoduleHom.barTensorRight MM g₁)).trans
    ((hg.barTensorRight MM).compRight (AInfinityBimoduleHom.barTensorLeft NN' f₂))

/-- Homotopic left bimodule morphisms induce the same cohomology map on `barTensorProduct`. -/
theorem cohomologyMap_barTensorLeft_eq (NN : AInfinityBimodule BB CC N)
    {f g : AInfinityBimoduleHom MM MM'} (h : Homotopy f g) :
    (barTensorLeft NN f).cohomologyMap = (barTensorLeft NN g).cohomologyMap :=
  (h.barTensorLeft NN).cohomologyMap_eq

/-- Homotopic right bimodule morphisms induce the same cohomology map on `barTensorProduct`. -/
theorem cohomologyMap_barTensorRight_eq (MM : AInfinityBimodule AA BB M)
    {g₁ g₂ : AInfinityBimoduleHom NN NN'} (h : Homotopy g₁ g₂) :
    (barTensorRight MM g₁).cohomologyMap = (barTensorRight MM g₂).cohomologyMap :=
  (h.barTensorRight MM).cohomologyMap_eq

/-- Homotopic left bimodule morphisms are quasi-isomorphisms on `barTensorProduct` together. -/
theorem isQuasiIso_barTensorLeft_iff (NN : AInfinityBimodule BB CC N)
    {f g : AInfinityBimoduleHom MM MM'} (h : Homotopy f g) :
    (barTensorLeft NN f).IsQuasiIso ↔ (barTensorLeft NN g).IsQuasiIso :=
  (h.barTensorLeft NN).isQuasiIso_iff

/-- Homotopic right bimodule morphisms are quasi-isomorphisms on `barTensorProduct` together. -/
theorem isQuasiIso_barTensorRight_iff (MM : AInfinityBimodule AA BB M)
    {g₁ g₂ : AInfinityBimoduleHom NN NN'} (h : Homotopy g₁ g₂) :
    (barTensorRight MM g₁).IsQuasiIso ↔ (barTensorRight MM g₂).IsQuasiIso :=
  (h.barTensorRight MM).isQuasiIso_iff

end HomotopyFunctor

end TauCeti.AInfinityBimoduleHom
