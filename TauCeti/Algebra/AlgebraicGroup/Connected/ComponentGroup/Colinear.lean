/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Unital colinear maps from the identity component

Let `H` be a finite-type commutative Hopf algebra over an algebraically closed field `k`, with
identity-component quotient `identityComponent H` via `identityComponentCoordinateMap H`. Right
multiplication on `H` by the canonical idempotent `e_1` of the identity component vanishes on the
identity-component Hopf ideal and therefore descends to a `k`-linear section
`identityComponentIdempotentSection H : identityComponent H →ₗ[k] H` that is left
`(identityComponent H)`-colinear (`rTensor_comul_identityComponentIdempotentSection`).

Translating `e_1` by rational coset representatives of `π₀(Spec H)` permutes the component
idempotents, whose sum is `1`. Summing the corresponding right translates of
`identityComponentIdempotentSection H` therefore yields a unital left
`(identityComponent H)`-colinear `k`-linear map `identityComponent H →ₗ[k] H`
(`exists_unital_colinear`), without any reducedness or linear-reductivity assumption.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.comul_connectedComponentsIdempotent_one`: comultiplication of
  the identity-component idempotent as `∑ C, e_C ⊗ e_{C⁻¹}`.
* `TauCeti.FiniteTypeCommHopfAlgCat.rightTranslationAlgHom_connectedComponentsIdempotent_one`: right
  translation of `e_1` by a point of component `C⁻¹` is `e_C`.
* `TauCeti.FiniteTypeCommHopfAlgCat.identityComponentIdempotentSection`: the `k`-linear section
  `identityComponent H →ₗ[k] H` induced by right multiplication by `e_1`.
* `TauCeti.FiniteTypeCommHopfAlgCat.rTensor_comul_identityComponentIdempotentSection`: left
  `(identityComponent H)`-colinearity of `identityComponentIdempotentSection H`.
* `TauCeti.FiniteTypeCommHopfAlgCat.exists_unital_colinear`: existence of a unital left
  `(identityComponent H)`-colinear `k`-linear map `identityComponent H →ₗ[k] H`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 12.l.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.
-/

public section

open scoped TensorProduct
open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The coordinate projection onto `identityComponent H` is surjective. -/
theorem identityComponentCoordinateMap_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Surjective ⇑(toBialgHom (identityComponentCoordinateMap H)) := by
  rw [identityComponentCoordinateMap_def]
  exact mkQuotient_surjective H _

/-- The canonical idempotent of the identity component maps to `1` under
`identityComponentCoordinateMap H`. -/
@[simp]
theorem toBialgHom_identityComponentCoordinateMap_connectedComponentsIdempotent_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    toBialgHom (identityComponentCoordinateMap H)
        (PrimeSpectrum.connectedComponentsIdempotent
          (1 : ConnectedComponents (PrimeSpectrum H))) = 1 := by
  have hmk : Ideal.Quotient.mk
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal
      (PrimeSpectrum.connectedComponentIdempotent
        (Bialgebra.augmentationPoint k H : PrimeSpectrum H)) = 1 := by
    let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
    let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
      HopfAlgebra.identityComponentHopfIdeal_toIdeal, ← Ideal.Quotient.eq, map_one]
    exact PrimeSpectrum.quotientMk_connectedComponentIdempotent_eq_one _
  rw [identityComponentCoordinateMap_def, mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk,
    connectedComponentsIdempotent_one H]
  exact hmk

/-- Comultiplication of the identity-component idempotent splits across opposite components as
`∑ C, e_C ⊗ e_{C⁻¹}`. -/
theorem comul_connectedComponentsIdempotent_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Fintype (ConnectedComponents (PrimeSpectrum H))] :
    Coalgebra.comul (R := k)
        (PrimeSpectrum.connectedComponentsIdempotent
          (1 : ConnectedComponents (PrimeSpectrum H))) =
      ∑ C : ConnectedComponents (PrimeSpectrum H),
        PrimeSpectrum.connectedComponentsIdempotent C ⊗ₜ[k]
          PrimeSpectrum.connectedComponentsIdempotent C⁻¹ := by
  let ι := componentCoordinateBialgHom H
  have hmap := (CoalgHomClass.map_comp_comul_apply ι
    (ConstantGroup.delta k (ConnectedComponents (PrimeSpectrum H)) 1)).symm
  rw [← componentCoordinateMap_delta H 1, ← componentCoordinateBialgHom_apply H, hmap,
    ConstantGroup.comul_delta, map_sum]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [mul_one, TensorProduct.map_tmul]
  simp only [ι, LinearMap.coe_ofClass]
  rw [componentCoordinateBialgHom_apply, componentCoordinateBialgHom_apply,
    componentCoordinateMap_delta, componentCoordinateMap_delta]

/-- Right translation of the identity-component idempotent by a rational point in component `C⁻¹`
gives the idempotent of component `C`. -/
theorem rightTranslationAlgHom_connectedComponentsIdempotent_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (u : WithConv (H →ₐ[k] k)) {C : ConnectedComponents (PrimeSpectrum H)}
    (hu : rationalComponentMap H u = C⁻¹) :
    HopfAlgebra.rightTranslationAlgHom u
        (PrimeSpectrum.connectedComponentsIdempotent
          (1 : ConnectedComponents (PrimeSpectrum H))) =
      PrimeSpectrum.connectedComponentsIdempotent C := by
  classical
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  have heval (D : ConnectedComponents (PrimeSpectrum H)) :
      u.ofConv (PrimeSpectrum.connectedComponentsIdempotent D⁻¹) =
        if D = C then 1 else 0 := by
    have h := AlgHom.congr_fun (eval_componentCoordinateMap H u)
      (ConstantGroup.delta k (ConnectedComponents (PrimeSpectrum H)) D⁻¹)
    rw [AlgHom.comp_apply, componentCoordinateMap_delta, hu, ConstantGroup.eval_apply,
      ConstantGroup.functionAlgEquiv_delta, Pi.single_apply] at h
    simpa [inv_inj, eq_comm] using h
  rw [HopfAlgebra.rightTranslationAlgHom_apply, comul_connectedComponentsIdempotent_one H,
    map_sum, map_sum, Finset.sum_eq_single C]
  · simp [heval C]
  · intro D _ hDC
    simp [heval D, hDC]
  · simp

private theorem mulRight_connectedComponentsIdempotent_one_mem_ker
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {x : H}
    (hx : x ∈ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal) :
    x ∈ LinearMap.ker
      (LinearMap.mulRight H
        (PrimeSpectrum.connectedComponentsIdempotent
          (1 : ConnectedComponents (PrimeSpectrum H)))) := by
  rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal_eq_span,
    ← connectedComponentsIdempotent_one H, Ideal.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  have hidem : IsIdempotentElem
      (PrimeSpectrum.connectedComponentsIdempotent
        (1 : ConnectedComponents (PrimeSpectrum H))) :=
    PrimeSpectrum.isIdempotentElem_connectedComponentsIdempotent _
  rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_right_comm, sub_mul, one_mul,
    hidem.eq, sub_self, zero_mul]

/-- Right multiplication by the identity-component idempotent descends from `H` to a `k`-linear
section `identityComponent H →ₗ[k] H` of `identityComponentCoordinateMap H`. -/
noncomputable def identityComponentIdempotentSection
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    identityComponent H →ₗ[k] H :=
  (((HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal.liftQ
    (LinearMap.mulRight H
      (PrimeSpectrum.connectedComponentsIdempotent
        (1 : ConnectedComponents (PrimeSpectrum H))))
    (fun _ hx ↦ mulRight_connectedComponentsIdempotent_one_mem_ker H hx)).restrictScalars k)

/-- On quotient classes, `identityComponentIdempotentSection H` multiplies on the right by the
idempotent of the identity component. -/
@[simp]
theorem identityComponentIdempotentSection_mk
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (a : H) :
    identityComponentIdempotentSection H
        (toBialgHom (identityComponentCoordinateMap H) a) =
      a * PrimeSpectrum.connectedComponentsIdempotent
        (1 : ConnectedComponents (PrimeSpectrum H)) := by
  rw [identityComponentCoordinateMap_def, mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk,
    ← Ideal.Quotient.mk_eq_mk, identityComponentIdempotentSection,
    LinearMap.restrictScalars_apply, Submodule.liftQ_apply, LinearMap.mulRight_apply]

/-- `identityComponentIdempotentSection H` is a right inverse to the coordinate projection onto
`identityComponent H`. -/
@[simp]
theorem toBialgHom_identityComponentCoordinateMap_identityComponentIdempotentSection
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (x : identityComponent H) :
    toBialgHom (identityComponentCoordinateMap H)
        (identityComponentIdempotentSection H x) = x := by
  obtain ⟨a, rfl⟩ := identityComponentCoordinateMap_surjective H x
  rw [identityComponentIdempotentSection_mk, map_mul,
    toBialgHom_identityComponentCoordinateMap_connectedComponentsIdempotent_one, mul_one]

private theorem rTensor_identityComponentCoordinateMap_comul_idempotent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (((toBialgHom (identityComponentCoordinateMap H)).toCoalgHom :
        H →ₗ[k] identityComponent H).rTensor H)
      (Coalgebra.comul (R := k)
        (PrimeSpectrum.connectedComponentsIdempotent
          (1 : ConnectedComponents (PrimeSpectrum H)))) =
      (1 : identityComponent H) ⊗ₜ[k]
        PrimeSpectrum.connectedComponentsIdempotent
          (1 : ConnectedComponents (PrimeSpectrum H)) := by
  classical
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  let q := toBialgHom (identityComponentCoordinateMap H)
  let e := PrimeSpectrum.connectedComponentsIdempotent (R := H)
  have hqne {C : ConnectedComponents (PrimeSpectrum H)} (hC : C ≠ 1) : q (e C) = 0 := by
    have hortho : e C * e 1 = 0 :=
      PrimeSpectrum.orthogonalIdempotents_connectedComponentsIdempotent.ortho hC
    calc
      q (e C) = q (e C) * q (e 1) := by
        rw [toBialgHom_identityComponentCoordinateMap_connectedComponentsIdempotent_one, mul_one]
      _ = q (e C * e 1) := (map_mul q _ _).symm
      _ = 0 := by rw [hortho, map_zero]
  rw [comul_connectedComponentsIdempotent_one H, map_sum, Finset.sum_eq_single 1]
  · rw [inv_one, LinearMap.rTensor_tmul, LinearMap.coe_ofClass, BialgHom.toCoalgHom_apply,
      toBialgHom_identityComponentCoordinateMap_connectedComponentsIdempotent_one]
  · intro C _ hC
    rw [LinearMap.rTensor_tmul, LinearMap.coe_ofClass, BialgHom.toCoalgHom_apply,
      hqne hC, TensorProduct.zero_tmul]
  · simp

/-- `identityComponentIdempotentSection H` is left `(identityComponent H)`-colinear along
`identityComponentCoordinateMap H`. -/
theorem rTensor_comul_identityComponentIdempotentSection
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (x : identityComponent H) :
    (((toBialgHom (identityComponentCoordinateMap H)).toCoalgHom :
        H →ₗ[k] identityComponent H).rTensor H)
      (Coalgebra.comul (R := k) (identityComponentIdempotentSection H x)) =
      (identityComponentIdempotentSection H).lTensor (identityComponent H)
        (Coalgebra.comul (R := k) x) := by
  let q := toBialgHom (identityComponentCoordinateMap H)
  let qLin : H →ₗ[k] identityComponent H := q.toCoalgHom
  let e₁ := PrimeSpectrum.connectedComponentsIdempotent
    (1 : ConnectedComponents (PrimeSpectrum H))
  obtain ⟨a, rfl⟩ := identityComponentCoordinateMap_surjective H x
  rw [identityComponentIdempotentSection_mk]
  let Φ : H →ₐ[k] identityComponent H ⊗[k] H :=
    (Algebra.TensorProduct.map q.toAlgHom (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H)
  have hΦ (b : H) : Φ b = (qLin.rTensor H) (Coalgebra.comul (R := k) b) := by
    simp only [Φ, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, LinearMap.rTensor_def]
    induction Coalgebra.comul (R := k) b using TensorProduct.inductionOn with
    | tmul u v => rfl
    | add u v hu hv => simp [hu, hv]
  have hmul (w : identityComponent H ⊗[k] H) :
      w * ((1 : identityComponent H) ⊗ₜ[k] e₁) =
        (LinearMap.mulRight k e₁).lTensor (identityComponent H) w := by
    induction w using TensorProduct.inductionOn with
    | tmul u v => simp
    | add u v hu hv => simp [add_mul, hu, hv]
  calc
    (qLin.rTensor H) (Coalgebra.comul (R := k) (a * e₁)) = Φ a * Φ e₁ := by
      rw [← hΦ, map_mul]
    _ = (LinearMap.mulRight k e₁).lTensor (identityComponent H)
          ((qLin.rTensor H) (Coalgebra.comul (R := k) a)) := by
      rw [hΦ e₁, rTensor_identityComponentCoordinateMap_comul_idempotent H, hmul, hΦ a]
    _ = (identityComponentIdempotentSection H).lTensor (identityComponent H)
          (Coalgebra.comul (R := k) (q a)) := by
      rw [← CoalgHomClass.map_comp_comul_apply q a]
      induction Coalgebra.comul (R := k) a using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [q, qLin, e₁, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
          TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.coe_ofClass]
        rw [BialgHom.toCoalgHom_apply, identityComponentIdempotentSection_mk]
      | add u v hu hv => simp only [map_add, hu, hv]

private theorem sum_rightTranslationAlgHom_identityComponentIdempotentSection_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Fintype (ConnectedComponents (PrimeSpectrum H))] :
    (∑ C : ConnectedComponents (PrimeSpectrum H),
        (HopfAlgebra.rightTranslationAlgHom (componentRepresentative H C)⁻¹).toLinearMap ∘ₗ
          identityComponentIdempotentSection H) 1 = 1 := by
  have hmk1 : identityComponentIdempotentSection H 1 =
      PrimeSpectrum.connectedComponentsIdempotent
        (1 : ConnectedComponents (PrimeSpectrum H)) := by
    simpa only [map_one, one_mul] using identityComponentIdempotentSection_mk H 1
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, hmk1, AlgHom.toLinearMap_apply]
  have hterm (C : ConnectedComponents (PrimeSpectrum H)) :
      HopfAlgebra.rightTranslationAlgHom (componentRepresentative H C)⁻¹
          (PrimeSpectrum.connectedComponentsIdempotent
            (1 : ConnectedComponents (PrimeSpectrum H))) =
        PrimeSpectrum.connectedComponentsIdempotent C :=
    rightTranslationAlgHom_connectedComponentsIdempotent_one H (componentRepresentative H C)⁻¹
      (by rw [map_inv, rationalComponentMap_componentRepresentative])
  simp_rw [hterm]
  exact PrimeSpectrum.completeOrthogonalIdempotents_connectedComponentsIdempotent.complete

/-- Over an algebraically closed field, there exists a unital left `(identityComponent H)`-colinear
`k`-linear map `identityComponent H →ₗ[k] H`. -/
theorem exists_unital_colinear (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ∃ σ : identityComponent H →ₗ[k] H,
      σ 1 = 1 ∧
      ∀ x : identityComponent H,
        (((toBialgHom (identityComponentCoordinateMap H)).toCoalgHom :
            H →ₗ[k] identityComponent H).rTensor H)
          (Coalgebra.comul (R := k) (σ x)) =
          σ.lTensor (identityComponent H) (Coalgebra.comul (R := k) x) := by
  classical
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  let H₀ := identityComponent H
  let q : H →ₗ[k] H₀ := (toBialgHom (identityComponentCoordinateMap H)).toCoalgHom
  let f (C : ConnectedComponents (PrimeSpectrum H)) : H₀ →ₗ[k] H :=
    (HopfAlgebra.rightTranslationAlgHom (componentRepresentative H C)⁻¹).toLinearMap ∘ₗ
      identityComponentIdempotentSection H
  let σ : H₀ →ₗ[k] H := ∑ C : ConnectedComponents (PrimeSpectrum H), f C
  refine ⟨σ, sum_rightTranslationAlgHom_identityComponentIdempotentSection_one H, fun x ↦ ?_⟩
  have hlsum : σ.lTensor H₀ (Coalgebra.comul (R := k) x) =
      ∑ C : ConnectedComponents (PrimeSpectrum H),
        (f C).lTensor H₀ (Coalgebra.comul (R := k) x) := by
    simpa only [LinearMap.coe_lTensorHom, LinearMap.sum_apply] using
      LinearMap.congr_fun
        (map_sum (LinearMap.lTensorHom H₀) f Finset.univ) (Coalgebra.comul (R := k) x)
  rw [LinearMap.sum_apply, map_sum, map_sum, hlsum]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  let τ := (HopfAlgebra.rightTranslationAlgHom (componentRepresentative H C)⁻¹).toLinearMap
  calc
    (q.rTensor H)
          (Coalgebra.comul (R := k)
            (HopfAlgebra.rightTranslationAlgHom (componentRepresentative H C)⁻¹
              (identityComponentIdempotentSection H x))) =
        (q.rTensor H)
          (τ.lTensor H (Coalgebra.comul (R := k) (identityComponentIdempotentSection H x))) := by
      rw [HopfAlgebra.comul_rightTranslationAlgHom]
    _ = τ.lTensor H₀
          ((q.rTensor H)
            (Coalgebra.comul (R := k) (identityComponentIdempotentSection H x))) := by
      rw [LinearMap.lTensor_rTensor_comm]
    _ = (f C).lTensor H₀ (Coalgebra.comul (R := k) x) := by
      rw [rTensor_comul_identityComponentIdempotentSection H x,
        LinearMap.lTensor_comp, LinearMap.comp_apply]

end TauCeti.FiniteTypeCommHopfAlgCat
