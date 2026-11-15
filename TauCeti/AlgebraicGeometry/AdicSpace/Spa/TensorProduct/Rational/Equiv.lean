/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Map
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Topological ring isomorphism for completed tensor products of rational localisations

For Huber pairs `(A, A⁺)`, `(B, B⁺)` and `(C, C⁺)` with adic structure maps from `A`, rational
subsets `W = R(T_A/s_A)`, `U = R(T_B/s_B)` and `V = R(T_C/s_C)` mapping into `W`, and a rational
presentation `d = (T_D, s_D)` of `p_B⁻¹(U) ∩ p_C⁻¹(V)` in `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`, we build
`Pair.completedTensorRationalEquiv : O_B(U) ⊗̂_{O_A(W)} O_C(V) ≃+* O_D(d)`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2(2).
-/

public section

open TensorProduct
open UniformSpace (Completion)

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

/-- Install localization topological-ring instances in a term. -/
local macro "withEquivLocRing " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg
    " => " body:term : term =>
  `(letI := locUniformSpace $P $T $s $L $h; letI := isUniformAddGroup_locUniformSpace $P $T $s $L $h
    letI := isTopologicalRing_locUniformSpace $P $T $s $L $h; $body)

/-- Install localization Huber-ring instances in a term. -/
local macro "withEquivLocHuber " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg
    " => " body:term : term =>
  `(withEquivLocRing $P $T $s $L $h => letI := isHuberRing_completion_locTopology $P $T $s $L $h
    $body)

/-- Register localization Huber-ring instances in tactic mode. -/
local macro "eqv_loc_huber " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg : tactic =>
  `(tactic| (
    let _ := locUniformSpace $P $T $s $L $h
    have _ := isUniformAddGroup_locUniformSpace $P $T $s $L $h
    have _ := isTopologicalRing_locUniformSpace $P $T $s $L $h
    have _ := isHuberRing_completion_locTopology $P $T $s $L $h))

/-- Induced `Completion LA →+* Completion L` map from `h`. -/
local macro:max "eqvHomAL " R:term:arg P:term:arg S:term:arg T:term:arg s:term:arg L:term:arg
    hd:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `(ringHomOfMapsToRationalSubset $(i `PA) ($(i `SA)).plus $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
      $P ($S).plus ($S).isRingOfIntegralElements.isPowerBounded_of_mem $T $s $L $hd
      (inferInstance : IsAdicHom (algebraMap $(i `A) $R)).continuous.continuousAt $h)

/-- Induced `Algebra (Completion LA) (Completion L)` structure from `h`. -/
local macro "eqvAlg " R:term:arg P:term:arg S:term:arg T:term:arg s:term:arg L:term:arg
    hd:term:arg h:term:arg : term =>
  `((eqvHomAL $R $P $S $T $s $L $hd $h).toAlgebra)

/-- Adicness of `algebraMap (Completion LA) (Completion L)` from `h`. -/
local macro "eqvAdic " R:term:arg P:term:arg S:term:arg T:term:arg s:term:arg L:term:arg
    hd:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `((isAdicHom_ringHomOfMapsToRationalSubset $(i `PA) ($(i `SA)).plus $(i `TA) $(i `sA) $(i `LA)
      $(i `hdenA) $P ($S).plus ($S).isRingOfIntegralElements.isPowerBounded_of_mem $T $s $L $hd
      (inferInstance : IsAdicHom (algebraMap $(i `A) $R)) $h :
      IsAdicHom (algebraMap (Completion $(i `LA)) (Completion $L))))

/-- Install the induced `Completion LA`-algebra and adicness instances in a term. -/
local macro "withEquivAlg " hf:term:arg hg:term:arg " => " body:term : term =>
  let i := Lean.mkIdent
  `(letI := eqvAlg $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    letI := eqvAlg $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    haveI := eqvAdic $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    haveI := eqvAdic $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    $body)

/-- Install the three-factor completed-tensor localization Huber-ring instances in a term. -/
local macro "withEquivHuber3 " hf:term:arg hg:term:arg " => " body:term : term =>
  let i := Lean.mkIdent
  `(withEquivLocRing $(i `PA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA) =>
    withEquivLocHuber $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) =>
    withEquivLocHuber $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) =>
    withEquivAlg $hf $hg => $body)

/-- Install the four-factor completed-tensor localization topological-ring instances in a term. -/
local macro "withEquivRing4 " hf:term:arg hg:term:arg " => " body:term : term =>
  let i := Lean.mkIdent
  `(withEquivLocRing $(i `PA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA) =>
    withEquivLocRing $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) =>
    withEquivLocRing $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) =>
    withEquivAlg $hf $hg =>
    withEquivLocRing $(i `PD) $(i `TD) $(i `sD) $(i `LD) $(i `hdenD) => $body)

/-- Register three-factor completed-tensor localization instances in tactic mode. -/
local macro "equiv_tensor_inst3 " hf:term:arg hg:term:arg : tactic =>
  let i := Lean.mkIdent
  `(tactic| (
    eqv_loc_huber $(i `PA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
    eqv_loc_huber $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
    eqv_loc_huber $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC)
    let _ := eqvAlg $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    let _ := eqvAlg $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    have _ := eqvAdic $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    have _ := eqvAdic $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg))

/-- Register four-factor completed-tensor localization instances in tactic mode. -/
local macro "equiv_tensor_inst " hf:term:arg hg:term:arg : tactic =>
  let i := Lean.mkIdent
  `(tactic| (
    equiv_tensor_inst3 $hf $hg
    eqv_loc_huber $(i `PD) $(i `TD) $(i `sD) $(i `LD) $(i `hdenD)))

/-- Apply `f` to the 18 three-factor section variables `PA .. hdenC`. -/
local macro:max "eqvApp18 " f:term:max : term =>
  let i := Lean.mkIdent
  `($f $(i `PA) $(i `SA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
      $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
      $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC))

/-- Apply `f` to the 23 four-factor section variables `PA .. hdenD`. -/
local macro:max "eqvApp23 " f:term:max : term =>
  let i := Lean.mkIdent
  `((eqvApp18 $f) $(i `PD) $(i `TD) $(i `sD) $(i `LD) $(i `hdenD))

private noncomputable def locPairAux {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsHuberRing R] (P : PairOfDefinition R) (SR : Pair R)
    (T : Finset R) (s : R) (L : Type*) [CommRing L] [Algebra R L]
    [IsLocalization.Away s L] (hden : HasDenominatorPower P T s L) :
    withEquivLocHuber P T s L hden => Pair (Completion L) :=
  withEquivLocHuber P T s L hden =>
  ⟨completedPlusSubring P SR.plus T s L hden,
    isRingOfIntegralElements_completedPlusSubring P SR.plus
      (fun _ hj ↦ SR.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
        (P.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
      SR.isRingOfIntegralElements.isPowerBounded_of_mem T s L hden⟩

private noncomputable def locPairHomAux {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsHuberRing R] (P : PairOfDefinition R) (SR : Pair R)
    (T : Finset R) (s : R) (L : Type*) [CommRing L] [Algebra R L]
    [IsLocalization.Away s L] (hden : HasDenominatorPower P T s L) :
    withEquivLocHuber P T s L hden => Pair.Hom SR (locPairAux P SR T s L hden) :=
  withEquivLocHuber P T s L hden =>
  ⟨toCompletionLoc P T s L hden, continuous_toCompletionLoc P T s L hden,
    fun _ hr ↦ toCompletionLoc_mem_completedPlusSubring P SR.plus T s L hden hr⟩

private noncomputable def factorToRationalLocHomAux {R D : Type*}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]
    [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    (PR : PairOfDefinition R) (SR : Pair R) (TR : Finset R) (sR : R) (LR : Type*) [CommRing LR]
    [Algebra R LR] [IsLocalization.Away sR LR] (hdenR : HasDenominatorPower PR TR sR LR)
    (PD : PairOfDefinition D) (SD : Pair D) (TD : Finset D) (sD : D) (LD : Type*) [CommRing LD]
    [Algebra D LD] [IsLocalization.Away sD LD] (hdenD : HasDenominatorPower PD TD sD LD)
    {ι : R →+* D} (hι : ContinuousAt ι 0)
    (hsub : Set.MapsTo (comap ι) (rationalSubset SD.plus TD sD) (rationalSubset SR.plus TR sR)) :
    withEquivLocHuber PR TR sR LR hdenR => withEquivLocHuber PD TD sD LD hdenD =>
      Pair.Hom (locPairAux PR SR TR sR LR hdenR) (locPairAux PD SD TD sD LD hdenD) :=
  withEquivLocHuber PR TR sR LR hdenR => withEquivLocHuber PD TD sD LD hdenD =>
  let hpb := SD.isRingOfIntegralElements.isPowerBounded_of_mem
  ⟨ringHomOfMapsToRationalSubset PR SR.plus TR sR LR hdenR PD SD.plus hpb TD sD LD hdenD hι hsub,
    continuous_ringHomOfMapsToRationalSubset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    fun x hx ↦ ringHomOfMapsToRationalSubset_mem_completedPlusSubring PR SR.plus TR sR LR hdenR
      PD SD.plus (fun _ hj ↦ SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
        (PD.isTopologicallyNilpotent_of_mem_idealOfDefinition hj)) hpb TD sD LD hdenD hι hsub x hx⟩

section RationalEquiv

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- Abbreviate the intersection presentation hypothesis on `(TD, sD)`. -/
local macro "eqvInterEq" : term =>
  let i := Lean.mkIdent
  `(Subtype.val ⁻¹' rationalSubset (($(i `SB)).completedTensor $(i `A) $(i `SC)).plus
        $(i `TD) $(i `sD) =
      ((Pair.completedTensor.inl $(i `A) $(i `SB) $(i `SC)).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset ($(i `SB)).plus $(i `TB) $(i `sB))) ∩
      ((Pair.completedTensor.inr $(i `A) $(i `SB) $(i `SC)).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset ($(i `SC)).plus $(i `TC) $(i `sC))))

/-- If `R(T_D/s_D)` cuts out `p_B⁻¹(U) ∩ p_C⁻¹(V)`, pullback along `inl` maps `R(T_D/s_D)` into
`R(T_B/s_B)`. -/
theorem Pair.completedTensor.mapsTo_inl_of_inter_eq
    {SB : Pair B} {TB : Finset B} {sB : B} {SC : Pair C} {TC : Finset C} {sC : C}
    {TD : Finset (CompletedTensor A B C)} {sD : CompletedTensor A B C} (hd : eqvInterEq) :
    Set.MapsTo (comap (CompletedTensor.inl A B C))
      (rationalSubset (SB.completedTensor A SC).plus TD sD) (rationalSubset SB.plus TB sB) := by
  rw [← Pair.completedTensor.toRingHom_inl (S := SB) (T := SC),
    ← Pair.Hom.mapsTo_spaComap_rationalSubset_iff]
  intro v hv; rw [hd] at hv; exact hv.1

/-- If `R(T_D/s_D)` cuts out `p_B⁻¹(U) ∩ p_C⁻¹(V)`, pullback along `inr` maps `R(T_D/s_D)` into
`R(T_C/s_C)`. -/
theorem Pair.completedTensor.mapsTo_inr_of_inter_eq
    {SB : Pair B} {TB : Finset B} {sB : B} {SC : Pair C} {TC : Finset C} {sC : C}
    {TD : Finset (CompletedTensor A B C)} {sD : CompletedTensor A B C} (hd : eqvInterEq) :
    Set.MapsTo (comap (CompletedTensor.inr A B C))
      (rationalSubset (SB.completedTensor A SC).plus TD sD) (rationalSubset SC.plus TC sC) := by
  rw [← Pair.completedTensor.toRingHom_inr (S := SB) (T := SC),
    ← Pair.Hom.mapsTo_spaComap_rationalSubset_iff]
  intro v hv; rw [hd] at hv; exact hv.2

variable [IsHuberRing A]
  (PA : PairOfDefinition A) (SA : Pair A) (TA : Finset A) (sA : A) (LA : Type*) [CommRing LA]
  [Algebra A LA] [IsLocalization.Away sA LA] (hdenA : HasDenominatorPower PA TA sA LA)
  (PB : PairOfDefinition B) (SB : Pair B) (TB : Finset B) (sB : B) (LB : Type*) [CommRing LB]
  [Algebra B LB] [IsLocalization.Away sB LB] (hdenB : HasDenominatorPower PB TB sB LB)
  (PC : PairOfDefinition C) (SC : Pair C) (TC : Finset C) (sC : C) (LC : Type*) [CommRing LC]
  [Algebra C LC] [IsLocalization.Away sC LC] (hdenC : HasDenominatorPower PC TC sC LC)
  (PD : PairOfDefinition (CompletedTensor A B C))
  (TD : Finset (CompletedTensor A B C)) (sD : CompletedTensor A B C)
  (LD : Type*) [CommRing LD] [Algebra (CompletedTensor A B C) LD]
  [IsLocalization.Away sD LD] (hdenD : HasDenominatorPower PD TD sD LD)

/-- Abbreviate `Set.MapsTo (comap (algebraMap A B)) R(TB/sB) R(TA/sA)`. -/
local macro "eqvMapsAB" : term =>
  let i := Lean.mkIdent
  `(Set.MapsTo (comap (algebraMap $(i `A) $(i `B)))
      (rationalSubset ($(i `SB)).plus $(i `TB) $(i `sB))
      (rationalSubset ($(i `SA)).plus $(i `TA) $(i `sA)))

/-- Abbreviate `Set.MapsTo (comap (algebraMap A C)) R(TC/sC) R(TA/sA)`. -/
local macro "eqvMapsAC" : term =>
  let i := Lean.mkIdent
  `(Set.MapsTo (comap (algebraMap $(i `A) $(i `C)))
      (rationalSubset ($(i `SC)).plus $(i `TC) $(i `sC))
      (rationalSubset ($(i `SA)).plus $(i `TA) $(i `sA)))

private noncomputable def toRationalLocHomAux (hf : eqvMapsAB) (hg : eqvMapsAC) (hd : eqvInterEq) :
    withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
      Pair.Hom ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
          (locPairAux PC SC TC sC LC hdenC))
        (locPairAux PD (SB.completedTensor A SC) TD sD LD hdenD) :=
  withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
  let fL := factorToRationalLocHomAux PB SB TB sB LB hdenB PD (SB.completedTensor A SC) TD sD LD
    hdenD (CompletedTensor.continuous_inl A B C).continuousAt
    (Pair.completedTensor.mapsTo_inl_of_inter_eq hd)
  let fR := factorToRationalLocHomAux PC SC TC sC LC hdenC PD (SB.completedTensor A SC) TD sD LD
    hdenD (CompletedTensor.continuous_inr A B C).continuousAt
    (Pair.completedTensor.mapsTo_inr_of_inter_eq hd)
  Pair.completedTensor.lift fL fR (by
    have hAB := (eqvAdic B PB SB TB sB LB hdenB hf).continuous
    have hAC := (eqvAdic C PC SC TC sC LC hdenC hg).continuous
    refine completion_locTopology_ringHom_ext_of_continuous PA TA sA LA hdenA _ _
      (fL.continuous_toRingHom.comp hAB) (fR.continuous_toRingHom.comp hAC) (RingHom.ext fun a ↦ ?_)
    change fL.toRingHom (eqvHomAL B PB SB TB sB LB hdenB hf (toCompletionLoc PA TA sA LA hdenA a)) =
      fR.toRingHom (eqvHomAL C PC SC TC sC LC hdenC hg (toCompletionLoc PA TA sA LA hdenA a))
    simp only [fL, fR, factorToRationalLocHomAux, toCompletionLoc_apply,
      ringHomOfMapsToRationalSubset_algebraMap_coe, CompletedTensor.inl_algebraMap,
      CompletedTensor.inr_algebraMap])

private noncomputable def baseToTensorLocHomAux (hf : eqvMapsAB) (hg : eqvMapsAC) :
    withEquivHuber3 hf hg =>
      Pair.Hom (SB.completedTensor A SC)
        ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
          (locPairAux PC SC TC sC LC hdenC)) :=
  withEquivHuber3 hf hg =>
  Pair.completedTensor.lift
    ((Pair.completedTensor.inl (Completion LA) (locPairAux PB SB TB sB LB hdenB)
      (locPairAux PC SC TC sC LC hdenC)).comp (locPairHomAux PB SB TB sB LB hdenB))
    ((Pair.completedTensor.inr (Completion LA) (locPairAux PB SB TB sB LB hdenB)
      (locPairAux PC SC TC sC LC hdenC)).comp (locPairHomAux PC SC TC sC LC hdenC))
    (by
      have hB : (toCompletionLoc PB TB sB LB hdenB).comp (algebraMap A B) =
          (algebraMap (Completion LA) (Completion LB)).comp (toCompletionLoc PA TA sA LA hdenA) :=
        (ringHomOfMapsToRationalSubset_comp_toCompletionLoc PA SA.plus TA sA LA hdenA PB SB.plus
          SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
          (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).symm
      have hC : (toCompletionLoc PC TC sC LC hdenC).comp (algebraMap A C) =
          (algebraMap (Completion LA) (Completion LC)).comp (toCompletionLoc PA TA sA LA hdenA) :=
        (ringHomOfMapsToRationalSubset_comp_toCompletionLoc PA SA.plus TA sA LA hdenA PC SC.plus
          SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
          (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).symm
      simp only [Pair.Hom.toRingHom_comp, Pair.completedTensor.toRingHom_inl,
        Pair.completedTensor.toRingHom_inr, locPairHomAux, RingHom.comp_assoc]
      rw [hB, ← RingHom.comp_assoc, CompletedTensor.inl_comp_algebraMap, RingHom.comp_assoc, ← hC])

private theorem baseToTensorLoc_comp_inl_and_inr (hf : eqvMapsAB) (hg : eqvMapsAC) :
    withEquivHuber3 hf hg =>
      (eqvApp18 baseToTensorLocHomAux hf hg).toRingHom.comp (CompletedTensor.inl A B C) =
        (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)).comp
          (toCompletionLoc PB TB sB LB hdenB) ∧
      (eqvApp18 baseToTensorLocHomAux hf hg).toRingHom.comp (CompletedTensor.inr A B C) =
        (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)).comp
          (toCompletionLoc PC TC sC LC hdenC) := by
  equiv_tensor_inst3 hf hg
  refine ⟨?_, ?_⟩ <;> simp [baseToTensorLocHomAux, locPairHomAux]

private theorem baseToTensorLoc_comap_mem_rationalSubset
    (hf : eqvMapsAB) (hg : eqvMapsAC) (hd : eqvInterEq) :
    withEquivHuber3 hf hg =>
      ∀ w ∈ spa ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
          (locPairAux PC SC TC sC LC hdenC)).plus,
        comap (eqvApp18 baseToTensorLocHomAux hf hg).toRingHom w ∈
          rationalSubset (SB.completedTensor A SC).plus TD sD := by
  equiv_tensor_inst3 hf hg; intro w hw
  let OU := locPairAux PB SB TB sB LB hdenB; let OV := locPairAux PC SC TC sC LC hdenC
  obtain ⟨hB, hC⟩ := eqvApp18 baseToTensorLoc_comp_inl_and_inr hf hg
  have hmem : (eqvApp18 baseToTensorLocHomAux hf hg).spaComap ⟨w, hw⟩ ∈
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD := by
    rw [hd]; refine ⟨?_, ?_⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inl A B C)), ← comap_comp, hB,
        comap_comp, Function.comp_apply]
      simpa only [spaComapLoc_val, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl] using
        spaComapLoc_mem_rationalSubset PB SB.plus TB sB LB hdenB
          ⟨_, ((Pair.completedTensor.inl (Completion LA) OU OV).spaComap ⟨w, hw⟩).2⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inr A B C)), ← comap_comp, hC,
        comap_comp, Function.comp_apply]
      simpa only [spaComapLoc_val, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr] using
        spaComapLoc_mem_rationalSubset PC SC.plus TC sC LC hdenC
          ⟨_, ((Pair.completedTensor.inr (Completion LA) OU OV).spaComap ⟨w, hw⟩).2⟩
  simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hmem

private noncomputable def ofRationalLocHomAux (hf : eqvMapsAB) (hg : eqvMapsAC) (hd : eqvInterEq) :
    withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
      Pair.Hom (locPairAux PD (SB.completedTensor A SC) TD sD LD hdenD)
        ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
          (locPairAux PC SC TC sC LC hdenC)) :=
  withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
  let PUV := (locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
    (locPairAux PC SC TC sC LC hdenC)
  let hmem := eqvApp18 baseToTensorLoc_comap_mem_rationalSubset TD sD hf hg hd
  let huniq := existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    PD (SB.completedTensor A SC).plus TD sD LD hdenD PUV.plus PUV.isRingOfIntegralElements
    (eqvApp18 baseToTensorLocHomAux hf hg).continuous_toRingHom.continuousAt hmem
  { toRingHom := huniq.choose, continuous_toRingHom := huniq.choose_spec.1.1
    map_mem_plus := fun z hz ↦ PUV.isRingOfIntegralElements.mem_of_forall_vle_one fun w hw ↦ by
      have hcomap := comap_mem_spa_completedPlusSubring
        PD (SB.completedTensor A SC).plus TD sD LD hdenD huniq.choose huniq.choose_spec.1.1
        ((mem_spa_iff _ _).mp hw).1 (by rw [huniq.choose_spec.1.2]; exact hmem w hw)
      simpa only [comap_vle, map_one] using ((mem_spa_iff _ _).mp hcomap).2 z hz }

private theorem toRationalLocHomAux_and_ofRationalLocHomAux_comp
    (hf : eqvMapsAB) (hg : eqvMapsAC) (hd : eqvInterEq) :
    withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
      ((eqvApp23 toRationalLocHomAux hf hg hd).toRingHom.comp
          (eqvApp23 ofRationalLocHomAux hf hg hd).toRingHom = RingHom.id (Completion LD)) ∧
        ((eqvApp23 ofRationalLocHomAux hf hg hd).toRingHom.comp
          (eqvApp23 toRationalLocHomAux hf hg hd).toRingHom =
          RingHom.id (CompletedTensor (Completion LA) (Completion LB) (Completion LC))) := by
  equiv_tensor_inst hf hg
  let φ := eqvApp23 toRationalLocHomAux hf hg hd; let ψ := eqvApp23 ofRationalLocHomAux hf hg hd
  let δ := eqvApp18 baseToTensorLocHomAux hf hg
  have hψρ : ψ.toRingHom.comp (toCompletionLoc PD TD sD LD hdenD) = δ.toRingHom :=
    (existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset PD
      (SB.completedTensor A SC).plus TD sD LD hdenD _ ((locPairAux PB SB TB sB LB
        hdenB).completedTensor (Completion LA) (locPairAux PC SC TC sC LC
        hdenC)).isRingOfIntegralElements δ.continuous_toRingHom.continuousAt
      (eqvApp18 baseToTensorLoc_comap_mem_rationalSubset TD sD hf hg hd)).choose_spec.1.2
  have hφL : (φ.toRingHom.comp (CompletedTensor.inl _ _ _)).comp
      (toCompletionLoc PB TB sB LB hdenB) =
      (toCompletionLoc PD TD sD LD hdenD).comp (CompletedTensor.inl A B C) := by
    simp [φ, toRationalLocHomAux, factorToRationalLocHomAux]
  have hφR : (φ.toRingHom.comp (CompletedTensor.inr _ _ _)).comp
      (toCompletionLoc PC TC sC LC hdenC) =
      (toCompletionLoc PD TD sD LD hdenD).comp (CompletedTensor.inr A B C) := by
    simp [φ, toRationalLocHomAux, factorToRationalLocHomAux]
  obtain ⟨hδL, hδR⟩ := eqvApp18 baseToTensorLoc_comp_inl_and_inr hf hg; refine ⟨?_, ?_⟩
  · refine eq_id_of_comp_toCompletionLoc_eq_self PD TD sD LD hdenD _
      (φ.continuous_toRingHom.comp ψ.continuous_toRingHom) ?_
    rw [RingHom.comp_assoc, hψρ]
    refine CompletedTensor.hom_ext (φ.continuous_toRingHom.comp δ.continuous_toRingHom)
      (continuous_toCompletionLoc PD TD sD LD hdenD)
      (by rw [RingHom.comp_assoc, hδL, ← RingHom.comp_assoc, hφL])
      (by rw [RingHom.comp_assoc, hδR, ← RingHom.comp_assoc, hφR])
  · have hc := ψ.continuous_toRingHom.comp φ.continuous_toRingHom
    refine CompletedTensor.hom_ext hc continuous_id ?_ ?_
    · refine completion_locTopology_ringHom_ext_of_continuous PB TB sB LB hdenB _ _
        (hc.comp (CompletedTensor.continuous_inl _ _ _))
        (continuous_id.comp (CompletedTensor.continuous_inl _ _ _)) (RingHom.ext fun b ↦ ?_)
      have h1 := RingHom.congr_fun hφL b; have h3 := RingHom.congr_fun hδL b
      have h2 := RingHom.congr_fun hψρ (CompletedTensor.inl A B C b)
      simp only [φ, ψ, δ, RingHom.comp_apply, RingHom.id_apply] at h1 h2 h3 ⊢; rw [h1, h2, h3]
    · refine completion_locTopology_ringHom_ext_of_continuous PC TC sC LC hdenC _ _
        (hc.comp (CompletedTensor.continuous_inr _ _ _))
        (continuous_id.comp (CompletedTensor.continuous_inr _ _ _)) (RingHom.ext fun c ↦ ?_)
      have h1 := RingHom.congr_fun hφR c; have h3 := RingHom.congr_fun hδR c
      have h2 := RingHom.congr_fun hψρ (CompletedTensor.inr A B C c)
      simp only [φ, ψ, δ, RingHom.comp_apply, RingHom.id_apply] at h1 h2 h3 ⊢; rw [h1, h2, h3]

/-- **Completed rational localisation commutes with completed tensor products of Huber pairs.** -/
noncomputable def Pair.completedTensorRationalEquiv (hf : eqvMapsAB) (hg : eqvMapsAC)
    (hd : eqvInterEq) : withEquivRing4 hf hg =>
      CompletedTensor (Completion LA) (Completion LB) (Completion LC) ≃+* Completion LD :=
  withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
  let hcomp := eqvApp23 toRationalLocHomAux_and_ofRationalLocHomAux_comp hf hg hd
  RingEquiv.ofRingHom (eqvApp23 toRationalLocHomAux hf hg hd).toRingHom
    (eqvApp23 ofRationalLocHomAux hf hg hd).toRingHom hcomp.1 hcomp.2

section EquivProps

variable (hf : eqvMapsAB) (hg : eqvMapsAC) (hd : eqvInterEq)

/-- `Pair.completedTensorRationalEquiv` is continuous. -/
@[fun_prop] theorem Pair.continuous_completedTensorRationalEquiv :
    withEquivRing4 hf hg => Continuous (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd) :=
  withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
  (eqvApp23 toRationalLocHomAux hf hg hd).continuous_toRingHom

/-- The inverse of `Pair.completedTensorRationalEquiv` is continuous. -/
@[fun_prop] theorem Pair.continuous_completedTensorRationalEquiv_symm :
    withEquivRing4 hf hg => Continuous (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd).symm :=
  withEquivHuber3 hf hg => withEquivLocHuber PD TD sD LD hdenD =>
  (eqvApp23 ofRationalLocHomAux hf hg hd).continuous_toRingHom

/-- `Pair.completedTensorRationalEquiv` is a homeomorphism. -/
theorem Pair.isHomeomorph_completedTensorRationalEquiv :
    withEquivRing4 hf hg => IsHomeomorph (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd) :=
  withEquivRing4 hf hg =>
  (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd).toEquiv.isHomeomorph_iff.mpr
    ⟨eqvApp23 Pair.continuous_completedTensorRationalEquiv hf hg hd,
      eqvApp23 Pair.continuous_completedTensorRationalEquiv_symm hf hg hd⟩

/-- `Pair.completedTensorRationalEquiv` maps `inl(ρ_B(b))` to `ρ_D(inl(b))`. -/
@[simp] theorem Pair.completedTensorRationalEquiv_inl_toCompletionLoc (b : B) :
    withEquivRing4 hf hg =>
      eqvApp23 Pair.completedTensorRationalEquiv hf hg hd
        (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)
          (algebraMap B LB b : Completion LB)) =
        (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inl A B C b) : Completion LD) := by
  equiv_tensor_inst hf hg; simp only [Pair.completedTensorRationalEquiv, RingEquiv.ofRingHom_apply,
    toRationalLocHomAux, Pair.completedTensor.toRingHom_lift, CompletedTensor.lift_inl,
    factorToRationalLocHomAux, ringHomOfMapsToRationalSubset_algebraMap_coe]

/-- `Pair.completedTensorRationalEquiv` maps `inr(ρ_C(c))` to `ρ_D(inr(c))`. -/
@[simp] theorem Pair.completedTensorRationalEquiv_inr_toCompletionLoc (c : C) :
    withEquivRing4 hf hg =>
      eqvApp23 Pair.completedTensorRationalEquiv hf hg hd
        (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)
          (algebraMap C LC c : Completion LC)) =
        (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inr A B C c) : Completion LD) := by
  equiv_tensor_inst hf hg; simp only [Pair.completedTensorRationalEquiv, RingEquiv.ofRingHom_apply,
    toRationalLocHomAux, Pair.completedTensor.toRingHom_lift, CompletedTensor.lift_inr,
    factorToRationalLocHomAux, ringHomOfMapsToRationalSubset_algebraMap_coe]

/-- The inverse of `Pair.completedTensorRationalEquiv` sends `ρ_D(inl(b))` to `inl(ρ_B(b))`. -/
@[simp] theorem Pair.completedTensorRationalEquiv_symm_toCompletionLoc_inl (b : B) :
    withEquivRing4 hf hg =>
      (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd).symm
          (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inl A B C b) : Completion LD) =
        CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)
          (algebraMap B LB b : Completion LB) :=
  (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd).toEquiv.symm_apply_eq.mpr
    (eqvApp23 Pair.completedTensorRationalEquiv_inl_toCompletionLoc hf hg hd b).symm

/-- The inverse of `Pair.completedTensorRationalEquiv` sends `ρ_D(inr(c))` to `inr(ρ_C(c))`. -/
@[simp] theorem Pair.completedTensorRationalEquiv_symm_toCompletionLoc_inr (c : C) :
    withEquivRing4 hf hg =>
      (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd).symm
          (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inr A B C c) : Completion LD) =
        CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)
          (algebraMap C LC c : Completion LC) :=
  (eqvApp23 Pair.completedTensorRationalEquiv hf hg hd).toEquiv.symm_apply_eq.mpr
    (eqvApp23 Pair.completedTensorRationalEquiv_inr_toCompletionLoc hf hg hd c).symm

/-- **Pure-tensor coefficient formula**: `e(ρ_B(b) ⊗ ρ_C(c)) = ρ_D(b ⊗ c)`. -/
theorem Pair.completedTensorRationalEquiv_toCompletion_tmul (b : B) (c : C) :
    withEquivRing4 hf hg =>
      eqvApp23 Pair.completedTensorRationalEquiv hf hg hd
          (CompletedTensor.toCompletion (Completion LA) (Completion LB) (Completion LC)
            (toCompletionLoc PB TB sB LB hdenB b ⊗ₜ[Completion LA]
              toCompletionLoc PC TC sC LC hdenC c)) =
        toCompletionLoc PD TD sD LD hdenD (CompletedTensor.toCompletion A B C (b ⊗ₜ[A] c)) := by
  equiv_tensor_inst hf hg
  rw [CompletedTensor.toCompletion_tmul, CompletedTensor.toCompletion_tmul, map_mul, map_mul,
    toCompletionLoc_apply, toCompletionLoc_apply,
    Pair.completedTensorRationalEquiv_inl_toCompletionLoc,
    Pair.completedTensorRationalEquiv_inr_toCompletionLoc,
    ← toCompletionLoc_apply PD TD sD LD hdenD, ← toCompletionLoc_apply PD TD sD LD hdenD]

end EquivProps

end RationalEquiv

end TauCeti.Huber

end
