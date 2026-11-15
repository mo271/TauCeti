/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Equiv
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Preimage
public import TauCeti.RingTheory.Huber.TensorProduct.Rational

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Plus

/-!
# Plus-ring comparison and Huber-pair morphisms for completed tensor rational localisations

Continuing `TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Equiv`, we prove that
`Pair.completedTensorRationalEquiv` and `CompletedTensor.completionLocEquiv` carry the completed
tensor plus ring onto `completedPlusSubring`, giving mutually inverse Huber-pair morphisms
`Pair.completedTensor.toRationalLoc` and `Pair.completedTensor.ofRationalLoc`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2(2).
-/

public section

open UniformSpace (Completion)
open scoped Pointwise

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

/-- Install localization topological-ring instances in a term. -/
local macro "withPairLocRing " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg
    " => " body:term : term =>
  `(letI := locUniformSpace $P $T $s $L $h; letI := isUniformAddGroup_locUniformSpace $P $T $s $L $h
    letI := isTopologicalRing_locUniformSpace $P $T $s $L $h; $body)

/-- Install localization Huber-ring instances in a term. -/
local macro "withPairLocHuber " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg
    " => " body:term : term =>
  `(withPairLocRing $P $T $s $L $h => letI := isHuberRing_completion_locTopology $P $T $s $L $h
    $body)

/-- Register localization Huber-ring instances in tactic mode. -/
local macro "pair_loc_huber " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg : tactic =>
  `(tactic| (
    let _ := locUniformSpace $P $T $s $L $h
    have _ := isUniformAddGroup_locUniformSpace $P $T $s $L $h
    have _ := isTopologicalRing_locUniformSpace $P $T $s $L $h
    have _ := isHuberRing_completion_locTopology $P $T $s $L $h))

private theorem map_plus_of_ringEquiv {A B C R : Type*} [CommRing A] [CommRing B] [CommRing C]
    [CommRing R] [Algebra A B] [Algebra A C] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace R] [IsTopologicalRing A] [IsTopologicalRing B]
    [IsTopologicalRing C] [IsTopologicalRing R] [IsHuberRing B] [IsHuberRing C]
    [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (PB : PairOfDefinition B) (SB : Pair B) (hPB : PB.ringOfDefinition ≤ SB.plus) (TB : Finset B)
    (sB : B) (LB : Type*) [CommRing LB] [Algebra B LB] [IsLocalization.Away sB LB]
    (hdenB : HasDenominatorPower PB TB sB LB)
    (PC : PairOfDefinition C) (SC : Pair C) (hPC : PC.ringOfDefinition ≤ SC.plus) (TC : Finset C)
    (sC : C) (LC : Type*) [CommRing LC] [Algebra C LC] [IsLocalization.Away sC LC]
    (hdenC : HasDenominatorPower PC TC sC LC)
    (PD : PairOfDefinition (CompletedTensor A B C)) (TD : Finset (CompletedTensor A B C))
    (sD : CompletedTensor A B C) (LD : Type*) [CommRing LD] [Algebra (CompletedTensor A B C) LD]
    [IsLocalization.Away sD LD] (hdenD : HasDenominatorPower PD TD sD LD) :
    withPairLocHuber PB TB sB LB hdenB => withPairLocHuber PC TC sC LC hdenC =>
    withPairLocRing PD TD sD LD hdenD =>
      ∀ [Algebra R (Completion LB)] [Algebra R (Completion LC)]
        [IsAdicHom (algebraMap R (Completion LB))] [IsAdicHom (algebraMap R (Completion LC))]
        (e : CompletedTensor R (Completion LB) (Completion LC) ≃+* Completion LD),
        Continuous e → Continuous e.symm →
        (∀ b, e (CompletedTensor.inl R _ _ (toCompletionLoc PB TB sB LB hdenB b)) =
          toCompletionLoc PD TD sD LD hdenD (CompletedTensor.inl A B C b)) →
        (∀ c, e (CompletedTensor.inr R _ _ (toCompletionLoc PC TC sC LC hdenC c)) =
          toCompletionLoc PD TD sD LD hdenD (CompletedTensor.inr A B C c)) →
        (Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
          ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
          ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) →
        ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor R
          (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus.map e.toRingHom =
          completedPlusSubring PD (SB.completedTensor A SC).plus TD sD LD hdenD := by
  pair_loc_huber PB TB sB LB hdenB; pair_loc_huber PC TC sC LC hdenC
  pair_loc_huber PD TD sD LD hdenD; intro _ _ _ _ e he he' heL heR hd
  let OU := PB.rationalLocalizationPair SB hPB TB sB LB hdenB
  let OV := PC.rationalLocalizationPair SC hPC TC sC LC hdenC
  let SD := SB.completedTensor A SC; let ODplus := completedPlusSubring PD SD.plus TD sD LD hdenD
  have hSD_nil (j) (hj : j ∈ PD.idealOfDefinition) : (j : CompletedTensor A B C) ∈ SD.plus :=
    SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
      (PD.isTopologicallyNilpotent_of_mem_idealOfDefinition hj)
  have hSD_pb := SD.isRingOfIntegralElements.isPowerBounded_of_mem
  have hOD_ring :=
    isRingOfIntegralElements_completedPlusSubring PD SD.plus hSD_nil hSD_pb TD sD LD hdenD
  have _ := hOD_ring.isIntegrallyClosedIn
  have hOD_closed := ODplus.toAddSubgroup.isClosed_of_isOpen hOD_ring.isOpen
  have hfwd : (OU.completedTensor R OV).plus ≤ ODplus.comap e.toRingHom := by
    refine OU.completedTensor_plus_le_comap OV hOD_closed he (fun u hu ↦ ?_) (fun v hv ↦ ?_)
    · rw [← RingHom.comp_apply e.toRingHom (CompletedTensor.inl R _ _),
        eq_ringHomOfMapsToRationalSubset PB SB.plus TB sB LB hdenB PD SD.plus hSD_pb TD sD LD hdenD
          (CompletedTensor.continuous_inl A B C).continuousAt
          (Pair.completedTensor.mapsTo_inl_of_inter_eq hd) (e.toRingHom.comp (CompletedTensor.inl R
            _ _)) (he.comp (CompletedTensor.continuous_inl _ _ _)) (RingHom.ext heL)]
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring PB SB.plus TB sB LB hdenB
        PD SD.plus hSD_nil hSD_pb TD sD LD hdenD (CompletedTensor.continuous_inl A B C).continuousAt
        (Pair.completedTensor.mapsTo_inl_of_inter_eq hd) u
        (by simpa only [OU, rationalLocalizationPair_plus] using hu)
    · rw [← RingHom.comp_apply e.toRingHom (CompletedTensor.inr R _ _),
        eq_ringHomOfMapsToRationalSubset PC SC.plus TC sC LC hdenC PD SD.plus hSD_pb TD sD LD hdenD
          (CompletedTensor.continuous_inr A B C).continuousAt
          (Pair.completedTensor.mapsTo_inr_of_inter_eq hd) (e.toRingHom.comp (CompletedTensor.inr R
            _ _)) (he.comp (CompletedTensor.continuous_inr _ _ _)) (RingHom.ext heR)]
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring PC SC.plus TC sC LC hdenC
        PD SD.plus hSD_nil hSD_pb TD sD LD hdenD (CompletedTensor.continuous_inr A B C).continuousAt
        (Pair.completedTensor.mapsTo_inr_of_inter_eq hd) v
        (by simpa only [OV, rationalLocalizationPair_plus] using hv)
  let g := e.symm.toRingHom.comp (toCompletionLoc PD TD sD LD hdenD)
  have hg_cont : Continuous g := he'.comp (continuous_toCompletionLoc PD TD sD LD hdenD)
  have hgB : g.comp (CompletedTensor.inl A B C) =
      (CompletedTensor.inl R _ _).comp (toCompletionLoc PB TB sB LB hdenB) :=
    RingHom.ext fun b ↦ e.symm_apply_eq.mpr (heL b).symm
  have hgC : g.comp (CompletedTensor.inr A B C) =
      (CompletedTensor.inr R _ _).comp (toCompletionLoc PC TC sC LC hdenC) :=
    RingHom.ext fun c ↦ e.symm_apply_eq.mpr (heR c).symm
  have _ := (OU.completedTensor R OV).isRingOfIntegralElements.isIntegrallyClosedIn
  have hE_closed := (OU.completedTensor R OV).plus.toAddSubgroup.isClosed_of_isOpen
    (OU.completedTensor R OV).isRingOfIntegralElements.isOpen
  have hg_plus : SD.plus ≤ (OU.completedTensor R OV).plus.comap g := by
    refine SB.completedTensor_plus_le_comap SC hE_closed hg_cont (fun b hb ↦ ?_) (fun c hc ↦ ?_)
    · have hinl := OU.inl_mem_completedTensor_plus (A := R) OV (by
        rw [rationalLocalizationPair_plus]
        exact toCompletionLoc_mem_completedPlusSubring PB SB.plus TB sB LB hdenB hb)
      rwa [← RingHom.comp_apply, ← hgB, RingHom.comp_apply] at hinl
    · have hinr := OU.inr_mem_completedTensor_plus (A := R) OV (by
        rw [rationalLocalizationPair_plus]
        exact toCompletionLoc_mem_completedPlusSubring PC SC.plus TC sC LC hdenC hc)
      rwa [← RingHom.comp_apply, ← hgC, RingHom.comp_apply] at hinr
  ext z; rw [Subring.mem_map]
  refine ⟨fun ⟨x, hx, hxz⟩ ↦ hxz ▸ hfwd hx, fun hz ↦ ⟨e.symm z, ?_, e.apply_symm_apply z⟩⟩
  refine (OU.completedTensor R OV).isRingOfIntegralElements.mem_of_forall_vle_one fun w hw ↦ ?_
  let gHom : Pair.Hom SD (OU.completedTensor R OV) := ⟨g, hg_cont, fun _ hd' ↦ hg_plus hd'⟩
  have hmemD : gHom.spaComap ⟨w, hw⟩ ∈ Subtype.val ⁻¹' rationalSubset SD.plus TD sD := by
    rw [hd]; refine ⟨?_, ?_⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inl A B C)), ← comap_comp,
        hgB, comap_comp, Function.comp_apply]
      simpa only [spaComapLoc_val] using spaComapLoc_mem_rationalSubset PB SB.plus TB sB LB hdenB
        ⟨_, by rw [← rationalLocalizationPair_plus PB SB hPB TB sB LB hdenB]; simpa only
          [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl] using
          ((Pair.completedTensor.inl R OU OV).spaComap ⟨w, hw⟩).2⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inr A B C)), ← comap_comp,
        hgC, comap_comp, Function.comp_apply]
      simpa only [spaComapLoc_val] using spaComapLoc_mem_rationalSubset PC SC.plus TC sC LC hdenC
        ⟨_, by rw [← rationalLocalizationPair_plus PC SC hPC TC sC LC hdenC]; simpa only
          [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr] using
          ((Pair.completedTensor.inr R OU OV).spaComap ⟨w, hw⟩).2⟩
  have hcomap := comap_mem_spa_completedPlusSubring PD SD.plus TD sD LD hdenD e.symm.toRingHom he'
    ((mem_spa_iff _ _).mp hw).1
    (by simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hmemD)
  simpa only [comap_vle, map_one, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
    ((mem_spa_iff _ _).mp hcomap).2 z hz

section RationalPair

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
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

/-- Induced `Algebra (Completion LA) (Completion L)` structure from `h`. -/
local macro "pairAlg " R:term:arg P:term:arg S:term:arg T:term:arg s:term:arg L:term:arg
    hd:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `((ringHomOfMapsToRationalSubset $(i `PA) ($(i `SA)).plus $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
      $P ($S).plus ($S).isRingOfIntegralElements.isPowerBounded_of_mem $T $s $L $hd
      (inferInstance : IsAdicHom (algebraMap $(i `A) $R)).continuous.continuousAt $h).toAlgebra)

/-- Adicness of `algebraMap (Completion LA) (Completion L)` from `h`. -/
local macro "pairAdic " R:term:arg P:term:arg S:term:arg T:term:arg s:term:arg L:term:arg
    hd:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `((isAdicHom_ringHomOfMapsToRationalSubset $(i `PA) ($(i `SA)).plus $(i `TA) $(i `sA) $(i `LA)
      $(i `hdenA) $P ($S).plus ($S).isRingOfIntegralElements.isPowerBounded_of_mem $T $s $L $hd
      (inferInstance : IsAdicHom (algebraMap $(i `A) $R)) $h :
      IsAdicHom (algebraMap (Completion $(i `LA)) (Completion $L))))

/-- Install the three-factor completed-tensor localization instances in a term. -/
local macro "withPairHuber3 " hf:term:arg hg:term:arg " => " body:term : term =>
  let i := Lean.mkIdent
  `(withPairLocRing $(i `PA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA) =>
    withPairLocHuber $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) =>
    withPairLocHuber $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) =>
    letI := pairAlg $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    letI := pairAlg $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    haveI := pairAdic $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    haveI := pairAdic $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    $body)

/-- Register completed-tensor localization instances in tactic mode. -/
local macro "pair_tensor_inst " hf:term:arg hg:term:arg : tactic =>
  let i := Lean.mkIdent
  `(tactic| (
    pair_loc_huber $(i `PA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
    pair_loc_huber $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
    pair_loc_huber $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC)
    let _ := pairAlg $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    let _ := pairAlg $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    have _ := pairAdic $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    have _ := pairAdic $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    pair_loc_huber $(i `PD) $(i `TD) $(i `sD) $(i `LD) $(i `hdenD)))

/-- Apply `f` to the 23 four-factor section variables `PA .. hdenD`. -/
local macro:max "pairApp23 " f:term:max : term =>
  let i := Lean.mkIdent
  `($f $(i `PA) $(i `SA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
      $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
      $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC)
      $(i `PD) $(i `TD) $(i `sD) $(i `LD) $(i `hdenD))

/-- Abbreviate `Set.MapsTo (comap (algebraMap A B)) R(TB/sB) R(TA/sA)`. -/
local macro "pairMapsAB" : term =>
  let i := Lean.mkIdent
  `(Set.MapsTo (comap (algebraMap $(i `A) $(i `B)))
      (rationalSubset ($(i `SB)).plus $(i `TB) $(i `sB))
      (rationalSubset ($(i `SA)).plus $(i `TA) $(i `sA)))

/-- Abbreviate `Set.MapsTo (comap (algebraMap A C)) R(TC/sC) R(TA/sA)`. -/
local macro "pairMapsAC" : term =>
  let i := Lean.mkIdent
  `(Set.MapsTo (comap (algebraMap $(i `A) $(i `C)))
      (rationalSubset ($(i `SC)).plus $(i `TC) $(i `sC))
      (rationalSubset ($(i `SA)).plus $(i `TA) $(i `sA)))

/-- Abbreviate the intersection presentation hypothesis on `(TD, sD)`. -/
local macro "pairInterEq" : term =>
  let i := Lean.mkIdent
  `(Subtype.val ⁻¹' rationalSubset (($(i `SB)).completedTensor $(i `A) $(i `SC)).plus
        $(i `TD) $(i `sD) =
      ((Pair.completedTensor.inl $(i `A) $(i `SB) $(i `SC)).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset ($(i `SB)).plus $(i `TB) $(i `sB))) ∩
      ((Pair.completedTensor.inr $(i `A) $(i `SB) $(i `SC)).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset ($(i `SC)).plus $(i `TC) $(i `sC))))

/-- Abbreviate the completed tensor Huber pair of `O_B(U)` and `O_C(V)` over `O_A(W)`. -/
local macro "pairCtPair " hPB:term:arg hPC:term:arg : term =>
  let i := Lean.mkIdent
  `(((($(i `PB)).rationalLocalizationPair $(i `SB) $hPB $(i `TB) $(i `sB) $(i `LB)
      $(i `hdenB)).completedTensor (Completion $(i `LA))
      (($(i `PC)).rationalLocalizationPair $(i `SC) $hPC $(i `TC) $(i `sC) $(i `LC) $(i `hdenC))))

/-- `Pair.completedTensorRationalEquiv` maps the completed tensor plus ring onto
`completedPlusSubring`. -/
theorem Pair.map_plus_completedTensorRationalEquiv (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus) (hf : pairMapsAB) (hg : pairMapsAC) (hd : pairInterEq) :
    withPairHuber3 hf hg => withPairLocRing PD TD sD LD hdenD =>
      (pairCtPair hPB hPC).plus.map (pairApp23 Pair.completedTensorRationalEquiv hf hg hd :
        CompletedTensor (Completion LA) (Completion LB) (Completion LC) →+* Completion LD) =
        completedPlusSubring PD (SB.completedTensor A SC).plus TD sD LD hdenD := by
  pair_tensor_inst hf hg
  exact map_plus_of_ringEquiv PB SB hPB TB sB LB hdenB PC SC hPC TC sC LC hdenC PD TD sD LD hdenD
    (pairApp23 Pair.completedTensorRationalEquiv hf hg hd)
    (pairApp23 Pair.continuous_completedTensorRationalEquiv hf hg hd)
    (pairApp23 Pair.continuous_completedTensorRationalEquiv_symm hf hg hd)
    (fun b ↦ by simp [toCompletionLoc_apply]) (fun c ↦ by simp [toCompletionLoc_apply]) hd

/-- Membership in the completed tensor plus ring is equivalent to membership of the image under
`Pair.completedTensorRationalEquiv` in `completedPlusSubring`. -/
theorem Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
    (hPB : PB.ringOfDefinition ≤ SB.plus) (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hf : pairMapsAB) (hg : pairMapsAC) (hd : pairInterEq) :
    withPairHuber3 hf hg => withPairLocRing PD TD sD LD hdenD =>
      ∀ x : CompletedTensor (Completion LA) (Completion LB) (Completion LC),
        pairApp23 Pair.completedTensorRationalEquiv hf hg hd x ∈
          completedPlusSubring PD (SB.completedTensor A SC).plus TD sD LD hdenD ↔
          x ∈ (pairCtPair hPB hPC).plus := by
  pair_tensor_inst hf hg; intro x
  rw [← pairApp23 Pair.map_plus_completedTensorRationalEquiv hPB hPC hf hg hd]
  simp only [Subring.mem_map_equiv, RingEquiv.symm_apply_apply]

section RationalLocProps

variable (hPB : PB.ringOfDefinition ≤ SB.plus) (hPC : PC.ringOfDefinition ≤ SC.plus)
  (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
  (hf : pairMapsAB) (hg : pairMapsAC) (hd : pairInterEq)

/-- Forward Huber-pair morphism `O_B(U) ⊗̂_{O_A(W)} O_C(V) → O_D(d)`. -/
noncomputable def Pair.completedTensor.toRationalLoc :
    withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
      Pair.Hom (pairCtPair hPB hPC)
        (PD.rationalLocalizationPair (SB.completedTensor A SC) hPD TD sD LD hdenD) :=
  withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
  { toRingHom := (pairApp23 Pair.completedTensorRationalEquiv hf hg hd).toRingHom
    continuous_toRingHom := pairApp23 Pair.continuous_completedTensorRationalEquiv hf hg hd
    map_mem_plus := fun x hx ↦ by
      rw [rationalLocalizationPair_plus]
      exact (pairApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        hPB hPC hf hg hd x).mpr hx }

/-- Inverse Huber-pair morphism `O_D(d) → O_B(U) ⊗̂_{O_A(W)} O_C(V)`. -/
noncomputable def Pair.completedTensor.ofRationalLoc :
    withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
      Pair.Hom (PD.rationalLocalizationPair (SB.completedTensor A SC) hPD TD sD LD hdenD)
        (pairCtPair hPB hPC) :=
  withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
  let e := pairApp23 Pair.completedTensorRationalEquiv hf hg hd
  { toRingHom := e.symm.toRingHom
    continuous_toRingHom := pairApp23 Pair.continuous_completedTensorRationalEquiv_symm hf hg hd
    map_mem_plus := fun z hz ↦ by
      rw [rationalLocalizationPair_plus] at hz
      exact (pairApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        hPB hPC hf hg hd (e.symm z)).mp (by simpa [e] using hz) }

/-- Underlying ring homomorphism of `Pair.completedTensor.toRationalLoc`. -/
@[simp] theorem Pair.completedTensor.toRationalLoc_toRingHom :
    withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
      (pairApp23 Pair.completedTensor.toRationalLoc hPB hPC hPD hf hg hd).toRingHom =
        (pairApp23 Pair.completedTensorRationalEquiv hf hg hd :
          CompletedTensor (Completion LA) (Completion LB) (Completion LC) →+* Completion LD) :=
  (rfl)

/-- Underlying ring homomorphism of `Pair.completedTensor.ofRationalLoc`. -/
@[simp] theorem Pair.completedTensor.ofRationalLoc_toRingHom :
    withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
      (pairApp23 Pair.completedTensor.ofRationalLoc hPB hPC hPD hf hg hd).toRingHom =
        ((pairApp23 Pair.completedTensorRationalEquiv hf hg hd).symm :
          Completion LD →+* CompletedTensor (Completion LA) (Completion LB) (Completion LC)) :=
  (rfl)

/-- `toRationalLoc` and `ofRationalLoc` compose to the identity on `O_D(d)`. -/
@[simp] theorem Pair.completedTensor.toRationalLoc_comp_ofRationalLoc :
    withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
      (pairApp23 Pair.completedTensor.toRationalLoc hPB hPC hPD hf hg hd).comp
          (pairApp23 Pair.completedTensor.ofRationalLoc hPB hPC hPD hf hg hd) =
        Pair.Hom.id (PD.rationalLocalizationPair (SB.completedTensor A SC) hPD TD sD LD hdenD) := by
  pair_tensor_inst hf hg; ext1; simp

/-- `ofRationalLoc` and `toRationalLoc` compose to the identity on `O_B(U) ⊗̂_{O_A(W)} O_C(V)`. -/
@[simp] theorem Pair.completedTensor.ofRationalLoc_comp_toRationalLoc :
    withPairHuber3 hf hg => withPairLocHuber PD TD sD LD hdenD =>
      (pairApp23 Pair.completedTensor.ofRationalLoc hPB hPC hPD hf hg hd).comp
          (pairApp23 Pair.completedTensor.toRationalLoc hPB hPC hPD hf hg hd) =
        Pair.Hom.id (pairCtPair hPB hPC) := by
  pair_tensor_inst hf hg; ext1; simp

end RationalLocProps

end RationalPair

section UnlocalisedBase

/-- Abbreviate the product numerator finset in `CompletedTensor A B C`. -/
local macro "unlocTD" : term =>
  let i := Lean.mkIdent
  `((insert (CompletedTensor.inl $(i `A) $(i `B) $(i `C) $(i `s))
        (($(i `T)).image (CompletedTensor.inl $(i `A) $(i `B) $(i `C))) *
      insert (CompletedTensor.inr $(i `A) $(i `B) $(i `C) $(i `s'))
        (($(i `T')).image (CompletedTensor.inr $(i `A) $(i `B) $(i `C))) : Finset _))

/-- Abbreviate the product denominator `inl(s) * inr(s')` in `CompletedTensor A B C`. -/
local macro "unlocSD" : term =>
  let i := Lean.mkIdent
  `((CompletedTensor.inl $(i `A) $(i `B) $(i `C) $(i `s)) *
    (CompletedTensor.inr $(i `A) $(i `B) $(i `C) $(i `s')))

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [DecidableEq (CompletedTensor A B C)]
  (P : PairOfDefinition B) (SB : Pair B) (hP : P.ringOfDefinition ≤ SB.plus)
  (T : Finset B) (s : B) (S : Type*) [CommRing S] [Algebra B S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition C) (SC : Pair C) (hP' : P'.ringOfDefinition ≤ SC.plus)
  (T' : Finset C) (s' : C) (S' : Type*) [CommRing S'] [Algebra C S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (Q : PairOfDefinition (CompletedTensor A B C)) (S'' : Type*) [CommRing S'']
  [Algebra (CompletedTensor A B C) S''] [IsLocalization.Away unlocSD S'']
  (hden'' : HasDenominatorPower Q unlocTD unlocSD S'')

/-- Induced `Algebra A (Completion L)` structure on an unlocalised-base factor. -/
local macro "unlocAlg " R:term:arg P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `(((toCompletionLoc $P $T $s $L $h).comp (algebraMap $(i `A) $R)).toAlgebra)

/-- Adicness of `algebraMap A (Completion L)` on an unlocalised-base factor. -/
local macro "unlocAdic " R:term:arg P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `((IsAdicHom.comp (isAdicHom_toCompletionLoc $P $T $s $L $h)
      (inferInstance : IsAdicHom (algebraMap $(i `A) $R)) :
      IsAdicHom (algebraMap $(i `A) (Completion $L))))

/-- Install unlocalised-base completed-tensor localization instances in a term. -/
local macro "withUnlocInst " " => " body:term : term =>
  let i := Lean.mkIdent
  `(withPairLocHuber $(i `P) $(i `T) $(i `s) $(i `S) $(i `hden) =>
    withPairLocHuber $(i `P') $(i `T') $(i `s') $(i `S') $(i `hden') =>
    letI := unlocAlg $(i `B) $(i `P) $(i `T) $(i `s) $(i `S) $(i `hden)
    letI := unlocAlg $(i `C) $(i `P') $(i `T') $(i `s') $(i `S') $(i `hden')
    haveI := unlocAdic $(i `B) $(i `P) $(i `T) $(i `s) $(i `S) $(i `hden)
    haveI := unlocAdic $(i `C) $(i `P') $(i `T') $(i `s') $(i `S') $(i `hden')
    withPairLocRing $(i `Q) _ _ $(i `S'') $(i `hden'') => $body)

/-- Register unlocalised-base completed-tensor localization instances in tactic mode. -/
local macro "pair_unloc_inst" : tactic =>
  let i := Lean.mkIdent
  `(tactic| (
    pair_loc_huber $(i `P) $(i `T) $(i `s) $(i `S) $(i `hden)
    pair_loc_huber $(i `P') $(i `T') $(i `s') $(i `S') $(i `hden')
    pair_loc_huber $(i `Q) _ _ $(i `S'') $(i `hden'')
    let _ := unlocAlg $(i `B) $(i `P) $(i `T) $(i `s) $(i `S) $(i `hden)
    let _ := unlocAlg $(i `C) $(i `P') $(i `T') $(i `s') $(i `S') $(i `hden')
    have _ := unlocAdic $(i `B) $(i `P) $(i `T) $(i `s) $(i `S) $(i `hden)
    have _ := unlocAdic $(i `C) $(i `P') $(i `T') $(i `s') $(i `S') $(i `hden')))

/-- Over an unlocalised base `A`, `CompletedTensor.completionLocEquiv` carries the completed tensor
plus ring onto `completedPlusSubring`. -/
theorem Pair.map_plus_completionLocEquiv :
    withUnlocInst =>
      ((P.rationalLocalizationPair SB hP T s S hden).completedTensor A
        (P'.rationalLocalizationPair SC hP' T' s' S' hden')).plus.map
        (CompletedTensor.completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'' :
          CompletedTensor A (Completion S) (Completion S') →+* Completion S'') =
        completedPlusSubring Q (SB.completedTensor A SC).plus unlocTD unlocSD S'' hden'' := by
  pair_unloc_inst
  exact map_plus_of_ringEquiv P SB hP T s S hden P' SC hP' T' s' S' hden' Q _ _ S'' hden''
    (CompletedTensor.completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'')
    (CompletedTensor.continuous_completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'')
    (CompletedTensor.continuous_completionLocEquiv_symm P T s S hden P' T' s' S' hden' Q S'' hden'')
    (fun b ↦ by simp [toCompletionLoc_apply]) (fun c ↦ by simp [toCompletionLoc_apply])
    (by convert (Pair.completedTensor.inter_preimage_rationalSubset (A := A) SB SC T s T' s').symm)

/-- Membership in the completed tensor plus ring over an unlocalised base `A` is equivalent to
membership of the image under `CompletedTensor.completionLocEquiv` in `completedPlusSubring`. -/
theorem Pair.mem_completedTensor_plus_iff_completionLocEquiv :
    withUnlocInst =>
      ∀ x : CompletedTensor A (Completion S) (Completion S'),
        CompletedTensor.completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'' x ∈
            completedPlusSubring Q (SB.completedTensor A SC).plus unlocTD unlocSD S'' hden'' ↔
          x ∈ ((P.rationalLocalizationPair SB hP T s S hden).completedTensor A
            (P'.rationalLocalizationPair SC hP' T' s' S' hden')).plus := by
  pair_unloc_inst; intro x
  rw [← Pair.map_plus_completionLocEquiv P SB hP T s S hden P' SC hP' T' s' S' hden' Q S'' hden'']
  simp only [Subring.mem_map_equiv, RingEquiv.symm_apply_apply]

end UnlocalisedBase

end TauCeti.Huber

end
