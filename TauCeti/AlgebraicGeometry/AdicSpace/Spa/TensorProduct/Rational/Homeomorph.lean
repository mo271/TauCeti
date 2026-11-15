/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RingEquiv
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Pair

import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Adic spectrum of a completed tensor product of rational localisations

Composing `spaHomeomorphOfRingEquiv` for `Pair.completedTensorRationalEquiv` with
`spaCompletedLocalizationHomeomorph` identifies the adic spectrum of
`O_B(U) ⊗̂_{O_A(W)} O_C(V)` with `p_B⁻¹(U) ∩ p_C⁻¹(V)` inside `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`
(`Pair.completedTensorRationalSpaHomeomorph`), matching rational subsets on both sides.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(2).
-/

public section

open UniformSpace (Completion)

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

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

/-- Install localization topological-ring instances in a term. -/
local macro "withSpaLocRing " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg
    " => " body:term : term =>
  `(letI := locUniformSpace $P $T $s $L $h; letI := isUniformAddGroup_locUniformSpace $P $T $s $L $h
    letI := isTopologicalRing_locUniformSpace $P $T $s $L $h; $body)

/-- Register localization topological-ring instances in tactic mode. -/
local macro "spa_loc_ring " P:term:arg T:term:arg s:term:arg L:term:arg h:term:arg : tactic =>
  `(tactic| (
    let _ := locUniformSpace $P $T $s $L $h
    have _ := isUniformAddGroup_locUniformSpace $P $T $s $L $h
    have _ := isTopologicalRing_locUniformSpace $P $T $s $L $h))

/-- Induced `Algebra (Completion LA) (Completion L)` structure from `h`. -/
local macro "spaAlg " R:term:arg P:term:arg S:term:arg T:term:arg s:term:arg L:term:arg
    hd:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `((ringHomOfMapsToRationalSubset $(i `PA) ($(i `SA)).plus $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
      $P ($S).plus ($S).isRingOfIntegralElements.isPowerBounded_of_mem $T $s $L $hd
      (inferInstance : IsAdicHom (algebraMap $(i `A) $R)).continuous.continuousAt $h).toAlgebra)

/-- Adicness of `algebraMap (Completion LA) (Completion L)` from `h`. -/
local macro "spaAdic " R:term:arg P:term:arg S:term:arg T:term:arg s:term:arg L:term:arg
    hd:term:arg h:term:arg : term =>
  let i := Lean.mkIdent
  `((isAdicHom_ringHomOfMapsToRationalSubset $(i `PA) ($(i `SA)).plus $(i `TA) $(i `sA) $(i `LA)
      $(i `hdenA) $P ($S).plus ($S).isRingOfIntegralElements.isPowerBounded_of_mem $T $s $L $hd
      (inferInstance : IsAdicHom (algebraMap $(i `A) $R)) $h :
      IsAdicHom (algebraMap (Completion $(i `LA)) (Completion $L))))

/-- Install the three-factor completed-tensor localization instances in a term. -/
local macro "withSpaHuber3 " hf:term:arg hg:term:arg " => " body:term : term =>
  let i := Lean.mkIdent
  `(withSpaLocRing $(i `PA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA) =>
    withSpaLocRing $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) =>
    letI := isHuberRing_completion_locTopology $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
    withSpaLocRing $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) =>
    letI := isHuberRing_completion_locTopology $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC)
    letI := spaAlg $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    letI := spaAlg $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    haveI := spaAdic $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    haveI := spaAdic $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    $body)

/-- Register completed-tensor localization instances in tactic mode. -/
local macro "homeomorph_tensor_inst " hf:term:arg hg:term:arg : tactic =>
  let i := Lean.mkIdent
  `(tactic| (
    spa_loc_ring $(i `PA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
    spa_loc_ring $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
    have _ := isHuberRing_completion_locTopology $(i `PB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
    spa_loc_ring $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC)
    have _ := isHuberRing_completion_locTopology $(i `PC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC)
    let _ := spaAlg $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    let _ := spaAlg $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    have _ := spaAdic $(i `B) $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB) $hf
    have _ := spaAdic $(i `C) $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC) $hg
    spa_loc_ring $(i `PD) $(i `TD) $(i `sD) $(i `LD) $(i `hdenD)))

/-- Apply `f` to the 23 four-factor section variables `PA .. hdenD`. -/
local macro:max "spaApp23 " f:term:max : term =>
  let i := Lean.mkIdent
  `($f $(i `PA) $(i `SA) $(i `TA) $(i `sA) $(i `LA) $(i `hdenA)
      $(i `PB) $(i `SB) $(i `TB) $(i `sB) $(i `LB) $(i `hdenB)
      $(i `PC) $(i `SC) $(i `TC) $(i `sC) $(i `LC) $(i `hdenC)
      $(i `PD) $(i `TD) $(i `sD) $(i `LD) $(i `hdenD))

/-- Abbreviate `Set.MapsTo (comap (algebraMap A B)) R(TB/sB) R(TA/sA)`. -/
local macro "spaMapsAB" : term =>
  let i := Lean.mkIdent
  `(Set.MapsTo (comap (algebraMap $(i `A) $(i `B)))
      (rationalSubset ($(i `SB)).plus $(i `TB) $(i `sB))
      (rationalSubset ($(i `SA)).plus $(i `TA) $(i `sA)))

/-- Abbreviate `Set.MapsTo (comap (algebraMap A C)) R(TC/sC) R(TA/sA)`. -/
local macro "spaMapsAC" : term =>
  let i := Lean.mkIdent
  `(Set.MapsTo (comap (algebraMap $(i `A) $(i `C)))
      (rationalSubset ($(i `SC)).plus $(i `TC) $(i `sC))
      (rationalSubset ($(i `SA)).plus $(i `TA) $(i `sA)))

/-- Abbreviate `p_B⁻¹(U) ∩ p_C⁻¹(V)` in `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`. -/
local macro "spaInterSub" : term =>
  let i := Lean.mkIdent
  `(((Pair.completedTensor.inl $(i `A) $(i `SB) $(i `SC)).spaComap ⁻¹'
      (Subtype.val ⁻¹' rationalSubset ($(i `SB)).plus $(i `TB) $(i `sB))) ∩
    ((Pair.completedTensor.inr $(i `A) $(i `SB) $(i `SC)).spaComap ⁻¹'
      (Subtype.val ⁻¹' rationalSubset ($(i `SC)).plus $(i `TC) $(i `sC))))

/-- Abbreviate the intersection presentation hypothesis on `(TD, sD)`. -/
local macro "spaInterEq" : term =>
  let i := Lean.mkIdent
  `(Subtype.val ⁻¹' rationalSubset (($(i `SB)).completedTensor $(i `A) $(i `SC)).plus
      $(i `TD) $(i `sD) = spaInterSub)

/-- Abbreviate the completed tensor Huber pair of `O_B(U)` and `O_C(V)` over `O_A(W)`. -/
local macro "spaCtPair " hPB:term:arg hPC:term:arg : term =>
  let i := Lean.mkIdent
  `(((($(i `PB)).rationalLocalizationPair $(i `SB) $hPB $(i `TB) $(i `sB) $(i `LB)
      $(i `hdenB)).completedTensor (Completion $(i `LA))
      (($(i `PC)).rationalLocalizationPair $(i `SC) $hPC $(i `TC) $(i `sC) $(i `LC) $(i `hdenC))))

section BasicProps

variable (hPB : PB.ringOfDefinition ≤ SB.plus) (hPC : PC.ringOfDefinition ≤ SC.plus)
  (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
  (hf : spaMapsAB) (hg : spaMapsAC) (hd : spaInterEq)

/-- **Homeomorphism of the adic spectrum of a completed tensor product of rational localisations
onto `p_B⁻¹(U) ∩ p_C⁻¹(V)`** in `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`. -/
noncomputable def Pair.completedTensorRationalSpaHomeomorph :
    withSpaHuber3 hf hg => spa (spaCtPair hPB hPC).plus ≃ₜ ↥spaInterSub :=
  withSpaHuber3 hf hg => withSpaLocRing PD TD sD LD hdenD =>
  let e := spaApp23 Pair.completedTensorRationalEquiv hf hg hd
  (spaHomeomorphOfRingEquiv e (spaApp23 Pair.continuous_completedTensorRationalEquiv hf hg hd)
    (spaApp23 Pair.continuous_completedTensorRationalEquiv_symm hf hg hd)
    (fun x hx ↦ (spaApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      hPB hPC hf hg hd x).mpr hx)
    (fun y hy ↦ (spaApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      hPB hPC hf hg hd (e.symm y)).mp (by simpa [e] using hy))).symm.trans
    ((spaCompletedLocalizationHomeomorph PD (SB.completedTensor A SC).plus hPD TD sD LD hdenD).trans
      (Homeomorph.setCongr hd))

/-- `Pair.completedTensorRationalSpaHomeomorph` acts on points by pulling valuations back along
`e⁻¹ ∘ ρ_D`. -/
@[simp] theorem Pair.completedTensorRationalSpaHomeomorph_val_val :
    withSpaHuber3 hf hg => withSpaLocRing PD TD sD LD hdenD =>
      ∀ z : spa (spaCtPair hPB hPC).plus,
        (((spaApp23 Pair.completedTensorRationalSpaHomeomorph hPB hPC hPD hf hg hd z).1 :
            spa (SB.completedTensor A SC).plus) : Spv (CompletedTensor A B C)) =
          comap (((spaApp23 Pair.completedTensorRationalEquiv hf hg hd).symm : Completion LD →+*
              CompletedTensor (Completion LA) (Completion LB) (Completion LC)).comp
            (toCompletionLoc PD TD sD LD hdenD)) z.1 := by
  homeomorph_tensor_inst hf hg; intro z
  dsimp only [Pair.completedTensorRationalSpaHomeomorph]
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.setCongr_apply]; dsimp only
  rw [spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val, spaComapLoc_val,
    spaHomeomorphOfRingEquiv_symm_val,
    ← Function.comp_apply (f := comap (toCompletionLoc PD TD sD LD hdenD)), ← comap_comp]

/-- Compatibility with the left completed tensor projection onto `Spa (B, B⁺)`. -/
theorem Pair.inl_spaComap_completedTensorRationalSpaHomeomorph :
    withSpaHuber3 hf hg =>
      ∀ z : spa (spaCtPair hPB hPC).plus,
        (Pair.completedTensor.inl A SB SC).spaComap
            (spaApp23 Pair.completedTensorRationalSpaHomeomorph hPB hPC hPD hf hg hd z).1 =
          spaComapLoc PB SB.plus TB sB LB hdenB
            ⟨((Pair.completedTensor.inl (Completion LA)
                (PB.rationalLocalizationPair SB hPB TB sB LB hdenB)
                (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).spaComap z).1,
              by rw [← rationalLocalizationPair_plus PB SB hPB TB sB LB hdenB]; exact
                ((Pair.completedTensor.inl (Completion LA) _ _).spaComap z).2⟩ := by
  homeomorph_tensor_inst hf hg; intro z; apply Subtype.ext
  simp only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl,
    Pair.completedTensorRationalSpaHomeomorph_val_val, spaComapLoc_val]
  rw [← Function.comp_apply (f := comap (CompletedTensor.inl A B C)), ← comap_comp,
    ← Function.comp_apply (f := comap (toCompletionLoc PB TB sB LB hdenB)), ← comap_comp]
  exact congrFun (congrArg comap (by ext b; simp [toCompletionLoc_apply])) z.1

/-- Compatibility with the right completed tensor projection onto `Spa (C, C⁺)`. -/
theorem Pair.inr_spaComap_completedTensorRationalSpaHomeomorph :
    withSpaHuber3 hf hg =>
      ∀ z : spa (spaCtPair hPB hPC).plus,
        (Pair.completedTensor.inr A SB SC).spaComap
            (spaApp23 Pair.completedTensorRationalSpaHomeomorph hPB hPC hPD hf hg hd z).1 =
          spaComapLoc PC SC.plus TC sC LC hdenC
            ⟨((Pair.completedTensor.inr (Completion LA)
                (PB.rationalLocalizationPair SB hPB TB sB LB hdenB)
                (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).spaComap z).1,
              by rw [← rationalLocalizationPair_plus PC SC hPC TC sC LC hdenC]; exact
                ((Pair.completedTensor.inr (Completion LA) _ _).spaComap z).2⟩ := by
  homeomorph_tensor_inst hf hg; intro z; apply Subtype.ext
  simp only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr,
    Pair.completedTensorRationalSpaHomeomorph_val_val, spaComapLoc_val]
  rw [← Function.comp_apply (f := comap (CompletedTensor.inr A B C)), ← comap_comp,
    ← Function.comp_apply (f := comap (toCompletionLoc PC TC sC LC hdenC)), ← comap_comp]
  exact congrFun (congrArg comap (by ext c; simp [toCompletionLoc_apply])) z.1

/-- Preimage under `Pair.completedTensorRationalSpaHomeomorph` preserves rational subsets. -/
theorem Pair.completedTensorRationalSpaHomeomorph_preimage_mem_spaRationalFamily
    {Z : Set (spa (SB.completedTensor A SC).plus)}
    (hZ : Z ∈ spaRationalFamily (SB.completedTensor A SC).plus) :
    withSpaHuber3 hf hg =>
      spaApp23 Pair.completedTensorRationalSpaHomeomorph hPB hPC hPD hf hg hd ⁻¹'
        (Subtype.val ⁻¹' Z) ∈ spaRationalFamily (spaCtPair hPB hPC).plus := by
  homeomorph_tensor_inst hf hg
  convert spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily
      (spaApp23 Pair.completedTensorRationalEquiv hf hg hd).symm
      (spaApp23 Pair.continuous_completedTensorRationalEquiv_symm hf hg hd)
      (spaApp23 Pair.continuous_completedTensorRationalEquiv hf hg hd)
      (fun y hy ↦ (spaApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        hPB hPC hf hg hd _).mp (by simpa using hy))
      (fun x hx ↦ (spaApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        hPB hPC hf hg hd x).mpr hx)
      (spaCompletedLocalizationHomeomorph_preimage_mem_spaRationalFamily
        PD (SB.completedTensor A SC).plus hPD TD sD LD hdenD hZ) using 1
  ext x; simp only [Pair.completedTensorRationalSpaHomeomorph, Set.mem_preimage,
    Homeomorph.trans_apply, Homeomorph.setCongr_apply, spaHomeomorphOfRingEquiv_symm]

end BasicProps

/-- **Rational subsets match across `Pair.completedTensorRationalSpaHomeomorph`**
(Huber Lemma 1.5(ii); Wedhorn Proposition 8.2(2)). -/
theorem Pair.bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily
    (hPB : PB.ringOfDefinition ≤ SB.plus) (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hTD : IsOpen (Ideal.span (TD : Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)))
    (hf : spaMapsAB) (hg : spaMapsAC) (hd : spaInterEq) :
    withSpaHuber3 hf hg =>
      Set.BijOn (fun Z : Set (spa (SB.completedTensor A SC).plus) ↦
          spaApp23 Pair.completedTensorRationalSpaHomeomorph hPB hPC hPD hf hg hd ⁻¹'
            (Subtype.val ⁻¹' Z))
        {Z ∈ spaRationalFamily (SB.completedTensor A SC).plus | Z ⊆ spaInterSub}
        (spaRationalFamily (spaCtPair hPB hPC).plus) := by
  homeomorph_tensor_inst hf hg; let e := spaApp23 Pair.completedTensorRationalEquiv hf hg hd
  have hdom : {Z ∈ spaRationalFamily (SB.completedTensor A SC).plus | Z ⊆ spaInterSub} =
      {Z ∈ spaRationalFamily (SB.completedTensor A SC).plus |
        Z ⊆ Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD} := by rw [hd]
  rw [hdom]
  have hb₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily e.symm
    (spaApp23 Pair.continuous_completedTensorRationalEquiv_symm hf hg hd)
    (spaApp23 Pair.continuous_completedTensorRationalEquiv hf hg hd)
    (fun y hy ↦ (spaApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      hPB hPC hf hg hd (e.symm y)).mp (by simpa [e] using hy))
    (fun x hx ↦ (spaApp23 Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      hPB hPC hf hg hd x).mpr hx)
  have hb₂ := bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily
    PD (SB.completedTensor A SC).plus hPD TD sD hTD LD hdenD
  refine (hb₁.comp hb₂).congr fun Z _ ↦ ?_; ext x
  simp only [Function.comp_apply, Pair.completedTensorRationalSpaHomeomorph, Set.mem_preimage,
    Homeomorph.trans_apply, Homeomorph.setCongr_apply, spaHomeomorphOfRingEquiv_symm]; exact Iff.rfl

/-- Image under `Pair.completedTensorRationalSpaHomeomorph` of a rational subset is rational when
`T_D` generates an open ideal. -/
theorem Pair.completedTensorRationalSpaHomeomorph_image_mem_spaRationalFamily
    (hPB : PB.ringOfDefinition ≤ SB.plus) (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hTD : IsOpen (Ideal.span (TD : Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)))
    (hf : spaMapsAB) (hg : spaMapsAC) (hd : spaInterEq) :
    withSpaHuber3 hf hg =>
      ∀ {Y : Set (spa (spaCtPair hPB hPC).plus)}, Y ∈ spaRationalFamily (spaCtPair hPB hPC).plus →
        Subtype.val '' (spaApp23 Pair.completedTensorRationalSpaHomeomorph hPB hPC hPD hf hg hd ''
          Y) ∈ spaRationalFamily (SB.completedTensor A SC).plus := by
  homeomorph_tensor_inst hf hg; intro Y hY
  obtain ⟨Z, ⟨hZ, hZsub⟩, rfl⟩ :=
    (spaApp23 Pair.bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily
      hPB hPC hPD hTD hf hg hd).surjOn hY
  rw [Set.image_preimage_eq _
      (spaApp23 Pair.completedTensorRationalSpaHomeomorph hPB hPC hPD hf hg hd).surjective,
    Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right hZsub]; exact hZ

end TauCeti.Huber

end
