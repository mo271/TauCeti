/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MorphismSpectral
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction

/-!
# Rational preimages and intersections in completed tensor adic spectra

For Huber pairs `(B, B⁺)` and `(C, C⁺)` with adic structure homomorphisms from `A`, and rational
presentations `U = R(T_B/s_B) ⊆ Spa (B, B⁺)` and `V = R(T_C/s_C) ⊆ Spa (C, C⁺)` with open
numerator ideals, this file constructs explicit rational presentations with open numerator ideals
for `p_B⁻¹(U)`, `p_C⁻¹(V)`, and `p_B⁻¹(U) ∩ p_C⁻¹(V)` in `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.30(5) and Lemma 7.46(3).
-/

public section

open scoped Pointwise

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- Abbreviate `CompletedTensor.inl A B C`. -/
local macro "prInl" : term =>
  let i := Lean.mkIdent; `(CompletedTensor.inl $(i `A) $(i `B) $(i `C))

/-- Abbreviate `CompletedTensor.inr A B C`. -/
local macro "prInr" : term =>
  let i := Lean.mkIdent; `(CompletedTensor.inr $(i `A) $(i `B) $(i `C))

/-- Abbreviate openness of the ideal spanned by a finset in `CompletedTensor A B C`. -/
local macro "prOpenSpan " T:term:arg : term =>
  let i := Lean.mkIdent
  `(IsOpen (Ideal.span (($T : Finset (CompletedTensor $(i `A) $(i `B) $(i `C))) :
      Set (CompletedTensor $(i `A) $(i `B) $(i `C))) :
      Set (CompletedTensor $(i `A) $(i `B) $(i `C))))

namespace Pair.completedTensor

open Classical in
/-- If `T_B` generates an open ideal in `B`, `inl '' T_B` generates an open ideal in `B ⊗̂_A C`. -/
theorem isOpen_span_image_inl {TB : Finset B} (hTB : IsOpen (Ideal.span (TB : Set B) : Set B)) :
    prOpenSpan (TB.image prInl) := by
  rw [Finset.coe_image, ← Ideal.map_span]
  exact (CompletedTensor.isAdicHom_inl A B C).isOpen_map hTB

open Classical in
/-- If `T_C` generates an open ideal in `C`, `inr '' T_C` generates an open ideal in `B ⊗̂_A C`. -/
theorem isOpen_span_image_inr {TC : Finset C} (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)) :
    prOpenSpan (TC.image prInr) := by
  rw [Finset.coe_image, ← Ideal.map_span]
  exact (CompletedTensor.isAdicHom_inr A B C).isOpen_map hTC

open Classical in
/-- If `T_B · B` and `T_C · C` are open, `insert (inl s_B) (inl T_B) * insert (inr s_C) (inr T_C)`
generates an open ideal in `B ⊗̂_A C`. -/
theorem isOpen_span_inter_inl_inr {TB : Finset B} (sB : B) {TC : Finset C} (sC : C)
    (hTB : IsOpen (Ideal.span (TB : Set B) : Set B))
    (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)) :
    prOpenSpan (insert (prInl sB) (TB.image prInl) * insert (prInr sC) (TC.image prInr)) :=
  (IsHuberRing.nonempty_pairOfDefinition (A := CompletedTensor A B C)).some
    |>.isOpen_span_insert_mul_insert (isOpen_span_image_inl (A := A) (C := C) hTB)
      (isOpen_span_image_inr (A := A) (B := B) hTC)

section Pairs

variable [IsHuberRing B] [IsHuberRing C] (SB : Pair B) (SC : Pair C)

open Classical in
/-- Preimage of `R(T_B/s_B) ⊆ Spa (B, B⁺)` under `(inl A SB SC).spaComap`. -/
theorem inl_spaComap_preimage_rationalSubset (TB : Finset B) (sB : B) :
    (inl A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SB.plus TB sB) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus (TB.image prInl) (prInl sB) :=
  by simpa using (inl A SB SC).spaComap_preimage_rationalSubset TB sB

open Classical in
/-- Preimage of `R(T_C/s_C) ⊆ Spa (C, C⁺)` under `(inr A SB SC).spaComap`. -/
theorem inr_spaComap_preimage_rationalSubset (TC : Finset C) (sC : C) :
    (inr A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SC.plus TC sC) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus (TC.image prInr) (prInr sC) :=
  by simpa using (inr A SB SC).spaComap_preimage_rationalSubset TC sC

/-- Preimage under `(inl A SB SC).spaComap` preserves membership in `spaRationalFamily`. -/
theorem inl_spaComap_preimage_mem_spaRationalFamily
    {U : Set (spa SB.plus)} (hU : U ∈ spaRationalFamily SB.plus) :
    (inl A SB SC).spaComap ⁻¹' U ∈ spaRationalFamily (SB.completedTensor A SC).plus :=
  (inl A SB SC).spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ by simpa using (CompletedTensor.isAdicHom_inl A B C).isOpen_map hJ) hU

/-- Preimage under `(inr A SB SC).spaComap` preserves membership in `spaRationalFamily`. -/
theorem inr_spaComap_preimage_mem_spaRationalFamily
    {V : Set (spa SC.plus)} (hV : V ∈ spaRationalFamily SC.plus) :
    (inr A SB SC).spaComap ⁻¹' V ∈ spaRationalFamily (SB.completedTensor A SC).plus :=
  (inr A SB SC).spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ by simpa using (CompletedTensor.isAdicHom_inr A B C).isOpen_map hJ) hV

open Classical in
/-- Intersection of the preimages of `R(T_B/s_B)` and `R(T_C/s_C)` in the completed tensor adic
spectrum, presented over `inl(s_B) * inr(s_C)`. -/
theorem inter_preimage_rationalSubset (TB : Finset B) (sB : B) (TC : Finset C) (sC : C) :
    ((inl A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((inr A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (insert (prInl sB) (TB.image prInl) * insert (prInr sC) (TC.image prInr))
        (prInl sB * prInr sC) := by
  rw [inl_spaComap_preimage_rationalSubset, inr_spaComap_preimage_rationalSubset,
    ← Set.preimage_inter, rationalSubset_inter]

end Pairs

end Pair.completedTensor

open Classical in
/-- **Rational preimages and intersections in the completed tensor adic spectrum**
(Wedhorn Lemma 7.46(3) and Remark 7.30(5)). -/
theorem Pair.completedTensorRationalEquiv_preimage [IsHuberRing B] [IsHuberRing C]
    (SB : Pair B) (SC : Pair C) {TB : Finset B} (sB : B) {TC : Finset C} (sC : C)
    (hTB : IsOpen (Ideal.span (TB : Set B) : Set B))
    (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)) :
    ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus (TB.image prInl) (prInl sB) ∧
      prOpenSpan (TB.image prInl)) ∧
    ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus (TC.image prInr) (prInr sC) ∧
      prOpenSpan (TC.image prInr)) ∧
    (((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
        ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (insert (prInl sB) (TB.image prInl) * insert (prInr sC) (TC.image prInr))
        (prInl sB * prInr sC) ∧
      prOpenSpan (insert (prInl sB) (TB.image prInl) * insert (prInr sC) (TC.image prInr))) :=
  ⟨⟨Pair.completedTensor.inl_spaComap_preimage_rationalSubset SB SC TB sB,
      Pair.completedTensor.isOpen_span_image_inl hTB⟩,
    ⟨Pair.completedTensor.inr_spaComap_preimage_rationalSubset SB SC TC sC,
      Pair.completedTensor.isOpen_span_image_inr hTC⟩,
    ⟨Pair.completedTensor.inter_preimage_rationalSubset SB SC TB sB TC sC,
      Pair.completedTensor.isOpen_span_inter_inl_inr sB sC hTB hTC⟩⟩

end TauCeti.Huber

end
