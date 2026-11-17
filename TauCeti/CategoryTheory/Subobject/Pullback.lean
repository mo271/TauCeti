/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
import TauCeti.CategoryTheory.Subobject.Image

/-!
# Pullback, image, and cokernel identities for subobjects

This file collects the basic subobject lattice identities in normal-mono and abelian categories
needed for the subquotient correspondence: vanishing criteria for kernel and image subobjects,
factoring through a subobject via its cokernel projection, pulling back `⊥` to `kernelSubobject`,
and the round-trip identities between `Subobject.pullback` and `Subobject.exists` in an abelian
category.

## Main results

* `CategoryTheory.Limits.kernelSubobject_eq_top_iff`,
  `CategoryTheory.Limits.imageSubobject_eq_bot_iff`: vanishing criteria for kernel and image
  subobjects.
* `CategoryTheory.Subobject.factors_iff_comp_cokernel_π_eq_zero`: factoring through a subobject in
  a normal-mono category is detected by its cokernel projection.
* `CategoryTheory.Limits.kernelSubobject_cokernel_π`: the kernel subobject of the cokernel
  projection of a monomorphism `f` is `Subobject.mk f`.
* `CategoryTheory.Subobject.pullback_bot`: pulling back `⊥` along a morphism gives its kernel
  subobject.
* `CategoryTheory.Subobject.exists_pullback_eq_of_epi`,
  `CategoryTheory.Subobject.pullback_exists_eq_of_kernelSubobject_le`: lattice correspondence
  identities for `Subobject.exists` and `Subobject.pullback` in an abelian category.
-/

public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Limits

section KernelImage

variable [HasZeroMorphisms C]

/-- The kernel subobject of a morphism is `⊤` if and only if the morphism is zero. -/
@[simp]
lemma kernelSubobject_eq_top_iff {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    kernelSubobject f = ⊤ ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ kernelSubobject_zero⟩
  have : IsIso (kernelSubobject f).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  rw [← cancel_epi (kernelSubobject f).arrow, kernelSubobject_arrow_comp, comp_zero]

/-- The image subobject of a morphism is `⊥` if and only if the morphism is zero. -/
@[simp]
lemma imageSubobject_eq_bot_iff [HasZeroObject C] {X Y : C} (f : X ⟶ Y) [HasImage f] :
    imageSubobject f = ⊥ ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ imageSubobject_zero⟩
  have harrow : (imageSubobject f).arrow = 0 := by rw [h, Subobject.bot_arrow]
  rw [← imageSubobject_arrow_comp f, harrow, comp_zero]

end KernelImage

end CategoryTheory.Limits

namespace CategoryTheory.Subobject

/-- Pulling back `⊥` along a morphism gives its kernel subobject. -/
@[simp]
lemma pullback_bot [HasZeroMorphisms C] [HasPullbacks C] [HasZeroObject C] {X Y : C} (f : X ⟶ Y)
    [HasKernel f] : (pullback f).obj ⊥ = kernelSubobject f := by
  refine le_antisymm ?_ ?_
  · refine le_kernelSubobject _ _ ?_
    have h := (pullback_factors_iff f ⊥ ((pullback f).obj ⊥).arrow).1 (factors_self _)
    exact (bot_factors_iff_zero _).1 h
  · refine le_pullback_of_comm f (0 : (kernelSubobject f : C) ⟶ (⊥ : Subobject Y)) ?_
    simp [kernelSubobject_arrow_comp]

section NormalMono

variable [HasZeroMorphisms C] [IsNormalMonoCategory C]

/-- In a normal-mono category, a morphism factors through a subobject `B` if and only if it
vanishes after postcomposition with `cokernel.π B.arrow`. -/
lemma factors_iff_comp_cokernel_π_eq_zero {W X : C} (B : Subobject X) [HasCokernel B.arrow]
    (f : W ⟶ X) : B.Factors f ↔ f ≫ cokernel.π B.arrow = 0 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · rw [← B.factorThru_arrow f hf, Category.assoc, cokernel.condition, comp_zero]
  · let nm := normalMonoOfMono B.arrow
    have hg : f ≫ nm.g = 0 := by
      have hdesc : cokernel.π B.arrow ≫ cokernel.desc B.arrow nm.g nm.w = nm.g :=
        cokernel.π_desc _ _ _
      rw [← hdesc, reassoc_of% hf, zero_comp]
    exact factors_iff B f |>.2
      ⟨nm.isLimit.lift (KernelFork.ofι f hg), nm.isLimit.fac (KernelFork.ofι f hg) .zero⟩

/-- In a normal-mono category, `A ≤ B` in `Subobject X` if and only if `A.arrow` vanishes after
postcomposition with `cokernel.π B.arrow`. -/
lemma le_iff_arrow_comp_cokernel_π_eq_zero {X : C} {A B : Subobject X} [HasCokernel B.arrow] :
    A ≤ B ↔ A.arrow ≫ cokernel.π B.arrow = 0 := by
  rw [← factors_iff_comp_cokernel_π_eq_zero B A.arrow]
  exact ⟨fun h ↦ (factors_iff B A.arrow).2 ⟨ofLE A B h, ofLE_arrow h⟩,
    fun h ↦ le_of_comm (B.factorThru A.arrow h) (by simp)⟩

/-- In a normal-mono category, the kernel subobject of the cokernel projection of any monomorphism
`f` is `Subobject.mk f`. -/
@[simp]
lemma _root_.CategoryTheory.Limits.kernelSubobject_cokernel_π {Y X : C} (f : Y ⟶ X)
    [Mono f] [HasCokernel f] [HasKernel (cokernel.π f)] :
    kernelSubobject (cokernel.π f) = Subobject.mk f := by
  refine le_antisymm ?_ ?_
  · let nm := normalMonoOfMono f
    have hg : (kernelSubobject (cokernel.π f)).arrow ≫ nm.g = 0 := by
      have hdesc : cokernel.π f ≫ cokernel.desc f nm.g nm.w = nm.g := cokernel.π_desc _ _ _
      rw [← hdesc, reassoc_of% kernelSubobject_arrow_comp, zero_comp]
    refine le_of_comm (nm.isLimit.lift (KernelFork.ofι _ hg) ≫ (underlyingIso f).inv) ?_
    simpa [Category.assoc] using nm.isLimit.fac (KernelFork.ofι _ hg) .zero
  · refine le_kernelSubobject _ _ ?_
    rw [← underlyingIso_hom_comp_eq_mk, Category.assoc, cokernel.condition, comp_zero]

end NormalMono

section Abelian

variable [Abelian C]

/-- In an abelian category, pushing forward the pullback of a subobject along an epimorphism
recovers the subobject. -/
@[simp]
lemma exists_pullback_eq_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (K : Subobject Y) :
    (Subobject.exists f).obj ((pullback f).obj K) = K := by
  rw [exists_eq_imageSubobject, ← (isPullback f K).w, imageSubobject_comp_eq_of_epi,
    imageSubobject_mono, mk_arrow]

/-- In an abelian category, pulling back the image of a subobject `T` along `f` recovers `T`
whenever `kernelSubobject f ≤ T`. -/
lemma pullback_exists_eq_of_kernelSubobject_le {X Y : C} (f : X ⟶ Y) {T : Subobject X}
    (hT : kernelSubobject f ≤ T) :
    (pullback f).obj ((Subobject.exists f).obj T) = T := by
  refine le_antisymm ?_ (le_pullback_exists f T)
  set I := (Subobject.exists f).obj T
  set P := (pullback f).obj I
  let q : (T : C) ⟶ (I : C) :=
    factorThruImageSubobject (T.arrow ≫ f) ≫ (isoOfEq _ _ (exists_eq_imageSubobject f T).symm).hom
  have hq : q ≫ I.arrow = T.arrow ≫ f := by
    simp [q, I]
  have : Epi q := epi_comp _ _
  -- Pull back `pullbackπ f I : P ⟶ I` along the epimorphism `q : T ↠ I`.
  let g₁ : Limits.pullback (pullbackπ f I) q ⟶ (P : C) := Limits.pullback.fst (pullbackπ f I) q
  let g₂ : Limits.pullback (pullbackπ f I) q ⟶ (T : C) := Limits.pullback.snd (pullbackπ f I) q
  have : Epi g₁ := Abelian.epi_pullback_of_epi_g (pullbackπ f I) q
  have hdiff : (g₁ ≫ P.arrow - g₂ ≫ T.arrow) ≫ f = 0 := by
    have h1 : g₁ ≫ P.arrow ≫ f = (g₁ ≫ pullbackπ f I) ≫ I.arrow := by
      rw [Category.assoc, (isPullback f I).w]
    have h2 : g₂ ≫ T.arrow ≫ f = (g₂ ≫ q) ≫ I.arrow := by
      rw [Category.assoc, hq]
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, h1, h2,
      Limits.pullback.condition, sub_self]
  have hdiff_zero : (g₁ ≫ P.arrow - g₂ ≫ T.arrow) ≫ cokernel.π T.arrow = 0 := by
    have hfac : T.Factors (g₁ ≫ P.arrow - g₂ ≫ T.arrow) :=
      factors_of_le _ hT (kernelSubobject_factors f _ hdiff)
    exact (factors_iff_comp_cokernel_π_eq_zero T _).1 hfac
  have hg₁ : g₁ ≫ P.arrow ≫ cokernel.π T.arrow = 0 := by
    have : g₁ ≫ P.arrow ≫ cokernel.π T.arrow - g₂ ≫ T.arrow ≫ cokernel.π T.arrow = 0 := by
      simpa only [Preadditive.sub_comp, Category.assoc] using hdiff_zero
    simpa only [cokernel.condition, comp_zero, sub_zero] using this
  exact le_iff_arrow_comp_cokernel_π_eq_zero.2 ((cancel_epi g₁).1 (by simpa using hg₁))

end Abelian

end CategoryTheory.Subobject
