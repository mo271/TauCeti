/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import TauCeti.Algebra.Homology.ShortComplex.LeftHomology
public import TauCeti.CategoryTheory.Subobject.Subquotient

/-!
# Subquotient presentation of the homology of a short complex

In an abelian category `C`, the homology `S.homology` of a short complex `S : ShortComplex C` is
canonically isomorphic to the subquotient
`cokernel (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) (image_le_kernel S.f S.g _))`
of `S.X₂`. This file packages this identification as a `TauCeti.SubquotientPresentation`:

* `CategoryTheory.ShortComplex.homologyPresentation`: the canonical
  `TauCeti.SubquotientPresentation S.X₂ S.homology` with `B = imageSubobject S.f` and
  `Z = kernelSubobject S.g`.
* `CategoryTheory.ShortComplex.descMap_homologyPresentation`: for any morphism `φ : S₁ ⟶ S₂`, the
  morphism induced on `homologyPresentation` by `φ.τ₂` agrees with `ShortComplex.homologyMap φ`.
* `CategoryTheory.ShortComplex.refl_transIso_eq_homologyPresentation`: when `S.f = 0` and
  `S.g = 0`, `S.homologyPresentation` agrees with transporting the identity presentation along the
  canonical isomorphism `S.X₂ ≅ S.homology`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

private noncomputable abbrev subquotientLeftHomologyData (S : ShortComplex C) :
    S.LeftHomologyData :=
  let hi : IsLimit (KernelFork.ofι (kernelSubobject S.g).arrow
      (kernelSubobject_arrow_comp S.g)) :=
    KernelFork.IsLimit.ofι _ _
      (fun k hk ↦ factorThruKernelSubobject S.g k hk)
      (fun k hk ↦ factorThruKernelSubobject_comp_arrow S.g k hk)
      (fun k hk m hm ↦ by
        rw [← cancel_mono (kernelSubobject S.g).arrow, hm,
          factorThruKernelSubobject_comp_arrow])
  have hf' : hi.lift (KernelFork.ofι S.f S.zero) =
      factorThruImageSubobject S.f ≫
        Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
          (image_le_kernel S.f S.g S.zero) :=
    (factorThruImageSubobject_comp_imageToKernel S.f S.g S.zero).symm
  have wπ : hi.lift (KernelFork.ofι S.f S.zero) ≫
      cokernel.π (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
        (image_le_kernel S.f S.g S.zero)) = 0 := by
    rw [hf', Category.assoc, cokernel.condition, comp_zero]
  { K := (kernelSubobject S.g : C)
    H := cokernel (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
      (image_le_kernel S.f S.g S.zero))
    i := (kernelSubobject S.g).arrow
    π := cokernel.π (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
      (image_le_kernel S.f S.g S.zero))
    wi := kernelSubobject_arrow_comp S.g
    hi := hi
    wπ := wπ
    hπ := CokernelCofork.IsColimit.ofπ' _ wπ fun {A} k hk ↦
      ⟨cokernel.desc _ k ((cancel_epi (factorThruImageSubobject S.f)).mp
        (by rw [comp_zero, ← Category.assoc, ← hf']; exact hk)),
        cokernel.π_desc _ _ _⟩ }

/-- The canonical presentation of `S.homology` as the subquotient
`kernelSubobject S.g / imageSubobject S.f` of `S.X₂`. -/
noncomputable def homologyPresentation (S : ShortComplex C) :
    TauCeti.SubquotientPresentation S.X₂ S.homology :=
  (TauCeti.SubquotientPresentation.ofLE (image_le_kernel S.f S.g S.zero)).transIso
    (subquotientLeftHomologyData S).homologyIso.symm

@[simp]
lemma homologyPresentation_B (S : ShortComplex C) :
    S.homologyPresentation.B = imageSubobject S.f := by
  dsimp only [homologyPresentation]
  rw [TauCeti.SubquotientPresentation.transIso_B, TauCeti.SubquotientPresentation.ofLE_B]

@[simp]
lemma homologyPresentation_Z (S : ShortComplex C) :
    S.homologyPresentation.Z = kernelSubobject S.g := by
  dsimp only [homologyPresentation]
  rw [TauCeti.SubquotientPresentation.transIso_Z, TauCeti.SubquotientPresentation.ofLE_Z]

private lemma homologyPresentation_π (S : ShortComplex C) :
    S.homologyPresentation.π =
      Subobject.ofLE S.homologyPresentation.Z (kernelSubobject S.g) (homologyPresentation_Z S).le ≫
        (subquotientLeftHomologyData S).π ≫
          (subquotientLeftHomologyData S).homologyIso.inv := by
  dsimp only [homologyPresentation]
  rw [TauCeti.SubquotientPresentation.transIso_π, TauCeti.SubquotientPresentation.ofLE_π]
  simp only [Iso.symm_hom, Category.assoc]
  rw [← Category.assoc _ _ (_ ≫ _), Subobject.ofLE_comp_ofLE]

/-- A morphism `φ : S₁ ⟶ S₂` of short complexes maps `imageSubobject S₁.f` into
`imageSubobject S₂.f` along `φ.τ₂`. -/
lemma exists_imageSubobject_f_le {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (Subobject.exists φ.τ₂).obj (imageSubobject S₁.f) ≤ imageSubobject S₂.f := by
  rw [Subobject.exists_eq_imageSubobject,
    ← imageSubobject_comp_eq_of_epi (factorThruImageSubobject S₁.f),
    imageSubobject_arrow_comp_assoc, ← φ.comm₁₂]
  exact imageSubobject_comp_le φ.τ₁ S₂.f

/-- A morphism `φ : S₁ ⟶ S₂` of short complexes maps `kernelSubobject S₁.g` into
`kernelSubobject S₂.g` along `φ.τ₂`. -/
lemma kernelSubobject_g_le_pullback {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    kernelSubobject S₁.g ≤ (Subobject.pullback φ.τ₂).obj (kernelSubobject S₂.g) := by
  rw [Subobject.le_iff_factors]
  have hfac : (kernelSubobject S₂.g).Factors ((kernelSubobject S₁.g).arrow ≫ φ.τ₂) := by
    rw [kernelSubobject_factors_iff, Category.assoc, φ.comm₂₃, ← Category.assoc,
      kernelSubobject_arrow_comp, zero_comp]
  let v := (Subobject.isPullback φ.τ₂ (kernelSubobject S₂.g)).lift
    ((kernelSubobject S₂.g).factorThru _ hfac) (kernelSubobject S₁.g).arrow
    (Subobject.factorThru_arrow _ _ _)
  have hv : v ≫ ((Subobject.pullback φ.τ₂).obj (kernelSubobject S₂.g)).arrow =
      (kernelSubobject S₁.g).arrow :=
    (Subobject.isPullback φ.τ₂ (kernelSubobject S₂.g)).lift_snd _ _ _
  rw [← hv]
  exact Subobject.factors_comp_arrow v

/-- The morphism induced on `homologyPresentation` by `φ : S₁ ⟶ S₂` agrees with
`ShortComplex.homologyMap φ`. -/
lemma descMap_homologyPresentation {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hB : (Subobject.exists φ.τ₂).obj S₁.homologyPresentation.B ≤ S₂.homologyPresentation.B := by
      simpa using exists_imageSubobject_f_le φ)
    (hZ : S₁.homologyPresentation.Z ≤ (Subobject.pullback φ.τ₂).obj S₂.homologyPresentation.Z := by
      simpa using kernelSubobject_g_le_pullback φ) :
    S₁.homologyPresentation.descMap S₂.homologyPresentation φ.τ₂ hB hZ =
      ShortComplex.homologyMap φ := by
  let h₁ := subquotientLeftHomologyData S₁
  let h₂ := subquotientLeftHomologyData S₂
  let u₁ : h₁.K ⟶ (S₁.homologyPresentation.Z : C) :=
    Subobject.ofLE _ _ (homologyPresentation_Z S₁).symm.le
  let v₂ : (S₂.homologyPresentation.Z : C) ⟶ h₂.K :=
    Subobject.ofLE _ _ (homologyPresentation_Z S₂).le
  let φK : h₁.K ⟶ h₂.K :=
    u₁ ≫ S₁.homologyPresentation.mapZ S₂.homologyPresentation φ.τ₂ hZ ≫ v₂
  have commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂ := by
    dsimp only [φK, u₁, v₂, h₁, h₂, subquotientLeftHomologyData]
    rw [Category.assoc, Category.assoc, Subobject.ofLE_arrow,
      S₁.homologyPresentation.mapZ_arrow S₂.homologyPresentation φ.τ₂ hZ,
      Subobject.ofLE_arrow_assoc]
  let γ : LeftHomologyMapData φ h₁ h₂ :=
    { φK := φK
      φH := h₁.homologyIso.inv ≫
        S₁.homologyPresentation.descMap S₂.homologyPresentation φ.τ₂ hB hZ ≫ h₂.homologyIso.hom
      commi := commi
      commf' := LeftHomologyMapData.commf'_of_commi h₁ h₂ commi
      commπ := by
        have hπ₁ : h₁.π ≫ h₁.homologyIso.inv = u₁ ≫ S₁.homologyPresentation.π := by
          rw [homologyPresentation_π]
          dsimp only [u₁]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl, Category.id_comp]
        have hπ₂ : S₂.homologyPresentation.π ≫ h₂.homologyIso.hom = v₂ ≫ h₂.π := by
          rw [homologyPresentation_π, Category.assoc, Category.assoc, Iso.inv_hom_id,
            Category.comp_id]
        rw [← Category.assoc, hπ₁, Category.assoc,
          S₁.homologyPresentation.π_comp_descMap_assoc S₂.homologyPresentation φ.τ₂ hB hZ, hπ₂]
        simp only [φK, Category.assoc] }
  rw [γ.homologyMap_eq]
  simp [γ]

/-- When `S.g = 0`, transporting the identity presentation of `S.X₂` along an isomorphism
`e : S.X₂ ≅ S.homology` satisfying `S.iCycles ≫ e.hom = S.homologyπ` yields
`S.homologyPresentation`. -/
lemma refl_transIso_eq_homologyPresentation (S : ShortComplex C) (hg : S.g = 0)
    (e : S.X₂ ≅ S.homology) (he : S.iCycles ≫ e.hom = S.homologyπ) :
    (TauCeti.SubquotientPresentation.refl S.X₂).transIso e = S.homologyPresentation := by
  have hZ : ((TauCeti.SubquotientPresentation.refl S.X₂).transIso e).Z =
      S.homologyPresentation.Z := by
    rw [TauCeti.SubquotientPresentation.transIso_Z, TauCeti.SubquotientPresentation.refl_Z,
      homologyPresentation_Z, hg, kernelSubobject_zero]
  refine TauCeti.SubquotientPresentation.ext hZ ?_
  rw [homologyPresentation_π, TauCeti.SubquotientPresentation.transIso_π,
    TauCeti.SubquotientPresentation.refl_π,
    (subquotientLeftHomologyData S).π_comp_homologyIso_inv, ← he]
  simp only [← Category.assoc]
  congr 1
  rw [Category.assoc, (subquotientLeftHomologyData S).cyclesIso_inv_comp_iCycles]
  dsimp only [subquotientLeftHomologyData]
  rw [Subobject.ofLE_arrow, Category.assoc, Subobject.ofLE_arrow, Subobject.ofLE_arrow]

end CategoryTheory.ShortComplex
