/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.ShortComplex.Subquotient

/-!
# Subquotient presentation of the homology of a homological complex

For a homological complex `K : HomologicalComplex C c` in an abelian category `C` and a degree
`i : ι`, `K.homologyPresentation i` presents `K.homology i` as the subquotient
`kernelSubobject (K.dFrom i) / imageSubobject (K.dTo i)` of `K.X i`, compatible with morphisms of
complexes (`HomologicalComplex.descMap_homologyPresentation`) and with
`HomologicalComplex.XIsoHomologyOfDEqZero` when the differentials into and out of `i` vanish
(`HomologicalComplex.refl_transIso_eq_homologyPresentation`).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] {c : ComplexShape ι}

section ZeroMorphisms

variable [HasZeroMorphisms C] (K : HomologicalComplex C c)

/-- The differential out of degree `i` vanishes if and only if all differentials `K.d i j` out of
`i` vanish. -/
lemma dFrom_eq_zero_iff (i : ι) : K.dFrom i = 0 ↔ ∀ j, K.d i j = 0 := by
  refine ⟨fun h j ↦ ?_, fun h ↦ h (c.next i)⟩
  by_cases hr : c.Rel i j
  · rw [← K.dFrom_comp_xNextIso hr, h, zero_comp]
  · exact K.shape i j hr

/-- The differential into degree `j` vanishes if and only if all differentials `K.d i j` into `j`
vanish. -/
lemma dTo_eq_zero_iff (j : ι) : K.dTo j = 0 ↔ ∀ i, K.d i j = 0 := by
  refine ⟨fun h i ↦ ?_, fun h ↦ h (c.prev j)⟩
  by_cases hr : c.Rel i j
  · rw [← K.xPrevIso_comp_dTo hr, h, comp_zero]
  · exact K.shape i j hr

end ZeroMorphisms

section Abelian

variable [Abelian C]

/-- The canonical presentation of `K.homology i` as the subquotient
`kernelSubobject (K.dFrom i) / imageSubobject (K.dTo i)` of `K.X i`. -/
noncomputable def homologyPresentation (K : HomologicalComplex C c) (i : ι) :
    TauCeti.SubquotientPresentation (K.X i) (K.homology i) :=
  (K.sc i).homologyPresentation

@[simp]
lemma homologyPresentation_B (K : HomologicalComplex C c) (i : ι) :
    (K.homologyPresentation i).B = imageSubobject (K.dTo i) := by
  simp [homologyPresentation]

@[simp]
lemma homologyPresentation_Z (K : HomologicalComplex C c) (i : ι) :
    (K.homologyPresentation i).Z = kernelSubobject (K.dFrom i) := by
  simp [homologyPresentation]

lemma exists_homologyPresentation_B_le {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι) :
    (Subobject.exists (φ.f i)).obj (K.homologyPresentation i).B ≤
      (L.homologyPresentation i).B := by
  simpa [homologyPresentation] using
    ShortComplex.exists_imageSubobject_f_le ((shortComplexFunctor C c i).map φ)

lemma homologyPresentation_Z_le_pullback {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι) :
    (K.homologyPresentation i).Z ≤
      (Subobject.pullback (φ.f i)).obj (L.homologyPresentation i).Z := by
  simpa [homologyPresentation] using
    ShortComplex.kernelSubobject_g_le_pullback ((shortComplexFunctor C c i).map φ)

/-- The morphism induced on `homologyPresentation i` by a morphism of complexes `φ : K ⟶ L` is
`HomologicalComplex.homologyMap φ i`. -/
lemma descMap_homologyPresentation {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι)
    (hB : (Subobject.exists (φ.f i)).obj (K.homologyPresentation i).B ≤
      (L.homologyPresentation i).B := exists_homologyPresentation_B_le φ i)
    (hZ : (K.homologyPresentation i).Z ≤
      (Subobject.pullback (φ.f i)).obj (L.homologyPresentation i).Z :=
      homologyPresentation_Z_le_pullback φ i) :
    (K.homologyPresentation i).descMap (L.homologyPresentation i) (φ.f i) hB hZ =
      homologyMap φ i :=
  ShortComplex.descMap_homologyPresentation ((shortComplexFunctor C c i).map φ) hB hZ

/-- When `K.dTo i = 0` and `K.dFrom i = 0`, `K.homologyPresentation i` is obtained by transporting
the identity presentation of `K.X i` along `K.XIsoHomologyOfDEqZero i`. -/
lemma refl_transIso_eq_homologyPresentation (K : HomologicalComplex C c) (i : ι)
    (h₁ : K.dTo i = 0) (h₂ : K.dFrom i = 0) :
    (TauCeti.SubquotientPresentation.refl (K.X i)).transIso (K.XIsoHomologyOfDEqZero i h₁ h₂) =
      K.homologyPresentation i := by
  refine (K.sc i).refl_transIso_eq_homologyPresentation h₂ (K.XIsoHomologyOfDEqZero i h₁ h₂) ?_
  rw [XIsoHomologyOfDEqZero_hom]
  exact iCyclesIso_hom_inv_id_assoc K i (c.next i) rfl h₂ (K.homologyπ i)

end Abelian

end HomologicalComplex
