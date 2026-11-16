/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.KanExtension
public import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete

import TauCeti.RingTheory.Huber.PowerBounded

/-!
# Sections of the structure presheaf on rational opens of a discrete Huber pair

Let `A` be a commutative ring with the discrete topology, `P` any pair of definition of `A`, and
`A⁺` any subring of `A`. Every element of `A` is power-bounded (`powerBoundedSubring_eq_top`), and
every finite subset generates an open ideal, so every pair `(T, s)` presents the rational open
`R(T/s) ⊆ Spa(A, A⁺)` and satisfies `HasDenominatorPower`
(`TauCeti.Huber.PairOfDefinition.hasDenominatorPower_of_discreteTopology`). Because the
localisation topology on `Aₛ` is discrete, no completion occurs (`A⟨T/s⟩ ≃+* Aₛ`), and the value of
the presentation-limit structure presheaf on `R(T/s)` is canonically the algebraic localisation of
`A` away from `s`, equipped with the discrete topology.

Equipping `A` with the discrete uniformity of its additive group makes `A` complete and Hausdorff,
so `TauCeti.ValuationSpectrum.toPresentationLimit` furnishes a canonical `A`-algebra structure on
`presentationLimit Aplus V` for every open `V ⊆ Spa(A, A⁺)`, compatible with restriction morphisms
(`TauCeti.ValuationSpectrum.presentationLimitMapAlgHom`). Over `R(T/s)`, the resulting `A`-algebra
is canonically isomorphic to any localisation `S` of `A` away from `s`
(`TauCeti.ValuationSpectrum.presentationLimitRationalAlgEquivOfDiscreteTopology`), and is itself an
`IsLocalization.Away s` algebra over `A`
(`TauCeti.ValuationSpectrum.isLocalization_away_presentationLimit_spaBasicOpen`). Under these
identifications, restriction along an inclusion `R(T'/s') ⊆ R(T/s)` is the algebraic localisation
lift (`TauCeti.ValuationSpectrum.presentationLimitRationalAlgEquivOfDiscreteTopology_map`), and a
rational open of denominator `s * g` inside `R(T/s)` has coordinate ring localised away from `g`
over the coordinate ring of `R(T/s)`
(`TauCeti.ValuationSpectrum.isLocalization_away_presentationLimit_spaBasicOpen_of_mul`).

## Main definitions

* `TauCeti.ValuationSpectrum.toPresentationLimitOfDiscreteTopology` : the canonical ring
  homomorphism `A →+* presentationLimit Aplus V` over a discrete ring `A`.
* `TauCeti.ValuationSpectrum.presentationLimitMapAlgHom` : the restriction map
  `presentationLimit Aplus V →ₐ[A] presentationLimit Aplus U` as an `A`-algebra homomorphism.
* `TauCeti.ValuationSpectrum.presentationLimitRationalAlgEquivOfDiscreteTopology` : the canonical
  `A`-algebra equivalence `presentationLimit Aplus (spaBasicOpen Aplus T s) ≃ₐ[A] S` for any
  localisation `S` of `A` away from `s`.

## Main results

* `TauCeti.ValuationSpectrum.discreteTopology_presentationLimit_of_mem_spaRationalOpens` : sections
  of `presentationLimit` over a rational open carry the discrete topology.
* `TauCeti.ValuationSpectrum.isLocalization_away_presentationLimit_spaBasicOpen` :
  `presentationLimit Aplus (spaBasicOpen Aplus T s)` is a localisation of `A` away from `s`.
* `TauCeti.ValuationSpectrum.presentationLimitRationalAlgEquivOfDiscreteTopology_map` : under
  `presentationLimitRationalAlgEquivOfDiscreteTopology`, restriction between rational opens is the
  canonical localisation lift.
* `TauCeti.ValuationSpectrum.isLocalization_away_presentationLimit_spaBasicOpen_of_mul` : for a
  rational open `U = R(T'/(s * g))` contained in `W = R(T/s)`, `presentationLimit Aplus U` is a
  localisation away from the image of `g` over `presentationLimit Aplus W`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51,
  §8.1, and Theorem 8.28(c).
-/

public section

open CategoryTheory TopologicalSpace Opposite TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- Over a discrete ring, every element of any subring `A⁺` is power-bounded. -/
theorem isPowerBounded_of_mem_of_discreteTopology {Aplus : Subring A} :
    ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a :=
  fun _ _ ↦ mem_powerBoundedSubring.mp (by simp)

/-! ### Discrete topology on sections over rational opens -/

/-- Over a discrete ring `A`, the sections of `presentationLimit` over `R(T/s)` carry the discrete
topology. -/
theorem discreteTopology_presentationLimit_spaBasicOpen (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) :
    DiscreteTopology (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) := by
  have hden := hasDenominatorPower_of_discreteTopology P T s (Localization.Away s)
  let p : Presentation P := ⟨T, s, hden⟩
  let _ := locUniformSpace P T s (Localization.Away s) hden
  have _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  have _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  have _ := discreteTopology_completion_locUniformSpace P T s (Localization.Away s) hden
  let iso : (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)).obj ≅
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away s)) :=
    TopCommRingCat.isCompleteSeparated.ι.mapIso
      (presentationLimitRationalIso Aplus isPowerBounded_of_mem_of_discreteTopology p
        (isOpen_discrete _)) ≪≫
      eqToIso (completionLocObj_obj P T s (Localization.Away s) hden)
  let e : ↥(presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)).obj ≃ₜ
      UniformSpace.Completion (Localization.Away s) :=
    TopCat.homeoOfIso ((forget₂ TopCommRingCat TopCat).mapIso iso)
  exact e.isEmbedding.discreteTopology

/-- Over a discrete ring `A`, the sections of `presentationLimit` over any rational open
`W ∈ spaRationalOpens Aplus` carry the discrete topology. -/
theorem discreteTopology_presentationLimit_of_mem_spaRationalOpens (P : PairOfDefinition A)
    {Aplus : Subring A} {W : Opens ↥(spa Aplus)} (hW : W ∈ spaRationalOpens Aplus) :
    DiscreteTopology (presentationLimit (P := P) Aplus W) := by
  obtain ⟨T, s, -, hWT⟩ := mem_spaRationalFamily_iff.mp (mem_spaRationalOpens.mp hW)
  obtain rfl : W = spaBasicOpen Aplus T s :=
    Opens.ext (hWT.trans (Set.ext fun _ ↦ mem_spaBasicOpen.symm))
  exact discreteTopology_presentationLimit_spaBasicOpen P Aplus T s

/-- Over a discrete ring `A`, the value of `presentationLimitPresheaf` on any rational open carries
the discrete topology. -/
theorem discreteTopology_presentationLimitPresheaf_obj_of_mem_spaRationalOpens
    (P : PairOfDefinition A) {Aplus : Subring A} {W : Opens ↥(spa Aplus)}
    (hW : W ∈ spaRationalOpens Aplus) :
    DiscreteTopology ((presentationLimitPresheaf P Aplus).obj (op W)).obj := by
  rw [presentationLimitPresheaf_obj]
  exact discreteTopology_presentationLimit_of_mem_spaRationalOpens P hW

/-! ### The canonical `A`-algebra structure on sections -/

/-- **The canonical ring homomorphism `A →+* presentationLimit Aplus V` over a discrete ring.**
Equipping `A` with the additive-group uniformity of its discrete topology makes `A` complete and
Hausdorff, so `TauCeti.ValuationSpectrum.toPresentationLimit` applies without completeness or
uniformity assumptions on `A`. -/
noncomputable def toPresentationLimitOfDiscreteTopology (P : PairOfDefinition A)
    (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    A →+* presentationLimit (P := P) Aplus V := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have _ : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  exact (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
      (toPresentationLimit (P := P) Aplus V).hom :
    TopCommRingCat.of A ⟶ (presentationLimit (P := P) Aplus V).obj).1

/-- Over a discrete ring `A`, sections of `presentationLimit` over any open `V` form an `A`-algebra
via `toPresentationLimitOfDiscreteTopology`. -/
noncomputable instance instAlgebraPresentationLimitOfDiscreteTopology (P : PairOfDefinition A)
    (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    Algebra A (presentationLimit (P := P) Aplus V) :=
  (toPresentationLimitOfDiscreteTopology P Aplus V).toAlgebra

theorem algebraMap_presentationLimit_eq (P : PairOfDefinition A) (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) :
    algebraMap A (presentationLimit (P := P) Aplus V) =
      toPresentationLimitOfDiscreteTopology P Aplus V := by
  rfl

/-- Restriction of `presentationLimit` along `U ≤ V` commutes with
`toPresentationLimitOfDiscreteTopology`. -/
@[simp]
theorem presentationLimitMap_comp_toPresentationLimitOfDiscreteTopology (P : PairOfDefinition A)
    {Aplus : Subring A} {U V : Opens ↥(spa Aplus)} (h : U ≤ V) :
    (presentationLimitMap (P := P) h).hom.1.comp
        (toPresentationLimitOfDiscreteTopology P Aplus V) =
      toPresentationLimitOfDiscreteTopology P Aplus U := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have _ : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  have hmap := congrArg TopCommRingCat.isCompleteSeparated.ι.map
    (toPresentationLimit_comp_presentationLimitMap (P := P) Aplus h)
  have hcomp :
      (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
          (toPresentationLimit (P := P) Aplus V).hom) ≫ (presentationLimitMap (P := P) h).hom =
        eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
          (toPresentationLimit (P := P) Aplus U).hom := by
    rw [Category.assoc]
    exact congrArg (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫ ·) hmap
  exact congrArg Subtype.val hcomp

/-- **The restriction map `presentationLimit Aplus V →ₐ[A] presentationLimit Aplus U` as an
`A`-algebra homomorphism**, over a discrete ring `A`. -/
noncomputable def presentationLimitMapAlgHom (P : PairOfDefinition A) {Aplus : Subring A}
    {U V : Opens ↥(spa Aplus)} (h : U ≤ V) :
    presentationLimit (P := P) Aplus V →ₐ[A] presentationLimit (P := P) Aplus U :=
  { (presentationLimitMap (P := P) h).hom.1 with
    commutes' := fun a ↦
      RingHom.congr_fun (presentationLimitMap_comp_toPresentationLimitOfDiscreteTopology P h) a }

@[simp]
theorem coe_presentationLimitMapAlgHom (P : PairOfDefinition A) {Aplus : Subring A}
    {U V : Opens ↥(spa Aplus)} (h : U ≤ V) :
    (presentationLimitMapAlgHom P h :
      presentationLimit (P := P) Aplus V →+* presentationLimit (P := P) Aplus U) =
      (presentationLimitMap (P := P) h).hom.1 := by
  rfl

@[simp]
theorem presentationLimitMapAlgHom_apply (P : PairOfDefinition A) {Aplus : Subring A}
    {U V : Opens ↥(spa Aplus)} (h : U ≤ V) (x : presentationLimit (P := P) Aplus V) :
    presentationLimitMapAlgHom P h x = (presentationLimitMap (P := P) h).hom.1 x := by
  rfl

@[simp]
theorem presentationLimitMapAlgHom_id (P : PairOfDefinition A) (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) :
    presentationLimitMapAlgHom P (le_refl V) =
      AlgHom.id A (presentationLimit (P := P) Aplus V) := by
  ext x
  rw [presentationLimitMapAlgHom_apply, presentationLimitMap_refl]
  rfl

@[simp]
theorem presentationLimitMapAlgHom_comp (P : PairOfDefinition A) {Aplus : Subring A}
    {U V W : Opens ↥(spa Aplus)} (hUV : U ≤ V) (hVW : V ≤ W) :
    (presentationLimitMapAlgHom P hUV).comp (presentationLimitMapAlgHom P hVW) =
      presentationLimitMapAlgHom P (hUV.trans hVW) := by
  ext x
  exact presentationLimitMap_apply_presentationLimitMap_apply hVW hUV x

/-! ### Identification with algebraic localisations on rational opens -/

/-- Compatibility of the rational presentation isomorphism with the canonical map from `A`, over a
discrete ring `A`. -/
private theorem toPresentationLimit_comp_presentationLimitRationalIso_eq (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower (↑T) s (Localization.Away s)) :
    let p : Presentation P := ⟨T, s, hden⟩
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    haveI : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
    letI := locUniformSpace P T s (Localization.Away s) hden
    haveI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    haveI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
        (toPresentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)).hom) ≫
      (TopCommRingCat.isCompleteSeparated.ι.mapIso
        (presentationLimitRationalIso Aplus isPowerBounded_of_mem_of_discreteTopology p
          (isOpen_discrete _)) ≪≫
        eqToIso (completionLocObj_obj P T s (Localization.Away s) hden)).hom =
      (⟨toCompletionLoc P T s (Localization.Away s) hden,
          continuous_toCompletionLoc P T s (Localization.Away s) hden⟩ :
        TopCommRingCat.of A ⟶
          TopCommRingCat.of (UniformSpace.Completion (Localization.Away s))) := by
  let p : Presentation P := ⟨T, s, hden⟩
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have _ : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ := locUniformSpace P T s (Localization.Away s) hden
  have _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  have _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  have h₁ := congrArg TopCommRingCat.isCompleteSeparated.ι.map
    (toPresentationLimit_comp_πToPresentation (P := P) Aplus (spaBasicOpen Aplus T s)
      ⟨p, isOpen_discrete _, le_rfl⟩)
  rw [Functor.map_comp] at h₁
  have h₂ : p.toCompletionLocObjHom.hom = _ := Presentation.toCompletionLocObjHom_hom p
  dsimp only [Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom]
  rw [presentationLimitRationalIso_hom, Category.assoc (eqToHom _),
    ← Category.assoc (toPresentationLimit _ _).hom]
  -- `TopCommRingCat.isCompleteSeparated.ι.map` is `.hom` on morphisms of the full subcategory.
  change eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
      (TopCommRingCat.isCompleteSeparated.ι.map
          (toPresentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) ≫
        TopCommRingCat.isCompleteSeparated.ι.map
          (presentationLimitπToPresentation Aplus (spaBasicOpen Aplus T s)
            ⟨p, isOpen_discrete _, le_rfl⟩)) ≫
      eqToHom (completionLocObj_obj P T s (Localization.Away s) hden) = _
  rw [h₁]
  -- Express `ι.map p.toCompletionLocObjHom` as `p.toCompletionLocObjHom`s `.hom` for `h₂`.
  change eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
      p.toCompletionLocObjHom.hom ≫
      eqToHom (completionLocObj_obj P T s (Localization.Away s) hden) = _
  rw [h₂]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc,
    Category.id_comp]
  rfl

/-- **Over a discrete ring `A`, `presentationLimit Aplus (spaBasicOpen Aplus T s) ≃ₐ[A] S`** for
any localisation `S` of `A` away from `s`. On `R(T/s)` the presentation limit is the completed
localisation `A⟨T/s⟩`, which is discrete (`completionLocEquivOfDiscreteTopology`) and therefore
agrees with the algebraic localisation `Aₛ`. -/
noncomputable def presentationLimitRationalAlgEquivOfDiscreteTopology (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] :
    presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃ₐ[A] S := by
  have hden := hasDenominatorPower_of_discreteTopology P T s (Localization.Away s)
  let p : Presentation P := ⟨T, s, hden⟩
  let _ := locUniformSpace P T s (Localization.Away s) hden
  have _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  have _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  let iso : (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)).obj ≅
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away s)) :=
    TopCommRingCat.isCompleteSeparated.ι.mapIso
      (presentationLimitRationalIso Aplus isPowerBounded_of_mem_of_discreteTopology p
        (isOpen_discrete _)) ≪≫
      eqToIso (completionLocObj_obj P T s (Localization.Away s) hden)
  let e₁ : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃+*
      UniformSpace.Completion (Localization.Away s) :=
    ((forget₂ TopCommRingCat CommRingCat).mapIso iso).commRingCatIsoToRingEquiv
  let e : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃+* S :=
    e₁.trans ((completionLocEquivOfDiscreteTopology P T s (Localization.Away s) hden).symm.trans
      (IsLocalization.algEquiv (.powers s) (Localization.Away s) S).toRingEquiv)
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  have hproj := toPresentationLimit_comp_presentationLimitRationalIso_eq P Aplus T s hden
  have he₁ : e₁ (algebraMap A (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) a) =
      (algebraMap A (Localization.Away s) a : UniformSpace.Completion (Localization.Away s)) :=
    (RingHom.congr_fun (congrArg Subtype.val hproj) a).trans
      (toCompletionLoc_apply P T s (Localization.Away s) hden a)
  rw [RingEquiv.trans_apply, he₁, RingEquiv.trans_apply,
    completionLocEquivOfDiscreteTopology_symm_coe]
  exact (IsLocalization.algEquiv (.powers s) (Localization.Away s) S).commutes a

/-- **Over a discrete ring `A`, `presentationLimit Aplus (spaBasicOpen Aplus T s)` is an algebraic
localisation of `A` away from `s`.** -/
theorem isLocalization_away_presentationLimit_spaBasicOpen (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) :
    IsLocalization.Away s (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) :=
  IsLocalization.isLocalization_of_algEquiv (.powers s)
    (presentationLimitRationalAlgEquivOfDiscreteTopology P Aplus T s (Localization.Away s)).symm

/-- **Under `presentationLimitRationalAlgEquivOfDiscreteTopology`, restriction between rational
opens is the algebraic localisation lift.** If `R(T'/s') ⊆ R(T/s)`, the image of `s` in `S'` is a
unit (`isUnit_algebraMap_of_rationalSubset_subset`), and the restriction map of `presentationLimit`
is the unique `A`-algebra homomorphism `S →ₐ[A] S'`. -/
theorem presentationLimitRationalAlgEquivOfDiscreteTopology_map (P : PairOfDefinition A)
    {Aplus : Subring A} {T T' : Finset A} {s s' : A}
    (h : spaBasicOpen Aplus T' s' ≤ spaBasicOpen Aplus T s)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S'] :
    (presentationLimitRationalAlgEquivOfDiscreteTopology P Aplus T' s'
        S').toRingEquiv.toRingHom.comp
      ((presentationLimitMap (P := P) h).hom.1.comp
        (presentationLimitRationalAlgEquivOfDiscreteTopology P Aplus T s
          S).symm.toRingEquiv.toRingHom) =
      IsLocalization.Away.lift s (isUnit_algebraMap_of_rationalSubset_subset S'
        (fun _ _ ↦ isOpen_discrete _) (spaBasicOpen_le_spaBasicOpen_iff.mp h)) := by
  let e := presentationLimitRationalAlgEquivOfDiscreteTopology P Aplus T s S
  let e' := presentationLimitRationalAlgEquivOfDiscreteTopology P Aplus T' s' S'
  apply IsLocalization.ringHom_ext (.powers s)
  ext a
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_toRingEquiv, ← presentationLimitMapAlgHom_apply, IsLocalization.Away.lift_eq]
  rw [← e.commutes a]
  -- `e.symm.toRingEquiv` is `(e.symm : S → presentationLimit ...)`, which cancels `e`.
  change e' (presentationLimitMapAlgHom P h (e.symm (e (algebraMap A _ a)))) = algebraMap A S' a
  rw [e.symm_apply_apply, (presentationLimitMapAlgHom P h).commutes a, e'.commutes a]

@[simp]
theorem presentationLimitRationalAlgEquivOfDiscreteTopology_map_symm_apply (P : PairOfDefinition A)
    {Aplus : Subring A} {T T' : Finset A} {s s' : A}
    (h : spaBasicOpen Aplus T' s' ≤ spaBasicOpen Aplus T s)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S'] (x : S) :
    presentationLimitRationalAlgEquivOfDiscreteTopology P Aplus T' s' S'
        ((presentationLimitMap (P := P) h).hom.1
          ((presentationLimitRationalAlgEquivOfDiscreteTopology P Aplus T s S).symm x)) =
      IsLocalization.Away.lift s (isUnit_algebraMap_of_rationalSubset_subset S'
        (fun _ _ ↦ isOpen_discrete _) (spaBasicOpen_le_spaBasicOpen_iff.mp h)) x :=
  RingHom.congr_fun (presentationLimitRationalAlgEquivOfDiscreteTopology_map P h S S') x

/-- **Relative localisation of coordinate rings on nested rational opens.** Over a discrete ring
`A`, if `U = R(T'/(s * g))` is contained in `W = R(T/s)`, then `presentationLimit Aplus U`, viewed
as an algebra over `presentationLimit Aplus W` via `presentationLimitMapAlgHom`, is an algebraic
localisation away from the image of `g`. -/
theorem isLocalization_away_presentationLimit_spaBasicOpen_of_mul (P : PairOfDefinition A)
    {Aplus : Subring A} {T T' : Finset A} {s g : A}
    (h : spaBasicOpen Aplus T' (s * g) ≤ spaBasicOpen Aplus T s) :
    letI : Algebra (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s))
        (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T' (s * g))) :=
      (presentationLimitMapAlgHom P h).toRingHom.toAlgebra
    IsLocalization.Away
      (algebraMap A (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) g)
      (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T' (s * g))) := by
  let R_W := presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)
  let R_U := presentationLimit (P := P) Aplus (spaBasicOpen Aplus T' (s * g))
  let _ : Algebra R_W R_U := (presentationLimitMapAlgHom P h).toRingHom.toAlgebra
  have _ : IsScalarTower A R_W R_U := IsScalarTower.of_algebraMap_eq'
    (presentationLimitMapAlgHom P h).comp_algebraMap.symm
  have _ : IsLocalization.Away s R_W :=
    isLocalization_away_presentationLimit_spaBasicOpen P Aplus T s
  have _ : IsLocalization.Away (s * g) R_U :=
    isLocalization_away_presentationLimit_spaBasicOpen P Aplus T' (s * g)
  let Q := Localization.Away (algebraMap A R_W g)
  let eA : Q ≃ₐ[A] R_U := IsLocalization.algEquiv (.powers (s * g)) Q R_U
  have hcomm : (eA.toRingEquiv.toRingHom).comp (algebraMap R_W Q) = algebraMap R_W R_U := by
    apply IsLocalization.ringHom_ext (.powers s)
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv]
    rw [← IsScalarTower.algebraMap_apply A R_W Q a, eA.commutes a,
      ← IsScalarTower.algebraMap_apply A R_W R_U a]
  let eRW : Q ≃ₐ[R_W] R_U :=
    AlgEquiv.ofRingEquiv (f := eA.toRingEquiv) (RingHom.congr_fun hcomm)
  exact IsLocalization.isLocalization_of_algEquiv (.powers (algebraMap A R_W g)) eRW

end TauCeti.ValuationSpectrum
