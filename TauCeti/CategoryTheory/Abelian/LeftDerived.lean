/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Resolution
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.CategoryTheory.ObjectProperty.Homology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import TauCeti.Algebra.Homology.HomotopyCategory.PreservesHomology
import TauCeti.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Left derived functors on short exact sequences and compositions

Let `S : 0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` be a short exact sequence in an abelian category with `P₁` and
`P₀` projective. Then `⋯ ⟶ 0 ⟶ P₁ ⟶ P₀` is a projective resolution of `M`
(`CategoryTheory.ShortComplex.ShortExact.projectiveResolution`), and for every additive functor
`F` it computes the left derived functors of `F` at `M`:

* `L₁F(M)` is the kernel of `F(P₁) ⟶ F(P₀)`
  (`CategoryTheory.ShortComplex.ShortExact.leftDerivedOneIsoKernel`);
* `LₙF(M)` vanishes for `n ≥ 2`
  (`CategoryTheory.ShortComplex.ShortExact.isZero_leftDerived_add_two`).

The complex, its augmentation, and the chain maps induced by morphisms of short complexes are
constructed in `TauCeti.Algebra.Homology.ShortComplex.Resolution` for any category with zero
morphisms and a zero object.

The identification of `L₁F(M)` is natural in the functor `F` and in maps of such presentations.
For an arbitrary additive `F` the projectivity of `P₁` is needed even in degree `1`: the long exact
sequence only gives `L₁F(M) ≅ ker(L₀F(P₁) ⟶ F(P₀))`, and `L₀F(P₁) = F(P₁)` for projective `P₁`.
Over a principal ideal domain every module has such a presentation, by a free module and its
kernel, which is again free; applied to the tensor product, this computes `Tor₁` in the Künneth
and universal coefficient theorems.

More generally, when only `X₂` is projective in a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`,
prepending `X₂` to a projective resolution of `X₁` gives a projective resolution of `X₃` and
therefore shifts left derived functors in degrees at least two: `L_{n+2}F(X₃) ≅ L_{n+1}F(X₁)`
(`CategoryTheory.ShortComplex.ShortExact.leftDerivedAddTwoIso`). When `F` is right exact,
`L₁F(X₃)` vanishes precisely when `F(X₁) ⟶ F(X₂)` is a monomorphism, equivalently when `F` sends
the short exact sequence to a short exact sequence
(`CategoryTheory.ShortComplex.ShortExact.mono_map_f_iff_isZero_leftDerived_one`,
`CategoryTheory.ShortComplex.ShortExact.shortExact_map_iff_isZero_leftDerived_one`).

The file also records general functoriality facts. The natural transformation `LₙF ⟶ LₙG` induced
by `α : F ⟶ G` is additive in `α` (`CategoryTheory.NatTrans.leftDerived_add`), and natural
isomorphisms induce natural isomorphisms of left derived functors
(`CategoryTheory.NatIso.leftDerived`). In degree zero, `NatTrans.leftDerived` is compatible with
the comparison maps `L₀F ⟶ F` and `L₀G ⟶ G`
(`CategoryTheory.NatTrans.leftDerived_zero_comp_fromLeftDerivedZero`). Postcomposing with an exact
additive functor `G` commutes with left derived functors
(`CategoryTheory.Functor.leftDerivedCompIso`), and when `G` is also faithful it preserves and
reflects their vanishing (`CategoryTheory.Functor.isZero_leftDerived_comp_iff`). An exact additive
functor has no positive left derived functors (`CategoryTheory.Functor.isZero_leftDerived_succ`).
If an additive functor sends projective objects into a class closed under subobjects and quotients,
for instance a Serre class, all its left derived functors take values in that class
(`CategoryTheory.ObjectProperty.prop_leftDerived_obj`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4, for left derived functors
  computed from a projective resolution and dimension shifting.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {S S' : ShortComplex C}

namespace ShortComplex

/-- For a short exact `S`, the augmentation of `S.resolutionComplex` is a quasi-isomorphism. -/
lemma quasiIso_resolutionπ (hS : S.ShortExact) : _root_.QuasiIso S.resolutionπ := by
  refine ⟨fun n => ?_⟩
  obtain _ | _ | n := n
  · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    refine ⟨(ShortComplex.exact_iff_of_iso ?_).2 hS.exact, ?_⟩
    · refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, Iso.refl_hom,
          resolutionπ_f_zero]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    · simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, resolutionπ_f_zero]
      exact hS.epi_g
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    exact ShortComplex.exact_of_f_is_kernel _ <|
      KernelFork.IsLimit.ofMonoOfIsZero _ hS.mono_f (isZero_zero C)
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)

namespace ShortExact

variable (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- A short exact sequence `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` with `P₁` and `P₀` projective gives the
projective resolution `⋯ ⟶ 0 ⟶ P₁ ⟶ P₀` of `M`, with `P₀` in degree `0`. -/
@[expose]
def projectiveResolution : ProjectiveResolution S.X₃ where
  complex := S.resolutionComplex
  projective n := by
    obtain _ | _ | n := n
    · exact inferInstanceAs (Projective S.X₂)
    · exact inferInstanceAs (Projective S.X₁)
    · exact inferInstanceAs (Projective (0 : C))
  π := S.resolutionπ
  quasiIso := quasiIso_resolutionπ hS

/-- The complex of the resolution is `S.resolutionComplex`. -/
@[simp]
lemma projectiveResolution_complex : hS.projectiveResolution.complex = S.resolutionComplex :=
  (rfl)

/-- The augmentation of the resolution is `S.resolutionπ`. -/
@[simp]
lemma projectiveResolution_π : hS.projectiveResolution.π = S.resolutionπ :=
  (rfl)

variable {D : Type*} [Category* D] [Abelian D] [HasProjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

include hS in
/-- The left derived functors of `F` vanish in degrees at least `2` on an object with a
projective presentation of length one. -/
lemma isZero_leftDerived_add_two (n : ℕ) : IsZero ((F.leftDerived (n + 2)).obj S.X₃) := by
  refine IsZero.of_iso ?_ (hS.projectiveResolution.isoLeftDerivedObj F (n + 2))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (S.isZero_resolutionComplex_X_add_two n))

omit [Projective S.X₁] [Projective S.X₂] [HasProjectiveResolutions C] in
/-- No differential enters degree `1` of the mapped presentation complex. -/
private lemma mapHomologicalComplex_d_two_one :
    ((F.mapHomologicalComplex _).obj S.resolutionComplex).d 2 1 = 0 :=
  (F.map_isZero (S.isZero_resolutionComplex_X_add_two 0)).eq_of_src _ _

/-- Homology in degree `1` of the mapped presentation consists of its cycles. -/
private abbrev resolutionHomologyOneIsoCycles :
    ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).cycles 1 ≅
      ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).homology 1 :=
  ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).isoHomologyπ
    2 1 (by simp) (mapHomologicalComplex_d_two_one F)

/-- The map `L₁F(M) ⟶ F(P₁)` computed on `F` applied to the resolution: the class in degree `1`
of a cycle goes to that cycle, since no nonzero differential enters degree `1`. -/
private def leftDerivedOneι :
    (F.leftDerived 1).obj S.X₃ ⟶
      ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).X 1 :=
  ((hS.projectiveResolution.isoLeftDerivedObj F 1).hom ≫
    (hS.resolutionHomologyOneIsoCycles F).inv) ≫
    ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).iCycles 1

private lemma leftDerivedOneι_comp :
    hS.leftDerivedOneι F ≫
      ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).d 1 0 = 0 := by
  rw [leftDerivedOneι, Category.assoc, HomologicalComplex.iCycles_d, Limits.comp_zero]

/-- `L₁F(M) ⟶ F(P₁)` is a kernel of `F(P₁) ⟶ F(P₀)`. -/
private def isLimitLeftDerivedOneι :
    IsLimit (KernelFork.ofι _ (hS.leftDerivedOneι_comp F)) :=
  IsKernel.isoKernel _ _
    (((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).cyclesIsKernel 1 0 (by simp))
    (hS.projectiveResolution.isoLeftDerivedObj F 1 ≪≫
      (hS.resolutionHomologyOneIsoCycles F).symm) rfl

/-- On an object with a projective presentation `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0`, the first left derived
functor of `F` is the kernel of `F(P₁) ⟶ F(P₀)`. It sends the homology class of a cycle of `F`
applied to the resolution to that cycle
(`homologyπ_comp_isoLeftDerivedObj_inv_comp_leftDerivedOneIsoKernel_hom_comp_ι`). -/
def leftDerivedOneIsoKernel : (F.leftDerived 1).obj S.X₃ ≅ kernel (F.map S.f) :=
  (hS.isLimitLeftDerivedOneι F).conePointUniqueUpToIso (limit.isLimit _)

/-- The identification of `L₁F(M)` with a kernel, followed by the inclusion into `F(P₁)`. -/
@[reassoc]
private lemma leftDerivedOneIsoKernel_hom_comp_ι :
    (hS.leftDerivedOneIsoKernel F).hom ≫ kernel.ι (F.map S.f) =
      (hS.projectiveResolution.isoLeftDerivedObj F 1).hom ≫
        (hS.resolutionHomologyOneIsoCycles F).inv ≫
        ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).iCycles 1 :=
  (IsLimit.conePointUniqueUpToIso_hom_comp (hS.isLimitLeftDerivedOneι F) (limit.isLimit _)
    WalkingParallelPair.zero).trans (Category.assoc _ _ _)

/-- The identification of `L₁F(M)` with the kernel of `F(P₁) ⟶ F(P₀)` sends the homology class
of a cycle of `F` applied to the resolution to that cycle. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_isoLeftDerivedObj_inv_comp_leftDerivedOneIsoKernel_hom_comp_ι :
    ((F.mapHomologicalComplex _).obj S.resolutionComplex).homologyπ 1 ≫
      (hS.projectiveResolution.isoLeftDerivedObj F 1).inv ≫
        (hS.leftDerivedOneIsoKernel F).hom ≫ kernel.ι (F.map S.f) =
      ((F.mapHomologicalComplex _).obj S.resolutionComplex).iCycles 1 := by
  rw [leftDerivedOneIsoKernel_hom_comp_ι]
  -- `homologyπ` lands in `homology`, while `isoLeftDerivedObj` lands in `homologyFunctor` applied
  -- to the complex. These agree only definitionally, so the cancellation needs `erw`, as in
  -- Mathlib's `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`.
  erw [Iso.inv_hom_id_assoc]
  exact HomologicalComplex.isoHomologyπ_hom_inv_id_assoc _ 2 1 (by simp)
    (mapHomologicalComplex_d_two_one F) _

variable {hS} {G : C ⥤ D} [G.Additive] (hS' : S'.ShortExact) [Projective S'.X₁] [Projective S'.X₂]

include hS' in
/-- A morphism between first left derived functors which is computed on the resolutions by a
chain map `ψ` acts on the kernels by the degree `1` component of `ψ`. -/
private lemma comp_leftDerivedOneIsoKernel_hom_comp_ι
    (ψ : (F.mapHomologicalComplex _).obj hS.projectiveResolution.complex ⟶
      (G.mapHomologicalComplex _).obj hS'.projectiveResolution.complex)
    (m : (F.leftDerived 1).obj S.X₃ ⟶ (G.leftDerived 1).obj S'.X₃)
    (hm : m = (hS.projectiveResolution.isoLeftDerivedObj F 1).hom ≫
      (HomologicalComplex.homologyFunctor D _ 1).map ψ ≫
        (hS'.projectiveResolution.isoLeftDerivedObj G 1).inv) :
    m ≫ (hS'.leftDerivedOneIsoKernel G).hom ≫ kernel.ι (G.map S'.f) =
      ((hS.leftDerivedOneIsoKernel F).hom ≫ kernel.ι (F.map S.f)) ≫ ψ.f 1 := by
  subst hm
  rw [Category.assoc, Category.assoc, leftDerivedOneIsoKernel_hom_comp_ι,
    leftDerivedOneIsoKernel_hom_comp_ι]
  -- The cycle inclusions land in `F` applied to the resolution in degree `1` rather than in
  -- `F.obj S.X₁`, and `homologyFunctor` is only definitionally `homology`. The rewrites at these
  -- junctions therefore need `erw`, as in Mathlib's
  -- `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`, and the final reassociation is
  -- composed as a term.
  erw [Iso.inv_hom_id_assoc,
    HomologicalComplex.isoHomologyπ_inv_naturality_assoc ψ 2 1 (by simp)
      (mapHomologicalComplex_d_two_one F)
      (mapHomologicalComplex_d_two_one G),
    HomologicalComplex.cyclesMap_i]
  exact ((Category.assoc _ _ _).trans (_ ≫= Category.assoc _ _ _)).symm

omit [G.Additive] [Projective S'.X₁] [Projective S'.X₂] in
/-- The identification of `L₁F(M)` with the kernel of `F(P₁) ⟶ F(P₀)` is natural in `F`. -/
@[reassoc]
lemma leftDerived_app_comp_leftDerivedOneIsoKernel_hom (hS : S.ShortExact) [G.Additive]
    (α : F ⟶ G) :
    (NatTrans.leftDerived α 1).app S.X₃ ≫ (hS.leftDerivedOneIsoKernel G).hom =
      (hS.leftDerivedOneIsoKernel F).hom ≫
        kernel.map (F.map S.f) (G.map S.f) (α.app S.X₁) (α.app S.X₂) (α.naturality S.f) := by
  rw [← cancel_mono (kernel.ι (G.map S.f)), Category.assoc, Category.assoc, kernel.lift_ι,
    ← Category.assoc (hS.leftDerivedOneIsoKernel F).hom]
  exact comp_leftDerivedOneIsoKernel_hom_comp_ι F hS _ _
    (ProjectiveResolution.leftDerived_app_eq α hS.projectiveResolution 1)

omit [G.Additive] in
/-- The identification of `L₁F(M)` with the kernel of `F(P₁) ⟶ F(P₀)` is natural in maps of
projective presentations. -/
@[reassoc]
lemma leftDerived_map_comp_leftDerivedOneIsoKernel_hom (φ : S ⟶ S') :
    (F.leftDerived 1).map φ.τ₃ ≫ (hS'.leftDerivedOneIsoKernel F).hom =
      (hS.leftDerivedOneIsoKernel F).hom ≫
        kernel.map (F.map S.f) (F.map S'.f) (F.map φ.τ₁) (F.map φ.τ₂)
          (by simp only [← F.map_comp, φ.comm₁₂]) := by
  rw [← cancel_mono (kernel.ι (F.map S'.f)), Category.assoc, Category.assoc, kernel.lift_ι,
    ← Category.assoc (hS.leftDerivedOneIsoKernel F).hom]
  rw [← resolutionComplexMap_f_one φ]
  exact comp_leftDerivedOneIsoKernel_hom_comp_ι F hS' _ _
    (F.leftDerived_map_eq 1 φ.τ₃ (P := hS.projectiveResolution) (Q := hS'.projectiveResolution)
      (resolutionComplexMap φ) (resolutionComplexMap_comp_resolutionπ φ))

end ShortExact

namespace ShortExact

variable [HasProjectiveResolutions C] {D : Type*} [Category* D] [Abelian D]
  (hS : S.ShortExact) [Projective S.X₂] (F : C ⥤ D) [F.Additive]

omit [HasProjectiveResolutions C] in
/-- For any projective resolution `P` of `S.X₁`, homology in degree `n + 2` of `F` on
`hS.augmentProjectiveResolution P` is naturally isomorphic to homology in degree `n + 1` of `F` on
`P`. -/
private def augmentProjectiveResolutionHomologyIso (P : ProjectiveResolution S.X₁) (n : ℕ) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 2)).obj
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (hS.augmentProjectiveResolution P).complex) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 1)).obj
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :=
  let K := P.complex.augment ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
    (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp])
  (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 2)).mapIso
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
        (eqToIso (hS.augmentProjectiveResolution_complex P))) ≪≫
    (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 3) (n + 2) (n + 1)
      (by simp) (by simp)).app ((F.mapHomologicalComplex _).obj K) ≪≫
    (ShortComplex.homologyFunctor D).mapIso
      (ShortComplex.isoMk
        (S₁ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
          (n + 3) (n + 2) (n + 1)).obj ((F.mapHomologicalComplex _).obj K))
        (S₂ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
          (n + 2) (n + 1) n).obj ((F.mapHomologicalComplex _).obj P.complex))
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)) ≪≫
    ((HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 2) (n + 1) n
      (by simp) (by simp)).app ((F.mapHomologicalComplex _).obj P.complex)).symm

omit [HasProjectiveResolutions C] in
private lemma map_comp_augmentProjectiveResolutionHomologyIso_hom
    {G : C ⥤ D} [G.Additive] {P P' : ProjectiveResolution S.X₁}
    (ψ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (P.complex.augment ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
          (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp])) ⟶
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (P'.complex.augment ((P'.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
          (by simp only [← Category.assoc, P'.complex_d_comp_π_f_zero, zero_comp])))
    (φ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ⟶
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P'.complex)
    (hψ : ∀ m, ψ.f (m + 1) = φ.f m) (n : ℕ) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 2)).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (eqToHom (hS.augmentProjectiveResolution_complex P)) ≫ ψ ≫
          (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (eqToHom (hS.augmentProjectiveResolution_complex P').symm)) ≫
      (hS.augmentProjectiveResolutionHomologyIso G P' n).hom =
      (hS.augmentProjectiveResolutionHomologyIso F P n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 1)).map φ := by
  dsimp only [augmentProjectiveResolutionHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  simp only [eqToIso.hom, Functor.map_comp, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rw [(HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 3) (n + 2) (n + 1)
    (by simp) (by simp)).hom.naturality_assoc ψ]
  simp only [Functor.comp_map]
  have hsc : (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
        (n + 3) (n + 2) (n + 1)).map ψ ≫
      (ShortComplex.isoMk
        (S₁ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
          (n + 3) (n + 2) (n + 1)).obj ((G.mapHomologicalComplex _).obj _))
        (S₂ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
          (n + 2) (n + 1) n).obj ((G.mapHomologicalComplex _).obj P'.complex))
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)).hom =
      (ShortComplex.isoMk
        (S₁ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
          (n + 3) (n + 2) (n + 1)).obj ((F.mapHomologicalComplex _).obj _))
        (S₂ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
          (n + 2) (n + 1) n).obj ((F.mapHomologicalComplex _).obj P.complex))
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)).hom ≫
        (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
          (n + 2) (n + 1) n).map φ :=
    ShortComplex.hom_ext _ _
      ((Category.comp_id _).trans ((hψ (n + 2)).trans (Category.id_comp _).symm))
      ((Category.comp_id _).trans ((hψ (n + 1)).trans (Category.id_comp _).symm))
      ((Category.comp_id _).trans ((hψ n).trans (Category.id_comp _).symm))
  rw [← Functor.map_comp_assoc, hsc, Functor.map_comp_assoc]
  refine congrArg _ (congrArg _ (congrArg _ ?_))
  exact (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 2) (n + 1) n
    (by simp) (by simp)).inv.naturality φ

/-- **Dimension shifting along a projective presentation.** Given a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₂` projective, prepending `X₂` to a projective resolution of `X₁`
identifies `L_{n+2}F(X₃)` with `L_{n+1}F(X₁)` for every additive functor `F`. -/
def leftDerivedAddTwoIso (n : ℕ) :
    (F.leftDerived (n + 2)).obj S.X₃ ≅ (F.leftDerived (n + 1)).obj S.X₁ :=
  let P := CategoryTheory.projectiveResolution S.X₁
  (hS.augmentProjectiveResolution P).isoLeftDerivedObj F (n + 2) ≪≫
    hS.augmentProjectiveResolutionHomologyIso F P n ≪≫
    (P.isoLeftDerivedObj F (n + 1)).symm

omit [HasProjectiveResolutions C] [Projective S.X₂] in
private def augmentProjectiveResolutionComplexMap {P P' : ProjectiveResolution S.X₁}
    (φ : P.complex ⟶ P'.complex) (hφ0 : φ.f 0 ≫ P'.π.f 0 = P.π.f 0) :
    P.complex.augment ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
        (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]) ⟶
      P'.complex.augment ((P'.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
        (by simp only [← Category.assoc, P'.complex_d_comp_π_f_zero, zero_comp]) where
  f
    | 0 => eqToHom (ChainComplex.augment_X_zero _ _ _) ≫
        eqToHom (ChainComplex.augment_X_zero _ _ _).symm
    | m + 1 => φ.f m
  comm' i j hij := by
    cases j with
    | zero =>
      obtain rfl : 1 = i := hij
      dsimp only [ChainComplex.augment_X_zero, ChainComplex.augment_X_succ]
      simp only [ChainComplex.augment_d_one_zero, ← Category.assoc]
      rw [hφ0]
      exact ((Category.comp_id (_ ≫ 𝟙 S.X₂)).trans (Category.comp_id _)).symm
    | succ m =>
      obtain rfl : m + 1 + 1 = i := hij
      dsimp only [ChainComplex.augment_X_succ]
      rw [ChainComplex.augment_d_succ_succ, ChainComplex.augment_d_succ_succ]
      exact φ.comm (m + 1) m

/-- Computation of `leftDerivedAddTwoIso` on an arbitrary projective resolution `P` of `S.X₁`. -/
theorem leftDerivedAddTwoIso_hom_eq (P : ProjectiveResolution S.X₁) (n : ℕ) :
    (hS.leftDerivedAddTwoIso F n).hom =
      ((hS.augmentProjectiveResolution P).isoLeftDerivedObj F (n + 2)).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 2)).map
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (eqToHom (hS.augmentProjectiveResolution_complex P))) ≫
        (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 3) (n + 2) (n + 1)
          (by simp) (by simp)).hom.app ((F.mapHomologicalComplex _).obj
            (P.complex.augment
              ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
              (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]))) ≫
        (ShortComplex.homologyFunctor D).map
          (ShortComplex.isoMk
            (S₁ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
              (n + 3) (n + 2) (n + 1)).obj ((F.mapHomologicalComplex _).obj
                (P.complex.augment
                  ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
                  (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]))))
            (S₂ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
              (n + 2) (n + 1) n).obj ((F.mapHomologicalComplex _).obj P.complex))
            (Iso.refl _) (Iso.refl _) (Iso.refl _)
            ((Category.id_comp _).trans (Category.comp_id _).symm)
            ((Category.id_comp _).trans (Category.comp_id _).symm)).hom ≫
        (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 2) (n + 1) n
          (by simp) (by simp)).inv.app ((F.mapHomologicalComplex _).obj P.complex) ≫
        (P.isoLeftDerivedObj F (n + 1)).inv := by
  let P' := CategoryTheory.projectiveResolution S.X₁
  let Q := hS.augmentProjectiveResolution P
  let Q' := hS.augmentProjectiveResolution P'
  let φ : P.complex ⟶ P'.complex := ProjectiveResolution.lift (𝟙 S.X₁) P P'
  have hφ0 : φ.f 0 ≫ P'.π.f 0 = P.π.f 0 :=
    (ProjectiveResolution.lift_commutes_zero (𝟙 S.X₁) P P').trans (Category.comp_id _)
  let aug := augmentProjectiveResolutionComplexMap φ hφ0
  let τ : Q.complex ⟶ Q'.complex :=
    eqToHom (hS.augmentProjectiveResolution_complex P) ≫ aug ≫
      eqToHom (hS.augmentProjectiveResolution_complex P').symm
  have hτ0 : τ.f 0 ≫ Q'.π.f 0 = Q.π.f 0 ≫ 𝟙 S.X₃ := by
    refine (?_ : τ.f 0 ≫ Q'.π.f 0 = Q.π.f 0).trans (Category.comp_id _).symm
    have hP0 : S.X₂ = Q.complex.X 0 :=
      (ChainComplex.augment_X_zero _ _ _).symm.trans
        (congrArg (fun C ↦ C.X 0) (hS.augmentProjectiveResolution_complex P).symm)
    rw [← cancel_epi (eqToHom hP0),
      ← cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 S.X₃).hom]
    have hQ0 := hS.augmentProjectiveResolution_π_f_zero P
    have hQ'0 := hS.augmentProjectiveResolution_π_f_zero P'
    dsimp only [τ, aug, augmentProjectiveResolutionComplexMap, Q, Q']
    simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f, Category.assoc,
      eqToHom_trans_assoc]
    exact hQ'0.trans hQ0.symm
  have hQ : (Q'.isoLeftDerivedObj F (n + 2)).hom =
      (Q.isoLeftDerivedObj F (n + 2)).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ (n + 2)).map τ := by
    simpa using ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 S.X₃) Q Q' τ hτ0 F (n + 2)
  have hP : (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 1)).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫
      (P'.isoLeftDerivedObj F (n + 1)).inv = (P.isoLeftDerivedObj F (n + 1)).inv := by
    simpa [Functor.comp_map] using (ProjectiveResolution.isoLeftDerivedObj_inv_naturality (𝟙 S.X₁)
      P P' φ (ProjectiveResolution.lift_commutes_zero (𝟙 S.X₁) P P') F (n + 1)).symm
  have hdef : (hS.leftDerivedAddTwoIso F n).hom =
      (Q'.isoLeftDerivedObj F (n + 2)).hom ≫
        (hS.augmentProjectiveResolutionHomologyIso F P' n).hom ≫
          (P'.isoLeftDerivedObj F (n + 1)).inv := rfl
  rw [hdef, hQ, Category.assoc]
  have hmid := hS.map_comp_augmentProjectiveResolutionHomologyIso_hom F
    ((F.mapHomologicalComplex _).map aug) ((F.mapHomologicalComplex _).map φ)
    (fun _ ↦ rfl) n
  simp only [Functor.comp_map, ← Functor.map_comp] at hmid ⊢
  rw [reassoc_of% hmid, hP]
  dsimp only [Q, augmentProjectiveResolutionHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  simp only [eqToIso.hom, Category.assoc]

/-- Computation of the inverse of `leftDerivedAddTwoIso` on an arbitrary projective resolution `P`
of `S.X₁`. -/
theorem leftDerivedAddTwoIso_inv_eq (P : ProjectiveResolution S.X₁) (n : ℕ) :
    (hS.leftDerivedAddTwoIso F n).inv =
      (P.isoLeftDerivedObj F (n + 1)).hom ≫
        (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 2) (n + 1) n
          (by simp) (by simp)).hom.app ((F.mapHomologicalComplex _).obj P.complex) ≫
        (ShortComplex.homologyFunctor D).map
          (ShortComplex.isoMk
            (S₁ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
              (n + 3) (n + 2) (n + 1)).obj ((F.mapHomologicalComplex _).obj
                (P.complex.augment
                  ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
                  (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]))))
            (S₂ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ)
              (n + 2) (n + 1) n).obj ((F.mapHomologicalComplex _).obj P.complex))
            (Iso.refl _) (Iso.refl _) (Iso.refl _)
            ((Category.id_comp _).trans (Category.comp_id _).symm)
            ((Category.id_comp _).trans (Category.comp_id _).symm)).inv ≫
        (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ) (n + 3) (n + 2) (n + 1)
          (by simp) (by simp)).inv.app ((F.mapHomologicalComplex _).obj
            (P.complex.augment
              ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
              (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]))) ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 2)).map
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (eqToHom (hS.augmentProjectiveResolution_complex P).symm)) ≫
        ((hS.augmentProjectiveResolution P).isoLeftDerivedObj F (n + 2)).inv := by
  rw [← cancel_epi (hS.leftDerivedAddTwoIso F n).hom, Iso.hom_inv_id,
    hS.leftDerivedAddTwoIso_hom_eq F P n]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl]

/-- Dimension shifting along a projective presentation is natural in the additive functor `F`. -/
@[reassoc]
theorem leftDerived_app_comp_leftDerivedAddTwoIso_hom {G : C ⥤ D} [G.Additive]
    (α : F ⟶ G) (n : ℕ) :
    (NatTrans.leftDerived α (n + 2)).app S.X₃ ≫ (hS.leftDerivedAddTwoIso G n).hom =
      (hS.leftDerivedAddTwoIso F n).hom ≫ (NatTrans.leftDerived α (n + 1)).app S.X₁ := by
  let P := CategoryTheory.projectiveResolution S.X₁
  let Q := hS.augmentProjectiveResolution P
  let K := P.complex.augment ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
    (by simp only [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp])
  have hdef : ∀ (H : C ⥤ D) [H.Additive], (hS.leftDerivedAddTwoIso H n).hom =
      (Q.isoLeftDerivedObj H (n + 2)).hom ≫
        (hS.augmentProjectiveResolutionHomologyIso H P n).hom ≫
          (P.isoLeftDerivedObj H (n + 1)).inv := fun _ _ ↦ rfl
  rw [hdef G, hdef F, Q.leftDerived_app_eq α (n + 2), P.leftDerived_app_eq α (n + 1)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  have hnat : (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app Q.complex =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (eqToHom (hS.augmentProjectiveResolution_complex P)) ≫
        (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app K ≫
        (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (eqToHom (hS.augmentProjectiveResolution_complex P).symm) := by
    rw [← cancel_mono ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (eqToHom (hS.augmentProjectiveResolution_complex P)))]
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl, Functor.map_id,
      Category.comp_id]
    exact ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).naturality
      (eqToHom (hS.augmentProjectiveResolution_complex P))).symm
  rw [hnat, reassoc_of% (hS.map_comp_augmentProjectiveResolutionHomologyIso_hom F
    ((NatTrans.mapHomologicalComplex α _).app K)
    ((NatTrans.mapHomologicalComplex α _).app P.complex) (fun _ ↦ rfl) n)]

include hS in
/-- Along a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₂` projective, `L_{n+2}F(X₃)`
vanishes if and only if `L_{n+1}F(X₁)` vanishes. -/
theorem isZero_leftDerived_add_two_iff (n : ℕ) :
    IsZero ((F.leftDerived (n + 2)).obj S.X₃) ↔ IsZero ((F.leftDerived (n + 1)).obj S.X₁) :=
  (hS.leftDerivedAddTwoIso F n).isZero_iff

include hS in
/-- For a right exact additive functor `F` and a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
with `X₂` projective, `F(X₁) ⟶ F(X₂)` is a monomorphism if and only if `L₁F(X₃)` vanishes. -/
theorem mono_map_f_iff_isZero_leftDerived_one [PreservesFiniteColimits F] :
    Mono (F.map S.f) ↔ IsZero ((F.leftDerived 1).obj S.X₃) := by
  let P := CategoryTheory.projectiveResolution S.X₁
  let Q := hS.augmentProjectiveResolution P
  let π₀ : P.complex.X 0 ⟶ S.X₁ :=
    P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 S.X₁).hom
  have hπ₀ : P.complex.d 1 0 ≫ π₀ = 0 := by
    simp only [π₀, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]
  let K := P.complex.augment (π₀ ≫ S.f) (by simp only [← Category.assoc, hπ₀, zero_comp])
  rw [(Q.isoLeftDerivedObj F 1).isZero_iff, HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    (hS.augmentProjectiveResolution_complex P : Q.complex = K),
    HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  let S₁ : ShortComplex D := ShortComplex.mk (F.map (P.complex.d 1 0)) (F.map π₀ ≫ F.map S.f)
    (by rw [← Category.assoc, ← F.map_comp, hπ₀, F.map_zero, zero_comp])
  have hS₁ : (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).sc' 2 1 0).Exact ↔
      S₁.Exact :=
    ShortComplex.exact_iff_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [K, S₁]) (by simp [K, S₁]))
  -- `F` preserves the cokernel `P₁ ⟶ P₀ ⟶ X₁`, so `coker F(d₁₀) ≅ F(X₁)` carries the
  -- induced map `coker F(d₁₀) ⟶ F(X₂)` to `F(S.f)`.
  have hcok : IsColimit (CokernelCofork.ofπ π₀ hπ₀) :=
    IsColimit.ofIsoColimit P.isColimitCokernelCofork
      (Cofork.ext (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 S.X₁) rfl)
  have hcokF : IsColimit (CokernelCofork.ofπ (F.map π₀)
      (by rw [← F.map_comp, hπ₀, F.map_zero])) :=
    isColimitCoforkMapOfIsColimit' F hπ₀ hcok
  let e : cokernel (F.map (P.complex.d 1 0)) ≅ F.obj S.X₁ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (F.map (P.complex.d 1 0))) hcokF
  have he : cokernel.π (F.map (P.complex.d 1 0)) ≫ e.hom = F.map π₀ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _) hcokF
      WalkingParallelPair.one
  have hdesc : cokernel.desc S₁.f S₁.g S₁.zero = e.hom ≫ F.map S.f := by
    rw [← cancel_epi (cokernel.π S₁.f), cokernel.π_desc, ← Category.assoc, he]
  rw [hS₁, S₁.exact_iff_mono_cokernel_desc, hdesc, mono_comp_iff_of_isIso]

include hS in
/-- A right exact additive functor sends a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with
`X₂` projective to a short exact sequence if and only if `L₁F(X₃)` vanishes. -/
theorem shortExact_map_iff_isZero_leftDerived_one [PreservesFiniteColimits F] :
    (S.map F).ShortExact ↔ IsZero ((F.leftDerived 1).obj S.X₃) := by
  obtain ⟨hex, hepi⟩ :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).1 inferInstance S hS
  rw [← hS.mono_map_f_iff_isZero_leftDerived_one F]
  exact ⟨fun h ↦ h.mono_f, fun h ↦ .mk' hex h hepi⟩

end ShortExact

end ShortComplex

section Additive

variable [HasProjectiveResolutions C] {D : Type*} [Category* D] [Abelian D]

/-- The natural transformation between left derived functors induced by a natural transformation
is additive in it. -/
@[simp]
theorem NatTrans.leftDerived_add {F G : C ⥤ D} [F.Additive] [G.Additive] (α β : F ⟶ G) (n : ℕ) :
    NatTrans.leftDerived (α + β) n = NatTrans.leftDerived α n + NatTrans.leftDerived β n := by
  ext X
  have h : (NatTrans.mapHomologicalComplex (α + β) _).app (projectiveResolution X).complex =
      (NatTrans.mapHomologicalComplex α _).app _ + (NatTrans.mapHomologicalComplex β _).app _ := by
    ext
    simp
  simp only [NatTrans.app_add, (projectiveResolution X).leftDerived_app_eq, h, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- A natural isomorphism between additive functors induces a natural isomorphism between their
left derived functors. -/
def NatIso.leftDerived {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.leftDerived n ≅ G.leftDerived n where
  hom := NatTrans.leftDerived e.hom n
  inv := NatTrans.leftDerived e.inv n
  hom_inv_id := by rw [← NatTrans.leftDerived_comp, e.hom_inv_id, NatTrans.leftDerived_id]
  inv_hom_id := by rw [← NatTrans.leftDerived_comp, e.inv_hom_id, NatTrans.leftDerived_id]

@[simp]
theorem NatIso.leftDerived_hom {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    (NatIso.leftDerived e n).hom = NatTrans.leftDerived e.hom n :=
  (rfl)

@[simp]
theorem NatIso.leftDerived_inv {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    (NatIso.leftDerived e n).inv = NatTrans.leftDerived e.inv n :=
  (rfl)

/-- The comparison `L₀F ⟶ F` is natural in the additive functor `F`: it intertwines the
natural transformation `L₀F ⟶ L₀G` induced by `α : F ⟶ G` with `α`. -/
@[reassoc]
theorem NatTrans.leftDerived_zero_comp_fromLeftDerivedZero {F G : C ⥤ D} [F.Additive]
    [G.Additive] (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.fromLeftDerivedZero = F.fromLeftDerivedZero ≫ α := by
  ext X
  let P := projectiveResolution X
  -- On opcycles in degree zero, both sides are induced by `α` on `F(P₀) ⟶ G(P₀) ⟶ G(X)`.
  have h : HomologicalComplex.opcyclesMap ((NatTrans.mapHomologicalComplex α _).app P.complex) 0 ≫
      P.fromLeftDerivedZero' G = P.fromLeftDerivedZero' F ≫ α.app X := by
    rw [← cancel_epi (HomologicalComplex.pOpcycles _ 0), HomologicalComplex.p_opcyclesMap_assoc]
    simpa using (α.naturality (P.π.f 0)).symm
  simp only [NatTrans.comp_app, P.leftDerived_app_eq, P.fromLeftDerivedZero_eq, Category.assoc,
    Iso.inv_hom_id_assoc]
  -- `erw`: the homology of `F(P)` appears both as `homologyFunctor.obj` and as `homology 0`.
  erw [HomologicalComplex.homologyι_naturality_assoc, h,
    Category.assoc (ChainComplex.isoHomologyι₀ _).hom]
  rfl

/-- Postcomposing an additive functor with an exact additive functor commutes with left derived
functors: `Lₙ(G ∘ F) ≅ G ∘ LₙF`. -/
def Functor.leftDerivedCompIso {E : Type*} [Category* E] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology] (n : ℕ) :
    (F ⋙ G).leftDerived n ≅ F.leftDerived n ⋙ G :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (projectiveResolutions C)
      (isoWhiskerRight
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.down ℕ)).symm
          (HomotopyCategory.homologyFunctor E (ComplexShape.down ℕ) n) ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.down ℕ))
          (G.mapHomotopyCategoryCompHomologyFunctorIso (ComplexShape.down ℕ) n) ≪≫
        (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.associator _ _ _).symm G

omit [HasProjectiveResolutions C] in
private lemma mapHomotopyCategoryCompIso_refl_inv_app_quotient {E : Type*} [Category* E]
    [Abelian E] (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    (K : ChainComplex C ℕ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.down ℕ)).inv.app
      ((HomotopyCategory.quotient C (ComplexShape.down ℕ)).obj K) =
      ((F ⋙ G).mapHomotopyCategoryFactors (ComplexShape.down ℕ)).hom.app K ≫
        (HomotopyCategory.quotient E (ComplexShape.down ℕ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.down ℕ)).inv.app K) ≫
        (G.mapHomotopyCategory (ComplexShape.down ℕ)).map
          ((F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)).inv.app K) := by
  let m := (HomotopyCategory.quotient E (ComplexShape.down ℕ)).map
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.down ℕ)).inv.app K)
  exact (Quotient.natTransLift_app _ _ _ _ K).trans
    ((Category.id_comp m).symm.trans
      (whisker_eq _ ((Category.comp_id m).symm.trans
        (whisker_eq m ((G.mapHomotopyCategory (ComplexShape.down ℕ)).map_id _).symm))))

/-- On any projective resolution `P` of `X`, `Functor.leftDerivedCompIso` is the complex-level
homology comparison `(G.mapHomologicalComplexCompHomologyFunctorIso _ n).hom.app (F(P))`. -/
theorem Functor.leftDerivedCompIso_hom_app {E : Type*} [Category* E] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology] (n : ℕ)
    {X : C} (P : ProjectiveResolution X) :
    (F.leftDerivedCompIso G n).hom.app X =
      (P.isoLeftDerivedObj (F ⋙ G) n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.down ℕ)).inv.app P.complex) ≫
        (G.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.down ℕ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
        G.map (P.isoLeftDerivedObj F n).inv := by
  let c := ComplexShape.down ℕ
  let β : (F ⋙ G).mapHomotopyCategory c ⋙ HomotopyCategory.homologyFunctor E c n ≅
      (F.mapHomotopyCategory c ⋙ HomotopyCategory.homologyFunctor D c n) ⋙ G :=
    isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).symm
        (HomotopyCategory.homologyFunctor E c n) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (F.mapHomotopyCategory c)
        (G.mapHomotopyCategoryCompHomologyFunctorIso c n) ≪≫
      (Functor.associator _ _ _).symm
  rw [← cancel_mono (G.map (P.isoLeftDerivedObj F n).hom)]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, Functor.map_id]
  dsimp only [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory,
    ProjectiveResolution.isoLeftDerivedObj,
    ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj, Functor.leftDerivedCompIso, β, c,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.mapIso_hom, Functor.comp_obj]
  simp only [Functor.map_id, Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc,
    Iso.app_hom]
  have hnat := β.hom.naturality P.iso.hom
  dsimp only [β, c, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.comp_map] at hnat
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hnat
  have hGnat := (G.mapHomotopyCategoryCompHomologyFunctorIso c n).hom.naturality
    ((F.mapHomotopyCategoryFactors c).inv.app P.complex)
  dsimp only [c, Functor.comp_obj, Functor.comp_map] at hGnat
  have hEnat := (HomotopyCategory.homologyFunctorFactors E c n).hom.naturality
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).inv.app P.complex)
  dsimp only [c, Functor.comp_obj, Functor.comp_map] at hEnat
  have hcancelF : G.map ((HomotopyCategory.homologyFunctor D c n).map
        ((F.mapHomotopyCategoryFactors c).inv.app P.complex)) ≫
      G.map ((HomotopyCategory.homologyFunctor D c n).map
        ((F.mapHomotopyCategoryFactors c).hom.app P.complex)) =
      𝟙 (G.obj ((HomotopyCategory.homologyFunctor D c n).obj
        ((HomotopyCategory.quotient D c).obj ((F.mapHomologicalComplex c).obj P.complex)))) := by
    rw [← G.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, G.map_id]
    rfl
  have hcancelD : G.map ((HomotopyCategory.homologyFunctorFactors D c n).inv.app
        ((F.mapHomologicalComplex c).obj P.complex)) ≫
      G.map ((HomotopyCategory.homologyFunctorFactors D c n).hom.app
        ((F.mapHomologicalComplex c).obj P.complex)) = 𝟙 _ := by
    rw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]
  rw [← reassoc_of% hnat]
  simp only [mapHomotopyCategoryCompIso_refl_inv_app_quotient F G P.complex, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% hGnat, G.mapHomotopyCategoryCompHomologyFunctorIso_hom_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc]
  rw [reassoc_of% hcancelF, hcancelD, Category.comp_id, reassoc_of% hEnat]

/-- When `G` is exact, additive and faithful, `(Lₙ(G ∘ F))(X)` vanishes if and only if
`(LₙF)(X)` vanishes. -/
theorem Functor.isZero_leftDerived_comp_iff {E : Type*} [Category* E] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology] [G.Faithful]
    (X : C) (n : ℕ) :
    IsZero (((F ⋙ G).leftDerived n).obj X) ↔ IsZero ((F.leftDerived n).obj X) :=
  ((F.leftDerivedCompIso G n).app X).isZero_iff.trans ⟨G.isZero_of_isZero_obj, G.map_isZero⟩

/-- An exact additive functor has no positive left derived functors. -/
theorem Functor.isZero_leftDerived_succ (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (X : C) (q : ℕ) : IsZero ((F.leftDerived (q + 1)).obj X) := by
  let P := projectiveResolution X
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp)]
  exact (P.exact_succ q).map F

/-- If an additive functor sends every projective object into a class closed under subobjects
and quotients, all its left derived functors take values in that class. -/
lemma ObjectProperty.prop_leftDerived_obj (P : ObjectProperty D) [P.IsClosedUnderSubobjects]
    [P.IsClosedUnderQuotients] (F : C ⥤ D) [F.Additive]
    (hF : ∀ (Y : C) [Projective Y], P (F.obj Y)) (X : C) (n : ℕ) :
    P ((F.leftDerived n).obj X) := by
  let Q := projectiveResolution X
  exact P.prop_of_iso (Q.isoLeftDerivedObj F n).symm
    (P.prop_homology ((F.mapHomologicalComplex _).obj Q.complex) n (hF _))

end Additive

end CategoryTheory
