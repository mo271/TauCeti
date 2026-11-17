/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Linear.Yoneda
public import TauCeti.Algebra.Homology.HomologicalComplex.Retract
public import TauCeti.AlgebraicTopology.ExtraCodegeneracy
public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Free

/-!
# Comonad cohomology and vanishing for `G`-projective objects

Given a comonad `G` on a category `C` and a contravariant functor `F : Cᵒᵖ ⥤ D` into a
preadditive category `D`, applying `F` to the augmented simplicial resolution of `G` produces an
augmented cosimplicial object (`CategoryTheory.Comonad.augmentedCosimplicialResolution`) and
hence a cochain complex (`CategoryTheory.Comonad.cochainComplexOfFunctor`) with coaugmentation
from `(CochainComplex.single₀ D).obj (F.obj (op X))` when `D` has a zero object.

When `X = G.obj W` is free, the extra degeneracy on the reversed simplicial resolution of `G.obj W`
dualizes to an extra codegeneracy on the reversed augmented cosimplicial object, yielding a
homotopy equivalence between the single-degree complex of `F.obj (op (G.obj W))` and the cochain
complex (`freeCochainComplexOfFunctorHomotopyEquiv`). When `X` is `G`-projective — meaning the
counit `G.ε.app X : G.obj X ⟶ X` is a split epimorphism — `X` is a retract of `G.obj X`, so
retract stability of homotopy equivalences transfers the contraction to `X`
(`cochainComplexOfFunctorHomotopyEquivOfSplitEpi`). In a category with homology, this gives a
quasi-isomorphism, an isomorphism `H⁰ ≅ F(X)`, and vanishing of `Hⁿ` for `n ≠ 0`.

Specializing `F` to the `R`-linear Yoneda functor `(linearYoneda R C).obj Y` for an `R`-linear
category `C` produces the bifunctorial comonad cochain complex `C_G(X, Y)` in
`CochainComplex (ModuleCat R) ℕ` (`CategoryTheory.Comonad.cochainComplex`), contravariant in `X`
and covariant in `Y`, together with its vanishing theorem for `G`-projective objects `X`.

## References

* M. Barr and J. Beck, *Homology and standard constructions*, Seminar on Triples and Categorical
  Homology Theory, Lecture Notes in Math. 80, Springer, 1969, §§1, 4.
* A. Gainutdinov, J. Haferkamp, and C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Proposition 2.12.
-/

public noncomputable section

open CategoryTheory Opposite Limits Functor

open scoped Simplicial

universe w v u v' u'

namespace CategoryTheory.Comonad

section GeneralFunctor

variable {C : Type u} [Category.{v} C] (G : Comonad C)
  {D : Type u'} [Category.{v'} D]

/-- Applying a contravariant functor `F : Cᵒᵖ ⥤ D` to the augmented simplicial resolution of
`G` gives a contravariant functor into augmented cosimplicial objects in `D`. -/
@[expose] def augmentedCosimplicialResolution (F : Cᵒᵖ ⥤ D) :
    Cᵒᵖ ⥤ CosimplicialObject.Augmented D :=
  G.augmentedSimplicialResolution.op ⋙
    simplicialToCosimplicialAugmented C ⋙
    CosimplicialObject.Augmented.whiskeringObj Cᵒᵖ D F

@[simp]
lemma augmentedCosimplicialResolution_obj_left (F : Cᵒᵖ ⥤ D) (X : C) :
    ((G.augmentedCosimplicialResolution F).obj (op X)).left = F.obj (op X) := (rfl)

@[simp]
lemma augmentedCosimplicialResolution_obj_right_obj (F : Cᵒᵖ ⥤ D) (X : C) (n : ℕ) :
    ((G.augmentedCosimplicialResolution F).obj (op X)).right.obj ⦋n⦌ =
      F.obj (op ((G.resolutionStage (n + 1)).obj X)) := (rfl)

lemma augmentedCosimplicialResolution_obj_right_δ (F : Cᵒᵖ ⥤ D) (X : C) {n : ℕ}
    (i : Fin (n + 2)) :
    ((G.augmentedCosimplicialResolution F).obj (op X)).right.δ i =
      F.map ((G.resolutionFace (n + 1) i).app X).op :=
  congrArg (fun g ↦ F.map (Quiver.Hom.op g)) (G.simplicialResolution_δ X i)

@[simp]
lemma augmentedCosimplicialResolution_obj_hom₀ (F : Cᵒᵖ ⥤ D) (X : C) :
    CosimplicialObject.Augmented.hom₀ ((G.augmentedCosimplicialResolution F).obj (op X)) =
      F.map (G.ε.app X).op :=
  (Category.id_comp _).trans
    (congrArg (fun g ↦ F.map (Quiver.Hom.op g)) (G.simplicialResolutionAugmentation_app_zero X))

/-- On a free object `G.obj W`, reversing the augmented cosimplicial resolution produces an
extra codegeneracy. -/
def freeReversedExtraCodegeneracy (F : Cᵒᵖ ⥤ D) (W : C) :
    CosimplicialObject.Augmented.ExtraCodegeneracy
      (CosimplicialObject.Augmented.opFunctor.obj
        ((G.augmentedCosimplicialResolution F).obj (op (G.obj W)))) :=
  ((CosimplicialObject.Augmented.ExtraCodegeneracy.ofExtraDegeneracyRightOp
      (G.freeReversedResolutionExtraDegeneracy W)).map F).ofIso
    ((CosimplicialObject.Augmented.whiskeringObj Cᵒᵖ D F).mapIso
      (SimplicialObject.Augmented.opFunctorRightOpIso _) ≪≫
        CosimplicialObject.Augmented.opFunctorWhiskeringObjIso F _)

section Preadditive

variable [Preadditive D]

/-- The alternating coface map cochain complex obtained by applying a contravariant functor
`F : Cᵒᵖ ⥤ D` to the simplicial resolution of `G`. -/
@[expose] def cochainComplexOfFunctor (F : Cᵒᵖ ⥤ D) :
    Cᵒᵖ ⥤ CochainComplex D ℕ :=
  G.augmentedCosimplicialResolution F ⋙
    CosimplicialObject.Augmented.drop ⋙
    AlgebraicTopology.alternatingCofaceMapComplex D

@[simp]
lemma cochainComplexOfFunctor_obj_X (F : Cᵒᵖ ⥤ D) (X : C) (n : ℕ) :
    ((G.cochainComplexOfFunctor F).obj (op X)).X n =
      F.obj (op ((G.resolutionStage (n + 1)).obj X)) := (rfl)

lemma cochainComplexOfFunctor_obj_d (F : Cᵒᵖ ⥤ D) (X : C) (n : ℕ) :
    ((G.cochainComplexOfFunctor F).obj (op X)).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        F.map ((G.resolutionFace (n + 1) i).app X).op :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_eq _ n).trans <|
    Finset.sum_congr rfl fun i _ ↦
      congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
        (G.augmentedCosimplicialResolution_obj_right_δ F X i)

@[simp]
lemma cochainComplexOfFunctor_map_f (F : Cᵒᵖ ⥤ D) {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((G.cochainComplexOfFunctor F).map f.op).f n =
      F.map ((G.resolutionStage (n + 1)).map f).op := (rfl)

variable [HasZeroObject D]

/-- The natural coaugmentation from `F(X)` concentrated in degree `0` to the comonad cochain
complex `(G.cochainComplexOfFunctor F).obj (op X)`. -/
def cochainComplexOfFunctorAugmentation (F : Cᵒᵖ ⥤ D) :
    F ⋙ CochainComplex.single₀ D ⟶ G.cochainComplexOfFunctor F :=
  whiskerLeft (G.augmentedCosimplicialResolution F)
    AlgebraicTopology.AlternatingCofaceMapComplex.η

@[simp]
lemma cochainComplexOfFunctorAugmentation_app_f_zero (F : Cᵒᵖ ⥤ D) (X : C) :
    ((G.cochainComplexOfFunctorAugmentation F).app (op X)).f 0 = F.map (G.ε.app X).op :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.η_app_f_zero _).trans
    (G.augmentedCosimplicialResolution_obj_hom₀ F X)

@[simp]
lemma cochainComplexOfFunctorAugmentation_app_f_succ (F : Cᵒᵖ ⥤ D) (X : C) (n : ℕ) :
    ((G.cochainComplexOfFunctorAugmentation F).app (op X)).f (n + 1) = 0 :=
  AlgebraicTopology.AlternatingCofaceMapComplex.η_app_f_succ _ n

/-- For a free object `G.obj W`, the coaugmentation into `cochainComplexOfFunctor F` is a
homotopy equivalence. -/
def freeCochainComplexOfFunctorHomotopyEquiv (F : Cᵒᵖ ⥤ D) (W : C) :
    HomotopyEquiv ((CochainComplex.single₀ D).obj (F.obj (op (G.obj W))))
      ((G.cochainComplexOfFunctor F).obj (op (G.obj W))) :=
  (G.freeReversedExtraCodegeneracy F W).revHomotopyEquiv

@[simp]
lemma freeCochainComplexOfFunctorHomotopyEquiv_hom (F : Cᵒᵖ ⥤ D) (W : C) :
    (G.freeCochainComplexOfFunctorHomotopyEquiv F W).hom =
      (G.cochainComplexOfFunctorAugmentation F).app (op (G.obj W)) :=
  CosimplicialObject.Augmented.ExtraCodegeneracy.revHomotopyEquiv_hom _

/-- For a `G`-projective object `X` (witnessed by a splitting `s` of `G.ε.app X`), the
coaugmentation into `cochainComplexOfFunctor F` is a homotopy equivalence. -/
def cochainComplexOfFunctorHomotopyEquivOfSplitEpi (F : Cᵒᵖ ⥤ D) {X : C}
    (s : SplitEpi (G.ε.app X)) :
    HomotopyEquiv ((CochainComplex.single₀ D).obj (F.obj (op X)))
      ((G.cochainComplexOfFunctor F).obj (op X)) :=
  (G.freeCochainComplexOfFunctorHomotopyEquiv F X).ofRetractArrow
    ((G.cochainComplexOfFunctorAugmentation F).retractArrowApp
      (Retract.mk s.section_ (G.ε.app X) s.id).op)
    (G.freeCochainComplexOfFunctorHomotopyEquiv_hom F X)

@[simp]
lemma cochainComplexOfFunctorHomotopyEquivOfSplitEpi_hom (F : Cᵒᵖ ⥤ D) {X : C}
    (s : SplitEpi (G.ε.app X)) :
    (G.cochainComplexOfFunctorHomotopyEquivOfSplitEpi F s).hom =
      (G.cochainComplexOfFunctorAugmentation F).app (op X) :=
  HomotopyEquiv.ofRetractArrow_hom _ _ _

section Homology

variable [CategoryWithHomology D]

/-- When `X` is `G`-projective, the coaugmentation into `cochainComplexOfFunctor F` is a
quasi-isomorphism. -/
instance quasiIso_cochainComplexOfFunctorAugmentation (F : Cᵒᵖ ⥤ D) (X : C)
    [IsSplitEpi (G.ε.app X)] :
    QuasiIso ((G.cochainComplexOfFunctorAugmentation F).app (op X)) := by
  obtain ⟨s⟩ := ‹IsSplitEpi (G.ε.app X)›.exists_splitEpi
  rw [← G.cochainComplexOfFunctorHomotopyEquivOfSplitEpi_hom F s]
  exact (G.cochainComplexOfFunctorHomotopyEquivOfSplitEpi F s).quasiIso_hom

/-- When `X` is `G`-projective, the degree-zero cohomology of `cochainComplexOfFunctor F` at `X`
is canonically isomorphic to `F.obj (op X)` via the coaugmentation. -/
def cochainComplexOfFunctorHomologyZeroIso (F : Cᵒᵖ ⥤ D) (X : C) [IsSplitEpi (G.ε.app X)] :
    ((G.cochainComplexOfFunctor F).obj (op X)).homology 0 ≅ F.obj (op X) :=
  (asIso (HomologicalComplex.homologyMap
      ((G.cochainComplexOfFunctorAugmentation F).app (op X)) 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (F.obj (op X))

/-- When `X` is `G`-projective, `cochainComplexOfFunctor F` at `X` is exact in every nonzero
degree. -/
lemma exactAt_cochainComplexOfFunctor (F : Cᵒᵖ ⥤ D) (X : C) [IsSplitEpi (G.ε.app X)]
    {n : ℕ} (hn : n ≠ 0) :
    ((G.cochainComplexOfFunctor F).obj (op X)).ExactAt n :=
  (exactAt_iff_of_quasiIsoAt ((G.cochainComplexOfFunctorAugmentation F).app (op X)) n).mp
    (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℕ) 0 (F.obj (op X)) n hn)

/-- When `X` is `G`-projective, the cohomology of `cochainComplexOfFunctor F` at `X` vanishes in
every nonzero degree. -/
lemma isZero_cochainComplexOfFunctor_homology (F : Cᵒᵖ ⥤ D) (X : C) [IsSplitEpi (G.ε.app X)]
    {n : ℕ} (hn : n ≠ 0) :
    IsZero (((G.cochainComplexOfFunctor F).obj (op X)).homology n) :=
  (((G.cochainComplexOfFunctor F).obj (op X)).exactAt_iff_isZero_homology n).mp
    (G.exactAt_cochainComplexOfFunctor F X hn)

end Homology

end Preadditive

end GeneralFunctor

section LinearCohomology

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  (G : Comonad C)

/-- The comonad cochain complex as a bifunctor, covariant in the target object `Y` and
contravariant in the source object `X`. -/
@[expose] def cochainComplexBifunctor :
    C ⥤ Cᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℕ where
  obj Y := G.cochainComplexOfFunctor ((linearYoneda R C).obj Y)
  map g :=
    whiskerRight
      (whiskerLeft (G.augmentedSimplicialResolution.op ⋙ simplicialToCosimplicialAugmented C)
        ((CosimplicialObject.Augmented.whiskering Cᵒᵖ (ModuleCat.{v} R)).map
          ((linearYoneda R C).map g)))
      (CosimplicialObject.Augmented.drop ⋙
        AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v} R))
  map_id Y := by
    ext X n f
    exact Category.comp_id f
  map_comp {Y₁ Y₂ Y₃} g₁ g₂ := by
    ext X n f
    exact (Category.assoc f g₁ g₂).symm

/-- The comonad cochain complex `C_G(X, Y)` of an `R`-linear category, with degree-`n` cochain
module `ModuleCat.of R ((G.resolutionStage (n + 1)).obj X ⟶ Y)`. -/
abbrev cochainComplex (X Y : C) : CochainComplex (ModuleCat.{v} R) ℕ :=
  ((G.cochainComplexBifunctor R).obj Y).obj (op X)

@[simp]
lemma cochainComplex_X (X Y : C) (n : ℕ) :
    (G.cochainComplex R X Y).X n = ModuleCat.of R ((G.resolutionStage (n + 1)).obj X ⟶ Y) := (rfl)

/-- The degree-`n` differential of `G.cochainComplex R X Y` sends a cochain `f` to the
alternating sum of precompositions with the resolution face maps. -/
lemma cochainComplex_d_apply (X Y : C) (n : ℕ) (f : (G.resolutionStage (n + 1)).obj X ⟶ Y) :
    ((G.cochainComplex R X Y).d n (n + 1)) f =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • ((G.resolutionFace (n + 1) i).app X ≫ f) := by
  have hd := G.cochainComplexOfFunctor_obj_d ((linearYoneda R C).obj Y) X n
  have hsum (f' : ((linearYoneda R C).obj Y).obj (op ((G.resolutionStage (n + 1)).obj X))) :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          ((linearYoneda R C).obj Y).map ((G.resolutionFace (n + 1) i).app X).op).hom f' =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (((linearYoneda R C).obj Y).map ((G.resolutionFace (n + 1) i).app X).op).hom f' := by
    rw [ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ModuleCat.hom_zsmul, LinearMap.smul_apply]
  exact (congrArg (fun φ ↦ φ.hom f) hd).trans (hsum f)

/-- Contravariant functoriality of `G.cochainComplex R` in the first argument acts by
precomposition with `(G.resolutionStage (n + 1)).map f`. -/
@[simp]
lemma cochainComplexBifunctor_obj_map_f_apply {X₁ X₂ : C} (Y : C) (f : X₁ ⟶ X₂) (n : ℕ)
    (φ : (G.resolutionStage (n + 1)).obj X₂ ⟶ Y) :
    (((G.cochainComplexBifunctor R).obj Y).map f.op).f n φ =
      (G.resolutionStage (n + 1)).map f ≫ φ := (rfl)

/-- Covariant functoriality of `G.cochainComplex R` in the second argument acts by
postcomposition with `g`. -/
@[simp]
lemma cochainComplexBifunctor_map_app_f_apply (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (n : ℕ)
    (φ : (G.resolutionStage (n + 1)).obj X ⟶ Y₁) :
    (((G.cochainComplexBifunctor R).map g).app (op X)).f n φ = φ ≫ g := (rfl)

/-- The coaugmentation `(CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (X ⟶ Y)) ⟶
G.cochainComplex R X Y`, given in degree `0` by precomposition with `G.ε.app X`. -/
abbrev cochainComplexAugmentation (X Y : C) :
    (CochainComplex.single₀ (ModuleCat.{v} R)).obj (ModuleCat.of R (X ⟶ Y)) ⟶
      G.cochainComplex R X Y :=
  (G.cochainComplexOfFunctorAugmentation ((linearYoneda R C).obj Y)).app (op X)

lemma cochainComplexAugmentation_f_zero_apply (X Y : C) (f : X ⟶ Y) :
    (G.cochainComplexAugmentation R X Y).f 0 f = G.ε.app X ≫ f := by
  rw [cochainComplexAugmentation, G.cochainComplexOfFunctorAugmentation_app_f_zero]
  rfl

/-- Naturality of `cochainComplexAugmentation` in the contravariant argument `X`. -/
@[reassoc]
lemma cochainComplexAugmentation_naturality_left {X₁ X₂ : C} (Y : C) (f : X₁ ⟶ X₂) :
    (CochainComplex.single₀ (ModuleCat.{v} R)).map (((linearYoneda R C).obj Y).map f.op) ≫
        G.cochainComplexAugmentation R X₁ Y =
      G.cochainComplexAugmentation R X₂ Y ≫
        ((G.cochainComplexBifunctor R).obj Y).map f.op :=
  (G.cochainComplexOfFunctorAugmentation ((linearYoneda R C).obj Y)).naturality f.op

/-- Naturality of `cochainComplexAugmentation` in the covariant argument `Y`. -/
@[reassoc]
lemma cochainComplexAugmentation_naturality_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (CochainComplex.single₀ (ModuleCat.{v} R)).map (((linearYoneda R C).map g).app (op X)) ≫
        G.cochainComplexAugmentation R X Y₂ =
      G.cochainComplexAugmentation R X Y₁ ≫
        ((G.cochainComplexBifunctor R).map g).app (op X) := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  ext f
  have h1 : (((CochainComplex.single₀ (ModuleCat.{v} R)).map
      (((linearYoneda R C).map g).app (op X)) ≫
      G.cochainComplexAugmentation R X Y₂).f 0) f = G.ε.app X ≫ (f ≫ g) := by
    have hs := congrArg (fun φ ↦ (ConcreteCategory.hom φ) f)
      (CochainComplex.single₀_map_f_zero (((linearYoneda R C).map g).app (op X)))
    exact (congrArg (fun x ↦ (G.cochainComplexAugmentation R X Y₂).f 0 x) hs).trans
      (G.cochainComplexAugmentation_f_zero_apply R X Y₂ (f ≫ g))
  have h2 : ((G.cochainComplexAugmentation R X Y₁ ≫
      ((G.cochainComplexBifunctor R).map g).app (op X)).f 0) f = (G.ε.app X ≫ f) ≫ g :=
    congrArg (· ≫ g) (G.cochainComplexAugmentation_f_zero_apply R X Y₁ f)
  exact h1.trans ((Category.assoc _ _ _).symm.trans h2.symm)

/-- For a `G`-projective object `X` with splitting `s : SplitEpi (G.ε.app X)`, the
coaugmentation into `G.cochainComplex R X Y` is a homotopy equivalence. -/
def cochainComplexHomotopyEquivOfSplitEpi {X : C} (Y : C) (s : SplitEpi (G.ε.app X)) :
    HomotopyEquiv ((CochainComplex.single₀ (ModuleCat.{v} R)).obj (ModuleCat.of R (X ⟶ Y)))
      (G.cochainComplex R X Y) :=
  G.cochainComplexOfFunctorHomotopyEquivOfSplitEpi ((linearYoneda R C).obj Y) s

@[simp]
lemma cochainComplexHomotopyEquivOfSplitEpi_hom {X : C} (Y : C) (s : SplitEpi (G.ε.app X)) :
    (G.cochainComplexHomotopyEquivOfSplitEpi R Y s).hom =
      G.cochainComplexAugmentation R X Y :=
  G.cochainComplexOfFunctorHomotopyEquivOfSplitEpi_hom ((linearYoneda R C).obj Y) s

/-- When `X` is `G`-projective, the coaugmentation into `G.cochainComplex R X Y` is a
quasi-isomorphism. -/
instance quasiIso_cochainComplexAugmentation (X Y : C) [IsSplitEpi (G.ε.app X)] :
    QuasiIso (G.cochainComplexAugmentation R X Y) :=
  G.quasiIso_cochainComplexOfFunctorAugmentation ((linearYoneda R C).obj Y) X

/-- For `G`-projective `X`, the degree-zero comonad cohomology of `G` with coefficients `(X, Y)`
is canonically isomorphic to `ModuleCat.of R (X ⟶ Y)`. -/
def cochainComplexHomologyZeroIso (X Y : C) [IsSplitEpi (G.ε.app X)] :
    (G.cochainComplex R X Y).homology 0 ≅ ModuleCat.of R (X ⟶ Y) :=
  G.cochainComplexOfFunctorHomologyZeroIso ((linearYoneda R C).obj Y) X

/-- For `G`-projective `X`, the comonad cochain complex `C_G(X, Y)` is exact in every nonzero
degree. -/
lemma exactAt_cochainComplex (X Y : C) [IsSplitEpi (G.ε.app X)] {n : ℕ} (hn : n ≠ 0) :
    (G.cochainComplex R X Y).ExactAt n :=
  G.exactAt_cochainComplexOfFunctor ((linearYoneda R C).obj Y) X hn

/-- **Vanishing of comonad cohomology for `G`-projective objects.** If the counit
`G.ε.app X : G.obj X ⟶ X` is a split epimorphism, then `Hⁿ(C_G(X, Y)) = 0` for all
`n ≠ 0`. -/
lemma isZero_cochainComplex_homology (X Y : C) [IsSplitEpi (G.ε.app X)] {n : ℕ} (hn : n ≠ 0) :
    IsZero ((G.cochainComplex R X Y).homology n) :=
  G.isZero_cochainComplexOfFunctor_homology ((linearYoneda R C).obj Y) X hn

end LinearCohomology

end CategoryTheory.Comonad
