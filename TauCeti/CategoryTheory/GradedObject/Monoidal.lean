/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.GradedObject

/-!
# Exactness, linearity, and reindexing for tensor products of graded objects

The tensor product of two graded objects `X` and `Y` has the coproduct of the `X i ⊗ Y j` with
`i + j = n` in degree `n` (`CategoryTheory.GradedObject.Monoidal.tensorObj`).  This file records
facts about these coproducts which are used both to compare homology of tensor products of
complexes and to work with `R`-linear monoidal categories of graded objects.

* The map of coproducts over the fibres of a map induced by a morphism of graded objects is a
  map of colimits of discrete diagrams (`CategoryTheory.GradedObject.mapMap_eq_colimMap`).
* A family of monomorphisms induces a monomorphism on coproducts over the fibres of a map, when
  colimits of that shape preserve monomorphisms (`CategoryTheory.GradedObject.mono_mapMap`), and
  a family of epimorphisms induces an epimorphism (`CategoryTheory.GradedObject.epi_mapMap`).
  When these coproducts are exact, a family of exact sequences induces an exact sequence
  (`CategoryTheory.GradedObject.exact_mapMap`), and likewise a family of short exact sequences
  induces a short exact sequence (`CategoryTheory.GradedObject.shortExact_mapMap`).  In particular
  the tensor product of morphisms of graded objects is a monomorphism in a degree with finitely
  many summands as soon as each summand is
  (`CategoryTheory.GradedObject.Monoidal.mono_tensorHom`), for instance in every degree for graded
  objects indexed by `ℕ`.  Tensoring with an identity is the map of coproducts induced by the
  whiskerings (`CategoryTheory.GradedObject.Monoidal.id_tensorHom_eq_mapMap`), so these facts
  apply to it.
* The inclusion of a summand `X i ⊗ Y j` into the tensor product is a split monomorphism in a
  category with zero morphisms (`CategoryTheory.GradedObject.Monoidal.isSplitMono_ιTensorObj`).
* Whiskering of graded objects is additive and `R`-linear whenever `C` is `MonoidalPreadditive`
  (resp. `MonoidalLinear R`), giving `MonoidalPreadditive (GradedObject I C)` and
  `MonoidalLinear R (GradedObject I C)`.
* The tensor product of two single-degree graded objects `(single i).obj A` and `(single j).obj B`
  exists whenever `C` has an initial object preserved by tensoring on either side
  (`CategoryTheory.GradedObject.Monoidal.hasTensor_single`), is canonically isomorphic to
  `(single (i + j)).obj (A ⊗ B)` (`CategoryTheory.GradedObject.Monoidal.singleTensorIso`),
  naturally in `A` and `B` (`singleTensorIso_naturality`), and is compatible with the left and
  right unitors (`singleTensorIso_leftUnitor`, `singleTensorIso_rightUnitor`).
* For graded objects indexed by `ℕ`, if `Y 0 = 0` then the summands of `X ⊗ Y` in degree
  `m + 1` are those of `X` tensored with `Y` shifted down by one, in degree `m`
  (`CategoryTheory.GradedObject.Monoidal.tensorObjSuccIso`).  This identifies the degree shift of
  a connecting morphism between tensor products.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject

variable {I J C : Type*} [Category* C]

/-- The map of coproducts over the fibre of `p : I → J` over `j` induced by a morphism of graded
objects is the map of colimits of the corresponding discrete diagrams. -/
lemma mapMap_eq_colimMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) :
    mapMap φ p j = colimMap (Discrete.natTrans fun i ↦ φ i.as.1 :
      Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j)) := by
  refine mapObj_ext _ _ _ _ fun i hi ↦ ?_
  rw [ι_mapMap]
  -- `ιMapObj` is the colimit inclusion `Sigma.ι` of the discrete diagram `mapObjFun`
  exact (ι_colimMap (Discrete.natTrans fun i ↦ φ i.as.1 :
    Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j)) ⟨⟨i, hi⟩⟩).symm

/-- A morphism of graded objects which is a monomorphism in each degree induces a monomorphism on
the coproducts over the fibre of `p : I → J` over `j`, when colimits of that shape preserve
monomorphisms. -/
lemma mono_mapMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [(colim : (Discrete (p ⁻¹' {j}) ⥤ C) ⥤ C).PreservesMonomorphisms]
    [hφ : ∀ i, Mono (φ i)] : Mono (mapMap φ p j) := by
  let α : Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natTrans fun i ↦ φ i.as.1
  have : ∀ i, Mono (α.app i) := fun i ↦ inferInstanceAs (Mono (φ i.as.1))
  have : Mono α := NatTrans.mono_of_mono_app _
  rw [mapMap_eq_colimMap, ← colim_map]
  exact CategoryTheory.Functor.map_mono colim α

/-- A morphism of graded objects which is an epimorphism in each degree induces an epimorphism on
the coproducts over the fibre of `p : I → J` over `j`. -/
lemma epi_mapMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) [∀ i, Epi (φ i)] : Epi (mapMap φ p j) where
  left_cancellation g₁ g₂ h := mapObj_ext _ _ _ _ fun i hi ↦ by
    rw [← cancel_epi (φ i), ← ι_mapMap_assoc φ p i j hi, h, ι_mapMap_assoc]

/-- A short complex of graded objects which is exact in each degree induces an exact sequence on
the coproducts over the fibre of `p : I → J` over `j`, when coproducts of that shape are exact. -/
lemma exact_mapMap [Abelian C] (S : ShortComplex (GradedObject I C)) (p : I → J)
    [S.X₁.HasMap p] [S.X₂.HasMap p] [S.X₃.HasMap p] (j : J)
    [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    (hS : ∀ i, (ShortComplex.mk (S.f i) (S.g i) (congr_fun S.zero i)).Exact) :
    (ShortComplex.mk (mapMap S.f p j) (mapMap S.g p j) (by
      rw [← Pi.comp_apply, ← mapMap_comp, S.zero]; ext; simp)).Exact := by
  -- the coproducts over the fibre are the colimits of the corresponding discrete diagrams, and
  -- `colim` is exact
  let T : ShortComplex (Discrete (p ⁻¹' {j}) ⥤ C) :=
    ShortComplex.mk (X₁ := Discrete.functor (S.X₁.mapObjFun p j))
      (X₂ := Discrete.functor (S.X₂.mapObjFun p j)) (X₃ := Discrete.functor (S.X₃.mapObjFun p j))
      (Discrete.natTrans fun i ↦ S.f i.as.1) (Discrete.natTrans fun i ↦ S.g i.as.1)
      (by ext i; exact congr_fun S.zero i.as.1)
  have hT : T.Exact := by
    have hP : JointlyReflectIsomorphisms fun i : Discrete (p ⁻¹' {j}) ↦ (evaluation _ C).obj i :=
      ⟨fun f h ↦ have : ∀ i, IsIso (f.app i) := h; NatIso.isIso_of_isIso_app f⟩
    rw [hP.exact_iff]
    exact fun i ↦ hS i.as.1
  exact colim.exact_mapShortComplex hT (colimit.isColimit _) (colimit.isColimit _)
    (colimit.isColimit _) (mapMap S.f p j) (mapMap S.g p j)
    (fun i ↦ ι_mapMap S.f p i.as.1 j i.as.2) (fun i ↦ ι_mapMap S.g p i.as.1 j i.as.2)

/-- A short complex of graded objects which is short exact in each degree induces a short exact
sequence on the coproducts over the fibre of `p : I → J` over `j`, when coproducts of that shape
are exact. -/
lemma shortExact_mapMap [Abelian C] (S : ShortComplex (GradedObject I C)) (p : I → J)
    [S.X₁.HasMap p] [S.X₂.HasMap p] [S.X₃.HasMap p] (j : J)
    [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    (hS : ∀ i, (ShortComplex.mk (S.f i) (S.g i) (congr_fun S.zero i)).ShortExact) :
    (ShortComplex.mk (mapMap S.f p j) (mapMap S.g p j) (by
      rw [← Pi.comp_apply, ← mapMap_comp, S.zero]; ext; simp)).ShortExact :=
  have (i : I) : Mono (S.f i) := (hS i).mono_f
  have (i : I) : Epi (S.g i) := (hS i).epi_g
  { exact := exact_mapMap S p j fun i ↦ (hS i).exact
    mono_f := mono_mapMap S.f p j
    epi_g := epi_mapMap S.g p j }

namespace Monoidal

/-- In a degree `n` with finitely many pairs `i + j = n`, the tensor product of two morphisms of
graded objects is a monomorphism as soon as each of its summands `f i ⊗ g j` is, in a category
with zero morphisms and finite biproducts. -/
lemma mono_tensorHom [AddMonoid I] [MonoidalCategory C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] {X₁ X₂ Y₁ Y₂ : GradedObject I C}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] (n : I)
    (hn : Set.Finite {x : I × I | x.1 + x.2 = n}) [∀ i j, Mono (f i ⊗ₘ g j)] :
    Mono (tensorHom f g n) := by
  have : Finite ((fun (⟨i, j⟩ : I × I) ↦ i + j) ⁻¹' {n}) := hn.to_subtype
  unfold tensorHom mapBifunctorMapMap
  refine mono_mapMap _ _ n (hφ := fun ⟨i, j⟩ ↦ ?_)
  -- Compute the component of the bifunctor map to identify it with the tensor product.
  rw [Pi.comp_apply]
  dsimp only [mapBifunctor, curriedTensor]
  rw [← MonoidalCategory.tensorHom_def]
  infer_instance

/-- Tensoring a morphism of graded objects with the identity of `X` is, in each degree, the map of
coproducts induced by the morphisms `X i ◁ g j`. -/
lemma id_tensorHom_eq_mapMap [AddMonoid I] [MonoidalCategory C] (X : GradedObject I C)
    {Y Y' : GradedObject I C} (g : Y ⟶ Y') [HasTensor X Y] [HasTensor X Y'] (n : I) :
    tensorHom (𝟙 X) g n =
      mapMap (((mapBifunctor (curriedTensor C) I I).obj X).map g) (fun x ↦ x.1 + x.2) n := by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

/-- The inclusion of the summand `X₁ i₁ ⊗ X₂ i₂` into the tensor product of graded objects in
degree `i₁ + i₂` is a split monomorphism in a category with zero morphisms, being a coprojection
into a coproduct. -/
instance isSplitMono_ιTensorObj [AddMonoid I] [MonoidalCategory C] [HasZeroMorphisms C]
    (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    IsSplitMono (ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h) := by
  unfold ιTensorObj ιMapBifunctorMapObj GradedObject.ιMapObj
  exact isSplitMono_sigma_ι _ _

section PreadditiveLinear

variable [AddMonoid I] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]

/-- Left whiskering a zero morphism of graded objects gives zero. -/
lemma whiskerLeft_zero (X Y Z : GradedObject I C) [HasTensor X Y] [HasTensor X Z] :
    whiskerLeft X (0 : Y ⟶ Z) = 0 := by
  ext n i j h
  rw [whiskerLeft, ι_tensorHom]
  simp

/-- Right whiskering a zero morphism of graded objects gives zero. -/
lemma zero_whiskerRight (X Y Z : GradedObject I C) [HasTensor X Z] [HasTensor Y Z] :
    whiskerRight (0 : X ⟶ Y) Z = 0 := by
  ext n i j h
  rw [whiskerRight, ι_tensorHom]
  simp

/-- Left whiskering of graded objects preserves sums of morphisms. -/
lemma whiskerLeft_add (X : GradedObject I C) {Y Z : GradedObject I C} (f g : Y ⟶ Z)
    [HasTensor X Y] [HasTensor X Z] :
    whiskerLeft X (f + g) = whiskerLeft X f + whiskerLeft X g := by
  ext n i j h
  rw [add_apply, Preadditive.comp_add, whiskerLeft, whiskerLeft, whiskerLeft,
    ι_tensorHom, ι_tensorHom, ι_tensorHom, add_apply]
  simp [MonoidalCategory.id_tensorHom, Preadditive.add_comp]

/-- Right whiskering of graded objects preserves sums of morphisms. -/
lemma add_whiskerRight {X Y : GradedObject I C} (f g : X ⟶ Y) (Z : GradedObject I C)
    [HasTensor X Z] [HasTensor Y Z] :
    whiskerRight (f + g) Z = whiskerRight f Z + whiskerRight g Z := by
  ext n i j h
  rw [add_apply, Preadditive.comp_add, whiskerRight, whiskerRight, whiskerRight,
    ι_tensorHom, ι_tensorHom, ι_tensorHom, add_apply]
  simp [MonoidalCategory.tensorHom_id, Preadditive.add_comp]

variable {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]

/-- Left whiskering of graded objects preserves scalar multiplication. -/
lemma whiskerLeft_smul (X : GradedObject I C) {Y Z : GradedObject I C} (r : R) (f : Y ⟶ Z)
    [HasTensor X Y] [HasTensor X Z] :
    whiskerLeft X (r • f) = r • whiskerLeft X f := by
  ext n i j h
  rw [smul_apply, Linear.comp_smul, whiskerLeft, whiskerLeft, ι_tensorHom, ι_tensorHom, smul_apply]
  simp [MonoidalCategory.id_tensorHom]

/-- Right whiskering of graded objects preserves scalar multiplication. -/
lemma smul_whiskerRight (r : R) {X Y : GradedObject I C} (f : X ⟶ Y) (Z : GradedObject I C)
    [HasTensor X Z] [HasTensor Y Z] :
    whiskerRight (r • f) Z = r • whiskerRight f Z := by
  ext n i j h
  rw [smul_apply, Linear.comp_smul, whiskerRight, whiskerRight, ι_tensorHom, ι_tensorHom,
    smul_apply]
  simp [MonoidalCategory.tensorHom_id]

end PreadditiveLinear

section SingleTensor

variable [AddMonoid I] [DecidableEq I] [MonoidalCategory C] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- The convolution tensor product of two single-degree graded objects exists whenever `C` has an
initial object preserved by tensoring on either side. -/
instance hasTensor_single (i j : I) (A B : C) :
    HasTensor ((single i).obj A) ((single j).obj B) := by
  intro n
  let p : I × I → I := fun ⟨a, b⟩ ↦ a + b
  let f := (((mapBifunctor (curriedTensor C) I I).obj ((single i).obj A)).obj
    ((single j).obj B)).mapObjFun p n
  let hinit (k : p ⁻¹' {n}) (h : k.1.1 ≠ i ∨ k.1.2 ≠ j) : IsInitial (f k) :=
    if ha : k.1.1 = i then
      (isInitialSingleObjApply j B k.1.2 (h.resolve_left (not_not.mpr ha))).isInitialObj
        ((curriedTensor C).obj _)
    else
      (isInitialSingleObjApply i A k.1.1 ha).isInitialObj ((curriedTensor C).flip.obj _)
  by_cases hn : n = i + j
  · let k₀ : p ⁻¹' {n} := ⟨(i, j), hn.symm⟩
    have hne : ∀ k : p ⁻¹' {n}, k ≠ k₀ → k.1.1 ≠ i ∨ k.1.2 ≠ j := fun k hk ↦ by
      by_contra h
      rw [not_or, not_ne_iff, not_ne_iff] at h
      exact hk (Subtype.ext (Prod.ext h.1 h.2))
    let c : Cofan f := Cofan.mk (f k₀) fun k ↦
      if hk : k = k₀ then eqToHom (congrArg f hk) else (hinit k (hne k hk)).to (f k₀)
    refine ⟨⟨⟨c, Cofan.IsColimit.mk c (fun s ↦ s.inj k₀) (fun s k ↦ ?_) (fun s m hm ↦ ?_)⟩⟩⟩
    · by_cases hk : k = k₀
      · subst hk; simp [c]
      · exact (hinit k (hne k hk)).hom_ext _ _
    · simpa [c] using hm k₀
  · have hne : ∀ k : p ⁻¹' {n}, k.1.1 ≠ i ∨ k.1.2 ≠ j := fun k ↦ by
      by_contra h
      rw [not_or, not_ne_iff, not_ne_iff] at h
      exact hn (by simpa [p, h.1, h.2] using (Set.mem_singleton_iff.mp k.2).symm)
    let c : Cofan f := Cofan.mk (⊥_ C) fun k ↦ (hinit k (hne k)).to (⊥_ C)
    exact ⟨⟨⟨c, Cofan.IsColimit.mk c (fun s ↦ initial.to s.pt)
      (fun s k ↦ (hinit k (hne k)).hom_ext _ _) (fun _ _ _ ↦ initial.hom_ext _ _)⟩⟩⟩

/-- The convolution tensor product of two single-degree graded objects `(single i).obj A` and
`(single j).obj B` is canonically isomorphic to `(single (i + j)).obj (A ⊗ B)`. -/
def singleTensorIso (i j : I) (A B : C) :
    tensorObj ((single i).obj A) ((single j).obj B) ≅ (single (i + j)).obj (A ⊗ B) where
  hom n := tensorObjDesc fun a b h ↦
    if ha : a = i then
      if hb : b = j then
        ((singleObjApplyIsoOfEq i A a ha).hom ⊗ₘ (singleObjApplyIsoOfEq j B b hb).hom) ≫
          (singleObjApplyIsoOfEq (i + j) (A ⊗ B) n (by rw [← h, ha, hb])).inv
      else
        ((isInitialSingleObjApply j B b hb).isInitialObj ((curriedTensor C).obj _)).to _
    else
      ((isInitialSingleObjApply i A a ha).isInitialObj ((curriedTensor C).flip.obj _)).to _
  inv n :=
    if hn : n = i + j then
      (singleObjApplyIsoOfEq (i + j) (A ⊗ B) n hn).hom ≫
        ((singleObjApplyIso i A).inv ⊗ₘ (singleObjApplyIso j B).inv) ≫
        ιTensorObj ((single i).obj A) ((single j).obj B) i j n hn.symm
    else
      (isInitialSingleObjApply (i + j) (A ⊗ B) n hn).to _
  hom_inv_id := by
    ext n a b h
    dsimp [categoryOfGradedObjects_comp]
    rw [ι_tensorObjDesc_assoc]
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = j
      · subst hb
        simp [h.symm, MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      · exact ((isInitialSingleObjApply j B b hb).isInitialObj
          ((curriedTensor C).obj _)).hom_ext _ _
    · exact ((isInitialSingleObjApply i A a ha).isInitialObj
        ((curriedTensor C).flip.obj _)).hom_ext _ _
  inv_hom_id := by
    funext n
    dsimp [categoryOfGradedObjects_comp]
    by_cases hn : n = i + j
    · subst hn
      simp [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    · exact (isInitialSingleObjApply (i + j) (A ⊗ B) n hn).hom_ext _ _

/-- On the unique nontrivial summand `(i, j)`, `singleTensorIso` identifies `X i ⊗ Y j` with
`A ⊗ B` via the degree-identification isomorphisms. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_singleTensorIso_hom (i j n : I) (h : i + j = n) (A B : C) :
    ιTensorObj ((single i).obj A) ((single j).obj B) i j n h ≫
        (singleTensorIso i j A B).hom n =
      ((singleObjApplyIso i A).hom ⊗ₘ (singleObjApplyIso j B).hom) ≫
        (singleObjApplyIsoOfEq (i + j) (A ⊗ B) n h.symm).inv := by
  subst h
  simp [singleTensorIso]

/-- On degree `i + j`, the inverse of `singleTensorIso` maps `A ⊗ B` into the `(i, j)` summand. -/
@[reassoc (attr := simp)]
lemma singleObjApplyIso_inv_singleTensorIso_inv (i j n : I) (h : n = i + j) (A B : C) :
    (singleObjApplyIsoOfEq (i + j) (A ⊗ B) n h).inv ≫ (singleTensorIso i j A B).inv n =
      ((singleObjApplyIso i A).inv ⊗ₘ (singleObjApplyIso j B).inv) ≫
        ιTensorObj ((single i).obj A) ((single j).obj B) i j n h.symm := by
  subst h
  simp [singleTensorIso]

/-- `singleTensorIso` is natural in both arguments. -/
@[reassoc]
lemma singleTensorIso_naturality (i j : I) {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom ((single i).map f) ((single j).map g) ≫ (singleTensorIso i j A' B').hom =
      (singleTensorIso i j A B).hom ≫ (single (i + j)).map (f ⊗ₘ g) := by
  ext n a b h
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = j
    · subst hb
      dsimp only [categoryOfGradedObjects_comp]
      rw [ι_tensorHom_assoc, ιTensorObj_singleTensorIso_hom, ιTensorObj_singleTensorIso_hom_assoc,
        ← cancel_mono (singleObjApplyIsoOfEq (a + b) (A' ⊗ B') n h.symm).hom]
      simp [Category.assoc, single_map_singleObjApplyIsoOfEq_hom,
        MonoidalCategory.tensorHom_comp_tensorHom]
    · exact ((isInitialSingleObjApply j B b hb).isInitialObj
        ((curriedTensor C).obj _)).hom_ext _ _
  · exact ((isInitialSingleObjApply i A a ha).isInitialObj
      ((curriedTensor C).flip.obj _)).hom_ext _ _

/-- Left whiskering commutes with `singleTensorIso`. -/
@[reassoc]
lemma whiskerLeft_single_map_singleTensorIso_hom (i j : I) (A : C) {B B' : C} (g : B ⟶ B') :
    whiskerLeft ((single i).obj A) ((single j).map g) ≫ (singleTensorIso i j A B').hom =
      (singleTensorIso i j A B).hom ≫ (single (i + j)).map (A ◁ g) := by
  simpa [whiskerLeft, MonoidalCategory.id_tensorHom] using
    singleTensorIso_naturality i j (𝟙 A) g

/-- Right whiskering commutes with `singleTensorIso`. -/
@[reassoc]
lemma whiskerRight_single_map_singleTensorIso_hom (i j : I) {A A' : C} (f : A ⟶ A') (B : C) :
    whiskerRight ((single i).map f) ((single j).obj B) ≫ (singleTensorIso i j A' B).hom =
      (singleTensorIso i j A B).hom ≫ (single (i + j)).map (f ▷ B) := by
  simpa [whiskerRight, MonoidalCategory.tensorHom_id] using
    singleTensorIso_naturality i j f (𝟙 B)

/-- The left unitor on `(single j).obj B` agrees with `singleTensorIso 0 j (𝟙_ C) B` composed with
`λ_ B`. -/
lemma singleTensorIso_leftUnitor (j : I) (B : C) :
    (singleTensorIso 0 j (𝟙_ C) B).hom ≫ (single (0 + j)).map (λ_ B).hom ≫
        eqToHom (congrArg (fun k ↦ (single k).obj B) (zero_add j)) =
      (leftUnitor ((single j).obj B)).hom := by
  -- `leftUnitor` is typed with `tensorUnit`, which is definitionally `(single 0).obj (𝟙_ C)`.
  refine (cancel_epi (leftUnitor ((single j).obj B)).inv).1 ?_
  refine (Iso.inv_hom_id (leftUnitor ((single j).obj B))).symm ▸ ?_
  funext n
  by_cases hn : n = j
  · subst hn
    have h0 : (0 : I) + n = n := zero_add n
    -- Unfold `(leftUnitor _).inv n` and `tensorUnit` uniformly to `(single 0).obj (𝟙_ C)`.
    change ((λ_ ((single n).obj B n)).inv ≫ (singleObjApplyIso (0 : I) (𝟙_ C)).inv ▷ _ ≫
          ιTensorObj ((single (0 : I)).obj (𝟙_ C)) ((single n).obj B) 0 n n h0) ≫
        (singleTensorIso 0 n (𝟙_ C) B).hom n ≫ (single (0 + n)).map (λ_ B).hom n ≫
        (eqToHom (congrArg (fun k ↦ (single k).obj B) h0) : _ ⟶ _) n = 𝟙 _
    rw [← cancel_mono (singleObjApplyIso n B).hom]
    simp only [Category.id_comp, Category.assoc]
    rw [eqToHom_single_comp_singleObjApplyIso_hom h0 B, single_map_singleObjApplyIsoOfEq_hom,
      ιTensorObj_singleTensorIso_hom_assoc 0 n n h0 (𝟙_ C) B, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Iso.inv_hom_id, Category.id_comp, MonoidalCategory.id_tensorHom,
      MonoidalCategory.leftUnitor_naturality, Iso.inv_hom_id_assoc]
  · exact (isInitialSingleObjApply j B n hn).hom_ext _ _

/-- The right unitor on `(single i).obj A` agrees with `singleTensorIso i 0 A (𝟙_ C)` composed with
`ρ_ A`. -/
lemma singleTensorIso_rightUnitor (i : I) (A : C) :
    (singleTensorIso i 0 A (𝟙_ C)).hom ≫ (single (i + 0)).map (ρ_ A).hom ≫
        eqToHom (congrArg (fun k ↦ (single k).obj A) (add_zero i)) =
      (rightUnitor ((single i).obj A)).hom := by
  -- `rightUnitor` is typed with `tensorUnit`, which is definitionally `(single 0).obj (𝟙_ C)`.
  refine (cancel_epi (rightUnitor ((single i).obj A)).inv).1 ?_
  refine (Iso.inv_hom_id (rightUnitor ((single i).obj A))).symm ▸ ?_
  funext n
  by_cases hn : n = i
  · subst hn
    have h0 : n + (0 : I) = n := add_zero n
    -- Unfold `(rightUnitor _).inv n` and `tensorUnit` uniformly to `(single 0).obj (𝟙_ C)`.
    change ((ρ_ ((single n).obj A n)).inv ≫ _ ◁ (singleObjApplyIso (0 : I) (𝟙_ C)).inv ≫
          ιTensorObj ((single n).obj A) ((single (0 : I)).obj (𝟙_ C)) n 0 n h0) ≫
        (singleTensorIso n 0 A (𝟙_ C)).hom n ≫ (single (n + 0)).map (ρ_ A).hom n ≫
        (eqToHom (congrArg (fun k ↦ (single k).obj A) h0) : _ ⟶ _) n = 𝟙 _
    rw [← cancel_mono (singleObjApplyIso n A).hom]
    simp only [Category.id_comp, Category.assoc]
    rw [eqToHom_single_comp_singleObjApplyIso_hom h0 A, single_map_singleObjApplyIsoOfEq_hom,
      ιTensorObj_singleTensorIso_hom_assoc n 0 n h0 A (𝟙_ C), Iso.inv_hom_id_assoc,
      ← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Iso.inv_hom_id, Category.id_comp, MonoidalCategory.tensorHom_id,
      MonoidalCategory.rightUnitor_naturality, Iso.inv_hom_id_assoc]
  · exact (isInitialSingleObjApply i A n hn).hom_ext _ _

end SingleTensor

variable [HasZeroMorphisms C] [MonoidalCategory C] (X Y : GradedObject ℕ C)
  [∀ p, (tensorLeft (X p)).PreservesZeroMorphisms] (hY : IsZero (Y 0))
  [HasTensor X Y] [HasTensor X (fun q ↦ Y (q + 1))] (m : ℕ)

/-- For graded objects indexed by `ℕ` with `Y 0 = 0`, the tensor product of `X` with `Y` shifted
down by one in degree `m` is the tensor product of `X` and `Y` in degree `m + 1`: both are the
coproduct of the `X p ⊗ Y (q + 1)` with `p + q = m`. -/
def tensorObjSuccIso : tensorObj X (fun q ↦ Y (q + 1)) m ≅ tensorObj X Y (m + 1) where
  hom := tensorObjDesc fun p q h ↦ ιTensorObj X Y p (q + 1) (m + 1) (by omega)
  inv := tensorObjDesc fun p q h ↦ match q, h with
    | 0, _ => 0
    | q + 1, h => ιTensorObj X (fun q ↦ Y (q + 1)) p q m (by omega)
  hom_inv_id := by ext; simp
  inv_hom_id := by
    ext p q h
    match q, h with
    | 0, _ => exact ((tensorLeft _).map_isZero hY).eq_of_src _ _
    | q + 1, h => simp

/-- `tensorObjSuccIso` sends the summand `X p ⊗ Y (q + 1)` of degree `m` to the same summand of
degree `m + 1`. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjSuccIso_hom (p q : ℕ) (h : p + q = m) :
    ιTensorObj X (fun q ↦ Y (q + 1)) p q m h ≫ (tensorObjSuccIso X Y hY m).hom =
      ιTensorObj X Y p (q + 1) (m + 1) (by omega) := by
  simp [tensorObjSuccIso]

/-- The inverse of `tensorObjSuccIso` sends the summand `X p ⊗ Y (q + 1)` of degree `m + 1` to the
same summand of degree `m`. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjSuccIso_inv (p q : ℕ) (h : p + (q + 1) = m + 1) :
    ιTensorObj X Y p (q + 1) (m + 1) h ≫ (tensorObjSuccIso X Y hY m).inv =
      ιTensorObj X (fun q ↦ Y (q + 1)) p q m (by omega) := by
  simp [tensorObjSuccIso]

end Monoidal

section MonoidalPreadditiveLinear

variable [AddMonoid I] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The monoidal category of `I`-graded objects in a monoidal preadditive category is monoidal
preadditive. -/
instance monoidalPreadditive : MonoidalPreadditive (GradedObject I C) where
  whiskerLeft_zero := Monoidal.whiskerLeft_zero _ _ _
  zero_whiskerRight := Monoidal.zero_whiskerRight _ _ _
  whiskerLeft_add _ _ := Monoidal.whiskerLeft_add _ _ _
  add_whiskerRight _ _ := Monoidal.add_whiskerRight _ _ _

/-- The monoidal category of `I`-graded objects in an `R`-linear monoidal category is `R`-linear
monoidal. -/
instance monoidalLinear (R : Type*) [Semiring R] [Linear R C] [MonoidalLinear R C] :
    MonoidalLinear R (GradedObject I C) where
  whiskerLeft_smul X _ _ r f := Monoidal.whiskerLeft_smul X r f
  smul_whiskerRight r _ _ f X := Monoidal.smul_whiskerRight r f X

end MonoidalPreadditiveLinear

end CategoryTheory.GradedObject
