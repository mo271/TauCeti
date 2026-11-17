/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import TauCeti.Algebra.Homology.HomotopyCofiber
import TauCeti.CategoryTheory.Linear.Yoneda

/-!
# Morphisms from a chain complex into an object

For a chain complex `X` in a `k`-linear abelian category `C` and an object `Y : C`, Mathlib's
`ChainComplex.linearYonedaObj` is the cochain complex of `k`-modules which in degree `i` is the
module of morphisms `X.X i ⟶ Y`, with differential given by precomposition with the differential
of `X`.  This file makes the construction a contravariant functor of `X`, shows that it takes a
chain homotopy to a cochain homotopy, and shows that it takes a short exact sequence of chain
complexes which is split in each degree to a short exact sequence of cochain complexes.  It also
records elementwise descriptions of the differential, cocycles, coboundaries and cohomology classes
of `Hom(X, Y)`, and of the maps between them induced by chain maps. Postcomposition
with coefficient morphisms is provided by `ChainComplex.linearYonedaObjMap`; it commutes with the
maps induced by chain maps (`ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map`).
It makes `Hom(X, -)` a functor of the coefficient object (`ChainComplex.linearYonedaObjFunctor`),
which is exact when every term of `X` is projective: it takes short exact sequences of
coefficients to short exact sequences of cochain complexes. For singular chains this gives the long
exact cohomology sequence of a short exact sequence of coefficients.

It also sends colimits of chain complexes, in particular coproducts, to limits of cochain
complexes. This uses the preservation of limits by `Hom(-, Y)`
(`CategoryTheory.preservesLimits_linearYoneda_obj`) and Mathlib's transfer of limit preservation
across opposite categories (Markus Himmel).

The functor and its action on homotopies require only a preadditive `k`-linear category.
Preservation of degreewise split short exact sequences additionally uses kernels,
cokernels and balancedness. The elementwise API uses Mathlib's
`ChainComplex.linearYonedaObj`, which is defined for abelian categories.

The functor `Hom(-, Y)` is only left exact, so the splitting hypothesis cannot be dropped.  It
holds for the singular chains of a pair of spaces, which is how the long exact sequence in
singular cohomology is obtained from the one of chain complexes.

For an `ℕ`-indexed chain complex `K` in a `k`-linear abelian category, acyclicity of `K` is
detected by the family of cochain complexes `Hom(K, Y)` as `Y` ranges over all objects of `C`,
and therefore quasi-isomorphisms of `ℕ`-indexed chain complexes are detected by the family of
functors `Hom(-, Y)`. Testing against the cokernels of the differentials turns exactness of
`Hom(K, -)` into exactness of `K`, and passing to the mapping cone reduces quasi-isomorphisms
to acyclicity.

## Main declarations

* `TauCeti.ChainComplex.linearYonedaFunctor`: the functor `X ↦ Hom(X, Y)` from chain complexes to
  cochain complexes of `k`-modules.
* `TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor`: `Hom(-, Y)` preserves short
  exactness of degreewise split sequences.
* `TauCeti.ChainComplex.mono_linearYonedaFunctor_map_op_of_epi_f`: `Hom(-, Y)` takes a degreewise
  epimorphism to a monomorphism, and
  `TauCeti.ChainComplex.mono_biprod_lift_linearYonedaFunctor_map_op_of_epi_f` does the same for a
  degreewise epimorphism `X₂ ⊞ X₃ ⟶ X₄` and the map `Hom(X₄, Y) ⟶ Hom(X₂, Y) ⊞ Hom(X₃, Y)`.
* `Homotopy.linearYonedaFunctorMap`: `Hom(-, Y)` takes a chain homotopy to a cochain homotopy.
* `HomotopyEquiv.linearYonedaFunctorMap`: `Hom(-, Y)` takes a chain homotopy
  equivalence to a cochain homotopy equivalence in the opposite direction.
* `ChainComplex.linearYonedaObjFunctor`: the functor `Y ↦ Hom(X, Y)` of the coefficients, with
  `ChainComplex.linearYonedaObjFunctorMap` the natural transformation induced by a chain map.
* `ChainComplex.shortExact_map_linearYonedaObjFunctor`: for `X` with projective terms, `Hom(X, -)`
  preserves short exact sequences.
* `TauCeti.ChainComplex.linearYonedaObjSingle₀Iso`: `Hom(-, Y)` sends the chain complex `X[0]`
  concentrated in degree zero to the cochain complex `Hom(X, Y)[0]`. It follows the unmerged Tau
  Ceti pull request https://github.com/TauCetiProject/TauCeti/pull/20882.
* `TauCeti.ChainComplex.linearYonedaObjExtendIso`: `Hom(-, Y)` commutes with extension by zero
  along matching embeddings of chain and cochain complex shapes.
* `ChainComplex.exactAt_linearYonedaObj_zero_iff` and
  `ChainComplex.exactAt_linearYonedaObj_succ_iff`: exactness of `Hom(K, Y)` for a chain complex
  `K` indexed by `ℕ`, in terms of morphisms out of the terms of `K`.
* `ChainComplex.acyclic_of_forall_acyclic_linearYonedaObj` and
  `ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor`: the family of functors
  `Hom(-, Y)` detects acyclicity and quasi-isomorphisms of `ℕ`-indexed chain complexes.
-/

public section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.ChainComplex

variable {C : Type u} [Category.{v} C] {α : Type*} [AddRightCancelSemigroup α] [One α]
  (k : Type*) [Ring k]

section Preadditive

variable [Preadditive C] [Linear k C] (Y : C)

/-- The contravariant functor sending a chain complex `X` to the cochain complex of `k`-modules
`Hom(X, Y)`, which in degree `i` is the module of morphisms `X.X i ⟶ Y`. -/
-- `@[expose]` is mandated by the module system: exported statements downstream (the singular
-- cochain maps, typed between `ChainComplex.linearYonedaObj` complexes) need
-- `(linearYonedaFunctor k Y).obj X` to unfold to `X.unop.linearYonedaObj k Y`, and an exported
-- statement may unfold only exposed definitions.
@[expose]
noncomputable def linearYonedaFunctor : (ChainComplex C α)ᵒᵖ ⥤ CochainComplex (ModuleCat k) α :=
  (((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).op ⋙
    HomologicalComplex.unopFunctor _ _

instance : (linearYonedaFunctor (α := α) k Y).Additive :=
  inferInstanceAs ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).op ⋙
    HomologicalComplex.unopFunctor _ _).Additive

/-- The contravariant chain-to-cochain functor `Hom(-, Y)` preserves limits of shape `J` in the
opposite category of chain complexes, equivalently it sends colimits of shape `Jᵒᵖ` of chains to
limits of cochains. -/
instance linearYonedaFunctor_preservesLimitsOfShape {J : Type*} [Category* J]
    [HasColimitsOfShape Jᵒᵖ C] :
    PreservesLimitsOfShape J (linearYonedaFunctor (α := α) k Y) := by
  let _ : PreservesLimitsOfShape J
      (((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down α)).op :=
    preservesLimitsOfShape_op _ _
  exact inferInstanceAs (PreservesLimitsOfShape J
    ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).op ⋙
      HomologicalComplex.unopFunctor _ _))

/-- The contravariant chain-to-cochain functor `Hom(-, Y)` preserves products in the opposite
category of chain complexes, equivalently it sends coproducts of chains to products of cochains. -/
instance linearYonedaFunctor_preservesLimitsOfShape_discrete {ι : Type*}
    [HasColimitsOfShape (Discrete ι) C] :
    PreservesLimitsOfShape (Discrete ι) (linearYonedaFunctor (α := α) k Y) :=
  have : HasColimitsOfShape (Discrete ι)ᵒᵖ C :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite ι).symm
  inferInstance

/-- `Hom(-, Y)` takes a chain homotopy between two chain maps `φ, ψ : X ⟶ X'` to a cochain
homotopy between the two maps `Hom(X', Y) ⟶ Hom(X, Y)` obtained by precomposition. -/
noncomputable def _root_.Homotopy.linearYonedaFunctorMap {X X' : ChainComplex C α} {φ ψ : X ⟶ X'}
    (h : Homotopy φ ψ) :
    Homotopy ((linearYonedaFunctor k Y).map φ.op) ((linearYonedaFunctor k Y).map ψ.op) :=
  (((linearYoneda k C).obj Y).rightOp.mapHomotopy h).unop

/-- `Hom(-, Y)` takes a chain homotopy equivalence to a cochain homotopy equivalence in
the opposite direction, with maps given by precomposition. -/
noncomputable def _root_.HomotopyEquiv.linearYonedaFunctorMap
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    _root_.HomotopyEquiv ((linearYonedaFunctor k Y).obj (op X'))
      ((linearYonedaFunctor k Y).obj (op X)) where
  hom := (linearYonedaFunctor k Y).map h.hom.op
  inv := (linearYonedaFunctor k Y).map h.inv.op
  homotopyHomInvId := by
    simpa only [← Functor.map_comp, ← op_comp] using
      (h.homotopyInvHomId.linearYonedaFunctorMap k Y).trans
        (Homotopy.ofEq ((linearYonedaFunctor k Y).map_id _))
  homotopyInvHomId := by
    simpa only [← Functor.map_comp, ← op_comp] using
      (h.homotopyHomInvId.linearYonedaFunctorMap k Y).trans
        (Homotopy.ofEq ((linearYonedaFunctor k Y).map_id _))

/-- The forward map of the induced homotopy equivalence is precomposition with `h.hom`. -/
@[simp]
lemma _root_.HomotopyEquiv.linearYonedaFunctorMap_hom
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    (h.linearYonedaFunctorMap k Y).hom =
      (linearYonedaFunctor k Y).map h.hom.op := (rfl)

/-- The inverse map of the induced homotopy equivalence is precomposition with `h.inv`. -/
@[simp]
lemma _root_.HomotopyEquiv.linearYonedaFunctorMap_inv
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    (h.linearYonedaFunctorMap k Y).inv =
      (linearYonedaFunctor k Y).map h.inv.op := (rfl)

/-- `Hom(-, Y)` takes a chain map that is an epimorphism in every degree to a monomorphism. -/
lemma mono_linearYonedaFunctor_map_op_of_epi_f {X X' : ChainComplex C α} (φ : X ⟶ X')
    (h : ∀ i, Epi (φ.f i)) : Mono ((linearYonedaFunctor k Y).map φ.op) := by
  refine HomologicalComplex.mono_of_mono_f _ fun i ↦ ?_
  rw [ModuleCat.mono_iff_injective]
  -- The component in degree `i` is precomposition with `φ.f i`, by definition.
  exact fun a a' he ↦ (cancel_epi (φ.f i)).1 he

/-- `Hom(-, Y)` takes two chain maps `f : X₂ ⟶ X₄` and `g : X₃ ⟶ X₄` whose descent
`X₂ ⊞ X₃ ⟶ X₄` is an epimorphism in every degree to a monomorphism
`Hom(X₄, Y) ⟶ Hom(X₂, Y) ⊞ Hom(X₃, Y)`. -/
lemma mono_biprod_lift_linearYonedaFunctor_map_op_of_epi_f {X₂ X₃ X₄ : ChainComplex C α}
    [HasBinaryBiproduct X₂ X₃] (f : X₂ ⟶ X₄) (g : X₃ ⟶ X₄)
    (h : ∀ i, Epi ((biprod.desc f g).f i)) :
    Mono (biprod.lift ((linearYonedaFunctor k Y).map f.op)
      ((linearYonedaFunctor k Y).map g.op)) := by
  have := mono_linearYonedaFunctor_map_op_of_epi_f k Y _ h
  have fac : biprod.lift ((linearYonedaFunctor k Y).map f.op) ((linearYonedaFunctor k Y).map g.op) ≫
      biprod.desc ((linearYonedaFunctor k Y).map biprod.fst.op)
        ((linearYonedaFunctor k Y).map biprod.snd.op) =
      (linearYonedaFunctor k Y).map (biprod.desc f g).op := by
    rw [biprod.lift_desc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, ← op_comp,
      ← op_comp, ← op_add, biprod.desc_eq]
  exact mono_of_mono_fac fac

/-- The functor `Hom(-, Y)` takes a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of chain
complexes which is split in each degree to a short exact sequence
`0 ⟶ Hom(X₃, Y) ⟶ Hom(X₂, Y) ⟶ Hom(X₁, Y) ⟶ 0` of cochain complexes. -/
lemma shortExact_map_linearYonedaFunctor
    [HasKernels C] [HasCokernels C] [Balanced C] {S : ShortComplex (ChainComplex C α)}
    (hS : S.ShortExact) [∀ i, IsSplitMono (S.f.f i)] :
    (S.op.map (linearYonedaFunctor k Y)).ShortExact := by
  let := Preadditive.hasEqualizers_of_hasKernels (C := C)
  let := Preadditive.hasCoequalizers_of_hasCokernels (C := C)
  have := hS.exact.hasZeroObject
  have := hS.epi_g
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  let : (HomologicalComplex.eval C (ComplexShape.down α) i).PreservesHomology := {}
  have hi := hS.exact.map (HomologicalComplex.eval C _ i)
  have := hi.hasZeroObject
  exact ((ShortComplex.Splitting.ofExactOfRetraction _ hi (retraction (S.f.f i))
    (IsSplitMono.id (S.f.f i))
    (inferInstance : Epi ((HomologicalComplex.eval C _ i).map S.g))).op.map
      ((linearYoneda k C).obj Y)).shortExact

end Preadditive

section Abelian

variable [Abelian C] [Linear k C] (Y : C)

@[simp]
lemma linearYonedaFunctor_obj (X : (ChainComplex C α)ᵒᵖ) :
    (linearYonedaFunctor k Y).obj X = X.unop.linearYonedaObj k Y := rfl

/-- The map `Hom(X', Y) ⟶ Hom(X, Y)` induced by a chain map `X ⟶ X'` is precomposition. -/
@[simp]
lemma linearYonedaFunctor_map_f_hom_apply {X X' : (ChainComplex C α)ᵒᵖ} (φ : X ⟶ X') (i : α)
    (g : (X.unop.linearYonedaObj k Y).X i) :
    ConcreteCategory.hom (X := (X.unop.linearYonedaObj k Y).X i)
      (Y := (X'.unop.linearYonedaObj k Y).X i) (((linearYonedaFunctor k Y).map φ).f i) g =
        φ.unop.f i ≫ g := rfl

/-- Precomposition with a scalar multiple of the identity is scalar multiplication on
`Hom(X, Y)`. -/
lemma _root_.ChainComplex.linearYonedaFunctor_map_smul_id {S : Type*} [CommRing S] [Linear S C]
    (X : ChainComplex C α) (r : S) :
    (linearYonedaFunctor S Y).map (r • 𝟙 X).op = r • 𝟙 (X.linearYonedaObj S Y) := by
  -- The functor's object and `linearYonedaObj` are definitionally the same Hom complex, so the
  -- components are `g ↦ (r • 𝟙) ≫ g` and `g ↦ r • g`; `simp` cannot see through this.
  ext i (g : X.X i ⟶ Y)
  exact (Linear.smul_comp _ _ _ r _ g).trans (congrArg (r • ·) (Category.id_comp g))

/-- The cochain homotopy induced by a chain homotopy `h` is precomposition with `h`. -/
@[simp]
lemma _root_.Homotopy.linearYonedaFunctorMap_hom_apply {X X' : ChainComplex C α} {φ ψ : X ⟶ X'}
    (h : Homotopy φ ψ) (i j : α) (g : (X'.linearYonedaObj k Y).X i) :
    ConcreteCategory.hom (X := (X'.linearYonedaObj k Y).X i) (Y := (X.linearYonedaObj k Y).X j)
      ((h.linearYonedaFunctorMap k Y).hom i j) g = h.hom j i ≫ g := (rfl)

/-- Postcomposition with a coefficient morphism induces a map of cochain complexes
`Hom(X, Y) ⟶ Hom(X, Z)`. -/
noncomputable def _root_.ChainComplex.linearYonedaObjMap (X : ChainComplex C α)
    {Y Z : C} (g : Y ⟶ Z) : X.linearYonedaObj k Y ⟶ X.linearYonedaObj k Z :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda k C).map g).rightOp.mapHomologicalComplex _).app X).op

/-- The coefficient map on cochains is postcomposition. -/
@[simp↓]
lemma _root_.ChainComplex.linearYonedaObjMap_f_hom_apply (X : ChainComplex C α)
    {Y Z : C} (g : Y ⟶ Z) (i : α) (a : X.X i ⟶ Y) :
    (X.linearYonedaObjMap k g).f i a = a ≫ g := (rfl)

/-- Identity coefficient maps induce identity maps of cochain complexes. -/
@[simp]
lemma _root_.ChainComplex.linearYonedaObjMap_id (X : ChainComplex C α) (Y : C) :
    X.linearYonedaObjMap k (𝟙 Y) = 𝟙 (X.linearYonedaObj k Y) := by
  -- The coefficient map is postcomposition by definition (`linearYonedaObjMap_f_hom_apply`).
  ext i (a : X.X i ⟶ Y)
  exact Category.comp_id a

/-- Coefficient maps on cochain complexes preserve composition. -/
@[simp]
lemma _root_.ChainComplex.linearYonedaObjMap_comp (X : ChainComplex C α)
    {Y Z T : C} (g : Y ⟶ Z) (h : Z ⟶ T) :
    X.linearYonedaObjMap k (g ≫ h) = X.linearYonedaObjMap k g ≫ X.linearYonedaObjMap k h := by
  -- The coefficient maps are postcomposition by definition (`linearYonedaObjMap_f_hom_apply`).
  ext i (a : X.X i ⟶ Y)
  exact (Category.assoc a g h).symm

/-- Coefficient maps on cochain complexes are linear in the coefficient morphism: the coefficient
map of `r • g` is `r` times the coefficient map of `g`. -/
@[simp]
lemma _root_.ChainComplex.linearYonedaObjMap_smul {S : Type*} [CommRing S] [Linear S C]
    (X : ChainComplex C α) {Y Z : C} (r : S) (g : Y ⟶ Z) :
    X.linearYonedaObjMap S (r • g) = r • X.linearYonedaObjMap S g := by
  -- The coefficient maps are postcomposition by definition (`linearYonedaObjMap_f_hom_apply`).
  ext i (a : X.X i ⟶ Y)
  exact Linear.comp_smul _ _ _ a r g

/-- Coefficient maps commute with the maps induced by chain maps: postcomposing with `g : Y ⟶ Z`
and precomposing with `β : X ⟶ X'` can be done in either order. -/
@[reassoc]
lemma _root_.ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map {X X' : ChainComplex C α}
    (β : X ⟶ X') {Y Z : C} (g : Y ⟶ Z) :
    X'.linearYonedaObjMap k g ≫ (linearYonedaFunctor k Z).map β.op =
      (linearYonedaFunctor k Y).map β.op ≫ X.linearYonedaObjMap k g := by
  ext i (a : X'.X i ⟶ Y)
  -- Both components send `a` to `β ≫ a ≫ g`. They are precomposition and postcomposition by
  -- definition (`linearYonedaFunctor_map_f_hom_apply`, `linearYonedaObjMap_f_hom_apply`), but
  -- `simp` cannot split the composite: its components live in `X.linearYonedaObj k Z` and in
  -- `(linearYonedaFunctor k Z).obj (op X)`, which agree only by unfolding.
  exact (Category.assoc (β.f i) a g).symm

/-- The coefficient map sends the class of a cocycle to the class of its image. -/
@[simp]
lemma _root_.ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply
    (X : ChainComplex C α) {Y Z : C} (g : Y ⟶ Z) (i : α)
    (a : (X.linearYonedaObj k Y).cycles i) :
    HomologicalComplex.homologyMap (X.linearYonedaObjMap k g) i
        ((X.linearYonedaObj k Y).homologyπ i a) =
      (X.linearYonedaObj k Z).homologyπ i
        (HomologicalComplex.cyclesMap (X.linearYonedaObjMap k g) i a) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality _ i) a

/-- The coefficient map on cocycles is postcomposition. -/
@[simp↓]
lemma _root_.ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply
    (X : ChainComplex C α) {Y Z : C} (g : Y ⟶ Z) (i : α)
    (a : (X.linearYonedaObj k Y).cycles i) :
    (X.linearYonedaObj k Z).iCycles i
        (HomologicalComplex.cyclesMap (X.linearYonedaObjMap k g) i a) =
      (X.linearYonedaObj k Y).iCycles i a ≫ g :=
  (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ i) a).trans
    (X.linearYonedaObjMap_f_hom_apply k g i _)

section Elementwise

variable {k Y} {X : ChainComplex C α}

/-- The differential of `Hom(X, Y)` is precomposition with the differential of `X`. -/
lemma linearYonedaObj_d_apply (i j : α) (g : (X.linearYonedaObj k Y).X i) :
    (X.linearYonedaObj k Y).d i j g = X.d j i ≫ g :=
  rfl

/-- A cocycle `a` of `Hom(X, Y)` vanishes on boundaries: `a ∘ d` is the zero of the module
`(X.linearYonedaObj k Y).X j`. -/
lemma d_comp_linearYonedaObj_iCycles (i j : α) (a : (X.linearYonedaObj k Y).cycles i) :
    X.d j i ≫ (X.linearYonedaObj k Y).iCycles i a = (0 : (X.linearYonedaObj k Y).X j) :=
  ConcreteCategory.congr_hom ((X.linearYonedaObj k Y).iCycles_d i j) a

/-- The coboundary of a cochain `g` of `Hom(X, Y)` is `g ∘ d`. -/
lemma linearYonedaObj_iCycles_toCycles_apply (i j : α) (g : (X.linearYonedaObj k Y).X i) :
    (X.linearYonedaObj k Y).iCycles j ((X.linearYonedaObj k Y).toCycles i j g) = X.d j i ≫ g :=
  ConcreteCategory.congr_hom ((X.linearYonedaObj k Y).toCycles_i i j) g

/-- A coboundary of `Hom(X, Y)` has zero cohomology class. -/
lemma linearYonedaObj_homologyπ_toCycles_apply (i j : α) (g : (X.linearYonedaObj k Y).X i) :
    (X.linearYonedaObj k Y).homologyπ j ((X.linearYonedaObj k Y).toCycles i j g) = 0 :=
  ConcreteCategory.congr_hom ((X.linearYonedaObj k Y).toCycles_comp_homologyπ i j) g

/-- The map on cohomology `H(Hom(X, Y)) ⟶ H(Hom(X', Y))` induced by a chain map `f : X' ⟶ X`
sends the class of a cocycle to the class of its image in the cocycles of `Hom(X', Y)`. -/
lemma homologyMap_linearYonedaFunctor_map_homologyπ_apply {X' : ChainComplex C α} (f : X' ⟶ X)
    (i : α) (a : (X.linearYonedaObj k Y).cycles i) :
    HomologicalComplex.homologyMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
        ((linearYonedaFunctor k Y).map f.op) i ((X.linearYonedaObj k Y).homologyπ i a) =
      (X'.linearYonedaObj k Y).homologyπ i
        (HomologicalComplex.cyclesMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
          ((linearYonedaFunctor k Y).map f.op) i a) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality _ i) a

/-- The map on cohomology `H(Hom(-, Y))` induced by a composite of chain maps `f : X'' ⟶ X'` and
`g : X' ⟶ X` is the composite of the induced maps, evaluated at a class. -/
lemma homologyMap_linearYonedaFunctor_map_comp_apply {X' X'' : ChainComplex C α} (f : X'' ⟶ X')
    (g : X' ⟶ X) (i : α) (a : (X.linearYonedaObj k Y).homology i) :
    HomologicalComplex.homologyMap (K := X.linearYonedaObj k Y) (L := X''.linearYonedaObj k Y)
        ((linearYonedaFunctor k Y).map (f ≫ g).op) i a =
      HomologicalComplex.homologyMap (K := X'.linearYonedaObj k Y) (L := X''.linearYonedaObj k Y)
        ((linearYonedaFunctor k Y).map f.op) i
        (HomologicalComplex.homologyMap (K := X.linearYonedaObj k Y)
          (L := X'.linearYonedaObj k Y) ((linearYonedaFunctor k Y).map g.op) i a) := by
  rw [op_comp, Functor.map_comp]
  exact ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp
    (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y) (M := X''.linearYonedaObj k Y)
    ((linearYonedaFunctor k Y).map g.op) ((linearYonedaFunctor k Y).map f.op) i) a

/-- The map on cocycles `Z(Hom(X, Y)) ⟶ Z(Hom(X', Y))` induced by a chain map `f : X' ⟶ X` is
precomposition with `f`. -/
lemma iCycles_cyclesMap_linearYonedaFunctor_map_apply {X' : ChainComplex C α} (f : X' ⟶ X)
    (i : α) (a : (X.linearYonedaObj k Y).cycles i) :
    (X'.linearYonedaObj k Y).iCycles i
        (HomologicalComplex.cyclesMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
          ((linearYonedaFunctor k Y).map f.op) i a) =
      f.f i ≫ (X.linearYonedaObj k Y).iCycles i a :=
  ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ i) a

end Elementwise

section CoefficientSequence

/-- For a chain complex `X`, the covariant functor `Y ↦ Hom(X, Y)` from the coefficient category to
cochain complexes of `k`-modules. Its action on morphisms is postcomposition. -/
-- `@[expose]` is mandated by the module system, as for `linearYonedaFunctor`: without it `map`
-- cannot be characterised at all, since `linearYonedaObjFunctorMap_app` and the `simps` lemmas only
-- typecheck once `obj` unfolds to `X.linearYonedaObj k Y`, and an exported statement may unfold
-- only exposed definitions. Downstream, the terms of `S.map (X.linearYonedaObjFunctor k)` must be
-- the singular cochain complexes with coefficients in the terms of `S`, for the same reason.
@[expose, simps]
noncomputable def _root_.ChainComplex.linearYonedaObjFunctor (X : ChainComplex C α) :
    C ⥤ CochainComplex (ModuleCat k) α where
  obj Y := X.linearYonedaObj k Y
  map g := X.linearYonedaObjMap k g
  map_id Y := X.linearYonedaObjMap_id k Y
  map_comp g h := X.linearYonedaObjMap_comp k g h

instance _root_.ChainComplex.linearYonedaObjFunctor_additive (X : ChainComplex C α) :
    (X.linearYonedaObjFunctor k).Additive where
  map_add {Y Z g h} := by
    ext i (a : X.X i ⟶ Y)
    -- The components of both sides send `a` to `a ≫ (g + h)` and `a ≫ g + a ≫ h`: the maps are
    -- postcomposition by definition (`linearYonedaObjMap_f_hom_apply`), and sums of cochain maps
    -- are computed degreewise and pointwise. `simp` cannot use the former, whose statement is
    -- typed in `X.linearYonedaObj k Y` rather than in the image of the functor.
    exact Preadditive.comp_add _ _ _ a g h

/-- A chain map `β : X ⟶ X'` induces, by precomposition, a natural transformation from
`Hom(X', -)` to `Hom(X, -)`. -/
noncomputable def _root_.ChainComplex.linearYonedaObjFunctorMap {X X' : ChainComplex C α}
    (β : X ⟶ X') : X'.linearYonedaObjFunctor k ⟶ X.linearYonedaObjFunctor k where
  app Y := (linearYonedaFunctor k Y).map β.op
  naturality _ _ g := X.linearYonedaObjMap_comp_linearYonedaFunctor_map k β g

@[simp]
lemma _root_.ChainComplex.linearYonedaObjFunctorMap_app {X X' : ChainComplex C α} (β : X ⟶ X')
    (Y : C) :
    (ChainComplex.linearYonedaObjFunctorMap k β).app Y = (linearYonedaFunctor k Y).map β.op :=
  (rfl)

/-- If every term of the chain complex `X` is projective, then `Hom(X, -)` takes a short exact
sequence `0 ⟶ Y₁ ⟶ Y₂ ⟶ Y₃ ⟶ 0` of coefficients to a short exact sequence of cochain complexes
`0 ⟶ Hom(X, Y₁) ⟶ Hom(X, Y₂) ⟶ Hom(X, Y₃) ⟶ 0`. -/
lemma _root_.ChainComplex.shortExact_map_linearYonedaObjFunctor (X : ChainComplex C α)
    [∀ i, Projective (X.X i)] {S : ShortComplex C} (hS : S.ShortExact) :
    (S.map (X.linearYonedaObjFunctor k)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro (a : X.X i ⟶ S.X₂) (ha : a ≫ S.g = 0)
    exact ⟨hS.exact.lift a ha, hS.exact.lift_f a ha⟩
  · rw [ModuleCat.mono_iff_injective]
    intro (a : X.X i ⟶ S.X₁) (b : X.X i ⟶ S.X₁) (h : a ≫ S.f = b ≫ S.f)
    exact (cancel_mono S.f).1 h
  · rw [ModuleCat.epi_iff_surjective]
    intro (a : X.X i ⟶ S.X₃)
    exact ⟨Projective.factorThru a S.g, Projective.factorThru_comp a S.g⟩

end CoefficientSequence

end Abelian

section Single

variable [Abelian C] [Linear k C] (X Y : C)

/-- `Hom(-, Y)` sends the chain complex with `X` in degree zero to the cochain complex with the
module `Hom(X, Y)` in degree zero. -/
noncomputable def linearYonedaObjSingle₀Iso :
    ((_root_.ChainComplex.single₀ C).obj X).linearYonedaObj k Y ≅
      (CochainComplex.single₀ (ModuleCat.{v} k)).obj (ModuleCat.of k (X ⟶ Y)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 => ((linearYoneda k C).obj Y).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X).symm.op ≪≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _).symm
      | n + 1 => IsZero.iso
          (((linearYoneda k C).obj Y).map_isZero
            (HomologicalComplex.isZero_single_obj_X _ 0 X (n + 1) n.succ_ne_zero).op)
          (HomologicalComplex.isZero_single_obj_X _ 0 _ (n + 1) n.succ_ne_zero))
    (fun i j hij ↦ (HomologicalComplex.isZero_single_obj_X _ 0 _ j (by
      simp only [ComplexShape.up_Rel] at hij; omega)).eq_of_tgt _ _)

/-- In degree zero, the comparison `Hom(X[0], Y) ≅ Hom(X, Y)[0]` sends a morphism out of the
degree-zero term of `X[0]` to its composite with the identification of `X` with that term. -/
lemma linearYonedaObjSingle₀Iso_hom_f_zero_apply
    (g : (((_root_.ChainComplex.single₀ C).obj X).linearYonedaObj k Y).X 0) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (ModuleCat.of k (X ⟶ Y))).hom
        ((linearYonedaObjSingle₀Iso k X Y).hom.f 0 g) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X).inv ≫ g :=
  -- This is the degree-zero component of the definition, followed by `singleObjXSelf`.
  (rfl)

end Single

section Extend

variable [Abelian C] [Linear k C] (Y : C)
  {α' : Type*} [AddRightCancelSemigroup α'] [One α']

private noncomputable def linearYonedaObjExtendXLeftIso (K : _root_.ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down α'))
    {i : α} {i' : α'} (hi : e.f i = i') :
    (_root_.ChainComplex.linearYonedaObj (K.extend e) k Y).X i' ≅ (K.linearYonedaObj k Y).X i :=
  ((linearYoneda k C).obj Y).mapIso (K.extendXIso e hi).symm.op

/-- `Hom(-, Y)` commutes with extension by zero along matching embeddings of chain and cochain
complex shapes: `Hom(K.extend e, Y) ≅ Hom(K, Y).extend e'`. -/
noncomputable def linearYonedaObjExtendIso (K : _root_.ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down α'))
    (e' : (ComplexShape.up α).Embedding (ComplexShape.up α'))
    (he : ∀ i, e.f i = e'.f i) :
    _root_.ChainComplex.linearYonedaObj (K.extend e) k Y ≅ (K.linearYonedaObj k Y).extend e' := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i' ↦ if h : ∃ i, e.f i = i' then
        linearYonedaObjExtendXLeftIso k Y K e h.choose_spec ≪≫
          ((K.linearYonedaObj k Y).extendXIso e' ((he h.choose).symm.trans h.choose_spec)).symm
      else
        IsZero.iso
          (((linearYoneda k C).obj Y).map_isZero
            (K.isZero_extend_X e i' fun i hi ↦ h ⟨i, hi⟩).op)
          ((K.linearYonedaObj k Y).isZero_extend_X e' i' fun i hi ↦
            h ⟨i, (he i).trans hi⟩))
    (fun i' j' _ ↦ ?_)
  by_cases hi : ∃ i, e.f i = i'
  · by_cases hj : ∃ j, e.f j = j'
    · have hi' : e'.f hi.choose = i' := (he hi.choose).symm.trans hi.choose_spec
      have hj' : e'.f hj.choose = j' := (he hj.choose).symm.trans hj.choose_spec
      rw [dite_eq_left hi, dite_eq_left hj, (K.linearYonedaObj k Y).extend_d_eq e' hi' hj']
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, ← Category.assoc, cancel_mono]
      ext (g : (K.extend e).X i' ⟶ Y)
      have hd₁ : (K.extendXIso e hj.choose_spec).inv ≫ (K.extend e).d j' i' =
          K.d hj.choose hi.choose ≫ (K.extendXIso e hi.choose_spec).inv := by
        rw [K.extend_d_eq e hj.choose_spec hi.choose_spec, Iso.inv_hom_id_assoc]
      -- Both sides evaluate precomposition in `Hom(-, Y)`; the identity is `hd₁` applied to `g`.
      exact (Category.assoc _ _ g).symm.trans
        ((congrArg (· ≫ g) hd₁.symm).trans (Category.assoc _ _ g))
    · exact ((K.linearYonedaObj k Y).isZero_extend_X e' j' fun j hfj ↦
        hj ⟨j, (he j).trans hfj⟩).eq_of_tgt _ _
  · exact (((linearYoneda k C).obj Y).map_isZero
      (K.isZero_extend_X e i' fun i hfi ↦ hi ⟨i, hfi⟩).op).eq_of_src _ _

/-- On a degree `i' = e.f i = e'.f i`, the inverse of `linearYonedaObjExtendIso` precomposes a
cochain `K.X i ⟶ Y` with `(K.extendXIso e hi).hom`. -/
lemma linearYonedaObjExtendIso_inv_f_apply (K : _root_.ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down α'))
    (e' : (ComplexShape.up α).Embedding (ComplexShape.up α'))
    (he : ∀ i, e.f i = e'.f i) {i : α} {i' : α'} (hi : e.f i = i')
    (g : ((K.linearYonedaObj k Y).extend e').X i') :
    ((linearYonedaObjExtendIso k Y K e e' he).inv.f i' g : (K.extend e).X i' ⟶ Y) =
      (K.extendXIso e hi).hom ≫
        ((K.linearYonedaObj k Y).extendXIso e' ((he i).symm.trans hi)).hom g := by
  classical
  have h : ∃ j, e.f j = i' := ⟨i, hi⟩
  have hch : h.choose = i := e.injective_f (h.choose_spec.trans hi.symm)
  subst hch
  dsimp [linearYonedaObjExtendIso]
  rw [dite_eq_left h]
  rfl

/-- On a degree `i' = e.f i = e'.f i`, `linearYonedaObjExtendIso` precomposes a cochain
`(K.extend e).X i' ⟶ Y` with `(K.extendXIso e hi).inv`. -/
lemma linearYonedaObjExtendIso_hom_f_apply (K : _root_.ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down α'))
    (e' : (ComplexShape.up α).Embedding (ComplexShape.up α'))
    (he : ∀ i, e.f i = e'.f i) {i : α} {i' : α'} (hi : e.f i = i')
    (g : (_root_.ChainComplex.linearYonedaObj (K.extend e) k Y).X i') :
    ((K.linearYonedaObj k Y).extendXIso e' ((he i).symm.trans hi)).hom
        ((linearYonedaObjExtendIso k Y K e e' he).hom.f i' g) =
      (K.extendXIso e hi).inv ≫ g := by
  classical
  have h : ∃ j, e.f j = i' := ⟨i, hi⟩
  have hch : h.choose = i := e.injective_f (h.choose_spec.trans hi.symm)
  subst hch
  dsimp [linearYonedaObjExtendIso]
  rw [dite_eq_left h]
  exact ConcreteCategory.congr_hom
    ((K.linearYonedaObj k Y).extendXIso e' ((he h.choose).symm.trans h.choose_spec)).inv_hom_id _

/-- `(linearYonedaObjExtendIso k Y _ e e' he).inv` is natural in chain maps `f : K ⟶ L`. -/
lemma linearYonedaObjExtendIso_inv_naturality {K L : _root_.ChainComplex C α} (f : K ⟶ L)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down α'))
    (e' : (ComplexShape.up α).Embedding (ComplexShape.up α'))
    (he : ∀ i, e.f i = e'.f i) :
    (linearYonedaObjExtendIso k Y L e e' he).inv ≫
        (linearYonedaFunctor k Y).map (HomologicalComplex.extendMap f e).op =
      HomologicalComplex.extendMap ((linearYonedaFunctor k Y).map f.op) e' ≫
        (linearYonedaObjExtendIso k Y K e e' he).inv := by
  ext i' : 1
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    ext g
    have hi : e.f i = e.f i := rfl
    have he' : e'.f i = e.f i := (he i).symm
    let φ : L.linearYonedaObj k Y ⟶ K.linearYonedaObj k Y := (linearYonedaFunctor k Y).map f.op
    let x : L.X i ⟶ Y := ((L.linearYonedaObj k Y).extendXIso e' he').hom g
    have hL : ((linearYonedaObjExtendIso k Y L e e' he).inv.f (e.f i) g :
        (L.extend e).X (e.f i) ⟶ Y) = (L.extendXIso e hi).hom ≫ x :=
      linearYonedaObjExtendIso_inv_f_apply k Y L e e' he hi g
    have hK := linearYonedaObjExtendIso_inv_f_apply k Y K e e' he hi
      ((HomologicalComplex.extendMap φ e').f (e.f i) g)
    have hK' : (((K.linearYonedaObj k Y).extendXIso e' he').hom
        ((HomologicalComplex.extendMap φ e').f (e.f i) g) : K.X i ⟶ Y) = f.f i ≫ x := by
      have hmap := ConcreteCategory.congr_hom (HomologicalComplex.extendMap_f φ e' he') g
      have hinv := ConcreteCategory.congr_hom
        ((K.linearYonedaObj k Y).extendXIso e' he').inv_hom_id (φ.f i x)
      exact (congrArg ((K.linearYonedaObj k Y).extendXIso e' he').hom hmap).trans hinv
    change ((HomologicalComplex.extendMap f e).f (e.f i) ≫
        (linearYonedaObjExtendIso k Y L e e' he).inv.f (e.f i) g : (K.extend e).X (e.f i) ⟶ Y) =
      (linearYonedaObjExtendIso k Y K e e' he).inv.f (e.f i)
        ((HomologicalComplex.extendMap φ e').f (e.f i) g)
    refine (congrArg ((HomologicalComplex.extendMap f e).f (e.f i) ≫ ·) hL).trans ?_
    refine (?_ : _ = (K.extendXIso e hi).hom ≫ (f.f i ≫ x)).trans ?_
    · rw [HomologicalComplex.extendMap_f f e hi, Category.assoc, Category.assoc,
        Iso.inv_hom_id_assoc]
    · exact (congrArg ((K.extendXIso e hi).hom ≫ ·) hK'.symm).trans hK.symm
  · exact ((L.linearYonedaObj k Y).isZero_extend_X e' i' fun i h ↦
      hi' ⟨i, (he i).trans h⟩).eq_of_src _ _

end Extend

section Exactness

variable [Abelian C] [Linear k C] (K : _root_.ChainComplex C ℕ) (Y : C)

/-- The complex `Hom(K, Y)` is exact in degree `0` exactly when every morphism `K₀ ⟶ Y` killed by
the differential `K₁ ⟶ K₀` is zero. -/
theorem _root_.ChainComplex.exactAt_linearYonedaObj_zero_iff :
    (K.linearYonedaObj k Y).ExactAt 0 ↔ ∀ f : K.X 0 ⟶ Y, K.d 1 0 ≫ f = 0 → f = 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero (by simp),
    ShortComplex.moduleCat_exact_iff]
  have h00 : (K.linearYonedaObj k Y).d 0 0 = 0 :=
    HomologicalComplex.shape _ 0 0 (Nat.succ_ne_zero 0)
  -- The elements of `Hom(K, Y)` in degree `0` are the morphisms `K₀ ⟶ Y`, and the zero element
  -- of `ModuleCat.of k (K₀ ⟶ Y)` is the zero morphism; `exact` uses this identification.
  refine forall_congr' fun f ↦ imp_congr Iff.rfl ⟨fun ⟨x, hx⟩ ↦ ?_, fun hf ↦ ⟨0, ?_⟩⟩
  · have h : f = 0 := by simpa [h00] using hx.symm
    exact h
  · subst hf
    exact map_zero _

/-- The complex `Hom(K, Y)` is exact in degree `n + 1` exactly when every morphism `Kₙ₊₁ ⟶ Y`
killed by the differential `Kₙ₊₂ ⟶ Kₙ₊₁` factors through the differential `Kₙ₊₁ ⟶ Kₙ`. -/
theorem _root_.ChainComplex.exactAt_linearYonedaObj_succ_iff (n : ℕ) :
    (K.linearYonedaObj k Y).ExactAt (n + 1) ↔
      ∀ f : K.X (n + 1) ⟶ Y, K.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : K.X n ⟶ Y, K.d (n + 1) n ≫ g = f := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
    (by simp), ShortComplex.moduleCat_exact_iff]
  -- The differentials of `Hom(K, Y)` are precomposition with those of `K`
  -- (`ChainComplex.linearYonedaObj_d`), so both sides are the same statement.
  rfl

/-- An `ℕ`-indexed chain complex `K` in a `k`-linear abelian category is acyclic if the cochain
complex `Hom(K, Y)` is acyclic for every object `Y`. -/
theorem _root_.ChainComplex.acyclic_of_forall_acyclic_linearYonedaObj
    (h : ∀ Y : C, (K.linearYonedaObj k Y).Acyclic) : K.Acyclic := by
  intro n
  cases n with
  | zero =>
    have hπ : cokernel.π (K.d 1 0) = 0 :=
      (K.exactAt_linearYonedaObj_zero_iff k (cokernel (K.d 1 0))).mp (h _ 0)
        _ (cokernel.condition _)
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) _root_.ChainComplex.next_nat_zero,
      ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    simp [hπ]
  | succ i =>
    obtain ⟨g, hg⟩ :=
      (K.exactAt_linearYonedaObj_succ_iff k (cokernel (K.d (i + 2) (i + 1))) i).mp (h _ (i + 1))
        (cokernel.π (K.d (i + 2) (i + 1))) (cokernel.condition _)
    rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp)
        (_root_.ChainComplex.next_nat_succ i),
      ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_f,
      HomologicalComplex.shortComplexFunctor'_obj_g]
    rw [← hg, ← Category.assoc, kernel.condition, zero_comp]

/-- A morphism `φ : K ⟶ L` of `ℕ`-indexed chain complexes in a `k`-linear abelian category is a
quasi-isomorphism if the induced map `Hom(L, Y) ⟶ Hom(K, Y)` is a quasi-isomorphism for every
object `Y`. -/
theorem _root_.ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor
    {K L : _root_.ChainComplex C ℕ} (φ : K ⟶ L)
    (h : ∀ Y : C, QuasiIso ((linearYonedaFunctor k Y).map φ.op)) : QuasiIso φ := by
  have hc : ∀ j : ℕ, ∃ i, (ComplexShape.down ℕ).Rel i j := fun j ↦ ⟨j + 1, rfl⟩
  rw [HomologicalComplex.homotopyCofiber.quasiIso_iff_acyclic φ hc]
  refine _root_.ChainComplex.acyclic_of_forall_acyclic_linearYonedaObj k _ fun Y ↦ ?_
  let α : Arrow.mk (𝟙 K) ⟶ Arrow.mk φ := Arrow.homMk (𝟙 K) φ (by simp)
  have hS₁ : (HomologicalComplex.homotopyCofiber.coneShortComplex (𝟙 K) hc).ShortExact :=
    HomologicalComplex.homotopyCofiber.coneShortComplex_shortExact (𝟙 K) hc
  have hS₂ : (HomologicalComplex.homotopyCofiber.coneShortComplex φ hc).ShortExact :=
    HomologicalComplex.homotopyCofiber.coneShortComplex_shortExact φ hc
  have : ∀ i, IsSplitMono ((HomologicalComplex.homotopyCofiber.coneShortComplex (𝟙 K) hc).f.f i) :=
    fun i ↦ IsSplitMono.mk' { retraction := HomologicalComplex.homotopyCofiber.sndX (𝟙 K) i }
  have : ∀ i, IsSplitMono ((HomologicalComplex.homotopyCofiber.coneShortComplex φ hc).f.f i) :=
    fun i ↦ IsSplitMono.mk' { retraction := HomologicalComplex.homotopyCofiber.sndX φ i }
  let τ : HomologicalComplex.homotopyCofiber.coneShortComplex (𝟙 K) hc ⟶
      HomologicalComplex.homotopyCofiber.coneShortComplex φ hc :=
    { τ₁ := φ
      τ₂ := HomologicalComplex.homotopyCofiber.mapArrowHom (𝟙 K) φ hc α
      τ₃ := 𝟙 _
      comm₁₂ := by simp [α]
      comm₂₃ := by
        simp only [Category.comp_id, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
        congr 1
        ext <;> simp [α] }
  let τ' := ((linearYonedaFunctor (α := ℕ) k Y).mapShortComplex).map (ShortComplex.opMap τ)
  have hτ₁ : QuasiIso τ'.τ₁ := by
    have heq : τ'.τ₁ = 𝟙 _ := (linearYonedaFunctor (α := ℕ) k Y).map_id _
    rw [heq]
    exact quasiIso_of_isIso (𝟙 _)
  have hτ₃ : QuasiIso τ'.τ₃ := h Y
  have hConeMap : QuasiIso ((linearYonedaFunctor (α := ℕ) k Y).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom (𝟙 K) φ hc α).op) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₂ τ'
      (shortExact_map_linearYonedaFunctor k Y hS₂)
      (shortExact_map_linearYonedaFunctor k Y hS₁) hτ₁ hτ₃
  have hIdAcyclic :
      ((linearYonedaFunctor (α := ℕ) k Y).obj
        (op (HomologicalComplex.homotopyCofiber (𝟙 K)))).Acyclic := by
    have hHom : Homotopy
        (𝟙 ((linearYonedaFunctor (α := ℕ) k Y).obj
          (op (HomologicalComplex.homotopyCofiber (𝟙 K))))) 0 :=
      (Homotopy.ofEq ((linearYonedaFunctor (α := ℕ) k Y).map_id _).symm).trans
        (((HomologicalComplex.homotopyCofiber.homotopyToZeroOfId K hc).linearYonedaFunctorMap
            k Y).trans
          (Homotopy.ofEq (Functor.map_zero _ _ _)))
    exact hHom.acyclic
  intro i
  exact (exactAt_iff_of_quasiIsoAt
    ((linearYonedaFunctor (α := ℕ) k Y).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom (𝟙 K) φ hc α).op) i).mpr (hIdAcyclic i)

end Exactness

end TauCeti.ChainComplex
