/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Augmented
public import TauCeti.AlgebraicTopology.SimplicialObject.Op

/-!
# Extra degeneracies for free objects in a comonad resolution

For any comonad `G` on a category `C` and any object `W : C`, the comultiplication `G.δ.app W`
splits `G.ε.app (G.obj W)` and induces a right extra degeneracy on the augmented simplicial
resolution of the free object `G.obj W`, with degree-`n` map given by applying `G^{n+1}` to
`G.δ.app W` (transported along the canonical stage-shift isomorphism
`G.compResolutionStageIso`). Its splitting face is the last face in each degree.

Reversing the simplicial part via `SimplicialObject.Augmented.opFunctor` turns the last face into
face `0`, yielding an `ExtraDegeneracy` in the sense of Mathlib
(`CategoryTheory.Comonad.freeReversedResolutionExtraDegeneracy`).

## References

* M. Barr and J. Beck, *Homology and standard constructions*, Seminar on Triples and Categorical
  Homology Theory, Lecture Notes in Math. 80, Springer, 1969, §1.
* A. Gainutdinov, J. Haferkamp, and C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Lemma 2.5(1).
-/

public noncomputable section

open CategoryTheory Opposite Functor

open scoped Simplicial

universe v u

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] (G : Comonad C)

/-- Shifting one application of `G` from the inside to the outside of `G.resolutionStage n`. -/
def compResolutionStageIso :
    ∀ n : ℕ, (G : C ⥤ C) ⋙ G.resolutionStage n ≅ G.resolutionStage (n + 1)
  | 0 => NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
      dsimp only [resolutionStage, Functor.comp_map, Functor.id_map, Iso.refl_hom]
      rw [Category.comp_id, Category.id_comp]
  | n + 1 =>
      NatIso.ofComponents (fun W ↦ G.mapIso ((compResolutionStageIso n).app W))
        fun {X Y} f ↦ by
          dsimp only [resolutionStage, Functor.comp_obj, Functor.comp_map, Functor.mapIso_hom]
          rw [← G.map_comp, ← G.map_comp]
          exact congrArg G.map ((compResolutionStageIso n).hom.naturality f)

@[simp]
lemma compResolutionStageIso_zero_hom_app (W : C) :
    (G.compResolutionStageIso 0).hom.app W = 𝟙 (G.obj W) := (rfl)

@[simp]
lemma compResolutionStageIso_zero_inv_app (W : C) :
    (G.compResolutionStageIso 0).inv.app W = 𝟙 (G.obj W) := (rfl)

@[simp]
lemma compResolutionStageIso_succ_hom_app (n : ℕ) (W : C) :
    (G.compResolutionStageIso (n + 1)).hom.app W =
      G.map ((G.compResolutionStageIso n).hom.app W) := (rfl)

@[simp]
lemma compResolutionStageIso_succ_inv_app (n : ℕ) (W : C) :
    (G.compResolutionStageIso (n + 1)).inv.app W =
      G.map ((G.compResolutionStageIso n).inv.app W) := (rfl)

/-- Under `compResolutionStageIso`, the last face of `G.resolutionStage (n + 1)` applies
`G.resolutionStage n` to the counit `G.ε`. -/
@[reassoc]
lemma compResolutionStageIso_hom_comp_resolutionFace_last (n : ℕ) (W : C) :
    (G.compResolutionStageIso n).hom.app W ≫ (G.resolutionFace n (Fin.last n)).app W =
      (G.resolutionStage n).map (G.ε.app W) := by
  induction n with
  | zero =>
    rw [compResolutionStageIso_zero_hom_app, Fin.last_zero, resolutionFace_zero_app]
    dsimp only [resolutionStage, Functor.comp_obj, Functor.id_obj, Functor.id_map]
    rw [Category.id_comp]
  | succ n ih =>
    rw [← Fin.succ_last, G.compResolutionStageIso_succ_hom_app, resolutionFace_succ_app]
    dsimp only [resolutionStage, Functor.comp_obj, Functor.comp_map]
    rw [← G.map_comp]
    exact congrArg G.map ih

/-- Under `compResolutionStageIso`, every non-last face `i.castSucc` commutes past the inner
comonad layer. -/
@[reassoc]
lemma compResolutionStageIso_hom_comp_resolutionFace_castSucc (n : ℕ) (i : Fin (n + 1)) (W : C) :
    (G.compResolutionStageIso (n + 1)).hom.app W ≫ (G.resolutionFace (n + 1) i.castSucc).app W =
      (G.resolutionFace n i).app (G.obj W) ≫ (G.compResolutionStageIso n).hom.app W := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.eq_zero i
    rw [G.compResolutionStageIso_succ_hom_app, G.compResolutionStageIso_zero_hom_app,
      Fin.castSucc_zero, resolutionFace_zero_app, resolutionFace_zero_app]
    dsimp only [resolutionStage, Functor.comp_obj, Functor.id_obj]
    rw [G.map_id, Category.id_comp, Category.comp_id]
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      rw [G.compResolutionStageIso_succ_hom_app, Fin.castSucc_zero, resolutionFace_zero_app,
        resolutionFace_zero_app]
      dsimp only [resolutionStage, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
        Functor.id_map]
      exact G.ε.naturality ((G.compResolutionStageIso (n + 1)).hom.app W)
    | succ j =>
      rw [G.compResolutionStageIso_succ_hom_app (n + 1), G.compResolutionStageIso_succ_hom_app n,
        Fin.castSucc_succ, resolutionFace_succ_app, resolutionFace_succ_app]
      dsimp only [resolutionStage, Functor.comp_obj, Functor.comp_map]
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (ih j)

/-- Under `compResolutionStageIso`, every degeneracy `i.castSucc` commutes past the inner
comonad layer. -/
@[reassoc]
lemma compResolutionStageIso_hom_comp_resolutionDegeneracy_castSucc (n : ℕ) (i : Fin (n + 1))
    (W : C) :
    (G.compResolutionStageIso (n + 1)).hom.app W ≫
        (G.resolutionDegeneracy (n + 1) i.castSucc).app W =
      (G.resolutionDegeneracy n i).app (G.obj W) ≫
        (G.compResolutionStageIso (n + 2)).hom.app W := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.eq_zero i
    simp only [compResolutionStageIso_succ_hom_app, compResolutionStageIso_zero_hom_app,
      Fin.castSucc_zero, resolutionDegeneracy_zero_app]
    dsimp only [resolutionStage, Functor.comp_obj, Functor.id_obj]
    rw [G.map_id, G.map_id, Category.id_comp, Category.comp_id]
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      rw [G.compResolutionStageIso_succ_hom_app (n + 1),
        G.compResolutionStageIso_succ_hom_app (n + 2),
        G.compResolutionStageIso_succ_hom_app (n + 1),
        Fin.castSucc_zero, resolutionDegeneracy_zero_app, resolutionDegeneracy_zero_app]
      dsimp only [resolutionStage, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
        Functor.id_map]
      exact G.δ.naturality ((G.compResolutionStageIso (n + 1)).hom.app W)
    | succ j =>
      rw [G.compResolutionStageIso_succ_hom_app (n + 1),
        G.compResolutionStageIso_succ_hom_app (n + 2), Fin.castSucc_succ,
        resolutionDegeneracy_succ_app, resolutionDegeneracy_succ_app]
      dsimp only [resolutionStage, Functor.comp_obj, Functor.comp_map]
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (ih j)

/-- The comultiplication splits the counit on every free object `G.obj W`. -/
def freeSplitEpi (W : C) : SplitEpi (G.ε.app (G.obj W)) where
  section_ := G.δ.app W
  id := G.left_counit W

instance instIsSplitEpi_ε_obj (W : C) : IsSplitEpi (G.ε.app (G.obj W)) :=
  ⟨⟨G.freeSplitEpi W⟩⟩

/-- The degree-`n` map of the right extra degeneracy on the simplicial resolution of `G.obj W`:
apply `G^{n+1}` to `G.δ.app W` and shift the newly introduced inner layer outward. -/
def freeRightExtraDegeneracyMap (n : ℕ) (W : C) :
    (G.resolutionStage (n + 1)).obj (G.obj W) ⟶ (G.resolutionStage (n + 2)).obj (G.obj W) :=
  (G.resolutionStage (n + 1)).map (G.δ.app W) ≫
    (G.compResolutionStageIso (n + 1)).hom.app (G.obj W)

private lemma freeRightExtraDegeneracyMap_zero_comp_face_zero (W : C) :
    G.freeRightExtraDegeneracyMap 0 W ≫ (G.resolutionFace 1 0).app (G.obj W) =
      G.ε.app (G.obj W) ≫ G.δ.app W := by
  rw [freeRightExtraDegeneracyMap, resolutionFace_zero_app,
    G.compResolutionStageIso_succ_hom_app, G.compResolutionStageIso_zero_hom_app]
  dsimp only [resolutionStage, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Functor.id_map]
  rw [G.map_id, Category.comp_id]
  exact G.ε.naturality (G.δ.app W)

private lemma freeRightExtraDegeneracyMap_comp_face_last (n : ℕ) (W : C) :
    G.freeRightExtraDegeneracyMap n W ≫
        (G.resolutionFace (n + 1) (Fin.last (n + 1))).app (G.obj W) =
      𝟙 ((G.resolutionStage (n + 1)).obj (G.obj W)) := by
  rw [freeRightExtraDegeneracyMap, Category.assoc,
    G.compResolutionStageIso_hom_comp_resolutionFace_last (n + 1) (G.obj W),
    ← Functor.map_comp, G.left_counit, Functor.map_id]

private lemma freeRightExtraDegeneracyMap_comp_face_castSucc (n : ℕ) (i : Fin (n + 2)) (W : C) :
    G.freeRightExtraDegeneracyMap (n + 1) W ≫
        (G.resolutionFace (n + 2) i.castSucc).app (G.obj W) =
      (G.resolutionFace (n + 1) i).app (G.obj W) ≫ G.freeRightExtraDegeneracyMap n W := by
  rw [freeRightExtraDegeneracyMap, freeRightExtraDegeneracyMap, Category.assoc,
    G.compResolutionStageIso_hom_comp_resolutionFace_castSucc (n + 1) i (G.obj W),
    ← (G.resolutionFace (n + 1) i).naturality_assoc (G.δ.app W)]
  rfl

private lemma freeRightExtraDegeneracyMap_comp_degeneracy_castSucc (n : ℕ) (i : Fin (n + 1))
    (W : C) :
    G.freeRightExtraDegeneracyMap n W ≫
        (G.resolutionDegeneracy (n + 1) i.castSucc).app (G.obj W) =
      (G.resolutionDegeneracy n i).app (G.obj W) ≫ G.freeRightExtraDegeneracyMap (n + 1) W := by
  rw [freeRightExtraDegeneracyMap, freeRightExtraDegeneracyMap, Category.assoc,
    G.compResolutionStageIso_hom_comp_resolutionDegeneracy_castSucc n i (G.obj W),
    ← (G.resolutionDegeneracy n i).naturality_assoc (G.δ.app W)]
  rfl

/-- Build an `ExtraDegeneracy` on `SimplicialObject.Augmented.opFunctor.obj X` from a right
extra degeneracy on `X` (whose splitting face is the last face in each degree). -/
private def extraDegeneracyOpFunctorMk {X : SimplicialObject.Augmented C}
    (s' : X.right ⟶ X.left _⦋0⦌)
    (s : ∀ n : ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌)
    (hs' : s' ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right)
    (hs₀ : s 0 ≫ X.left.δ (n := 0) 0 = X.hom.app (op ⦋0⦌) ≫ s')
    (hlast : ∀ n : ℕ, s n ≫ X.left.δ (n := n) (Fin.last (n + 1)) = 𝟙 _)
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)),
      s (n + 1) ≫ X.left.δ (n := n + 1) i.castSucc = X.left.δ (n := n) i ≫ s n)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)),
      s n ≫ X.left.σ (n := n + 1) i.castSucc = X.left.σ (n := n) i ≫ s (n + 1)) :
    SimplicialObject.Augmented.ExtraDegeneracy (SimplicialObject.Augmented.opFunctor.obj X) where
  s' := s' ≫ (_root_.SimplicialObject.opObjIso (X := X.left) (n := op ⦋0⦌)).inv
  s n := (_root_.SimplicialObject.opObjIso (X := X.left) (n := op ⦋n⦌)).hom ≫ s n ≫
    (_root_.SimplicialObject.opObjIso (X := X.left) (n := op ⦋n + 1⦌)).inv
  s'_comp_ε := by
    dsimp only [SimplicialObject.Augmented.opFunctor]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hs']
  s₀_comp_δ₁ := by
    dsimp only [SimplicialObject.Augmented.opFunctor]
    simp only [_root_.SimplicialObject.opFunctor_obj_δ, Category.assoc, Iso.inv_hom_id_assoc]
    have hrev : (1 : Fin 2).rev = 0 := rfl
    rw [hrev, reassoc_of% hs₀]
  s_comp_δ₀ n := by
    dsimp only [SimplicialObject.Augmented.opFunctor]
    simp only [_root_.SimplicialObject.opFunctor_obj_δ, Fin.rev_zero, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [reassoc_of% hlast n, Iso.hom_inv_id]
  s_comp_δ n i := by
    dsimp only [SimplicialObject.Augmented.opFunctor]
    simp only [_root_.SimplicialObject.opFunctor_obj_δ, Fin.rev_succ, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [reassoc_of% hδ n i.rev]
  s_comp_σ n i := by
    dsimp only [SimplicialObject.Augmented.opFunctor]
    simp only [_root_.SimplicialObject.opFunctor_obj_σ, Fin.rev_succ, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [reassoc_of% hσ n i.rev]

/-- Reversing the simplicial part of the augmented comonad resolution of a free object `G.obj W`
produces an augmented simplicial object with an extra degeneracy. -/
def freeReversedResolutionExtraDegeneracy (W : C) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (SimplicialObject.Augmented.opFunctor.obj
        (G.augmentedSimplicialResolution.obj (G.obj W))) :=
  extraDegeneracyOpFunctorMk
    (X := G.augmentedSimplicialResolution.obj (G.obj W))
    (G.δ.app W)
    (fun n ↦ G.freeRightExtraDegeneracyMap n W)
    (by
      rw [augmentedSimplicialResolution_obj_hom, simplicialResolutionAugmentation_app_zero]
      exact G.left_counit W)
    (by
      dsimp only [augmentedSimplicialResolution]
      rw [G.simplicialResolution_δ, G.simplicialResolutionAugmentation_app_zero]
      exact G.freeRightExtraDegeneracyMap_zero_comp_face_zero W)
    (fun n ↦ by
      dsimp only [augmentedSimplicialResolution]
      rw [G.simplicialResolution_δ]
      exact G.freeRightExtraDegeneracyMap_comp_face_last n W)
    (fun n i ↦ by
      dsimp only [augmentedSimplicialResolution]
      rw [G.simplicialResolution_δ, G.simplicialResolution_δ]
      exact G.freeRightExtraDegeneracyMap_comp_face_castSucc n i W)
    (fun n i ↦ by
      dsimp only [augmentedSimplicialResolution]
      rw [G.simplicialResolution_σ, G.simplicialResolution_σ]
      exact G.freeRightExtraDegeneracyMap_comp_degeneracy_castSucc n i W)

lemma freeReversedResolutionExtraDegeneracy_s' (W : C) :
    (G.freeReversedResolutionExtraDegeneracy W).s' =
      G.δ.app W ≫
        (_root_.SimplicialObject.opObjIso
          (X := G.simplicialResolution.obj (G.obj W)) (n := op ⦋0⦌)).inv := (rfl)

lemma freeReversedResolutionExtraDegeneracy_s (W : C) (n : ℕ) :
    (G.freeReversedResolutionExtraDegeneracy W).s n =
      (_root_.SimplicialObject.opObjIso
          (X := G.simplicialResolution.obj (G.obj W)) (n := op ⦋n⦌)).hom ≫
        G.freeRightExtraDegeneracyMap n W ≫
        (_root_.SimplicialObject.opObjIso
          (X := G.simplicialResolution.obj (G.obj W)) (n := op ⦋n + 1⦌)).inv := (rfl)

end CategoryTheory.Comonad
