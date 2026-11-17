/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import TauCeti.AlgebraicTopology.SimplicialObject.Op
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Extra codegeneracies and reversal of alternating coface map complexes

This file develops the cosimplicial dual of Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy`
together with the sign comparison between the alternating coface map complexes of a cosimplicial
object and its reversal along `SimplexCategory.rev`.

## Main definitions

* `AlgebraicTopology.AlternatingCofaceMapComplex.η`: the natural coaugmentation from the
  single-degree complex of the coaugmentation object to the alternating coface map complex of an
  augmented cosimplicial object.
* `AlgebraicTopology.AlternatingCofaceMapComplex.revSign`: the degree-`n` sign
  `(-1) ^ (n * (n + 1) / 2)`.
* `AlgebraicTopology.AlternatingCofaceMapComplex.revIso`: the natural cochain isomorphism
  `AlternatingCofaceMapComplex.obj (CosimplicialObject.opFunctor.obj X) ≅
    AlternatingCofaceMapComplex.obj X`, given in degree `n` by multiplication by `revSign n`,
  compatible with `η`.
* `CategoryTheory.CosimplicialObject.Augmented.ExtraCodegeneracy`: an extra codegeneracy on an
  augmented cosimplicial object, dual to Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy`.
* `CategoryTheory.CosimplicialObject.Augmented.ExtraCodegeneracy.homotopyEquiv`: an extra
  codegeneracy on an augmented cosimplicial object in a preadditive category with a zero object
  induces a homotopy equivalence between the single-degree complex of its coaugmentation object
  and its alternating coface map complex, with forward morphism `η.app X`.
* `CategoryTheory.CosimplicialObject.Augmented.ExtraCodegeneracy.revHomotopyEquiv`: the
  corresponding homotopy equivalence for an extra codegeneracy on the reversed augmented
  cosimplicial object (i.e. a right extra codegeneracy), transported along `revIso`.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, p. 190.
* Mathlib's `Mathlib.AlgebraicTopology.ExtraDegeneracy` by Joël Riou, for the simplicial dual
  `ExtraDegeneracy` and `ExtraDegeneracy.homotopyEquiv`.
-/

public section

open CategoryTheory Category Opposite Limits

open scoped Simplicial

universe v u v' u'

namespace CategoryTheory.CosimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- The degree-`0` coaugmentation morphism `point.obj X ⟶ (drop.obj X) ^⦋0⦌`. -/
@[expose]
def hom₀ (X : CosimplicialObject.Augmented C) : point.obj X ⟶ (drop.obj X) ^⦋0⦌ :=
  X.hom.app ⦋0⦌

@[reassoc]
lemma point_map_comp_hom₀ {X Y : CosimplicialObject.Augmented C} (f : X ⟶ Y) :
    point.map f ≫ hom₀ Y = hom₀ X ≫ (drop.map f).app ⦋0⦌ :=
  w_app (η := f)

@[simp]
lemma hom₀_opFunctor (X : CosimplicialObject.Augmented C) :
    hom₀ (opFunctor.obj X) =
      hom₀ X ≫ (CosimplicialObject.opObjIso (X := drop.obj X) (n := ⦋0⦌)).inv := (rfl)

end CategoryTheory.CosimplicialObject.Augmented

namespace AlgebraicTopology.AlternatingCofaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
lemma obj_X (X : CosimplicialObject C) (n : ℕ) :
    (obj X).X n = X.obj ⦋n⦌ := (rfl)

lemma obj_d_eq (X : CosimplicialObject C) (n : ℕ) :
    (obj X).d n (n + 1) = objD X n :=
  CochainComplex.of_d _ (objD X) n

@[simp]
lemma map_f {X Y : CosimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    (map f).f n = f.app ⦋n⦌ := (rfl)

private lemma const_natTrans_app_zero_comp_objD {A : C} {Y : CosimplicialObject C}
    (u : (CosimplicialObject.const C).obj A ⟶ Y) :
    u.app ⦋0⦌ ≫ objD Y 0 = 0 := by
  rw [objD, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_zsmul, one_zsmul, Preadditive.comp_add, Preadditive.comp_neg]
  have h0 : u.app ⦋0⦌ ≫ Y.δ (0 : Fin 2) = u.app ⦋1⦌ :=
    (u.naturality (SimplexCategory.δ (0 : Fin 2))).symm.trans (Category.id_comp _)
  have h1 : u.app ⦋0⦌ ≫ Y.δ (1 : Fin 2) = u.app ⦋1⦌ :=
    (u.naturality (SimplexCategory.δ (1 : Fin 2))).symm.trans (Category.id_comp _)
  rw [h0, h1, add_neg_cancel]

/-- The natural transformation giving the coaugmentation of the alternating coface map complex
attached to an augmented cosimplicial object. -/
noncomputable def η [HasZeroObject C] :
    CosimplicialObject.Augmented.point ⋙ CochainComplex.single₀ C ⟶
      CosimplicialObject.Augmented.drop ⋙ AlgebraicTopology.alternatingCofaceMapComplex C where
  app X :=
    (CochainComplex.fromSingle₀Equiv _ _).symm
      ⟨CosimplicialObject.Augmented.hom₀ X,
        (congrArg (X.hom.app ⦋0⦌ ≫ ·) (obj_d_eq X.right 0)).trans
          (const_natTrans_app_zero_comp_objD X.hom)⟩
  naturality X Y f := by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    have hY := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := (CosimplicialObject.Augmented.drop ⋙
        AlgebraicTopology.alternatingCofaceMapComplex C).obj Y)
      (CosimplicialObject.Augmented.hom₀ Y)
      ((congrArg (Y.hom.app ⦋0⦌ ≫ ·) (obj_d_eq Y.right 0)).trans
        (const_natTrans_app_zero_comp_objD Y.hom))
    have hX := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := (CosimplicialObject.Augmented.drop ⋙
        AlgebraicTopology.alternatingCofaceMapComplex C).obj X)
      (CosimplicialObject.Augmented.hom₀ X)
      ((congrArg (X.hom.app ⦋0⦌ ≫ ·) (obj_d_eq X.right 0)).trans
        (const_natTrans_app_zero_comp_objD X.hom))
    exact (congrArg₂ (· ≫ ·) (CochainComplex.single₀_map_f_zero _) hY).trans
      ((CosimplicialObject.Augmented.point_map_comp_hom₀ f).trans
        (congrArg (· ≫ _) hX.symm))

@[simp]
lemma η_app_f_zero [HasZeroObject C] (X : CosimplicialObject.Augmented C) :
    (η.app X).f 0 = CosimplicialObject.Augmented.hom₀ X :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

@[simp]
lemma η_app_f_succ [HasZeroObject C] (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (η.app X).f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
    (CosimplicialObject.Augmented.point.obj X) (n + 1) (Nat.succ_ne_zero n)).eq_of_src _ _

/-- The degree-`n` sign `(-1) ^ (n * (n + 1) / 2)` comparing the alternating coface map complex
of a reversed cosimplicial object with the original complex. -/
@[expose]
def revSign (n : ℕ) : ℤ :=
  (-1) ^ (n * (n + 1) / 2)

@[simp]
lemma revSign_zero : revSign 0 = 1 := rfl

lemma revSign_succ (n : ℕ) : revSign (n + 1) = (-1) ^ (n + 1) * revSign n := by
  have hdiv : (n + 1) * (n + 2) / 2 = (n + 1) + n * (n + 1) / 2 := by
    have heq : (n + 1) * (n + 2) = 2 * (n + 1) + n * (n + 1) := by
      calc (n + 1) * (n + 2)
          = (n + 1) * n + (n + 1) * 2 := Nat.mul_add (n + 1) n 2
        _ = 2 * (n + 1) + n * (n + 1) := by
            rw [Nat.add_comm, Nat.mul_comm (n + 1) 2, Nat.mul_comm (n + 1) n]
    rw [heq, Nat.mul_add_div (by omega)]
  rw [revSign, revSign, hdiv, pow_add]

@[simp]
lemma revSign_mul_self (n : ℕ) : revSign n * revSign n = 1 := by
  rw [revSign, ← mul_pow]
  norm_num

private lemma neg_one_pow_fin_rev {n : ℕ} (i : Fin (n + 2)) :
    (-1 : ℤ) ^ (i.rev : ℕ) = (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (i : ℕ) := by
  have hsum : (i.rev : ℕ) + (i : ℕ) = n + 1 := by
    simp only [Fin.val_rev]
    omega
  have hmul : (-1 : ℤ) ^ (i.rev : ℕ) * (-1 : ℤ) ^ (i : ℕ) = (-1 : ℤ) ^ (n + 1) := by
    rw [← pow_add, hsum]
  calc
    (-1 : ℤ) ^ (i.rev : ℕ)
        = (-1 : ℤ) ^ (i.rev : ℕ) * ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (i : ℕ)) := by
          rw [← mul_pow]; norm_num
    _ = ((-1 : ℤ) ^ (i.rev : ℕ) * (-1 : ℤ) ^ (i : ℕ)) * (-1 : ℤ) ^ (i : ℕ) :=
          (mul_assoc _ _ _).symm
    _ = (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (i : ℕ) := by rw [hmul]

/-- The degree-`n` differential of a reversed cosimplicial object equals `(-1) ^ (n + 1)` times
the original differential, transported through `CosimplicialObject.opObjIso`. -/
lemma objD_opFunctor (X : CosimplicialObject C) (n : ℕ) :
    objD (CosimplicialObject.opFunctor.obj X) n =
      (-1 : ℤ) ^ (n + 1) •
        (CosimplicialObject.opObjIso.hom ≫ objD X n ≫ CosimplicialObject.opObjIso.inv) := by
  unfold objD
  simp only [CosimplicialObject.opFunctor_obj_δ, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, smul_smul, neg_one_pow_fin_rev]

private def revIsoComponent (X : CosimplicialObject C) (n : ℕ) :
    (CosimplicialObject.opFunctor.obj X) ^⦋n⦌ ≅ X ^⦋n⦌ where
  hom := revSign n • (CosimplicialObject.opObjIso (X := X) (n := ⦋n⦌)).hom
  inv := revSign n • (CosimplicialObject.opObjIso (X := X) (n := ⦋n⦌)).inv
  hom_inv_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, revSign_mul_self,
      one_zsmul, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, revSign_mul_self,
      one_zsmul, Iso.inv_hom_id]

/-- The canonical isomorphism between the alternating coface map complex of a reversed
cosimplicial object and that of the original cosimplicial object, multiplying degree `n` by
`revSign n = (-1) ^ (n * (n + 1) / 2)`. -/
def revIso (X : CosimplicialObject C) :
    obj (CosimplicialObject.opFunctor.obj X) ≅ obj X :=
  HomologicalComplex.Hom.isoOfComponents (revIsoComponent X) fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    have hcomm : (revIsoComponent X i).hom ≫ objD X i =
        objD (CosimplicialObject.opFunctor.obj X) i ≫ (revIsoComponent X (i + 1)).hom := by
      rw [objD_opFunctor]
      dsimp only [revIsoComponent]
      simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, smul_smul, revSign_succ]
      have hsign : (-1 : ℤ) ^ (i + 1) * revSign i * (-1 : ℤ) ^ (i + 1) = revSign i := by
        rw [mul_right_comm, ← mul_pow]; norm_num
      rw [hsign]
    exact (congrArg ((revIsoComponent X i).hom ≫ ·) (obj_d_eq X i)).trans
      (hcomm.trans (congrArg (· ≫ (revIsoComponent X (i + 1)).hom) (obj_d_eq _ i).symm))

@[simp]
lemma revIso_hom_f (X : CosimplicialObject C) (n : ℕ) :
    (revIso X).hom.f n =
      revSign n • (CosimplicialObject.opObjIso (X := X) (n := ⦋n⦌)).hom := (rfl)

@[simp]
lemma revIso_inv_f (X : CosimplicialObject C) (n : ℕ) :
    (revIso X).inv.f n =
      revSign n • (CosimplicialObject.opObjIso (X := X) (n := ⦋n⦌)).inv := (rfl)

variable (C) in
/-- Naturality of `revIso` in the cosimplicial object. -/
def revNatIso :
    CosimplicialObject.opFunctor (C := C) ⋙ alternatingCofaceMapComplex C ≅
      alternatingCofaceMapComplex C :=
  NatIso.ofComponents revIso fun {X Y} f ↦ by
    ext n
    have h : (CosimplicialObject.opFunctor.map f).app ⦋n⦌ ≫
        (revSign n • (CosimplicialObject.opObjIso (X := Y) (n := ⦋n⦌)).hom) =
        (revSign n • (CosimplicialObject.opObjIso (X := X) (n := ⦋n⦌)).hom) ≫
          f.app ⦋n⦌ := by
      simp only [CosimplicialObject.opFunctor_map_app, Preadditive.comp_zsmul,
        Preadditive.zsmul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact h

/-- The reversal isomorphism commutes with the coaugmentation `η`. -/
@[reassoc, simp]
lemma η_app_opFunctor_comp_revIso_hom [HasZeroObject C] (X : CosimplicialObject.Augmented C) :
    η.app (CosimplicialObject.Augmented.opFunctor.obj X) ≫
        (revIso (CosimplicialObject.Augmented.drop.obj X)).hom =
      η.app X := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  have h0 : CosimplicialObject.Augmented.hom₀ X ≫
      (CosimplicialObject.opObjIso
        (X := CosimplicialObject.Augmented.drop.obj X) (n := ⦋0⦌)).inv ≫
      (revSign 0 • (CosimplicialObject.opObjIso
        (X := CosimplicialObject.Augmented.drop.obj X) (n := ⦋0⦌)).hom) =
      CosimplicialObject.Augmented.hom₀ X := by
    rw [revSign_zero, one_zsmul, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (· ≫ _) (η_app_f_zero _)).trans
    ((Category.assoc _ _ _).trans (h0.trans (η_app_f_zero X).symm))

end AlgebraicTopology.AlternatingCofaceMapComplex

namespace CategoryTheory.CosimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- An extra codegeneracy on an augmented cosimplicial object, cosimplicially dual to Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy`. The morphisms `s'` and `s n` formally behave
like an extra codegeneracy `σ (-1)`. -/
@[ext]
structure ExtraCodegeneracy (X : CosimplicialObject.Augmented C) where
  /-- A retraction of the coaugmentation in degree `0`. -/
  s' : (drop.obj X) ^⦋0⦌ ⟶ point.obj X
  /-- The extra codegeneracy in each degree. -/
  s : ∀ n : ℕ, (drop.obj X) ^⦋n + 1⦌ ⟶ (drop.obj X) ^⦋n⦌
  η_comp_s' : hom₀ X ≫ s' = 𝟙 (point.obj X) := by cat_disch
  δ₁_comp_s₀ : (drop.obj X).δ (n := 0) 1 ≫ s 0 = s' ≫ hom₀ X := by cat_disch
  δ₀_comp_s : ∀ n : ℕ, (drop.obj X).δ (n := n) 0 ≫ s n = 𝟙 _ := by cat_disch
  δ_comp_s : ∀ (n : ℕ) (i : Fin (n + 2)),
    (drop.obj X).δ (n := n + 1) i.succ ≫ s (n + 1) =
      s n ≫ (drop.obj X).δ (n := n) i := by cat_disch
  σ_comp_s : ∀ (n : ℕ) (i : Fin (n + 1)),
    (drop.obj X).σ (n := n + 1) i.succ ≫ s n =
      s (n + 1) ≫ (drop.obj X).σ (n := n) i := by cat_disch

namespace ExtraCodegeneracy

attribute [reassoc] δ₁_comp_s₀ δ_comp_s σ_comp_s
attribute [reassoc (attr := simp)] η_comp_s' δ₀_comp_s

/-- Applying any functor preserves extra codegeneracies. -/
def map {D : Type u'} [Category.{v'} D] {X : CosimplicialObject.Augmented C}
    (ec : ExtraCodegeneracy X) (F : C ⥤ D) :
    ExtraCodegeneracy ((whiskeringObj C D F).obj X) where
  s' := F.map ec.s'
  s n := F.map (ec.s n)
  η_comp_s' :=
    (congrArg (· ≫ F.map ec.s') (Category.id_comp _)).trans
      ((F.map_comp _ _).symm.trans ((congrArg F.map ec.η_comp_s').trans (F.map_id _)))
  δ₁_comp_s₀ :=
    ((F.map_comp _ _).symm.trans ((congrArg F.map ec.δ₁_comp_s₀).trans (F.map_comp _ _))).trans
      (congrArg (F.map ec.s' ≫ ·) (Category.id_comp _).symm)
  δ₀_comp_s n :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (ec.δ₀_comp_s n)).trans (F.map_id _))
  δ_comp_s n i :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (ec.δ_comp_s n i)).trans (F.map_comp _ _))
  σ_comp_s n i :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (ec.σ_comp_s n i)).trans (F.map_comp _ _))

/-- Transport an extra codegeneracy along an isomorphism of augmented cosimplicial objects. -/
def ofIso {X Y : CosimplicialObject.Augmented C} (e : X ≅ Y) (ec : ExtraCodegeneracy X) :
    ExtraCodegeneracy Y where
  s' := (drop.mapIso e).inv.app ⦋0⦌ ≫ ec.s' ≫ (point.mapIso e).hom
  s n := (drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ec.s n ≫ (drop.mapIso e).hom.app ⦋n⦌
  η_comp_s' := by
    have hw : hom₀ Y ≫ (drop.mapIso e).inv.app ⦋0⦌ = (point.mapIso e).inv ≫ hom₀ X :=
      (point_map_comp_hom₀ e.inv).symm
    rw [reassoc_of% hw, ec.η_comp_s'_assoc]
    exact (point.mapIso e).inv_hom_id
  δ₁_comp_s₀ := by
    have hδ : (drop.obj Y).δ (n := 0) 1 ≫ (drop.mapIso e).inv.app ⦋1⦌ =
        (drop.mapIso e).inv.app ⦋0⦌ ≫ (drop.obj X).δ (n := 0) 1 :=
      (drop.mapIso e).inv.naturality (SimplexCategory.δ (n := 0) 1)
    have hw : (point.mapIso e).hom ≫ hom₀ Y = hom₀ X ≫ (drop.mapIso e).hom.app ⦋0⦌ :=
      point_map_comp_hom₀ e.hom
    rw [reassoc_of% hδ, ec.δ₁_comp_s₀_assoc, Category.assoc, Category.assoc, hw]
  δ₀_comp_s n := by
    have hδ : (drop.obj Y).δ (n := n) 0 ≫ (drop.mapIso e).inv.app ⦋n + 1⦌ =
        (drop.mapIso e).inv.app ⦋n⦌ ≫ (drop.obj X).δ (n := n) 0 :=
      (drop.mapIso e).inv.naturality (SimplexCategory.δ (n := n) 0)
    rw [reassoc_of% hδ, ec.δ₀_comp_s_assoc]
    exact congr_app (drop.mapIso e).inv_hom_id ⦋n⦌
  δ_comp_s n i := by
    have hδ₁ : (drop.obj Y).δ (n := n + 1) i.succ ≫ (drop.mapIso e).inv.app ⦋n + 2⦌ =
        (drop.mapIso e).inv.app ⦋n + 1⦌ ≫ (drop.obj X).δ (n := n + 1) i.succ :=
      (drop.mapIso e).inv.naturality (SimplexCategory.δ (n := n + 1) i.succ)
    have hδ₂ : (drop.mapIso e).hom.app ⦋n⦌ ≫ (drop.obj Y).δ (n := n) i =
        (drop.obj X).δ (n := n) i ≫ (drop.mapIso e).hom.app ⦋n + 1⦌ :=
      ((drop.mapIso e).hom.naturality (SimplexCategory.δ (n := n) i)).symm
    rw [reassoc_of% hδ₁, ec.δ_comp_s_assoc, Category.assoc, Category.assoc, hδ₂]
  σ_comp_s n i := by
    have hσ₁ : (drop.obj Y).σ (n := n + 1) i.succ ≫ (drop.mapIso e).inv.app ⦋n + 1⦌ =
        (drop.mapIso e).inv.app ⦋n + 2⦌ ≫ (drop.obj X).σ (n := n + 1) i.succ :=
      (drop.mapIso e).inv.naturality (SimplexCategory.σ (n := n + 1) i.succ)
    have hσ₂ : (drop.mapIso e).hom.app ⦋n + 1⦌ ≫ (drop.obj Y).σ (n := n) i =
        (drop.obj X).σ (n := n) i ≫ (drop.mapIso e).hom.app ⦋n⦌ :=
      ((drop.mapIso e).hom.naturality (SimplexCategory.σ (n := n) i)).symm
    rw [reassoc_of% hσ₁, ec.σ_comp_s_assoc, Category.assoc, Category.assoc, hσ₂]

/-- The constant augmented cosimplicial object carries a canonical extra codegeneracy. -/
@[expose, simps]
def const (X : C) : ExtraCodegeneracy (Augmented.const.obj X) where
  s' := 𝟙 X
  s _ := 𝟙 X
  η_comp_s' := Category.id_comp _
  δ₁_comp_s₀ := rfl
  δ₀_comp_s _ := Category.id_comp _
  δ_comp_s _ _ := rfl
  σ_comp_s _ _ := rfl

/-- The retraction of the coaugmentation induced by an extra codegeneracy. -/
def retraction {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X) :
    drop.obj X ⟶ (CosimplicialObject.const C).obj (point.obj X) where
  app n := (drop.obj X).map (SimplexCategory.isTerminalZero.from n) ≫ ec.s'
  naturality {n m} f := by
    dsimp only [CosimplicialObject.const, Functor.const_obj_obj, Functor.const_obj_map]
    rw [Category.comp_id, ← Category.assoc, ← (drop.obj X).map_comp]
    exact congrArg (fun g ↦ (drop.obj X).map g ≫ ec.s')
      (SimplexCategory.isTerminalZero.hom_ext _ _)

@[simp]
lemma retraction_app_zero {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X) :
    ec.retraction.app ⦋0⦌ = ec.s' := by
  have h : SimplexCategory.isTerminalZero.from ⦋0⦌ = 𝟙 ⦋0⦌ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  dsimp only [retraction]
  rw [h, (drop.obj X).map_id, Category.id_comp]

@[reassoc, simp]
lemma hom_app_comp_retraction_app {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X)
    (n : SimplexCategory) : X.hom.app n ≫ ec.retraction.app n = 𝟙 (point.obj X) := by
  have h : X.hom.app n ≫ (drop.obj X).map (SimplexCategory.isTerminalZero.from n) = hom₀ X :=
    (X.hom.naturality (SimplexCategory.isTerminalZero.from n)).symm.trans (Category.id_comp _)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ec.s') h).trans ec.η_comp_s')

@[simp]
lemma hom_comp_retraction {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X) :
    X.hom ≫ ec.retraction = 𝟙 _ := by
  ext n
  exact ec.hom_app_comp_retraction_app n

/-- An extra codegeneracy makes the coaugmentation a split monomorphism. -/
def splitMono {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X) :
    SplitMono X.hom where
  retraction := ec.retraction
  id := ec.hom_comp_retraction

/-- An extra degeneracy on an augmented simplicial object `X` induces an extra codegeneracy
on `X.rightOp`. -/
@[expose, simps]
def ofExtraDegeneracyRightOp {X : SimplicialObject.Augmented C}
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X) :
    ExtraCodegeneracy X.rightOp where
  s' := ed.s'.op
  s n := (ed.s n).op
  η_comp_s' := op_comp.symm.trans (congrArg Quiver.Hom.op ed.s'_comp_ε)
  δ₁_comp_s₀ := op_comp.symm.trans ((congrArg Quiver.Hom.op ed.s₀_comp_δ₁).trans op_comp)
  δ₀_comp_s n := op_comp.symm.trans (congrArg Quiver.Hom.op (ed.s_comp_δ₀ n))
  δ_comp_s n i := op_comp.symm.trans ((congrArg Quiver.Hom.op (ed.s_comp_δ n i)).trans op_comp)
  σ_comp_s n i := op_comp.symm.trans ((congrArg Quiver.Hom.op (ed.s_comp_σ n i)).trans op_comp)

/-- An extra codegeneracy on an augmented cosimplicial object `X` in `Cᵒᵖ` induces an extra
degeneracy on `X.leftOp`. -/
@[expose, simps]
def toExtraDegeneracyLeftOp {X : CosimplicialObject.Augmented Cᵒᵖ}
    (ec : ExtraCodegeneracy X) :
    SimplicialObject.Augmented.ExtraDegeneracy X.leftOp where
  s' := ec.s'.unop
  s n := (ec.s n).unop
  s'_comp_ε := unop_comp.symm.trans (congrArg Quiver.Hom.unop ec.η_comp_s')
  s₀_comp_δ₁ :=
    unop_comp.symm.trans ((congrArg Quiver.Hom.unop ec.δ₁_comp_s₀).trans unop_comp)
  s_comp_δ₀ n := unop_comp.symm.trans (congrArg Quiver.Hom.unop (ec.δ₀_comp_s n))
  s_comp_δ n i :=
    unop_comp.symm.trans ((congrArg Quiver.Hom.unop (ec.δ_comp_s n i)).trans unop_comp)
  s_comp_σ n i :=
    unop_comp.symm.trans ((congrArg Quiver.Hom.unop (ec.σ_comp_s n i)).trans unop_comp)

section HomotopyEquiv

variable [Preadditive C]

private def homotopyHom {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X)
    (i j : ℕ) : (AlgebraicTopology.AlternatingCofaceMapComplex.obj (drop.obj X)).X i ⟶
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj (drop.obj X)).X j :=
  if hij : j + 1 = i then eqToHom (by subst hij; rfl) ≫ (-ec.s j) else 0

private lemma homotopyHom_succ {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X)
    (n : ℕ) : ec.homotopyHom (n + 1) n = -ec.s n :=
  (dite_eq_left rfl).trans (Category.id_comp _)

private lemma objD_zero_comp_s_zero {X : CosimplicialObject.Augmented C}
    (ec : ExtraCodegeneracy X) :
    ec.s' ≫ hom₀ X =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (drop.obj X) 0 ≫ (-ec.s 0) +
        𝟙 ((drop.obj X) ^⦋0⦌) := by
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul,
    Preadditive.add_comp, Preadditive.comp_neg, Preadditive.neg_comp,
    ec.δ₀_comp_s, ec.δ₁_comp_s₀]
  abel

private lemma objD_succ_comp_s_succ_add_s_comp_objD {X : CosimplicialObject.Augmented C}
    (ec : ExtraCodegeneracy X) (n : ℕ) :
    (0 : (drop.obj X) ^⦋n + 1⦌ ⟶ (drop.obj X) ^⦋n + 1⦌) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (drop.obj X) (n + 1) ≫ (-ec.s (n + 1)) +
        (-ec.s n) ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD (drop.obj X) n +
        𝟙 ((drop.obj X) ^⦋n + 1⦌) := by
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, Preadditive.comp_neg,
    Preadditive.neg_comp, Preadditive.sum_comp, Preadditive.comp_sum,
    Fin.sum_univ_succ (n := n + 2)]
  simp only [Fin.val_zero, pow_zero, one_zsmul, ec.δ₀_comp_s, Fin.val_succ, pow_succ,
    mul_neg_one, neg_zsmul, Preadditive.neg_comp, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, ec.δ_comp_s, Finset.sum_neg_distrib]
  abel

variable [HasZeroObject C]

/-- An extra codegeneracy on an augmented cosimplicial object in a preadditive category with a
zero object induces a homotopy equivalence between the single-degree complex of its coaugmentation
object and its alternating coface map complex, with forward map `η.app X`. -/
noncomputable def homotopyEquiv {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X) :
    HomotopyEquiv ((CochainComplex.single₀ C).obj (point.obj X))
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj (drop.obj X)) where
  hom := AlgebraicTopology.AlternatingCofaceMapComplex.η.app X
  inv := (CochainComplex.toSingle₀Equiv _ _).symm ec.s'
  homotopyHomInvId := Homotopy.ofEq (by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    exact (congrArg₂ (· ≫ ·)
      (AlgebraicTopology.AlternatingCofaceMapComplex.η_app_f_zero X)
      (CochainComplex.toSingle₀Equiv_symm_apply_f_zero
        (C := AlgebraicTopology.AlternatingCofaceMapComplex.obj (drop.obj X)) ec.s')).trans
      ec.η_comp_s')
  homotopyInvHomId :=
    { hom := ec.homotopyHom
      zero i j hij := dite_eq_right (by simpa [ComplexShape.up_Rel] using hij)
      comm i := by
        let K := AlgebraicTopology.AlternatingCofaceMapComplex.obj (drop.obj X)
        cases i with
        | zero =>
          have h1 : (((CochainComplex.toSingle₀Equiv K _).symm ec.s' ≫
              AlgebraicTopology.AlternatingCofaceMapComplex.η.app X).f 0) = ec.s' ≫ hom₀ X :=
            congrArg₂ (· ≫ ·)
              (CochainComplex.toSingle₀Equiv_symm_apply_f_zero (C := K) ec.s')
              (AlgebraicTopology.AlternatingCofaceMapComplex.η_app_f_zero X)
          have h2 : K.d 0 1 ≫ ec.homotopyHom 1 0 =
              AlgebraicTopology.AlternatingCofaceMapComplex.objD (drop.obj X) 0 ≫ (-ec.s 0) :=
            congrArg₂ (· ≫ ·)
              (AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_eq (drop.obj X) 0)
              (ec.homotopyHom_succ 0)
          have hrhs : dNext 0 ec.homotopyHom + prevD 0 ec.homotopyHom =
              K.d 0 1 ≫ ec.homotopyHom 1 0 := by
            rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex, add_zero]
          exact h1.trans (ec.objD_zero_comp_s_zero.trans
            (congrArg (· + 𝟙 _) (h2.symm.trans hrhs.symm)))
        | succ n =>
          have h1 : (((CochainComplex.toSingle₀Equiv K _).symm ec.s' ≫
              AlgebraicTopology.AlternatingCofaceMapComplex.η.app X).f (n + 1)) = 0 :=
            (congrArg (· ≫ _)
              (CochainComplex.toSingle₀Equiv_symm_apply_f_succ (C := K) ec.s' n)).trans
              Limits.zero_comp
          have h2 : K.d (n + 1) (n + 2) ≫ ec.homotopyHom (n + 2) (n + 1) =
              AlgebraicTopology.AlternatingCofaceMapComplex.objD (drop.obj X) (n + 1) ≫
                (-ec.s (n + 1)) :=
            congrArg₂ (· ≫ ·)
              (AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_eq (drop.obj X) (n + 1))
              (ec.homotopyHom_succ (n + 1))
          have h3 : ec.homotopyHom (n + 1) n ≫ K.d n (n + 1) =
              (-ec.s n) ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD (drop.obj X) n :=
            congrArg₂ (· ≫ ·) (ec.homotopyHom_succ n)
              (AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_eq (drop.obj X) n)
          have hrhs : dNext (n + 1) ec.homotopyHom + prevD (n + 1) ec.homotopyHom =
              K.d (n + 1) (n + 2) ≫ ec.homotopyHom (n + 2) (n + 1) +
                ec.homotopyHom (n + 1) n ≫ K.d n (n + 1) := by
            rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
          exact h1.trans ((ec.objD_succ_comp_s_succ_add_s_comp_objD n).trans
            (congrArg (· + 𝟙 _) ((congrArg₂ (· + ·) h2.symm h3.symm).trans hrhs.symm))) }

@[simp]
lemma homotopyEquiv_hom {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X) :
    ec.homotopyEquiv.hom = AlgebraicTopology.AlternatingCofaceMapComplex.η.app X := (rfl)

@[simp]
lemma homotopyEquiv_inv {X : CosimplicialObject.Augmented C} (ec : ExtraCodegeneracy X) :
    ec.homotopyEquiv.inv = (CochainComplex.toSingle₀Equiv _ _).symm ec.s' := (rfl)

/-- An extra codegeneracy on the reversed augmented cosimplicial object `opFunctor.obj X`
induces a homotopy equivalence between `(CochainComplex.single₀ C).obj (point.obj X)` and
`AlternatingCofaceMapComplex.obj (drop.obj X)` with forward map `η.app X`, obtained by
transporting `homotopyEquiv` along `AlternatingCofaceMapComplex.revIso`. -/
noncomputable def revHomotopyEquiv {X : CosimplicialObject.Augmented C}
    (ec : ExtraCodegeneracy (Augmented.opFunctor.obj X)) :
    HomotopyEquiv ((CochainComplex.single₀ C).obj (point.obj X))
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj (drop.obj X)) :=
  (ec.homotopyEquiv.trans
    (HomotopyEquiv.ofIso
      (AlgebraicTopology.AlternatingCofaceMapComplex.revIso (drop.obj X)))).copy
    (Homotopy.ofEq
      (AlgebraicTopology.AlternatingCofaceMapComplex.η_app_opFunctor_comp_revIso_hom X))

@[simp]
lemma revHomotopyEquiv_hom {X : CosimplicialObject.Augmented C}
    (ec : ExtraCodegeneracy (Augmented.opFunctor.obj X)) :
    ec.revHomotopyEquiv.hom = AlgebraicTopology.AlternatingCofaceMapComplex.η.app X := (rfl)

end HomotopyEquiv

end ExtraCodegeneracy

end CategoryTheory.CosimplicialObject.Augmented
