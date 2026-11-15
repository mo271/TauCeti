/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.CategoryTheory.Monoidal.Center.Relative.Basic
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# Additive, linear, and biproduct structure on the relative centre

Given a strong monoidal functor `F : C ⥤ D` whose target `D` is monoidal preadditive (or monoidal
`R`-linear), the relative centre `F.RelativeCenter` inherits a preadditive (resp. `R`-linear) and
monoidal preadditive (resp. monoidal `R`-linear) structure, with all operations computed on
underlying morphisms in `D`. Neither `C` nor `F` needs any additive or linear structure: a morphism
`g : X ⟶ Y` in `F.RelativeCenter` is a morphism `g.f : X.1 ⟶ Y.1` in `D` satisfying
`g.f ▷ F.obj U ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ F.obj U ◁ g.f` for every `U : C`, and
this condition is linear in `g.f` as soon as whiskering in `D` is additive or `R`-linear.

Over a division ring `k`, the faithful `k`-linear forgetful functor `RelativeCenter.forget F`
embeds each morphism space `X ⟶ Y` into `X.1 ⟶ Y.1`, so `F.RelativeCenter` is Hom-finite
whenever `D` is.

Finite biproducts in `F.RelativeCenter` are likewise lifted from `D`: if a finite family
`f : J → D` admits a biproduct `⨁ f` in `D` and each summand `f j` carries an `F`-relative
half-braiding `b j`, then `⨁ f` carries an `F`-relative half-braiding
`RelativeHalfBraiding.biproduct F f b` that restricts to `b j` on each summand, making `⨁ f` the
biproduct in `F.RelativeCenter`. These constructions parallel those for the Drinfeld centre in
`TauCeti.CategoryTheory.Monoidal.Center.Preadditive`.

## Main declarations

* `CategoryTheory.Functor.RelativeCenter.instPreadditive` and
  `CategoryTheory.Functor.RelativeCenter.instLinear`: preadditive and `R`-linear category
  structures on `F.RelativeCenter`;
* `CategoryTheory.Functor.RelativeCenter.instAdditiveForget` and
  `CategoryTheory.Functor.RelativeCenter.instLinearForget`: the forgetful functor is additive and
  `R`-linear;
* `CategoryTheory.Functor.RelativeCenter.instMonoidalPreadditive` and
  `CategoryTheory.Functor.RelativeCenter.instMonoidalLinear`: `F.RelativeCenter` is monoidal
  preadditive and monoidal `R`-linear;
* `CategoryTheory.Functor.RelativeCenter.instFiniteDimensionalHom`: finite-dimensionality of
  morphism spaces in `F.RelativeCenter` over a division ring;
* `CategoryTheory.Functor.RelativeHalfBraiding.biproduct`: the `F`-relative half-braiding on a
  finite biproduct `⨁ f` in `D`;
* `CategoryTheory.Functor.RelativeCenter.biproductBicone` and
  `CategoryTheory.Functor.RelativeCenter.isBilimitBiproductBicone`: finite biproducts in
  `F.RelativeCenter`, yielding `HasFiniteBiproducts F.RelativeCenter`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13.
* A. M. Gainutdinov, J. Haferkamp, C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. **414** (2023), 108853, §3.1.
-/

public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

namespace RelativeHalfBraiding

section Biproduct

variable (F : C ⥤ D) [F.Monoidal] [Preadditive D] [MonoidalPreadditive D]
  {J : Type w} [Finite J]

private theorem whiskerRight_biproduct_ext {f : J → D} [HasBiproduct f] {W Z : D}
    {g₁ g₂ : (⨁ f) ⊗ W ⟶ Z}
    (h : ∀ j, biproduct.ι f j ▷ W ≫ g₁ = biproduct.ι f j ▷ W ≫ g₂) :
    g₁ = g₂ := by
  cases nonempty_fintype J
  calc
    g₁ = (𝟙 (⨁ f) ▷ W) ≫ g₁ := by rw [id_whiskerRight, Category.id_comp]
    _ = ((∑ j, biproduct.π f j ≫ biproduct.ι f j) ▷ W) ≫ g₁ := by rw [biproduct.total]
    _ = ∑ j, biproduct.π f j ▷ W ≫ (biproduct.ι f j ▷ W ≫ g₁) := by
      simp only [CategoryTheory.sum_whiskerRight, Preadditive.sum_comp, comp_whiskerRight_assoc]
    _ = ∑ j, biproduct.π f j ▷ W ≫ (biproduct.ι f j ▷ W ≫ g₂) := by simp only [h]
    _ = ((∑ j, biproduct.π f j ≫ biproduct.ι f j) ▷ W) ≫ g₂ := by
      simp only [CategoryTheory.sum_whiskerRight, Preadditive.sum_comp, comp_whiskerRight_assoc]
    _ = (𝟙 (⨁ f) ▷ W) ≫ g₂ := by rw [biproduct.total]
    _ = g₂ := by rw [id_whiskerRight, Category.id_comp]

private theorem whiskerLeft_biproduct_ext {f : J → D} [HasBiproduct f] {W Z : D}
    {g₁ g₂ : W ⊗ (⨁ f) ⟶ Z}
    (h : ∀ j, W ◁ biproduct.ι f j ≫ g₁ = W ◁ biproduct.ι f j ≫ g₂) :
    g₁ = g₂ := by
  cases nonempty_fintype J
  calc
    g₁ = (W ◁ 𝟙 (⨁ f)) ≫ g₁ := by
      rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    _ = (W ◁ ∑ j, biproduct.π f j ≫ biproduct.ι f j) ≫ g₁ := by rw [biproduct.total]
    _ = ∑ j, W ◁ biproduct.π f j ≫ (W ◁ biproduct.ι f j ≫ g₁) := by
      simp only [CategoryTheory.whiskerLeft_sum, Preadditive.sum_comp,
        MonoidalCategory.whiskerLeft_comp_assoc]
    _ = ∑ j, W ◁ biproduct.π f j ≫ (W ◁ biproduct.ι f j ≫ g₂) := by simp only [h]
    _ = (W ◁ ∑ j, biproduct.π f j ≫ biproduct.ι f j) ≫ g₂ := by
      simp only [CategoryTheory.whiskerLeft_sum, Preadditive.sum_comp,
        MonoidalCategory.whiskerLeft_comp_assoc]
    _ = (W ◁ 𝟙 (⨁ f)) ≫ g₂ := by rw [biproduct.total]
    _ = g₂ := by rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]

private noncomputable def biproductβHom (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) :
    (⨁ f) ⊗ F.obj U ⟶ F.obj U ⊗ ⨁ f :=
  let := Fintype.ofFinite J
  ∑ j, biproduct.π f j ▷ F.obj U ≫ ((b j).β U).hom ≫ F.obj U ◁ biproduct.ι f j

private noncomputable def biproductβInv (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) :
    F.obj U ⊗ ⨁ f ⟶ (⨁ f) ⊗ F.obj U :=
  let := Fintype.ofFinite J
  ∑ j, F.obj U ◁ biproduct.π f j ≫ ((b j).β U).inv ≫ biproduct.ι f j ▷ F.obj U

private theorem biproduct_ι_comp_biproductβHom (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) (j : J) :
    biproduct.ι f j ▷ F.obj U ≫ biproductβHom F f b U =
      ((b j).β U).hom ≫ F.obj U ◁ biproduct.ι f j := by
  classical
  dsimp [biproductβHom]
  let := Fintype.ofFinite J
  simp [Preadditive.comp_sum, ← comp_whiskerRight_assoc, biproduct.ι_π, dite_whiskerRight,
    dite_comp]

private theorem biproduct_ι_comp_biproductβInv (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) (j : J) :
    F.obj U ◁ biproduct.ι f j ≫ biproductβInv F f b U =
      ((b j).β U).inv ≫ biproduct.ι f j ▷ F.obj U := by
  classical
  dsimp [biproductβInv]
  let := Fintype.ofFinite J
  simp [Preadditive.comp_sum, ← MonoidalCategory.whiskerLeft_comp_assoc, biproduct.ι_π,
    whiskerLeft_dite, dite_comp]

/-- The component at `U : C` of the `F`-relative half-braiding on a finite biproduct `⨁ f` of
objects carrying `F`-relative half-braidings `b j`. -/
noncomputable def biproductβ (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) :
    (⨁ f) ⊗ F.obj U ≅ F.obj U ⊗ ⨁ f where
  hom := biproductβHom F f b U
  inv := biproductβInv F f b U
  hom_inv_id := by
    refine whiskerRight_biproduct_ext fun j ↦ ?_
    rw [← Category.assoc, biproduct_ι_comp_biproductβHom, Category.assoc,
      biproduct_ι_comp_biproductβInv, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine whiskerLeft_biproduct_ext fun j ↦ ?_
    rw [← Category.assoc, biproduct_ι_comp_biproductβInv, Category.assoc,
      biproduct_ι_comp_biproductβHom, Iso.inv_hom_id_assoc, Category.comp_id]

variable {F}

/-- On the summand `f j`, the component `biproductβ F f b U` agrees with `(b j).β U`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_comp_biproductβ_hom (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) (j : J) :
    biproduct.ι f j ▷ F.obj U ≫ (biproductβ F f b U).hom =
      ((b j).β U).hom ≫ F.obj U ◁ biproduct.ι f j :=
  biproduct_ι_comp_biproductβHom F f b U j

/-- Projected to the summand `f j`, the component `biproductβ F f b U` agrees with `(b j).β U`. -/
@[reassoc (attr := simp)]
theorem biproductβ_hom_comp_biproduct_π (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) (j : J) :
    (biproductβ F f b U).hom ≫ F.obj U ◁ biproduct.π f j =
      biproduct.π f j ▷ F.obj U ≫ ((b j).β U).hom := by
  refine whiskerRight_biproduct_ext fun k ↦ ?_
  rw [biproduct_ι_comp_biproductβ_hom_assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← comp_whiskerRight_assoc]
  by_cases h : k = j
  · subst h
    simp
  · simp [biproduct.ι_π_ne f h]

variable (F) in
/-- The `F`-relative half-braiding on a finite biproduct `⨁ f` of objects carrying `F`-relative
half-braidings `b j`, with components `biproductβ F f b`. -/
noncomputable def biproduct (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) :
    F.RelativeHalfBraiding (⨁ f) where
  β := biproductβ F f b
  monoidal U U' := by
    refine whiskerRight_biproduct_ext fun j ↦ ?_
    rw [biproduct_ι_comp_biproductβ_hom, (b j).monoidal]
    simp only [Category.assoc]
    rw [← whisker_exchange, ← associator_inv_naturality_right_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ← biproduct_ι_comp_biproductβ_hom,
      MonoidalCategory.whiskerLeft_comp_assoc, ← associator_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, ← biproduct_ι_comp_biproductβ_hom, comp_whiskerRight_assoc,
      ← associator_inv_naturality_left_assoc, whisker_exchange_assoc]
  naturality g := by
    refine whiskerRight_biproduct_ext fun j ↦ ?_
    rw [← whisker_exchange_assoc, biproduct_ι_comp_biproductβ_hom,
      biproduct_ι_comp_biproductβ_hom_assoc, RelativeHalfBraiding.naturality_assoc,
      whisker_exchange]

/-- On the summand `f j`, the `F`-relative half-braiding of `⨁ f` agrees with `b j`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_comp_biproduct_β_hom (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) (j : J) :
    biproduct.ι f j ▷ F.obj U ≫ ((RelativeHalfBraiding.biproduct F f b).β U).hom =
      ((b j).β U).hom ≫ F.obj U ◁ biproduct.ι f j :=
  biproduct_ι_comp_biproductβ_hom f b U j

/-- Projected to the summand `f j`, the `F`-relative half-braiding of `⨁ f` agrees with `b j`. -/
@[reassoc (attr := simp)]
theorem biproduct_β_hom_comp_biproduct_π (f : J → D) [HasBiproduct f]
    (b : ∀ j, F.RelativeHalfBraiding (f j)) (U : C) (j : J) :
    ((RelativeHalfBraiding.biproduct F f b).β U).hom ≫ F.obj U ◁ biproduct.π f j =
      biproduct.π f j ▷ F.obj U ≫ ((b j).β U).hom :=
  biproductβ_hom_comp_biproduct_π f b U j

end Biproduct

end RelativeHalfBraiding

namespace RelativeCenter

variable {F : C ⥤ D} [F.Monoidal]

section Preadditive

variable [Preadditive D] [MonoidalPreadditive D] {X Y : F.RelativeCenter}

instance instZeroHom : Zero (X ⟶ Y) where
  zero := { f := 0 }

instance instAddHom : Add (X ⟶ Y) where
  add f g := { f := f.f + g.f }

instance instNegHom : Neg (X ⟶ Y) where
  neg f := { f := -f.f }

instance instSubHom : Sub (X ⟶ Y) where
  sub f g := { f := f.f - g.f }

instance instSMulNatHom : SMul ℕ (X ⟶ Y) where
  smul n f := { f := n • f.f }

instance instSMulIntHom : SMul ℤ (X ⟶ Y) where
  smul n f := { f := n • f.f }

@[simp] theorem zero_f : (0 : X ⟶ Y).f = 0 := rfl
@[simp] theorem add_f (f g : X ⟶ Y) : (f + g).f = f.f + g.f := rfl
@[simp] theorem neg_f (f : X ⟶ Y) : (-f).f = -f.f := rfl
@[simp] theorem sub_f (f g : X ⟶ Y) : (f - g).f = f.f - g.f := rfl
@[simp] theorem nsmul_f (n : ℕ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl
@[simp] theorem zsmul_f (n : ℤ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl

/-- When `D` is monoidal preadditive, `F.RelativeCenter` is preadditive, with addition and
negation computed on underlying morphisms in `D`. -/
instance instPreadditive : Preadditive F.RelativeCenter where
  homGroup _ _ :=
    (forget F).map_injective.addCommGroup _ zero_f add_f neg_f sub_f
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  add_comp _ _ _ _ _ _ := by ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := by ext; exact Preadditive.comp_add _ _ _ _ _ _

/-- The forgetful functor `RelativeCenter.forget F : F.RelativeCenter ⥤ D` is additive. -/
instance instAdditiveForget : (forget F).Additive where

@[simp]
theorem sum_f {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i).f = ∑ i ∈ s, (f i).f :=
  (forget F).map_sum f s

/-- When `D` is monoidal preadditive, `F.RelativeCenter` is monoidal preadditive. -/
instance instMonoidalPreadditive : MonoidalPreadditive F.RelativeCenter :=
  monoidalPreadditive_of_faithful (forget F)

end Preadditive

section Linear

variable [Preadditive D] [MonoidalPreadditive D] {R : Type*} [Semiring R]
  [CategoryTheory.Linear R D] [MonoidalLinear R D]

/-- When `D` is monoidal `R`-linear, `F.RelativeCenter` is `R`-linear, with scalar multiplication
computed on underlying morphisms in `D`. -/
instance instLinear : CategoryTheory.Linear R F.RelativeCenter where
  homModule _ _ :=
    { smul r f := { f := r • f.f }
      one_smul _ := by ext; exact one_smul _ _
      mul_smul _ _ _ := by ext; exact mul_smul _ _ _
      smul_zero _ := by ext; exact smul_zero _
      smul_add _ _ _ := by ext; exact smul_add _ _ _
      add_smul _ _ _ := by ext; exact add_smul _ _ _
      zero_smul _ := by ext; exact zero_smul _ _ }
  smul_comp _ _ _ _ _ _ := by ext; exact CategoryTheory.Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := by ext; exact CategoryTheory.Linear.comp_smul _ _ _ _ _ _

@[simp]
theorem smul_f {X Y : F.RelativeCenter} (r : R) (f : X ⟶ Y) : (r • f).f = r • f.f :=
  rfl

/-- The forgetful functor `RelativeCenter.forget F : F.RelativeCenter ⥤ D` is `R`-linear. -/
instance instLinearForget : (forget F).Linear R where

/-- When `D` is monoidal `R`-linear, `F.RelativeCenter` is monoidal `R`-linear. -/
instance instMonoidalLinear : MonoidalLinear R F.RelativeCenter :=
  MonoidalLinear.ofFaithful R (forget F)

end Linear

/-- Over a division ring `k`, each morphism space `X ⟶ Y` in `F.RelativeCenter` is
finite-dimensional whenever the underlying morphism space `X.1 ⟶ Y.1` in `D` is. -/
instance instFiniteDimensionalHom [Preadditive D] [MonoidalPreadditive D]
    {k : Type*} [DivisionRing k] [CategoryTheory.Linear k D] [MonoidalLinear k D]
    (X Y : F.RelativeCenter) [FiniteDimensional k (X.1 ⟶ Y.1)] :
    FiniteDimensional k (X ⟶ Y) := by
  have : FiniteDimensional k ((forget F).obj X ⟶ (forget F).obj Y) :=
    ‹FiniteDimensional k (X.1 ⟶ Y.1)›
  exact FiniteDimensional.of_injective ((forget F).mapLinearMap k) (forget F).map_injective

section Biproduct

variable [Preadditive D] [MonoidalPreadditive D] {J : Type w} [Finite J]

/-- The biproduct bicone of a finite family `G : J → F.RelativeCenter` whose underlying family
admits a biproduct in `D`: its point is `⨁ fun j ↦ (G j).1` equipped with
`RelativeHalfBraiding.biproduct`, with projections and inclusions inherited from `D`. -/
@[expose]
noncomputable def biproductBicone (G : J → F.RelativeCenter)
    [HasBiproduct fun j ↦ (G j).1] : Bicone G where
  pt := ⟨⨁ fun j ↦ (G j).1, RelativeHalfBraiding.biproduct F _ fun j ↦ (G j).2⟩
  π j :=
    { f := biproduct.π (fun j ↦ (G j).1) j
      comm U :=
        (RelativeHalfBraiding.biproduct_β_hom_comp_biproduct_π _ (fun j ↦ (G j).2) U j).symm }
  ι j :=
    { f := biproduct.ι (fun j ↦ (G j).1) j
      comm U :=
        RelativeHalfBraiding.biproduct_ι_comp_biproduct_β_hom _ (fun j ↦ (G j).2) U j }
  ι_π j j' := by
    split_ifs with h
    · subst h
      ext
      exact biproduct.ι_π_self _ j
    · ext
      exact biproduct.ι_π_ne _ h

@[simp]
theorem biproductBicone_pt_fst (G : J → F.RelativeCenter) [HasBiproduct fun j ↦ (G j).1] :
    (biproductBicone G).pt.1 = ⨁ fun j ↦ (G j).1 :=
  rfl

@[simp]
theorem biproductBicone_pt_snd (G : J → F.RelativeCenter) [HasBiproduct fun j ↦ (G j).1] :
    (biproductBicone G).pt.2 = RelativeHalfBraiding.biproduct F _ fun j ↦ (G j).2 :=
  rfl

@[simp]
theorem biproductBicone_π_f (G : J → F.RelativeCenter) [HasBiproduct fun j ↦ (G j).1] (j : J) :
    ((biproductBicone G).π j).f = biproduct.π (fun j ↦ (G j).1) j :=
  rfl

@[simp]
theorem biproductBicone_ι_f (G : J → F.RelativeCenter) [HasBiproduct fun j ↦ (G j).1] (j : J) :
    ((biproductBicone G).ι j).f = biproduct.ι (fun j ↦ (G j).1) j :=
  rfl

/-- The bicone `biproductBicone G` is a bilimit bicone in `F.RelativeCenter`. -/
noncomputable def isBilimitBiproductBicone (G : J → F.RelativeCenter)
    [HasBiproduct fun j ↦ (G j).1] : (biproductBicone G).IsBilimit :=
  let := Fintype.ofFinite J
  isBilimitOfTotal _ <| by
    ext
    simp only [sum_f, comp_f, id_f, biproductBicone_π_f, biproductBicone_ι_f,
      biproductBicone_pt_fst]
    exact biproduct.total

instance instHasBiproduct (G : J → F.RelativeCenter) [HasBiproduct fun j ↦ (G j).1] :
    HasBiproduct G :=
  HasBiproduct.mk ⟨_, isBilimitBiproductBicone G⟩

instance instHasBiproductsOfShape [HasBiproductsOfShape J D] :
    HasBiproductsOfShape J F.RelativeCenter where
  has_biproduct _ := inferInstance

instance instHasFiniteBiproducts [HasFiniteBiproducts D] :
    HasFiniteBiproducts F.RelativeCenter where
  out _ := inferInstance

end Biproduct

end RelativeCenter

end CategoryTheory.Functor
