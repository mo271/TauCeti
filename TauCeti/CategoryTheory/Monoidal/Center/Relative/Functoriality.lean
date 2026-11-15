/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Basic
public import TauCeti.CategoryTheory.Monoidal.Center.Preadditive
public import TauCeti.CategoryTheory.Monoidal.Center.Relative.Preadditive
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Functoriality of the relative centre

While the Drinfeld centre `Center C` is not directly functorial in a strong monoidal functor
`F : C ⥤ D`, passing to the relative centre `F.RelativeCenter` produces a span of strong monoidal
functors connecting `Center C` and `Center D` through `F.RelativeCenter`. This file establishes the
functoriality of the relative centre:

1. **Identity functor (`Z(𝟭 C) ≌ Center C`)**: an `(𝟭 C)`-relative half-braiding on `X : C` has
   the same data and axioms as an ordinary `HalfBraiding X`
   (`CategoryTheory.Functor.RelativeHalfBraiding.idEquiv`), yielding a monoidal equivalence
   `CategoryTheory.Functor.RelativeCenter.equivCenter C : (𝟭 C).RelativeCenter ≌ Center C` that
   commutes strictly with the forgetful functors to `C` and is additive and `R`-linear when `C` is
   monoidal preadditive or monoidal `R`-linear.
2. **Lift from the Drinfeld centre (`J_F : Center C ⥤ F.RelativeCenter`)**: a strong monoidal
   functor `F : C ⥤ D` maps a half-braiding `b : HalfBraiding X` to an `F`-relative half-braiding
   `F.mapHalfBraiding b` on `F.obj X` with component `μ F X U ≫ F.map (b.β U).hom ≫ δ F U X`.
   This assembles into a strong monoidal functor
   `CategoryTheory.Functor.RelativeCenter.ofCenter F : Center C ⥤ F.RelativeCenter` equipped with
   a monoidal natural isomorphism `ofCenter F ⋙ forget F ≅ Center.forget C ⋙ F` and a monoidal
   identification `ofCenter (𝟭 C) ≅ (equivCenter C).inverse`.
3. **Change of functor (`precompose` and `congrNatIso`)**: precomposing `F : C ⥤ D` with a strong
   monoidal functor `G : C' ⥤ C` restricts `F`-relative half-braidings to `(G ⋙ F)`-relative
   half-braidings via a strong monoidal functor
   `RelativeCenter.precompose G F : F.RelativeCenter ⥤ (G ⋙ F).RelativeCenter`,
   and a monoidal natural isomorphism `α : F ≅ F'` induces a monoidal equivalence
   `CategoryTheory.Functor.RelativeCenter.congrNatIso α : F.RelativeCenter ≌ F'.RelativeCenter`.

## Main declarations

* `CategoryTheory.Functor.RelativeHalfBraiding.idEquiv`: equivalence between
  `(𝟭 C).RelativeHalfBraiding X` and `HalfBraiding X`;
* `CategoryTheory.Functor.RelativeCenter.equivCenter`: the monoidal equivalence
  `(𝟭 C).RelativeCenter ≌ Center C`;
* `CategoryTheory.Functor.mapHalfBraiding`: the `F`-relative half-braiding on `F.obj X` induced by
  a half-braiding on `X`;
* `CategoryTheory.Functor.RelativeCenter.ofCenter`: the strong monoidal functor
  `Center C ⥤ F.RelativeCenter`, together with `ofCenterForgetIso` and `ofCenterIdIso`;
* `CategoryTheory.Functor.RelativeCenter.precompose`: the strong monoidal functor
  `F.RelativeCenter ⥤ (G ⋙ F).RelativeCenter` induced by `G : C' ⥤ C`;
* `CategoryTheory.Functor.RelativeCenter.congrNatIso`: the monoidal equivalence
  `F.RelativeCenter ≌ F'.RelativeCenter` induced by a monoidal natural isomorphism `α : F ≅ F'`.

## References

* S. Majid, *Representations, duals and quantum doubles of monoidal categories*, Rend. Circ. Mat.
  Palermo (2) Suppl. **26** (1991), 197–206.
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13.
* A. M. Gainutdinov, J. Haferkamp, C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. **414** (2023), 108853, §3.1.
-/

public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace CategoryTheory.Functor

variable {C' : Type u₃} [Category.{v₃} C'] [MonoidalCategory C']
  {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-! ### Comparison at the identity functor -/

namespace RelativeHalfBraiding

/-- An `(𝟭 C)`-relative half-braiding on `X : C` seen as an ordinary half-braiding on `X`. -/
@[expose, simps]
def toHalfBraiding {X : C} (b : (𝟭 C).RelativeHalfBraiding X) : HalfBraiding X where
  β := b.β
  monoidal _ _ := by simp
  naturality f := b.naturality f

/-- An ordinary half-braiding on `X : C` seen as an `(𝟭 C)`-relative half-braiding on `X`. -/
@[expose, simps]
def ofHalfBraiding {X : C} (b : HalfBraiding X) : (𝟭 C).RelativeHalfBraiding X where
  β := b.β
  monoidal _ _ := by simp
  naturality f := b.naturality f

@[simp]
theorem ofHalfBraiding_toHalfBraiding {X : C} (b : (𝟭 C).RelativeHalfBraiding X) :
    ofHalfBraiding b.toHalfBraiding = b :=
  rfl

@[simp]
theorem toHalfBraiding_ofHalfBraiding {X : C} (b : HalfBraiding X) :
    (ofHalfBraiding b).toHalfBraiding = b :=
  rfl

/-- Equivalence between `(𝟭 C)`-relative half-braidings on `X` and half-braidings on `X`. -/
@[expose, simps]
def idEquiv (X : C) : (𝟭 C).RelativeHalfBraiding X ≃ HalfBraiding X where
  toFun := toHalfBraiding
  invFun := ofHalfBraiding
  left_inv _ := rfl
  right_inv _ := rfl

end RelativeHalfBraiding

namespace RelativeCenter

section Identity

variable (C)

/-- The functor from `(𝟭 C).RelativeCenter` to `Center C` identifying `(𝟭 C)`-relative
half-braidings with ordinary half-braidings. -/
@[expose]
def toCenter : (𝟭 C).RelativeCenter ⥤ Center C where
  obj X := ⟨X.1, X.2.toHalfBraiding⟩
  map f := ⟨f.f, f.comm⟩

@[simp]
theorem toCenter_obj_fst (X : (𝟭 C).RelativeCenter) :
    (Center.forget C).obj ((toCenter C).obj X) = X.1 :=
  rfl

@[simp]
theorem toCenter_map_f {X Y : (𝟭 C).RelativeCenter} (f : X ⟶ Y) :
    ((toCenter C).map f).f = f.f :=
  rfl

/-- The functor from `Center C` to `(𝟭 C).RelativeCenter` viewing ordinary half-braidings as
`(𝟭 C)`-relative half-braidings. -/
@[expose]
def ofCenterId : Center C ⥤ (𝟭 C).RelativeCenter where
  obj X := ⟨X.1, .ofHalfBraiding X.2⟩
  map f := ⟨f.f, f.comm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem ofCenterId_obj_fst (X : Center C) :
    ((ofCenterId C).obj X).1 = (Center.forget C).obj X :=
  rfl

@[simp]
theorem ofCenterId_obj_snd (X : Center C) :
    ((ofCenterId C).obj X).2 = .ofHalfBraiding X.2 :=
  rfl

@[simp]
theorem ofCenterId_map_f {X Y : Center C} (f : X ⟶ Y) : ((ofCenterId C).map f).f = f.f :=
  rfl

instance instMonoidalToCenter : (toCenter C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := fun f X' ↦
        Center.ext _ _ ((Category.comp_id (f.f ▷ X'.1)).trans (Category.id_comp _).symm)
      μIso_hom_natural_right := fun X' f ↦
        Center.ext _ _ ((Category.comp_id (X'.1 ◁ f.f)).trans (Category.id_comp _).symm)
      associativity := fun X Y Z ↦
        Center.ext _ _
          (by change (𝟙 (X.1 ⊗ Y.1) ▷ Z.1) ≫ 𝟙 _ ≫ (α_ X.1 Y.1 Z.1).hom =
                (α_ X.1 Y.1 Z.1).hom ≫ (X.1 ◁ 𝟙 (Y.1 ⊗ Z.1)) ≫ 𝟙 _; simp)
      left_unitality := fun X ↦
        Center.ext _ _
          (by change (λ_ X.1).hom = (𝟙 (𝟙_ C) ▷ X.1) ≫ 𝟙 _ ≫ (λ_ X.1).hom; simp)
      right_unitality := fun X ↦
        Center.ext _ _
          (by change (ρ_ X.1).hom = (X.1 ◁ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ X.1).hom; simp) }

@[simp] theorem toCenter_ε_f : (ε (toCenter C)).f = 𝟙 (𝟙_ C) := rfl
@[simp] theorem toCenter_η_f : (η (toCenter C)).f = 𝟙 (𝟙_ C) := rfl
@[simp] theorem toCenter_μ_f (X Y : (𝟭 C).RelativeCenter) :
    (μ (toCenter C) X Y).f = 𝟙 (X.1 ⊗ Y.1) := rfl
@[simp] theorem toCenter_δ_f (X Y : (𝟭 C).RelativeCenter) :
    (δ (toCenter C) X Y).f = 𝟙 (X.1 ⊗ Y.1) := rfl

instance instMonoidalOfCenterId : (ofCenterId C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := fun f X' ↦
        Hom.ext ((Category.comp_id (f.f ▷ ((Center.forget C).obj X'))).trans
          (Category.id_comp _).symm)
      μIso_hom_natural_right := fun X' f ↦
        Hom.ext ((Category.comp_id (((Center.forget C).obj X') ◁ f.f)).trans
          (Category.id_comp _).symm)
      associativity := fun X Y Z ↦
        Hom.ext <| by
          let X₀ := (Center.forget C).obj X
          let Y₀ := (Center.forget C).obj Y
          let Z₀ := (Center.forget C).obj Z
          change (𝟙 (X₀ ⊗ Y₀) ▷ Z₀) ≫ 𝟙 _ ≫ (α_ X₀ Y₀ Z₀).hom =
            (α_ X₀ Y₀ Z₀).hom ≫ (X₀ ◁ 𝟙 (Y₀ ⊗ Z₀)) ≫ 𝟙 _
          simp
      left_unitality := fun X ↦
        Hom.ext <| by
          let X₀ := (Center.forget C).obj X
          change (λ_ X₀).hom = (𝟙 (𝟙_ C) ▷ X₀) ≫ 𝟙 _ ≫ (λ_ X₀).hom
          simp
      right_unitality := fun X ↦
        Hom.ext <| by
          let X₀ := (Center.forget C).obj X
          change (ρ_ X₀).hom = (X₀ ◁ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ X₀).hom
          simp }

@[simp] theorem ofCenterId_ε_f : (ε (ofCenterId C)).f = 𝟙 (𝟙_ C) := rfl
@[simp] theorem ofCenterId_η_f : (η (ofCenterId C)).f = 𝟙 (𝟙_ C) := rfl
@[simp] theorem ofCenterId_μ_f (X Y : Center C) :
    (μ (ofCenterId C) X Y).f = 𝟙 ((Center.forget C).obj X ⊗ (Center.forget C).obj Y) := rfl
@[simp] theorem ofCenterId_δ_f (X Y : Center C) :
    (δ (ofCenterId C) X Y).f = 𝟙 ((Center.forget C).obj X ⊗ (Center.forget C).obj Y) := rfl

/-- The monoidal equivalence `(𝟭 C).RelativeCenter ≌ Center C` identifying `(𝟭 C)`-relative
half-braidings with ordinary half-braidings. -/
@[expose]
def equivCenter : (𝟭 C).RelativeCenter ≌ Center C where
  functor := toCenter C
  inverse := ofCenterId C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.comp_id _

@[simp] theorem equivCenter_functor : (equivCenter C).functor = toCenter C := rfl
@[simp] theorem equivCenter_inverse : (equivCenter C).inverse = ofCenterId C := rfl
@[simp] theorem equivCenter_unit_app (X : (𝟭 C).RelativeCenter) :
    (equivCenter C).unit.app X = 𝟙 X := rfl
@[simp] theorem equivCenter_counit_app (X : Center C) :
    (equivCenter C).counit.app X = 𝟙 X := rfl

instance instMonoidalEquivCenterFunctor : (equivCenter C).functor.Monoidal :=
  inferInstanceAs (toCenter C).Monoidal

instance instMonoidalEquivCenterInverse : (equivCenter C).inverse.Monoidal :=
  inferInstanceAs (ofCenterId C).Monoidal

instance instIsMonoidalEquivCenterUnit : NatTrans.IsMonoidal (equivCenter C).unit where
  unit := Hom.ext rfl
  tensor X Y := Hom.ext <| by
    change 𝟙 (X.1 ⊗ Y.1) ≫ 𝟙 (X.1 ⊗ Y.1) =
      (𝟙 X.1 ⊗ₘ 𝟙 Y.1) ≫ (𝟙 (X.1 ⊗ Y.1) ≫ 𝟙 (X.1 ⊗ Y.1))
    simp

instance instIsMonoidalEquivCenter : (equivCenter C).IsMonoidal :=
  Equivalence.isMonoidal_of_isMonoidal_unit (equivCenter C)

/-- `toCenter C` commutes strictly with the forgetful functors to `C`. -/
@[expose, simps!]
def toCenterForgetIso : toCenter C ⋙ Center.forget C ≅ forget (𝟭 C) :=
  Iso.refl _

instance instIsMonoidalToCenterForgetIsoHom :
    NatTrans.IsMonoidal (toCenterForgetIso C).hom where
  unit := by change (𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C)) ≫ 𝟙 (𝟙_ C) = 𝟙 (𝟙_ C); simp
  tensor X Y := by
    change (𝟙 (X.1 ⊗ Y.1) ≫ 𝟙 (X.1 ⊗ Y.1)) ≫ 𝟙 (X.1 ⊗ Y.1) =
      (𝟙 X.1 ⊗ₘ 𝟙 Y.1) ≫ 𝟙 (X.1 ⊗ Y.1)
    simp

/-- `ofCenterId C` commutes strictly with the forgetful functors to `C`. -/
@[expose, simps!]
def ofCenterIdForgetIso : ofCenterId C ⋙ forget (𝟭 C) ≅ Center.forget C :=
  Iso.refl _

instance instIsMonoidalOfCenterIdForgetIsoHom :
    NatTrans.IsMonoidal (ofCenterIdForgetIso C).hom where
  unit := by change (𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C)) ≫ 𝟙 (𝟙_ C) = 𝟙 (𝟙_ C); simp
  tensor X Y := by
    let X₀ := (Center.forget C).obj X
    let Y₀ := (Center.forget C).obj Y
    change (𝟙 (X₀ ⊗ Y₀) ≫ 𝟙 (X₀ ⊗ Y₀)) ≫ 𝟙 (X₀ ⊗ Y₀) = (𝟙 X₀ ⊗ₘ 𝟙 Y₀) ≫ 𝟙 (X₀ ⊗ Y₀)
    simp

instance instAdditiveToCenter [Preadditive C] [MonoidalPreadditive C] :
    (toCenter C).Additive where

instance instAdditiveOfCenterId [Preadditive C] [MonoidalPreadditive C] :
    (ofCenterId C).Additive where

instance instLinearToCenter [Preadditive C] [MonoidalPreadditive C]
    {R : Type*} [Semiring R] [CategoryTheory.Linear R C] [MonoidalLinear R C] :
    (toCenter C).Linear R where

instance instLinearOfCenterId [Preadditive C] [MonoidalPreadditive C]
    {R : Type*} [Semiring R] [CategoryTheory.Linear R C] [MonoidalLinear R C] :
    (ofCenterId C).Linear R where

end Identity

end RelativeCenter

/-! ### Pushing half-braidings forward along a strong monoidal functor -/

/-- A strong monoidal functor `F : C ⥤ D` carries a half-braiding `b` on `X : C` to an
`F`-relative half-braiding on `F.obj X`, with component at `U : C` given by
`μ F X U ≫ F.map (b.β U).hom ≫ δ F U X`. -/
@[expose]
noncomputable def mapHalfBraiding (F : C ⥤ D) [F.Monoidal] {X : C} (b : HalfBraiding X) :
    F.RelativeHalfBraiding (F.obj X) where
  β U := μIso F X U ≪≫ F.mapIso (b.β U) ≪≫ (μIso F U X).symm
  monoidal U U' := by
    simp only [μIso_hom, μIso_inv, mapIso_hom, Iso.trans_hom, Iso.symm_hom, b.monoidal,
      F.map_comp, map_associator_inv, map_associator, map_whiskerRight, map_whiskerLeft,
      comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_δ_assoc, μ_δ,
      Category.comp_id]
  naturality g := by
    dsimp
    rw [μ_natural_right_assoc, ← F.map_comp_assoc, b.naturality, F.map_comp, Category.assoc,
      ← δ_natural_left, Category.assoc, Category.assoc]

@[simp]
theorem mapHalfBraiding_β_hom (F : C ⥤ D) [F.Monoidal] {X : C} (b : HalfBraiding X) (U : C) :
    ((F.mapHalfBraiding b).β U).hom = μ F X U ≫ F.map (b.β U).hom ≫ δ F U X :=
  rfl

@[simp]
theorem mapHalfBraiding_β_inv (F : C ⥤ D) [F.Monoidal] {X : C} (b : HalfBraiding X) (U : C) :
    ((F.mapHalfBraiding b).β U).inv = μ F U X ≫ F.map (b.β U).inv ≫ δ F X U := by
  simp [mapHalfBraiding]

@[simp]
theorem mapHalfBraiding_id {X : C} (b : HalfBraiding X) :
    (𝟭 C).mapHalfBraiding b = .ofHalfBraiding b := by
  ext U
  simp

/-- If `g : X ⟶ Y` commutes with half-braidings `bX` and `bY` at `U`, then `F.map g` commutes with
`F.mapHalfBraiding bX` and `F.mapHalfBraiding bY` at `U`. -/
theorem mapHalfBraiding_comm (F : C ⥤ D) [F.Monoidal] {X Y : C} {bX : HalfBraiding X}
    {bY : HalfBraiding Y} {g : X ⟶ Y} {U : C}
    (hg : g ▷ U ≫ (bY.β U).hom = (bX.β U).hom ≫ U ◁ g) :
    F.map g ▷ F.obj U ≫ ((F.mapHalfBraiding bY).β U).hom =
      ((F.mapHalfBraiding bX).β U).hom ≫ F.obj U ◁ F.map g := by
  rw [mapHalfBraiding_β_hom, mapHalfBraiding_β_hom, μ_natural_left_assoc, ← F.map_comp_assoc,
    hg, F.map_comp, Category.assoc, ← δ_natural_right, Category.assoc, Category.assoc]

namespace RelativeCenter

section OfCenter

variable (F : C ⥤ D) [F.Monoidal]

/-- The strong monoidal functor `J_F : Center C ⥤ F.RelativeCenter` sending `(X, b)` to
`(F.obj X, F.mapHalfBraiding b)` and `f` to `F.map f.f`. -/
@[expose]
noncomputable def ofCenter : Center C ⥤ F.RelativeCenter where
  obj X := ⟨F.obj X.1, F.mapHalfBraiding X.2⟩
  map f :=
    { f := F.map f.f
      comm U := F.mapHalfBraiding_comm (f.comm U) }
  map_id X := Hom.ext (F.map_id ((Center.forget C).obj X))
  map_comp f g := Hom.ext (F.map_comp f.f g.f)

@[simp]
theorem ofCenter_obj_fst (X : Center C) :
    ((ofCenter F).obj X).1 = F.obj ((Center.forget C).obj X) :=
  rfl

@[simp]
theorem ofCenter_obj_snd (X : Center C) : ((ofCenter F).obj X).2 = F.mapHalfBraiding X.2 :=
  rfl

@[simp]
theorem ofCenter_map_f {X Y : Center C} (f : X ⟶ Y) : ((ofCenter F).map f).f = F.map f.f :=
  rfl

/-- Compatibility of `ε F` with the unit relative half-braiding and `F.mapHalfBraiding`. -/
theorem ofCenter_ε_comm_aux {b : HalfBraiding (𝟙_ C)} {U : C}
    (hb : (b.β U).hom = (λ_ U).hom ≫ (ρ_ U).inv) :
    ε F ▷ F.obj U ≫ ((F.mapHalfBraiding b).β U).hom =
      ((unitHalfBraiding (F := F)).β U).hom ≫ F.obj U ◁ ε F := by
  rw [mapHalfBraiding_β_hom, hb, F.map_comp, map_leftUnitor, map_rightUnitor_inv]
  simp [unitHalfBraiding]

/-- Compatibility of `η F` with the unit relative half-braiding and `F.mapHalfBraiding`. -/
theorem ofCenter_η_comm_aux {b : HalfBraiding (𝟙_ C)} {U : C}
    (hb : (b.β U).hom = (λ_ U).hom ≫ (ρ_ U).inv) :
    η F ▷ F.obj U ≫ ((unitHalfBraiding (F := F)).β U).hom =
      ((F.mapHalfBraiding b).β U).hom ≫ F.obj U ◁ η F := by
  rw [← cancel_epi (ε F ▷ F.obj U), ← comp_whiskerRight_assoc, ε_η, id_whiskerRight,
    Category.id_comp, ← Category.assoc, ofCenter_ε_comm_aux F hb, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ε_η, MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- Compatibility of `μ F X Y` with tensor relative half-braidings and `F.mapHalfBraiding`. -/
theorem ofCenter_μ_comm_aux {X Y : C} (bX : HalfBraiding X) (bY : HalfBraiding Y)
    {bXY : HalfBraiding (X ⊗ Y)} {U : C}
    (hb : (bXY.β U).hom =
      (α_ X Y U).hom ≫ X ◁ (bY.β U).hom ≫ (α_ X U Y).inv ≫
        (bX.β U).hom ▷ Y ≫ (α_ U X Y).hom) :
    μ F X Y ▷ F.obj U ≫ ((F.mapHalfBraiding bXY).β U).hom =
      ((tensorHalfBraiding ⟨F.obj X, F.mapHalfBraiding bX⟩
          ⟨F.obj Y, F.mapHalfBraiding bY⟩).β U).hom ≫
        F.obj U ◁ μ F X Y := by
  simp only [mapHalfBraiding_β_hom, hb, F.map_comp, map_associator, map_associator_inv,
    map_whiskerLeft, map_whiskerRight, tensorHalfBraiding_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
    Category.assoc, μ_δ_assoc, whiskerRight_μ_δ_assoc, μ_δ, Category.comp_id]

/-- Compatibility of `δ F X Y` with tensor relative half-braidings and `F.mapHalfBraiding`. -/
theorem ofCenter_δ_comm_aux {X Y : C} (bX : HalfBraiding X) (bY : HalfBraiding Y)
    {bXY : HalfBraiding (X ⊗ Y)} {U : C}
    (hb : (bXY.β U).hom =
      (α_ X Y U).hom ≫ X ◁ (bY.β U).hom ≫ (α_ X U Y).inv ≫
        (bX.β U).hom ▷ Y ≫ (α_ U X Y).hom) :
    δ F X Y ▷ F.obj U ≫
        ((tensorHalfBraiding ⟨F.obj X, F.mapHalfBraiding bX⟩
            ⟨F.obj Y, F.mapHalfBraiding bY⟩).β U).hom =
      ((F.mapHalfBraiding bXY).β U).hom ≫ F.obj U ◁ δ F X Y := by
  rw [← cancel_epi (μ F X Y ▷ F.obj U), ← comp_whiskerRight_assoc, μ_δ, id_whiskerRight,
    Category.id_comp, ← Category.assoc, ofCenter_μ_comm_aux F bX bY hb, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, μ_δ, MonoidalCategory.whiskerLeft_id, Category.comp_id]

noncomputable instance instMonoidalOfCenter : (ofCenter F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := { f := ε F, comm := fun _ ↦ ofCenter_ε_comm_aux F rfl }
          inv := { f := η F, comm := fun _ ↦ ofCenter_η_comm_aux F rfl }
          hom_inv_id := Hom.ext (ε_η F)
          inv_hom_id := Hom.ext (η_ε F) }
      μIso := fun X Y ↦
        { hom := { f := μ F X.1 Y.1, comm := fun _ ↦ ofCenter_μ_comm_aux F X.2 Y.2 rfl }
          inv := { f := δ F X.1 Y.1, comm := fun _ ↦ ofCenter_δ_comm_aux F X.2 Y.2 rfl }
          hom_inv_id := Hom.ext (μ_δ F X.1 Y.1)
          inv_hom_id := Hom.ext (δ_μ F X.1 Y.1) }
      μIso_hom_natural_left := fun f X' ↦ Hom.ext (μ_natural_left F f.f X'.1)
      μIso_hom_natural_right := fun X' f ↦ Hom.ext (μ_natural_right F X'.1 f.f)
      associativity := fun X Y Z ↦ Hom.ext (LaxMonoidal.associativity F X.1 Y.1 Z.1)
      left_unitality := fun X ↦ Hom.ext (LaxMonoidal.left_unitality F X.1)
      right_unitality := fun X ↦ Hom.ext (LaxMonoidal.right_unitality F X.1) }

@[simp] theorem ofCenter_ε_f : (ε (ofCenter F)).f = ε F := rfl
@[simp] theorem ofCenter_η_f : (η (ofCenter F)).f = η F := rfl
@[simp] theorem ofCenter_μ_f (X Y : Center C) :
    (μ (ofCenter F) X Y).f = μ F ((Center.forget C).obj X) ((Center.forget C).obj Y) := rfl
@[simp] theorem ofCenter_δ_f (X Y : Center C) :
    (δ (ofCenter F) X Y).f = δ F ((Center.forget C).obj X) ((Center.forget C).obj Y) := rfl

/-- `ofCenter F` intertwines the forgetful functors to `D` and `C` with `F`. -/
@[expose, simps!]
noncomputable def ofCenterForgetIso : ofCenter F ⋙ forget F ≅ Center.forget C ⋙ F :=
  Iso.refl _

instance instIsMonoidalOfCenterForgetIsoHom :
    NatTrans.IsMonoidal (ofCenterForgetIso F).hom where
  unit := by
    change (𝟙 (𝟙_ D) ≫ ε F) ≫ 𝟙 (F.obj (𝟙_ C)) = ε F ≫ F.map (𝟙 (𝟙_ C))
    simp
  tensor X Y := by
    let X₀ := (Center.forget C).obj X
    let Y₀ := (Center.forget C).obj Y
    change (𝟙 (F.obj X₀ ⊗ F.obj Y₀) ≫ μ F X₀ Y₀) ≫ 𝟙 (F.obj (X₀ ⊗ Y₀)) =
      (𝟙 (F.obj X₀) ⊗ₘ 𝟙 (F.obj Y₀)) ≫ (μ F X₀ Y₀ ≫ F.map (𝟙 (X₀ ⊗ Y₀)))
    simp

/-- Compatibility of the identity morphism with `mapHalfBraiding` for `𝟭 C`. -/
theorem ofCenterIdIso_hom_comm {X U : C} (b : HalfBraiding X) :
    𝟙 X ▷ U ≫ (b.β U).hom = (((𝟭 C).mapHalfBraiding b).β U).hom ≫ U ◁ 𝟙 X := by
  simp

/-- Inverse compatibility of the identity morphism with `mapHalfBraiding` for `𝟭 C`. -/
theorem ofCenterIdIso_inv_comm {X U : C} (b : HalfBraiding X) :
    𝟙 X ▷ U ≫ (((𝟭 C).mapHalfBraiding b).β U).hom = (b.β U).hom ≫ U ◁ 𝟙 X := by
  simp

/-- At the identity functor `𝟭 C`, `ofCenter (𝟭 C)` is naturally isomorphic to `ofCenterId C`
(the inverse of `equivCenter C`) as a monoidal functor. -/
@[expose]
noncomputable def ofCenterIdIso (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] :
    ofCenter (𝟭 C) ≅ ofCenterId C :=
  NatIso.ofComponents
    (fun X ↦
      { hom := { f := 𝟙 X.1, comm := fun _ ↦ ofCenterIdIso_hom_comm X.2 }
        inv := { f := 𝟙 X.1, comm := fun _ ↦ ofCenterIdIso_inv_comm X.2 }
        hom_inv_id := Hom.ext (Category.comp_id (𝟙 ((Center.forget C).obj X)))
        inv_hom_id := Hom.ext (Category.comp_id (𝟙 ((Center.forget C).obj X))) })
    (fun f ↦ Hom.ext ((Category.comp_id f.f).trans (Category.id_comp f.f).symm))

@[simp]
theorem ofCenterIdIso_hom_app_f (X : Center C) :
    ((ofCenterIdIso C).hom.app X).f = 𝟙 ((Center.forget C).obj X) :=
  rfl

@[simp]
theorem ofCenterIdIso_inv_app_f (X : Center C) :
    ((ofCenterIdIso C).inv.app X).f = 𝟙 ((Center.forget C).obj X) :=
  rfl

instance instIsMonoidalOfCenterIdIsoHom (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] :
    NatTrans.IsMonoidal (ofCenterIdIso C).hom where
  unit := Hom.ext (Category.comp_id _)
  tensor X Y := Hom.ext <| by
    let X₀ := (Center.forget C).obj X
    let Y₀ := (Center.forget C).obj Y
    change 𝟙 (X₀ ⊗ Y₀) ≫ 𝟙 (X₀ ⊗ Y₀) = (𝟙 X₀ ⊗ₘ 𝟙 Y₀) ≫ 𝟙 (X₀ ⊗ Y₀)
    simp

instance instAdditiveOfCenter [Preadditive C] [MonoidalPreadditive C]
    [Preadditive D] [MonoidalPreadditive D] [F.Additive] :
    (ofCenter F).Additive where

instance instLinearOfCenter [Preadditive C] [MonoidalPreadditive C]
    [Preadditive D] [MonoidalPreadditive D]
    {R : Type*} [Semiring R] [CategoryTheory.Linear R C] [MonoidalLinear R C]
    [CategoryTheory.Linear R D] [MonoidalLinear R D] [F.Linear R] :
    (ofCenter F).Linear R where

end OfCenter

end RelativeCenter

/-! ### Precomposition and transport along monoidal natural isomorphisms -/

local instance instIsMonoidalIsoSymmHom {F F' : C ⥤ D} [F.LaxMonoidal] [F'.LaxMonoidal]
    (α : F ≅ F') [NatTrans.IsMonoidal α.hom] : NatTrans.IsMonoidal α.symm.hom :=
  inferInstanceAs (NatTrans.IsMonoidal α.inv)

local instance instIsMonoidalIsoTransHom {F F' F'' : C ⥤ D} [F.LaxMonoidal] [F'.LaxMonoidal]
    [F''.LaxMonoidal] (α : F ≅ F') (α' : F' ≅ F'')
    [NatTrans.IsMonoidal α.hom] [NatTrans.IsMonoidal α'.hom] :
    NatTrans.IsMonoidal (α ≪≫ α').hom :=
  inferInstanceAs (NatTrans.IsMonoidal (α.hom ≫ α'.hom))

namespace RelativeHalfBraiding

/-- Restrict an `F`-relative half-braiding along a strong monoidal functor `G : C' ⥤ C` to obtain
a `(G ⋙ F)`-relative half-braiding on the same object of `D`. -/
@[expose, simps]
def precompose (G : C' ⥤ C) [G.Monoidal] {F : C ⥤ D} [F.Monoidal] {X : D}
    (b : F.RelativeHalfBraiding X) : (G ⋙ F).RelativeHalfBraiding X where
  β U' := b.β (G.obj U')
  monoidal U₁ U₂ := by
    simp only [comp_obj, comp_δ, comp_μ, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
      Category.assoc]
    rw [← b.monoidal_assoc (G.obj U₁) (G.obj U₂), b.naturality_assoc (δ G U₁ U₂),
      ← comp_whiskerRight, ← F.map_comp, δ_μ, F.map_id, id_whiskerRight, Category.comp_id]
  naturality g := b.naturality (G.map g)

/-- Transport an `F`-relative half-braiding along a monoidal natural isomorphism `α : F ≅ F'`. -/
@[expose]
def congrNatIso {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] (α : F ≅ F')
    [NatTrans.IsMonoidal α.hom] {X : D} (b : F.RelativeHalfBraiding X) :
    F'.RelativeHalfBraiding X where
  β U := whiskerLeftIso X (α.app U).symm ≪≫ b.β U ≪≫ whiskerRightIso (α.app U) X
  monoidal U U' := by
    have hδ : δ F' U U' ≫ (α.inv.app U ⊗ₘ α.inv.app U') = α.inv.app (U ⊗ U') ≫ δ F U U' := by
      rw [← cancel_epi (μ F' U U'), μ_δ_assoc, ← cancel_mono (μ F U U'), Category.assoc,
        Category.assoc, δ_μ, Category.comp_id, ← NatTrans.IsMonoidal.tensor]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, Iso.app_inv,
      whiskerRightIso_hom, Iso.app_hom]
    rw [b.monoidal U U']
    simp only [Category.assoc]
    rw [← comp_whiskerRight, NatTrans.IsMonoidal.tensor (τ := α.hom) U U', tensorHom_def',
      comp_whiskerRight, comp_whiskerRight, ← MonoidalCategory.whiskerLeft_comp_assoc, ← hδ,
      tensorHom_def, MonoidalCategory.whiskerLeft_comp_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
      whisker_exchange_assoc, associator_naturality_right_assoc]
    slice_lhs 8 9 =>
      rw [← associator_inv_naturality_middle]
    simp only [Category.assoc]
    slice_lhs 9 10 =>
      rw [← associator_inv_naturality_left]
    simp only [Category.assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      whisker_exchange_assoc, ← associator_naturality_left_assoc, comp_whiskerRight_assoc,
      comp_whiskerRight_assoc]
    simp only [Category.assoc]
  naturality g := by
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, Iso.app_inv,
      whiskerRightIso_hom, Iso.app_hom, Category.assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, α.inv.naturality,
      MonoidalCategory.whiskerLeft_comp_assoc, b.naturality_assoc, ← comp_whiskerRight,
      α.hom.naturality, comp_whiskerRight]

@[simp]
theorem congrNatIso_β_hom {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] (α : F ≅ F')
    [NatTrans.IsMonoidal α.hom] {X : D} (b : F.RelativeHalfBraiding X) (U : C) :
    ((b.congrNatIso α).β U).hom = X ◁ α.inv.app U ≫ (b.β U).hom ≫ α.hom.app U ▷ X :=
  rfl

@[simp]
theorem congrNatIso_β_inv {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] (α : F ≅ F')
    [NatTrans.IsMonoidal α.hom] {X : D} (b : F.RelativeHalfBraiding X) (U : C) :
    ((b.congrNatIso α).β U).inv = α.inv.app U ▷ X ≫ (b.β U).inv ≫ X ◁ α.hom.app U := by
  simp [congrNatIso]

@[simp]
theorem congrNatIso_refl {F : C ⥤ D} [F.Monoidal] {_ : NatTrans.IsMonoidal (Iso.refl F).hom}
    {X : D} (b : F.RelativeHalfBraiding X) :
    b.congrNatIso (Iso.refl F) = b := by
  ext U
  simp

/-- Transporting an `F`-relative half-braiding along `α` and then `α'` agrees with transporting
along `α ≪≫ α'`. -/
theorem congrNatIso_trans {F F' F'' : C ⥤ D} [F.Monoidal] [F'.Monoidal] [F''.Monoidal]
    (α : F ≅ F') (α' : F' ≅ F'') [NatTrans.IsMonoidal α.hom] [NatTrans.IsMonoidal α'.hom]
    {X : D} (b : F.RelativeHalfBraiding X) :
    (b.congrNatIso α).congrNatIso α' = b.congrNatIso (α ≪≫ α') := by
  ext U
  simp only [congrNatIso_β_hom, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]

@[simp]
theorem congrNatIso_symm_congrNatIso {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] (α : F ≅ F')
    [NatTrans.IsMonoidal α.hom] {X : D} (b : F.RelativeHalfBraiding X) :
    (b.congrNatIso α).congrNatIso α.symm = b := by
  ext U
  simp [← MonoidalCategory.whiskerLeft_comp_assoc, ← comp_whiskerRight]

@[simp]
theorem congrNatIso_congrNatIso_symm {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] (α : F ≅ F')
    [NatTrans.IsMonoidal α.hom] {X : D} (b : F'.RelativeHalfBraiding X) :
    (b.congrNatIso α.symm).congrNatIso α = b :=
  congrNatIso_symm_congrNatIso α.symm b

end RelativeHalfBraiding

namespace RelativeCenter

section Precompose

variable (G : C' ⥤ C) (F : C ⥤ D) [G.Monoidal] [F.Monoidal]

/-- Precomposition with a strong monoidal functor `G : C' ⥤ C` restricts `F`-relative
half-braidings to `(G ⋙ F)`-relative half-braidings. -/
@[expose]
def precompose : F.RelativeCenter ⥤ (G ⋙ F).RelativeCenter where
  obj X := ⟨X.1, X.2.precompose G⟩
  map f := ⟨f.f, fun U' ↦ f.comm (G.obj U')⟩

@[simp]
theorem precompose_obj_fst (X : F.RelativeCenter) : ((precompose G F).obj X).1 = X.1 :=
  rfl

@[simp]
theorem precompose_obj_snd (X : F.RelativeCenter) :
    ((precompose G F).obj X).2 = X.2.precompose G :=
  rfl

@[simp]
theorem precompose_map_f {X Y : F.RelativeCenter} (f : X ⟶ Y) :
    ((precompose G F).map f).f = f.f :=
  rfl

instance instMonoidalPrecompose : (precompose G F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := { f := 𝟙 (𝟙_ D), comm := fun _ ↦ by simp }
          inv := { f := 𝟙 (𝟙_ D), comm := fun _ ↦ by simp }
          hom_inv_id := Hom.ext (Category.comp_id _)
          inv_hom_id := Hom.ext (Category.comp_id _) }
      μIso := fun X Y ↦
        { hom := { f := 𝟙 (X.1 ⊗ Y.1), comm := fun _ ↦ by simp }
          inv := { f := 𝟙 (X.1 ⊗ Y.1), comm := fun _ ↦ by simp }
          hom_inv_id := Hom.ext (Category.comp_id _)
          inv_hom_id := Hom.ext (Category.comp_id _) }
      μIso_hom_natural_left := fun f X' ↦
        Hom.ext ((Category.comp_id (f.f ▷ X'.1)).trans (Category.id_comp _).symm)
      μIso_hom_natural_right := fun X' f ↦
        Hom.ext ((Category.comp_id (X'.1 ◁ f.f)).trans (Category.id_comp _).symm)
      associativity := fun X Y Z ↦
        Hom.ext
          (by change (𝟙 (X.1 ⊗ Y.1) ▷ Z.1) ≫ 𝟙 _ ≫ (α_ X.1 Y.1 Z.1).hom =
                (α_ X.1 Y.1 Z.1).hom ≫ (X.1 ◁ 𝟙 (Y.1 ⊗ Z.1)) ≫ 𝟙 _; simp)
      left_unitality := fun X ↦
        Hom.ext (by change (λ_ X.1).hom = (𝟙 (𝟙_ D) ▷ X.1) ≫ 𝟙 _ ≫ (λ_ X.1).hom; simp)
      right_unitality := fun X ↦
        Hom.ext (by change (ρ_ X.1).hom = (X.1 ◁ 𝟙 (𝟙_ D)) ≫ 𝟙 _ ≫ (ρ_ X.1).hom; simp) }

@[simp] theorem precompose_ε_f : (ε (precompose G F)).f = 𝟙 (𝟙_ D) := rfl
@[simp] theorem precompose_η_f : (η (precompose G F)).f = 𝟙 (𝟙_ D) := rfl
@[simp] theorem precompose_μ_f (X Y : F.RelativeCenter) :
    (μ (precompose G F) X Y).f = 𝟙 (X.1 ⊗ Y.1) := rfl
@[simp] theorem precompose_δ_f (X Y : F.RelativeCenter) :
    (δ (precompose G F) X Y).f = 𝟙 (X.1 ⊗ Y.1) := rfl

/-- `precompose G F` commutes strictly with the forgetful functors to `D`. -/
@[expose, simps!]
def precomposeForgetIso : precompose G F ⋙ forget (G ⋙ F) ≅ forget F :=
  Iso.refl _

instance instIsMonoidalPrecomposeForgetIsoHom :
    NatTrans.IsMonoidal (precomposeForgetIso G F).hom where
  unit := by change (𝟙 (𝟙_ D) ≫ 𝟙 (𝟙_ D)) ≫ 𝟙 (𝟙_ D) = 𝟙 (𝟙_ D); simp
  tensor X Y := by
    change (𝟙 (X.1 ⊗ Y.1) ≫ 𝟙 (X.1 ⊗ Y.1)) ≫ 𝟙 (X.1 ⊗ Y.1) =
      (𝟙 X.1 ⊗ₘ 𝟙 Y.1) ≫ 𝟙 (X.1 ⊗ Y.1)
    simp

instance instAdditivePrecompose [Preadditive D] [MonoidalPreadditive D] :
    (precompose G F).Additive where

instance instLinearPrecompose [Preadditive D] [MonoidalPreadditive D]
    {R : Type*} [Semiring R] [CategoryTheory.Linear R D] [MonoidalLinear R D] :
    (precompose G F).Linear R where

end Precompose

section CongrNatIso

variable {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] (α : F ≅ F') [NatTrans.IsMonoidal α.hom]

/-- The functor `F.RelativeCenter ⥤ F'.RelativeCenter` transporting `F`-relative half-braidings
along a monoidal natural isomorphism `α : F ≅ F'`. -/
@[expose]
def congrNatIsoFunctor : F.RelativeCenter ⥤ F'.RelativeCenter where
  obj X := ⟨X.1, X.2.congrNatIso α⟩
  map f :=
    { f := f.f
      comm U := by
        rw [RelativeHalfBraiding.congrNatIso_β_hom, RelativeHalfBraiding.congrNatIso_β_hom,
          ← whisker_exchange_assoc, f.comm_assoc, Category.assoc, Category.assoc,
          whisker_exchange] }

@[simp]
theorem congrNatIsoFunctor_obj_fst (X : F.RelativeCenter) :
    ((congrNatIsoFunctor α).obj X).1 = X.1 :=
  rfl

@[simp]
theorem congrNatIsoFunctor_obj_snd (X : F.RelativeCenter) :
    ((congrNatIsoFunctor α).obj X).2 = X.2.congrNatIso α :=
  rfl

@[simp]
theorem congrNatIsoFunctor_map_f {X Y : F.RelativeCenter} (f : X ⟶ Y) :
    ((congrNatIsoFunctor α).map f).f = f.f :=
  rfl

/-- Compatibility of the unit relative half-braidings under `congrNatIsoFunctor`. -/
theorem congrNatIsoFunctor_ε_comm (U : C) :
    (((unitHalfBraiding (F := F)).congrNatIso α).β U).hom =
      ((unitHalfBraiding (F := F')).β U).hom := by
  simp only [RelativeHalfBraiding.congrNatIso_β_hom, unitHalfBraiding_β, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [leftUnitor_naturality_assoc, ← rightUnitor_inv_naturality, Iso.inv_hom_id_app_assoc]

/-- Compatibility of tensor relative half-braidings under `congrNatIsoFunctor`. -/
theorem congrNatIsoFunctor_μ_comm (X Y : F.RelativeCenter) (U : C) :
    (((tensorHalfBraiding X Y).congrNatIso α).β U).hom =
      ((tensorHalfBraiding ((congrNatIsoFunctor α).obj X)
          ((congrNatIsoFunctor α).obj Y)).β U).hom := by
  simp only [congrNatIsoFunctor_obj_fst, congrNatIsoFunctor_obj_snd,
    RelativeHalfBraiding.congrNatIso_β_hom, tensorHalfBraiding_β, Iso.trans_hom,
    whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom, MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight, Category.assoc]
  rw [associator_naturality_right_assoc]
  slice_rhs 4 5 =>
    rw [associator_inv_naturality_middle]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc (X.1 ◁ α.hom.app U), ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id_app, MonoidalCategory.whiskerLeft_id, id_whiskerRight, Category.id_comp,
    associator_naturality_left]

instance instMonoidalCongrNatIsoFunctor : (congrNatIsoFunctor α).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom :=
            { f := 𝟙 (𝟙_ D)
              comm := fun U ↦ by
                simp only [tensorUnit_fst, tensorUnit_snd, congrNatIsoFunctor_obj_fst,
                  congrNatIsoFunctor_obj_snd, id_whiskerRight, MonoidalCategory.whiskerLeft_id,
                  Category.id_comp, Category.comp_id, congrNatIsoFunctor_ε_comm α U] }
          inv :=
            { f := 𝟙 (𝟙_ D)
              comm := fun U ↦ by
                simp only [tensorUnit_fst, tensorUnit_snd, congrNatIsoFunctor_obj_fst,
                  congrNatIsoFunctor_obj_snd, id_whiskerRight, MonoidalCategory.whiskerLeft_id,
                  Category.id_comp, Category.comp_id, congrNatIsoFunctor_ε_comm α U] }
          hom_inv_id := Hom.ext (Category.comp_id _)
          inv_hom_id := Hom.ext (Category.comp_id _) }
      μIso := fun X Y ↦
        { hom :=
            { f := 𝟙 (X.1 ⊗ Y.1)
              comm := fun U ↦ by
                simp only [tensor_fst, tensor_snd, congrNatIsoFunctor_obj_fst,
                  congrNatIsoFunctor_obj_snd, id_whiskerRight, MonoidalCategory.whiskerLeft_id,
                  Category.id_comp, Category.comp_id, congrNatIsoFunctor_μ_comm α X Y U] }
          inv :=
            { f := 𝟙 (X.1 ⊗ Y.1)
              comm := fun U ↦ by
                simp only [tensor_fst, tensor_snd, congrNatIsoFunctor_obj_fst,
                  congrNatIsoFunctor_obj_snd, id_whiskerRight, MonoidalCategory.whiskerLeft_id,
                  Category.id_comp, Category.comp_id, congrNatIsoFunctor_μ_comm α X Y U] }
          hom_inv_id := Hom.ext (Category.comp_id _)
          inv_hom_id := Hom.ext (Category.comp_id _) }
      μIso_hom_natural_left := fun f X' ↦
        Hom.ext ((Category.comp_id (f.f ▷ X'.1)).trans (Category.id_comp _).symm)
      μIso_hom_natural_right := fun X' f ↦
        Hom.ext ((Category.comp_id (X'.1 ◁ f.f)).trans (Category.id_comp _).symm)
      associativity := fun X Y Z ↦
        Hom.ext
          (by change (𝟙 (X.1 ⊗ Y.1) ▷ Z.1) ≫ 𝟙 _ ≫ (α_ X.1 Y.1 Z.1).hom =
                (α_ X.1 Y.1 Z.1).hom ≫ (X.1 ◁ 𝟙 (Y.1 ⊗ Z.1)) ≫ 𝟙 _; simp)
      left_unitality := fun X ↦
        Hom.ext (by change (λ_ X.1).hom = (𝟙 (𝟙_ D) ▷ X.1) ≫ 𝟙 _ ≫ (λ_ X.1).hom; simp)
      right_unitality := fun X ↦
        Hom.ext (by change (ρ_ X.1).hom = (X.1 ◁ 𝟙 (𝟙_ D)) ≫ 𝟙 _ ≫ (ρ_ X.1).hom; simp) }

@[simp] theorem congrNatIsoFunctor_ε_f : (ε (congrNatIsoFunctor α)).f = 𝟙 (𝟙_ D) := rfl
@[simp] theorem congrNatIsoFunctor_η_f : (η (congrNatIsoFunctor α)).f = 𝟙 (𝟙_ D) := rfl
@[simp] theorem congrNatIsoFunctor_μ_f (X Y : F.RelativeCenter) :
    (μ (congrNatIsoFunctor α) X Y).f = 𝟙 (X.1 ⊗ Y.1) := rfl
@[simp] theorem congrNatIsoFunctor_δ_f (X Y : F.RelativeCenter) :
    (δ (congrNatIsoFunctor α) X Y).f = 𝟙 (X.1 ⊗ Y.1) := rfl

/-- A monoidal natural isomorphism `α : F ≅ F'` induces a monoidal equivalence
`F.RelativeCenter ≌ F'.RelativeCenter`. -/
@[expose]
def congrNatIso : F.RelativeCenter ≌ F'.RelativeCenter where
  functor := congrNatIsoFunctor α
  inverse := congrNatIsoFunctor α.symm
  unitIso :=
    NatIso.ofComponents
      (fun X ↦
        { hom := { f := 𝟙 X.1, comm := fun _ ↦ by simp }
          inv := { f := 𝟙 X.1, comm := fun _ ↦ by simp }
          hom_inv_id := Hom.ext (Category.comp_id _)
          inv_hom_id := Hom.ext (Category.comp_id _) })
      (fun f ↦ Hom.ext ((Category.comp_id f.f).trans (Category.id_comp f.f).symm))
  counitIso :=
    NatIso.ofComponents
      (fun X ↦
        { hom := { f := 𝟙 X.1, comm := fun _ ↦ by simp }
          inv := { f := 𝟙 X.1, comm := fun _ ↦ by simp }
          hom_inv_id := Hom.ext (Category.comp_id _)
          inv_hom_id := Hom.ext (Category.comp_id _) })
      (fun f ↦ Hom.ext ((Category.comp_id f.f).trans (Category.id_comp f.f).symm))
  functor_unitIso_comp _ := Hom.ext (Category.comp_id _)

@[simp] theorem congrNatIso_functor : (congrNatIso α).functor = congrNatIsoFunctor α := rfl
@[simp] theorem congrNatIso_inverse : (congrNatIso α).inverse = congrNatIsoFunctor α.symm := rfl
@[simp] theorem congrNatIso_unit_app_f (X : F.RelativeCenter) :
    ((congrNatIso α).unit.app X).f = 𝟙 X.1 := rfl
@[simp] theorem congrNatIso_counit_app_f (X : F'.RelativeCenter) :
    ((congrNatIso α).counit.app X).f = 𝟙 X.1 := rfl

instance instMonoidalCongrNatIsoEquivFunctor : (congrNatIso α).functor.Monoidal :=
  inferInstanceAs (congrNatIsoFunctor α).Monoidal

instance instMonoidalCongrNatIsoEquivInverse : (congrNatIso α).inverse.Monoidal :=
  inferInstanceAs (congrNatIsoFunctor α.symm).Monoidal

instance instIsMonoidalCongrNatIsoUnit : NatTrans.IsMonoidal (congrNatIso α).unit where
  unit := Hom.ext rfl
  tensor X Y := Hom.ext <| by
    change 𝟙 (X.1 ⊗ Y.1) ≫ 𝟙 (X.1 ⊗ Y.1) =
      (𝟙 X.1 ⊗ₘ 𝟙 Y.1) ≫ (𝟙 (X.1 ⊗ Y.1) ≫ 𝟙 (X.1 ⊗ Y.1))
    simp

instance instIsMonoidalCongrNatIso : (congrNatIso α).IsMonoidal :=
  Equivalence.isMonoidal_of_isMonoidal_unit (congrNatIso α)

/-- `congrNatIso α` commutes strictly with the forgetful functors to `D`. -/
@[expose, simps!]
def congrNatIsoForgetIso : (congrNatIso α).functor ⋙ forget F' ≅ forget F :=
  Iso.refl _

instance instIsMonoidalCongrNatIsoForgetIsoHom :
    NatTrans.IsMonoidal (congrNatIsoForgetIso α).hom where
  unit := by change (𝟙 (𝟙_ D) ≫ 𝟙 (𝟙_ D)) ≫ 𝟙 (𝟙_ D) = 𝟙 (𝟙_ D); simp
  tensor X Y := by
    change (𝟙 (X.1 ⊗ Y.1) ≫ 𝟙 (X.1 ⊗ Y.1)) ≫ 𝟙 (X.1 ⊗ Y.1) =
      (𝟙 X.1 ⊗ₘ 𝟙 Y.1) ≫ 𝟙 (X.1 ⊗ Y.1)
    simp

instance instAdditiveCongrNatIsoFunctor [Preadditive D] [MonoidalPreadditive D] :
    (congrNatIsoFunctor α).Additive where

instance instLinearCongrNatIsoFunctor [Preadditive D] [MonoidalPreadditive D]
    {R : Type*} [Semiring R] [CategoryTheory.Linear R D] [MonoidalLinear R D] :
    (congrNatIsoFunctor α).Linear R where

end CongrNatIso

end RelativeCenter

end CategoryTheory.Functor

end
