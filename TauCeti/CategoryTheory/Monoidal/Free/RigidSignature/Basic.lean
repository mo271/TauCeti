/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# The free rigid monoidal category on a rigid signature

A *rigid signature* (or *autonomous signature*) consists of a type of generating objects and a type
of generating morphisms (*coupons*), each coupon having a source and a target which are formal
rigid object expressions (`TauCeti.RigidObject`) in the generating objects. Because `RigidObject`
contains the formal unit, tensor product, and both formal right and left duals, a coupon keeps its
individual port structure rather than collapsing a composite boundary into a single atom, may be
nullary on either side, and may attach to ports at arbitrary integer dual levels. Any monoidal
`TensorSignature` embeds as a rigid signature with level-zero ports via
`TensorSignature.toRigidSignature`.

The free rigid monoidal category `RigidSignature.FreeRigid S` on a signature `S` has formal rigid
objects as its objects. Its morphisms are formal composites, tensor products, and whiskerings of
identities, associators, unitors, right and left coevaluations and evaluations, and coupons, modulo
the monoidal-category axioms and the four snake (zigzag) equations for the chosen right and left
duals; neither mixed-dual equality on raw objects, nor any pivotal identification `X ≅ Xᘁᘁ`, nor
any extra relation between coupons is imposed. The quotient and universal-lift architecture adapts
`TauCeti.TensorSignature.FreeMonoidal` and `Mathlib/CategoryTheory/Monoidal/Free/Basic.lean`
(Markus Himmel) to include formal dual objects, evaluations, coevaluations, and snake relations.

## Main definitions and results

* `TauCeti.RigidObject.projectObj`: interpret formal rigid objects in any rigid monoidal category,
  using the duals chosen by its `RigidCategory` structure and extending
  `FreeMonoidalCategory.projectObj` along `FreeMonoidalCategory.toRigidObject`.
* `TauCeti.RigidSignature` and `TauCeti.TensorSignature.toRigidSignature`: rigid signatures and the
  inclusion of monoidal tensor signatures.
* `TauCeti.RigidSignature.FreeRigid S`: the free rigid monoidal category on `S`, equipped with
  `MonoidalCategory` and `RigidCategory` instances, generators `FreeRigid.of` and
  `FreeRigid.coupon`, morphism induction `FreeRigid.Hom.inductionOn`, and the strong monoidal
  inclusion `FreeRigid.ofFreeMonoidal` from `TensorSignature.FreeMonoidal`.
* `FreeRigid.lift fo fc`: the strong monoidal functor into an arbitrary (not necessarily strict)
  rigid monoidal category determined by object images `fo` and coupon images `fc`, with computation
  rules for coupons, structural morphisms, evaluations, coevaluations, and the dual comparisons
  `Functor.mapRightDualIso` and `Functor.mapLeftDualIso`.
* `FreeRigid.monoidalNatIso` and `FreeRigid.natTrans_ext`: two strong monoidal functors out of
  `S.FreeRigid` that agree up to objectwise isomorphisms on the generating objects, compatibly with
  every coupon, are connected by a unique monoidal natural isomorphism extending those generator
  isomorphisms.

## References

* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, unpublished manuscript (1988), §2.
* A. Joyal and R. Street, *The geometry of tensor calculus, I*, Adv. Math. 88 (1991), 55–112.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813, Springer (2011), §4.1.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti

namespace RigidObject

section ProjectObj

variable {α : Type u} {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D]

/-- Interpret a formal rigid object in a rigid monoidal category `D`, sending generating objects by
`fo`, the formal unit and tensor to those of `D`, and formal right and left duals to the duals
chosen by the `RigidCategory` structure on `D`. -/
@[expose] def projectObj (fo : α → D) : RigidObject α → D
  | .of a => fo a
  | .unit => 𝟙_ D
  | .tensor X Y => projectObj fo X ⊗ projectObj fo Y
  | .rightDual X => (RightRigidCategory.rightDual (projectObj fo X)).rightDual
  | .leftDual X => (LeftRigidCategory.leftDual (projectObj fo X)).leftDual

@[simp]
theorem projectObj_of (fo : α → D) (a : α) : projectObj fo (.of a) = fo a := rfl

@[simp]
theorem projectObj_unit (fo : α → D) : projectObj fo .unit = 𝟙_ D := rfl

@[simp]
theorem projectObj_tensor (fo : α → D) (X Y : RigidObject α) :
    projectObj fo (X.tensor Y) = projectObj fo X ⊗ projectObj fo Y := rfl

@[simp]
theorem projectObj_rightDual (fo : α → D) (X : RigidObject α) :
    projectObj fo X.rightDual = (RightRigidCategory.rightDual (projectObj fo X)).rightDual := rfl

@[simp]
theorem projectObj_leftDual (fo : α → D) (X : RigidObject α) :
    projectObj fo X.leftDual = (LeftRigidCategory.leftDual (projectObj fo X)).leftDual := rfl

/-- Interpreting a monoidal object expression after including it into `RigidObject` agrees with
Mathlib's `FreeMonoidalCategory.projectObj`. -/
@[simp]
theorem projectObj_toRigidObject (fo : α → D) (X : FreeMonoidalCategory α) :
    projectObj fo X.toRigidObject = FreeMonoidalCategory.projectObj fo X := by
  induction X <;> simp_all [FreeMonoidalCategory.projectObj]

end ProjectObj

end RigidObject

/-- A rigid (autonomous) signature: a type `Obj` of generating objects and a type `Coupon` of
generating morphisms, each coupon having a source and a target formal rigid object expression in
the generating objects. -/
structure RigidSignature where
  /-- The generating objects. -/
  Obj : Type u
  /-- The generating morphisms (coupons). -/
  Coupon : Type v
  /-- The source formal rigid object of a coupon. -/
  src : Coupon → RigidObject Obj
  /-- The target formal rigid object of a coupon. -/
  tgt : Coupon → RigidObject Obj

namespace TensorSignature

/-- View a monoidal tensor signature as a rigid signature by including its source and target tensor
words into `RigidObject`. Every port keeps its arity and sits at integer dual level zero. -/
@[expose]
def toRigidSignature (S : TensorSignature.{u, v}) : RigidSignature.{u, v} where
  Obj := S.Obj
  Coupon := S.Coupon
  src g := (S.src g).toRigidObject
  tgt g := (S.tgt g).toRigidObject

@[simp]
theorem toRigidSignature_obj (S : TensorSignature.{u, v}) :
    S.toRigidSignature.Obj = S.Obj := rfl

@[simp]
theorem toRigidSignature_coupon (S : TensorSignature.{u, v}) :
    S.toRigidSignature.Coupon = S.Coupon := rfl

@[simp]
theorem toRigidSignature_src (S : TensorSignature.{u, v}) (g : S.Coupon) :
    S.toRigidSignature.src g = (S.src g).toRigidObject := rfl

@[simp]
theorem toRigidSignature_tgt (S : TensorSignature.{u, v}) (g : S.Coupon) :
    S.toRigidSignature.tgt g = (S.tgt g).toRigidObject := rfl

end TensorSignature

namespace RigidSignature

variable (S : RigidSignature.{u, v})

/-- The free rigid (autonomous) monoidal category on a rigid signature `S`. Its objects are formal
rigid object expressions in `S.Obj`. -/
@[ext]
structure FreeRigid where
  /-- The formal rigid object expression underlying an object of `S.FreeRigid`. -/
  as : RigidObject S.Obj

namespace FreeRigid

variable {S}

/-- The object of `S.FreeRigid` given by a single generating object. -/
@[expose] def of (a : S.Obj) : S.FreeRigid := ⟨.of a⟩

/-- Formal composites, tensor products, and whiskerings of identities, associators, unitors,
chosen right and left coevaluations and evaluations, and coupons. -/
inductive Hom : RigidObject S.Obj → RigidObject S.Obj → Type (max u v)
  | id (X : RigidObject S.Obj) : Hom X X
  | α_hom (X Y Z : RigidObject S.Obj) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : RigidObject S.Obj) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X : RigidObject S.Obj) : Hom (RigidObject.unit.tensor X) X
  | l_inv (X : RigidObject S.Obj) : Hom X (RigidObject.unit.tensor X)
  | ρ_hom (X : RigidObject S.Obj) : Hom (X.tensor RigidObject.unit) X
  | ρ_inv (X : RigidObject S.Obj) : Hom X (X.tensor RigidObject.unit)
  | η_right (X : RigidObject S.Obj) : Hom .unit (X.tensor X.rightDual)
  | ε_right (X : RigidObject S.Obj) : Hom (X.rightDual.tensor X) .unit
  | η_left (X : RigidObject S.Obj) : Hom .unit (X.leftDual.tensor X)
  | ε_left (X : RigidObject S.Obj) : Hom (X.tensor X.leftDual) .unit
  | coupon (g : S.Coupon) : Hom (S.src g) (S.tgt g)
  | comp {X Y Z : RigidObject S.Obj} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : RigidObject S.Obj) {Y₁ Y₂ : RigidObject S.Obj} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂ : RigidObject S.Obj} (f : Hom X₁ X₂) (Y : RigidObject S.Obj) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z : RigidObject S.Obj} (f : Hom W Y) (g : Hom X Z) :
      Hom (W.tensor X) (Y.tensor Z)

/-- The congruence on formal morphisms generated by the monoidal-category axioms and the four snake
(zigzag) identities for `(X, X.rightDual)` and `(X.leftDual, X)`. No extra equation on coupons and
no pivotal identification are imposed. -/
inductive HomEquiv : ∀ {X Y : RigidObject S.Obj}, Hom X Y → Hom X Y → Prop
  | refl {X Y} (f : Hom X Y) : HomEquiv f f
  | symm {X Y} (f g : Hom X Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : Hom X Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : Hom X Y} {g g' : Hom Y Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Hom Y Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Hom Y Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : Hom W X} {g g' : Hom Y Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : Hom X₁ Y₁) (g : Hom X₂ Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : Hom X Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : Hom X Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V} (f : Hom X U) (g : Hom U V) (h : Hom V Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂)
      (g₁ : Hom Y₁ Z₁) (g₂ : Hom Y₂ Z₂) :
      HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂)
      (f₃ : Hom X₃ Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : Hom X Y) :
      HomEquiv ((f.whiskerRight .unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : Hom X Y) :
      HomEquiv ((f.whiskerLeft .unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X .unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)
  | coevaluation_evaluation_right (X : RigidObject S.Obj) :
      HomEquiv
        (((Hom.η_right X).whiskerLeft X.rightDual).comp
          ((Hom.α_inv X.rightDual X X.rightDual).comp
            ((Hom.ε_right X).whiskerRight X.rightDual)))
        ((Hom.ρ_hom X.rightDual).comp (Hom.l_inv X.rightDual))
  | evaluation_coevaluation_right (X : RigidObject S.Obj) :
      HomEquiv
        (((Hom.η_right X).whiskerRight X).comp
          ((Hom.α_hom X X.rightDual X).comp ((Hom.ε_right X).whiskerLeft X)))
        ((Hom.l_hom X).comp (Hom.ρ_inv X))
  | coevaluation_evaluation_left (X : RigidObject S.Obj) :
      HomEquiv
        (((Hom.η_left X).whiskerLeft X).comp
          ((Hom.α_inv X X.leftDual X).comp ((Hom.ε_left X).whiskerRight X)))
        ((Hom.ρ_hom X).comp (Hom.l_inv X))
  | evaluation_coevaluation_left (X : RigidObject S.Obj) :
      HomEquiv
        (((Hom.η_left X).whiskerRight X.leftDual).comp
          ((Hom.α_hom X.leftDual X X.leftDual).comp ((Hom.ε_left X).whiskerLeft X.leftDual)))
        ((Hom.l_hom X.leftDual).comp (Hom.ρ_inv X.leftDual))

/-- Formal rigid morphisms modulo the monoidal and snake axioms. -/
instance setoidHom (X Y : RigidObject S.Obj) : Setoid (Hom X Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

open HomEquiv

instance : Category.{max u v} S.FreeRigid where
  Hom X Y := Quotient (setoidHom X.as Y.as)
  id X := ⟦Hom.id X.as⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (assoc f g h)

instance : MonoidalCategory S.FreeRigid where
  tensorObj X Y := ⟨X.as.tensor Y.as⟩
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f :=
    Quot.map (fun f ↦ Hom.whiskerLeft X.as f) (fun f f' ↦ .whiskerLeft _ f f') f
  whiskerRight f Y :=
    Quot.map (fun f ↦ Hom.whiskerRight f Y.as) (fun f f' ↦ .whiskerRight f f' _) f
  tensorHom_def := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩
    exact Quotient.sound (tensorHom_def _ _)
  id_tensorHom_id _ _ := Quot.sound id_tensorHom_id
  tensorHom_comp_tensorHom := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X.as Y.as)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X.as Y.as)
  tensorUnit := ⟨.unit⟩
  associator X Y Z :=
    ⟨⟦Hom.α_hom X.as Y.as Z.as⟧, ⟦Hom.α_inv X.as Y.as Z.as⟧, Quotient.sound α_hom_inv,
      Quotient.sound α_inv_hom⟩
  associator_naturality := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact Quotient.sound (associator_naturality _ _ _)
  leftUnitor X :=
    ⟨⟦Hom.l_hom X.as⟧, ⟦Hom.l_inv X.as⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  leftUnitor_naturality := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X.as⟧, ⟦Hom.ρ_inv X.as⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound (ρ_naturality _)
  pentagon _ _ _ _ := Quotient.sound pentagon
  triangle _ _ := Quotient.sound triangle

instance : RightRigidCategory S.FreeRigid where
  rightDual X :=
    { rightDual := ⟨X.as.rightDual⟩
      exact :=
        { coevaluation' := ⟦Hom.η_right X.as⟧
          evaluation' := ⟦Hom.ε_right X.as⟧
          coevaluation_evaluation' := Quotient.sound (coevaluation_evaluation_right X.as)
          evaluation_coevaluation' := Quotient.sound (evaluation_coevaluation_right X.as) } }

instance : LeftRigidCategory S.FreeRigid where
  leftDual X :=
    { leftDual := ⟨X.as.leftDual⟩
      exact :=
        { coevaluation' := ⟦Hom.η_left X.as⟧
          evaluation' := ⟦Hom.ε_left X.as⟧
          coevaluation_evaluation' := Quotient.sound (coevaluation_evaluation_left X.as)
          evaluation_coevaluation' := Quotient.sound (evaluation_coevaluation_left X.as) } }

instance : RigidCategory S.FreeRigid where

/-- The morphism of `S.FreeRigid` represented by a formal morphism. -/
abbrev homMk {X Y : S.FreeRigid} (f : Hom X.as Y.as) : X ⟶ Y := ⟦f⟧

/-- The generating morphism of `S.FreeRigid` associated to a coupon `g`. -/
@[expose] def coupon (g : S.Coupon) : (⟨S.src g⟩ : S.FreeRigid) ⟶ ⟨S.tgt g⟩ :=
  homMk (Hom.coupon g)

@[simp]
theorem homMk_id (X : S.FreeRigid) : homMk (Hom.id X.as) = 𝟙 X := rfl

@[simp]
theorem homMk_comp {X Y Z : S.FreeRigid} (f : Hom X.as Y.as) (g : Hom Y.as Z.as) :
    homMk (Y := Z) (f.comp g) = homMk f ≫ homMk g := rfl

@[simp]
theorem homMk_tensor {X₁ Y₁ X₂ Y₂ : S.FreeRigid} (f : Hom X₁.as Y₁.as) (g : Hom X₂.as Y₂.as) :
    homMk (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (f.tensor g) = homMk f ⊗ₘ homMk g := rfl

@[simp]
theorem homMk_whiskerLeft (X : S.FreeRigid) {Y₁ Y₂ : S.FreeRigid} (f : Hom Y₁.as Y₂.as) :
    homMk (X := X ⊗ Y₁) (Y := X ⊗ Y₂) (f.whiskerLeft X.as) = X ◁ homMk f := rfl

@[simp]
theorem homMk_whiskerRight {X₁ X₂ : S.FreeRigid} (f : Hom X₁.as X₂.as) (Y : S.FreeRigid) :
    homMk (X := X₁ ⊗ Y) (Y := X₂ ⊗ Y) (f.whiskerRight Y.as) = homMk f ▷ Y := rfl

@[simp]
theorem homMk_α_hom (X Y Z : S.FreeRigid) :
    homMk (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (Hom.α_hom X.as Y.as Z.as) = (α_ X Y Z).hom := rfl

@[simp]
theorem homMk_α_inv (X Y Z : S.FreeRigid) :
    homMk (X := X ⊗ (Y ⊗ Z)) (Y := (X ⊗ Y) ⊗ Z) (Hom.α_inv X.as Y.as Z.as) = (α_ X Y Z).inv := rfl

@[simp]
theorem homMk_l_hom (X : S.FreeRigid) :
    homMk (X := 𝟙_ _ ⊗ X) (Hom.l_hom X.as) = (λ_ X).hom := rfl

@[simp]
theorem homMk_l_inv (X : S.FreeRigid) :
    homMk (Y := 𝟙_ _ ⊗ X) (Hom.l_inv X.as) = (λ_ X).inv := rfl

@[simp]
theorem homMk_ρ_hom (X : S.FreeRigid) :
    homMk (X := X ⊗ 𝟙_ _) (Hom.ρ_hom X.as) = (ρ_ X).hom := rfl

@[simp]
theorem homMk_ρ_inv (X : S.FreeRigid) :
    homMk (Y := X ⊗ 𝟙_ _) (Hom.ρ_inv X.as) = (ρ_ X).inv := rfl

@[simp]
theorem homMk_η_right (X : S.FreeRigid) :
    homMk (X := 𝟙_ _) (Y := X ⊗ Xᘁ) (Hom.η_right X.as) = η_ X Xᘁ := rfl

@[simp]
theorem homMk_ε_right (X : S.FreeRigid) :
    homMk (X := Xᘁ ⊗ X) (Y := 𝟙_ _) (Hom.ε_right X.as) = ε_ X Xᘁ := rfl

@[simp]
theorem homMk_η_left (X : S.FreeRigid) :
    homMk (X := 𝟙_ _) (Y := (ᘁX) ⊗ X) (Hom.η_left X.as) = η_ (ᘁX) X := rfl

@[simp]
theorem homMk_ε_left (X : S.FreeRigid) :
    homMk (X := X ⊗ (ᘁX)) (Y := 𝟙_ _) (Hom.ε_left X.as) = ε_ (ᘁX) X := rfl

@[simp]
theorem homMk_coupon (g : S.Coupon) :
    homMk (X := ⟨S.src g⟩) (Y := ⟨S.tgt g⟩) (Hom.coupon g) = coupon g := rfl

/-- Induction principle for morphisms of `S.FreeRigid`: a property of morphisms holding for
identities, associators, unitors, chosen right and left coevaluations and evaluations, and coupons,
and closed under composition and whiskering on both sides, holds for every morphism. -/
theorem Hom.inductionOn {motive : {X Y : S.FreeRigid} → (X ⟶ Y) → Prop} {X Y : S.FreeRigid}
    (t : X ⟶ Y)
    (id : (X : S.FreeRigid) → motive (𝟙 X))
    (α_hom : (X Y Z : S.FreeRigid) → motive (α_ X Y Z).hom)
    (α_inv : (X Y Z : S.FreeRigid) → motive (α_ X Y Z).inv)
    (l_hom : (X : S.FreeRigid) → motive (λ_ X).hom)
    (l_inv : (X : S.FreeRigid) → motive (λ_ X).inv)
    (ρ_hom : (X : S.FreeRigid) → motive (ρ_ X).hom)
    (ρ_inv : (X : S.FreeRigid) → motive (ρ_ X).inv)
    (η_right : (X : S.FreeRigid) → motive (η_ X Xᘁ))
    (ε_right : (X : S.FreeRigid) → motive (ε_ X Xᘁ))
    (η_left : (X : S.FreeRigid) → motive (η_ (ᘁX) X))
    (ε_left : (X : S.FreeRigid) → motive (ε_ (ᘁX) X))
    (coupon : (g : S.Coupon) → motive (FreeRigid.coupon g))
    (comp : {X Y Z : S.FreeRigid} → (f : X ⟶ Y) → (g : Y ⟶ Z) → motive f → motive g →
      motive (f ≫ g))
    (whiskerLeft : (X : S.FreeRigid) → {Y Z : S.FreeRigid} → (f : Y ⟶ Z) → motive f →
      motive (X ◁ f))
    (whiskerRight : {X Y : S.FreeRigid} → (f : X ⟶ Y) → (Z : S.FreeRigid) → motive f →
      motive (f ▷ Z)) :
    motive t := by
  suffices H : ∀ {X Y : RigidObject S.Obj} (f : Hom X Y),
      motive (homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) by
    induction t using Quotient.inductionOn with | _ f
    exact H f
  intro X Y f
  induction f with
  | id X => exact id ⟨X⟩
  | α_hom X Y Z => exact α_hom ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact α_inv ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact l_hom ⟨X⟩
  | l_inv X => exact l_inv ⟨X⟩
  | ρ_hom X => exact ρ_hom ⟨X⟩
  | ρ_inv X => exact ρ_inv ⟨X⟩
  | η_right X => exact η_right ⟨X⟩
  | ε_right X => exact ε_right ⟨X⟩
  | η_left X => exact η_left ⟨X⟩
  | ε_left X => exact ε_left ⟨X⟩
  | coupon g => exact coupon g
  | comp f g hf hg => exact comp _ _ hf hg
  | whiskerLeft X f hf => exact whiskerLeft ⟨X⟩ _ hf
  | whiskerRight f X hf => exact whiskerRight _ ⟨X⟩ hf
  | @tensor W X Y Z f g hf hg =>
    have h : (homMk (f.tensor g) : (⟨W.tensor X⟩ : S.FreeRigid) ⟶ ⟨Y.tensor Z⟩) =
        homMk (X := ⟨W⟩) (Y := ⟨Y⟩) f ▷ (⟨X⟩ : S.FreeRigid) ≫
          (⟨Y⟩ : S.FreeRigid) ◁ homMk (X := ⟨X⟩) (Y := ⟨Z⟩) g :=
      Quotient.sound (HomEquiv.tensorHom_def f g)
    rw [h]
    exact comp _ _ (whiskerRight _ _ hf) (whiskerLeft _ _ hg)

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D]
  (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon, RigidObject.projectObj fo (S.src g) ⟶ RigidObject.projectObj fo (S.tgt g))

/-- Interpret a formal rigid morphism in `D`, given interpretations `fo` of the generating objects
and `fc` of the coupons. -/
private def liftMapAux :
    ∀ {X Y : RigidObject S.Obj},
      Hom X Y → (RigidObject.projectObj fo X ⟶ RigidObject.projectObj fo Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, Hom.α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, Hom.l_hom _ => (λ_ _).hom
  | _, _, Hom.l_inv _ => (λ_ _).inv
  | _, _, Hom.ρ_hom _ => (ρ_ _).hom
  | _, _, Hom.ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.η_right X =>
      @ExactPairing.coevaluation D _ _ (RigidObject.projectObj fo X) _
        (RightRigidCategory.rightDual (RigidObject.projectObj fo X)).exact
  | _, _, Hom.ε_right X =>
      @ExactPairing.evaluation D _ _ (RigidObject.projectObj fo X) _
        (RightRigidCategory.rightDual (RigidObject.projectObj fo X)).exact
  | _, _, Hom.η_left X =>
      @ExactPairing.coevaluation D _ _ _ (RigidObject.projectObj fo X)
        (LeftRigidCategory.leftDual (RigidObject.projectObj fo X)).exact
  | _, _, Hom.ε_left X =>
      @ExactPairing.evaluation D _ _ _ (RigidObject.projectObj fo X)
        (LeftRigidCategory.leftDual (RigidObject.projectObj fo X)).exact
  | _, _, Hom.coupon g => fc g
  | _, _, Hom.comp f g => liftMapAux f ≫ liftMapAux g
  | _, _, Hom.whiskerLeft X p => RigidObject.projectObj fo X ◁ liftMapAux p
  | _, _, Hom.whiskerRight p X => liftMapAux p ▷ RigidObject.projectObj fo X
  | _, _, Hom.tensor f g => liftMapAux f ⊗ₘ liftMapAux g

/-- The interpretation of formal rigid morphisms respects all monoidal and snake axioms. -/
private theorem liftMapAux_sound {X Y : RigidObject S.Obj} {f g : Hom X Y} (h : HomEquiv f g) :
    liftMapAux fo fc f = liftMapAux fo fc g := by
  induction h with
  | refl => rfl
  | symm _ _ _ hfg => exact hfg.symm
  | trans _ _ hfg hgh => exact hfg.trans hgh
  | comp _ _ hf hg => simp only [liftMapAux, hf, hg]
  | whiskerLeft _ _ _ _ hf => dsimp only [liftMapAux]; rw [hf]
  | whiskerRight _ _ _ _ hf => dsimp only [liftMapAux]; rw [hf]
  | tensor _ _ hf hg => dsimp only [liftMapAux]; rw [hf, hg]
  | tensorHom_def => exact MonoidalCategory.tensorHom_def _ _
  | comp_id => exact Category.comp_id _
  | id_comp => exact Category.id_comp _
  | assoc => exact Category.assoc _ _ _
  | id_tensorHom_id => exact MonoidalCategory.id_tensorHom_id _ _
  | tensorHom_comp_tensorHom => exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  | whiskerLeft_id => exact MonoidalCategory.whiskerLeft_id _ _
  | id_whiskerRight => exact MonoidalCategory.id_whiskerRight _ _
  | α_hom_inv => exact Iso.hom_inv_id _
  | α_inv_hom => exact Iso.inv_hom_id _
  | associator_naturality => exact MonoidalCategory.associator_naturality _ _ _
  | ρ_hom_inv => exact Iso.hom_inv_id _
  | ρ_inv_hom => exact Iso.inv_hom_id _
  | ρ_naturality => exact MonoidalCategory.rightUnitor_naturality _
  | l_hom_inv => exact Iso.hom_inv_id _
  | l_inv_hom => exact Iso.inv_hom_id _
  | l_naturality => exact MonoidalCategory.leftUnitor_naturality _
  | pentagon => exact MonoidalCategory.pentagon _ _ _ _
  | triangle => exact MonoidalCategory.triangle _ _
  | coevaluation_evaluation_right X =>
    exact @ExactPairing.coevaluation_evaluation D _ _ (RigidObject.projectObj fo X) _
      (RightRigidCategory.rightDual (RigidObject.projectObj fo X)).exact
  | evaluation_coevaluation_right X =>
    exact @ExactPairing.evaluation_coevaluation D _ _ (RigidObject.projectObj fo X) _
      (RightRigidCategory.rightDual (RigidObject.projectObj fo X)).exact
  | coevaluation_evaluation_left X =>
    exact @ExactPairing.coevaluation_evaluation D _ _ _ (RigidObject.projectObj fo X)
      (LeftRigidCategory.leftDual (RigidObject.projectObj fo X)).exact
  | evaluation_coevaluation_left X =>
    exact @ExactPairing.evaluation_coevaluation D _ _ _ (RigidObject.projectObj fo X)
      (LeftRigidCategory.leftDual (RigidObject.projectObj fo X)).exact

/-- The interpretation of morphisms of `S.FreeRigid` determined by `fo` and `fc`. -/
def liftMap {X Y : S.FreeRigid} (f : X ⟶ Y) :
    RigidObject.projectObj fo X.as ⟶ RigidObject.projectObj fo Y.as :=
  Quotient.lift (liftMapAux fo fc) (fun _ _ h ↦ liftMapAux_sound fo fc h) f

theorem liftMap_id (X : S.FreeRigid) : liftMap fo fc (𝟙 X) = 𝟙 _ :=
  (rfl)

theorem liftMap_comp {X Y Z : S.FreeRigid} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftMap fo fc (f ≫ g) = liftMap fo fc f ≫ liftMap fo fc g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

/-- The strong monoidal functor out of `S.FreeRigid` into an arbitrary rigid monoidal category `D`
determined by object images `fo` and coupon images `fc`. Its unit comparison, tensorators, and
chosen-dual comparisons are identities. -/
@[expose] def lift : S.FreeRigid ⥤ D where
  obj X := RigidObject.projectObj fo X.as
  map := liftMap fo fc
  map_id := liftMap_id fo fc
  map_comp := liftMap_comp fo fc

@[simp]
theorem lift_obj_of (a : S.Obj) : (lift fo fc).obj (of a) = fo a := rfl

@[simp]
theorem lift_obj_tensor (X Y : S.FreeRigid) :
    (lift fo fc).obj (X ⊗ Y) = (lift fo fc).obj X ⊗ (lift fo fc).obj Y := rfl

@[simp]
theorem lift_obj_tensorUnit : (lift fo fc).obj (𝟙_ S.FreeRigid) = 𝟙_ D := rfl

theorem lift_obj_rightDual (X : S.FreeRigid) :
    (lift fo fc).obj Xᘁ = ((lift fo fc).obj X)ᘁ := rfl

theorem lift_obj_leftDual (X : S.FreeRigid) :
    (lift fo fc).obj (ᘁX) = ᘁ((lift fo fc).obj X) := rfl

@[simp]
theorem lift_map_coupon (g : S.Coupon) : (lift fo fc).map (coupon g) = fc g := by rfl

@[simp]
theorem lift_map_whiskerLeft (X : S.FreeRigid) {Y₁ Y₂ : S.FreeRigid} (f : Y₁ ⟶ Y₂) :
    (lift fo fc).map (X ◁ f) = (lift fo fc).obj X ◁ (lift fo fc).map f := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem lift_map_whiskerRight {X₁ X₂ : S.FreeRigid} (f : X₁ ⟶ X₂) (Y : S.FreeRigid) :
    (lift fo fc).map (f ▷ Y) = (lift fo fc).map f ▷ (lift fo fc).obj Y := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem lift_map_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeRigid} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (lift fo fc).map (f ⊗ₘ g) = (lift fo fc).map f ⊗ₘ (lift fo fc).map g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

@[simp]
theorem lift_map_associator_hom (X Y Z : S.FreeRigid) :
    (lift fo fc).map (α_ X Y Z).hom =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).hom := by rfl

@[simp]
theorem lift_map_associator_inv (X Y Z : S.FreeRigid) :
    (lift fo fc).map (α_ X Y Z).inv =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).inv := by rfl

/- As in `FreeMonoidal`, the unitor equations are not marked `@[simp]` because
`Functor.LaxMonoidal.left_unitality` and `right_unitality` simplify in the opposite direction. -/
theorem lift_map_leftUnitor_hom (X : S.FreeRigid) :
    (lift fo fc).map (λ_ X).hom = (λ_ ((lift fo fc).obj X)).hom := by rfl

theorem lift_map_leftUnitor_inv (X : S.FreeRigid) :
    (lift fo fc).map (λ_ X).inv = (λ_ ((lift fo fc).obj X)).inv := by rfl

theorem lift_map_rightUnitor_hom (X : S.FreeRigid) :
    (lift fo fc).map (ρ_ X).hom = (ρ_ ((lift fo fc).obj X)).hom := by rfl

theorem lift_map_rightUnitor_inv (X : S.FreeRigid) :
    (lift fo fc).map (ρ_ X).inv = (ρ_ ((lift fo fc).obj X)).inv := by rfl

@[simp]
theorem lift_map_coevaluation_right (X : S.FreeRigid) :
    (lift fo fc).map (η_ X Xᘁ) = η_ ((lift fo fc).obj X) ((lift fo fc).obj X)ᘁ := by rfl

@[simp]
theorem lift_map_evaluation_right (X : S.FreeRigid) :
    (lift fo fc).map (ε_ X Xᘁ) = ε_ ((lift fo fc).obj X) ((lift fo fc).obj X)ᘁ := by rfl

@[simp]
theorem lift_map_coevaluation_left (X : S.FreeRigid) :
    (lift fo fc).map (η_ (ᘁX) X) = η_ (ᘁ((lift fo fc).obj X)) ((lift fo fc).obj X) := by rfl

@[simp]
theorem lift_map_evaluation_left (X : S.FreeRigid) :
    (lift fo fc).map (ε_ (ᘁX) X) = ε_ (ᘁ((lift fo fc).obj X)) ((lift fo fc).obj X) := by rfl

instance : (lift fo fc).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      μIso_hom_natural_right := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      associativity := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      left_unitality := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_leftUnitor_hom]
      right_unitality := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_rightUnitor_hom] }

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc) = 𝟙 _ := rfl

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc) = 𝟙 _ := rfl

@[simp]
theorem lift_μ (X Y : S.FreeRigid) : Functor.LaxMonoidal.μ (lift fo fc) X Y = 𝟙 _ := rfl

@[simp]
theorem lift_δ (X Y : S.FreeRigid) : Functor.OplaxMonoidal.δ (lift fo fc) X Y = 𝟙 _ := rfl

/-- Because `lift fo fc` sends formal duals directly to the chosen duals of `D` with identity unit
and tensor comparisons, its right-dual comparison is the identity isomorphism. -/
@[simp]
theorem lift_mapRightDualIso (X : S.FreeRigid) :
    (lift fo fc).mapRightDualIso X = Iso.refl _ := by
  ext
  refine ExactPairing.rightHom_ext (X := (lift fo fc).obj X) ?_
  refine ((lift fo fc).mapRightDualIso_hom_whiskerRight_evaluation X).trans ?_
  dsimp only [Iso.refl_hom, lift_μ, lift_η, lift_obj_tensor, lift_obj_tensorUnit,
    lift_obj_rightDual]
  simp

/-- Because `lift fo fc` sends formal duals directly to the chosen duals of `D` with identity unit
and tensor comparisons, its left-dual comparison is the identity isomorphism. -/
@[simp]
theorem lift_mapLeftDualIso (X : S.FreeRigid) :
    (lift fo fc).mapLeftDualIso X = Iso.refl _ := by
  ext
  refine ExactPairing.leftDualHom_ext (Y := (lift fo fc).obj X) ?_
  refine ((lift fo fc).whiskerLeft_mapLeftDualIso_hom_evaluation X).trans ?_
  dsimp only [Iso.refl_hom, lift_μ, lift_η, lift_obj_tensor, lift_obj_tensorUnit,
    lift_obj_leftDual]
  simp

end Lift

section OfFreeMonoidal

open TensorSignature

/-- Interpreting a formal monoidal object in `T.toRigidSignature.FreeRigid` via `of` agrees with
including it via `FreeMonoidalCategory.toRigidObject`. -/
theorem projectObj_of_eq (T : TensorSignature.{u, v}) (X : FreeMonoidalCategory T.Obj) :
    FreeMonoidalCategory.projectObj (fun a : T.Obj ↦ of (S := T.toRigidSignature) a) X =
      ⟨X.toRigidObject⟩ := by
  induction X with
  | of a =>
    simp only [FreeMonoidalCategory.toRigidObject_of]
    rfl
  | unit =>
    rw [show (FreeMonoidalCategory.unit : FreeMonoidalCategory T.Obj) = 𝟙_ _ from rfl,
      FreeMonoidalCategory.toRigidObject_unit]
    rfl
  | tensor X Y ihX ihY =>
    exact (congrArg₂ (· ⊗ ·) ihX ihY).trans
      (congrArg FreeRigid.mk
        (FreeMonoidalCategory.toRigidObject_tensor (X := X) (Y := Y)).symm)

/-- The canonical strong monoidal functor including `T.FreeMonoidal` into
`T.toRigidSignature.FreeRigid`, obtained as the universal lift of the generating objects and
coupons. -/
@[expose]
def ofFreeMonoidal (T : TensorSignature.{u, v}) :
    T.FreeMonoidal ⥤ T.toRigidSignature.FreeRigid :=
  FreeMonoidal.lift (fun a : T.Obj ↦ of (S := T.toRigidSignature) a) fun g ↦
    eqToHom (projectObj_of_eq T (T.src g)) ≫
      coupon (S := T.toRigidSignature) g ≫
      eqToHom (projectObj_of_eq T (T.tgt g)).symm

instance (T : TensorSignature.{u, v}) : (ofFreeMonoidal T).Monoidal :=
  inferInstanceAs
    (FreeMonoidal.lift (fun a : T.Obj ↦ of (S := T.toRigidSignature) a) fun g ↦
      eqToHom (projectObj_of_eq T (T.src g)) ≫
        coupon (S := T.toRigidSignature) g ≫
        eqToHom (projectObj_of_eq T (T.tgt g)).symm).Monoidal

@[simp]
theorem ofFreeMonoidal_obj_of (T : TensorSignature.{u, v}) (a : T.Obj) :
    (ofFreeMonoidal T).obj (FreeMonoidal.of a) = of a := rfl

theorem ofFreeMonoidal_obj_eq (T : TensorSignature.{u, v}) (X : T.FreeMonoidal) :
    (ofFreeMonoidal T).obj X = ⟨X.as.toRigidObject⟩ :=
  projectObj_of_eq T X.as

@[simp]
theorem ofFreeMonoidal_map_coupon (T : TensorSignature.{u, v}) (g : T.Coupon) :
    (ofFreeMonoidal T).map (FreeMonoidal.coupon g) =
      eqToHom (projectObj_of_eq T (T.src g)) ≫
        coupon (S := T.toRigidSignature) g ≫
        eqToHom (projectObj_of_eq T (T.tgt g)).symm :=
  FreeMonoidal.lift_map_coupon _ _ g

end OfFreeMonoidal

section Uniqueness

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation between strong monoidal functors out of `S.FreeRigid` is
determined by its components at the generating objects: unit and tensor components are determined by
monoidality, and dual components are determined by `NatTrans.app_eq_iff_of_exactPairing`. -/
theorem natTrans_ext {F G : S.FreeRigid ⥤ D} [F.Monoidal] [G.Monoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β] (h : ∀ a, α.app (of a) = β.app (of a)) :
    α = β := by
  ext ⟨X⟩
  induction X with
  | of a => exact h a
  | unit =>
    rw [← cancel_epi (ε F)]
    exact (NatTrans.IsMonoidal.unit (τ := α)).trans (NatTrans.IsMonoidal.unit (τ := β)).symm
  | tensor X Y hX hY =>
    rw [← cancel_epi (μ F ⟨X⟩ ⟨Y⟩)]
    refine (NatTrans.IsMonoidal.tensor (τ := α) ⟨X⟩ ⟨Y⟩).trans ?_
    refine Eq.trans ?_ (NatTrans.IsMonoidal.tensor (τ := β) ⟨X⟩ ⟨Y⟩).symm
    rw [hX, hY]
  | rightDual X hX =>
    let X' : S.FreeRigid := ⟨X⟩
    let XR : S.FreeRigid := ⟨X.rightDual⟩
    have : ExactPairing X' XR := (RightRigidCategory.rightDual X').exact
    exact (NatTrans.app_eq_iff_of_exactPairing (α := α) (β := β) X' XR).mp hX
  | leftDual X hX =>
    let XL : S.FreeRigid := ⟨X.leftDual⟩
    let X' : S.FreeRigid := ⟨X⟩
    have : ExactPairing XL X' := (LeftRigidCategory.leftDual X').exact
    exact (NatTrans.app_eq_iff_of_exactPairing (α := α) (β := β) XL X').mpr hX

variable [RigidCategory D] (F G : S.FreeRigid ⥤ D) [F.Monoidal] [G.Monoidal]
  (e : ∀ a, F.obj (of a) ≅ G.obj (of a))

/-- The isomorphism between the images of a formal rigid object under two strong monoidal functors
out of `S.FreeRigid` into a rigid category `D`, induced by generator isomorphisms `e` together with
the unit, tensor, and chosen-dual comparisons of `F` and `G`. -/
noncomputable def wordIso : ∀ X : RigidObject S.Obj, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩
  | .of a => e a
  | .unit => (Functor.Monoidal.εIso F).symm ≪≫ Functor.Monoidal.εIso G
  | .tensor X Y =>
    (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (wordIso X ⊗ᵢ wordIso Y) ≪≫
      Functor.Monoidal.μIso G ⟨X⟩ ⟨Y⟩
  | .rightDual X =>
    F.mapRightDualIso ⟨X⟩ ≪≫ (wordIso X).symm.rightAdjointMate ≪≫
      (G.mapRightDualIso ⟨X⟩).symm
  | .leftDual X =>
    F.mapLeftDualIso ⟨X⟩ ≪≫ (wordIso X).symm.leftAdjointMate ≪≫
      (G.mapLeftDualIso ⟨X⟩).symm

@[simp]
theorem wordIso_of (a : S.Obj) : wordIso F G e (of a).as = e a := by rfl

@[simp]
theorem wordIso_tensorUnit_hom : (wordIso F G e (𝟙_ S.FreeRigid).as).hom = η F ≫ ε G := by rfl

@[simp]
theorem wordIso_tensor_hom (X Y : S.FreeRigid) :
    (wordIso F G e (X ⊗ Y).as).hom =
      δ F X Y ≫ ((wordIso F G e X.as).hom ⊗ₘ (wordIso F G e Y.as).hom) ≫ μ G X Y := by rfl

@[simp]
theorem wordIso_rightDual_hom (X : S.FreeRigid) :
    (wordIso F G e Xᘁ.as).hom =
      (F.mapRightDualIso X).hom ≫ ((wordIso F G e X.as).inv)ᘁ ≫
        (G.mapRightDualIso X).inv := by
  change (F.mapRightDualIso X ≪≫ (wordIso F G e X.as).symm.rightAdjointMate ≪≫
    (G.mapRightDualIso X).symm).hom = _
  simp

@[simp]
theorem wordIso_leftDual_hom (X : S.FreeRigid) :
    (wordIso F G e (ᘁX).as).hom =
      (F.mapLeftDualIso X).hom ≫ (ᘁ((wordIso F G e X.as).inv)) ≫
        (G.mapLeftDualIso X).inv := by
  change (F.mapLeftDualIso X ≪≫ (wordIso F G e X.as).symm.leftAdjointMate ≪≫
    (G.mapLeftDualIso X).symm).hom = _
  simp

variable {F G e}

attribute [local simp] whiskerLeft_comp_tensorHom whiskerLeft_comp_tensorHom_assoc
  whiskerRight_comp_tensorHom whiskerRight_comp_tensorHom_assoc tensorHom_comp_whiskerLeft
  tensorHom_comp_whiskerLeft_assoc tensorHom_comp_whiskerRight tensorHom_comp_whiskerRight_assoc

/-- The family `wordIso F G e` is natural with respect to every morphism of `S.FreeRigid` as soon as
it commutes with the coupons. -/
theorem map_comp_wordIso_hom
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))
    {X Y : S.FreeRigid} (f : X ⟶ Y) :
    F.map f ≫ (wordIso F G e Y.as).hom = (wordIso F G e X.as).hom ≫ G.map f := by
  induction f using Hom.inductionOn with
  | id X => simp
  | α_hom X Y Z =>
    rw [← cancel_epi (μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z),
      ← cancel_mono (δ G X (Y ⊗ Z) ≫ G.obj X ◁ δ G Y Z)]
    simp [← Functor.OplaxMonoidal.associativity]
  | α_inv X Y Z =>
    rw [← cancel_epi (F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z)),
      ← cancel_mono (δ G (X ⊗ Y) Z ≫ δ G X Y ▷ G.obj Z)]
    simp [← Functor.OplaxMonoidal.associativity_inv]
  | l_hom X =>
    rw [← cancel_epi (ε F ▷ F.obj X ≫ μ F (𝟙_ _) X)]
    simp
    simp [tensorHom_def']
  | l_inv X =>
    rw [← cancel_mono (δ G (𝟙_ _) X ≫ η G ▷ G.obj X)]
    simp
    simp [MonoidalCategory.tensorHom_def, ← Functor.OplaxMonoidal.left_unitality]
  | ρ_hom X =>
    rw [← cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ _))]
    simp
    simp [MonoidalCategory.tensorHom_def]
  | ρ_inv X =>
    rw [← cancel_mono (δ G X (𝟙_ _) ≫ G.obj X ◁ η G)]
    simp
    simp [tensorHom_def', ← Functor.OplaxMonoidal.right_unitality]
  | η_right X =>
    -- Cancel the unit comparison of `F` on the left and the inverse tensorator of `G` on the
    -- right, then slide `(wordIso X).hom` against its inverse's right mate across coevaluation.
    rw [← cancel_epi (ε F), ← cancel_mono (δ G X Xᘁ)]
    simp only [wordIso_tensorUnit_hom, wordIso_tensor_hom, wordIso_rightDual_hom, Category.assoc,
      Functor.Monoidal.ε_η_assoc, Functor.Monoidal.μ_δ, Category.comp_id,
      ← F.coevaluation_whiskerLeft_mapRightDualIso_inv_assoc,
      ← G.coevaluation_whiskerLeft_mapRightDualIso_inv, whiskerLeft_comp_tensorHom,
      Iso.inv_hom_id_assoc]
    rw [← tensorHom_comp_whiskerLeft, tensorHom_def']
    simp only [Category.assoc, coevaluation_comp_rightAdjointMate_assoc,
      ← comp_whiskerRight_assoc, Iso.inv_hom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  | ε_right X =>
    -- Cancel the tensorator of `F` on the left and the inverse unit comparison of `G` on the
    -- right, then evaluate the right mate of `(wordIso X).inv` against `(wordIso X).hom`.
    rw [← cancel_epi (μ F Xᘁ X), ← cancel_mono (η G)]
    simp only [wordIso_tensorUnit_hom, wordIso_tensor_hom, wordIso_rightDual_hom, Category.assoc,
      Functor.Monoidal.ε_η, Category.comp_id, Functor.Monoidal.μ_δ_assoc,
      ← G.mapRightDualIso_hom_whiskerRight_evaluation,
      ← F.mapRightDualIso_hom_whiskerRight_evaluation, tensorHom_comp_whiskerRight_assoc,
      Iso.inv_hom_id]
    rw [← whiskerRight_comp_tensorHom_assoc, tensorHom_def']
    simp only [Category.assoc, rightAdjointMate_comp_evaluation,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  | η_left X =>
    rw [← cancel_epi (ε F), ← cancel_mono (δ G (ᘁX) X)]
    simp only [wordIso_tensorUnit_hom, wordIso_tensor_hom, wordIso_leftDual_hom, Category.assoc,
      Functor.Monoidal.ε_η_assoc, Functor.Monoidal.μ_δ, Category.comp_id,
      ← F.coevaluation_mapLeftDualIso_inv_whiskerRight_assoc,
      ← G.coevaluation_mapLeftDualIso_inv_whiskerRight, whiskerRight_comp_tensorHom,
      Iso.inv_hom_id_assoc]
    rw [← tensorHom_comp_whiskerRight, MonoidalCategory.tensorHom_def]
    simp only [Category.assoc, coevaluation_comp_leftAdjointMate_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  | ε_left X =>
    rw [← cancel_epi (μ F X (ᘁX)), ← cancel_mono (η G)]
    simp only [wordIso_tensorUnit_hom, wordIso_tensor_hom, wordIso_leftDual_hom, Category.assoc,
      Functor.Monoidal.ε_η, Category.comp_id, Functor.Monoidal.μ_δ_assoc,
      ← G.whiskerLeft_mapLeftDualIso_hom_evaluation,
      ← F.whiskerLeft_mapLeftDualIso_hom_evaluation, tensorHom_comp_whiskerLeft_assoc,
      Iso.inv_hom_id]
    rw [← whiskerLeft_comp_tensorHom_assoc, MonoidalCategory.tensorHom_def]
    simp only [Category.assoc, leftAdjointMate_comp_evaluation, ← comp_whiskerRight_assoc,
      Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  | coupon g => exact he g
  | comp f g hf hg =>
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg, reassoc_of% hf]
  | whiskerLeft X f hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerLeft, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerLeft_comp_tensorHom_assoc,
      tensorHom_comp_whiskerLeft_assoc, hf]
  | whiskerRight f X hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerRight, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerRight_comp_tensorHom_assoc,
      tensorHom_comp_whiskerRight_assoc, hf]

/-- Two strong monoidal functors out of `S.FreeRigid` into a rigid category `D` that agree up to
isomorphisms `e` on the generating objects, compatibly with every coupon, are connected by a
monoidal natural isomorphism extending `e`. -/
noncomputable def monoidalNatIso
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g)) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ wordIso F G e X.as) fun f ↦ map_comp_wordIso_hom he f

variable (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
  (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeRigid) :
    (monoidalNatIso he).hom.app X = (wordIso F G e X.as).hom := by rfl

@[simp]
theorem monoidalNatIso_inv_app (X : S.FreeRigid) :
    (monoidalNatIso he).inv.app X = (wordIso F G e X.as).inv := by rfl

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso he).hom.app (of a) = (e a).hom := by rfl

instance : NatTrans.IsMonoidal (monoidalNatIso he).hom where
  unit := by
    rw [monoidalNatIso_hom_app, wordIso_tensorUnit_hom, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    rw [monoidalNatIso_hom_app, wordIso_tensor_hom, Functor.Monoidal.μ_δ_assoc,
      monoidalNatIso_hom_app, monoidalNatIso_hom_app]

end Uniqueness

end FreeRigid

end RigidSignature

end TauCeti
