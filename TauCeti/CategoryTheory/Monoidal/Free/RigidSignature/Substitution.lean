/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Substitution
public import TauCeti.CategoryTheory.Monoidal.Free.RigidSignature.Basic

/-!
# Substitution of rigid expressions for coupons

A `RigidSignature.Substitution S T` replaces object generators of `S` by formal rigid object
expressions in `T` and coupons of `S` by raw morphism expressions in `T` with the resulting
boundaries. An object generator may be replaced by the formal unit, by a multi-factor tensor
product, or by an arbitrarily dualized expression; at odd dual levels its ports reverse order while
at even dual levels they keep their order, with integer winding levels preserved throughout.

`FreeRigid.Hom.subst` performs this replacement directly on raw morphism terms before quotienting by
the monoidal and snake axioms, and `FreeRigid.HomEquiv.subst` proves that it respects both families
of axioms without requiring any equations between the replacing coupons. The induced strong monoidal
functor `Substitution.toFunctor` is obtained from `FreeRigid.lift`,
`Substitution.toFunctor_map_homMk` identifies its action on equivalence classes with `Hom.subst`,
and `Substitution.normalize_toFunctor_obj` identifies its object action on normalized boundaries
with `WindingWord.subst`.

The design mirrors `TauCeti.TensorSignature.Substitution`. The mathematical setting follows
Joyal–Street, *The geometry of tensor calculus I*, §1, and *Planar diagrams and tensor algebra*, §2.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory

namespace TauCeti.RigidSignature

/-- A typed raw substitution between rigid signatures. Object generators of `S` are replaced by
objects of `T.FreeRigid` (formal rigid object expressions in `T`), and coupons of `S` are replaced
by raw morphism expressions in `T` between the interpreted source and target boundaries. The two
signatures need not share the same universes. -/
@[ext]
structure Substitution (S : RigidSignature.{u, v}) (T : RigidSignature.{u', v'}) where
  /-- The formal rigid object expression replacing each generating object. -/
  obj : S.Obj → T.FreeRigid
  /-- The raw morphism expression replacing each coupon. -/
  coupon : ∀ g : S.Coupon, FreeRigid.Hom
    (RigidObject.projectObj obj (S.src g)).as (RigidObject.projectObj obj (S.tgt g)).as

variable {S : RigidSignature.{u, v}} {T : RigidSignature.{u', v'}}

namespace FreeRigid

/-- Interpreting a formal rigid object in `T.FreeRigid` via `RigidObject.projectObj` agrees on
underlying syntax with `RigidObject.subst`. -/
@[simp]
theorem projectObj_as_eq_subst (f : S.Obj → T.FreeRigid) (X : RigidObject S.Obj) :
    (RigidObject.projectObj f X).as = X.subst (fun a ↦ (f a).as) := by
  induction X with
  | of a => simp
  | unit => simp; rfl
  | tensor X Y ihX ihY =>
    simp only [RigidObject.projectObj_tensor, RigidObject.subst_tensor, ← ihX, ← ihY]
    rfl
  | rightDual X ihX =>
    simp only [RigidObject.projectObj_rightDual, RigidObject.subst_rightDual, ← ihX]
    rfl
  | leftDual X ihX =>
    simp only [RigidObject.projectObj_leftDual, RigidObject.subst_leftDual, ← ihX]
    rfl

/-- Substitute formal rigid object expressions for object generators and raw morphism expressions
for coupons. Because `RigidObject.projectObj` and the monoidal and rigid object operations on
`T.FreeRigid` are exposed, the endpoints of all structural constructors match definitionally without
`eqToHom` casts. -/
def Hom.subst (σ : Substitution S T) : ∀ {X Y : RigidObject S.Obj}, Hom X Y →
    Hom (RigidObject.projectObj σ.obj X).as (RigidObject.projectObj σ.obj Y).as
  | _, _, .id X => .id (RigidObject.projectObj σ.obj X).as
  | _, _, .α_hom X Y Z => .α_hom (RigidObject.projectObj σ.obj X).as
      (RigidObject.projectObj σ.obj Y).as (RigidObject.projectObj σ.obj Z).as
  | _, _, .α_inv X Y Z => .α_inv (RigidObject.projectObj σ.obj X).as
      (RigidObject.projectObj σ.obj Y).as (RigidObject.projectObj σ.obj Z).as
  | _, _, .l_hom X => .l_hom (RigidObject.projectObj σ.obj X).as
  | _, _, .l_inv X => .l_inv (RigidObject.projectObj σ.obj X).as
  | _, _, .ρ_hom X => .ρ_hom (RigidObject.projectObj σ.obj X).as
  | _, _, .ρ_inv X => .ρ_inv (RigidObject.projectObj σ.obj X).as
  | _, _, .η_right X => .η_right (RigidObject.projectObj σ.obj X).as
  | _, _, .ε_right X => .ε_right (RigidObject.projectObj σ.obj X).as
  | _, _, .η_left X => .η_left (RigidObject.projectObj σ.obj X).as
  | _, _, .ε_left X => .ε_left (RigidObject.projectObj σ.obj X).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (RigidObject.projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (RigidObject.projectObj σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp]
theorem Hom.subst_id (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.id X).subst σ = .id (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_coupon (σ : Substitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl

@[simp]
theorem Hom.subst_comp (σ : Substitution S T) {X Y Z : RigidObject S.Obj}
    (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_tensor (σ : Substitution S T) {W X Y Z : RigidObject S.Obj}
    (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_whiskerLeft (σ : Substitution S T) (X : RigidObject S.Obj)
    {Y Z : RigidObject S.Obj} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (RigidObject.projectObj σ.obj X).as := by
  rfl

@[simp]
theorem Hom.subst_whiskerRight (σ : Substitution S T) {Y Z : RigidObject S.Obj}
    (f : Hom Y Z) (X : RigidObject S.Obj) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (RigidObject.projectObj σ.obj X).as := by
  rfl

@[simp]
theorem Hom.subst_α_hom (σ : Substitution S T) (X Y Z : RigidObject S.Obj) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (RigidObject.projectObj σ.obj X).as (RigidObject.projectObj σ.obj Y).as
        (RigidObject.projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_α_inv (σ : Substitution S T) (X Y Z : RigidObject S.Obj) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (RigidObject.projectObj σ.obj X).as (RigidObject.projectObj σ.obj Y).as
        (RigidObject.projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_l_hom (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.l_hom X).subst σ = .l_hom (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_l_inv (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.l_inv X).subst σ = .l_inv (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_hom (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_inv (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_η_right (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.η_right X).subst σ = .η_right (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ε_right (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.ε_right X).subst σ = .ε_right (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_η_left (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.η_left X).subst σ = .η_left (RigidObject.projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ε_left (σ : Substitution S T) (X : RigidObject S.Obj) :
    (Hom.ε_left X).subst σ = .ε_left (RigidObject.projectObj σ.obj X).as := by rfl

end FreeRigid

namespace Substitution

open FreeRigid

variable (σ : Substitution S T)

/-- The strong monoidal functor induced by a raw rigid substitution, defined as the universal lift
of the replacing objects and the equivalence classes of the replacing coupons. Its definition is
exposed so that substituted raw morphisms have definitionally matching endpoints. -/
@[expose]
def toFunctor : S.FreeRigid ⥤ T.FreeRigid :=
  FreeRigid.lift σ.obj (fun g ↦ FreeRigid.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal :=
  inferInstanceAs (FreeRigid.lift σ.obj (fun g ↦ FreeRigid.homMk (σ.coupon g))).Monoidal

@[simp]
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ :=
  FreeRigid.lift_ε _ _

@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ :=
  FreeRigid.lift_η _ _

@[simp]
theorem toFunctor_μ (X Y : S.FreeRigid) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeRigid.lift_μ _ _ X Y

@[simp]
theorem toFunctor_δ (X Y : S.FreeRigid) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeRigid.lift_δ _ _ X Y

@[simp]
theorem toFunctor_obj (X : S.FreeRigid) :
    σ.toFunctor.obj X = RigidObject.projectObj σ.obj X.as := rfl

@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeRigid.coupon g) = FreeRigid.homMk (σ.coupon g) :=
  FreeRigid.lift_map_coupon _ _ g

@[simp]
theorem toFunctor_mapRightDualIso (X : S.FreeRigid) :
    σ.toFunctor.mapRightDualIso X = Iso.refl _ :=
  FreeRigid.lift_mapRightDualIso _ _ X

@[simp]
theorem toFunctor_mapLeftDualIso (X : S.FreeRigid) :
    σ.toFunctor.mapLeftDualIso X = Iso.refl _ :=
  FreeRigid.lift_mapLeftDualIso _ _ X

/-- Normalizing the image of an object under `σ.toFunctor` agrees with substituting the normalized
replacing boundaries via `WindingWord.subst`, reversing multi-port replacements at odd dual levels
and retaining integer dual levels throughout. -/
theorem normalize_toFunctor_obj (X : S.FreeRigid) :
    (σ.toFunctor.obj X).as.normalize =
      WindingWord.subst (fun a ↦ (σ.obj a).as.normalize) X.as.normalize := by
  rw [toFunctor_obj, projectObj_as_eq_subst, RigidObject.normalize_subst]

/-- Applying `σ.toFunctor` to the equivalence class of a raw morphism yields the equivalence class
of its raw substitution `f.subst σ`. -/
@[simp]
theorem toFunctor_map_homMk {X Y : RigidObject S.Obj} (f : FreeRigid.Hom X Y) :
    σ.toFunctor.map (FreeRigid.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeRigid.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | η_right X => exact lift_map_coevaluation_right _ _ ⟨X⟩
  | ε_right X => exact lift_map_evaluation_right _ _ ⟨X⟩
  | η_left X => exact lift_map_coevaluation_left _ _ ⟨X⟩
  | ε_left X => exact lift_map_evaluation_left _ _ ⟨X⟩
  | coupon g => exact lift_map_coupon _ _ g
  | comp f g hf hg =>
    exact (liftMap_comp _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ (homMk f)).trans
      (congrArg (RigidObject.projectObj σ.obj X ◁ ·) hf)
  | whiskerRight f X hf =>
    exact (lift_map_whiskerRight _ _ (homMk f) ⟨X⟩).trans
      (congrArg (· ▷ RigidObject.projectObj σ.obj X) hf)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end Substitution

namespace FreeRigid

/-- Raw substitution preserves the congruence generated by the monoidal-category and snake (zigzag)
axioms, without requiring any equations between the replacing coupons. -/
theorem HomEquiv.subst (σ : Substitution S T) {X Y : RigidObject S.Obj} {f g : Hom X Y}
    (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeRigid

end TauCeti.RigidSignature
