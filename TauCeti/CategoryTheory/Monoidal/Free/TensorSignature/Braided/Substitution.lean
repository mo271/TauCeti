/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.EqToHom
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Substitution

/-!
# Braided substitution of tensor expressions for coupons

A `TensorSignature.BraidedSubstitution S T` replaces object generators of `S` by formal tensor
words in `T.FreeBraided` and coupons of `S` by raw braided morphism expressions in `T` between the
substituted source and target words (`FreeBraided.Hom.subst`). The strong braided functor
`BraidedSubstitution.toFunctor` is the universal lift of the substitution data, its morphism action
agrees with raw substitution (`toFunctor_map_homMk`), and `FreeBraided.HomEquiv.subst` deduces that
raw substitution respects the braided monoidal axioms.

Braided substitutions form a category under `BraidedSubstitution.id` and `BraidedSubstitution.comp`
(`id_comp`, `comp_id`, `comp_assoc`), and `toFunctor` preserves identities and composition up to
monoidal natural isomorphism (`idToFunctorIso`, `compToFunctorIso`). Every monoidal substitution
embeds via `Substitution.toBraided`, compatibly with `FreeMonoidal.toFreeBraided`. The formal
design adapts `TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Substitution`
(`TauCeti.TensorSignature.Substitution`) to braided expressions.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
* P. Selinger, *A survey of graphical languages for monoidal categories*, Lecture Notes in Physics
  813 (2011), §3.3.
-/

public section

universe u v u' v' u'' v'' u''' v'''

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- A typed braided substitution between tensor signatures: object generators are replaced by
formal tensor words in `T.FreeBraided`, and coupons by raw braided expressions between the
substituted source and target words. -/
@[ext]
structure BraidedSubstitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The formal tensor word replacing each object generator. -/
  obj : S.Obj → T.FreeBraided
  /-- The raw braided expression replacing each coupon. -/
  coupon : ∀ g : S.Coupon, FreeBraided.Hom
    (projectObj obj (S.src g)).as (projectObj obj (S.tgt g)).as

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}} {V : TensorSignature.{u''', v'''}}

namespace BraidedSubstitution

/-- Pointwise extensionality for braided substitutions using heterogeneous equality on coupons. -/
theorem ext' {σ₁ σ₂ : BraidedSubstitution S T} (h₁ : ∀ a, σ₁.obj a = σ₂.obj a)
    (h₂ : ∀ g, σ₁.coupon g ≍ σ₂.coupon g) : σ₁ = σ₂ := by
  cases σ₁ with | mk obj₁ c₁ =>
  cases σ₂ with | mk obj₂ c₂ =>
  cases funext h₁
  exact congrArg _ (funext fun g ↦ eq_of_heq (h₂ g))

end BraidedSubstitution

namespace FreeBraided

/-- Substitute formal tensor words for object generators and raw braided expressions for
coupons. -/
def Hom.subst (σ : BraidedSubstitution S T) : ∀ {X Y}, Hom X Y →
    Hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .id X => .id (projectObj σ.obj X).as
  | _, _, .α_hom X Y Z => .α_hom (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .α_inv X Y Z => .α_inv (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .l_hom X => .l_hom (projectObj σ.obj X).as
  | _, _, .l_inv X => .l_inv (projectObj σ.obj X).as
  | _, _, .ρ_hom X => .ρ_hom (projectObj σ.obj X).as
  | _, _, .ρ_inv X => .ρ_inv (projectObj σ.obj X).as
  | _, _, .β_hom X Y => .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .β_inv X Y => .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (projectObj σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp] theorem Hom.subst_id (σ : BraidedSubstitution S T) (X) :
    (Hom.id X).subst σ = .id (projectObj σ.obj X).as := (rfl)
@[simp] theorem Hom.subst_coupon (σ : BraidedSubstitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := (rfl)
@[simp] theorem Hom.subst_comp (σ : BraidedSubstitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := (rfl)
@[simp] theorem Hom.subst_tensor (σ : BraidedSubstitution S T) {W X Y Z}
    (f : Hom W X) (g : Hom Y Z) : (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := (rfl)
@[simp] theorem Hom.subst_whiskerLeft (σ : BraidedSubstitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (projectObj σ.obj X).as := (rfl)
@[simp] theorem Hom.subst_whiskerRight (σ : BraidedSubstitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (projectObj σ.obj X).as := (rfl)
@[simp] theorem Hom.subst_α_hom (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := (rfl)
@[simp] theorem Hom.subst_α_inv (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := (rfl)
@[simp] theorem Hom.subst_l_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (projectObj σ.obj X).as := (rfl)
@[simp] theorem Hom.subst_l_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (projectObj σ.obj X).as := (rfl)
@[simp] theorem Hom.subst_ρ_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (projectObj σ.obj X).as := (rfl)
@[simp] theorem Hom.subst_ρ_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (projectObj σ.obj X).as := (rfl)
@[simp] theorem Hom.subst_β_hom (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_hom X Y).subst σ = .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as := (rfl)
@[simp] theorem Hom.subst_β_inv (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_inv X Y).subst σ = .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as := (rfl)

theorem Hom.subst_cast_heq (σ : BraidedSubstitution S T)
    {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y') (f : Hom X Y) :
    (f.cast hX hY).subst σ ≍ f.subst σ := by
  subst hX hY; rw [Hom.cast_rfl]

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

variable (σ : BraidedSubstitution S T)

/-- The strong braided functor induced by a braided substitution. -/
@[expose] def toFunctor : S.FreeBraided ⥤ T.FreeBraided :=
  FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Monoidal
instance : σ.toFunctor.Braided := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Braided

@[simp] theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ := FreeBraided.lift_ε _ _
@[simp] theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ := FreeBraided.lift_η _ _
@[simp] theorem toFunctor_μ (X Y : S.FreeBraided) : Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_μ _ _ X Y
@[simp] theorem toFunctor_δ (X Y : S.FreeBraided) : Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_δ _ _ X Y
@[simp] theorem toFunctor_obj (X : S.FreeBraided) : σ.toFunctor.obj X = projectObj σ.obj X.as := rfl
@[simp] theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeBraided.coupon g) = FreeBraided.homMk (σ.coupon g) :=
  FreeBraided.lift_map_coupon _ _ g

/-- Interpreting a raw braided expression by `σ.toFunctor` produces `homMk (f.subst σ)`. -/
@[simp] theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    σ.toFunctor.map (FreeBraided.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeBraided.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | β_hom X Y => exact lift_map_braiding_hom _ _ ⟨X⟩ ⟨Y⟩
  | β_inv X Y => exact lift_map_braiding_inv _ _ ⟨X⟩ ⟨Y⟩
  | coupon g => exact lift_map_coupon _ _ g
  | comp f g hf hg => exact (liftMap_comp _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ (homMk f)).trans (congrArg (projectObj σ.obj X ◁ ·) hf)
  | whiskerRight f X hf =>
    exact (lift_map_whiskerRight _ _ (homMk f) ⟨X⟩).trans (congrArg (· ▷ projectObj σ.obj X) hf)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end BraidedSubstitution

namespace FreeBraided

/-- Braided substitution preserves the relation generated by the braided monoidal axioms. -/
theorem HomEquiv.subst (σ : BraidedSubstitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

/-! ### Identity and composition of braided substitutions -/

private def idCoupon (S : TensorSignature.{u, v}) (g : S.Coupon) :
    FreeBraided.Hom (projectObj FreeBraided.of (S.src g)).as
      (projectObj FreeBraided.of (S.tgt g)).as :=
  (Hom.coupon g).cast (congrArg FreeBraided.as (projectObj_of_eq (S.src g))).symm
    (congrArg FreeBraided.as (projectObj_of_eq (S.tgt g))).symm

/-- The identity braided substitution on `S`, sending each object generator to itself and each
coupon to itself along the canonical word identification `projectObj_of_eq`. -/
def id (S : TensorSignature.{u, v}) : BraidedSubstitution S S := ⟨FreeBraided.of, idCoupon S⟩

@[simp] theorem id_obj (a : S.Obj) : (id S).obj a = FreeBraided.of a := (rfl)
@[simp] theorem projectObj_id_obj (X : FreeMonoidalCategory S.Obj) :
    projectObj (id S).obj X = ⟨X⟩ := projectObj_of_eq X
@[simp] theorem id_coupon (g : S.Coupon) :
    (id S).coupon g = (Hom.coupon g).cast
      (congrArg FreeBraided.as (projectObj_id_obj (S.src g))).symm
      (congrArg FreeBraided.as (projectObj_id_obj (S.tgt g))).symm := (rfl)
theorem id_coupon_heq (g : S.Coupon) : (id S).coupon g ≍ Hom.coupon g :=
  Hom.cast_heq _ _ (Hom.coupon g)

/-- Substituting the identity braided substitution into any raw braided expression leaves it
unchanged (heterogeneously, and strictly after casting endpoints). -/
theorem subst_id_heq {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    f.subst (id S) ≍ f := by
  induction f with
  | coupon g => exact id_coupon_heq g
  | _ => dsimp only [Hom.subst]; congr <;> exact projectObj_id_obj _

/-- Interpreting a word along composite generator images agrees with iterating `projectObj`. -/
theorem comp_projectObj_eq (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    projectObj (fun a ↦ projectObj τ.obj (σ.obj a).as) X =
      projectObj τ.obj (projectObj σ.obj X).as := by
  induction X with
  | of _ | unit => rfl
  | tensor _ _ hX hY => exact congrArg₂ (· ⊗ ·) hX hY

private def compCoupon (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) (g : S.Coupon) :
    FreeBraided.Hom (projectObj (fun a ↦ projectObj τ.obj (σ.obj a).as) (S.src g)).as
      (projectObj (fun a ↦ projectObj τ.obj (σ.obj a).as) (S.tgt g)).as :=
  ((σ.coupon g).subst τ).cast (congrArg FreeBraided.as (comp_projectObj_eq τ σ (S.src g))).symm
    (congrArg FreeBraided.as (comp_projectObj_eq τ σ (S.tgt g))).symm

/-- Composition of braided substitutions: `τ.comp σ` first applies `σ` and then `τ`. -/
def comp (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) : BraidedSubstitution S U :=
  ⟨fun a ↦ projectObj τ.obj (σ.obj a).as, compCoupon τ σ⟩

@[simp] theorem comp_obj (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) (a : S.Obj) :
    (τ.comp σ).obj a = projectObj τ.obj (σ.obj a).as := (rfl)
theorem projectObj_comp_obj (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    projectObj (τ.comp σ).obj X = projectObj τ.obj (projectObj σ.obj X).as :=
  comp_projectObj_eq τ σ X
@[simp] theorem comp_coupon (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (g : S.Coupon) :
    (τ.comp σ).coupon g = ((σ.coupon g).subst τ).cast
      (congrArg FreeBraided.as (projectObj_comp_obj τ σ (S.src g))).symm
      (congrArg FreeBraided.as (projectObj_comp_obj τ σ (S.tgt g))).symm := (rfl)
theorem comp_coupon_heq (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (g : S.Coupon) : (τ.comp σ).coupon g ≍ (σ.coupon g).subst τ :=
  Hom.cast_heq _ _ ((σ.coupon g).subst τ)

/-- Iterated raw braided substitution agrees with substituting the composite substitution. -/
theorem subst_comp_heq (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    (f.subst σ).subst τ ≍ f.subst (τ.comp σ) := by
  induction f with
  | coupon g => exact (comp_coupon_heq τ σ g).symm
  | _ => dsimp only [Hom.subst]; congr <;> exact (projectObj_comp_obj τ σ _).symm

@[simp] theorem id_comp (σ : BraidedSubstitution S T) : (id T).comp σ = σ :=
  ext' (fun a ↦ projectObj_id_obj (σ.obj a).as) fun g ↦
    (comp_coupon_heq (id T) σ g).trans (subst_id_heq (σ.coupon g))

@[simp] theorem comp_id (σ : BraidedSubstitution S T) : σ.comp (id S) = σ :=
  ext' (fun a ↦ congrArg (fun X : S.FreeBraided ↦ projectObj σ.obj X.as) (id_obj a)) fun g ↦
    (comp_coupon_heq σ (id S) g).trans
      (by rw [id_coupon]; exact Hom.subst_cast_heq σ _ _ (Hom.coupon g))

/-- Composition of braided substitutions is associative. -/
theorem comp_assoc (υ : BraidedSubstitution U V) (τ : BraidedSubstitution T U)
    (σ : BraidedSubstitution S T) : (υ.comp τ).comp σ = υ.comp (τ.comp σ) :=
  ext' (fun a ↦ by simp only [comp_obj, projectObj_comp_obj]) fun g ↦
    ((comp_coupon_heq (υ.comp τ) σ g).trans (subst_comp_heq υ τ (σ.coupon g)).symm).trans
      ((comp_coupon_heq υ (τ.comp σ) g).trans
        (by rw [comp_coupon]; exact Hom.subst_cast_heq υ _ _ ((σ.coupon g).subst τ))).symm

/-! ### Functoriality of `toFunctor` up to monoidal natural isomorphism -/

private theorem wordIso_eqToIso_hom {D : Type*} [Category* D] [MonoidalCategory D]
    (F G : S.FreeBraided ⥤ D) [F.Monoidal] [G.Monoidal] (h : ∀ X : S.FreeBraided, F.obj X = G.obj X)
    (h_unit : Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε G = eqToHom (h (𝟙_ S.FreeBraided)))
    (h_tensor : ∀ X Y : S.FreeBraided, Functor.OplaxMonoidal.δ F X Y ≫
      (eqToHom (h X) ⊗ₘ eqToHom (h Y)) ≫ Functor.LaxMonoidal.μ G X Y = eqToHom (h (X ⊗ Y)))
    (X : FreeMonoidalCategory S.Obj) :
    (FreeBraided.wordIso F G (fun a ↦ eqToIso (h (FreeBraided.of a))) X).hom =
      eqToHom (h ⟨X⟩) := by
  induction X with
  | of a => exact (congrArg Iso.hom (FreeBraided.wordIso_of F G _ a)).trans (eqToIso.hom _)
  | unit => exact (FreeBraided.wordIso_tensorUnit_hom F G _).trans h_unit
  | tensor Y Z hY hZ =>
    refine (FreeBraided.wordIso_tensor_hom F G _ ⟨Y⟩ ⟨Z⟩).trans ?_; rw [hY, hZ]; exact h_tensor _ _

private theorem id_toFunctor_obj (X : S.FreeBraided) :
    (id S).toFunctor.obj X = (𝟭 S.FreeBraided).obj X := projectObj_id_obj X.as

private theorem wordIso_id_hom (X : FreeMonoidalCategory S.Obj) :
    (FreeBraided.wordIso (id S).toFunctor (𝟭 S.FreeBraided)
      (fun a ↦ eqToIso (id_toFunctor_obj (FreeBraided.of a))) X).hom =
      eqToHom (id_toFunctor_obj ⟨X⟩) :=
  wordIso_eqToIso_hom _ _ id_toFunctor_obj
    (by rw [(id S).toFunctor_η, Functor.LaxMonoidal.id_ε]; erw [Category.comp_id]; rfl)
    (fun Y Z ↦ by
      have hf : Functor.OplaxMonoidal.δ (id S).toFunctor Y Z = eqToHom rfl :=
        ((id S).toFunctor_δ Y Z).trans rfl
      have hg : Functor.LaxMonoidal.μ (𝟭 S.FreeBraided) Y Z = eqToHom rfl :=
        (Functor.LaxMonoidal.id_μ Y Z).trans rfl
      rw [TauCeti.eqToHom_tensorHom_eqToHom, hf, hg]
      exact (congrArg (_ ≫ ·) (eqToHom_trans _ _)).trans (eqToHom_trans _ _)) X

/-- The strong braided functor of the identity substitution is monoidally naturally isomorphic to
the identity functor on `S.FreeBraided`. -/
def idToFunctorIso (S : TensorSignature.{u, v}) : (id S).toFunctor ≅ 𝟭 S.FreeBraided :=
  FreeBraided.monoidalNatIso fun g ↦ by
    rw [wordIso_id_hom, wordIso_id_hom]
    have hf : (id S).toFunctor.map (FreeBraided.coupon g) =
        eqToHom (id_toFunctor_obj ⟨S.src g⟩) ≫ FreeBraided.coupon g ≫
          eqToHom (id_toFunctor_obj ⟨S.tgt g⟩).symm :=
      ((id S).toFunctor_map_coupon g).trans
        (by rw [id_coupon]; exact FreeBraided.homMk_cast _ _ (Hom.coupon g))
    exact (comp_eqToHom_iff (id_toFunctor_obj ⟨S.tgt g⟩) _
      (eqToHom (id_toFunctor_obj ⟨S.src g⟩) ≫ _)).2
        (by simpa only [Functor.id_map, Category.assoc] using hf)

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (idToFunctorIso S).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (FreeBraided.monoidalNatIso _).hom)

@[simp] theorem idToFunctorIso_hom_app_of (a : S.Obj) :
    (idToFunctorIso S).hom.app (FreeBraided.of a) = eqToHom (id_obj a) := by
  rw [idToFunctorIso, FreeBraided.monoidalNatIso_hom_app, wordIso_id_hom]; rfl

private theorem comp_toFunctor_obj (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : S.FreeBraided) : (τ.comp σ).toFunctor.obj X = (σ.toFunctor ⋙ τ.toFunctor).obj X :=
  projectObj_comp_obj τ σ X.as

private theorem wordIso_comp_hom (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    (FreeBraided.wordIso (τ.comp σ).toFunctor (σ.toFunctor ⋙ τ.toFunctor)
      (fun a ↦ eqToIso (comp_toFunctor_obj τ σ (FreeBraided.of a))) X).hom =
      eqToHom (comp_toFunctor_obj τ σ ⟨X⟩) :=
  wordIso_eqToIso_hom _ _ (comp_toFunctor_obj τ σ)
    (by rw [(τ.comp σ).toFunctor_η, Functor.LaxMonoidal.comp_ε, τ.toFunctor_ε, σ.toFunctor_ε]
        erw [Functor.map_id, Category.comp_id, Category.comp_id]; rfl)
    (fun Y Z ↦ by
      have hf : Functor.OplaxMonoidal.δ (τ.comp σ).toFunctor Y Z = eqToHom rfl :=
        ((τ.comp σ).toFunctor_δ Y Z).trans rfl
      have hg : Functor.LaxMonoidal.μ (σ.toFunctor ⋙ τ.toFunctor) Y Z = eqToHom rfl := by
        rw [Functor.LaxMonoidal.comp_μ, τ.toFunctor_μ, σ.toFunctor_μ]
        erw [Functor.map_id, Category.comp_id]; rfl
      rw [TauCeti.eqToHom_tensorHom_eqToHom, hf, hg]
      exact (congrArg (_ ≫ ·) (eqToHom_trans _ _)).trans (eqToHom_trans _ _)) X

/-- The strong braided functor of a composite substitution `τ.comp σ` is monoidally naturally
isomorphic to `σ.toFunctor ⋙ τ.toFunctor`. -/
def compToFunctorIso (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) :
    (τ.comp σ).toFunctor ≅ σ.toFunctor ⋙ τ.toFunctor :=
  FreeBraided.monoidalNatIso fun g ↦ by
    rw [wordIso_comp_hom, wordIso_comp_hom]
    have hrhs : (σ.toFunctor ⋙ τ.toFunctor).map (FreeBraided.coupon g) =
        FreeBraided.homMk ((σ.coupon g).subst τ) :=
      (congrArg τ.toFunctor.map (σ.toFunctor_map_coupon g)).trans (τ.toFunctor_map_homMk _)
    have hf : (τ.comp σ).toFunctor.map (FreeBraided.coupon g) =
        eqToHom (comp_toFunctor_obj τ σ ⟨S.src g⟩) ≫
          (σ.toFunctor ⋙ τ.toFunctor).map (FreeBraided.coupon g) ≫
            eqToHom (comp_toFunctor_obj τ σ ⟨S.tgt g⟩).symm :=
      ((τ.comp σ).toFunctor_map_coupon g).trans (by
        rw [comp_coupon]
        exact (FreeBraided.homMk_cast _ _ _).trans
          (congrArg (fun m ↦ eqToHom _ ≫ m ≫ eqToHom _) hrhs.symm))
    exact (comp_eqToHom_iff (comp_toFunctor_obj τ σ ⟨S.tgt g⟩) _
      (eqToHom (comp_toFunctor_obj τ σ ⟨S.src g⟩) ≫ _)).2 (by simpa only [Category.assoc] using hf)

instance (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) :
    NatTrans.IsMonoidal (compToFunctorIso τ σ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (FreeBraided.monoidalNatIso _).hom)

@[simp] theorem compToFunctorIso_hom_app_of (τ : BraidedSubstitution T U)
    (σ : BraidedSubstitution S T) (a : S.Obj) :
    (compToFunctorIso τ σ).hom.app (FreeBraided.of a) = eqToHom (comp_obj τ σ a) := by
  rw [compToFunctorIso, FreeBraided.monoidalNatIso_hom_app, wordIso_comp_hom]; rfl

end BraidedSubstitution

namespace Substitution

/-! ### Comparison with monoidal substitutions -/

/-- Interpreting a word along `FreeMonoidal.toFreeBraided.obj ∘ σ.obj` agrees with applying
`FreeMonoidal.toFreeBraided` to `projectObj σ.obj X`. -/
theorem toFreeBraided_projectObj_eq (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) X =
      FreeMonoidal.toFreeBraided.obj (projectObj σ.obj X) := by
  induction X with
  | of _ | unit => rfl
  | tensor _ _ hX hY => exact congrArg₂ (· ⊗ ·) hX hY

private theorem toFreeBraided_projectObj_as (σ : Substitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    (projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) X).as =
      (projectObj σ.obj X).as :=
  congrArg FreeBraided.as
    ((toFreeBraided_projectObj_eq σ X).trans
      (FreeMonoidal.toFreeBraided_obj (projectObj σ.obj X)))

private def toBraidedCoupon (σ : Substitution S T) (g : S.Coupon) :
    FreeBraided.Hom (projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) (S.src g)).as
      (projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) (S.tgt g)).as :=
  ((σ.coupon g).toBraided).cast (toFreeBraided_projectObj_as σ (S.src g)).symm
    (toFreeBraided_projectObj_as σ (S.tgt g)).symm

/-- Embed a monoidal substitution `Substitution S T` into a `BraidedSubstitution S T`. -/
def toBraided (σ : Substitution S T) : BraidedSubstitution S T :=
  ⟨fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a), toBraidedCoupon σ⟩

@[simp] theorem toBraided_obj (σ : Substitution S T) (a : S.Obj) :
    σ.toBraided.obj a = FreeMonoidal.toFreeBraided.obj (σ.obj a) := (rfl)
theorem projectObj_toBraided_obj (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    projectObj σ.toBraided.obj X = FreeMonoidal.toFreeBraided.obj (projectObj σ.obj X) :=
  toFreeBraided_projectObj_eq σ X
theorem projectObj_toBraided_obj_as (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    (projectObj σ.toBraided.obj X).as = (projectObj σ.obj X).as :=
  toFreeBraided_projectObj_as σ X
@[simp] theorem toBraided_coupon (σ : Substitution S T) (g : S.Coupon) :
    σ.toBraided.coupon g = ((σ.coupon g).toBraided).cast
      (projectObj_toBraided_obj_as σ (S.src g)).symm
      (projectObj_toBraided_obj_as σ (S.tgt g)).symm := (rfl)
theorem toBraided_coupon_heq (σ : Substitution S T) (g : S.Coupon) :
    σ.toBraided.coupon g ≍ (σ.coupon g).toBraided :=
  FreeBraided.Hom.cast_heq _ _ (σ.coupon g).toBraided

private theorem toBraided_toFunctor_obj (σ : Substitution S T) (X : S.FreeMonoidal) :
    (FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor).obj X =
      (σ.toFunctor ⋙ FreeMonoidal.toFreeBraided).obj X :=
  (congrArg σ.toBraided.toFunctor.obj (FreeMonoidal.toFreeBraided_obj X)).trans
    (projectObj_toBraided_obj σ X.as)

private theorem wordIso_toBraided_hom (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    (FreeMonoidal.wordIso (FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor)
      (σ.toFunctor ⋙ FreeMonoidal.toFreeBraided)
      (fun a ↦ eqToIso (toBraided_toFunctor_obj σ (FreeMonoidal.of a))) X).hom =
      eqToHom (toBraided_toFunctor_obj σ ⟨X⟩) := by
  let F := FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor
  let G := σ.toFunctor ⋙ FreeMonoidal.toFreeBraided
  let e := fun a ↦ eqToIso (toBraided_toFunctor_obj σ (FreeMonoidal.of a))
  induction X with
  | of a => exact (congrArg Iso.hom (FreeMonoidal.wordIso_of F G e a)).trans (eqToIso.hom _)
  | unit =>
    refine (FreeMonoidal.wordIso_tensorUnit_hom F G e).trans ?_; dsimp only [F, G]
    rw [Functor.OplaxMonoidal.comp_η, FreeMonoidal.toFreeBraided_η, σ.toBraided.toFunctor_η,
      Functor.LaxMonoidal.comp_ε, FreeMonoidal.toFreeBraided_ε, σ.toFunctor_ε]
    erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]; rfl
  | tensor Y Z hY hZ =>
    refine (FreeMonoidal.wordIso_tensor_hom F G e ⟨Y⟩ ⟨Z⟩).trans ?_
    have hf : Functor.OplaxMonoidal.δ F ⟨Y⟩ ⟨Z⟩ = eqToHom rfl := by
      dsimp only [F]; rw [Functor.OplaxMonoidal.comp_δ, FreeMonoidal.toFreeBraided_δ,
        σ.toBraided.toFunctor_δ]; erw [Functor.map_id, Category.id_comp]; rfl
    have hg : Functor.LaxMonoidal.μ G ⟨Y⟩ ⟨Z⟩ = eqToHom rfl := by
      dsimp only [G]; rw [Functor.LaxMonoidal.comp_μ, FreeMonoidal.toFreeBraided_μ,
        σ.toFunctor_μ]; erw [Functor.map_id, Category.comp_id]; rfl
    rw [hY, hZ, TauCeti.eqToHom_tensorHom_eqToHom, hf, hg]
    exact (congrArg (_ ≫ ·) (eqToHom_trans _ _)).trans (eqToHom_trans _ _)

/-- `FreeMonoidal.toFreeBraided` intertwines `σ.toFunctor` and `σ.toBraided.toFunctor` up to a
monoidal natural isomorphism. -/
def toBraidedToFunctorIso (σ : Substitution S T) :
    FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor ≅
      σ.toFunctor ⋙ FreeMonoidal.toFreeBraided :=
  FreeMonoidal.monoidalNatIso fun g ↦ by
    rw [wordIso_toBraided_hom, wordIso_toBraided_hom]
    have hlhs₁ : (FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor).map
          (FreeMonoidal.coupon g) ≍ σ.toBraided.toFunctor.map (FreeBraided.coupon g) := by
      dsimp only [Functor.comp_map]
      rw [FreeMonoidal.toFreeBraided_map_coupon, Functor.map_comp, Functor.map_comp,
        eqToHom_map, eqToHom_map]
      exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
    have hlhs₂ : σ.toBraided.toFunctor.map (FreeBraided.coupon g) ≍
        FreeBraided.homMk (X := ⟨(projectObj σ.obj (S.src g)).as⟩)
          (Y := ⟨(projectObj σ.obj (S.tgt g)).as⟩) (σ.coupon g).toBraided := by
      rw [σ.toBraided.toFunctor_map_coupon, toBraided_coupon]
      exact (conj_eqToHom_iff_heq' _ _ _ _).1 (FreeBraided.homMk_cast
        (projectObj_toBraided_obj_as σ (S.src g)).symm
        (projectObj_toBraided_obj_as σ (S.tgt g)).symm (σ.coupon g).toBraided)
    have hrhs : (σ.toFunctor ⋙ FreeMonoidal.toFreeBraided).map (FreeMonoidal.coupon g) ≍
        FreeBraided.homMk (X := ⟨(projectObj σ.obj (S.src g)).as⟩)
          (Y := ⟨(projectObj σ.obj (S.tgt g)).as⟩) (σ.coupon g).toBraided := by
      dsimp only [Functor.comp_map]; rw [σ.toFunctor_map_coupon]
      exact FreeMonoidal.toFreeBraided_map_homMk_heq (σ.coupon g)
    have hf := (conj_eqToHom_iff_heq _ _ (toBraided_toFunctor_obj σ ⟨S.src g⟩)
      (toBraided_toFunctor_obj σ ⟨S.tgt g⟩)).2 ((hlhs₁.trans hlhs₂).trans hrhs.symm)
    exact (comp_eqToHom_iff (toBraided_toFunctor_obj σ ⟨S.tgt g⟩) _
      (eqToHom (toBraided_toFunctor_obj σ ⟨S.src g⟩) ≫ _)).2
        (by simpa only [Category.assoc] using hf)

instance (σ : Substitution S T) : NatTrans.IsMonoidal (toBraidedToFunctorIso σ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (FreeMonoidal.monoidalNatIso _).hom)

end Substitution

end TauCeti.TensorSignature
